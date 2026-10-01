import KiknadzeKrasnov.FiniteTimeAsymptotics
import KiknadzeKrasnov.EndpointRatio
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace KiknadzeKrasnov
noncomputable section
open Set Filter MeasureTheory intervalIntegral
open scoped Topology

/-- The singular-family exponential integrand is continuous at every positive argument. -/
theorem singularExpIntegrand_continuousAt {lambda p y : ℝ} (hy : 0 < y) :
    ContinuousAt (fun v => Real.exp (singularAccumNoncritical lambda p v)) y := by
  unfold singularAccumNoncritical
  exact Real.continuous_exp.continuousAt.comp
    (continuousAt_const.mul
      (continuousAt_const.sub (Real.continuousAt_rpow_const y (1 - p)
        (Or.inl hy.ne'))))

/-- Actual derivative of the endpoint integral; no asymptotic hypothesis is assumed. -/
theorem singularExpIntegralY_hasDerivAt {lambda p y : ℝ} (hy : 0 < y) :
    HasDerivAt (singularExpIntegralY lambda p)
      (-Real.exp (singularAccumNoncritical lambda p y)) y := by
  have hc : ContinuousOn (fun v => Real.exp (singularAccumNoncritical lambda p v))
      (Ioi (0 : ℝ)) := fun v hv =>
    (singularExpIntegrand_continuousAt hv).continuousWithinAt
  have hi : IntervalIntegrable
      (fun v => Real.exp (singularAccumNoncritical lambda p v)) volume y 1 := by
    apply ContinuousOn.intervalIntegrable
    apply hc.mono
    intro v hv
    rw [uIcc] at hv
    have hm : 0 < min y 1 := lt_min hy zero_lt_one
    exact lt_of_lt_of_le hm hv.1
  have hm : StronglyMeasurableAtFilter
      (fun v => Real.exp (singularAccumNoncritical lambda p v)) (𝓝 y) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (fun v hv => singularExpIntegrand_continuousAt hv) y hy
  exact intervalIntegral.integral_hasDerivAt_left hi hm
    (singularExpIntegrand_continuousAt hy)

/-- Endpoint comparison scale diverges for p>1, by exponential domination of powers. -/
theorem singularEndpointD_tendsto_atTop {lambda p : ℝ}
    (hl : 0 < lambda) (hp : 1 < p) :
    Tendsto (singularEndpointD lambda p) (𝓝[>] 0) atTop := by
  let c : ℝ := lambda / (p - 1)
  let k : ℝ := p / (p - 1)
  have hc : 0 < c := div_pos hl (sub_pos.mpr hp)
  have hz : Tendsto (fun y : ℝ => y ^ (1 - p)) (𝓝[>] 0) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (sub_neg.mpr hp)
  have he := (tendsto_exp_mul_div_rpow_atTop k c hc).comp hz
  have hlim := he.const_mul_atTop (div_pos (Real.exp_pos (-c)) hl)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hpow : (y ^ (1 - p)) ^ k = y ^ (-p) := by
    rw [← Real.rpow_mul hy.le]
    congr 1
    dsimp [k]
    field_simp [(sub_pos.mpr hp).ne']
    ring
  have hA : singularAccumNoncritical lambda p y = -c + c * y ^ (1 - p) := by
    unfold singularAccumNoncritical c
    rw [show 1 - p = -(p - 1) by ring, div_neg]
    ring
  dsimp only [Function.comp_apply]
  unfold singularEndpointD
  rw [hA, Real.exp_add, hpow, Real.rpow_neg hy.le]
  simp only [div_inv_eq_mul]
  ring

/-- The derivative ratio of the endpoint integral and comparison scale tends to one. -/
theorem singularEndpoint_derivative_ratio {lambda p : ℝ}
    (hl : 0 < lambda) (hp : 1 < p) :
    Tendsto (fun y => -Real.exp (singularAccumNoncritical lambda p y) /
      singularEndpointDDot lambda p y) (𝓝[>] 0) (𝓝 1) := by
  have hpow := rpow_tendsto_zero_nhdsGT (sub_pos.mpr hp)
  have hcoef : Tendsto (fun y : ℝ => 1 - (p / lambda) * y ^ (p - 1))
      (𝓝[>] 0) (𝓝 1) := by
    simpa using (hpow.const_mul (p / lambda)).const_sub 1
  have hlim := hcoef.inv₀ one_ne_zero
  rw [inv_one] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [singularEndpointDDot_eq hy hl.ne']
  field_simp [(Real.exp_pos (singularAccumNoncritical lambda p y)).ne']

/-- Supplement S044: the actual endpoint integral has the leading Laplace balance. -/
theorem singularExpIntegralY_endpoint_ratio {lambda p : ℝ}
    (hl : 0 < lambda) (hp : 1 < p) :
    Tendsto (fun y => singularExpIntegralY lambda p y /
      singularEndpointD lambda p y) (𝓝[>] 0) (𝓝 1) := by
  apply endpoint_ratio_tendsto_one
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact singularExpIntegralY_hasDerivAt hy
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact singularEndpointD_hasDerivAt hy hl.ne' (ne_of_gt hp)
  · have hpow := rpow_tendsto_zero_nhdsGT (sub_pos.mpr hp)
    have hcoef : Tendsto (fun y : ℝ => 1 - (p / lambda) * y ^ (p - 1))
        (𝓝[>] 0) (𝓝 1) := by
      simpa using (hpow.const_mul (p / lambda)).const_sub 1
    filter_upwards [self_mem_nhdsWithin, hcoef.eventually (Ioi_mem_nhds zero_lt_one)]
      with y hy hpos
    rw [singularEndpointDDot_eq hy hl.ne']
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos (Real.exp_pos _)) hpos
  · exact singularEndpointD_tendsto_atTop hl hp
  · exact singularEndpoint_derivative_ratio hl hp

/-- The initial-condition term is lower order in the supercritical endpoint balance. -/
theorem singularInverseScaleY_supercritical_ratio {nu T h0 lambda p : ℝ}
    (hn : 0 < nu) (hT : 0 < T) (hl : 0 < lambda) (hp : 1 < p) :
    Tendsto (fun y => singularInverseScaleY nu T h0 lambda p y /
      (4 * nu * T * y ^ p / lambda)) (𝓝[>] 0) (𝓝 1) := by
  have hJ := singularExpIntegralY_endpoint_ratio hl hp
  have hD := (singularEndpointD_tendsto_atTop hl hp).inv_tendsto_atTop
  have hlim : Tendsto (fun y => (h0 / (4 * nu * T)) *
      (singularEndpointD lambda p y)⁻¹ +
        singularExpIntegralY lambda p y / singularEndpointD lambda p y)
      (𝓝[>] 0) (𝓝 1) := by
    simpa using (hD.const_mul (h0 / (4 * nu * T))).add hJ
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  unfold singularInverseScaleY singularEndpointD
  rw [Real.exp_neg]
  field_simp [hn.ne', hT.ne', hl.ne', (Real.exp_pos _).ne',
    (Real.rpow_pos_of_pos hy p).ne']

/-- Complete p>1 certificate: beta/a tends to 1/(4 nu), written as a ratio-one limit. -/
theorem singularBetaY_supercritical_ratio {nu T h0 lambda p : ℝ}
    (hn : 0 < nu) (hT : 0 < T) (hl : 0 < lambda) (hp : 1 < p) :
    Tendsto (fun y => singularBetaY nu T h0 lambda p y /
      (singularStrainY lambda T p y / (4 * nu))) (𝓝[>] 0) (𝓝 1) := by
  have hlim := singularInverseScaleY_supercritical_ratio
    (h0 := h0) hn hT hl hp
  have hR : ∀ᶠ y in 𝓝[>] (0 : ℝ), 4 * nu * T * y ^ p / lambda ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (div_pos (mul_pos (mul_pos (mul_pos (by norm_num) hn) hT)
      (Real.rpow_pos_of_pos hy p)) hl).ne'
  have hH := eventually_ne_zero_of_ratio_tendsto_one hlim hR
  have hi := inverse_ratio_tendsto_one hlim hH hR
  apply hi.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  unfold singularBetaY singularStrainY
  rw [Real.rpow_neg hy.le]
  field_simp [hn.ne', hT.ne', hl.ne', (Real.rpow_pos_of_pos hy p).ne']

end
end KiknadzeKrasnov
