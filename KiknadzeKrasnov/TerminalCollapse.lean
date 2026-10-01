import KiknadzeKrasnov.SingularFamilyDynamics

namespace KiknadzeKrasnov
noncomputable section
open Filter Set
open scoped Topology

/-- The positive terminal variable tends to zero from the right as physical time tends to T from the left. -/
theorem terminalY_tendsto_terminal {T : ℝ} (hT : 0 < T) :
    Tendsto (terminalY T) (𝓝[<] T) (𝓝[>] 0) := by
  have hc : ContinuousAt (terminalY T) T := by unfold terminalY; fun_prop
  have h0 : Tendsto (terminalY T) (𝓝[<] T) (𝓝 0) := by
    simpa [terminalY, hT.ne'] using hc.tendsto.mono_left
      (show 𝓝[<] T ≤ 𝓝 T from inf_le_left)
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h0
  filter_upwards [self_mem_nhdsWithin] with t ht
  change t < T at ht
  unfold terminalY
  exact sub_pos.mpr ((div_lt_one hT).mpr ht)

/-- Positivity of the exact p=1 inverse scale before the terminal time. -/
theorem reciprocalInverseScaleNoncritical_pos {nu T h0 lambda y : ℝ}
    (hn : 0 < nu) (hT : 0 < T) (hh : 0 < h0) (hy : 0 < y)
    (hy1 : y ≤ 1) (hl : lambda ≠ 1) :
    0 < reciprocalInverseScaleNoncritical nu T h0 lambda y := by
  have hfrac : 0 ≤ (1 - y ^ (1 - lambda)) / (1 - lambda) := by
    rcases lt_or_gt_of_ne hl with hlt | hgt
    · exact div_nonneg (sub_nonneg.mpr (Real.rpow_le_one hy.le hy1
        (sub_nonneg.mpr hlt.le))) (sub_nonneg.mpr hlt.le)
    · exact div_nonneg_of_nonpos
        (sub_nonpos.mpr (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy hy1
          (sub_nonpos.mpr hgt.le))) (sub_nonpos.mpr hgt.le)
  unfold reciprocalInverseScaleNoncritical
  apply mul_pos (Real.rpow_pos_of_pos hy _)
  have hnonneg : 0 ≤ 4 * nu * T * ((1 - y ^ (1 - lambda)) / (1 - lambda)) := by positivity
  rw [← mul_div_assoc] at hnonneg
  linarith

/-- Every positive lambda in the p=1 noncritical branch gives actual core collapse. -/
theorem reciprocalBeta_noncritical_tendsto_atTop {nu T h0 lambda : ℝ}
    (hn : 0 < nu) (hT : 0 < T) (hh : 0 < h0) (hl : 0 < lambda) (hl1 : lambda ≠ 1) :
    Tendsto (fun y => (reciprocalInverseScaleNoncritical nu T h0 lambda y)⁻¹)
      (𝓝[>] 0) atTop := by
  have hpos : ∀ᶠ y in 𝓝[>] (0 : ℝ), 0 < reciprocalInverseScaleNoncritical nu T h0 lambda y := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)] with y hy hy1
    change 0 < y at hy
    change y < 1 at hy1
    exact reciprocalInverseScaleNoncritical_pos hn hT hh hy (le_of_lt hy1) hl1
  apply (inv_tendsto_atTop_iff_tendsto_zero_of_eventually_pos hpos).mpr
  have hy : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ)) tendsto_id
  have hlim := ((rpow_tendsto_zero_nhdsGT hl).const_mul
    (h0 + 4 * nu * T / (1 - lambda))).sub (hy.const_mul (4 * nu * T / (1 - lambda)))
  have hz : Tendsto (fun y => (h0 + 4 * nu * T / (1 - lambda)) * y ^ lambda -
      (4 * nu * T / (1 - lambda)) * y) (𝓝[>] 0) (𝓝 0) := by simpa using hlim
  apply hz.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (reciprocalInverseScaleNoncritical_decomp hy hl1).symm

/-- The logarithmic critical branch also collapses; y log(1/y) still tends to zero. -/
theorem reciprocalBeta_critical_tendsto_atTop {nu T h0 : ℝ}
    (hn : 0 < nu) (hT : 0 < T) (hh : 0 < h0) :
    Tendsto (fun y => (reciprocalInverseScaleCritical nu T h0 y)⁻¹)
      (𝓝[>] 0) atTop := by
  have hpos : ∀ᶠ y in 𝓝[>] (0 : ℝ), 0 < reciprocalInverseScaleCritical nu T h0 y := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)] with y hy hy1
    change 0 < y at hy
    change y < 1 at hy1
    have hlog : 0 < Real.log (y⁻¹) := by
      rw [Real.log_pos_iff (inv_nonneg.mpr (le_of_lt hy))]
      exact (one_lt_inv₀ hy).mpr hy1
    unfold reciprocalInverseScaleCritical
    positivity
  apply (inv_tendsto_atTop_iff_tendsto_zero_of_eventually_pos hpos).mpr
  have hy : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ)) tendsto_id
  have hl := tendsto_log_mul_rpow_nhdsGT_zero (r := 1) zero_lt_one
  have hlog : Tendsto (fun y : ℝ => y * Real.log (y⁻¹)) (𝓝[>] 0) (𝓝 0) := by
    convert hl.neg using 1
    · funext y; simp [Real.log_inv, mul_comm]
    · simp
  have hlim := (hy.const_mul h0).add (hlog.const_mul (4 * nu * T))
  convert hlim using 1
  · funext y; unfold reciprocalInverseScaleCritical; ring
  · simp

/-- Radius asymptotics follow from the proved inverse-scale ratios by continuity of square root. -/
theorem radius_ratio_tendsto_one {α : Type*} {l : Filter α} {H R : α → ℝ}
    (hlim : Tendsto (fun x => H x / R x) l (𝓝 1))
    (hpos : ∀ᶠ x in l, 0 ≤ H x) :
    Tendsto (fun x => Real.sqrt (H x) / Real.sqrt (R x)) l (𝓝 1) := by
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hlim
  rw [Real.sqrt_one] at h
  apply h.congr'
  filter_upwards [hpos] with x hx
  exact Real.sqrt_div hx (R x)

/-- Positive initial scale stays positive throughout the positive terminal-coordinate interval. -/
theorem singularInverseScaleY_pos {nu T h0 lambda p y : ℝ}
    (hn : 0 < nu) (hT : 0 < T) (hh : 0 < h0) (_hy : 0 < y) (hy1 : y ≤ 1) :
    0 < singularInverseScaleY nu T h0 lambda p y := by
  have hJ : 0 ≤ singularExpIntegralY lambda p y := by
    apply intervalIntegral.integral_nonneg hy1
    intro v hv
    exact Real.exp_nonneg _
  unfold singularInverseScaleY
  apply mul_pos (Real.exp_pos _)
  have hnonneg : 0 ≤ 4 * nu * T * singularExpIntegralY lambda p y := by positivity
  linarith

/-- The proved supercritical balance yields actual beta blow-up for p>1. -/
theorem singularBetaY_supercritical_tendsto_atTop {nu T h0 lambda p : ℝ}
    (hn : 0 < nu) (hT : 0 < T) (hh : 0 < h0) (hl : 0 < lambda) (hp : 1 < p) :
    Tendsto (singularBetaY nu T h0 lambda p) (𝓝[>] 0) atTop := by
  have hpos : ∀ᶠ y in 𝓝[>] (0 : ℝ), 0 < singularInverseScaleY nu T h0 lambda p y := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)] with y hy hy1
    change 0 < y at hy
    change y < 1 at hy1
    exact singularInverseScaleY_pos hn hT hh hy (le_of_lt hy1)
  unfold singularBetaY
  apply (inv_tendsto_atTop_iff_tendsto_zero_of_eventually_pos hpos).mpr
  have hr : Tendsto (fun y : ℝ => 4 * nu * T * y ^ p / lambda) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((rpow_tendsto_zero_nhdsGT (lt_trans zero_lt_one hp)).const_mul
      (4 * nu * T)).div_const lambda
  have h := (singularInverseScaleY_supercritical_ratio (h0 := h0) hn hT hl hp).mul hr
  have hz : Tendsto (fun y => (singularInverseScaleY nu T h0 lambda p y /
      (4 * nu * T * y ^ p / lambda)) * (4 * nu * T * y ^ p / lambda))
      (𝓝[>] 0) (𝓝 0) := by simpa using h
  apply hz.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hrne : 4 * nu * T * y ^ p / lambda ≠ 0 := by
    exact (div_pos (mul_pos (mul_pos (mul_pos (by norm_num) hn) hT)
      (Real.rpow_pos_of_pos hy p)) hl).ne'
  exact div_mul_cancel₀ _ hrne

end
end KiknadzeKrasnov
