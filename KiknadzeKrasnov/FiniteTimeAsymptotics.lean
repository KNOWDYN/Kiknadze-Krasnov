import KiknadzeKrasnov.FiniteTimeCriteria
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace KiknadzeKrasnov

noncomputable section

open Filter Set MeasureTheory intervalIntegral
open scoped Topology

/-!
Detailed finite-time scale asymptotics from Supplementary Eqs. (42)--(51).
The terminal variable is y=1-t/T.  This file keeps asymptotic statements as
literal filter limits, rather than informal proportionality notation.
-/

/-- Supplementary Eq. (43): terminal similarity variable y=1-t/T. -/
def terminalY (T t : ℝ) : ℝ := 1 - t / T

/-- Supplementary Eq. (43): singular strain family written in y. -/
def singularStrainY (lambda T p y : ℝ) : ℝ :=
  lambda / T * y ^ (-p)

/-- Supplementary Eq. (44), p != 1 branch, written as a function of y. -/
def singularAccumNoncritical (lambda p y : ℝ) : ℝ :=
  lambda / (1 - p) * (1 - y ^ (1 - p))

/-- Supplementary Eq. (44), p=1 branch. -/
def singularAccumCritical (lambda y : ℝ) : ℝ :=
  lambda * Real.log (y⁻¹)

/-- Supplementary Eq. (46): exact p=1 inverse scale for lambda != 1. -/
def reciprocalInverseScaleNoncritical
    (nu T h0 lambda y : ℝ) : ℝ :=
  y ^ lambda *
    (h0 + 4 * nu * T * (1 - y ^ (1 - lambda)) / (1 - lambda))

/-- Supplementary Eq. (48): exact p=1 inverse scale at lambda=1. -/
def reciprocalInverseScaleCritical
    (nu T h0 y : ℝ) : ℝ :=
  y * (h0 + 4 * nu * T * Real.log (y⁻¹))

/-- The positive-scale beta associated with an inverse scale h. -/
def betaFromInverseScale (h : ℝ) : ℝ := h⁻¹

/-- Positive powers vanish as y approaches zero from the right. -/
theorem rpow_tendsto_zero_nhdsGT {q : ℝ} (hq : 0 < q) :
    Tendsto (fun y : ℝ => y ^ q) (𝓝[>] 0) (𝓝 0) := by
  have hfull := (Real.continuous_rpow_const hq.le).tendsto 0
  have h := hfull.mono_left inf_le_left
  simpa [Real.zero_rpow hq.ne'] using h

/-- Exact y-space viscous integral obtained from Eq. (42) after
t=T(1-y). -/
def singularExpIntegralY (lambda p y : ℝ) : ℝ :=
  ∫ v in y..1, Real.exp (singularAccumNoncritical lambda p v)

/-- Exact inverse scale in the p≠1 singular family, expressed in y. -/
def singularInverseScaleY
    (nu T h0 lambda p y : ℝ) : ℝ :=
  Real.exp (-(singularAccumNoncritical lambda p y)) *
    (h0 + 4 * nu * T * singularExpIntegralY lambda p y)

/-- Corresponding beta in the p≠1 singular family. -/
def singularBetaY
    (nu T h0 lambda p y : ℝ) : ℝ :=
  (singularInverseScaleY nu T h0 lambda p y)⁻¹

/-- For 0<p<1 the accumulated strain has the finite terminal value
lambda/(1-p), Supplementary Eq. (45). -/
theorem singularAccumNoncritical_subcritical_tendsto
    {lambda p : ℝ} (hp1 : p < 1) :
    Tendsto (singularAccumNoncritical lambda p)
      (𝓝[>] 0) (𝓝 (lambda / (1 - p))) := by
  have hpow := rpow_tendsto_zero_nhdsGT (sub_pos.mpr hp1)
  unfold singularAccumNoncritical
  simpa using (hpow.const_sub 1).const_mul (lambda / (1 - p))

/-- The y-space exponential integrand is continuous when p<1. -/
theorem singularExpIntegrand_continuous
    {lambda p : ℝ} (hp1 : p < 1) :
    Continuous (fun y : ℝ =>
      Real.exp (singularAccumNoncritical lambda p y)) := by
  have hpow : Continuous (fun y : ℝ => y ^ (1 - p)) :=
    Real.continuous_rpow_const (sub_nonneg.mpr hp1.le)
  unfold singularAccumNoncritical
  exact Real.continuous_exp.comp
    (continuous_const.mul (continuous_const.sub hpow))

/-- For 0<p<1 the exact viscous integral has a finite terminal value. -/
theorem singularExpIntegralY_subcritical_tendsto
    {lambda p : ℝ} (hp1 : p < 1) :
    Tendsto (singularExpIntegralY lambda p)
      (𝓝[>] 0)
      (𝓝 (∫ v in 0..1,
        Real.exp (singularAccumNoncritical lambda p v))) := by
  let E : ℝ → ℝ :=
    fun v => Real.exp (singularAccumNoncritical lambda p v)
  have hE : Continuous E := singularExpIntegrand_continuous hp1
  have hInt : ∀ a b : ℝ, IntervalIntegrable E volume a b :=
    fun a b => hE.intervalIntegrable a b
  have hP :
      Tendsto (fun y => ∫ v in 0..y, E v)
        (𝓝[>] 0) (𝓝 0) := by
    have hc := intervalIntegral.continuous_primitive hInt 0
    have hc0 : Tendsto (fun y => ∫ v in 0..y, E v)
        (𝓝 0) (𝓝 0) := by
      simpa using hc.continuousAt.tendsto
    exact tendsto_nhdsWithin_of_tendsto_nhds
      (s := Ioi (0 : ℝ)) hc0
  have hlim :
      Tendsto
        (fun y => (∫ v in 0..1, E v) - ∫ v in 0..y, E v)
        (𝓝[>] 0) (𝓝 (∫ v in 0..1, E v)) := by
    simpa using tendsto_const_nhds.sub hP
  apply hlim.congr'
  filter_upwards with y
  unfold singularExpIntegralY E
  rw [intervalIntegral.integral_add_adjacent_intervals
    (hInt 0 y) (hInt y 1)]
  ring

/-- The exact inverse scale has a finite positive terminal limit for
0<p<1 when h0,nu,T are positive. -/
theorem singularInverseScaleY_subcritical_tendsto
    {nu T h0 lambda p : ℝ}
    (hnu : 0 < nu) (hT : 0 < T) (hh0 : 0 < h0)
    (hp0 : 0 < p) (hp1 : p < 1) :
    let H :=
      Real.exp (-(lambda / (1 - p))) *
        (h0 + 4 * nu * T *
          (∫ v in 0..1,
            Real.exp (singularAccumNoncritical lambda p v)))
    Tendsto (singularInverseScaleY nu T h0 lambda p)
      (𝓝[>] 0) (𝓝 H) ∧ 0 < H := by
  dsimp
  have hA := singularAccumNoncritical_subcritical_tendsto
    (lambda := lambda) hp1
  have hE :
      Tendsto
        (fun y => Real.exp (-(singularAccumNoncritical lambda p y)))
        (𝓝[>] 0) (𝓝 (Real.exp (-(lambda / (1 - p))))) :=
    hA.neg.exp
  have hJ := singularExpIntegralY_subcritical_tendsto
    (lambda := lambda) hp1
  have hbracket :
      Tendsto
        (fun y => h0 + 4 * nu * T * singularExpIntegralY lambda p y)
        (𝓝[>] 0)
        (𝓝 (h0 + 4 * nu * T *
          (∫ v in 0..1,
            Real.exp (singularAccumNoncritical lambda p v)))) := by
    simpa using (hJ.const_mul (4 * nu * T)).const_add h0
  have hlim := hE.mul hbracket
  have hIntNonneg :
      0 ≤ ∫ v in 0..1,
        Real.exp (singularAccumNoncritical lambda p v) := by
    exact intervalIntegral.integral_nonneg zero_le_one
      (fun v hv => (Real.exp_pos _).le)
  have hbrpos :
      0 < h0 + 4 * nu * T *
        (∫ v in 0..1,
          Real.exp (singularAccumNoncritical lambda p v)) := by
    have hcoef : 0 ≤ 4 * nu * T := by positivity
    nlinarith [mul_nonneg hcoef hIntNonneg]
  constructor
  · simpa [singularInverseScaleY] using hlim
  · exact mul_pos (Real.exp_pos _) hbrpos

/-- Supplementary p<1 conclusion in beta form: the distributed scale has a
finite positive terminal value, hence no distributed-core collapse occurs. -/
theorem singularBetaY_subcritical_tendsto_finite
    {nu T h0 lambda p : ℝ}
    (hnu : 0 < nu) (hT : 0 < T) (hh0 : 0 < h0)
    (hp0 : 0 < p) (hp1 : p < 1) :
    let H :=
      Real.exp (-(lambda / (1 - p))) *
        (h0 + 4 * nu * T *
          (∫ v in 0..1,
            Real.exp (singularAccumNoncritical lambda p v)))
    Tendsto (singularBetaY nu T h0 lambda p)
      (𝓝[>] 0) (𝓝 H⁻¹) ∧ 0 < H⁻¹ := by
  dsimp
  rcases singularInverseScaleY_subcritical_tendsto
      hnu hT hh0 hp0 hp1 with ⟨hH, hHpos⟩
  constructor
  · unfold singularBetaY
    exact hH.inv₀ hHpos.ne'
  · exact inv_pos.mpr hHpos

/-- log(1/y) diverges to +infinity at the terminal endpoint. -/
theorem log_inv_tendsto_atTop_nhdsGT :
    Tendsto (fun y : ℝ => Real.log (y⁻¹)) (𝓝[>] 0) atTop := by
  simpa [Real.log_inv] using
    (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)

/-- Reciprocal logarithm tends to zero at the terminal endpoint. -/
theorem inv_log_inv_tendsto_zero_nhdsGT :
    Tendsto (fun y : ℝ => (Real.log (y⁻¹))⁻¹) (𝓝[>] 0) (𝓝 0) :=
  log_inv_tendsto_atTop_nhdsGT.inv_tendsto_atTop

/-- Algebraic decomposition of Supplementary Eq. (46). -/
theorem reciprocalInverseScaleNoncritical_decomp
    {nu T h0 lambda y : ℝ} (hy : 0 < y) (hlambda : lambda ≠ 1) :
    reciprocalInverseScaleNoncritical nu T h0 lambda y =
      (h0 + 4 * nu * T / (1 - lambda)) * y ^ lambda
        - (4 * nu * T / (1 - lambda)) * y := by
  have hpow :
      y ^ lambda * y ^ (1 - lambda) = y := by
    rw [← Real.rpow_add hy]
    norm_num
  unfold reciprocalInverseScaleNoncritical
  field_simp [sub_ne_zero.mpr hlambda]
  nlinarith [hpow]

/-- Supplementary Eq. (47): for 0<lambda<1 the exact inverse scale is
asymptotic to C y^lambda, where C=h0+4 nu T/(1-lambda). -/
theorem reciprocalInverseScale_subcritical_ratio_tendsto_one
    {nu T h0 lambda : ℝ}
    (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    (hC : h0 + 4 * nu * T / (1 - lambda) ≠ 0) :
    Tendsto
      (fun y =>
        reciprocalInverseScaleNoncritical nu T h0 lambda y /
          ((h0 + 4 * nu * T / (1 - lambda)) * y ^ lambda))
      (𝓝[>] 0) (𝓝 1) := by
  let C : ℝ := h0 + 4 * nu * T / (1 - lambda)
  let D : ℝ := 4 * nu * T / (1 - lambda)
  have hpow := rpow_tendsto_zero_nhdsGT (sub_pos.mpr hlambda1)
  have hlim :
      Tendsto (fun y : ℝ => 1 - (D / C) * y ^ (1 - lambda))
        (𝓝[>] 0) (𝓝 1) := by
    simpa using (hpow.const_mul (D / C)).const_sub 1
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy0 : 0 < y := hy
  have hylam : y ^ lambda ≠ 0 :=
    (Real.rpow_pos_of_pos hy0 lambda).ne'
  have hdecomp :=
    reciprocalInverseScaleNoncritical_decomp
      (nu := nu) (T := T) (h0 := h0) (lambda := lambda)
      hy0 (ne_of_lt hlambda1)
  unfold C D
  rw [hdecomp]
  field_simp [hC, hylam]
  have hpowid :
      y = y ^ lambda * y ^ (1 - lambda) := by
    rw [← Real.rpow_add hy0]
    norm_num
  rw [hpowid]
  ring

/-- Supplementary Eq. (46) reorganized for lambda>1. -/
theorem reciprocalInverseScale_supercritical_decomp
    {nu T h0 lambda y : ℝ} (hy : 0 < y) (hlambda : 1 < lambda) :
    reciprocalInverseScaleNoncritical nu T h0 lambda y =
      (4 * nu * T / (lambda - 1)) * y
        + (h0 - 4 * nu * T / (lambda - 1)) * y ^ lambda := by
  rw [reciprocalInverseScaleNoncritical_decomp
    (nu := nu) (T := T) (h0 := h0) (lambda := lambda)
    hy (ne_of_gt hlambda)]
  have hne : lambda - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlambda)
  field_simp [hne]
  ring

/-- Supplementary Eq. (50), inverse-scale form: for lambda>1,
h is asymptotic to [4 nu T/(lambda-1)] y. -/
theorem reciprocalInverseScale_supercritical_ratio_tendsto_one
    {nu T h0 lambda : ℝ}
    (hlambda : 1 < lambda)
    (hC : 4 * nu * T / (lambda - 1) ≠ 0) :
    Tendsto
      (fun y =>
        reciprocalInverseScaleNoncritical nu T h0 lambda y /
          ((4 * nu * T / (lambda - 1)) * y))
      (𝓝[>] 0) (𝓝 1) := by
  let C : ℝ := 4 * nu * T / (lambda - 1)
  have hpow := rpow_tendsto_zero_nhdsGT (sub_pos.mpr hlambda)
  have hlim :
      Tendsto
        (fun y : ℝ => 1 + ((h0 - C) / C) * y ^ (lambda - 1))
        (𝓝[>] 0) (𝓝 1) := by
    simpa using (hpow.const_mul ((h0 - C) / C)).const_add 1
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy0 : 0 < y := hy
  have hyne : y ≠ 0 := hy0.ne'
  have hdecomp :=
    reciprocalInverseScale_supercritical_decomp
      (nu := nu) (T := T) (h0 := h0) (lambda := lambda)
      hy0 hlambda
  unfold C
  rw [hdecomp]
  have hpowid :
      y ^ lambda = y * y ^ (lambda - 1) := by
    calc
      y ^ lambda = y ^ ((1 : ℝ) + (lambda - 1)) := by congr 1 <;> ring
      _ = y ^ (1 : ℝ) * y ^ (lambda - 1) :=
        Real.rpow_add hy0 1 (lambda - 1)
      _ = y * y ^ (lambda - 1) := by rw [Real.rpow_one]
  rw [hpowid]
  field_simp [hC, hyne]
  ring

/-- Supplementary Eq. (49), inverse-scale form: at lambda=1 the h0 term is
lower order than the logarithmic viscous term. -/
theorem reciprocalInverseScale_critical_ratio_tendsto_one
    {nu T h0 : ℝ} (hK : 4 * nu * T ≠ 0) :
    Tendsto
      (fun y =>
        reciprocalInverseScaleCritical nu T h0 y /
          (4 * nu * T * y * Real.log (y⁻¹)))
      (𝓝[>] 0) (𝓝 1) := by
  have hinvlog := inv_log_inv_tendsto_zero_nhdsGT
  have hlim :
      Tendsto
        (fun y : ℝ => 1 + (h0 / (4 * nu * T)) *
          (Real.log (y⁻¹))⁻¹)
        (𝓝[>] 0) (𝓝 1) := by
    simpa using
      (hinvlog.const_mul (h0 / (4 * nu * T))).const_add 1
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin,
    (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with y hy hy1
  have hy0 : 0 < y := hy
  have hyne : y ≠ 0 := hy0.ne'
  have hloginv : 0 < Real.log (y⁻¹) := by
    rw [Real.log_pos_iff]
    exact (one_lt_inv₀ hy0).2 hy1
  unfold reciprocalInverseScaleCritical
  field_simp [hK, hyne, hloginv.ne']
  ring

/-- Inverting two asymptotically equivalent nonzero inverse scales preserves
their ratio-one asymptotic. -/
theorem inverse_ratio_tendsto_one
    {α : Type*} {l : Filter α} {H R : α → ℝ}
    (hlim : Tendsto (fun x => H x / R x) l (𝓝 1))
    (hH : ∀ᶠ x in l, H x ≠ 0)
    (hR : ∀ᶠ x in l, R x ≠ 0) :
    Tendsto (fun x => H x⁻¹ / R x⁻¹) l (𝓝 1) := by
  have hinv := hlim.inv₀ one_ne_zero
  apply hinv.congr'
  filter_upwards [hH, hR] with x hHx hRx
  field_simp [hHx, hRx]

/-- A ratio tending to one is eventually nonzero in its numerator whenever
the reference denominator is eventually nonzero. -/
theorem eventually_ne_zero_of_ratio_tendsto_one
    {α : Type*} {l : Filter α} {H R : α → ℝ}
    (hlim : Tendsto (fun x => H x / R x) l (𝓝 1))
    (hR : ∀ᶠ x in l, R x ≠ 0) :
    ∀ᶠ x in l, H x ≠ 0 := by
  have hratio :
      ∀ᶠ x in l, 0 < H x / R x :=
    hlim.eventually (Ioi_mem_nhds zero_lt_one)
  filter_upwards [hratio, hR] with x hx hRx
  intro hHx
  rw [hHx] at hx
  simp [hRx] at hx

/-- Supplementary Eq. (47) in beta form. -/
theorem beta_subcritical_ratio_tendsto_one
    {nu T h0 lambda : ℝ}
    (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    (hC : h0 + 4 * nu * T / (1 - lambda) ≠ 0) :
    Tendsto
      (fun y =>
        betaFromInverseScale
            (reciprocalInverseScaleNoncritical nu T h0 lambda y) /
          betaFromInverseScale
            ((h0 + 4 * nu * T / (1 - lambda)) * y ^ lambda))
      (𝓝[>] 0) (𝓝 1) := by
  have hlim :=
    reciprocalInverseScale_subcritical_ratio_tendsto_one
      (nu := nu) (T := T) (h0 := h0)
      hlambda0 hlambda1 hC
  have hR :
      ∀ᶠ y in 𝓝[>] (0 : ℝ),
        (h0 + 4 * nu * T / (1 - lambda)) * y ^ lambda ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact mul_ne_zero hC (Real.rpow_pos_of_pos hy lambda).ne'
  have hH := eventually_ne_zero_of_ratio_tendsto_one hlim hR
  simpa [betaFromInverseScale] using
    (inverse_ratio_tendsto_one hlim hH hR)

/-- Supplementary Eq. (50) in beta form. -/
theorem beta_supercritical_ratio_tendsto_one
    {nu T h0 lambda : ℝ}
    (hlambda : 1 < lambda)
    (hC : 4 * nu * T / (lambda - 1) ≠ 0) :
    Tendsto
      (fun y =>
        betaFromInverseScale
            (reciprocalInverseScaleNoncritical nu T h0 lambda y) /
          betaFromInverseScale
            ((4 * nu * T / (lambda - 1)) * y))
      (𝓝[>] 0) (𝓝 1) := by
  have hlim :=
    reciprocalInverseScale_supercritical_ratio_tendsto_one
      (nu := nu) (T := T) (h0 := h0) hlambda hC
  have hR :
      ∀ᶠ y in 𝓝[>] (0 : ℝ),
        (4 * nu * T / (lambda - 1)) * y ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact mul_ne_zero hC hy.ne'
  have hH := eventually_ne_zero_of_ratio_tendsto_one hlim hR
  simpa [betaFromInverseScale] using
    (inverse_ratio_tendsto_one hlim hH hR)

/-- Supplementary Eq. (49) in beta form. -/
theorem beta_critical_ratio_tendsto_one
    {nu T h0 : ℝ} (hK : 4 * nu * T ≠ 0) :
    Tendsto
      (fun y =>
        betaFromInverseScale (reciprocalInverseScaleCritical nu T h0 y) /
          betaFromInverseScale
            (4 * nu * T * y * Real.log (y⁻¹)))
      (𝓝[>] 0) (𝓝 1) := by
  have hlim :=
    reciprocalInverseScale_critical_ratio_tendsto_one
      (nu := nu) (T := T) (h0 := h0) hK
  have hR :
      ∀ᶠ y in 𝓝[>] (0 : ℝ),
        4 * nu * T * y * Real.log (y⁻¹) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin,
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with y hy hy1
    have hlog : 0 < Real.log (y⁻¹) := by
      rw [Real.log_pos_iff]
      exact (one_lt_inv₀ hy).2 hy1
    exact mul_ne_zero (mul_ne_zero hK hy.ne') hlog.ne'
  have hH := eventually_ne_zero_of_ratio_tendsto_one hlim hR
  simpa [betaFromInverseScale] using
    (inverse_ratio_tendsto_one hlim hH hR)

end

end KiknadzeKrasnov
