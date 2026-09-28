import KiknadzeKrasnov.HeatTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace KiknadzeKrasnov

noncomputable section

open Filter Set
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
  apply inverse_ratio_tendsto_one
    (reciprocalInverseScale_subcritical_ratio_tendsto_one
      hlambda0 hlambda1 hC)
  · filter_upwards [self_mem_nhdsWithin,
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with y hy hy1
    have hratio :=
      reciprocalInverseScale_subcritical_ratio_tendsto_one
        (nu := nu) (T := T) (h0 := h0)
        hlambda0 hlambda1 hC
    have hR : (h0 + 4 * nu * T / (1 - lambda)) * y ^ lambda ≠ 0 :=
      mul_ne_zero hC (Real.rpow_pos_of_pos hy lambda).ne'
    by_contra hH
    have : reciprocalInverseScaleNoncritical nu T h0 lambda y /
        ((h0 + 4 * nu * T / (1 - lambda)) * y ^ lambda) = 0 := by
      simp [hH, hR]
    have hdecomp := reciprocalInverseScaleNoncritical_decomp
      (nu := nu) (T := T) (h0 := h0) (lambda := lambda)
      hy (ne_of_lt hlambda1)
    rw [hdecomp] at hH
    exact hH (by
      have hpowpos := Real.rpow_pos_of_pos hy lambda
      -- Exact nonvanishing is only needed eventually; use the ratio limit below.
      nlinarith)
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact mul_ne_zero hC (Real.rpow_pos_of_pos hy lambda).ne'

end

end KiknadzeKrasnov
