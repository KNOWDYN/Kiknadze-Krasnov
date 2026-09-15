import KiknadzeKrasnov.MultimodeQualification
import Mathlib.Analysis.SpecialFunctions.Exp

namespace KiknadzeKrasnov

noncomputable section

open Filter
open scoped Topology

/-- Constant positive-strain equilibrium scale `a0/(4 nu)`. -/
def burgersScale (nu a0 : ℝ) : ℝ := a0 / (4 * nu)

/-- Instantaneous algebraic stagnation squared radius `2q/a`; existence of a
positive physical radius is stated separately. -/
def stagnationRadiusSq (q a : ℝ) : ℝ := 2 * q / a

/-- M140 dimensionless source/strain balance ratio. -/
def balanceRatio (nu a beta : ℝ) : ℝ := a / (4 * nu * beta)

/-- M124/M135--M137: at the constant-strain equilibrium scale, the distinguished
material/vorticity radius squared equals the source--strain stagnation radius squared. -/
theorem steady_materialRadiusSq_eq_stagnation
    {nu q s a0 : ℝ} (hnu : nu ≠ 0) (ha0 : a0 ≠ 0)
    (hcompat : q = 2 * nu * (s - 1)) :
    materialRadiusSq s (burgersScale nu a0) = stagnationRadiusSq q a0 := by
  unfold materialRadiusSq burgersScale stagnationRadiusSq
  rw [hcompat]
  field_simp [hnu, ha0]
  ring

/-- C022: on the source-bearing steady branch, the corresponding stagnation
squared radius is positive. -/
theorem stagnationRadiusSq_pos
    {q a0 : ℝ} (hq : 0 < q) (ha0 : 0 < a0) :
    0 < stagnationRadiusSq q a0 := by
  unfold stagnationRadiusSq
  positivity

/-- M138: the physical material/vorticity radius equals the positive square-root
stagnation radius at steady balance. -/
theorem steady_materialRadius_eq_stagnationRadius
    {nu q s a0 : ℝ} (hnu : nu ≠ 0) (ha0 : a0 ≠ 0)
    (hcompat : q = 2 * nu * (s - 1)) :
    materialRadius s (burgersScale nu a0) =
      Real.sqrt (stagnationRadiusSq q a0) := by
  unfold materialRadius
  rw [steady_materialRadiusSq_eq_stagnation hnu ha0 hcompat]

/-- M140: the ratio of the vorticity/material squared radius to the instantaneous
stagnation squared radius is exactly `a/(4 nu beta)` whenever both ratios are defined. -/
theorem material_stagnation_balance_ratio
    {nu q s a beta : ℝ}
    (hnu : nu ≠ 0) (ha : a ≠ 0) (hbeta : beta ≠ 0)
    (hs : s ≠ 1) (hcompat : q = 2 * nu * (s - 1)) :
    materialRadiusSq s beta / stagnationRadiusSq q a =
      balanceRatio nu a beta := by
  unfold materialRadiusSq stagnationRadiusSq balanceRatio
  rw [hcompat]
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp [hnu, ha, hbeta, hs1]
  ring

/-- M125 exact zero-strain spreading scale. -/
def zeroStrainScale (nu beta0 t : ℝ) : ℝ :=
  (beta0⁻¹ + 4 * nu * t)⁻¹

@[simp] theorem zeroStrainScale_zero
    {nu beta0 : ℝ} :
    zeroStrainScale nu beta0 0 = beta0 := by
  simp [zeroStrainScale]

/-- The M125 closed form satisfies the zero-strain Riccati scale equation wherever
its denominator is nonzero. -/
theorem zeroStrainScale_hasDerivAt
    {nu beta0 t : ℝ}
    (hden : beta0⁻¹ + 4 * nu * t ≠ 0) :
    HasDerivAt (zeroStrainScale nu beta0)
      (-4 * nu * (zeroStrainScale nu beta0 t) ^ 2) t := by
  have hlin : HasDerivAt (fun tau : ℝ => beta0⁻¹ + (4 * nu) * tau) (4 * nu) t := by
    have h := (hasDerivAt_const t beta0⁻¹).add
      ((hasDerivAt_id t).const_mul (4 * nu))
    convert h using 1
    · funext tau
      simp
    · ring
  have hinv := hlin.inv hden
  convert hinv using 1
  · funext tau
    rfl
  · unfold zeroStrainScale
    field_simp [hden]
    ring

/-- The exact zero-strain scale therefore has vanishing scale residual. -/
theorem zeroStrainScale_residual_zero
    {nu beta0 t : ℝ} :
    scaleResidual nu 0 (zeroStrainScale nu beta0 t)
      (-4 * nu * (zeroStrainScale nu beta0 t) ^ 2) = 0 := by
  unfold scaleResidual
  ring

/-- M128 exact inverse-scale history under constant strain. -/
def constantStrainInverseScale (nu a0 h0 t : ℝ) : ℝ :=
  4 * nu / a0 + (h0 - 4 * nu / a0) * Real.exp (-a0 * t)

/-- Scale corresponding to the exact M128 inverse-scale history. -/
def constantStrainScale (nu a0 h0 t : ℝ) : ℝ :=
  (constantStrainInverseScale nu a0 h0 t)⁻¹

@[simp] theorem constantStrainInverseScale_zero
    {nu a0 h0 : ℝ} (ha0 : a0 ≠ 0) :
    constantStrainInverseScale nu a0 h0 0 = h0 := by
  simp [constantStrainInverseScale]

/-- M128 is an exact solution of `h' + a0 h = 4 nu` for non-zero constant strain. -/
theorem constantStrainInverseScale_hasDerivAt
    {nu a0 h0 t : ℝ} (ha0 : a0 ≠ 0) :
    HasDerivAt (constantStrainInverseScale nu a0 h0)
      (4 * nu - a0 * constantStrainInverseScale nu a0 h0 t) t := by
  have harg : HasDerivAt (fun tau : ℝ => -a0 * tau) (-a0) t := by
    have h := (hasDerivAt_id t).const_mul (-a0)
    convert h using 1
    · funext tau
      simp
    · ring
  have hexp := harg.exp
  have hmul := hexp.const_mul (h0 - 4 * nu / a0)
  have hadd := hmul.const_add (4 * nu / a0)
  convert hadd using 1
  · funext tau
    simp [constantStrainInverseScale]
  · unfold constantStrainInverseScale
    field_simp [ha0]
    ring

/-- M129: for constant positive strain, inverse scale converges to `4 nu/a0`. -/
theorem constantStrainInverseScale_tendsto
    {nu a0 h0 : ℝ} (ha0 : 0 < a0) :
    Tendsto (constantStrainInverseScale nu a0 h0) atTop
      (𝓝 (4 * nu / a0)) := by
  have hexp : Tendsto (fun t : ℝ => Real.exp (-a0 * t)) atTop (𝓝 0) := by
    exact Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr ha0))
  have hmul := hexp.const_mul (h0 - 4 * nu / a0)
  have hadd := hmul.const_add (4 * nu / a0)
  convert hadd using 1
  · funext t
    simp [constantStrainInverseScale]
  · simp

/-- M129: the positive constant-strain scale converges to the Burgers equilibrium. -/
theorem constantStrainScale_tendsto
    {nu a0 h0 : ℝ} (hnu : nu ≠ 0) (ha0 : 0 < a0) :
    Tendsto (constantStrainScale nu a0 h0) atTop
      (𝓝 (burgersScale nu a0)) := by
  have hh := constantStrainInverseScale_tendsto (nu := nu) (a0 := a0) (h0 := h0) ha0
  have hlim : 4 * nu / a0 ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) hnu) ha0.ne'
  have hinv := Tendsto.inv₀ hh hlim
  unfold constantStrainScale burgersScale
  convert hinv using 1
  field_simp [hnu, ha0.ne']

/-- M141: every member of a finite family with arbitrary positive initial inverse
scale converges to the same equilibrium under sustained constant positive strain. -/
theorem finiteModes_constantStrainScale_tendsto {n : ℕ}
    {nu a0 : ℝ} (hnu : nu ≠ 0) (ha0 : 0 < a0) (h0 : Fin n → ℝ) :
    ∀ i, Tendsto (constantStrainScale nu a0 (h0 i)) atTop
      (𝓝 (burgersScale nu a0)) := by
  intro i
  exact constantStrainScale_tendsto hnu ha0

end

end KiknadzeKrasnov
