import KiknadzeKrasnov.Kinematics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace KiknadzeKrasnov

noncomputable section

open Set MeasureTheory intervalIntegral

/-- Pointwise residual for the nonlinear radial-scale equation, manuscript Eq. (32). -/
def scaleResidual (nu a beta betaDot : ℝ) : ℝ :=
  betaDot - a * beta + 4 * nu * beta ^ 2

/-- Pointwise residual for the linear inverse-scale equation, manuscript Eq. (45). -/
def inverseScaleResidual (nu a h hDot : ℝ) : ℝ :=
  hDot + a * h - 4 * nu

/-- The reciprocal scale derivative. -/
theorem inverseScale_hasDerivAt {beta : ℝ → ℝ} {betaDot t : ℝ}
    (hbeta : HasDerivAt beta betaDot t) (hne : beta t ≠ 0) :
    HasDerivAt (fun tau => (beta tau)⁻¹) (-betaDot / (beta t) ^ 2) t := by
  exact hbeta.inv hne

/-- Eq. (32) implies Eq. (45) under the reciprocal change of variables. -/
theorem scaleResidual_zero_imp_inverseScaleResidual_zero
    {nu a beta betaDot : ℝ} (hbeta : beta ≠ 0)
    (hscale : scaleResidual nu a beta betaDot = 0) :
    inverseScaleResidual nu a beta⁻¹ (-betaDot / beta ^ 2) = 0 := by
  unfold scaleResidual at hscale
  unfold inverseScaleResidual
  field_simp [hbeta] at *
  nlinarith

/-- Conversely, Eq. (45) recovers Eq. (32) when the scale is nonzero. -/
theorem inverseScaleResidual_zero_imp_scaleResidual_zero
    {nu a beta betaDot : ℝ} (hbeta : beta ≠ 0)
    (hinv : inverseScaleResidual nu a beta⁻¹ (-betaDot / beta ^ 2) = 0) :
    scaleResidual nu a beta betaDot = 0 := by
  unfold inverseScaleResidual at hinv
  unfold scaleResidual
  field_simp [hbeta] at *
  nlinarith

/-- The exponential integral appearing in the exact inverse-scale solution. -/
def expStrainIntegral (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ tau in 0..t, Real.exp (strainAccum a tau)

/-- Manuscript Eq. (47), written as an explicit function. -/
def inverseScaleExact (nu beta0 : ℝ) (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-strainAccum a t) *
    (beta0⁻¹ + 4 * nu * expStrainIntegral a t)

/-- Manuscript Eq. (48), written as an explicit function. -/
def betaExact (nu beta0 : ℝ) (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (strainAccum a t) /
    (beta0⁻¹ + 4 * nu * expStrainIntegral a t)

/-- Eqs. (47)-(48) are reciprocal representations whenever their denominator is nonzero. -/
theorem betaExact_inv_eq_inverseScaleExact
    {nu beta0 : ℝ} {a : ℝ → ℝ} {t : ℝ}
    (hden : beta0⁻¹ + 4 * nu * expStrainIntegral a t ≠ 0) :
    (betaExact nu beta0 a t)⁻¹ = inverseScaleExact nu beta0 a t := by
  unfold betaExact inverseScaleExact
  rw [inv_div]
  rw [Real.exp_neg]
  field_simp [hden, Real.exp_ne_zero]
  ring

/-- Eq. (49): the common forcing cancels from the difference of inverse scales. -/
theorem inverseScaleExact_sub
    (nu beta0i beta0j : ℝ) (a : ℝ → ℝ) (t : ℝ) :
    inverseScaleExact nu beta0i a t - inverseScaleExact nu beta0j a t =
      Real.exp (-strainAccum a t) * (beta0i⁻¹ - beta0j⁻¹) := by
  unfold inverseScaleExact
  ring

/-- Ordering of inverse scales is preserved by the exact separation identity. -/
theorem inverseScaleExact_order_preserved
    {nu beta0i beta0j : ℝ} {a : ℝ → ℝ} {t : ℝ}
    (hij : beta0i⁻¹ ≤ beta0j⁻¹) :
    inverseScaleExact nu beta0i a t ≤ inverseScaleExact nu beta0j a t := by
  rw [← sub_nonpos]
  rw [inverseScaleExact_sub]
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr hij)

/-- Fundamental theorem for the accumulated strain when the imposed history is continuous. -/
theorem strainAccum_hasDerivAt {a : ℝ → ℝ} (ha : Continuous a) (t : ℝ) :
    HasDerivAt (strainAccum a) (a t) t := by
  unfold strainAccum
  have hint : IntervalIntegrable a volume 0 t := ha.intervalIntegrable _ _
  have hmeas : StronglyMeasurableAtFilter a (𝓝 t) volume :=
    ha.stronglyMeasurableAtFilter volume (𝓝 t)
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas ha.continuousAt

/-- The exponential forcing integral in Eq. (47) has the expected endpoint derivative. -/
theorem expStrainIntegral_hasDerivAt {a : ℝ → ℝ} (ha : Continuous a) (t : ℝ) :
    HasDerivAt (expStrainIntegral a) (Real.exp (strainAccum a t)) t := by
  have hAcont : Continuous (strainAccum a) := by
    rw [continuous_iff_continuousAt]
    intro y
    exact (strainAccum_hasDerivAt ha y).continuousAt
  have hcont : Continuous (fun y => Real.exp (strainAccum a y)) :=
    Real.continuous_exp.comp hAcont
  unfold expStrainIntegral
  have hint : IntervalIntegrable (fun y => Real.exp (strainAccum a y)) volume 0 t :=
    hcont.intervalIntegrable _ _
  have hmeas : StronglyMeasurableAtFilter
      (fun y => Real.exp (strainAccum a y)) (𝓝 t) volume :=
    hcont.stronglyMeasurableAtFilter volume (𝓝 t)
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcont.continuousAt

/-- Eq. (47) is not merely an algebraic expression: it solves the linear inverse-scale ODE. -/
theorem inverseScaleExact_hasDerivAt
    {nu beta0 : ℝ} {a : ℝ → ℝ} (ha : Continuous a) (t : ℝ) :
    HasDerivAt (inverseScaleExact nu beta0 a)
      (4 * nu - a t * inverseScaleExact nu beta0 a t) t := by
  have hA := strainAccum_hasDerivAt ha t
  have hleft : HasDerivAt
      (fun y => Real.exp (-strainAccum a y))
      (Real.exp (-strainAccum a t) * (-a t)) t := by
    convert hA.neg.exp using 1 <;> ring
  have hJ := expStrainIntegral_hasDerivAt ha t
  have hright : HasDerivAt
      (fun y => beta0⁻¹ + 4 * nu * expStrainIntegral a y)
      (4 * nu * Real.exp (strainAccum a t)) t := by
    convert (hJ.const_mul (4 * nu)).const_add beta0⁻¹ using 1 <;> ring
  have hprod := hleft.mul hright
  convert hprod using 1
  · ext y
    rfl
  · unfold inverseScaleExact
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero]
    ring

/-- Eq. (48) differentiates to the nonlinear scale equation whenever its denominator is nonzero. -/
theorem betaExact_hasDerivAt
    {nu beta0 : ℝ} {a : ℝ → ℝ} (ha : Continuous a) {t : ℝ}
    (hden : beta0⁻¹ + 4 * nu * expStrainIntegral a t ≠ 0) :
    HasDerivAt (betaExact nu beta0 a)
      (a t * betaExact nu beta0 a t -
        4 * nu * (betaExact nu beta0 a t) ^ 2) t := by
  have hA := strainAccum_hasDerivAt ha t
  have hnum : HasDerivAt
      (fun y => Real.exp (strainAccum a y))
      (Real.exp (strainAccum a t) * a t) t :=
    hA.exp
  have hJ := expStrainIntegral_hasDerivAt ha t
  have hdenDeriv : HasDerivAt
      (fun y => beta0⁻¹ + 4 * nu * expStrainIntegral a y)
      (4 * nu * Real.exp (strainAccum a t)) t := by
    convert (hJ.const_mul (4 * nu)).const_add beta0⁻¹ using 1 <;> ring
  have hquot := hnum.div hdenDeriv hden
  convert hquot using 1
  · ext y
    rfl
  · unfold betaExact
    field_simp [hden]
    ring

/-- The explicit scale formula has zero Eq. (32) residual. -/
theorem betaExact_scaleResidual_zero
    {nu beta0 : ℝ} {a : ℝ → ℝ} (ha : Continuous a) {t : ℝ}
    (hden : beta0⁻¹ + 4 * nu * expStrainIntegral a t ≠ 0) :
    scaleResidual nu (a t) (betaExact nu beta0 a t)
      (a t * betaExact nu beta0 a t -
        4 * nu * (betaExact nu beta0 a t) ^ 2) = 0 := by
  unfold scaleResidual
  ring

/-- The exact inverse-scale formula has zero Eq. (45) residual. -/
theorem inverseScaleExact_residual_zero
    {nu beta0 : ℝ} {a : ℝ → ℝ} (ha : Continuous a) (t : ℝ) :
    inverseScaleResidual nu (a t) (inverseScaleExact nu beta0 a t)
      (4 * nu - a t * inverseScaleExact nu beta0 a t) = 0 := by
  unfold inverseScaleResidual
  ring

/-- Initial value encoded by Eq. (47). -/
@[simp] theorem inverseScaleExact_zero (nu beta0 : ℝ) (a : ℝ → ℝ) :
    inverseScaleExact nu beta0 a 0 = beta0⁻¹ := by
  simp [inverseScaleExact, expStrainIntegral, strainAccum]

/-- Initial value encoded by Eq. (48). -/
@[simp] theorem betaExact_zero {nu beta0 : ℝ} (a : ℝ → ℝ) (hbeta0 : beta0 ≠ 0) :
    betaExact nu beta0 a 0 = beta0 := by
  simp [betaExact, expStrainIntegral, strainAccum, hbeta0]

end

end KiknadzeKrasnov
