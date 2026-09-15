import KiknadzeKrasnov.ClassicalLimits
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace KiknadzeKrasnov

noncomputable section

open Set MeasureTheory intervalIntegral

/-- On the regular branch `s=1`, the gamma kernel is the simple exponential. -/
theorem gammaKernel_one (x : ℝ) :
    gammaKernel 1 x = Real.exp (-x) := by
  simp [gammaKernel]

/-- C024: the lower incomplete gamma at shape one is `1-exp(-x)` for `x≥0`. -/
theorem lowerGamma_one {x : ℝ} (hx : 0 ≤ x) :
    lowerGamma 1 x = 1 - Real.exp (-x) := by
  unfold lowerGamma
  rw [show (fun ξ : ℝ => gammaKernel 1 ξ) = (fun ξ : ℝ => Real.exp (-ξ)) by
    funext ξ
    exact gammaKernel_one ξ]
  have hderiv : ∀ y ∈ Ioo (0 : ℝ) x,
      HasDerivAt (fun z : ℝ => -Real.exp (-z)) (Real.exp (-y)) y := by
    intro y hy
    have h := ((hasDerivAt_id y).neg.exp).neg
    convert h using 1 <;> ring
  have hint : IntervalIntegrable (fun y : ℝ => Real.exp (-y)) volume 0 x :=
    (by fun_prop : Continuous fun y : ℝ => Real.exp (-y)).intervalIntegrable 0 x
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hx (by fun_prop) hderiv hint
  simpa using h

/-- Regularised lower gamma at shape one. -/
theorem regLowerGamma_one {x : ℝ} (hx : 0 ≤ x) :
    regLowerGamma 1 x = 1 - Real.exp (-x) := by
  rw [regLowerGamma, lowerGamma_one hx]
  simp [gammaFn]

/-- C024: the `s=1` distributed swirl is the regular Gaussian/Oseen profile. -/
theorem distributedSwirl_one
    {circ beta r : ℝ} (hx : 0 ≤ scaledX beta r) :
    distributedSwirl circ 1 beta r =
      circ / (2 * Real.pi * r) *
        (1 - Real.exp (-(scaledX beta r))) := by
  unfold distributedSwirl
  rw [regLowerGamma_one hx]

/-- C024: the `s=1` distributed vorticity is Gaussian. -/
theorem distributedVorticity_one (circ beta r : ℝ) :
    distributedVorticity circ 1 beta r =
      circ * beta / Real.pi * Real.exp (-(scaledX beta r)) := by
  simp [distributedVorticity, vorticityShape, gammaFn]

/-- Effective viscous-age shift `t₀=(4νβ₀)⁻¹` in the Oseen reduction. -/
def oseenAgeShift (nu beta0 : ℝ) : ℝ := (4 * nu * beta0)⁻¹

/-- M125 rewritten in the classical Oseen effective-age form. -/
theorem zeroStrainScale_eq_oseenAge
    {nu beta0 t : ℝ} (hnu : nu ≠ 0) (hbeta0 : beta0 ≠ 0) :
    zeroStrainScale nu beta0 t =
      (4 * nu * (t + oseenAgeShift nu beta0))⁻¹ := by
  unfold zeroStrainScale oseenAgeShift
  congr 1
  field_simp [hnu, hbeta0]
  ring

/-- The Oseen scaled radius is `r²/[4ν(t+t₀)]`. -/
theorem scaledX_zeroStrainScale_eq
    {nu beta0 t r : ℝ} (hnu : nu ≠ 0) (hbeta0 : beta0 ≠ 0) :
    scaledX (zeroStrainScale nu beta0 t) r =
      r ^ 2 / (4 * nu * (t + oseenAgeShift nu beta0)) := by
  rw [zeroStrainScale_eq_oseenAge hnu hbeta0]
  unfold scaledX
  simp only [div_eq_mul_inv]
  ring

/-- C024: exact algebraic Lamb--Oseen swirl formula at effective age `t+t₀`. -/
theorem oseen_swirl_formula
    {circ nu beta0 t r : ℝ}
    (hnu : 0 < nu) (hbeta0 : 0 < beta0) (ht : 0 ≤ t) :
    distributedSwirl circ 1 (zeroStrainScale nu beta0 t) r =
      circ / (2 * Real.pi * r) *
        (1 - Real.exp (-(r ^ 2 /
          (4 * nu * (t + oseenAgeShift nu beta0))))) := by
  have hbeta : 0 < zeroStrainScale nu beta0 t := by
    unfold zeroStrainScale
    positivity
  rw [distributedSwirl_one (mul_nonneg hbeta.le (sq_nonneg r))]
  rw [scaledX_zeroStrainScale_eq hnu.ne' hbeta0.ne']

/-- C024: exact algebraic Lamb--Oseen Gaussian vorticity formula at effective age. -/
theorem oseen_vorticity_formula
    {circ nu beta0 t r : ℝ}
    (hnu : 0 < nu) (hbeta0 : 0 < beta0) (ht : 0 ≤ t) :
    distributedVorticity circ 1 (zeroStrainScale nu beta0 t) r =
      circ / (4 * Real.pi * nu * (t + oseenAgeShift nu beta0)) *
        Real.exp (-(r ^ 2 /
          (4 * nu * (t + oseenAgeShift nu beta0)))) := by
  rw [distributedVorticity_one]
  rw [zeroStrainScale_eq_oseenAge hnu.ne' hbeta0.ne']
  rw [scaledX_zeroStrainScale_eq hnu.ne' hbeta0.ne']
  simp only [div_eq_mul_inv]
  ring

/-- At the constant-strain Burgers scale, the scaled radius is `a₀r²/(4ν)`. -/
theorem scaledX_burgersScale_eq
    {nu a0 r : ℝ} (hnu : nu ≠ 0) :
    scaledX (burgersScale nu a0) r = a0 * r ^ 2 / (4 * nu) := by
  unfold scaledX burgersScale
  field_simp [hnu]
  ring

/-- C025: stationary Burgers swirl under the manuscript's strain convention. -/
theorem burgers_swirl_formula
    {circ nu a0 r : ℝ} (hnu : 0 < nu) (ha0 : 0 ≤ a0) :
    distributedSwirl circ 1 (burgersScale nu a0) r =
      circ / (2 * Real.pi * r) *
        (1 - Real.exp (-(a0 * r ^ 2 / (4 * nu)))) := by
  have hbeta : 0 ≤ burgersScale nu a0 := by
    unfold burgersScale
    positivity
  rw [distributedSwirl_one (mul_nonneg hbeta (sq_nonneg r))]
  rw [scaledX_burgersScale_eq hnu.ne']

/-- C025: `β=a₀/(4ν)` is exactly stationary in the Riccati scale equation. -/
theorem burgersScale_residual_zero
    {nu a0 : ℝ} (hnu : nu ≠ 0) :
    scaleResidual nu a0 (burgersScale nu a0) 0 = 0 := by
  unfold scaleResidual burgersScale
  field_simp [hnu]
  ring

end

end KiknadzeKrasnov
