import KiknadzeKrasnov.FieldResiduals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace KiknadzeKrasnov

noncomputable section

open Set MeasureTheory intervalIntegral

/-- Swirl contribution to the radial pressure gradient, `u_theta^2/r`. -/
def swirlPressureIntegrand (uTheta : ℝ → ℝ) (r : ℝ) : ℝ :=
  uTheta r ^ 2 / r

/-- The manuscript's swirl-induced pressure potential with a collision-free reference radius name. -/
def swirlPressureIntegral (uTheta : ℝ → ℝ) (rRef r : ℝ) : ℝ :=
  ∫ xi in rRef..r, swirlPressureIntegrand uTheta xi

/-- Fundamental-theorem verification of the swirl pressure integral at a regular endpoint. -/
theorem swirlPressureIntegral_hasDerivAt
    {uTheta : ℝ → ℝ} {rRef r : ℝ}
    (hint : IntervalIntegrable (swirlPressureIntegrand uTheta) volume rRef r)
    (hmeas : StronglyMeasurableAtFilter (swirlPressureIntegrand uTheta) (nhds r) volume)
    (hcont : ContinuousAt (swirlPressureIntegrand uTheta) r) :
    HasDerivAt (swirlPressureIntegral uTheta rRef)
      (swirlPressureIntegrand uTheta r) r := by
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcont

/-- Fixed-time KK pressure field from the manuscript. -/
def pressureField
    (rho p0 a aDot q b bDot z rRef r : ℝ) (uTheta : ℝ → ℝ) : ℝ :=
  p0 + rho * (aDot / 4 - a ^ 2 / 8) * r ^ 2 -
    rho * q ^ 2 / (2 * r ^ 2) -
    rho / 2 * (aDot + a ^ 2) * z ^ 2 -
    rho * (bDot + a * b) * z +
    rho * swirlPressureIntegral uTheta rRef r

/-- The exact pressure field differentiates to the radial pressure-gradient relation. -/
theorem pressureField_hasDerivAt_r
    {rho p0 a aDot q b bDot z rRef r : ℝ} {uTheta : ℝ → ℝ}
    (hr : r ≠ 0)
    (hPi : HasDerivAt (swirlPressureIntegral uTheta rRef)
      (swirlPressureIntegrand uTheta r) r) :
    HasDerivAt (fun y => pressureField rho p0 a aDot q b bDot z rRef y uTheta)
      (rho * radialPressureGradientOverRho a aDot q (uTheta r) r) r := by
  have hr2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * r) r := by
    convert (hasDerivAt_id r).pow 2 using 1
    · funext y
      simp
    · simp
  have hquad := hr2.const_mul (rho * (aDot / 4 - a ^ 2 / 8))
  have hinv := hr2.inv (pow_ne_zero 2 hr)
  have hinvTerm := hinv.const_mul (-(rho * q ^ 2 / 2))
  have hPiScaled := hPi.const_mul rho
  have hconst : HasDerivAt
      (fun _ : ℝ => p0 - rho / 2 * (aDot + a ^ 2) * z ^ 2 -
        rho * (bDot + a * b) * z) 0 r :=
    hasDerivAt_const r _
  have hsum := (hconst.add hquad).add hinvTerm |>.add hPiScaled
  unfold pressureField radialPressureGradientOverRho swirlPressureIntegrand at *
  convert hsum using 1
  · funext y
    simp [div_eq_mul_inv, inv_pow]
    ring
  · field_simp [hr]
    ring

/-- The exact pressure field differentiates to the axial pressure-gradient relation. -/
theorem pressureField_hasDerivAt_z
    {rho p0 a aDot q b bDot z rRef r : ℝ} (uTheta : ℝ → ℝ) :
    HasDerivAt (fun y => pressureField rho p0 a aDot q b bDot y rRef r uTheta)
      (rho * axialPressureGradientOverRho a aDot b bDot z) z := by
  have hz2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by
    convert (hasDerivAt_id z).pow 2 using 1
    · funext y
      simp
    · simp
  have hquad := hz2.const_mul (-(rho / 2 * (aDot + a ^ 2)))
  have hlin := (hasDerivAt_const_mul (x := z) (-(rho * (bDot + a * b))))
  have hconst : HasDerivAt
      (fun _ : ℝ => p0 + rho * (aDot / 4 - a ^ 2 / 8) * r ^ 2 -
        rho * q ^ 2 / (2 * r ^ 2) + rho * swirlPressureIntegral uTheta rRef r) 0 z :=
    hasDerivAt_const z _
  have hsum := (hconst.add hquad).add hlin
  unfold pressureField axialPressureGradientOverRho
  convert hsum using 1
  · funext y
    simp [div_eq_mul_inv, inv_pow]
    ring
  · ring

end

end KiknadzeKrasnov
