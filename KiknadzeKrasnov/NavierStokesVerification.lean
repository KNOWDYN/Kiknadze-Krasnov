import KiknadzeKrasnov.Pressure

namespace KiknadzeKrasnov

noncomputable section

/-- Scalar continuity residual for the explicit KK meridional field. -/
def continuityResidual (a : ℝ) : ℝ :=
  radialDivergenceContribution a + axialDivergenceContribution a

/-- Scalar radial momentum residual after substitution of the explicit KK derivatives. -/
def radialMomentumResidual
    (nu a aDot q uTheta r : ℝ) : ℝ :=
  radialVelocityTimeDerivative aDot r
    + radialVelocity a q r * radialVelocityRadialDerivative a q r
    - uTheta ^ 2 / r
    + radialPressureGradientOverRho a aDot q uTheta r
    - nu * (radialVelocitySecondRadialDerivative q r
      + radialVelocityRadialDerivative a q r / r
      - radialVelocity a q r / r ^ 2)

/-- Scalar axial momentum residual after substitution of the explicit KK derivatives. -/
def axialMomentumResidual
    (a aDot b bDot z : ℝ) : ℝ :=
  axialAcceleration a aDot b bDot z
    + axialPressureGradientOverRho a aDot b bDot z

/-- Scalar azimuthal residual in scaled angular-momentum variables. -/
def azimuthalMomentumResidual
    (nu a q beta betaDot x Fp Fpp : ℝ) : ℝ :=
  scaledAngularMomentumResidual nu a q beta betaDot x Fp Fpp

@[simp] theorem continuityResidual_zero (a : ℝ) :
    continuityResidual a = 0 := by
  simp [continuityResidual, meridional_continuity]

theorem radialMomentumResidual_zero
    {nu a aDot q uTheta r : ℝ} (hr : r ≠ 0) :
    radialMomentumResidual nu a aDot q uTheta r = 0 := by
  unfold radialMomentumResidual
  rw [radial_convective_acceleration hr]
  rw [radial_viscous_operator_zero hr]
  unfold radialVelocityTimeDerivative radialPressureGradientOverRho
  field_simp [hr]
  ring

@[simp] theorem axialMomentumResidual_zero
    (a aDot b bDot z : ℝ) :
    axialMomentumResidual a aDot b bDot z = 0 := by
  unfold axialMomentumResidual axialAcceleration axialPressureGradientOverRho
  ring

theorem azimuthalMomentumResidual_zero
    {nu a q beta betaDot x Fp Fpp : ℝ}
    (hbeta : beta ≠ 0)
    (hscale : betaScaleResidual nu a beta betaDot = 0)
    (hprofile : profileResidual nu q x Fp Fpp = 0) :
    azimuthalMomentumResidual nu a q beta betaDot x Fp Fpp = 0 := by
  exact scaledAngularMomentumResidual_eq_zero hbeta hscale hprofile

/-- Complete pointwise scalar residual audit for the KK field.

The radial and axial equations use the pressure gradients dictated by the exact pressure field;
the azimuthal equation is discharged by the scale and fixed-profile compatibility equations.
-/
theorem kk_all_scalar_residuals_zero
    {nu a aDot b bDot q uTheta r z beta betaDot x Fp Fpp : ℝ}
    (hr : r ≠ 0)
    (hbeta : beta ≠ 0)
    (hscale : betaScaleResidual nu a beta betaDot = 0)
    (hprofile : profileResidual nu q x Fp Fpp = 0) :
    continuityResidual a = 0
      ∧ radialMomentumResidual nu a aDot q uTheta r = 0
      ∧ azimuthalMomentumResidual nu a q beta betaDot x Fp Fpp = 0
      ∧ axialMomentumResidual a aDot b bDot z = 0 := by
  constructor
  · exact continuityResidual_zero a
  constructor
  · exact radialMomentumResidual_zero hr
  constructor
  · exact azimuthalMomentumResidual_zero hbeta hscale hprofile
  · exact axialMomentumResidual_zero a aDot b bDot z

end

end KiknadzeKrasnov
