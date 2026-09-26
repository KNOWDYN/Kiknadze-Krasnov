import KiknadzeKrasnov.Pressure

namespace KiknadzeKrasnov

noncomputable section

/-- Pointwise continuity residual in the punctured radial domain. -/
def continuityResidual (a r : ℝ) : ℝ :=
  (-a * r) / r + a

/-- Pointwise radial Navier--Stokes residual, with the pressure gradient of Eq. (54). -/
def radialNSResidual
    (rho nu a aDot q uTheta r : ℝ) : ℝ :=
  radialVelocityTimeDeriv aDot r +
    radialVelocity a q r * radialVelocityRadialDeriv a q r -
    uTheta ^ 2 / r +
    pressureRadialGradient rho a aDot q uTheta r / rho -
    nu * (radialVelocityRadialSecond q r +
      radialVelocityRadialDeriv a q r / r -
      radialVelocity a q r / r ^ 2)

/-- Pointwise axial Navier--Stokes residual, all axial viscous terms being zero. -/
def axialNSResidual
    (rho a aDot b bDot z : ℝ) : ℝ :=
  axialAcceleration a aDot b bDot z +
    pressureAxialGradient rho a aDot b bDot z / rho

/-- Equation (71): continuity vanishes pointwise off the axis. -/
theorem continuityResidual_zero {a r : ℝ} (hr : r ≠ 0) :
    continuityResidual a r = 0 := by
  unfold continuityResidual
  exact meridional_continuity_residual hr

/-- Equation (72), radial part: the exact pressure gradient cancels radial inertia and swirl. -/
theorem radialNSResidual_zero
    {rho nu a aDot q uTheta r : ℝ}
    (hrho : rho ≠ 0) (hr : r ≠ 0) :
    radialNSResidual rho nu a aDot q uTheta r = 0 := by
  have hconv := radial_convective_acceleration (a := a) (q := q) hr
  have hvisc := radial_viscous_operator_zero (a := a) (q := q) hr
  unfold radialNSResidual radialVelocityTimeDeriv pressureRadialGradient
  rw [hconv, hvisc]
  field_simp [hrho, hr]
  ring

/-- Equation (72), axial part: the exact axial pressure gradient cancels material acceleration. -/
theorem axialNSResidual_zero
    {rho a aDot b bDot z : ℝ} (hrho : rho ≠ 0) :
    axialNSResidual rho a aDot b bDot z = 0 := by
  unfold axialNSResidual axialAcceleration pressureAxialGradient
  field_simp [hrho]
  ring

/-- The azimuthal equation is zero through its equivalent angular-momentum residual. -/
theorem azimuthalNSResidual_zero
    {nu a q beta betaDot s r : ℝ}
    (hr : r ≠ 0) (hbeta : beta ≠ 0)
    (hs : 0 < s) (hx : 0 < scaledX beta r)
    (hscale : scaleResidual nu a beta betaDot = 0)
    (hq : q = 2 * nu * (s - 1)) :
    angularMomentumResidual nu a q beta betaDot s r = 0 :=
  angularMomentumResidual_zero hr hbeta hs hx hscale hq

/--
Pointwise Pass-3 certificate: continuity and all three momentum balances vanish for the
single distributed KK mode under the paper's compatibility relations.
The azimuthal balance is represented by its exactly equivalent angular-momentum equation.
-/
theorem kk_governing_residuals_zero
    {rho nu a aDot q uTheta beta betaDot s r b bDot z : ℝ}
    (hrho : rho ≠ 0) (hr : r ≠ 0) (hbeta : beta ≠ 0)
    (hs : 0 < s) (hx : 0 < scaledX beta r)
    (hscale : scaleResidual nu a beta betaDot = 0)
    (hq : q = 2 * nu * (s - 1)) :
    continuityResidual a r = 0 ∧
    radialNSResidual rho nu a aDot q uTheta r = 0 ∧
    angularMomentumResidual nu a q beta betaDot s r = 0 ∧
    axialNSResidual rho a aDot b bDot z = 0 := by
  constructor
  · exact continuityResidual_zero hr
  constructor
  · exact radialNSResidual_zero hrho hr
  constructor
  · exact azimuthalNSResidual_zero hr hbeta hs hx hscale hq
  · exact axialNSResidual_zero hrho

end

end KiknadzeKrasnov
