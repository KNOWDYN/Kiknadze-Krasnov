import KiknadzeKrasnov.AngularMomentum

namespace KiknadzeKrasnov

noncomputable section

/-- Named first radial derivative of the KK radial velocity. -/
def radialVelocityRadialDeriv (a q r : ℝ) : ℝ := -a / 2 - q / r ^ 2

/-- Named second radial derivative of the KK radial velocity on the punctured domain. -/
def radialVelocitySecondRadialDeriv (q r : ℝ) : ℝ := 2 * q / r ^ 3

/-- The named first derivative agrees with the actual derivative. -/
theorem deriv_radialVelocity {a q r : ℝ} (hr : r ≠ 0) :
    deriv (radialVelocity a q) r = radialVelocityRadialDeriv a q r := by
  exact (radialVelocity_hasDerivAt (a := a) (q := q) hr).deriv

/-- The explicit first-derivative formula differentiates to the manuscript's second derivative. -/
theorem radialVelocityRadialDeriv_hasDerivAt {a q r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (radialVelocityRadialDeriv a q)
      (radialVelocitySecondRadialDeriv q r) r := by
  unfold radialVelocityRadialDeriv radialVelocitySecondRadialDeriv
  have hden : HasDerivAt (fun y : ℝ => y ^ 2) (2 * r) r := by
    convert (hasDerivAt_id r).pow 2 using 1
    · funext y
      simp
    · simp
  have hquot := (hasDerivAt_const r q).div hden (pow_ne_zero 2 hr)
  convert (hasDerivAt_const r (-a / 2)).sub hquot using 1
  field_simp [hr]
  ring

/-- Time derivative of `u_r` when `q` is frozen, as required by the fixed-profile construction. -/
theorem radialVelocity_time_hasDerivAt
    {a : ℝ → ℝ} {aDot t q r : ℝ} (ha : HasDerivAt a aDot t) :
    HasDerivAt (fun tau => radialVelocity (a tau) q r)
      (-aDot / 2 * r) t := by
  unfold radialVelocity
  have h := (ha.mul_const (-r / 2)).add_const (q / r)
  convert h using 1
  · funext tau
    ring
  · ring

/-- Time derivative of `u_z=a(t)z+b(t)`. -/
theorem axialVelocity_time_hasDerivAt
    {a b : ℝ → ℝ} {aDot bDot t z : ℝ}
    (ha : HasDerivAt a aDot t) (hb : HasDerivAt b bDot t) :
    HasDerivAt (fun tau => axialVelocity (a tau) (b tau) z)
      (aDot * z + bDot) t := by
  unfold axialVelocity
  exact (ha.mul_const z).add hb

/-- The radial viscous operator from the axisymmetric radial momentum equation. -/
def radialViscousOperator (a q r : ℝ) : ℝ :=
  radialVelocitySecondRadialDeriv q r +
    radialVelocityRadialDeriv a q r / r -
    radialVelocity a q r / r ^ 2

/-- The radial viscous operator vanishes identically on the punctured domain. -/
theorem radialViscousOperator_zero {a q r : ℝ} (hr : r ≠ 0) :
    radialViscousOperator a q r = 0 := by
  unfold radialViscousOperator radialVelocitySecondRadialDeriv
    radialVelocityRadialDeriv radialVelocity
  field_simp [hr]
  ring

/-- Non-swirl radial acceleration from the supplementary residual algebra. -/
def radialAccelerationNoSwirl (a aDot q r : ℝ) : ℝ :=
  -aDot / 2 * r + radialVelocity a q r * radialVelocityRadialDeriv a q r

/-- Expanded non-swirl radial acceleration. -/
theorem radialAccelerationNoSwirl_eq {a aDot q r : ℝ} (hr : r ≠ 0) :
    radialAccelerationNoSwirl a aDot q r =
      (-aDot / 2 + a ^ 2 / 4) * r - q ^ 2 / r ^ 3 := by
  unfold radialAccelerationNoSwirl radialVelocity radialVelocityRadialDeriv
  field_simp [hr]
  ring

/-- Pressure-gradient relation from radial momentum, divided by density. -/
def radialPressureGradientOverRho (a aDot q uTheta r : ℝ) : ℝ :=
  (aDot / 2 - a ^ 2 / 4) * r + q ^ 2 / r ^ 3 + uTheta ^ 2 / r

/-- Pressure-gradient relation from axial momentum, divided by density. -/
def axialPressureGradientOverRho (a aDot b bDot z : ℝ) : ℝ :=
  -(aDot + a ^ 2) * z - (bDot + a * b)

/-- Radial Navier--Stokes residual with every term moved to the left. -/
def radialMomentumResidual
    (nu a aDot q r uTheta : ℝ) : ℝ :=
  radialAccelerationNoSwirl a aDot q r - uTheta ^ 2 / r +
    radialPressureGradientOverRho a aDot q uTheta r -
    nu * radialViscousOperator a q r

/-- The radial residual vanishes exactly with the KK pressure gradient. -/
theorem radialMomentumResidual_zero
    {nu a aDot q r uTheta : ℝ} (hr : r ≠ 0) :
    radialMomentumResidual nu a aDot q r uTheta = 0 := by
  unfold radialMomentumResidual radialPressureGradientOverRho
  rw [radialAccelerationNoSwirl_eq hr, radialViscousOperator_zero hr]
  field_simp [hr]
  ring

/-- Axial material acceleration for `u_z=az+b`. -/
def axialAcceleration (a aDot b bDot z : ℝ) : ℝ :=
  aDot * z + bDot + axialVelocity a b z * a

/-- Expanded axial acceleration used in the manuscript. -/
theorem axialAcceleration_eq (a aDot b bDot z : ℝ) :
    axialAcceleration a aDot b bDot z =
      (aDot + a ^ 2) * z + (bDot + a * b) := by
  unfold axialAcceleration axialVelocity
  ring

/-- The axial viscous operator vanishes because the field is affine in `z` and independent of `r`. -/
def axialViscousOperator : ℝ := 0

/-- Axial Navier--Stokes residual with every term moved to the left. -/
def axialMomentumResidual (nu a aDot b bDot z : ℝ) : ℝ :=
  axialAcceleration a aDot b bDot z +
    axialPressureGradientOverRho a aDot b bDot z - nu * axialViscousOperator

/-- The axial residual vanishes exactly with the KK pressure gradient. -/
theorem axialMomentumResidual_zero (nu a aDot b bDot z : ℝ) :
    axialMomentumResidual nu a aDot b bDot z = 0 := by
  unfold axialMomentumResidual axialPressureGradientOverRho axialViscousOperator
  rw [axialAcceleration_eq]
  ring

end

end KiknadzeKrasnov
