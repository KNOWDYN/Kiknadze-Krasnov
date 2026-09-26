import KiknadzeKrasnov.AngularMomentum
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace KiknadzeKrasnov

noncomputable section

open Set MeasureTheory intervalIntegral

/-- Closed time derivative of the radial KK velocity, manuscript Eq. (51). -/
def radialVelocityTimeDeriv (aDot r : ℝ) : ℝ := -(aDot / 2) * r

/-- Closed radial derivative of the radial KK velocity, manuscript Eq. (51). -/
def radialVelocityRadialDeriv (a q r : ℝ) : ℝ := -(a / 2) - q / r ^ 2

/-- Closed second radial derivative of the radial KK velocity. -/
def radialVelocityRadialSecond (q r : ℝ) : ℝ := 2 * q / r ^ 3

/-- Equation (52): cross terms proportional to a*q/r cancel. -/
theorem radial_convective_acceleration
    {a q r : ℝ} (hr : r ≠ 0) :
    radialVelocity a q r * radialVelocityRadialDeriv a q r =
      a ^ 2 / 4 * r - q ^ 2 / r ^ 3 := by
  unfold radialVelocity radialVelocityRadialDeriv
  field_simp [hr]
  ring

/-- Equation (53): the cylindrical radial viscous operator vanishes identically off-axis. -/
theorem radial_viscous_operator_zero
    {a q r : ℝ} (hr : r ≠ 0) :
    radialVelocityRadialSecond q r +
        radialVelocityRadialDeriv a q r / r -
        radialVelocity a q r / r ^ 2 = 0 := by
  unfold radialVelocityRadialSecond radialVelocityRadialDeriv radialVelocity
  field_simp [hr]
  ring

/-- Equation (55): axial material acceleration for u_z=a z+b. -/
def axialAcceleration (a aDot b bDot z : ℝ) : ℝ :=
  (aDot + a ^ 2) * z + (bDot + a * b)

/-- Equation (54), expressed as the pressure-gradient value required by radial momentum. -/
def pressureRadialGradient
    (rho a aDot q uTheta r : ℝ) : ℝ :=
  rho * ((aDot / 2 - a ^ 2 / 4) * r + q ^ 2 / r ^ 3 + uTheta ^ 2 / r)

/-- Equation (56), expressed as the pressure-gradient value required by axial momentum. -/
def pressureAxialGradient
    (rho a aDot b bDot z : ℝ) : ℝ :=
  -rho * ((aDot + a ^ 2) * z + (bDot + a * b))

/-- Swirl-induced pressure potential of Eq. (58), with the lower limit named rRef. -/
def swirlPressurePotential (uTheta : ℝ → ℝ) (rRef r : ℝ) : ℝ :=
  ∫ xi in rRef..r, uTheta xi ^ 2 / xi

/-- Fundamental-theorem certification of the swirl pressure derivative. -/
theorem swirlPressurePotential_hasDerivAt
    {uTheta : ℝ → ℝ} {rRef r : ℝ}
    (hint : IntervalIntegrable (fun xi => uTheta xi ^ 2 / xi) volume rRef r)
    (hmeas : StronglyMeasurableAtFilter (fun xi => uTheta xi ^ 2 / xi) (𝓝 r) volume)
    (hcont : ContinuousAt (fun xi => uTheta xi ^ 2 / xi) r) :
    HasDerivAt (swirlPressurePotential uTheta rRef) (uTheta r ^ 2 / r) r := by
  unfold swirlPressurePotential
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcont

/-- Radial part of the exact pressure field, Eq. (57). -/
def radialPressurePart
    (rho a aDot q : ℝ) (Pi : ℝ → ℝ) (r : ℝ) : ℝ :=
  rho * (aDot / 4 - a ^ 2 / 8) * r ^ 2 -
    (rho * q ^ 2 / 2) * (r ^ 2)⁻¹ +
    rho * Pi r

/-- The radial pressure field differentiates to Eq. (54). -/
theorem radialPressurePart_hasDerivAt
    {rho a aDot q uTheta r : ℝ} {Pi : ℝ → ℝ}
    (hr : r ≠ 0) (hPi : HasDerivAt Pi (uTheta ^ 2 / r) r) :
    HasDerivAt (radialPressurePart rho a aDot q Pi)
      (pressureRadialGradient rho a aDot q uTheta r) r := by
  have hquad :=
    ((hasDerivAt_id r).pow 2).const_mul (rho * (aDot / 4 - a ^ 2 / 8))
  have hinv :=
    (((hasDerivAt_id r).pow 2).inv (pow_ne_zero 2 hr)).const_mul (-(rho * q ^ 2 / 2))
  have hswirl := hPi.const_mul rho
  have hsum := (hquad.add hinv).add hswirl
  convert hsum using 1
  · ext y
    simp [radialPressurePart, div_eq_mul_inv]
    ring
  · unfold pressureRadialGradient
    field_simp [hr]
    ring

/-- Axial part of the exact pressure field, Eq. (57). -/
def axialPressurePart
    (rho a aDot b bDot z : ℝ) : ℝ :=
  -(rho / 2) * (aDot + a ^ 2) * z ^ 2 -
    rho * (bDot + a * b) * z

/-- The axial pressure field differentiates to Eq. (56). -/
theorem axialPressurePart_hasDerivAt
    (rho a aDot b bDot z : ℝ) :
    HasDerivAt (axialPressurePart rho a aDot b bDot)
      (pressureAxialGradient rho a aDot b bDot z) z := by
  unfold axialPressurePart pressureAxialGradient
  convert
    ((((hasDerivAt_id z).pow 2).const_mul (-(rho / 2) * (aDot + a ^ 2))).add
      ((hasDerivAt_id z).const_mul (-(rho * (bDot + a * b))))) using 1 <;> ring

/-- Exact pressure field up to an arbitrary time-dependent reference p0(t), Eq. (57). -/
def pressureField
    (rho p0 a aDot q b bDot : ℝ) (Pi : ℝ → ℝ) (r z : ℝ) : ℝ :=
  p0 + radialPressurePart rho a aDot q Pi r +
    axialPressurePart rho a aDot b bDot z

/-- Radial derivative of the complete pressure field. -/
theorem pressureField_hasDerivAt_radius
    {rho p0 a aDot q b bDot uTheta r z : ℝ} {Pi : ℝ → ℝ}
    (hr : r ≠ 0) (hPi : HasDerivAt Pi (uTheta ^ 2 / r) r) :
    HasDerivAt (fun y => pressureField rho p0 a aDot q b bDot Pi y z)
      (pressureRadialGradient rho a aDot q uTheta r) r := by
  have hrpart := radialPressurePart_hasDerivAt (rho := rho) (a := a) (aDot := aDot)
    (q := q) (uTheta := uTheta) (r := r) (Pi := Pi) hr hPi
  convert (hrpart.const_add p0).add_const (axialPressurePart rho a aDot b bDot z) using 1 <;>
    ring

/-- Axial derivative of the complete pressure field. -/
theorem pressureField_hasDerivAt_axial
    (rho p0 a aDot q b bDot r z : ℝ) (Pi : ℝ → ℝ) :
    HasDerivAt (fun y => pressureField rho p0 a aDot q b bDot Pi r y)
      (pressureAxialGradient rho a aDot b bDot z) z := by
  have hzpart := axialPressurePart_hasDerivAt rho a aDot b bDot z
  convert hzpart.const_add (p0 + radialPressurePart rho a aDot q Pi r) using 1 <;> ring

/-- Pointwise identity behind the W-form of Eq. (58). -/
theorem swirl_pressure_integrand_circulation_form
    {uTheta W r : ℝ} (hr : r ≠ 0)
    (hW : W = 2 * Real.pi * r * uTheta) :
    uTheta ^ 2 / r = W ^ 2 / (4 * Real.pi ^ 2 * r ^ 3) := by
  rw [hW]
  field_simp [hr, Real.pi_ne_zero]
  ring

end

end KiknadzeKrasnov
