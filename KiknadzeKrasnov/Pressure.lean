import KiknadzeKrasnov.ScaleDynamics

namespace KiknadzeKrasnov

noncomputable section

open MeasureTheory intervalIntegral

/-- Pointwise time derivative of the KK radial velocity for q constant. -/
def radialVelocityTimeDerivative (aDot r : ℝ) : ℝ := -(aDot / 2) * r

/-- Pointwise radial derivative of the KK radial velocity. -/
def radialVelocityRadialDerivative (a q r : ℝ) : ℝ := -a / 2 - q / r ^ 2

/-- Pointwise second radial derivative of the KK radial velocity. -/
def radialVelocitySecondRadialDerivative (q r : ℝ) : ℝ := 2 * q / r ^ 3

/-- The radial convective acceleration has no aq/r cross term. -/
theorem radial_convective_acceleration
    {a q r : ℝ} (hr : r ≠ 0) :
    radialVelocity a q r * radialVelocityRadialDerivative a q r
      = a ^ 2 / 4 * r - q ^ 2 / r ^ 3 := by
  unfold radialVelocity radialVelocityRadialDerivative
  field_simp [hr]
  ring

/-- The radial vector-Laplacian contribution vanishes identically on the punctured domain. -/
theorem radial_viscous_operator_zero
    {a q r : ℝ} (hr : r ≠ 0) :
    radialVelocitySecondRadialDerivative q r
      + radialVelocityRadialDerivative a q r / r
      - radialVelocity a q r / r ^ 2 = 0 := by
  unfold radialVelocitySecondRadialDerivative radialVelocityRadialDerivative radialVelocity
  field_simp [hr]
  ring

/-- Axial material acceleration for u_z=az+b. -/
def axialAcceleration (a aDot b bDot z : ℝ) : ℝ :=
  (aDot + a ^ 2) * z + (bDot + a * b)

/-- Radial pressure gradient divided by density, as required by radial momentum balance. -/
def radialPressureGradientOverRho
    (a aDot q uTheta r : ℝ) : ℝ :=
  (aDot / 2 - a ^ 2 / 4) * r + q ^ 2 / r ^ 3 + uTheta ^ 2 / r

/-- Axial pressure gradient divided by density, as required by axial momentum balance. -/
def axialPressureGradientOverRho
    (a aDot b bDot z : ℝ) : ℝ :=
  -(aDot + a ^ 2) * z - (bDot + a * b)

/-- Swirl-induced radial pressure potential with a reference radius rRef. -/
def swirlPressurePotential
    (uTheta : ℝ → ℝ) (rRef r : ℝ) : ℝ :=
  ∫ ξ in rRef..r, uTheta ξ ^ 2 / ξ

/-- Exact pressure field at a fixed time, up to the arbitrary reference p0. -/
def pressureFieldAtTime
    (rho a aDot b bDot q p0 : ℝ)
    (Pi : ℝ → ℝ) (r z : ℝ) : ℝ :=
  p0
    + rho * (aDot / 4 - a ^ 2 / 8) * r ^ 2
    - rho * q ^ 2 / (2 * r ^ 2)
    - rho / 2 * (aDot + a ^ 2) * z ^ 2
    - rho * (bDot + a * b) * z
    + rho * Pi r

/-- The swirl pressure integral has the required radial derivative under the standard FTC hypotheses. -/
theorem swirlPressurePotential_hasDerivAt
    {uTheta : ℝ → ℝ} {rRef r : ℝ}
    (hint : IntervalIntegrable (fun ξ => uTheta ξ ^ 2 / ξ) volume rRef r)
    (hmeas : StronglyMeasurableAtFilter
      (fun ξ => uTheta ξ ^ 2 / ξ) (𝓝 r) volume)
    (hcont : ContinuousAt (fun ξ => uTheta ξ ^ 2 / ξ) r) :
    HasDerivAt (swirlPressurePotential uTheta rRef)
      (uTheta r ^ 2 / r) r := by
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcont

/-- Radial derivative of the exact pressure field. -/
theorem pressureFieldAtTime_radial_hasDerivAt
    {rho a aDot b bDot q p0 r z uThetaVal : ℝ}
    {Pi : ℝ → ℝ}
    (hr : r ≠ 0)
    (hPi : HasDerivAt Pi (uThetaVal ^ 2 / r) r) :
    HasDerivAt
      (fun ρr => pressureFieldAtTime rho a aDot b bDot q p0 Pi ρr z)
      (rho * radialPressureGradientOverRho a aDot q uThetaVal r) r := by
  have hquad :
      HasDerivAt
        (fun x : ℝ => rho * (aDot / 4 - a ^ 2 / 8) * x ^ 2)
        (rho * (aDot / 4 - a ^ 2 / 8) * (2 * r)) r := by
    convert! ((hasDerivAt_id r).pow 2).const_mul
      (rho * (aDot / 4 - a ^ 2 / 8)) using 1 <;> ring
  have hden : 2 * r ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hr)
  have hrat :
      HasDerivAt
        (fun x : ℝ => rho * q ^ 2 / (2 * x ^ 2))
        ((0 * (2 * r ^ 2) - (rho * q ^ 2) * (2 * (2 * r))) /
          (2 * r ^ 2) ^ 2) r := by
    have hnum : HasDerivAt (fun _x : ℝ => rho * q ^ 2) 0 r :=
      hasDerivAt_const r _
    have hdenDeriv :
        HasDerivAt (fun x : ℝ => 2 * x ^ 2) (2 * (2 * r)) r := by
      convert! ((hasDerivAt_id r).pow 2).const_mul 2 using 1 <;> ring
    exact hnum.div hdenDeriv hden
  have hbase :
      HasDerivAt
        (fun x : ℝ =>
          p0
            + rho * (aDot / 4 - a ^ 2 / 8) * x ^ 2
            - rho * q ^ 2 / (2 * x ^ 2))
        (0
          + rho * (aDot / 4 - a ^ 2 / 8) * (2 * r)
          - ((0 * (2 * r ^ 2) - (rho * q ^ 2) * (2 * (2 * r))) /
            (2 * r ^ 2) ^ 2)) r := by
    exact ((hasDerivAt_const r p0).add hquad).sub hrat
  have hall :=
    (((hbase.sub_const (rho / 2 * (aDot + a ^ 2) * z ^ 2))
      .sub_const (rho * (bDot + a * b) * z))
      .add (hPi.const_mul rho))
  unfold pressureFieldAtTime radialPressureGradientOverRho
  convert! hall using 1 <;> field_simp [hr] <;> ring

/-- Axial derivative of the exact pressure field. -/
theorem pressureFieldAtTime_axial_hasDerivAt
    {rho a aDot b bDot q p0 r z : ℝ}
    {Pi : ℝ → ℝ} :
    HasDerivAt
      (fun ζ => pressureFieldAtTime rho a aDot b bDot q p0 Pi r ζ)
      (rho * axialPressureGradientOverRho a aDot b bDot z) z := by
  have hquad :
      HasDerivAt
        (fun x : ℝ => -(rho / 2 * (aDot + a ^ 2)) * x ^ 2)
        (-(rho / 2 * (aDot + a ^ 2)) * (2 * z)) z := by
    convert! ((hasDerivAt_id z).pow 2).const_mul
      (-(rho / 2 * (aDot + a ^ 2))) using 1 <;> ring
  have hlin :
      HasDerivAt
        (fun x : ℝ => -(rho * (bDot + a * b)) * x)
        (-(rho * (bDot + a * b))) z := by
    convert! (hasDerivAt_id z).const_mul (-(rho * (bDot + a * b))) using 1 <;> ring
  have hconst : HasDerivAt
      (fun _x : ℝ =>
        p0
          + rho * (aDot / 4 - a ^ 2 / 8) * r ^ 2
          - rho * q ^ 2 / (2 * r ^ 2)
          + rho * Pi r)
      0 z := hasDerivAt_const z _
  unfold pressureFieldAtTime axialPressureGradientOverRho
  convert! (hconst.add hquad |>.add hlin) using 1 <;> ring

end

end KiknadzeKrasnov
