import KiknadzeKrasnov.ScaleDynamics

namespace KiknadzeKrasnov

noncomputable section

open MeasureTheory intervalIntegral

/-!
Pressure reconstruction for the exact KK field, corresponding to manuscript
Eqs. (50)--(59).  The pressure reference radius is named `rRef` and is
kept distinct from the distinguished material radius of Pass 4.
-/

/-- Eq. (51): pointwise time derivative of u_r for constant q. -/
def radialVelocityTimeDerivative (aDot r : ℝ) : ℝ := -(aDot / 2) * r

/-- Eq. (51): pointwise radial derivative of u_r. -/
def radialVelocityRadialDerivative (a q r : ℝ) : ℝ := -a / 2 - q / r ^ 2

/-- Eq. (53): pointwise second radial derivative of u_r. -/
def radialVelocitySecondRadialDerivative (q r : ℝ) : ℝ := 2 * q / r ^ 3

/-- The time-derivative coefficient in Eq. (51) comes from the actual time-dependent field. -/
theorem radialVelocity_time_hasDerivAt
    {a : ℝ → ℝ} {aDot q t r : ℝ}
    (ha : HasDerivAt a aDot t) :
    HasDerivAt (fun tau => radialVelocity (a tau) q r)
      (radialVelocityTimeDerivative aDot r) t := by
  unfold radialVelocity radialVelocityTimeDerivative
  have h := (ha.mul_const (-r / 2)).add_const (q / r)
  convert h using 1
  · funext tau
    ring
  · ring

/-- The radial derivative in Eq. (51) is the derivative of the actual u_r field. -/
theorem radialVelocity_radial_hasDerivAt
    {a q r : ℝ} (hr : PuncturedRadius r) :
    HasDerivAt (fun rho => radialVelocity a q rho)
      (radialVelocityRadialDerivative a q r) r := by
  change HasDerivAt (fun rho : ℝ => radialVelocity a q rho)
    (-(a / 2) - q / r ^ 2) r
  exact radialVelocity_hasDerivAt (a := a) (q := q) hr

/-- The second radial derivative in Eq. (53) is likewise obtained from the actual field. -/
theorem radialVelocityRadialDerivative_hasDerivAt
    {a q r : ℝ} (hr : PuncturedRadius r) :
    HasDerivAt (radialVelocityRadialDerivative a q)
      (radialVelocitySecondRadialDerivative q r) r := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hden : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
    convert (hasDerivAt_id r).pow 2 using 1
    · funext y
      simp
    · simp
  have hquot := (hasDerivAt_const r q).div hden (pow_ne_zero 2 hr0)
  have hconst : HasDerivAt (fun _x : ℝ => -a / 2) 0 r :=
    hasDerivAt_const r _
  have h := hconst.sub hquot
  unfold radialVelocityRadialDerivative radialVelocitySecondRadialDerivative
  convert h using 1
  field_simp [hr0]
  ring

/-- Eq. (52): the radial convective acceleration has no a q / r cross term. -/
theorem radial_convective_acceleration
    {a q r : ℝ} (hr : PuncturedRadius r) :
    radialVelocity a q r * radialVelocityRadialDerivative a q r
      = a ^ 2 / 4 * r - q ^ 2 / r ^ 3 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  unfold radialVelocity radialVelocityRadialDerivative
  field_simp [hr0]
  ring

/-- Eq. (53): the radial vector-Laplacian contribution vanishes on r>0. -/
theorem radial_viscous_operator_zero
    {a q r : ℝ} (hr : PuncturedRadius r) :
    radialVelocitySecondRadialDerivative q r
      + radialVelocityRadialDerivative a q r / r
      - radialVelocity a q r / r ^ 2 = 0 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  unfold radialVelocitySecondRadialDerivative radialVelocityRadialDerivative radialVelocity
  field_simp [hr0]
  ring

/-- Time derivative of the actual axial field u_z=a(t)z+b(t). -/
def axialVelocityTimeDerivative (aDot bDot z : ℝ) : ℝ :=
  aDot * z + bDot

theorem axialVelocity_time_hasDerivAt
    {a b : ℝ → ℝ} {aDot bDot t z : ℝ}
    (ha : HasDerivAt a aDot t) (hb : HasDerivAt b bDot t) :
    HasDerivAt (fun tau => axialVelocity (a tau) (b tau) z)
      (axialVelocityTimeDerivative aDot bDot z) t := by
  unfold axialVelocity axialVelocityTimeDerivative
  exact (ha.mul_const z).add hb

/-- Eq. (55): axial material acceleration. -/
def axialAcceleration (a aDot b bDot z : ℝ) : ℝ :=
  (aDot + a ^ 2) * z + (bDot + a * b)

theorem axial_acceleration_from_actual_field
    {a b : ℝ → ℝ} {aDot bDot t z : ℝ}
    (ha : HasDerivAt a aDot t) (hb : HasDerivAt b bDot t) :
    deriv (fun tau => axialVelocity (a tau) (b tau) z) t
      + axialVelocity (a t) (b t) z *
        deriv (fun zeta => axialVelocity (a t) (b t) zeta) z
      = axialAcceleration (a t) aDot (b t) bDot z := by
  rw [(axialVelocity_time_hasDerivAt ha hb).deriv]
  rw [axialVelocity_deriv]
  unfold axialVelocity axialVelocityTimeDerivative axialAcceleration
  ring

/-- Eq. (54): radial pressure gradient divided by density. -/
def radialPressureGradientOverRho
    (a aDot q uTheta r : ℝ) : ℝ :=
  (aDot / 2 - a ^ 2 / 4) * r + q ^ 2 / r ^ 3 + uTheta ^ 2 / r

/-- Eq. (56): axial pressure gradient divided by density. -/
def axialPressureGradientOverRho
    (a aDot b bDot z : ℝ) : ℝ :=
  -(aDot + a ^ 2) * z - (bDot + a * b)

/-- Eq. (58): swirl-induced radial pressure potential with reference radius rRef. -/
def swirlPressurePotential
    (uTheta : ℝ → ℝ) (rRef r : ℝ) : ℝ :=
  ∫ xi in rRef..r, uTheta xi ^ 2 / xi

/-- Eq. (57): exact pressure field at a fixed time, up to arbitrary p0(t). -/
def pressureFieldAtTime
    (rho a aDot b bDot q p0 : ℝ)
    (Pi : ℝ → ℝ) (r z : ℝ) : ℝ :=
  p0
    + rho * (aDot / 4 - a ^ 2 / 8) * r ^ 2
    - rho * q ^ 2 / (2 * r ^ 2)
    - rho / 2 * (aDot + a ^ 2) * z ^ 2
    - rho * (bDot + a * b) * z
    + rho * Pi r

/-- FTC certificate for the actual swirl-pressure integral. -/
theorem swirlPressurePotential_hasDerivAt
    {uTheta : ℝ → ℝ} {rRef r : ℝ}
    (hint : IntervalIntegrable (fun xi => uTheta xi ^ 2 / xi) volume rRef r)
    (hmeas : StronglyMeasurableAtFilter
      (fun xi => uTheta xi ^ 2 / xi) (nhds r) volume)
    (hcont : ContinuousAt (fun xi => uTheta xi ^ 2 / xi) r) :
    HasDerivAt (swirlPressurePotential uTheta rRef)
      (uTheta r ^ 2 / r) r := by
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcont

/-- Radial derivative of Eq. (57). -/
theorem pressureFieldAtTime_radial_hasDerivAt
    {rho a aDot b bDot q p0 r z uThetaVal : ℝ}
    {Pi : ℝ → ℝ}
    (hr : PuncturedRadius r)
    (hPi : HasDerivAt Pi (uThetaVal ^ 2 / r) r) :
    HasDerivAt
      (fun rr => pressureFieldAtTime rho a aDot b bDot q p0 Pi rr z)
      (rho * radialPressureGradientOverRho a aDot q uThetaVal r) r := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hr2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * r) r := by
    convert (hasDerivAt_id r).pow 2 using 1
    · funext y
      simp
    · simp
  have hquad :=
    hr2.const_mul (rho * (aDot / 4 - a ^ 2 / 8))
  have hinv := hr2.inv (pow_ne_zero 2 hr0)
  have hinvTerm := hinv.const_mul (-(rho * q ^ 2 / 2))
  have hPiScaled := hPi.const_mul rho
  have hconst : HasDerivAt
      (fun _ : ℝ =>
        p0
          - rho / 2 * (aDot + a ^ 2) * z ^ 2
          - rho * (bDot + a * b) * z)
      0 r := hasDerivAt_const r _
  have hsum := ((hconst.add hquad).add hinvTerm).add hPiScaled
  unfold pressureFieldAtTime radialPressureGradientOverRho
  convert hsum using 1
  · funext y
    simp [div_eq_mul_inv]
    ring
  · field_simp [hr0]
    ring

/-- Axial derivative of Eq. (57). -/
theorem pressureFieldAtTime_axial_hasDerivAt
    {rho a aDot b bDot q p0 r z : ℝ}
    {Pi : ℝ → ℝ} :
    HasDerivAt
      (fun zz => pressureFieldAtTime rho a aDot b bDot q p0 Pi r zz)
      (rho * axialPressureGradientOverRho a aDot b bDot z) z := by
  have hz2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by
    convert (hasDerivAt_id z).pow 2 using 1
    · funext y
      simp
    · simp
  have hquad :=
    hz2.const_mul (-(rho / 2 * (aDot + a ^ 2)))
  have hlin :=
    hasDerivAt_const_mul (x := z) (-(rho * (bDot + a * b)))
  have hconst : HasDerivAt
      (fun _ : ℝ =>
        p0
          + rho * (aDot / 4 - a ^ 2 / 8) * r ^ 2
          - rho * q ^ 2 / (2 * r ^ 2)
          + rho * Pi r)
      0 z := hasDerivAt_const z _
  have hsum := (hconst.add hquad).add hlin
  unfold pressureFieldAtTime axialPressureGradientOverRho
  convert hsum using 1
  · funext y
    simp [div_eq_mul_inv]
    ring
  · ring

/-- Eq. (54) obtained by differentiating the actual pressure field. -/
theorem pressureFieldAtTime_radial_deriv_eq
    {rho a aDot b bDot q p0 r z uThetaVal : ℝ}
    {Pi : ℝ → ℝ}
    (hrho : rho ≠ 0)
    (hr : PuncturedRadius r)
    (hPi : HasDerivAt Pi (uThetaVal ^ 2 / r) r) :
    deriv (fun rr => pressureFieldAtTime rho a aDot b bDot q p0 Pi rr z) r / rho
      = radialPressureGradientOverRho a aDot q uThetaVal r := by
  rw [(pressureFieldAtTime_radial_hasDerivAt hr hPi).deriv]
  field_simp [hrho]

/-- Eq. (56) obtained by differentiating the actual pressure field. -/
theorem pressureFieldAtTime_axial_deriv_eq
    {rho a aDot b bDot q p0 r z : ℝ}
    {Pi : ℝ → ℝ}
    (hrho : rho ≠ 0) :
    deriv (fun zz => pressureFieldAtTime rho a aDot b bDot q p0 Pi r zz) z / rho
      = axialPressureGradientOverRho a aDot b bDot z := by
  rw [(pressureFieldAtTime_axial_hasDerivAt
    (rho := rho) (a := a) (aDot := aDot) (b := b) (bDot := bDot)
    (q := q) (p0 := p0) (r := r) (z := z) (Pi := Pi)).deriv]
  field_simp [hrho]

end

end KiknadzeKrasnov
