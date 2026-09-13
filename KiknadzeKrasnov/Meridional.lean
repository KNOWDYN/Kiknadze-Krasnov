import KiknadzeKrasnov.Kinematics

namespace KiknadzeKrasnov

noncomputable section

open intervalIntegral

/-- Radial flux factor `r u_r` appearing in cylindrical continuity. -/
def radialFlux (a q r : ℝ) : ℝ := r * radialVelocity a q r

/-- Pointwise cylindrical continuity residual for the explicit KK meridional field. -/
def continuityResidual (a q r b z : ℝ) : ℝ :=
  deriv (radialFlux a q) r / r + deriv (axialVelocity a b) z

/-- The derivative of the punctured-domain radial velocity. -/
theorem radialVelocity_hasDerivAt {a q r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (radialVelocity a q) (-a / 2 - q / r ^ 2) r := by
  have hlin : HasDerivAt (fun y : ℝ => -(a / 2) * y) (-(a / 2)) r :=
    hasDerivAt_const_mul (x := r) (-(a / 2))
  have hquot := (hasDerivAt_const r q).div (hasDerivAt_id r) hr
  have h := hlin.add hquot
  convert h using 1
  · funext y
    simp [radialVelocity]
  · simp only [id_eq]
    field_simp [hr]
    ring

/-- The radial flux derivative is exactly `-a r`; the source term differentiates away. -/
theorem radialFlux_hasDerivAt {a q r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (radialFlux a q) (-a * r) r := by
  have h := (hasDerivAt_id r).mul
    (radialVelocity_hasDerivAt (a := a) (q := q) hr)
  convert h using 1
  · funext y
    rfl
  · simp only [id_eq]
    unfold radialVelocity
    field_simp [hr]
    ring

/-- The axial KK velocity has constant spatial derivative `a`. -/
theorem axialVelocity_hasDerivAt (a b z : ℝ) :
    HasDerivAt (axialVelocity a b) a z := by
  have h := (hasDerivAt_const_mul (x := z) a).add (hasDerivAt_const z b)
  convert h using 1
  · funext y
    simp [axialVelocity]
  · ring

/-- Machine-checked cylindrical incompressibility on the punctured radial domain. -/
theorem continuityResidual_zero {a q r b z : ℝ} (hr : r ≠ 0) :
    continuityResidual a q r b z = 0 := by
  unfold continuityResidual
  rw [(radialFlux_hasDerivAt (a := a) (q := q) hr).deriv,
    (axialVelocity_hasDerivAt a b z).deriv]
  field_simp [hr]
  ring

/-- Source/sink flux per unit axial length, written exactly as the manuscript's angular integral. -/
def sourceFlux (q : ℝ) : ℝ := ∫ _theta : ℝ in 0..2 * Real.pi, q

/-- `q/r` carries radial flux `2πq` per unit axial length. -/
theorem sourceFlux_eq (q : ℝ) : sourceFlux q = 2 * Real.pi * q := by
  simp [sourceFlux]

end

end KiknadzeKrasnov
