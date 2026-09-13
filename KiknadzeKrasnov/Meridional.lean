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
  unfold radialVelocity
  convert
    (hasDerivAt_const_mul (x := r) (-(a / 2))).add
      ((hasDerivAt_const r q).div (hasDerivAt_id r) hr)
    using 1 <;> field_simp [hr] <;> ring

/-- The radial flux derivative is exactly `-a r`; the source term differentiates away. -/
theorem radialFlux_hasDerivAt {a q r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (radialFlux a q) (-a * r) r := by
  convert (hasDerivAt_id r).mul (radialVelocity_hasDerivAt (a := a) (q := q) hr) using 1
  · rfl
  · unfold radialVelocity
    field_simp [hr]
    ring

/-- The axial KK velocity has constant spatial derivative `a`. -/
theorem axialVelocity_hasDerivAt (a b z : ℝ) :
    HasDerivAt (axialVelocity a b) a z := by
  unfold axialVelocity
  convert (hasDerivAt_const_mul (x := z) a).add_const b using 1 <;> ring

/-- Machine-checked cylindrical incompressibility on the punctured radial domain. -/
theorem continuityResidual_zero {a q r b z : ℝ} (hr : r ≠ 0) :
    continuityResidual a q r b z = 0 := by
  unfold continuityResidual
  rw [(radialFlux_hasDerivAt (a := a) (q := q) hr).deriv,
    (axialVelocity_hasDerivAt a b z).deriv]
  field_simp [hr]
  ring

/-- Source/sink flux per unit axial length, written exactly as the manuscript's angular integral. -/
def sourceFlux (q : ℝ) : ℝ := ∫ θ : ℝ in 0..2 * Real.pi, q

/-- `q/r` carries radial flux `2πq` per unit axial length. -/
theorem sourceFlux_eq (q : ℝ) : sourceFlux q = 2 * Real.pi * q := by
  simp [sourceFlux]
  ring

end

end KiknadzeKrasnov
