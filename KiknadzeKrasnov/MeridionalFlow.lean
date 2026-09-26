import KiknadzeKrasnov.Kinematics

namespace KiknadzeKrasnov

noncomputable section

open intervalIntegral

/-- The polynomial form of \(r u_r\) obtained from axisymmetric continuity. -/
def radialMomentum (a q r : ℝ) : ℝ := -(a / 2) * r ^ 2 + q

/-- Equation (24): the polynomial radial momentum equals \(r u_r\) off the axis. -/
theorem radialMomentum_eq_radius_mul_velocity {a q r : ℝ} (hr : r ≠ 0) :
    radialMomentum a q r = r * radialVelocity a q r := by
  unfold radialMomentum radialVelocity
  field_simp [hr]

/-- Equation (23): derivative of \(r u_r\) in its polynomial representation. -/
theorem radialMomentum_hasDerivAt (a q r : ℝ) :
    HasDerivAt (radialMomentum a q) (-a * r) r := by
  unfold radialMomentum
  convert (((hasDerivAt_id r).pow 2).const_mul (-(a / 2))).add_const q using 1 <;> ring

/-- Equation (21)-(22): the prescribed axial gradient is exactly \(a\). -/
theorem axialVelocity_hasDerivAt (a b z : ℝ) :
    HasDerivAt (axialVelocity a b) a z := by
  simpa [axialVelocity] using ((hasDerivAt_id z).const_mul a).add_const b

/-- Equation (23): the cylindrical radial-divergence contribution is \(-a\). -/
theorem radial_divergence_term {a r : ℝ} (hr : r ≠ 0) :
    (-a * r) / r = -a := by
  field_simp [hr]

/-- Equations (23) and (21) cancel exactly in the continuity equation. -/
theorem meridional_continuity_residual {a r : ℝ} (hr : r ≠ 0) :
    (-a * r) / r + a = 0 := by
  rw [radial_divergence_term hr]
  ring

/-- Equation (26): flux per unit axial length carried by the \(q/r\) term. -/
theorem radial_source_flux (q : ℝ) :
    (∫ _theta : ℝ in 0..(2 * Real.pi), q) = 2 * Real.pi * q := by
  simp

end

end KiknadzeKrasnov
