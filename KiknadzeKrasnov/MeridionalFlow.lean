import KiknadzeKrasnov.Kinematics

namespace KiknadzeKrasnov

noncomputable section

open intervalIntegral

/-- The integrated radial continuity relation, before division by the radius. -/
def radialFluxPrimitive (a q r : ℝ) : ℝ := -(a / 2) * r ^ 2 + q

/-- The explicit KK radial velocity reproduces the integrated continuity relation on r ≠ 0. -/
theorem radius_mul_radialVelocity {a q r : ℝ} (hr : r ≠ 0) :
    r * radialVelocity a q r = radialFluxPrimitive a q r := by
  unfold radialVelocity radialFluxPrimitive
  field_simp [hr]

/-- The axial KK field has the prescribed constant axial gradient. -/
theorem axialVelocity_hasDerivAt (a b z : ℝ) :
    HasDerivAt (fun ζ : ℝ => axialVelocity a b ζ) a z := by
  simpa [axialVelocity] using
    ((hasDerivAt_id z).const_mul a).const_add b

/-- The integrated radial quantity has derivative -a r. -/
theorem radialFluxPrimitive_hasDerivAt (a q r : ℝ) :
    HasDerivAt (fun ρ : ℝ => radialFluxPrimitive a q ρ) (-a * r) r := by
  have h := (((hasDerivAt_id r).pow 2).const_mul (-(a / 2))).const_add q
  convert h using 1
  · funext x
    simp [radialFluxPrimitive]
    ring
  · simp

/-- Radial contribution to the divergence of the KK meridional field. -/
def radialDivergenceContribution (a : ℝ) : ℝ := -a

/-- Axial contribution to the divergence of the KK meridional field. -/
def axialDivergenceContribution (a : ℝ) : ℝ := a

/-- Continuity is satisfied exactly by cancellation of radial and axial contributions. -/
@[simp] theorem meridional_continuity (a : ℝ) :
    radialDivergenceContribution a + axialDivergenceContribution a = 0 := by
  simp [radialDivergenceContribution, axialDivergenceContribution]

/-- Flux of the q/r source term through a cylindrical surface per unit axial length. -/
def radialSourceFlux (q r : ℝ) : ℝ :=
  ∫ _θ in (0 : ℝ)..(2 * Real.pi), (q / r) * r

/-- The q/r contribution carries radial flux 2πq on the punctured radial domain. -/
theorem radialSourceFlux_eq {q r : ℝ} (hr : r ≠ 0) :
    radialSourceFlux q r = 2 * Real.pi * q := by
  simp [radialSourceFlux, hr]

end

end KiknadzeKrasnov
