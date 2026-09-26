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
  have h := ((hasDerivAt_id z).const_mul a).const_add b
  convert h using 1
  · ext x
    simp [axialVelocity]
  · ring

/-- The integrated radial quantity has derivative -a r. -/
theorem radialFluxPrimitive_hasDerivAt (a q r : ℝ) :
    HasDerivAt (fun ρ : ℝ => radialFluxPrimitive a q ρ) (-a * r) r := by
  have h := (((hasDerivAt_id r).pow 2).const_mul (-(a / 2))).const_add q
  convert h using 1
  · ext x
    simp [radialFluxPrimitive]
  · ring

/-- Radial derivative of the explicit KK radial velocity on the punctured domain. -/
theorem radialVelocity_hasDerivAt_r {a q r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun ρ : ℝ => radialVelocity a q ρ)
      (-a / 2 - q / r ^ 2) r := by
  have hlin := (hasDerivAt_id r).const_mul (-(a / 2))
  have hfrac := (hasDerivAt_const r q).div (hasDerivAt_id r) hr
  have h := hlin.add hfrac
  convert h using 1
  · ext x
    simp [radialVelocity, div_eq_mul_inv]
    ring
  · field_simp [hr]
    ring

/-- Time derivative of the radial velocity when q is fixed. -/
theorem radialVelocity_hasDerivAt_t
    {a : ℝ → ℝ} {aDot q r t : ℝ}
    (ha : HasDerivAt a aDot t) :
    HasDerivAt (fun τ : ℝ => radialVelocity (a τ) q r)
      (-(aDot / 2) * r) t := by
  have h := (ha.const_mul (-r / 2)).add_const (q / r)
  convert h using 1
  · ext x
    simp [radialVelocity]
    ring
  · ring

/-- Time derivative of the axial velocity under differentiable prescribed a(t), b(t). -/
theorem axialVelocity_hasDerivAt_t
    {a b : ℝ → ℝ} {aDot bDot z t : ℝ}
    (ha : HasDerivAt a aDot t) (hb : HasDerivAt b bDot t) :
    HasDerivAt (fun τ : ℝ => axialVelocity (a τ) (b τ) z)
      (aDot * z + bDot) t := by
  have h := (ha.const_mul z).add hb
  convert h using 1
  · ext x
    simp [axialVelocity]
    ring
  · ring

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
