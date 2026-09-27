import KiknadzeKrasnov.Kinematics

namespace KiknadzeKrasnov

noncomputable section

open intervalIntegral

/-!
Pass 3A formalises the manuscript's meridional construction at a fixed time.
The scalars `a`, `b`, and `q` are therefore instantaneous values; this file does
not assume that `q` is time-independent. Constancy of `q` is a later
angular-momentum compatibility result.
-/

/-- The integrated radial continuity relation before division by the radius. -/
def radialFluxPrimitive (a q r : ℝ) : ℝ := -(a / 2) * r ^ 2 + q

/-- Eq. (21): the explicit axial KK field has the prescribed axial gradient. -/
theorem axialVelocity_hasDerivAt (a b z : ℝ) :
    HasDerivAt (fun ζ : ℝ => axialVelocity a b ζ) a z := by
  simpa [axialVelocity] using
    ((hasDerivAt_id z).const_mul a).const_add b

/-- Eq. (21), stated using `deriv`. -/
@[simp] theorem axialVelocity_deriv (a b z : ℝ) :
    deriv (fun ζ : ℝ => axialVelocity a b ζ) z = a :=
  (axialVelocity_hasDerivAt a b z).deriv

/-- Radial derivative of the explicit KK velocity on the punctured radial domain. -/
theorem radialVelocity_hasDerivAt
    {a q r : ℝ} (hr : PuncturedRadius r) :
    HasDerivAt (fun ρ : ℝ => radialVelocity a q ρ)
      (-(a / 2) - q / r ^ 2) r := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hlin : HasDerivAt (fun ρ : ℝ => -(a / 2) * ρ) (-(a / 2)) r := by
    simpa using (hasDerivAt_id r).const_mul (-(a / 2))
  have hsource : HasDerivAt (fun ρ : ℝ => q / ρ) (-q / r ^ 2) r := by
    convert (hasDerivAt_const r q).div (hasDerivAt_id r) hr0 using 1
    · funext x
      rfl
    · field_simp [hr0]
      ring
  simpa [radialVelocity] using hlin.add hsource

/--
Eq. (23): the derivative of the actual radial flux `r u_r` is `-a r`.
This is the non-tautological radial part of the continuity verification.
-/
theorem radialFlux_hasDerivAt
    {a q r : ℝ} (hr : PuncturedRadius r) :
    HasDerivAt (fun ρ : ℝ => ρ * radialVelocity a q ρ) (-a * r) r := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hprod := (hasDerivAt_id r).mul
    (radialVelocity_hasDerivAt (a := a) (q := q) hr)
  convert hprod using 1
  · funext x
    simp
  · unfold radialVelocity
    field_simp [hr0]
    ring

/-- Eq. (23): `(1/r) ∂_r(r u_r) = -a` on the natural punctured domain. -/
theorem radial_continuity_term_eq
    {a q r : ℝ} (hr : PuncturedRadius r) :
    deriv (fun ρ : ℝ => ρ * radialVelocity a q ρ) r / r = -a := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  rw [(radialFlux_hasDerivAt (a := a) (q := q) hr).deriv]
  field_simp [hr0]

/--
Eqs. (23)--(24): the explicit radial velocity satisfies the integrated
continuity relation `r u_r = -a r²/2 + q`.
-/
theorem radius_mul_radialVelocity
    {a q r : ℝ} (hr : PuncturedRadius r) :
    r * radialVelocity a q r = radialFluxPrimitive a q r := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  unfold radialVelocity radialFluxPrimitive
  field_simp [hr0]
  ring

/--
Eq. (25): on `r > 0`, the integrated relation uniquely determines the
radial velocity `u_r = -a r/2 + q/r`.
-/
theorem radialVelocity_eq_of_integrated_relation
    {ur a q r : ℝ} (hr : PuncturedRadius r)
    (hflux : r * ur = radialFluxPrimitive a q r) :
    ur = radialVelocity a q r := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  unfold radialFluxPrimitive at hflux
  unfold radialVelocity
  apply (eq_div_iff hr0).2
  calc
    ur * r = r * ur := by ring
    _ = -(a / 2) * r ^ 2 + q := hflux
    _ = (-(a / 2) * r + q / r) * r := by
      field_simp [hr0]
      ring

/--
Eq. (14) specialised to the KK meridional field: continuity is proved from
the derivatives of the actual velocity components, not from preassigned
residual values.
-/
theorem meridional_continuity
    {a b q r z : ℝ} (hr : PuncturedRadius r) :
    deriv (fun ρ : ℝ => ρ * radialVelocity a q ρ) r / r
      + deriv (fun ζ : ℝ => axialVelocity a b ζ) z = 0 := by
  rw [radial_continuity_term_eq (a := a) (q := q) hr]
  rw [axialVelocity_deriv]
  ring

/-- Eq. (26): source/sink flux through a cylindrical surface per unit axial length. -/
def radialSourceFlux (q r : ℝ) : ℝ :=
  ∫ _θ in (0 : ℝ)..(2 * Real.pi), (q / r) * r

/-- Eq. (26): the `q/r` contribution carries flux `2πq` for `r > 0`. -/
theorem radialSourceFlux_eq
    {q r : ℝ} (hr : PuncturedRadius r) :
    radialSourceFlux q r = 2 * Real.pi * q := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  simp [radialSourceFlux, hr0]

end

end KiknadzeKrasnov
