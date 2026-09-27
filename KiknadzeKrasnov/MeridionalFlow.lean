import KiknadzeKrasnov.Kinematics

namespace KiknadzeKrasnov

noncomputable section

open Set intervalIntegral

/-!
Pass 3A formalises the manuscript's meridional construction at a fixed time.
The scalars `a`, `b`, and `q` are therefore instantaneous values; this file does
not assume that `q` is time-independent. Constancy of `q` is a later
angular-momentum compatibility result.
-/

/-- The integrated radial continuity relation before division by the radius. -/
def radialFluxPrimitive (a q r : ℝ) : ℝ := -(a / 2) * r ^ 2 + q

/--
Eqs. (21)--(22): a globally differentiable axial velocity whose prescribed
gradient is the fixed-time strain value `a` is affine in `z`.
-/
theorem axial_affine_of_prescribed_gradient
    {uz : ℝ → ℝ} {a : ℝ}
    (huz : Differentiable ℝ uz)
    (hgrad : ∀ z : ℝ, deriv uz z = a) :
    ∃ b : ℝ, ∀ z : ℝ, uz z = a * z + b := by
  have hlin : Differentiable ℝ (fun z : ℝ => a * z) := by
    fun_prop
  have hderiv :
      Set.EqOn (deriv uz) (deriv fun z : ℝ => a * z) Set.univ := by
    intro z _
    calc
      deriv uz z = a := hgrad z
      _ = deriv (fun ζ : ℝ => a * ζ) z := by
        symm
        exact ((hasDerivAt_id z).const_mul a).deriv
  obtain ⟨b, hb⟩ :=
    isOpen_univ.exists_eq_add_of_deriv_eq isPreconnected_univ
      huz.differentiableOn hlin.differentiableOn hderiv
  refine ⟨b, ?_⟩
  intro z
  simpa using hb (Set.mem_univ z)

/-- The strain-only radial primitive has derivative `-a r`. -/
theorem radialStrainPrimitive_hasDerivAt (a r : ℝ) :
    HasDerivAt (fun ρ : ℝ => -(a / 2) * ρ ^ 2) (-a * r) r := by
  have h :=
    ((hasDerivAt_id r).mul (hasDerivAt_id r)).const_mul (-(a / 2))
  convert h using 1
  · funext x
    simp [pow_two]
  · simp
    ring

/--
Eqs. (23)--(24): on the connected punctured radial domain `r > 0`,
integrating `∂_r(r u_r) = -a r` yields one radial integration constant `q`.
At this stage `q` is only constant with respect to radius at the fixed time.
-/
theorem integrated_radial_relation_of_continuity
    {ur : ℝ → ℝ} {a : ℝ}
    (hflux : ∀ r : ℝ, PuncturedRadius r →
      HasDerivAt (fun ρ : ℝ => ρ * ur ρ) (-a * r) r) :
    ∃ q : ℝ, ∀ r : ℝ, PuncturedRadius r →
      r * ur r = radialFluxPrimitive a q r := by
  let f : ℝ → ℝ := fun r => r * ur r
  let g : ℝ → ℝ := fun r => -(a / 2) * r ^ 2
  have hf : DifferentiableOn ℝ f (Set.Ioi 0) := by
    intro r hr
    have hp : PuncturedRadius r := by
      simpa [PuncturedRadius] using hr
    exact (hflux r hp).differentiableAt.differentiableWithinAt
  have hg : DifferentiableOn ℝ g (Set.Ioi 0) := by
    fun_prop
  have hd : Set.EqOn (deriv f) (deriv g) (Set.Ioi 0) := by
    intro r hr
    have hp : PuncturedRadius r := by
      simpa [PuncturedRadius] using hr
    have hfd := (hflux r hp).deriv
    have hgd := (radialStrainPrimitive_hasDerivAt a r).deriv
    dsimp [f, g] at hfd hgd ⊢
    rw [hfd, hgd]
  obtain ⟨q, hq⟩ :=
    isOpen_Ioi.exists_eq_add_of_deriv_eq isPreconnected_Ioi hf hg hd
  refine ⟨q, ?_⟩
  intro r hr
  have hri : r ∈ Set.Ioi (0 : ℝ) := by
    simpa [PuncturedRadius] using hr
  have h := hq hri
  dsimp [f, g] at h
  simpa [radialFluxPrimitive] using h

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
    · rfl
    · simp
  convert hlin.add hsource using 1
  · funext x
    simp [radialVelocity]
  · ring

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
  · simp only [id_eq]
    unfold radialVelocity
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

/--
Eq. (25): on `r > 0`, the integrated relation uniquely determines the
radial velocity `u_r = -a r/2 + q/r`.
-/
theorem radialVelocity_eq_of_integrated_relation
    {ur a q r : ℝ} (hr : PuncturedRadius r)
    (hflux : r * ur = radialFluxPrimitive a q r) :
    ur = radialVelocity a q r := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hmodel :
      r * radialVelocity a q r = radialFluxPrimitive a q r :=
    radius_mul_radialVelocity hr
  have hmul : r * ur = r * radialVelocity a q r := hflux.trans hmodel.symm
  exact mul_left_cancel₀ hr0 hmul

/--
Eqs. (23)--(25) as one derivation: every radial velocity satisfying the
fixed-time continuity equation on `r > 0` belongs to the KK family
`-a r/2 + q/r` for one radial integration constant `q`.
-/
theorem radialVelocity_family_of_continuity
    {ur : ℝ → ℝ} {a : ℝ}
    (hflux : ∀ r : ℝ, PuncturedRadius r →
      HasDerivAt (fun ρ : ℝ => ρ * ur ρ) (-a * r) r) :
    ∃ q : ℝ, ∀ r : ℝ, PuncturedRadius r →
      ur r = radialVelocity a q r := by
  obtain ⟨q, hq⟩ := integrated_radial_relation_of_continuity hflux
  refine ⟨q, ?_⟩
  intro r hr
  exact radialVelocity_eq_of_integrated_relation hr (hq r hr)

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
