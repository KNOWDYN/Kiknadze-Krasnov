import KiknadzeKrasnov.MeridionalFlow

namespace KiknadzeKrasnov

noncomputable section

open Set

/-!
This module formalises the manuscript's angular-momentum reduction, Eqs. (27)--(36),
and the corresponding supplementary residual factorisation.  The source coefficient
`q(t)` is allowed to depend on time until the fixed-profile compatibility theorem
proves that it is constant on the physical time interval under an explicit
non-trivial-profile hypothesis.
-/

/-- Eq. (27): specific axial angular momentum. -/
def specificAngularMomentum (r uTheta : ℝ) : ℝ := r * uTheta

@[simp] theorem specificAngularMomentum_eq (r uTheta : ℝ) :
    specificAngularMomentum r uTheta = angularMomentum r uTheta := by
  rfl

/--
Pointwise azimuthal momentum residual from manuscript Eq. (16), after using the
KK assumption that the swirl is independent of `z`.
-/
def azimuthalVelocityResidual
    (nu ur r uTheta uTheta_t uTheta_r uTheta_rr : ℝ) : ℝ :=
  uTheta_t + ur * uTheta_r + ur * uTheta / r
    - nu * (uTheta_rr + uTheta_r / r - uTheta / r ^ 2)

/-- Pointwise angular-momentum residual from manuscript Eq. (28). -/
def angularMomentumResidual
    (nu ur r L_t L_r L_rr : ℝ) : ℝ :=
  L_t + ur * L_r - nu * (L_rr - L_r / r)

/--
Eq. (28) follows from Eq. (16): after `L = r u_θ`, the angular-momentum
residual is exactly `r` times the azimuthal-velocity residual.
-/
theorem angularMomentumResidual_eq_radius_mul_azimuthalResidual
    {nu ur r uTheta uTheta_t uTheta_r uTheta_rr : ℝ}
    (hr : PuncturedRadius r) :
    angularMomentumResidual nu ur r
      (r * uTheta_t)
      (uTheta + r * uTheta_r)
      (2 * uTheta_r + r * uTheta_rr)
      =
    r * azimuthalVelocityResidual nu ur r
      uTheta uTheta_t uTheta_r uTheta_rr := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  unfold angularMomentumResidual azimuthalVelocityResidual
  field_simp [hr0]
  ring

/-- Vanishing azimuthal residual implies the angular-momentum equation. -/
theorem angularMomentumResidual_zero_of_azimuthalResidual_zero
    {nu ur r uTheta uTheta_t uTheta_r uTheta_rr : ℝ}
    (hr : PuncturedRadius r)
    (hres : azimuthalVelocityResidual nu ur r
      uTheta uTheta_t uTheta_r uTheta_rr = 0) :
    angularMomentumResidual nu ur r
      (r * uTheta_t)
      (uTheta + r * uTheta_r)
      (2 * uTheta_r + r * uTheta_rr) = 0 := by
  rw [angularMomentumResidual_eq_radius_mul_azimuthalResidual hr, hres]
  ring

/-- On `r>0`, Eq. (28) is also sufficient for the z-independent Eq. (16). -/
theorem azimuthalResidual_zero_of_angularMomentumResidual_zero
    {nu ur r uTheta uTheta_t uTheta_r uTheta_rr : ℝ}
    (hr : PuncturedRadius r)
    (hres : angularMomentumResidual nu ur r
      (r * uTheta_t)
      (uTheta + r * uTheta_r)
      (2 * uTheta_r + r * uTheta_rr) = 0) :
    azimuthalVelocityResidual nu ur r
      uTheta uTheta_t uTheta_r uTheta_rr = 0 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  rw [angularMomentumResidual_eq_radius_mul_azimuthalResidual hr] at hres
  exact (mul_eq_zero.mp hres).resolve_left hr0

/-- Eq. (29) with a time-dependent inverse-squared scale. -/
def profileAngularMomentum
    (beta : ℝ → ℝ) (F : ℝ → ℝ) (t r : ℝ) : ℝ :=
  F (scaledX (beta t) r)

/-- Time chain rule for `L(t,r)=F(β(t)r²)`. -/
theorem profileAngularMomentum_time_hasDerivAt
    {beta F : ℝ → ℝ} {t r betaDot Fp : ℝ}
    (hbeta : HasDerivAt beta betaDot t)
    (hF : HasDerivAt F Fp (scaledX (beta t) r)) :
    HasDerivAt (fun τ : ℝ => profileAngularMomentum beta F τ r)
      (betaDot * r ^ 2 * Fp) t := by
  have hx : HasDerivAt (fun τ : ℝ => scaledX (beta τ) r)
      (betaDot * r ^ 2) t := by
    simpa [scaledX] using hbeta.mul_const (r ^ 2)
  convert hF.comp t hx using 1
  · rfl
  · ring

/--
First identity in Eq. (30): `L_t=(βdot/β)xF'`, stated pointwise for
`β ≠ 0`.
-/
theorem profileAngularMomentum_time_deriv_eq
    {beta F : ℝ → ℝ} {t r betaDot Fp : ℝ}
    (hbeta0 : beta t ≠ 0)
    (hbeta : HasDerivAt beta betaDot t)
    (hF : HasDerivAt F Fp (scaledX (beta t) r)) :
    deriv (fun τ : ℝ => profileAngularMomentum beta F τ r) t
      = (betaDot / beta t) * scaledX (beta t) r * Fp := by
  rw [(profileAngularMomentum_time_hasDerivAt hbeta hF).deriv]
  unfold scaledX
  field_simp [hbeta0]

/-- Radial chain rule for `L=F(βr²)`, the second identity in Eq. (30). -/
theorem profileAngularMomentum_radial_hasDerivAt
    {F : ℝ → ℝ} {beta r Fp : ℝ}
    (hF : HasDerivAt F Fp (scaledX beta r)) :
    HasDerivAt (fun ρ : ℝ => F (scaledX beta ρ))
      (2 * beta * r * Fp) r := by
  have hx : HasDerivAt (fun ρ : ℝ => scaledX beta ρ)
      (2 * beta * r) r := by
    unfold scaledX
    have hsquare := (hasDerivAt_id r).mul (hasDerivAt_id r)
    convert hsquare.const_mul beta using 1
    · funext x
      simp [pow_two]
    · simp
      ring
  convert hF.comp r hx using 1
  · rfl
  · ring

/-- The explicit first radial derivative appearing in Eq. (30). -/
def profileRadialDerivative
    (beta : ℝ) (Fp : ℝ → ℝ) (r : ℝ) : ℝ :=
  2 * beta * r * Fp (scaledX beta r)

/--
When `Fp` is genuinely the derivative of the fixed profile `F`, the
auxiliary radial-derivative expression is the derivative of the actual
composed angular-momentum profile at every radius.
-/
theorem profileAngularMomentum_radial_deriv_eq
    {F Fp : ℝ → ℝ} {beta r : ℝ}
    (hF : ∀ x : ℝ, HasDerivAt F (Fp x) x) :
    deriv (fun ρ : ℝ => F (scaledX beta ρ)) r
      = profileRadialDerivative beta Fp r := by
  rw [(profileAngularMomentum_radial_hasDerivAt (hF (scaledX beta r))).deriv]
  rfl

/--
Derivative of the first radial derivative.  This is the actual second
radial derivative of the scaled profile whenever `Fp` is its profile derivative.
-/
theorem profileRadialDerivative_hasDerivAt
    {Fp : ℝ → ℝ} {beta r Fpp : ℝ}
    (hFp : HasDerivAt Fp Fpp (scaledX beta r)) :
    HasDerivAt (profileRadialDerivative beta Fp)
      (2 * beta * Fp (scaledX beta r)
        + 4 * beta ^ 2 * r ^ 2 * Fpp) r := by
  have hx : HasDerivAt (fun ρ : ℝ => scaledX beta ρ)
      (2 * beta * r) r := by
    unfold scaledX
    have hsquare := (hasDerivAt_id r).mul (hasDerivAt_id r)
    convert hsquare.const_mul beta using 1
    · funext x
      simp [pow_two]
    · simp
      ring
  have hcomp : HasDerivAt (fun ρ : ℝ => Fp (scaledX beta ρ))
      (Fpp * (2 * beta * r)) r := hFp.comp r hx
  have hlin : HasDerivAt (fun ρ : ℝ => 2 * beta * ρ) (2 * beta) r := by
    simpa using (hasDerivAt_id r).const_mul (2 * beta)
  convert hlin.mul hcomp using 1
  · funext x
    rfl
  · ring

/--
Third identity in Eq. (30):
`L_rr - (1/r)L_r = 4 β x F''` on the punctured radial domain.
-/
theorem profile_radial_diffusion_operator_eq
    {Fp : ℝ → ℝ} {beta r Fpp : ℝ}
    (hr : PuncturedRadius r)
    (hFp : HasDerivAt Fp Fpp (scaledX beta r)) :
    deriv (profileRadialDerivative beta Fp) r
      - profileRadialDerivative beta Fp r / r
      = 4 * beta * scaledX beta r * Fpp := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  rw [(profileRadialDerivative_hasDerivAt hFp).deriv]
  unfold profileRadialDerivative scaledX
  field_simp [hr0]
  ring

/--
The third identity in Eq. (30) for the actual composed profile, not merely
for an auxiliary jet: if `Fp=F'` globally and `Fp'(x)=Fpp` at the point,
then `L_rr-(1/r)L_r=4βxFpp`.
-/
theorem profileAngularMomentum_radial_second_operator_eq
    {F Fp : ℝ → ℝ} {beta r Fpp : ℝ}
    (hr : PuncturedRadius r)
    (hF : ∀ x : ℝ, HasDerivAt F (Fp x) x)
    (hFp : HasDerivAt Fp Fpp (scaledX beta r)) :
    deriv (fun ρ : ℝ =>
      deriv (fun σ : ℝ => F (scaledX beta σ)) ρ) r
      - deriv (fun σ : ℝ => F (scaledX beta σ)) r / r
      = 4 * beta * scaledX beta r * Fpp := by
  have hfun :
      (fun ρ : ℝ => deriv (fun σ : ℝ => F (scaledX beta σ)) ρ)
        = profileRadialDerivative beta Fp := by
    funext ρ
    exact profileAngularMomentum_radial_deriv_eq hF
  rw [hfun]
  rw [profileAngularMomentum_radial_deriv_eq hF]
  exact profile_radial_diffusion_operator_eq hr hFp

/-- Eq. (31) moved to the left-hand side. -/
def preSeparationResidual
    (nu a q beta betaDot x Fp Fpp : ℝ) : ℝ :=
  (betaDot / beta - a) * x * Fp
    + 2 * beta * q * Fp
    - 4 * nu * beta * x * Fpp

/--
Manuscript Eq. (31) is exactly the angular-momentum residual after substituting
Eq. (25) and the three chain-rule coefficients in Eq. (30).  This theorem
connects the reduced residual to the actual KK radial velocity rather than
introducing Eq. (31) as an independent assumption.
-/
theorem angularMomentumResidual_eq_preSeparationResidual
    {nu a q beta betaDot r Fp Fpp : ℝ}
    (hr : PuncturedRadius r)
    (hbeta : beta ≠ 0) :
    angularMomentumResidual nu (radialVelocity a q r) r
      ((betaDot / beta) * scaledX beta r * Fp)
      (2 * beta * r * Fp)
      (2 * beta * Fp + 4 * beta ^ 2 * r ^ 2 * Fpp)
      =
    preSeparationResidual nu a q beta betaDot
      (scaledX beta r) Fp Fpp := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  unfold angularMomentumResidual preSeparationResidual radialVelocity scaledX
  field_simp [hr0, hbeta]
  ring

/-- Eq. (32) moved to the left-hand side. -/
def betaScaleResidual (nu a beta betaDot : ℝ) : ℝ :=
  betaDot - a * beta + 4 * nu * beta ^ 2

/-- Eq. (33) moved to the left-hand side. -/
def profileResidual (nu q x Fp Fpp : ℝ) : ℝ :=
  2 * nu * x * Fpp + (2 * nu * x - q) * Fp

/--
Exact separation identity behind Eqs. (31)--(33).  It prevents the two
compatibility equations from being inserted as unrelated assumptions.
-/
theorem preSeparationResidual_factor
    {nu a q beta betaDot x Fp Fpp : ℝ}
    (hbeta : beta ≠ 0) :
    preSeparationResidual nu a q beta betaDot x Fp Fpp
      =
    (x * Fp / beta) * betaScaleResidual nu a beta betaDot
      - 2 * beta * profileResidual nu q x Fp Fpp := by
  unfold preSeparationResidual betaScaleResidual profileResidual
  field_simp [hbeta]
  ring

/-- Eqs. (32) and (33) jointly discharge Eq. (31). -/
theorem preSeparationResidual_zero
    {nu a q beta betaDot x Fp Fpp : ℝ}
    (hbeta : beta ≠ 0)
    (hscale : betaScaleResidual nu a beta betaDot = 0)
    (hprofile : profileResidual nu q x Fp Fpp = 0) :
    preSeparationResidual nu a q beta betaDot x Fp Fpp = 0 := by
  rw [preSeparationResidual_factor hbeta, hscale, hprofile]
  ring

/--
Once Eq. (32) holds and `β ≠ 0`, Eq. (31) is equivalent to the fixed-profile
equation Eq. (33).
-/
theorem preSeparationResidual_zero_iff_profileResidual_zero
    {nu a q beta betaDot x Fp Fpp : ℝ}
    (hbeta : beta ≠ 0)
    (hscale : betaScaleResidual nu a beta betaDot = 0) :
    preSeparationResidual nu a q beta betaDot x Fp Fpp = 0
      ↔ profileResidual nu q x Fp Fpp = 0 := by
  rw [preSeparationResidual_factor hbeta, hscale]
  simp [hbeta]

/--
Claim C004 / Eq. (34): a fixed radial profile whose derivative is nonzero
at at least one witness point forces `q(t)` to be constant on `[0,T)`.
-/
theorem source_constant_of_fixed_nontrivial_profile
    {T nu : ℝ} {q Fp Fpp : ℝ → ℝ}
    (hT : 0 < T)
    (hnontrivial : ∃ x : ℝ, Fp x ≠ 0)
    (hprofile : ∀ t ∈ TimeDomain T, ∀ x : ℝ,
      profileResidual nu (q t) x (Fp x) (Fpp x) = 0) :
    ∃ q0 : ℝ, ∀ t ∈ TimeDomain T, q t = q0 := by
  obtain ⟨x, hx⟩ := hnontrivial
  have h0mem : 0 ∈ TimeDomain T := zero_mem_timeDomain hT
  refine ⟨q 0, ?_⟩
  intro t ht
  have htEq := hprofile t ht x
  have h0Eq := hprofile 0 h0mem x
  unfold profileResidual at htEq h0Eq
  have hmul : (q t - q 0) * Fp x = 0 := by
    nlinarith [htEq, h0Eq]
  have hqdiff : q t - q 0 = 0 :=
    (mul_eq_zero.mp hmul).resolve_right hx
  exact sub_eq_zero.mp hqdiff

/-- Eq. (35): dimensionless source parameter `χ=q/(2ν)`. -/
def sourceRatio (nu q : ℝ) : ℝ := q / (2 * nu)

/-- Eq. (35) agrees exactly with the shape parameter already defined in Parameters. -/
theorem shape_eq_one_add_sourceRatio (p : FluidParams) (q : ℝ) :
    shape p q = 1 + sourceRatio p.nu q := by
  rfl

/--
Eq. (36): after `χ=q/(2ν)`, Eq. (33) is exactly
`xF'' + (x-χ)F' = 0`.
-/
theorem profileResidual_zero_iff_shapeODE
    {nu q x Fp Fpp : ℝ} (hnu : nu ≠ 0) :
    profileResidual nu q x Fp Fpp = 0
      ↔ x * Fpp + (x - sourceRatio nu q) * Fp = 0 := by
  unfold profileResidual sourceRatio
  constructor <;> intro h
  · field_simp [hnu]
    nlinarith
  · field_simp [hnu] at h ⊢
    nlinarith

/--
Supplementary Eq. (14) in denominator-free form:
`x P_xx = (s-1-x) P_x`.
-/
def gammaProfileSecondDerivativeRelation
    (s x Px Pxx : ℝ) : Prop :=
  x * Pxx = (s - 1 - x) * Px

/--
Supplementary Eq. (16): substituting the gamma-profile derivative relation
factors the full angular residual into the scale and source-shape compatibility
conditions.
-/
theorem preSeparationResidual_gamma_factor
    {nu a q beta betaDot s x Px Pxx : ℝ}
    (hbeta : beta ≠ 0)
    (hgamma : gammaProfileSecondDerivativeRelation s x Px Pxx) :
    preSeparationResidual nu a q beta betaDot x Px Pxx
      =
    Px * ((x / beta) * betaScaleResidual nu a beta betaDot
      + 2 * beta * (q - 2 * nu * (s - 1))) := by
  unfold gammaProfileSecondDerivativeRelation at hgamma
  unfold preSeparationResidual betaScaleResidual
  field_simp [hbeta]
  linear_combination -4 * beta ^ 2 * nu * hgamma

/-- Supplementary Eq. (17): the two compatibility conditions annihilate the residual. -/
theorem gamma_profile_residual_zero
    {nu a q beta betaDot s x Px Pxx : ℝ}
    (hbeta : beta ≠ 0)
    (hgamma : gammaProfileSecondDerivativeRelation s x Px Pxx)
    (hscale : betaScaleResidual nu a beta betaDot = 0)
    (hshape : q = 2 * nu * (s - 1)) :
    preSeparationResidual nu a q beta betaDot x Px Pxx = 0 := by
  rw [preSeparationResidual_gamma_factor hbeta hgamma, hscale, hshape]
  ring

end

end KiknadzeKrasnov
