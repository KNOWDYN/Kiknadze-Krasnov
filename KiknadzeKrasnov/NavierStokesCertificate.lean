import KiknadzeKrasnov.PressureField

namespace KiknadzeKrasnov

noncomputable section

/-!
Pointwise exact Navier--Stokes certificate for the source-bearing one-mode KK
field, with optional constant central line circulation.  The four residuals
correspond to manuscript Eqs. (69)--(77) and Supplementary Eqs. (6)--(17).
-/

/-- One distributed KK mode plus the optional constant central line circulation. -/
def oneModeSwirlWithLine
    (gammaLine circ s beta r : ℝ) : ℝ :=
  centralLineSwirl gammaLine r + distributedSwirl circ s beta r

/-- Angular momentum of the same one-mode-plus-line field. -/
def oneModeAngularMomentumWithLine
    (gammaLine circ s beta r : ℝ) : ℝ :=
  gammaLine / (2 * Real.pi) + distributedAngularMomentum circ s beta r

/-- On r>0 the angular momentum is exactly r u_theta for the actual swirl. -/
theorem oneModeAngularMomentumWithLine_eq_radius_mul_swirl
    {gammaLine circ s beta r : ℝ} (hr : PuncturedRadius r) :
    oneModeAngularMomentumWithLine gammaLine circ s beta r
      = r * oneModeSwirlWithLine gammaLine circ s beta r := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  rw [show distributedAngularMomentum circ s beta r =
      r * distributedSwirl circ s beta r from
        distributedAngularMomentum_eq_radius_mul_swirl hr]
  unfold oneModeAngularMomentumWithLine oneModeSwirlWithLine centralLineSwirl
  field_simp [hr0, Real.pi_ne_zero]
  ring

/-- The actual continuity residual of the meridional KK field. -/
def continuityResidualActual (a b q r z : ℝ) : ℝ :=
  deriv (fun rho => rho * radialVelocity a q rho) r / r
    + deriv (fun zeta => axialVelocity a b zeta) z

/-- Eq. (71): the actual continuity residual vanishes on the punctured domain. -/
theorem continuityResidualActual_zero
    {a b q r z : ℝ} (hr : PuncturedRadius r) :
    continuityResidualActual a b q r z = 0 := by
  exact meridional_continuity hr

/-- Actual radial vector-Laplacian coefficient, using the certified first derivative formula. -/
def radialViscousOperatorActual (a q r : ℝ) : ℝ :=
  deriv (radialVelocityRadialDerivative a q) r
    + deriv (radialVelocity a q) r / r
    - radialVelocity a q r / r ^ 2

/-- Supplementary Eqs. (8)--(9): the actual radial viscous operator vanishes. -/
theorem radialViscousOperatorActual_zero
    {a q r : ℝ} (hr : PuncturedRadius r) :
    radialViscousOperatorActual a q r = 0 := by
  rw [(radialVelocityRadialDerivative_hasDerivAt hr).deriv]
  rw [(radialVelocity_radial_hasDerivAt hr).deriv]
  exact radial_viscous_operator_zero hr

/--
Actual radial momentum residual, including the derivative of the reconstructed
pressure field rather than a preassigned pressure-gradient symbol.
-/
def radialMomentumResidualActual
    (p : FluidParams) (a b : ℝ → ℝ)
    (aDot bDot q p0 t r z : ℝ)
    (Pi uTheta : ℝ → ℝ) : ℝ :=
  deriv (fun tau => radialVelocity (a tau) q r) t
    + radialVelocity (a t) q r * deriv (radialVelocity (a t) q) r
    - uTheta r ^ 2 / r
    + deriv
        (fun rr =>
          pressureFieldAtTime p.rho (a t) aDot (b t) bDot q p0 Pi rr z) r
        / p.rho
    - p.nu * radialViscousOperatorActual (a t) q r

/-- Eq. (72), radial part: the actual radial momentum residual vanishes. -/
theorem radialMomentumResidualActual_zero
    (p : FluidParams)
    {a b : ℝ → ℝ} {aDot bDot q p0 t r z : ℝ}
    {Pi uTheta : ℝ → ℝ}
    (ha : HasDerivAt a aDot t)
    (hr : PuncturedRadius r)
    (hPi : HasDerivAt Pi (uTheta r ^ 2 / r) r) :
    radialMomentumResidualActual p a b aDot bDot q p0 t r z Pi uTheta = 0 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  unfold radialMomentumResidualActual
  rw [(radialVelocity_time_hasDerivAt (q := q) (r := r) ha).deriv]
  rw [(radialVelocity_radial_hasDerivAt (a := a t) (q := q) hr).deriv]
  rw [pressureFieldAtTime_radial_deriv_eq p.rho_ne_zero hr hPi]
  rw [radialViscousOperatorActual_zero hr]
  rw [radial_convective_acceleration hr]
  unfold radialVelocityTimeDerivative radialPressureGradientOverRho
  field_simp [hr0]
  ring

/--
Actual axial viscous operator from Eq. (17).  The first two derivatives are
radial derivatives of a radial-constant field; the final term is the second
z derivative of the affine axial velocity.
-/
def axialViscousOperatorActual (a b r z : ℝ) : ℝ :=
  deriv (fun rr : ℝ => deriv (fun _ss : ℝ => axialVelocity a b z) rr) r
    + deriv (fun _rr : ℝ => axialVelocity a b z) r / r
    + deriv
        (fun zz : ℝ => deriv (fun eta : ℝ => axialVelocity a b eta) zz) z

/-- The actual axial viscous operator vanishes identically. -/
theorem axialViscousOperatorActual_zero (a b r z : ℝ) :
    axialViscousOperatorActual a b r z = 0 := by
  have hrad1 :
      (fun rr : ℝ => deriv (fun _ss : ℝ => axialVelocity a b z) rr)
        = (fun _rr : ℝ => 0) := by
    funext rr
    exact (hasDerivAt_const rr (axialVelocity a b z)).deriv
  have hz1 :
      (fun zz : ℝ => deriv (fun eta : ℝ => axialVelocity a b eta) zz)
        = (fun _zz : ℝ => a) := by
    funext zz
    exact axialVelocity_deriv a b zz
  unfold axialViscousOperatorActual
  rw [hrad1, hz1]
  simp

/-- Actual axial momentum residual, including all radial and axial viscous terms. -/
def axialMomentumResidualActual
    (p : FluidParams) (a b : ℝ → ℝ)
    (aDot bDot q p0 t r z : ℝ)
    (Pi : ℝ → ℝ) : ℝ :=
  deriv (fun tau => axialVelocity (a tau) (b tau) z) t
    + radialVelocity (a t) q r *
        deriv (fun _rr : ℝ => axialVelocity (a t) (b t) z) r
    + axialVelocity (a t) (b t) z *
        deriv (fun zz => axialVelocity (a t) (b t) zz) z
    + deriv
        (fun zz =>
          pressureFieldAtTime p.rho (a t) aDot (b t) bDot q p0 Pi r zz) z
        / p.rho
    - p.nu * axialViscousOperatorActual (a t) (b t) r z

/-- Eq. (72), axial part: the actual axial momentum residual vanishes. -/
theorem axialMomentumResidualActual_zero
    (p : FluidParams)
    {a b : ℝ → ℝ} {aDot bDot q p0 t r z : ℝ}
    {Pi : ℝ → ℝ}
    (ha : HasDerivAt a aDot t)
    (hb : HasDerivAt b bDot t) :
    axialMomentumResidualActual p a b aDot bDot q p0 t r z Pi = 0 := by
  unfold axialMomentumResidualActual
  rw [(axialVelocity_time_hasDerivAt ha hb).deriv]
  have hrad :
      deriv (fun _rr : ℝ => axialVelocity (a t) (b t) z) r = 0 :=
    (hasDerivAt_const r (axialVelocity (a t) (b t) z)).deriv
  rw [hrad]
  rw [axialVelocity_deriv]
  rw [pressureFieldAtTime_axial_deriv_eq p.rho_ne_zero]
  rw [axialViscousOperatorActual_zero]
  unfold axialVelocityTimeDerivative axialPressureGradientOverRho axialVelocity
  ring

/-- Second profile density P_xx on x>0. -/
def regLowerGammaSecondDensity (s x : ℝ) : ℝ :=
  ((s - 1) / x - 1) * regLowerGammaDensity s x

/-- The actual gamma-profile second density satisfies Supplementary Eq. (14). -/
theorem regLowerGammaSecondDensity_relation
    {s x : ℝ} (hx : 0 < x) :
    gammaProfileSecondDerivativeRelation s x
      (regLowerGammaDensity s x) (regLowerGammaSecondDensity s x) := by
  unfold gammaProfileSecondDerivativeRelation regLowerGammaSecondDensity
  field_simp [hx.ne']
  ring

/-- Actual time-derivative coefficient of one distributed angular momentum mode. -/
def distributedAngularMomentumTimeDerivative
    (circ s beta betaDot r : ℝ) : ℝ :=
  circ / (2 * Real.pi) * regLowerGammaDensity s (scaledX beta r)
    * (betaDot * r ^ 2)

/-- Actual first radial derivative coefficient of one distributed angular momentum mode. -/
def distributedAngularMomentumRadialDerivative
    (circ s beta r : ℝ) : ℝ :=
  circ / (2 * Real.pi) * regLowerGammaDensity s (scaledX beta r)
    * (2 * beta * r)

/-- Actual second radial derivative coefficient of one distributed angular momentum mode. -/
def distributedAngularMomentumSecondRadialDerivative
    (circ s beta r : ℝ) : ℝ :=
  circ / (2 * Real.pi) *
    (regLowerGammaSecondDensity s (scaledX beta r) * (2 * beta * r) ^ 2
      + regLowerGammaDensity s (scaledX beta r) * (2 * beta))

/-- The time coefficient above is the derivative of the actual one-mode angular momentum. -/
theorem distributedAngularMomentum_time_hasDerivAt_actual
    {beta : ℝ → ℝ} {betaDot circ s t r : ℝ}
    (hs : 0 < s) (hbetaPos : 0 < beta t) (hr : PuncturedRadius r)
    (hbeta : HasDerivAt beta betaDot t) :
    HasDerivAt
      (fun tau => distributedAngularMomentum circ s (beta tau) r)
      (distributedAngularMomentumTimeDerivative
        circ s (beta t) betaDot r) t := by
  have hx : 0 < scaledX (beta t) r := by
    unfold scaledX
    exact mul_pos hbetaPos (pow_pos hr 2)
  have hxTime :
      HasDerivAt (fun tau => scaledX (beta tau) r)
        (betaDot * r ^ 2) t := by
    simpa [scaledX] using hbeta.mul_const (r ^ 2)
  have hP := (regLowerGamma_hasDerivAt hs hx).comp t hxTime
  have h := hP.const_mul (circ / (2 * Real.pi))
  unfold distributedAngularMomentum distributedAngularMomentumTimeDerivative
    regLowerGammaDensity
  simpa only [Function.comp_apply, mul_assoc] using h

/-- The named first radial coefficient is the derivative of the actual mode. -/
theorem distributedAngularMomentum_radial_hasDerivAt_actual
    {circ s beta r : ℝ}
    (hs : 0 < s) (hbetaPos : 0 < beta) (hr : PuncturedRadius r) :
    HasDerivAt (distributedAngularMomentum circ s beta)
      (distributedAngularMomentumRadialDerivative circ s beta r) r := by
  have hx : 0 < scaledX beta r := by
    unfold scaledX
    exact mul_pos hbetaPos (pow_pos hr 2)
  simpa [distributedAngularMomentumRadialDerivative, mul_assoc] using
    (distributedAngularMomentum_hasDerivAt (circ := circ) hs hx)

/-- The named second radial coefficient differentiates the certified first derivative. -/
theorem distributedAngularMomentumRadialDerivative_hasDerivAt
    {circ s beta r : ℝ}
    (hs : 0 < s) (hbetaPos : 0 < beta) (hr : PuncturedRadius r) :
    HasDerivAt (distributedAngularMomentumRadialDerivative circ s beta)
      (distributedAngularMomentumSecondRadialDerivative circ s beta r) r := by
  have hx : 0 < scaledX beta r := by
    unfold scaledX
    exact mul_pos hbetaPos (pow_pos hr 2)
  have hDensity :=
    (regLowerGammaDensity_hasDerivAt hs hx).comp r (scaledX_hasDerivAt beta r)
  have hLinear : HasDerivAt (fun rho : ℝ => 2 * beta * rho) (2 * beta) r := by
    simpa using (hasDerivAt_id r).const_mul (2 * beta)
  have hProduct := hDensity.mul hLinear
  have hScaled := hProduct.const_mul (circ / (2 * Real.pi))
  unfold distributedAngularMomentumRadialDerivative
    distributedAngularMomentumSecondRadialDerivative
    regLowerGammaSecondDensity
  simp only [Function.comp_apply] at hScaled
  convert hScaled using 1
  · funext rho
    ring
  · ring

/--
Actual angular-momentum residual assembled from certified temporal and radial
derivative coefficients of the one distributed mode.
-/
def distributedAngularMomentumResidualActual
    (nu a q beta betaDot circ s r : ℝ) : ℝ :=
  distributedAngularMomentumTimeDerivative circ s beta betaDot r
    + radialVelocity a q r *
        distributedAngularMomentumRadialDerivative circ s beta r
    - nu *
        (distributedAngularMomentumSecondRadialDerivative circ s beta r
          - distributedAngularMomentumRadialDerivative circ s beta r / r)

/-- The actual one-mode residual reduces exactly to the Pass-3B separated residual. -/
theorem distributedAngularMomentumResidualActual_eq_preSeparation
    {nu a q beta betaDot circ s r : ℝ}
    (hbeta : 0 < beta) (hr : PuncturedRadius r) :
    distributedAngularMomentumResidualActual
      nu a q beta betaDot circ s r
      =
    (circ / (2 * Real.pi)) *
      preSeparationResidual nu a q beta betaDot (scaledX beta r)
        (regLowerGammaDensity s (scaledX beta r))
        (regLowerGammaSecondDensity s (scaledX beta r)) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hx : 0 < scaledX beta r := by
    unfold scaledX
    exact mul_pos hbeta (pow_pos hr 2)
  unfold distributedAngularMomentumResidualActual
    distributedAngularMomentumTimeDerivative
    distributedAngularMomentumRadialDerivative
    distributedAngularMomentumSecondRadialDerivative
    preSeparationResidual radialVelocity regLowerGammaSecondDensity scaledX
  field_simp [hr0, hbeta.ne', hx.ne', Real.pi_ne_zero]
  ring

/-- The actual one-mode angular-momentum residual vanishes under the KK compatibility equations. -/
theorem distributedAngularMomentumResidualActual_zero
    {nu a q beta betaDot circ s r : ℝ}
    (hbeta : 0 < beta) (hr : PuncturedRadius r)
    (hscale : betaScaleResidual nu a beta betaDot = 0)
    (hshape : q = 2 * nu * (s - 1)) :
    distributedAngularMomentumResidualActual
      nu a q beta betaDot circ s r = 0 := by
  have hx : 0 < scaledX beta r := by
    unfold scaledX
    exact mul_pos hbeta (pow_pos hr 2)
  have hgamma :=
    regLowerGammaSecondDensity_relation (s := s) hx
  have hpre :=
    gamma_profile_residual_zero
      (nu := nu) (a := a) (q := q) (beta := beta)
      (betaDot := betaDot) (s := s) (x := scaledX beta r)
      (Px := regLowerGammaDensity s (scaledX beta r))
      (Pxx := regLowerGammaSecondDensity s (scaledX beta r))
      hbeta.ne' hgamma hscale hshape
  rw [distributedAngularMomentumResidualActual_eq_preSeparation hbeta hr, hpre]
  ring

/--
R_theta in velocity units.  Pass 3B proves on r>0 that the angular-momentum
residual is exactly r times the z-independent azimuthal velocity residual.
The constant line-circulation angular momentum is constant, so it contributes
zero to this residual.
-/
def azimuthalMomentumResidualActual
    (nu a q beta betaDot circ s r : ℝ) : ℝ :=
  distributedAngularMomentumResidualActual
    nu a q beta betaDot circ s r / r

/-- Eq. (77), azimuthal part: the actual one-mode-plus-constant-line residual vanishes. -/
theorem azimuthalMomentumResidualActual_zero
    {nu a q beta betaDot circ s r : ℝ}
    (hbeta : 0 < beta) (hr : PuncturedRadius r)
    (hscale : betaScaleResidual nu a beta betaDot = 0)
    (hshape : q = 2 * nu * (s - 1)) :
    azimuthalMomentumResidualActual nu a q beta betaDot circ s r = 0 := by
  rw [azimuthalMomentumResidualActual,
    distributedAngularMomentumResidualActual_zero hbeta hr hscale hshape]
  simp

/-- Constant line angular momentum has zero time derivative. -/
theorem centralLineAngularMomentum_time_hasDerivAt_zero
    (gammaLine t : ℝ) :
    HasDerivAt (fun _tau : ℝ => gammaLine / (2 * Real.pi)) 0 t :=
  hasDerivAt_const t _

/--
The actual time derivative of total one-mode-plus-line angular momentum equals
the distributed-mode coefficient; the constant line term contributes zero.
-/
theorem oneModeAngularMomentumWithLine_time_hasDerivAt
    {beta : ℝ → ℝ} {betaDot gammaLine circ s t r : ℝ}
    (hs : 0 < s) (hbetaPos : 0 < beta t) (hr : PuncturedRadius r)
    (hbeta : HasDerivAt beta betaDot t) :
    HasDerivAt
      (fun tau =>
        oneModeAngularMomentumWithLine gammaLine circ s (beta tau) r)
      (distributedAngularMomentumTimeDerivative
        circ s (beta t) betaDot r) t := by
  have hline := centralLineAngularMomentum_time_hasDerivAt_zero gammaLine t
  have hdist :=
    distributedAngularMomentum_time_hasDerivAt_actual
      (circ := circ) (s := s) (t := t) (r := r)
      hs hbetaPos hr hbeta
  unfold oneModeAngularMomentumWithLine
  convert hline.add hdist using 1
  ring

/--
The actual first radial derivative of total one-mode-plus-line angular
momentum equals the distributed-mode radial coefficient.
-/
theorem oneModeAngularMomentumWithLine_radial_hasDerivAt
    {gammaLine circ s beta r : ℝ}
    (hs : 0 < s) (hbetaPos : 0 < beta) (hr : PuncturedRadius r) :
    HasDerivAt
      (oneModeAngularMomentumWithLine gammaLine circ s beta)
      (distributedAngularMomentumRadialDerivative circ s beta r) r := by
  have hline : HasDerivAt
      (fun _rho : ℝ => gammaLine / (2 * Real.pi)) 0 r :=
    hasDerivAt_const r _
  have hdist :=
    distributedAngularMomentum_radial_hasDerivAt_actual
      (circ := circ) (s := s) (beta := beta) hs hbetaPos hr
  unfold oneModeAngularMomentumWithLine
  convert hline.add hdist using 1
  ring

/--
Complete pointwise certificate answering whether the field containing the
Pass-4 material surface satisfies the axisymmetric incompressible
Navier--Stokes equations.  The pressure potential is the actual swirl
integral from Eq. (58); `hPi` is discharged by
`swirlPressurePotential_hasDerivAt` under its standard FTC hypotheses.
-/
theorem kk_exact_navier_stokes_certificate
    (p : FluidParams)
    {a b beta : ℝ → ℝ}
    {aDot bDot betaDot q gammaLine circ p0 rRef t r z : ℝ}
    (hann : AnnularSourceBranch p q)
    (ha : HasDerivAt a aDot t)
    (hb : HasDerivAt b bDot t)
    (hbeta : HasDerivAt beta betaDot t)
    (hbetaPos : 0 < beta t)
    (hscale : betaScaleResidual p.nu (a t) (beta t) betaDot = 0)
    (hr : PuncturedRadius r)
    (hPi :
      let uTheta := oneModeSwirlWithLine
        gammaLine circ (shape p q) (beta t)
      HasDerivAt
        (swirlPressurePotential uTheta rRef)
        (uTheta r ^ 2 / r) r) :
    let s := shape p q
    let uTheta := oneModeSwirlWithLine gammaLine circ s (beta t)
    let Pi := swirlPressurePotential uTheta rRef
    continuityResidualActual (a t) (b t) q r z = 0
      ∧ radialMomentumResidualActual
          p a b aDot bDot q p0 t r z Pi uTheta = 0
      ∧ azimuthalMomentumResidualActual
          p.nu (a t) q (beta t) betaDot circ s r = 0
      ∧ axialMomentumResidualActual
          p a b aDot bDot q p0 t r z Pi = 0 := by
  dsimp
  have hs : 1 < shape p q := hann
  have hshape : q = 2 * p.nu * (shape p q - 1) :=
    source_eq_two_nu_mul_shape_sub_one p q
  refine ⟨continuityResidualActual_zero hr, ?_⟩
  refine ⟨radialMomentumResidualActual_zero p ha hr hPi, ?_⟩
  refine ⟨azimuthalMomentumResidualActual_zero hbetaPos hr hscale hshape, ?_⟩
  exact axialMomentumResidualActual_zero p ha hb

end

end KiknadzeKrasnov
