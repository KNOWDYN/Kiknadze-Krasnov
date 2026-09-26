import KiknadzeKrasnov.MeridionalFlow
import KiknadzeKrasnov.ScaleDynamics
import KiknadzeKrasnov.SpecialFunctions

namespace KiknadzeKrasnov

noncomputable section

/-- A unit-amplitude KK angular-momentum profile. Circulation prefactors are constant and linear. -/
def kkProfile (s beta r : ℝ) : ℝ :=
  regLowerGamma s (scaledX beta r)

/-- Closed-form time derivative coefficient for a fixed radial point. -/
def kkProfileTimeDeriv (s beta betaDot r : ℝ) : ℝ :=
  betaDot * r ^ 2 * regLowerGammaPrime s (scaledX beta r)

/-- Closed-form radial derivative coefficient. -/
def kkProfileRadialDeriv (s beta r : ℝ) : ℝ :=
  2 * beta * r * regLowerGammaPrime s (scaledX beta r)

/-- Closed-form cylindrical radial viscous operator L_rr - L_r/r. -/
def kkProfileRadialViscous (s beta r : ℝ) : ℝ :=
  4 * beta * scaledX beta r * regLowerGammaSecond s (scaledX beta r)

/-- Radial derivative of the fixed KK profile. -/
theorem kkProfile_hasDerivAt_radius {s beta r : ℝ}
    (hs : 0 < s) (hx : 0 < scaledX beta r) :
    HasDerivAt (kkProfile s beta) (kkProfileRadialDeriv s beta r) r := by
  have hinner : HasDerivAt (fun y : ℝ => scaledX beta y) (2 * beta * r) r := by
    unfold scaledX
    convert ((hasDerivAt_id r).pow 2).const_mul beta using 1 <;> ring
  have houter := regLowerGamma_hasDerivAt_prime hs hx
  convert houter.comp r hinner using 1 <;> ring

/-- Time derivative of the profile when the scale is differentiable. -/
theorem kkProfile_hasDerivAt_time
    {s r t : ℝ} {beta : ℝ → ℝ} {betaDot : ℝ}
    (hs : 0 < s) (hx : 0 < scaledX (beta t) r)
    (hbeta : HasDerivAt beta betaDot t) :
    HasDerivAt (fun tau => kkProfile s (beta tau) r)
      (kkProfileTimeDeriv s (beta t) betaDot r) t := by
  have hinner : HasDerivAt (fun tau => scaledX (beta tau) r)
      (betaDot * r ^ 2) t := by
    unfold scaledX
    simpa using hbeta.mul_const (r ^ 2)
  have houter := regLowerGamma_hasDerivAt_prime hs hx
  convert houter.comp t hinner using 1 <;> ring

/-- Derivative of L_r, used to certify the cylindrical viscous operator. -/
theorem kkProfileRadialDeriv_hasDerivAt
    {s beta r : ℝ} (hs : 0 < s) (hx : 0 < scaledX beta r) :
    HasDerivAt (kkProfileRadialDeriv s beta)
      (2 * beta * regLowerGammaPrime s (scaledX beta r) +
       4 * beta ^ 2 * r ^ 2 * regLowerGammaSecond s (scaledX beta r)) r := by
  have hinner : HasDerivAt (fun y : ℝ => scaledX beta y) (2 * beta * r) r := by
    unfold scaledX
    convert ((hasDerivAt_id r).pow 2).const_mul beta using 1 <;> ring
  have hprime : HasDerivAt
      (fun y => regLowerGammaPrime s (scaledX beta y))
      (regLowerGammaSecond s (scaledX beta r) * (2 * beta * r)) r :=
    (regLowerGammaPrime_hasDerivAt hs hx).comp r hinner
  have hlinear : HasDerivAt (fun y : ℝ => 2 * beta * y) (2 * beta) r := by
    convert (hasDerivAt_id r).const_mul (2 * beta) using 1 <;> ring
  convert hlinear.mul hprime using 1 <;> ring

/-- The derivative formulas reduce L_rr - L_r/r to Eq. (30). -/
theorem kkProfile_radial_viscous_identity
    {s beta r : ℝ} (hr : r ≠ 0) :
    (2 * beta * regLowerGammaPrime s (scaledX beta r) +
       4 * beta ^ 2 * r ^ 2 * regLowerGammaSecond s (scaledX beta r))
      - kkProfileRadialDeriv s beta r / r =
    kkProfileRadialViscous s beta r := by
  unfold kkProfileRadialDeriv kkProfileRadialViscous scaledX
  field_simp [hr]
  ring

/-- The separated profile equation in the dimensional q, nu notation of Eq. (33). -/
theorem kkProfile_separated_ode
    {nu q s x : ℝ} (hs : 0 < s) (hx : 0 < x)
    (hq : q = 2 * nu * (s - 1)) :
    2 * nu * x * regLowerGammaSecond s x +
      (2 * nu * x - q) * regLowerGammaPrime s x = 0 := by
  have hp := regLowerGamma_profile_ode hs hx
  rw [hq]
  nlinarith

/-- A nontrivial fixed profile cannot satisfy the separated equation with two different q values. -/
theorem fixedProfile_source_unique
    {nu x fp fpp q1 q2 : ℝ} (hfp : fp ≠ 0)
    (h1 : 2 * nu * x * fpp + (2 * nu * x - q1) * fp = 0)
    (h2 : 2 * nu * x * fpp + (2 * nu * x - q2) * fp = 0) :
    q1 = q2 := by
  have h : (q2 - q1) * fp = 0 := by
    nlinarith [h1, h2]
  rcases mul_eq_zero.mp h with hq | hp
  · linarith
  · exact (hfp hp).elim

/-- Pointwise angular-momentum PDE residual for a unit-amplitude distributed mode. -/
def angularMomentumResidual
    (nu a q beta betaDot s r : ℝ) : ℝ :=
  kkProfileTimeDeriv s beta betaDot r +
    radialVelocity a q r * kkProfileRadialDeriv s beta r -
    nu * kkProfileRadialViscous s beta r

/-- The incomplete-gamma mode satisfies the angular-momentum equation under Eqs. (32),(35). -/
theorem angularMomentumResidual_zero
    {nu a q beta betaDot s r : ℝ}
    (hr : r ≠ 0) (hbeta : beta ≠ 0)
    (hs : 0 < s) (hx : 0 < scaledX beta r)
    (hscale : scaleResidual nu a beta betaDot = 0)
    (hq : q = 2 * nu * (s - 1)) :
    angularMomentumResidual nu a q beta betaDot s r = 0 := by
  have hp := kkProfile_separated_ode (nu := nu) (q := q) (s := s)
    (x := scaledX beta r) hs hx hq
  unfold angularMomentumResidual kkProfileTimeDeriv kkProfileRadialDeriv
    kkProfileRadialViscous radialVelocity scaledX scaleResidual at *
  field_simp [hr] at *
  nlinarith [hp]

/-- A constant central line-circulation contribution has zero angular-momentum residual. -/
theorem constantAngularMomentum_residual_zero (nu a q c r : ℝ) :
    0 + radialVelocity a q r * 0 - nu * 0 = 0 := by
  ring

end

end KiknadzeKrasnov
