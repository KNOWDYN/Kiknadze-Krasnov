import KiknadzeKrasnov.MeridionalFlow

namespace KiknadzeKrasnov

noncomputable section

/-- Pointwise residual of the radial angular-momentum advection-diffusion equation. -/
def angularMomentumResidual
    (nu ur Lt Lr LrrMinus r : ℝ) : ℝ :=
  Lt + ur * Lr - nu * LrrMinus

/-- Residual after the substitution L(r,t)=F(β(t)r²), written in the paper's scaled variables. -/
def scaledAngularMomentumResidual
    (nu a q beta betaDot x Fp Fpp : ℝ) : ℝ :=
  (betaDot / beta - a) * x * Fp + 2 * beta * q * Fp - 4 * nu * beta * x * Fpp

/-- The three chain-rule components used in the scaled angular-momentum reduction. -/
def scaledLt (beta betaDot x Fp : ℝ) : ℝ := betaDot / beta * x * Fp

def scaledLr (beta r Fp : ℝ) : ℝ := 2 * beta * r * Fp

def scaledRadialDiffusion (beta x Fpp : ℝ) : ℝ := 4 * beta * x * Fpp

/-- Algebraic reduction of the pointwise angular-momentum residual to Eq. (31). -/
theorem angularMomentumResidual_eq_scaled
    {nu a q beta betaDot r x Fp Fpp : ℝ}
    (hbeta : beta ≠ 0) (hr : r ≠ 0) :
    angularMomentumResidual nu (radialVelocity a q r)
      (scaledLt beta betaDot x Fp)
      (scaledLr beta r Fp)
      (scaledRadialDiffusion beta x Fpp) r
      = scaledAngularMomentumResidual nu a q beta betaDot x Fp Fpp := by
  unfold angularMomentumResidual scaledLt scaledLr scaledRadialDiffusion
    scaledAngularMomentumResidual radialVelocity
  field_simp [hbeta, hr]
  ring

/-- Radial-profile equation left after separation of the scale dynamics. -/
def profileResidual (nu q x Fp Fpp : ℝ) : ℝ :=
  2 * nu * x * Fpp + (2 * nu * x - q) * Fp

/-- Scale residual from the KK separation. -/
def betaScaleResidual (nu a beta betaDot : ℝ) : ℝ :=
  betaDot - a * beta + 4 * nu * beta ^ 2

/-- The scale equation and fixed-profile equation together annihilate the azimuthal residual. -/
theorem scaledAngularMomentumResidual_eq_zero
    {nu a q beta betaDot x Fp Fpp : ℝ}
    (hbeta : beta ≠ 0)
    (hscale : betaScaleResidual nu a beta betaDot = 0)
    (hprofile : profileResidual nu q x Fp Fpp = 0) :
    scaledAngularMomentumResidual nu a q beta betaDot x Fp Fpp = 0 := by
  unfold betaScaleResidual at hscale
  unfold profileResidual at hprofile
  unfold scaledAngularMomentumResidual
  field_simp [hbeta]
  nlinarith

/-- A fixed nontrivial radial profile forces the source coefficient to be time-independent.

If the same profile derivative F' is nonzero at one witness x and satisfies the separated
profile equation for two source values, those source values are equal.
-/
theorem source_eq_of_fixed_nontrivial_profile
    {nu x Fp Fpp q₁ q₂ : ℝ}
    (hFp : Fp ≠ 0)
    (h₁ : profileResidual nu q₁ x Fp Fpp = 0)
    (h₂ : profileResidual nu q₂ x Fp Fpp = 0) :
    q₁ = q₂ := by
  unfold profileResidual at h₁ h₂
  have h : (q₁ - q₂) * Fp = 0 := by
    nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hFp)

/-- Rewriting the profile equation with χ=q/(2ν) gives xF''+(x-χ)F'=0. -/
theorem profileResidual_iff_shapeODE
    {nu q x Fp Fpp : ℝ} (hnu : nu ≠ 0) :
    profileResidual nu q x Fp Fpp = 0 ↔
      x * Fpp + (x - q / (2 * nu)) * Fp = 0 := by
  unfold profileResidual
  constructor <;> intro h
  · field_simp [hnu]
    nlinarith
  · field_simp [hnu] at h ⊢
    nlinarith

/-- Incomplete-gamma second-derivative identity in the algebraic form used by the residual audit. -/
def gammaSecondDerivativeRelation (s x Px Pxx : ℝ) : Prop :=
  x * Pxx = (s - 1 - x) * Px

/-- Under the gamma profile identity, the azimuthal residual factors into the two compatibility residuals. -/
theorem scaledResidual_gamma_factor
    {nu a q beta betaDot s x Px Pxx : ℝ}
    (hbeta : beta ≠ 0)
    (hx : x ≠ 0)
    (hgamma : gammaSecondDerivativeRelation s x Px Pxx) :
    scaledAngularMomentumResidual nu a q beta betaDot x Px Pxx
      = Px * ((x / beta) * betaScaleResidual nu a beta betaDot
          + 2 * beta * (q - 2 * nu * (s - 1))) := by
  unfold gammaSecondDerivativeRelation at hgamma
  unfold scaledAngularMomentumResidual betaScaleResidual
  field_simp [hbeta, hx] at hgamma ⊢
  nlinarith

end

end KiknadzeKrasnov
