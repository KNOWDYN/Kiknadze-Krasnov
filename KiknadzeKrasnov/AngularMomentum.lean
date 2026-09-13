import KiknadzeKrasnov.GammaProfile

namespace KiknadzeKrasnov

noncomputable section

/-- Separated fixed-profile ODE residual after imposing the KK scale equation. -/
def separatedProfileResidual (nu q x px pxx : ℝ) : ℝ :=
  2 * nu * x * pxx + (2 * nu * x - q) * px

/-- A non-trivial fixed profile forces the source coefficient to be time independent. -/
theorem fixedProfile_forces_q_constant {nu q₁ q₂ x px pxx : ℝ}
    (hpx : px ≠ 0)
    (h₁ : separatedProfileResidual nu q₁ x px pxx = 0)
    (h₂ : separatedProfileResidual nu q₂ x px pxx = 0) :
    q₁ = q₂ := by
  have hmul : q₁ * px = q₂ * px := by
    unfold separatedProfileResidual at h₁ h₂
    linarith
  exact mul_right_cancel₀ hpx hmul

/-- The source's one-mode angular-momentum residual after the chain-rule substitutions. -/
def gammaAngularResidual
    (nu a q beta betaDot s x : ℝ) : ℝ :=
  ((betaDot / beta - a) * x + 2 * beta * q) * regLowerGammaDensity s x -
    4 * nu * beta * x *
      (((s - 1) / x - 1) * regLowerGammaDensity s x)

/-- The residual factor displayed in the manuscript and supplementary material. -/
def angularResidualFactor
    (nu a q beta betaDot s x : ℝ) : ℝ :=
  x / beta * scaleResidual nu a beta betaDot +
    2 * beta * (q - 2 * nu * (s - 1))

/-- Exact algebraic factorisation of the incomplete-gamma angular-momentum residual. -/
theorem gammaAngularResidual_factorisation
    {nu a q beta betaDot s x : ℝ}
    (hbeta : beta ≠ 0) (hx : x ≠ 0) :
    gammaAngularResidual nu a q beta betaDot s x =
      regLowerGammaDensity s x *
        angularResidualFactor nu a q beta betaDot s x := by
  unfold gammaAngularResidual angularResidualFactor scaleResidual
  field_simp [hbeta, hx]
  ring

/-- Equation (75)'s factor vanishes under the scale ODE and the project shape relation. -/
theorem angularResidualFactor_zero
    (p : FluidParams) {a q beta betaDot x : ℝ}
    (hscale : scaleResidual p.nu a beta betaDot = 0) :
    angularResidualFactor p.nu a q beta betaDot (shape p q) x = 0 := by
  unfold angularResidualFactor
  rw [hscale]
  have hcompat : q - 2 * p.nu * (shape p q - 1) = 0 := by
    exact sub_eq_zero.mpr (source_eq_two_nu_mul_shape_sub_one p q)
  rw [hcompat]
  ring

/-- A single finite-circulation gamma mode satisfies the angular-momentum equation locally. -/
theorem gammaAngularResidual_zero
    (p : FluidParams) {a q beta betaDot x : ℝ}
    (hbeta : beta ≠ 0) (hx : x ≠ 0)
    (hscale : scaleResidual p.nu a beta betaDot = 0) :
    gammaAngularResidual p.nu a q beta betaDot (shape p q) x = 0 := by
  rw [gammaAngularResidual_factorisation hbeta hx,
    angularResidualFactor_zero p hscale]
  ring

/-- Local cylindrical azimuthal Navier--Stokes residual, with the `z` derivatives absent. -/
def azimuthalResidualLocal
    (nu ur r uTheta uThetaT uThetaR uThetaRR : ℝ) : ℝ :=
  uThetaT + ur * uThetaR + ur * uTheta / r -
    nu * (uThetaRR + uThetaR / r - uTheta / r ^ 2)

/-- Local angular-momentum residual corresponding to `L=r u_theta`. -/
def angularMomentumResidualLocal
    (nu ur r LT LR LRR : ℝ) : ℝ :=
  LT + ur * LR - nu * (LRR - LR / r)

/-- Multiplying the azimuthal residual by `r` gives the angular-momentum residual exactly. -/
theorem angularMomentum_azimuthal_identity
    {nu ur r uTheta uThetaT uThetaR uThetaRR : ℝ} (hr : r ≠ 0) :
    angularMomentumResidualLocal nu ur r
      (r * uThetaT)
      (uTheta + r * uThetaR)
      (2 * uThetaR + r * uThetaRR) =
    r * azimuthalResidualLocal nu ur r
      uTheta uThetaT uThetaR uThetaRR := by
  unfold angularMomentumResidualLocal azimuthalResidualLocal
  field_simp [hr]
  ring

/-- Vanishing angular-momentum residual is therefore equivalent to vanishing azimuthal residual on `r>0`. -/
theorem azimuthalResidual_zero_of_angularMomentum
    {nu ur r uTheta uThetaT uThetaR uThetaRR : ℝ}
    (hr : r ≠ 0)
    (hL : angularMomentumResidualLocal nu ur r
      (r * uThetaT)
      (uTheta + r * uThetaR)
      (2 * uThetaR + r * uThetaRR) = 0) :
    azimuthalResidualLocal nu ur r
      uTheta uThetaT uThetaR uThetaRR = 0 := by
  have h := angularMomentum_azimuthal_identity
    (nu := nu) (ur := ur) (r := r)
    (uTheta := uTheta) (uThetaT := uThetaT)
    (uThetaR := uThetaR) (uThetaRR := uThetaRR) hr
  rw [hL] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hr

end

end KiknadzeKrasnov
