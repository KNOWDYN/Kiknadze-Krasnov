import KiknadzeKrasnov.LagrangianTrajectories

namespace KiknadzeKrasnov

noncomputable section

/-- Local residual for manuscript Eq. (80):
`ω_t + u_r ω_r = a ω + ν(ω_rr + ω_r/r)` with
`u_r = -a r/2 + q/r`. -/
def vorticityTransportResidualLocal
    (nu a q r omega omegaT omegaR omegaRR : ℝ) : ℝ :=
  omegaT + radialVelocity a q r * omegaR - a * omega -
    nu * (omegaRR + omegaR / r)

/-- Radial derivative of the prescribed meridional velocity. -/
def radialVelocityR (a q r : ℝ) : ℝ :=
  -a / 2 - q / r ^ 2

/-- If `L=r u_theta` satisfies the differentiated angular-momentum equation,
then `ω=(1/r)L_r` satisfies the axial vorticity transport equation exactly.
This is the algebraic content of manuscript Eq. (80) on the punctured domain. -/
theorem vorticityTransport_from_differentiated_angularMomentum
    {nu a q r LT_r LR LRR LRRR : ℝ}
    (hr : r ≠ 0)
    (hL : LT_r + radialVelocityR a q r * LR +
        radialVelocity a q r * LRR =
      nu * (LRRR - LRR / r + LR / r ^ 2)) :
    vorticityTransportResidualLocal nu a q r
      (LR / r)
      (LT_r / r)
      (LRR / r - LR / r ^ 2)
      (LRRR / r - 2 * LRR / r ^ 2 + 2 * LR / r ^ 3) = 0 := by
  unfold radialVelocityR radialVelocity at hL
  unfold vorticityTransportResidualLocal radialVelocity
  field_simp [hr] at hL ⊢
  nlinarith

/-- Equivalent expanded form of manuscript Eq. (80). -/
theorem vorticityTransport_eq_zero_iff
    {nu a q r omega omegaT omegaR omegaRR : ℝ} :
    vorticityTransportResidualLocal nu a q r omega omegaT omegaR omegaRR = 0 ↔
      omegaT + radialVelocity a q r * omegaR =
        a * omega + nu * (omegaRR + omegaR / r) := by
  unfold vorticityTransportResidualLocal
  constructor <;> intro h <;> linarith

/-- Scaled residual obtained by substituting the one-mode gamma vorticity shape into Eq. (80). -/
def vorticityTransportScaledResidual
    (nu a q beta betaDot s x : ℝ) : ℝ :=
  (betaDot / beta) * (s - x) +
    (-a * x + 2 * beta * q) * ((s - 1) / x - 1) - a -
    4 * nu * beta *
      ((s ^ 2 - 2 * s * x - 2 * s + x ^ 2 + x + 1) / x)

/-- Direct one-mode verification of Eq. (80): the scaled vorticity residual vanishes under
exactly the scale Riccati law and source/profile relation, with no additional dynamical assumption. -/
theorem vorticityTransportScaledResidual_zero
    {nu a q beta betaDot s x : ℝ}
    (hbeta : beta ≠ 0) (hx : x ≠ 0)
    (hscale : betaScaleResidual nu a beta betaDot = 0)
    (hcompat : q = 2 * nu * (s - 1)) :
    vorticityTransportScaledResidual nu a q beta betaDot s x = 0 := by
  have hbdot : betaDot = a * beta - 4 * nu * beta ^ 2 :=
    betaScaleResidual_zero_iff.mp hscale
  unfold vorticityTransportScaledResidual
  rw [hbdot, hcompat]
  field_simp [hbeta, hx]
  ring

/-- Project-parameter form of the direct Eq. (80) verification. -/
theorem vorticityTransportScaledResidual_zero_for_shape
    (p : FluidParams) {a q beta betaDot x : ℝ}
    (hbeta : beta ≠ 0) (hx : x ≠ 0)
    (hscale : betaScaleResidual p.nu a beta betaDot = 0) :
    vorticityTransportScaledResidual
      p.nu a q beta betaDot (shape p q) x = 0 := by
  exact vorticityTransportScaledResidual_zero hbeta hx hscale
    (source_eq_two_nu_mul_shape_sub_one p q)

end

end KiknadzeKrasnov
