import KiknadzeKrasnov.VorticityAnalysis

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
  unfold vorticityTransportResidualLocal radialVelocityR radialVelocity
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

end

end KiknadzeKrasnov
