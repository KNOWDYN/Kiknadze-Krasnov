import KiknadzeKrasnov.GammaMoments

namespace KiknadzeKrasnov

noncomputable section

/-- One distributed component without central line circulation, manuscript Eq. (91). -/
def oneModeSwirl (circ s beta r : ℝ) : ℝ :=
  circ * regLowerGamma s (scaledX beta r) / (2 * Real.pi * r)

/-- Exact radial derivative of the one-mode swirl on `r>0`. -/
theorem oneModeSwirl_hasDerivAt
    {circ s beta r : ℝ} (hs : 0 < s) (hbeta : 0 < beta) (hr : 0 < r) :
    HasDerivAt (oneModeSwirl circ s beta)
      (circ / (2 * Real.pi) *
        ((regLowerGammaDensity s (scaledX beta r) * (2 * beta * r) * r -
            regLowerGamma s (scaledX beta r)) / r ^ 2)) r := by
  have hx : 0 < scaledX beta r := by
    unfold scaledX
    positivity
  have hP := regLowerGamma_scaledX_hasDerivAt (s := s) (beta := beta) hs hx
  have hquot := hP.div (hasDerivAt_id r) hr.ne'
  unfold oneModeSwirl
  convert hquot.const_mul (circ / (2 * Real.pi)) using 1 <;> ring

/-- Stationarity of the one-mode swirl is equivalent to the regularised form of Eq. (92). -/
theorem oneModeSwirl_deriv_zero_iff_scaled
    {circ s beta r : ℝ}
    (hcirc : circ ≠ 0) (hs : 0 < s) (hbeta : 0 < beta) (hr : 0 < r) :
    deriv (oneModeSwirl circ s beta) r = 0 ↔
      2 * scaledX beta r * regLowerGammaDensity s (scaledX beta r) =
        regLowerGamma s (scaledX beta r) := by
  rw [(oneModeSwirl_hasDerivAt (circ := circ) hs hbeta hr).deriv]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hr0 : r ≠ 0 := hr.ne'
  unfold scaledX
  constructor <;> intro h
  · field_simp [hcirc, hpi, hr0] at h
    nlinarith
  · field_simp [hcirc, hpi, hr0]
    unfold scaledX at h
    nlinarith

/-- Eq. (92) in the paper's unregularised lower-gamma notation. -/
theorem swirl_extremum_scaled_eq_lowerGamma
    {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    2 * x * regLowerGammaDensity s x = regLowerGamma s x ↔
      2 * x ^ s * Real.exp (-x) = lowerGamma s x := by
  unfold regLowerGammaDensity gammaKernel regLowerGamma
  have hG := gammaFn_ne_zero hs
  constructor <;> intro h
  · field_simp [hG] at h ⊢
    rw [← Real.rpow_add hx.le]
    ring_nf at h ⊢
    simpa using h
  · field_simp [hG] at h ⊢
    rw [← Real.rpow_add hx.le]
    ring_nf at h ⊢
    simpa using h

/-- The threshold `s>1/2` is exactly positivity of the small-radius swirl exponent `2s-1`. -/
theorem swirl_axis_exponent_pos_iff {s : ℝ} :
    0 < 2 * s - 1 ↔ (1 / 2 : ℝ) < s := by
  constructor <;> intro h <;> linarith

/-- Generic derivative identity behind manuscript Eq. (94).
If `Γ_r=2πrω`, then `u_theta=Γ/(2πr)` is stationary exactly when `2πr²ω=Γ`. -/
theorem swirl_stationary_iff_circulation_vorticity
    {Gamma omega r GammaR : ℝ}
    (hr : r ≠ 0) (hGammaR : GammaR = 2 * Real.pi * r * omega) :
    (GammaR * r - Gamma = 0) ↔
      2 * Real.pi * r ^ 2 * omega = Gamma := by
  rw [hGammaR]
  ring_nf
  constructor <;> intro h <;> nlinarith

end

end KiknadzeKrasnov
