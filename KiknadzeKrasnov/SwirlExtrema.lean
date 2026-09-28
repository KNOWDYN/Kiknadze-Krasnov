import KiknadzeKrasnov.GammaMoments

namespace KiknadzeKrasnov

noncomputable section

open scoped BigOperators

/-- One distributed component without central line circulation, manuscript Eq. (91). -/
def oneModeSwirl (circ s beta r : ℝ) : ℝ :=
  (circ / (2 * Real.pi)) *
    (regLowerGamma s (scaledX beta r) / r)

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
  change HasDerivAt
    (fun y => (circ / (2 * Real.pi)) *
      (regLowerGamma s (scaledX beta y) / y))
    (circ / (2 * Real.pi) *
      ((regLowerGammaDensity s (scaledX beta r) * (2 * beta * r) * r -
          regLowerGamma s (scaledX beta r)) / r ^ 2)) r
  simpa only [Pi.div_apply, id_eq, one_mul, mul_one] using
    hquot.const_mul (circ / (2 * Real.pi))

/-- Stationarity of the one-mode swirl is equivalent to the regularised form of Eq. (92). -/
theorem oneModeSwirl_deriv_zero_iff_scaled
    {circ s beta r : ℝ}
    (hcirc : circ ≠ 0) (hs : 0 < s) (hbeta : 0 < beta) (hr : 0 < r) :
    deriv (oneModeSwirl circ s beta) r = 0 ↔
      2 * scaledX beta r * regLowerGammaDensity s (scaledX beta r) =
        regLowerGamma s (scaledX beta r) := by
  rw [(oneModeSwirl_hasDerivAt (circ := circ) hs hbeta hr).deriv]
  have hconst : circ / (2 * Real.pi) ≠ 0 := by
    exact div_ne_zero hcirc (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr.ne'
  constructor
  · intro h
    have hfrac :
        (regLowerGammaDensity s (scaledX beta r) * (2 * beta * r) * r -
          regLowerGamma s (scaledX beta r)) / r ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_left hconst
    have hnum :
        regLowerGammaDensity s (scaledX beta r) * (2 * beta * r) * r -
          regLowerGamma s (scaledX beta r) = 0 := by
      rcases div_eq_zero_iff.mp hfrac with hn | hd
      · exact hn
      · exact (hr2 hd).elim
    have heq := sub_eq_zero.mp hnum
    unfold scaledX at heq ⊢
    calc
      2 * (beta * r ^ 2) * regLowerGammaDensity s (beta * r ^ 2) =
          regLowerGammaDensity s (beta * r ^ 2) * (2 * beta * r) * r := by ring
      _ = regLowerGamma s (beta * r ^ 2) := heq
  · intro h
    have hnum :
        regLowerGammaDensity s (scaledX beta r) * (2 * beta * r) * r -
          regLowerGamma s (scaledX beta r) = 0 := by
      apply sub_eq_zero.mpr
      unfold scaledX at h ⊢
      calc
        regLowerGammaDensity s (beta * r ^ 2) * (2 * beta * r) * r =
            2 * (beta * r ^ 2) * regLowerGammaDensity s (beta * r ^ 2) := by ring
        _ = regLowerGamma s (beta * r ^ 2) := h
    rw [hnum, zero_div, mul_zero]

/-- Eq. (92) in the paper's unregularised lower-gamma notation. -/
theorem swirl_extremum_scaled_eq_lowerGamma
    {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    2 * x * regLowerGammaDensity s x = regLowerGamma s x ↔
      2 * x ^ s * Real.exp (-x) = lowerGamma s x := by
  unfold regLowerGammaDensity gammaKernel regLowerGamma
  have hG := gammaFn_ne_zero hs
  have hpow : x * x ^ (s - 1) = x ^ s := by
    calc
      x * x ^ (s - 1) = x ^ (1 : ℝ) * x ^ (s - 1) := by rw [Real.rpow_one]
      _ = x ^ ((1 : ℝ) + (s - 1)) := (Real.rpow_add hx 1 (s - 1)).symm
      _ = x ^ s := by ring_nf
  constructor
  · intro h
    field_simp [hG] at h
    calc
      2 * x ^ s * Real.exp (-x) =
          2 * (x * x ^ (s - 1)) * Real.exp (-x) := by rw [hpow]
      _ = 2 * x * Real.exp (-x) * x ^ (s - 1) := by ring
      _ = lowerGamma s x := h
  · intro h
    field_simp [hG]
    calc
      2 * x * Real.exp (-x) * x ^ (s - 1) =
          2 * (x * x ^ (s - 1)) * Real.exp (-x) := by ring
      _ = 2 * x ^ s * Real.exp (-x) := by rw [hpow]
      _ = lowerGamma s x := h

/-- The threshold `s>1/2` is exactly positivity of the small-radius swirl exponent `2s-1`. -/
theorem swirl_axis_exponent_pos_iff {s : ℝ} :
    0 < 2 * s - 1 ↔ (1 / 2 : ℝ) < s := by
  constructor <;> intro h <;> linarith


end

end KiknadzeKrasnov
