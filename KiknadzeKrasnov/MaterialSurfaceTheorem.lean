import KiknadzeKrasnov.CirculationSurface

namespace KiknadzeKrasnov

noncomputable section

/-- Source-form completion of manuscript Eq. (109):
`rStar^2 = (s-1)/beta = q/(2*nu*beta)`. -/
theorem materialRadiusSq_eq_source_form
    {nu q s beta : ℝ}
    (hnu : nu ≠ 0) (hbeta : beta ≠ 0)
    (hcompat : q = 2 * nu * (s - 1)) :
    materialRadiusSq s beta = q / (2 * nu * beta) := by
  unfold materialRadiusSq
  rw [hcompat]
  field_simp [hnu, hbeta]
  ring

/-- The distinguished physical material radius maps exactly to `x=s-1`. -/
theorem scaledX_materialRadius
    {s beta : ℝ} (hs : 1 < s) (hbeta : 0 < beta) :
    scaledX beta (materialRadius s beta) = s - 1 := by
  rw [materialRadius_eq_vorticityPeakRadius]
  exact scaledX_vorticityPeakRadius hs hbeta

/-- The inside sign of the radial offset is preserved, complementing
`materialOffsetSq_pos_iff` for the outside region. -/
theorem materialOffsetSq_neg_iff
    {a beta y betaDot : ℝ → ℝ} {nu q s t₁ t₂ : ℝ}
    (hA : ∀ t, HasDerivAt (strainAccum a) (a t) t)
    (hbeta : ∀ t, HasDerivAt beta (betaDot t) t)
    (hbetane : ∀ t, beta t ≠ 0)
    (hy : ∀ t, HasDerivAt y (-a t * y t + 2 * q) t)
    (hscale : ∀ t, scaleResidual nu (a t) (beta t) (betaDot t) = 0)
    (hcompat : q = 2 * nu * (s - 1)) :
    materialOffsetSq s (beta t₁) (y t₁) < 0 ↔
      materialOffsetSq s (beta t₂) (y t₂) < 0 := by
  have hI := radialInvariant_eq hA hbeta hbetane hy hscale hcompat
    (t₁ := t₁) (t₂ := t₂)
  unfold radialInvariant at hI
  constructor
  · intro hneg
    have hleft :
        Real.exp (strainAccum a t₁) * materialOffsetSq s (beta t₁) (y t₁) < 0 :=
      mul_neg_of_pos_of_neg (Real.exp_pos _) hneg
    rw [hI] at hleft
    by_contra hnot
    have hnonneg : 0 ≤ materialOffsetSq s (beta t₂) (y t₂) := le_of_not_gt hnot
    have hright :
        0 ≤ Real.exp (strainAccum a t₂) * materialOffsetSq s (beta t₂) (y t₂) :=
      mul_nonneg (Real.exp_pos _).le hnonneg
    linarith
  · intro hneg
    have hright :
        Real.exp (strainAccum a t₂) * materialOffsetSq s (beta t₂) (y t₂) < 0 :=
      mul_neg_of_pos_of_neg (Real.exp_pos _) hneg
    rw [← hI] at hright
    by_contra hnot
    have hnonneg : 0 ≤ materialOffsetSq s (beta t₁) (y t₁) := le_of_not_gt hnot
    have hleft :
        0 ≤ Real.exp (strainAccum a t₁) * materialOffsetSq s (beta t₁) (y t₁) :=
      mul_nonneg (Real.exp_pos _).le hnonneg
    linarith

/-- Algebraic differential identity used in manuscript Eq. (120): if
`omegaR = LRR/r - LR/r^2`, then `LRR - LR/r = r*omegaR` on `r ≠ 0`. -/
theorem angularMomentumDiffusionTerm_eq_r_vorticityGradient
    {r LR LRR omegaR : ℝ} (hr : r ≠ 0)
    (homegaR : omegaR = LRR / r - LR / r ^ 2) :
    LRR - LR / r = r * omegaR := by
  rw [homegaR]
  field_simp [hr]
  ring

/-- The sign of one-mode distributed vorticity follows positive circulation. -/
theorem distributedVorticity_pos_of_circ_pos
    {circ s beta r : ℝ}
    (hcirc : 0 < circ) (hs : 0 < s) (hbeta : 0 < beta) (hr : 0 < r) :
    0 < distributedVorticity circ s beta r := by
  have hx : 0 < scaledX beta r := by
    unfold scaledX
    positivity
  have hden : 0 < Real.pi * gammaFn s :=
    mul_pos Real.pi_pos (gammaFn_pos hs)
  have hpref : 0 < circ * beta / (Real.pi * gammaFn s) :=
    div_pos (mul_pos hcirc hbeta) hden
  unfold distributedVorticity
  exact mul_pos hpref (vorticityShape_pos hx)

/-- The sign of one-mode distributed vorticity follows negative circulation. -/
theorem distributedVorticity_neg_of_circ_neg
    {circ s beta r : ℝ}
    (hcirc : circ < 0) (hs : 0 < s) (hbeta : 0 < beta) (hr : 0 < r) :
    distributedVorticity circ s beta r < 0 := by
  have hx : 0 < scaledX beta r := by
    unfold scaledX
    positivity
  have hden : 0 < Real.pi * gammaFn s :=
    mul_pos Real.pi_pos (gammaFn_pos hs)
  have hnum : circ * beta < 0 := mul_neg_of_neg_of_pos hcirc hbeta
  have hpref : circ * beta / (Real.pi * gammaFn s) < 0 :=
    div_neg_of_neg_of_pos hnum hden
  unfold distributedVorticity
  exact mul_neg_of_neg_of_pos hpref (vorticityShape_pos hx)

/-- Direct F9 statement: for nonzero circulation, `|omega_z|` has its unique
positive-radius maximum at the material cylinder. -/
theorem abs_distributedVorticity_lt_materialRadius
    {circ s beta r : ℝ}
    (hcirc : circ ≠ 0) (hs : 1 < s) (hbeta : 0 < beta)
    (hr : 0 < r) (hne : r ≠ materialRadius s beta) :
    |distributedVorticity circ s beta r| <
      |distributedVorticity circ s beta (materialRadius s beta)| := by
  rw [materialRadius_eq_vorticityPeakRadius] at hne ⊢
  exact abs_distributedVorticity_lt_peak hcirc hs hbeta hr hne

/-- For positive circulation the material radius is the unique positive-radius
signed maximum of the one-mode vorticity. -/
theorem distributedVorticity_lt_materialRadius_of_circ_pos
    {circ s beta r : ℝ}
    (hcirc : 0 < circ) (hs : 1 < s) (hbeta : 0 < beta)
    (hr : 0 < r) (hne : r ≠ materialRadius s beta) :
    distributedVorticity circ s beta r <
      distributedVorticity circ s beta (materialRadius s beta) := by
  have hcirc0 : circ ≠ 0 := ne_of_gt hcirc
  have hmag := abs_distributedVorticity_lt_materialRadius hcirc0 hs hbeta hr hne
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  have hstar : 0 < materialRadius s beta := materialRadius_pos hs hbeta
  have hvr := distributedVorticity_pos_of_circ_pos hcirc hs0 hbeta hr
  have hvstar := distributedVorticity_pos_of_circ_pos hcirc hs0 hbeta hstar
  rw [abs_of_pos hvr, abs_of_pos hvstar] at hmag
  exact hmag

/-- For negative circulation the material radius is the unique positive-radius
signed minimum of the one-mode vorticity. -/
theorem distributedVorticity_materialRadius_lt_of_circ_neg
    {circ s beta r : ℝ}
    (hcirc : circ < 0) (hs : 1 < s) (hbeta : 0 < beta)
    (hr : 0 < r) (hne : r ≠ materialRadius s beta) :
    distributedVorticity circ s beta (materialRadius s beta) <
      distributedVorticity circ s beta r := by
  have hcirc0 : circ ≠ 0 := ne_of_lt hcirc
  have hmag := abs_distributedVorticity_lt_materialRadius hcirc0 hs hbeta hr hne
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  have hstar : 0 < materialRadius s beta := materialRadius_pos hs hbeta
  have hvr := distributedVorticity_neg_of_circ_neg hcirc hs0 hbeta hr
  have hvstar := distributedVorticity_neg_of_circ_neg hcirc hs0 hbeta hstar
  rw [abs_of_neg hvr, abs_of_neg hvstar] at hmag
  linarith

/-- The viscous circulation-transfer expression vanishes directly on the
material/vorticity-extremum cylinder. -/
theorem viscousCirculationFlux_zero_at_materialRadius
    {nu beta circ s : ℝ} (hs : 1 < s) (hbeta : 0 < beta) :
    2 * Real.pi * nu * materialRadius s beta *
        deriv (distributedVorticity circ s beta) (materialRadius s beta) = 0 := by
  rw [distributedVorticity_deriv_at_materialRadius hs hbeta]
  ring

/-- The explicit material-circulation rate is zero at the physical material cylinder. -/
theorem materialCirculationRate_zero_at_materialRadius
    {nu beta circ s : ℝ} (hs : 1 < s) (hbeta : 0 < beta) :
    materialCirculationRate nu beta circ s
      (scaledX beta (materialRadius s beta)) = 0 := by
  rw [scaledX_materialRadius hs hbeta]
  exact materialCirculationRate_at_star nu beta circ s

end

end KiknadzeKrasnov
