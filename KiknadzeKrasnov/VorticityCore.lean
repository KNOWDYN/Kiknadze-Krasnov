import KiknadzeKrasnov.GammaProfile
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace KiknadzeKrasnov

noncomputable section

open Set

/-!
Pass 4 one-mode vorticity layer. This file connects the already-defined KK
swirl/circulation profile to the actual cylindrical curl and proves the
sign-correct annular vorticity extremum used by the principal material-surface
theorem.
-/


/-- Optional central line-circulation swirl Gamma_line/(2 pi r) on the punctured domain. -/
def centralLineSwirl (gammaLine r : ℝ) : ℝ :=
  (gammaLine / (2 * Real.pi)) / r

/--
The angular momentum of the central 1/r circulation has zero radial
derivative at every r>0.
-/
theorem centralLineAngularMomentum_hasDerivAt_zero
    {gammaLine r : ℝ} (hr : PuncturedRadius r) :
    HasDerivAt (fun rho => rho * centralLineSwirl gammaLine rho) 0 r := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  let c : ℝ := gammaLine / (2 * Real.pi)
  have hsource : HasDerivAt (fun rho : ℝ => c / rho) (-c / r ^ 2) r := by
    convert (hasDerivAt_const r c).div (hasDerivAt_id r) hr0 using 1
    · rfl
    · simp
  have hprod := (hasDerivAt_id r).mul hsource
  unfold centralLineSwirl
  dsimp [c] at hprod ⊢
  convert hprod using 1
  · funext rho
    rfl
  · field_simp [hr0]
    ring

/--
Claim C010, classical part: the optional central line circulation contributes
zero classical axial vorticity on r>0.  The distribution concentrated on the
excluded axis is intentionally outside this real-variable formalisation.
-/
theorem centralLineClassicalVorticity_zero
    {gammaLine r : ℝ} (hr : PuncturedRadius r) :
    deriv (fun rho => rho * centralLineSwirl gammaLine rho) r / r = 0 := by
  rw [(centralLineAngularMomentum_hasDerivAt_zero
    (gammaLine := gammaLine) hr).deriv]
  simp

/-- One distributed mode's angular momentum L = Gamma P(s,beta r^2)/(2 pi). -/
def distributedAngularMomentum (circ s beta r : ℝ) : ℝ :=
  circ / (2 * Real.pi) * regLowerGamma s (scaledX beta r)

/-- The scaled squared radius has radial derivative 2 beta r. -/
theorem scaledX_hasDerivAt (beta r : ℝ) :
    HasDerivAt (scaledX beta) (2 * beta * r) r := by
  unfold scaledX
  convert ((hasDerivAt_id r).pow 2).const_mul beta using 1
  · funext y
    simp
  · simp
    ring

/-- Radial derivative of P(s,beta r^2). -/
theorem regLowerGamma_scaledX_hasDerivAt
    {s beta r : ℝ} (hs : 0 < s) (hx : 0 < scaledX beta r) :
    HasDerivAt (fun y => regLowerGamma s (scaledX beta y))
      (regLowerGammaDensity s (scaledX beta r) * (2 * beta * r)) r := by
  have hP := (regLowerGamma_hasDerivAt hs hx).comp r (scaledX_hasDerivAt beta r)
  convert hP using 1
  · rfl
  · unfold regLowerGammaDensity
    ring

/-- Radial derivative of the one-mode angular momentum profile. -/
theorem distributedAngularMomentum_hasDerivAt
    {circ s beta r : ℝ} (hs : 0 < s) (hx : 0 < scaledX beta r) :
    HasDerivAt (distributedAngularMomentum circ s beta)
      (circ / (2 * Real.pi) *
        (regLowerGammaDensity s (scaledX beta r) * (2 * beta * r))) r := by
  unfold distributedAngularMomentum
  exact (regLowerGamma_scaledX_hasDerivAt hs hx).const_mul (circ / (2 * Real.pi))

/-- The angular momentum is exactly r times the distributed swirl on r>0. -/
theorem distributedAngularMomentum_eq_radius_mul_swirl
    {circ s beta r : ℝ} (hr : PuncturedRadius r) :
    distributedAngularMomentum circ s beta r =
      r * distributedSwirl circ s beta r := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  unfold distributedAngularMomentum distributedSwirl
  field_simp [hr0, Real.pi_ne_zero]

/--
The source vorticity formula is not assumed: it is exactly
(1/r) d_r (r u_theta) for the one-mode distributed swirl.
-/
theorem distributedVorticity_eq_swirl_curl
    {circ s beta r : ℝ}
    (hs : 0 < s) (hbeta : 0 < beta) (hr : PuncturedRadius r) :
    deriv (fun rho => rho * distributedSwirl circ s beta rho) r / r =
      distributedVorticity circ s beta r := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hx : 0 < scaledX beta r := by
    unfold scaledX
    exact mul_pos hbeta (pow_pos hr 2)
  have hfun :
      (fun rho => rho * distributedSwirl circ s beta rho) =
        distributedAngularMomentum circ s beta := by
    funext rho
    by_cases hzero : rho = 0
    · subst rho
      simp [distributedAngularMomentum, distributedSwirl]
    · unfold distributedAngularMomentum distributedSwirl
      field_simp [hzero, Real.pi_ne_zero]
  rw [hfun, (distributedAngularMomentum_hasDerivAt (circ := circ) hs hx).deriv]
  unfold distributedVorticity vorticityShape regLowerGammaDensity gammaKernel
  field_simp [hr0, Real.pi_ne_zero, gammaFn_ne_zero hs]

/-- The enclosed distributed circulation is exactly 2 pi r u_theta on r>0. -/
theorem distributedCirculation_eq_two_pi_radius_swirl
    {circ s beta r : ℝ} (hr : PuncturedRadius r) :
    distributedCirculation circ s beta r =
      2 * Real.pi * r * distributedSwirl circ s beta r := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  unfold distributedCirculation distributedSwirl
  field_simp [hr0, Real.pi_ne_zero]

/-- Radial derivative of enclosed distributed circulation equals 2 pi r omega_z. -/
theorem distributedCirculation_hasDerivAt_r
    {circ s beta r : ℝ} (hs : 0 < s) (hbeta : 0 < beta) (hr : PuncturedRadius r) :
    HasDerivAt (distributedCirculation circ s beta)
      (2 * Real.pi * r * distributedVorticity circ s beta r) r := by
  have hx : 0 < scaledX beta r := by
    unfold scaledX
    exact mul_pos hbeta (pow_pos hr 2)
  have hP :=
    (regLowerGamma_scaledX_hasDerivAt (s := s) (beta := beta) hs hx).const_mul circ
  unfold distributedCirculation distributedVorticity regLowerGammaDensity
    vorticityShape gammaKernel at *
  convert hP using 1
  field_simp [gammaFn_ne_zero hs, Real.pi_ne_zero]

/-- The vorticity-shape function is the gamma kernel. -/
theorem vorticityShape_eq_gammaKernel (s x : ℝ) :
    vorticityShape s x = gammaKernel s x := by
  unfold vorticityShape gammaKernel
  ring

/-- The one-mode vorticity shape has the factored derivative on x>0. -/
theorem vorticityShape_hasDerivAt {s x : ℝ} (hx : 0 < x) :
    HasDerivAt (vorticityShape s)
      (((s - 1) / x - 1) * vorticityShape s x) x := by
  convert gammaKernel_hasDerivAt_profile (s := s) hx using 1
  · funext y
    exact vorticityShape_eq_gammaKernel s y
  · rw [vorticityShape_eq_gammaKernel]

/-- The one-mode vorticity shape is strictly positive for x>0. -/
theorem vorticityShape_pos {s x : ℝ} (hx : 0 < x) :
    0 < vorticityShape s x := by
  unfold vorticityShape
  exact mul_pos (Real.rpow_pos_of_pos hx _) (Real.exp_pos _)

/-- Before x=s-1, the shape derivative is positive for s>1. -/
theorem vorticityShape_deriv_pos_before_peak {s x : ℝ}
    (_hs : 1 < s) (hx : 0 < x) (hxp : x < s - 1) :
    0 < deriv (vorticityShape s) x := by
  rw [(vorticityShape_hasDerivAt (s := s) hx).deriv]
  have hcoef : 0 < (s - 1) / x - 1 := by
    rw [sub_pos]
    exact (lt_div_iff₀ hx).2 (by linarith)
  exact mul_pos hcoef (vorticityShape_pos hx)

/-- After x=s-1, the shape derivative is negative for s>1. -/
theorem vorticityShape_deriv_neg_after_peak {s x : ℝ}
    (_hs : 1 < s) (hx : 0 < x) (hxp : s - 1 < x) :
    deriv (vorticityShape s) x < 0 := by
  rw [(vorticityShape_hasDerivAt (s := s) hx).deriv]
  have hcoef : (s - 1) / x - 1 < 0 := by
    rw [sub_neg]
    exact (div_lt_iff₀ hx).2 (by linarith)
  exact mul_neg_of_neg_of_pos hcoef (vorticityShape_pos hx)

/-- The scaled shape has zero derivative at x=s-1. -/
theorem vorticityShape_deriv_at_peak {s : ℝ} (hs : 1 < s) :
    deriv (vorticityShape s) (s - 1) = 0 := by
  have hx : 0 < s - 1 := by linarith
  rw [(vorticityShape_hasDerivAt (s := s) hx).deriv]
  field_simp [hx.ne']
  ring

/-- Strict global peak of the positive vorticity shape on x>0 for s>1. -/
theorem vorticityShape_lt_peak {s x : ℝ}
    (hs : 1 < s) (hx : 0 < x) (hne : x ≠ s - 1) :
    vorticityShape s x < vorticityShape s (s - 1) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hcont : ContinuousOn (vorticityShape s) (Icc x (s - 1)) := by
      intro y hy
      have hpos : 0 < y := lt_of_lt_of_le hx hy.1
      exact (vorticityShape_hasDerivAt (s := s) hpos).continuousAt.continuousWithinAt
    have hmono : StrictMonoOn (vorticityShape s) (Icc x (s - 1)) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc x (s - 1)) hcont
      intro y hy
      rw [interior_Icc] at hy
      exact vorticityShape_deriv_pos_before_peak hs
        (lt_trans hx hy.1) hy.2
    exact hmono (left_mem_Icc.mpr hlt.le) (right_mem_Icc.mpr hlt.le) hlt
  · have hcont : ContinuousOn (vorticityShape s) (Icc (s - 1) x) := by
      intro y hy
      have hpos : 0 < y := lt_of_lt_of_le (sub_pos.mpr hs) hy.1
      exact (vorticityShape_hasDerivAt (s := s) hpos).continuousAt.continuousWithinAt
    have hanti : StrictAntiOn (vorticityShape s) (Icc (s - 1) x) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc (s - 1) x) hcont
      intro y hy
      rw [interior_Icc] at hy
      exact vorticityShape_deriv_neg_after_peak hs
        (lt_trans (sub_pos.mpr hs) hy.1) hy.1
    exact hanti (left_mem_Icc.mpr hgt.le) (right_mem_Icc.mpr hgt.le) hgt

/-- Positive annular peak radius in physical space. -/
def vorticityPeakRadius (s beta : ℝ) : ℝ :=
  Real.sqrt ((s - 1) / beta)

/-- The peak radius is positive for s>1 and beta>0. -/
theorem vorticityPeakRadius_pos {s beta : ℝ} (hs : 1 < s) (hbeta : 0 < beta) :
    0 < vorticityPeakRadius s beta := by
  unfold vorticityPeakRadius
  exact Real.sqrt_pos.2 (div_pos (by linarith) hbeta)

/-- The physical peak radius maps exactly to x=s-1. -/
theorem scaledX_vorticityPeakRadius {s beta : ℝ}
    (hs : 1 < s) (hbeta : 0 < beta) :
    scaledX beta (vorticityPeakRadius s beta) = s - 1 := by
  unfold scaledX vorticityPeakRadius
  rw [Real.sq_sqrt (div_nonneg (by linarith) hbeta.le)]
  field_simp [hbeta.ne']

/-- Radial derivative of one-mode vorticity. -/
theorem distributedVorticity_hasDerivAt_r
    {circ s beta r : ℝ} (_hs : 0 < s) (hbeta : 0 < beta) (hr : PuncturedRadius r) :
    HasDerivAt (distributedVorticity circ s beta)
      (circ * beta / (Real.pi * gammaFn s) *
        (((s - 1) / scaledX beta r - 1) * vorticityShape s (scaledX beta r)) *
        (2 * beta * r)) r := by
  have hx : 0 < scaledX beta r := by
    unfold scaledX
    exact mul_pos hbeta (pow_pos hr 2)
  have hshape :=
    (vorticityShape_hasDerivAt (s := s) hx).comp r (scaledX_hasDerivAt beta r)
  unfold distributedVorticity
  simpa only [Function.comp_apply, mul_assoc] using
    hshape.const_mul (circ * beta / (Real.pi * gammaFn s))

/-- The physical one-mode vorticity derivative vanishes at the annular peak radius. -/
theorem distributedVorticity_deriv_at_peak
    {circ s beta : ℝ} (hs : 1 < s) (hbeta : 0 < beta) :
    deriv (distributedVorticity circ s beta) (vorticityPeakRadius s beta) = 0 := by
  have hr := vorticityPeakRadius_pos hs hbeta
  rw [(distributedVorticity_hasDerivAt_r (circ := circ) (s := s)
    (beta := beta) (r := vorticityPeakRadius s beta) (by linarith) hbeta hr).deriv]
  rw [scaledX_vorticityPeakRadius hs hbeta]
  field_simp [sub_ne_zero.mpr (ne_of_gt hs)]
  ring

/-- For nonzero circulation, |omega_z| has a unique positive-radius maximum. -/
theorem abs_distributedVorticity_lt_peak
    {circ s beta r : ℝ} (hcirc : circ ≠ 0) (hs : 1 < s)
    (hbeta : 0 < beta) (hr : PuncturedRadius r)
    (hne : r ≠ vorticityPeakRadius s beta) :
    |distributedVorticity circ s beta r| <
      |distributedVorticity circ s beta (vorticityPeakRadius s beta)| := by
  have hx : 0 < scaledX beta r := by
    unfold scaledX
    exact mul_pos hbeta (pow_pos hr 2)
  have hxpeak := scaledX_vorticityPeakRadius hs hbeta
  have hxr_ne : scaledX beta r ≠ s - 1 := by
    intro h
    have hscaled : scaledX beta r =
        scaledX beta (vorticityPeakRadius s beta) := h.trans hxpeak.symm
    have hmul : beta * r ^ 2 =
        beta * (vorticityPeakRadius s beta) ^ 2 := by
      simpa [scaledX] using hscaled
    have hr2 : r ^ 2 = (vorticityPeakRadius s beta) ^ 2 :=
      mul_left_cancel₀ hbeta.ne' hmul
    have hrpos : 0 < r := hr
    have hpeakpos : 0 < vorticityPeakRadius s beta :=
      vorticityPeakRadius_pos hs hbeta
    have hrEq : r = vorticityPeakRadius s beta := by
      nlinarith [hr2, hrpos, hpeakpos]
    exact hne hrEq
  have hshape := vorticityShape_lt_peak hs hx hxr_ne
  unfold distributedVorticity
  have hspos : 0 < s := lt_trans zero_lt_one hs
  have hpref_ne : circ * beta / (Real.pi * gammaFn s) ≠ 0 := by
    exact div_ne_zero (mul_ne_zero hcirc hbeta.ne')
      (mul_ne_zero Real.pi_ne_zero (gammaFn_ne_zero hspos))
  have hpref : 0 < |circ * beta / (Real.pi * gammaFn s)| := abs_pos.mpr hpref_ne
  simp only [abs_mul]
  rw [abs_of_pos (vorticityShape_pos hx)]
  rw [hxpeak, abs_of_pos (vorticityShape_pos (sub_pos.mpr hs))]
  exact mul_lt_mul_of_pos_left hshape hpref

/-- For positive circulation, the annular radius is the signed vorticity maximum. -/
theorem distributedVorticity_lt_peak_of_circ_pos
    {circ s beta r : ℝ}
    (hcirc : 0 < circ) (hs : 1 < s) (hbeta : 0 < beta)
    (hr : PuncturedRadius r) (hne : r ≠ vorticityPeakRadius s beta) :
    distributedVorticity circ s beta r <
      distributedVorticity circ s beta (vorticityPeakRadius s beta) := by
  have hmag := abs_distributedVorticity_lt_peak (ne_of_gt hcirc) hs hbeta hr hne
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  have hx : 0 < scaledX beta r := by
    unfold scaledX
    exact mul_pos hbeta (pow_pos hr 2)
  have hxp : 0 < scaledX beta (vorticityPeakRadius s beta) := by
    rw [scaledX_vorticityPeakRadius hs hbeta]
    linarith
  unfold distributedVorticity at hmag ⊢
  have hden : 0 < Real.pi * gammaFn s :=
    mul_pos Real.pi_pos (gammaFn_pos hs0)
  have hpref : 0 < circ * beta / (Real.pi * gammaFn s) :=
    div_pos (mul_pos hcirc hbeta) hden
  rw [abs_of_pos (mul_pos hpref (vorticityShape_pos hx))] at hmag
  rw [abs_of_pos (mul_pos hpref (vorticityShape_pos hxp))] at hmag
  exact hmag

/-- For negative circulation, the annular radius is the signed vorticity minimum. -/
theorem distributedVorticity_peak_lt_of_circ_neg
    {circ s beta r : ℝ}
    (hcirc : circ < 0) (hs : 1 < s) (hbeta : 0 < beta)
    (hr : PuncturedRadius r) (hne : r ≠ vorticityPeakRadius s beta) :
    distributedVorticity circ s beta (vorticityPeakRadius s beta) <
      distributedVorticity circ s beta r := by
  have hmag := abs_distributedVorticity_lt_peak (ne_of_lt hcirc) hs hbeta hr hne
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  have hx : 0 < scaledX beta r := by
    unfold scaledX
    exact mul_pos hbeta (pow_pos hr 2)
  have hxp : 0 < scaledX beta (vorticityPeakRadius s beta) := by
    rw [scaledX_vorticityPeakRadius hs hbeta]
    linarith
  unfold distributedVorticity at hmag ⊢
  have hden : 0 < Real.pi * gammaFn s :=
    mul_pos Real.pi_pos (gammaFn_pos hs0)
  have hpref : circ * beta / (Real.pi * gammaFn s) < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hcirc hbeta) hden
  rw [abs_of_neg (mul_neg_of_neg_of_pos hpref (vorticityShape_pos hx))] at hmag
  rw [abs_of_neg (mul_neg_of_neg_of_pos hpref (vorticityShape_pos hxp))] at hmag
  linarith

end

end KiknadzeKrasnov
