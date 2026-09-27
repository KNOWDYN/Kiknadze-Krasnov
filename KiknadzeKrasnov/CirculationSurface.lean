import KiknadzeKrasnov.MaterialSurface

namespace KiknadzeKrasnov

noncomputable section

/-!
Pass 4 circulation-transfer layer for manuscript Eqs. (116)--(123) and
Supplementary Eqs. (30)--(35).
-/

/-- Distributed circulation written as a function of scaled material radius. -/
def materialCirculationFromX (circ s x : ℝ) : ℝ :=
  circ * regLowerGamma s x

/-- The scaled material-circulation notation is exactly the existing physical one-mode circulation. -/
@[simp] theorem materialCirculationFromX_scaled_eq
    (circ s beta r : ℝ) :
    materialCirculationFromX circ s (scaledX beta r) =
      distributedCirculation circ s beta r := by
  rfl

/-- Exact material circulation-rate expression from manuscript Eq. (119). -/
def materialCirculationRate (nu beta circ s x : ℝ) : ℝ :=
  (4 * nu * beta * circ / gammaFn s) *
    vorticityShape s x * ((s - 1) - x)

/--
For an arbitrary material scaled-radius history satisfying Eq. (106),
differentiate Gamma P(s,x) exactly.
-/
theorem materialCirculationFromX_hasDerivAt
    {x : ℝ → ℝ} {nu beta circ s t : ℝ}
    (hs : 0 < s) (hx : 0 < x t)
    (hxdot : HasDerivAt x
      (4 * nu * beta * ((s - 1) - x t)) t) :
    HasDerivAt (fun tau => materialCirculationFromX circ s (x tau))
      (materialCirculationRate nu beta circ s (x t)) t := by
  have hP := (regLowerGamma_hasDerivAt hs hx).comp t hxdot
  have hC := hP.const_mul circ
  unfold materialCirculationFromX materialCirculationRate
  convert hC using 1
  · funext tau
    simp only [Function.comp_apply]
  · unfold gammaKernel vorticityShape
    ring

/-- The material circulation rate vanishes at x=s-1. -/
@[simp] theorem materialCirculationRate_at_star
    (nu beta circ s : ℝ) :
    materialCirculationRate nu beta circ s (s - 1) = 0 := by
  simp [materialCirculationRate]

/-- A material loop on x=s-1 has zero instantaneous circulation derivative. -/
theorem materialCirculation_hasDerivAt_zero_at_star
    {x : ℝ → ℝ} {nu beta circ s t : ℝ}
    (hs : 1 < s)
    (hxdot : HasDerivAt x
      (4 * nu * beta * ((s - 1) - x t)) t)
    (hstar : x t = s - 1) :
    HasDerivAt (fun tau => materialCirculationFromX circ s (x tau)) 0 t := by
  have hx : 0 < x t := by rw [hstar]; linarith
  convert materialCirculationFromX_hasDerivAt (circ := circ) (s := s)
    (nu := nu) (beta := beta) (t := t) (by linarith) hx hxdot using 1
  rw [hstar]
  simp

/-- Enclosed distributed circulation at the distinguished radius. -/
theorem materialCirculation_at_star (circ s : ℝ) :
    materialCirculationFromX circ s (s - 1) =
      circ * regLowerGamma s (s - 1) := by
  rfl

/-- The enclosed distributed-circulation fraction depends only on s. -/
theorem materialCirculation_fraction_at_star
    {circ s : ℝ} (hcirc : circ ≠ 0) :
    materialCirculationFromX circ s (s - 1) / circ =
      regLowerGamma s (s - 1) := by
  unfold materialCirculationFromX
  field_simp [hcirc]

/-- The material radius and the one-mode peak-vorticity radius coincide. -/
theorem materialRadius_eq_vorticityPeakRadius (s beta : ℝ) :
    materialRadius s beta = vorticityPeakRadius s beta := by
  rfl

/-- The one-mode vorticity derivative vanishes on the material cylinder. -/
theorem distributedVorticity_deriv_at_materialRadius
    {circ s beta : ℝ} (hs : 1 < s) (hbeta : 0 < beta) :
    deriv (distributedVorticity circ s beta) (materialRadius s beta) = 0 := by
  rw [materialRadius_eq_vorticityPeakRadius]
  exact distributedVorticity_deriv_at_peak hs hbeta

/--
Manuscript Eq. (121): the material circulation-rate formula is exactly the
viscous transfer 2 pi nu r partial_r omega_z.
-/
theorem materialCirculationRate_eq_viscousFlux
    {nu beta circ s r : ℝ}
    (hs : 0 < s) (hbeta : 0 < beta) (hr : PuncturedRadius r) :
    materialCirculationRate nu beta circ s (scaledX beta r) =
      2 * Real.pi * nu * r * deriv (distributedVorticity circ s beta) r := by
  rw [(distributedVorticity_hasDerivAt_r
    (circ := circ) (s := s) (beta := beta) (r := r) hs hbeta hr).deriv]
  have hx : 0 < scaledX beta r := by
    unfold scaledX
    exact mul_pos hbeta (pow_pos hr 2)
  unfold materialCirculationRate
  field_simp [gammaFn_ne_zero hs, Real.pi_ne_zero, hx.ne']
  unfold scaledX
  ring

/-- The viscous circulation transfer vanishes on the material/vorticity-peak cylinder. -/
theorem viscousCirculationFlux_zero_at_materialRadius
    {nu beta circ s : ℝ} (hs : 1 < s) (hbeta : 0 < beta) :
    2 * Real.pi * nu * materialRadius s beta *
        deriv (distributedVorticity circ s beta) (materialRadius s beta) = 0 := by
  rw [distributedVorticity_deriv_at_materialRadius hs hbeta]
  ring

/-- The explicit material-circulation rate vanishes on the physical material cylinder. -/
theorem materialCirculationRate_zero_at_materialRadius
    {nu beta circ s : ℝ} (hs : 1 < s) (hbeta : 0 < beta) :
    materialCirculationRate nu beta circ s
      (scaledX beta (materialRadius s beta)) = 0 := by
  rw [scaledX_materialRadius hs hbeta]
  exact materialCirculationRate_at_star nu beta circ s

/-- For positive circulation, transfer is positive inside x=s-1. -/
theorem materialCirculationRate_pos_before_star_of_circ_pos
    {nu beta circ s x : ℝ}
    (hnu : 0 < nu) (hbeta : 0 < beta) (hcirc : 0 < circ)
    (hs : 0 < s) (hx : 0 < x) (hbefore : x < s - 1) :
    0 < materialCirculationRate nu beta circ s x := by
  unfold materialCirculationRate
  have hG : 0 < gammaFn s := gammaFn_pos hs
  have hshape : 0 < vorticityShape s x := vorticityShape_pos hx
  have hlast : 0 < (s - 1) - x := sub_pos.mpr hbefore
  positivity

/-- For positive circulation, transfer is negative outside x=s-1. -/
theorem materialCirculationRate_neg_after_star_of_circ_pos
    {nu beta circ s x : ℝ}
    (hnu : 0 < nu) (hbeta : 0 < beta) (hcirc : 0 < circ)
    (hs : 0 < s) (hx : 0 < x) (hafter : s - 1 < x) :
    materialCirculationRate nu beta circ s x < 0 := by
  unfold materialCirculationRate
  have hpre : 0 < (4 * nu * beta * circ / gammaFn s) * vorticityShape s x := by
    have hG : 0 < gammaFn s := gammaFn_pos hs
    have hshape : 0 < vorticityShape s x := vorticityShape_pos hx
    positivity
  exact mul_neg_of_pos_of_neg hpre (sub_neg.mpr hafter)

/-- For negative circulation, the transfer orientation reverses inside. -/
theorem materialCirculationRate_neg_before_star_of_circ_neg
    {nu beta circ s x : ℝ}
    (hnu : 0 < nu) (hbeta : 0 < beta) (hcirc : circ < 0)
    (hs : 0 < s) (hx : 0 < x) (hbefore : x < s - 1) :
    materialCirculationRate nu beta circ s x < 0 := by
  unfold materialCirculationRate
  have hpre : (4 * nu * beta * circ / gammaFn s) * vorticityShape s x < 0 := by
    have hG : 0 < gammaFn s := gammaFn_pos hs
    have hshape : 0 < vorticityShape s x := vorticityShape_pos hx
    have hfour : 0 < 4 * nu * beta := by positivity
    have hnum : 4 * nu * beta * circ < 0 := mul_neg_of_pos_of_neg hfour hcirc
    have hfrac : 4 * nu * beta * circ / gammaFn s < 0 :=
      div_neg_of_neg_of_pos hnum hG
    exact mul_neg_of_neg_of_pos hfrac hshape
  exact mul_neg_of_neg_of_pos hpre (sub_pos.mpr hbefore)

/-- For negative circulation, the transfer orientation reverses outside. -/
theorem materialCirculationRate_pos_after_star_of_circ_neg
    {nu beta circ s x : ℝ}
    (hnu : 0 < nu) (hbeta : 0 < beta) (hcirc : circ < 0)
    (hs : 0 < s) (hx : 0 < x) (hafter : s - 1 < x) :
    0 < materialCirculationRate nu beta circ s x := by
  unfold materialCirculationRate
  have hpre : (4 * nu * beta * circ / gammaFn s) * vorticityShape s x < 0 := by
    have hG : 0 < gammaFn s := gammaFn_pos hs
    have hshape : 0 < vorticityShape s x := vorticityShape_pos hx
    have hfour : 0 < 4 * nu * beta := by positivity
    have hnum : 4 * nu * beta * circ < 0 := mul_neg_of_pos_of_neg hfour hcirc
    have hfrac : 4 * nu * beta * circ / gammaFn s < 0 :=
      div_neg_of_neg_of_pos hnum hG
    exact mul_neg_of_neg_of_pos hfrac hshape
  exact mul_pos_of_neg_of_neg hpre (sub_neg.mpr hafter)


/--
Material-loop circulation including the optional constant central line
circulation allowed by the manuscript.  The line term is additive and carries
zero time derivative.
-/
def materialCirculationWithLine
    (gammaLine circ s x : ℝ) : ℝ :=
  gammaLine + materialCirculationFromX circ s x

/-- A constant central line circulation does not alter the material circulation rate. -/
theorem materialCirculationWithLine_hasDerivAt
    {x : ℝ → ℝ} {gammaLine nu beta circ s t : ℝ}
    (hs : 0 < s) (hx : 0 < x t)
    (hxdot : HasDerivAt x
      (4 * nu * beta * ((s - 1) - x t)) t) :
    HasDerivAt
      (fun tau => materialCirculationWithLine gammaLine circ s (x tau))
      (materialCirculationRate nu beta circ s (x t)) t := by
  have h :=
    materialCirculationFromX_hasDerivAt
      (circ := circ) (s := s) (nu := nu) (beta := beta)
      (t := t) hs hx hxdot
  have hc := (hasDerivAt_const t gammaLine).add h
  unfold materialCirculationWithLine
  convert hc using 1
  simp

/-- The optional constant line circulation preserves zero transfer on x=s-1. -/
theorem materialCirculationWithLine_hasDerivAt_zero_at_star
    {x : ℝ → ℝ} {gammaLine nu beta circ s t : ℝ}
    (hs : 1 < s)
    (hxdot : HasDerivAt x
      (4 * nu * beta * ((s - 1) - x t)) t)
    (hstar : x t = s - 1) :
    HasDerivAt
      (fun tau => materialCirculationWithLine gammaLine circ s (x tau))
      0 t := by
  have hx : 0 < x t := by rw [hstar]; linarith
  have h :=
    materialCirculationWithLine_hasDerivAt
      (x := x) (gammaLine := gammaLine) (nu := nu) (beta := beta)
      (circ := circ) (s := s) (t := t) (by linarith) hx hxdot
  rw [hstar] at h
  simpa [materialCirculationRate] using h

/-- Enclosed circulation at the distinguished cylinder, including a constant line term. -/
theorem materialCirculationWithLine_at_star
    (gammaLine circ s : ℝ) :
    materialCirculationWithLine gammaLine circ s (s - 1) =
      gammaLine + circ * regLowerGamma s (s - 1) := by
  rfl

/--
Manuscript Eqs. (119)--(121) in one certificate: differentiating the
material-loop circulation and evaluating the same point as a physical cylinder
gives exactly the viscous transfer 2 pi nu r partial_r omega_z.
-/
theorem materialCirculationFromX_hasDerivAt_viscousFlux
    {x : ℝ → ℝ} {nu beta circ s r t : ℝ}
    (hs : 0 < s) (hbeta : 0 < beta) (hr : PuncturedRadius r)
    (hxval : x t = scaledX beta r)
    (hxdot : HasDerivAt x
      (4 * nu * beta * ((s - 1) - x t)) t) :
    HasDerivAt
      (fun tau => materialCirculationFromX circ s (x tau))
      (2 * Real.pi * nu * r *
        deriv (distributedVorticity circ s beta) r) t := by
  have hxpos : 0 < x t := by
    rw [hxval]
    unfold scaledX
    exact mul_pos hbeta (pow_pos hr 2)
  have h :=
    materialCirculationFromX_hasDerivAt
      (circ := circ) (s := s) (nu := nu) (beta := beta)
      (t := t) hs hxpos hxdot
  rw [hxval] at h
  rw [materialCirculationRate_eq_viscousFlux hs hbeta hr] at h
  exact h

/--
The same viscous-flux identity holds when the constant central line
circulation is included; its derivative is identically zero.
-/
theorem materialCirculationWithLine_hasDerivAt_viscousFlux
    {x : ℝ → ℝ} {gammaLine nu beta circ s r t : ℝ}
    (hs : 0 < s) (hbeta : 0 < beta) (hr : PuncturedRadius r)
    (hxval : x t = scaledX beta r)
    (hxdot : HasDerivAt x
      (4 * nu * beta * ((s - 1) - x t)) t) :
    HasDerivAt
      (fun tau => materialCirculationWithLine gammaLine circ s (x tau))
      (2 * Real.pi * nu * r *
        deriv (distributedVorticity circ s beta) r) t := by
  have h :=
    materialCirculationFromX_hasDerivAt_viscousFlux
      (x := x) (nu := nu) (beta := beta) (circ := circ)
      (s := s) (r := r) (t := t) hs hbeta hr hxval hxdot
  have hc := (hasDerivAt_const t gammaLine).add h
  unfold materialCirculationWithLine
  convert hc using 1
  simp

end

end KiknadzeKrasnov
