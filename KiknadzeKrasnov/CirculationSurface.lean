import KiknadzeKrasnov.MaterialSurface
import KiknadzeKrasnov.VorticityAnalysis

namespace KiknadzeKrasnov

noncomputable section

/-- Distributed circulation written directly as a function of scaled material radius. -/
def materialCirculationFromX (circ s x : ℝ) : ℝ :=
  circ * regLowerGamma s x

/-- Exact material circulation-rate expression from manuscript Eq. (114). -/
def materialCirculationRate (nu beta circ s x : ℝ) : ℝ :=
  (4 * nu * beta * circ / gammaFn s) *
    vorticityShape s x * ((s - 1) - x)

/-- Manuscript Eq. (114): circulation differentiated along an arbitrary material scaled-radius
history satisfying Eq. (105). -/
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
  unfold gammaKernel vorticityShape
  ring

/-- The material circulation rate vanishes exactly at the distinguished scaled radius. -/
@[simp] theorem materialCirculationRate_at_star
    (nu beta circ s : ℝ) :
    materialCirculationRate nu beta circ s (s - 1) = 0 := by
  simp [materialCirculationRate]

/-- A material loop instantaneously on `x=s-1` has zero circulation derivative. -/
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

/-- Exact circulation enclosed by the distinguished cylinder, manuscript Eq. (118). -/
theorem materialCirculation_at_star (circ s : ℝ) :
    materialCirculationFromX circ s (s - 1) =
      circ * regLowerGamma s (s - 1) := by
  rfl

/-- The enclosed distributed-circulation fraction depends only on `s`, manuscript Eq. (119). -/
theorem materialCirculation_fraction_at_star
    {circ s : ℝ} (hcirc : circ ≠ 0) :
    materialCirculationFromX circ s (s - 1) / circ =
      regLowerGamma s (s - 1) := by
  unfold materialCirculationFromX
  field_simp [hcirc]

/-- The material-cylinder radius and the Pass-4 peak-vorticity radius are definitionally
the same physical radius, manuscript Eq. (112). -/
theorem materialRadius_eq_vorticityPeakRadius (s beta : ℝ) :
    materialRadius s beta = vorticityPeakRadius s beta := by
  rfl

/-- Therefore the distinguished material cylinder carries the one-mode vorticity extremum. -/
theorem distributedVorticity_deriv_at_materialRadius
    {circ s beta : ℝ} (hs : 1 < s) (hbeta : 0 < beta) :
    deriv (distributedVorticity circ s beta) (materialRadius s beta) = 0 := by
  rw [materialRadius_eq_vorticityPeakRadius]
  exact distributedVorticity_deriv_at_peak hs hbeta

/-- Eq. (116): the material circulation-rate formula is exactly the viscous circulation
transfer `2*pi*nu*r*partial_r omega_z` on a positive one-mode cylinder. -/
theorem materialCirculationRate_eq_viscousFlux
    {nu beta circ s r : ℝ}
    (hs : 0 < s) (hbeta : 0 < beta) (hr : 0 < r) :
    materialCirculationRate nu beta circ s (scaledX beta r) =
      2 * Real.pi * nu * r * deriv (distributedVorticity circ s beta) r := by
  rw [(distributedVorticity_hasDerivAt_r
    (circ := circ) (s := s) (beta := beta) (r := r) hs hbeta hr).deriv]
  have hx : 0 < scaledX beta r := by
    unfold scaledX
    positivity
  unfold materialCirculationRate distributedVorticity
  field_simp [gammaFn_ne_zero hs, Real.pi_ne_zero, hx.ne']
  unfold scaledX
  ring

/-- For positive circulation, circulation transfer is positive inside `x=s-1`. -/
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

/-- For positive circulation, circulation transfer is negative outside `x=s-1`. -/
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

/-- For negative circulation the transfer orientation is reversed inside the distinguished surface. -/
theorem materialCirculationRate_neg_before_star_of_circ_neg
    {nu beta circ s x : ℝ}
    (hnu : 0 < nu) (hbeta : 0 < beta) (hcirc : circ < 0)
    (hs : 0 < s) (hx : 0 < x) (hbefore : x < s - 1) :
    materialCirculationRate nu beta circ s x < 0 := by
  unfold materialCirculationRate
  have hpre : (4 * nu * beta * circ / gammaFn s) * vorticityShape s x < 0 := by
    have hG : 0 < gammaFn s := gammaFn_pos hs
    have hshape : 0 < vorticityShape s x := vorticityShape_pos hx
    have hnum : 4 * nu * beta * circ < 0 := by positivity
    have hfrac : 4 * nu * beta * circ / gammaFn s < 0 := div_neg_of_neg_of_pos hnum hG
    exact mul_neg_of_neg_of_pos hfrac hshape
  exact mul_neg_of_neg_of_pos hpre (sub_pos.mpr hbefore)

/-- For negative circulation the transfer orientation is reversed outside the distinguished surface. -/
theorem materialCirculationRate_pos_after_star_of_circ_neg
    {nu beta circ s x : ℝ}
    (hnu : 0 < nu) (hbeta : 0 < beta) (hcirc : circ < 0)
    (hs : 0 < s) (hx : 0 < x) (hafter : s - 1 < x) :
    0 < materialCirculationRate nu beta circ s x := by
  unfold materialCirculationRate
  have hpre : (4 * nu * beta * circ / gammaFn s) * vorticityShape s x < 0 := by
    have hG : 0 < gammaFn s := gammaFn_pos hs
    have hshape : 0 < vorticityShape s x := vorticityShape_pos hx
    have hnum : 4 * nu * beta * circ < 0 := by positivity
    have hfrac : 4 * nu * beta * circ / gammaFn s < 0 := div_neg_of_neg_of_pos hnum hG
    exact mul_neg_of_neg_of_pos hfrac hshape
  exact mul_pos_of_neg_of_neg hpre (sub_neg.mpr hafter)

end

end KiknadzeKrasnov
