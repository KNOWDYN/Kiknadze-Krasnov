import KiknadzeKrasnov.Trajectories
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace KiknadzeKrasnov

noncomputable section

/-- Squared-radius offset from the distinguished material cylinder. -/
def materialOffsetSq (s beta y : ℝ) : ℝ := y - materialRadiusSq s beta

/-- Radial integrating-factor invariant from manuscript Eq. (110). -/
def radialInvariant (a : ℝ → ℝ) (s : ℝ) (beta y : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (strainAccum a t) * materialOffsetSq s (beta t) (y t)

/-- Exact local transport law for `x=beta*r^2`, manuscript Eq. (105).  The variable `y`
is the squared material radius, so no division by `r` is required in this theorem. -/
theorem scaledMaterial_hasDerivAt
    {beta y : ℝ → ℝ} {betaDot nu a q s t : ℝ}
    (hbeta : HasDerivAt beta betaDot t)
    (hy : HasDerivAt y (-a * y t + 2 * q) t)
    (hscale : scaleResidual nu a (beta t) betaDot = 0)
    (hcompat : q = 2 * nu * (s - 1)) :
    HasDerivAt (fun tau => beta tau * y tau)
      (4 * nu * beta t * ((s - 1) - beta t * y t)) t := by
  have hprod := hbeta.mul hy
  convert hprod using 1
  have hbdot := scaleResidual_zero_iff.mp hscale
  rw [hbdot, hcompat]
  ring

/-- At `x=s-1`, the scaled material-radius derivative vanishes exactly. -/
theorem scaledMaterial_hasDerivAt_zero_at_star
    {beta y : ℝ → ℝ} {betaDot nu a q s t : ℝ}
    (hbeta : HasDerivAt beta betaDot t)
    (hy : HasDerivAt y (-a * y t + 2 * q) t)
    (hscale : scaleResidual nu a (beta t) betaDot = 0)
    (hcompat : q = 2 * nu * (s - 1))
    (hstar : beta t * y t = s - 1) :
    HasDerivAt (fun tau => beta tau * y tau) 0 t := by
  convert scaledMaterial_hasDerivAt hbeta hy hscale hcompat using 1
  rw [hstar]
  ring

/-- Below the invariant scaled radius, the instantaneous material motion is outward in `x`. -/
theorem scaledMaterial_rate_pos_before_star
    {nu beta s x : ℝ} (hnu : 0 < nu) (hbeta : 0 < beta) (hx : x < s - 1) :
    0 < 4 * nu * beta * ((s - 1) - x) := by
  positivity

/-- Above the invariant scaled radius, the instantaneous material motion is inward in `x`. -/
theorem scaledMaterial_rate_neg_after_star
    {nu beta s x : ℝ} (hnu : 0 < nu) (hbeta : 0 < beta) (hx : s - 1 < x) :
    4 * nu * beta * ((s - 1) - x) < 0 := by
  have hleft : 0 < 4 * nu * beta := by positivity
  exact mul_neg_of_pos_of_neg hleft (sub_neg.mpr hx)

/-- The distinguished squared radius `(s-1)/beta` obeys the same squared-radius
particle equation as the fluid, manuscript Eqs. (107)--(108). -/
theorem materialRadiusSq_history_hasDerivAt
    {beta : ℝ → ℝ} {betaDot nu a q s t : ℝ}
    (hbeta : HasDerivAt beta betaDot t)
    (hne : beta t ≠ 0)
    (hscale : scaleResidual nu a (beta t) betaDot = 0)
    (hcompat : q = 2 * nu * (s - 1)) :
    HasDerivAt (fun tau => materialRadiusSq s (beta tau))
      (-a * materialRadiusSq s (beta t) + 2 * q) t := by
  have hh := inverseScale_ode (nu := nu) (a := a) hbeta hne hscale
  have hmul := hh.const_mul (s - 1)
  convert hmul using 1
  · funext tau
    simp only [materialRadiusSq, inverseScale, div_eq_mul_inv]
  · rw [hcompat]
    simp only [materialRadiusSq, inverseScale, div_eq_mul_inv]
    ring

/-- Positive physical radius of the distinguished material cylinder. -/
def materialRadius (s beta : ℝ) : ℝ := Real.sqrt (materialRadiusSq s beta)

/-- On the source-bearing branch, the distinguished material radius is positive. -/
theorem materialRadius_pos {s beta : ℝ} (hs : 1 < s) (hbeta : 0 < beta) :
    0 < materialRadius s beta := by
  unfold materialRadius materialRadiusSq
  exact Real.sqrt_pos.2 (div_pos (sub_pos.mpr hs) hbeta)

/-- The distinguished physical radius is transported by the radial KK velocity,
manuscript Eq. (109). -/
theorem materialRadius_history_hasDerivAt
    {beta : ℝ → ℝ} {betaDot nu a q s t : ℝ}
    (hs : 1 < s) (hbetapos : 0 < beta t)
    (hbeta : HasDerivAt beta betaDot t)
    (hscale : scaleResidual nu a (beta t) betaDot = 0)
    (hcompat : q = 2 * nu * (s - 1)) :
    HasDerivAt (fun tau => materialRadius s (beta tau))
      (radialVelocity a q (materialRadius s (beta t))) t := by
  have hy := materialRadiusSq_history_hasDerivAt hbeta hbetapos.ne' hscale hcompat
  have hypos : 0 < materialRadiusSq s (beta t) := by
    unfold materialRadiusSq
    exact div_pos (sub_pos.mpr hs) hbetapos
  have hsqrt := hy.sqrt hypos.ne'
  unfold materialRadius
  convert hsqrt using 1
  have hrpos : 0 < Real.sqrt (materialRadiusSq s (beta t)) := Real.sqrt_pos.2 hypos
  have hrsq : (Real.sqrt (materialRadiusSq s (beta t))) ^ 2 = materialRadiusSq s (beta t) :=
    Real.sq_sqrt hypos.le
  unfold radialVelocity
  rw [hcompat]
  field_simp [hrpos.ne']
  nlinarith

/-- The radial integrating factor has zero derivative along every material squared-radius
trajectory satisfying the KK scale and particle equations. -/
theorem radialInvariant_hasDerivAt_zero
    {a beta y : ℝ → ℝ} {betaDot nu q s t : ℝ}
    (hA : HasDerivAt (strainAccum a) (a t) t)
    (hbeta : HasDerivAt beta betaDot t)
    (hbetane : beta t ≠ 0)
    (hy : HasDerivAt y (-a t * y t + 2 * q) t)
    (hscale : scaleResidual nu (a t) (beta t) betaDot = 0)
    (hcompat : q = 2 * nu * (s - 1)) :
    HasDerivAt (radialInvariant a s beta y) 0 t := by
  have hstar := materialRadiusSq_history_hasDerivAt
    (beta := beta) (betaDot := betaDot) (nu := nu) (a := a t)
    (q := q) (s := s) hbeta hbetane hscale hcompat
  have hoff := hy.sub hstar
  have hexp := hA.exp
  have hprod := hexp.mul hoff
  unfold radialInvariant materialOffsetSq at *
  convert hprod using 1
  ring

/-- Global form of manuscript Eq. (110): if the KK differential hypotheses hold for all
real times under consideration, the radial integrating-factor quantity is constant. -/
theorem radialInvariant_eq
    {a beta y betaDot : ℝ → ℝ} {nu q s t₁ t₂ : ℝ}
    (hA : ∀ t, HasDerivAt (strainAccum a) (a t) t)
    (hbeta : ∀ t, HasDerivAt beta (betaDot t) t)
    (hbetane : ∀ t, beta t ≠ 0)
    (hy : ∀ t, HasDerivAt y (-a t * y t + 2 * q) t)
    (hscale : ∀ t, scaleResidual nu (a t) (beta t) (betaDot t) = 0)
    (hcompat : q = 2 * nu * (s - 1)) :
    radialInvariant a s beta y t₁ = radialInvariant a s beta y t₂ := by
  apply is_const_of_deriv_eq_zero
  · intro t
    exact (radialInvariant_hasDerivAt_zero
      (hA t) (hbeta t) (hbetane t) (hy t) (hscale t) hcompat).differentiableAt
  · intro t
    exact (radialInvariant_hasDerivAt_zero
      (hA t) (hbeta t) (hbetane t) (hy t) (hscale t) hcompat).deriv

/-- A trajectory initially on the distinguished cylinder remains on it: the exact
no-crossing/invariance statement for `x=s-1`. -/
theorem materialSurface_invariant
    {a beta y betaDot : ℝ → ℝ} {nu q s t₀ t : ℝ}
    (hA : ∀ tau, HasDerivAt (strainAccum a) (a tau) tau)
    (hbeta : ∀ tau, HasDerivAt beta (betaDot tau) tau)
    (hbetane : ∀ tau, beta tau ≠ 0)
    (hy : ∀ tau, HasDerivAt y (-a tau * y tau + 2 * q) tau)
    (hscale : ∀ tau, scaleResidual nu (a tau) (beta tau) (betaDot tau) = 0)
    (hcompat : q = 2 * nu * (s - 1))
    (hinit : y t₀ = materialRadiusSq s (beta t₀)) :
    y t = materialRadiusSq s (beta t) := by
  have hI := radialInvariant_eq hA hbeta hbetane hy hscale hcompat
    (t₁ := t₀) (t₂ := t)
  unfold radialInvariant materialOffsetSq at hI
  rw [hinit, sub_self, mul_zero] at hI
  have hexp : Real.exp (strainAccum a t) ≠ 0 := (Real.exp_pos _).ne'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hI.symm).resolve_left hexp)

/-- A material trajectory that starts away from the distinguished cylinder cannot cross it. -/
theorem materialSurface_no_crossing
    {a beta y betaDot : ℝ → ℝ} {nu q s t₀ t : ℝ}
    (hA : ∀ tau, HasDerivAt (strainAccum a) (a tau) tau)
    (hbeta : ∀ tau, HasDerivAt beta (betaDot tau) tau)
    (hbetane : ∀ tau, beta tau ≠ 0)
    (hy : ∀ tau, HasDerivAt y (-a tau * y tau + 2 * q) tau)
    (hscale : ∀ tau, scaleResidual nu (a tau) (beta tau) (betaDot tau) = 0)
    (hcompat : q = 2 * nu * (s - 1))
    (hinit : y t₀ ≠ materialRadiusSq s (beta t₀)) :
    y t ≠ materialRadiusSq s (beta t) := by
  intro hcross
  have hI := radialInvariant_eq hA hbeta hbetane hy hscale hcompat
    (t₁ := t₀) (t₂ := t)
  unfold radialInvariant materialOffsetSq at hI
  rw [hcross, sub_self, mul_zero] at hI
  have hexp : Real.exp (strainAccum a t₀) ≠ 0 := (Real.exp_pos _).ne'
  have hzero : y t₀ - materialRadiusSq s (beta t₀) = 0 :=
    (mul_eq_zero.mp hI).resolve_left hexp
  exact hinit (sub_eq_zero.mp hzero)

/-- Inside/outside ordering relative to the material cylinder is preserved. -/
theorem materialOffsetSq_pos_iff
    {a beta y betaDot : ℝ → ℝ} {nu q s t₁ t₂ : ℝ}
    (hA : ∀ t, HasDerivAt (strainAccum a) (a t) t)
    (hbeta : ∀ t, HasDerivAt beta (betaDot t) t)
    (hbetane : ∀ t, beta t ≠ 0)
    (hy : ∀ t, HasDerivAt y (-a t * y t + 2 * q) t)
    (hscale : ∀ t, scaleResidual nu (a t) (beta t) (betaDot t) = 0)
    (hcompat : q = 2 * nu * (s - 1)) :
    0 < materialOffsetSq s (beta t₁) (y t₁) ↔
      0 < materialOffsetSq s (beta t₂) (y t₂) := by
  have hI := radialInvariant_eq hA hbeta hbetane hy hscale hcompat
    (t₁ := t₁) (t₂ := t₂)
  unfold radialInvariant at hI
  constructor
  · intro hpos
    have hleft : 0 < Real.exp (strainAccum a t₁) * materialOffsetSq s (beta t₁) (y t₁) :=
      mul_pos (Real.exp_pos _) hpos
    rw [hI] at hleft
    by_contra hnot
    have hnonpos : materialOffsetSq s (beta t₂) (y t₂) ≤ 0 := le_of_not_gt hnot
    have : Real.exp (strainAccum a t₂) * materialOffsetSq s (beta t₂) (y t₂) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hnonpos
    linarith
  · intro hpos
    have hright : 0 < Real.exp (strainAccum a t₂) * materialOffsetSq s (beta t₂) (y t₂) :=
      mul_pos (Real.exp_pos _) hpos
    rw [← hI] at hright
    by_contra hnot
    have hnonpos : materialOffsetSq s (beta t₁) (y t₁) ≤ 0 := le_of_not_gt hnot
    have : Real.exp (strainAccum a t₁) * materialOffsetSq s (beta t₁) (y t₁) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hnonpos
    linarith

end

end KiknadzeKrasnov
