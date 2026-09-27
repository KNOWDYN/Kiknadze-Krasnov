import KiknadzeKrasnov.VorticityCore
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace KiknadzeKrasnov

noncomputable section

/-!
Pass 4 material-motion layer for manuscript Eqs. (103)--(112) and
Supplementary Eqs. (18)--(26).  The source-bearing distinguished radius is
proved to obey the same radial particle law as the fluid.
-/

/-- Algebraic rate form of the Pass-3B scale residual. -/
theorem betaScaleResidual_zero_iff_rate {nu a beta betaDot : ℝ} :
    betaScaleResidual nu a beta betaDot = 0 ↔
      betaDot = a * beta - 4 * nu * beta ^ 2 := by
  unfold betaScaleResidual
  constructor <;> intro h <;> linarith

/-- Squared-radius offset from the distinguished material cylinder. -/
def materialOffsetSq (s beta y : ℝ) : ℝ := y - materialRadiusSq s beta

/-- Physical positive radius corresponding to rStar^2=(s-1)/beta. -/
def materialRadius (s beta : ℝ) : ℝ := Real.sqrt (materialRadiusSq s beta)

/-- Radial integrating-factor quantity from manuscript Eq. (112). -/
def radialInvariant (a : ℝ → ℝ) (s : ℝ) (beta y : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (strainAccum a t) * materialOffsetSq s (beta t) (y t)

/--
Manuscript Eqs. (103)--(106): for a material squared-radius y=r^2,
x=beta*y has rate 4 nu beta ((s-1)-x).
-/
theorem scaledMaterial_hasDerivAt
    {beta y : ℝ → ℝ} {betaDot nu a q s t : ℝ}
    (hbeta : HasDerivAt beta betaDot t)
    (hy : HasDerivAt y (-a * y t + 2 * q) t)
    (hscale : betaScaleResidual nu a (beta t) betaDot = 0)
    (hcompat : q = 2 * nu * (s - 1)) :
    HasDerivAt (fun tau => beta tau * y tau)
      (4 * nu * beta t * ((s - 1) - beta t * y t)) t := by
  have hprod := hbeta.mul hy
  convert hprod using 1
  have hbdot := (betaScaleResidual_zero_iff_rate.mp hscale)
  rw [hbdot, hcompat]
  ring

/-- At x=s-1, the material scaled-radius rate vanishes exactly. -/
theorem scaledMaterial_hasDerivAt_zero_at_star
    {beta y : ℝ → ℝ} {betaDot nu a q s t : ℝ}
    (hbeta : HasDerivAt beta betaDot t)
    (hy : HasDerivAt y (-a * y t + 2 * q) t)
    (hscale : betaScaleResidual nu a (beta t) betaDot = 0)
    (hcompat : q = 2 * nu * (s - 1))
    (hstar : beta t * y t = s - 1) :
    HasDerivAt (fun tau => beta tau * y tau) 0 t := by
  convert scaledMaterial_hasDerivAt hbeta hy hscale hcompat using 1
  rw [hstar]
  ring

/-- Below x=s-1, the instantaneous scaled material motion points upward. -/
theorem scaledMaterial_rate_pos_before_star
    {nu beta s x : ℝ} (hnu : 0 < nu) (hbeta : 0 < beta) (hx : x < s - 1) :
    0 < 4 * nu * beta * ((s - 1) - x) := by
  positivity

/-- Above x=s-1, the instantaneous scaled material motion points downward. -/
theorem scaledMaterial_rate_neg_after_star
    {nu beta s x : ℝ} (hnu : 0 < nu) (hbeta : 0 < beta) (hx : s - 1 < x) :
    4 * nu * beta * ((s - 1) - x) < 0 := by
  have hleft : 0 < 4 * nu * beta := by positivity
  exact mul_neg_of_pos_of_neg hleft (sub_neg.mpr hx)

/-- Differentiation of h=1/beta for a genuine scale history. -/
theorem inverseScale_history_hasDerivAt
    {beta : ℝ → ℝ} {betaDot t : ℝ}
    (hbeta : HasDerivAt beta betaDot t) (hne : beta t ≠ 0) :
    HasDerivAt (fun tau => inverseScale (beta tau))
      (-betaDot / (beta t) ^ 2) t := by
  unfold inverseScale
  exact hbeta.inv hne

/-- The Riccati scale law gives h'=-a h+4 nu. -/
theorem inverseScale_history_ode
    {beta : ℝ → ℝ} {betaDot nu a t : ℝ}
    (hbeta : HasDerivAt beta betaDot t) (hne : beta t ≠ 0)
    (hscale : betaScaleResidual nu a (beta t) betaDot = 0) :
    HasDerivAt (fun tau => inverseScale (beta tau))
      (4 * nu - a * inverseScale (beta t)) t := by
  have hrec := inverseScale_history_hasDerivAt hbeta hne
  convert hrec using 1
  have hbdot := betaScaleResidual_zero_iff_rate.mp hscale
  unfold inverseScale
  rw [hbdot]
  field_simp [hne]
  ring

/--
Manuscript Eqs. (108)--(110): rStar^2=(s-1)/beta obeys
(rStar^2)'=-a rStar^2+2q.
-/
theorem materialRadiusSq_history_hasDerivAt
    {beta : ℝ → ℝ} {betaDot nu a q s t : ℝ}
    (hbeta : HasDerivAt beta betaDot t)
    (hne : beta t ≠ 0)
    (hscale : betaScaleResidual nu a (beta t) betaDot = 0)
    (hcompat : q = 2 * nu * (s - 1)) :
    HasDerivAt (fun tau => materialRadiusSq s (beta tau))
      (-a * materialRadiusSq s (beta t) + 2 * q) t := by
  have hh := inverseScale_history_ode
    (nu := nu) (a := a) hbeta hne hscale
  have hmul := hh.const_mul (s - 1)
  convert hmul using 1
  · funext tau
    simp only [materialRadiusSq, inverseScale, div_eq_mul_inv]
  · rw [hcompat]
    simp only [materialRadiusSq, inverseScale, div_eq_mul_inv]
    ring

/-- On s>1 and beta>0, the distinguished physical radius is positive. -/
theorem materialRadius_pos {s beta : ℝ} (hs : 1 < s) (hbeta : 0 < beta) :
    0 < materialRadius s beta := by
  unfold materialRadius materialRadiusSq
  exact Real.sqrt_pos.2 (div_pos (sub_pos.mpr hs) hbeta)

/--
Manuscript Eq. (111): the distinguished physical cylinder is transported by
the actual KK radial velocity.
-/
theorem materialRadius_history_hasDerivAt
    {beta : ℝ → ℝ} {betaDot nu a q s t : ℝ}
    (hs : 1 < s) (hbetapos : 0 < beta t)
    (hbeta : HasDerivAt beta betaDot t)
    (hscale : betaScaleResidual nu a (beta t) betaDot = 0)
    (hcompat : q = 2 * nu * (s - 1)) :
    HasDerivAt (fun tau => materialRadius s (beta tau))
      (radialVelocity a q (materialRadius s (beta t))) t := by
  have hy := materialRadiusSq_history_hasDerivAt
    hbeta hbetapos.ne' hscale hcompat
  have hypos : 0 < materialRadiusSq s (beta t) := by
    unfold materialRadiusSq
    exact div_pos (sub_pos.mpr hs) hbetapos
  have hsqrt := hy.sqrt hypos.ne'
  unfold materialRadius
  convert hsqrt using 1
  have hrpos : 0 < Real.sqrt (materialRadiusSq s (beta t)) :=
    Real.sqrt_pos.2 hypos
  have hrsq :
      (Real.sqrt (materialRadiusSq s (beta t))) ^ 2 =
        materialRadiusSq s (beta t) :=
    Real.sq_sqrt hypos.le
  unfold radialVelocity
  field_simp [hrpos.ne']
  rw [hrsq]

/-- The material radius maps exactly to the invariant scaled value x=s-1. -/
theorem scaledX_materialRadius
    {s beta : ℝ} (hs : 1 < s) (hbeta : 0 < beta) :
    scaledX beta (materialRadius s beta) = s - 1 := by
  unfold scaledX materialRadius materialRadiusSq
  rw [Real.sq_sqrt (div_nonneg (by linarith) hbeta.le)]
  field_simp [hbeta.ne']

/-- Source form rStar^2=q/(2 nu beta). -/
theorem materialRadiusSq_eq_source_form
    {nu q s beta : ℝ}
    (hnu : nu ≠ 0) (hbeta : beta ≠ 0)
    (hcompat : q = 2 * nu * (s - 1)) :
    materialRadiusSq s beta = q / (2 * nu * beta) := by
  unfold materialRadiusSq
  rw [hcompat]
  field_simp [hnu, hbeta]

/--
The radial integrating factor has zero derivative along every material
squared-radius trajectory satisfying the KK scale and particle equations.
-/
theorem radialInvariant_hasDerivAt_zero
    {a beta y : ℝ → ℝ} {betaDot nu q s t : ℝ}
    (hA : HasDerivAt (strainAccum a) (a t) t)
    (hbeta : HasDerivAt beta betaDot t)
    (hbetane : beta t ≠ 0)
    (hy : HasDerivAt y (-a t * y t + 2 * q) t)
    (hscale : betaScaleResidual nu (a t) (beta t) betaDot = 0)
    (hcompat : q = 2 * nu * (s - 1)) :
    HasDerivAt (radialInvariant a s beta y) 0 t := by
  have hstar := materialRadiusSq_history_hasDerivAt
    (beta := beta) (betaDot := betaDot) (nu := nu) (a := a t)
    (q := q) (s := s) hbeta hbetane hscale hcompat
  have hoff := hy.sub hstar
  have hexp := hA.exp
  have hprod := hexp.mul hoff
  unfold radialInvariant materialOffsetSq
  convert hprod using 1
  simp only [Pi.sub_apply]
  ring

/--
Global algebraic form of manuscript Eq. (112). The hypotheses are deliberately
stated as differential hypotheses on the whole compared history; later
submission documentation records the physical restriction to the admissible
time interval.
-/
theorem radialInvariant_eq
    {a beta y betaDot : ℝ → ℝ} {nu q s t₁ t₂ : ℝ}
    (hA : ∀ t, HasDerivAt (strainAccum a) (a t) t)
    (hbeta : ∀ t, HasDerivAt beta (betaDot t) t)
    (hbetane : ∀ t, beta t ≠ 0)
    (hy : ∀ t, HasDerivAt y (-a t * y t + 2 * q) t)
    (hscale : ∀ t, betaScaleResidual nu (a t) (beta t) (betaDot t) = 0)
    (hcompat : q = 2 * nu * (s - 1)) :
    radialInvariant a s beta y t₁ = radialInvariant a s beta y t₂ := by
  apply is_const_of_deriv_eq_zero
  · intro t
    exact (radialInvariant_hasDerivAt_zero
      (hA t) (hbeta t) (hbetane t) (hy t) (hscale t) hcompat).differentiableAt
  · intro t
    exact (radialInvariant_hasDerivAt_zero
      (hA t) (hbeta t) (hbetane t) (hy t) (hscale t) hcompat).deriv

/-- A trajectory initially on the distinguished cylinder remains on it. -/
theorem materialSurface_invariant
    {a beta y betaDot : ℝ → ℝ} {nu q s t₀ t : ℝ}
    (hA : ∀ tau, HasDerivAt (strainAccum a) (a tau) tau)
    (hbeta : ∀ tau, HasDerivAt beta (betaDot tau) tau)
    (hbetane : ∀ tau, beta tau ≠ 0)
    (hy : ∀ tau, HasDerivAt y (-a tau * y tau + 2 * q) tau)
    (hscale : ∀ tau, betaScaleResidual nu (a tau) (beta tau) (betaDot tau) = 0)
    (hcompat : q = 2 * nu * (s - 1))
    (hinit : y t₀ = materialRadiusSq s (beta t₀)) :
    y t = materialRadiusSq s (beta t) := by
  have hI := radialInvariant_eq hA hbeta hbetane hy hscale hcompat
    (t₁ := t₀) (t₂ := t)
  unfold radialInvariant materialOffsetSq at hI
  rw [hinit, sub_self, mul_zero] at hI
  have hexp : Real.exp (strainAccum a t) ≠ 0 := (Real.exp_pos _).ne'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hI.symm).resolve_left hexp)

/-- A material trajectory that starts away from the cylinder cannot cross it. -/
theorem materialSurface_no_crossing
    {a beta y betaDot : ℝ → ℝ} {nu q s t₀ t : ℝ}
    (hA : ∀ tau, HasDerivAt (strainAccum a) (a tau) tau)
    (hbeta : ∀ tau, HasDerivAt beta (betaDot tau) tau)
    (hbetane : ∀ tau, beta tau ≠ 0)
    (hy : ∀ tau, HasDerivAt y (-a tau * y tau + 2 * q) tau)
    (hscale : ∀ tau, betaScaleResidual nu (a tau) (beta tau) (betaDot tau) = 0)
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

end

end KiknadzeKrasnov
