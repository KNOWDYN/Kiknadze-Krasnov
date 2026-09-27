import KiknadzeKrasnov.VorticityCore
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace KiknadzeKrasnov

noncomputable section

open Set

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
Source-domain form of the radial invariant: the integrating-factor quantity
is constant between any two times in the physical interval [0,T), using only
the differential hypotheses on that interval.
-/
theorem radialInvariant_eq_on
    {T : ℝ} {a beta y betaDot : ℝ → ℝ} {nu q s t₁ t₂ : ℝ}
    (hA : ∀ t ∈ TimeDomain T, HasDerivAt (strainAccum a) (a t) t)
    (hbeta : ∀ t ∈ TimeDomain T, HasDerivAt beta (betaDot t) t)
    (hbetane : ∀ t ∈ TimeDomain T, beta t ≠ 0)
    (hy : ∀ t ∈ TimeDomain T,
      HasDerivAt y (-a t * y t + 2 * q) t)
    (hscale : ∀ t ∈ TimeDomain T,
      betaScaleResidual nu (a t) (beta t) (betaDot t) = 0)
    (hcompat : q = 2 * nu * (s - 1))
    (ht₁ : t₁ ∈ TimeDomain T) (ht₂ : t₂ ∈ TimeDomain T) :
    radialInvariant a s beta y t₁ = radialInvariant a s beta y t₂ := by
  have hbound :
      ‖radialInvariant a s beta y t₂ - radialInvariant a s beta y t₁‖ ≤ 0 := by
    simpa using
      (Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := radialInvariant a s beta y)
        (f' := fun _ : ℝ => 0)
        (s := TimeDomain T)
        (C := 0)
        (fun t ht =>
          (radialInvariant_hasDerivAt_zero
            (hA t ht) (hbeta t ht) (hbetane t ht)
            (hy t ht) (hscale t ht) hcompat).hasDerivWithinAt)
        (fun _ _ => by simp)
        (by simpa [TimeDomain] using (convex_Ico (0 : ℝ) T))
        ht₁ ht₂)
  have hn :
      ‖radialInvariant a s beta y t₂ - radialInvariant a s beta y t₁‖ = 0 :=
    le_antisymm hbound (norm_nonneg _)
  have hsub :
      radialInvariant a s beta y t₂ - radialInvariant a s beta y t₁ = 0 :=
    norm_eq_zero.mp hn
  exact (sub_eq_zero.mp hsub).symm

/-- Physical-time-domain invariance of the distinguished material cylinder. -/
theorem materialSurface_invariant_on
    {T : ℝ} {a beta y betaDot : ℝ → ℝ} {nu q s t₀ t : ℝ}
    (hA : ∀ tau ∈ TimeDomain T, HasDerivAt (strainAccum a) (a tau) tau)
    (hbeta : ∀ tau ∈ TimeDomain T, HasDerivAt beta (betaDot tau) tau)
    (hbetane : ∀ tau ∈ TimeDomain T, beta tau ≠ 0)
    (hy : ∀ tau ∈ TimeDomain T,
      HasDerivAt y (-a tau * y tau + 2 * q) tau)
    (hscale : ∀ tau ∈ TimeDomain T,
      betaScaleResidual nu (a tau) (beta tau) (betaDot tau) = 0)
    (hcompat : q = 2 * nu * (s - 1))
    (ht₀ : t₀ ∈ TimeDomain T) (ht : t ∈ TimeDomain T)
    (hinit : y t₀ = materialRadiusSq s (beta t₀)) :
    y t = materialRadiusSq s (beta t) := by
  have hI :=
    radialInvariant_eq_on hA hbeta hbetane hy hscale hcompat ht₀ ht
  unfold radialInvariant materialOffsetSq at hI
  rw [hinit, sub_self, mul_zero] at hI
  have hexp : Real.exp (strainAccum a t) ≠ 0 := (Real.exp_pos _).ne'
  exact sub_eq_zero.mp ((mul_eq_zero.mp hI.symm).resolve_left hexp)

/-- Physical-time-domain no-crossing theorem for the distinguished cylinder. -/
theorem materialSurface_no_crossing_on
    {T : ℝ} {a beta y betaDot : ℝ → ℝ} {nu q s t₀ t : ℝ}
    (hA : ∀ tau ∈ TimeDomain T, HasDerivAt (strainAccum a) (a tau) tau)
    (hbeta : ∀ tau ∈ TimeDomain T, HasDerivAt beta (betaDot tau) tau)
    (hbetane : ∀ tau ∈ TimeDomain T, beta tau ≠ 0)
    (hy : ∀ tau ∈ TimeDomain T,
      HasDerivAt y (-a tau * y tau + 2 * q) tau)
    (hscale : ∀ tau ∈ TimeDomain T,
      betaScaleResidual nu (a tau) (beta tau) (betaDot tau) = 0)
    (hcompat : q = 2 * nu * (s - 1))
    (ht₀ : t₀ ∈ TimeDomain T) (ht : t ∈ TimeDomain T)
    (hinit : y t₀ ≠ materialRadiusSq s (beta t₀)) :
    y t ≠ materialRadiusSq s (beta t) := by
  intro hcross
  have hI :=
    radialInvariant_eq_on hA hbeta hbetane hy hscale hcompat ht₀ ht
  unfold radialInvariant materialOffsetSq at hI
  rw [hcross, sub_self, mul_zero] at hI
  have hexp : Real.exp (strainAccum a t₀) ≠ 0 := (Real.exp_pos _).ne'
  have hzero : y t₀ - materialRadiusSq s (beta t₀) = 0 :=
    (mul_eq_zero.mp hI).resolve_left hexp
  exact hinit (sub_eq_zero.mp hzero)

/-- Outside ordering is preserved on the physical time interval. -/
theorem materialOffsetSq_pos_iff_on
    {T : ℝ} {a beta y betaDot : ℝ → ℝ} {nu q s t₁ t₂ : ℝ}
    (hA : ∀ t ∈ TimeDomain T, HasDerivAt (strainAccum a) (a t) t)
    (hbeta : ∀ t ∈ TimeDomain T, HasDerivAt beta (betaDot t) t)
    (hbetane : ∀ t ∈ TimeDomain T, beta t ≠ 0)
    (hy : ∀ t ∈ TimeDomain T,
      HasDerivAt y (-a t * y t + 2 * q) t)
    (hscale : ∀ t ∈ TimeDomain T,
      betaScaleResidual nu (a t) (beta t) (betaDot t) = 0)
    (hcompat : q = 2 * nu * (s - 1))
    (ht₁ : t₁ ∈ TimeDomain T) (ht₂ : t₂ ∈ TimeDomain T) :
    0 < materialOffsetSq s (beta t₁) (y t₁) ↔
      0 < materialOffsetSq s (beta t₂) (y t₂) := by
  have hI :=
    radialInvariant_eq_on hA hbeta hbetane hy hscale hcompat ht₁ ht₂
  unfold radialInvariant at hI
  constructor
  · intro hpos
    have hleft :
        0 < Real.exp (strainAccum a t₁) *
          materialOffsetSq s (beta t₁) (y t₁) :=
      mul_pos (Real.exp_pos _) hpos
    rw [hI] at hleft
    by_contra hnot
    have hnonpos : materialOffsetSq s (beta t₂) (y t₂) ≤ 0 :=
      le_of_not_gt hnot
    have hright :
        Real.exp (strainAccum a t₂) *
          materialOffsetSq s (beta t₂) (y t₂) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hnonpos
    linarith
  · intro hpos
    have hright :
        0 < Real.exp (strainAccum a t₂) *
          materialOffsetSq s (beta t₂) (y t₂) :=
      mul_pos (Real.exp_pos _) hpos
    rw [← hI] at hright
    by_contra hnot
    have hnonpos : materialOffsetSq s (beta t₁) (y t₁) ≤ 0 :=
      le_of_not_gt hnot
    have hleft :
        Real.exp (strainAccum a t₁) *
          materialOffsetSq s (beta t₁) (y t₁) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hnonpos
    linarith

/-- Inside ordering is preserved on the physical time interval. -/
theorem materialOffsetSq_neg_iff_on
    {T : ℝ} {a beta y betaDot : ℝ → ℝ} {nu q s t₁ t₂ : ℝ}
    (hA : ∀ t ∈ TimeDomain T, HasDerivAt (strainAccum a) (a t) t)
    (hbeta : ∀ t ∈ TimeDomain T, HasDerivAt beta (betaDot t) t)
    (hbetane : ∀ t ∈ TimeDomain T, beta t ≠ 0)
    (hy : ∀ t ∈ TimeDomain T,
      HasDerivAt y (-a t * y t + 2 * q) t)
    (hscale : ∀ t ∈ TimeDomain T,
      betaScaleResidual nu (a t) (beta t) (betaDot t) = 0)
    (hcompat : q = 2 * nu * (s - 1))
    (ht₁ : t₁ ∈ TimeDomain T) (ht₂ : t₂ ∈ TimeDomain T) :
    materialOffsetSq s (beta t₁) (y t₁) < 0 ↔
      materialOffsetSq s (beta t₂) (y t₂) < 0 := by
  have hI :=
    radialInvariant_eq_on hA hbeta hbetane hy hscale hcompat ht₁ ht₂
  unfold radialInvariant at hI
  constructor
  · intro hneg
    have hleft :
        Real.exp (strainAccum a t₁) *
          materialOffsetSq s (beta t₁) (y t₁) < 0 :=
      mul_neg_of_pos_of_neg (Real.exp_pos _) hneg
    rw [hI] at hleft
    by_contra hnot
    have hnonneg : 0 ≤ materialOffsetSq s (beta t₂) (y t₂) :=
      le_of_not_gt hnot
    have hright :
        0 ≤ Real.exp (strainAccum a t₂) *
          materialOffsetSq s (beta t₂) (y t₂) :=
      mul_nonneg (Real.exp_pos _).le hnonneg
    linarith
  · intro hneg
    have hright :
        Real.exp (strainAccum a t₂) *
          materialOffsetSq s (beta t₂) (y t₂) < 0 :=
      mul_neg_of_pos_of_neg (Real.exp_pos _) hneg
    rw [← hI] at hright
    by_contra hnot
    have hnonneg : 0 ≤ materialOffsetSq s (beta t₁) (y t₁) :=
      le_of_not_gt hnot
    have hleft :
        0 ≤ Real.exp (strainAccum a t₁) *
          materialOffsetSq s (beta t₁) (y t₁) :=
      mul_nonneg (Real.exp_pos _).le hnonneg
    linarith


end

end KiknadzeKrasnov
