import KiknadzeKrasnov.ScaleDynamics

namespace KiknadzeKrasnov

noncomputable section

open Set intervalIntegral

/-!
Formal layer for the Nature-level interpretation of selective material
conservation.  No new physical model is introduced here: the theorems assemble
and sharpen consequences already implied by the KK material-radius and
circulation identities.
-/

/-- Scaled displacement from the distinguished material partition x*=s-1. -/
def scaledOffset (s x : ℝ) : ℝ := x - (s - 1)

/-- Viscous clock B(t)=∫₀ᵗ 4 nu beta(tau) d tau controlling scaled-radius contraction. -/
def diffusiveClock (nu : ℝ) (beta : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ tau in 0..t, 4 * nu * beta tau

@[simp] theorem diffusiveClock_zero (nu : ℝ) (beta : ℝ → ℝ) :
    diffusiveClock nu beta 0 = 0 := by
  simp [diffusiveClock]

/--
If x obeys the exact KK scaled-material law x'=4 nu beta ((s-1)-x),
then exp(B(t)) (x-(s-1)) has zero derivative, where B'=4 nu beta.
-/
theorem scaledOffset_integratingFactor_hasDerivAt_zero
    {x beta : ℝ → ℝ} {nu s t : ℝ}
    (hB : HasDerivAt (diffusiveClock nu beta) (4 * nu * beta t) t)
    (hx : HasDerivAt x
      (4 * nu * beta t * ((s - 1) - x t)) t) :
    HasDerivAt
      (fun tau =>
        Real.exp (diffusiveClock nu beta tau) * scaledOffset s (x tau))
      0 t := by
  have hExp := hB.exp
  have hOff :
      HasDerivAt (fun tau => scaledOffset s (x tau))
        (4 * nu * beta t * ((s - 1) - x t)) t := by
    unfold scaledOffset
    simpa using hx.sub_const (s - 1)
  have hProd := hExp.mul hOff
  convert hProd using 1
  · rfl
  · unfold scaledOffset
    ring

/--
The integrating-factor quantity is constant between any two physical times
when the scaled-radius law and diffusive-clock derivative hold throughout the
physical interval.
-/
theorem scaledOffset_integratingFactor_eq_on
    {T nu s : ℝ} {x beta : ℝ → ℝ} {t₁ t₂ : ℝ}
    (hB : ∀ t ∈ TimeDomain T,
      HasDerivAt (diffusiveClock nu beta) (4 * nu * beta t) t)
    (hx : ∀ t ∈ TimeDomain T,
      HasDerivAt x (4 * nu * beta t * ((s - 1) - x t)) t)
    (ht₁ : t₁ ∈ TimeDomain T) (ht₂ : t₂ ∈ TimeDomain T) :
    Real.exp (diffusiveClock nu beta t₁) * scaledOffset s (x t₁) =
      Real.exp (diffusiveClock nu beta t₂) * scaledOffset s (x t₂) := by
  let F : ℝ → ℝ := fun t =>
    Real.exp (diffusiveClock nu beta t) * scaledOffset s (x t)
  have hbound : ‖F t₂ - F t₁‖ ≤ 0 := by
    simpa [F] using
      (Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := F)
        (f' := fun _ : ℝ => 0)
        (s := TimeDomain T)
        (C := 0)
        (fun t ht =>
          (scaledOffset_integratingFactor_hasDerivAt_zero
            (hB t ht) (hx t ht)).hasDerivWithinAt)
        (fun _ _ => by simp)
        (by simpa [TimeDomain] using (convex_Ico (0 : ℝ) T))
        ht₁ ht₂)
  have hn : ‖F t₂ - F t₁‖ = 0 :=
    le_antisymm hbound (norm_nonneg _)
  have hsub : F t₂ - F t₁ = 0 := norm_eq_zero.mp hn
  exact (sub_eq_zero.mp hsub).symm

/--
Exact exponential evolution of the scaled displacement from x*=s-1:
  x(t2)-x* = (x(t1)-x*) exp(-(B(t2)-B(t1))).
This is the formal basis for dynamic selection of the material partition.
-/
theorem scaledOffset_exact_exponential
    {T nu s : ℝ} {x beta : ℝ → ℝ} {t₁ t₂ : ℝ}
    (hB : ∀ t ∈ TimeDomain T,
      HasDerivAt (diffusiveClock nu beta) (4 * nu * beta t) t)
    (hx : ∀ t ∈ TimeDomain T,
      HasDerivAt x (4 * nu * beta t * ((s - 1) - x t)) t)
    (ht₁ : t₁ ∈ TimeDomain T) (ht₂ : t₂ ∈ TimeDomain T) :
    scaledOffset s (x t₂) =
      scaledOffset s (x t₁) *
        Real.exp (-(diffusiveClock nu beta t₂ - diffusiveClock nu beta t₁)) := by
  have hI := scaledOffset_integratingFactor_eq_on hB hx ht₁ ht₂
  have hcancel :
      Real.exp (-diffusiveClock nu beta t₂) *
          Real.exp (diffusiveClock nu beta t₂) = 1 := by
    rw [← Real.exp_add]
    simp
  have hratio :
      Real.exp (-diffusiveClock nu beta t₂) *
          Real.exp (diffusiveClock nu beta t₁) =
        Real.exp (-(diffusiveClock nu beta t₂ - diffusiveClock nu beta t₁)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    scaledOffset s (x t₂)
        = (Real.exp (-diffusiveClock nu beta t₂) *
            Real.exp (diffusiveClock nu beta t₂)) * scaledOffset s (x t₂) := by
              rw [hcancel]
    _ = Real.exp (-diffusiveClock nu beta t₂) *
          (Real.exp (diffusiveClock nu beta t₂) * scaledOffset s (x t₂)) := by ring
    _ = Real.exp (-diffusiveClock nu beta t₂) *
          (Real.exp (diffusiveClock nu beta t₁) * scaledOffset s (x t₁)) := by
            rw [← hI]
    _ = (Real.exp (-diffusiveClock nu beta t₂) *
          Real.exp (diffusiveClock nu beta t₁)) * scaledOffset s (x t₁) := by ring
    _ = Real.exp (-(diffusiveClock nu beta t₂ - diffusiveClock nu beta t₁)) *
          scaledOffset s (x t₁) := by rw [hratio]
    _ = scaledOffset s (x t₁) *
          Real.exp (-(diffusiveClock nu beta t₂ - diffusiveClock nu beta t₁)) := by ring

/-- The exact viscous contraction factor is strictly between zero and one when the clock advances. -/
theorem diffusiveFactor_pos_lt_one {B₁ B₂ : ℝ} (hB : B₁ < B₂) :
    0 < Real.exp (-(B₂ - B₁)) ∧ Real.exp (-(B₂ - B₁)) < 1 := by
  constructor
  · exact Real.exp_pos _
  · have hneg : -(B₂ - B₁) < 0 := by linarith
    have h := Real.exp_lt_exp.mpr hneg
    simpa using h

/--
Sign-safe circulation-transfer partition: multiplying the transfer rate by the
circulation sign gives positive transfer inside x*=s-1 and negative transfer
outside, with zero transfer at x*.
-/
theorem selectiveTransferPartition
    {nu beta circ s : ℝ}
    (hnu : 0 < nu) (hbeta : 0 < beta) (hcirc : circ ≠ 0) (hs : 1 < s) :
    materialCirculationRate nu beta circ s (s - 1) = 0
      ∧ (∀ x : ℝ, 0 < x → x < s - 1 →
          0 < circ * materialCirculationRate nu beta circ s x)
      ∧ (∀ x : ℝ, 0 < x → s - 1 < x →
          circ * materialCirculationRate nu beta circ s x < 0) := by
  refine ⟨materialCirculationRate_at_star nu beta circ s, ?_, ?_⟩
  · intro x hx hbefore
    rcases lt_or_gt_of_ne hcirc with hneg | hpos
    · exact mul_pos_of_neg_of_neg hneg
        (materialCirculationRate_neg_before_star_of_circ_neg
          hnu hbeta hneg (by linarith) hx hbefore)
    · exact mul_pos hpos
        (materialCirculationRate_pos_before_star_of_circ_pos
          hnu hbeta hpos (by linarith) hx hbefore)
  · intro x hx hafter
    rcases lt_or_gt_of_ne hcirc with hneg | hpos
    · exact mul_neg_of_neg_of_pos hneg
        (materialCirculationRate_pos_after_star_of_circ_neg
          hnu hbeta hneg (by linarith) hx hafter)
    · exact mul_neg_of_pos_of_neg hpos
        (materialCirculationRate_neg_after_star_of_circ_pos
          hnu hbeta hpos (by linarith) hx hafter)

/--
The distinguished enclosed circulation fraction is independent of the positive
radial scale, and therefore of any admissible strain history acting only
through that scale.
-/
theorem distinguishedFraction_independent_of_scale
    {circ s beta₁ beta₂ : ℝ}
    (hcirc : circ ≠ 0) (hs : 1 < s) (hb₁ : 0 < beta₁) (hb₂ : 0 < beta₂) :
    materialCirculationFromX circ s
        (scaledX beta₁ (materialRadius s beta₁)) / circ =
      materialCirculationFromX circ s
        (scaledX beta₂ (materialRadius s beta₂)) / circ := by
  rw [scaledX_materialRadius hs hb₁, scaledX_materialRadius hs hb₂]

/--
Nature-level assembled consequence: at every physical time, the exact material
surface certified by `exactMaterialCirculationSurface` is also the separator of
opposite signed viscous circulation transfer on its two sides.
-/
theorem selectiveMaterialConservation
    (p : FluidParams) {T q circ : ℝ}
    {a beta betaDot : ℝ → ℝ}
    (hann : AnnularSourceBranch p q)
    (hcirc : circ ≠ 0)
    (hbetaPos : PositiveScaleOn T beta)
    (hbeta : ∀ t ∈ TimeDomain T, HasDerivAt beta (betaDot t) t)
    (hscale : ∀ t ∈ TimeDomain T,
      betaScaleResidual p.nu (a t) (beta t) (betaDot t) = 0) :
    (∀ t ∈ TimeDomain T,
      HasDerivAt
        (fun tau => materialRadius (shape p q) (beta tau))
        (radialVelocity (a t) q
          (materialRadius (shape p q) (beta t))) t)
    ∧
    (∀ t ∈ TimeDomain T,
      HasDerivAt
        (fun tau =>
          materialCirculationFromX circ (shape p q)
            (beta tau * materialRadiusSq (shape p q) (beta tau)))
        0 t)
    ∧
    (∀ t ∈ TimeDomain T,
      let s := shape p q
      let rStar := materialRadius s (beta t)
      0 < rStar
        ∧ scaledX (beta t) rStar = s - 1
        ∧ deriv (distributedVorticity circ s (beta t)) rStar = 0
        ∧ 2 * Real.pi * p.nu * rStar *
            deriv (distributedVorticity circ s (beta t)) rStar = 0
        ∧ materialCirculationFromX circ s
            (scaledX (beta t) rStar) =
              circ * regLowerGamma s (s - 1))
    ∧
    (∀ t ∈ TimeDomain T,
      materialCirculationRate p.nu (beta t) circ (shape p q)
          (shape p q - 1) = 0
      ∧ (∀ x : ℝ, 0 < x → x < shape p q - 1 →
          0 < circ * materialCirculationRate
            p.nu (beta t) circ (shape p q) x)
      ∧ (∀ x : ℝ, 0 < x → shape p q - 1 < x →
          circ * materialCirculationRate
            p.nu (beta t) circ (shape p q) x < 0)) := by
  have hprincipal :=
    exactMaterialCirculationSurface p hann hcirc hbetaPos hbeta hscale
  refine ⟨hprincipal.1, hprincipal.2.1, ?_, ?_⟩
  · intro t ht
    have hsnap := hprincipal.2.2 t ht
    dsimp at hsnap ⊢
    exact ⟨hsnap.1, hsnap.2.1, hsnap.2.2.2.1,
      hsnap.2.2.2.2.1, hsnap.2.2.2.2.2.1⟩
  · intro t ht
    exact selectiveTransferPartition
      p.nu_pos (hbetaPos t ht) hcirc (hann : 1 < shape p q)

end

end KiknadzeKrasnov
