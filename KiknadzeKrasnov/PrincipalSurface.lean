import KiknadzeKrasnov.CirculationSurface

namespace KiknadzeKrasnov

noncomputable section

/-!
Pass 4 principal certificate.  This theorem family assembles the manuscript's
central single-mode result without strengthening it to distinct-scale
multimode fields or to variational transport-barrier statements.
-/

/--
For every physical time at which the Pass-3B scale equation holds, the
source-bearing distinguished radius is transported by the KK radial velocity.
This is the reviewer-facing materiality statement corresponding to manuscript
Eq. (111).
-/
theorem materialRadius_is_material_on
    (p : FluidParams) {T q : ℝ}
    {a beta betaDot : ℝ → ℝ}
    (hann : AnnularSourceBranch p q)
    (hbetaPos : PositiveScaleOn T beta)
    (hbeta : ∀ t ∈ TimeDomain T, HasDerivAt beta (betaDot t) t)
    (hscale : ∀ t ∈ TimeDomain T,
      betaScaleResidual p.nu (a t) (beta t) (betaDot t) = 0) :
    ∀ t ∈ TimeDomain T,
      HasDerivAt
        (fun tau => materialRadius (shape p q) (beta tau))
        (radialVelocity (a t) q
          (materialRadius (shape p q) (beta t))) t := by
  intro t ht
  have hs : 1 < shape p q := hann
  have hb : 0 < beta t := hbetaPos t ht
  exact materialRadius_history_hasDerivAt
    hs hb (hbeta t ht) (hscale t ht)
    (source_eq_two_nu_mul_shape_sub_one p q)

/--
Along the distinguished material cylinder, the enclosed distributed
circulation Gamma P(s,s-1) has zero time derivative.  This is the dynamic
conservation statement in manuscript Eq. (122), not merely its fixed-time
value.
-/
theorem materialCirculation_at_star_hasDerivAt_zero_on
    (p : FluidParams) {T q circ : ℝ}
    {a beta betaDot : ℝ → ℝ}
    (hann : AnnularSourceBranch p q)
    (hbetaPos : PositiveScaleOn T beta)
    (hbeta : ∀ t ∈ TimeDomain T, HasDerivAt beta (betaDot t) t)
    (hscale : ∀ t ∈ TimeDomain T,
      betaScaleResidual p.nu (a t) (beta t) (betaDot t) = 0) :
    ∀ t ∈ TimeDomain T,
      HasDerivAt
        (fun tau =>
          materialCirculationFromX circ (shape p q)
            (beta tau * materialRadiusSq (shape p q) (beta tau)))
        0 t := by
  intro t ht
  have hs : 1 < shape p q := hann
  have hb : 0 < beta t := hbetaPos t ht
  have hcompat : q = 2 * p.nu * (shape p q - 1) :=
    source_eq_two_nu_mul_shape_sub_one p q
  have hy :=
    materialRadiusSq_history_hasDerivAt
      (beta := beta) (betaDot := betaDot t) (nu := p.nu)
      (a := a t) (q := q) (s := shape p q) (t := t)
      (hbeta t ht) hb.ne' (hscale t ht) hcompat
  have hx :=
    scaledMaterial_hasDerivAt
      (beta := beta)
      (y := fun tau => materialRadiusSq (shape p q) (beta tau))
      (betaDot := betaDot t) (nu := p.nu) (a := a t)
      (q := q) (s := shape p q) (t := t)
      (hbeta t ht) hy (hscale t ht) hcompat
  have hstar :
      beta t * materialRadiusSq (shape p q) (beta t) =
        shape p q - 1 :=
    scaledX_materialRadiusSq hb.ne'
  exact materialCirculation_hasDerivAt_zero_at_star
    (x := fun tau =>
      beta tau * materialRadiusSq (shape p q) (beta tau))
    (nu := p.nu) (beta := beta t) (circ := circ)
    (s := shape p q) (t := t) hs hx hstar

/--
At each physical time, the material radius maps to x=s-1, equals the unique
positive-radius maximum of |omega_z| for nonzero distributed circulation, has
zero radial vorticity gradient and zero viscous circulation transfer, and
encloses Gamma P(s,s-1).  This is the fixed-time intrinsic part of the main
result.
-/
theorem principalSurface_snapshot
    (p : FluidParams) {q circ beta : ℝ}
    (hann : AnnularSourceBranch p q)
    (hbeta : 0 < beta)
    (hcirc : circ ≠ 0) :
    let s := shape p q
    let rStar := materialRadius s beta
    0 < rStar
      ∧ scaledX beta rStar = s - 1
      ∧ materialRadiusSq s beta = q / (2 * p.nu * beta)
      ∧ deriv (distributedVorticity circ s beta) rStar = 0
      ∧ 2 * Real.pi * p.nu * rStar *
          deriv (distributedVorticity circ s beta) rStar = 0
      ∧ materialCirculationFromX circ s (scaledX beta rStar) =
          circ * regLowerGamma s (s - 1)
      ∧ (∀ r : ℝ, PuncturedRadius r → r ≠ rStar →
          |distributedVorticity circ s beta r| <
            |distributedVorticity circ s beta rStar|) := by
  dsimp
  have hs : 1 < shape p q := hann
  have hrpos : 0 < materialRadius (shape p q) beta :=
    materialRadius_pos hs hbeta
  have hxstar :
      scaledX beta (materialRadius (shape p q) beta) =
        shape p q - 1 :=
    scaledX_materialRadius hs hbeta
  have hsource :
      materialRadiusSq (shape p q) beta =
        q / (2 * p.nu * beta) :=
    materialRadiusSq_eq_source_form p.nu_ne_zero hbeta.ne'
      (source_eq_two_nu_mul_shape_sub_one p q)
  have hgrad :
      deriv (distributedVorticity circ (shape p q) beta)
        (materialRadius (shape p q) beta) = 0 :=
    distributedVorticity_deriv_at_materialRadius hs hbeta
  have hflux :
      2 * Real.pi * p.nu * materialRadius (shape p q) beta *
          deriv (distributedVorticity circ (shape p q) beta)
            (materialRadius (shape p q) beta) = 0 :=
    viscousCirculationFlux_zero_at_materialRadius hs hbeta
  have hcirculation :
      materialCirculationFromX circ (shape p q)
          (scaledX beta (materialRadius (shape p q) beta)) =
        circ * regLowerGamma (shape p q) (shape p q - 1) := by
    rw [hxstar]
    rfl
  refine ⟨hrpos, hxstar, hsource, hgrad, hflux, hcirculation, ?_⟩
  intro r hr hne
  rw [materialRadius_eq_vorticityPeakRadius] at hne ⊢
  exact abs_distributedVorticity_lt_peak hcirc hs hbeta hr hne

/--
Pass-4 assembled form of the paper's headline theorem: on the source-bearing
single-mode branch, the same positive cylinder is material for every physical
time and, at each time, is the one-mode |omega_z| peak and an exact zero
viscous-circulation-transfer surface enclosing the fixed profile fraction
P(s,s-1).
-/
theorem exactMaterialCirculationSurface
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
      scaledX (beta t) rStar = s - 1
        ∧ deriv (distributedVorticity circ s (beta t)) rStar = 0
        ∧ 2 * Real.pi * p.nu * rStar *
            deriv (distributedVorticity circ s (beta t)) rStar = 0
        ∧ materialCirculationFromX circ s
            (scaledX (beta t) rStar) =
              circ * regLowerGamma s (s - 1)
        ∧ (∀ r : ℝ, PuncturedRadius r → r ≠ rStar →
            |distributedVorticity circ s (beta t) r| <
              |distributedVorticity circ s (beta t) rStar|)) := by
  refine ⟨materialRadius_is_material_on p hann hbetaPos hbeta hscale, ?_⟩
  refine ⟨materialCirculation_at_star_hasDerivAt_zero_on
    p hann hbetaPos hbeta hscale, ?_⟩
  intro t ht
  have snap := principalSurface_snapshot p hann (hbetaPos t ht) hcirc
  dsimp at snap ⊢
  exact ⟨snap.2.1, snap.2.2.2.1, snap.2.2.2.2.1,
    snap.2.2.2.2.2.1, snap.2.2.2.2.2.2⟩

end

end KiknadzeKrasnov
