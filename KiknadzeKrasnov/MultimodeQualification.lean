import KiknadzeKrasnov.MaterialSurfaceTheorem

namespace KiknadzeKrasnov

noncomputable section

open scoped BigOperators

/-- S032: with one common scale, finite distributed circulation collapses to one
common radial profile multiplied by the summed distributed circulation. -/
theorem multimodeCirculationValue_equalScale {n : ℕ}
    (gammaLine : ℝ) (circ : Fin n → ℝ) (s beta r : ℝ) :
    multimodeCirculationValue gammaLine circ s (fun _ => beta) r =
      gammaLine + (∑ i, circ i) * regLowerGamma s (scaledX beta r) := by
  classical
  unfold multimodeCirculationValue
  rw [Finset.sum_mul]

/-- S032: equal scales similarly collapse the finite distributed-vorticity sum
onto one common radial shape. -/
theorem multimodeDistributedVorticity_equalScale {n : ℕ}
    (circ : Fin n → ℝ) (s beta r : ℝ) :
    multimodeDistributedVorticity circ s (fun _ => beta) r =
      distributedVorticity (∑ i, circ i) s beta r := by
  classical
  unfold multimodeDistributedVorticity distributedVorticity
  let K := beta / (Real.pi * gammaFn s) * vorticityShape s (scaledX beta r)
  calc
    (∑ i, circ i * beta / (Real.pi * gammaFn s) *
        vorticityShape s (scaledX beta r)) = ∑ i, circ i * K := by
          apply Finset.sum_congr rfl
          intro i hi
          unfold K
          ring
    _ = (∑ i, circ i) * K := by
          rw [Finset.sum_mul]
    _ = (∑ i, circ i) * beta / (Real.pi * gammaFn s) *
        vorticityShape s (scaledX beta r) := by
          unfold K
          ring

/-- S033: every finite mode obeys the same scaled-material law, with its own
scale history. -/
theorem multimode_scaledMaterial_hasDerivAt {n : ℕ}
    {beta betaDot : Fin n → ℝ → ℝ} {y : ℝ → ℝ}
    {nu q s t : ℝ} {a : ℝ → ℝ}
    (hbeta : ∀ i, HasDerivAt (beta i) (betaDot i t) t)
    (hy : HasDerivAt y (-a t * y t + 2 * q) t)
    (hscale : ∀ i, scaleResidual nu (a t) (beta i t) (betaDot i t) = 0)
    (hcompat : q = 2 * nu * (s - 1)) :
    ∀ i, HasDerivAt (fun tau => beta i tau * y tau)
      (4 * nu * beta i t * ((s - 1) - beta i t * y t)) t := by
  intro i
  exact scaledMaterial_hasDerivAt (hbeta i) hy (hscale i) hcompat

/-- S034: radial differentiation commutes with the finite vorticity sum. -/
theorem multimodeDistributedVorticity_hasDerivAt {n : ℕ}
    {circ : Fin n → ℝ} {s r : ℝ} {beta : Fin n → ℝ}
    (hs : 0 < s) (hbeta : ∀ i, 0 < beta i) (hr : 0 < r) :
    HasDerivAt (multimodeDistributedVorticity circ s beta)
      (∑ i, deriv (distributedVorticity (circ i) s (beta i)) r) r := by
  classical
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (distributedVorticity_hasDerivAt_r
      (circ := circ i) (s := s) (beta := beta i) (r := r)
      hs (hbeta i) hr).differentiableAt.hasDerivAt)
  unfold multimodeDistributedVorticity
  simpa only [Finset.sum_apply] using hsum

/-- The derivative of total finite-mode vorticity is exactly the sum of the
component radial derivatives. -/
theorem deriv_multimodeDistributedVorticity {n : ℕ}
    {circ : Fin n → ℝ} {s r : ℝ} {beta : Fin n → ℝ}
    (hs : 0 < s) (hbeta : ∀ i, 0 < beta i) (hr : 0 < r) :
    deriv (multimodeDistributedVorticity circ s beta) r =
      ∑ i, deriv (distributedVorticity (circ i) s (beta i)) r := by
  exact (multimodeDistributedVorticity_hasDerivAt hs hbeta hr).deriv

/-- Equal positive scales give one common distinguished material radius. -/
theorem materialRadius_eq_of_beta_eq
    {s beta₁ beta₂ : ℝ} (hbeta : beta₁ = beta₂) :
    materialRadius s beta₁ = materialRadius s beta₂ := by
  rw [hbeta]

/-- For `s>1`, distinct positive scales have distinct component material
radii.  This is the precise obstruction to inheriting a universal component
surface when scales differ; it does not assert where a zero of the summed
vorticity derivative lies. -/
theorem materialRadius_ne_of_beta_ne
    {s beta₁ beta₂ : ℝ} (hs : 1 < s)
    (hb₁ : 0 < beta₁) (hb₂ : 0 < beta₂) (hne : beta₁ ≠ beta₂) :
    materialRadius s beta₁ ≠ materialRadius s beta₂ := by
  intro hr
  have hsx₁ := scaledX_materialRadius (s := s) (beta := beta₁) hs hb₁
  have hsx₂ := scaledX_materialRadius (s := s) (beta := beta₂) hs hb₂
  unfold scaledX at hsx₁ hsx₂
  rw [hr] at hsx₁
  have hsqpos : 0 < (materialRadius s beta₂) ^ 2 :=
    sq_pos_of_pos (materialRadius_pos hs hb₂)
  have hmul : beta₁ * (materialRadius s beta₂) ^ 2 =
      beta₂ * (materialRadius s beta₂) ^ 2 := hsx₁.trans hsx₂.symm
  have hbeq : beta₁ = beta₂ :=
    mul_right_cancel₀ (ne_of_gt hsqpos) hmul
  exact hne hbeq

end

end KiknadzeKrasnov
