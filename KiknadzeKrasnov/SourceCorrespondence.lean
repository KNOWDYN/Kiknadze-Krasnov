import KiknadzeKrasnov.FamilyClosure

namespace KiknadzeKrasnov
noncomputable section
open Set Filter
open scoped Topology

/-- Supplement S001--S003: the original meridional notation agrees with the current field. -/
theorem original_meridional_notation (C0 C1 C2 r z : ℝ) :
    radialVelocity (-2 * C0) C1 r = C0 * r + C1 / r ∧
    axialVelocity (-2 * C0) C2 z = -2 * C0 * z + C2 := by
  unfold radialVelocity axialVelocity
  constructor <;> ring

/-- Supplement S002--S005: upper-gamma constants map to line and distributed circulations. -/
theorem original_upperGamma_swirl_notation {A1 A2 s beta r : ℝ}
    (hs : 0 < s) (hr : 0 < r) :
    oneModeSwirlWithLine (2 * Real.pi * (A1 + A2 * gammaFn s))
      (-2 * Real.pi * A2 * gammaFn s) s beta r =
    (A1 + A2 * upperGammaComplement s (scaledX beta r)) / r := by
  unfold oneModeSwirlWithLine centralLineSwirl distributedSwirl regLowerGamma upperGammaComplement
  field_simp [hr.ne', Real.pi_ne_zero, gammaFn_ne_zero hs]
  ring

/-- Far-field circulation coefficient, with a scaled limit that also handles cancellation of signed modes. -/
theorem multimodeSwirl_far_field {n : ℕ} {gammaLine s : ℝ}
    {circ beta : Fin n → ℝ} (hs : 0 < s) (hb : ∀ i, 0 < beta i) :
    Tendsto (fun r => r * multimodeSwirl gammaLine circ s beta r) atTop
      (𝓝 ((gammaLine + ∑ i, circ i) / (2 * Real.pi))) := by
  have hlim := (multimodeCirculationValue_tendsto_atTop (gammaLine := gammaLine) (circ := circ) hs hb).div_const (2 * Real.pi)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  unfold multimodeSwirl
  field_simp [hr.ne', Real.pi_ne_zero]

/-- The radial source term is lower order than the imposed linear far-field strain. -/
theorem radialVelocity_far_field (a q : ℝ) :
    Tendsto (fun r => radialVelocity a q r / r) atTop (𝓝 (-a / 2)) := by
  have h := tendsto_id.inv_tendsto_atTop (α := ℝ)
  have hlim : Tendsto (fun r : ℝ => -a / 2 + q * r⁻¹ * r⁻¹) atTop (𝓝 (-a / 2)) := by
    simpa using ((h.const_mul q).mul h).const_add (-a / 2)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  unfold radialVelocity
  field_simp [hr.ne']

/-- The actual regular finite-mode swirl formula, allowing distinct positive scales. -/
theorem multimodeSwirl_regular_formula {n : ℕ} (circ beta : Fin n → ℝ)
    {r : ℝ} (hb : ∀ i, 0 < beta i) :
    multimodeSwirl 0 circ 1 beta r =
      (∑ i, circ i * (1 - Real.exp (-(beta i * r ^ 2)))) / (2 * Real.pi * r) := by
  unfold multimodeSwirl multimodeCirculationValue distributedCirculation
  simp only [zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hbi := hb i
  rw [regLowerGamma_one (by unfold scaledX; positivity)]
  rfl

end
end KiknadzeKrasnov
