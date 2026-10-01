import KiknadzeKrasnov.EnergyAndScalar

namespace KiknadzeKrasnov
noncomputable section
open Set MeasureTheory intervalIntegral Filter
open scoped Topology

/-- Physical kinetic energy in the annular cylinder 1≤r≤2, -L≤z≤L,
using the cylindrical volume element 2 pi r dr dz. -/
def annularCylinderEnergy (rho a b q : ℝ) (u : ℝ → ℝ) (L : ℝ) : ℝ :=
  rho / 2 * ∫ z in -L..L, ∫ r in (1 : ℝ)..2,
    (radialVelocity a q r ^ 2 + u r ^ 2 + axialVelocity a b z ^ 2) * (2 * Real.pi * r)

def radialAnnulusEnergy (a q : ℝ) (u : ℝ → ℝ) : ℝ :=
  ∫ r in (1 : ℝ)..2, (radialVelocity a q r ^ 2 + u r ^ 2) * (2 * Real.pi * r)

/-- Exact annular-cylinder energy, separated into radial/swirl and axial contributions. -/
theorem annularCylinderEnergy_eq {rho a b q L : ℝ} {u : ℝ → ℝ}
    (hu : ContinuousOn u (Icc (1 : ℝ) 2)) :
    annularCylinderEnergy rho a b q u L =
      rho * L * radialAnnulusEnergy a q u + 3 * Real.pi * axialCylinderEnergy rho a b L := by
  have hc : ContinuousOn (fun r => (radialVelocity a q r ^ 2 + u r ^ 2) *
      (2 * Real.pi * r)) (Icc (1 : ℝ) 2) := by
    have hr : ContinuousOn (radialVelocity a q) (Icc (1 : ℝ) 2) := by
      intro r hr
      exact (radialVelocity_hasDerivAt (a := a) (q := q) (r := r) (lt_of_lt_of_le zero_lt_one hr.1)).continuousAt.continuousWithinAt
    exact (hr.pow 2 |>.add (hu.pow 2)).mul (by fun_prop)
  have hi : IntervalIntegrable (fun r => (radialVelocity a q r ^ 2 + u r ^ 2) *
      (2 * Real.pi * r)) volume 1 2 := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hc
  have hweight : (∫ r in (1 : ℝ)..2, (2 : ℝ) / 3 * r) = 1 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    norm_num
  have hinner : ∀ z, (∫ r in (1 : ℝ)..2,
      (radialVelocity a q r ^ 2 + u r ^ 2 + axialVelocity a b z ^ 2) * (2 * Real.pi * r)) =
      radialAnnulusEnergy a q u + 3 * Real.pi * axialVelocity a b z ^ 2 := by
    intro z
    have he : (fun r => (radialVelocity a q r ^ 2 + u r ^ 2 + axialVelocity a b z ^ 2) *
        (2 * Real.pi * r)) = (fun r =>
        (radialVelocity a q r ^ 2 + u r ^ 2) * (2 * Real.pi * r) +
        (3 * Real.pi * axialVelocity a b z ^ 2) * ((2 : ℝ) / 3 * r)) := by funext r; ring
    rw [he, intervalIntegral.integral_add hi (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const_mul, hweight]
    simp only [mul_one]
    rfl
  unfold annularCylinderEnergy
  simp_rw [hinner]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; unfold axialVelocity; fun_prop),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
  unfold axialCylinderEnergy
  ring

/-- Actual nonnegative kinetic-energy density bounds its axial contribution below. -/
theorem annularCylinderEnergy_lower_bound {rho a b q L : ℝ} {u : ℝ → ℝ}
    (hrho : 0 < rho) (hL : 0 < L) (hu : ContinuousOn u (Icc (1 : ℝ) 2)) :
    3 * Real.pi * axialCylinderEnergy rho a b L ≤ annularCylinderEnergy rho a b q u L := by
  rw [annularCylinderEnergy_eq hu]
  have hrad : 0 ≤ radialAnnulusEnergy a q u := by
    apply intervalIntegral.integral_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    intro r hr
    have hrp : 0 < r := by linarith [hr.1]
    positivity
  have hn : 0 ≤ rho * L * radialAnnulusEnergy a q u := by positivity
  linarith

/-- C003: actual kinetic energies in expanding annular cylinders have no finite bound.
Consequently the whole-space energy, which contains every such cylinder, is infinite. -/
theorem annularCylinderEnergy_no_finite_bound {rho a b q : ℝ} {u : ℝ → ℝ}
    (hrho : 0 < rho) (ha : a ≠ 0) (hu : ContinuousOn u (Icc (1 : ℝ) 2)) :
    ¬ ∃ E : ℝ, ∀ L > 0, annularCylinderEnergy rho a b q u L ≤ E := by
  rintro ⟨E, hE⟩
  apply no_finite_energy_bound_for_nonzero_strain (b := b) hrho ha
    (energy := fun L => annularCylinderEnergy rho a b q u L / (3 * Real.pi))
  · intro L hL
    exact (le_div_iff₀ (by positivity : 0 < 3 * Real.pi)).mpr
      (by simpa [mul_comm] using annularCylinderEnergy_lower_bound hrho hL hu)
  · refine ⟨E / (3 * Real.pi), ?_⟩
    intro L hL
    exact div_le_div_of_nonneg_right (hE L hL) (by positivity)

end
end KiknadzeKrasnov
