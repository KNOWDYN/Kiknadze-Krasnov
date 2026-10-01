import KiknadzeKrasnov.HeatTransform
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace KiknadzeKrasnov
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology

/-- Axial kinetic-energy contribution in a unit-area cylinder of half-height L. -/
def axialCylinderEnergy (rho a b L : ℝ) : ℝ :=
  (rho / 2) * ∫ z in -L..L, (axialVelocity a b z) ^ 2

/-- Exact growing-cylinder lower bound, including arbitrary axial translation. -/
theorem axialCylinderEnergy_eq (rho a b L : ℝ) :
    axialCylinderEnergy rho a b L = rho * (a ^ 2 * L ^ 3 / 3 + b ^ 2 * L) := by
  have he : (fun z => (axialVelocity a b z) ^ 2) =
      (fun z => a ^ 2 * z ^ 2 + (2 * a * b) * z + b ^ 2) := by
    funext z
    unfold axialVelocity
    ring
  unfold axialCylinderEnergy
  rw [he, intervalIntegral.integral_add, intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pow]
    simp
    ring
  all_goals (apply Continuous.intervalIntegrable; fun_prop)

/-- Nonzero imposed strain has arbitrarily large axial kinetic energy in
expanding cylinders; the full velocity energy is bounded below by this term. -/
theorem axialCylinderEnergy_tendsto_atTop {rho a b : ℝ}
    (hrho : 0 < rho) (ha : a ≠ 0) :
    Tendsto (axialCylinderEnergy rho a b) atTop atTop := by
  have hlead : Tendsto (fun L : ℝ => (rho * a ^ 2 / 3) * L ^ 3) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0)).const_mul_atTop (by positivity)
  apply tendsto_atTop_mono' atTop ?_ hlead
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
  rw [axialCylinderEnergy_eq]
  have hnonneg : 0 ≤ rho * b ^ 2 * L := by positivity
  nlinarith

/-- No finite whole-space energy can bound all expanding cylinders when strain is nonzero.
The premise is the standard restriction lower bound for the nonnegative kinetic-energy density. -/
theorem no_finite_energy_bound_for_nonzero_strain {rho a b : ℝ}
    {energy : ℝ → ℝ} (hrho : 0 < rho) (ha : a ≠ 0)
    (hlower : ∀ L > 0, axialCylinderEnergy rho a b L ≤ energy L) :
    ¬ ∃ E : ℝ, ∀ L > 0, energy L ≤ E := by
  rintro ⟨E, hE⟩
  have he := (axialCylinderEnergy_tendsto_atTop (b := b) hrho ha).eventually
    (eventually_gt_atTop E)
  obtain ⟨L, hL, hgt⟩ := (eventually_gt_atTop (0 : ℝ)).and he |>.exists
  exact (not_lt_of_ge ((hlower L hL).trans (hE L hL))) hgt

/-- C034: the radial diffusive flux for the standard passive-scalar model. -/
def scalarRadialFlux (diffusivity radialGradient : ℝ) : ℝ :=
  -diffusivity * radialGradient

/-- For positive diffusivity, zero scalar flux is equivalent to zero scalar
gradient; zero vorticity gradient alone does not supply this condition. -/
theorem scalarRadialFlux_zero_iff {diffusivity radialGradient : ℝ}
    (hd : 0 < diffusivity) :
    scalarRadialFlux diffusivity radialGradient = 0 ↔ radialGradient = 0 := by
  unfold scalarRadialFlux
  exact mul_eq_zero.trans (or_iff_right (neg_ne_zero.mpr hd.ne'))

/-- Explicit counterexample to inferring scalar impermeability from the
circulation-transfer condition. -/
theorem zero_vorticity_gradient_does_not_force_scalar_flux_zero
    {diffusivity : ℝ} (hd : 0 < diffusivity) :
    scalarRadialFlux diffusivity 1 ≠ 0 := by
  simp [scalarRadialFlux, hd.ne']

end
end KiknadzeKrasnov
