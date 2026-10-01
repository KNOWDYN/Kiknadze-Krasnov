import KiknadzeKrasnov.PhysicalIntegrals
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace KiknadzeKrasnov
noncomputable section
open Set MeasureTheory Filter
open scoped Topology

/-- The actual exponential enstrophy kernel has the same local integrability threshold as its axis power. -/
theorem enstrophy_kernel_axis_integrable_iff (s B : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ (2 * s - 2) * Real.exp (-(B * x))) (Ioo 0 1) ↔
      (1 / 2 : ℝ) < s := by
  constructor
  · intro hi
    have h := hi.mul_continuousOn_of_subset
      (show ContinuousOn (fun x : ℝ => Real.exp (B * x)) (Icc 0 1) by fun_prop)
      measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self
    have he : (fun x : ℝ => (x ^ (2 * s - 2) * Real.exp (-(B * x))) * Real.exp (B * x)) =
        (fun x => x ^ (2 * s - 2)) := by
      funext x
      rw [mul_assoc, ← Real.exp_add]
      simp
    rw [he] at h
    exact enstrophy_axis_power_integrable_iff.mp h
  · intro hs
    exact (enstrophy_axis_power_integrable_iff.mpr hs).mul_continuousOn_of_subset
      (show ContinuousOn (fun x : ℝ => Real.exp (-(B * x))) (Icc 0 1) by fun_prop)
      measurableSet_Ioo isCompact_Icc Ioo_subset_Icc_self

/-- Full convergence threshold for the actual reduced kernel on the positive half-line. -/
theorem enstrophy_kernel_integrable_iff {s B : ℝ} (hB : 0 < B) :
    IntegrableOn (fun x : ℝ => x ^ (2 * s - 2) * Real.exp (-(B * x))) (Ioi 0) ↔
      (1 / 2 : ℝ) < s := by
  constructor
  · intro hi
    exact (enstrophy_kernel_axis_integrable_iff s B).mp (hi.mono_set Ioo_subset_Ioi_self)
  · intro hs
    by_contra hi
    have hz := integral_undef hi
    have he := enstrophyKernelIntegral_eq hs hB
    unfold enstrophyKernelIntegral at he
    rw [hz] at he
    have hp : 0 < (1 / B) ^ (2 * s - 1) * gammaFn (2 * s - 1) := by
      apply mul_pos (Real.rpow_pos_of_pos (div_pos zero_lt_one hB) _)
      exact gammaFn_pos (by linarith)
    linarith

/-- The original one-mode enstrophy definition equals its physical diagonal pair integral. -/
theorem singleModeEnstrophy_eq_physicalPair (circ s beta : ℝ) :
    enstrophyPerUnitLength (distributedVorticity circ s beta) =
      physicalEnstrophyPair circ circ s beta beta := by
  unfold enstrophyPerUnitLength physicalEnstrophyPair
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  ring

/-- The enstrophy evolution law differentiates the original physical integral. -/
theorem physicalSingleModeEnstrophy_hasDerivAt {circ s nu a betaDot t : ℝ}
    {beta : ℝ → ℝ} (hs : (1 / 2 : ℝ) < s) (hb : 0 < beta t)
    (hd : HasDerivAt beta betaDot t)
    (hscale : betaScaleResidual nu a (beta t) betaDot = 0) :
    HasDerivAt (fun u => enstrophyPerUnitLength (distributedVorticity circ s (beta u)))
      ((a - 4 * nu * beta t) *
        enstrophyPerUnitLength (distributedVorticity circ s (beta t))) t := by
  have he : ∀ u, 0 < beta u → enstrophyPerUnitLength (distributedVorticity circ s (beta u)) =
      singleModeEnstrophyClosed circ s (beta u) := by
    intro u hu
    rw [singleModeEnstrophy_eq_physicalPair, physicalEnstrophyPair_eq hs hu hu,
      enstrophyPairClosed_diagonal_eq_single hs hu]
  rw [he t hb]
  apply (singleModeEnstrophy_hasDerivAt hs hd hscale).congr_of_eventuallyEq
  filter_upwards [hd.continuousAt.eventually (Ioi_mem_nhds hb)] with u hu
  exact he u hu

end
end KiknadzeKrasnov
