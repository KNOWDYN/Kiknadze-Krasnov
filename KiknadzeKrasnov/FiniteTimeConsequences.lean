import KiknadzeKrasnov.FiniteTimeCriteria

namespace KiknadzeKrasnov
noncomputable section
open Filter Set intervalIntegral
open scoped Topology

/-- Concentration requires accumulated stretching with no eventual finite upper bound.
This preserves the positive initial-condition term rather than discarding viscosity. -/
theorem concentration_requires_unbounded_accumulated_strain
    {nu h0 : ℝ} {a : ℝ → ℝ} {l : Filter ℝ} [NeBot l]
    (hn : 0 < nu) (hh : 0 < h0) (ht : ∀ᶠ t in l, 0 ≤ t)
    (hlim : Tendsto (inverseScaleExact nu h0 a) l (𝓝 0)) :
    ¬ ∃ M : ℝ, ∀ᶠ t in l, strainAccum a t ≤ M := by
  rintro ⟨M, hM⟩
  let c : ℝ := Real.exp (-M) * h0
  have hc : 0 < c := mul_pos (Real.exp_pos _) hh
  have hsmall : ∀ᶠ t in l, inverseScaleExact nu h0 a t < c :=
    hlim.eventually (Iio_mem_nhds hc)
  have hlarge : ∀ᶠ t in l, c ≤ inverseScaleExact nu h0 a t := by
    filter_upwards [ht, hM] with t ht hM
    have hJ : 0 ≤ scaleIntegral a t := by
      apply intervalIntegral.integral_nonneg ht
      intro u hu
      exact Real.exp_nonneg _
    have hE : Real.exp (-M) ≤ Real.exp (-strainAccum a t) :=
      Real.exp_le_exp.mpr (neg_le_neg hM)
    unfold inverseScaleExact c
    calc
      Real.exp (-M) * h0 ≤ Real.exp (-strainAccum a t) * h0 :=
        mul_le_mul_of_nonneg_right hE hh.le
      _ ≤ Real.exp (-strainAccum a t) * (h0 + 4 * nu * scaleIntegral a t) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        have hnonneg : 0 ≤ 4 * nu * scaleIntegral a t := by positivity
        linarith
  obtain ⟨t, hl, hs⟩ := (hlarge.and hsmall).exists
  exact not_lt_of_ge hl hs

end
end KiknadzeKrasnov
