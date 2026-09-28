import KiknadzeKrasnov.VorticityTransport

namespace KiknadzeKrasnov

noncomputable section

/-!
Parameter-domain audit from Supplementary Table II.  These lemmas keep the
different thresholds separate instead of silently identifying them.
-/

/-- The near-axis swirl exponent is positive exactly for s>1/2. -/
theorem swirlAxisExponent_pos_iff {s : ℝ} :
    0 < 2 * s - 1 ↔ (1 / 2 : ℝ) < s := by
  constructor <;> intro h <;> linarith

/-- The near-axis vorticity exponent is nonnegative exactly for s>=1. -/
theorem vorticityAxisExponent_nonneg_iff {s : ℝ} :
    0 ≤ 2 * s - 2 ↔ (1 : ℝ) ≤ s := by
  constructor <;> intro h <;> linarith

/-- The gamma integral used by the finite-circulation representation has
positive shape precisely on the declared finite-circulation branch. -/
theorem finiteCirculation_shape_pos_iff (p : FluidParams) (q : ℝ) :
    0 < shape p q ↔ FiniteCirculationBranch p q := by
  rfl

/-- The regular shape s=1 is equivalent to zero source strength. -/
theorem shape_eq_one_iff_source_zero (p : FluidParams) (q : ℝ) :
    shape p q = 1 ↔ q = 0 := by
  unfold shape
  have hden : 2 * p.nu ≠ 0 :=
    mul_ne_zero (by norm_num) p.nu_ne_zero
  constructor
  · intro h
    have hq : q / (2 * p.nu) = 0 := by linarith
    exact (div_eq_zero_iff.mp hq).resolve_right hden
  · intro hq
    subst q
    simp

/-- The annular material/vorticity branch is exactly s>1, equivalently q>0. -/
theorem annular_parameter_threshold (p : FluidParams) (q : ℝ) :
    1 < shape p q ↔ 0 < q :=
  annularSourceBranch_iff_q_pos p q

/-- The finite-circulation sink subbranch 0<s<1 is exactly -2nu<q<0. -/
theorem sink_shape_interval_iff (p : FluidParams) (q : ℝ) :
    (0 < shape p q ∧ shape p q < 1) ↔ (-2 * p.nu < q ∧ q < 0) := by
  rw [finiteCirculationBranch_iff p q] at *
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    unfold shape at h
    have hden : 0 < 2 * p.nu := mul_pos (by norm_num) p.nu_pos
    have : q / (2 * p.nu) < 0 := by linarith
    exact (div_neg_iff hden).mp this
  · intro h
    refine ⟨h.1, ?_⟩
    unfold shape
    have hden : 0 < 2 * p.nu := mul_pos (by norm_num) p.nu_pos
    have hdiv : q / (2 * p.nu) < 0 := div_neg_of_neg_of_pos h.2 hden
    linarith

/-- The enstrophy gamma-integral shape 2s-1 is positive exactly at the
same s>1/2 threshold as the interior-swirl exponent. -/
theorem enstrophy_and_swirl_threshold_same {s : ℝ} :
    0 < 2 * s - 1 ↔ (1 / 2 : ℝ) < s :=
  swirlAxisExponent_pos_iff

/-- The annular threshold is strictly stronger than bounded-axis vorticity. -/
theorem annular_implies_bounded_axis_threshold {s : ℝ} (hs : 1 < s) :
    1 ≤ s := hs.le

/-- Bounded-axis threshold implies the finite-circulation threshold. -/
theorem bounded_axis_implies_finite_circulation_threshold {s : ℝ}
    (hs : 1 ≤ s) : 0 < s := lt_of_lt_of_le zero_lt_one hs

/-- The swirl/enstrophy threshold alone does not algebraically force bounded
axis vorticity; the interval (1/2,1) is nonempty. -/
theorem half_lt_three_quarters_lt_one :
    (1 / 2 : ℝ) < 3 / 4 ∧ (3 / 4 : ℝ) < 1 := by
  norm_num

end

end KiknadzeKrasnov
