import KiknadzeKrasnov.VorticityTransport
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace KiknadzeKrasnov

noncomputable section

open Filter
open scoped Topology

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
  have hden : 0 < 2 * p.nu := mul_pos (by norm_num) p.nu_pos
  unfold shape
  constructor
  · rintro ⟨hpos, hlt⟩
    have hlo : (-1 : ℝ) < q / (2 * p.nu) := by linarith
    have hhi : q / (2 * p.nu) < 0 := by linarith
    have hqlo : -2 * p.nu < q := by
      have := (lt_div_iff₀ hden).mp hlo
      nlinarith
    have hqneg : q < 0 := by
      rcases (div_neg_iff.mp hhi) with hbad | hgood
      · exact (not_lt_of_ge hden.le hbad.2).elim
      · exact hgood.1
    exact ⟨hqlo, hqneg⟩
  · rintro ⟨hqlo, hqneg⟩
    have hlo : (-1 : ℝ) < q / (2 * p.nu) := by
      apply (lt_div_iff₀ hden).mpr
      nlinarith
    have hhi : q / (2 * p.nu) < 0 := div_neg_of_neg_of_pos hqneg hden
    constructor <;> linarith

/-- For s>1 the dimensionless vorticity kernel tends to zero at the axis. -/
theorem vorticityShape_tendsto_zero_nhdsGT
    {s : ℝ} (hs : 1 < s) :
    Tendsto (vorticityShape s) (𝓝[>] 0) (𝓝 0) := by
  have hpfull :=
    (Real.continuous_rpow_const (sub_nonneg.mpr hs.le)).tendsto 0
  have hp : Tendsto (fun x : ℝ => x ^ (s - 1)) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_nhdsWithin_of_tendsto_nhds
      (s := Ioi (0 : ℝ)) hpfull
    simpa [Real.zero_rpow (sub_pos.mpr hs).ne'] using h
  have hefull :
      Tendsto (fun x : ℝ => Real.exp (-x)) (𝓝 0) (𝓝 1) := by
    simpa using (by fun_prop :
      ContinuousAt (fun x : ℝ => Real.exp (-x)) 0).tendsto
  have he : Tendsto (fun x : ℝ => Real.exp (-x)) (𝓝[>] 0) (𝓝 1) :=
    tendsto_nhdsWithin_of_tendsto_nhds hefull
  unfold vorticityShape
  simpa using hp.mul he

/-- At s=1 the dimensionless vorticity kernel tends to its finite on-axis value one. -/
theorem vorticityShape_one_tendsto_one :
    Tendsto (vorticityShape 1) (𝓝[>] 0) (𝓝 1) := by
  have hefull :
      Tendsto (fun x : ℝ => Real.exp (-x)) (𝓝 0) (𝓝 1) := by
    simpa using (by fun_prop :
      ContinuousAt (fun x : ℝ => Real.exp (-x)) 0).tendsto
  have he : Tendsto (fun x : ℝ => Real.exp (-x)) (𝓝[>] 0) (𝓝 1) :=
    tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ)) hefull
  have hfun :
      vorticityShape 1 = (fun x : ℝ => Real.exp (-x)) := by
    funext x
    simp [vorticityShape]
  rw [hfun]
  exact he

/-- For 0<s<1 the dimensionless distributed-vorticity kernel diverges toward
the excluded axis, exactly as stated in the parameter audit. -/
theorem vorticityShape_tendsto_atTop_nhdsGT
    {s : ℝ} (_hs0 : 0 < s) (hs1 : s < 1) :
    Tendsto (vorticityShape s) (𝓝[>] 0) atTop := by
  have hp :
      Tendsto (fun x : ℝ => x ^ (s - 1)) (𝓝[>] 0) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (sub_neg.mpr hs1)
  have hefull :
      Tendsto (fun x : ℝ => Real.exp (-x)) (𝓝 0) (𝓝 1) := by
    simpa using (by fun_prop :
      ContinuousAt (fun x : ℝ => Real.exp (-x)) 0).tendsto
  have he : Tendsto (fun x : ℝ => Real.exp (-x)) (𝓝[>] 0) (𝓝 1) :=
    tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ)) hefull
  unfold vorticityShape
  exact hp.atTop_mul_pos zero_lt_one he

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
