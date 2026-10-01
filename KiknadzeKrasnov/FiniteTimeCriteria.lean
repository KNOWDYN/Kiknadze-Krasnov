import KiknadzeKrasnov.HeatTransform
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace KiknadzeKrasnov

noncomputable section

open Filter Set MeasureTheory intervalIntegral
open scoped Topology

/-!
Finite-terminal criteria for the exact inverse scale.  This closes manuscript
Eqs. (142)--(146) before the singular-strain case split.
-/

/-- An absolutely integrable imposed strain has a continuous accumulated
strain on every finite interval. -/
theorem strainAccum_continuousOn_Icc
    {a : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T) :
    ContinuousOn (strainAccum a) (Icc 0 T) := by
  have h :=
    intervalIntegral.continuousOn_primitive_interval'
      ha (show (0 : ℝ) ∈ uIcc 0 T by simp)
  unfold strainAccum
  simpa [uIcc_of_le hT] using h

/-- The weighted viscous primitive is continuous on a finite interval whenever
the imposed strain is absolutely integrable there. -/
theorem scaleIntegral_continuousOn_Icc
    {a : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T) :
    ContinuousOn (scaleIntegral a) (Icc 0 T) := by
  have hA := strainAccum_continuousOn_Icc hT ha
  have hE :
      ContinuousOn (fun t => Real.exp (strainAccum a t)) (Icc 0 T) := by
    exact Real.continuous_exp.comp_continuousOn hA
  have hEint :
      IntervalIntegrable (fun t => Real.exp (strainAccum a t)) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hT] using hE
  have h :=
    intervalIntegral.continuousOn_primitive_interval'
      hEint (show (0 : ℝ) ∈ uIcc 0 T by simp)
  unfold scaleIntegral
  simpa [uIcc_of_le hT] using h

/-- Eq. (144) is continuous up to every finite terminal time at which the
strain is absolutely integrable. -/
theorem inverseScaleExact_continuousOn_Icc
    {nu h0 T : ℝ} {a : ℝ → ℝ} (hT : 0 ≤ T)
    (ha : IntervalIntegrable a volume 0 T) :
    ContinuousOn (inverseScaleExact nu h0 a) (Icc 0 T) := by
  have hA := strainAccum_continuousOn_Icc hT ha
  have hJ := scaleIntegral_continuousOn_Icc hT ha
  unfold inverseScaleExact
  have hExp :
      ContinuousOn (fun t => Real.exp (-strainAccum a t)) (Icc 0 T) :=
    Real.continuous_exp.comp_continuousOn hA.neg
  have hBracket :
      ContinuousOn
        (fun t => h0 + 4 * nu * scaleIntegral a t) (Icc 0 T) :=
    continuousOn_const.add (continuousOn_const.mul hJ)
  exact hExp.mul hBracket

/-- The exact inverse scale tends to its finite endpoint value from the left. -/
theorem inverseScaleExact_tendsto_terminal
    {nu h0 T : ℝ} {a : ℝ → ℝ} (hT : 0 < T)
    (ha : IntervalIntegrable a volume 0 T) :
    Tendsto (inverseScaleExact nu h0 a) (𝓝[<] T)
      (𝓝 (inverseScaleExact nu h0 a T)) := by
  have hc := inverseScaleExact_continuousOn_Icc (nu := nu) (h0 := h0) hT.le ha
  have ht : T ∈ Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have h := (hc T ht).tendsto
  rw [nhdsWithin_Icc_eq_nhdsLE hT] at h
  exact h.mono_left (nhdsWithin_mono T Iio_subset_Iic_self)

/-- With positive viscosity and positive initial inverse scale, the finite
terminal inverse scale is strictly positive. -/
theorem inverseScaleExact_terminal_pos
    {nu h0 T : ℝ} {a : ℝ → ℝ}
    (hnu : 0 < nu) (hh0 : 0 < h0) (hT : 0 < T) :
    0 < inverseScaleExact nu h0 a T := by
  have hJ : 0 ≤ scaleIntegral a T := by
    unfold scaleIntegral
    exact intervalIntegral.integral_nonneg hT.le
      (fun x _ => Real.exp_nonneg (strainAccum a x))
  unfold inverseScaleExact
  have hbr : 0 < h0 + 4 * nu * scaleIntegral a T := by
    have hnonneg : 0 ≤ 4 * nu * scaleIntegral a T := by positivity
    linarith
  exact mul_pos (Real.exp_pos _) hbr

/-- Manuscript Eq. (145): absolute integrability of the imposed strain on a
finite interval preserves a finite positive distributed scale at the terminal
time. -/
theorem finiteAccumulatedStrain_preserves_positive_scale
    {nu h0 T : ℝ} {a : ℝ → ℝ}
    (hnu : 0 < nu) (hh0 : 0 < h0) (hT : 0 < T)
    (ha : IntervalIntegrable a volume 0 T) :
    Tendsto
        (fun t => (inverseScaleExact nu h0 a t)⁻¹)
        (𝓝[<] T)
        (𝓝 ((inverseScaleExact nu h0 a T)⁻¹))
      ∧ 0 < (inverseScaleExact nu h0 a T)⁻¹ := by
  have hh := inverseScaleExact_tendsto_terminal
    (nu := nu) (h0 := h0) hT ha
  have hp := inverseScaleExact_terminal_pos
    (a := a) hnu hh0 hT
  refine ⟨?_, inv_pos.mpr hp⟩
  simpa only [Pi.inv_apply] using hh.inv₀ hp.ne'

/-- Reciprocal blow-up is equivalent to decay of a positive inverse scale. -/
theorem inv_tendsto_atTop_iff_tendsto_zero_of_eventually_pos
    {α : Type*} {l : Filter α} {h : α → ℝ}
    (hpos : ∀ᶠ x in l, 0 < h x) :
    Tendsto (fun x => (h x)⁻¹) l atTop ↔ Tendsto h l (𝓝 0) := by
  constructor
  · intro hinv
    have hz := hinv.inv_tendsto_atTop
    convert hz using 1
    funext x
    simp
  · intro hz
    have hgt : Tendsto h l (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hz, hpos⟩
    convert hgt.inv_tendsto_nhdsGT_zero using 1

/-- Manuscript Eq. (146): exact finite-time concentration diagnostic.  No
weighted-viscous term is discarded. -/
theorem exact_concentration_diagnostic
    {nu h0 : ℝ} {a : ℝ → ℝ} {l : Filter ℝ}
    (hpos : ∀ᶠ t in l, 0 < inverseScaleExact nu h0 a t) :
    Tendsto (fun t => (inverseScaleExact nu h0 a t)⁻¹) l atTop ↔
      Tendsto
        (fun t =>
          Real.exp (-strainAccum a t) *
            (h0 + 4 * nu * scaleIntegral a t))
        l (𝓝 0) := by
  exact inv_tendsto_atTop_iff_tendsto_zero_of_eventually_pos hpos

end

end KiknadzeKrasnov
