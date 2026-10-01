import KiknadzeKrasnov.SwirlExtrema
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace KiknadzeKrasnov
noncomputable section
open Set Filter MeasureTheory intervalIntegral
open scoped Topology

/-- Lower gamma continuity at the origin is obtained from its integrable kernel. -/
theorem lowerGamma_tendsto_zero_nhdsGT {s : ℝ} (hs : 0 < s) :
    Tendsto (lowerGamma s) (𝓝[>] 0) (𝓝 0) := by
  have hi := gammaKernel_intervalIntegrable (s := s) hs (x := 1) zero_le_one
  have hc := intervalIntegral.continuousOn_primitive_interval' hi
    (show (0 : ℝ) ∈ uIcc 0 1 by simp)
  have h0 := (hc 0 (by simp)).tendsto
  have hlim : Tendsto (lowerGamma s) (𝓝[≥] 0) (𝓝 0) := by
    unfold lowerGamma
    simpa [nhdsWithin_Icc_eq_nhdsGE zero_lt_one] using h0
  exact hlim.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)

/-- Actual regularised-gamma origin asymptotic, valid also for singular kernels 0<s<1. -/
theorem regLowerGamma_origin_ratio {s : ℝ} (hs : 0 < s) :
    Tendsto (fun x : ℝ => regLowerGamma s x / x ^ s)
      (𝓝[>] 0) (𝓝 (1 / (s * gammaFn s))) := by
  have hP : Tendsto (regLowerGamma s) (𝓝[>] 0) (𝓝 0) := by
    unfold regLowerGamma
    simpa using (lowerGamma_tendsto_zero_nhdsGT hs).div_const (gammaFn s)
  have hpow : Tendsto (fun x : ℝ => x ^ s) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuous_rpow_const hs.le).tendsto 0
    simpa [Real.zero_rpow hs.ne'] using (tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ)) h)
  have he : Tendsto (fun x : ℝ => Real.exp (-x) / (s * gammaFn s))
      (𝓝[>] 0) (𝓝 (1 / (s * gammaFn s))) := by
    have h : Tendsto (fun x : ℝ => Real.exp (-x)) (𝓝[>] 0) (𝓝 1) := by
      simpa using tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ))
        (by fun_prop : ContinuousAt (fun x : ℝ => Real.exp (-x)) 0).tendsto
    exact h.div_const _
  apply HasDerivAt.lhopital_zero_nhdsGT
    (f' := fun x => gammaKernel s x / gammaFn s)
    (g' := fun x => s * x ^ (s - 1))
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact regLowerGamma_hasDerivAt hs hx
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero hs.ne' (Real.rpow_pos_of_pos hx (s - 1)).ne'
  · exact hP
  · exact hpow
  · apply he.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    unfold gammaKernel
    field_simp [hs.ne', gammaFn_ne_zero hs, (Real.rpow_pos_of_pos hx (s - 1)).ne']

/-- Shape of the one-mode swirl in positive scaled radius. -/
def scaledSwirlShape (s x : ℝ) : ℝ := regLowerGamma s x / x ^ (1 / 2 : ℝ)

/-- For s>1/2 the swirl shape vanishes at the physical axis. -/
theorem scaledSwirlShape_tendsto_zero_axis {s : ℝ} (hs : (1 / 2 : ℝ) < s) :
    Tendsto (scaledSwirlShape s) (𝓝[>] 0) (𝓝 0) := by
  have hs0 : 0 < s := by linarith
  have hpow : Tendsto (fun x : ℝ => x ^ (s - 1 / 2)) (𝓝[>] 0) (𝓝 0) := by
    have hp : 0 < s - 1 / 2 := by linarith
    have h := (Real.continuous_rpow_const hp.le).tendsto 0
    rw [Real.zero_rpow hp.ne'] at h
    exact tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ)) h
  have hlim := (regLowerGamma_origin_ratio hs0).mul hpow
  have hz : Tendsto (fun x : ℝ => (regLowerGamma s x / x ^ s) * x ^ (s - 1 / 2))
      (𝓝[>] 0) (𝓝 0) := by simpa using hlim
  apply hz.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  unfold scaledSwirlShape
  have hp : x ^ s = x ^ (1 / 2 : ℝ) * x ^ (s - 1 / 2) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  rw [hp]
  rw [div_mul_eq_mul_div]
  exact mul_div_mul_right _ _ (Real.rpow_pos_of_pos hx (s - 1 / 2)).ne'


/-- The finite-circulation swirl shape also vanishes at infinite radius. -/
theorem scaledSwirlShape_tendsto_zero_atTop {s : ℝ} (hs : 0 < s) :
    Tendsto (scaledSwirlShape s) atTop (𝓝 0) := by
  have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).inv_tendsto_atTop
  unfold scaledSwirlShape
  simpa [div_eq_mul_inv] using (regLowerGamma_tendsto_one hs).mul hpow

/-- Positive circulation profile at each positive scaled radius. -/
theorem regLowerGamma_pos {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    0 < regLowerGamma s x := by
  apply div_pos _ (gammaFn_pos hs)
  unfold lowerGamma
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (gammaKernel_intervalIntegrable hs hx.le) _ hx
  intro y hy
  unfold gammaKernel
  exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hy.1 (s - 1))

/-- A continuous positive-radius profile vanishing at both ends attains a
global maximum at a positive radius. -/
theorem positive_profile_exists_max {f : ℝ → ℝ}
    (hc : ContinuousOn f (Ioi (0 : ℝ)))
    (h0 : Tendsto f (𝓝[>] 0) (𝓝 0)) (hinf : Tendsto f atTop (𝓝 0))
    (h1 : 0 < f 1) : ∃ x ∈ Ioi (0 : ℝ), IsMaxOn f (Ioi (0 : ℝ)) x := by
  obtain ⟨u, hu, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    (h0.eventually (Iio_mem_nhds h1))
  change 0 < u at hu
  obtain ⟨R, hlarge⟩ := (hinf.eventually (Iio_mem_nhds h1)).exists_forall_of_atTop
  let lo : ℝ := min (u / 2) (1 / 2)
  let hi : ℝ := max R 2
  have hlo : 0 < lo := lt_min (by linarith) (by norm_num)
  have hlo1 : lo ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  have hhi1 : 1 ≤ hi := le_trans (by norm_num : (1 : ℝ) ≤ 2) (le_max_right _ _)
  have hsub : Icc lo hi ⊆ Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le hlo hx.1
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    ⟨1, hlo1, hhi1⟩ (hc.mono hsub)
  refine ⟨x, hsub hx, ?_⟩
  intro y hy
  by_cases hyl : lo ≤ y
  · by_cases hyh : y ≤ hi
    · exact hmax ⟨hyl, hyh⟩
    · have hyR : R ≤ y := le_trans (le_max_left _ _) (le_of_lt (lt_of_not_ge hyh))
      exact (hlarge y hyR).le.trans (show f 1 ≤ f x from hmax ⟨hlo1, hhi1⟩)
  · have hyu : y < u := lt_trans (lt_of_not_ge hyl)
      (lt_of_le_of_lt (min_le_left _ _) (by linarith))
    exact (hsmall ⟨hy, hyu⟩).le.trans (show f 1 ≤ f x from hmax ⟨hlo1, hhi1⟩)

/-- The actual scaled one-mode swirl shape has a positive interior global maximum. -/
theorem scaledSwirlShape_exists_max {s : ℝ} (hs : (1 / 2 : ℝ) < s) :
    ∃ x ∈ Ioi (0 : ℝ), IsMaxOn (scaledSwirlShape s) (Ioi (0 : ℝ)) x := by
  have hs0 : 0 < s := by linarith
  apply positive_profile_exists_max
  · intro x hx
    unfold scaledSwirlShape
    exact ((regLowerGamma_hasDerivAt hs0 hx).continuousAt.div
      (Real.continuousAt_rpow_const x (1 / 2) (Or.inl hx.ne'))
      (Real.rpow_pos_of_pos hx (1 / 2)).ne').continuousWithinAt
  · exact scaledSwirlShape_tendsto_zero_axis hs
  · exact scaledSwirlShape_tendsto_zero_atTop hs0
  · unfold scaledSwirlShape
    exact div_pos (regLowerGamma_pos hs0 zero_lt_one) (by positivity)

/-- Exact scaled representation of the signed physical one-mode swirl. -/
theorem oneModeSwirl_scaled {circ s beta r : ℝ} (hb : 0 < beta) (hr : 0 < r) :
    oneModeSwirl circ s beta r =
      (circ * beta ^ (1 / 2 : ℝ) / (2 * Real.pi)) *
        scaledSwirlShape s (scaledX beta r) := by
  have hroot : (scaledX beta r) ^ (1 / 2 : ℝ) = beta ^ (1 / 2 : ℝ) * r := by
    unfold scaledX
    rw [Real.mul_rpow hb.le (sq_nonneg r)]
    have h : (r ^ 2) ^ (1 / 2 : ℝ) = r := by
      rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
      norm_num
    rw [h]
  unfold oneModeSwirl scaledSwirlShape
  rw [hroot]
  field_simp [hr.ne', (Real.rpow_pos_of_pos hb (1 / 2 : ℝ)).ne', Real.pi_ne_zero]

/-- Nonzero circulation has a positive-radius global maximum of swirl magnitude,
with the actual stationary-radius equation from the manuscript. -/
theorem oneModeSwirl_magnitude_maximum {circ s beta : ℝ}
    (hcirc : circ ≠ 0) (hs : (1 / 2 : ℝ) < s) (hb : 0 < beta) :
    ∃ r ∈ Ioi (0 : ℝ),
      IsMaxOn (fun y => |oneModeSwirl circ s beta y|) (Ioi (0 : ℝ)) r ∧
      2 * (scaledX beta r) ^ s * Real.exp (-(scaledX beta r)) =
        lowerGamma s (scaledX beta r) := by
  have hs0 : 0 < s := by linarith
  obtain ⟨x, hx, hmax⟩ := scaledSwirlShape_exists_max hs
  let r : ℝ := scaledFractionRadius beta x
  have hr : 0 < r := Real.sqrt_pos.mpr (div_pos hx hb)
  have hxr : scaledX beta r = x := scaledX_scaledFractionRadius hb hx.le
  have hbound : ∀ y ∈ Ioi (0 : ℝ),
      scaledSwirlShape s (scaledX beta y) ≤ scaledSwirlShape s (scaledX beta r) := by
    intro y hy
    rw [hxr]
    apply hmax
    unfold scaledX
    exact mul_pos hb (sq_pos_of_pos hy)
  have hmag : IsMaxOn (fun y => |oneModeSwirl circ s beta y|) (Ioi (0 : ℝ)) r := by
    intro y hy
    change |oneModeSwirl circ s beta y| ≤ |oneModeSwirl circ s beta r|
    rw [oneModeSwirl_scaled hb hy, oneModeSwirl_scaled hb hr, abs_mul, abs_mul]
    have hsy : 0 < scaledSwirlShape s (scaledX beta y) := by
      unfold scaledSwirlShape
      have hyx : 0 < scaledX beta y := by
        unfold scaledX
        exact mul_pos hb (sq_pos_of_pos hy)
      exact div_pos (regLowerGamma_pos hs0 hyx) (Real.rpow_pos_of_pos hyx _)
    have hsr : 0 < scaledSwirlShape s (scaledX beta r) := by
      unfold scaledSwirlShape
      rw [hxr]
      exact div_pos (regLowerGamma_pos hs0 hx) (Real.rpow_pos_of_pos hx _)
    rw [abs_of_pos hsy, abs_of_pos hsr]
    exact mul_le_mul_of_nonneg_left (hbound y hy) (abs_nonneg _)
  have hd : deriv (oneModeSwirl circ s beta) r = 0 := by
    rcases lt_or_gt_of_ne hcirc with hneg | hpos
    · have hmin : IsMinOn (oneModeSwirl circ s beta) (Ioi (0 : ℝ)) r := by
        intro y hy
        change oneModeSwirl circ s beta r ≤ oneModeSwirl circ s beta y
        rw [oneModeSwirl_scaled hb hr, oneModeSwirl_scaled hb hy]
        exact mul_le_mul_of_nonpos_left (hbound y hy) (by
          exact (div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hneg
            (Real.rpow_pos_of_pos hb _)) (mul_pos (by norm_num) Real.pi_pos)).le)
      exact (hmin.isLocalMin (Ioi_mem_nhds hr)).deriv_eq_zero
    · have hmaxu : IsMaxOn (oneModeSwirl circ s beta) (Ioi (0 : ℝ)) r := by
        intro y hy
        change oneModeSwirl circ s beta y ≤ oneModeSwirl circ s beta r
        rw [oneModeSwirl_scaled hb hy, oneModeSwirl_scaled hb hr]
        exact mul_le_mul_of_nonneg_left (hbound y hy) (by positivity)
      exact (hmaxu.isLocalMax (Ioi_mem_nhds hr)).deriv_eq_zero
  have hstat := (oneModeSwirl_deriv_zero_iff_scaled hcirc hs0 hb hr).mp hd
  have hxp : 0 < scaledX beta r := by rw [hxr]; exact hx
  exact ⟨r, hr, hmag, (swirl_extremum_scaled_eq_lowerGamma hs0 hxp).mp hstat⟩

end
end KiknadzeKrasnov
