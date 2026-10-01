import KiknadzeKrasnov.FamilyClosure
import Mathlib.Analysis.Asymptotics.Ring

namespace KiknadzeKrasnov
noncomputable section
open Set Filter Asymptotics
open scoped Topology

/-- The cubic remainder in the regular one-mode swirl expansion, M063. -/
theorem oneModeSwirl_regular_cubic_remainder (circ : ℝ) {beta : ℝ} (hb : 0 < beta) :
    (fun r => oneModeSwirl circ 1 beta r - circ * beta / (2 * Real.pi) * r)
      =O[𝓝[>] 0] (fun r : ℝ => r ^ 3) := by
  have hx : Tendsto (fun r : ℝ => -beta * r ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun r : ℝ => -beta * r ^ 2) 0 := by fun_prop
    simpa using tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ)) hc.tendsto
  have he := (Real.exp_sub_sum_range_isBigO_pow 2).comp_tendsto hx
  have hm := he.mul (isBigO_refl (fun r : ℝ => r⁻¹) (𝓝[>] 0))
  have hc := hm.const_mul_left (-circ / (2 * Real.pi))
  have h : (fun r => oneModeSwirl circ 1 beta r - circ * beta / (2 * Real.pi) * r)
      =O[𝓝[>] 0] (fun r : ℝ => beta ^ 2 * r ^ 3) := by
    apply hc.congr'
    · filter_upwards [self_mem_nhdsWithin] with r hr
      change 0 < r at hr
      dsimp only [Function.comp_apply]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
        Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one, zero_add]
      rw [oneModeSwirl, regLowerGamma_one (by unfold scaledX; positivity)]
      unfold scaledX
      field_simp [hr.ne', Real.pi_ne_zero]
      ring
    · filter_upwards [self_mem_nhdsWithin] with r hr
      change 0 < r at hr
      dsimp only [Function.comp_apply]
      field_simp [hr.ne']
  exact h.of_const_mul_right

/-- The finite regular-mode sum has the same cubic remainder, including signed coefficients. -/
theorem multimodeSwirl_regular_cubic_remainder {n : ℕ} (circ beta : Fin n → ℝ) (hb : ∀ i, 0 < beta i) :
    (fun r => multimodeSwirl 0 circ 1 beta r -
      r / (2 * Real.pi) * ∑ i, circ i * beta i)
      =O[𝓝[>] 0] (fun r : ℝ => r ^ 3) := by
  have h := IsBigO.sum (s := Finset.univ) (fun i _ =>
    oneModeSwirl_regular_cubic_remainder (circ i) (hb i))
  apply h.congr'
  · filter_upwards with r
    simp only [Finset.sum_apply, Finset.sum_sub_distrib]
    unfold multimodeSwirl multimodeCirculationValue oneModeSwirl distributedCirculation
    simp only [zero_add, Finset.sum_div, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
  · rfl

end
end KiknadzeKrasnov
