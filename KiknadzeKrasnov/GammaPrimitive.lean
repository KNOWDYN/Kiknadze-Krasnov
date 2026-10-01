import KiknadzeKrasnov.FamilyClosure
import KiknadzeKrasnov.SwirlMaximum
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue

namespace KiknadzeKrasnov
noncomputable section
open Set Filter
open scoped Topology

/-- General first-derivative solution of the separated gamma-profile ODE on x>0. -/
theorem separated_profile_derivative_general {G : ℝ → ℝ} {s : ℝ}
    (hG : ∀ x > 0, HasDerivAt G (((s - 1) / x - 1) * G x) x) :
    ∃ K : ℝ, ∀ x > 0, G x = K * gammaKernel s x := by
  let H : ℝ → ℝ := fun x => G x / gammaKernel s x
  have hd : ∀ x > 0, HasDerivAt H 0 x := by
    intro x hx
    have hk : gammaKernel s x ≠ 0 := by
      unfold gammaKernel
      exact (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hx _)).ne'
    have h := (hG x hx).div (gammaKernel_hasDerivAt_profile hx) hk
    convert h using 1
    ring
  obtain ⟨K, hK⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hd x hx).deriv)
  refine ⟨K, ?_⟩
  intro x hx
  have hk : gammaKernel s x ≠ 0 := by
    unfold gammaKernel
    exact (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hx _)).ne'
  exact (div_eq_iff hk).mp (hK x hx)

/-- Integration gives the full affine upper-incomplete-gamma profile. -/
theorem separated_profile_primitive_general {F : ℝ → ℝ} {s K : ℝ}
    (hs : 0 < s) (hF : ∀ x > 0, HasDerivAt F (K * gammaKernel s x) x) :
    ∃ K0 : ℝ, ∀ x > 0, F x = K0 - K * upperGammaComplement s x := by
  let H : ℝ → ℝ := fun x => F x + K * upperGammaComplement s x
  have hd : ∀ x > 0, HasDerivAt H 0 x := by
    intro x hx
    have hu := (hasDerivAt_const x (gammaFn s)).sub (lowerGamma_hasDerivAt hs hx)
    have h := (hF x hx).add (hu.const_mul K)
    convert h using 1
    · funext v; rfl
    · ring
  obtain ⟨K0, hK0⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hd x hx).deriv)
  refine ⟨K0, ?_⟩
  intro x hx
  have h := hK0 x hx
  dsimp [H] at h
  linarith

/-- Every fraction strictly between zero and one has a positive gamma quantile. -/
theorem regLowerGamma_quantile_exists {s fraction : ℝ}
    (hs : 0 < s) (hf0 : 0 < fraction) (hf1 : fraction < 1) :
    ∃ x > 0, regLowerGamma s x = fraction := by
  have hc : ContinuousOn (regLowerGamma s) (Ioi (0 : ℝ)) :=
    fun x hx => (regLowerGamma_hasDerivAt hs hx).continuousAt.continuousWithinAt
  have h0 : Tendsto (regLowerGamma s) (𝓝[>] 0) (𝓝 0) := by
    unfold regLowerGamma
    simpa using (lowerGamma_tendsto_zero_nhdsGT hs).div_const (gammaFn s)
  have hsub := isPreconnected_Ioi.intermediate_value_Ioo
    (show 𝓝[>] (0 : ℝ) ≤ 𝓟 (Ioi 0) from inf_le_right)
    (show atTop ≤ 𝓟 (Ioi (0 : ℝ)) from le_principal_iff.mpr (eventually_gt_atTop 0))
    hc h0 (regLowerGamma_tendsto_one hs)
  exact hsub ⟨hf0, hf1⟩

end
end KiknadzeKrasnov
