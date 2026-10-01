import KiknadzeKrasnov.PhysicalIntegrals
import KiknadzeKrasnov.VorticityCertificate
import KiknadzeKrasnov.ClassicalProfiles

namespace KiknadzeKrasnov
noncomputable section
open Set Filter MeasureTheory intervalIntegral
open scoped Topology

/-- The complementary gamma definition is the actual improper tail integral. -/
theorem upperGammaComplement_eq_integral {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    upperGammaComplement s x = ∫ y in Ioi x, gammaKernel s y := by
  have h := integral_Ioi_sub_Ioi (Real.GammaIntegral_convergent hs) hx
  rw [← Real.Gamma_eq_integral hs] at h
  change gammaFn s - (∫ y in Ioi x, gammaKernel s y) = lowerGamma s x at h
  unfold upperGammaComplement
  linarith

/-- The logarithmic derivative in the separated profile equation. -/
theorem gammaKernel_logarithmic_derivative {s x : ℝ} (hx : 0 < x) :
    deriv (gammaKernel s) x / gammaKernel s x = (s - 1) / x - 1 := by
  rw [(gammaKernel_hasDerivAt_profile hx).deriv]
  unfold gammaKernel
  have hp : x ^ (s - 1) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  field_simp [hx.ne', hp, (Real.exp_pos (-x)).ne']

/-- Actual finite-mode circulation has the stated far-field limit. -/
theorem multimodeCirculationValue_tendsto_atTop {n : ℕ}
    {gammaLine s : ℝ} {circ beta : Fin n → ℝ}
    (hs : 0 < s) (hb : ∀ i, 0 < beta i) :
    Tendsto (multimodeCirculationValue gammaLine circ s beta) atTop
      (𝓝 (gammaLine + ∑ i, circ i)) := by
  have hi : ∀ i, Tendsto (fun r => distributedCirculation (circ i) s (beta i) r)
      atTop (𝓝 (circ i)) := by
    intro i
    have hx : Tendsto (fun r : ℝ => scaledX (beta i) r) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).const_mul_atTop (hb i)
    have h := (regLowerGamma_tendsto_one hs).comp hx
    simpa [distributedCirculation, Function.comp_def] using h.const_mul (circ i)
  unfold multimodeCirculationValue
  exact (tendsto_finsetSum Finset.univ (fun i _ => hi i)).const_add gammaLine

/-- Nondimensionalisation of the actual Riccati scale ODE, M147--M148. -/
theorem nondimensional_scale_hasDerivAt {nu beta0 tau : ℝ} {beta a : ℝ → ℝ}
    (hn : nu ≠ 0) (hb : beta0 ≠ 0)
    (hd : HasDerivAt beta
      (a (tau / (4 * nu * beta0)) * beta (tau / (4 * nu * beta0)) -
       4 * nu * beta (tau / (4 * nu * beta0)) ^ 2) (tau / (4 * nu * beta0))) :
    HasDerivAt (fun u => beta (u / (4 * nu * beta0)) / beta0)
      ((a (tau / (4 * nu * beta0)) / (4 * nu * beta0)) *
          (beta (tau / (4 * nu * beta0)) / beta0) -
        (beta (tau / (4 * nu * beta0)) / beta0) ^ 2) tau := by
  have h := (hd.comp tau ((hasDerivAt_id tau).div_const (4 * nu * beta0))).div_const beta0
  convert h using 1
  · funext u; rfl
  · field_simp [hn, hb]

/-- The local transport operator commutes with finite superposition. -/
theorem vorticityTransportResidualLocal_sum {n : ℕ} (nu a q r : ℝ)
    (w wt wr wrr : Fin n → ℝ) :
    vorticityTransportResidualLocal nu a q r (∑ i, w i) (∑ i, wt i)
      (∑ i, wr i) (∑ i, wrr i) =
    ∑ i, vorticityTransportResidualLocal nu a q r (w i) (wt i) (wr i) (wrr i) := by
  unfold vorticityTransportResidualLocal
  simp_rw [div_eq_mul_inv, mul_add]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]

/-- Both actual incomplete-gamma representations give the same regularised profile. -/
theorem regLowerGamma_eq_one_sub_upper {s : ℝ} (hs : 0 < s) (x : ℝ) :
    regLowerGamma s x = 1 - upperGammaComplement s x / gammaFn s := by
  unfold regLowerGamma upperGammaComplement
  field_simp [gammaFn_ne_zero hs]
  ring

end
end KiknadzeKrasnov
