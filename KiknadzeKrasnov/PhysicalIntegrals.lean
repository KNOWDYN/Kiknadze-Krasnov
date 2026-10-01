import KiknadzeKrasnov.MultimodeQualification
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace KiknadzeKrasnov
noncomputable section
open Set MeasureTheory

/-- Exact physical radial substitution x=beta r^2, including its Jacobian. -/
theorem integral_scaled_radius (f : ℝ → ℝ) {beta : ℝ} (hb : 0 < beta) :
    (∫ r in Ioi (0 : ℝ), (2 * beta * r) * f (scaledX beta r)) =
      ∫ x in Ioi (0 : ℝ), f x := by
  have hs := integral_comp_rpow_Ioi_of_pos
    (g := fun x : ℝ => beta * f (beta * x)) (p := 2) (by norm_num)
  have hm := integral_comp_mul_left_Ioi f 0 hb
  simp only [mul_zero, smul_eq_mul] at hm
  have he : (∫ r in Ioi (0 : ℝ), (2 * beta * r) * f (scaledX beta r)) =
      ∫ r in Ioi (0 : ℝ), ((2 : ℝ) * r ^ ((2 : ℝ) - 1)) *
        (beta * f (beta * r ^ (2 : ℝ))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    norm_num [scaledX, Real.rpow_natCast]
    ring
  rw [he]
  change (∫ r in Ioi (0 : ℝ), ((2 : ℝ) * r ^ ((2 : ℝ) - 1)) •
        (beta * f (beta * r ^ (2 : ℝ)))) = _
  rw [hs, integral_const_mul, hm]
  simp [hb.ne']

/-- Normalised physical radial circulation density, with respect to dr. -/
def radialCirculationDensity (s beta r : ℝ) : ℝ :=
  (2 * beta * r) * scaledCirculationDensity s (scaledX beta r)

/-- This density is the derivative of the actual enclosed circulation per unit amplitude. -/
theorem distributedCirculation_derivative_density {circ s beta r : ℝ}
    (hs : 0 < s) (hb : 0 < beta) (hr : 0 < r) :
    HasDerivAt (distributedCirculation circ s beta)
      (circ * radialCirculationDensity s beta r) r := by
  have hx : 0 < scaledX beta r := by unfold scaledX; positivity
  have h := (regLowerGamma_hasDerivAt_scaledDensity hs hx).comp r
    (scaledX_hasDerivAt beta r)
  unfold distributedCirculation radialCirculationDensity
  convert h.const_mul circ using 1
  · funext y; rfl
  · ring

/-- The physical moment integral, rather than a definition of its closed form. -/
def physicalRadialEvenMoment (s beta : ℝ) (n : ℕ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), r ^ (2 * n) * radialCirculationDensity s beta r

/-- The physical radial moment reduces to the certified gamma moment. -/
theorem physicalRadialEvenMoment_eq {s beta : ℝ} (n : ℕ)
    (_hs : 0 < s) (hb : 0 < beta) :
    physicalRadialEvenMoment s beta n = radialEvenMoment s beta n := by
  have hsub := integral_scaled_radius
    (fun x => (x / beta) ^ n * scaledCirculationDensity s x) hb
  have he : physicalRadialEvenMoment s beta n =
      ∫ r in Ioi (0 : ℝ), (2 * beta * r) *
        ((scaledX beta r / beta) ^ n * scaledCirculationDensity s (scaledX beta r)) := by
    unfold physicalRadialEvenMoment radialCirculationDensity
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hx : scaledX beta r / beta = r ^ 2 := by
      unfold scaledX
      field_simp
    dsimp only
    rw [hx, ← pow_mul]
    ring
  rw [he, hsub]
  unfold radialEvenMoment scaledGammaMoment
  rw [← integral_div, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  unfold scaledCirculationDensity
  rw [div_pow]
  have hp : s + (n : ℝ) - 1 = (s - 1) + (n : ℝ) := by ring
  rw [hp, Real.rpow_add hx, Real.rpow_natCast]
  ring

/-- Pair contribution to the actual enstrophy integral in physical radius. -/
def physicalEnstrophyPair (circI circJ s betaI betaJ : ℝ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), Real.pi * r *
    distributedVorticity circI s betaI r * distributedVorticity circJ s betaJ r

/-- Pointwise radial Jacobian identity for a pair of physical vorticity modes. -/
theorem physicalEnstrophyPair_integrand {circI circJ s betaI betaJ r : ℝ}
    (hbi : 0 < betaI) (hbj : 0 < betaJ) (hr : 0 < r) :
    Real.pi * r * distributedVorticity circI s betaI r *
      distributedVorticity circJ s betaJ r =
    (2 * r) * (circI * circJ * (betaI * betaJ) ^ s /
      (2 * Real.pi * gammaFn s ^ 2) *
        ((r ^ 2) ^ (2 * s - 2) * Real.exp (-((betaI + betaJ) * r ^ 2)))) := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hpow : (r ^ 2) ^ (s - 1) * (r ^ 2) ^ (s - 1) =
      (r ^ 2) ^ (2 * s - 2) := by
    rw [← Real.rpow_add hr2]
    congr 1
    ring
  have hbiPow : betaI * betaI ^ (s - 1) = betaI ^ s := by
    calc
      betaI * betaI ^ (s - 1) = betaI ^ (1 : ℝ) * betaI ^ (s - 1) := by rw [Real.rpow_one]
      _ = betaI ^ ((1 : ℝ) + (s - 1)) := (Real.rpow_add hbi 1 (s - 1)).symm
      _ = betaI ^ s := by congr 1; ring
  have hbjPow : betaJ * betaJ ^ (s - 1) = betaJ ^ s := by
    calc
      betaJ * betaJ ^ (s - 1) = betaJ ^ (1 : ℝ) * betaJ ^ (s - 1) := by rw [Real.rpow_one]
      _ = betaJ ^ ((1 : ℝ) + (s - 1)) := (Real.rpow_add hbj 1 (s - 1)).symm
      _ = betaJ ^ s := by congr 1; ring
  unfold distributedVorticity vorticityShape scaledX
  rw [Real.mul_rpow hbi.le hr2.le, Real.mul_rpow hbj.le hr2.le,
    Real.mul_rpow hbi.le hbj.le]
  have hexp : Real.exp (-(betaI * r ^ 2)) * Real.exp (-(betaJ * r ^ 2)) =
      Real.exp (-((betaI + betaJ) * r ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = circI * circJ / (Real.pi * gammaFn s ^ 2) * r *
        (betaI * betaI ^ (s - 1)) * (betaJ * betaJ ^ (s - 1)) *
        ((r ^ 2) ^ (s - 1) * (r ^ 2) ^ (s - 1)) *
        (Real.exp (-(betaI * r ^ 2)) * Real.exp (-(betaJ * r ^ 2))) := by field_simp [Real.pi_ne_zero]
    _ = _ := by rw [hbiPow, hbjPow, hpow, hexp]; ring

/-- Evaluation of the original physical pair integral, including the radial substitution. -/
theorem physicalEnstrophyPair_eq {circI circJ s betaI betaJ : ℝ}
    (hs : (1 / 2 : ℝ) < s) (hbi : 0 < betaI) (hbj : 0 < betaJ) :
    physicalEnstrophyPair circI circJ s betaI betaJ =
      enstrophyPairClosed circI circJ s betaI betaJ := by
  have hsub := integral_scaled_radius
    (fun x => circI * circJ * (betaI * betaJ) ^ s /
      (2 * Real.pi * gammaFn s ^ 2) *
        (x ^ (2 * s - 2) * Real.exp (-((betaI + betaJ) * x))))
    (beta := 1) zero_lt_one
  have he : physicalEnstrophyPair circI circJ s betaI betaJ =
      ∫ r in Ioi (0 : ℝ), (2 * (1 : ℝ) * r) *
        (circI * circJ * (betaI * betaJ) ^ s /
          (2 * Real.pi * gammaFn s ^ 2) *
            ((scaledX 1 r) ^ (2 * s - 2) *
              Real.exp (-((betaI + betaJ) * scaledX 1 r)))) := by
    unfold physicalEnstrophyPair
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simpa [scaledX] using physicalEnstrophyPair_integrand hbi hbj hr
  rw [he, hsub, integral_const_mul]
  change enstrophyPairReduced circI circJ s betaI betaJ = _
  exact enstrophyPairReduced_eq_closed hs hbi hbj

/-- Integrability is certified for each physical pair, including zero amplitudes. -/
theorem physicalEnstrophyPair_integrable {circI circJ s betaI betaJ : ℝ}
    (hs : (1 / 2 : ℝ) < s) (hbi : 0 < betaI) (hbj : 0 < betaJ) :
    IntegrableOn (fun r => Real.pi * r * distributedVorticity circI s betaI r *
      distributedVorticity circJ s betaJ r) (Ioi (0 : ℝ)) := by
  by_cases hi : circI = 0
  · simp [hi, distributedVorticity]
  by_cases hj : circJ = 0
  · simp [hj, distributedVorticity]
  by_contra hbad
  have hz : physicalEnstrophyPair circI circJ s betaI betaJ = 0 :=
    integral_undef hbad
  rw [physicalEnstrophyPair_eq hs hbi hbj] at hz
  have hs0 : 0 < s := by linarith
  have hs2 : 0 < 2 * s - 1 := by linarith
  have hn : enstrophyPairClosed circI circJ s betaI betaJ ≠ 0 := by
    unfold enstrophyPairClosed
    apply mul_ne_zero
    · exact div_ne_zero (gammaFn_ne_zero hs2)
        (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)
          (pow_ne_zero 2 (gammaFn_ne_zero hs0)))
    · exact div_ne_zero (mul_ne_zero (mul_ne_zero hi hj)
        (Real.rpow_pos_of_pos (mul_pos hbi hbj) s).ne')
        (Real.rpow_pos_of_pos (add_pos hbi hbj) (2 * s - 1)).ne'
  exact hn hz

/-- The full physical enstrophy integral equals the finite-mode closed formula. -/
theorem physicalMultimodeEnstrophy_eq {n : ℕ} {circ beta : Fin n → ℝ} {s : ℝ}
    (hs : (1 / 2 : ℝ) < s) (hb : ∀ i, 0 < beta i) :
    enstrophyPerUnitLength (multimodeDistributedVorticity circ s beta) =
      multimodeEnstrophyClosed circ s beta := by
  classical
  have he : (fun r => (1 / 2 : ℝ) *
      ((multimodeDistributedVorticity circ s beta r) ^ 2 * (2 * Real.pi * r))) =
      (fun r => ∑ i, ∑ j, Real.pi * r * distributedVorticity (circ i) s (beta i) r *
        distributedVorticity (circ j) s (beta j) r) := by
    funext r
    unfold multimodeDistributedVorticity
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  unfold enstrophyPerUnitLength
  rw [← integral_const_mul, he, integral_finsetSum]
  · unfold multimodeEnstrophyClosed
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      exact physicalEnstrophyPair_eq hs (hb i) (hb j)
    · intro j hj
      exact physicalEnstrophyPair_integrable hs (hb i) (hb j)
  · intro i hi
    exact integrable_finsetSum _ (fun j hj => physicalEnstrophyPair_integrable hs (hb i) (hb j))

end
end KiknadzeKrasnov
