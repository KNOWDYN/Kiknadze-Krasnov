import KiknadzeKrasnov.FamilyClosure

namespace KiknadzeKrasnov
noncomputable section
open Set Filter
open scoped Topology

/-- Actual total specific angular momentum, with a constant line term. -/
def multimodeAngularMomentum {n : ℕ} (gammaLine : ℝ) (circ : Fin n → ℝ)
    (s : ℝ) (beta : Fin n → ℝ) (r : ℝ) : ℝ :=
  gammaLine / (2 * Real.pi) + ∑ i, distributedAngularMomentum (circ i) s (beta i) r

theorem multimodeAngularMomentum_eq_radius_swirl {n : ℕ} (gammaLine : ℝ)
    (circ : Fin n → ℝ) (s : ℝ) (beta : Fin n → ℝ) {r : ℝ} (hr : 0 < r) :
    multimodeAngularMomentum gammaLine circ s beta r =
      r * multimodeSwirl gammaLine circ s beta r := by
  unfold multimodeAngularMomentum multimodeSwirl multimodeCirculationValue
    distributedAngularMomentum distributedCirculation
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  field_simp [hr.ne', Real.pi_ne_zero]

/-- Time derivative commutes with the physical finite angular-momentum sum. -/
theorem multimodeAngularMomentum_time_hasDerivAt {n : ℕ} {gammaLine s r t : ℝ}
    {circ betaDot : Fin n → ℝ} {beta : Fin n → ℝ → ℝ}
    (hs : 0 < s) (hr : 0 < r) (hb : ∀ i, 0 < beta i t)
    (hd : ∀ i, HasDerivAt (beta i) (betaDot i) t) :
    HasDerivAt (fun u => multimodeAngularMomentum gammaLine circ s (fun i => beta i u) r)
      (∑ i, distributedAngularMomentumTimeDerivative (circ i) s (beta i t) (betaDot i) r) t := by
  have h := (HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    distributedAngularMomentum_time_hasDerivAt_actual (circ := circ i) hs (hb i) hr (hd i))).const_add
    (gammaLine / (2 * Real.pi))
  convert h using 1
  · funext u; simp [multimodeAngularMomentum]

/-- First radial derivative of the physical total angular momentum. -/
theorem multimodeAngularMomentum_radial_hasDerivAt {n : ℕ} {gammaLine s r : ℝ}
    {circ beta : Fin n → ℝ} (hs : 0 < s) (hr : 0 < r) (hb : ∀ i, 0 < beta i) :
    HasDerivAt (multimodeAngularMomentum gammaLine circ s beta)
      (∑ i, distributedAngularMomentumRadialDerivative (circ i) s (beta i) r) r := by
  have h := (HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    distributedAngularMomentum_radial_hasDerivAt_actual (circ := circ i) hs (hb i) hr)).const_add
    (gammaLine / (2 * Real.pi))
  convert h using 1
  · funext u; simp [multimodeAngularMomentum]

/-- Second radial derivative obtained by differentiating the certified finite first derivative. -/
theorem multimodeAngularMomentumRadialDerivative_hasDerivAt {n : ℕ} {s r : ℝ}
    {circ beta : Fin n → ℝ} (hs : 0 < s) (hr : 0 < r) (hb : ∀ i, 0 < beta i) :
    HasDerivAt (fun u => ∑ i, distributedAngularMomentumRadialDerivative (circ i) s (beta i) u)
      (∑ i, distributedAngularMomentumSecondRadialDerivative (circ i) s (beta i) r) r := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    distributedAngularMomentumRadialDerivative_hasDerivAt (circ := circ i) hs (hb i) hr)
  convert h using 1
  funext u; simp

/-- The actual finite-field angular-momentum operator equals the certified sum of mode residuals. -/
theorem multimodeAngularMomentum_operator_zero {n : ℕ} {nu a q s r : ℝ}
    {circ beta betaDot : Fin n → ℝ} (hr : 0 < r) (hb : ∀ i, 0 < beta i)
    (hscale : ∀ i, betaScaleResidual nu a (beta i) (betaDot i) = 0)
    (hshape : q = 2 * nu * (s - 1)) :
    angularMomentumResidual nu (radialVelocity a q r) r
      (∑ i, distributedAngularMomentumTimeDerivative (circ i) s (beta i) (betaDot i) r)
      (∑ i, distributedAngularMomentumRadialDerivative (circ i) s (beta i) r)
      (∑ i, distributedAngularMomentumSecondRadialDerivative (circ i) s (beta i) r) = 0 := by
  have h := multimodeAngularMomentumResidual_zero (circ := circ) hr hb hscale hshape
  unfold multimodeAngularMomentumResidual distributedAngularMomentumResidualActual at h
  unfold angularMomentumResidual
  simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.sum_div, mul_sub] using h

/-- With distinct scales and a nonzero second mode, the total vorticity gradient
is nonzero at the first component's distinguished radius. This is an actual
field counterexample to a universal common total-field zero-flux cylinder. -/
theorem twoMode_vorticity_gradient_nonzero_at_component_peak
    {circ1 circ2 s beta1 beta2 r : ℝ} (hs : 1 < s)
    (hb1 : 0 < beta1) (hb2 : 0 < beta2) (hr : 0 < r)
    (hpeak : scaledX beta1 r = s - 1) (hne : beta2 ≠ beta1) (hc : circ2 ≠ 0) :
    deriv (fun y => distributedVorticity circ1 s beta1 y +
      distributedVorticity circ2 s beta2 y) r ≠ 0 := by
  have hs0 : 0 < s := lt_trans zero_lt_one hs
  have hcoef1 : vorticityRadialCoefficient s beta1 r = 0 := by
    unfold vorticityRadialCoefficient
    unfold scaledX at hpeak
    field_simp [hr.ne']
    nlinarith [hpeak]
  have hcoef2 : vorticityRadialCoefficient s beta2 r ≠ 0 := by
    intro hz
    unfold vorticityRadialCoefficient at hz
    field_simp [hr.ne'] at hz
    unfold scaledX at hpeak
    have he : beta2 * r ^ 2 = beta1 * r ^ 2 := by nlinarith [hz, hpeak]
    exact hne (mul_right_cancel₀ (sq_pos_of_pos hr).ne' he)
  have hw : distributedVorticity circ2 s beta2 r ≠ 0 := by
    unfold distributedVorticity
    apply mul_ne_zero
    · exact div_ne_zero (mul_ne_zero hc hb2.ne')
        (mul_ne_zero Real.pi_ne_zero (gammaFn_ne_zero hs0))
    · exact (vorticityShape_pos (by unfold scaledX; positivity)).ne'
  have hsum := (distributedVorticity_hasDerivAt_coefficient (circ := circ1) hs0 hb1 hr).add
    (distributedVorticity_hasDerivAt_coefficient (circ := circ2) hs0 hb2 hr)
  change deriv (distributedVorticity circ1 s beta1 + distributedVorticity circ2 s beta2) r ≠ 0
  rw [hsum.deriv, hcoef1, zero_mul, zero_add]
  exact mul_ne_zero hcoef2 hw

end
end KiknadzeKrasnov
