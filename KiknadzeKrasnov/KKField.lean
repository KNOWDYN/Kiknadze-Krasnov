import KiknadzeKrasnov.PressureField

namespace KiknadzeKrasnov

noncomputable section

open scoped BigOperators

/-- Finite-mode circulation function `W=2π r u_theta`. -/
def multimodeCirculationValue {n : ℕ}
    (gammaLine : ℝ) (circ : Fin n → ℝ) (s : ℝ)
    (beta : Fin n → ℝ) (r : ℝ) : ℝ :=
  gammaLine + ∑ i, circ i * regLowerGamma s (scaledX (beta i) r)

/-- Complete finite-mode KK swirl at one time. -/
def multimodeSwirl {n : ℕ}
    (gammaLine : ℝ) (circ : Fin n → ℝ) (s : ℝ)
    (beta : Fin n → ℝ) (r : ℝ) : ℝ :=
  multimodeCirculationValue gammaLine circ s beta r / (2 * Real.pi * r)

/-- The swirl definition reproduces `L=r u_theta=W/(2π)` on the punctured domain. -/
theorem angularMomentum_multimodeSwirl {n : ℕ}
    {gammaLine : ℝ} {circ : Fin n → ℝ} {s r : ℝ} {beta : Fin n → ℝ}
    (hr : r ≠ 0) :
    angularMomentum r (multimodeSwirl gammaLine circ s beta r) =
      multimodeCirculationValue gammaLine circ s beta r / (2 * Real.pi) := by
  unfold angularMomentum multimodeSwirl
  field_simp [hr, Real.pi_ne_zero]

/-- Constant central line circulation contributes a constant angular momentum on `r>0`. -/
def centralAngularMomentum (gammaLine : ℝ) : ℝ := gammaLine / (2 * Real.pi)

/-- A frozen line-circulation amplitude has zero radial and temporal derivatives. -/
theorem centralAngularMomentum_hasDerivAt (gammaLine r : ℝ) :
    HasDerivAt (fun _ : ℝ => centralAngularMomentum gammaLine) 0 r := by
  exact hasDerivAt_const r _

/-- Sum of the distributed one-mode angular residuals; the constant line term contributes zero. -/
def multimodeAngularResidual {n : ℕ}
    (p : FluidParams) (q a : ℝ)
    (circ beta betaDot : Fin n → ℝ) (r : ℝ) : ℝ :=
  ∑ i, (circ i / (2 * Real.pi)) *
    gammaAngularResidual p.nu a q (beta i) (betaDot i)
      (shape p q) (scaledX (beta i) r)

/-- Every finite superposition satisfies the angular-momentum equation when each scale satisfies its Riccati ODE. -/
theorem multimodeAngularResidual_zero {n : ℕ}
    (p : FluidParams) {q a r : ℝ}
    {circ beta betaDot : Fin n → ℝ}
    (hr : 0 < r) (hbeta : ∀ i, 0 < beta i)
    (hscale : ∀ i, scaleResidual p.nu a (beta i) (betaDot i) = 0) :
    multimodeAngularResidual p q a circ beta betaDot r = 0 := by
  classical
  unfold multimodeAngularResidual
  apply Finset.sum_eq_zero
  intro i hi
  have hxi : 0 < scaledX (beta i) r := by
    unfold scaledX
    exact mul_pos (hbeta i) (pow_pos hr 2)
  rw [gammaAngularResidual_zero p (hbeta i).ne' hxi.ne' (hscale i)]
  ring

/-- The full pointwise KK velocity triplet at one time. -/
structure KKVelocity where
  ur : ℝ
  uTheta : ℝ
  uz : ℝ

/-- Assemble the prescribed meridional field and finite-mode swirl into one velocity value. -/
def kkVelocityAt {n : ℕ}
    (a b q gammaLine r z : ℝ) (circ : Fin n → ℝ)
    (s : ℝ) (beta : Fin n → ℝ) : KKVelocity where
  ur := radialVelocity a q r
  uTheta := multimodeSwirl gammaLine circ s beta r
  uz := axialVelocity a b z

end

end KiknadzeKrasnov
