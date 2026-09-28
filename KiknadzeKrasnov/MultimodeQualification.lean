import KiknadzeKrasnov.Enstrophy

namespace KiknadzeKrasnov

noncomputable section

open scoped BigOperators

/-!
Finite-mode qualifications for the KK family.  The angular-momentum equation is
linear once the meridional field is fixed.  Theorems in this file deliberately
stop short of asserting a common material zero-flux surface for distinct scales.
-/

/-- Finite-mode circulation W=2 pi r u_theta, including optional line circulation. -/
def multimodeCirculationValue {n : ℕ}
    (gammaLine : ℝ) (circ : Fin n → ℝ) (s : ℝ)
    (beta : Fin n → ℝ) (r : ℝ) : ℝ :=
  gammaLine + ∑ i, distributedCirculation (circ i) s (beta i) r

/-- Complete finite-mode swirl at one time. -/
def multimodeSwirl {n : ℕ}
    (gammaLine : ℝ) (circ : Fin n → ℝ) (s : ℝ)
    (beta : Fin n → ℝ) (r : ℝ) : ℝ :=
  multimodeCirculationValue gammaLine circ s beta r / (2 * Real.pi * r)

/-- Finite sum of distributed axial-vorticity modes. -/
def multimodeDistributedVorticity {n : ℕ}
    (circ : Fin n → ℝ) (s : ℝ) (beta : Fin n → ℝ) (r : ℝ) : ℝ :=
  ∑ i, distributedVorticity (circ i) s (beta i) r

/-- On r>0, the finite-mode circulation is exactly 2 pi r u_theta. -/
theorem multimodeCirculationValue_eq_two_pi_radius_swirl {n : ℕ}
    {gammaLine : ℝ} {circ : Fin n → ℝ} {s r : ℝ} {beta : Fin n → ℝ}
    (hr : PuncturedRadius r) :
    multimodeCirculationValue gammaLine circ s beta r =
      2 * Real.pi * r * multimodeSwirl gammaLine circ s beta r := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  unfold multimodeSwirl
  field_simp [hr0, Real.pi_ne_zero]

/-- Manuscript/Supplement multimode exactness: each compatible mode has zero
angular-momentum residual, hence so does any finite superposition. -/
def multimodeAngularMomentumResidual {n : ℕ}
    (nu a q s r : ℝ) (circ beta betaDot : Fin n → ℝ) : ℝ :=
  ∑ i, distributedAngularMomentumResidualActual
    nu a q (beta i) (betaDot i) (circ i) s r

theorem multimodeAngularMomentumResidual_zero {n : ℕ}
    {nu a q s r : ℝ} {circ beta betaDot : Fin n → ℝ}
    (hr : PuncturedRadius r)
    (hbeta : ∀ i, 0 < beta i)
    (hscale : ∀ i, betaScaleResidual nu a (beta i) (betaDot i) = 0)
    (hshape : q = 2 * nu * (s - 1)) :
    multimodeAngularMomentumResidual nu a q s r circ beta betaDot = 0 := by
  classical
  unfold multimodeAngularMomentumResidual
  apply Finset.sum_eq_zero
  intro i hi
  exact distributedAngularMomentumResidualActual_zero
    (hbeta i) hr (hscale i) hshape

/-- With one common scale, finite distributed circulation collapses to one
radial profile multiplied by the summed distributed circulation. -/
theorem multimodeCirculationValue_equalScale {n : ℕ}
    (gammaLine : ℝ) (circ : Fin n → ℝ) (s beta r : ℝ) :
    multimodeCirculationValue gammaLine circ s (fun _ => beta) r =
      gammaLine + (∑ i, circ i) * regLowerGamma s (scaledX beta r) := by
  classical
  unfold multimodeCirculationValue distributedCirculation
  rw [Finset.sum_mul]

/-- Equal scales collapse the distributed-vorticity sum to one common radial shape. -/
theorem multimodeDistributedVorticity_equalScale {n : ℕ}
    (circ : Fin n → ℝ) (s beta r : ℝ) :
    multimodeDistributedVorticity circ s (fun _ => beta) r =
      distributedVorticity (∑ i, circ i) s beta r := by
  classical
  unfold multimodeDistributedVorticity distributedVorticity
  let K := beta / (Real.pi * gammaFn s) * vorticityShape s (scaledX beta r)
  calc
    (∑ i, circ i * beta / (Real.pi * gammaFn s) *
        vorticityShape s (scaledX beta r)) = ∑ i, circ i * K := by
          apply Finset.sum_congr rfl
          intro i hi
          unfold K
          ring
    _ = (∑ i, circ i) * K := by rw [Finset.sum_mul]
    _ = (∑ i, circ i) * beta / (Real.pi * gammaFn s) *
        vorticityShape s (scaledX beta r) := by
          unfold K
          ring

/-- Every finite component has its own scaled-material transport law. -/
theorem multimode_scaledMaterial_hasDerivAt {n : ℕ}
    {beta betaDot : Fin n → ℝ → ℝ} {y : ℝ → ℝ}
    {nu q s t : ℝ} {a : ℝ → ℝ}
    (hbeta : ∀ i, HasDerivAt (beta i) (betaDot i t) t)
    (hy : HasDerivAt y (-a t * y t + 2 * q) t)
    (hscale : ∀ i, betaScaleResidual nu (a t) (beta i t) (betaDot i t) = 0)
    (hcompat : q = 2 * nu * (s - 1)) :
    ∀ i, HasDerivAt (fun tau => beta i tau * y tau)
      (4 * nu * beta i t * ((s - 1) - beta i t * y t)) t := by
  intro i
  exact scaledMaterial_hasDerivAt
    (hbeta i) hy (hscale i) hcompat

/-- Radial differentiation commutes with the finite vorticity sum. -/
theorem multimodeDistributedVorticity_hasDerivAt {n : ℕ}
    {circ : Fin n → ℝ} {s r : ℝ} {beta : Fin n → ℝ}
    (hs : 0 < s) (hbeta : ∀ i, 0 < beta i) (hr : PuncturedRadius r) :
    HasDerivAt (multimodeDistributedVorticity circ s beta)
      (∑ i, deriv (distributedVorticity (circ i) s (beta i)) r) r := by
  classical
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (distributedVorticity_hasDerivAt_r
      (circ := circ i) (s := s) (beta := beta i) (r := r)
      hs (hbeta i) hr).differentiableAt.hasDerivAt)
  unfold multimodeDistributedVorticity
  have hfun :
      (∑ i, distributedVorticity (circ i) s (beta i)) =
        (fun x => ∑ i, distributedVorticity (circ i) s (beta i) x) := by
    funext x
    simp
  rw [← hfun]
  exact hsum

theorem deriv_multimodeDistributedVorticity {n : ℕ}
    {circ : Fin n → ℝ} {s r : ℝ} {beta : Fin n → ℝ}
    (hs : 0 < s) (hbeta : ∀ i, 0 < beta i) (hr : PuncturedRadius r) :
    deriv (multimodeDistributedVorticity circ s beta) r =
      ∑ i, deriv (distributedVorticity (circ i) s (beta i)) r :=
  (multimodeDistributedVorticity_hasDerivAt hs hbeta hr).deriv

/-- Equal positive scales give one common distinguished material radius. -/
theorem materialRadius_eq_of_beta_eq
    {s beta₁ beta₂ : ℝ} (hbeta : beta₁ = beta₂) :
    materialRadius s beta₁ = materialRadius s beta₂ := by
  rw [hbeta]

/-- For s>1, distinct positive scales have distinct component material radii.
This records the obstruction without asserting where a zero of the summed
vorticity derivative lies. -/
theorem materialRadius_ne_of_beta_ne
    {s beta₁ beta₂ : ℝ} (hs : 1 < s)
    (hb₁ : 0 < beta₁) (hb₂ : 0 < beta₂) (hne : beta₁ ≠ beta₂) :
    materialRadius s beta₁ ≠ materialRadius s beta₂ := by
  intro hrEq
  have hsx₁ := scaledX_materialRadius (s := s) (beta := beta₁) hs hb₁
  have hsx₂ := scaledX_materialRadius (s := s) (beta := beta₂) hs hb₂
  unfold scaledX at hsx₁ hsx₂
  rw [hrEq] at hsx₁
  have hsqpos : 0 < (materialRadius s beta₂) ^ 2 :=
    sq_pos_of_pos (materialRadius_pos hs hb₂)
  have hmul : beta₁ * (materialRadius s beta₂) ^ 2 =
      beta₂ * (materialRadius s beta₂) ^ 2 := hsx₁.trans hsx₂.symm
  have hbeq : beta₁ = beta₂ :=
    mul_right_cancel₀ (ne_of_gt hsqpos) hmul
  exact hne hbeq

/-- The finite-mode enclosed circulation has radial derivative 2 pi r times
the summed distributed vorticity; the line circulation is constant. -/
theorem multimodeCirculationValue_hasDerivAt {n : ℕ}
    {gammaLine : ℝ} {circ : Fin n → ℝ} {s r : ℝ}
    {beta : Fin n → ℝ}
    (hs : 0 < s) (hr : PuncturedRadius r) (hbeta : ∀ i, 0 < beta i) :
    HasDerivAt (multimodeCirculationValue gammaLine circ s beta)
      (2 * Real.pi * r * multimodeDistributedVorticity circ s beta r) r := by
  classical
  have hsum' :
      HasDerivAt
        (∑ i : Fin n, distributedCirculation (circ i) s (beta i))
        (∑ i : Fin n,
          2 * Real.pi * r * distributedVorticity (circ i) s (beta i) r) r := by
    apply HasDerivAt.sum
    intro i hi
    exact distributedCirculation_hasDerivAt_r hs (hbeta i) hr
  have hfun :
      (fun y => ∑ i : Fin n, distributedCirculation (circ i) s (beta i) y) =
        (∑ i : Fin n, distributedCirculation (circ i) s (beta i)) := by
    funext y
    simp only [Finset.sum_apply]
  have hsum :
      HasDerivAt
        (fun y => ∑ i : Fin n, distributedCirculation (circ i) s (beta i) y)
        (∑ i : Fin n,
          2 * Real.pi * r * distributedVorticity (circ i) s (beta i) r) r := by
    rw [hfun]
    exact hsum'
  have htotal := (hasDerivAt_const r gammaLine).add hsum
  convert htotal using 1
  · funext y
    rfl
  · simp [multimodeDistributedVorticity, Finset.mul_sum]

/-- Exact derivative of the finite-mode swirl. -/
theorem multimodeSwirl_hasDerivAt {n : ℕ}
    {gammaLine : ℝ} {circ : Fin n → ℝ} {s r : ℝ}
    {beta : Fin n → ℝ}
    (hs : 0 < s) (hr : PuncturedRadius r) (hbeta : ∀ i, 0 < beta i) :
    HasDerivAt (multimodeSwirl gammaLine circ s beta)
      ((2 * Real.pi * r ^ 2 * multimodeDistributedVorticity circ s beta r -
          multimodeCirculationValue gammaLine circ s beta r) /
        (2 * Real.pi * r ^ 2)) r := by
  have hG := multimodeCirculationValue_hasDerivAt
    (gammaLine := gammaLine) (circ := circ) (beta := beta) hs hr hbeta
  have hden : HasDerivAt (fun y : ℝ => 2 * Real.pi * y) (2 * Real.pi) r := by
    simpa using (hasDerivAt_id r).const_mul (2 * Real.pi)
  have hden0 : 2 * Real.pi * r ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (ne_of_gt hr)
  have hquot := hG.div hden hden0
  unfold multimodeSwirl
  convert hquot using 1
  field_simp [ne_of_gt hr, Real.pi_ne_zero]

/-- Manuscript Eq. (94): a positive-radius stationary swirl point satisfies
2 pi r^2 omega_z = Gamma(r,t), and conversely. -/
theorem multimodeSwirl_deriv_zero_iff_extremum_relation {n : ℕ}
    {gammaLine : ℝ} {circ : Fin n → ℝ} {s r : ℝ}
    {beta : Fin n → ℝ}
    (hs : 0 < s) (hr : PuncturedRadius r) (hbeta : ∀ i, 0 < beta i) :
    deriv (multimodeSwirl gammaLine circ s beta) r = 0 ↔
      2 * Real.pi * r ^ 2 * multimodeDistributedVorticity circ s beta r =
        multimodeCirculationValue gammaLine circ s beta r := by
  rw [(multimodeSwirl_hasDerivAt hs hr hbeta).deriv]
  have hden : 2 * Real.pi * r ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)
      (pow_ne_zero 2 (ne_of_gt hr))
  constructor
  · intro h
    rcases div_eq_zero_iff.mp h with hn | hd
    · exact sub_eq_zero.mp hn
    · exact (hden hd).elim
  · intro h
    rw [sub_eq_zero.mpr h, zero_div]

end

end KiknadzeKrasnov
