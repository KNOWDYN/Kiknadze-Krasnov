import KiknadzeKrasnov.AngularMomentum

namespace KiknadzeKrasnov

noncomputable section

open intervalIntegral

/-- Linear inverse-scale residual h' + a h - 4ν. -/
def inverseScaleResidual (nu a h hDot : ℝ) : ℝ :=
  hDot + a * h - 4 * nu

/-- Derivative of h=1/β expressed in terms of β and β'. -/
def inverseScaleDotFromBeta (beta betaDot : ℝ) : ℝ :=
  -betaDot / beta ^ 2

/-- The nonlinear β equation is exactly equivalent pointwise to the linear h equation. -/
theorem betaScaleResidual_imp_inverseScaleResidual
    {nu a beta betaDot : ℝ}
    (hbeta : beta ≠ 0)
    (hscale : betaScaleResidual nu a beta betaDot = 0) :
    inverseScaleResidual nu a (inverseScale beta)
      (inverseScaleDotFromBeta beta betaDot) = 0 := by
  unfold betaScaleResidual at hscale
  unfold inverseScaleResidual inverseScaleDotFromBeta inverseScale
  field_simp [hbeta]
  nlinarith

/-- Time integral appearing in the exact inverse-scale solution. -/
def scaleIntegral (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ τ in 0..t, Real.exp (strainAccum a τ)

/-- Explicit integrating-factor solution for h=1/β. -/
def inverseScaleExact (nu h0 : ℝ) (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-strainAccum a t) * (h0 + 4 * nu * scaleIntegral a t)

/-- Explicit β formula reported in the manuscript. -/
def betaExact (nu beta0 : ℝ) (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (strainAccum a t) /
    (beta0⁻¹ + 4 * nu * scaleIntegral a t)

@[simp] theorem scaleIntegral_zero (a : ℝ → ℝ) : scaleIntegral a 0 = 0 := by
  simp [scaleIntegral]

@[simp] theorem inverseScaleExact_zero (nu h0 : ℝ) (a : ℝ → ℝ) :
    inverseScaleExact nu h0 a 0 = h0 := by
  simp [inverseScaleExact, strainAccum]

/-- The explicit h solution satisfies h' + a h = 4ν whenever the two FTC derivatives hold. -/
theorem inverseScaleExact_hasDerivAt
    {nu h0 t : ℝ} {a : ℝ → ℝ}
    (hA : HasDerivAt (strainAccum a) (a t) t)
    (hJ : HasDerivAt (scaleIntegral a) (Real.exp (strainAccum a t)) t) :
    HasDerivAt (inverseScaleExact nu h0 a)
      (-a t * inverseScaleExact nu h0 a t + 4 * nu) t := by
  unfold inverseScaleExact
  have hExp : HasDerivAt (fun x => Real.exp (-strainAccum a x))
      (Real.exp (-strainAccum a t) * (-a t)) t := by
    simpa using hA.neg.exp
  have hBracket : HasDerivAt
      (fun x => h0 + 4 * nu * scaleIntegral a x)
      (4 * nu * Real.exp (strainAccum a t)) t := by
    convert (hJ.const_mul (4 * nu)).const_add h0 using 1 <;> ring
  convert hExp.mul hBracket using 1 <;>
    simp [inverseScaleExact] <;>
    ring_nf <;>
    simp [Real.exp_neg] <;>
    field_simp [Real.exp_ne_zero (strainAccum a t)] <;>
    ring

/-- The exact β formula is reciprocal to the exact inverse-scale formula. -/
theorem betaExact_mul_inverseScaleExact
    {nu beta0 t : ℝ} {a : ℝ → ℝ}
    (hbeta0 : beta0 ≠ 0)
    (hden : beta0⁻¹ + 4 * nu * scaleIntegral a t ≠ 0) :
    betaExact nu beta0 a t *
      inverseScaleExact nu beta0⁻¹ a t = 1 := by
  unfold betaExact inverseScaleExact
  field_simp [hden, hbeta0, Real.exp_ne_zero (strainAccum a t)]
  rw [← Real.exp_add]
  simp

/-- Difference of two inverse-scale solutions with the same strain history. -/
theorem inverseScaleExact_sub
    (nu h0i h0j : ℝ) (a : ℝ → ℝ) (t : ℝ) :
    inverseScaleExact nu h0i a t - inverseScaleExact nu h0j a t
      = Real.exp (-strainAccum a t) * (h0i - h0j) := by
  unfold inverseScaleExact
  ring

/-- Ordering of inverse squared scales is preserved by the positive exponential factor. -/
theorem inverseScaleExact_order_preserved
    {nu h0i h0j : ℝ} {a : ℝ → ℝ} {t : ℝ}
    (hij : h0i ≤ h0j) :
    inverseScaleExact nu h0i a t ≤ inverseScaleExact nu h0j a t := by
  rw [sub_nonpos]
  rw [inverseScaleExact_sub]
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) (sub_nonpos.mpr hij)

/-- Strict ordering is likewise preserved. -/
theorem inverseScaleExact_strict_order_preserved
    {nu h0i h0j : ℝ} {a : ℝ → ℝ} {t : ℝ}
    (hij : h0i < h0j) :
    inverseScaleExact nu h0i a t < inverseScaleExact nu h0j a t := by
  rw [sub_pos] at hij ⊢
  rw [inverseScaleExact_sub]
  exact mul_pos (Real.exp_pos _) hij

end

end KiknadzeKrasnov
