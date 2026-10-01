import KiknadzeKrasnov.PrincipalSurface

namespace KiknadzeKrasnov

noncomputable section

open intervalIntegral

/-!
Exact radial-scale dynamics used by the Navier--Stokes solution certificate.
This formalises manuscript Eqs. (44)--(49).  FiniteTimeCriteria and FiniteTimeAsymptotics certify the terminal classification.
-/

/-- Linear inverse-scale residual h' + a h - 4 nu. -/
def inverseScaleResidual (nu a h hDot : ℝ) : ℝ :=
  hDot + a * h - 4 * nu

/-- Derivative of h=1/beta expressed in terms of beta and beta'. -/
def inverseScaleDotFromBeta (beta betaDot : ℝ) : ℝ :=
  -betaDot / beta ^ 2

/-- Eq. (45): the nonlinear beta equation implies the linear inverse-scale equation. -/
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
  ∫ tau in 0..t, Real.exp (strainAccum a tau)

/-- Eq. (47): explicit integrating-factor solution for h=1/beta. -/
def inverseScaleExact (nu h0 : ℝ) (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-strainAccum a t) * (h0 + 4 * nu * scaleIntegral a t)

/-- Eq. (48): explicit beta formula. -/
def betaExact (nu beta0 : ℝ) (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (strainAccum a t) /
    (beta0⁻¹ + 4 * nu * scaleIntegral a t)

@[simp] theorem scaleIntegral_zero (a : ℝ → ℝ) : scaleIntegral a 0 = 0 := by
  simp [scaleIntegral]

@[simp] theorem inverseScaleExact_zero (nu h0 : ℝ) (a : ℝ → ℝ) :
    inverseScaleExact nu h0 a 0 = h0 := by
  simp [inverseScaleExact, strainAccum]

@[simp] theorem betaExact_zero (nu beta0 : ℝ) (a : ℝ → ℝ) :
    betaExact nu beta0 a 0 = beta0 := by
  simp [betaExact, strainAccum]

/-- Eq. (47) differentiates back to h' + a h = 4 nu. -/
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
    simpa [add_comm] using (hJ.const_mul (4 * nu)).const_add h0
  have he :
      Real.exp (-strainAccum a t) * Real.exp (strainAccum a t) = 1 := by
    rw [← Real.exp_add]
    simp
  have heTerm :
      Real.exp (-strainAccum a t) * nu * Real.exp (strainAccum a t) * 4
        = nu * 4 := by
    calc
      Real.exp (-strainAccum a t) * nu * Real.exp (strainAccum a t) * 4
          = nu * 4 *
              (Real.exp (-strainAccum a t) * Real.exp (strainAccum a t)) := by
              ring
      _ = nu * 4 := by rw [he]; ring
  convert hExp.mul hBracket using 1
  · ring_nf
    rw [heTerm]

/-- The exact inverse-scale solution satisfies Eq. (45) pointwise. -/
theorem inverseScaleExact_residual_zero
    {nu h0 t : ℝ} {a : ℝ → ℝ}
    (hA : HasDerivAt (strainAccum a) (a t) t)
    (hJ : HasDerivAt (scaleIntegral a) (Real.exp (strainAccum a t)) t) :
    inverseScaleResidual nu (a t) (inverseScaleExact nu h0 a t)
      (deriv (inverseScaleExact nu h0 a) t) = 0 := by
  rw [(inverseScaleExact_hasDerivAt hA hJ).deriv]
  unfold inverseScaleResidual
  ring

/-- Eq. (48) differentiates back to the nonlinear scale equation. -/
theorem betaExact_hasDerivAt
    {nu beta0 t : ℝ} {a : ℝ → ℝ}
    (hA : HasDerivAt (strainAccum a) (a t) t)
    (hJ : HasDerivAt (scaleIntegral a) (Real.exp (strainAccum a t)) t)
    (hden : beta0⁻¹ + 4 * nu * scaleIntegral a t ≠ 0) :
    HasDerivAt (betaExact nu beta0 a)
      (a t * betaExact nu beta0 a t
        - 4 * nu * (betaExact nu beta0 a t) ^ 2) t := by
  have hnum : HasDerivAt (fun x => Real.exp (strainAccum a x))
      (Real.exp (strainAccum a t) * a t) t := hA.exp
  have hdenDeriv : HasDerivAt
      (fun x => beta0⁻¹ + 4 * nu * scaleIntegral a x)
      (4 * nu * Real.exp (strainAccum a t)) t := by
    simpa [add_comm] using (hJ.const_mul (4 * nu)).const_add beta0⁻¹
  have hquot := hnum.div hdenDeriv hden
  unfold betaExact
  convert hquot using 1
  field_simp [hden]

/-- The explicit beta solution satisfies Eq. (32) pointwise. -/
theorem betaExact_scaleResidual_zero
    {nu beta0 t : ℝ} {a : ℝ → ℝ}
    (hA : HasDerivAt (strainAccum a) (a t) t)
    (hJ : HasDerivAt (scaleIntegral a) (Real.exp (strainAccum a t)) t)
    (hden : beta0⁻¹ + 4 * nu * scaleIntegral a t ≠ 0) :
    betaScaleResidual nu (a t) (betaExact nu beta0 a t)
      (deriv (betaExact nu beta0 a) t) = 0 := by
  rw [(betaExact_hasDerivAt hA hJ hden).deriv]
  unfold betaScaleResidual
  ring

/-- The exact beta formula is reciprocal to the exact inverse-scale formula. -/
theorem betaExact_mul_inverseScaleExact
    {nu beta0 t : ℝ} {a : ℝ → ℝ}
    (hden : beta0⁻¹ + 4 * nu * scaleIntegral a t ≠ 0) :
    betaExact nu beta0 a t *
      inverseScaleExact nu beta0⁻¹ a t = 1 := by
  unfold betaExact inverseScaleExact
  rw [div_eq_mul_inv]
  calc
    Real.exp (strainAccum a t)
          * (beta0⁻¹ + 4 * nu * scaleIntegral a t)⁻¹
          * (Real.exp (-strainAccum a t)
            * (beta0⁻¹ + 4 * nu * scaleIntegral a t))
        = (Real.exp (strainAccum a t) * Real.exp (-strainAccum a t))
          * ((beta0⁻¹ + 4 * nu * scaleIntegral a t)⁻¹
            * (beta0⁻¹ + 4 * nu * scaleIntegral a t)) := by ring
    _ = 1 := by
      rw [inv_mul_cancel₀ hden]
      rw [← Real.exp_add]
      simp

/-- Eq. (49): exact inverse-scale separation for two modes under the same strain. -/
theorem inverseScaleExact_sub
    (nu h0i h0j : ℝ) (a : ℝ → ℝ) (t : ℝ) :
    inverseScaleExact nu h0i a t - inverseScaleExact nu h0j a t
      = Real.exp (-strainAccum a t) * (h0i - h0j) := by
  unfold inverseScaleExact
  ring

/-- Ordering of inverse squared scales is preserved. -/
theorem inverseScaleExact_order_preserved
    {nu h0i h0j : ℝ} {a : ℝ → ℝ} {t : ℝ}
    (hij : h0i ≤ h0j) :
    inverseScaleExact nu h0i a t ≤ inverseScaleExact nu h0j a t := by
  unfold inverseScaleExact
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  linarith

/-- Strict ordering of inverse squared scales is preserved. -/
theorem inverseScaleExact_strict_order_preserved
    {nu h0i h0j : ℝ} {a : ℝ → ℝ} {t : ℝ}
    (hij : h0i < h0j) :
    inverseScaleExact nu h0i a t < inverseScaleExact nu h0j a t := by
  unfold inverseScaleExact
  apply mul_lt_mul_of_pos_left _ (Real.exp_pos _)
  linarith

end

end KiknadzeKrasnov
