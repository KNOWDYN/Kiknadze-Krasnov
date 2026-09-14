import KiknadzeKrasnov.KKField
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace KiknadzeKrasnov

noncomputable section

open Set MeasureTheory intervalIntegral
open scoped BigOperators

/-- Integral appearing in the exact radial squared-radius trajectory. -/
def expStrainIntegral (a : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ tau in 0..t, Real.exp (strainAccum a tau)

/-- Integral appearing in the exact axial trajectory. -/
def weightedAxialIntegral (a b : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ tau in 0..t, Real.exp (-(strainAccum a tau)) * b tau

/-- Exact squared-radius trajectory from manuscript Eq. (100). -/
def radialSqTrajectory (a : ℝ → ℝ) (q r0 t : ℝ) : ℝ :=
  Real.exp (-(strainAccum a t)) *
    (r0 ^ 2 + 2 * q * expStrainIntegral a t)

/-- Exact axial trajectory from manuscript Eq. (101). -/
def axialTrajectory (a b : ℝ → ℝ) (z0 t : ℝ) : ℝ :=
  Real.exp (strainAccum a t) *
    (z0 + weightedAxialIntegral a b t)

/-- Instantaneous angular rate written from the enclosed finite-mode circulation. -/
def azimuthalRate {n : ℕ}
    (gammaLine : ℝ) (circ : Fin n → ℝ) (s : ℝ)
    (beta : Fin n → ℝ → ℝ) (r : ℝ → ℝ) (t : ℝ) : ℝ :=
  multimodeCirculationValue gammaLine circ s (fun i => beta i t) (r t) /
    (2 * Real.pi * (r t) ^ 2)

/-- Exact azimuthal time integral from manuscript Eq. (102). -/
def azimuthalTrajectory {n : ℕ}
    (gammaLine theta0 : ℝ) (circ : Fin n → ℝ) (s : ℝ)
    (beta : Fin n → ℝ → ℝ) (r : ℝ → ℝ) (t : ℝ) : ℝ :=
  theta0 + ∫ tau in 0..t, azimuthalRate gammaLine circ s beta r tau

/-- Fundamental derivative of the accumulated strain integral at a regular endpoint. -/
theorem strainAccum_hasDerivAt
    {a : ℝ → ℝ} {t : ℝ}
    (hint : IntervalIntegrable a volume 0 t)
    (hmeas : StronglyMeasurableAtFilter a (nhds t) volume)
    (hcont : ContinuousAt a t) :
    HasDerivAt (strainAccum a) (a t) t := by
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcont

/-- Fundamental derivative of the exponential-strain primitive. -/
theorem expStrainIntegral_hasDerivAt
    {a : ℝ → ℝ} {t : ℝ}
    (hint : IntervalIntegrable (fun tau => Real.exp (strainAccum a tau)) volume 0 t)
    (hmeas : StronglyMeasurableAtFilter
      (fun tau => Real.exp (strainAccum a tau)) (nhds t) volume)
    (hcont : ContinuousAt (fun tau => Real.exp (strainAccum a tau)) t) :
    HasDerivAt (expStrainIntegral a) (Real.exp (strainAccum a t)) t := by
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcont

/-- Fundamental derivative of the weighted axial primitive. -/
theorem weightedAxialIntegral_hasDerivAt
    {a b : ℝ → ℝ} {t : ℝ}
    (hint : IntervalIntegrable
      (fun tau => Real.exp (-(strainAccum a tau)) * b tau) volume 0 t)
    (hmeas : StronglyMeasurableAtFilter
      (fun tau => Real.exp (-(strainAccum a tau)) * b tau) (nhds t) volume)
    (hcont : ContinuousAt
      (fun tau => Real.exp (-(strainAccum a tau)) * b tau) t) :
    HasDerivAt (weightedAxialIntegral a b)
      (Real.exp (-(strainAccum a t)) * b t) t := by
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcont

/-- Squaring the radial particle equation gives `D(r²)/Dt=-a r²+2q`. -/
theorem radialSq_particle_hasDerivAt
    {r : ℝ → ℝ} {rDot a q t : ℝ}
    (hr : HasDerivAt r rDot t)
    (hrt : r t ≠ 0)
    (hparticle : rDot = radialVelocity a q (r t)) :
    HasDerivAt (fun tau => (r tau) ^ 2)
      (-a * (r t) ^ 2 + 2 * q) t := by
  have hsq := hr.pow 2
  rw [hparticle]
  unfold radialVelocity
  convert hsq using 1
  field_simp [hrt]
  ring

/-- The closed squared-radius formula satisfies the exact radial particle equation. -/
theorem radialSqTrajectory_hasDerivAt
    {a : ℝ → ℝ} {q r0 t : ℝ}
    (hA : HasDerivAt (strainAccum a) (a t) t)
    (hJ : HasDerivAt (expStrainIntegral a)
      (Real.exp (strainAccum a t)) t) :
    HasDerivAt (radialSqTrajectory a q r0)
      (-a t * radialSqTrajectory a q r0 t + 2 * q) t := by
  have hnegA := hA.neg
  have hexp := hnegA.exp
  have hbracket :=
    (hasDerivAt_const t (r0 ^ 2)).add (hJ.const_mul (2 * q))
  have hprod := hexp.mul hbracket
  unfold radialSqTrajectory at *
  convert hprod using 1
  · funext tau
    ring
  · have hcancel :
      Real.exp (-(strainAccum a t)) * Real.exp (strainAccum a t) = 1 := by
      rw [← Real.exp_add]
      simp
    rw [hcancel]
    ring

@[simp] theorem radialSqTrajectory_zero (a : ℝ → ℝ) (q r0 : ℝ) :
    radialSqTrajectory a q r0 0 = r0 ^ 2 := by
  simp [radialSqTrajectory, strainAccum, expStrainIntegral]

/-- The closed axial formula satisfies `z'=a z+b`. -/
theorem axialTrajectory_hasDerivAt
    {a b : ℝ → ℝ} {z0 t : ℝ}
    (hA : HasDerivAt (strainAccum a) (a t) t)
    (hK : HasDerivAt (weightedAxialIntegral a b)
      (Real.exp (-(strainAccum a t)) * b t) t) :
    HasDerivAt (axialTrajectory a b z0)
      (axialVelocity (a t) (b t) (axialTrajectory a b z0 t)) t := by
  have hexp := hA.exp
  have hbracket := (hasDerivAt_const t z0).add hK
  have hprod := hexp.mul hbracket
  unfold axialTrajectory axialVelocity at *
  convert hprod using 1
  · funext tau
    ring
  · have hcancel :
      Real.exp (strainAccum a t) * Real.exp (-(strainAccum a t)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      a t * Real.exp (strainAccum a t) *
          (z0 + weightedAxialIntegral a b t) +
          Real.exp (strainAccum a t) *
            (Real.exp (-(strainAccum a t)) * b t)
          = a t * (Real.exp (strainAccum a t) *
              (z0 + weightedAxialIntegral a b t)) +
              (Real.exp (strainAccum a t) *
                Real.exp (-(strainAccum a t))) * b t := by ring
      _ = a t * (Real.exp (strainAccum a t) *
              (z0 + weightedAxialIntegral a b t)) + b t := by rw [hcancel]; ring

@[simp] theorem axialTrajectory_zero (a b : ℝ → ℝ) (z0 : ℝ) :
    axialTrajectory a b z0 0 = z0 := by
  simp [axialTrajectory, strainAccum, weightedAxialIntegral]

/-- On the punctured domain the angular rate is exactly `u_theta/r`. -/
theorem azimuthalRate_eq_multimodeSwirl_div_radius {n : ℕ}
    {gammaLine : ℝ} {circ : Fin n → ℝ} {s r : ℝ} {beta : Fin n → ℝ}
    (hr : r ≠ 0) :
    multimodeSwirl gammaLine circ s beta r / r =
      multimodeCirculationValue gammaLine circ s beta r /
        (2 * Real.pi * r ^ 2) := by
  unfold multimodeSwirl
  field_simp [hr, Real.pi_ne_zero]
  ring

/-- The azimuthal integral differentiates to the exact angular rate at a regular endpoint. -/
theorem azimuthalTrajectory_hasDerivAt {n : ℕ}
    {gammaLine theta0 s t : ℝ} {circ : Fin n → ℝ}
    {beta : Fin n → ℝ → ℝ} {r : ℝ → ℝ}
    (hint : IntervalIntegrable
      (azimuthalRate gammaLine circ s beta r) volume 0 t)
    (hmeas : StronglyMeasurableAtFilter
      (azimuthalRate gammaLine circ s beta r) (nhds t) volume)
    (hcont : ContinuousAt (azimuthalRate gammaLine circ s beta r) t) :
    HasDerivAt (azimuthalTrajectory gammaLine theta0 circ s beta r)
      (azimuthalRate gammaLine circ s beta r t) t := by
  unfold azimuthalTrajectory
  exact (intervalIntegral.integral_hasDerivAt_right hint hmeas hcont).const_add theta0

@[simp] theorem azimuthalTrajectory_zero {n : ℕ}
    (gammaLine theta0 : ℝ) (circ : Fin n → ℝ) (s : ℝ)
    (beta : Fin n → ℝ → ℝ) (r : ℝ → ℝ) :
    azimuthalTrajectory gammaLine theta0 circ s beta r 0 = theta0 := by
  simp [azimuthalTrajectory]

end

end KiknadzeKrasnov
