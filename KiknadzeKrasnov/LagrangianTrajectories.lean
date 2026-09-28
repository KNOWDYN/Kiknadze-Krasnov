import KiknadzeKrasnov.MultimodeQualification
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace KiknadzeKrasnov

noncomputable section

open Set MeasureTheory intervalIntegral
open scoped BigOperators

/-! Exact Lagrangian trajectories, manuscript Eqs. (99)--(102). -/

/-- Integral appearing in the exact axial trajectory. -/
def weightedAxialIntegral (a b : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ tau in 0..t, Real.exp (-(strainAccum a tau)) * b tau

/-- Exact squared-radius trajectory from Eq. (100). -/
def radialSqTrajectory (a : ℝ → ℝ) (q r0 t : ℝ) : ℝ :=
  Real.exp (-(strainAccum a t)) *
    (r0 ^ 2 + 2 * q * scaleIntegral a t)

/-- Exact axial trajectory from Eq. (101). -/
def axialTrajectory (a b : ℝ → ℝ) (z0 t : ℝ) : ℝ :=
  Real.exp (strainAccum a t) *
    (z0 + weightedAxialIntegral a b t)

/-- Instantaneous angular rate from the finite-mode enclosed circulation. -/
def azimuthalRate {n : ℕ}
    (gammaLine : ℝ) (circ : Fin n → ℝ) (s : ℝ)
    (beta : Fin n → ℝ → ℝ) (r : ℝ → ℝ) (t : ℝ) : ℝ :=
  multimodeCirculationValue gammaLine circ s (fun i => beta i t) (r t) /
    (2 * Real.pi * (r t) ^ 2)

/-- Exact azimuthal time integral from Eq. (102). -/
def azimuthalTrajectory {n : ℕ}
    (gammaLine theta0 : ℝ) (circ : Fin n → ℝ) (s : ℝ)
    (beta : Fin n → ℝ → ℝ) (r : ℝ → ℝ) (t : ℝ) : ℝ :=
  theta0 + ∫ tau in 0..t, azimuthalRate gammaLine circ s beta r tau

/-- FTC derivative for accumulated strain. -/
theorem strainAccum_hasDerivAt
    {a : ℝ → ℝ} {t : ℝ}
    (hint : IntervalIntegrable a volume 0 t)
    (hmeas : StronglyMeasurableAtFilter a (nhds t) volume)
    (hcont : ContinuousAt a t) :
    HasDerivAt (strainAccum a) (a t) t :=
  intervalIntegral.integral_hasDerivAt_right hint hmeas hcont

/-- FTC derivative for the scale integral used in Eqs. (47),(100). -/
theorem scaleIntegral_hasDerivAt
    {a : ℝ → ℝ} {t : ℝ}
    (hint : IntervalIntegrable (fun tau => Real.exp (strainAccum a tau)) volume 0 t)
    (hmeas : StronglyMeasurableAtFilter
      (fun tau => Real.exp (strainAccum a tau)) (nhds t) volume)
    (hcont : ContinuousAt (fun tau => Real.exp (strainAccum a tau)) t) :
    HasDerivAt (scaleIntegral a) (Real.exp (strainAccum a t)) t :=
  intervalIntegral.integral_hasDerivAt_right hint hmeas hcont

/-- FTC derivative of the weighted axial primitive. -/
theorem weightedAxialIntegral_hasDerivAt
    {a b : ℝ → ℝ} {t : ℝ}
    (hint : IntervalIntegrable
      (fun tau => Real.exp (-(strainAccum a tau)) * b tau) volume 0 t)
    (hmeas : StronglyMeasurableAtFilter
      (fun tau => Real.exp (-(strainAccum a tau)) * b tau) (nhds t) volume)
    (hcont : ContinuousAt
      (fun tau => Real.exp (-(strainAccum a tau)) * b tau) t) :
    HasDerivAt (weightedAxialIntegral a b)
      (Real.exp (-(strainAccum a t)) * b t) t :=
  intervalIntegral.integral_hasDerivAt_right hint hmeas hcont

/-- Squaring the punctured radial particle equation gives (r^2)'=-a r^2+2q. -/
theorem radialSq_particle_hasDerivAt
    {r : ℝ → ℝ} {rDot a q t : ℝ}
    (hr : HasDerivAt r rDot t)
    (hrt : PuncturedRadius (r t))
    (hparticle : rDot = radialVelocity a q (r t)) :
    HasDerivAt (fun tau => (r tau) ^ 2)
      (-a * (r t) ^ 2 + 2 * q) t := by
  have hsq := hr.pow 2
  convert hsq using 1
  rw [hparticle]
  unfold radialVelocity
  field_simp [ne_of_gt hrt]
  ring

/-- Eq. (100) satisfies the squared radial particle law. -/
theorem radialSqTrajectory_hasDerivAt
    {a : ℝ → ℝ} {q r0 t : ℝ}
    (hA : HasDerivAt (strainAccum a) (a t) t)
    (hJ : HasDerivAt (scaleIntegral a)
      (Real.exp (strainAccum a t)) t) :
    HasDerivAt (radialSqTrajectory a q r0)
      (-a t * radialSqTrajectory a q r0 t + 2 * q) t := by
  have hexp := hA.neg.exp
  have hbracket :=
    (hasDerivAt_const t (r0 ^ 2)).add (hJ.const_mul (2 * q))
  have hprod := hexp.mul hbracket
  unfold radialSqTrajectory
  convert hprod using 1
  have hcancel :
      Real.exp (-(strainAccum a t)) * Real.exp (strainAccum a t) = 1 := by
    rw [← Real.exp_add]
    simp
  simp only [Pi.add_apply]
  let E := Real.exp (-(strainAccum a t))
  let F := Real.exp (strainAccum a t)
  let B := r0 ^ 2 + 2 * q * scaleIntegral a t
  have hEF : E * F = 1 := by
    simpa [E, F] using hcancel
  change -a t * (E * B) + 2 * q =
    E * (-a t) * B + E * (0 + 2 * q * F)
  calc
    -a t * (E * B) + 2 * q
        = E * (-a t) * B + 2 * q := by ring
    _ = E * (-a t) * B + 2 * q * (E * F) := by rw [hEF]; ring
    _ = E * (-a t) * B + E * (0 + 2 * q * F) := by ring

@[simp] theorem radialSqTrajectory_zero (a : ℝ → ℝ) (q r0 : ℝ) :
    radialSqTrajectory a q r0 0 = r0 ^ 2 := by
  simp [radialSqTrajectory, strainAccum]

/-- Positive radial branch corresponding to the exact squared-radius trajectory. -/
def radialTrajectory (a : ℝ → ℝ) (q r0 t : ℝ) : ℝ :=
  Real.sqrt (radialSqTrajectory a q r0 t)

/-- The positive radial trajectory squares to Eq. (100) whenever the latter is nonnegative. -/
theorem radialTrajectory_sq
    {a : ℝ → ℝ} {q r0 t : ℝ}
    (hY : 0 ≤ radialSqTrajectory a q r0 t) :
    radialTrajectory a q r0 t ^ 2 = radialSqTrajectory a q r0 t := by
  unfold radialTrajectory
  exact Real.sq_sqrt hY

/-- On intervals where Eq. (100) remains strictly positive, its positive
square-root satisfies the original punctured radial particle equation Eq. (99). -/
theorem radialTrajectory_hasDerivAt
    {a : ℝ → ℝ} {q r0 t : ℝ}
    (hA : HasDerivAt (strainAccum a) (a t) t)
    (hJ : HasDerivAt (scaleIntegral a)
      (Real.exp (strainAccum a t)) t)
    (hY : 0 < radialSqTrajectory a q r0 t) :
    HasDerivAt (radialTrajectory a q r0)
      (radialVelocity (a t) q (radialTrajectory a q r0 t)) t := by
  have hsq := radialSqTrajectory_hasDerivAt
    (a := a) (q := q) (r0 := r0) hA hJ
  have hsqrt :=
    (Real.hasDerivAt_sqrt (ne_of_gt hY)).comp t hsq
  have hsqrt' :
      HasDerivAt
        (fun tau => Real.sqrt (radialSqTrajectory a q r0 tau))
        ((1 / (2 * Real.sqrt (radialSqTrajectory a q r0 t))) *
          (-a t * radialSqTrajectory a q r0 t + 2 * q)) t := by
    simpa only [Function.comp_apply] using hsqrt
  have hrpos : 0 < radialTrajectory a q r0 t := by
    unfold radialTrajectory
    exact Real.sqrt_pos.2 hY
  have hsqeq := radialTrajectory_sq
    (a := a) (q := q) (r0 := r0) (t := t) hY.le
  unfold radialTrajectory
  convert hsqrt' using 1
  unfold radialVelocity
  have hsqrtpos : 0 < Real.sqrt (radialSqTrajectory a q r0 t) :=
    Real.sqrt_pos.2 hY
  field_simp [hsqrtpos.ne']
  nlinarith

@[simp] theorem radialTrajectory_zero
    {a : ℝ → ℝ} {q r0 : ℝ} (hr0 : 0 ≤ r0) :
    radialTrajectory a q r0 0 = r0 := by
  unfold radialTrajectory
  rw [radialSqTrajectory_zero]
  simpa [abs_of_nonneg hr0] using Real.sqrt_sq_eq_abs r0

/-- Eq. (101) satisfies z'=a z+b. -/
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
  unfold axialTrajectory axialVelocity
  convert hprod using 1
  have hcancel :
      Real.exp (strainAccum a t) * Real.exp (-(strainAccum a t)) = 1 := by
    rw [← Real.exp_add]
    simp
  simp only [Pi.add_apply]
  let E := Real.exp (strainAccum a t)
  let F := Real.exp (-(strainAccum a t))
  let B := z0 + weightedAxialIntegral a b t
  have hEF : E * F = 1 := by
    simpa [E, F] using hcancel
  change a t * (E * B) + b t =
    E * a t * B + E * (0 + F * b t)
  calc
    a t * (E * B) + b t = E * a t * B + b t := by ring
    _ = E * a t * B + (E * F) * b t := by rw [hEF]
    _ = E * a t * B + E * (0 + F * b t) := by ring

@[simp] theorem axialTrajectory_zero (a b : ℝ → ℝ) (z0 : ℝ) :
    axialTrajectory a b z0 0 = z0 := by
  simp [axialTrajectory, strainAccum, weightedAxialIntegral]

/-- On the punctured domain the angular rate is exactly u_theta/r. -/
theorem azimuthalRate_eq_multimodeSwirl_div_radius {n : ℕ}
    {gammaLine : ℝ} {circ : Fin n → ℝ} {s r : ℝ} {beta : Fin n → ℝ}
    (hr : PuncturedRadius r) :
    multimodeSwirl gammaLine circ s beta r / r =
      multimodeCirculationValue gammaLine circ s beta r /
        (2 * Real.pi * r ^ 2) := by
  unfold multimodeSwirl
  field_simp [ne_of_gt hr, Real.pi_ne_zero]

/-- Eq. (102) differentiates to the exact angular rate wherever the integrand is regular. -/
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
