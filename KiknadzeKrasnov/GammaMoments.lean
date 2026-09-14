import KiknadzeKrasnov.VorticityAnalysis
import Mathlib.MeasureTheory.Integral.Gamma

namespace KiknadzeKrasnov

noncomputable section

open Set MeasureTheory

/-- Normalised raw moment of the scaled gamma circulation density. -/
def scaledGammaMoment (s : ℝ) (n : ℕ) : ℝ :=
  (∫ x in Ioi (0 : ℝ), x ^ (s + (n : ℝ) - 1) * Real.exp (-x)) / gammaFn s

/-- Exact scaled gamma-moment identity. -/
theorem scaledGammaMoment_eq_gamma_ratio
    {s : ℝ} (n : ℕ) (hs : 0 < s) :
    scaledGammaMoment s n = gammaFn (s + n) / gammaFn s := by
  have ha : 0 < s + (n : ℝ) := by positivity
  have h := _root_.integral_rpow_mul_exp_neg_mul_Ioi
    (a := s + (n : ℝ)) (r := 1) ha one_pos
  have hint :
      (∫ x in Ioi (0 : ℝ), x ^ (s + (n : ℝ) - 1) * Real.exp (-x)) =
        gammaFn (s + n) := by
    simpa [gammaFn] using h
  unfold scaledGammaMoment
  rw [hint]

/-- Even radial moment after the exact change of variables `x=βr²`. -/
def radialEvenMoment (s beta : ℝ) (n : ℕ) : ℝ :=
  (beta ^ n)⁻¹ * scaledGammaMoment s n

/-- Manuscript Eq. (83): `⟨r^(2n)⟩=β^(-n) Γ(s+n)/Γ(s)`. -/
theorem radialEvenMoment_eq
    {s beta : ℝ} (n : ℕ) (hs : 0 < s) :
    radialEvenMoment s beta n =
      (beta ^ n)⁻¹ * (gammaFn (s + n) / gammaFn s) := by
  unfold radialEvenMoment
  rw [scaledGammaMoment_eq_gamma_ratio n hs]

/-- Real gamma recurrence in the project's collision-free notation. -/
theorem gammaFn_add_one {s : ℝ} (hs : 0 < s) :
    gammaFn (s + 1) = s * gammaFn s := by
  simpa [gammaFn] using Real.Gamma_add_one s hs.ne'

/-- Manuscript Eq. (84), first identity: `⟨r²⟩=s/β`. -/
theorem radialSecondMoment_eq
    {s beta : ℝ} (hs : 0 < s) (hbeta : beta ≠ 0) :
    radialEvenMoment s beta 1 = s / beta := by
  rw [radialEvenMoment_eq 1 hs]
  norm_num
  rw [gammaFn_add_one hs]
  field_simp [hbeta, gammaFn_ne_zero hs]

/-- Closed fourth radial moment used to derive the variance of `r²`. -/
theorem radialFourthMoment_eq
    {s beta : ℝ} (hs : 0 < s) (hbeta : beta ≠ 0) :
    radialEvenMoment s beta 2 = s * (s + 1) / beta ^ 2 := by
  rw [radialEvenMoment_eq 2 hs]
  have hs1 : 0 < s + 1 := by linarith
  have hrec1 := gammaFn_add_one hs
  have hrec2 := gammaFn_add_one hs1
  have harg : s + (2 : ℕ) = (s + 1) + 1 := by norm_num; ring
  rw [harg, hrec2, hrec1]
  field_simp [hbeta, gammaFn_ne_zero hs]
  ring

/-- Variance of the squared radius under the normalised distributed-circulation density. -/
def radialSquaredVariance (s beta : ℝ) : ℝ :=
  radialEvenMoment s beta 2 - (radialEvenMoment s beta 1) ^ 2

/-- Manuscript Eq. (84), second identity: `Var(r²)=s/β²`. -/
theorem radialSquaredVariance_eq
    {s beta : ℝ} (hs : 0 < s) (hbeta : beta ≠ 0) :
    radialSquaredVariance s beta = s / beta ^ 2 := by
  unfold radialSquaredVariance
  rw [radialFourthMoment_eq hs hbeta, radialSecondMoment_eq hs hbeta]
  field_simp [hbeta]
  ring

/-- RMS radius associated with the distributed-circulation density. -/
def rmsRadius (s beta : ℝ) : ℝ :=
  Real.sqrt (radialEvenMoment s beta 1)

/-- Manuscript Eq. (85): `r_rms=sqrt(s/β)` on the positive-scale branch. -/
theorem rmsRadius_eq
    {s beta : ℝ} (hs : 0 < s) (hbeta : 0 < beta) :
    rmsRadius s beta = Real.sqrt (s / beta) := by
  unfold rmsRadius
  rw [radialSecondMoment_eq hs hbeta.ne']

/-- Radius corresponding to a prescribed positive scaled squared radius. -/
def scaledFractionRadius (beta x : ℝ) : ℝ :=
  Real.sqrt (x / beta)

/-- The characteristic-radius construction maps back exactly to the prescribed scaled radius. -/
theorem scaledX_scaledFractionRadius
    {beta x : ℝ} (hbeta : 0 < beta) (hx : 0 ≤ x) :
    scaledX beta (scaledFractionRadius beta x) = x := by
  unfold scaledX scaledFractionRadius
  rw [Real.sq_sqrt (div_nonneg hx hbeta.le)]
  field_simp [hbeta.ne']

/-- If `P(s,xp)=p`, the corresponding physical radius encloses fraction `p` of a mode's circulation. -/
theorem distributedCirculation_at_fractionRadius
    {circ s beta xp p : ℝ}
    (hbeta : 0 < beta) (hxp : 0 ≤ xp)
    (hp : regLowerGamma s xp = p) :
    distributedCirculation circ s beta (scaledFractionRadius beta xp) = circ * p := by
  unfold distributedCirculation
  rw [scaledX_scaledFractionRadius hbeta hxp, hp]

/-- The peak-vorticity cylinder encloses the source fraction `P(s,s-1)`. -/
theorem distributedCirculation_at_vorticityPeak
    {circ s beta : ℝ} (hs : 1 < s) (hbeta : 0 < beta) :
    distributedCirculation circ s beta (vorticityPeakRadius s beta) =
      circ * regLowerGamma s (s - 1) := by
  unfold distributedCirculation
  rw [scaledX_vorticityPeakRadius hs hbeta]

end

end KiknadzeKrasnov
