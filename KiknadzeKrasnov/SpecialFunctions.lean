import KiknadzeKrasnov.Domains
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace KiknadzeKrasnov

noncomputable section

open Set MeasureTheory intervalIntegral
open scoped Topology

/-- Euler gamma function, given a collision-free project name. -/
def gammaFn (s : ℝ) : ℝ := Real.Gamma s

/-- Real gamma integrand `exp(-x) x^(s-1)`. -/
def gammaKernel (s x : ℝ) : ℝ := Real.exp (-x) * x ^ (s - 1)

/-- Lower incomplete gamma function, defined directly by its real interval integral. -/
def lowerGamma (s x : ℝ) : ℝ := ∫ ξ in 0..x, gammaKernel s ξ

/-- Regularised lower incomplete gamma `P(s,x) = γ(s,x)/Γ(s)`. -/
def regLowerGamma (s x : ℝ) : ℝ := lowerGamma s x / gammaFn s

/-- Complementary representation used when the paper writes the upper incomplete gamma. -/
def upperGammaComplement (s x : ℝ) : ℝ := gammaFn s - lowerGamma s x

@[simp] theorem gammaFn_pos {s : ℝ} (hs : 0 < s) : 0 < gammaFn s := by
  exact Real.Gamma_pos_of_pos hs

@[simp] theorem gammaFn_ne_zero {s : ℝ} (hs : 0 < s) : gammaFn s ≠ 0 :=
  ne_of_gt (gammaFn_pos hs)

@[simp] theorem lowerGamma_zero (s : ℝ) : lowerGamma s 0 = 0 := by
  simp [lowerGamma]

@[simp] theorem regLowerGamma_zero (s : ℝ) : regLowerGamma s 0 = 0 := by
  simp [regLowerGamma]

@[simp] theorem lower_add_upperGammaComplement (s x : ℝ) :
    lowerGamma s x + upperGammaComplement s x = gammaFn s := by
  simp [upperGammaComplement]

/-- On a positive argument, the gamma kernel is continuous. -/
theorem gammaKernel_continuousAt {s x : ℝ} (hx : 0 < x) :
    ContinuousAt (gammaKernel s) x := by
  unfold gammaKernel
  apply ContinuousAt.mul
  · fun_prop
  · exact Real.continuousAt_rpow_const x (s - 1) (Or.inl hx.ne')

/-- For `s>0`, the real gamma kernel is interval-integrable from `0` to every positive `x`. -/
theorem gammaKernel_intervalIntegrable {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    IntervalIntegrable (gammaKernel s) volume 0 x := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
  exact (Real.GammaIntegral_convergent hs).mono_set Ioc_subset_Ioi_self

/-- Fundamental derivative identity for the lower incomplete gamma function. -/
theorem lowerGamma_hasDerivAt {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    HasDerivAt (lowerGamma s) (gammaKernel s x) x := by
  have hcont : ContinuousAt (gammaKernel s) x := gammaKernel_continuousAt hx
  have hmeas : StronglyMeasurableAtFilter (gammaKernel s) (𝓝 x) volume := by
    exact ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (fun y hy => gammaKernel_continuousAt hy) x hx
  exact intervalIntegral.integral_hasDerivAt_right
    (gammaKernel_intervalIntegrable hs hx.le) hmeas hcont

/-- Fundamental derivative identity for the regularised lower incomplete gamma function. -/
theorem regLowerGamma_hasDerivAt {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    HasDerivAt (regLowerGamma s) (gammaKernel s x / gammaFn s) x := by
  unfold regLowerGamma
  exact (lowerGamma_hasDerivAt hs hx).div_const (gammaFn s)

/-- The derivative is exactly the density used throughout the KK construction. -/
theorem deriv_regLowerGamma {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    deriv (regLowerGamma s) x = x ^ (s - 1) * Real.exp (-x) / gammaFn s := by
  rw [(regLowerGamma_hasDerivAt hs hx).deriv]
  simp only [gammaKernel]
  ring

/-- Closed form for the first derivative of the regularised lower incomplete gamma. -/
def regLowerGammaPrime (s x : ℝ) : ℝ :=
  gammaKernel s x / gammaFn s

/-- Closed form for the second derivative used in the KK profile equation. -/
def regLowerGammaSecond (s x : ℝ) : ℝ :=
  ((s - 1) * Real.exp (-x) * x ^ (s - 2) -
      Real.exp (-x) * x ^ (s - 1)) / gammaFn s

/-- The first derivative wrapper agrees with the derivative already certified above. -/
theorem regLowerGamma_hasDerivAt_prime {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    HasDerivAt (regLowerGamma s) (regLowerGammaPrime s x) x := by
  simpa [regLowerGammaPrime] using regLowerGamma_hasDerivAt hs hx

/-- The gamma-density derivative gives the second radial-profile derivative. -/
theorem regLowerGammaPrime_hasDerivAt {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    HasDerivAt (regLowerGammaPrime s) (regLowerGammaSecond s x) x := by
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    convert ((hasDerivAt_id x).neg.exp) using 1 <;> ring
  have hpow : HasDerivAt (fun y : ℝ => y ^ (s - 1))
      ((s - 1) * x ^ (s - 2)) x := by
    convert Real.hasDerivAt_rpow_const (x := x) (p := s - 1) (Or.inl hx.ne') using 1 <;> ring
  have hprod := hexp.mul hpow
  convert hprod.div_const (gammaFn s) using 1
  · ext y
    rfl
  · unfold regLowerGammaSecond
    ring

/-- The incomplete-gamma profile satisfies the separated KK profile ODE. -/
theorem regLowerGamma_profile_ode {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    x * regLowerGammaSecond s x + (x - (s - 1)) * regLowerGammaPrime s x = 0 := by
  unfold regLowerGammaSecond regLowerGammaPrime gammaKernel
  rw [show s - 2 = (s - 1) - 1 by ring]
  rw [Real.rpow_sub_one hx.ne' (s - 1)]
  field_simp [gammaFn_ne_zero hs, hx.ne']
  ring

end

end KiknadzeKrasnov
