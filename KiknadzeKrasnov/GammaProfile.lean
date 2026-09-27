import KiknadzeKrasnov.AngularMomentum
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace KiknadzeKrasnov

noncomputable section

/-!
Pass 4 analytic profile layer. These lemmas certify the regularised
incomplete-gamma derivatives used in the manuscript's one-mode vorticity and
material-circulation arguments.
-/

/-- The derivative density P_x(s,x) of the regularised lower incomplete gamma profile. -/
def regLowerGammaDensity (s x : ℝ) : ℝ := gammaKernel s x / gammaFn s

/-- Manuscript Eq. (118): P_x=x^(s-1)e^{-x}/Gamma(s) on x>0. -/
theorem deriv_regLowerGamma_eq_density {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    deriv (regLowerGamma s) x = regLowerGammaDensity s x := by
  rw [deriv_regLowerGamma hs hx]
  unfold regLowerGammaDensity gammaKernel
  ring

/-- Derivative of the gamma kernel on the positive scaled-radius branch. -/
theorem gammaKernel_hasDerivAt_profile {s x : ℝ} (hx : 0 < x) :
    HasDerivAt (gammaKernel s)
      (((s - 1) / x - 1) * gammaKernel s x) x := by
  have hcomp := (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    convert hcomp using 1
    · funext y
      simp
    · ring
  have hpow : HasDerivAt (fun y : ℝ => y ^ (s - 1))
      ((s - 1) * x ^ ((s - 1) - 1)) x :=
    Real.hasDerivAt_rpow_const (x := x) (p := s - 1) (Or.inl hx.ne')
  have hmul := hexp.mul hpow
  unfold gammaKernel
  convert hmul using 1
  rw [Real.rpow_sub_one hx.ne' (s - 1)]
  field_simp [hx.ne']; ring

/-- Supplementary Eq. (14): P_xx=((s-1)/x-1)P_x on x>0. -/
theorem regLowerGammaDensity_hasDerivAt {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    HasDerivAt (regLowerGammaDensity s)
      (((s - 1) / x - 1) * regLowerGammaDensity s x) x := by
  unfold regLowerGammaDensity
  convert (gammaKernel_hasDerivAt_profile (s := s) hx).div_const (gammaFn s) using 1
  field_simp [gammaFn_ne_zero hs]

/-- Denominator-free second-profile relation used in the residual and circulation audits. -/
theorem regLowerGammaDensity_second_relation
    {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    x * deriv (regLowerGammaDensity s) x =
      (s - 1 - x) * regLowerGammaDensity s x := by
  rw [(regLowerGammaDensity_hasDerivAt hs hx).deriv]
  field_simp [hx.ne']

end

end KiknadzeKrasnov
