import KiknadzeKrasnov.ScaleDynamics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace KiknadzeKrasnov

noncomputable section

/-- The derivative density `P_x(s,x)` of the regularised lower incomplete gamma profile. -/
def regLowerGammaDensity (s x : ℝ) : ℝ := gammaKernel s x / gammaFn s

/-- Pass-2's first-derivative theorem expressed with the named profile density. -/
theorem deriv_regLowerGamma_eq_density {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    deriv (regLowerGamma s) x = regLowerGammaDensity s x := by
  rw [deriv_regLowerGamma hs hx]
  unfold regLowerGammaDensity gammaKernel
  ring

/-- Derivative of the gamma kernel on the positive radial branch. -/
theorem gammaKernel_hasDerivAt_profile {s x : ℝ} (hx : 0 < x) :
    HasDerivAt (gammaKernel s)
      (((s - 1) / x - 1) * gammaKernel s x) x := by
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    convert (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x) using 1 <;> ring
  have hpow : HasDerivAt (fun y : ℝ => y ^ (s - 1))
      ((s - 1) * x ^ ((s - 1) - 1)) x :=
    Real.hasDerivAt_rpow_const (x := x) (p := s - 1) (Or.inl hx.ne')
  have hmul := hexp.mul hpow
  unfold gammaKernel
  convert hmul using 1
  rw [Real.rpow_sub_one hx.ne' (s - 1)]
  field_simp [hx.ne']
  ring

/-- The certified second-profile relation `P_xx=((s-1)/x-1)P_x`. -/
theorem regLowerGammaDensity_hasDerivAt {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    HasDerivAt (regLowerGammaDensity s)
      (((s - 1) / x - 1) * regLowerGammaDensity s x) x := by
  unfold regLowerGammaDensity
  convert (gammaKernel_hasDerivAt_profile (s := s) hx).div_const (gammaFn s) using 1
  field_simp [gammaFn_ne_zero hs]
  ring

/-- Algebraic gamma-profile ODE after `q=2ν(s-1)`. -/
theorem gammaProfile_ode_identity {nu q s x : ℝ}
    (hx : x ≠ 0) (hq : q = 2 * nu * (s - 1)) :
    2 * nu * x * (((s - 1) / x - 1) * regLowerGammaDensity s x) +
      (2 * nu * x - q) * regLowerGammaDensity s x = 0 := by
  rw [hq]
  field_simp [hx]
  ring

/-- The project shape definition supplies exactly the source/profile compatibility relation. -/
theorem gammaProfile_ode_for_shape (p : FluidParams) (q s x : ℝ)
    (hs : s = shape p q) (hx : x ≠ 0) :
    2 * p.nu * x * (((s - 1) / x - 1) * regLowerGammaDensity s x) +
      (2 * p.nu * x - q) * regLowerGammaDensity s x = 0 := by
  subst s
  exact gammaProfile_ode_identity hx (source_eq_two_nu_mul_shape_sub_one p q)

end

end KiknadzeKrasnov
