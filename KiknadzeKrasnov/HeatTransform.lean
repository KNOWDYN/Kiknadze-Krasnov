import KiknadzeKrasnov.ClassicalProfiles

namespace KiknadzeKrasnov

noncomputable section

open scoped BigOperators

/-- Radial stretching factor `exp(A/2)` used in the regular `q=0` transform. -/
def heatStretch (A : ℝ) : ℝ := Real.exp (A / 2)

/-- Transformed radial coordinate `ξ=r exp(A/2)`. -/
def heatXi (A r : ℝ) : ℝ := r * heatStretch A

/-- Transformed diffusion time `τ=∫₀ᵗ exp(A(σ)) dσ`. -/
def heatTime (a : ℝ → ℝ) (t : ℝ) : ℝ := expStrainIntegral a t

/-- Radial heat-equation residual in transformed coordinates. -/
def radialHeatResidual
    (nu xi WTau WXi WXiXi : ℝ) : ℝ :=
  WTau - nu * (WXiXi + WXi / xi)

/-- Regular `q=0` vorticity-equation residual in physical coordinates. -/
def regularVorticityResidual
    (nu a r omega omegaT omegaR omegaRR : ℝ) : ℝ :=
  omegaT - (a / 2) * r * omegaR - a * omega -
    nu * (omegaRR + omegaR / r)

/-- Radial derivative of `ξ=r exp(A/2)` at fixed accumulated strain. -/
theorem heatXi_hasDerivAt_r (A r : ℝ) :
    HasDerivAt (heatXi A) (heatStretch A) r := by
  unfold heatXi
  simpa only [one_mul] using (hasDerivAt_id r).mul_const (heatStretch A)

/-- Time derivative of the radial stretching factor when `A'=a`. -/
theorem heatStretch_history_hasDerivAt
    {A : ℝ → ℝ} {a t : ℝ} (hA : HasDerivAt A a t) :
    HasDerivAt (fun tau => heatStretch (A tau))
      ((a / 2) * heatStretch (A t)) t := by
  unfold heatStretch
  have hhalf := hA.div_const 2
  have h := hhalf.exp
  convert h using 1 <;> ring

/-- At fixed physical radius, `ξ_t=(a/2)ξ`. -/
theorem heatXi_history_hasDerivAt
    {A : ℝ → ℝ} {a r t : ℝ} (hA : HasDerivAt A a t) :
    HasDerivAt (fun tau => heatXi (A tau) r)
      ((a / 2) * heatXi (A t) r) t := by
  have h := (heatStretch_history_hasDerivAt hA).const_mul r
  unfold heatXi
  convert h using 1 <;> ring

/-- The transformed time has derivative `exp(A)=exp(A/2)^2`. -/
theorem heatTime_hasDerivAt
    {a : ℝ → ℝ} {t : ℝ}
    (hint : IntervalIntegrable (fun tau => Real.exp (strainAccum a tau)) volume 0 t)
    (hmeas : StronglyMeasurableAtFilter
      (fun tau => Real.exp (strainAccum a tau)) (nhds t) volume)
    (hcont : ContinuousAt (fun tau => Real.exp (strainAccum a tau)) t) :
    HasDerivAt (heatTime a) ((heatStretch (strainAccum a t)) ^ 2) t := by
  have h := expStrainIntegral_hasDerivAt hint hmeas hcont
  unfold heatTime heatStretch
  convert h using 1
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- C026: exact algebraic cancellation behind the Kambe change of variables.
The inputs `W`, `WXi`, `WXiXi`, `WTau` denote the value and transformed
partial derivatives at `(ξ,τ)`; their chain-rule coefficients are certified
explicitly here. -/
theorem regularVorticityResidual_heatTransform
    {nu a A r W WTau WXi WXiXi : ℝ} (hr : r ≠ 0) :
    regularVorticityResidual nu a r
      ((heatStretch A) ^ 2 * W)
      ((heatStretch A) ^ 2 *
        (a * W + (a / 2) * heatXi A r * WXi) +
        (heatStretch A) ^ 4 * WTau)
      ((heatStretch A) ^ 3 * WXi)
      ((heatStretch A) ^ 4 * WXiXi) =
    (heatStretch A) ^ 4 *
      radialHeatResidual nu (heatXi A r) WTau WXi WXiXi := by
  unfold regularVorticityResidual radialHeatResidual heatXi heatStretch
  have hE : Real.exp (A / 2) ≠ 0 := (Real.exp_pos _).ne'
  field_simp [hr, hE]
  ring

/-- C026: a transformed radial-heat solution therefore gives zero regular
vorticity residual on the punctured radial domain. -/
theorem regularVorticityResidual_zero_of_heat
    {nu a A r W WTau WXi WXiXi : ℝ} (hr : r ≠ 0)
    (hheat : radialHeatResidual nu (heatXi A r) WTau WXi WXiXi = 0) :
    regularVorticityResidual nu a r
      ((heatStretch A) ^ 2 * W)
      ((heatStretch A) ^ 2 *
        (a * W + (a / 2) * heatXi A r * WXi) +
        (heatStretch A) ^ 4 * WTau)
      ((heatStretch A) ^ 3 * WXi)
      ((heatStretch A) ^ 4 * WXiXi) = 0 := by
  rw [regularVorticityResidual_heatTransform hr, hheat, mul_zero]

/-- Linearity of the transformed radial heat equation. -/
theorem radialHeatResidual_add
    {nu xi WTau₁ WXi₁ WXiXi₁ WTau₂ WXi₂ WXiXi₂ : ℝ} :
    radialHeatResidual nu xi
      (WTau₁ + WTau₂) (WXi₁ + WXi₂) (WXiXi₁ + WXiXi₂) =
    radialHeatResidual nu xi WTau₁ WXi₁ WXiXi₁ +
      radialHeatResidual nu xi WTau₂ WXi₂ WXiXi₂ := by
  unfold radialHeatResidual
  ring

/-- C026: finite superpositions remain exact for the transformed diffusion
equation, which is the formal content needed for finite Gaussian sums. -/
theorem radialHeatResidual_finset_sum {n : ℕ}
    (nu xi : ℝ) (WTau WXi WXiXi : Fin n → ℝ) :
    radialHeatResidual nu xi
      (∑ i, WTau i) (∑ i, WXi i) (∑ i, WXiXi i) =
      ∑ i, radialHeatResidual nu xi (WTau i) (WXi i) (WXiXi i) := by
  classical
  unfold radialHeatResidual
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul, div_eq_mul_inv]
  ring

end

end KiknadzeKrasnov
