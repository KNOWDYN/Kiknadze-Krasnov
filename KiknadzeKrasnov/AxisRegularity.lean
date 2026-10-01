import KiknadzeKrasnov.ClassicalProfiles
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace KiknadzeKrasnov

noncomputable section

open Filter Set
open scoped Topology

/-!
Regular-axis consequences from manuscript Eqs. (60)--(63).  Because division
by zero is totalised in Lean, axis regularity is expressed by finite one-sided
limits from the physical domain r>0 rather than by evaluating 1/r terms at
r=0.
-/

/-- A finite radial-velocity limit at the axis rules out the q/r line source
or sink. -/
theorem radialVelocity_finite_axis_limit_forces_source_zero
    {a q ur0 : ℝ}
    (hreg : Tendsto (radialVelocity a q) (𝓝[>] 0) (𝓝 ur0)) :
    q = 0 := by
  have hid : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ)) tendsto_id
  have hprod :
      Tendsto (fun r : ℝ => r * radialVelocity a q r)
        (𝓝[>] 0) (𝓝 0) := by
    simpa using hid.mul hreg
  have hpoly :
      Tendsto (fun r : ℝ => -(a / 2) * r ^ 2 + q)
        (𝓝[>] 0) (𝓝 q) := by
    have hfull :
        Tendsto (fun r : ℝ => -(a / 2) * r ^ 2 + q)
          (𝓝 0) (𝓝 q) := by
      have hc : ContinuousAt (fun r : ℝ => -(a / 2) * r ^ 2 + q) 0 := by fun_prop
      simpa using hc.tendsto
    exact tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ)) hfull
  have heq :
      (fun r : ℝ => r * radialVelocity a q r) =ᶠ[𝓝[>] 0]
        (fun r : ℝ => -(a / 2) * r ^ 2 + q) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    unfold radialVelocity
    field_simp [hr0]
  have hq : Tendsto (fun r : ℝ => r * radialVelocity a q r)
      (𝓝[>] 0) (𝓝 q) := hpoly.congr' heq.symm
  exact tendsto_nhds_unique hq hprod

/-- The regular one-mode distributed angular momentum tends to zero at the
axis. -/
theorem distributedAngularMomentum_one_tendsto_zero
    {circ beta : ℝ} (hbeta : 0 ≤ beta) :
    Tendsto (distributedAngularMomentum circ 1 beta)
      (𝓝[>] 0) (𝓝 0) := by
  have hxfull :
      Tendsto (fun r : ℝ => scaledX beta r) (𝓝 0) (𝓝 0) := by
    unfold scaledX
    have hc : ContinuousAt (fun r : ℝ => beta * r ^ 2) 0 := by fun_prop
    simpa using hc.tendsto
  have hx : Tendsto (fun r : ℝ => scaledX beta r)
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ)) hxfull
  have hP :
      Tendsto (fun r : ℝ => regLowerGamma 1 (scaledX beta r))
        (𝓝[>] 0) (𝓝 0) := by
    have hformula :
        (fun r : ℝ => regLowerGamma 1 (scaledX beta r)) =ᶠ[𝓝[>] 0]
          (fun r : ℝ => 1 - Real.exp (-(scaledX beta r))) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [regLowerGamma_one]
      unfold scaledX
      exact mul_nonneg hbeta (sq_nonneg r)
    have hexp :
        Tendsto (fun r : ℝ => 1 - Real.exp (-(scaledX beta r)))
          (𝓝[>] 0) (𝓝 0) := by
      have he := Real.continuous_exp.continuousAt.tendsto.comp hx.neg
      simpa using he.const_sub (1 : ℝ)
    exact hexp.congr' hformula.symm
  unfold distributedAngularMomentum
  simpa using hP.const_mul (circ / (2 * Real.pi))

/-- A finite limit of the actual regular one-mode swirl at the axis rules out
an independent central line circulation. -/
theorem oneModeSwirlWithLine_finite_axis_limit_forces_line_zero
    {gammaLine circ beta u0 : ℝ}
    (hbeta : 0 ≤ beta)
    (hreg : Tendsto (oneModeSwirlWithLine gammaLine circ 1 beta)
      (𝓝[>] 0) (𝓝 u0)) :
    gammaLine = 0 := by
  have hid : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ)) tendsto_id
  have hru :
      Tendsto
        (fun r : ℝ => r * oneModeSwirlWithLine gammaLine circ 1 beta r)
        (𝓝[>] 0) (𝓝 0) := by
    simpa using hid.mul hreg
  have hdist := distributedAngularMomentum_one_tendsto_zero
    (circ := circ) hbeta
  have hL :
      Tendsto
        (fun r : ℝ =>
          gammaLine / (2 * Real.pi) +
            distributedAngularMomentum circ 1 beta r)
        (𝓝[>] 0) (𝓝 (gammaLine / (2 * Real.pi))) := by
    simpa using tendsto_const_nhds.add hdist
  have heq :
      (fun r : ℝ => r * oneModeSwirlWithLine gammaLine circ 1 beta r)
        =ᶠ[𝓝[>] 0]
      (fun r : ℝ =>
        gammaLine / (2 * Real.pi) +
          distributedAngularMomentum circ 1 beta r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    symm
    exact oneModeAngularMomentumWithLine_eq_radius_mul_swirl hr
  have hline :
      Tendsto
        (fun r : ℝ => r * oneModeSwirlWithLine gammaLine circ 1 beta r)
        (𝓝[>] 0) (𝓝 (gammaLine / (2 * Real.pi))) :=
    hL.congr' heq.symm
  have hz : gammaLine / (2 * Real.pi) = 0 :=
    tendsto_nhds_unique hline hru
  exact (div_eq_zero_iff.mp hz).resolve_right
    (mul_ne_zero two_ne_zero Real.pi_ne_zero)

/-- The exponential slope identity needed for the linear regular-axis swirl
asymptotic. -/
theorem exp_slope_comp_neg_beta_sq
    {beta : ℝ} (hbeta : 0 < beta) :
    Tendsto
      (fun r : ℝ =>
        (-(beta * r ^ 2))⁻¹ *
          (Real.exp (-(beta * r ^ 2)) - 1))
      (𝓝[>] 0) (𝓝 1) := by
  have hslope :=
    (Real.hasDerivAt_exp 0).tendsto_slope_zero
  have hargFull :
      Tendsto (fun r : ℝ => -(beta * r ^ 2)) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun r : ℝ => -(beta * r ^ 2)) 0 := by fun_prop
    simpa using hc.tendsto
  have harg :
      Tendsto (fun r : ℝ => -(beta * r ^ 2))
        (𝓝[>] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ)) hargFull
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hr0 : r ≠ 0 := ne_of_gt hr
      simp [hbeta.ne', hr0]
  simpa [slope, Function.comp_def] using hslope.comp harg

/-- Manuscript Eq. (63), in its reviewer-relevant asymptotic form:
u_theta/r tends to Gamma beta/(2 pi) for one regular Gaussian mode. -/
theorem distributedSwirl_one_div_radius_tendsto
    {circ beta : ℝ} (hbeta : 0 < beta) :
    Tendsto
      (fun r : ℝ => distributedSwirl circ 1 beta r / r)
      (𝓝[>] 0) (𝓝 (circ * beta / (2 * Real.pi))) := by
  have hslope := exp_slope_comp_neg_beta_sq hbeta
  have hscaled :
      Tendsto
        (fun r : ℝ =>
          (circ * beta / (2 * Real.pi)) *
            ((-(beta * r ^ 2))⁻¹ *
              (Real.exp (-(beta * r ^ 2)) - 1)))
        (𝓝[>] 0) (𝓝 (circ * beta / (2 * Real.pi))) := by
    simpa using hslope.const_mul (circ * beta / (2 * Real.pi))
  apply hscaled.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : r ≠ 0 := ne_of_gt hr
  rw [distributedSwirl_one]
  · unfold scaledX
    field_simp [hr0, hbeta.ne', Real.pi_ne_zero]
    ring
  · unfold scaledX
    positivity

/-- In particular the regular one-mode swirl vanishes linearly at the axis. -/
theorem distributedSwirl_one_tendsto_zero
    {circ beta : ℝ} (hbeta : 0 < beta) :
    Tendsto (distributedSwirl circ 1 beta) (𝓝[>] 0) (𝓝 0) := by
  have hratio := distributedSwirl_one_div_radius_tendsto
    (circ := circ) hbeta
  have hr : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds (s := Ioi (0 : ℝ)) tendsto_id
  have hmul : Tendsto (fun r : ℝ => distributedSwirl circ 1 beta r / r * r)
      (𝓝[>] 0) (𝓝 0) := by simpa using hratio.mul hr
  apply hmul.congr'
  filter_upwards [self_mem_nhdsWithin] with r hpos
  have hr0 : r ≠ 0 := ne_of_gt hpos
  field_simp [hr0]

end

end KiknadzeKrasnov
