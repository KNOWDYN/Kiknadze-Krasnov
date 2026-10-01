import KiknadzeKrasnov.VorticityTransport

namespace KiknadzeKrasnov
noncomputable section

/-- Explicit radial derivative coefficient of an actual gamma-vorticity mode. -/
def vorticityRadialCoefficient (s beta r : ℝ) : ℝ :=
  2 * (s - 1) / r - 2 * beta * r

/-- First radial derivative of the physical field, in coefficient form. -/
theorem distributedVorticity_hasDerivAt_coefficient {circ s beta r : ℝ}
    (hs : 0 < s) (hb : 0 < beta) (hr : 0 < r) :
    HasDerivAt (distributedVorticity circ s beta)
      (vorticityRadialCoefficient s beta r * distributedVorticity circ s beta r) r := by
  have h := distributedVorticity_hasDerivAt_r (circ := circ) hs hb hr
  convert h using 1
  unfold vorticityRadialCoefficient distributedVorticity scaledX
  field_simp [hr.ne', hb.ne', Real.pi_ne_zero, gammaFn_ne_zero hs]

/-- Derivative of the coefficient itself. -/
theorem vorticityRadialCoefficient_hasDerivAt {s beta r : ℝ} (hr : 0 < r) :
    HasDerivAt (vorticityRadialCoefficient s beta)
      (-2 * (s - 1) / r ^ 2 - 2 * beta) r := by
  have h := ((hasDerivAt_const r (2 * (s - 1))).div (hasDerivAt_id r) hr.ne').sub
    ((hasDerivAt_id r).const_mul (2 * beta))
  unfold vorticityRadialCoefficient
  convert h using 1
  · funext y; simp
  · simp

/-- Second radial derivative obtained by differentiating the first physical derivative. -/
theorem distributedVorticity_radialDerivative_hasDerivAt {circ s beta r : ℝ}
    (hs : 0 < s) (hb : 0 < beta) (hr : 0 < r) :
    HasDerivAt (fun y => vorticityRadialCoefficient s beta y *
      distributedVorticity circ s beta y)
      ((-2 * (s - 1) / r ^ 2 - 2 * beta +
        vorticityRadialCoefficient s beta r ^ 2) *
          distributedVorticity circ s beta r) r := by
  have h := (vorticityRadialCoefficient_hasDerivAt (s := s) (beta := beta) hr).mul
    (distributedVorticity_hasDerivAt_coefficient (circ := circ) hs hb hr)
  convert h using 1
  ring

/-- Actual time derivative of a gamma-vorticity field with fixed amplitude and shape. -/
theorem distributedVorticity_time_hasDerivAt {circ s r t betaDot : ℝ} {beta : ℝ → ℝ}
    (hb : 0 < beta t) (hr : 0 < r) (hd : HasDerivAt beta betaDot t) :
    HasDerivAt (fun tau => distributedVorticity circ s (beta tau) r)
      ((betaDot / beta t) * (s - scaledX (beta t) r) *
        distributedVorticity circ s (beta t) r) t := by
  have hx : 0 < scaledX (beta t) r := by unfold scaledX; positivity
  have hX : HasDerivAt (fun tau => scaledX (beta tau) r) (betaDot * r ^ 2) t :=
    hd.mul_const (r ^ 2)
  have hF := (vorticityShape_hasDerivAt (s := s) hx).comp t hX
  have h := ((hd.const_mul circ).div_const (Real.pi * gammaFn s)).mul hF
  unfold distributedVorticity
  convert h using 1
  · funext y; rfl
  · dsimp only [Function.comp_apply]
    unfold scaledX
    field_simp [hb.ne', hr.ne']
    ring

/-- All derivatives in the actual vorticity residual have now been separately certified. -/
theorem actualVorticityTransportResidual_zero {nu a q circ s beta betaDot r : ℝ}
    (hb : 0 < beta) (hr : 0 < r)
    (hscale : betaScaleResidual nu a beta betaDot = 0)
    (hcompat : q = 2 * nu * (s - 1)) :
    vorticityTransportResidualLocal nu a q r
      (distributedVorticity circ s beta r)
      ((betaDot / beta) * (s - scaledX beta r) * distributedVorticity circ s beta r)
      (vorticityRadialCoefficient s beta r * distributedVorticity circ s beta r)
      ((-2 * (s - 1) / r ^ 2 - 2 * beta + vorticityRadialCoefficient s beta r ^ 2) *
        distributedVorticity circ s beta r) = 0 := by
  have hbd := betaScaleResidual_zero_iff_rate.mp hscale
  unfold vorticityTransportResidualLocal radialVelocity vorticityRadialCoefficient scaledX
  rw [hbd, hcompat]
  field_simp [hb.ne', hr.ne']
  ring

end
end KiknadzeKrasnov
