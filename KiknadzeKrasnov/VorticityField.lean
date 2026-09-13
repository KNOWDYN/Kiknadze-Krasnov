import KiknadzeKrasnov.KKField

namespace KiknadzeKrasnov

noncomputable section

/-- One distributed mode's angular momentum `L=Γ P(s,βr²)/(2π)`. -/
def distributedAngularMomentum (circ s beta r : ℝ) : ℝ :=
  circ / (2 * Real.pi) * regLowerGamma s (scaledX beta r)

/-- The scaled squared radius has radial derivative `2βr`. -/
theorem scaledX_hasDerivAt (beta r : ℝ) :
    HasDerivAt (scaledX beta) (2 * beta * r) r := by
  unfold scaledX
  convert ((hasDerivAt_id r).pow 2).const_mul beta using 1 <;> ring

/-- Radial derivative of a regularised incomplete-gamma profile after the KK change of variables. -/
theorem regLowerGamma_scaledX_hasDerivAt
    {s beta r : ℝ} (hs : 0 < s) (hx : 0 < scaledX beta r) :
    HasDerivAt (fun y => regLowerGamma s (scaledX beta y))
      (regLowerGammaDensity s (scaledX beta r) * (2 * beta * r)) r := by
  have hP := (regLowerGamma_hasDerivAt hs hx).comp r (scaledX_hasDerivAt beta r)
  convert hP using 1
  unfold regLowerGammaDensity
  ring

/-- Certified radial derivative of a one-mode angular momentum profile. -/
theorem distributedAngularMomentum_hasDerivAt
    {circ s beta r : ℝ} (hs : 0 < s) (hx : 0 < scaledX beta r) :
    HasDerivAt (distributedAngularMomentum circ s beta)
      (circ / (2 * Real.pi) *
        (regLowerGammaDensity s (scaledX beta r) * (2 * beta * r))) r := by
  unfold distributedAngularMomentum
  exact (regLowerGamma_scaledX_hasDerivAt hs hx).const_mul (circ / (2 * Real.pi))

/-- The source vorticity formula is exactly `(1/r) ∂_r(r u_theta)` for one distributed mode. -/
theorem distributedVorticity_eq_angularMomentumCurl
    {circ s beta r : ℝ}
    (hs : 0 < s) (hbeta : 0 < beta) (hr : 0 < r) :
    deriv (distributedAngularMomentum circ s beta) r / r =
      distributedVorticity circ s beta r := by
  have hx : 0 < scaledX beta r := by
    unfold scaledX
    positivity
  rw [(distributedAngularMomentum_hasDerivAt (circ := circ) hs hx).deriv]
  unfold distributedVorticity vorticityShape regLowerGammaDensity gammaKernel
  field_simp [hr.ne', Real.pi_ne_zero, gammaFn_ne_zero hs]
  ring

/-- Finite-mode distributed axial vorticity; constant central line circulation has no classical vorticity on `r>0`. -/
def multimodeDistributedVorticity {n : ℕ}
    (circ : Fin n → ℝ) (s : ℝ) (beta : Fin n → ℝ) (r : ℝ) : ℝ :=
  ∑ i, distributedVorticity (circ i) s (beta i) r

end

end KiknadzeKrasnov
