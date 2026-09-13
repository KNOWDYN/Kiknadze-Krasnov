import KiknadzeKrasnov.Meridional

namespace KiknadzeKrasnov

noncomputable section

/-- Riccati residual for the KK inverse-squared radial scale. -/
def scaleResidual (nu a beta betaDot : ℝ) : ℝ :=
  betaDot - a * beta + 4 * nu * beta ^ 2

/-- Rate obtained by differentiating `h=1/beta`. -/
def inverseScaleRate (beta betaDot : ℝ) : ℝ := -betaDot / beta ^ 2

/-- Differentiation of the reciprocal scale is machine checked rather than inserted algebraically. -/
theorem inverseScale_hasDerivAt {beta : ℝ → ℝ} {betaDot t : ℝ}
    (hbeta : HasDerivAt beta betaDot t) (hne : beta t ≠ 0) :
    HasDerivAt (fun tau => inverseScale (beta tau))
      (inverseScaleRate (beta t) betaDot) t := by
  unfold inverseScale inverseScaleRate
  exact hbeta.inv hne

/-- Algebraic form of the scale equation used throughout the paper. -/
theorem scaleResidual_zero_iff {nu a beta betaDot : ℝ} :
    scaleResidual nu a beta betaDot = 0 ↔
      betaDot = a * beta - 4 * nu * beta ^ 2 := by
  unfold scaleResidual
  constructor <;> intro h <;> linarith

/-- The Riccati scale equation becomes the linear inverse-scale equation. -/
theorem inverseScale_linear_identity {nu a beta betaDot : ℝ}
    (hne : beta ≠ 0) (hscale : scaleResidual nu a beta betaDot = 0) :
    inverseScaleRate beta betaDot + a * inverseScale beta = 4 * nu := by
  unfold inverseScaleRate inverseScale
  have hb := (scaleResidual_zero_iff.mp hscale)
  field_simp [hne]
  nlinarith

/-- Differential version of `h' + a h = 4 nu` for a genuine differentiable scale history. -/
theorem inverseScale_ode {nu a betaDot t : ℝ} {beta : ℝ → ℝ}
    (hbeta : HasDerivAt beta betaDot t) (hne : beta t ≠ 0)
    (hscale : scaleResidual nu a (beta t) betaDot = 0) :
    HasDerivAt (fun tau => inverseScale (beta tau))
      (4 * nu - a * inverseScale (beta t)) t := by
  have hrec := inverseScale_hasDerivAt hbeta hne
  convert hrec using 1
  have hlin := inverseScale_linear_identity (nu := nu) (a := a)
    (beta := beta t) (betaDot := betaDot) hne hscale
  linarith

end

end KiknadzeKrasnov
