import KiknadzeKrasnov.VorticityField
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace KiknadzeKrasnov

noncomputable section

open Set

/-- The gamma kernel and the manuscript vorticity-shape function are the same function. -/
theorem vorticityShape_eq_gammaKernel (s x : ℝ) :
    vorticityShape s x = gammaKernel s x := by
  unfold vorticityShape gammaKernel
  ring

/-- The one-mode vorticity shape has the exact factored derivative on `x>0`. -/
theorem vorticityShape_hasDerivAt {s x : ℝ} (hx : 0 < x) :
    HasDerivAt (vorticityShape s)
      (((s - 1) / x - 1) * vorticityShape s x) x := by
  convert gammaKernel_hasDerivAt_profile (s := s) hx using 1
  · funext y
    exact vorticityShape_eq_gammaKernel s y
  · rw [vorticityShape_eq_gammaKernel]

/-- The gamma/vorticity shape is strictly positive at positive scaled radius. -/
theorem vorticityShape_pos {s x : ℝ} (hx : 0 < x) :
    0 < vorticityShape s x := by
  unfold vorticityShape
  exact mul_pos (Real.rpow_pos_of_pos hx _) (Real.exp_pos _)

/-- Before `x=s-1`, the shape derivative is positive for `s>1`. -/
theorem vorticityShape_deriv_pos_before_peak {s x : ℝ}
    (_hs : 1 < s) (hx : 0 < x) (hxp : x < s - 1) :
    0 < deriv (vorticityShape s) x := by
  rw [(vorticityShape_hasDerivAt (s := s) hx).deriv]
  have hcoef : 0 < (s - 1) / x - 1 := by
    rw [sub_pos]
    exact (lt_div_iff₀ hx).2 (by linarith)
  exact mul_pos hcoef (vorticityShape_pos hx)

/-- After `x=s-1`, the shape derivative is negative for `s>1`. -/
theorem vorticityShape_deriv_neg_after_peak {s x : ℝ}
    (_hs : 1 < s) (hx : 0 < x) (hxp : s - 1 < x) :
    deriv (vorticityShape s) x < 0 := by
  rw [(vorticityShape_hasDerivAt (s := s) hx).deriv]
  have hcoef : (s - 1) / x - 1 < 0 := by
    rw [sub_neg]
    exact (div_lt_iff₀ hx).2 (by linarith)
  exact mul_neg_of_neg_of_pos hcoef (vorticityShape_pos hx)

/-- The scaled shape has zero derivative at the annular point `x=s-1`. -/
theorem vorticityShape_deriv_at_peak {s : ℝ} (hs : 1 < s) :
    deriv (vorticityShape s) (s - 1) = 0 := by
  have hx : 0 < s - 1 := by linarith
  rw [(vorticityShape_hasDerivAt (s := s) hx).deriv]
  field_simp [hx.ne']
  ring

/-- Strict global peak of the positive gamma/vorticity shape on `x>0` for `s>1`. -/
theorem vorticityShape_lt_peak {s x : ℝ}
    (hs : 1 < s) (hx : 0 < x) (hne : x ≠ s - 1) :
    vorticityShape s x < vorticityShape s (s - 1) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hcont : ContinuousOn (vorticityShape s) (Icc x (s - 1)) := by
      intro y hy
      have hpos : 0 < y := lt_of_lt_of_le hx hy.1
      exact (vorticityShape_hasDerivAt (s := s) hpos).continuousAt.continuousWithinAt
    have hmono : StrictMonoOn (vorticityShape s) (Icc x (s - 1)) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc x (s - 1)) hcont
      intro y hy
      rw [interior_Icc] at hy
      exact vorticityShape_deriv_pos_before_peak hs
        (lt_trans hx hy.1) hy.2
    exact hmono (left_mem_Icc.mpr hlt.le) (right_mem_Icc.mpr hlt.le) hlt
  · have hcont : ContinuousOn (vorticityShape s) (Icc (s - 1) x) := by
      intro y hy
      have hpos : 0 < y := lt_of_lt_of_le (sub_pos.mpr hs) hy.1
      exact (vorticityShape_hasDerivAt (s := s) hpos).continuousAt.continuousWithinAt
    have hanti : StrictAntiOn (vorticityShape s) (Icc (s - 1) x) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc (s - 1) x) hcont
      intro y hy
      rw [interior_Icc] at hy
      exact vorticityShape_deriv_neg_after_peak hs
        (lt_trans (sub_pos.mpr hs) hy.1) hy.1
    exact hanti (left_mem_Icc.mpr hgt.le) (right_mem_Icc.mpr hgt.le) hgt

/-- Radial derivative of the one-mode enclosed circulation equals `2πrω_z`. -/
theorem distributedCirculation_hasDerivAt_r
    {circ s beta r : ℝ} (hs : 0 < s) (hbeta : 0 < beta) (hr : 0 < r) :
    HasDerivAt (distributedCirculation circ s beta)
      (2 * Real.pi * r * distributedVorticity circ s beta r) r := by
  have hx : 0 < scaledX beta r := by
    unfold scaledX
    positivity
  have hP := (regLowerGamma_scaledX_hasDerivAt (s := s) (beta := beta) hs hx).const_mul circ
  unfold distributedCirculation distributedVorticity regLowerGammaDensity
    vorticityShape gammaKernel at *
  convert hP using 1
  field_simp [gammaFn_ne_zero hs, Real.pi_ne_zero]

/-- Radial derivative of the one-mode vorticity in factored scaled-radius form. -/
theorem distributedVorticity_hasDerivAt_r
    {circ s beta r : ℝ} (hs : 0 < s) (hbeta : 0 < beta) (hr : 0 < r) :
    HasDerivAt (distributedVorticity circ s beta)
      (circ * beta / (Real.pi * gammaFn s) *
        (((s - 1) / scaledX beta r - 1) * vorticityShape s (scaledX beta r)) *
        (2 * beta * r)) r := by
  have hx : 0 < scaledX beta r := by
    unfold scaledX
    positivity
  have hshape := (vorticityShape_hasDerivAt (s := s) hx).comp r (scaledX_hasDerivAt beta r)
  unfold distributedVorticity
  simpa only [Function.comp_apply, mul_assoc] using
    hshape.const_mul (circ * beta / (Real.pi * gammaFn s))

/-- Positive annular peak radius in physical space. -/
def vorticityPeakRadius (s beta : ℝ) : ℝ :=
  Real.sqrt ((s - 1) / beta)

/-- The peak radius is positive for `s>1` and `beta>0`. -/
theorem vorticityPeakRadius_pos {s beta : ℝ} (hs : 1 < s) (hbeta : 0 < beta) :
    0 < vorticityPeakRadius s beta := by
  unfold vorticityPeakRadius
  exact Real.sqrt_pos.2 (div_pos (by linarith) hbeta)

/-- The physical peak radius maps exactly to `x=s-1`. -/
theorem scaledX_vorticityPeakRadius {s beta : ℝ}
    (hs : 1 < s) (hbeta : 0 < beta) :
    scaledX beta (vorticityPeakRadius s beta) = s - 1 := by
  unfold scaledX vorticityPeakRadius
  rw [Real.sq_sqrt (div_nonneg (by linarith) hbeta.le)]
  field_simp [hbeta.ne']

/-- The physical one-mode vorticity derivative vanishes at the annular peak radius. -/
theorem distributedVorticity_deriv_at_peak
    {circ s beta : ℝ} (hs : 1 < s) (hbeta : 0 < beta) :
    deriv (distributedVorticity circ s beta) (vorticityPeakRadius s beta) = 0 := by
  have hr := vorticityPeakRadius_pos hs hbeta
  rw [(distributedVorticity_hasDerivAt_r (circ := circ) (s := s)
    (beta := beta) (r := vorticityPeakRadius s beta) (by linarith) hbeta hr).deriv]
  rw [scaledX_vorticityPeakRadius hs hbeta]
  field_simp [sub_ne_zero.mpr (ne_of_gt hs)]
  ring

/-- Exact signed vorticity value at the annular peak radius. -/
theorem distributedVorticity_at_peak
    {circ s beta : ℝ} (hs : 1 < s) (hbeta : 0 < beta) :
    distributedVorticity circ s beta (vorticityPeakRadius s beta) =
      circ * beta / (Real.pi * gammaFn s) *
        ((s - 1) ^ (s - 1) * Real.exp (-(s - 1))) := by
  unfold distributedVorticity vorticityShape
  rw [scaledX_vorticityPeakRadius hs hbeta]

/-- For nonzero circulation, the magnitude of one-mode vorticity has a unique positive-radius peak. -/
theorem abs_distributedVorticity_lt_peak
    {circ s beta r : ℝ} (hcirc : circ ≠ 0) (hs : 1 < s)
    (hbeta : 0 < beta) (hr : 0 < r)
    (hne : r ≠ vorticityPeakRadius s beta) :
    |distributedVorticity circ s beta r| <
      |distributedVorticity circ s beta (vorticityPeakRadius s beta)| := by
  have hx : 0 < scaledX beta r := by
    unfold scaledX
    positivity
  have hxpeak := scaledX_vorticityPeakRadius hs hbeta
  have hxr_ne : scaledX beta r ≠ s - 1 := by
    intro h
    have hscaled : scaledX beta r =
        scaledX beta (vorticityPeakRadius s beta) := h.trans hxpeak.symm
    have hmul : beta * r ^ 2 =
        beta * (vorticityPeakRadius s beta) ^ 2 := by
      simpa [scaledX] using hscaled
    have hr2 : r ^ 2 = (vorticityPeakRadius s beta) ^ 2 :=
      mul_left_cancel₀ hbeta.ne' hmul
    have hrEq : r = vorticityPeakRadius s beta := by
      nlinarith [hr, vorticityPeakRadius_pos hs hbeta]
    exact hne hrEq
  have hshape := vorticityShape_lt_peak hs hx hxr_ne
  unfold distributedVorticity
  have hspos : 0 < s := lt_trans zero_lt_one hs
  have hpref_ne : circ * beta / (Real.pi * gammaFn s) ≠ 0 := by
    exact div_ne_zero (mul_ne_zero hcirc hbeta.ne')
      (mul_ne_zero Real.pi_ne_zero (gammaFn_ne_zero hspos))
  have hpref : 0 < |circ * beta / (Real.pi * gammaFn s)| := abs_pos.mpr hpref_ne
  simp only [abs_mul]
  rw [abs_of_pos (vorticityShape_pos hx)]
  rw [hxpeak, abs_of_pos (vorticityShape_pos (sub_pos.mpr hs))]
  exact mul_lt_mul_of_pos_left hshape hpref

end

end KiknadzeKrasnov
