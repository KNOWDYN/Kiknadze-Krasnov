import KiknadzeKrasnov.SupercriticalEndpoint
import KiknadzeKrasnov.InverseScaleUniqueness

namespace KiknadzeKrasnov
noncomputable section
open Filter Set
open scoped Topology

/-- Accumulated strain really differentiates to the imposed singular strain in physical time. -/
theorem singularAccum_time_hasDerivAt {lambda p T t : ℝ}
    (hT : T ≠ 0) (hy : 0 < terminalY T t) (hp : p ≠ 1) :
    HasDerivAt (fun u => singularAccumNoncritical lambda p (terminalY T u))
      (singularStrainY lambda T p (terminalY T t)) t := by
  have h := (singularAccumNoncritical_hasDerivAt (lambda := lambda) hy hp).comp t
    ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).div_const T))
  convert h using 1
  · funext u; rfl
  · unfold singularStrainY
    field_simp [hT]
    ring

/-- The noncritical exact endpoint inverse scale solves the original linear scale equation. -/
theorem singularInverseScaleY_hasDerivAt {nu T h0 lambda p y : ℝ}
    (hy : 0 < y) (hp : p ≠ 1) :
    HasDerivAt (singularInverseScaleY nu T h0 lambda p)
      (lambda * y ^ (-p) * singularInverseScaleY nu T h0 lambda p y - 4 * nu * T) y := by
  have hA := singularAccumNoncritical_hasDerivAt (lambda := lambda) hy hp
  have hE := hA.neg.exp
  have hJ := singularExpIntegralY_hasDerivAt (lambda := lambda) (p := p) hy
  have h := hE.mul ((hJ.const_mul (4 * nu * T)).const_add h0)
  unfold singularInverseScaleY
  convert h using 1
  simp only [Pi.neg_apply]
  rw [Real.exp_neg]
  field_simp [(Real.exp_pos _).ne']
  ring

@[simp] theorem singularInverseScaleY_initial (nu T h0 lambda p : ℝ) :
    singularInverseScaleY nu T h0 lambda p 1 = h0 := by
  simp [singularInverseScaleY, singularAccumNoncritical, singularExpIntegralY]

/-- Noncritical singular family in physical time: h'+a h=4 nu. -/
theorem singularInverseScale_time_hasDerivAt {nu T h0 lambda p t : ℝ}
    (hT : T ≠ 0) (hy : 0 < terminalY T t) (hp : p ≠ 1) :
    HasDerivAt (fun u => singularInverseScaleY nu T h0 lambda p (terminalY T u))
      (4 * nu - singularStrainY lambda T p (terminalY T t) *
        singularInverseScaleY nu T h0 lambda p (terminalY T t)) t := by
  have h := (singularInverseScaleY_hasDerivAt (nu := nu) (T := T) (h0 := h0) (lambda := lambda) hy hp).comp t
    ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).div_const T))
  convert h using 1
  · funext u; rfl
  · unfold singularStrainY
    field_simp [hT]
    ring

/-- Exact p=1, lambda≠1 formula also solves the scale equation. -/
theorem reciprocalInverseScaleNoncritical_hasDerivAt {nu T h0 lambda y : ℝ}
    (hy : 0 < y) (hl : lambda ≠ 1) :
    HasDerivAt (reciprocalInverseScaleNoncritical nu T h0 lambda)
      (lambda / y * reciprocalInverseScaleNoncritical nu T h0 lambda y - 4 * nu * T) y := by
  have hpow := Real.hasDerivAt_rpow_const (p := lambda) (Or.inl hy.ne')
  have hpow2 := Real.hasDerivAt_rpow_const (p := 1 - lambda) (Or.inl hy.ne')
  have h := hpow.mul (((((hasDerivAt_const y (1 : ℝ)).sub hpow2).const_mul
    (4 * nu * T)).div_const (1 - lambda)).const_add h0)
  unfold reciprocalInverseScaleNoncritical
  convert h using 1
  simp only [Pi.sub_apply]
  rw [Real.rpow_sub_one hy.ne' lambda, Real.rpow_sub_one hy.ne' (1 - lambda)]
  have hcancel : y ^ lambda * y ^ (1 - lambda) = y := by
    rw [← Real.rpow_add hy]; norm_num
  field_simp [hy.ne', sub_ne_zero.mpr (Ne.symm hl)]
  linear_combination (4 * nu * T * (1 - lambda)) * hcancel

/-- Exact p=1, lambda=1 formula solves the scale equation including its logarithmic term. -/
theorem reciprocalInverseScaleCritical_hasDerivAt {nu T h0 y : ℝ} (hy : 0 < y) :
    HasDerivAt (reciprocalInverseScaleCritical nu T h0)
      (reciprocalInverseScaleCritical nu T h0 y / y - 4 * nu * T) y := by
  have hlog : HasDerivAt (fun v : ℝ => Real.log (v⁻¹)) (-1 / y) y := by
    have h := (Real.hasDerivAt_log hy.ne').neg
    convert h using 1
    · funext v; exact Real.log_inv v
    · simp only [neg_div, one_div]
  have h := (hasDerivAt_id y).mul ((hlog.const_mul (4 * nu * T)).const_add h0)
  unfold reciprocalInverseScaleCritical
  convert h using 1
  · funext v; rfl
  · dsimp only [id_eq]
    field_simp [hy.ne']
    ring

@[simp] theorem reciprocalInverseScaleNoncritical_initial (nu T h0 lambda : ℝ) :
    reciprocalInverseScaleNoncritical nu T h0 lambda 1 = h0 := by
  simp [reciprocalInverseScaleNoncritical]

@[simp] theorem reciprocalInverseScaleCritical_initial (nu T h0 : ℝ) :
    reciprocalInverseScaleCritical nu T h0 1 = h0 := by
  simp [reciprocalInverseScaleCritical]

/-- The critical accumulated strain is also an actual physical-time primitive. -/
theorem singularAccumCritical_time_hasDerivAt {lambda T t : ℝ}
    (_hT : T ≠ 0) (hy : 0 < terminalY T t) :
    HasDerivAt (fun u => singularAccumCritical lambda (terminalY T u))
      (singularStrainY lambda T 1 (terminalY T t)) t := by
  have hlog : HasDerivAt (fun y : ℝ => Real.log (y⁻¹)) (-(terminalY T t)⁻¹)
      (terminalY T t) := by
    convert (Real.hasDerivAt_log hy.ne').neg using 1
    funext y; simp [Real.log_inv]
  have h := (hlog.const_mul lambda).comp t
    ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).div_const T))
  unfold singularAccumCritical
  convert h using 1
  · funext u; rfl
  · unfold singularStrainY
    norm_num [Real.rpow_neg_one]
    ring

@[simp] theorem singularAccumNoncritical_initial (lambda p : ℝ) :
    singularAccumNoncritical lambda p 1 = 0 := by simp [singularAccumNoncritical]

@[simp] theorem singularAccumCritical_initial (lambda : ℝ) :
    singularAccumCritical lambda 1 = 0 := by simp [singularAccumCritical]

/-- Physical-time chain rule for both exact p=1 inverse-scale formulas. -/
theorem reciprocalScale_time_chainRule {H : ℝ → ℝ} {nu T lambda t : ℝ}
    (hT : T ≠ 0)
    (hd : HasDerivAt H (lambda / terminalY T t * H (terminalY T t) - 4 * nu * T)
      (terminalY T t)) :
    HasDerivAt (fun u => H (terminalY T u))
      (4 * nu - singularStrainY lambda T 1 (terminalY T t) * H (terminalY T t)) t := by
  have h := hd.comp t
    ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).div_const T))
  convert h using 1
  · funext u; rfl
  · unfold singularStrainY
    norm_num [Real.rpow_neg_one]
    field_simp [hT]
    ring

end
end KiknadzeKrasnov
