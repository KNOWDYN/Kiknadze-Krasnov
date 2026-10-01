import KiknadzeKrasnov.HeatTransform

namespace KiknadzeKrasnov
noncomputable section

/-- Collision-free two-variable derivative map for the transformed heat profile. -/
def heatProfileDerivative (WX WT : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  WX • ContinuousLinearMap.fst ℝ ℝ ℝ + WT • ContinuousLinearMap.snd ℝ ℝ ℝ

/-- Actual radial chain rule for a transformed heat profile. -/
theorem heatProfile_radial_hasDerivAt {A tau r WX WT : ℝ} {W : ℝ × ℝ → ℝ}
    (hW : HasFDerivAt W (heatProfileDerivative WX WT) (heatXi A r, tau)) :
    HasDerivAt (fun y => heatStretch A ^ 2 * W (heatXi A y, tau))
      (heatStretch A ^ 3 * WX) r := by
  have hp := (heatXi_hasDerivAt_r A r).prodMk (hasDerivAt_const r tau)
  have h := (hW.comp_hasDerivAt r hp).const_mul (heatStretch A ^ 2)
  convert h using 1
  · funext y; rfl
  · simp [heatProfileDerivative]
    ring

/-- Actual second radial chain rule, differentiating the certified first-derivative field. -/
theorem heatProfile_radialDerivative_hasDerivAt {A tau r WXX WXT : ℝ}
    {WX : ℝ × ℝ → ℝ}
    (hWX : HasFDerivAt WX (heatProfileDerivative WXX WXT) (heatXi A r, tau)) :
    HasDerivAt (fun y => heatStretch A ^ 3 * WX (heatXi A y, tau))
      (heatStretch A ^ 4 * WXX) r := by
  have hp := (heatXi_hasDerivAt_r A r).prodMk (hasDerivAt_const r tau)
  have h := (hWX.comp_hasDerivAt r hp).const_mul (heatStretch A ^ 3)
  convert h using 1
  · funext y; rfl
  · simp [heatProfileDerivative]
    ring

/-- Actual time chain rule with stretched radius and transformed heat time. -/
theorem heatProfile_time_hasDerivAt {A tau : ℝ → ℝ} {t r a WX WT : ℝ}
    {W : ℝ × ℝ → ℝ} (hA : HasDerivAt A a t)
    (htau : HasDerivAt tau (heatStretch (A t) ^ 2) t)
    (hW : HasFDerivAt W (heatProfileDerivative WX WT) (heatXi (A t) r, tau t)) :
    HasDerivAt (fun u => heatStretch (A u) ^ 2 * W (heatXi (A u) r, tau u))
      (heatStretch (A t) ^ 2 * (a * W (heatXi (A t) r, tau t) +
        (a / 2) * heatXi (A t) r * WX) + heatStretch (A t) ^ 4 * WT) t := by
  have he : HasDerivAt (fun u => heatStretch (A u)) (a / 2 * heatStretch (A t)) t := by
    have h := (hA.div_const 2).exp
    unfold heatStretch
    convert h using 1
    ring
  have hx : HasDerivAt (fun u => heatXi (A u) r) ((a / 2) * heatXi (A t) r) t := by
    unfold heatXi
    convert he.const_mul r using 1
    ring
  have h := (he.pow 2).mul (hW.comp_hasDerivAt t (hx.prodMk htau))
  convert h using 1
  · funext y; rfl
  · simp [heatProfileDerivative]
    ring

end
end KiknadzeKrasnov
