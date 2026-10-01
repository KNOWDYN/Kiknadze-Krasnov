import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace KiknadzeKrasnov
noncomputable section
open Set Filter
open scoped Topology

/-- Endpoint ratio theorem for two differentiable functions with a denominator
diverging at the right-hand endpoint. The numerator need not have an assumed limit. -/
theorem endpoint_ratio_tendsto
    {f g fp gp : ℝ → ℝ} {L : ℝ}
    (hf : ∀ᶠ x in 𝓝[>] (0 : ℝ), HasDerivAt f (fp x) x)
    (hg : ∀ᶠ x in 𝓝[>] (0 : ℝ), HasDerivAt g (gp x) x)
    (hgneg : ∀ᶠ x in 𝓝[>] (0 : ℝ), gp x < 0)
    (hgtop : Tendsto g (𝓝[>] (0 : ℝ)) atTop)
    (hratio : Tendsto (fun x => fp x / gp x) (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    Tendsto (fun x => f x / g x) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  have hgpos : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < g x :=
    hgtop.eventually (eventually_gt_atTop 0)
  have hinv := hgtop.inv_tendsto_atTop
  apply tendsto_order.2
  constructor
  · intro c hc
    let d : ℝ := (c + L) / 2
    have hcd : c < d := by dsimp [d]; linarith
    have hd1 : d < L := by dsimp [d]; linarith
    have he : ∀ᶠ x in 𝓝[>] (0 : ℝ),
        HasDerivAt f (fp x) x ∧ HasDerivAt g (gp x) x ∧
        gp x < 0 ∧ d < fp x / gp x := by
      filter_upwards [hf, hg, hgneg, hratio.eventually (Ioi_mem_nhds hd1)]
        with x hfx hgx hgn hrat
      exact ⟨hfx, hgx, hgn, hrat⟩
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
    change 0 < u at hu
    let v : ℝ := u / 2
    have hv : v ∈ Ioo (0 : ℝ) u := by dsimp [v]; constructor <;> linarith
    have hder : ∀ x ∈ Ioo (0 : ℝ) u,
        HasDerivAt (fun y => f y - d * g y) (fp x - d * gp x) x := by
      intro x hx
      exact (hsub hx).1.sub ((hsub hx).2.1.const_mul d)
    have hant : AntitoneOn (fun y => f y - d * g y) (Ioo (0 : ℝ) u) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 u)
      · intro x hx; exact (hder x hx).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Ioo] at hx
        exact (hder x hx).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Ioo] at hx
        rw [(hder x hx).deriv]
        have h := (lt_div_iff_of_neg (hsub hx).2.2.1).mp (hsub hx).2.2.2
        linarith
    let C : ℝ := f v - d * g v
    have hlim : Tendsto (fun x => d + C / g x)
        (𝓝[>] (0 : ℝ)) (𝓝 d) := by
      simpa [div_eq_mul_inv] using (hinv.const_mul C).const_add d
    filter_upwards [hlim.eventually (Ioi_mem_nhds hcd), hgpos,
      Ioo_mem_nhdsGT (show (0 : ℝ) < v from hv.1)] with x hcx hgx hx
    have hbound := hant ⟨hx.1, lt_trans hx.2 hv.2⟩ hv hx.2.le
    have hdiv : d + C / g x ≤ f x / g x := by
      apply (le_div_iff₀ hgx).2
      dsimp [C] at *
      field_simp [hgx.ne']
      linarith
    exact lt_of_lt_of_le hcx hdiv
  · intro c hc
    let d : ℝ := (c + L) / 2
    have hdc : d < c := by dsimp [d]; linarith
    have h1d : L < d := by dsimp [d]; linarith
    have he : ∀ᶠ x in 𝓝[>] (0 : ℝ),
        HasDerivAt f (fp x) x ∧ HasDerivAt g (gp x) x ∧
        gp x < 0 ∧ fp x / gp x < d := by
      filter_upwards [hf, hg, hgneg, hratio.eventually (Iio_mem_nhds h1d)]
        with x hfx hgx hgn hrat
      exact ⟨hfx, hgx, hgn, hrat⟩
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp he
    change 0 < u at hu
    let v : ℝ := u / 2
    have hv : v ∈ Ioo (0 : ℝ) u := by dsimp [v]; constructor <;> linarith
    have hder : ∀ x ∈ Ioo (0 : ℝ) u,
        HasDerivAt (fun y => f y - d * g y) (fp x - d * gp x) x := by
      intro x hx
      exact (hsub hx).1.sub ((hsub hx).2.1.const_mul d)
    have hmon : MonotoneOn (fun y => f y - d * g y) (Ioo (0 : ℝ) u) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 u)
      · intro x hx; exact (hder x hx).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Ioo] at hx
        exact (hder x hx).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Ioo] at hx
        rw [(hder x hx).deriv]
        have h := (div_lt_iff_of_neg (hsub hx).2.2.1).mp (hsub hx).2.2.2
        linarith
    let C : ℝ := f v - d * g v
    have hlim : Tendsto (fun x => d + C / g x)
        (𝓝[>] (0 : ℝ)) (𝓝 d) := by
      simpa [div_eq_mul_inv] using (hinv.const_mul C).const_add d
    filter_upwards [hlim.eventually (Iio_mem_nhds hdc), hgpos,
      Ioo_mem_nhdsGT (show (0 : ℝ) < v from hv.1)] with x hcx hgx hx
    have hbound := hmon ⟨hx.1, lt_trans hx.2 hv.2⟩ hv hx.2.le
    have hdiv : f x / g x ≤ d + C / g x := by
      apply (div_le_iff₀ hgx).2
      dsimp [C] at *
      field_simp [hgx.ne']
      linarith
    exact lt_of_le_of_lt hdiv hcx

/-- Ratio-one specialisation used by the Laplace endpoint certificate. -/
theorem endpoint_ratio_tendsto_one
    {f g fp gp : ℝ → ℝ}
    (hf : ∀ᶠ x in 𝓝[>] (0 : ℝ), HasDerivAt f (fp x) x)
    (hg : ∀ᶠ x in 𝓝[>] (0 : ℝ), HasDerivAt g (gp x) x)
    (hgneg : ∀ᶠ x in 𝓝[>] (0 : ℝ), gp x < 0)
    (hgtop : Tendsto g (𝓝[>] (0 : ℝ)) atTop)
    (hratio : Tendsto (fun x => fp x / gp x) (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    Tendsto (fun x => f x / g x) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
  endpoint_ratio_tendsto hf hg hgneg hgtop hratio

end
end KiknadzeKrasnov
