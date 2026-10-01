import KiknadzeKrasnov.ScaleDynamics
import Mathlib.Analysis.Calculus.MeanValue

namespace KiknadzeKrasnov
noncomputable section
open Set

/-- Initial-value uniqueness for the inverse-scale equation on a connected open time domain.
This justifies identification of an explicit ODE/initial-value certificate with any other solution. -/
theorem inverseScale_initial_value_unique {D : Set ℝ} {A a H K : ℝ → ℝ}
    {nu t0 : ℝ} (hD : IsOpen D) (hconn : IsPreconnected D) (ht0 : t0 ∈ D)
    (hA : ∀ t ∈ D, HasDerivAt A (a t) t)
    (hH : ∀ t ∈ D, HasDerivAt H (4 * nu - a t * H t) t)
    (hK : ∀ t ∈ D, HasDerivAt K (4 * nu - a t * K t) t)
    (h0 : H t0 = K t0) : EqOn H K D := by
  let F : ℝ → ℝ := fun t => Real.exp (A t) * (H t - K t)
  have hd : ∀ t ∈ D, HasDerivAt F 0 t := by
    intro t ht
    have h := ((hA t ht).exp).mul ((hH t ht).sub (hK t ht))
    convert h using 1; dsimp [F]; ring
  intro t ht
  have he := hD.is_const_of_deriv_eq_zero hconn
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) ht ht0
  dsimp [F] at he
  rw [h0, sub_self, mul_zero] at he
  have hz := (mul_eq_zero.mp he).resolve_left (Real.exp_pos _).ne'
  exact sub_eq_zero.mp hz

end
end KiknadzeKrasnov
