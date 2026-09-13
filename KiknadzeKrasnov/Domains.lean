import KiknadzeKrasnov.Parameters

namespace KiknadzeKrasnov

noncomputable section

open Set

/-- Radial domain for a regular-axis KK field. -/
def RegularRadius (r : ℝ) : Prop := 0 ≤ r

/-- Radial domain for source/sink or line-circulation KK fields. -/
def PuncturedRadius (r : ℝ) : Prop := 0 < r

/-- Half-open physical time interval used by the source, `[0,T)`. -/
def TimeDomain (T : ℝ) : Set ℝ := Ico 0 T

/-- Pointwise interior of the physical time interval. -/
def InteriorTime (T t : ℝ) : Prop := 0 < t ∧ t < T

/--
Exact formal rendering of the source requirement that a prescribed history is continuously
differentiable on every compact subinterval of `[0,T)`.
-/
def AdmissibleHistory (T : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ K : Set ℝ, IsCompact K → K ⊆ TimeDomain T → ContDiffOn ℝ 1 f K

/-- Positivity of an inverse-squared radial scale on the physical time interval. -/
def PositiveScaleOn (T : ℝ) (beta : ℝ → ℝ) : Prop :=
  ∀ t ∈ TimeDomain T, 0 < beta t

@[simp] theorem puncturedRadius_imp_regularRadius {r : ℝ} (hr : PuncturedRadius r) :
    RegularRadius r := le_of_lt hr

@[simp] theorem zero_regularRadius : RegularRadius 0 := le_rfl

@[simp] theorem zero_not_puncturedRadius : ¬ PuncturedRadius 0 := by
  simp [PuncturedRadius]

/-- A positive terminal time makes `0` part of the half-open time domain. -/
theorem zero_mem_timeDomain {T : ℝ} (hT : 0 < T) : 0 ∈ TimeDomain T := by
  exact ⟨le_rfl, hT⟩

end

end KiknadzeKrasnov
