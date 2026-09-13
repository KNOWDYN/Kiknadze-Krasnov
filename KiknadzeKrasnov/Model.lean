import KiknadzeKrasnov.SpecialFunctions

namespace KiknadzeKrasnov

noncomputable section

/-- Frozen-data representation of a finite-mode KK problem on `[0,T)`. -/
structure KKModel (T : ℝ) where
  fluid : FluidParams
  q : ℝ
  gammaLine : ℝ
  nModes : ℕ
  circMode : Fin nModes → ℝ
  beta0 : Fin nModes → ℝ
  beta0_pos : ∀ i, 0 < beta0 i
  a : ℝ → ℝ
  b : ℝ → ℝ
  a_admissible : AdmissibleHistory T a
  b_admissible : AdmissibleHistory T b

/-- Regular-axis branch: no radial line source/sink and no central line circulation. -/
def KKModel.IsRegularAxis {T : ℝ} (M : KKModel T) : Prop :=
  M.q = 0 ∧ M.gammaLine = 0

/-- Finite-circulation source/sink branch. -/
def KKModel.IsFiniteCirculation {T : ℝ} (M : KKModel T) : Prop :=
  FiniteCirculationBranch M.fluid M.q

/-- Source-bearing branch supporting the annular material surface. -/
def KKModel.IsAnnularSource {T : ℝ} (M : KKModel T) : Prop :=
  AnnularSourceBranch M.fluid M.q

@[simp] theorem KKModel.regular_shape {T : ℝ} {M : KKModel T}
    (hM : M.IsRegularAxis) : shape M.fluid M.q = 1 := by
  rw [hM.1]
  exact shape_zero_source M.fluid

end

end KiknadzeKrasnov
