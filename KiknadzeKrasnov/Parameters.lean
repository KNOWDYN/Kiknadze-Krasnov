import Mathlib

namespace KiknadzeKrasnov

noncomputable section

/-- Constant fluid parameters used by the Kiknadze--Krasnov family. -/
structure FluidParams where
  rho : ℝ
  mu : ℝ
  nu : ℝ
  rho_pos : 0 < rho
  mu_pos : 0 < mu
  nu_eq : nu = mu / rho

namespace FluidParams

@[simp] theorem rho_ne_zero (p : FluidParams) : p.rho ≠ 0 := ne_of_gt p.rho_pos

@[simp] theorem mu_ne_zero (p : FluidParams) : p.mu ≠ 0 := ne_of_gt p.mu_pos

theorem nu_pos (p : FluidParams) : 0 < p.nu := by
  rw [p.nu_eq]
  exact div_pos p.mu_pos p.rho_pos

@[simp] theorem nu_ne_zero (p : FluidParams) : p.nu ≠ 0 := ne_of_gt p.nu_pos

end FluidParams

/-- Incomplete-gamma shape parameter `s = 1 + q/(2ν)`. -/
def shape (p : FluidParams) (q : ℝ) : ℝ := 1 + q / (2 * p.nu)

@[simp] theorem shape_zero_source (p : FluidParams) : shape p 0 = 1 := by
  simp [shape]

theorem shape_sub_one (p : FluidParams) (q : ℝ) :
    shape p q - 1 = q / (2 * p.nu) := by
  simp [shape]

theorem source_eq_two_nu_mul_shape_sub_one (p : FluidParams) (q : ℝ) :
    q = 2 * p.nu * (shape p q - 1) := by
  rw [shape_sub_one]
  field_simp [p.nu_ne_zero]

/-- The finite-circulation normalised incomplete-gamma branch. -/
def FiniteCirculationBranch (p : FluidParams) (q : ℝ) : Prop := 0 < shape p q

/-- The source-bearing branch possessing a positive annular distinguished radius. -/
def AnnularSourceBranch (p : FluidParams) (q : ℝ) : Prop := 1 < shape p q

/-- `s > 1` is equivalent to a positive line-source coefficient `q > 0`. -/
theorem annularSourceBranch_iff_q_pos (p : FluidParams) (q : ℝ) :
    AnnularSourceBranch p q ↔ 0 < q := by
  have hden : 0 < 2 * p.nu := mul_pos (by norm_num) p.nu_pos
  constructor
  · intro h
    have hdiv : 0 < q / (2 * p.nu) := by
      unfold AnnularSourceBranch shape at h
      linarith
    calc
      0 < (q / (2 * p.nu)) * (2 * p.nu) := mul_pos hdiv hden
      _ = q := by field_simp [p.nu_ne_zero]
  · intro hq
    unfold AnnularSourceBranch shape
    have hdiv : 0 < q / (2 * p.nu) := div_pos hq hden
    linarith

/-- `s > 0` is equivalent to `q > -2ν`. -/
theorem finiteCirculationBranch_iff (p : FluidParams) (q : ℝ) :
    FiniteCirculationBranch p q ↔ -2 * p.nu < q := by
  have hden : 0 < 2 * p.nu := mul_pos (by norm_num) p.nu_pos
  constructor
  · intro h
    unfold FiniteCirculationBranch shape at h
    have hqdiv : (-1 : ℝ) < q / (2 * p.nu) := by linarith
    have hraw : (-1 : ℝ) * (2 * p.nu) < q :=
      (lt_div_iff₀ hden).1 hqdiv
    convert hraw using 1 <;> ring
  · intro hq
    unfold FiniteCirculationBranch shape
    have hraw : (-1 : ℝ) * (2 * p.nu) < q := by
      convert hq using 1 <;> ring
    have hqdiv : (-1 : ℝ) < q / (2 * p.nu) :=
      (lt_div_iff₀ hden).2 hraw
    linarith

end

end KiknadzeKrasnov
