import KiknadzeKrasnov.Model

namespace KiknadzeKrasnov

noncomputable section

open intervalIntegral

/-- Radial KK velocity at one time. -/
def radialVelocity (a q r : ℝ) : ℝ := -(a / 2) * r + q / r

/-- Axial KK velocity at one time. -/
def axialVelocity (a b z : ℝ) : ℝ := a * z + b

/-- Specific axial angular momentum. -/
def angularMomentum (r uTheta : ℝ) : ℝ := r * uTheta

/-- Scaled squared radius used throughout the paper. -/
def scaledX (beta r : ℝ) : ℝ := beta * r ^ 2

/-- Inverse squared radial scale `h=1/β`. -/
def inverseScale (beta : ℝ) : ℝ := beta⁻¹

/-- Accumulated imposed strain `A(t)=∫₀ᵗ a(τ)dτ`. -/
def strainAccum (a : ℝ → ℝ) (t : ℝ) : ℝ := ∫ τ in 0..t, a τ

/-- Squared distinguished material radius `(s-1)/β`. -/
def materialRadiusSq (s beta : ℝ) : ℝ := (s - 1) / beta

/-- Distributed one-mode circulation enclosed by radius `r`. -/
def distributedCirculation (circ s beta r : ℝ) : ℝ :=
  circ * regLowerGamma s (scaledX beta r)

/-- Distributed one-mode swirl, defined on the punctured radial domain. -/
def distributedSwirl (circ s beta r : ℝ) : ℝ :=
  circ / (2 * Real.pi * r) * regLowerGamma s (scaledX beta r)

/-- Gamma-shaped axial-vorticity kernel, excluding dimensional prefactors. -/
def vorticityShape (s x : ℝ) : ℝ := x ^ (s - 1) * Real.exp (-x)

/-- Single distributed-mode axial vorticity. -/
def distributedVorticity (circ s beta r : ℝ) : ℝ :=
  circ * beta / (Real.pi * gammaFn s) * vorticityShape s (scaledX beta r)

@[simp] theorem scaledX_zero_radius (beta : ℝ) : scaledX beta 0 = 0 := by
  simp [scaledX]

@[simp] theorem distributedCirculation_zero_radius (circ s beta : ℝ) :
    distributedCirculation circ s beta 0 = 0 := by
  simp [distributedCirculation]

/-- Algebraic identity behind `r_*²=(s-1)/β`. -/
theorem scaledX_materialRadiusSq {s beta : ℝ} (hbeta : beta ≠ 0) :
    beta * materialRadiusSq s beta = s - 1 := by
  unfold materialRadiusSq
  field_simp [hbeta]

end

end KiknadzeKrasnov
