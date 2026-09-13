# PASS 2 COMPLETE — Lean Foundation Freeze

This file marks completion of Pass 2. **The commit containing this file is the Pass-2 freeze commit.** The foundation below extends the frozen Pass-1 specification without changing its mathematical scope or source interpretation.

## Toolchain and dependency freeze

- Lean: `leanprover/lean4:v4.34.0-rc2`
- Mathlib: `8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a`
- dependency resolution frozen by the committed `lake-manifest.json`
- CI sequence: `lake update`, `lake exe cache get`, `lake build`, followed by rejection of any `sorry` or `admit` in the project Lean sources

## Frozen foundation modules

- `KiknadzeKrasnov/Parameters.lean`: `FluidParams`, positivity and non-vanishing facts, the incomplete-gamma shape parameter, and the finite-circulation and annular-source branch predicates and equivalences.
- `KiknadzeKrasnov/Domains.lean`: regular and punctured radial domains, the half-open physical time domain `[0,T)`, interior time, admissible prescribed histories and scale positivity.
- `KiknadzeKrasnov/SpecialFunctions.lean`: collision-free gamma notation, lower and regularised incomplete-gamma definitions, continuity and integrability infrastructure, and machine-checked derivative identities.
- `KiknadzeKrasnov/Model.lean`: the finite-mode frozen-data `KKModel` and its regular-axis, finite-circulation and annular-source branches.
- `KiknadzeKrasnov/Kinematics.lean`: canonical definitions for radial and axial velocity, angular momentum, `scaledX`, inverse scale, accumulated strain, distributed circulation, swirl, vorticity and material-radius square.
- `KiknadzeKrasnov.lean`: aggregate library import for the complete Pass-2 foundation.

## Machine-checked foundation facts

The frozen foundation proves, rather than merely records, the following results needed downstream:

1. `ν = μ/ρ > 0`, hence the relevant denominators are nonzero.
2. `s = 1 + q/(2ν)`, with `s > 1 ↔ q > 0` and `s > 0 ↔ q > -2ν`.
3. The regular branch `q = 0` has `s = 1`.
4. `Γ(s) > 0` for `s > 0`, with the corresponding non-vanishing result.
5. The lower incomplete gamma and its regularised form vanish at zero.
6. The real gamma kernel is continuous for positive arguments and interval-integrable from zero when `s > 0`.
7. For `s > 0` and `x > 0`,
   `d/dx regLowerGamma s x = x^(s-1) exp(-x) / gammaFn s`.
   This derivative is derived from the interval-integral definition and the fundamental theorem of calculus; it is not postulated as an axiom.
8. For `beta ≠ 0`, `beta * materialRadiusSq s beta = s - 1`.
9. The zero-radius distributed-circulation identity is established in the common kinematic layer.

## Traceability and scope boundary

Pass 2 fixes the Lean objects, domains, names and elementary analytic infrastructure needed by the twelve theorem bundles frozen in Pass 1. It does **not** claim completion of the downstream derivations for meridional flow, angular-momentum reduction, scale dynamics, pressure and Navier–Stokes residuals, vorticity/extrema/enstrophy, Lagrangian trajectories, the principal material-surface theorem, multimode qualification, classical limits or finite-time asymptotics. Those remain later proof targets.

No additional sign restriction on circulation has been introduced. Frozen coefficients such as `q`, the line circulation and distributed mode circulations remain time-independent. The Pass-1 distinction between regular-axis and punctured/source-bearing branches is preserved. None of the claims explicitly excluded at Pass 1 is promoted by this foundation.

## Verification

The Pass-2 acceptance gate is:

- `lake build` succeeds for the aggregate project against the pinned Lean and Mathlib revisions;
- the project Lean sources contain no `sorry` or `admit` proof placeholders.

The final code revision immediately preceding this freeze marker passed both checks. The freeze commit changes documentation only and is accepted as the Pass-2 freeze only after the same CI workflow succeeds on this commit.

## Acceptance

**PASS 2: ACCEPTED AND FROZEN.**

Pass 3 may begin from this foundation without altering the Pass-1 source interpretation unless a later change of scope is explicitly documented.
