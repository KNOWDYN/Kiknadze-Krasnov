<div align="center">

# Kiknadze–Krasnov Vortex

**Lean 4 / Mathlib formal verification and reproducibility companion**

[![Lean](https://img.shields.io/badge/Lean-4.34.0--rc2-0C6BFF)](lean-toolchain)
[![Lean CI](https://github.com/KNOWDYN/Kiknadze-Krasnov/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/KNOWDYN/Kiknadze-Krasnov/actions/workflows/lean.yml)
![Mathlib](https://img.shields.io/badge/Mathlib-pinned%20%408d52ea9-2F74C0)
![Package](https://img.shields.io/badge/package-v1.1.0-4C566A)
![Proof trust](https://img.shields.io/badge/proof%20trust-audited-brightgreen)
![Baseline coverage](https://img.shields.io/badge/baseline%20coverage-206%20displays%20%2B%2037%20claims-brightgreen)

Formal certificates for the Kiknadze–Krasnov vortex family and its selective material-circulation structure.

</div>

---

## Principal certificates

`KiknadzeKrasnov.exactMaterialCirculationSurface` certifies the central single-mode result on the annular source branch: the distinguished cylinder is transported by the KK radial velocity, is the one-mode **vorticity-magnitude maximum**, has **zero viscous circulation transfer**, and encloses the fixed profile fraction `Γ P(s, s − 1)`.

The v1.1.0 extension adds `KiknadzeKrasnov.selectiveMaterialConservation` and the supporting results in `KiknadzeKrasnov/SelectiveConservation.lean`. These certify the scaled material-coordinate dynamics, exact exponential evolution of the offset from `x_* = s - 1` in the accumulated diffusive clock, the sign-safe circulation-transfer partition, and scale independence of the distinguished enclosed-circulation fraction.

The development also certifies the scalar axisymmetric Navier–Stokes residuals for the actual KK fields, finite-mode angular-momentum and vorticity transport, physical moments and enstrophy, global one-mode swirl-magnitude extrema, Lagrangian trajectories, classical limits, and the finite-time radial-scale classification.

## Certification map

| Layer | What is certified | Reviewer entry point |
|---|---|---|
| Principal surface | Materiality, no crossing, vorticity-magnitude peak, zero circulation transfer | `PrincipalSurface.lean` |
| Selective conservation | Scaled-offset dynamics, exact exponential selection, signed transfer partition, distinguished-fraction scale independence | `SelectiveConservation.lean` |
| Navier–Stokes | Continuity and all three momentum residuals for the actual fields | `NavierStokesCertificate.lean` |
| Pressure | Exact pressure derivatives and corrected near-axis coefficient with optional line circulation | `PressureAsymptotics.lean` |
| Multimode field | Finite superposition, equal-scale reduction, distinct-scale qualification | `MultimodeCertificate.lean` |
| Physical integrals | Gamma moments, enstrophy and sharp convergence threshold | `PhysicalIntegrals.lean`, `EnstrophyConvergence.lean` |
| Classical limits | Oseen, Burgers, steady source–strain and regular-axis heat transform | `ClassicalLimits.lean`, `HeatTransform.lean` |
| Finite-time scale | Exact inverse scale and singular-strain endpoint regimes | `FiniteTimeAsymptotics.lean`, `TerminalCollapse.lean` |

For the selective-conservation theorem map and scope, see [`docs/SELECTIVE_CONSERVATION.md`](docs/SELECTIVE_CONSERVATION.md). For the broader proof map, see the [reviewer guide](docs/REVIEWER_GUIDE.md).

## Release history and provenance

### v1.0.0 baseline

The frozen `v1.0.0` release is the formal companion to **A Zero-Flux Material Cylinder in the Unsteady Kiknadze–Krasnov Vortex**. Its source ledger contains 206 mathematical display blocks and 37 consequential prose claims. The corresponding [coverage ledger](docs/coverage.csv), [claim coverage](docs/claim-coverage.csv), [source specification](docs/SOURCE_SPEC.md), and [final release audit](docs/FINAL_RELEASE_AUDIT.md) remain unchanged historical records.

The reviewed v1.0.0 publication artifacts are identified by SHA-256:

| Artifact | SHA-256 |
|---|---|
| Manuscript v3, 30 pages | `153c7cff9d0418015ec7b8375bc4ee0559ef70d66405051ee1ef406086b31bdc` |
| Supplementary Material v3, 10 pages | `5a3ac52605ca0deeafc4f8f9614f54abb2d1db69de98d0b374b799a0cced1372` |

### v1.1.0 selective-conservation extension

v1.1.0 is an additive formal extension. It does not replace the v1.0.0 source ledger or alter its historical coverage counts. The new theorem layer is mapped separately in [`docs/SELECTIVE_CONSERVATION.md`](docs/SELECTIVE_CONSERVATION.md), and the release procedure is recorded in [`docs/RELEASE_1_1_0.md`](docs/RELEASE_1_1_0.md).

Experimental observations are not Lean premises and are not formally certified. Their interpretation relative to the analytical theorem is summarized in [`docs/EXPERIMENTAL_SCOPE.md`](docs/EXPERIMENTAL_SCOPE.md).

## Reproduce the certificate

Install [elan](https://github.com/leanprover/elan), then run from the repository root:

```sh
lake exe cache get
lake build
lake env lean scripts/TrustAudit.lean
python3 scripts/check_coverage.py
```

The repository pins Lean and Mathlib through `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json`. CI executes the same build, proof-placeholder rejection, transitive trust audit, and frozen-baseline source-coverage check.

### Trust boundary

The trust audit walks every declaration in the imported `KiknadzeKrasnov` modules and rejects any project-specific axiom. The only permitted transitive proof dependencies are Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

The certificates are intentionally scoped to the stated KK family and explicit physical premises. They do **not** claim a finite-energy whole-space Navier–Stokes regularity result, equivalence to a variational active-transport barrier, a universal distinct-scale multimode zero-flux surface, empirical validity of a source-bearing laboratory realization, or zero passive-scalar flux from the circulation condition alone.

---

<div align="center">

**v1.1.0 release candidate · additive selective-conservation layer · zero proof placeholders · transitive trust audited by CI**

</div>
