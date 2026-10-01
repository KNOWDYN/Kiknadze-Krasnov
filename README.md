<div align="center">

# A Zero-Flux Material Cylinder in the Unsteady Kiknadze–Krasnov Vortex

**Lean 4 / Mathlib formal verification companion**

[![Lean](https://img.shields.io/badge/Lean-4.34.0--rc2-0C6BFF)
![Lean CI](https://github.com/KNOWDYN/Kiknadze-Krasnov/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/KNOWDYN/Kiknadze-Krasnov/actions/workflows/lean.yml)
![Mathlib](https://img.shields.io/badge/Mathlib-pinned%20%408d52ea9-2F74C0)
![Package](https://img.shields.io/badge/package-v1.0.0-4C566A)
![Proof trust](https://img.shields.io/badge/proof%20trust-audited-brightgreen)
![Coverage](https://img.shields.io/badge/source%20coverage-206%20displays%20%2B%2037%20claims-brightgreen)
![Status](https://img.shields.io/badge/status-reviewer--ready-brightgreen)

Formal certificates for the mathematical results of the final manuscript and Supplementary Material.

</div>

---

## Principal certificate

`KiknadzeKrasnov.exactMaterialCirculationSurface` certifies the central single-mode result on the annular source branch: the distinguished cylinder is transported by the KK radial velocity, is the one-mode **vorticity-magnitude maximum**, has **zero viscous circulation transfer**, and encloses the fixed profile fraction `Γ P(s, s − 1)`.

The development also certifies the actual scalar axisymmetric Navier–Stokes residuals, finite-mode angular-momentum and vorticity transport, physical moments and enstrophy, global one-mode swirl-magnitude extrema, Lagrangian trajectories, classical limits, and the finite-time radial-scale classification.

## Certification map

| Layer | What is certified | Reviewer entry point |
|---|---|---|
| Principal surface | Materiality, no crossing, vorticity-magnitude peak, zero circulation transfer | `PrincipalSurface.lean` |
| Navier–Stokes | Continuity and all three momentum residuals for the actual fields | `NavierStokesCertificate.lean` |
| Pressure | Exact pressure derivatives and corrected near-axis coefficient with optional line circulation | `PressureAsymptotics.lean` |
| Multimode field | Finite superposition, equal-scale reduction, distinct-scale qualification | `MultimodeCertificate.lean` |
| Physical integrals | Gamma moments, enstrophy and sharp convergence threshold | `PhysicalIntegrals.lean`, `EnstrophyConvergence.lean` |
| Classical limits | Oseen, Burgers, steady source–strain and regular-axis heat transform | `ClassicalLimits.lean`, `HeatTransform.lean` |
| Finite-time scale | Exact inverse scale and all singular-strain endpoint regimes | `FiniteTimeAsymptotics.lean`, `TerminalCollapse.lean` |

For the complete theorem-to-source map, see the [reviewer guide](docs/REVIEWER_GUIDE.md), [coverage ledger](docs/coverage.csv), and [claim coverage](docs/claim-coverage.csv).

## Final source provenance

The release candidate is reconciled against the final reviewed PDFs titled **A Zero-Flux Material Cylinder in the Unsteady Kiknadze–Krasnov Vortex**.

| Artifact | SHA-256 |
|---|---|
| Manuscript v3, 30 pages | `153c7cff9d0418015ec7b8375bc4ee0559ef70d66405051ee1ef406086b31bdc` |
| Supplementary Material v3, 10 pages | `5a3ac52605ca0deeafc4f8f9614f54abb2d1db69de98d0b374b799a0cced1372` |

The original TeX source archive and equation fingerprints remain frozen as the formal source ledger. The final PDFs incorporate the audited near-axis pressure correction and the sign-safe vorticity/swirl terminology already certified by Lean. See [SOURCE_SPEC.md](docs/SOURCE_SPEC.md) and [FINAL_RELEASE_AUDIT.md](docs/FINAL_RELEASE_AUDIT.md).

## Reproduce the certificate

Install [elan](https://github.com/leanprover/elan), then run from the repository root:

```sh
lake exe cache get
lake build
lake env lean scripts/TrustAudit.lean
python3 scripts/check_coverage.py
```

The repository pins Lean and Mathlib through `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json`. CI executes the same build, placeholder rejection, transitive trust audit, and source-coverage check.

### Trust boundary

The trust audit rejects `sorryAx` and any project-specific axiom. The only permitted transitive proof dependencies are Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

This certificate is intentionally scoped to the stated KK family and physical premises. It does **not** claim a finite-energy whole-space Navier–Stokes regularity result, equivalence to a variational active-transport barrier, a universal distinct-scale multimode zero-flux surface, or zero passive-scalar flux from the circulation condition alone.

---

<div align="center">

**206 mathematical display blocks · 37 consequential prose claims · zero proof placeholders · transitive trust audited**

</div>
