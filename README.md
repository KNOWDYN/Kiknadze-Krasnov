# Kiknadze–Krasnov formalisation

Lean 4 and Mathlib certificates for the mathematical results of *Exact Material Circulation Surface in an Unsteady Viscous Vortex*.

The principal certificate is `KiknadzeKrasnov.exactMaterialCirculationSurface`: for the annular source branch, the distinguished cylinder is material, is the one-mode vorticity-magnitude maximum, and has zero viscous circulation transfer. The development also verifies the scalar axisymmetric Navier–Stokes residuals, finite-mode qualifications, physical moment and enstrophy integrals, classical limits, and finite-time scale asymptotics.

Read [the reviewer guide](docs/REVIEWER_GUIDE.md) for theorem entry points and hypotheses, [the coverage ledger](docs/coverage.csv) for source traceability, and [the source specification](docs/SOURCE_SPEC.md) for the certification boundary. [Manuscript notes](docs/MANUSCRIPT_NOTES.md) record the pressure correction and sign/domain qualifications.

## Reproduce the checks

Install [elan](https://github.com/leanprover/elan), then run from the repository root:

```sh
lake exe cache get
lake build
lake env lean scripts/TrustAudit.lean
python3 scripts/check_coverage.py
```

`lean-toolchain`, `lakefile.lean`, and `lake-manifest.json` pin Lean and all dependencies. CI runs these same checks. The trust audit rejects proof dependencies other than Lean's standard `propext`, `Classical.choice`, and `Quot.sound`, including any placeholder or project-specific axiom.

This is a certificate for the specified KK family under its stated physical premises. The cylindrical governing equations are adopted model premises; the central line's distributional vorticity, the cited Bessel kernel, applications, and a global finite-energy Navier–Stokes regularity theorem are outside this certificate.
