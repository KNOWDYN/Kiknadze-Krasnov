# v1.1.0 release preparation

This document records the journal-neutral release procedure for the additive selective-conservation extension of the Kiknadze–Krasnov formal development.

## Release intent

Version `v1.1.0` extends the frozen `v1.0.0` baseline without changing its historical manuscript source ledger.

The release adds:

- `KiknadzeKrasnov/SelectiveConservation.lean`;
- the exact scaled-offset integrating-factor result;
- the exact exponential scaled-offset evolution law;
- the strict contraction-factor theorem when the diffusive clock advances;
- the sign-safe selective circulation-transfer partition;
- scale independence of the distinguished enclosed-circulation fraction;
- the assembled `selectiveMaterialConservation` theorem;
- journal-neutral scope and reviewer documentation for the new layer.

The package version in `lakefile.lean` is `1.1.0`.

## Verification commands

Run from a clean checkout of the exact commit that will be tagged:

```sh
lake exe cache get
lake build
lake env lean scripts/TrustAudit.lean
python3 scripts/check_coverage.py
```

The GitHub Actions workflow additionally rejects `sorry` and `admit` placeholders in project Lean files.

The existing coverage checker intentionally preserves the frozen v1.0.0 source inventory of 206 mathematical displays and 37 consequential prose claims. The additive v1.1.0 theorem layer is mapped separately in [`SELECTIVE_CONSERVATION.md`](SELECTIVE_CONSERVATION.md).

## Pre-tag checklist

Do not create the `v1.1.0` tag until all of the following are true:

- [ ] the release-preparation pull request has been reviewed and merged into `main`;
- [ ] `main` contains no current journal-specific naming or submission-specific status files;
- [ ] the package version is `1.1.0`;
- [ ] `KiknadzeKrasnov.lean` imports `SelectiveConservation.lean`;
- [ ] the GitHub Actions `Lean` workflow is green on the exact `main` commit to be tagged;
- [ ] the exact release commit SHA has been recorded outside the repository before tagging;
- [ ] the release notes below have been checked against the final commit;
- [ ] any obsolete merged development branches have been deleted if no longer needed.

## Recommended tag

Create an **annotated** tag named:

```text
v1.1.0
```

pointing to the exact verified `main` commit.

Recommended tag message:

```text
Kiknadze–Krasnov formal verification v1.1.0: selective material-circulation extension
```

## Recommended GitHub release title

```text
Kiknadze–Krasnov Formal Verification v1.1.0 — Selective Material-Circulation Extension
```

## Recommended GitHub release description

```markdown
# Formal Verification v1.1.0

This is an additive release of the Lean 4 / Mathlib formal verification development for the Kiknadze–Krasnov vortex family.

## New in v1.1.0

The release adds the selective material-circulation layer in `KiknadzeKrasnov/SelectiveConservation.lean`, including formal certificates for:

- the scaled displacement from the distinguished coordinate `x_* = s - 1`;
- the accumulated diffusive clock `B(t) = ∫ 4 ν β(τ) dτ`;
- the integrating-factor invariant for the exact scaled material-coordinate law;
- exact exponential evolution of the offset from `x_*`;
- strict contraction of the offset whenever the diffusive clock advances;
- the sign-safe circulation-transfer partition across `x_*`;
- scale independence of the distinguished enclosed-circulation fraction;
- the assembled `selectiveMaterialConservation` theorem.

## Relationship to v1.0.0

The `v1.0.0` release remains the frozen formal baseline for the earlier material-cylinder development. Version `v1.1.0` is additive and does not alter the historical 206-display / 37-prose-claim source ledger associated with that release.

The selective-conservation theorem map and assumptions are documented in `docs/SELECTIVE_CONSERVATION.md`.

## Verification

The release is built with the pinned Lean and Mathlib versions committed in the repository.

The release commit must pass:

- `lake build`;
- rejection of `sorry` and `admit` placeholders;
- the transitive proof-trust audit;
- the frozen-baseline source-coverage audit.

The trust audit permits only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` dependencies and rejects project-specific axioms.

## Scope

The formal certificates concern the exact Kiknadze–Krasnov family under explicit premises. They do not claim empirical identification of a source-bearing laboratory realization, equivalence to a variational active-transport barrier, a universal distinct-scale multimode common zero-flux surface, finite-energy whole-space Navier–Stokes regularity, or zero passive-scalar flux from the circulation condition alone.

Experimental interpretation is documented separately in `docs/EXPERIMENTAL_SCOPE.md` and is not part of the Lean proof premises.
```

## Post-release check

After publishing the GitHub release:

1. confirm that `v1.1.0` resolves to the intended verified commit;
2. confirm that the automatically generated source archives contain `SelectiveConservation.lean` and report package version `1.1.0`;
3. verify that the README badge and release links render correctly;
4. preserve `v1.0.0` unchanged as the historical baseline.
