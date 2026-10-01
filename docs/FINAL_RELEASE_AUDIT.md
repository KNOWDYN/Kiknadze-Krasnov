# Final release audit

Date: **2026-10-01**  
Project: **A Zero-Flux Material Cylinder in the Unsteady Kiknadze–Krasnov Vortex**  
Release target: **v1.0.0**

## Final reviewed artifacts

| Artifact | Pages | SHA-256 |
|---|---:|---|
| Manuscript v3 | 30 | `153c7cff9d0418015ec7b8375bc4ee0559ef70d66405051ee1ef406086b31bdc` |
| Supplementary Material v3 | 10 | `5a3ac52605ca0deeafc4f8f9614f54abb2d1db69de98d0b374b799a0cced1372` |

The PDFs are not redistributed by this repository. These hashes identify the exact final artifacts used for the release reconciliation.

## Cross-check result

The final manuscript and Supplementary Material were checked against the completed Lean development and against each other. No new mathematical development was required.

Confirmed:

1. The manuscript and Supplementary Material use the same final title and KK notation.
2. Manuscript Eq. (60) now gives the combined near-axis pressure scaled limit `lim_(r→0+) r²p = −(ρ/2)[q² + Γ_ℓ²/(4π²)]`, matching `PressureAsymptotics.lean`.
3. Sign-independent vorticity statements now use the maximum of `|ω_z|`; signed maximum/minimum statements are conditioned on circulation sign.
4. Sign-independent swirl statements now use the maximum of `|u_θ|`; signed maximum/minimum statements are conditioned on circulation sign.
5. The introductory text before manuscript Eq. (75) correctly identifies the displayed quantities as profile derivatives.
6. The Supplementary Material glossary, parameter-domain table, material-surface derivation and multimode qualification use terminology consistent with the manuscript.
7. The distinct-scale multimode restriction remains explicit: componentwise material cylinders do not imply a universal common total-field zero-flux surface.
8. The finite-time asymptotic regimes remain unchanged and consistent with the certified endpoint theorems.
9. Passive-scalar flux, finite whole-space energy and variational active-transport-barrier claims remain correctly outside the principal theorem.
10. No equation or theorem correction was required in the Lean source during this final release audit.

## Formal source coverage

The frozen formal inventory remains:

- **206** mathematical display blocks;
- **37** consequential prose claims;
- all proof/definition obligations mapped to Lean entry points or explicit scope classifications.

The original TeX archive hashes and line-indexed equation fingerprints remain preserved in [SOURCE_SPEC.md](SOURCE_SPEC.md). The final reviewed PDF hashes above form the release-level presentation provenance.

## Trust and CI gate

The release gate is the repository workflow:

```sh
lake exe cache get
lake build
lake env lean scripts/TrustAudit.lean
python3 scripts/check_coverage.py
```

The workflow rejects `sorry`/`admit`, audits transitive proof trust, and verifies the complete source mapping.

## Release procedure

This audit records the documentation-only release-hygiene pass. No theorem source is modified here.

The author manually reviews and merges the release-hygiene pull request. The immutable `v1.0.0` tag must point to that merged `main` commit, after CI passes on the merge commit.
