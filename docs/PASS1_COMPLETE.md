# PASS 1 COMPLETE — Source-to-Formal-Specification Freeze

This file marks completion of Pass 1. **The commit containing this file is the Pass-1 freeze commit.** Subsequent formalisation work must remain traceable to the artefacts frozen here.

## Frozen source identity

- final-submission archive SHA-256: `c0e9f4c3d99a0d97f5f2d82b56187de50a0350260dde98dbaed3112e60d14b7b`
- `main.tex`: `7a77240317464855e449baf2129e681b62ebfe5f73903ae76932229adea7cce4`
- `supplementary_material.tex`: `f9f49be01bee360d72c60ca8f110206a7601b7eda454b4be85f6d90ac64de1c1`
- `references.bib`: `48c59b2f7ffe0709370c88c873e0b727a93aaa5637188b5212353bee85b51708`

## Completeness audit

- 159 mathematical display blocks from `main.tex`
- 47 mathematical display blocks from `supplementary_material.tex`
- **206/206 display blocks inventoried** in `docs/pass1_equation_ledger/part_01.csv` through `part_05.csv`
- **89/89 manuscript `eq:*` labels accounted for**
- **37 consequential prose claims/restrictions** registered in `docs/PASS1_claim_register.csv`
- formal certification boundary, hypotheses, naming discipline and twelve theorem bundles frozen in `docs/PASS1_SOURCE_SPEC.md`

## Formalisation-sensitive findings frozen at Pass 1

1. The source permits circulation of either sign. The sign-independent peak theorem must therefore concern `|ω_z|`; signed vorticity has a maximum for positive circulation and a minimum for negative circulation at the same radius.
2. The analogous swirl-extremum statement must distinguish signed velocity from `|u_θ|` rather than silently assuming positive circulation.
3. Direction toward `x*=s-1` and no-crossing follow directly from the scaled-radius equation; asymptotic convergence requires an additional accumulated-relaxation condition and will not be inferred from the word “approach”.
4. The pressure-integral reference radius and the later distinguished material radius share the printed symbol `r_*` but are different objects; Lean names are frozen as `rRef` and `rStar`.
5. Cartesian `x` and scaled `x=βr²` are distinct; Lean names are `cartX` and `scaledX`.
6. Euler/incomplete gamma functions and circulation amplitudes will use disjoint identifiers.
7. Sink trajectories on the punctured branch are only asserted on intervals for which `r(t)>0`.
8. A positive instantaneous stagnation radius from `r_s²=2q/a(t)` requires the appropriate nonzero/sign hypotheses.

## Scope safeguards

Pass 1 explicitly prevents later code from silently claiming: a Navier–Stokes Millennium-problem result; finite whole-space kinetic energy for nonzero linear strain; equivalence to a variational active-transport barrier; a universal material zero-flux surface for distinct multimode scales; zero passive-scalar flux from zero circulation flux; or unconditional applicability to physical systems whose additional governing equations are absent from the source.

## Acceptance

**PASS 1: ACCEPTED AND FROZEN.**

Pass 2 may now construct the Lean 4 + Mathlib foundations only from this frozen specification. Any later intentional change of mathematical scope or source interpretation must be documented rather than silently incorporated.
