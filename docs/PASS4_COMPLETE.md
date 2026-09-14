# PASS 4 COMPLETE — Vorticity, Extrema, Enstrophy and Lagrangian Freeze

This file marks completion of Pass 4. **The commit containing this file is the Pass-4 freeze commit.** The layer below extends the frozen Pass-3 field verification without changing any frozen Pass-1 source interpretation or modifying any Pass-3 Lean source module.

## Toolchain and dependency freeze

- Lean: `leanprover/lean4:v4.34.0-rc2`
- Mathlib: `8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a`
- dependency resolution remains frozen by the committed `lake-manifest.json`
- CI sequence: `lake update`, `lake exe cache get`, `lake build`, followed by rejection of `sorry` and `admit` in the project Lean sources

## Pass-4 modules

Pass 4 adds the following machine-checked modules:

- `KiknadzeKrasnov/VorticityAnalysis.lean`
- `KiknadzeKrasnov/GammaMoments.lean`
- `KiknadzeKrasnov/VorticityTransport.lean`
- `KiknadzeKrasnov/SwirlExtrema.lean`
- `KiknadzeKrasnov/Enstrophy.lean`
- `KiknadzeKrasnov/Trajectories.lean`

`KiknadzeKrasnov.lean` imports the complete frozen Pass-3 layer and all six modules above.

## Machine-checked Pass-4 results

The frozen Pass-4 layer certifies the following results required by the manuscript before the principal material-surface theorem.

1. **Vorticity-shape extrema.** On positive scaled radius, the one-mode shape `x^(s-1) exp(-x)` has its exact factored derivative. For `s>1`, the derivative is positive before `x=s-1`, negative after it, and zero at it. The resulting positive-radius extremum is therefore the unique strict global peak of the positive shape. In physical radius, `r_omega=sqrt((s-1)/beta)` maps exactly to `scaledX=s-1`, and the one-mode vorticity derivative vanishes there.
2. **Sign-safe peak statement.** For arbitrary nonzero circulation sign, Pass 4 proves the strict global positive-radius maximum of `|omega_z|`, not an incorrectly sign-independent maximum of signed vorticity. The exact signed value at the peak is also retained. No undocumented `circ>0` restriction is introduced.
3. **Gamma moments and characteristic radii.** The gamma-density moment integral is evaluated exactly, giving `⟨r^(2n)⟩=beta^(-n) Gamma(s+n)/Gamma(s)`, `⟨r²⟩=s/beta`, `Var(r²)=s/beta²`, and `r_rms=sqrt(s/beta)`. Fraction radii map exactly back to their prescribed scaled radius, and the peak-vorticity cylinder encloses the fraction `P(s,s-1)`.
4. **Axial-vorticity transport, manuscript Eq. (80).** The vorticity transport equation is obtained algebraically from the differentiated angular-momentum equation on the punctured domain. Independently, the one-mode scaled residual is proved to vanish under exactly the scale Riccati law and source/profile compatibility `q=2 nu (s-1)`; the project `shape` definition supplies this compatibility without an added assumption.
5. **One-mode swirl extremum, manuscript Eqs. (91)–(92).** The exact radial derivative of the one-mode swirl is certified for `r>0`. For nonzero circulation, stationarity is equivalent to the regularised incomplete-gamma condition, and that condition is proved equivalent to the manuscript equation `2 x^s exp(-x)=lowerGamma(s,x)`. The threshold statement `s>1/2 ↔ 2s-1>0` is kept explicit. The formalisation does not turn the manuscript's sign-sensitive phrase “positive interior maximum” into an unconditional signed maximum claim.
6. **Finite-mode extremum relation, manuscript Eq. (94).** The radial derivative of the complete finite-mode enclosed circulation is proved to be `2 pi r omega_z`; the derivative of the complete finite-mode swirl, including central line circulation, is then certified. At positive radius, zero swirl derivative is equivalent exactly to `2 pi r² omega_z = Gamma(r,t)`. No uniqueness claim is made for multimode extrema.
7. **Enstrophy, manuscript Eqs. (95)–(98).** Enstrophy per unit axial length is represented by the manuscript integral. The pairwise gamma integral is evaluated for `s>1/2`; near-axis power integrability is proved equivalent to that same threshold. The reduced pair integral gives the exact `(i,j)` term of the multimode closed formula, the finite double sum gives Eq. (96), its diagonal reduces to the single-mode Eq. (97), and the Riccati scale law gives `Zdot=(a-4 nu beta) Z` as Eq. (98).
8. **Exact Lagrangian trajectories, manuscript Eqs. (100)–(102).** The squared-radius closed form is proved to satisfy `D(r²)/Dt=-a r²+2q` and its initial value; the axial closed form is proved to satisfy `z'=a z+b` and its initial value; and the azimuthal integral differentiates to the exact angular rate at every regular endpoint where the integral hypotheses hold. The identity `u_theta/r = Gamma/(2 pi r²)` is restricted to the punctured domain, so no division-by-zero statement is hidden.

## Adversarial scope and traceability audit

The Pass-4 branch was compared directly with the Pass-3 freeze commit `473e991a4c2bbead3cd8fe40d29f0811acf8be52`. Before this documentation-only freeze marker, the branch changed only:

- the aggregate `KiknadzeKrasnov.lean`, by adding the six Pass-4 imports; and
- the six new Pass-4 modules listed above.

No frozen Pass-3 Lean source file was modified.

The semantic audit preserves the Pass-1 restrictions:

- arbitrary circulation sign remains permitted;
- peak vorticity is stated sign-independently through `|omega_z|` rather than by silently assuming positive circulation;
- the swirl-extremum condition is sign-neutral and no unconditional signed “positive maximum” is asserted;
- all formulas containing division by radius retain positive/nonzero-radius hypotheses;
- the central line circulation is not promoted to a classical off-axis vorticity contribution;
- no universal common material surface is asserted for distinct multimode scales;
- no variational transport-barrier equivalence, passive-scalar zero-flux implication, or global Navier–Stokes regularity claim is introduced.

The Pass-4 source files contain no project-defined `axiom`, no `sorry`, and no `admit` proof hole. The CI placeholder gate independently rejects `sorry` and `admit`.

## Scope boundary

Pass 4 deliberately stops before the material-surface section. It does **not** yet claim the manuscript's Eq. (103)+ scaled-radius material transport law, the invariant cylinder `scaledX=s-1`, the Lagrangian invariant, no-crossing/inside-outside result, zero viscous circulation transfer on the distinguished material cylinder, constancy of the enclosed circulation fraction, distinct/equal-scale multimode material-surface qualifications, classical limiting cases, or finite-time concentration/asymptotic results. Those remain subsequent passes.

The endpoint prose concerning the complete axis-limit classification of swirl/vorticity is not strengthened beyond the exact threshold/exponent and integrability statements certified here; no source endpoint limit is silently inferred from an algebraic exponent test.

## Verification

The Pass-4 pre-freeze code revision

`b11f40ace14890a9770eddd88a1f9563a27b29dc`

passed the complete GitHub Actions gate in workflow run `34886594451`:

- pinned Lean and Mathlib dependencies resolved successfully;
- `lake build` succeeded for the complete aggregate project;
- the explicit project-source rejection check for `sorry` and `admit` succeeded.

This freeze commit changes documentation only. It is accepted as the Pass-4 freeze only after the same CI workflow succeeds independently on the commit containing this file.

## Acceptance

**PASS 4: ACCEPTED AND FROZEN**, conditional only on the documentation-only freeze commit passing the same CI gate. Once that run is green, this statement is unconditional and the commit containing this file is the official Pass-4 freeze commit.
