# PASS 5 COMPLETE — Principal Material Circulation Surface Freeze

This file marks completion of Pass 5. **The commit containing this file is the Pass-5 freeze commit.** The layer extends the frozen Pass-4 vorticity/Lagrangian development without modifying any frozen Pass-4 Lean source module or changing the Pass-1 source interpretation.

## Toolchain and dependency freeze

- Lean: `leanprover/lean4:v4.34.0-rc2`
- Mathlib: `8d52ea9a145a9255c4d301c0d1a1b8bf6e59305a`
- dependency resolution remains frozen by the committed `lake-manifest.json`
- CI sequence: `lake update`, `lake exe cache get`, `lake build`, followed by explicit rejection of `sorry` and `admit` in project Lean sources

## Pass-5 modules

Pass 5 adds:

- `KiknadzeKrasnov/MaterialSurface.lean`
- `KiknadzeKrasnov/CirculationSurface.lean`
- `KiknadzeKrasnov/MaterialSurfaceTheorem.lean`

`KiknadzeKrasnov.lean` imports the complete frozen Pass-4 layer and these three modules.

## Machine-checked principal theorem family

The frozen Pass-5 layer certifies the manuscript's F9 principal material-surface theorem family.

1. **Scaled material-radius transport.** For `x=beta*r^2`, the material derivative is exactly `4*nu*beta*((s-1)-x)` under the scale Riccati law and `q=2*nu*(s-1)`. The rate is positive below `s-1`, negative above it, and zero at it.
2. **Distinguished physical radius.** `materialRadiusSq s beta=(s-1)/beta`; the source-form bridge additionally proves `(s-1)/beta=q/(2*nu*beta)` when the required nonzero denominators and source/profile compatibility hold. For `s>1`, `beta>0`, the physical radius is positive and maps exactly to `scaledX=s-1`.
3. **Material motion.** The squared distinguished radius satisfies `d(rStar^2)/dt=-a*rStar^2+2q`, and the positive physical radius satisfies `drStar/dt=radialVelocity a q rStar`.
4. **Exact radial invariant and no crossing.** `exp(strainAccum a t) * [r^2-rStar^2]` has zero derivative and is globally constant under the stated differentiability hypotheses. A trajectory initially on the distinguished cylinder remains on it; a trajectory initially away from it cannot cross it. Both positive and negative offset signs are preserved, so outside/inside ordering is certified explicitly.
5. **Coincidence with the one-mode vorticity extremum.** `materialRadius=vorticityPeakRadius`. The vorticity derivative vanishes there. For arbitrary nonzero circulation sign, `|omega_z|` has its unique positive-radius maximum there. For positive circulation this is the signed maximum; for negative circulation it is the signed minimum. No hidden `circ>0` assumption is used in the sign-independent theorem.
6. **Material-loop circulation.** With `Gamma_m=Gamma*P(s,x_R)`, differentiation along a material scaled-radius history gives the exact manuscript rate proportional to `x_R^(s-1) exp(-x_R) [(s-1)-x_R]`.
7. **Viscous circulation transfer.** The algebraic identity `L_rr-L_r/r=r*omega_r` is certified on `r≠0`, and the explicit one-mode material circulation rate is proved equal to `2*pi*nu*r*partial_r omega_z` on positive radius.
8. **Zero-flux material cylinder.** Both the explicit circulation-rate expression and the viscous-transfer expression vanish at the physical material radius. The enclosed circulation is exactly `Gamma*P(s,s-1)`, and for nonzero distributed circulation its fraction is exactly `P(s,s-1)`.
9. **Transfer orientation.** For positive circulation, the material circulation rate is positive inside and negative outside `x=s-1`; for negative circulation both signs reverse. Thus the sign change across the surface is formalised without privileging one circulation orientation.

## Equation traceability audit

The canonical main-manuscript material-surface sequence is completely accounted for.

| Source item | Formal representation |
|---|---|
| M103, `x=beta r^2` | `scaledX` in `Kinematics.lean` |
| M104, product material derivative | product differentiation inside `scaledMaterial_hasDerivAt` |
| M105, scale and squared-radius laws | `scaleResidual_zero_iff`; `radialSq_particle_hasDerivAt` |
| M106, `Dx/Dt=4 nu beta[(s-1)-x]` | `scaledMaterial_hasDerivAt` |
| M107, `xStar=s-1` | distinguished value used explicitly by `scaledMaterial_hasDerivAt_zero_at_star` and the invariant theorems |
| M108, `hDot+a h=4 nu` | `inverseScale_ode` |
| M109, `rStar^2=(s-1)/beta=q/(2 nu beta)` | `materialRadiusSq`; `materialRadiusSq_eq_source_form` |
| M110, squared-radius material motion | `materialRadiusSq_history_hasDerivAt` |
| M111, `drStar/dt=u_r(rStar,t)` | `materialRadius_history_hasDerivAt` |
| M112, radial integrating-factor invariant | `radialInvariant_hasDerivAt_zero`; `radialInvariant_eq`; no-crossing and sign-preservation theorems |
| M113, one-mode vorticity formula | frozen Pass-4 `distributedVorticity` definition/results, reused without modification |
| M114, radial vorticity derivative | frozen Pass-4 `distributedVorticity_hasDerivAt_r`, reused without modification |
| M115, `rStar=rOmega` | `materialRadius_eq_vorticityPeakRadius` plus direct magnitude/signed extremum bridge theorems |
| M116, `x_R=beta R^2` | `scaledX`; `scaledX_materialRadius` for the distinguished cylinder |
| M117, `Gamma_m=Gamma P(s,x_R)` | `materialCirculationFromX` |
| M118, `P_x=x^(s-1)e^-x/Gamma(s)` | frozen special-function derivative theorem `regLowerGamma_hasDerivAt` |
| M119, explicit `dGamma_m/dt` | `materialCirculationFromX_hasDerivAt` and `materialCirculationRate` |

The closing F9 consequences are also explicit rather than left as prose:

- M120: `angularMomentumDiffusionTerm_eq_r_vorticityGradient`;
- M121: `materialCirculationRate_eq_viscousFlux`;
- M122: `materialCirculation_hasDerivAt_zero_at_star`, `materialCirculationRate_zero_at_materialRadius`, `viscousCirculationFlux_zero_at_materialRadius`, and `materialCirculation_at_star`;
- M123: `materialCirculation_fraction_at_star`.

## Adversarial semantic audit

The Pass-1 claims C015–C020 were checked against the theorem statements.

- The scaled-radius ODE gives direction toward `s-1` and exact no-crossing. It is **not** promoted to unconditional asymptotic convergence; no limit `x(t)→s-1` is asserted without an additional accumulated-relaxation hypothesis.
- The material-radius theorem uses the `s>1`, positive-scale source-bearing branch where a positive physical cylinder exists.
- Inside and outside signs are both preserved explicitly.
- Vorticity coincidence is sign-safe: arbitrary nonzero circulation uses the maximum of `|omega_z|`; signed maximum/minimum are separated by circulation sign.
- Material circulation transfer is sign-aware on both sides of the cylinder.
- The conserved fraction `P(s,s-1)` contains no dependence on strain history or initial scale once `s` and the distributed circulation are fixed.
- No equivalence to a variational transport barrier is asserted.
- No passive-scalar or thermal zero-flux claim is inferred from zero circulation flux.
- No common zero-flux material surface is asserted for distinct multimode scales.
- No global Navier-Stokes regularity claim is introduced.

## Structural audit and scope boundary

Relative to the frozen Pass-4 commit

`8fb9bb9ed95b937fa2cbd7e576dc65da2a0f445f`

the final pre-freeze Pass-5 code revision is ten commits ahead and zero behind. Before this documentation-only marker, the only changed paths were:

- `KiknadzeKrasnov.lean` — three new Pass-5 imports;
- `KiknadzeKrasnov/MaterialSurface.lean` — new;
- `KiknadzeKrasnov/CirculationSurface.lean` — new;
- `KiknadzeKrasnov/MaterialSurfaceTheorem.lean` — new.

No frozen Pass-4 Lean source module was modified.

Pass 5 deliberately stops before the manuscript's later steady-limit and multimode-qualification results beginning at M124 and the subsequent classical-limit/finite-time-scale sections. In particular, this pass does not assert a universal material zero-flux surface for distinct scales.

The Pass-5 Lean sources contain no project-defined `axiom`, no `sorry`, and no `admit`. The CI placeholder gate independently rejects `sorry` and `admit`.

## Verification

The Pass-5 pre-freeze code revision

`e80ae3164625f58e7323354b6de3e9d0c6dad156`

passed the complete GitHub Actions gate in workflow run `34907534212`:

- pinned Lean and Mathlib dependencies resolved successfully;
- `lake build` succeeded for the complete aggregate project;
- the explicit project-source rejection check for `sorry` and `admit` succeeded.

This freeze commit changes documentation only. It is accepted as the Pass-5 freeze only after the same CI workflow succeeds independently on the commit containing this file.

## Acceptance

**PASS 5: ACCEPTED AND FROZEN**, conditional only on the documentation-only freeze commit passing the same CI gate. Once that run is green, this statement is unconditional and the commit containing this file is the official Pass-5 freeze commit.
