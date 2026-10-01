# Source specification

Project: **Exact Material Circulation Surface in an Unsteady Viscous Vortex**  
Formal target: Lean 4 + Mathlib  
Repository: `KNOWDYN/Kiknadze-Krasnov`

## 1. Frozen source set

The formalisation is grounded in the supplied final-submission archive, not in retyped PDF equations.

- archive SHA-256: `c0e9f4c3d99a0d97f5f2d82b56187de50a0350260dde98dbaed3112e60d14b7b`
- `main.tex` SHA-256: `7a77240317464855e449baf2129e681b62ebfe5f73903ae76932229adea7cce4`
- `supplementary_material.tex` SHA-256: `f9f49be01bee360d72c60ca8f110206a7601b7eda454b4be85f6d90ac64de1c1`
- `references.bib` SHA-256: `48c59b2f7ffe0709370c88c873e0b727a93aaa5637188b5212353bee85b51708`

The archive contains 17 files: `main.tex`, `supplementary_material.tex`, `references.bib`, four manuscript tables, two supplementary tables, and eight vector-PDF figures.

Mathematical display inventory:

- `main.tex`: 154 `equation` environments + 5 `align` environments = **159 display blocks**
- `supplementary_material.tex`: 42 `equation` environments + 5 `align` environments = **47 display blocks**
- total = **206 display blocks**
- manuscript equation labels `eq:*` = **89**
- all manuscript labels (equations, sections, figures, tables) = **111**

Every display block is represented in the five sharded CSV files under `docs/equations/` (indexed by its `README.md`). Mathematically consequential prose assertions that are not uniquely represented by a display equation are represented in `docs/source-claims.csv`.

## 2. Certification boundary

The Lean development will certify the mathematical derivations made in the manuscript and supplementary material, subject to the physical/model premises explicitly adopted there.

### 2.1 Governing premises rather than proof targets

The following are treated as the physical/mathematical model supplied to the formalisation rather than novel conclusions to be independently derived from first principles:

1. incompressible Newtonian constitutive law;
2. constant density and viscosity;
3. incompressible Navier–Stokes equations;
4. the standard axisymmetric cylindrical-coordinate component form of those equations;
5. absence of non-conservative body force;
6. standard passive-scalar advection–diffusion equation when it appears in the discussion.

The project **will** prove that the stated KK fields satisfy the scalar axisymmetric equations under the paper's hypotheses. It will **not** attempt to formalise continuum mechanics from Cauchy's theorem or rederive cylindrical-coordinate differential operators from Euclidean differential geometry within this certificate.

### 2.2 External literature statements

Historical attribution and cited results are not certified merely because they are mentioned in the paper. In particular:

- the displayed Kambe heat-kernel formula is treated as a cited external representation; the manuscript's change-of-variables reduction to the radial heat equation is a proof target;
- the large-source local Burgers-layer limit attributed to Rajamanickam and Weiss is recorded as external unless independently derived in this source;
- equivalence to a variational active-transport barrier is explicitly **not** claimed by the paper and must not appear as a Lean theorem;
- bibliographic identifications such as “this is the Lamb–Oseen/Burgers vortex” will be represented by algebraic formula equivalence, not by formalising historical priority.

### 2.3 Distributional statements

The claim that a central line circulation corresponds distributionally to vorticity concentrated on the excluded axis is outside the core theorem set. The classical statement that its vorticity is zero for `r > 0` is in scope.

## 3. Canonical mathematical universe

The implementation must distinguish the following branches rather than hiding them behind one over-general theorem.

### Regular-axis branch

- `r ≥ 0`
- `q = 0`
- `GammaLine = 0`
- hence `s = 1`
- regular Gaussian distributed modes

### Punctured/source-bearing branch

- `r > 0`
- `q` may be nonzero
- `s = 1 + q/(2ν)`
- finite-circulation normalised profile requires `s > 0`
- the nontrivial annular material-surface theorem requires `s > 1`, equivalently `q > 0`

### Time interval

For a finite terminal time `T`, the basic pointwise solution interval is `0 < t < T`. The source assumes `a(t)` and `b(t)` are continuously differentiable on every compact subinterval of `[0,T)`. Terminal singular behaviour may occur as `t → T⁻`.

### Fixed parameters and coefficients

The canonical model hypotheses include

- `ρ > 0`
- `μ > 0`
- `ν = μ / ρ > 0`
- constant `q`
- constant `GammaLine`
- constant distributed circulations `Gamma_i`
- `beta_i(0) > 0`
- a finite number of distributed modes
- prescribed strain `a(t)` and axial translation `b(t)`

The fixed-profile construction must not silently permit time-dependent `q` or circulation amplitudes.

## 4. Lean naming discipline

The manuscript has notation collisions that are harmless on paper but must be removed in the formal development.

| Manuscript notation | Lean-side name | Reason |
|---|---|---|
| Cartesian `x` in `x=r cos θ` | `cartX` | avoids collision with scaled squared radius |
| scaled `x=βr²` | `scaledX` | principal dynamical variable |
| lower integration reference `r_*` in pressure integral | `rRef` | distinct from the later material radius |
| material radius `r_*` | `rStar` | headline surface |
| Euler gamma function `Γ(s)` | `gammaFn s` | avoids collision with circulation amplitudes |
| incomplete gamma / regularised `P(s,x)` | `regLowerGamma s x` or a project wrapper | the project wrapper is defined by its actual interval integral |
| accumulated strain `\mathcal A(t)` | `strainAccum t` | separate from dimensionless `A(τ)` used later |
| circulation `Γ` | `circ`, `circLine`, `circMode i` | sign must remain explicit |

No theorem name may use an overloaded manuscript symbol without a descriptive Lean identifier.

## 5. Formal theorem bundles

The equation and claim ledgers map every item into one of these bundles.

### F1 — Foundations and domains

Formal definitions and hypotheses for density, viscosity, time interval, regular/punctured radial domains, finite mode index set, and differentiability/positivity conditions. Prove the paper's regular-axis necessity statements and the whole-space kinetic-energy divergence claim for nonzero linear strain.

### F2 — Meridional flow

From axisymmetric continuity with the prescribed axial gradient, derive

- `u_z = a(t) z + b(t)`;
- `u_r = -a(t) r / 2 + q(t)/r`;
- radial source flux `2πq`.

### F3 — Angular momentum and KK profile

Formalise `L = r u_θ`, reduce the azimuthal equation to the radial angular-momentum advection–diffusion equation, introduce `scaledX = βr²`, and derive the separated equations.

The constancy of `q` must use an explicit nontrivial-profile hypothesis. “Non-trivial” will not be left as prose.

### F4 — Incomplete-gamma profile

Formalise the upper/lower incomplete-gamma construction and the regularised finite-circulation profile. Prove the derivative identities needed throughout the paper. The principal branch requires enough special-function infrastructure to certify, rather than assume, the derivative of `P(s,x)`.

### F5 — Scale dynamics

Prove

- `β' - aβ + 4νβ² = 0`;
- `h=1/β` gives `h' + a h = 4ν`;
- exact integrating-factor solution;
- exact `β(t)` formula;
- inverse-scale separation identity and preserved ordering.

### F6 — Pressure and Navier–Stokes residuals

Derive radial and axial pressure gradients, the pressure field up to a time-dependent reference, and prove the scalar continuity/radial/azimuthal/axial residuals vanish. The pressure integral lower bound will be called `rRef`, never `rStar`.

### F7 — Vorticity, circulation, gamma moments, extrema and enstrophy

Prove the distributed vorticity formula, vorticity transport equation, circulation formula, gamma-density representation, radial moments, characteristic radii, extrema equations, enstrophy convergence threshold and enstrophy evolution.

### F8 — Lagrangian trajectories

Prove the exact radial and axial trajectories and the azimuthal integral where its denominator is defined. For source/sink punctured trajectories, statements are restricted to intervals on which `r(t) > 0`.

### F9 — Principal material-surface theorem

This is the primary certified theorem family:

1. `scaledX = β r²` obeys `D scaledX / Dt = 4 ν β ((s-1)-scaledX)`;
2. for `s>1`, `scaledX=s-1` is invariant;
3. `rStar²=(s-1)/β=q/(2νβ)`;
4. `rStar` is transported by the radial fluid velocity;
5. `exp(strainAccum(t)) [r²-rStar²]` is a Lagrangian invariant;
6. inside/outside ordering is preserved;
7. the same radius is the unique positive extremum location of the one-mode vorticity profile;
8. the magnitude `|ω_z|` is maximal there for nonzero circulation;
9. material-loop circulation obeys `dΓ_m/dt = 2πν R ∂_R ω_z`;
10. the rate vanishes at `rStar`;
11. `ΓStar = Γ P(s,s-1)` is constant;
12. the transfer sign reverses across the surface, with orientation depending on `sign Γ`.

### F10 — Multimode qualification

Prove componentwise identities and the equal-scale reduction to a common radial profile. Do **not** assert a common material zero-flux surface for distinct scales. The total-vorticity zero is obtained from the summed derivative and requires separate materiality analysis.

### F11 — Classical limits

Algebraically certify the Oseen reduction, Burgers equilibrium, steady source–strain stagnation/peak coincidence, balance ratio, and multiscale convergence under constant positive strain. Formalise the transformation to the radial heat equation in the regular `q=0` branch.

### F12 — Finite-time scale analysis

Prove the finite accumulated-strain criterion, exact concentration diagnostic, and detailed singular-strain family asymptotics from the supplementary material:

- `0<p<1`;
- `p=1, 0<λ<1`;
- `p=1, λ=1`;
- `p=1, λ>1`;
- `p>1` endpoint asymptotic `β ~ a/(4ν)`.

The `p>1` statement is expected to be the highest-analysis-risk proof in the source.

## 6. Semantic audit findings that must be preserved, not silently repaired

### S1 — Signed vorticity versus vorticity magnitude

The source permits circulation coefficients of either sign but repeatedly calls `x=s-1` the “vorticity maximum”. For `Γ<0`, the signed vorticity has a minimum at that point while `|ω_z|` has its maximum there. The source itself later gives a magnitude formula with `|Γ|`.

Formalisation rule: prove the sign-independent statement for `|ω_z|`, and separately prove signed maximum/minimum according to `sign Γ`. Do not insert an undocumented `Γ>0` assumption into the main theorem.

### S2 — Maximum swirl wording

The manuscript says the azimuthal velocity has a positive interior maximum for `s>1/2`, while the supplementary parameter table refers to a maximum of `|u_θ|`. The sign of `u_θ` is controlled by the sign of circulation.

Formalisation rule: the canonical sign-independent theorem concerns `|u_θ|`; signed extrema are stated conditionally on circulation sign.

### S3 — “Approach” is not unconditional asymptotic convergence

The scaled-radius ODE always points trajectories toward `xStar`, and the sign of `x-xStar` is preserved. Actual convergence `x(t)→xStar` over an infinite interval additionally depends on the accumulated relaxation `∫4νβ dt`.

Formalisation rule: certify direction/no-crossing unconditionally; certify asymptotic convergence only under a sufficient integral-divergence hypothesis. Do not infer a stronger limit theorem from the prose.

### S4 — `r_*` notation collision

`r_*` is used once as an arbitrary lower radial reference in the pressure integral and later as the distinguished material radius. These are not the same object.

Formalisation rule: `rRef` and `rStar` are separate definitions.

### S5 — `x` notation collision

The Cartesian coordinate `x` in the coordinate introduction and the scaled squared radius `x=βr²` are distinct.

Formalisation rule: `cartX` versus `scaledX`.

### S6 — `Γ` notation overload

Euler's gamma function, incomplete gamma functions and circulations share glyphs.

Formalisation rule: use disjoint identifiers and types.

### S7 — Radial sink trajectories

For `q<0`, an exact squared-radius solution can reach zero; the punctured-domain solution is valid only before any such axis encounter.

Formalisation rule: trajectory theorems carry an explicit positivity/domain interval.

### S8 — Instantaneous stagnation radius

`r_s²(t)=2q/a(t)` only makes sense as a positive real radius under sign/nonzero conditions on `a(t)` and `q`.

Formalisation rule: separate algebraic ratio identity from existence of a positive stagnation cylinder.

## 7. Source statements intentionally not strengthened

The Lean project must not claim any of the following unless a later source or explicit user instruction adds them:

- solution of the global Navier–Stokes existence/smoothness problem;
- finite whole-space kinetic energy for the nonzero linear-strain KK field;
- equivalence of the material surface to a variational active transport barrier;
- a universal common zero-flux material surface for distinct multimode scales;
- zero passive-scalar/thermal flux merely because circulation flux vanishes;
- applicability to anatomical, plasma, atmospheric, combustion or fibre systems without their additional governing assumptions.

## 8. Source audit artefacts

- `docs/SOURCE_SPEC.md` — this frozen formal specification
- `docs/equations/part_01.csv` … `part_05.csv` — all 206 display blocks with source lines, labels, fingerprints, action and target bundle
- `docs/source-claims.csv` — mathematically consequential prose claims and restrictions not safely represented by display equations alone

These artefacts are the source audit inputs. A proof may refine theorem names or split a claim into smaller lemmas, but it must not silently delete, strengthen or weaken a source claim. Any intentional scope change must be recorded in the repository.

