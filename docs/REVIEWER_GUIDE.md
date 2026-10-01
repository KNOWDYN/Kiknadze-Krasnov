# Reviewer guide

All names below are in the `KiknadzeKrasnov` namespace. `KiknadzeKrasnov.lean` imports the complete development. The source inventory contains 206 mathematical displays and 37 consequential prose claims; [coverage.csv](coverage.csv) and [claim-coverage.csv](claim-coverage.csv) map each to its certificate or explicit scope classification. Inventory coverage does not mean that adopted model premises or cited external results have been independently proved.

## Principal results

| Result | Entry point | Principal hypotheses |
|---|---|---|
| Material cylinder, vorticity-magnitude peak, zero circulation transfer | `exactMaterialCirculationSurface` in `PrincipalSurface.lean` | Positive density/viscosity, source branch `s>1`, positive scale history, Riccati law; nonzero circulation for a nontrivial peak |
| Actual scalar Navier–Stokes residuals | `kk_exact_navier_stokes_certificate` in `NavierStokesCertificate.lean` | Differentiable imposed histories and scale; pressure primitive FTC; punctured radius |
| Actual finite-field angular momentum | `multimodeAngularMomentum_operator_zero` and derivative certificates in `MultimodeCertificate.lean` | Finite modes, common shape/source compatibility, individually positive scales obeying the same strain law |
| Actual vorticity transport | `actualVorticityTransportResidual_zero` and three derivative certificates in `VorticityCertificate.lean` | Positive scale and radius, source/shape compatibility, scale ODE |
| Physical radial moments and enstrophy | `physicalRadialEvenMoment_eq`, `physicalMultimodeEnstrophy_eq` in `PhysicalIntegrals.lean` | Shape `s>0` for moments, `s>1/2` for enstrophy; positive scales |
| Global one-mode swirl-magnitude maximum | `oneModeSwirl_magnitude_maximum` in `SwirlMaximum.lean` | Nonzero circulation, `s>1/2`, positive scale |
| Exact terminal classification | `FiniteTimeCriteria.lean`, `FiniteTimeAsymptotics.lean`, `SupercriticalEndpoint.lean`, `SingularFamilyDynamics.lean`, `TerminalCollapse.lean` | Positive viscosity, initial inverse scale, terminal time; singular-family parameters as stated |

## Reading the proof layers

`Parameters`, `Domains`, `Model`, and `Kinematics` give the physical hypotheses and collision-free notation. `MeridionalFlow` derives the affine axial and source-bearing radial fields. `AngularMomentum` reduces the actual azimuthal equation and certifies source constancy with a nonzero derivative witness.

`SpecialFunctions` defines lower gamma by its interval integral. `GammaProfile` certifies its derivatives. `GammaPrimitive` proves the general separated primitive and quantile existence; `FamilyClosure` identifies the complementary definition with the actual improper upper tail. `SourceCorrespondence` checks the original upper-gamma notation and the far-field coefficients.

`VorticityCore`, `MaterialSurface`, `CirculationSurface`, and `PrincipalSurface` assemble the headline theorem. The circulation sign stays explicit. No-crossing follows from an integrating-factor invariant; it is not advertised as unconditional convergence.

`ScaleDynamics`, `PressureField`, and `NavierStokesCertificate` verify the exact scale and pressure formulas against actual derivatives. `PressureAsymptotics` discharges the pressure primitive's FTC conditions for finite modes and certifies the corrected near-axis coefficient. `AxisRegularity` and `RegularAxisExpansion` treat the regular axis, including the finite-sum cubic remainder.

`GammaMoments` and `Enstrophy` give the analytic integral identities. `PhysicalIntegrals` supplies the change of variables from the manuscript's radial integrals, including integrability of all mixed enstrophy terms. `EnstrophyConvergence` proves the sharp kernel integrability threshold and differentiates the actual one-mode physical integral. `SwirlMaximum` proves existence before applying the stationary-radius equation. `MultimodeQualification` keeps the equal-scale reduction separate from distinct-scale component surfaces; `MultimodeCertificate` gives a distinct-scale counterexample to a common zero-flux surface.

`LagrangianTrajectories` differentiates all three trajectory formulas with their domain/FTC hypotheses. `ClassicalLimits` and `ClassicalProfiles` give algebraic Oseen/Burgers equivalences and constant-strain convergence. `HeatChainRule` certifies the actual transformed-profile chain rules; `HeatTransform` cancels their residual and proves finite-sum closure. The cited Bessel representation remains external.

`InverseScaleUniqueness` supplies initial-value uniqueness on connected open intervals. `FiniteTimeConsequences` proves that concentration requires unbounded accumulated strain. The finite-time proofs use literal filter limits. `SingularFamilyDynamics` checks that the explicit singular-family formulas solve the inverse-scale equation and have the prescribed initial value. `TerminalCollapse` transfers the endpoint coordinate to physical time and proves collapse in both critical branches. `SupercriticalEndpoint` derives the `p>1` endpoint integral balance from derivatives and exponential domination, using the proved comparison theorem in `EndpointRatio`; no asymptotic is added as an assumption.

`KineticEnergy` integrates the actual nonnegative kinetic-energy density over expanding annular cylinders. Its unbounded axial lower bound rules out finite whole-space energy for nonzero strain. `EnergyAndScalar` states the scalar-flux condition separately from circulation transfer.

## Trust and reproducibility

Run the four commands in the repository README using the committed toolchain and dependency lock. `scripts/TrustAudit.lean` walks transitive axiom dependencies of every project declaration and permits only `propext`, `Classical.choice`, and `Quot.sound`. It rejects `sorryAx` and any project-specific axiom. The coverage checker verifies the complete source inventory and that every documented certificate name exists. CI checks the same committed source.

The source archive itself is not redistributed in this repository. Its archive and component hashes, original source line references, and equation fingerprints are preserved in [SOURCE_SPEC.md](SOURCE_SPEC.md) and [equations](equations/README.md).

## Submission boundary

The manual merge/release is left to the author. Carry the pressure correction and the sign/domain qualifications from [MANUSCRIPT_NOTES.md](MANUSCRIPT_NOTES.md) into the manuscript. Distributional line vorticity, historical attribution, cited kernel/layer results, numerical figure interpretation, and application-specific governing assumptions are outside the certificate. No finite-energy whole-space Navier–Stokes regularity claim is made.
