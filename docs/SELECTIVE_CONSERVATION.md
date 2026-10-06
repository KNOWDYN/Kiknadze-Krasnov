# Selective material-circulation formal layer

`KiknadzeKrasnov/SelectiveConservation.lean` is the additive v1.1.0 theorem layer for the selective material-circulation structure of the Kiknadze–Krasnov vortex.

It introduces no new physical model. The results sharpen consequences of the material-radius, circulation, vorticity and scale identities already present in the v1.0.0 development.

## Core definitions

- `scaledOffset s x = x - (s - 1)` is the displacement from the distinguished similarity coordinate `x_* = s - 1`.
- `diffusiveClock nu beta t = ∫_0^t 4 nu beta(tau) d tau` is the accumulated clock controlling scaled-coordinate contraction.

## Principal entry points

| Entry point | Certified statement |
|---|---|
| `scaledOffset_integratingFactor_hasDerivAt_zero` | The integrating-factor quantity `exp(B(t)) [x(t)-(s-1)]` has zero derivative under the exact scaled material-coordinate law. |
| `scaledOffset_integratingFactor_eq_on` | The integrating-factor quantity is constant between admissible physical times. |
| `scaledOffset_exact_exponential` | Exact exponential evolution of the scaled offset between two physical times. |
| `diffusiveFactor_pos_lt_one` | The contraction factor lies strictly between zero and one whenever the diffusive clock advances. |
| `selectiveTransferPartition` | Sign-safe circulation-transfer partition: zero at `x=s-1`, with opposite signed transfer on the two sides after multiplication by the circulation sign. |
| `distinguishedFraction_independent_of_scale` | The distinguished enclosed-circulation fraction is independent of the positive radial scale. |
| `selectiveMaterialConservation` | Assembled exact result combining material transport, constant enclosed circulation, vorticity-gradient zero, zero diffusive circulation transfer, fixed enclosed fraction, and the signed transfer partition. |

## Mathematical scope

The assembled theorem is stated on the annular source branch with positive viscosity, a positive scale history satisfying the KK scale law, and nonzero circulation where required for a nontrivial signed partition. The existing domain definitions continue to distinguish physical time, radius, scale, shape and source parameters.

The exponential selection theorem is conditional on the exact scaled material-coordinate differential law and the derivative of the diffusive clock. It is not an empirical fit or an asymptotic approximation.

## Relation to v1.0.0

v1.0.0 remains the frozen baseline certificate for the earlier zero-flux material-cylinder development. The v1.1.0 selective-conservation layer is additive:

- it does not change the v1.0.0 theorem statements;
- it does not alter the frozen 206-display / 37-prose-claim source ledger;
- it imports and reuses the existing KK definitions and principal-surface certificates;
- it adds the explicit scaled-offset dynamics and signed transfer-partition formulation.

## Certification boundary

The formal layer does not claim:

- empirical identification of a source-bearing laboratory realization;
- equivalence to a variational active-transport-barrier functional;
- a universal distinct-scale multimode common zero-flux surface;
- finite-energy whole-space Navier–Stokes regularity;
- zero passive-scalar flux from the circulation condition alone.

The relationship to the available laboratory analyses is summarized separately in [`EXPERIMENTAL_SCOPE.md`](EXPERIMENTAL_SCOPE.md).

## Verification

The top-level `KiknadzeKrasnov.lean` imports `SelectiveConservation.lean`, so the standard project build and transitive trust audit include this layer. `scripts/TrustAudit.lean` walks every declaration in all imported project modules and rejects any axiom outside Lean's permitted `propext`, `Classical.choice`, and `Quot.sound` dependencies.
