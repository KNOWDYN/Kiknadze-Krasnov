# Manuscript qualifications

The source hashes and original formulas remain in the frozen equation ledger. These notes describe the interpretation used in Lean and the correction to carry into the submission text.

## Near-axis pressure (M059)

For fixed time and axial coordinate, positive shape, positive distributed scales, and positive pressure reference radius, the actual swirl-pressure primitive gives

\[
\lim_{r\to0^+}r^2p(r,z,t)
=-\frac{\rho}{2}\left(q^2+\frac{\Gamma_\ell^2}{4\pi^2}\right).
\]

When `Gamma_line = 0`, this reduces to the source's coefficient `-rho q²/2`. For nonzero line circulation there is an additional term `-rho Gamma_line²/(8 pi² r²)`. Write an asymptotic equivalence only when the resulting coefficient is nonzero; otherwise state the scaled limit. The unrestricted source formula omits the independent line-circulation contribution. Both cases are certified in `PressureAsymptotics.lean`.

Suggested replacement text:

> Near the axis, at fixed time and axial coordinate, the pressure has scaled limit \(r^2p\to-\rho[q^2+\Gamma_\ell^2/(4\pi^2)]/2\). Thus the leading singular coefficient reduces to \(-\rho q^2/2\) on the zero-line-circulation branch. A nonzero central line circulation contributes the additional swirl-pressure term \(-\rho\Gamma_\ell^2/(8\pi^2r^2)\).

## Sign and scope

- With negative distributed circulation, the signed vorticity and swirl extremum is a minimum. The sign-independent peak statements concern magnitude. Zero circulation is excluded where a nontrivial extremum is asserted.
- Source/sink and line-bearing fields are certified on `r > 0`. Sink trajectories are restricted to intervals before an axis encounter.
- Material no-crossing and direction toward the scaled distinguished radius do not, by themselves, prove infinite-time convergence.
- Equal scales admit a common total-field profile. Distinct scales admit componentwise material cylinders; no universal common total-field zero-flux material surface is asserted.
- Zero circulation transfer does not imply zero passive-scalar flux. The latter additionally requires zero radial scalar gradient for positive diffusivity.
- Nonzero linear strain gives an unbounded energy lower bound in expanding cylinders. These fields are outside the finite whole-space energy class of the Navier–Stokes global regularity problem.

Historical identifications and cited external representations retain their source attribution and are not independent Lean proof claims.
