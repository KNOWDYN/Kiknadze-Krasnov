# Final manuscript reconciliation

The formal source hashes and original equation fingerprints remain preserved in the frozen ledger. The final reviewed manuscript and Supplementary Material have incorporated the corrections and qualifications identified during formalisation.

Final reviewed artifacts:

- manuscript v3 SHA-256: `153c7cff9d0418015ec7b8375bc4ee0559ef70d66405051ee1ef406086b31bdc`
- Supplementary Material v3 SHA-256: `5a3ac52605ca0deeafc4f8f9614f54abb2d1db69de98d0b374b799a0cced1372`

## Near-axis pressure — resolved

For fixed time and axial coordinate, the certified scaled limit is:

`lim_(r→0+) r² p(r,z,t) = −(ρ/2)[q² + Γ_ℓ²/(4π²)]`.

When `Γ_ℓ = 0`, this reduces to `−ρq²/2`. For nonzero line circulation there is an additional leading term `−ρΓ_ℓ²/(8π²r²)`.

The final v3 manuscript states the combined scaled limit in Eq. (60), then gives the zero-line-circulation asymptotic as a special case. This matches `PressureAsymptotics.lean`.

## Signed extrema — resolved

The final v3 manuscript and Supplementary Material use sign-independent magnitude statements where the circulation sign is unrestricted:

- for nonzero distributed circulation, the distinguished radius is the maximum of `|ω_z|`; the signed field has a maximum for positive circulation and a minimum for negative circulation;
- for nonzero single-mode circulation and `s > 1/2`, the interior extremum is stated for `|u_θ|`, with signed maximum/minimum distinguished by circulation sign.

These formulations match `PrincipalSurface.lean`, `VorticityCore.lean`, and `SwirlMaximum.lean`.

## Scope qualifications preserved

- Source/sink and line-bearing fields are certified on `r > 0`. Sink trajectories are restricted to intervals before an axis encounter.
- Material no-crossing and direction toward the scaled distinguished radius do not, by themselves, prove infinite-time convergence.
- Equal scales admit a common total-field profile. Distinct scales admit componentwise material cylinders; no universal common total-field zero-flux material surface is asserted.
- Zero circulation transfer does not imply zero passive-scalar flux. The latter additionally requires zero radial scalar gradient for positive diffusivity.
- Nonzero linear strain gives an unbounded energy lower bound in expanding cylinders. These fields are outside the finite whole-space energy class of the Navier–Stokes global regularity problem.
- Historical identifications and cited external representations retain their source attribution and are not independent Lean proof claims.

## Final status

No outstanding manuscript-side mathematical correction remains from the Lean audit. The final v3 manuscript and Supplementary Material are reconciled with the certified theorem set. See [FINAL_RELEASE_AUDIT.md](FINAL_RELEASE_AUDIT.md) for the release-level verification record.
