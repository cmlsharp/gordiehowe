# Pure quantum state re-audit, 2026-11-03

Scope: 8 declarations at source commit `4425ab407`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.Quantum.born` | 13504422159381556762 | 8699662579112709379 |
| `GordieHowe.Quantum.mask` | 4183481097734610608 | 8299037976579662177 |
| `GordieHowe.Quantum.KrausMap.haltOp` | 4790218402983258659 | 741959876386433197 |
| `GordieHowe.Quantum.Distinguisher.accept` | 18310920030668031961 | 17183243327746776065 |
| `GordieHowe.Quantum.Distinguisher.init` | 10607271998559628448 | 15154885029364781909 |
| `GordieHowe.Quantum.Distinguisher.kind` | 6236775517049230821 | 14104459198104916511 |
| `GordieHowe.Quantum.Distinguisher.step` | 11713540599568303513 | 18372719936725178684 |
| `GordieHowe.Quantum.Distinguisher.stepAt` | 14090162642877852768 | 10814816210446933491 |

## Born distribution and coordinate projection

`Quantum.born` has the same defining formula as the last matching source
`3688cc383` in `PQ/Quantum/Born.lean`: the PMF weights are the squared extended
norms of the amplitudes, with their sum proved one from the explicit unit-norm
hypothesis. There is no division by a possibly zero norm, postselection, or
renormalization of an arbitrary vector. An empty basis cannot supply a unit
vector; the hypothesis is a state-normalization condition, not a restriction
on measured outcomes.

`Quantum.mask`, compared with `54b23c22b` in `PQ/Quantum/State.lean`, still
applies the set indicator coordinatewise and packages the resulting linear
map as continuous in the finite-dimensional space. Coordinates in A remain
unchanged; all others become zero. The map is not claimed to preserve norm
or normalize the result. Empty and universal A give zero and identity,
respectively, and linearity follows independently in each membership branch.
There is no hidden selection of a favorable nonzero output.

Disposition: both definitions pass weight, normalization and projection review.
They remain mathematical quantum constructions, not executable samplers.

## Halting effect

`Quantum.KrausMap.haltOp` has a substantive change since `f01311529` in
`Model/Quantum/Pure/Bridge.lean`. It formerly chose an arbitrary matrix factor
of the halting effect. It now uses the continuous-functional-calculus positive
square root of `1 - sum_r op(r)^H * op(r)`. The order and adjoints in this
effect agree with KrausMap.sum_le; the effect is positive semidefinite because
the summed effect is at most identity.

The current haltOp_spec derives exactly `B^H * B = 1 - sum_r op(r)^H * op(r)`:
the square root is self-adjoint and its square is the nonnegative effect.
No trace-preservation assumption was added. When the input map is trace
preserving, the separate haltOp_eq_zero theorem gives zero. In general the
nonzero deficit is preserved, not discarded. Choosing the positive square
root additionally supports the current commutation lemmas.

Disposition: the current canonical factor passes the halting-effect review.
This is not a claim that its matrix entries equal the historical arbitrary
factor, nor a new source change to a headline. The factorization property is
the semantic fact reviewed here; full dilation theorems are separate entries.

## Distinguisher interface

The four field projections and step extension are compared with `54b23c22b`
in `PQ/Quantum/Game.lean`. `Distinguisher.init` returns the supplied vector,
whose unit norm is a separate required field of the same record.
`Distinguisher.kind` returns the supplied workspace-to-Bool function, permitting
a branch-dependent request/query choice rather than a fixed schedule.
`Distinguisher.step` returns the supplied unitary at the exact index in
Fin(m+1), including the map after the last of m slots. These fields have no
oracle or environment-tape argument. `Distinguisher.accept` returns the
supplied set of the distinguisher's full basis registers; it does not substitute
an existentially favorable log set or a condition on the environment state.

`Distinguisher.stepAt` extends that same finite family: k<m+1 uses step k,
and every later natural index gives identity. Thus k=m still applies the
last real map; k=m+1 is the first identity case. At m=0, step zero remains
present before the final measurement. The extension does not insert extra
oracle queries or silently omit a boundary step.

Disposition: all five entries pass projection, information-access and endpoint
review. This audit covers their interface and extension, not every quantum
game theorem that uses them.

## Validation scope

The eight own fingerprints match both the tracked closure and completed
combined environment. All four reviewed source files are identical to that
compiled snapshot. Only these eight ledger rows and this report change; no
new hypothesis, axiom, choice operation or computability exception is added.
Final-head closure reconciliation remains required.
