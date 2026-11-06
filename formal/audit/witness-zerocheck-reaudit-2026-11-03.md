# Witness sampler and zerocheck re-audit, 2026-11-03

Scope: 15 declarations at source commit `639843e2d`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.SPBCS.WitnessSampler.Draw` | 1124086864 | 2006407076 |
| `GordieHowe.SPBCS.WitnessSampler.Draw.coins` | 2415499868542707024 | 8399465773077062358 |
| `GordieHowe.SPBCS.WitnessSampler.Draw.mk` | 2563966634 | 1125899488 |
| `GordieHowe.SPBCS.WitnessSampler.Draw.oracle` | 3043788582214944904 | 14146820698290170010 |
| `GordieHowe.SPBCS.WitnessSampler.MissesAtMost` | 3291343820992161823 | 4000596402830462849 |
| `GordieHowe.SPBCS.WitnessSampler.MissesAtMostAt` | 12677814137563880373 | 17652617835959219528 |
| `GordieHowe.SPBCS.WitnessSampler.drawEquiv` | 350291632493799036 | 3005058643730864502 |
| `GordieHowe.SPBCS.WitnessSampler.instFintypeDraw` | 7229950373133337955 | 10730542060676267179 |
| `GordieHowe.SPBCS.WitnessSampler.instNonemptyDraw` | 4230671171 | 3241470765 |
| `GordieHowe.Sumcheck.FieldSkip.PadTriples.left` | 15536895232436471707 | 14097386701327181842 |
| `GordieHowe.Sumcheck.FieldSkip.PadTriples.mk` | 2500665245 | 3762190737 |
| `GordieHowe.Sumcheck.FieldSkip.PadTriples.right` | 10396751373035536254 | 4267210005240849051 |
| `GordieHowe.Sumcheck.Nodes.mk` | 2712164815 | 2003546211 |
| `GordieHowe.BatchedZerocheck.maskedReduction` | 11403675845388694237 | 3543363835573334056 |
| `GordieHowe.Sumcheck.Nodes.zeroOneTwo` | 775535858066802667 | 4674203827131251394 |

## Witness sampling

The seven Draw-related entries were last matched in `5831d8fb`, in
`PQ/BCS/Theorems.lean`; the two failure predicates were last matched in
`c92d56ad2`. The current source is `SPBCS/WitnessSampler.lean`.

`WitnessSampler.Draw` previously depended on a complete compiler `Setting`
and stored its oracle type. It now takes that oracle type as the explicit
parameter `Ω`. The fields remain the sampler's coins and the oracle value.
`Draw.mk` accepts those two fields without a success predicate or a relation
proof. The `coins` and `oracle` projections return those exact components; no
filter removes failed draws and neither component is chosen from the other.
The abstraction allows non-oracle types too, but a caller claiming an oracle
experiment must supply the actual oracle type.

`drawEquiv` pairs the fields and reconstructs the record, with both inverse
laws by reflexivity. The `instFintypeDraw` enumeration transports the product
enumeration through the inverse equivalence. It therefore enumerates every
coin/oracle pair once; uniform draws have the product law, not correlated or
success-conditioned coins. The finite instance on `Ω` is explicit instead of
being read from a setting. `instNonemptyDraw` combines nonemptiness of the
sampler's coins and of `Ω`. Its uses of arbitrary elements occur inside a
proof of Nonempty and are not an executable sampler or a selected distribution.
No nonempty oracle assumption is inferred from an empty type.

`MissesAtMostAt` counts the event that `(x, D.draw u r)` is outside `rel`
over all uniform sampler coins and bounds it by `η`. Failure is not conditioned
away. `MissesAtMost` requires that same bound at every `(x,u)` in the stated
query relation `relU`. An empty `relU` makes this hypothesis vacuous, but the
resulting claims are restricted to that same relation; this definition alone
asserts no security for arbitrary requests. A bound at or above one may be
uninformative and is not silently strengthened to a useful probability bound.
The current `prob_draw_le` explicitly adds the failure budget once to the
per-valid-witness oracle bound; it does not replace failure by zero. The
sampler's draw function has no oracle argument, consistent with the product
experiment used here.

Disposition: the four Draw data declarations, product equivalence, two
instances and two failure predicates pass current type, distribution and
vacuity review. The source change generalizes the oracle parameter rather
than changing the product experiment.

## Product-pad coordinates

The old `PadTriples` record in `bd92a613e` (`PQ/Sumcheck/FieldSkipMasked.lean`)
stored a finite cell type and the left/right coordinate maps. The current
record additionally stores `Encodable Cell`, used for constructive numbering.
`PadTriples.mk` requires that encoding together with the finite instance and
both maps. It does not assert that the maps implement a correct polynomial.
The semantic obligations remain in `SkipRelation.Computes` and the explicit
product equations.

`PadTriples.left` still returns either a terminal coordinate in `Fin k` or a
product cell, preserving the sum tag. `right` still returns only a terminal
coordinate in `Fin k`. The extra encoding field changes projection positions,
not their meaning. No acyclicity is asserted for arbitrary triples; concrete
honest filling and its correctness require separate evidence. At `k=0`, a
right-coordinate map can exist only when the cell type is empty, so there is
no manufactured out-of-range terminal coordinate.

Disposition: the constructor and both coordinate projections pass. This ledger
review does not certify every finite encoding as an efficient numbering
implementation or waive runtime checks on consumers.

## Interpolation nodes

`Sumcheck.Nodes.mk` has the same four fields as the last matching source
`ef8908bfd` (`PQ/Sumcheck/Round.lean`): three field-valued points, their
injectivity, and the equations fixing points zero and one. It requires the
injectivity proof rather than assuming distinctness of arbitrary submitted
points. The third slot need not be field element two; this matters in binary
fields, where zero and two coincide. Nothing in the constructor asserts a
false characteristic-independent choice of three points.

`Nodes.zeroOneTwo`, last matched in `5831d8fb`, still constructs the points
`[0,1,2]` with `CharP F p` and `2 < p`. If two were zero, the characteristic
would divide two, contradicting that inequality; two differs from one because
a field is nontrivial. All three finite-index cases are checked for injectivity,
and the endpoint equations are reflexive computations. The hypothesis is on
the field parameters, not on an adversary. This definition deliberately does
not cover characteristic two or claim to instantiate every field.

Disposition: the constructor and concrete node family pass the interpolation
and characteristic-boundary review.

## Batched masked reduction

The historical name of `BatchedZerocheck.maskedReduction` is
`PQ.GordieHowe.SkipBatch.claimIP` in `bd92a613e`; reading only the current name
would miss the predecessor. Both bodies assemble the same batch specification,
one terminal linear row (`Lin = Unit`), products indexed by `Rel.Cell`, and
one opening claim on the logical coordinates. The later constructive cell
encoding enters through the relation data, and `ClaimIP` is now named
`FieldProof.MaskedReduction`.

The terminal row reads the challenge and message projections of the same
transcript. Each product constraint uses the left pad/cell, right terminal
pad and target product cell in that order. The opening claim uses the same
public input and logical level as the reduction; it is not replaced by an
unconstrained existential assignment. Empty product-cell types produce no
product constraints, but the terminal row and opening claim still remain.
There is exactly one opening claim, with index type `Fin 1`.

The current `outHolds_iff` states the exact conjunction of the pads' product
equations and the deferred masked-verifier equations, in both directions.
`accepts_of_outHolds` additionally requires `Rel.Computes Q` before relating
this to the polynomial verifier, and `maskedReductionSound` retains the
explicit degree parameter condition. The bare reduction definition is data;
it does not claim soundness for arbitrary inconsistent relation computations.
These boundaries avoid hiding a correctness premise in a constructor.

Disposition: the assembled reduction passes the current specification review.
Its numerical soundness budgets and all concrete instantiations are separate
entries, not certified by this row alone.

## Validation scope

All fifteen own fingerprints match the tracked closure and completed combined
environment. The five reviewed source files are byte-identical to that compiled
snapshot. Only these ledger rows and this report change; no source, hypothesis,
coin law or acceptance predicate is edited. Final-head reconciliation remains
required.
