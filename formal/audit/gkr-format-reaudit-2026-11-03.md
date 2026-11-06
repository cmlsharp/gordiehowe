# GKR write-codec re-audit, 2026-11-03

Scope: 3 declarations at source commit `f54843e5a`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.SPBCS.SpecWrites.gkrCircuit` | 1683432876583281317 | 13977937666020011084 |
| `GordieHowe.SPBCS.SpecWrites.gkrSpec` | 6999639709115458441 | 6609552435714858509 |
| `GordieHowe.SPBCS.SpecWrites.sourceInteraction` | 1333888668132141335 | 11549060702977777744 |

## Protocol-indexed write codecs

The last matching source for all three entries is `5831d8fbc`, in
`PQ/BCS/Format/SpecWrites.lean`. The current `SpecWrites` assigns a bounded
write codec to every prover message of the indexed protocol. Verifier moves
need no prover-message codec: oneV discharges that case using the absence of
prover-message indices, rather than an arbitrary encoding of a challenge.

`SpecWrites.gkrCircuit` follows the actual current Schedule.circuit recursion.
The input case has one verifier move and no prover write. Each layer starts
with a verifier pair, then has exactly 2*inDim sumcheck rounds, each with a
field-pair prover message and a verifier challenge, then one field-pair wire
claim and the recursive tail. The codecs preserve that order and use the
same tail circuit; no layer or wire-claim message is skipped.

Every prover pair uses WriteCodec.fieldPair, the product of two field-element
codecs. Its stated bound is 2*(1+fb), including both element tags, and the
explicit hB transfers that bound to B. There is no unchecked truncation to B
or decoding fallback. The recursion at zero-dimensional inputs still includes
the wire claim and tail even when there are zero sumcheck rounds.

The old Circuit.layer constructor also carried a uniqueness proof; the current
constructor takes the layer and tail without that extra constructor field.
This codec handles the current layer's transcript independently of that proof.
The semantic adequacy of the circuit representation is a separate GKR audit,
not assumed from this codec's existence.

Disposition: gkrCircuit passes message-order, coverage and byte-bound review.

## Initial challenge

`SpecWrites.gkrSpec` prefixes the circuit codecs with exactly the current
initial verifier move of type Fin d -> F, matching Schedule.initial and spec.
The historical source used a pair of 40-coordinate vectors. That is a genuine
protocol-interface change; this audit does not describe it as a rename or
claim the historical protocols are identical. The current specification uses
the output dimension d explicitly, and the codec is indexed by precisely that
specification. Since this is a verifier move, it adds no omitted prover message
or unbounded prover serialization. At d=0 the challenge type is the singleton
empty function type, with the same absence of a prover write.

Disposition: gkrSpec passes current protocol alignment. The randomness and
soundness of the GKR initial move are separate semantic obligations.

## Source interaction

`SpecWrites.sourceInteraction` deconstructs the same LayeredCircuit used by
its source interaction, eliminates its proved tail-input dimension equality,
and selects gkrSpec on `.layer Q tail`. The circuit, field bytes and bound
are those of the supplied arguments. It does not substitute an unrelated
circuit or require a new relation-validity premise to construct the codecs.
The interaction definition uses exactly the same deconstruction and calls
SourceReduction.ofCircuit on that layer and tail.

The historical Source record carried uniqueness and dimension-bound proofs
that are no longer fields of the current LayeredCircuit. This code's pattern
changed accordingly; neither proof is manufactured or silently assumed by
the current codec. Sumcheck nodes remain an explicit interaction argument;
the codecs depend on message types, not on an assumed choice of node values.

Disposition: sourceInteraction passes source-circuit and dimension alignment.
This row certifies codecs for the stated interaction, not full compiler
correctness or a serialized-byte equality with an external implementation.

## Validation scope

The three own fingerprints match the tracked closure and completed combined
environment, and the source file is identical to that built snapshot. Only
these ledger rows and this report change. Final-head closure reconciliation
and the separate GKR semantic audits remain required.
