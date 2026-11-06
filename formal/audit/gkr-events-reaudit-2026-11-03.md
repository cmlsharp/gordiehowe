# GKR challenge events and reduction review, 2026-11-03

Scope: 22 declarations at source commit `63b71565a`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.GKR.CircuitEvents.AssertionStep` | 1527934273634878379 | 645441022366176674 |
| `GordieHowe.GKR.CircuitEvents.Event` | 12379286103788082885 | 12044949398043114707 |
| `GordieHowe.GKR.CircuitEvents.HeadEscape` | 12736542148007214410 | 2397945699197862904 |
| `GordieHowe.GKR.CircuitEvents.Index` | 3382611283102138679 | 9604571048075576426 |
| `GordieHowe.GKR.CircuitEvents.InitialEvent` | 14753704509782671002 | 13030756960523332048 |
| `GordieHowe.GKR.CircuitEvents.RoundEvent` | 9721145405628052162 | 3106426917397579515 |
| `GordieHowe.GKR.CircuitEvents.assertionTable` | 10731264613968397166 | 10033151789468316476 |
| `GordieHowe.GKR.CircuitEvents.cost` | 5286599615757475833 | 16185165433447733312 |
| `GordieHowe.GKR.CircuitEvents.error` | 7652890496409093405 | 17152383858996601479 |
| `GordieHowe.GKR.CircuitProtocol.AssertionEscape` | 8462547126194552288 | 14864666057332814568 |
| `GordieHowe.GKR.CircuitProtocol.Trace` | 4239515955626598264 | 12055727246401579151 |
| `GordieHowe.GKR.CircuitProtocol.check` | 7111405008251461148 | 6952268080037451136 |
| `GordieHowe.GKR.ProtocolEvents.Context` | 10204207844663044784 | 12888748568712324725 |
| `GordieHowe.GKR.ProtocolEvents.circuitIndex` | 7157262816669932666 | 15964780064138965015 |
| `GordieHowe.GKR.ProtocolEvents.fullBad` | 5612307349653730580 | 2376548402199516422 |
| `GordieHowe.GKR.ProtocolEvents.index` | 14948671210494751165 | 676606748007887672 |
| `GordieHowe.GKR.ProtocolEvents.initialPoint` | 16402829196813015051 | 9337514384784593995 |
| `GordieHowe.GKR.ProtocolEvents.terminal` | 962565814794701132 | 18042347801090376977 |
| `GordieHowe.GKR.ProtocolReduction.error` | 14919498064016643299 | 4858406215256044759 |
| `GordieHowe.GKR.ProtocolReduction.fullBad_causal` | 3734262086 | 550064162 |
| `GordieHowe.GKR.ProtocolReduction.fullBad_count` | 4265719164 | 2146336992 |
| `GordieHowe.GKR.ProtocolReduction.reduction` | 4349495220475856507 | 2109685897551815792 |

## Method and historical classification

Reviewed current recursive verifier algebra, event predicates, exact challenge
index equivalences, causal/counting transport, and the round-by-round reduction.
Compared all four files against `ef8908bfd`; namespace substitutions in the scratch
diffs were for readability only, not a normalized-identity acceptance claim.

The historical changes include the grouped assertion relation (see
`gkr-circuit-reaudit-2026-11-03.md`) and replacement of a pair of fixed 40-element
initial arrays plus restriction by the actual `Fin d → F` initial point. The
old `d ≤ 40` bound consequently disappears. This changes the generic protocol's
challenge type; it is not claimed to preserve arbitrary old transcript bytes.
The current initial count is proved on the exact `F^d` space. No statistical
claim is imported from the old fixed-size-array model.

## Recursive algebra and event entries

Names are relative to `GordieHowe.GKR`.

- `CircuitProtocol.Trace`: a terminal scalar challenge, or the current layer's
  alpha/beta pair, every sumcheck message/challenge, two wire claims, and the
  complete tail. The tail is indexed by the actual circuit.
- `CircuitProtocol.check`: checks the terminal affine combination at an input
  circuit; at a layer, checks the final sumcheck value against the wiring times
  both wire claims and recursively checks the tail with those claims and points.
  The conjunction retains every layer. This is a semantic Prop checker, not a
  new executable Bool-verifier claim.
- `CircuitProtocol.AssertionEscape`: a nonzero grouped assertion table whose
  evaluation at hand zero is zero. Both conjuncts are needed: a correct zero table
  is not itself an escape event. The grouped relation change is explicit above.
- `CircuitEvents.assertionTable`: computes the current layer's actual table from
  deterministic tail evaluation; the terminal input has the zero table. It is
  fixed by circuit and input before the verifier challenges.
- `CircuitEvents.HeadEscape`: the corresponding current-layer assertion escape,
  false at the terminal input.
- `CircuitEvents.InitialEvent`: the union of nonzero output escaping evaluation
  and the current assertion table escaping. It does not assume either table zero.
- `CircuitEvents.Index`: one terminal scalar event; at each layer, one shared
  alpha/beta event, every position in the complete interleaved sumcheck schedule,
  and every tail event. No prover-message position is charged as a fresh challenge.
- `CircuitEvents.cost`: assigns one to terminal scalar batching, two to the
  alpha/beta pair, three to hand-zero sumcheck rounds, and two to hand-one rounds.
  The extra hand-zero unit pays for assertion tracking, not another assumed test.
- `CircuitEvents.error`: divides that numerator by the actual finite field size.
  A field has positive cardinality. Bounds above one are conservative upper bounds;
  there is no truncation that would invalidate counting.
- `CircuitEvents.AssertionStep`: tracks only hand-zero coordinates and uses the
  fixed next-layer assertion table. Although its spelling reads the terminal
  environment, `assertionStep_congr` reduces dependence to the prefix through the
  charged challenge; later coordinates cannot influence the event.
- `CircuitEvents.RoundEvent`: the union of sumcheck healing and assertion tracking.
  The cardinality proof uses a union upper bound and degree at most two, so it
  does not require the two bad events to be disjoint.
- `CircuitEvents.Event`: selects initial layer batching, the selected scalar round,
  or the recursive tail event using the actual computed next points and revealed
  claims. The input case uses final scalar batching. Arbitrary prover messages
  remain allowed in every branch.

For these entries, the checked support proofs replace only the charged challenge:
`updateRound` leaves both prover response values fixed, and recursive `update`
leaves every unrelated component fixed. Hand-zero tracking covers every coordinate
of the next-layer table. Thus `accepted_false_has_event` derives an initial or
actual recursive event from acceptance of a false circuit relation; it does not
assume assertion-evaluation soundness as an extra premise.

## Typed schedule and reduction entries

- `ProtocolEvents.circuitIndex`: is a bijection from actual verifier moves to
  recursive event indices. Its sumcheck branch uses the proved schedule length
  and skips the prover's two wire claims; challenge type equality is proved for
  each branch. The alpha/beta challenge remains `F × F`.
- `ProtocolEvents.index`: adds exactly the initial `Fin d → F` move to that
  bijection. It does not flatten the initial vector into one scalar sample.
- `ProtocolEvents.Context`: contains the circuit input and arbitrary fixed pads.
  It imposes no distribution or honesty requirement on those committed values.
- `ProtocolEvents.initialPoint`: reads exactly the first challenge vector, with
  no unused array component, width cap, or post-draw restriction.
- `ProtocolEvents.fullBad`: uses the initial event at the first move and the
  recursive events on the unmasked actual trace thereafter, beginning from the
  two zero output claims at the same initial point.
- `ProtocolEvents.terminal`: conjuncts the pad-product equations with the complete
  unmasked verifier algebra. Pad consistency remains an explicit checked output
  obligation; it is not assumed about adversarial pads for free.
- `ProtocolReduction.error`: charges `2*d / |F|` to the initial vector and the
  recursive errors elsewhere. `InitialChallenge.bad_count` bounds both fixed
  multilinear-table residuals on the actual vector space. For `d = 0`, a nonzero
  constant table cannot evaluate to zero, so zero initial error is correct.
- `ProtocolReduction.fullBad_causal`: requires agreement only through the charged
  verifier move and derives event equivalence, including the hand-zero tracker.
  It does not assume future transcript agreement or honest prover causality in
  place of the event's own prefix property.
- `ProtocolReduction.fullBad_count`: quantifies over arbitrary context and complete
  transcript, varies only the selected challenge, and transports counts through
  exact type equivalences. The initial cardinality is `|F|^d`; the shared batching
  cardinality is `|F × F|`, with error `2 / |F|`. No good-challenge subset replaces
  either space. Unmasking commutes with this challenge update.
- `ProtocolReduction.reduction`: supplies `TranscriptEventReduction.reduction`
  with the named source relation, terminal predicate, proved causality and counts,
  and deterministic implication from terminal acceptance to the relation or an
  event. It introduces no statistical hypothesis, oracle axiom, or restriction on
  prover values. Its noncomputable proof/error record is not an executable
  prover/extractor/simulator or a newly exempted runtime definition.

## Outcome and scope

These 22 declarations pass the current semantic review. The initial challenge
and grouped assertion changes are substantive historical changes, separately
classified from constructor-pattern adaptations and namespace moves. The source
bytes and fingerprints match the compiled acceptance snapshot. This audit edits
no Lean source, headline, hypothesis, distribution, or exception list. Final-head
closure reconciliation remains required.
