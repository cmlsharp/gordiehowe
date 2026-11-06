# GKR flattening and honest families audit, 2026-11-03

Scope: 17 declarations at source commit `f71a57293`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.GKR.CircuitFlatten.PadIndex` | 9992137030258817635 | 12130201928841888585 |
| `GordieHowe.GKR.CircuitFlatten.flatPads` | 16302320087412313743 | 13619429237434812552 |
| `GordieHowe.GKR.CircuitFlatten.inputAlpha` | 11724583854372784472 | 10064534287367089619 |
| `GordieHowe.GKR.CircuitFlatten.inputPoints` | 14837564397097511768 | 10658533076414021715 |
| `GordieHowe.GKR.CircuitFlatten.layerValues` | 6092639974980595122 | 2002836592797903525 |
| `GordieHowe.GKR.CircuitFlatten.layout` | 5001499478497114559 | 11426429228193174476 |
| `GordieHowe.GKR.CircuitFlatten.pads` | 7174205173833712876 | 13207063188641542134 |
| `GordieHowe.GKR.CircuitFlatten.roundCount` | 12184115621681038988 | 3664367484220290365 |
| `GordieHowe.GKR.CircuitFlatten.transcript` | 15818356076987190473 | 9301023330102043774 |
| `GordieHowe.GKR.CircuitFlatten.wiringValuesDec` | 3798287335426638766 | 1767072882970512094 |
| `GordieHowe.GKR.HonestTranscript.maskedCircuitFamily` | 12530516133415258808 | 16213279992919740853 |
| `GordieHowe.GKR.HonestTranscript.maskedFamily` | 18192554840508036364 | 6981256699590227383 |
| `GordieHowe.GKR.HonestTranscript.valueCircuitFamily` | 16846645452484772885 | 5446029393008282079 |
| `GordieHowe.GKR.HonestTranscript.valueFamily` | 14682530110653746148 | 4987338252224553169 |
| `GordieHowe.GKR.LayeredCircuit.family` | 11304271775866156675 | 6819248922360295395 |
| `GordieHowe.GKR.LayeredCircuit.padValues` | 14051484824740402642 | 17879037813190727610 |
| `GordieHowe.GKR.LayeredCircuit.valueFamily` | 9036855815864928147 | 10010647641960122248 |

## Evidence and classification

The current definitions and their consumers were read in CircuitFlatten,
HonestTranscript and OrdinaryCompleteness. Historical counterparts at
5831d8fbc were compared before the protocol integration and namespace rename.
The selected fingerprints match both the tracked closure and the compiled
accepted closure; source bytes match that compiled snapshot. This is a semantic
re-audit, not an assertion that the historical expressions are identical.

The historical circuit constructors carried a uniqueness argument that the
current grouped per-gate relation does not require. The initial challenge also
changed from two fixed-capacity arrays to one vector at the actual input
dimension. Those are substantive interface changes. The review below checks
that the current flattening and honest strategies follow that current protocol;
it does not infer per-corner assertions from grouped assertions without the
removed uniqueness assumption.

## Per-declaration review

Names in this section have prefix `GordieHowe.GKR`.

- `CircuitFlatten.roundCount`: a layer contributes its scheduled input-dimension
  length, and the successor index recurses into the tail. The input constructor
  has no layer index. This follows circuit depth, not a padded upper bound.
- `CircuitFlatten.layerValues`: extracts the actual head scalar, scheduled round
  values and wire claims, then recurses on the actual tail transcript. It does
  not replace prover messages with honest evaluations.
- `CircuitFlatten.inputAlpha`: follows all recursive tails to the terminal
  scalar. In particular, it does not mistakenly return the outer layer scalar.
- `CircuitFlatten.inputPoints`: runs each layer's challenge environment and
  follows its false and true points into the tail. Point selection depends on
  actual challenges, not prover messages; the input case preserves the pair.
- `CircuitFlatten.wiringValuesDec`: computes actual corner wiring contributions
  with `layerWiringDec`, including the alpha/beta weights in the challenge
  environment, then recurses. Its equation theorem identifies it with the
  semantic polynomial wiring value; no free wiring value was introduced.
- `CircuitFlatten.PadIndex`: the dependent layer index is bounded by circuit
  depth. A disjoint sum separates each round's two coefficient pads from the
  three claim pads. The sum avoids overlap between these pad classes.
- `CircuitFlatten.layout`: a layer constructor supplies the nonempty layout,
  exact round counts and the corresponding coefficient/claim pad injections.
  Its tail-depth parameter denotes a circuit with one additional layer.
- `CircuitFlatten.transcript`: supplies the actual alpha, interpolation
  coefficients at each challenge, two wire claims, computed wiring value and
  terminal input scalar. The two coefficient coordinates select the intended
  degree-zero and degree-two terms; finite indexing excludes an extra term.
- `CircuitFlatten.pads`: reads the flat layer-zero coordinates for the head and
  uses successor layer indices for the tail. No coordinate is silently reused
  across layers.
- `CircuitFlatten.flatPads`: reverses that indexing by cases on the layer and
  coefficient/claim sum. The proved `pads_flatPads` equation confirms the round
  trip. This is an indexing equivalence, not a claim that a dependent product
  pad is an independently uniform random variable.
- `HonestTranscript.maskedCircuitFamily`: uses actual tail evaluations and
  challenge-derived points. Round messages are masked by the given pads; wire
  claims subtract their corresponding claim pads. Recursive families respect
  the causal challenge order, and the input case consumes its one challenge.
- `HonestTranscript.maskedFamily`: first receives the actual input-dimension
  vector and passes it as both initial points to the masked circuit family.
  There is no restriction on a verifier challenge added as a hypothesis.
- `HonestTranscript.valueCircuitFamily`: emits the supplied free values with
  the round/claim shape and propagates actual challenges. It does not call the
  honest prover or read a secret input to manufacture its messages.
- `HonestTranscript.valueFamily`: combines the same initial vector challenge
  with that value family. The accompanying distribution proof translates pads
  by fixed honest values through `Equiv.subLeft`; the shift depends on the
  fixed input and challenges, not on the sampled pads. It does not require the
  input to satisfy the circuit.
- `LayeredCircuit.padValues`: flattens the actual circuit pads, including the
  derived third claim pad. Its historical body is unchanged apart from the
  enclosing source/interface rename.
- `LayeredCircuit.family`: destructs the source and transports along its input
  dimension equality, then applies the honest family to the interpreted
  public/witness input and actual pads. The interface pad argument does not
  create an unrestricted prover witness.
- `LayeredCircuit.valueFamily`: uses the same source/dimension transport and
  the supplied values. It does not read the interpreted input or witness.

## Hypotheses, vacuity and boundary checks

`CircuitFlatten.terminal_iff` connects the flattened pad checks and terminal
weighted input equation with `ProductsHold` and the unmasked circuit check in
both directions. Thus flattening retains the complete current acceptance
condition. Ordinary completeness keeps explicit satisfaction, pad-coordinate
agreement and product-hold premises; it is not a statement about an assumed
successful prover. The value-family distribution result is independent of
satisfaction, whereas completeness is correctly conditional on honest input
satisfaction. Empty depth, tail recursion and both finite pad-coordinate cases
were checked at their constructor equations.

No Lean source, hypothesis, headline statement, distribution or trust exception
is changed by this ledger update. Reconciliation against the final generated
closure is still required after the remaining implementation work lands.
