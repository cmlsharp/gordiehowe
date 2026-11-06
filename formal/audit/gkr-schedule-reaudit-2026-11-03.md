# GKR schedule and pad-translation review, 2026-11-03

Scope: 20 declarations at source commit `400a8f471`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.GKR.PadTranslation.FreePads` | 723669412090760403 | 10469488021577757612 |
| `GordieHowe.GKR.PadTranslation.FreePads.instFintype` | 17488892101861395402 | 7495812352047464751 |
| `GordieHowe.GKR.PadTranslation.FreePads.pads` | 4156811168457690739 | 6182555924365148950 |
| `GordieHowe.GKR.PadTranslation.Pads` | 18182550686957319583 | 6396758353154976115 |
| `GordieHowe.GKR.PadTranslation.ProductsHold` | 6388050910388962176 | 15391744953853739836 |
| `GordieHowe.GKR.PadTranslation.unmask` | 8004720429482497332 | 14865592896770861088 |
| `GordieHowe.GKR.Schedule.circuit` | 18379854253059988273 | 13583789466759246297 |
| `GordieHowe.GKR.Schedule.circuitLength` | 1696287483350213095 | 1863391021829439246 |
| `GordieHowe.GKR.Schedule.circuitTrace` | 13716865275464232103 | 425812024851261313 |
| `GordieHowe.GKR.Schedule.circuitTranscript` | 5035556656853627588 | 14052647482376348291 |
| `GordieHowe.GKR.Schedule.circuit_decidableEq` | 12295161671778954362 | 16049958972132512066 |
| `GordieHowe.GKR.Schedule.circuit_fintype` | 2072556239887293613 | 9574602784287911681 |
| `GordieHowe.GKR.Schedule.circuit_inhabited` | 10404741558122749053 | 15439276592899380958 |
| `GordieHowe.GKR.Schedule.initial` | 15050374647946407536 | 12589542971329164880 |
| `GordieHowe.GKR.Schedule.initialValues` | 4260376054066028644 | 5564938037183591369 |
| `GordieHowe.GKR.Schedule.spec` | 12563201067535944269 | 9828940345810739013 |
| `GordieHowe.GKR.Schedule.spec_decidableEq` | 3106935256486809779 | 11715802900798800697 |
| `GordieHowe.GKR.Schedule.spec_fintype` | 4082402218562616253 | 9280625253510702712 |
| `GordieHowe.GKR.Schedule.spec_inhabited` | 13996073458811288555 | 6463958856632840115 |
| `GordieHowe.GKR.Schedule.trace` | 11621880717710425763 | 7404718721362375400 |

## Method and historical classification

Reviewed the typed schedule, transcript decoding, its six finite/default/equality
instances, and the recursive pad translation against source at `ef8908bfd` and
`5831d8fbc` as appropriate to each ledger entry. The significant initial-challenge
change is the actual `F^d` vector in place of two fixed 40-element arrays, as
classified in `gkr-events-reaudit-2026-11-03.md`. Removing the circuit's uniqueness
field changes recursive patterns without deleting any protocol round. Other
historical changes include computational recursive instance implementations.
Current source bytes and fingerprints match the compiled acceptance snapshot.

## Individual schedule entries

Names are relative to `GordieHowe.GKR.Schedule`.

- `circuitLength`: terminal input contributes one scalar move. Each layer adds
  one batching move, two moves for each of `2 * inDim` sumcheck coordinates, and
  one wire-claim move before the tail. Thus even zero-width layers retain their
  batching and claim moves, and the final input-binding challenge is never lost.
- `circuit`: constructs precisely that ordering and direction: verifier pair;
  repeated prover pair then verifier scalar; prover wire-claim pair; recursive
  tail. The terminal input is verifier-to-prover.
- `initial`: one verifier move with type `Fin d → F`. For `d = 0`, that is the
  singleton empty function space, consistent with a constant output table.
- `spec`: prepends that move to the complete circuit schedule, without shortening
  the circuit or reusing a later challenge.
- `initialValues`: reads the first move with its actual vector type; it does not
  project an arbitrary component of the old fixed-array representation.
- `circuitTranscript`: reads the entire right-hand transcript after the initial
  move, preserving its dependent message types.
- `circuitTrace`: decodes alpha/beta, each alternating response/challenge pair,
  both final wire claims in order, and the recursive tail. The cast between
  `schedule.length` and `2 * inDim` preserves each numeric index. The input case
  reads the final scalar directly.
- `trace`: composes the exact circuit-transcript projection and decoder; the
  initial point is handled separately rather than decoded again as a layer value.
- `circuit_inhabited`: supplies explicit zero-based defaults recursively for each
  message type. These defaults establish inhabited types and do not replace the
  uniform challenge law by a point mass.
- `spec_inhabited`: adds the zero vector default for the initial message to the
  same circuit defaults. No classical selection is needed in this instance.
- `circuit_fintype`: assembles the exact field, pair, and recursive challenge
  enumerations; prover-message branches contain no challenge indices.
- `spec_fintype`: includes the complete finite initial function space, then those
  same recursive enumerations. There is no restricted subset of challenge values.
- `circuit_decidableEq`: uses the supplied field equality and structural product/
  append equality at each actual challenge type; it is not an independent equality
  dictionary chosen through a proposition.
- `spec_decidableEq`: combines finite-function equality for the initial vector
  with the circuit instance, preserving the same append index transports.

## Individual pad entries

Names are relative to `GordieHowe.GKR.PadTranslation`.

- `Pads`: terminal unit, or two coefficient pads for every sumcheck round, three
  claim pads, and the tail's pads. The third claim pad is included in committed
  data even though it is not a separately transmitted wire claim.
- `unmask`: adds coefficient pads to the two revealed polynomial values and the
  first two claim pads to the wire claims. It leaves alpha, beta, every scalar
  round challenge, and the terminal scalar unchanged. Addition is the inverse
  of the prover's subtraction convention, including in odd characteristic.
- `ProductsHold`: checks `claim 0 * claim 1 = claim 2` at every layer and recurses;
  the terminal input has no product equation. This is a checked constraint on
  arbitrary committed pads, not an assumed property of adversarial randomness.
- `FreePads`: samples the two coefficient pads per round and two claim pads per
  layer, with terminal unit. It deliberately does not sample the product pad
  independently, which would generally violate the quadratic constraint.
- `FreePads.instFintype`: recursively enumerates that exact product of field
  function spaces and the tail. Empty round sets have the unique empty function,
  not a missing whole-layer pad component.
- `FreePads.pads`: copies the sampled pads and fills the third claim pad with the
  product of the first two. The named `productsHold` proof establishes every
  layer's equation. It does not claim that this map gives independent uniform
  values for all three committed claim coordinates.

## Outcome

These 20 entries pass current-source review. The existing mask/unmask inverse
lemmas and challenge-preservation equations substantiate the translation, without
requiring honest pads for the inverse identities. The audit makes no production
change, adds no runtime exception, and makes no raw old/new expression identity
claim for the changed initial challenge type. Final closure reconciliation remains
required after the remaining implementation units.
