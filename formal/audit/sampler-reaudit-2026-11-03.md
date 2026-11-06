# Sampler and challenge-reader semantic re-audit, 2026-11-03

Scope: 14 declarations at source commit `19976a779`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.SPBCS.FisherYates.equiv` | 1178909808492428501 | 4631129925605990626 |
| `GordieHowe.SPBCS.Sampler.ofReader` | 236405105399454417 | 165057388984254896 |
| `GordieHowe.SPBCS.CReader.binary` | 12281530937386147149 | 12949415783777930103 |
| `GordieHowe.SPBCS.CReader.choose` | 11076098084334225173 | 920862525728415084 |
| `GordieHowe.SPBCS.CReader.extend` | 4526896100726185488 | 11253526202727682683 |
| `GordieHowe.SPBCS.CReader.grant` | 4877717196801322860 | 16183019880307071108 |
| `GordieHowe.SPBCS.CReader.map` | 10933879210438525788 | 13554600292677130784 |
| `GordieHowe.SPBCS.CReader.mk` | 2907093496 | 2208771318 |
| `GordieHowe.SPBCS.CReader.nat` | 13783976050729327937 | 9323115298234781357 |
| `GordieHowe.SPBCS.CReader.piDep` | 3766748931800607814 | 2700796400305377605 |
| `GordieHowe.SPBCS.CReader.prod` | 7571796294544051103 | 501046665783901524 |
| `GordieHowe.SPBCS.SpecReaders.sampler` | 16032229255829174095 | 11446518838322899649 |
| `GordieHowe.SPBCS.SpecReaders.gkrCircuit` | 15852348668342643406 | 14645575537024215993 |
| `GordieHowe.SPBCS.SpecReaders.gkrSpec` | 1830965165406015662 | 13962918331968565714 |

Historical sources reviewed: the sampler definitions at `ef8908bf`, challenge readers at
`28705d8ee`, and the Fisher–Yates caller at `5831d8fb`, under their former `PQ.BCS` names.
Current source files were compared byte for byte with the compiled acceptance snapshot;
each recorded fingerprint agrees with its actual statement closure. This review updates
historical ledger entries, not Lean declarations or headline statements.

The changes include computational defaults and exact-path unranking added to `CReader`,
an explicit Fisher–Yates inverse, and the historical GKR protocol integration. They are
not classified wholesale as renames or as definitionally identical to the original audit.

- `FisherYates.equiv`: the forward map remains `emb`, which takes the first `k` positions
  after swaps at positions `i` and `i + r i`. The inverse reconstructs each current target
  position using `invState`, then subtracts `i`. Its bounds follow from the injective tuple;
  `emb_inv` and injectivity establish both inverse laws. This replaces the noncomputable
  `Equiv.ofBijective` inverse. If `k > n`, both types are empty; no successful sampling of
  an impossible tuple is implied.
- `Sampler.ofReader`: `sample` is still `R.sampleOf`, preserving `none` on failure.
  Equal counts of each successful value follow from `Reader.Uniform`, which equates counts
  at every exact consumed length. The new explicit default only totalizes challenge
  reads. The acceptance predicate in `SPBCS/Basic.lean` separately requires every sampled
  challenge to be `isSome`, so a default does not turn rejected sampling into acceptance.
- `CReader.mk`: all reader, uniformity and load bounds remain required. New unranking is
  checked by its exact-path interface, and a default supplies an actual challenge value.
  Uniformity alone does not promise positive success probability; exhaustion remains
  charged by the failure bounds, rather than conditioned away.
- `CReader.grant`: this is a natural number of additional stream bytes, defaulting to zero,
  not a nonemptiness hypothesis. Its projection changed with the added structure fields.
- `CReader.extend`: changes only `grant` to `grant + g`; reader, distribution, load,
  unranking and default are preserved. `streamLength` uses `base + grant`; grants do not
  silently enlarge the `Fin (k + e)` input of a sampler constructed with explicit `N`.
- `CReader.map`: maps through a bijection, preserving equal successful fibre counts,
  byte loads, rejection bounds and grant. The unranking is transported and the default
  mapped by the same equivalence. An arbitrary many-to-one map is not accepted here.
- `CReader.prod`: consumes the second reader after the first, sums draw counts and grants,
  takes the maximum byte bound, and uses product unranking and a paired default. Its
  failure estimate is the sum bound; no unsupported independence assumption is added.
- `CReader.piDep`: consumes the finite family in order. The explicit component load bounds
  justify `n * L.draws` and `L.bytes`; grants sum, defaults are pointwise, and unranking
  follows the same dependent product. At `n = 0`, the tuple is unique and the draw/grant
  sums are zero.
- `CReader.nat`: requires `m > 0`, masks to the bit length of `m`, and rejects values at
  least `m`. The acceptance probability is at least one half and the load is one draw
  of `byteLen m`. Its default is the valid element zero; rejection and attempt exhaustion
  are retained. No modulo reduction bias is introduced.
- `CReader.binary`: reads exactly `b` bytes and maps them through the supplied equivalence.
  Every sufficiently long byte string succeeds; the raw reader has no rejection branch.
  Its load remains one draw of `b` bytes, and its default is the image of all-zero bytes.
- `CReader.choose`: requires `k ≤ n` and draws `nat (n - i)` for each `i < k`, so every bound
  is positive. The forward Fisher–Yates map is the same as the older `mapBij` call.
  It samples ordered injective tuples, not unordered subsets. The empty tuple at `k = 0`
  is supported; the load bound is `k` draws with byte bound `byteLen n`.
- `SpecReaders.sampler`: uses attempt bound `N i`, limits the reader to `N i` bytes, then
  runs on the supplied `k + e` byte stream. The new default is inherited explicitly from
  the reader. The theorem identifying its rejection probability with the reader's
  failure probability requires `N i ≤ k + e`; the definition does not assume it silently.
- `SpecReaders.gkrCircuit`: matches the current circuit schedule: input binding draws one
  field element; each layer draws the alpha/beta pair, then `2 * inDim` scalar challenges,
  skips the prover's wire pair, and recursively reads the tail. Prover messages contribute
  no challenge draws. Both base and recursive cases match `GKR.Schedule.circuit`.
- `SpecReaders.gkrSpec`: draws the `d` coordinates of the current initial point and then
  the circuit readers. The historical fixed 40-plus-40 initial draws were replaced by
  the current protocol's `F^d` point during integration. This is a substantive historical
  protocol change, not equality of old and new stream layouts. The source documents the
  C++ grouping distinction; this audit certifies the current reader/schedule correspondence,
  not an unproved byte-for-byte equivalence of those two protocols.

No adversary restriction, additional acceptance branch, excluded bad-randomness event or
new trusted hypothesis was introduced by this ledger update. Generic readers can have
zero success at insufficient budgets; the rejection-probability accounting keeps that
case visible. This review does not assert that every C++ transcript layout equals the
abstract GKR schedule, nor does it authorize the separately parked challenge-default redesign.
