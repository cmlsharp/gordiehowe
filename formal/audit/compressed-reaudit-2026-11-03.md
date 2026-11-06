# Compressed-oracle source and equality re-audit, 2026-11-03

Scope: 12 declarations at source commit `b15fea29a`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.QROM.compressedOracle` | 12512543508168980822 | 15085911667758494678 |
| `GordieHowe.QROM.decOp` | 14187337883742132144 | 1735853028613711365 |
| `GordieHowe.QROM.decX` | 9829082505351029668 | 4340068892626477396 |
| `GordieHowe.QROM.hadamard` | 625427347977783175 | 14211149586093325737 |
| `GordieHowe.QROM.invSqrtCard` | 10177481340864613450 | 5914664459948558237 |
| `GordieHowe.QROM.phaseOp` | 12515585646574635505 | 18219313257379743147 |
| `GordieHowe.QROM.simInit` | 1476253534278078565 | 14467712847827655372 |
| `GordieHowe.QROM.simLaw` | 3037781344274976399 | 17633161969776871695 |
| `GordieHowe.QROM.simQuery` | 7584616059804056046 | 5700433692562467559 |
| `GordieHowe.QROM.simStage` | 10158890880319685578 | 3314850423980648864 |
| `GordieHowe.QROM.simState` | 2918103136778624713 | 13192061242550197173 |
| `GordieHowe.QROM.simStep` | 16647218051286498158 | 477052415316305107 |

The complete historical source at `f01311529` was compared with the current module.
The only source changes are the copyright header and three named Prop-valued instances:
`instNonemptyBitStr`, `instNeZeroTwo`, and `instAtLeastTwo12`. No algorithm, branch,
parameter or probability expression changed. The historical source SHA256 is
`4553b0a2c5d6cc9d5941826d1a45fea6aa0c7e710b9fd7849c5aedd771533e7b`; the current source is
`4ab5ab6f3db620dbee92d967c5e9e3413a5d8185dd47efd4ea3e084831905539`.
Current source bytes match the compiled snapshot and all twelve measured fingerprints
match the current statement closure.

A bounded scratch probe replayed the complete historical source in an isolated
namespace, disabled exactly those three new instances, and renamed three root-qualified
proof lemmas to avoid duplicate names. All twelve complete named historical/current
constant equalities passed ordinary kernel-checked `rfl`. A separate check compared each
actual type and definition body at reducible transparency after normalizing only the
historical namespace and private names. All twelve passed. Probe SHA256:
`710b018ab4ded7e7a0ed1b7544a01d7a192055a5baabfb1203143bb2717c9311`.
The coordinator reviewed the probe, whole-source diff, source hashes and accepted log.
No Model source is edited by this audit.

Provenance limitation: the replay uses the current imported environment. Five old raw
fingerprints are reproduced, while seven differ from the historical ledger. Accordingly,
this is a fresh semantic/source review supported by equality of the reconstructed
constants, not a claim to reproduce the complete historical environment. No headline
fingerprint is changed, and no headline-rule exception is being exercised.

Per-declaration semantic review:

- `invSqrtCard` is the inverse square root of the bit-string cardinality, embedded from
  the reals into the complexes. Bit strings are nonempty even for empty index types;
  the normalization denominator is positive.
- `hadamard` changes only the answer register. It preserves work, query input and
  database coordinates, with coefficient `invSqrtCard * signOf (u.dot y)`. The sign
  remains the mod-two character and both normalization and register guards are present.
- `decX` distinguishes an absent query at spare capacity, an absent query at capacity,
  and an existing query. The existing-query branch still acts at full capacity, with
  the erased-database term and twice-normalized sum. It does not incorrectly make all
  full databases fixed points. Its intended database domain remains `size ≤ t`.
- `decOp` applies `decX` only to valid database states, preserves adversary registers,
  and is the identity on other database basis states. It does not discard those states.
- `phaseOp` is diagonal on the entire register and uses the database phase with
  missing-answer phase one. No measurement or postselection appears in this operator.
- `compressedOracle` composes `Dec`, then the phase operator, then `Dec`; both
  decompression factors are retained in the same order.
- `simQuery` surrounds the compressed phase oracle by two answer-register Hadamard
  transforms, preserving the standard-oracle interface.
- `simInit` tensors the algorithm's actual initial amplitudes with the empty database
  basis state. It does not resample or normalize the adversary's state.
- `simStep` extends the algorithm's indexed unitary by the identity on the database.
  Its total-index behavior is inherited from `stepAt`; no out-of-range query is inserted.
- `simStage` begins with step zero applied to the initial state, then performs one
  query followed by step `k + 1` at each recurrence. At zero iterations no query occurs.
- `simState` selects exactly `t` such iterations for an algorithm with `t` queries;
  the initial step is not counted as an extra oracle query.
- `simLaw` pushes forward the Born weights jointly to the algorithm's output and the
  measured database. It preserves their joint law rather than replacing it with a
  product of marginals or conditioning on a successful output. Its normalization is
  proved separately by the existing unitary/norm theorems.

These are mathematical quantum-state operators and their measure, not a new classical
runtime simulator implementation. This ledger update adds no computability exemption,
trust assumption, source declaration or resource-limit override.
