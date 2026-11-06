# Ring-switching routing semantic re-audit, 2026-11-03

Scope: 12 declarations at source commit `3dc2ddf0b`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.FieldProof.MaskedReduction.Honest.combineFirst` | 15889332180854038394 | 9132994669652275585 |
| `GordieHowe.FieldProof.MaskedReduction.Honest.measureHead` | 6786308563771651212 | 14072581109582492664 |
| `GordieHowe.FieldProof.MaskedReduction.Honest.reorder` | 18297794044527678000 | 10173125309910242100 |
| `GordieHowe.FieldProof.MaskedReduction.Honest.routedStage` | 3138204447472536379 | 1211729734773597329 |
| `GordieHowe.FieldProof.MaskedReduction.Sound.routedStage` | 4840810585693554102 | 3565960923735322293 |
| `GordieHowe.FieldProof.MaskedReduction.combineFirst` | 860665763617370072 | 11358355267457499441 |
| `GordieHowe.FieldProof.MaskedReduction.measureHead` | 10389405612995792285 | 9784329053985625503 |
| `GordieHowe.FieldProof.MaskedReduction.routedStage` | 3214510148033990421 | 9865949115329850069 |
| `GordieHowe.FieldProof.MaskedReduction.routedStageError` | 6087033402431345823 | 5113000212082701090 |
| `GordieHowe.StageRouting.combinations` | 17954088047309950674 | 6299354147797281202 |
| `GordieHowe.StageRouting.rec` | 1606076208 | 3522642523 |
| `GordieHowe.StageRouting.split` | 5287724933764036838 | 5445895073090432786 |

Reviewed the historical `PackingRoute` at `b67250008` and `407240beb`, including the
former `ClaimIP` names, against the current whole module. Current source bytes and
all twelve fingerprints match the compiled acceptance snapshot. Historical changes
include the zero-touching branch, named simulator separation and factoring the
routing into `touch` followed by measurement; this is not merely a namespace refresh.

- `StageRouting.rec`: the generated eliminator now covers `none`, `single` and
  `combine`. The new `none` branch carries an equivalence from all incoming claims
  to the passing claims, so it cannot discard an incoming claim. `single` selects
  exactly one touching claim; `combine` requires at least two. Constructor indices
  determine the branch counts, with no arbitrary missing case.
- `StageRouting.split`: `none` embeds the passing equivalence into the right side
  of `Fin 0 ⊕ Fin np`; the other branches retain their supplied bijection. Thus
  touching and passing claims partition the incoming indices without duplication.
- `StageRouting.combinations`: counts zero for none/single and one for combine.
  It counts random linear-combination rounds, not the number of coefficients.
- `MaskedReduction.combineFirst`: appends one verifier challenge containing one
  field coefficient per touching claim. It replaces only the first `nt` claims
  by their linear combination, retaining the passing claims and all linear and
  product constraints. The first segment uses `Fin.castAdd`, the second
  `Fin.natAdd`; no end index is omitted. The routed caller invokes this branch
  only for `nt ≥ 2`; its soundness retains the `1/|F|` bad-combination event.
- `Honest.combineFirst`: keeps pads and commitments, appends the same challenge
  to the causal prover, and transports its distribution through the named
  `Sim.combineFirst`. No fresh prover randomness or validity conditioning enters
  this step. Compared with the older source, the simulator is now an explicit
  parameter of the correctness bundle and the distribution law is unconditional
  in the honest input, which strengthens rather than weakens that law.
- `Honest.reorder`: keeps the exact prover, pads, commitments and simulator;
  only the claims use the inverse permutation. Completeness follows from the
  bidirectional claim-equivalence theorem, not an extra restriction on inputs.
- `MaskedReduction.measureHead`: appends a prover message of `d` field elements,
  replaces the head by the stage's `d + 1` rows, and passes the remaining `np`
  claims through `restPart`. Product constraints include both existing and mask
  triples. This construction alone is not a claim of soundness for arbitrary
  passing rows: the accompanying soundness requires their child coefficients
  to vanish for every public input and transcript.
- `Honest.measureHead`: uses independent paired pads for the preceding prover
  and the masks. `hword` ties computed words to committed cells; mask commitments
  tie the fresh masks to those cells. Completeness retains both commitments.
  Distribution equality uses the mask's uniform law and translation by a fixed
  vector after fixing the preceding pads; no independence from an adaptively
  chosen previous transcript is asserted without that conditioning argument.
- `MaskedReduction.routedStage`: performs `touch`, then the same head measurement.
  With no touching claims it prepends a zero claim and preserves every passing
  claim; with one it only reorders; with multiple it combines first. The zero
  claim is additional, not a replacement for an original obligation.
- `routedStageError`: retains all previous round errors, adds `1/|F|` exactly in
  the combine branch, and adds none for the prover-only measurement. The checked
  sum theorem gives old error plus `R.combinations / card F`; it does not divide
  by the count of touching claims or omit their combination event.
- `Sound.routedStage`: retains the explicit relative-Frobenius-order assumption,
  previous soundness and structural `PassingAvoid`. Its result is sound for
  `masks.Valid (cells w) → sat p w`, exactly as documented in the old source.
  This implication can be vacuous when masks are invalid; downstream full
  soundness must establish mask validity. This audit does not relabel it as
  unconditional soundness. `PassingAvoid` quantifies over all transcripts, so
  it is a restriction on the reduction's row syntax, not on the adversary.
- `Honest.routedStage`: composes the same branch-specific honest step with head
  measurement and the named simulator. It preserves the word/commitment and
  passing-row premises, and pairs fresh mask pads only at measurement.

No Lean declaration is edited here. This audit records current behavior and the
scope of its hypotheses; it does not claim definitional equality of the historical
and current protocol types, nor discharge mask validity for arbitrary instances.
