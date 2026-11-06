# GKR source and masked-reduction review, 2026-11-03

Scope: 17 declarations at source commit `2187cfb45`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.GKR.LayeredCircuit.ClaimCommits` | 2321359598 | 2764777213 |
| `GordieHowe.GKR.LayeredCircuit.maskedHonest` | 1470739971179498305 | 7583913798747901455 |
| `GordieHowe.GKR.LayeredCircuit.maskedReduction` | 14609676649642623964 | 4942697920093004050 |
| `GordieHowe.GKR.LayeredCircuit.maskedSound` | 11316055197837263293 | 11894139714470340160 |
| `GordieHowe.GKR.LayeredCircuit.PadIdx` | 11098279301557790699 | 18265930359855187087 |
| `GordieHowe.GKR.LayeredCircuit.Satisfied` | 5175975929013144459 | 3325124134368471676 |
| `GordieHowe.GKR.LayeredCircuit.circuit` | 6412322928998862584 | 9833187942985026025 |
| `GordieHowe.GKR.LayeredCircuit.error` | 9310372783321110532 | 2972281511601857851 |
| `GordieHowe.GKR.LayeredCircuit.inputIndex` | 2683284810238187605 | 10290841146886905546 |
| `GordieHowe.GKR.LayeredCircuit.interaction` | 2713287595364771926 | 4660012825744482696 |
| `GordieHowe.GKR.LayeredCircuit.mk` | 541083845 | 2131573634 |
| `GordieHowe.GKR.LayeredCircuit.padLayout` | 8844761149872569942 | 16022513835593034755 |
| `GordieHowe.GKR.LayeredCircuit.rec` | 583650725 | 528787579 |
| `GordieHowe.GKR.LayeredCircuit.sound` | 11937780220807461774 | 17685999715284024454 |
| `GordieHowe.GKR.LayeredCircuit.tail` | 10737672782332163027 | 16575247685186296596 |
| `GordieHowe.GKR.SourceReduction.ofCircuit` | 13730441052312498595 | 4017708468826699157 |
| `GordieHowe.GKR.SourceReduction.ofCircuitSound` | 10168961731749735048 | 9187714137118103658 |

## Method and historical classification

Reviewed source-circuit wrappers, the source-derived interaction/soundness split,
and the masked reduction against `ef8908bfd`, `5831d8fbc`, and `4cd3a9bb1` as
indicated by the ledger. The historical counterpart of the current masked
reduction is `GKR/ClaimIP.lean`, not the old `GKR/MaskedIP.lean`; the latter contains
other superseded constructions and is not used to justify this audit.

The circuit's uniqueness and fixed output-capacity fields disappeared with the
previously reviewed grouped assertion relation and actual-dimensional initial
challenge. The old all-in-one source reduction was separated into computational
interaction data and soundness/error records. The masked reduction's simulator
is now a separate named argument to honesty, and its simulation law is required
at every honest input, not merely satisfying inputs. Current source and fingerprints
are verified against the compiled acceptance snapshot.

## Individual source-circuit entries

Names are relative to `GordieHowe.GKR.LayeredCircuit`.

- `mk`: constructs output/input dimensions, the complete corner array, tail, and
  equality of terminal input dimension to the advertised dimension. The source
  always has at least its head layer. It no longer asserts unique assertion gates
  or a fixed capacity; neither is silently assumed later.
- `rec`: the generated eliminator uses these current fields and their dependent
  types, without the removed premises. No separate axiom or source recursor is added.
- `tail`: the actual circuit at the head layer's input dimension, retaining every
  lower layer and its input-dimension computation.
- `circuit`: exactly combines the head layer and tail. It does not replace the
  source by a circuit satisfying an unrelated relation.
- `PadIdx`: the full recursive pad index of that combined circuit.
- `padLayout`: the layout of the head and tail, with `tail.depth + 1` layer entries
  represented by `Transcript.Layout` at index parameter `tail.depth`.
- `inputIndex`: transports `Fin (2^tail.inputDim)` to `Fin (2^d)` with the stored
  dimension equality. This is an equal-size index transport, not truncation.
- `Satisfied`: applies the complete circuit relation to the input through that
  transport; its grouped-assertion meaning and limits are recorded separately.
- `interaction`: transports the input-dimension equality and invokes the source
  construction with the same head and tail. It contains executable schedule and
  readout data, without passing the noncomputable error record as runtime data.
- `error`: uses the exact protocol's challenge-indexed error function after that
  same transport. The shape-bound API separately bounds the top output dimension,
  so removing the old capacity field does not produce a free fixed-size error bound.
- `sound`: transports the input equality and invokes the proved source soundness
  constructor. Its explicit `hcompile` is functional compiler correctness from
  this circuit's satisfaction to the desired relation; it is not a statistical
  GKR assumption or a restriction on cheating prover values.

## Individual source-reduction entries

Names are relative to `GordieHowe.GKR.SourceReduction`.

- `ofCircuit`: constructs the full typed schedule and computes both terminal
  points and the flat transcript from the source and actual trace, starting both
  points at the same initial challenge vector. It retains the final scalar
  input-binding challenge. The caller does not supply a transcript correspondence.
- `ofCircuitSound`: maps the public/witness context to the actual input and pad
  readouts, applies the source reduction, and uses `hcompile` in the direction
  circuit satisfaction implies the requested relation. The terminal predicate is
  related by `CircuitFlatten.terminal_iff`, an equivalence, so no acceptance
  obligation is dropped. A vacuous target relation could make a generic theorem
  uninteresting; this interface does not certify a chosen application's relation
  without its actual compiler theorem.

## Individual masked-reduction entries

Names are relative to `GordieHowe.GKR.LayeredCircuit`.

- `maskedReduction`: has exactly one finalization row and one pad product for
  every head/tail layer (`Fin (tail.depth + 1)`), plus exactly one logical input
  claim. It uses the same interaction and pads throughout. The claim is over the
  logical level, with committed pad coordinates mapped through `L.cell`; it is
  not mistaken for an already-checked row on packed cells.
- `maskedSound`: composes source soundness for the logical input with the exact
  output equivalence: all pad equations and the terminal weighted input equation.
  The functional compiler implication here is the identity on source satisfaction.
  All challenges and their error terms remain those of the source interaction.
- `ClaimCommits`: conjuncts exact pad-cell values with equality of the logical
  circuit input. It intentionally need not equate every unused logical coordinate.
  Aliased pad locations may make a particular commitment impossible; the generic
  interface does not assert existence of a committing witness for arbitrary layouts.
- `maskedHonest`: runs the same source prover on the logical assignment with free
  pads; completeness uses both commitment fields and `Level.view_cell` to identify
  the actual committed input and pads. The simulator uses the named `maskedSim`
  with the same free-pad space. Its equal-law proof is unconditional in the input,
  a stronger obligation than the older domain-restricted honest interface. Source
  satisfaction is still required for completeness, not for this simulation law.

## Outcome

These 17 declarations pass current-source review. The review distinguishes the
computational interaction from noncomputable proof/error records and makes no
new runtime exception. It changes no Lean source, headline, hypothesis, or
sampling distribution. Final-head closure reconciliation remains required.
