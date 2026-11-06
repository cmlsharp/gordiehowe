# FieldProof masked-reduction review, 2026-11-03

Scope: 30 declarations at source commit `c693adec5`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.FieldProof.MaskedReduction.Honest` | 1237146069 | 2546512877 |
| `GordieHowe.FieldProof.MaskedReduction.Honest.Commits` | 3290830080241748426 | 5129605012986372247 |
| `GordieHowe.FieldProof.MaskedReduction.Honest.Pads` | 15498001897287199388 | 519344968199447564 |
| `GordieHowe.FieldProof.MaskedReduction.Honest.append` | 16590968701157735494 | 11068523380599160959 |
| `GordieHowe.FieldProof.MaskedReduction.Honest.close` | 6398522413484845721 | 11319383620903566617 |
| `GordieHowe.FieldProof.MaskedReduction.Honest.comap` | 6122140711685654133 | 5068080204640298694 |
| `GordieHowe.FieldProof.MaskedReduction.Honest.combine` | 13378106304076200219 | 16163040693531050499 |
| `GordieHowe.FieldProof.MaskedReduction.Honest.fintype` | 3130382534101249096 | 1773676692620466271 |
| `GordieHowe.FieldProof.MaskedReduction.Honest.identDistrib` | 1503048737 | 3074441800 |
| `GordieHowe.FieldProof.MaskedReduction.Honest.mk` | 1022350815 | 517350444 |
| `GordieHowe.FieldProof.MaskedReduction.Honest.nonempty` | 3347283675 | 4254573792 |
| `GordieHowe.FieldProof.MaskedReduction.Honest.prover` | 8308705141517462057 | 6176061956592563152 |
| `GordieHowe.FieldProof.MaskedReduction.Honest.static` | 17346378976828449689 | 3711396551421230189 |
| `GordieHowe.FieldProof.MaskedReduction.Honest.withCommits` | 10834597674112453531 | 15845115149648094836 |
| `GordieHowe.FieldProof.MaskedReduction.close` | 11378383153736161439 | 129743023107332407 |
| `GordieHowe.FieldProof.MaskedReduction.combine` | 14465929257311504797 | 15821110715235368774 |
| `GordieHowe.FieldProof.MaskedReduction.static` | 3250012860943075670 | 17739063250711039056 |
| `GordieHowe.FieldProof.MaskedRowReduction.Honest` | 133615422 | 2320785083 |
| `GordieHowe.FieldProof.MaskedRowReduction.Honest.Commits` | 10188242491882688743 | 13932199098549293471 |
| `GordieHowe.FieldProof.MaskedRowReduction.Honest.Pads` | 16128527763638725220 | 6076235440098298470 |
| `GordieHowe.FieldProof.MaskedRowReduction.Honest.fintype` | 13702909347173259836 | 8744456670651789051 |
| `GordieHowe.FieldProof.MaskedRowReduction.Honest.mk` | 1629486756 | 384658625 |
| `GordieHowe.FieldProof.MaskedRowReduction.Honest.prover` | 14354875631000635436 | 5779141439819307596 |
| `GordieHowe.FieldProof.MaskedRowReduction.Q` | 14336102633870859028 | 16987769118102720956 |
| `GordieHowe.FieldProof.MaskedRowReduction.append` | 15938889392781735120 | 17498923177693699932 |
| `GordieHowe.FieldProof.MaskedRowReduction.finQ` | 7911089893474475819 | 17009883730815721387 |
| `GordieHowe.FieldProof.MaskedRowReduction.linear` | 4741186523969951342 | 18052879133889444412 |
| `GordieHowe.FieldProof.MaskedRowReduction.mk` | 2435048053 | 2597281846 |
| `GordieHowe.FieldProof.MaskedRowReduction.products` | 15030528879326387965 | 3838650938186455924 |
| `GordieHowe.FieldProof.MaskedRowReduction.static` | 7569233220491061614 | 15160214181247969260 |

## Method and historical changes

Reviewed the current declarations and their constructor/projection dependencies in
`MaskedReduction.lean` and `MaskedRowReduction.lean`, against historical source at
`4cd3a9bb1`, `5831d8fbc`, `b46e966d0`, and `407240beb` as applicable to the ledger entries.
The old `ClaimIP` and `MaskedIP` names were followed to their current names. This is
an adversarial review of the current semantics, not a claim that every old expression
is definitionally identical. The current source bytes and fingerprints are checked
against the compiled acceptance snapshot before recording these entries.

The row interface now carries `Encodable` dictionaries for both row index types,
providing explicit finite numbering. These are computational data, not assumptions
excluding adversaries or challenges. The later simulator split supplies a named
`IOP.TranscriptSim` as a parameter instead of storing its coins and function in the
honest record. The masked-reduction simulation law was also strengthened historically:
it is unconditional in the honest input, whereas the older source required its domain
predicate. The row-reduction law still requires the domain. These distinctions are
reviewed below rather than attributed solely to renaming.

## Per-entry review

Names in the following paragraphs are relative to `GordieHowe.FieldProof`.

- `MaskedRowReduction.mk`: constructs the protocol, challenge dictionaries, linear
  index and its finite encoding, affine rows, product index and its encoding, and
  fixed product layout. No soundness assertion is smuggled into this data constructor.
- `MaskedRowReduction.linear`: reads affine rows at the public input and full
  transcript. All linear indices remain quantified by `RowsHold`.
- `MaskedRowReduction.Q`: the product index type, independent of challenges.
- `MaskedRowReduction.finQ`: the finite dictionary for precisely that index type;
  it does not drop product rows or introduce an independent cardinality assumption.
- `MaskedRowReduction.products`: reads the fixed layout before interaction; the
  verifier cannot select a weaker layout after seeing a challenge.
- `MaskedRowReduction.append`: concatenates round specifications and uses disjoint
  sums for both row families, with the appropriate left/right transcript projections.
  Both constraint families survive; an empty family does not erase the other.
- `MaskedRowReduction.static`: has zero rounds and the supplied fixed rows and
  products. A unique empty transcript does not imply an empty constraint set.
- `MaskedRowReduction.Honest`: keeps completeness on the honest domain and on every
  witness satisfying `Commits`, while simulation is against the named public-input
  simulator on that domain. Neither obligation restricts a cheating prover.
- `MaskedRowReduction.Honest.mk`: requires both laws, finite nonempty pads, and the
  actual causal prover; it cannot manufacture a simulator merely by existential choice.
- `MaskedRowReduction.Honest.Pads`: the honest randomness type, not verifier challenges.
- `MaskedRowReduction.Honest.fintype`: the finite dictionary on those same pads, used
  by the uniform law.
- `MaskedRowReduction.Honest.prover`: the causal family indexed by public input,
  honest input, and pads; future challenges are not available to earlier messages.
- `MaskedRowReduction.Honest.Commits`: the relation binding this input and these pads
  to the committed witness. It may be empty for a generic record; a concrete
  completeness application must separately produce a committing witness.
- `MaskedReduction.Honest`: extends completeness to every output claim as well as
  every row. Its simulation law is unconditional in public and honest input, a
  stronger obligation than the old domain-restricted version.
- `MaskedReduction.Honest.mk`: requires the specified named simulator's law and the
  output completeness proof; no arbitrary simulator existence is accepted.
- `MaskedReduction.Honest.Pads`: the exact pad type used by the prover and its law.
- `MaskedReduction.Honest.fintype`: the finite dictionary for that type; there is no
  alternate sampling measure hidden in this projection.
- `MaskedReduction.Honest.nonempty`: ensures uniform pad sampling is defined. This
  is an honest randomness requirement, not an adversarial exclusion.
- `MaskedReduction.Honest.prover`: causal transcript generation from the input and
  committed pads, with the same specification as the masked reduction.
- `MaskedReduction.Honest.Commits`: the same conditional witness obligation described
  above. The interface alone does not assert existence of such witnesses.
- `MaskedReduction.Honest.identDistrib`: compares the complete honest transcript
  under uniform pads to the fixed named simulator for every fixed challenge tuple;
  it does not assume that input belongs to the completeness domain.
- `MaskedReduction.close`: keeps the specification and products and adds every claim
  as a linear row through `M.Lin ⊕ Fin nc`. `rowsHold_close_iff` identifies the exact
  conjunction; neither the first nor last claim is omitted, including when `nc = 0`.
- `MaskedReduction.Honest.close`: preserves pads, prover, and commitment relation;
  completeness uses that exact conjunction equivalence. Its unconditional simulation
  law legitimately specializes to the row interface's domain-restricted law.
- `MaskedReduction.Honest.append`: uses product pads, causal concatenation, and the
  conjunction of both commitment relations for the same witness. The second input
  includes the first pads. Its simulation argument uses the second law for every
  first-pad value before joining transcripts, rather than assuming an unjustified
  independence of the honest transcripts.
- `MaskedReduction.static`: retains all supplied affine claims, with no interactive
  rounds and empty underlying row/product index types.
- `MaskedReduction.Honest.static`: uses unit pads and the empty causal transcript;
  its explicit `hcomplete` obligation proves every claim for every committing witness
  in the domain. The empty transcript does not discharge those claims automatically.
- `MaskedReduction.combine`: appends one verifier coefficient-vector round after
  the claims have been fixed and replaces them by their affine linear combination;
  the old rows and products remain. For zero claims the sum is zero; for any nonzero
  claim vector the existing counting argument charges at most `1 / |F|`, including
  the one-claim case. No bad coefficient vector is excluded by a hypothesis.
- `MaskedReduction.Honest.combine`: retains the pads and commitment relation, copies
  the new challenge into the appended transcript, and proves the sum of zero claim
  values is zero. The simulator uses the same public challenge.
- `MaskedReduction.Honest.comap`: precomposes honest inputs and their commitment
  relation. The explicit domain implication is used for completeness only; the
  unconditional simulation law applies to the mapped input without that implication.
- `MaskedReduction.Honest.withCommits`: strengthens the honest commitment predicate
  to a conjunction while leaving prover, pads, and simulator unchanged. Completeness
  projects the original conjunct. It does not prove the added predicate inhabited,
  change verifier acceptance, or weaken the adversarial soundness relation.

## Scope and outcome

These 30 declarations pass this current-source review. The changes represented by
these stale fingerprints include explicit finite encodings, named simulator/data
separation, and the stronger simulation obligation, in addition to namespace moves.
No Lean source, headline, hypothesis, distribution, or exception list is changed by
this audit commit. Final-head closure reconciliation remains a separate gate step.
