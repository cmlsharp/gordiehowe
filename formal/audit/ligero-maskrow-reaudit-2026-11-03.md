# Ligero prefix-row layout audit, 2026-11-03

Scope: 16 declarations at source commit `350c6aaa8`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.Ligero.MaskRow.TreeLayout.Numbers.hidingData` | 8009821584085523501 | 16269239500434593216 |
| `GordieHowe.Ligero.MaskRow.TreeLayout.Numbers.mk` | 2265719695 | 84487224 |
| `GordieHowe.Ligero.MaskRow.TreeLayout.Numbers.setup` | 15930524333851377595 | 9854113700047728970 |
| `GordieHowe.Ligero.MaskRow.TreeLayout.Numbers.splitSetup` | 13481768895250005150 | 8710093905009689764 |
| `GordieHowe.Ligero.MaskRow.TreeLayout.Numbers.tableau` | 12190072472838457530 | 17277827865005026798 |
| `GordieHowe.Ligero.MaskRow.TreeLayout.place` | 17799427716073429842 | 15854652005630859285 |
| `GordieHowe.Ligero.MaskRow.TreeLayout.pos` | 11127381801251674648 | 6017322929709624571 |
| `GordieHowe.Ligero.MaskRow.hidingLayout` | 13411706628976831181 | 7164127746826348167 |
| `GordieHowe.Ligero.MaskRow.prefixFields` | 3897634165212480017 | 6339689001135299709 |
| `GordieHowe.Ligero.MaskTest.hidingOf` | 12165874833256180754 | 6466928470244342024 |
| `GordieHowe.Ligero.MaskRow.Setup.Admissible` | 2466366650644952672 | 11093146029567326772 |
| `GordieHowe.Ligero.MaskRow.Setup.bounds` | 12206772874849862117 | 10320192191517574817 |
| `GordieHowe.Ligero.MaskRow.Setup.commitError` | 4957053525730750549 | 260754453464043284 |
| `GordieHowe.Ligero.MaskRow.Setup.honest` | 563649487088030783 | 677275603779479442 |
| `GordieHowe.Ligero.MaskRow.Setup.honestConfined` | 10172028245218771735 | 6161308623003497181 |
| `GordieHowe.Ligero.MaskRow.Setup.simulate` | 14288710077748500327 | 3714927960762905834 |

## Evidence and classification

Read MaskRow/Layout and MaskRow/Masked, including each selected constructor,
placement bounds, setup dispatch, hiding data and confined honest construction.
Historical counterparts were compared at c0304fc4a, b67250008, aaf4876b8 and
f01311529 as listed in the entry inventory. The aaf4876b8 files are under the
reorganized MaskRow path, not the absent earlier Prefix path. Selected current
sources and fingerprints match the accepted compiled closure.

Substantive changes include support for either masking, privacy width separate
from query count, computational finite encodings/decision procedures, repeated
low-degree tests and a simulator separated from the honest bundle. The split
mask covering condition remains explicit. This review does not classify these
as namespace-only changes.

## Per-declaration review

Names have prefix `GordieHowe.Ligero`.

- `MaskRow.prefixFields`: assigns E exactly to rows containing a prefix cell,
  and the full field otherwise. Membership uses a supplied decision for E;
  no nonprefix data row is accidentally constrained to E.
- `MaskRow.hidingLayout`: combines those fields with actual node/code-point
  membership, off-witness/nonempty-witness facts and allocation conditions. Its
  equality procedure is data; all mathematical layout conditions stay explicit.
- `MaskTest.hidingOf`: builds the inner layout, aliases/product coverage,
  privacy bound, free piece rows and 2t≤k, and proves every prefix cell's row
  uses E. It does not omit either hiding bound.
- `MaskRow.TreeLayout.pos`: prefix cells occupy their own initial indices;
  words start after ceil(np/w)*w padded positions; root coordinates follow the
  words via Encodable.fintypeEquivFin. The embedding proof handles all nine
  cross-class cases and bounds, preventing aliasing with prefix padding.
- `MaskRow.TreeLayout.place`: composes that embedding with the ordinary shape
  placement and product enumeration, preserving exact source/copy positions.
- `MaskRow.TreeLayout.Numbers.mk`: keeps shape validity and point membership
  in E, now stores the selected masking and its Covers condition. Covers is
  trivial for untested masks and exactly 2t≤k for split masks; it is a parameter
  fact, not an assumption about an adversary.
- `MaskRow.TreeLayout.Numbers.tableau`: uses no extra rows for untested masks
  and six for split masks, through tableauOf and the chosen masking.
- `MaskRow.TreeLayout.Numbers.splitSetup`: places the six rows after data and
  product rows, uses actual encoded product/linear-row enumerations, and passes
  the specified threshold/line certificate, nrep, query count and prefix field
  facts. The required mask rate follows from layout validity.
- `MaskRow.TreeLayout.Numbers.setup`: dispatches to the matching setup for
  the masking stored in Numbers, with the corresponding dependent tableau type.
  It cannot silently use split parameters for an untested-mask tableau.
- `MaskRow.TreeLayout.Numbers.hidingData`: dispatches along the same masking
  and supplies stored coverage plus proved allocation/privacy/free-row facts.
  It constructs parameter evidence, not an assumed successful transcript.
- `MaskRow.Setup.commitError`: returns the selected setup's repeated
  low-degree exceptional-event bound. No additional challenge is omitted.
- `MaskRow.Setup.bounds`: returns that commit term and the selected masking's
  test/column terms. The joint subfield term is separately added by error_sum
  when np is nonzero; this tuple alone is not advertised as the full error.
- `MaskRow.Setup.Admissible`: dispatches to the actual inner honest placement
  predicate for the chosen masking. The admissible_honest equation confirms
  that it is exactly the honest bundle's condition.
- `MaskRow.Setup.honest`: dispatches to the matching honest prover, now typed
  against the separately named simulator. It retains its existing
  noncomputability; this ledger update grants no runtime exception.
- `MaskRow.Setup.simulate`: dispatches to the correct underlying named
  simulator with the same public context/challenges/coins and maps the view
  through the prefix-test wrapper. Coins come from the simulator, not a
  noncomputable honest bundle, and the map remains computable.
- `MaskRow.Setup.honestConfined`: retains the original coins, commitment,
  causal transcripts, admissibility and completeness. Only extraction is
  confined; hiding is mapped through the same viewConfine as simConfined.
  It does not claim that replacing invalid extracted prefix coordinates by
  zero preserves arbitrary rows: soundConfined uses the established SoundOn
  guarantee and confines-good/id-on-good facts.

## Boundaries and scope

Valid gives positive witness width, enough privacy and query/domain bounds.
The np=0 case has zero padded prefix rows and no prefix membership constraint;
other coordinate blocks still have distinct offsets. PrefixRowsPure ensures
all occupied entries of a prefix row originate from prefix cells, so subfield
blinding does not silently assume unrelated witness values are in E. Product
rows and piece rows are separated by the actual placement lemmas. Hiding has
its own honest-input admissibility; soundness accounts for failed subfield
membership through the joint column event rather than excluding challenges.

Only audit records and this report change. No protocol definition, headline,
distribution, hypothesis or CostLint exception is altered. Reconcile the final
closure after the remaining implementation lands.
