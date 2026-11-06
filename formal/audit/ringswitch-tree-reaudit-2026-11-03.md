# Ring-switching honest tree semantic re-audit, 2026-11-03

Scope: 12 declarations at source commit `ea063b999`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.RingSwitching.Tree.honestRun` | 13839150237594245304 | 17222215083237433926 |
| `GordieHowe.RingSwitching.TreeFieldProof.HonestData` | 3733225184 | 3161402044 |
| `GordieHowe.RingSwitching.TreeFieldProof.HonestData.cells` | 15553040735294322956 | 11150379696011718699 |
| `GordieHowe.RingSwitching.TreeFieldProof.HonestData.commits` | 2932386106 | 3707502483 |
| `GordieHowe.RingSwitching.TreeFieldProof.HonestData.maskedReduction` | 9033490160743114633 | 16346016574760281741 |
| `GordieHowe.RingSwitching.TreeFieldProof.HonestData.masks` | 7342148640881587860 | 3322080728023267585 |
| `GordieHowe.RingSwitching.TreeFieldProof.HonestData.mk` | 1100278636 | 3838676018 |
| `GordieHowe.RingSwitching.TreeFieldProof.HonestData.val` | 269582681367691605 | 1862543527796228853 |
| `GordieHowe.RingSwitching.TreeFieldProof.HonestData.val_word` | 678210192 | 714949673 |
| `GordieHowe.RingSwitching.TreeFieldProof.completeness` | 978634702 | 1340647187 |
| `GordieHowe.RingSwitching.TreeFieldProof.honest` | 16134197377056447926 | 4818795039475666750 |
| `GordieHowe.RingSwitching.TreeFieldProof.hvzk` | 386098142 | 2788366247 |

Historical `PackingTree` and `TreeDomain` at `407240beb`, and the older `TreeDomain`
at `f01311529`, were compared with the current modules. The relevant historical
changes separate named simulator data from honest correctness and factor identical
routed recursion cases. Current bytes and all twelve fingerprints agree with the
compiled acceptance closure. No Lean source or headline is modified in this audit.

- `Tree.honestRun`: nil returns the preceding honest reduction. A full stage and
  a routed stage each consume the head mask bundle, perform the corresponding
  honest stage, and recurse using the tail masks. Routed recursion retains both
  the passing-row obligation and the tail routing obligations. After adding fresh
  stage pads, old word values use the first pad projection; recursive word proofs
  use the corresponding first commitment projection. Thus current pads do not
  alter previously committed words. The simulator is the named `simRun`, built
  from the preceding simulator and the same tree, independently of honest inputs.
- `TreeFieldProof.HonestData`: fixes a `SimData` value before the honest input
  implementation. Its fields tie the masked-reduction prover, all stage masks,
  computed words and actual committed cells to that same simulator and hiding
  layout. The former hiding field moved to `SimData`; it was not dropped.
- `HonestData.mk`: requires all commitment and admissibility proofs together with
  the data. It provides no automatic witness satisfying a false honest domain.
  These are honest-implementation obligations, not assumptions restricting a
  cheating prover in the separately stated soundness theorem.
- `HonestData.maskedReduction`: projects the honest masked reduction at the
  tree's logical view and the fixed `SD.maskedReduction`. It cannot choose a
  different simulator for each honest witness.
- `HonestData.masks`: contains a valid honest mask bundle for every stage. Uniformity,
  mask/product consistency and validity remain required by those bundles; no stage
  is skipped when its routing has no touching claims.
- `HonestData.val`: computes word values from the public input, honest input and
  preceding masked-reduction pads. It has no future challenge argument.
- `HonestData.val_word`: quantifies over all committed assignments matching those
  pads and every coordinate marked as a stage word. It identifies the logical
  cell view with the computed value. Its restriction to word coordinates is
  precisely what the stage measurement reads; it does not claim all coordinates
  are independent of fresh masks.
- `HonestData.cells`: supplies actual cells from the honest input and the complete
  tree-run pads, including every stage's mask pads. It does not read verifier
  challenges or choose cells after the proof transcript.
- `HonestData.commits`: proves those actual cells satisfy the whole run's
  commitment predicate for every pad value on the honest domain. It therefore
  prevents a vacuous commitment relation from establishing completeness for a
  supplied valid input. The separate admissibility field is also retained.
- `TreeFieldProof.honest`: assembles the closed honest tree run, Ligero's confined
  honest prover, and the supplied cells/commitments. Admissibility is transported
  through its established characterization at the same hiding data. Its existing
  `noncomputable` annotation is not removed or exempted by this semantic audit;
  the runtime issue belongs to the separately recorded computability work.
- `TreeFieldProof.completeness`: requires `dom pub x` and proves acceptance for
  every prover coin value and every challenge tuple of both commit and proof
  phases. It is not an existential success claim and does not exclude bad draws
  by an added premise. Like any generic honest-domain theorem it may have no
  application when `dom` is empty; concrete instantiations must supply valid inputs.
- `TreeFieldProof.hvzk`: states perfect simulation for the named
  `FieldProof.simulator (T.sim Rel SD)`, at the actual honest prover shape and
  its honest domain. It is honest-verifier zero knowledge, not a malicious-verifier
  theorem. The simulator is specified by data before the honest witness and has
  no witness argument; the result is not an unrestricted existential simulator.

The historical headline signatures changed when simulator data was separated, so
this report does not assert byte identity with those old revisions. Current headline
own fingerprints are unchanged by the rollout relative to its accepted baseline.
Generic mask-validity implications remain discharged in the full tree proof through
`masks_prefix` and the confined Ligero prefix condition; no such implication is
silently treated as unconditional by this audit.
