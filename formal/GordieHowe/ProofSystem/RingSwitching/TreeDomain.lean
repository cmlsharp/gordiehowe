-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.RingSwitching.PackingTree
public import GordieHowe.ProofSystem.Ligero.MaskRow.Masked
public import GordieHowe.ProofSystem.FieldProof.Basic
public import GordieHowe.Headline

@[expose] public section

/-!
# The domain proof over any packing tree

A GordieHowe domain packs its values along a tree of subfields of its field `K` (`tree.h`) and
proves its predicate in three parts (`tree_zk.h`, header):

* **the masked reduction** of the batched relations and GKR, whose claims are affine forms on the tree's
  logical coordinates (`MaskedReduction` on `V`);
* **the tree** in processing order (`GordieHowe.RingSwitching.Tree`): every non-root node's stage, deepest first,
  each combining the claims that read its region (`route`) or every claim (`cons`) and measuring
  their combination. Every stage's subfield masks are prefix cells (`masks_prefix`);
* **Ligero with the prefix-row test** (`GordieHowe.Ligero.MaskRow.Setup`) on the committed cells
  `[prefix | root children's words | root own]`, with the joint subfield test on every prefix row.

`GordieHowe.RingSwitching.TreeFieldProof` bundles the three; `GordieHowe.RingSwitching.TreeFieldProof.proof` is the circuit proof (`GordieHowe.FieldProof`)
of a relation read from the cells (`GordieHowe.RingSwitching.TreeFieldProof.Relation`), whose commit-and-prove system reads the
extracted cells confined to the prefix condition (`GordieHowe.Ligero.MaskRow.Setup.confined`), so the masks'
condition holds on them.

**The headline**, for every tree, every masked reduction sound for `sat` at the tree's logical assignment,
and every Ligero setup whose evaluation points and prefix message nodes lie in `S0`:

* **soundness** (`knowledge_soundness`): knowledge sound with error the masked reduction's, `1/|K|` per
  combination (`GordieHowe.RingSwitching.Tree.combinations`: every `cons` stage and every routed stage two or more
  claims touch), the test and column errors of Ligero, and the joint subfield term
  `(k − 1)_t / (N)_t` when the prefix is nonempty; the commit error `B/(|K| − 1)` is charged by the
  protocol running the commit phase (`sum_commitError`);
* **completeness** (`completeness`) and **honest-verifier zero knowledge** (`hvzk`), from the masked
  reduction's honest prover, uniform masks per stage (`GordieHowe.RingSwitching.Tree.honestRun`) and Ligero's honest prover
  (`GordieHowe.Ligero.MaskRow.Setup.honestConfined`).
-/

namespace GordieHowe

open IOP IOP.ProtocolSpec PackingStage RelativePacking
open scoped NNReal

/-- **A domain over a packing tree** (`tree_zk.h`): the tree in processing order with its routing
(`path`, nested: each stage's words are its parent's coordinates), the masked reduction of the batches and
GKR on the tree's logical coordinates (`maskedReduction`, with the routing obligations `routes`), and Ligero
with the prefix-row test on the committed cells (`cp`, on the code `code` and the tableau
`tableau`); every subfield-mask stage's cells are prefix cells, so the prefix condition gives every
stage's mask condition (`masks_prefix`). -/
structure RingSwitching.TreeFieldProof (K : Type) [Field K] [Fintype K] [DecidableEq K] (p : ℕ) [ExpChar K p]
    (ι : Type) [Fintype ι] (V Pub : Type) (nc : ℕ) where
  /-- The tree in processing order. -/
  path : Tree K p ι V nc
  /-- Each stage's words are its parent's coordinates. -/
  nested : path.Nested
  /-- The masked reduction of the batches and GKR. -/
  maskedReduction : FieldProof.MaskedReduction K ι Pub (ι → K) id V nc
  /-- At every routed stage the passing claims read no child coordinate. -/
  routes : path.Routes maskedReduction
  /-- The code length. -/
  N : ℕ
  /-- The data rows of the tableau. -/
  R : ℕ
  /-- The quadratic groups of the tableau. -/
  nQ : ℕ
  /-- The prepared linear rows of the tableau. -/
  nLr : ℕ
  /-- The number of prefix cells. -/
  np : ℕ
  /-- The code. -/
  code : GordieHowe.RSCode K N
  /-- The tableau. -/
  tableau : Ligero.Tableau.Parameters (R := R) (nQ := nQ) code
  /-- Ligero with the prefix-row test on the committed cells. -/
  cp : Ligero.MaskRow.Setup code tableau (path.close maskedReduction).products (path.close maskedReduction).Lin nLr
    np
  /-- The prefix condition gives every stage's mask condition. -/
  masks_prefix : ∀ x, cp.PrefixIn x → path.MasksValid x

namespace RingSwitching.TreeFieldProof

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {p : ℕ} [ExpChar K p] {ι : Type}
  [Fintype ι] [DecidableEq ι] {V Pub Wit : Type} {nc : ℕ} (T : TreeFieldProof K p ι V Pub nc)
  {holds : Pub → Wit → Prop}

/-- **The relation a tree domain proves**: a relation `sat` on the cells (the masked reduction's), the
witness read from the cells (`readout`), and `holds` on the read witness from `sat` on cells whose
prefix lies in `S0` (`readout_sound`). -/
structure Relation (holds : Pub → Wit → Prop) where
  /-- The relation on the cells. -/
  sat : Pub → (ι → K) → Prop
  /-- The witness read from the cells. It becomes part of the circuit proof's named extractor
  (`FieldProof.readout`), so each instance must give a computable, polynomial-time readout. -/
  readout : (ι → K) → Wit
  /-- `sat` gives `holds` on cells whose prefix lies in `S0`. -/
  readout_sound : ∀ p x, T.cp.PrefixIn x → sat p x → holds p (readout x)

/-- **The circuit proof of a tree domain** (`FieldProof`): the masked row reduction of the tree
(`Tree.close`: the masked reduction, then the stages), then Ligero with the prefix-row test with its
extracted cells confined to the prefix condition; the relation on the cells is "every stage's mask
condition implies `sat`", which the confined cells reduce to `sat` (`masks_prefix`). -/
def proof (Rel : T.Relation holds) : FieldProof Pub Wit holds where
  F := K
  ι := ι
  sat p x := T.path.MasksValid x → Rel.sat p x
  ip := T.path.close T.maskedReduction
  cp := T.cp.confined (T.path.close T.maskedReduction).rowsAt
  readout := Rel.readout
  readout_sound p O r h :=
    Rel.readout_sound p _ (T.cp.in_extract_confined _ O r)
      (h (T.masks_prefix _ (T.cp.in_extract_confined _ O r)))

/-- **The soundness of a tree domain's circuit proof**: the tree's masked row reduction sound for "every
stage's mask condition implies `sat`" with the run's errors (`Tree.soundClose`), and Ligero with
the prefix-row test, confined (`Ligero.MaskRow.Setup.soundConfined`). -/
noncomputable def sound (Rel : T.Relation holds) {ε : T.maskedReduction.spec.ChallengeIdx → ℝ≥0}
    (H : T.maskedReduction.Sound T.path.level.view Rel.sat ε) : (T.proof Rel).Sound where
  ipε := T.path.runError T.maskedReduction ε
  ipSound := T.path.soundClose H T.routes
  cpεc := fun _ => T.cp.commitError
  cpε := T.cp.error _
  cpSound := T.cp.soundConfined _

variable {Rel : T.Relation holds} {ε : T.maskedReduction.spec.ChallengeIdx → ℝ≥0}
  (H : T.maskedReduction.Sound T.path.level.view Rel.sat ε)

/-- **The masked-row-reduction errors**: the masked reduction's and `1/|K|` per combination
(`Tree.sum_runError`). -/
theorem sum_ipError :
    ∑ j, (T.sound Rel H).ipε j = ∑ i, ε i + T.path.combinations / Fintype.card K :=
  T.path.sum_runError T.maskedReduction ε

/-- **The commit-and-prove error of a tree domain**: the test and column errors of Ligero and, when
the prefix is nonempty, the joint subfield term `(k − 1)_t/(N)_t`. -/
noncomputable def cpError : ℝ≥0 :=
  T.cp.bounds.test + T.cp.bounds.column +
    if T.np = 0 then 0 else Ligero.SubfieldTest.jointSubfieldError T.code.k T.N T.cp.t

/-- **The commit-and-prove errors** sum to `cpError` (`Ligero.MaskRow.Setup.error_sum`). -/
theorem sum_cpError : ∑ j, (T.sound Rel H).cpε j = T.cpError :=
  T.cp.error_sum

/-- **The commit error**: the commit phase draws one challenge, exceptional with probability at
most `B/(|K| − 1)`. -/
theorem sum_commitError : ∑ j, (T.sound Rel H).cpεc j = T.cp.bounds.commit := by
  change ∑ _j, T.cp.commitError = _
  have hc : Fintype.card (T.proof Rel).cp.commitRounds.ChallengeIdx = 1 :=
    Ligero.MaskRow.Setup.card_commitIdx (rows := (T.path.close T.maskedReduction).rowsAt) T.cp
  rw [Finset.sum_const, Finset.card_univ, hc, one_smul, Ligero.MaskRow.Setup.commitError_eq]

variable (Rel) in
/-- **The relation a tree domain's proof phase is knowledge sound for**: the commit phase was bad
(`commitBad` of `sound`, a challenge event of the commit phase charged by the multi-circuit IOP's
soundness as `cpεc`), or `holds` on the witness the circuit proof reads (the relation of
`FieldProof.rbr_knowledge_soundness` at `proof`). -/
abbrev relation :
    Set (FieldProof.Shape.Statement Pub (T.proof Rel).toShape.Com (T.proof Rel).toShape.Rounds × Wit) :=
  (T.proof Rel).toShape.relation holds (T.sound Rel H).commitBad

variable (ε) in
/-- **The knowledge error of a tree domain's proof phase**: the masked reduction's errors `Σ ε`, `1/|K|`
per combination of the tree (`Tree.combinations`) and the commit-and-prove error `cpError`. -/
noncomputable def knowledgeError : ℝ≥0 :=
  ∑ i, ε i + T.path.combinations / Fintype.card K + T.cpError

/-- **Every round error of a tree domain's proof phase is at most `δ`** when the masked-row-reduction errors
`Σ ε + c/|K|` are, the test bound is, and the column bound with, when the prefix is nonempty, the
joint subfield term is: each masked-row-reduction round is one term of `sum_ipError`, each Ligero round one of
the test or the column query (`Ligero.MaskRow.Setup.error_le_of`). -/
theorem error_le_of {δ : ℝ≥0} (hip : ∑ i, ε i + T.path.combinations / Fintype.card K ≤ δ)
    (htest : T.cp.bounds.test ≤ δ)
    (hcol : T.cp.bounds.column +
      (if T.np = 0 then 0 else Ligero.SubfieldTest.jointSubfieldError T.code.k T.N T.cp.t) ≤ δ)
    (j : (T.proof Rel).spec.ChallengeIdx) : (T.sound Rel H).error j ≤ δ :=
  (T.sound Rel H).error_le
    (fun j => (Finset.single_le_sum (f := (T.sound Rel H).ipε) (fun _ _ => zero_le)
      (Finset.mem_univ j)).trans ((T.sum_ipError H).trans_le hip))
    (fun _ => T.cp.error_le_of htest hcol _) j

/-- **Knowledge soundness of a domain over any packing tree** (at `TreeFieldProof.proof`): for every
tree in processing order, every masked reduction sound for `sat` at the tree's logical assignment with round
errors `ε`, and every Ligero setup with the prefix-row test, the proof phase is knowledge sound for
`relation` ("the commit phase was bad or `holds`") at the circuit proof's named extractor, with
error `knowledgeError`: `Σ ε + c/|K| + test + column + [np ≠ 0] · (k − 1)_t/(N)_t`, where `c` counts
the combinations (every inner node receiving two or more rows, and the root's combination when it
has a child). -/
@[headline]
theorem knowledge_soundness :
    knowledgeSoundness (T.relation Rel H) (T.proof Rel).toShape.verifier
      (T.proof Rel).toShape.extractor (T.knowledgeError ε) := by
  have h := FieldProof.knowledge_soundness (T.sound Rel H)
  rwa [T.sum_ipError H, T.sum_cpError H] at h

/-! ### The honest prover -/

variable {In : Type} {dom : Pub → In → Prop}

/-- **The simulator data of a tree domain**: the masked reduction's simulator and Ligero's hiding data
(the blinding layout its simulator reads). -/
structure SimData where
  /-- The masked reduction's simulator. -/
  maskedReduction : T.maskedReduction.Sim
  /-- Ligero's hiding data. -/
  ligero : T.cp.Hiding

variable (Rel) in
/-- **The simulator data of a tree domain's circuit proof**: the tree's simulator (`Tree.simRun`:
the masked reduction's simulator, uniform measurements per stage), closed, and Ligero's simulator,
confined (`Ligero.MaskRow.Setup.simConfined`).

Running time: the masked reduction's simulator, a copy of each stage's challenge and measurement,
and Ligero's simulator (their docstrings). This running time is argued here, not proved in Lean. -/
def sim (SD : T.SimData) : (T.proof Rel).Sim where
  ip := T.path.simRun SD.maskedReduction
  cp := T.cp.simConfined _ SD.ligero

/-- **The honest data of a tree domain**, simulated by `SD`: the masked reduction's honest prover at the
tree's logical assignment (`maskedReduction`), the honest masks of every stage (`masks`), the words'
values (`val`, which the committed cells match at every word, `val_word`), and the committed cells
(`cells`) from the honest input and the pads, which commit the honest input and the pads (`commits`)
and are admissible for Ligero at the hiding data of `SD` (`admissible`). -/
structure HonestData (Rel : T.Relation holds) (SD : T.SimData) (In : Type) (dom : Pub → In → Prop) where
  /-- The masked reduction's honest prover. -/
  maskedReduction : T.maskedReduction.Honest T.path.level.view In dom SD.maskedReduction
  /-- The honest masks of every stage. -/
  masks : T.path.MaskHonest
  /-- The words' values. -/
  val : Pub → In → maskedReduction.Pads → V → K
  /-- The committed cells match `val` at every word. -/
  val_word : ∀ p x π w, maskedReduction.Commits p x π w → ∀ z, T.path.IsWord z →
    T.path.level.view w z = val p x π z
  /-- The committed cells. -/
  cells : In → (T.path.honestRun T.routes maskedReduction masks val val_word).Pads → ι → K
  /-- The cells commit the honest input and the pads. -/
  commits : ∀ p x π, dom p x → (T.path.honestRun T.routes maskedReduction masks val val_word).Commits p x π
    (cells x π)
  /-- The cells are admissible for Ligero. -/
  admissible : ∀ p x π, dom p x → T.cp.Admissible SD.ligero (cells x π)

/-- **The honest prover of a tree domain's circuit proof**: the honest run of the tree
(`Tree.honestRun`), closed; Ligero's honest prover, confined
(`Ligero.MaskRow.Setup.honestConfined`); the committed cells of the honest data. -/
noncomputable def honest {SD : T.SimData} (Hd : T.HonestData Rel SD In dom) :
    (T.proof Rel).Honest (T.sim Rel SD) In dom where
  ip := (T.path.honestRun T.routes Hd.maskedReduction Hd.masks Hd.val Hd.val_word).close
  cp := T.cp.honestConfined _ SD.ligero
  cells := Hd.cells
  commits := Hd.commits
  admissible p x π hx := (T.cp.admissible_honest _ SD.ligero _).mpr (Hd.admissible p x π hx)

/-- **Completeness of a domain over any packing tree** (`FieldProof.completeness` at
`TreeFieldProof.honest`): on the honest domain, the verdict accepts the honest proof at every challenge
of the commit rounds and of the proof phase. -/
@[headline]
theorem completeness {SD : T.SimData} (Hd : T.HonestData Rel SD In dom) {pub : Pub} {x : In} (hx : dom pub x)
    (ρ : (T.honest Hd).Coins) (chc : (T.proof Rel).cp.commitRounds.Challenges)
    (ch : (T.proof Rel).spec.Challenges) :
    (T.proof Rel).verdict pub ((T.honest Hd).commit x ρ) ((T.honest Hd).rounds x ρ chc)
      (((T.honest Hd).prove pub x ρ ((T.honest Hd).rounds x ρ chc)).transcript ch) = true :=
  FieldProof.completeness (T.honest Hd) hx ρ chc ch

/-- **Honest-verifier zero knowledge of a domain over any packing tree** (`FieldProof.hvzk` at
`TreeFieldProof.honest`): the simulator `FieldProof.simulator` at `sim` (the masked reduction's simulator, uniform
measurements per stage, Ligero's simulator with the prefix rows' openings in `S0`) is perfect on the
honest domain. -/
@[headline]
theorem hvzk {SD : T.SimData} (Hd : T.HonestData Rel SD In dom) :
    (FieldProof.simulator (T.sim Rel SD)).Perfect (T.honest Hd).toShape dom :=
  FieldProof.hvzk (T.honest Hd)

end RingSwitching.TreeFieldProof

end GordieHowe
