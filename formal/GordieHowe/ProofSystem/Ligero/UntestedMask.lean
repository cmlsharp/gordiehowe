-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Ligero.MaskRow.Basic
public import GordieHowe.ProofSystem.Ligero.AgreementThreshold
public import GordieHowe.Applications.Keccak.HashCircuit.Packed.Basic

@[expose] public section

/-!
# Ligero at agreement threshold `A` with the prefix-row test

Ligero at agreement threshold `A` with untested masks (`GordieHowe.Ligero.AgreementThreshold`) on the committed cells
themselves, with the subfield test on the rows of the prefix cells (`PrefixCells`) charged jointly
with the low-degree test. It has no batching phase and no unpacking: a packing tree's root stages
run in the masked row reduction (`GordieHowe/ProofSystem/RingSwitching/PackingTree.lean`), and the commitment's only packing-specific
part is the test that the prefix, which holds every subfield-mask stage's masks, lies in `S0`.

* **the oracle message, the commit rounds, the proof phase**: those of `GordieHowe.Ligero.AgreementThreshold`;
* **the extracted cells**: those of `GordieHowe.Ligero.AgreementThreshold` (`TableauSetup.extract`);
* **the verdict** (`verdict`): that of `GordieHowe.Ligero.AgreementThreshold`, and every queried entry of every
  prefix cell's row lies in `E`.

**Soundness** (`sound`, `CommitProve.SoundOn`): the commit event of `GordieHowe.Ligero.AgreementThreshold`; the proof
phase of `GordieHowe.Ligero.AgreementThreshold` with the joint subfield test at its query round
(`GordieHowe.IOP.LigeroQuery.withJointSubfield`, `jointCheck`): off the commit event, a prefix cell
extracted outside `E` makes its pinned row a polynomial of degree `< k` with a coefficient outside
`E` that equals the tableau row on the common agreement set
(`GordieHowe.Ligero.AgreementThreshold.Threshold.agreesWithNonSubfield_pinnedRows`, the prefix cells' message nodes in
`E`), and accepted queries lie in the common agreement set. The claim is "the commit phase was bad, or the
rows hold on the extracted cells and every prefix cell lies in `E`"; the errors (`error_sum`) are
the test and column errors of `GordieHowe.Ligero.AgreementThreshold` and one joint subfield term
`(k − 1)_t / (N)_t`, whatever the number of prefix rows.

**The honest prover** (`honest`): that of `GordieHowe.Ligero.AgreementThreshold` (`GordieHowe.Ligero.AgreementThreshold.honest`); the
prefix-row test accepts it because every prefix cell's row has blinding field inside `E`, and an
honest row whose message values and nodes lie in `E` evaluates into `E` at the code's points
(`Placement.commit_prefixRow_mem`, `Ligero.HVZK.rows_succ_eval_mem`). The view is that of
`GordieHowe.Ligero.AgreementThreshold`, so hiding is its hiding.
-/

namespace GordieHowe.Ligero.UntestedMask
open IOP

open ProtocolSpec
open Ligero.AgreementThreshold (ldtChallenge ldtResponse commonAgreement)
open scoped NNReal

section

variable {K ι Q Lin : Type} [Field K] [Fintype K] [DecidableEq K] [Fintype ι] [Fintype Q]
  [Fintype Lin] {N R nQ nL np : ℕ}

/-! ### The setup -/

/-- **The data of Ligero at agreement threshold `A` with untested masks and the prefix-row test**
on the code `C` and the tableau `P`, for cells `ι → K` with the product layout `products` and
affine rows indexed by `Lin`: the setup of `Ligero.AgreementThreshold`, the prefix cells `pre`, and the
field facts of the test: the code's evaluation points (`domain_mem`) and the prefix cells' message
nodes (`node_mem`) lie in `E`. -/
structure Setup (C : GordieHowe.RSCode K N) (P : Tableau.Parameters (R := R) (nQ := nQ) C)
    (products : Routing.ProductLayout ι Q) (Lin : Type) (nL np : ℕ)
    extends Ligero.AgreementThreshold.Setup C P products Lin nL where
  /-- The prefix cells. -/
  pre : MaskRow.PrefixCells K ι np
  /-- The code's evaluation points lie in `E`. -/
  domain_mem : ∀ j, C.D j ∈ pre.E
  /-- The prefix cells' message nodes lie in `E`. -/
  node_mem : ∀ j, placement.messageReadout.point (pre.cell j) ∈ pre.E

variable {C : GordieHowe.RSCode K N} {P : Tableau.Parameters (R := R) (nQ := nQ) C}
  {products : Routing.ProductLayout ι Q}

variable (S : Setup C P products Lin nL np) {Ctx : Type} (rows : Ctx → Lin → AffineForm K ι)

/-- Ligero at agreement threshold `A` with untested masks on the cells, without the test. -/
abbrev inner : FieldProof.CommitProve K ι products Ctx rows :=
  Ligero.AgreementThreshold.commitProve S.toSetup rows

/-- The input of the proof phase: the context, the oracle message and the commit rounds. -/
abbrev Input (Ctx K : Type) (N R k nrep : ℕ) : Type := Ligero.AgreementThreshold.Input Ctx K N R k nrep

/-- **The verdict**: the verdict of `Ligero.AgreementThreshold`, and the prefix-row test: every queried
entry of every prefix cell's row lies in `E`. -/
def verdict (c : Input Ctx K N R C.k S.nrep)
    (tr : (Ligero.AgreementThreshold.proofSpec K N nL nQ C.k S.t).Transcript (Fin.last 3)) : Bool :=
  Ligero.AgreementThreshold.verdict S.toSetup rows c tr &&
    decide (∀ (j : Fin np) (s : Fin S.t),
      c.com.tableau (S.placement.messageReadout.row (S.pre.cell j))
        (Ligero.AgreementThreshold.queryOf tr s) ∈ S.pre.E)

/-- **Ligero at agreement threshold `A` with untested masks and the prefix-row test as a
commit-and-prove system**: the oracle message, commit rounds, extracted cells and proof phase of
`Ligero.AgreementThreshold`, with the prefix-row test in the verdict (`verdict`). -/
def commitProve : FieldProof.CommitProve K ι products Ctx rows where
  Com := Tableau.Commitment K N R S.nrep
  nLeaves := N
  Leaf := Tableau.Leaf K R S.nrep
  leaf := Tableau.Commitment.leaf
  leaf_injective := Tableau.Commitment.leaf_injective
  ofLeaves := Tableau.Commitment.ofLeaves
  leaf_ofLeaves := Tableau.Commitment.leaf_ofLeaves
  leafDefault := ⟨⟨0, 0⟩, 0, 0⟩
  nc := 2
  commitRounds := Ligero.AgreementThreshold.commitSpec K R C.k S.nrep
  extract O tr := S.extract O.rows tr
  n := 3
  spec := Ligero.AgreementThreshold.proofSpec K N nL nQ C.k S.t
  V := verdict S rows
  queries := (inner S rows).queries
  reads c ch U U' r tr htr h := by
    have hq : Ligero.AgreementThreshold.queryOf tr = Ligero.AgreementThreshold.chQuery ch :=
      htr (Ligero.AgreementThreshold.queryIdx K N nL nQ C.k S.t)
    have hcol : ∀ s, U.leaf (Ligero.AgreementThreshold.queryOf tr s) =
        U'.leaf (Ligero.AgreementThreshold.queryOf tr s) := fun s => by
      rw [hq]
      exact h _ (Finset.mem_map_of_mem _ (Finset.mem_univ s))
    have hv : Ligero.AgreementThreshold.verdict S.toSetup rows ⟨c, U, r⟩ tr =
        Ligero.AgreementThreshold.verdict S.toSetup rows ⟨c, U', r⟩ tr :=
      (inner S rows).reads c ch U U' r tr htr h
    unfold verdict
    dsimp only
    rw [hv]
    congr 2
    refine propext (forall_congr' fun j => forall_congr' fun s => ?_)
    rw [show U.tableau (S.placement.messageReadout.row (S.pre.cell j))
        (Ligero.AgreementThreshold.queryOf tr s) =
        U'.tableau (S.placement.messageReadout.row (S.pre.cell j))
          (Ligero.AgreementThreshold.queryOf tr s)
      from Tableau.Rows.ldtMatrix_congr (congrArg Tableau.Leaf.column (hcol s)) 0 _]

/-- **The verifier queries `t` leaves** at every challenge vector. -/
theorem card_queries (ch : (Ligero.AgreementThreshold.proofSpec K N nL nQ C.k S.t).Challenges) :
    ((commitProve S rows).queries ch).card = S.t :=
  Ligero.AgreementThreshold.card_queries S.toSetup rows ch

/-! ### Soundness -/

/-- The proof phase of `Ligero.AgreementThreshold`, with its column-query round. -/
noncomputable def ligeroQuery : LigeroQuery (Input Ctx K N R C.k S.nrep) S.t N where
  n := 3
  spec := Ligero.AgreementThreshold.proofSpec K N nL nQ C.k S.t
  fintype _ := inferInstance
  nonempty := (inner S rows).nonempty
  ε := Ligero.AgreementThreshold.error S.toSetup
  proof := ClaimProof.ofFintype _ _ (Ligero.AgreementThreshold.sound S.toSetup rows).proof
  q := Ligero.AgreementThreshold.queryIdx K N nL nQ C.k S.t
  query := Equiv.refl _

/-- **The prefix-row test, charged jointly with the low-degree test**: the prefix cells' rows of
the committed tableau. When some low-degree challenge is not exceptional and an extracted prefix
cell lies outside `E`, its pinned row has a coefficient outside `E` and equals the tableau row on
the common agreement set (`Ligero.AgreementThreshold.Threshold.agreesWithNonSubfield_pinnedRows`). -/
def jointCheck :
    HashCircuit.Packed.JointSubfieldCheck (F := K) (Input Ctx K N R C.k S.nrep) N np
      (fun c => S.Exceptional c.com.rows c.rounds ∨
        S.pre.In (S.extract c.com.rows c.rounds)) where
  E := S.pre.E
  D := C.D
  D_injective := C.D_injective
  D_mem := S.domain_mem
  rows c j := c.com.tableau (S.placement.messageReadout.row (S.pre.cell j))
  k := C.k
  agree c := commonAgreement C c.com.rows (ldtChallenge c.rounds) (ldtResponse c.rounds)
  decode c h := by
    obtain ⟨hr, hm⟩ := not_or.mp h
    obtain ⟨j, hj⟩ := not_forall.mp hm
    rw [Ligero.AgreementThreshold.TableauSetup.extract_eq_eval] at hj
    exact ⟨j, _, S.agreesWithNonSubfield_pinnedRows _ hr (S.node_mem j) hj⟩

/-- **Accepted queries lie in the common agreement set of the low-degree test**
(`Ligero.AgreementThreshold.mem_commonAgreement_of_accept`). -/
theorem ligeroQuery_acceptsWithin :
    (ligeroQuery S rows).AcceptsWithin (jointCheck S (Ctx := Ctx)).agree := by
  intro c tr h s
  have h' := (Tableau.accept_eq_true_iff ..).mp h
  exact Ligero.AgreementThreshold.mem_commonAgreement_of_accept h' s

/-- The proof phase of `Ligero.AgreementThreshold` with the joint prefix-row test. -/
noncomputable def ligeroJoint :=
  (ligeroQuery S rows).withJointSubfield (jointCheck S) (ligeroQuery_acceptsWithin S rows)

open Classical in
/-- **The errors**: those of `Ligero.AgreementThreshold`, and, when the prefix is nonempty, the joint
subfield term `(k − 1).descFactorial t / N.descFactorial t` at the column query. -/
noncomputable def error :
    (Ligero.AgreementThreshold.proofSpec K N nL nQ C.k S.t).ChallengeIdx → ℝ≥0 :=
  fun i => Ligero.AgreementThreshold.error S.toSetup i +
    if np = 0 then 0 else if i = Ligero.AgreementThreshold.queryIdx K N nL nQ C.k S.t then
      SubfieldTest.jointSubfieldError C.k N S.t else 0

omit [DecidableEq K] [Fintype ι] [Fintype Q] [Fintype Lin] in
/-- **The errors sum** to the test and column errors of `Ligero.AgreementThreshold` and, when the prefix is
nonempty, the joint subfield term. -/
theorem error_sum :
    ∑ i, error S i = Ligero.AgreementThreshold.testError S.toSetup +
      Ligero.AgreementThreshold.columnError S.toSetup +
      if np = 0 then 0 else SubfieldTest.jointSubfieldError C.k N S.t := by
  classical
  unfold error
  rw [Finset.sum_add_distrib, Ligero.AgreementThreshold.error_sum]
  split_ifs with h
  · simp
  · rw [Finset.sum_eq_single_of_mem (Ligero.AgreementThreshold.queryIdx K N nL nQ C.k S.t)
      (Finset.mem_univ _) fun j _ hj => ite_eq_right hj, ite_eq_left rfl]

omit [DecidableEq K] [Fintype ι] [Fintype Q] [Fintype Lin] in
/-- **Every round error is at most `δ`** when the test error is and the column error with, when
the prefix is nonempty, the joint subfield term is: the constraint challenge's error is the test
error, the column query's the column error and the joint subfield term. -/
theorem error_le_of {δ : ℝ≥0} (htest : Ligero.AgreementThreshold.testError S.toSetup ≤ δ)
    (hcol : Ligero.AgreementThreshold.columnError S.toSetup +
      (if np = 0 then 0 else SubfieldTest.jointSubfieldError C.k N S.t) ≤ δ)
    (i : (Ligero.AgreementThreshold.proofSpec K N nL nQ C.k S.t).ChallengeIdx) : error S i ≤ δ := by
  classical
  unfold error
  rcases Ligero.AgreementThreshold.proof_challengeIdx_cases i with rfl | rfl
  · have hne : Ligero.AgreementThreshold.constraintIdx (F := K) (N := N) (nL := nL) (nQ := nQ) C.k S.t ≠
        Ligero.AgreementThreshold.queryIdx K N nL nQ C.k S.t := fun h => by
      have := congrArg (fun i => (i.1 : ℕ)) h
      simp [Ligero.AgreementThreshold.constraintIdx, Ligero.AgreementThreshold.queryIdx] at this
    simp only [hne, ite_false, ite_self, add_zero]
    exact Ligero.AgreementThreshold.error_le_of S.toSetup htest (le_self_add.trans hcol) _
  · simp only [ite_true]
    exact hcol

omit [Fintype K] [Fintype Lin] in
/-- With no prefix cell the prefix-row test accepts every transcript. -/
theorem verdict_of_eq_zero (h : np = 0) (c : Input Ctx K N R C.k S.nrep)
    (tr : (Ligero.AgreementThreshold.proofSpec K N nL nQ C.k S.t).Transcript (Fin.last 3)) :
    Ligero.AgreementThreshold.verdict S.toSetup rows c tr = verdict S rows c tr := by
  rw [verdict, decide_eq_true fun j => absurd j.isLt (by omega), Bool.and_true]

omit [Fintype K] [DecidableEq K] [Fintype ι] [Fintype Q] [Fintype Lin] in
/-- With no prefix cell every vector satisfies the prefix condition. -/
theorem in_of_eq_zero (h : np = 0) (x : ι → K) : S.pre.In x :=
  fun j => absurd j.isLt (by omega)

/-- The proof phase with an empty prefix: the proof phase of `Ligero.AgreementThreshold` alone, whose
verdict is the system's (`verdict_of_eq_zero`). -/
noncomputable def proofEmpty (h : np = 0) :
    ClaimProof (Ligero.AgreementThreshold.proofSpec K N nL nQ C.k S.t) (Input Ctx K N R C.k S.nrep) (error S) :=
  ((ligeroQuery S rows).proof.monoError fun _ => le_self_add).withV (verdict S rows)
    fun c tr => verdict_of_eq_zero S rows h c tr

/-- The proof phase with a nonempty prefix: the proof phase of `Ligero.AgreementThreshold` with the joint
prefix-row test (`ligeroJoint`). -/
noncomputable def proofJoint (h : np ≠ 0) :
    ClaimProof (Ligero.AgreementThreshold.proofSpec K N nL nQ C.k S.t) (Input Ctx K N R C.k S.nrep) (error S) :=
  (ligeroJoint S rows).monoError fun i => by
    simp only [error, h, ↓reduceIte]
    rfl

/-- **The proof phase**: `proofJoint` with a nonempty prefix, `proofEmpty` with an empty one. -/
noncomputable def proofPhase :
    ClaimProof (Ligero.AgreementThreshold.proofSpec K N nL nQ C.k S.t) (Input Ctx K N R C.k S.nrep) (error S) :=
  if h : np = 0 then proofEmpty S rows h else proofJoint S rows h

/-- The verdict of the proof phase is the system's. -/
theorem proofPhase_V (c : Input Ctx K N R C.k S.nrep)
    (tr : (Ligero.AgreementThreshold.proofSpec K N nL nQ C.k S.t).Transcript (Fin.last 3)) :
    (proofPhase S rows).V c tr = verdict S rows c tr := by
  unfold proofPhase
  by_cases h : np = 0
  · rw [dite_eq_left_of_eq_true (eq_true h)]
    rfl
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    rfl

/-- **The claim of the proof phase**: every low-degree challenge was exceptional, or the rows hold on
the extracted cells and every prefix cell lies in `E`. -/
theorem proofPhase_claim (c : Input Ctx K N R C.k S.nrep) :
    (proofPhase S rows).claim c ↔ S.Exceptional c.com.rows c.rounds ∨
      (RowsHold (rows c.ctx) products (S.extract c.com.rows c.rounds) ∧
        S.pre.In (S.extract c.com.rows c.rounds)) := by
  unfold proofPhase
  by_cases h : np = 0
  · rw [dite_eq_left_of_eq_true (eq_true h)]
    change (Ligero.AgreementThreshold.sound S.toSetup rows).proof.claim c ↔ _
    rw [(Ligero.AgreementThreshold.sound S.toSetup rows).claim_iff c]
    exact or_congr S.eventOccurs_iff ⟨fun hL => ⟨hL, in_of_eq_zero S h _⟩, fun h => h.1⟩
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    change ((Ligero.AgreementThreshold.sound S.toSetup rows).proof.claim c ∧ _) ↔ _
    rw [(Ligero.AgreementThreshold.sound S.toSetup rows).claim_iff c]
    constructor
    · rintro ⟨hL | hL, hE⟩
      · exact .inl (S.eventOccurs_iff.mp hL)
      rcases hE with he | hE
      · exact .inl he
      · exact .inr ⟨hL, hE⟩
    · rintro (h | ⟨hL, hE⟩)
      · exact ⟨.inl (S.eventOccurs_iff.mpr h), .inl h⟩
      · exact ⟨.inr hL, .inr hE⟩

/-- **Soundness of Ligero at agreement threshold `A` with untested masks and the prefix-row
test**: the commit event of `Ligero.AgreementThreshold` (every low-degree challenge exceptional,
probability at most `(B / (|K| − 1)) ^ nrep`); its proof phase with the joint prefix-row test (`proofPhase`),
round-by-round sound relative to "the commit phase was bad, or the rows hold on the extracted cells
and every prefix cell lies in `E`", with the errors `error` (`error_sum`). -/
noncomputable def soundIP :
    (commitProve S rows).SoundOn S.pre.In (fun _ => S.commitError) (error S) where
  commitEvent := S.commitEvent Tableau.Commitment.rows
  commitEvent_bound := S.commitEvent_bound Tableau.Commitment.rows
  proof := ClaimProof.ofFintype _ _ (proofPhase S rows)
  V_eq c tr := proofPhase_V S rows c tr
  claim_iff c := (proofPhase_claim S rows c).trans (or_congr_left S.eventOccurs_iff.symm)

/-! ### The honest prover -/

/-- **The data of the honest prover** of Ligero at agreement threshold `A` with untested masks and
the prefix-row test: that of `Ligero.AgreementThreshold` (`Ligero.AgreementThreshold.TableauSetup.Hiding`), and the
blinding field of every prefix cell's row lies inside `E` (a parameter condition of the
layout). -/
structure Hiding (S : Setup C P products Lin nL np) where
  /-- The honest prover of `Ligero.AgreementThreshold`. -/
  inner : S.Hiding
  /-- Every prefix cell's row has blinding field inside `E`. -/
  prefix_field : ∀ j (row : Fin R), (S.placement.source (S.pre.cell j)).1 = row.succ →
    inner.layout.field row ≤ S.pre.E

/-- **The data of the honest prover** of Ligero at agreement threshold `A` with untested masks and
the prefix-row test: that of `Ligero.AgreementThreshold` (`Ligero.AgreementThreshold.TableauSetup.Placement`), and
the blinding field of every prefix cell's row lies inside `E` (a parameter condition of the
layout). Completeness needs only these. -/
structure Placement (S : Setup C P products Lin nL np) where
  /-- The honest prover of `Ligero.AgreementThreshold`. -/
  inner : S.Placement
  /-- Every prefix cell's row has blinding field inside `E`. -/
  prefix_field : ∀ j (row : Fin R), (S.placement.source (S.pre.cell j)).1 = row.succ →
    inner.layout.field row ≤ S.pre.E

/-- The data for completeness (`Placement`) from the data for hiding. -/
def Hiding.toPlacement {S : Setup C P products Lin nL np} (Hd : Hiding S) : Placement S :=
  ⟨Hd.inner.toPlacement, Hd.prefix_field⟩

namespace Placement

variable {S} (Pl : Placement S)

/-- **The honest prover's coins**: those of `Ligero.AgreementThreshold`. -/
abbrev Coins : Type := Pl.inner.Coins

/-- **The honest oracle message**: that of `Ligero.AgreementThreshold`. -/
noncomputable def commit (x : ι → K) (ρ : Pl.Coins) : (commitProve S rows).Com :=
  Pl.inner.commit rows x ρ

/-- **The honest commit rounds**: those of `Ligero.AgreementThreshold`. -/
noncomputable def commitRounds (x : ι → K) (ρ : Pl.Coins) :
    CausalTranscript (commitProve S rows).commitRounds :=
  Pl.inner.commitRounds rows x ρ

/-- **The honest proof**: that of `Ligero.AgreementThreshold`. -/
noncomputable def prove (c : Ctx) (x : ι → K) (ρ : Pl.Coins) (r : (commitProve S rows).Rounds) :
    CausalTranscript (commitProve S rows).spec :=
  Pl.inner.prove rows c x ρ r

/-- **The prefix cells' rows of the honest tableau lie in `E`** at every column: the row's message
values lie in its blinding field, inside `E`, and so do the message nodes, so its values at the
code's points (in `E`) lie in `E` (`Ligero.HVZK.rows_succ_eval_mem`). -/
theorem commit_prefixRow_mem (x : ι → K) (ρ : Pl.Coins) (j : Fin np) (col : Fin N) :
    (Pl.commit rows x ρ).tableau (S.placement.messageReadout.row (S.pre.cell j)) col ∈ S.pre.E := by
  obtain ⟨r, hr⟩ := Fin.exists_succ_eq.mpr (S.placement.source_nonzero (S.pre.cell j))
  have hf := Pl.prefix_field j r hr.symm
  let κ : HVZK.Coins S.rate_le Pl.inner.layout.toBlindingFields S.nrep := ρ
  change (HVZK.commitOf (Pl.inner.cells x) κ).tableau (S.placement.source (S.pre.cell j)).1 col ∈ _
  rw [HVZK.commitOf_tableau, ← hr]
  exact HVZK.rows_succ_eval_mem _ κ hf (fun i => hf (Pl.inner.layout.nodes_mem r i))
    (S.domain_mem col)

/-- **Completeness of the honest prover**: on admissible cells satisfying the rows, the verifier
accepts at every coins and every challenge (`Ligero.AgreementThreshold.TableauSetup.Placement.complete`, and
the prefix-row test by `commit_prefixRow_mem`). No query bound is needed. -/
theorem complete (c : Ctx) (x : ι → K)
    (hx : FieldProof.CommitProve.Admits Pl.inner.Admissible (rows c) products x) (ρ : Pl.Coins)
    (chc : (commitProve S rows).commitRounds.Challenges)
    (ch : (commitProve S rows).spec.Challenges) :
    (commitProve S rows).V ⟨c, Pl.commit rows x ρ, (Pl.commitRounds rows x ρ).transcript chc⟩
      ((Pl.prove rows c x ρ ((Pl.commitRounds rows x ρ).transcript chc)).transcript ch) =
        true := by
  change verdict S rows _ _ = true
  simp only [verdict, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨Pl.inner.complete rows c x hx ρ chc ch, fun j s => Pl.commit_prefixRow_mem rows x ρ j _⟩

end Placement

variable {S} (Hd : Hiding S)

/-- The honest prover of `Ligero.AgreementThreshold` on the cells. -/
noncomputable abbrev innerHonest :
    (inner S rows).Honest (Ligero.AgreementThreshold.honestSim rows Hd.inner) :=
  Ligero.AgreementThreshold.honest rows Hd.inner

variable (S) in
/-- A view of `Ligero.AgreementThreshold` as a view of the system with the prefix-row test (the same
leaves, rounds and transcript). -/
def viewOfInner (v : (inner S rows).View) : (commitProve S rows).View :=
  ⟨v.leaves, v.rounds, v.transcript⟩

/-- **The simulator of Ligero at agreement threshold `A` with untested masks and the prefix-row
test**: that of `Ligero.AgreementThreshold` (`simulate`), its views read as the system's.

Running time: that of `Ligero.AgreementThreshold.simulate`. This running time is argued here, not
proved in Lean. -/
def honestSim : (commitProve S rows).Sim where
  SimCoins := (Ligero.AgreementThreshold.honestSim rows Hd.inner).SimCoins
  sim c chc ch s := viewOfInner S rows (Ligero.AgreementThreshold.simulate rows Hd.inner c chc ch s)

/-- **The honest prover of Ligero at agreement threshold `A` with untested masks and the prefix-row
test**: that of `Ligero.AgreementThreshold`, simulated by `honestSim`; the prefix-row test accepts
the honest tableau (`Placement.commit_prefixRow_mem`). -/
noncomputable def honest : (commitProve S rows).Honest (honestSim rows Hd) where
  Coins := Hd.toPlacement.Coins
  commit := Hd.toPlacement.commit rows
  commitRounds := Hd.toPlacement.commitRounds rows
  prove := Hd.toPlacement.prove rows
  Admissible := (innerHonest rows Hd).Admissible
  complete := Hd.toPlacement.complete rows
  hides c x hx chc ch := ((innerHonest rows Hd).hides c x hx chc ch).comp (viewOfInner S rows)

/-- The admissible cells of the honest prover are those of `Ligero.AgreementThreshold`: every placed value
in its row's blinding field. -/
theorem admissible_honest (x : ι → K) : (honest rows Hd).Admissible x ↔ Hd.inner.Admissible x :=
  Iff.rfl

end

end GordieHowe.Ligero.UntestedMask
