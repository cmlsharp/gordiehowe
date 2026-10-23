-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldHonestTree
public import GordieHowe.ProofSystem.Program.FieldDomain

@[expose] public section

/-!
# GordieHowe: the honest prover of any domain's circuit proof

The honest prover of domain `d`'s circuit proof (`GordieHowe.RealizedProgram.fieldProof`) under the compiler's
completeness (`CircuitsAccept`):

* **the honest input** (`GordieHowe.RealizedProgram.treeInput_eq_circuitInput`): the input of the logical assignment
  of any committed cells whose filler cells decode to `0` is the circuit's honest input vector at
  the decoded cells (`GordieHowe.RealizedProgram.circuitInput`): a committed or pad input the decoded cell, a view
  input the decoded cell's bit (`wordBit_treeBits`), filler and the batch pads `0`.
-/

namespace GordieHowe.RealizedProgram

open Export PEdge

section

section Input

variable {ir : RealizedProgram} {I : Interp} {c : ℕ}
  {Pk : (I (ir.circField c)).Packing} {rs : List (REdge (I (ir.circField c)) Pk)}
  {Pads : Type} [Fintype Pads]

/-- **The input of the logical assignment is the decoded cells' honest input vector**, when the
filler cells decode to `0`: the public inputs the verifier's; a committed or pad input its decoded
cell (`optVal_keyCoord`); a view input the decoded cell's bit (`optVal_viewCoord`,
`wordBit_treeBits`, `bitValuation_cellBits`); filler and the batch pads `0`; zero past the
layout. -/
theorem treeInput_eq_circuitInput (hc : ir.InputsT (ir.circuit c).domain c)
    (hv : ir.ViewsOk (ir.circuit c).domain (rs.map REdge.plan))
    (ht : TreeOk (rs.map REdge.plan) Pk.n)
    (hp : ir.PlaceOk (ir.circuit c).domain Pk (rs.map REdge.plan))
    (hr : ir.RealizedOk (ir.circuit c).domain rs) {dd : ℕ} (p : ir.DomainPub I)
    (x : ir.TreeCell (ir.circuit c).domain Pk rs Pads → (I (ir.circField c)).K)
    (hfill : ∀ (j : ℕ) (hk : CellKey.filler c j ∈ ir.cellKeys (ir.circuit c).domain),
      ir.treeDecode (ir.circuit c).domain rs Pads x ⟨_, hk⟩ = 0) :
    (ir.treeInputForms rs Pads c dd).input p ((ir.treeLevel (ir.circuit c).domain rs Pads).view x) =
      ir.circuitInput I c p.stmt p.run
        (ir.ofCells I (ir.circuit c).domain (ir.treeDecode (ir.circuit c).domain rs Pads x)) := by
  have hpe : ir.privEnd c ≤ (ir.circuit c).inputCount := Nat.sub_le _ _
  funext q
  rw [treeInputForms_input]
  unfold circuitInput
  by_cases hpq : (q : ℕ) < (ir.circuit c).publicInputs
  · rw [if_pos hpq, if_pos (show (ir.circuit c).IsPublicPos q from hpq), castElt_self]
  · rw [if_neg hpq, if_neg (show ¬ (ir.circuit c).IsPublicPos q from hpq)]
    by_cases hw : (q : ℕ) < (ir.circuit c).inputCount
    · have h1 : 1 ≤ (q : ℕ) := by
        have := hc.one_le
        omega
      obtain ⟨b, hb, hbq⟩ := InputBlock.layoutEnd_cover hc.layout (q := q) h1 hw
      rw [InputBlock.findSome?_eq_of_holds hc.layout hb hbq fun b' => InputBlock.holds_of_privValue?]
      have hbp := hc.blocks b hb
      have hbq' := hbq
      unfold InputBlock.Holds at hbq
      cases b with
      | pub u a n =>
        simp only [blockOkT, Bool.and_eq_true, decide_eq_true_eq] at hbp
        simp only [InputBlock.first, InputBlock.len] at hbq
        omega
      | realizationPub rp a n =>
        simp only [blockOkT, Bool.and_eq_true, decide_eq_true_eq] at hbp
        simp only [InputBlock.first, InputBlock.len] at hbq
        omega
      | committed u a n =>
        have hpl := blockOkT_committed hbp
        simp only [InputBlock.first, InputBlock.len] at hbq
        have hk : CellKey.val u (q - a) ∈ ir.cellKeys (ir.circuit c).domain :=
          (ir.mem_cellKeys_val).2 ⟨hpl.1, hpl.2.1, by omega⟩
        rw [if_pos (by omega), ir.inputCoord_eq rs Pads hc hb hbq']
        simp only [blockCoord, if_pos (show a ≤ (q : ℕ) ∧ (q : ℕ) < a + n by omega), Option.bind_some,
          id_eq, InputBlock.privValue?, Option.getD_some, ofCells, dif_pos hk]
        rw [optVal_keyCoord hk, castElt_castElt_of_eq (by rw [ir.isCellValue_valueField hpl.2.1])]
      | pad u a n =>
        have hpl := blockOkT_pad hbp
        simp only [InputBlock.first, InputBlock.len] at hbq
        have hk : CellKey.pad u (q - a) ∈ ir.cellKeys (ir.circuit c).domain :=
          (ir.mem_cellKeys_pad).2 ⟨hpl.1, hpl.2.1, hpl.2.2.1, by omega⟩
        rw [if_pos (by omega), ir.inputCoord_eq rs Pads hc hb hbq']
        simp only [blockCoord, if_pos (show a ≤ (q : ℕ) ∧ (q : ℕ) < a + n by omega), Option.bind_some,
          id_eq, InputBlock.privValue?, Option.getD_some, ofCells, dif_pos hk]
        rw [optVal_keyCoord hk, castElt_castElt_of_eq (by rw [ir.isLateOf_valueField hpl.2.2.1])]
      | view u a n =>
        have hpl := blockOkT_view hbp
        simp only [InputBlock.first, InputBlock.len] at hbq
        obtain ⟨w, sel, hkv, hvd, -, -, -, -⟩ := bitViewOk_spec hpl.1
        have hww := hv u w sel hkv hvd
        rw [if_pos (by omega), ir.inputCoord_eq rs Pads hc hb hbq']
        simp only [blockCoord, if_pos (show a ≤ (q : ℕ) ∧ (q : ℕ) < a + n by omega), Option.bind_some,
          id_eq, InputBlock.privValue?, Option.getD_some]
        rw [optVal_viewCoord Pk.bitsAdditive hkv, wordBit_treeBits ht hp hr x hww]
        change _ = castElt (ir.cellValuation I (ir.circuit c).domain p.stmt p.run
          (ir.treeDecode (ir.circuit c).domain rs Pads x) u (q - a))
        rw [← bitValuation_cellBits (show ir.bitViewOk (ir.circuit c).domain u = true from hpl.1)
          (ir.cellValuation I (ir.circuit c).domain p.stmt p.run
            (ir.treeDecode (ir.circuit c).domain rs Pads x)) p.stmt p.run
          (ir.treeDecode (ir.circuit c).domain rs Pads x)]
        simp only [bitValuation, hkv]
        rw [castElt_castElt_of_eq (by
          rw [ir.valueField_of_allowsField (v := u) (by rw [hkv]; rfl), hvd])]
      | filler a n =>
        simp only [blockOkT, Bool.and_eq_true, decide_eq_true_eq] at hbp
        simp only [InputBlock.first, InputBlock.len] at hbq
        rw [if_pos (by omega), ir.inputCoord_eq rs Pads hc hb hbq']
        simp only [blockCoord, if_pos (show a ≤ (q : ℕ) ∧ (q : ℕ) < a + n by omega), Option.bind_some,
          id_eq, InputBlock.privValue?, Option.getD_some]
        unfold keyCoord
        split_ifs with hk
        · exact hfill q hk
        · rfl
      | batchPads bb a n =>
        simp only [blockOkT, Bool.and_eq_true, decide_eq_true_eq] at hbp
        simp only [InputBlock.first, InputBlock.len] at hbq
        rw [if_neg (by omega)]
        simp only [InputBlock.privValue?, if_pos (show a ≤ (q : ℕ) ∧ (q : ℕ) < a + n by omega),
          Option.getD_some]
    · rw [if_neg (by omega), InputBlock.findSome?_eq_none_of_end_le hc.layout (by omega)
        fun b' => InputBlock.holds_of_privValue?]
      rfl

end Input

/-! ## Filler cells -/

section Filler

variable {ir : RealizedProgram} {I : Interp} {d : ℕ}

/-- **The cells with every filler cell `0`.** -/
def zeroFiller (a : ir.Cell d → (I (ir.domainField d)).K) : ir.Cell d → (I (ir.domainField d)).K :=
  fun k => match k with
    | ⟨.filler _ _, _⟩ => 0
    | k => a k

variable (ir) in
/-- **The filler cells are `0`.** -/
def FillerZero (a : ir.Cell d → (I (ir.domainField d)).K) : Prop :=
  ∀ (c j : ℕ) (hk : CellKey.filler c j ∈ ir.cellKeys d), a ⟨_, hk⟩ = 0

theorem fillerZero_zeroFiller (a : ir.Cell d → (I (ir.domainField d)).K) :
    ir.FillerZero (zeroFiller a) := fun _ _ _ => rfl

/-- **The committed assignment of the cells does not read the filler cells.** -/
theorem ofCells_zeroFiller (a : ir.Cell d → (I (ir.domainField d)).K) :
    ir.ofCells I d (zeroFiller a) = ir.ofCells I d a := rfl

/-- **The domain's predicate does not read the filler cells**: every circuit, row, batch and
quadratic triple reads the cells through their committed assignment (`affineRow_holds_iff`,
`batchRelation_holds_congr`, `bitsBatchRelation_holds_congr`, `viewRow_holds_iff`), and a filler
cell's base is the whole field. -/
theorem holds_zeroFiller {x : ir.Valuation I} {r : (ir.layout I).Run}
    {a : ir.Cell d → (I (ir.domainField d)).K} (h : (ir.domainOf I d).Holds x a r) :
    (ir.domainOf I d).Holds x (zeroFiller a) r where
  base k := by
    obtain ⟨⟨v, i⟩ | ⟨v, i⟩ | ⟨c, j⟩, hk⟩ := k
    · exact h.base _
    · exact h.base _
    · show (0 : (I (ir.domainField d)).K) ∈ ir.cellBase I d ⟨.filler c j, hk⟩
      simp only [cellBase, Set.mem_univ]
  circuit c := h.circuit c
  affine q := (affineRow_holds_iff q x (zeroFiller a) r).2 ((affineRow_holds_iff q x a r).1 (h.affine q))
  quad q := by
    have hq := h.quad q
    change (ir.quadRow I d q).Holds (zeroFiller a)
    change (ir.quadRow I d q).Holds a at hq
    unfold quadRow at hq ⊢
    revert hq
    cases ir.quadLeaves d q.1.1 with
    | none => exact id
    | some t =>
      obtain ⟨a', b', c'⟩ := t
      exact id
  batch b := by
    rcases b with ⟨b, hb⟩ | ⟨b, hb, hadd⟩
    · exact (batchRelation_holds_congr (partsOk_of_cols hb) (a := zeroFiller a) (a' := a)
        (r := r) (r' := r) rfl).2
        (h.batch (.inl ⟨b, hb⟩))
    · exact (bitsBatchRelation_holds_congr hb hadd (a := zeroFiller a) (a' := a) (r := r)
        (r' := r) rfl).2
        (h.batch (.inr ⟨b, hb, hadd⟩))
  viewRow q := (viewRow_holds_iff q x (zeroFiller a) r).2 ((viewRow_holds_iff q x a r).1 (h.viewRow q))

end Filler

/-! ## The honest masked reduction -/

section HonestClaim

variable (ir : RealizedProgram) {I : Interp} {d : ℕ}
  (src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c)
  {Pk : (I (ir.domainField d)).Packing} (rs : List (REdge (I (ir.domainField d)) Pk))

variable (d) in
/-- **The honest domain of domain `d`'s circuit proof**: the domain's predicate on the cells, the
filler cells `0`. -/
def HonestDom (p : ir.DomainPub I) (a : ir.Cell d → (I (ir.domainField d)).K) : Prop :=
  (ir.domainOf I d).Holds p.stmt a p.run ∧ ir.FillerZero a

/-- **The honest logical assignment** of the cells `a`: the logical assignment of the honest
committed cells with zero masks and pads. -/
def fieldHonestLog (a : ir.Cell d → (I (ir.domainField d)).K) :
    ir.FLog src Pk rs → (I (ir.domainField d)).K :=
  (ir.treeLevel d rs (ir.ClaimPads d src Pk)).view
    (ir.treeHonestCells d rs (ir.ClaimPads d src Pk) a 0 0 0)

variable {ir src rs}

theorem treeCells_fieldHonestLog (hok : ir.ClaimOk rs) {a : ir.Cell d → (I (ir.domainField d)).K}
    (hbase : ∀ k, a k ∈ ir.cellBase I d k) :
    ir.treeCells rs (ir.ClaimPads d src Pk) (ir.fieldHonestLog src rs a) = a :=
  treeDecode_treeHonestCells hok.tree hok.place hbase 0 0 0

theorem colsBatchOkB_of (cb : ir.CBatch I d .columns) : ir.colsBatchOkB d cb.idx = true := by
  simp only [colsBatchOkB, cb.ok, cb.operands, Bool.true_and, beq_self_eq_true]

theorem bitsBatchOkB_of (cb : ir.CBatch I d .bits) : ir.bitsBatchOkB d cb.idx = true := by
  simp only [bitsBatchOkB, cb.ok, cb.operands, Bool.true_and, beq_self_eq_true]

/-- **Completeness of the compiler correspondence on the tree's coordinates**, the circuit's
source read along its domain: where the circuit's meaning holds at the decoded cells and the
filler cells decode to `0`, the source accepts the input of the logical assignment
(`treeInput_eq_circuitInput`, `CircuitsAccept`). -/
theorem satisfied_cast_of_accept (TA : ir.CircuitsAccept I src) {c : Fin ir.circuits.length}
    (hcd : (ir.circuit c).domain = d) {Pk : (I (ir.domainField d)).Packing}
    {rs : List (REdge (I (ir.domainField d)) Pk)} {Pads : Type} [Fintype Pads]
    (hc : ir.InputsT d c) (hv : ir.ViewsOk d (rs.map REdge.plan))
    (ht : TreeOk (rs.map REdge.plan) Pk.n) (hp : ir.PlaceOk d Pk (rs.map REdge.plan))
    (hr : ir.RealizedOk d rs) (p : ir.DomainPub I)
    (x : ir.TreeCell d Pk rs Pads → (I (ir.domainField d)).K)
    (hfill : ∀ (j : ℕ) (hk : CellKey.filler c j ∈ ir.cellKeys d), ir.treeDecode d rs Pads x ⟨_, hk⟩ = 0)
    (hcirc : ir.CircuitHolds I c (ir.cellValuation I d p.stmt p.run (ir.treeDecode d rs Pads x))) :
    (cast (congrArg (fun e => GordieHowe.GKR.LayeredCircuit (I (ir.domainField e)).K (src c).d) hcd)
      (src c).S).Satisfied ((ir.treeInputForms rs Pads c (src c).d).input p
        ((ir.treeLevel d rs Pads).view x)) := by
  subst hcd
  rw [treeInput_eq_circuitInput hc hv ht hp hr p x hfill]
  exact TA.accept c p.stmt p.run _ hcirc

/-- **The honest circuits' sources accept the honest logical assignment** (`satisfied_cast_of_accept`
at the honest committed cells, which decode to the cells). -/
theorem circSource_satisfied (hok : ir.ClaimOk rs) (TA : ir.CircuitsAccept I src)
    (i : Fin (ir.circs d).length) (p : ir.DomainPub I) {a : ir.Cell d → (I (ir.domainField d)).K}
    (h : ir.HonestDom d p a) :
    (ir.circSource d src i).Satisfied
      ((ir.treeInputForms rs (ir.ClaimPads d src Pk) (ir.circAt d i) (src (ir.circAt d i)).d).input p
        (ir.fieldHonestLog src rs a)) := by
  have hdec := treeDecode_treeHonestCells (Pads := ir.ClaimPads d src Pk) hok.tree hok.place h.1.base 0 0 0
  refine satisfied_cast_of_accept TA (circAt_domain i) (hok.inputs _ (List.getElem_mem _)) hok.views
    hok.tree hok.place hok.realized p _ (fun j hk => ?_) ?_
  · rw [hdec]
    exact h.2 _ j hk
  · rw [hdec]
    exact h.1.circuit ⟨ir.circAt d i, circAt_domain i⟩

variable (ir src rs) in
/-- **The simulator of the `i`-th circuit's GKR** (`GKR.LayeredCircuit.maskedSim`).

Running time: that of `GKR.LayeredCircuit.maskedSim`, linear in the GKR transcript. This running
time is argued here, not proved in Lean. -/
def gkrSim (i : Fin (ir.circs d).length) : (ir.gkrIP src rs i).Sim :=
  GKR.LayeredCircuit.maskedSim (ir.circSource d src i) (ir.circNodes d src i)
    (ir.treeInputForms rs (ir.ClaimPads d src Pk) (ir.circAt d i) (src (ir.circAt d i)).d)
    (ir.gkrPadCell src rs i) (ir.treeLevel d rs (ir.ClaimPads d src Pk))

variable (ir src rs) in
/-- **The honest GKR of the `i`-th circuit** at the honest logical assignment
(`GKR.LayeredCircuit.maskedHonest`, `circSource_satisfied`), simulated by `gkrSim`. -/
def gkrHonest (hok : ir.ClaimOk rs) (TA : ir.CircuitsAccept I src)
    (i : Fin (ir.circs d).length) :
    (ir.gkrIP src rs i).Honest (ir.treeLevel d rs (ir.ClaimPads d src Pk)).view
      (ir.Cell d → (I (ir.domainField d)).K) (ir.HonestDom d) (ir.gkrSim src rs i) :=
  (GKR.LayeredCircuit.maskedHonest (ir.circSource d src i) (ir.circNodes d src i)
    (ir.treeInputForms rs (ir.ClaimPads d src Pk) (ir.circAt d i) (src (ir.circAt d i)).d)
    (ir.gkrPadCell src rs i) (ir.treeLevel d rs (ir.ClaimPads d src Pk))).comap
    (fun _ a => ir.fieldHonestLog src rs a) fun p a h => circSource_satisfied hok TA i p h

variable (ir src rs) in
/-- **The simulator of branch `j`**: the batch's (`BatchedZerocheck.AffineBatch.sim`,
`BatchedZerocheck.MergedAffineBatch.sim`), with the bit sumcheck on bits (`bitSim`), or every circuit's
GKR simulator in order (`gkrSim`).

Running time: one run of the branch's simulators (their docstrings). This running time is argued
here, not proved in Lean. -/
def branchSim : (j : ir.BranchIdx d Pk) → (ir.branchIP src rs j).Sim
  | .inl (.inl (.inl i)) =>
    (ir.colsBatchAt rs (ir.ClaimPads d src Pk) (ir.cbatches d Pk)[i]).sim
      (ir.DomainPub I) (ir.colsPadCell src rs i) (ir.treeLevel d rs (ir.ClaimPads d src Pk))
  | .inl (.inl (.inr i)) =>
    (ir.bitsBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumBatches d Pk)[i]).cb).bitSim
      (ir.DomainPub I) (fun q : ((ir.sumBatches d Pk)[i]).cb.Pad => ir.sumPadCell src rs i (.inl q))
      (ir.treeLevel d rs (ir.ClaimPads d src Pk))
      (ir.bitLayoutAt src rs (fun r => ir.sumPadCell src rs i (.inr r))
        ((ir.sumBatches d Pk)[i]).nodes)
  | .inl (.inr (.inl i)) =>
    (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) (ir.mbatches d Pk)[i]).sim
      (ir.DomainPub I) (ir.mergedPadCell src rs i) (ir.treeLevel d rs (ir.ClaimPads d src Pk))
  | .inl (.inr (.inr i)) =>
    (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumMBatches d Pk)[i]).mb).bitSim
      (ir.DomainPub I) (fun q : ((ir.sumMBatches d Pk)[i]).mb.Pad => ir.sumMergedPadCell src rs i (.inl q))
      (ir.treeLevel d rs (ir.ClaimPads d src Pk))
      (ir.bitLayoutAt src rs (fun r => ir.sumMergedPadCell src rs i (.inr r))
        ((ir.sumMBatches d Pk)[i]).nodes)
  | .inr _ => FieldProof.MaskedReduction.Sim.ofList (M := ir.gkrIP src rs) (ncOf := fun _ => 1)
      (ir.gkrSim src rs) (List.finRange _)

variable (ir src rs) in
/-- **The honest masked reduction of branch `j`** on the honest domain (`HonestDom`) at the honest logical
assignment (`fieldHonestLog`): the honest batch (`BatchedZerocheck.AffineBatch.honest`,
`BatchedZerocheck.MergedAffineBatch.honest`) where the domain's batched relation holds on the cells
(`colsBatchAt_holds_iff`, `bitsBatchAt_holds_iff`, `mergedBatchAt_holds_iff`,
`mergedBatchAt_holds_iff_bits`), with the bit sumcheck on bits (`bitHonest`), or the honest GKR of
every circuit (`GKR.LayeredCircuit.maskedHonest`) through the compiler's completeness; simulated by
`branchSim`. -/
noncomputable def branchHonest (hok : ir.ClaimOk rs) (TA : ir.CircuitsAccept I src) :
    (j : ir.BranchIdx d Pk) → (ir.branchIP src rs j).Honest
      (ir.treeLevel d rs (ir.ClaimPads d src Pk)).view (ir.Cell d → (I (ir.domainField d)).K)
      (ir.HonestDom d) (ir.branchSim src rs j)
  | .inl (.inl (.inl i)) =>
    ((ir.colsBatchAt rs (ir.ClaimPads d src Pk) (ir.cbatches d Pk)[i]).honest
      (ir.DomainPub I) (ir.colsPadCell src rs i) (ir.treeLevel d rs (ir.ClaimPads d src Pk))).comap
      (fun _ a => ir.fieldHonestLog src rs a) fun p a h => by
        refine (ir.colsBatchAt_holds_iff rs (ir.ClaimPads d src Pk) _ p _).2 ?_
        rw [treeCells_fieldHonestLog hok h.1.base]
        exact h.1.batch (.inl ⟨_, colsBatchOkB_of _⟩)
  | .inl (.inl (.inr i)) =>
    ((ir.bitsBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumBatches d Pk)[i]).cb).bitHonest
      (ir.DomainPub I) (fun q : ((ir.sumBatches d Pk)[i]).cb.Pad => ir.sumPadCell src rs i (.inl q))
      (ir.treeLevel d rs (ir.ClaimPads d src Pk))
      (ir.bitLayoutAt src rs (fun r => ir.sumPadCell src rs i (.inr r))
        ((ir.sumBatches d Pk)[i]).nodes)).comap
      (fun _ a => ir.fieldHonestLog src rs a) fun p a h => by
        refine (ir.bitsBatchAt_holds_iff rs (ir.ClaimPads d src Pk) hok.tree hok.place hok.realized
          hok.views _ (bitsBatchOkB_of _) p _).2 ?_
        rw [treeDecode_treeHonestCells hok.tree hok.place h.1.base 0 0 0]
        exact h.1.batch (.inr ⟨_, bitsBatchOkB_of _, Pk.bitsAdditive⟩)
  | .inl (.inr (.inl i)) =>
    ((ir.mergedBatchAt rs (ir.ClaimPads d src Pk) (ir.mbatches d Pk)[i]).honest
      (ir.DomainPub I) (ir.mergedPadCell src rs i) (ir.treeLevel d rs (ir.ClaimPads d src Pk))).comap
      (fun _ a => ir.fieldHonestLog src rs a) fun p a h => by
        have hom : ((ir.mbatches d Pk)[i]).om = .columns := om_of_mem_mbatches (List.getElem_mem _)
        refine (ir.mergedBatchAt_holds_iff rs (ir.ClaimPads d src Pk) _ hom p _).2 ?_
        rw [treeCells_fieldHonestLog hok h.1.base]
        exact h.1.batch (.inl ⟨_, MBatch.colsOkB _ hom⟩)
  | .inl (.inr (.inr i)) =>
    ((ir.mergedBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumMBatches d Pk)[i]).mb).bitHonest
      (ir.DomainPub I) (fun q : ((ir.sumMBatches d Pk)[i]).mb.Pad => ir.sumMergedPadCell src rs i (.inl q))
      (ir.treeLevel d rs (ir.ClaimPads d src Pk))
      (ir.bitLayoutAt src rs (fun r => ir.sumMergedPadCell src rs i (.inr r))
        ((ir.sumMBatches d Pk)[i]).nodes)).comap
      (fun _ a => ir.fieldHonestLog src rs a) fun p a h => by
        refine (ir.mergedBatchAt_holds_iff_bits rs (ir.ClaimPads d src Pk) hok.tree hok.place
          hok.realized hok.views _ ((ir.sumMBatches d Pk)[i]).bits p _).2 ?_
        rw [treeDecode_treeHonestCells hok.tree hok.place h.1.base 0 0 0]
        exact h.1.batch (.inr ⟨_, MBatch.bitsOkB _ ((ir.sumMBatches d Pk)[i]).bits, Pk.bitsAdditive⟩)
  | .inr _ => FieldProof.MaskedReduction.Honest.ofList (M := ir.gkrIP src rs) (ncOf := fun _ => 1)
      (ir.gkrHonest src rs hok TA) (List.finRange _)

variable (ir src rs) in
/-- **The rows' commitment**: committed cells whose cells are the honest cells and whose bits are
the honest logical assignment's. -/
def RowsCommit (p : ir.DomainPub I) (a : ir.Cell d → (I (ir.domainField d)).K)
    (w : ir.FCell src Pk rs → (I (ir.domainField d)).K) : Prop :=
  ir.treeCells rs (ir.ClaimPads d src Pk) ((ir.treeLevel d rs (ir.ClaimPads d src Pk)).view w) = a ∧
    ir.treeCellBits rs (ir.ClaimPads d src Pk) ((ir.treeLevel d rs (ir.ClaimPads d src Pk)).view w) =
      ir.treeCellBits rs (ir.ClaimPads d src Pk) (ir.fieldHonestLog src rs a)

/-- **The honest rows and quadratic triples hold**: committed cells satisfying the rows'
commitment satisfy every affine row (`affineRow`), every row on views (`viewValuation_treeBits` at
the honest committed cells) and every quadratic triple (at the root cells, `treeDecode_root`). -/
theorem rows_of_honest (hok : ir.ClaimOk rs) (p : ir.DomainPub I)
    (a : ir.Cell d → (I (ir.domainField d)).K) (h : ir.HonestDom d p a)
    (w : ir.FCell src Pk rs → (I (ir.domainField d)).K) (hw : ir.RowsCommit src rs p a w) :
    (∀ c, (ir.rowClaims src rs p c).eval ((ir.treeLevel d rs (ir.ClaimPads d src Pk)).view w) = 0) ∧
      Ligero.Routing.SourceProducts (ir.quadProducts src rs) w := by
  set x0 := ir.treeHonestCells d rs (ir.ClaimPads d src Pk) a 0 0 0 with hx0
  have hdec : ir.treeDecode d rs (ir.ClaimPads d src Pk) x0 = a :=
    treeDecode_treeHonestCells hok.tree hok.place h.1.base 0 0 0
  refine ⟨fun c => ?_, fun q => ?_⟩
  · simp only [rowClaims]
    generalize (Encodable.fintypeEquivFin (α := ir.RowIdx d)).symm c = q
    rcases q with q | q
    · simp only [rowForm, eval_affineOn, LinearMap.comp_apply]
      change (ir.affineRow I d q).form p.stmt p.run
        (ir.treeCells rs (ir.ClaimPads d src Pk) ((ir.treeLevel d rs (ir.ClaimPads d src Pk)).view w)) +
          (ir.affineRow I d q).const p.stmt p.run = 0
      rw [hw.1]
      exact h.1.affine q
    · simp only [rowForm, eval_affineOn, LinearMap.comp_apply]
      change (ir.viewRow I d q).Holds p.stmt
        (Sum.elim (ir.treeCells rs (ir.ClaimPads d src Pk) ((ir.treeLevel d rs (ir.ClaimPads d src Pk)).view w))
          (ir.treeCellBits rs (ir.ClaimPads d src Pk) ((ir.treeLevel d rs (ir.ClaimPads d src Pk)).view w)))
        p.run
      rw [hw.1, hw.2]
      change (ir.viewRow I d q).Holds p.stmt
        (Sum.elim a (ir.treeBits d rs (ir.ClaimPads d src Pk) x0)) p.run
      have h0 := h.1.viewRow q
      change (ir.viewRow I d q).Holds p.stmt (Sum.elim a (ir.cellBits I d a)) p.run at h0
      rw [AffineRow.Holds, viewRow_eval] at h0
      unfold viewDiff at h0
      have hE : ∀ e, ir.viewExprOk d e = true →
          ir.evalWith (ir.viewValuation I d p.stmt p.run
            (Sum.elim (ir.treeDecode d rs (ir.ClaimPads d src Pk) x0)
              (ir.treeBits d rs (ir.ClaimPads d src Pk) x0))) d e =
          ir.evalWith (ir.viewValuation I d p.stmt p.run
            (Sum.elim (ir.treeDecode d rs (ir.ClaimPads d src Pk) x0)
              (ir.cellBits I d (ir.treeDecode d rs (ir.ClaimPads d src Pk) x0)))) d e :=
        fun e he => evalE_congr fun v hv =>
          ir.viewValuation_treeBits rs (ir.ClaimPads d src Pk) hok.tree hok.place hok.realized
            hok.views x0 p.stmt p.run (viewValueOk_of_mem he hv)
      have hsd := viewExprOk_sides q.1.2
      rw [AffineRow.Holds, viewRow_eval]
      unfold viewDiff
      rw [← hdec, hE _ hsd.1, hE _ hsd.2, hdec]
      exact h0
  · obtain ⟨⟨⟨pi, hpi⟩, hq⟩, i⟩ := q
    obtain ⟨⟨a', b', c'⟩, hl⟩ := Option.isSome_iff_exists.1 hq
    obtain ⟨-, ha, hb, hc⟩ := quadLeaves_spec hl
    obtain ⟨hka, hkb, hkc⟩ := hok.quads ⟨⟨⟨pi, hpi⟩, hq⟩, i⟩ a' b' c' hl
    have hroot : ∀ v, ir.quadCellB d v = true → ∀ (hk : CellKey.val v i ∈ ir.cellKeys d),
        w (ir.quadCell src rs (.val v i)) = ir.cellLin I d (.val v i) a := fun v hv hk => by
      have hn : ir.cellNode (rs.map REdge.plan) (CellKey.val v i) = none := by
        simp only [quadCellB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hv
        simp only [cellNode, cellName, hv.1.2, Option.map_none, Option.bind_none]
      rw [cellLin_of_mem hk, quadCell, dif_pos ⟨hk, hn⟩, ← hw.1]
      exact (treeDecode_root (ir := ir) (d := d) w (k := ⟨_, hk⟩) hn).symm
    have hquad := h.1.quad ⟨⟨⟨pi, hpi⟩, hq⟩, i⟩
    change (ir.quadRow I d ⟨⟨⟨pi, hpi⟩, hq⟩, i⟩).Holds a at hquad
    simp only [quadRow, hl, QuadRow.Holds] at hquad
    simp only [quadProducts, hl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [hroot a' ha hka, hroot b' hb hkb, hroot c' hc hkc]
    exact hquad

variable (ir src rs) in
/-- **The honest rows and quadratic triples** (`rows_of_honest`). -/
def rowsHonest (hok : ir.ClaimOk rs) :
    (FieldProof.MaskedReduction.staticProducts (cells := id) (ir.rowClaims src rs) (ir.quadProducts src rs)).Honest
      (ir.treeLevel d rs (ir.ClaimPads d src Pk)).view (ir.Cell d → (I (ir.domainField d)).K)
      (ir.HonestDom d)
      (FieldProof.MaskedReduction.Sim.staticProducts (ir.rowClaims src rs) (ir.quadProducts src rs)) :=
  FieldProof.MaskedReduction.Honest.staticProducts (ir.RowsCommit src rs) fun p a h w hw => rows_of_honest hok p a h w hw

variable (ir src rs) in
/-- **The simulator of domain `d`'s masked reduction**: every branch's simulator in order
(`branchSim`), then the rows' (no rounds).

Running time: the branches' simulators' and the concatenations. This running time is argued here,
not proved in Lean. -/
def fieldClaimSim : (ir.fieldMaskedReduction src rs).Sim :=
  (FieldProof.MaskedReduction.Sim.ofList (M := fun b => ir.branchIP src rs (ir.branchEquiv d Pk b))
      (ncOf := fun b => ir.branchNc d Pk (ir.branchEquiv d Pk b))
      (fun b => ir.branchSim src rs (ir.branchEquiv d Pk b)) (List.finRange _)).append
    (FieldProof.MaskedReduction.Sim.staticProducts (ir.rowClaims src rs) (ir.quadProducts src rs))

variable (ir src rs) in
/-- **The honest masked reduction of domain `d`** on the tree's logical assignment: every branch's honest
masked reduction in order (`branchHonest`), then the honest rows (`rowsHonest`); simulated by
`fieldClaimSim`. -/
noncomputable def fieldClaimHonestLv (hok : ir.ClaimOk rs) (TA : ir.CircuitsAccept I src) :
    (ir.fieldMaskedReduction src rs).Honest (ir.treeLevel d rs (ir.ClaimPads d src Pk)).view
      (ir.Cell d → (I (ir.domainField d)).K) (ir.HonestDom d) (ir.fieldClaimSim src rs) :=
  (FieldProof.MaskedReduction.Honest.ofList (M := fun b => ir.branchIP src rs (ir.branchEquiv d Pk b))
      (ncOf := fun b => ir.branchNc d Pk (ir.branchEquiv d Pk b))
      (fun b => ir.branchHonest src rs hok TA (ir.branchEquiv d Pk b)) (List.finRange _)).append
    ((ir.rowsHonest src rs hok).comap (fun _ x => x.input) fun _ _ h => h)

/-! ### The honest committed cells and their commitment -/

/-- **The operands of a covered batch on columns read only the cells.** -/
theorem colsBatchAt_ops_congr {Pads : Type} [Fintype Pads] [DecidableEq Pads] [Encodable Pads]
    (cb : ir.CBatch I d .columns)
    (p : ir.DomainPub I) {z z' : ir.TLog d rs Pads → (I (ir.domainField d)).K}
    (h : ir.treeCells rs Pads z = ir.treeCells rs Pads z') :
    (ir.colsBatchAt rs Pads cb).map.ops p z = (ir.colsBatchAt rs Pads cb).map.ops p z' := by
  funext row c j
  simp only [BatchedZerocheck.AffineBatch.map, BatchedZerocheck.OperandMap.affine, BatchedZerocheck.affineForm]
  split_ifs
  · simp only [colsBatchAt, eval_affineOn, LinearMap.comp_apply]
    change _ + _ = _ + _
    congr 2
  · rfl

/-- **The operands of a covered merged batch at two committed cell vectors with the same decoded
cells agree**: on columns they read the cells (`mergedBatchAt_form_eval`), on bits the variables of
the decoded cells (`mergedBatchAt_form_eval_bits`). -/
theorem mergedBatchAt_ops_congr {Pads : Type} [Fintype Pads] [DecidableEq Pads] [Encodable Pads]
    (hok : ir.ClaimOk rs)
    (cb : ir.MBatch I d) (p : ir.DomainPub I)
    {x x' : ir.TreeCell d Pk rs Pads → (I (ir.domainField d)).K}
    (h : ir.treeDecode d rs Pads x = ir.treeDecode d rs Pads x') :
    (ir.mergedBatchAt rs Pads cb).map.ops p ((ir.treeLevel d rs Pads).view x) =
      (ir.mergedBatchAt rs Pads cb).map.ops p ((ir.treeLevel d rs Pads).view x') := by
  funext row c j
  simp only [BatchedZerocheck.MergedAffineBatch.map, BatchedZerocheck.OperandMap.affine, BatchedZerocheck.affineForm]
  split_ifs with hN
  · cases hom : cb.om
    · rw [ir.mergedBatchAt_form_eval rs Pads cb hom, ir.mergedBatchAt_form_eval rs Pads cb hom]
      exact congrArg (fun a => ∑ p' : Fin (ir.batch cb.idx).parts.length, ir.opValAt I d
        (ir.cellReader I d a) (ir.instOperand (atomAt ir d cb.om) d cb.idx p' j) _) h
    · rw [ir.mergedBatchAt_form_eval_bits rs Pads hok.tree hok.place hok.realized hok.views cb hom,
        ir.mergedBatchAt_form_eval_bits rs Pads hok.tree hok.place hok.realized hok.views cb hom, h]
  · rfl

/-- **The operands of a covered batch on bits at two committed cell vectors with the same decoded
cells agree** (`bitsBatchAt_form_eval`). -/
theorem bitsBatchAt_ops_congr {Pads : Type} [Fintype Pads] [DecidableEq Pads] [Encodable Pads]
    (hok : ir.ClaimOk rs)
    (cb : ir.CBatch I d .bits) (p : ir.DomainPub I)
    {x x' : ir.TreeCell d Pk rs Pads → (I (ir.domainField d)).K}
    (h : ir.treeDecode d rs Pads x = ir.treeDecode d rs Pads x') :
    (ir.bitsBatchAt rs Pads cb).map.ops p ((ir.treeLevel d rs Pads).view x) =
      (ir.bitsBatchAt rs Pads cb).map.ops p ((ir.treeLevel d rs Pads).view x') := by
  funext row c j
  simp only [BatchedZerocheck.AffineBatch.map, BatchedZerocheck.OperandMap.affine, BatchedZerocheck.affineForm]
  split_ifs with hN
  · have e1 := ir.bitsBatchAt_form_eval rs Pads hok.tree hok.place hok.realized hok.views cb
      (bitsBatchOkB_of cb) p x ⟨_, hN⟩ j
    have e2 := ir.bitsBatchAt_form_eval rs Pads hok.tree hok.place hok.realized hok.views cb
      (bitsBatchOkB_of cb) p x' ⟨_, hN⟩ j
    rw [h] at e1
    exact e1.trans e2.symm
  · rfl

/-- **A private input's coordinate** is a cell's or a bit's coordinate. -/
theorem inputCoord_cases {Pads : Type} {c q : ℕ} {o : ir.TLog d rs Pads}
    (h : ir.inputCoord rs Pads c q = some o) :
    (∃ k, o = ir.place d rs Pads k) ∨ ∃ k j, o = ir.viewPlace d rs Pads k j := by
  unfold inputCoord at h
  obtain ⟨oo, hoo, hb⟩ := Option.bind_eq_some_iff.1 h
  cases hb
  obtain ⟨b, -, hbc⟩ := List.exists_of_findSome?_eq_some hoo
  cases b <;> simp only [blockCoord] at hbc
  all_goals
    first
    | (split_ifs at hbc with h'
       · simp only [Option.some.injEq] at hbc
         first
         | (unfold keyCoord at hbc
            split_ifs at hbc
            cases hbc
            exact .inl ⟨_, rfl⟩)
         | (unfold viewCoord at hbc
            split at hbc
            · split_ifs at hbc
              cases hbc
              exact .inr ⟨_, _, rfl⟩
            · cases hbc))
    | cases hbc

/-- **The input of the logical assignment reads only the cells and their bits.** -/
theorem treeInput_congr {Pads : Type} {c dd : ℕ} (p : ir.DomainPub I)
    {z z' : ir.TLog d rs Pads → (I (ir.domainField d)).K}
    (h1 : ir.treeCells rs Pads z = ir.treeCells rs Pads z')
    (h2 : ir.treeCellBits rs Pads z = ir.treeCellBits rs Pads z') :
    (ir.treeInputForms rs Pads c dd).input p z = (ir.treeInputForms rs Pads c dd).input p z' := by
  funext q
  rw [treeInputForms_input, treeInputForms_input]
  split_ifs
  · rfl
  · cases hq : ir.inputCoord rs Pads c q with
    | none => rfl
    | some o =>
      rcases inputCoord_cases hq with ⟨k, rfl⟩ | ⟨k, j, rfl⟩
      · exact congrFun h1 k
      · exact congrFun h2 (k, j)
  · rfl

variable (ir src rs) in
/-- **The branches' pads.** -/
abbrev BranchPads (hok : ir.ClaimOk rs) (TA : ir.CircuitsAccept I src) : Type :=
  (b : Fin (ir.nBranch d Pk)) → (ir.branchHonest src rs hok TA (ir.branchEquiv d Pk b)).Pads

/-- **The pads of branch `j`** among the branches' pads (`branchEquiv`). -/
def padsOfIdx {hok : ir.ClaimOk rs} {TA : ir.CircuitsAccept I src} (bp : ir.BranchPads src rs hok TA)
    (j : ir.BranchIdx d Pk) : (ir.branchHonest src rs hok TA j).Pads :=
  cast (congrArg (fun j => (ir.branchHonest src rs hok TA j).Pads) ((ir.branchEquiv d Pk).apply_symm_apply j))
    (bp ((ir.branchEquiv d Pk).symm j))

theorem padsOfIdx_branch {hok : ir.ClaimOk rs} {TA : ir.CircuitsAccept I src}
    (bp : ir.BranchPads src rs hok TA) (b : Fin (ir.nBranch d Pk)) :
    padsOfIdx bp (ir.branchEquiv d Pk b) = bp b := by
  have key : ∀ b' (hb : b' = b)
      (h : (ir.branchHonest src rs hok TA (ir.branchEquiv d Pk b')).Pads =
        (ir.branchHonest src rs hok TA (ir.branchEquiv d Pk b)).Pads), cast h (bp b') = bp b := by
    intro b' hb
    subst hb
    intro h
    rfl
  exact key _ ((ir.branchEquiv d Pk).symm_apply_apply b) _

/-- **The honest values of the masked reduction's pad cells**: each batch's pads (`padValue`), each
circuit's (`GKR.LayeredCircuit.padValues`). -/
def claimPadVal {hok : ir.ClaimOk rs} {TA : ir.CircuitsAccept I src}
    (bp : ir.BranchPads src rs hok TA) : ir.ClaimPads d src Pk → (I (ir.domainField d)).K
  | .inl (.inl (.inl ⟨i, q⟩)) =>
    (ir.colsBatchAt rs (ir.ClaimPads d src Pk) (ir.cbatches d Pk)[i]).padValue
      (padsOfIdx bp (.inl (.inl (.inl i)))) q
  | .inl (.inl (.inr ⟨i, .inl q⟩)) =>
    (ir.bitsBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumBatches d Pk)[i]).cb).padValue
      (padsOfIdx bp (.inl (.inl (.inr i)))).1 q
  | .inl (.inl (.inr ⟨i, .inr r⟩)) =>
    (padsOfIdx bp (.inl (.inl (.inr i)))).2 r.1 r.2
  | .inl (.inr (.inl ⟨i, q⟩)) =>
    (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) (ir.mbatches d Pk)[i]).padValue
      (padsOfIdx bp (.inl (.inr (.inl i)))) q
  | .inl (.inr (.inr ⟨i, .inl q⟩)) =>
    (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumMBatches d Pk)[i]).mb).padValue
      (padsOfIdx bp (.inl (.inr (.inr i)))).1 q
  | .inl (.inr (.inr ⟨i, .inr r⟩)) =>
    (padsOfIdx bp (.inl (.inr (.inr i)))).2 r.1 r.2
  | .inr ⟨i, q⟩ =>
    GKR.LayeredCircuit.padValues (ir.circSource d src i)
      (FieldProof.MaskedReduction.Honest.ofListPads (M := ir.gkrIP src rs) (ncOf := fun _ => 1)
        (ir.gkrHonest src rs hok TA) (List.finRange _) (padsOfIdx bp (.inr ())) i
        (List.mem_finRange i)) q

/-- **The honest committed cells of domain `d`** at the cells `a`, the branches' pads `bp` and the
masks' pads `mp`: the prefix and mask cells hold the masks' values (`maskVal`), the pad cells the
branches' pad values (`claimPadVal`). -/
def fieldHonestCells {hok : ir.ClaimOk rs} {TA : ir.CircuitsAccept I src}
    (a : ir.Cell d → (I (ir.domainField d)).K) (bp : ir.BranchPads src rs hok TA)
    (mp : MaskPads (ir.fieldEdges d Pk rs (ir.ClaimPads d src Pk))) :
    ir.FCell src Pk rs → (I (ir.domainField d)).K :=
  ir.treeHonestCells d rs (ir.ClaimPads d src Pk) a
    (fun j => (maskVal (ir.fieldEdges d Pk rs (ir.ClaimPads d src Pk)) mp (.inl j)).getD 0)
    (fun o => (maskVal (ir.fieldEdges d Pk rs (ir.ClaimPads d src Pk)) mp (.inr (.inr (.mask o)))).getD 0)
    (claimPadVal bp)

/-- **The honest committed cells' cells and bits are the honest logical assignment's**
(`honestView_place`). -/
theorem fieldHonestCells_place {hok : ir.ClaimOk rs} {TA : ir.CircuitsAccept I src}
    {a : ir.Cell d → (I (ir.domainField d)).K} (hbase : ∀ k, a k ∈ ir.cellBase I d k)
    (bp : ir.BranchPads src rs hok TA) (mp : MaskPads (ir.fieldEdges d Pk rs (ir.ClaimPads d src Pk))) :
    ir.treeCells rs (ir.ClaimPads d src Pk)
        ((ir.treeLevel d rs (ir.ClaimPads d src Pk)).view (ir.fieldHonestCells a bp mp)) =
      ir.treeCells rs (ir.ClaimPads d src Pk) (ir.fieldHonestLog src rs a) ∧
    ir.treeCellBits rs (ir.ClaimPads d src Pk)
        ((ir.treeLevel d rs (ir.ClaimPads d src Pk)).view (ir.fieldHonestCells a bp mp)) =
      ir.treeCellBits rs (ir.ClaimPads d src Pk) (ir.fieldHonestLog src rs a) := by
  obtain ⟨h1, h2⟩ := honestView_place (Pads := ir.ClaimPads d src Pk) hok.tree hok.place hbase _ 0 _ 0 _ 0
  exact ⟨funext fun k => h1 k, funext fun kj => h2 kj.1 kj.2⟩

/-- **The honest committed cells commit every branch** at its pads: the pad cells hold the pad
values, and the operands and the circuits' inputs read the honest cells and bits
(`colsBatchAt_ops_congr`, `bitsBatchAt_ops_congr`, `mergedBatchAt_ops_congr`, `treeInput_congr`). -/
theorem branch_commits (hok : ir.ClaimOk rs) (TA : ir.CircuitsAccept I src) (p : ir.DomainPub I)
    {a : ir.Cell d → (I (ir.domainField d)).K} (hbase : ∀ k, a k ∈ ir.cellBase I d k)
    (bp : ir.BranchPads src rs hok TA) (mp : MaskPads (ir.fieldEdges d Pk rs (ir.ClaimPads d src Pk))) :
    ∀ j, (ir.branchHonest src rs hok TA j).Commits p a (padsOfIdx bp j) (ir.fieldHonestCells a bp mp)
  | .inl (.inl (.inl i)) =>
    BatchedZerocheck.AffineBatch.commits_of _ _ _ p _ _ _
      (colsBatchAt_ops_congr _ p (fieldHonestCells_place hbase bp mp).1) (funext fun _ => rfl)
  | .inl (.inl (.inr i)) =>
    (ir.bitsBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumBatches d Pk)[i]).cb).bitCommits_of
      (fun q : ((ir.sumBatches d Pk)[i]).cb.Pad => ir.sumPadCell src rs i (.inl q))
      (ir.treeLevel d rs (ir.ClaimPads d src Pk))
      (ir.bitLayoutAt src rs (fun r => ir.sumPadCell src rs i (.inr r)) ((ir.sumBatches d Pk)[i]).nodes)
      p (ir.fieldHonestLog src rs a) (padsOfIdx bp (.inl (.inl (.inr i)))).1
      (padsOfIdx bp (.inl (.inl (.inr i)))).2 (ir.fieldHonestCells a bp mp)
      (BatchedZerocheck.AffineBatch.commits_of _ _ _ p _ _ _
        (bitsBatchAt_ops_congr hok _ p ((treeDecode_treeHonestCells hok.tree hok.place hbase _ _ _).trans
          (treeDecode_treeHonestCells hok.tree hok.place hbase 0 0 0).symm)) (funext fun _ => rfl))
      ⟨fun _ _ => rfl, funext fun q => funext fun b =>
        congrFun (fieldHonestCells_place hbase bp mp).2 (ir.bitWord d q, Fin.cast (by norm_num) b)⟩
  | .inl (.inr (.inl i)) =>
    BatchedZerocheck.MergedAffineBatch.commits_of _ _ _ p _ _ _
      (mergedBatchAt_ops_congr hok _ p ((treeDecode_treeHonestCells hok.tree hok.place hbase _ _ _).trans
        (treeDecode_treeHonestCells hok.tree hok.place hbase 0 0 0).symm)) (funext fun _ => rfl)
  | .inl (.inr (.inr i)) =>
    (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumMBatches d Pk)[i]).mb).bitCommits_of
      (fun q : ((ir.sumMBatches d Pk)[i]).mb.Pad => ir.sumMergedPadCell src rs i (.inl q))
      (ir.treeLevel d rs (ir.ClaimPads d src Pk))
      (ir.bitLayoutAt src rs (fun r => ir.sumMergedPadCell src rs i (.inr r))
        ((ir.sumMBatches d Pk)[i]).nodes)
      p (ir.fieldHonestLog src rs a) (padsOfIdx bp (.inl (.inr (.inr i)))).1
      (padsOfIdx bp (.inl (.inr (.inr i)))).2 (ir.fieldHonestCells a bp mp)
      (BatchedZerocheck.MergedAffineBatch.commits_of _ _ _ p _ _ _
        (mergedBatchAt_ops_congr hok _ p ((treeDecode_treeHonestCells hok.tree hok.place hbase _ _ _).trans
          (treeDecode_treeHonestCells hok.tree hok.place hbase 0 0 0).symm)) (funext fun _ => rfl))
      ⟨fun _ _ => rfl, funext fun q => funext fun b =>
        congrFun (fieldHonestCells_place hbase bp mp).2 (ir.bitWord d q, Fin.cast (by norm_num) b)⟩
  | .inr _ => by
    refine (FieldProof.MaskedReduction.Honest.commits_ofList_iff _ _ (List.nodup_finRange _) p a _ _).2 fun i _ => ?_
    exact ⟨funext fun _ => rfl, treeInput_congr p (fieldHonestCells_place hbase bp mp).1
      (fieldHonestCells_place hbase bp mp).2⟩

end HonestClaim

/-! ## The honest prover of the circuit proof -/

section Proof

variable {ir : RealizedProgram} {I : Interp} {d : ℕ} {P : Export.Plan}
  (src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c) (R : ir.FieldReady I d P)
  (TA : ir.CircuitsAccept I src)

/-- **The tree domain's logical assignment is the tree's** (`path_level_eq`). -/
theorem fieldDomain_view :
    (ir.fieldDomain src R).path.level.view = (ir.treeLevel d R.rs (ir.ClaimPads d src R.Pk)).view :=
  congrArg Level.view (path_level_eq _ 0 _ _ 0 _ Fin.elim0)

/-- **The honest masked reduction of domain `d`'s tree domain** (`fieldClaimHonestLv`), its committed
cells' words the honest logical assignment's. -/
noncomputable def fieldClaimHonest :
    (ir.fieldMaskedReduction src R.rs).Honest (ir.fieldDomain src R).path.level.view
      (ir.Cell d → (I (ir.domainField d)).K) (ir.HonestDom d) (ir.fieldClaimSim src R.rs) :=
  ((ir.fieldClaimHonestLv src R.rs R.claimOk TA).withCommits fun _ a _ w =>
    ∀ z, (ir.fieldDomain src R).path.IsWord z →
      (ir.treeLevel d R.rs (ir.ClaimPads d src R.Pk)).view w z = ir.fieldHonestLog src R.rs a z).congrView
    (fieldDomain_view src R).symm

theorem fieldClaimHonest_val_word : ∀ p a π w, (fieldClaimHonest src R TA).Commits p a π w →
    ∀ z, (ir.fieldDomain src R).path.IsWord z →
      (ir.fieldDomain src R).path.level.view w z = ir.fieldHonestLog src R.rs a z := fun _p _x _π _w hw z hz => by
  rw [fieldDomain_view]
  exact hw.2 z hz

/-- **The branches' pads among the masked reduction's pads.** -/
noncomputable def listBranchPads (π : (fieldClaimHonest src R TA).Pads) :
    ir.BranchPads src R.rs R.claimOk TA := fun b =>
  FieldProof.MaskedReduction.Honest.ofListPads (M := fun b => ir.branchIP src R.rs (ir.branchEquiv d R.Pk b))
    (ncOf := fun b => ir.branchNc d R.Pk (ir.branchEquiv d R.Pk b))
    (fun b => ir.branchHonest src R.rs R.claimOk TA (ir.branchEquiv d R.Pk b)) (List.finRange _) π.1 b
    (List.mem_finRange b)

/-- **The honest committed cells hold the masks' values at the mask cells.** -/
theorem fieldHonestCells_maskVal {a : ir.Cell d → (I (ir.domainField d)).K}
    (bp : ir.BranchPads src R.rs R.claimOk TA)
    (mp : MaskPads (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk))) :
    ∀ i v, maskVal (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk)) mp i = some v →
      ir.fieldHonestCells a bp mp i = v := by
  intro i v hv
  obtain ⟨e, he, -, c, hc, -⟩ := exists_of_maskVal _ mp i v hv
  rcases c with j | o
  · obtain ⟨j', hj'⟩ := fieldEdges_maskPre he j
    have hi : i = .inl j' := hc.symm.trans hj'
    subst hi
    simp only [fieldHonestCells, treeHonestCells, cellVal, treeRootAt, treeBase, hv, Option.getD_some]
  · obtain ⟨o', ho'⟩ := fieldEdges_maskOwn he o
    have hi : i = .inr (.inr (.mask o')) := hc.symm.trans ho'
    subst hi
    simp only [fieldHonestCells, treeHonestCells, cellVal, treeRootAt, treeBase, hv, Option.getD_some]

/-- **The simulator data of domain `d`'s tree domain** (`RingSwitching.TreeFieldProof.SimData`): the masked
reduction's simulator (`fieldClaimSim`) and the tree layout's Ligero hiding data. -/
def fieldSimData : (ir.fieldDomain src R).SimData where
  maskedReduction := ir.fieldClaimSim src R.rs
  ligero := (ir.fieldTreeOf src R).layoutHiding R.numbers (ir.fieldMaskedReduction src R.rs)
    (routes_path _ 0 _ _ _ _ (readsOnly_fieldMaskedReduction src R.rs))

/-- **The simulator data of domain `d`'s circuit proof** (`RingSwitching.TreeFieldProof.sim` at
`fieldSimData`). -/
def fieldSim : (ir.fieldProof src R).proof.Sim :=
  (ir.fieldDomain src R).sim (ir.fieldRelation src R) (fieldSimData src R)

/-- **The honest data of domain `d`'s tree domain** (`RingSwitching.TreeFieldProof.HonestData`) on the honest domain
(`HonestDom`): the honest masked reduction (`fieldClaimHonest`), the kits' honest masks
(`PEdge.maskHonest`), the honest logical assignment as the words' values (`fieldHonestLog`), the tree
layout's Ligero honest prover, and the honest committed cells (`fieldHonestCells`) at the masked reduction's
and the masks' pads (`PEdge.splitPads`): they commit every branch (`branch_commits`), the rows
(`fieldHonestCells_place`), the words (`honestView_word`) and the masks
(`PEdge.maskCommits_of_maskVal`), and their prefix cells lie in `S0`. -/
noncomputable def fieldHonestData :
    (ir.fieldDomain src R).HonestData (ir.fieldRelation src R) (fieldSimData src R)
      (ir.Cell d → (I (ir.domainField d)).K) (ir.HonestDom d) where
  maskedReduction := fieldClaimHonest src R TA
  masks := maskHonest (ir.spareCell d R.Pk R.rs (ir.ClaimPads d src R.Pk)) 0
    (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk)) (ir.claimCount (d := d) (Pk := R.Pk))
        (claimReads R.rs)
  val _ a _ := ir.fieldHonestLog src R.rs a
  val_word := fieldClaimHonest_val_word src R TA
  cells a π :=
    ir.fieldHonestCells a
      (listBranchPads src R TA (splitPads (ir.spareCell d R.Pk R.rs (ir.ClaimPads d src R.Pk)) 0
        (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk)) (ir.claimCount (d := d) (Pk := R.Pk))
        (claimReads R.rs)
        (routes_path _ 0 _ _ _ _ (readsOnly_fieldMaskedReduction src R.rs)) (fieldClaimHonest src R TA) (fun _ a _ => ir.fieldHonestLog src R.rs a)
        (fieldClaimHonest_val_word src R TA) π).1)
      (splitPads (ir.spareCell d R.Pk R.rs (ir.ClaimPads d src R.Pk)) 0
        (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk)) (ir.claimCount (d := d) (Pk := R.Pk))
        (claimReads R.rs)
        (routes_path _ 0 _ _ _ _ (readsOnly_fieldMaskedReduction src R.rs)) (fieldClaimHonest src R TA) (fun _ a _ => ir.fieldHonestLog src R.rs a)
        (fieldClaimHonest_val_word src R TA) π).2
  commits p a π h := by
    have hok := R.claimOk
    have hbase := h.1.base
    set sp := splitPads (ir.spareCell d R.Pk R.rs (ir.ClaimPads d src R.Pk)) 0
      (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk)) (ir.claimCount (d := d) (Pk := R.Pk))
        (claimReads R.rs)
      (routes_path _ 0 _ _ _ _ (readsOnly_fieldMaskedReduction src R.rs)) (fieldClaimHonest src R TA) (fun _ a _ => ir.fieldHonestLog src R.rs a)
      (fieldClaimHonest_val_word src R TA) π with hsp
    refine (commits_honestRun_iff _ 0 _ _ _ _ _ _ _ p a π _).2 ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · refine (FieldProof.MaskedReduction.Honest.commits_ofList_iff _ _ (List.nodup_finRange _) p a _ _).2 fun b _ => ?_
      have hc := branch_commits hok TA p hbase (listBranchPads src R TA sp.1) sp.2
        (ir.branchEquiv d R.Pk b)
      rw [padsOfIdx_branch] at hc
      exact hc
    · exact ⟨(fieldHonestCells_place hbase _ _).1.trans (treeCells_fieldHonestLog hok hbase),
        (fieldHonestCells_place hbase _ _).2⟩
    · intro z hz
      exact honestView_word (Pads := ir.ClaimPads d src R.Pk) hok.tree hok.place hbase _ 0 _ 0 _ 0 _ _ z hz
    · exact maskCommits_of_maskVal _ _ (maskCellsDistinct_fieldEdges R.rs) _
        (fieldHonestCells_maskVal src R TA _ _)
  admissible p a π h := by
    refine TreeSpec.admissible_layoutDomain _ _ _ _ fun j => ?_
    change ir.fieldHonestCells a _ _ (.inl j) ∈ R.Pk.S0
    simp only [fieldHonestCells, treeHonestCells, cellVal, treeRootAt, treeBase]
    cases hv : maskVal (ir.fieldEdges d R.Pk R.rs (ir.ClaimPads d src R.Pk)) _ (.inl j) with
    | none => exact R.Pk.S0.zero_mem
    | some v =>
      obtain ⟨e, he, πe, c, hc, rfl⟩ := exists_of_maskVal (h := hv) ..
      rcases c with j0 | o
      · exact e.kit.masks.preVal_mem πe j0
      · obtain ⟨o', ho'⟩ := fieldEdges_maskOwn he o
        exact absurd (hc.symm.trans ho') (by simp)

/-- **The honest prover of domain `d`'s circuit proof** (`GordieHowe.DomainProof.Honest`) at an
honest predicate `hpred` giving the domain's predicate (`hh`): the cells with filler `0` as the
honest input (`zeroFiller`, `holds_zeroFiller`), the tree domain's honest prover at the honest data
(`fieldHonestData`). `TA`: the compiler's completeness (trust base). -/
noncomputable def fieldHonest {hpred : (ir.layout I).Constraint (ir.Valuation I) (ir.domainOf I d).Cells}
    (hh : ∀ x a r, hpred x a r → (ir.domainOf I d).Holds x a r) :
    (ir.fieldProof src R).Honest hpred (fieldSim src R) where
  In := ir.Cell d → (I (ir.domainField d)).K
  dom p a := ir.HonestDom d p a
  encode := zeroFiller
  dom_of x a r h := ⟨holds_zeroFiller (hh x a r h), fillerZero_zeroFiller a⟩
  circuit := (ir.fieldDomain src R).honest (fieldHonestData src R TA)

end Proof

end

end GordieHowe.RealizedProgram
