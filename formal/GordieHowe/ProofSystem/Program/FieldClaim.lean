-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldInput
public import GordieHowe.Language.RealizedProgram.ViewsLemmas
public import GordieHowe.ProofSystem.Zerocheck.MergedAffineBatch
public import GordieHowe.ProofSystem.GKR.MaskedReduction
public import GordieHowe.ProofSystem.FieldProof.MaskedReductionList

@[expose] public section

/-!
# GordieHowe: the masked reduction of a domain on its packing tree

The masked reduction of domain `d` on the logical coordinates of its packing tree (`GordieHowe.RealizedProgram.TLog`), for any
number of batches and GKR circuits:

* **the covered batches on columns** (`GordieHowe.RealizedProgram.cbatches`): every batch of `d` on
  columns that passes the batch check (`BatchOk`), unmerged, with the field's skip domain at its
  width and degree; each as a batch on affine operands of the tree's coordinates
  (`GordieHowe.RealizedProgram.colsBatchAt`, `GordieHowe.BatchedZerocheck.AffineBatch`), an operand
  the operand at the decoded cells;
* **the covered merged batches on columns** (`GordieHowe.RealizedProgram.mbatches`): every batch of
  `d` on columns that passes the batch check with a merging challenge, with the field's skip
  domain; each as a merged batch `Σ_p γ^p Q_p` on the parts' operands summed
  (`GordieHowe.RealizedProgram.mergedForm`, `GordieHowe.BatchedZerocheck.MergedAffineBatch`, error
  `(np − 1)/|K|` at the merging challenge);
* **the covered batches on bits** (`GordieHowe.RealizedProgram.sumBatches` unmerged,
  `GordieHowe.RealizedProgram.sumMBatches` merged): the batch on affine operands of the tree's
  coordinates (`GordieHowe.RealizedProgram.bitsBatchAt`, `GordieHowe.RealizedProgram.mergedForm`;
  an operand on bits the operand at the decoded cells, their bits (`viewPlace`) and the statement
  (`treeLift`)), its masked reduction followed by the masked sumcheck over the `4` bit-index variables of
  the domain's `GF(2^16)` cells (`GordieHowe.BatchedZerocheck.AffineBatch.bitIp`,
  `GordieHowe.BatchedZerocheck.MergedAffineBatch.bitIp`, at the layout `bitLayoutAt`), error
  `2/|K|` per bit round and `8` more pads (`BitPad`). Every batch on bits takes the bit sumcheck;
  the batch check of the domain (`BatchesOk`) requires the export's `Batch.bitSumcheck` on it;
* **the pads** (`GordieHowe.RealizedProgram.ClaimPads`): the batches' pads and the GKR circuits' pads, root own cells
  of the tree layout;
* **the GKR circuits** (`GordieHowe.RealizedProgram.circs`): every circuit of `d`, its source and nodes read in `d`'s
  field (`circSource`, `circNodes`), its input claim on the tree's coordinates
  (`GordieHowe.GKR.LayeredCircuit.maskedReduction` at `treeInputForms`);
* **the rows** (`GordieHowe.RealizedProgram.rowClaims`): the affine rows on the decoded cells and the rows on views on
  the decoded cells and their bits, fixed claims;
* **the masked reduction** (`GordieHowe.RealizedProgram.fieldMaskedReduction`): the batches in order, then the circuits, then the rows
  (`MaskedReduction.ofList`, `MaskedReduction.append`, `MaskedReduction.static`); its soundness (`fieldClaimSound`) for
  the conjunction of the batches', the circuits' and the rows' relations, with the batches' and the
  circuits' errors (`fieldClaimError`).
-/

namespace GordieHowe.RealizedProgram

open Export PEdge BatchedZerocheck IOP Sumcheck.FieldSkip
open Sumcheck.FieldSkip (SkipPoints)
open scoped NNReal

section

variable (ir : RealizedProgram) (I : Interp) (d : ℕ)

/-! ## The covered batches -/

/-- **The atom test of a covered batch**: `atomB` on columns, `bitsAtomB` on bits. -/
abbrev atomAt (ir : RealizedProgram) (d : ℕ) : OperandMap → Expr → Bool
  | .columns => ir.atomB
  | .bits => ir.bitsAtomB d

/-- **A covered batch of domain `d` on the operand map `om`**: a batch passing the batch check with
that operand map, unmerged, with its skip domain. -/
structure CBatch (om : OperandMap) where
  /-- The batch. -/
  idx : Fin ir.batches.length
  /-- It passes the batch check. -/
  ok : ir.batchOkB d idx = true
  /-- Its operand map. -/
  operands : (ir.batch idx).operands = om
  /-- No merging challenge. -/
  unmerged : ir.merged idx = false
  /-- The skip domain. -/
  dom : SkipPoints (I (ir.domainField d)).K (ir.batch idx).width (ir.batch idx).degree

variable {I} in
/-- **The covered batches on columns of domain `d`**, in declaration order, with the field's skip
domains. The covered batches on bits are `sumBatches`. -/
def cbatches (Pk : (I (ir.domainField d)).Packing) : List (ir.CBatch I d .columns) :=
  (List.finRange ir.batches.length).filterMap fun b : Fin ir.batches.length =>
    if h : ir.batchOkB d b = true ∧ (ir.batch b).operands = .columns ∧ ir.merged b = false then
      (Pk.skip (ir.batch b).width (ir.batch b).degree).map fun dom => ⟨b, h.1, h.2.1, h.2.2, dom⟩
    else none

/-- **A covered batch on bits**: the covered batch and the field's interpolation nodes of its bit
sumcheck. -/
structure SCBatch where
  /-- The covered batch. -/
  cb : ir.CBatch I d .bits
  /-- The interpolation nodes of the bit rounds. -/
  nodes : Sumcheck.Nodes (I (ir.domainField d)).K

variable {I} in
/-- **The covered batches on bits of domain `d`**, unmerged, in declaration order, with the field's
skip domains and interpolation nodes. -/
def sumBatches (Pk : (I (ir.domainField d)).Packing) : List (ir.SCBatch I d) :=
  (List.finRange ir.batches.length).filterMap fun b : Fin ir.batches.length =>
    if h : ir.batchOkB d b = true ∧ (ir.batch b).operands = .bits ∧ ir.merged b = false then
      (Pk.skip (ir.batch b).width (ir.batch b).degree).bind fun dom =>
        Pk.nodes.map fun nodes => ⟨⟨b, h.1, h.2.1, h.2.2, dom⟩, nodes⟩
    else none

/-- **A covered merged batch of domain `d`**: a batch passing the batch check, on columns or on
bits, with a merging challenge, with its skip domain. -/
structure MBatch where
  /-- The batch. -/
  idx : Fin ir.batches.length
  /-- It passes the batch check. -/
  ok : ir.batchOkB d idx = true
  /-- Its operand map. -/
  om : OperandMap
  /-- Its operands are on `om`. -/
  operands : (ir.batch idx).operands = om
  /-- Its merging challenge. -/
  merged : ir.merged idx = true
  /-- The skip domain. -/
  dom : SkipPoints (I (ir.domainField d)).K (ir.batch idx).width (ir.batch idx).degree

variable {I} in
/-- **The covered merged batches on columns of domain `d`**, in declaration order, with the field's
skip domains. The covered merged batches on bits are `sumMBatches`. -/
def mbatches (Pk : (I (ir.domainField d)).Packing) : List (ir.MBatch I d) :=
  (List.finRange ir.batches.length).filterMap fun b : Fin ir.batches.length =>
    if h : ir.batchOkB d b = true ∧ ir.merged b = true ∧ (ir.batch b).operands = .columns then
      (Pk.skip (ir.batch b).width (ir.batch b).degree).map fun dom =>
        ⟨b, h.1, .columns, h.2.2, h.2.1, dom⟩
    else none

variable {ir I d} in
/-- **The covered merged batches are on columns.** -/
theorem om_of_mem_mbatches {Pk : (I (ir.domainField d)).Packing} {cb : ir.MBatch I d}
    (h : cb ∈ ir.mbatches d Pk) : cb.om = .columns := by
  obtain ⟨b, -, hb⟩ := List.mem_filterMap.1 h
  split at hb
  · obtain ⟨dom, -, rfl⟩ := Option.map_eq_some_iff.1 hb
    rfl
  · cases hb

/-- **A covered merged batch on bits**: the covered merged batch, on bits, and the field's
interpolation nodes of its bit sumcheck. -/
structure SMBatch where
  /-- The covered merged batch. -/
  mb : ir.MBatch I d
  /-- It is on bits. -/
  bits : mb.om = .bits
  /-- The interpolation nodes of the bit rounds. -/
  nodes : Sumcheck.Nodes (I (ir.domainField d)).K

variable {I} in
/-- **The covered merged batches on bits of domain `d`**, in declaration order, with the field's
skip domains and interpolation nodes. -/
def sumMBatches (Pk : (I (ir.domainField d)).Packing) : List (ir.SMBatch I d) :=
  (List.finRange ir.batches.length).filterMap fun b : Fin ir.batches.length =>
    if h : ir.batchOkB d b = true ∧ ir.merged b = true ∧ (ir.batch b).operands = .bits then
      (Pk.skip (ir.batch b).width (ir.batch b).degree).bind fun dom =>
        Pk.nodes.map fun nodes => ⟨⟨b, h.1, _, rfl, h.2.1, dom⟩, h.2.2, nodes⟩
    else none

variable {ir I d}

theorem MBatch.batchOk (cb : ir.MBatch I d) : ir.BatchOk d cb.idx := (ir.batchOkB_iff d _).1 cb.ok

/-- A covered merged batch on columns passes the check on columns. -/
theorem MBatch.colsOkB (cb : ir.MBatch I d) (hom : cb.om = .columns) :
    ir.colsBatchOkB d cb.idx = true := by
  simp only [colsBatchOkB, cb.ok, cb.operands, hom, beq_self_eq_true, Bool.and_self]

/-- A covered merged batch on bits passes the check on bits. -/
theorem MBatch.bitsOkB (cb : ir.MBatch I d) (hom : cb.om = .bits) :
    ir.bitsBatchOkB d cb.idx = true := by
  simp only [bitsBatchOkB, cb.ok, cb.operands, hom, beq_self_eq_true, Bool.and_self]

theorem MBatch.partsOk (cb : ir.MBatch I d) : ir.PartsOk (atomAt ir d cb.om) d cb.idx := by
  have h := cb.batchOk.partsOk
  simp only [atomOf, cb.operands] at h
  obtain ⟨idx, ok, om, hops, hm, dom⟩ := cb
  cases om <;> exact h

/-- **The instances of a covered merged batch fit its rows**: one part's coordinates, in whole
lanes (`BatchOk.instances`, merged). -/
theorem MBatch.fits (cb : ir.MBatch I d) :
    ir.partLen d cb.idx 0 ≤ 2 ^ (ir.batch cb.idx).rounds * (ir.batch cb.idx).width := by
  have hi := cb.batchOk.instances
  have hr := cb.batchOk.rows
  rw [if_pos cb.merged] at hi
  refine le_trans ?_ hr
  rw [hi]
  have hl : 0 < (ir.batch cb.idx).operands.lane := by
    cases (ir.batch cb.idx).operands <;> simp [OperandMap.lane]
  unfold partCount
  have := Nat.div_add_mod (ir.partLen d cb.idx 0 + ((ir.batch cb.idx).operands.lane - 1))
    (ir.batch cb.idx).operands.lane
  have := Nat.mod_lt (ir.partLen d cb.idx 0 + ((ir.batch cb.idx).operands.lane - 1)) hl
  have h2 : (ir.partLen d cb.idx 0 + ((ir.batch cb.idx).operands.lane - 1)) /
      (ir.batch cb.idx).operands.lane * (ir.batch cb.idx).operands.lane =
      (ir.batch cb.idx).operands.lane * ((ir.partLen d cb.idx 0 +
        ((ir.batch cb.idx).operands.lane - 1)) / (ir.batch cb.idx).operands.lane) := Nat.mul_comm _ _
  omega

/-- **Relation `q` of a covered merged batch**: part `q`'s shape on its slice (`sliceShape`). -/
abbrev MBatch.rels (cb : ir.MBatch I d) (q : Fin (ir.batch cb.idx).parts.length) :
    MonoRelation (I (ir.domainField d)).K (ir.relShape (atomAt ir d cb.om) d cb.idx).k
      (ir.batch cb.idx).degree :=
  (ir.sliceShape (atomAt ir d cb.om) d cb.idx q).rel I (ir.domainField d) _
    (cb.partsOk.sliceShape_ok cb.merged q.2)

/-- **The pads of a covered merged batch** (`BatchedZerocheck.MergedAffineBatch.Pad`). -/
abbrev MBatch.Pad (cb : ir.MBatch I d) : Type :=
  PadIdx (((ir.batch cb.idx).degree - 1) * ((ir.batch cb.idx).width - 1)) (ir.batch cb.idx).degree
    (ir.batch cb.idx).rounds (ir.relShape (atomAt ir d cb.om) d cb.idx).k
    (MonoRelation.mergeShape cb.rels).ChainCell

theorem CBatch.batchOk {om : OperandMap} (cb : ir.CBatch I d om) : ir.BatchOk d cb.idx :=
  (ir.batchOkB_iff d _).1 cb.ok

theorem CBatch.partsOk {om : OperandMap} (cb : ir.CBatch I d om) :
    ir.PartsOk (atomAt ir d om) d cb.idx := by
  have h := cb.batchOk.partsOk
  simp only [atomOf, cb.operands] at h
  cases om <;> exact h

/-- **The instances of a covered batch fit its rows**: its instances are its parts' coordinates
in whole lanes (`BatchOk.instances`), each at least the part's coordinates. -/
theorem CBatch.fits {om : OperandMap} (cb : ir.CBatch I d om) :
    ∑ j : Fin (ir.batch cb.idx).parts.length, ir.partLen d cb.idx j ≤
      2 ^ (ir.batch cb.idx).rounds * (ir.batch cb.idx).width := by
  have hi := cb.batchOk.instances
  have hr := cb.batchOk.rows
  rw [if_neg (by simp [cb.unmerged])] at hi
  refine le_trans ?_ hr
  rw [hi, sum_map_range_eq_sum_fin]
  refine Finset.sum_le_sum fun j _ => ?_
  have hl : 0 < (ir.batch cb.idx).operands.lane := by
    cases (ir.batch cb.idx).operands <;> simp [OperandMap.lane]
  unfold partCount
  have := Nat.div_add_mod (ir.partLen d cb.idx j + ((ir.batch cb.idx).operands.lane - 1))
    (ir.batch cb.idx).operands.lane
  have := Nat.mod_lt (ir.partLen d cb.idx j + ((ir.batch cb.idx).operands.lane - 1)) hl
  have h2 : (ir.partLen d cb.idx j + ((ir.batch cb.idx).operands.lane - 1)) /
      (ir.batch cb.idx).operands.lane * (ir.batch cb.idx).operands.lane =
      (ir.batch cb.idx).operands.lane * ((ir.partLen d cb.idx j +
        ((ir.batch cb.idx).operands.lane - 1)) / (ir.batch cb.idx).operands.lane) := Nat.mul_comm _ _
  omega

/-- **The relation of a covered batch** (`Shape.rel` at the batch's shape). -/
abbrev CBatch.rel {om : OperandMap} (cb : ir.CBatch I d om) :
    MonoRelation (I (ir.domainField d)).K (ir.relShape (atomAt ir d om) d cb.idx).k
      (ir.batch cb.idx).degree :=
  (ir.relShape (atomAt ir d om) d cb.idx).rel I (ir.domainField d) _ cb.partsOk.relShape_ok

/-- **The pads of a covered batch** (the masked skip's, `BatchedZerocheck.AffineBatch.Pad`). -/
abbrev CBatch.Pad {om : OperandMap} (cb : ir.CBatch I d om) : Type :=
  PadIdx (((ir.batch cb.idx).degree - 1) * ((ir.batch cb.idx).width - 1)) (ir.batch cb.idx).degree
    (ir.batch cb.idx).rounds (ir.relShape (atomAt ir d om) d cb.idx).k cb.rel.ChainCell

/-- **The pads of the bit rounds**: two per round of the `4` rounds over the bit index of a
`GF(2^16)` word. The program layer fixes `m = 4`: its bit views are `16` bits per cell
(`viewPlace`, `treeCellBits` on `Fin 16`), so the designated word subfield is `GF(2^16)`; the bit
sumcheck itself (`FieldProof.MaskedReduction.bitSumcheck`) is generic in `m`. -/
abbrev BitPad : Type := Fin 4 × Fin 2

/-- **The pads of a covered batch on bits**: the batch's, then the bit rounds'. -/
abbrev SCBatch.Pad (sb : ir.SCBatch I d) : Type := sb.cb.Pad ⊕ BitPad

/-- **The pads of a covered merged batch on bits**: the merged batch's, then the bit rounds'. -/
abbrev SMBatch.Pad (sb : ir.SMBatch I d) : Type := sb.mb.Pad ⊕ BitPad

/-! ## The circuits -/

variable (ir d) in
/-- **The GKR circuits of domain `d`**, in order. -/
def circs : List (Fin ir.circuits.length) :=
  (List.finRange ir.circuits.length).filter fun c => (ir.circuit c).domain == d

theorem circs_domain {c : Fin ir.circuits.length} (h : c ∈ ir.circs d) : (ir.circuit c).domain = d := by
  simp only [circs, List.mem_filter, beq_iff_eq] at h
  exact h.2

variable (src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c)

variable (d) in
/-- The `i`-th circuit of domain `d`. -/
abbrev circAt (i : Fin (ir.circs d).length) : Fin ir.circuits.length := (ir.circs d)[i]

theorem circAt_domain (i : Fin (ir.circs d).length) : (ir.circuit (ir.circAt d i)).domain = d :=
  circs_domain (List.getElem_mem _)

variable (d) in
/-- **The source of the `i`-th circuit of domain `d`, read in `d`'s field.** -/
def circSource (i : Fin (ir.circs d).length) :
    GordieHowe.GKR.LayeredCircuit (I (ir.domainField d)).K (src (ir.circAt d i)).d :=
  cast (congrArg (fun e => GordieHowe.GKR.LayeredCircuit (I (ir.domainField e)).K (src (ir.circAt d i)).d)
    (circAt_domain i)) (src (ir.circAt d i)).S

variable (d) in
/-- **The sumcheck nodes of the `i`-th circuit of domain `d`, read in `d`'s field.** -/
def circNodes (i : Fin (ir.circs d).length) : Sumcheck.Nodes (I (ir.domainField d)).K :=
  cast (congrArg (fun e => Sumcheck.Nodes (I (ir.domainField e)).K) (circAt_domain i))
    (src (ir.circAt d i)).nodes

theorem shapeAtMost_cast_source {c : Fin ir.circuits.length} {d' : ℕ}
    (h : (ir.circuit c).domain = d') {w l : ℕ} :
    (cast (congrArg (fun e => GordieHowe.GKR.LayeredCircuit
      (I (ir.domainField e)).K (src c).d) h) (src c).S).ShapeAtMost w l ↔
      (src c).S.ShapeAtMost w l := by
  subst h
  rfl

/-- **The shape bounds of a circuit's source read in the domain's field** are the source's. -/
theorem shapeAtMost_circSource (i : Fin (ir.circs d).length) {w l : ℕ} :
    (ir.circSource d src i).ShapeAtMost w l ↔ (src (ir.circAt d i)).S.ShapeAtMost w l :=
  shapeAtMost_cast_source src (circAt_domain i)

variable (d) {Pk : (I (ir.domainField d)).Packing} in
/-- **The pads of domain `d`'s masked reduction**: every covered batch's, every circuit's. -/
abbrev ClaimPads (Pk : (I (ir.domainField d)).Packing) : Type :=
  (((Σ i : Fin (ir.cbatches d Pk).length, ((ir.cbatches d Pk)[i]).Pad) ⊕
      (Σ i : Fin (ir.sumBatches d Pk).length, ((ir.sumBatches d Pk)[i]).Pad)) ⊕
    ((Σ i : Fin (ir.mbatches d Pk).length, ((ir.mbatches d Pk)[i]).Pad) ⊕
      (Σ i : Fin (ir.sumMBatches d Pk).length, ((ir.sumMBatches d Pk)[i]).Pad))) ⊕
    (Σ i : Fin (ir.circs d).length, (ir.circSource d src i).PadIdx)

instance (Pk : (I (ir.domainField d)).Packing) : Fintype (ir.ClaimPads d src Pk) := by
  unfold ClaimPads
  infer_instance

/-- The masked reduction's pads are encoded as the sum of the batches' and the circuits' pads. -/
instance (Pk : (I (ir.domainField d)).Packing) : Encodable (ir.ClaimPads d src Pk) := by
  unfold ClaimPads
  infer_instance

instance (Pk : (I (ir.domainField d)).Packing) : DecidableEq (ir.ClaimPads d src Pk) := by
  haveI h1 : ∀ (om : OperandMap) (cb : ir.CBatch I d om), DecidableEq cb.Pad := fun _ _ => inferInstance
  haveI h2 : ∀ i, DecidableEq (ir.circSource d src i).PadIdx := fun _ => inferInstance
  haveI h3 : ∀ cb : ir.MBatch I d, DecidableEq cb.Pad := fun _ => inferInstance
  haveI h4 : ∀ sb : ir.SCBatch I d, DecidableEq sb.Pad := fun sb =>
    @instDecidableEqSum _ _ (h1 _ sb.cb) inferInstance
  haveI h5 : ∀ sb : ir.SMBatch I d, DecidableEq sb.Pad := fun sb =>
    @instDecidableEqSum _ _ (h3 sb.mb) inferInstance
  haveI : DecidableEq (Σ i : Fin (ir.cbatches d Pk).length, ((ir.cbatches d Pk)[i]).Pad) :=
    inferInstance
  haveI : DecidableEq (Σ i : Fin (ir.sumBatches d Pk).length, ((ir.sumBatches d Pk)[i]).Pad) :=
    inferInstance
  haveI : DecidableEq (Σ i : Fin (ir.mbatches d Pk).length, ((ir.mbatches d Pk)[i]).Pad) :=
    inferInstance
  haveI : DecidableEq (Σ i : Fin (ir.sumMBatches d Pk).length, ((ir.sumMBatches d Pk)[i]).Pad) :=
    inferInstance
  haveI : DecidableEq (Σ i : Fin (ir.circs d).length, (ir.circSource d src i).PadIdx) :=
    inferInstance
  unfold ClaimPads
  infer_instance

/-! ## The variables of the tree -/

variable {Pk : (I (ir.domainField d)).Packing} (rs : List (REdge (I (ir.domainField d)) Pk))
  (Pads : Type) [Fintype Pads] [DecidableEq Pads] [Encodable Pads]

/-- **The cells of the logical coordinates `z`**: each cell's coordinate. -/
def treeCells (z : ir.TLog d rs Pads → (I (ir.domainField d)).K) :
    ir.Cell d → (I (ir.domainField d)).K :=
  fun k => z (ir.place d rs Pads k)

/-- **The cells' bits of the logical coordinates `z`**: each bit's coordinate. -/
def treeCellBits (z : ir.TLog d rs Pads → (I (ir.domainField d)).K) :
    ir.Cell d × Fin 16 → (I (ir.domainField d)).K :=
  fun kj => z (ir.viewPlace d rs Pads kj.1 kj.2)

/-- **The cells of the logical coordinates, as a linear map.** -/
def treeCellsLin : (ir.TLog d rs Pads → (I (ir.domainField d)).K) →ₗ[(I (ir.domainField d)).K]
    (ir.Cell d → (I (ir.domainField d)).K) where
  toFun := ir.treeCells rs Pads
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The cells and their bits of the logical coordinates, as a linear map.** -/
def treeViewLin : (ir.TLog d rs Pads → (I (ir.domainField d)).K) →ₗ[(I (ir.domainField d)).K]
    (ir.Cell d ⊕ (ir.Cell d × Fin 16) → (I (ir.domainField d)).K) where
  toFun z := Sum.elim (ir.treeCells rs Pads z) (ir.treeCellBits rs Pads z)
  map_add' z z' := by
    funext v
    rcases v with k | kj <;> rfl
  map_smul' t z := by
    funext v
    rcases v with k | kj <;> rfl

/-- **The variables of a bit operand read from the logical coordinates** `z` at the statement `x`:
the cells, their bits, the statement's coordinates. -/
def treeLift (x : ir.Valuation I) (z : ir.TLog d rs Pads → (I (ir.domainField d)).K) :
    ir.BitsVar d → (I (ir.domainField d)).K :=
  Sum.elim (ir.treeCells rs Pads z) (Sum.elim (ir.treeCellBits rs Pads z) fun vi => castElt (x vi.1 vi.2))

/-- **The variables read from the logical coordinates at the zero statement, as a linear map.** -/
def treeLiftLin : (ir.TLog d rs Pads → (I (ir.domainField d)).K) →ₗ[(I (ir.domainField d)).K]
    (ir.BitsVar d → (I (ir.domainField d)).K) where
  toFun := ir.treeLift rs Pads 0
  map_add' z z' := by
    funext v
    rcases v with k | kj | vi
    · rfl
    · rfl
    · simp [treeLift]
  map_smul' t z := by
    funext v
    rcases v with k | kj | vi
    · rfl
    · rfl
    · simp [treeLift]

/-- **The variables read from the logical coordinates split**: those at the zero statement plus
those of the zero coordinates. -/
theorem treeLift_split (x : ir.Valuation I) (z : ir.TLog d rs Pads → (I (ir.domainField d)).K) :
    ir.treeLift rs Pads x z = ir.treeLiftLin rs Pads z + ir.treeLift rs Pads x 0 := by
  funext v
  rcases v with k | kj | vi <;> simp [treeLiftLin, treeLift, treeCells, treeCellBits]

/-- **A function of a bit operand's variables, affine, is affine read from the logical
coordinates.** -/
theorem IsAff.treeLift {g : (ir.BitsVar d → (I (ir.domainField d)).K) → (I (ir.domainField d)).K}
    (h : IsAff g) (x : ir.Valuation I) : IsAff fun z => g (ir.treeLift rs Pads x z) := by
  obtain ⟨l, c, h⟩ := h
  refine ⟨l ∘ₗ ir.treeLiftLin rs Pads, l (ir.treeLift rs Pads x 0) + c, fun z => ?_⟩
  show g _ = _
  rw [h, treeLift_split, map_add, LinearMap.comp_apply]
  ring

/-! ## The batches on the tree's coordinates -/

/-- **A covered batch on columns on the tree's coordinates**: the batch's shape and relation,
operand `o` of instance `t` the batched relation's operand at the decoded cells
(`RealizedProgram.batchRelation`) plus its offset. -/
def colsBatchAt (cb : ir.CBatch I d .columns) :
    AffineBatch (I (ir.domainField d)).K (ir.DomainPub I) (ir.TLog d rs Pads) where
  k := (ir.relShape ir.atomB d cb.idx).k
  D := (ir.batch cb.idx).degree
  N := ∑ j : Fin (ir.batch cb.idx).parts.length, ir.partLen d cb.idx j
  w := (ir.batch cb.idx).width
  n := (ir.batch cb.idx).rounds
  rel := cb.rel
  form p t o := affineOn
    ((gradLin fun z => ir.opValAt I d (ir.cellReader I d z)
      (ir.instOperand ir.atomB d cb.idx (finSigmaFinEquiv.symm t).1 o)
        (finSigmaFinEquiv.symm t).2) ∘ₗ ir.treeCellsLin rs Pads)
    ((ir.batchRelation I d cb.idx).offset p.stmt (finSigmaFinEquiv.symm t) o)
  dom := cb.dom
  fits := cb.fits
  width_ne := Nat.pos_iff_ne_zero.1 cb.batchOk.width
  degree_ne := Nat.pos_iff_ne_zero.1 cb.batchOk.degree

/-- **A covered batch on bits on the tree's coordinates**: the batch's shape and relation, operand
`o` of instance `t` the affine form of the operand at the variables read from the coordinates
(`treeLift`, the gradient and the value at zero). -/
def bitsBatchAt (cb : ir.CBatch I d .bits) :
    AffineBatch (I (ir.domainField d)).K (ir.DomainPub I) (ir.TLog d rs Pads) where
  k := (ir.relShape (ir.bitsAtomB d) d cb.idx).k
  D := (ir.batch cb.idx).degree
  N := ∑ j : Fin (ir.batch cb.idx).parts.length, ir.partLen d cb.idx j
  w := (ir.batch cb.idx).width
  n := (ir.batch cb.idx).rounds
  rel := cb.rel
  form p t o := affineOn
    (gradLin fun z => ir.bitsOperandAt I d cb.idx (finSigmaFinEquiv.symm t) o
      (ir.treeLift rs Pads p.stmt z))
    (ir.bitsOperandAt I d cb.idx (finSigmaFinEquiv.symm t) o (ir.treeLift rs Pads p.stmt 0))
  dom := cb.dom
  fits := cb.fits
  width_ne := Nat.pos_iff_ne_zero.1 cb.batchOk.width
  degree_ne := Nat.pos_iff_ne_zero.1 cb.batchOk.degree

/-- **Operand `o` of instance `t` of a merged batch `b` on the operand map `om`** on the tree's
coordinates at the public input `p`: the parts' operands `o` at coordinate `t` summed, on columns
at the decoded cells (`mergedOpAt`), on bits at the variables read from the coordinates
(`mergedBitsOpAt` at `treeLift`), as the gradient plus the value at zero. -/
def mergedForm (b : Fin ir.batches.length) (p : ir.DomainPub I) (t o : ℕ) :
    OperandMap → AffineForm (I (ir.domainField d)).K (ir.TLog d rs Pads)
  | .columns => affineOn ((gradLin fun z => ir.mergedOpAt I d b z o t) ∘ₗ ir.treeCellsLin rs Pads)
      (ir.mergedOpAt I d b 0 o t)
  | .bits => affineOn (gradLin fun z => ir.mergedBitsOpAt I d b (ir.treeLift rs Pads p.stmt z) o t)
      (ir.mergedBitsOpAt I d b (ir.treeLift rs Pads p.stmt 0) o t)

/-- **A covered merged batch on the tree's coordinates**: relation `q` part `q`'s shape on its
slice, operand `o` of instance `t` the parts' operands `o` at coordinate `t` summed
(`mergedForm` at the batch's operand map). -/
def mergedBatchAt (cb : ir.MBatch I d) :
    MergedAffineBatch (I (ir.domainField d)).K (ir.DomainPub I) (ir.TLog d rs Pads) where
  k := (ir.relShape (atomAt ir d cb.om) d cb.idx).k
  D := (ir.batch cb.idx).degree
  N := ir.partLen d cb.idx 0
  w := (ir.batch cb.idx).width
  n := (ir.batch cb.idx).rounds
  np := (ir.batch cb.idx).parts.length
  rels := cb.rels
  form p t o := ir.mergedForm rs Pads cb.idx p t o cb.om
  dom := cb.dom
  fits := cb.fits
  width_ne := Nat.pos_iff_ne_zero.1 cb.batchOk.width
  degree_ne := Nat.pos_iff_ne_zero.1 cb.batchOk.degree

/-! ## The masked reduction -/

section Claim

variable (Pk) in
/-- **The committed cells of domain `d`** with the masked reduction's pads. -/
abbrev FCell : Type := ir.TreeCell d Pk rs (ir.ClaimPads d src Pk)

variable (Pk) in
/-- **The logical coordinates of domain `d`'s tree** with the masked reduction's pads. -/
abbrev FLog : Type := ir.TLog d rs (ir.ClaimPads d src Pk)

/-- The pad cells of the `i`-th covered batch on columns. -/
def colsPadCell (i : Fin (ir.cbatches d Pk).length) (q : ((ir.cbatches d Pk)[i]).Pad) :
    ir.FCell src Pk rs :=
  .inr (.inr (.pad (.inl (.inl (.inl ⟨i, q⟩)))))

/-- The pad cells of the `i`-th covered batch on bits. -/
def sumPadCell (i : Fin (ir.sumBatches d Pk).length) (q : ((ir.sumBatches d Pk)[i]).Pad) :
    ir.FCell src Pk rs :=
  .inr (.inr (.pad (.inl (.inl (.inr ⟨i, q⟩)))))

/-- The pad cells of the `i`-th covered merged batch on columns. -/
def mergedPadCell (i : Fin (ir.mbatches d Pk).length) (q : ((ir.mbatches d Pk)[i]).Pad) :
    ir.FCell src Pk rs :=
  .inr (.inr (.pad (.inl (.inr (.inl ⟨i, q⟩)))))

/-- The pad cells of the `i`-th covered merged batch on bits. -/
def sumMergedPadCell (i : Fin (ir.sumMBatches d Pk).length) (q : ((ir.sumMBatches d Pk)[i]).Pad) :
    ir.FCell src Pk rs :=
  .inr (.inr (.pad (.inl (.inr (.inr ⟨i, q⟩)))))

variable (d) in
/-- **The word `q` of the bit sumcheck**: the `q`-th cell of domain `d`. -/
def bitWord (q : Fin (ir.cellKeys d).length) : ir.Cell d :=
  ⟨(ir.cellKeys d)[q], List.getElem_mem _⟩

/-- **The bit layout of a batch on bits** on the tree's coordinates at the pad cells `pad` and the
nodes `nodes`: bit `b` of word `q` is bit `b` of the `q`-th cell (`viewPlace`, the spare coordinate
for a cell with no view child). The weights are the opening claim's coefficients, so the layout
need not be injective. -/
def bitLayoutAt (pad : BitPad → ir.FCell src Pk rs)
    (nodes : Sumcheck.Nodes (I (ir.domainField d)).K) :
    BitLayout (I (ir.domainField d)).K (ir.FCell src Pk rs) (ir.FLog src Pk rs) 4
      (ir.cellKeys d).length where
  bit q b := ir.viewPlace d rs (ir.ClaimPads d src Pk) (ir.bitWord d q) (Fin.cast (by norm_num) b)
  pad r j := pad (r, j)
  nodes := nodes

/-- The pad cells of the `i`-th circuit. -/
def gkrPadCell (i : Fin (ir.circs d).length) (q : (ir.circSource d src i).PadIdx) :
    ir.FCell src Pk rs :=
  .inr (.inr (.pad (.inr ⟨i, q⟩)))

/-- **The masked reduction of the `i`-th covered batch on columns** (`BatchedZerocheck.AffineBatch.ip`). -/
def colsIP (i : Fin (ir.cbatches d Pk).length) :
    FieldProof.MaskedReduction (I (ir.domainField d)).K (ir.FCell src Pk rs) (ir.DomainPub I)
      (ir.FCell src Pk rs → (I (ir.domainField d)).K) id (ir.FLog src Pk rs) 1 :=
  (ir.colsBatchAt rs (ir.ClaimPads d src Pk) (ir.cbatches d Pk)[i]).ip (ir.DomainPub I)
    (ir.colsPadCell src rs i) (ir.treeLevel d rs (ir.ClaimPads d src Pk))

/-- **The masked reduction of the `i`-th covered batch on bits**
(`BatchedZerocheck.AffineBatch.bitIp`). -/
def sumIP (i : Fin (ir.sumBatches d Pk).length) :
    FieldProof.MaskedReduction (I (ir.domainField d)).K (ir.FCell src Pk rs) (ir.DomainPub I)
      (ir.FCell src Pk rs → (I (ir.domainField d)).K) id (ir.FLog src Pk rs) 1 :=
  (ir.bitsBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumBatches d Pk)[i]).cb).bitIp (ir.DomainPub I)
    (fun q : ((ir.sumBatches d Pk)[i]).cb.Pad => ir.sumPadCell src rs i (.inl q)) (ir.treeLevel d rs (ir.ClaimPads d src Pk))
    (ir.bitLayoutAt src rs (fun r => ir.sumPadCell src rs i (.inr r)) ((ir.sumBatches d Pk)[i]).nodes)

/-- **The masked reduction of the `i`-th covered merged batch on columns**
(`BatchedZerocheck.MergedAffineBatch.ip`). -/
def mergedIP (i : Fin (ir.mbatches d Pk).length) :
    FieldProof.MaskedReduction (I (ir.domainField d)).K (ir.FCell src Pk rs) (ir.DomainPub I)
      (ir.FCell src Pk rs → (I (ir.domainField d)).K) id (ir.FLog src Pk rs) 1 :=
  (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) (ir.mbatches d Pk)[i]).ip (ir.DomainPub I)
    (ir.mergedPadCell src rs i) (ir.treeLevel d rs (ir.ClaimPads d src Pk))

/-- **The masked reduction of the `i`-th covered merged batch on bits**
(`BatchedZerocheck.MergedAffineBatch.bitIp`). -/
def sumMergedIP (i : Fin (ir.sumMBatches d Pk).length) :
    FieldProof.MaskedReduction (I (ir.domainField d)).K (ir.FCell src Pk rs) (ir.DomainPub I)
      (ir.FCell src Pk rs → (I (ir.domainField d)).K) id (ir.FLog src Pk rs) 1 :=
  (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumMBatches d Pk)[i]).mb).bitIp (ir.DomainPub I)
    (fun q : ((ir.sumMBatches d Pk)[i]).mb.Pad => ir.sumMergedPadCell src rs i (.inl q)) (ir.treeLevel d rs (ir.ClaimPads d src Pk))
    (ir.bitLayoutAt src rs (fun r => ir.sumMergedPadCell src rs i (.inr r))
      ((ir.sumMBatches d Pk)[i]).nodes)

/-- **The masked reduction of the `i`-th circuit** (`GKR.LayeredCircuit.maskedReduction` at the input forms on the tree's
coordinates). -/
def gkrIP (i : Fin (ir.circs d).length) :
    FieldProof.MaskedReduction (I (ir.domainField d)).K (ir.FCell src Pk rs) (ir.DomainPub I)
      (ir.FCell src Pk rs → (I (ir.domainField d)).K) id (ir.FLog src Pk rs) 1 :=
  GKR.LayeredCircuit.maskedReduction (ir.circSource d src i) (ir.circNodes d src i)
    (ir.treeInputForms rs (ir.ClaimPads d src Pk) (ir.circAt d i) (src (ir.circAt d i)).d)
    (ir.gkrPadCell src rs i) (ir.treeLevel d rs (ir.ClaimPads d src Pk))

variable (ir d) in
/-- **The rows of domain `d`**: its affine rows and its rows on views. -/
abbrev RowIdx : Type := ir.Row d ⊕ ir.ViewRow d

/-- **A row of domain `d` on the tree's coordinates** at the public input `p`: an affine row on the
cells, a row on views on the cells and their bits. -/
def rowForm (p : ir.DomainPub I) :
    ir.RowIdx d → AffineForm (I (ir.domainField d)).K (ir.FLog src Pk rs)
  | .inl q => affineOn ((ir.affineRow I d q).form p.stmt p.run ∘ₗ
      ir.treeCellsLin rs (ir.ClaimPads d src Pk)) ((ir.affineRow I d q).const p.stmt p.run)
  | .inr q => affineOn ((ir.viewRow I d q).form p.stmt p.run ∘ₗ
      ir.treeViewLin rs (ir.ClaimPads d src Pk)) ((ir.viewRow I d q).const p.stmt p.run)

/-- **The rows of domain `d` as fixed claims.** -/
def rowClaims (p : ir.DomainPub I) (q : Fin (Fintype.card (ir.RowIdx d))) :
    AffineForm (I (ir.domainField d)).K (ir.FLog src Pk rs) :=
  ir.rowForm src rs p ((Encodable.fintypeEquivFin (α := ir.RowIdx d)).symm q)

/-- **The committed cell of a quadratic triple's cell key**: its root cell (the spare cell off the
root cells). -/
def quadCell (k : CellKey) : ir.FCell src Pk rs :=
  if h : k ∈ ir.cellKeys d ∧ ir.cellNode (rs.map REdge.plan) k = none then
    .inr (.inr (.cell ⟨⟨k, h.1⟩, h.2⟩))
  else ir.spareCell d Pk rs (ir.ClaimPads d src Pk)

/-- **The quadratic triples of domain `d` as Ligero's product triples** on the root cells. -/
def quadProducts : Ligero.Routing.ProductLayout (ir.FCell src Pk rs) (ir.QuadIdx d) where
  source q j :=
    match ir.quadLeaves d q.1.1 with
    | some (a, b, c) => ir.quadCell src rs (.val (![a, b, c] j) q.2)
    | none => ir.spareCell d Pk rs (ir.ClaimPads d src Pk)

variable (d Pk) in
/-- **The branches of domain `d`'s masked reduction** (`lib/gordiehowe/transcript_fork.h`, the nested
fork): the covered batches on columns, on bits, the covered merged batches on columns, on bits,
then GKR. -/
abbrev BranchIdx : Type :=
  ((Fin (ir.cbatches d Pk).length ⊕ Fin (ir.sumBatches d Pk).length) ⊕
    (Fin (ir.mbatches d Pk).length ⊕ Fin (ir.sumMBatches d Pk).length)) ⊕ Unit

variable (d Pk) in
/-- **The number of branches**: one per covered batch, then GKR. -/
abbrev nBranch : ℕ :=
  (ir.cbatches d Pk).length + (ir.sumBatches d Pk).length +
    ((ir.mbatches d Pk).length + (ir.sumMBatches d Pk).length) + 1

variable (d Pk) in
/-- **The branches in order** (`finSumFinEquiv`). -/
def branchEquiv : Fin (ir.nBranch d Pk) ≃ ir.BranchIdx d Pk :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr
    (finSumFinEquiv.symm.trans (Equiv.sumCongr finSumFinEquiv.symm finSumFinEquiv.symm))
    finOneEquiv)

variable (d Pk) in
/-- **The claims each branch leaves**: one for a batch, one per circuit for GKR. -/
def branchNc : ir.BranchIdx d Pk → ℕ
  | .inl _ => 1
  | .inr _ => ((List.finRange (ir.circs d).length).map fun _ => 1).sum

/-- **The masked reduction of branch `j`**: the batch's, or the circuits' GKR in sequence. -/
def branchIP : (j : ir.BranchIdx d Pk) →
    FieldProof.MaskedReduction (I (ir.domainField d)).K (ir.FCell src Pk rs) (ir.DomainPub I)
      (ir.FCell src Pk rs → (I (ir.domainField d)).K) id (ir.FLog src Pk rs) (ir.branchNc d Pk j)
  | .inl (.inl (.inl i)) => ir.colsIP src rs i
  | .inl (.inl (.inr i)) => ir.sumIP src rs i
  | .inl (.inr (.inl i)) => ir.mergedIP src rs i
  | .inl (.inr (.inr i)) => ir.sumMergedIP src rs i
  | .inr _ => FieldProof.MaskedReduction.ofList (ncOf := fun _ => 1) (ir.gkrIP src rs) (List.finRange _)

/-- **The relation of branch `j`**: the batch's (`BatchedZerocheck.AffineBatch.Sat`,
`BatchedZerocheck.MergedAffineBatch.Sat`), or every circuit's source satisfied on its input. -/
def branchSat : ir.BranchIdx d Pk → ir.DomainPub I →
    (ir.FCell src Pk rs → (I (ir.domainField d)).K) → Prop
  | .inl (.inl (.inl i)) =>
    (ir.colsBatchAt rs (ir.ClaimPads d src Pk) (ir.cbatches d Pk)[i]).Sat
      (ir.colsPadCell src rs i) (ir.treeLevel d rs (ir.ClaimPads d src Pk))
  | .inl (.inl (.inr i)) =>
    (ir.bitsBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumBatches d Pk)[i]).cb).Sat
      (fun q : ((ir.sumBatches d Pk)[i]).cb.Pad => ir.sumPadCell src rs i (.inl q)) (ir.treeLevel d rs (ir.ClaimPads d src Pk))
  | .inl (.inr (.inl i)) =>
    (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) (ir.mbatches d Pk)[i]).Sat
      (ir.mergedPadCell src rs i) (ir.treeLevel d rs (ir.ClaimPads d src Pk))
  | .inl (.inr (.inr i)) =>
    (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumMBatches d Pk)[i]).mb).Sat
      (fun q : ((ir.sumMBatches d Pk)[i]).mb.Pad => ir.sumMergedPadCell src rs i (.inl q)) (ir.treeLevel d rs (ir.ClaimPads d src Pk))
  | .inr _ => FieldProof.MaskedReduction.ListSat (fun i p x => (ir.circSource d src i).Satisfied
      ((ir.treeInputForms rs (ir.ClaimPads d src Pk) (ir.circAt d i) (src (ir.circAt d i)).d).input
        p ((ir.treeLevel d rs (ir.ClaimPads d src Pk)).view x))) (List.finRange _)

/-- **The round errors of branch `j`**: its batch's, or each circuit's. -/
noncomputable def branchError : (j : ir.BranchIdx d Pk) →
    (ir.branchIP src rs j).spec.ChallengeIdx → ℝ≥0
  | .inl (.inl (.inl i)) =>
    (ir.colsBatchAt rs (ir.ClaimPads d src Pk) (ir.cbatches d Pk)[i]).error
  | .inl (.inl (.inr i)) =>
    (ir.bitsBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumBatches d Pk)[i]).cb).bitError 4
  | .inl (.inr (.inl i)) => (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) (ir.mbatches d Pk)[i]).error
  | .inl (.inr (.inr i)) =>
    (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumMBatches d Pk)[i]).mb).bitError 4
  | .inr _ => FieldProof.MaskedReduction.ofListError (ncOf := fun _ => 1) (ir.gkrIP src rs)
      (fun i => (ir.circSource d src i).error (ir.circNodes d src i)) (List.finRange _)

/-- **Soundness of branch `j`** (`BatchedZerocheck.AffineBatch.sound`, `BatchedZerocheck.MergedAffineBatch.sound`,
`GKR.LayeredCircuit.maskedSound` in sequence). -/
noncomputable def branchSound : (j : ir.BranchIdx d Pk) →
    (ir.branchIP src rs j).Sound (ir.treeLevel d rs (ir.ClaimPads d src Pk)).view (ir.branchSat src rs j) (ir.branchError src rs j)
  | .inl (.inl (.inl i)) =>
    (ir.colsBatchAt rs (ir.ClaimPads d src Pk) (ir.cbatches d Pk)[i]).sound
      (ir.colsPadCell src rs i) (ir.treeLevel d rs (ir.ClaimPads d src Pk))
  | .inl (.inl (.inr i)) =>
    (ir.bitsBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumBatches d Pk)[i]).cb).bitSumcheckSound
      (fun q : ((ir.sumBatches d Pk)[i]).cb.Pad => ir.sumPadCell src rs i (.inl q)) (ir.treeLevel d rs (ir.ClaimPads d src Pk))
      (ir.bitLayoutAt src rs (fun r => ir.sumPadCell src rs i (.inr r)) ((ir.sumBatches d Pk)[i]).nodes)
  | .inl (.inr (.inl i)) =>
    (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) (ir.mbatches d Pk)[i]).sound
      (ir.mergedPadCell src rs i) (ir.treeLevel d rs (ir.ClaimPads d src Pk))
  | .inl (.inr (.inr i)) =>
    (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumMBatches d Pk)[i]).mb).bitSumcheckSound
      (fun q : ((ir.sumMBatches d Pk)[i]).mb.Pad => ir.sumMergedPadCell src rs i (.inl q)) (ir.treeLevel d rs (ir.ClaimPads d src Pk))
      (ir.bitLayoutAt src rs (fun r => ir.sumMergedPadCell src rs i (.inr r))
        ((ir.sumMBatches d Pk)[i]).nodes)
  | .inr _ => FieldProof.MaskedReduction.Sound.ofList (M := ir.gkrIP src rs) (ncOf := fun _ => 1)
      (fun i => GKR.LayeredCircuit.maskedSound (ir.circSource d src i) (ir.circNodes d src i)
        (ir.treeInputForms rs (ir.ClaimPads d src Pk) (ir.circAt d i) (src (ir.circAt d i)).d)
        (ir.gkrPadCell src rs i) (ir.treeLevel d rs (ir.ClaimPads d src Pk))) (List.finRange _)

/-- **The claim count of domain `d`'s masked reduction**: the branches', then the rows. -/
abbrev claimCount : ℕ :=
  ((List.finRange (ir.nBranch d Pk)).map fun b => ir.branchNc d Pk (ir.branchEquiv d Pk b)).sum +
    Fintype.card (ir.RowIdx d)

/-- **The masked reduction of domain `d`** (see the module docstring): the branches in order
(`branchEquiv`), then the rows and the quadratic triples. -/
def fieldMaskedReduction :
    FieldProof.MaskedReduction (I (ir.domainField d)).K (ir.FCell src Pk rs) (ir.DomainPub I)
      (ir.FCell src Pk rs → (I (ir.domainField d)).K) id (ir.FLog src Pk rs)
      (ir.claimCount (d := d) (Pk := Pk)) :=
  (FieldProof.MaskedReduction.ofList (ncOf := fun b => ir.branchNc d Pk (ir.branchEquiv d Pk b))
    (fun b => ir.branchIP src rs (ir.branchEquiv d Pk b)) (List.finRange _)).append
    (FieldProof.MaskedReduction.staticProducts (ir.rowClaims src rs) (ir.quadProducts src rs))

/-- **The relation domain `d`'s masked reduction proves** on the committed cells: every covered batch's
(`BatchedZerocheck.AffineBatch.Sat`), every circuit's source satisfied on its input, every row. -/
structure FieldSat (p : ir.DomainPub I) (x : ir.FCell src Pk rs → (I (ir.domainField d)).K) :
    Prop where
  /-- Every covered batch on columns. -/
  cols : ∀ i, (ir.colsBatchAt rs (ir.ClaimPads d src Pk) (ir.cbatches d Pk)[i]).Sat
    (ir.colsPadCell src rs i) (ir.treeLevel d rs (ir.ClaimPads d src Pk)) p x
  /-- Every covered batch on bits. -/
  sumBits : ∀ i, (ir.bitsBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumBatches d Pk)[i]).cb).Sat
    (fun q : ((ir.sumBatches d Pk)[i]).cb.Pad => ir.sumPadCell src rs i (.inl q)) (ir.treeLevel d rs (ir.ClaimPads d src Pk)) p x
  /-- Every covered merged batch on columns. -/
  merged : ∀ i, (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) (ir.mbatches d Pk)[i]).Sat
    (ir.mergedPadCell src rs i) (ir.treeLevel d rs (ir.ClaimPads d src Pk)) p x
  /-- Every covered merged batch on bits. -/
  sumMerged : ∀ i, (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumMBatches d Pk)[i]).mb).Sat
    (fun q : ((ir.sumMBatches d Pk)[i]).mb.Pad => ir.sumMergedPadCell src rs i (.inl q)) (ir.treeLevel d rs (ir.ClaimPads d src Pk)) p x
  /-- Every circuit's source is satisfied on its input. -/
  gkr : ∀ i, (ir.circSource d src i).Satisfied
    ((ir.treeInputForms rs (ir.ClaimPads d src Pk) (ir.circAt d i) (src (ir.circAt d i)).d).input p
      ((ir.treeLevel d rs (ir.ClaimPads d src Pk)).view x))
  /-- Every row. -/
  rows : ∀ q, (ir.rowClaims src rs p q).eval ((ir.treeLevel d rs (ir.ClaimPads d src Pk)).view x) = 0
  /-- Every quadratic triple. -/
  quads : Ligero.Routing.SourceProducts (ir.quadProducts src rs) x

/-- **Every branch's relation** is `FieldSat`'s batches and circuits. -/
theorem forall_branchSat_iff (p : ir.DomainPub I) (x : ir.FCell src Pk rs → (I (ir.domainField d)).K) :
    (∀ b, ir.branchSat src rs (ir.branchEquiv d Pk b) p x) ↔
      ((∀ i, (ir.colsBatchAt rs (ir.ClaimPads d src Pk) (ir.cbatches d Pk)[i]).Sat
        (ir.colsPadCell src rs i) (ir.treeLevel d rs (ir.ClaimPads d src Pk)) p x) ∧
      (∀ i, (ir.bitsBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumBatches d Pk)[i]).cb).Sat
        (fun q : ((ir.sumBatches d Pk)[i]).cb.Pad => ir.sumPadCell src rs i (.inl q)) (ir.treeLevel d rs (ir.ClaimPads d src Pk)) p x) ∧
      (∀ i, (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) (ir.mbatches d Pk)[i]).Sat
        (ir.mergedPadCell src rs i) (ir.treeLevel d rs (ir.ClaimPads d src Pk)) p x) ∧
      (∀ i, (ir.mergedBatchAt rs (ir.ClaimPads d src Pk) ((ir.sumMBatches d Pk)[i]).mb).Sat
        (fun q : ((ir.sumMBatches d Pk)[i]).mb.Pad => ir.sumMergedPadCell src rs i (.inl q)) (ir.treeLevel d rs (ir.ClaimPads d src Pk))
          p x)) ∧
      ∀ i, (ir.circSource d src i).Satisfied
        ((ir.treeInputForms rs (ir.ClaimPads d src Pk) (ir.circAt d i) (src (ir.circAt d i)).d).input p
          ((ir.treeLevel d rs (ir.ClaimPads d src Pk)).view x)) := by
  have he : (∀ b, ir.branchSat src rs (ir.branchEquiv d Pk b) p x) ↔
      ∀ j, ir.branchSat src rs j p x := by
    refine ⟨fun h j => ?_, fun h b => h _⟩
    have := h ((ir.branchEquiv d Pk).symm j)
    rwa [Equiv.apply_symm_apply] at this
  rw [he, Sum.forall, Sum.forall, Sum.forall, Sum.forall]
  simp only [branchSat, FieldProof.MaskedReduction.listSat_iff, List.mem_finRange, true_implies]
  constructor
  · rintro ⟨⟨⟨hc, hsb⟩, hm, hsm⟩, hg⟩
    exact ⟨⟨hc, hsb, hm, hsm⟩, hg ()⟩
  · rintro ⟨⟨hc, hsb, hm, hsm⟩, hg⟩
    exact ⟨⟨⟨hc, hsb⟩, hm, hsm⟩, fun _ => hg⟩

/-- **The round errors of domain `d`'s masked reduction**: each branch's, none for the rows. -/
noncomputable def fieldClaimError : (ir.fieldMaskedReduction src rs).spec.ChallengeIdx → ℝ≥0 :=
  ProtocolSpec.appendError
    (FieldProof.MaskedReduction.ofListError (ncOf := fun b => ir.branchNc d Pk (ir.branchEquiv d Pk b))
      (fun b => ir.branchIP src rs (ir.branchEquiv d Pk b))
      (fun b => ir.branchError src rs (ir.branchEquiv d Pk b)) (List.finRange _))
    fun i => i.1.elim0

/-- **Soundness of domain `d`'s masked reduction** for `FieldSat` with `fieldClaimError`: the branches'
(`branchSound`) and the rows' (`MaskedReduction.Sound.staticProducts`) in sequence. -/
noncomputable def fieldClaimSound :
    (ir.fieldMaskedReduction src rs).Sound (ir.treeLevel d rs (ir.ClaimPads d src Pk)).view (ir.FieldSat src rs) (ir.fieldClaimError src rs) :=
  ((FieldProof.MaskedReduction.Sound.ofList (M := fun b => ir.branchIP src rs (ir.branchEquiv d Pk b))
      (ncOf := fun b => ir.branchNc d Pk (ir.branchEquiv d Pk b))
      (fun b => ir.branchSound src rs (ir.branchEquiv d Pk b)) (List.finRange _)).append
    (FieldProof.MaskedReduction.Sound.staticProducts (sat := fun p x => (∀ q, (ir.rowClaims src rs p q).eval
        ((ir.treeLevel d rs (ir.ClaimPads d src Pk)).view x) = 0) ∧ Ligero.Routing.SourceProducts (ir.quadProducts src rs) x)
      fun _ _ => Iff.rfl)).congr
    fun p x => by
      rw [FieldProof.MaskedReduction.listSat_iff]
      simp only [List.mem_finRange, true_implies]
      rw [forall_branchSat_iff]
      exact ⟨fun h => ⟨h.1.1.1, h.1.1.2.1, h.1.1.2.2.1, h.1.1.2.2.2, h.1.2, h.2.1, h.2.2⟩,
        fun h => ⟨⟨⟨h.cols, h.sumBits, h.merged, h.sumMerged⟩, h.gkr⟩, h.rows, h.quads⟩⟩

/-- **The phase error of a covered batch** (`BatchedZerocheck.AffineBatch.error_sum`): `n/|K|`,
`D(w − 1)/|K|`, `(D + 1)n/|K|` and `1/|K|` at its rounds `n`, width `w` and degree `D`. -/
noncomputable def cbError {om : OperandMap} (cb : ir.CBatch I d om) : ℝ≥0 :=
  ((ir.batch cb.idx).rounds : ℝ≥0) / Fintype.card (I (ir.domainField d)).K +
    (((ir.batch cb.idx).degree * ((ir.batch cb.idx).width - 1) : ℕ) : ℝ≥0) /
      Fintype.card (I (ir.domainField d)).K +
      (((ir.batch cb.idx).degree + 1 : ℕ) : ℝ≥0) * (ir.batch cb.idx).rounds /
        Fintype.card (I (ir.domainField d)).K +
        1 / Fintype.card (I (ir.domainField d)).K

/-- A sum over the positions of a list is the sum over its entries. -/
theorem sum_map_finRange_getElem {α : Type} (l : List α) (f : α → ℝ≥0) :
    ((List.finRange l.length).map fun i => f l[i]).sum = (l.map f).sum := by
  congr 1
  exact List.ext_getElem (by simp) fun n h1 h2 => by simp

/-- **The phase error of a covered merged batch** (`BatchedZerocheck.MergedAffineBatch.error_sum`):
`(np − 1)/|K|` at the merging challenge, then the batch phase's. -/
noncomputable def mbError (cb : ir.MBatch I d) : ℝ≥0 :=
  (((ir.batch cb.idx).parts.length - 1 : ℕ) : ℝ≥0) / Fintype.card (I (ir.domainField d)).K +
    (((ir.batch cb.idx).rounds : ℝ≥0) / Fintype.card (I (ir.domainField d)).K +
      (((ir.batch cb.idx).degree * ((ir.batch cb.idx).width - 1) : ℕ) : ℝ≥0) /
        Fintype.card (I (ir.domainField d)).K +
      (((ir.batch cb.idx).degree + 1 : ℕ) : ℝ≥0) * (ir.batch cb.idx).rounds /
        Fintype.card (I (ir.domainField d)).K +
      1 / Fintype.card (I (ir.domainField d)).K)

/-- **The phase error of a covered batch on bits**
(`BatchedZerocheck.AffineBatch.bitError_sum`): the batch's, and `2/|K|` for each of the `4` bit
rounds. -/
noncomputable def sbError (sb : ir.SCBatch I d) : ℝ≥0 :=
  cbError sb.cb + ((2 * 4 : ℕ) : ℝ≥0) / Fintype.card (I (ir.domainField d)).K

/-- **The phase error of a covered merged batch on bits**
(`BatchedZerocheck.MergedAffineBatch.bitError_sum`): the merged batch's, and `2/|K|` for each of
the `4` bit rounds. -/
noncomputable def smbError (sb : ir.SMBatch I d) : ℝ≥0 :=
  mbError sb.mb + ((2 * 4 : ℕ) : ℝ≥0) / Fintype.card (I (ir.domainField d)).K

variable (d Pk) in
/-- **The covered batches' phase errors of domain `d`**, summed: `cbError` of every covered batch
on columns, `sbError` of every covered batch on bits, `mbError` of every covered merged batch on
columns and `smbError` of every covered merged batch on bits. -/
noncomputable def batchesError : ℝ≥0 :=
  ((ir.cbatches d Pk).map cbError).sum + ((ir.sumBatches d Pk).map sbError).sum +
    ((ir.mbatches d Pk).map mbError).sum + ((ir.sumMBatches d Pk).map smbError).sum

variable (ir d) in
/-- **The GKR width of domain `d`**: the largest width bound (`circuitWidth`) of its circuits, `0`
when it has none. -/
def gkrWidth : ℕ := (ir.circs d).foldr (fun (c : Fin ir.circuits.length) m => max (ir.circuitWidth c) m) 0

/-- Every circuit of domain `d` has width bound at most `gkrWidth d`. -/
theorem circuitWidth_le_gkrWidth (i : Fin (ir.circs d).length) :
    ir.circuitWidth (ir.circAt d i) ≤ ir.gkrWidth d := by
  have hm : ir.circAt d i ∈ ir.circs d := List.getElem_mem _
  unfold gkrWidth
  generalize ir.circs d = l at hm
  induction l with
  | nil => simp at hm
  | cons a l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.1 hm with h | h
    · rw [← h]
      exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

variable (I d) in
/-- **The charge of a GKR round of domain `d`**: `max 3 (2 · gkrWidth d)/|K|`. It bounds the
initial point's `2 m_0/|K|`, as `m_0 ≤ circuitWidth` for every circuit under the compiler trust's
shape, and every later GKR challenge's `3/|K|` (`GordieHowe.GKR.LayeredCircuit.ShapeAtMost.error_le`). -/
noncomputable def gkrRoundError : ℝ≥0 :=
  ((max 3 (2 * ir.gkrWidth d) : ℕ) : ℝ≥0) / Fintype.card (I (ir.domainField d)).K

/-- **Every round of GKR's branch is at most `gkrRoundError`** under the compiler trust's shapes
(`CircuitsEnforce.shape`): each circuit's rounds (`GordieHowe.GKR.LayeredCircuit.ShapeAtMost.error_le`)
in sequence (`MaskedReduction.ofListError_le`). -/
theorem gkrBranchError_le (T : ir.CircuitsEnforce I src) (u : Unit) (k) :
    ir.branchError src rs (.inr u) k ≤ ir.gkrRoundError I d :=
  FieldProof.MaskedReduction.ofListError_le (fun i j => by
    have hw : max 3 (2 * ir.circuitWidth (ir.circAt d i)) ≤ max 3 (2 * ir.gkrWidth d) :=
      max_le_max le_rfl (Nat.mul_le_mul_left 2 (ir.circuitWidth_le_gkrWidth i))
    exact (((shapeAtMost_circSource src i).2 (T.shape _)).error_le (ir.circNodes d src i) j).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast hw) (by positivity))) _ k

/-- **Every round of branch `j` is at most `δ`** when the covered batches' phase errors together are
(`batchesError`) and a GKR round's charge is (`gkrRoundError`): a batch branch's round within its
batch's summed phase error (`AffineBatch.error_sum`, `MergedAffineBatch.error_sum`), a round of GKR's
branch within `gkrRoundError` (`gkrBranchError_le`). -/
theorem branchError_le (T : ir.CircuitsEnforce I src) {δ : ℝ≥0} (hb : ir.batchesError d Pk ≤ δ)
    (hg : ir.gkrRoundError I d ≤ δ) (j : ir.BranchIdx d Pk) (k) : ir.branchError src rs j k ≤ δ := by
  have entry : ∀ {α : Type} (l : List α) (f : α → ℝ≥0) (i : Fin l.length),
      f l[i] ≤ (l.map f).sum := fun l f i =>
    List.le_sum_of_mem (List.mem_map.mpr ⟨l[i], List.getElem_mem _, rfl⟩)
  have single : ir.branchError src rs j k ≤ ∑ i, ir.branchError src rs j i :=
    Finset.single_le_sum (f := ir.branchError src rs j) (fun _ _ => zero_le) (Finset.mem_univ k)
  unfold batchesError at hb
  rcases j with ((i | i) | i | i) | u
  · have e : ∑ k, ir.branchError src rs (.inl (.inl (.inl i))) k =
        cbError (ir.cbatches d Pk)[i] := AffineBatch.error_sum _
    rw [e] at single
    exact single.trans ((entry _ _ i).trans ((le_self_add.trans (le_self_add.trans
      le_self_add)).trans hb))
  · have e : ∑ k, ir.branchError src rs (.inl (.inl (.inr i))) k =
        sbError (ir.sumBatches d Pk)[i] := AffineBatch.bitError_sum _
    rw [e] at single
    exact single.trans ((entry _ _ i).trans ((le_add_self.trans (le_self_add.trans
      le_self_add)).trans hb))
  · have e : ∑ k, ir.branchError src rs (.inl (.inr (.inl i))) k = mbError (ir.mbatches d Pk)[i] :=
      MergedAffineBatch.error_sum _
    rw [e] at single
    exact single.trans ((entry _ _ i).trans ((le_add_self.trans le_self_add).trans hb))
  · have e : ∑ k, ir.branchError src rs (.inl (.inr (.inr i))) k =
        smbError (ir.sumMBatches d Pk)[i] := MergedAffineBatch.bitError_sum _
    rw [e] at single
    exact single.trans ((entry _ _ i).trans (le_add_self.trans hb))
  · exact (ir.gkrBranchError_le src rs T u k).trans hg

end Claim

/-! ## From the masked reduction's relation to the domain's predicate -/

section Bridge

/-- **A covered batch on columns on the tree's coordinates holds exactly when the batched
relation holds on the cells** of the coordinates. -/
theorem colsBatchAt_holds_iff (cb : ir.CBatch I d .columns) (p : ir.DomainPub I)
    (z : ir.TLog d rs Pads → (I (ir.domainField d)).K) :
    (ir.colsBatchAt rs Pads cb).Holds p z ↔
      (ir.batchRelation I d cb.idx).Holds p.stmt (ir.treeCells rs Pads z) := by
  unfold AffineBatch.Holds BatchRelation.Holds
  constructor
  · intro h i
    obtain ⟨t, rfl⟩ := finSigmaFinEquiv.symm.surjective i
    have := h t
    simp only [colsBatchAt, Shape.eval_rel, eval_affineOn, LinearMap.comp_apply] at this
    exact this
  · intro h t
    simp only [colsBatchAt, Shape.eval_rel, eval_affineOn, LinearMap.comp_apply]
    exact h _

/-- **Relation `q` of a covered merged batch at instance `t`** is part `q`'s shape on its operands
at coordinate `t`, for any reading `val` of the operands that reads the constant zero as `0` and
whose sum over the parts is the batch's operand (`hform`): every other part reads a constant zero in
part `q`'s slice (`sum_instOperand_slice`). -/
theorem mergedBatchAt_rel_eval (cb : ir.MBatch I d) (p : ir.DomainPub I)
    (z : ir.TLog d rs Pads → (I (ir.domainField d)).K) (val : BOperand → (I (ir.domainField d)).K)
    (hval : val .zero = 0) (q : Fin (ir.batch cb.idx).parts.length) (t : Fin (ir.partLen d cb.idx 0))
    (hform : ∀ o : Fin (ir.mergedBatchAt rs Pads cb).k,
      ((ir.mergedBatchAt rs Pads cb).form p t o).eval z =
        ∑ p' : Fin (ir.batch cb.idx).parts.length, val (ir.instOperand (atomAt ir d cb.om) d cb.idx p' o)) :
    ((ir.mergedBatchAt rs Pads cb).rels q).eval
        (fun o => ((ir.mergedBatchAt rs Pads cb).form p t o).eval z) =
      (ir.partShape (atomAt ir d cb.om) d cb.idx q).evalAt (fun o =>
        val ((ir.partOperands (atomAt ir d cb.om) d cb.idx q).getD o default)) := by
  have hb := cb.partsOk
  have hok := hb.sliceShape_ok cb.merged q.2
  have hlt : ∀ o < (ir.partShape (atomAt ir d cb.om) d cb.idx q).k,
      o + ir.partOffset (atomAt ir d cb.om) d cb.idx q <
        (ir.relShape (atomAt ir d cb.om) d cb.idx).k := fun o ho => by
    have h2 := partOffset_mono (atom := atomAt ir d cb.om) (d := d) cb.merged (Nat.succ_le_of_lt q.2)
    rw [partOffset_succ cb.merged] at h2
    rw [relShape_k_of_merged cb.merged]
    omega
  refine (Shape.eval_rel _ hok _).trans ?_
  unfold Shape.evalFin
  rw [sliceShape_evalAt]
  refine monosEval_congr fun m hm o ho => ?_
  have hko := (hb.ok q q.2).lt m hm o ho
  rw [dif_pos (show o + ir.partOffset (atomAt ir d cb.om) d cb.idx q <
    (ir.sliceShape (atomAt ir d cb.om) d cb.idx q).k from hlt o hko)]
  refine (hform _).trans ?_
  exact sum_instOperand_slice cb.merged (fun _ op => val op) (fun _ => hval) q hko

/-- **An operand of a covered merged batch on columns** is the parts' operands summed at the cells
of the coordinates (`isAff_mergedOpAt`). -/
theorem mergedBatchAt_form_eval (cb : ir.MBatch I d) (hom : cb.om = .columns) (p : ir.DomainPub I)
    (t : Fin (ir.mergedBatchAt rs Pads cb).N) (o : Fin (ir.mergedBatchAt rs Pads cb).k)
    (z : ir.TLog d rs Pads → (I (ir.domainField d)).K) :
    ((ir.mergedBatchAt rs Pads cb).form p t o).eval z =
      ∑ p' : Fin (ir.batch cb.idx).parts.length, ir.opValAt I d
        (ir.cellReader I d (ir.treeCells rs Pads z)) (ir.instOperand (atomAt ir d cb.om) d cb.idx p' o) t := by
  have hb := partsOk_of_cols (cb.colsOkB hom)
  obtain ⟨idx, ok, om, hops, hm, dom⟩ := cb
  dsimp only at hom
  subst hom
  simp only [mergedBatchAt, mergedForm, eval_affineOn, LinearMap.comp_apply]
  exact gradLin_apply (isAff_mergedOpAt hb o t) _

/-- **A covered merged batch on columns on the tree's coordinates holds exactly when the batched
relation holds on the cells** of the coordinates (`mergedBatchAt_rel_eval`, `batchRelation_Q`). -/
theorem mergedBatchAt_holds_iff (cb : ir.MBatch I d) (hom : cb.om = .columns) (p : ir.DomainPub I)
    (z : ir.TLog d rs Pads → (I (ir.domainField d)).K) :
    (ir.mergedBatchAt rs Pads cb).Holds p z ↔
      (ir.batchRelation I d cb.idx).Holds p.stmt (ir.treeCells rs Pads z) := by
  have hb := partsOk_of_cols (cb.colsOkB hom)
  have hat : atomAt ir d cb.om = ir.atomB := by rw [hom]
  have hlen : ∀ q : Fin (ir.batch cb.idx).parts.length, ir.partLen d cb.idx q = ir.partLen d cb.idx 0 :=
    fun q => cb.partsOk.lens cb.merged q q.2
  have hrel : ∀ q t, ((ir.mergedBatchAt rs Pads cb).rels q).eval
      (fun o => ((ir.mergedBatchAt rs Pads cb).form p t o).eval z) =
        (ir.partShape ir.atomB d cb.idx q).evalAt (fun o =>
          ir.opValAt I d (ir.cellReader I d (ir.treeCells rs Pads z))
            ((ir.partOperands ir.atomB d cb.idx q).getD o default) t) := fun q t => by
    refine (ir.mergedBatchAt_rel_eval rs Pads cb p z
      (fun op => ir.opValAt I d (ir.cellReader I d (ir.treeCells rs Pads z)) op t) rfl q t
      fun o => ir.mergedBatchAt_form_eval rs Pads cb hom p t o z).trans ?_
    rw [hat]
  unfold MergedAffineBatch.Holds BatchRelation.Holds
  constructor
  · rintro h ⟨q, i⟩
    rw [batchRelation_Q hb q p.stmt _ i]
    exact (hrel q _).symm.trans (h q (Fin.cast (hlen q) i))
  · intro h q t
    have := h ⟨q, Fin.cast (hlen q).symm t⟩
    rw [batchRelation_Q hb q p.stmt _ _] at this
    exact (hrel q t).trans this

/-- **The bit operands' valuation read from the logical assignment of the committed cells reads as
at the decoded cells**, at every value a bit operand may read (`wordBit_treeBits` at a bit view). -/
theorem bitsReader_treeLift (ht : TreeOk (rs.map REdge.plan) Pk.n)
    (hp : ir.PlaceOk d Pk (rs.map REdge.plan)) (hr : ir.RealizedOk d rs)
    (hv : ir.ViewsOk d (rs.map REdge.plan)) (x : ir.TreeCell d Pk rs Pads → (I (ir.domainField d)).K)
    (stmt : ir.Valuation I) {v : ℕ} (hl : ir.bitsLeafOk d v = true) :
    ir.bitsReader I d (ir.treeLift rs Pads stmt ((ir.treeLevel d rs Pads).view x)) v =
      ir.bitsReader I d (ir.bitsLift I d stmt (ir.treeDecode d rs Pads x)) v := by
  funext i
  unfold bitsReader bitValuation
  split
  · rename_i w sel hk
    have hb : ir.bitViewOk d v = true := by
      unfold bitsLeafOk at hl
      rw [hk] at hl
      exact hl
    obtain ⟨-, -, -, hud, -⟩ := bitViewOk_spec hb
    exact congrArg castElt (wordBit_treeBits ht hp hr x (hv v w sel hk hud) _ _)
  · rfl

/-- **An operand of a covered batch on bits at the logical assignment of committed cells** is the
batched relation's operand at the decoded cells plus its offset (`gradLin_apply`,
`bitsReader_treeLift`). -/
theorem bitsBatchAt_form_eval (ht : TreeOk (rs.map REdge.plan) Pk.n)
    (hp : ir.PlaceOk d Pk (rs.map REdge.plan)) (hr : ir.RealizedOk d rs)
    (hv : ir.ViewsOk d (rs.map REdge.plan)) (cb : ir.CBatch I d .bits)
    (hb : ir.bitsBatchOkB d cb.idx = true) (p : ir.DomainPub I)
    (x : ir.TreeCell d Pk rs Pads → (I (ir.domainField d)).K) (t : Fin (ir.bitsBatchAt rs Pads cb).N)
    (o : Fin (ir.relShape (ir.bitsAtomB d) d cb.idx).k) :
    ((ir.bitsBatchAt rs Pads cb).form p t o).eval ((ir.treeLevel d rs Pads).view x) =
      (ir.bitsBatchRelation I d cb.idx hb Pk.bitsAdditive).operand
          (finSigmaFinEquiv.symm t) o (ir.treeDecode d rs Pads x) +
        (ir.bitsBatchRelation I d cb.idx hb Pk.bitsAdditive).offset p.stmt
          (finSigmaFinEquiv.symm t) o := by
  have hok := partsOk_of_bits hb
  rw [bitsBatchRelation_operand]
  change (affineOn _ _).eval _ = _
  rw [eval_affineOn, gradLin_apply (IsAff.treeLift rs Pads (isAff_bitsOperandAt (I := I) hok _ o)
    p.stmt)]
  obtain ⟨e, e', pf, -, hpf, hsh, hops⟩ := hok.exists_part (finSigmaFinEquiv.symm t).1
  have hk : (ir.partShape (ir.bitsAtomB d) d cb.idx (finSigmaFinEquiv.symm t).1).k =
      pf.operands.length := by rw [hsh]; rfl
  have hatE : ∀ e, ir.bitsAtomB d e = true →
      ir.evalWith (ir.bitsReader I d (ir.treeLift rs Pads p.stmt
        ((ir.treeLevel d rs Pads).view x))) d e =
        ir.evalWith (ir.bitsReader I d (ir.bitsLift I d p.stmt (ir.treeDecode d rs Pads x))) d e :=
    fun e he => by
      simp only [bitsAtomB, Bool.and_eq_true, List.all_eq_true] at he
      exact evalE_congr fun v hv' => ir.bitsReader_treeLift rs Pads ht hp hr hv x p.stmt (he.1.1 v hv')
  unfold bitsOperandAt
  rcases instOperand_atoms hpf hops hk o with ⟨a, ha, hat⟩ | ⟨ts, hts, hat⟩ | hz
  · rw [ha]
    simp only [opValAt, BOperand.val, hatE a hat]
  · rw [hts]
    simp only [opValAt, BOperand.val]
    exact sum_map_congr fun t ht => by rw [hatE t.2 (hat t ht)]
  · rw [hz]
    rfl

/-- **A covered batch on bits on the tree's coordinates holds exactly when the batched relation on
bits holds on the decoded cells**, at the logical assignment of any committed cells. -/
theorem bitsBatchAt_holds_iff (ht : TreeOk (rs.map REdge.plan) Pk.n)
    (hp : ir.PlaceOk d Pk (rs.map REdge.plan)) (hr : ir.RealizedOk d rs)
    (hv : ir.ViewsOk d (rs.map REdge.plan)) (cb : ir.CBatch I d .bits)
    (hb : ir.bitsBatchOkB d cb.idx = true) (p : ir.DomainPub I)
    (x : ir.TreeCell d Pk rs Pads → (I (ir.domainField d)).K) :
    (ir.bitsBatchAt rs Pads cb).Holds p ((ir.treeLevel d rs Pads).view x) ↔
      (ir.bitsBatchRelation I d cb.idx hb Pk.bitsAdditive).Holds p.stmt
        (ir.treeDecode d rs Pads x) := by
  have hok := partsOk_of_bits hb
  have hop : ∀ t (o : Fin (ir.relShape (ir.bitsAtomB d) d cb.idx).k),
      ((ir.bitsBatchAt rs Pads cb).form p t o).eval ((ir.treeLevel d rs Pads).view x) =
        (ir.bitsBatchRelation I d cb.idx hb Pk.bitsAdditive).operand
            (finSigmaFinEquiv.symm t) o (ir.treeDecode d rs Pads x) +
          (ir.bitsBatchRelation I d cb.idx hb Pk.bitsAdditive).offset p.stmt
            (finSigmaFinEquiv.symm t) o :=
    fun t o => ir.bitsBatchAt_form_eval rs Pads ht hp hr hv cb hb p x t o
  have hrel : ∀ y, (ir.bitsBatchAt rs Pads cb).rel.eval y =
      (ir.bitsBatchRelation I d cb.idx hb Pk.bitsAdditive).Q y :=
    fun y => Shape.eval_rel _ hok.relShape_ok y
  unfold AffineBatch.Holds BatchRelation.Holds
  constructor
  · intro h i
    obtain ⟨t, rfl⟩ := finSigmaFinEquiv.symm.surjective i
    exact (hrel _).symm.trans
      ((congrArg (ir.bitsBatchAt rs Pads cb).rel.eval (funext (hop t))).symm.trans (h t))
  · intro h t
    exact (congrArg (ir.bitsBatchAt rs Pads cb).rel.eval (funext (hop t))).trans ((hrel _).trans (h _))

/-- **An operand of a batch on bits at the logical assignment of committed cells reads as at the
decoded cells**: every operand of an instance reads atoms only (`instOperand_atoms`), each read
alike (`bitsReader_treeLift`). -/
theorem opValAt_instOperand_treeLift (ht : TreeOk (rs.map REdge.plan) Pk.n)
    (hp : ir.PlaceOk d Pk (rs.map REdge.plan)) (hr : ir.RealizedOk d rs)
    (hv : ir.ViewsOk d (rs.map REdge.plan)) {b : ℕ} (hb : ir.PartsOk (ir.bitsAtomB d) d b)
    (j : Fin (ir.batch b).parts.length) (o t : ℕ) (stmt : ir.Valuation I)
    (x : ir.TreeCell d Pk rs Pads → (I (ir.domainField d)).K) :
    ir.opValAt I d (ir.bitsReader I d (ir.treeLift rs Pads stmt ((ir.treeLevel d rs Pads).view x)))
        (ir.instOperand (ir.bitsAtomB d) d b j o) t =
      ir.opValAt I d (ir.bitsReader I d (ir.bitsLift I d stmt (ir.treeDecode d rs Pads x)))
        (ir.instOperand (ir.bitsAtomB d) d b j o) t := by
  obtain ⟨e, e', pf, -, hpf, hsh, hops⟩ := hb.exists_part j
  have hk : (ir.partShape (ir.bitsAtomB d) d b j).k = pf.operands.length := by rw [hsh]; rfl
  have hatE : ∀ e, ir.bitsAtomB d e = true →
      ir.evalWith (ir.bitsReader I d (ir.treeLift rs Pads stmt ((ir.treeLevel d rs Pads).view x))) d e =
        ir.evalWith (ir.bitsReader I d (ir.bitsLift I d stmt (ir.treeDecode d rs Pads x))) d e :=
    fun e he => by
      simp only [bitsAtomB, Bool.and_eq_true, List.all_eq_true] at he
      exact evalE_congr fun v hv' => ir.bitsReader_treeLift rs Pads ht hp hr hv x stmt (he.1.1 v hv')
  rcases instOperand_atoms hpf hops hk o with ⟨a, ha, hat⟩ | ⟨ts, hts, hat⟩ | hz
  · rw [ha]
    simp only [opValAt, BOperand.val, hatE a hat]
  · rw [hts]
    simp only [opValAt, BOperand.val]
    exact sum_map_congr fun u hu => by rw [hatE u.2 (hat u hu)]
  · rw [hz]
    rfl

/-- **An operand of a covered merged batch on bits at the logical assignment of committed cells** is
the parts' operands summed at the variables of the decoded cells (`isAff_mergedBitsOpAt`,
`opValAt_instOperand_treeLift`). -/
theorem mergedBatchAt_form_eval_bits (ht : TreeOk (rs.map REdge.plan) Pk.n)
    (hp : ir.PlaceOk d Pk (rs.map REdge.plan)) (hr : ir.RealizedOk d rs)
    (hv : ir.ViewsOk d (rs.map REdge.plan)) (cb : ir.MBatch I d) (hom : cb.om = .bits)
    (p : ir.DomainPub I) (x : ir.TreeCell d Pk rs Pads → (I (ir.domainField d)).K)
    (t : Fin (ir.mergedBatchAt rs Pads cb).N) (o : Fin (ir.mergedBatchAt rs Pads cb).k) :
    ((ir.mergedBatchAt rs Pads cb).form p t o).eval ((ir.treeLevel d rs Pads).view x) =
      ∑ p' : Fin (ir.batch cb.idx).parts.length, ir.opValAt I d
        (ir.bitsReader I d (ir.bitsLift I d p.stmt (ir.treeDecode d rs Pads x)))
        (ir.instOperand (atomAt ir d cb.om) d cb.idx p' o) t := by
  have hb := partsOk_of_bits (cb.bitsOkB hom)
  obtain ⟨idx, ok, om, hops, hm, dom⟩ := cb
  dsimp only at hom
  subst hom
  simp only [mergedBatchAt, mergedForm, eval_affineOn]
  rw [gradLin_apply (IsAff.treeLift rs Pads (isAff_mergedBitsOpAt hb o t) p.stmt)]
  unfold mergedBitsOpAt
  exact Finset.sum_congr rfl fun p' _ =>
    ir.opValAt_instOperand_treeLift rs Pads ht hp hr hv hb p' o t p.stmt x

/-- **A covered merged batch on bits on the tree's coordinates holds exactly when the batched
relation on bits holds on the decoded cells**, at the logical assignment of any committed cells
(`mergedBatchAt_rel_eval`, `bitsBatchRelation_Q`). -/
theorem mergedBatchAt_holds_iff_bits (ht : TreeOk (rs.map REdge.plan) Pk.n)
    (hp : ir.PlaceOk d Pk (rs.map REdge.plan)) (hr : ir.RealizedOk d rs)
    (hv : ir.ViewsOk d (rs.map REdge.plan)) (cb : ir.MBatch I d) (hom : cb.om = .bits)
    (p : ir.DomainPub I) (x : ir.TreeCell d Pk rs Pads → (I (ir.domainField d)).K) :
    (ir.mergedBatchAt rs Pads cb).Holds p ((ir.treeLevel d rs Pads).view x) ↔
      (ir.bitsBatchRelation I d cb.idx (cb.bitsOkB hom) Pk.bitsAdditive).Holds p.stmt
        (ir.treeDecode d rs Pads x) := by
  have hat : atomAt ir d cb.om = ir.bitsAtomB d := by rw [hom]
  have hlen : ∀ q : Fin (ir.batch cb.idx).parts.length, ir.partLen d cb.idx q = ir.partLen d cb.idx 0 :=
    fun q => cb.partsOk.lens cb.merged q q.2
  have hrel : ∀ q t, ((ir.mergedBatchAt rs Pads cb).rels q).eval
      (fun o => ((ir.mergedBatchAt rs Pads cb).form p t o).eval ((ir.treeLevel d rs Pads).view x)) =
        (ir.partShape (ir.bitsAtomB d) d cb.idx q).evalAt (fun o =>
          ir.opValAt I d (ir.bitsReader I d (ir.bitsLift I d p.stmt (ir.treeDecode d rs Pads x)))
            ((ir.partOperands (ir.bitsAtomB d) d cb.idx q).getD o default) t) := fun q t => by
    refine (ir.mergedBatchAt_rel_eval rs Pads cb p _
      (fun op => ir.opValAt I d (ir.bitsReader I d (ir.bitsLift I d p.stmt
        (ir.treeDecode d rs Pads x))) op t) rfl q t
      fun o => ir.mergedBatchAt_form_eval_bits rs Pads ht hp hr hv cb hom p x t o).trans ?_
    rw [hat]
  unfold MergedAffineBatch.Holds BatchRelation.Holds
  constructor
  · rintro h ⟨q, i⟩
    rw [bitsBatchRelation_Q (cb.bitsOkB hom) Pk.bitsAdditive q p.stmt _ i]
    exact (hrel q _).symm.trans (h q (Fin.cast (hlen q) i))
  · intro h q t
    have := h ⟨q, Fin.cast (hlen q).symm t⟩
    rw [bitsBatchRelation_Q (cb.bitsOkB hom) Pk.bitsAdditive q p.stmt _ _] at this
    exact (hrel q t).trans this

/-- **The views read from the logical assignment of the committed cells read as at the decoded
cells and their bits**, at every value a row on views may read (`wordBit_treeBits` at a bit
view). -/
theorem viewValuation_treeBits (ht : TreeOk (rs.map REdge.plan) Pk.n)
    (hp : ir.PlaceOk d Pk (rs.map REdge.plan)) (hr : ir.RealizedOk d rs)
    (hv : ir.ViewsOk d (rs.map REdge.plan)) (x : ir.TreeCell d Pk rs Pads → (I (ir.domainField d)).K)
    (stmt : ir.Valuation I) (run : (ir.layout I).Run) {v : ℕ} (hl : ir.viewValueOk d v = true) :
    ir.viewValuation I d stmt run (Sum.elim (ir.treeDecode d rs Pads x) (ir.treeBits d rs Pads x)) v =
      ir.viewValuation I d stmt run
        (Sum.elim (ir.treeDecode d rs Pads x) (ir.cellBits I d (ir.treeDecode d rs Pads x))) v := by
  funext i
  unfold viewValuation bitValuation
  split
  · rename_i w sel hk
    have hb : ir.bitViewOk d v = true := by
      rcases Bool.or_eq_true_iff.1 hl with h | h
      · simp [rowValueOk, hk] at h
      · exact h
    obtain ⟨-, -, -, hud, -⟩ := bitViewOk_spec hb
    exact congrArg castElt (wordBit_treeBits ht hp hr x (hv v w sel hk hud) _ _)
  · rfl

end Bridge

/-! ## The domain's predicate -/

section Holds

variable (d) in
/-- **The covered batches are realized** (a check on the program and the field): every batch of
`d` passing the batch check, merged or not, on columns or on bits, has a skip domain in the field,
and every one on bits has the export's `Batch.bitSumcheck` set (the C++ runs the bit sumcheck on
it) and the field's interpolation nodes for its bit rounds. -/
def BatchesOk (Pk : (I (ir.domainField d)).Packing) : Prop :=
  ∀ b : Fin ir.batches.length, ir.batchOkB d b = true →
    (Pk.skip (ir.batch b).width (ir.batch b).degree).isSome ∧
      ((ir.batch b).operands = .bits → (ir.batch b).bitSumcheck = true ∧ Pk.nodes.isSome)

variable (d) in
/-- **The covered batches are realized, as a test.** -/
def batchesOkB (Pk : (I (ir.domainField d)).Packing) : Bool :=
  (List.finRange ir.batches.length).all fun b =>
    !ir.batchOkB d b || ((Pk.skip (ir.batch b).width (ir.batch b).degree).isSome &&
      (!decide ((ir.batch b).operands = .bits) || ((ir.batch b).bitSumcheck && Pk.nodes.isSome)))

theorem BatchesOk.of_batchesOkB {Pk : (I (ir.domainField d)).Packing}
    (h : ir.batchesOkB d Pk = true) : ir.BatchesOk d Pk := by
  intro b hb
  have := List.all_eq_true.1 h b (List.mem_finRange b)
  simp only [hb, Bool.not_true, Bool.false_or, Bool.and_eq_true] at this
  refine ⟨this.1, fun hom => ?_⟩
  simpa [hom] using this.2

/-- **A covered batch on columns is listed** among `cbatches`. -/
theorem exists_cbatch {Pk : (I (ir.domainField d)).Packing} (hB : ir.BatchesOk d Pk)
    {b : Fin ir.batches.length} (hb : ir.batchOkB d b = true)
    (hom : (ir.batch b).operands = .columns) (hm : ir.merged b = false) :
    ∃ i : Fin (ir.cbatches d Pk).length, ((ir.cbatches d Pk)[i]).idx = b := by
  obtain ⟨dom, hdom⟩ := Option.isSome_iff_exists.1 (hB b hb).1
  have hmem : (⟨b, hb, hom, hm, dom⟩ : ir.CBatch I d .columns) ∈ ir.cbatches d Pk := by
    refine List.mem_filterMap.2 ⟨b, List.mem_finRange b, ?_⟩
    simp only [hb, hom, hm, and_self, ↓reduceDIte, hdom, Option.map_some]
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hmem
  exact ⟨⟨i, hi⟩, by simp only [Fin.getElem_fin, he]⟩

/-- **A covered merged batch on columns is listed** among `mbatches`. -/
theorem exists_mbatch {Pk : (I (ir.domainField d)).Packing} (hB : ir.BatchesOk d Pk)
    {b : Fin ir.batches.length} (hb : ir.batchOkB d b = true) (hm : ir.merged b = true)
    (hom : (ir.batch b).operands = .columns) :
    ∃ i : Fin (ir.mbatches d Pk).length, ((ir.mbatches d Pk)[i]).idx = b := by
  obtain ⟨dom, hdom⟩ := Option.isSome_iff_exists.1 (hB b hb).1
  have hmem : (⟨b, hb, .columns, hom, hm, dom⟩ : ir.MBatch I d) ∈ ir.mbatches d Pk := by
    refine List.mem_filterMap.2 ⟨b, List.mem_finRange b, ?_⟩
    simp only [hb, hm, hom, and_self, ↓reduceDIte, hdom, Option.map_some]
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hmem
  exact ⟨⟨i, hi⟩, by simp only [Fin.getElem_fin, he]⟩

/-- **A covered batch on bits is listed** among `sumBatches`. -/
theorem exists_sbatch {Pk : (I (ir.domainField d)).Packing} (hB : ir.BatchesOk d Pk)
    {b : Fin ir.batches.length} (hb : ir.batchOkB d b = true)
    (hom : (ir.batch b).operands = .bits) (hm : ir.merged b = false) :
    ∃ i : Fin (ir.sumBatches d Pk).length, ((ir.sumBatches d Pk)[i]).cb.idx = b := by
  obtain ⟨dom, hdom⟩ := Option.isSome_iff_exists.1 (hB b hb).1
  obtain ⟨nodes, hnodes⟩ := Option.isSome_iff_exists.1 ((hB b hb).2 hom).2
  have hmem : (⟨⟨b, hb, hom, hm, dom⟩, nodes⟩ : ir.SCBatch I d) ∈ ir.sumBatches d Pk := by
    refine List.mem_filterMap.2 ⟨b, List.mem_finRange b, ?_⟩
    simp only [hb, hom, hm, and_self, ↓reduceDIte, hdom, hnodes, Option.bind_some,
      Option.map_some]
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hmem
  exact ⟨⟨i, hi⟩, by simp only [Fin.getElem_fin, he]⟩

/-- **A covered merged batch on bits is listed** among `sumMBatches`. -/
theorem exists_smbatch {Pk : (I (ir.domainField d)).Packing} (hB : ir.BatchesOk d Pk)
    {b : Fin ir.batches.length} (hb : ir.batchOkB d b = true) (hm : ir.merged b = true)
    (hom : (ir.batch b).operands = .bits) :
    ∃ i : Fin (ir.sumMBatches d Pk).length, ((ir.sumMBatches d Pk)[i]).mb.idx = b := by
  obtain ⟨dom, hdom⟩ := Option.isSome_iff_exists.1 (hB b hb).1
  obtain ⟨nodes, hnodes⟩ := Option.isSome_iff_exists.1 ((hB b hb).2 hom).2
  have hmem : (⟨⟨b, hb, _, rfl, hm, dom⟩, hom, nodes⟩ : ir.SMBatch I d) ∈ ir.sumMBatches d Pk := by
    refine List.mem_filterMap.2 ⟨b, List.mem_finRange b, ?_⟩
    simp only [hb, hm, hom, and_self, ↓reduceDIte, hdom, hnodes, Option.bind_some,
      Option.map_some]
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hmem
  exact ⟨⟨i, hi⟩, by simp only [Fin.getElem_fin, he]⟩

/-- **A circuit's source read in the domain's field, satisfied on its input on the tree's
coordinates, gives the circuit's meaning** at the decoded cells, under the trust bundle
(`circuitHolds_of_treeInput`, the field read along the circuit's domain). -/
theorem circuitHolds_of_castSat (T : ir.CircuitsEnforce I src) {c : Fin ir.circuits.length}
    (hcd : (ir.circuit c).domain = d) {Pk : (I (ir.domainField d)).Packing}
    {rs : List (REdge (I (ir.domainField d)) Pk)} {Pads : Type} [Fintype Pads]
    (hc : ir.InputsT d c) (hv : ir.ViewsOk d (rs.map REdge.plan))
    (ht : TreeOk (rs.map REdge.plan) Pk.n) (hp : ir.PlaceOk d Pk (rs.map REdge.plan))
    (hr : ir.RealizedOk d rs) (hwf : ir.WellFormed) (p : ir.DomainPub I)
    (x : ir.TreeCell d Pk rs Pads → (I (ir.domainField d)).K)
    (h : (cast (congrArg (fun e => GordieHowe.GKR.LayeredCircuit (I (ir.domainField e)).K (src c).d) hcd)
      (src c).S).Satisfied ((ir.treeInputForms rs Pads c (src c).d).input p
        ((ir.treeLevel d rs Pads).view x))) :
    ir.CircuitHolds I c (ir.cellValuation I d p.stmt p.run (ir.treeDecode d rs Pads x)) := by
  subst hcd
  exact circuitHolds_of_treeInput T hc hv ht hp hr hwf p x h

variable (d) in
/-- **Every quadratic triple's cells are cells of domain `d`.** -/
def QuadsOk : Prop :=
  ∀ q : ir.QuadIdx d, ∀ a b c, ir.quadLeaves d q.1.1 = some (a, b, c) →
    CellKey.val a q.2 ∈ ir.cellKeys d ∧ CellKey.val b q.2 ∈ ir.cellKeys d ∧
      CellKey.val c q.2 ∈ ir.cellKeys d

instance : Decidable (ir.QuadsOk d) := by
  unfold QuadsOk
  haveI : ∀ q : ir.QuadIdx d, Decidable (∀ a b c, ir.quadLeaves d q.1.1 = some (a, b, c) →
      CellKey.val a q.2 ∈ ir.cellKeys d ∧ CellKey.val b q.2 ∈ ir.cellKeys d ∧
        CellKey.val c q.2 ∈ ir.cellKeys d) := fun q => by
    cases h : ir.quadLeaves d q.1.1 with
    | none => exact isTrue fun a b c h' => by cases h'
    | some t =>
      obtain ⟨a, b, c⟩ := t
      exact decidable_of_iff (CellKey.val a q.2 ∈ ir.cellKeys d ∧ CellKey.val b q.2 ∈ ir.cellKeys d ∧
        CellKey.val c q.2 ∈ ir.cellKeys d) ⟨fun hk a' b' c' h' => by
          cases h'
          exact hk, fun hk => hk a b c rfl⟩
  infer_instance

/-- **The checks of domain `d`'s masked reduction** (decidable facts about the program, the plan and the
field): the tree, the cells' nodes, the realized edges, the viewed words, every circuit's input
layout, and the covered batches. -/
structure ClaimOk (rs : List (REdge (I (ir.domainField d)) Pk)) : Prop where
  /-- The tree condition. -/
  tree : TreeOk (rs.map REdge.plan) Pk.n
  /-- The cells' nodes. -/
  place : ir.PlaceOk d Pk (rs.map REdge.plan)
  /-- The realized edges carry the field's kits. -/
  realized : ir.RealizedOk d rs
  /-- The viewed words. -/
  views : ir.ViewsOk d (rs.map REdge.plan)
  /-- Every circuit's input layout. -/
  inputs : ∀ c ∈ ir.circs d, ir.InputsT d c
  /-- The covered batches. -/
  batches : ir.BatchesOk d Pk
  /-- Every quadratic triple's cells are cells of `d`. -/
  quads : ir.QuadsOk d
  /-- The program is well formed. -/
  wf : ir.WellFormed

/-- **The domain's predicate from the masked reduction's relation**, given the trust bundle: the decoded
cells lie in their bases (`treeDecode_mem`); every circuit's meaning (`circuitHolds_of_castSat`);
every affine row and row on views (`rowForm`); every covered batch, on columns
(`colsBatchAt_holds_iff`) and on bits (`bitsBatchAt_holds_iff`). -/
theorem holds_of_fieldSat (h : ir.ClaimOk rs) (T : ir.CircuitsEnforce I src) (p : ir.DomainPub I)
    (x : ir.FCell src Pk rs → (I (ir.domainField d)).K) (hs : ir.FieldSat src rs p x) :
    (ir.domainOf I d).Holds p.stmt (ir.treeDecode d rs (ir.ClaimPads d src Pk) x) p.run where
  base := treeDecode_mem ir h.tree h.place x
  circuit c := by
    obtain ⟨c, hc⟩ := c
    have hmem : c ∈ ir.circs d := by
      simp only [circs, List.mem_filter, List.mem_finRange, hc, beq_self_eq_true, and_self]
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 hmem
    have := ir.circuitHolds_of_castSat src T (circAt_domain ⟨i, hi⟩) (h.inputs _ (List.getElem_mem hi))
      h.views h.tree h.place h.realized h.wf p x (hs.gkr ⟨i, hi⟩)
    change ir.CircuitHolds I c _
    simp only [circAt, Fin.getElem_fin, he] at this
    exact this
  affine q := by
    have hq := hs.rows (Encodable.fintypeEquivFin (α := ir.RowIdx d) (.inl q))
    simp only [rowClaims, Equiv.symm_apply_apply, rowForm, eval_affineOn, LinearMap.comp_apply] at hq
    exact hq
  quad q := by
    obtain ⟨⟨⟨p, hp⟩, hq⟩, i⟩ := q
    obtain ⟨⟨a, b, c⟩, hl⟩ := Option.isSome_iff_exists.1 hq
    obtain ⟨-, ha, hb, hc⟩ := quadLeaves_spec hl
    obtain ⟨hka, hkb, hkc⟩ := h.quads ⟨⟨⟨p, hp⟩, hq⟩, i⟩ a b c hl
    have hroot : ∀ v, ir.quadCellB d v = true → ∀ (hk : CellKey.val v i ∈ ir.cellKeys d),
        ir.cellLin I d (.val v i) (ir.treeDecode d rs (ir.ClaimPads d src Pk) x) =
          x (ir.quadCell src rs (.val v i)) := fun v hv hk => by
      have hn : ir.cellNode (rs.map REdge.plan) (CellKey.val v i) = none := by
        simp only [quadCellB, Bool.and_eq_true, Option.isNone_iff_eq_none] at hv
        simp only [cellNode, cellName, hv.1.2, Option.map_none, Option.bind_none]
      rw [cellLin_of_mem hk, treeDecode_root (ir := ir) (d := d) x (k := ⟨_, hk⟩) hn, quadCell,
        dif_pos ⟨hk, hn⟩]
    have hprod := hs.quads ⟨⟨⟨p, hp⟩, hq⟩, i⟩
    simp only [quadProducts, hl] at hprod
    show (ir.quadRow I d ⟨⟨⟨p, hp⟩, hq⟩, i⟩).Holds _
    simp only [quadRow, hl, QuadRow.Holds]
    rw [hroot a ha hka, hroot b hb hkb, hroot c hc hkc]
    exact hprod
  batch b := by
    rcases b with ⟨b, hb⟩ | ⟨b, hb, -⟩
    · obtain ⟨hok, hom⟩ := colsBatchOk hb
      cases hm : ir.merged b
      · obtain ⟨i, hi⟩ := exists_cbatch h.batches ((ir.batchOkB_iff d b).2 hok) hom hm
        have := (ir.colsBatchAt_holds_iff rs (ir.ClaimPads d src Pk) _ p _).1 (hs.cols i).holds
        rw [hi] at this
        exact this
      · obtain ⟨i, hi⟩ := exists_mbatch h.batches ((ir.batchOkB_iff d b).2 hok) hm hom
        have hc : ((ir.mbatches d Pk)[i]).om = .columns := om_of_mem_mbatches (List.getElem_mem _)
        have := (ir.mergedBatchAt_holds_iff rs (ir.ClaimPads d src Pk) _ hc p _).1 (hs.merged i).holds
        rw [hi] at this
        exact this
    · obtain ⟨hok, hom⟩ := bitsBatchOk hb
      cases hm : ir.merged b
      · obtain ⟨i, hi⟩ := exists_sbatch h.batches ((ir.batchOkB_iff d b).2 hok) hom hm
        have := (ir.bitsBatchAt_holds_iff rs (ir.ClaimPads d src Pk) h.tree h.place h.realized
          h.views _ (hi ▸ hb) p x).1 (hs.sumBits i).holds
        revert this
        generalize ((ir.sumBatches d Pk)[i]).cb.idx = b' at hi
        subst hi
        intro this
        exact this
      · obtain ⟨i, hi⟩ := exists_smbatch h.batches ((ir.batchOkB_iff d b).2 hok) hm hom
        have := (ir.mergedBatchAt_holds_iff_bits rs (ir.ClaimPads d src Pk) h.tree h.place
          h.realized h.views _ ((ir.sumMBatches d Pk)[i]).bits p x).1 (hs.sumMerged i).holds
        subst hi
        exact this
  viewRow q := by
    change ir.ViewRow d at q
    show (ir.viewRow I d q).Holds p.stmt (Sum.elim (ir.treeDecode d rs (ir.ClaimPads d src Pk) x)
      (ir.cellBits I d (ir.treeDecode d rs (ir.ClaimPads d src Pk) x))) p.run
    have hq := hs.rows (Encodable.fintypeEquivFin (α := ir.RowIdx d) (.inr q))
    simp only [rowClaims, Equiv.symm_apply_apply, rowForm, eval_affineOn, LinearMap.comp_apply] at hq
    have h' : ir.viewDiff I d p.stmt p.run q.1.1 q.2
        (Sum.elim (ir.treeDecode d rs (ir.ClaimPads d src Pk) x)
          (ir.treeBits d rs (ir.ClaimPads d src Pk) x)) = 0 := by
      rw [← viewRow_eval q p.stmt p.run]
      exact hq
    have hE : ∀ e, ir.viewExprOk d e = true →
        ir.evalWith (ir.viewValuation I d p.stmt p.run
          (Sum.elim (ir.treeDecode d rs (ir.ClaimPads d src Pk) x)
            (ir.treeBits d rs (ir.ClaimPads d src Pk) x))) d e =
        ir.evalWith (ir.viewValuation I d p.stmt p.run
          (Sum.elim (ir.treeDecode d rs (ir.ClaimPads d src Pk) x)
            (ir.cellBits I d (ir.treeDecode d rs (ir.ClaimPads d src Pk) x)))) d e :=
      fun e he => evalE_congr fun v hv =>
        ir.viewValuation_treeBits rs (ir.ClaimPads d src Pk) h.tree h.place h.realized h.views x
          p.stmt p.run (viewValueOk_of_mem he hv)
    have hsd := viewExprOk_sides q.1.2
    unfold viewDiff at h'
    rw [AffineRow.Holds, viewRow_eval]
    unfold viewDiff
    rwa [hE _ hsd.1, hE _ hsd.2] at h'

end Holds

end

end GordieHowe.RealizedProgram
