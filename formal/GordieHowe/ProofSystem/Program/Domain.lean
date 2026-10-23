-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Views

@[expose] public section

/-!
# GordieHowe: a program's domain as a domain of the lowered system

Domain `d` of a program as a `GordieHowe.Domain` on the program's layout (`GordieHowe.RealizedProgram.domainOf`), over
the statements `GordieHowe.RealizedProgram.Valuation`:

* the field: domain `d`'s field; the coordinates: its cells (`RealizedProgram.Cell d`), each with its base
  (`GordieHowe.RealizedProgram.cellBase`: the packing-tree node of its value, the pad space of its late value);
* the circuit constraints: the GKR circuits of `d` (`GordieHowe.RealizedProgram.DomainCircuit`), each the meaning of
  the circuit (`GordieHowe.RealizedProgram.CircuitHolds`) at the cells' valuation (`GordieHowe.RealizedProgram.cellValuation`: the reader
  of the layout's environment at the committed assignment read from the cells);
* the affine rows: the predicates of `d` with target `affine` whose sides may be rows
  (`GordieHowe.RealizedProgram.Row`, `GordieHowe.RealizedProgram.affineRow`);
* the batched relations: the batches of `d` the proof system covers (`GordieHowe.RealizedProgram.BatchOk`), those on columns (`GordieHowe.RealizedProgram.DomainBatch`) each the batched relation of
  its parts (`GordieHowe.RealizedProgram.batchRelation`), and those on bits when the field's bit coordinates are
  additive (`GordieHowe.RealizedProgram.DomainBitsBatch`, `GordieHowe.RealizedProgram.bitsBatchRelation`);
* the view coordinates: bit `j < 16` of every cell (`GordieHowe.RealizedProgram.cellBits`), and the rows on views,
  the predicates with target `affine` reading bit views (`GordieHowe.RealizedProgram.ViewRow`, `GordieHowe.RealizedProgram.viewRow`);
* no quadratic triple (a predicate with a quadratic target is not lowered here).

**A domain under a trust assumption** (`GordieHowe.Domain.guard`): the same field and coordinates
and one circuit constraint, "`T` gives the domain's predicate"; a domain's circuit proof under the
compiler trust is defined without the trust bundle.

**Decoding and encoding** (`GordieHowe.RealizedProgram.ofCells`, `GordieHowe.RealizedProgram.toCells`): the committed assignment of the
program read from the cells, and the cells read from a committed assignment; the two agree at every
cell (`ofCells_toCells_val`, `ofCells_toCells_pad`).

**The lowered constraints give the realized program's** (`GordieHowe.RealizedProgram.placedHolds_of_holds`): where
domain `d`'s predicate holds on the cells `a`, every field `equal` and every `mod_0`'s field
equation of `d` that is an affine row, is placed in a GKR circuit of `d` or is a part of a covered
batch of `d` holds in the layout's environment at the realized assignment of the committed
assignment read from `a` (`GordieHowe.RealizedProgram.Lowered`).
-/

namespace GordieHowe

open RealizedProgram.ProofSystem.PhaseLayout

variable {K : ℕ} {L : RealizedProgram.ProofSystem.PhaseLayout K} {Stmt : Type}

/-! ## A domain under a trust assumption -/

/-- **The domain `D` under the assumption `T`**: the same field and coordinates, every coordinate in
the whole field, and one circuit constraint, "`T` gives `D`'s predicate" (`holds_guard_iff`). A
circuit proof of `D.guard T` proves `D`'s predicate given `T`; its construction does not need
`T`. -/
def Domain.guard (T : Prop) (D : Domain L Stmt) : Domain L Stmt where
  F := D.F
  ι := D.ι
  base _ := Set.univ
  Circ := Unit
  circuit _ x a r := T → D.Holds x a r
  Row := Empty
  affine := Empty.elim
  Quad := Empty
  quad := Empty.elim
  Batch := Empty
  batch := Empty.elim

/-- **The predicate of a domain under `T`** is "`T` gives the domain's predicate". -/
theorem Domain.holds_guard_iff {T : Prop} {D : Domain L Stmt} {x : Stmt} {a : D.Cells}
    {r : L.Run} : (D.guard T).Holds x a r ↔ (T → D.Holds x a r) :=
  ⟨fun h => h.circuit (), fun h =>
    ⟨fun _ => trivial, fun _ => h, fun i => i.elim, fun i => i.elim, fun i => i.elim,
      fun i => i.elim⟩⟩

end GordieHowe

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram) (I : Interp)

/-- **The GKR circuits of domain `d`.** -/
def DomainCircuit (d : ℕ) : Type := {c : Fin ir.circuits.length // (ir.circuit c).domain = d}

/-- **The batches on columns of domain `d` the proof system covers**: those that pass the batch check
(`RealizedProgram.BatchOk`) with the operand map `columns`. -/
def DomainBatch (d : ℕ) : Type := {b : Fin ir.batches.length // ir.colsBatchOkB d b = true}

/-- **The batches on bits of domain `d` the proof system covers**: those that pass the batch check
(`RealizedProgram.BatchOk`) with the operand map `bits`, when the field's bit coordinates are additive
(`FieldInterp.BitsAdditive`; their batched relation's operands are additive in the cells). -/
def DomainBitsBatch (d : ℕ) : Type :=
  {b : Fin ir.batches.length // ir.bitsBatchOkB d b = true ∧ (I (ir.domainField d)).BitsAdditive}

/-- **The domains with batches on bits read additive bit coordinates** (a property of the model):
the field of every domain with a batch on bits the proof system covers has additive bit coordinates
(`FieldInterp.BitsAdditive`), so its batches on bits are in its predicate (`DomainBitsBatch`). -/
def BitsBatchAdditive : Prop :=
  ∀ d b, ir.bitsBatchOkB d b = true → (I (ir.domainField d)).BitsAdditive

/-- **The quadratic predicates of domain `d`.** -/
def QuadPred (d : ℕ) : Type := {p : Fin ir.predicates.length // ir.isQuad d p = true}

instance (d : ℕ) : Fintype (ir.QuadPred d) := Subtype.fintype _

/-- The quadratic predicates are encoded by their indices. -/
instance (d : ℕ) : Encodable (ir.QuadPred d) :=
  inferInstanceAs (Encodable {p : Fin ir.predicates.length // ir.isQuad d p = true})

/-- The left side of a quadratic predicate. -/
def quadLhs (p : ℕ) : Expr :=
  match (ir.predicate p).body with
  | .equal _ e _ _ => e
  | _ => .leaf 0

/-- **The quadratic triples of domain `d`**: every coordinate of every quadratic predicate. -/
abbrev QuadIdx (d : ℕ) : Type := Σ q : ir.QuadPred d, Fin (ir.exprLen (ir.quadLhs q.1))

/-- **The cell of a cell key as a linear form** on the cells of domain `d`, zero off the cells. -/
def cellLin (d : ℕ) (k : CellKey) :
    (ir.Cell d → (I (ir.domainField d)).K) →ₗ[(I (ir.domainField d)).K] (I (ir.domainField d)).K where
  toFun a := if h : k ∈ ir.cellKeys d then a (⟨k, h⟩ : ir.Cell d) else 0
  map_add' a b := by
    by_cases h : k ∈ ir.cellKeys d
    · simp only [dif_pos h]
      rfl
    · simp only [dif_neg h, add_zero]
  map_smul' t a := by
    by_cases h : k ∈ ir.cellKeys d
    · simp only [dif_pos h]
      rfl
    · simp only [dif_neg h, smul_zero]

variable {ir I} in
theorem cellLin_of_mem {d : ℕ} {k : CellKey} (h : k ∈ ir.cellKeys d)
    (a : ir.Cell d → (I (ir.domainField d)).K) : ir.cellLin I d k a = a (⟨k, h⟩ : ir.Cell d) :=
  dif_pos h

variable {ir I} in
theorem cellLin_of_not_mem {d : ℕ} {k : CellKey} (h : k ∉ ir.cellKeys d)
    (a : ir.Cell d → (I (ir.domainField d)).K) : ir.cellLin I d k a = 0 :=
  dif_neg h

/-- **Quadratic triple `q` of domain `d`**: coordinate `i` of `a · b = c`, the three cells. -/
def quadRow (d : ℕ) (q : ir.QuadIdx d) : QuadRow (I (ir.domainField d)).K (ir.Cell d) :=
  match ir.quadLeaves d q.1.1 with
  | some (a, b, c) => ⟨ir.cellLin I d (.val a q.2), ir.cellLin I d (.val b q.2),
      ir.cellLin I d (.val c q.2)⟩
  | none => ⟨0, 0, 0⟩

/-- **Domain `d` of the program as a domain of the lowered system** (see the module docstring). -/
def domainOf (d : ℕ) : GordieHowe.Domain (ir.layout I) (ir.Valuation I) where
  F := (I (ir.domainField d)).K
  ι := ir.Cell d
  base := ir.cellBase I d
  Circ := ir.DomainCircuit d
  circuit c x a r := ir.CircuitHolds I c.1 (ir.cellValuation I d x r a)
  Row := ir.Row d
  affine := ir.affineRow I d
  Quad := ir.QuadIdx d
  quad := ir.quadRow I d
  Batch := ir.DomainBatch d ⊕ ir.DomainBitsBatch I d
  batch := Sum.elim (fun b => ir.batchRelation I d b.1)
    fun b => ir.bitsBatchRelation I d b.1 b.2.1 b.2.2
  View := ir.Cell d × Fin 16
  view := ir.cellBits I d
  ViewRow := ir.ViewRow d
  viewRow := ir.viewRow I d

/-- **The cells of domain `d` read from a committed assignment** `A`: each committed coordinate and
pad at its cell, `0` at filler. -/
def toCells (d : ℕ) (A : ir.Assignment I) : ir.Cell d → (I (ir.domainField d)).K
  | ⟨.val v i, _⟩ => castElt (A.val v i)
  | ⟨.pad v i, _⟩ => castElt (A.pad v i)
  | ⟨.filler _ _, _⟩ => 0

variable {ir I}

/-- **Decoding the encoded cells gives the committed coordinates back** at every cell. -/
theorem ofCells_toCells_val {d u i : ℕ} (A : ir.Assignment I)
    (h : CellKey.val u i ∈ ir.cellKeys d) :
    (ir.ofCells I d (ir.toCells I d A)).val u i = A.val u i := by
  have hd := ir.isCellValue_valueField ((ir.mem_cellKeys_val).1 h).2.1
  simp only [ofCells, dif_pos h, toCells]
  exact castElt_castElt_of_eq hd _

/-- **Decoding the encoded cells gives the pads back** at every cell. -/
theorem ofCells_toCells_pad {d u i : ℕ} (A : ir.Assignment I)
    (h : CellKey.pad u i ∈ ir.cellKeys d) :
    (ir.ofCells I d (ir.toCells I d A)).pad u i = A.pad u i := by
  have hd := ir.isLateOf_valueField ((ir.mem_cellKeys_pad).1 h).2.2.1
  simp only [ofCells, dif_pos h, toCells]
  exact castElt_castElt_of_eq hd _

/-! ## The lowered constraints give the realized program's -/

theorem placedHolds_of_isEqual {rd : ir.Valuation I} {b : PredBody} (hb : b.isEqual = true)
    (h : ir.PlacedHolds rd b) : ir.HoldsWith rd b := by
  cases b <;> simp_all [PredBody.isEqual, PlacedHolds]

variable (ir) in
/-- **Predicate `p` is lowered into domain `d`**: an affine row of `d` (`isRow`), a family of rows
on views of `d` (`isViewRow`), a field `equal` or a `mod_0` placed in a GKR circuit of `d` (a
Boolean check or a placed predicate of its emission order), a part of a batch of `d` the proof system
covers, on columns or on bits, or a quadratic triple of `d` (`isQuad`). -/
inductive Lowered (d p : ℕ) : Prop where
  /-- An affine row of `d`. -/
  | row (hp : p < ir.predicates.length) (hrow : ir.isRow d p = true)
  /-- A family of rows on views of `d`. -/
  | viewRow (hp : p < ir.predicates.length) (hrow : ir.isViewRow d p = true)
  /-- A field `equal` or a `mod_0` placed in circuit `c` of `d`. -/
  | placed (c : ir.DomainCircuit d)
      (heq : ((ir.predicate p).body.isEqual || (ir.predicate p).body.isIntEq) = true)
      (hmem : CircuitEntry.pred p ∈ (ir.circuit c.1).entries ∨
        CircuitEntry.typeCheck p ∈ (ir.circuit c.1).entries)
  /-- A part of batch `b` of `d`. -/
  | batch (b : ir.DomainBatch d) (hmem : p ∈ (ir.batch b.1).parts)
  /-- A part of batch on bits `b` of `d`. -/
  | bitsBatch (b : Fin ir.batches.length) (hok : ir.bitsBatchOkB d b = true)
      (hmem : p ∈ (ir.batch b).parts)
  /-- A quadratic triple of `d`. -/
  | quad (hp : p < ir.predicates.length) (hq : ir.isQuad d p = true)

/-- **A cell of the quadratic test is read as its cell** by the cells' valuation, zero off the
cells. -/
theorem evalWith_leaf_quadCell {d v : ℕ} (hv : ir.quadCellB d v = true) (x : ir.Valuation I)
    (r : (ir.layout I).Run) (a : ir.Cell d → (I (ir.domainField d)).K) (i : ℕ) :
    ir.evalWith (ir.cellValuation I d x r a) d (.leaf v) i = ir.cellLin I d (.val v i) a := by
  simp only [quadCellB, Bool.and_eq_true] at hv
  obtain ⟨⟨⟨⟨hcv, -⟩, -⟩, -⟩, hk⟩ := hv
  have hpriv : (ir.value v).kind = .priv := by
    revert hk
    cases (ir.value v).kind <;> simp
  have hf := ir.isCellValue_valueField hcv
  simp only [evalWith, evalE, Expr.eval, cellValuation, reader_of_priv _ hpriv, layoutEnv,
    ir.bindAsg_val_of_isBound (v := v) _ (by rw [hpriv]; rfl), ofCells]
  by_cases h : CellKey.val v i ∈ ir.cellKeys d
  · rw [cellLin_of_mem h, dif_pos h]
    exact castElt_castElt_of_eq hf.symm _
  · rw [cellLin_of_not_mem h, dif_neg h, castElt_zero]

/-- **The shape of a quadratic predicate** (`quadLeaves`). -/
theorem quadLeaves_spec {d p a b c : ℕ} (h : ir.quadLeaves d p = some (a, b, c)) :
    (ir.predicate p).body = .equal d (.mul (.leaf a) (.leaf b)) (.leaf c) .quadratic ∧
      ir.quadCellB d a = true ∧ ir.quadCellB d b = true ∧ ir.quadCellB d c = true := by
  unfold quadLeaves at h
  split at h
  · next d' a' b' c' heq =>
    split_ifs at h with hc
    obtain ⟨rfl, h1, h2, h3⟩ := hc
    cases h
    exact ⟨heq, h1, h2, h3⟩
  · cases h

/-- **A quadratic predicate holds placed** at the cells' valuation when its triples hold on the
cells (`evalWith_leaf_quadCell`). -/
theorem placedHolds_of_quad {d p : ℕ} (hp : p < ir.predicates.length) (hq : ir.isQuad d p = true)
    {x : ir.Valuation I} {r : (ir.layout I).Run} {a : ir.Cell d → (I (ir.domainField d)).K}
    (h : ∀ i, (ir.quadRow I d ⟨⟨⟨p, hp⟩, hq⟩, i⟩).Holds a) :
    ir.PlacedHolds (ir.cellValuation I d x r a) (ir.predicate p).body := by
  obtain ⟨⟨a', b', c'⟩, hl⟩ := Option.isSome_iff_exists.1 hq
  obtain ⟨hbody, ha, hb, hc⟩ := quadLeaves_spec hl
  have hlen : ir.exprLen (ir.quadLhs p) = ir.exprLen (.mul (.leaf a') (.leaf b')) := by
    simp only [quadLhs, hbody]
  rw [hbody]
  intro i hi
  have hi' := h ⟨i, hlen ▸ hi⟩
  simp only [quadRow, hl, QuadRow.Holds] at hi'
  change ir.evalWith _ d (.leaf a') i * ir.evalWith _ d (.leaf b') i = ir.evalWith _ d (.leaf c') i
  rw [evalWith_leaf_quadCell ha, evalWith_leaf_quadCell hb, evalWith_leaf_quadCell hc]
  exact hi'

/-- **A quadratic predicate placed at the cells' valuation gives its triples** on the cells
(`evalWith_leaf_quadCell`). -/
theorem quadRow_holds_of_placed {d p : ℕ} (hp : p < ir.predicates.length)
    (hq : ir.isQuad d p = true) {x : ir.Valuation I} {r : (ir.layout I).Run}
    {a : ir.Cell d → (I (ir.domainField d)).K}
    (h : ir.PlacedHolds (ir.cellValuation I d x r a) (ir.predicate p).body)
    (i : Fin (ir.exprLen (ir.quadLhs p))) : (ir.quadRow I d ⟨⟨⟨p, hp⟩, hq⟩, i⟩).Holds a := by
  obtain ⟨⟨a', b', c'⟩, hl⟩ := Option.isSome_iff_exists.1 hq
  obtain ⟨hbody, ha, hb, hc⟩ := quadLeaves_spec hl
  have hlen : ir.exprLen (ir.quadLhs p) = ir.exprLen (.mul (.leaf a') (.leaf b')) := by
    simp only [quadLhs, hbody]
  rw [hbody] at h
  have hi := h i (hlen ▸ i.2)
  change ir.evalWith _ d (.leaf a') i * ir.evalWith _ d (.leaf b') i = ir.evalWith _ d (.leaf c') i
    at hi
  rw [evalWith_leaf_quadCell ha, evalWith_leaf_quadCell hb, evalWith_leaf_quadCell hc] at hi
  simp only [quadRow, hl, QuadRow.Holds]
  exact hi

/-- **The lowered constraints give the realized program's predicates, placed**: where domain `d`'s
predicate holds on the cells `a` at the statement `x` and the run `r`, every predicate lowered into
`d` (`Lowered`) holds placed (`PlacedHolds`: a field `equal` itself, a `mod_0` its field equation)
at the cells' valuation. `hadd` and `hz` are properties of the model (`BitsBatchAdditive`,
`ZeroDecodes`). -/
theorem placedHolds_of_holds (hadd : ir.BitsBatchAdditive I) (hz : ir.ZeroDecodes I) {d : ℕ}
    {x : ir.Valuation I} {a : ir.Cell d → (I (ir.domainField d)).K} {r : (ir.layout I).Run}
    (h : (ir.domainOf I d).Holds x a r) {p : ℕ} (hp : ir.Lowered d p) :
    ir.PlacedHolds (ir.cellValuation I d x r a) (ir.predicate p).body := by
  rcases hp with ⟨hp, hrow⟩ | ⟨hp, hrow⟩ | ⟨c, -, hmem⟩ | ⟨b, hmem⟩ | ⟨b, hok, hmem⟩ | ⟨hp, hq⟩
  · exact (affineRows_iff ⟨⟨p, hp⟩, hrow⟩ x a r).1 fun i => h.affine ⟨⟨⟨p, hp⟩, hrow⟩, i⟩
  · exact (viewRows_iff ⟨⟨p, hp⟩, hrow⟩ x a r).1 fun i => h.viewRow ⟨⟨⟨p, hp⟩, hrow⟩, i⟩
  · have hc : ir.CircuitHolds I c.1 (ir.cellValuation I d x r a) := h.circuit c
    rcases hmem with hm | hm
    · exact hc _ hm
    · exact hc _ hm
  · exact (batchRelation_holds_iff hz (partsOk_of_cols b.2) x r a).1 (h.batch (.inl b)) p hmem
  · exact (bitsBatchRelation_holds_iff hz hok (hadd d b hok) x r a).1
      (h.batch (.inr ⟨b, hok, hadd d b hok⟩)) p hmem
  · exact placedHolds_of_quad hp hq fun i => h.quad ⟨⟨⟨p, hp⟩, hq⟩, i⟩

end

end GordieHowe.RealizedProgram
