-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Ligero.Preparation

@[expose] public section

/-!
# Block placement for the Ligero tableau

The formulas follow `LigeroParam` and `LigeroCommon::inner_product_vector`:
physical rows are ILDT, IDOT, IQUAD, witness blocks, X blocks, Y blocks, Z blocks.
The algebraic tableau keeps ILDT and the data blocks; its two other masks are
separate auxiliary messages. `physicalRow` makes that flattening explicit.
This verifies the mathematical layout formulas, not C++ execution or allocation.
-/

namespace GordieHowe.Ligero.Layout
open IOP

open scoped Classical
section

/-- Public block dimensions; privacy occupies the first `r` message nodes. After the witness and
product rows come `extra` unused data rows (the six piece rows of the mask test,
`Ligero.Layout.Shape.pieceRows`; none for untested masks). -/
structure Shape where
  /-- The block width: witness positions per row. -/
  w : ℕ
  /-- The number of privacy coordinates at the start of each row. -/
  r : ℕ
  /-- The number of witness values. -/
  nw : ℕ
  /-- The number of quadratic triples. -/
  nq : ℕ
  /-- The number of unused data rows after the witness and product rows. -/
  extra : ℕ
  /-- The block width is positive. -/
  width_pos : 0 < w

namespace Shape

variable (S : Shape)

/-- The number of rows of width `w` that hold `n` values: `⌈n / w⌉`. -/
def blocks (n : ℕ) : ℕ := (n + S.w - 1) / S.w
/-- The number of witness rows. -/
def witnessRows : ℕ := S.blocks S.nw
/-- The number of product groups: rows of width `w` per X, Y and Z block. -/
def productGroups : ℕ := S.blocks S.nq
/-- The number of data rows: the witness rows, the X, Y and Z blocks and the extra rows. -/
def dataRows : ℕ := S.witnessRows + 3 * S.productGroups + S.extra
/-- The number of physical rows: the data rows and the three masks ILDT, IDOT, IQUAD. -/
def physicalRows : ℕ := S.dataRows + 3

theorem block_lt {n i : ℕ} (hi : i < n) : i / S.w < S.blocks n := by
  apply Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
  apply (Nat.le_div_iff_mul_le S.width_pos).mpr
  calc
    (i / S.w + 1) * S.w = i / S.w * S.w + S.w := by ring
    _ ≤ i + S.w := Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
    _ ≤ n + S.w - 1 := by have := S.width_pos; omega

/-- ILDT remains row zero; the two auxiliary mask rows are skipped. The offset `+2` is the two
unsplit auxiliary mask rows IDOT and IQUAD at physical rows `1` and `2`; the mask test puts its
piece rows among the data rows (`extra`), and this map does not model any other physical
order. -/
def physicalRow (row : Fin (S.dataRows + 1)) : Fin S.physicalRows :=
  ⟨if row.val = 0 then 0 else row.val + 2, by
    have := row.isLt
    unfold physicalRows
    split_ifs <;> omega⟩

@[simp] theorem physicalRow_zero : (S.physicalRow 0).val = 0 := by
  simp [physicalRow]

theorem physicalRow_nonzero (row : Fin (S.dataRows + 1)) (h : row ≠ 0) :
    (S.physicalRow row).val = row.val + 2 := by
  have hv : row.val ≠ 0 := by
    intro hz
    apply h
    exact Fin.ext hz
  simp [physicalRow, hv]

theorem physicalRow_injective : Function.Injective S.physicalRow := by
  intro a b h
  have hv := congrArg Fin.val h
  dsimp [physicalRow] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

/-- Project the committed physical array to the code-test matrix. -/
def flatten {F : Type} {N : ℕ} (U : Fin S.physicalRows → Fin N → F) :
    Fin (S.dataRows + 1) → Fin N → F := fun row => U (S.physicalRow row)

/-- IDOT and IQUAD are the two masks consumed separately by the tableau test. -/
def masks {F : Type} {N : ℕ} (U : Fin S.physicalRows → Fin N → F) :
    (Fin N → F) × (Fin N → F) :=
  (U ⟨1, by unfold physicalRows; omega⟩, U ⟨2, by unfold physicalRows; omega⟩)

@[simp] theorem flatten_apply {F : Type} {N : ℕ}
    (U : Fin S.physicalRows → Fin N → F) (row : Fin (S.dataRows + 1)) (j : Fin N) :
    S.flatten U row j = U (S.physicalRow row) j := rfl

variable {F : Type} [Field F] {N : ℕ} (C : GordieHowe.RSCode F N)
    (hk : C.k = S.r + S.w)

/-- Witness columns are exactly the suffix after the privacy coordinates. -/
def witness : Finset (Fin C.k) := Finset.univ.filter (fun j => S.r ≤ j.val)

/-- The column of the `i`-th value of a block: the `(i mod w)`-th witness position. -/
def column (i : ℕ) : Fin C.k :=
  ⟨S.r + i % S.w, by have := Nat.mod_lt i S.width_pos; omega⟩

theorem column_mem (i : ℕ) : S.column C hk i ∈ S.witness C := by
  simp [witness, column]

/-- The position of witness value `i`: row `1 + i / w` (after ILDT), column `column i`. -/
def source (i : Fin S.nw) : Fin (S.dataRows + 1) × Fin C.k :=
  (⟨1 + i.val / S.w, by
      have h := S.block_lt i.isLt
      change i.val / S.w < S.witnessRows at h
      unfold dataRows
      omega⟩, S.column C hk i.val)

/-- The row of product group `q` in the X, Y or Z block (`slot` `0`, `1`, `2`), after the witness
rows. -/
def products (q : Fin S.productGroups) (slot : Fin 3) : Fin (S.dataRows + 1) :=
  ⟨1 + S.witnessRows + slot.val * S.productGroups + q.val, by
    clear hk C
    have hq := q.isLt
    have hs := slot.isLt
    have hm : slot.val * S.productGroups ≤ 2 * S.productGroups :=
      Nat.mul_le_mul_right _ (by omega)
    unfold dataRows
    omega⟩

/-- The tableau parameters of the shape at the message nodes `nodes`: the witness suffix and the
product rows. -/
def parameters (nodes : Fin C.k → F) (hinj : Function.Injective nodes) :
    Tableau.Parameters (R := S.dataRows) (nQ := S.productGroups) C where
  nodes := nodes
  nodes_injective := hinj
  witness := S.witness C
  products := S.products

/-- Every multiplication gets a co-column copy in each of the X/Y/Z blocks. -/
def placement (nodes : Fin C.k → F) (hinj : Function.Injective nodes) :
    Preparation.Placement C (S.parameters C nodes hinj) (Fin S.nw) (Fin S.nq) where
  source := S.source C hk
  source_nonzero i := by
    intro h
    have hv := congrArg Fin.val h
    change 1 + i.val / S.w = 0 at hv
    exact (Nat.ne_of_gt (Nat.add_pos_left (by decide : 0 < 1) _)) hv
  source_witness i := S.column_mem C hk i.val
  copyGroup q := ⟨q.val / S.w, S.block_lt q.isLt⟩
  copyCol q := S.column C hk q.val
  copy_witness q := S.column_mem C hk q.val
  product_nonzero q slot := by
    intro h
    have hv := congrArg Fin.val h
    change 1 + S.witnessRows + slot.val * S.productGroups + q.val / S.w = 0 at hv
    have hpos : 0 < 1 + S.witnessRows + slot.val * S.productGroups + q.val / S.w := by positivity
    exact (Nat.ne_of_gt hpos) hv

/-- Enumerating source variables and multiplication constraints specializes the
same physical layout to arbitrary finite index types. -/
def indexedPlacement {ι Q : Type} (sourceIndex : ι ≃ Fin S.nw)
    (productIndex : Q ≃ Fin S.nq)
    (nodes : Fin C.k → F) (hinj : Function.Injective nodes) :
    Preparation.Placement C (S.parameters C nodes hinj) ι Q where
  source i := (S.placement C hk nodes hinj).source (sourceIndex i)
  source_nonzero i := (S.placement C hk nodes hinj).source_nonzero (sourceIndex i)
  source_witness i := (S.placement C hk nodes hinj).source_witness (sourceIndex i)
  copyGroup q := (S.placement C hk nodes hinj).copyGroup (productIndex q)
  copyCol q := (S.placement C hk nodes hinj).copyCol (productIndex q)
  copy_witness q := (S.placement C hk nodes hinj).copy_witness (productIndex q)
  product_nonzero q s := (S.placement C hk nodes hinj).product_nonzero (productIndex q) s

/-- The model source location is the implementation's witness row and column. -/
theorem source_physical (i : Fin S.nw) :
    (S.physicalRow (S.source C hk i).1).val = 3 + i.val / S.w := by
  simp [physicalRow, source]
  omega

/-- Contiguous X, Y, and Z row groups begin after all witness rows. -/
theorem product_physical (q : Fin S.productGroups) (slot : Fin 3) :
    (S.physicalRow (S.products q slot)).val =
      3 + S.witnessRows + slot.val * S.productGroups + q.val := by
  simp [physicalRow, products]
  omega

/-- Row-major source indices are recovered exactly, including a final partial
block. This is independent of the field values placed in those slots. -/
theorem source_index (i : Fin S.nw) :
    ((S.source C hk i).1.val - 1) * S.w +
      ((S.source C hk i).2.val - S.r) = i.val := by
  simp only [source, column, Nat.add_sub_cancel_left]
  simpa only [Nat.mul_comm] using Nat.div_add_mod i.val S.w

end Shape
end
end GordieHowe.Ligero.Layout
