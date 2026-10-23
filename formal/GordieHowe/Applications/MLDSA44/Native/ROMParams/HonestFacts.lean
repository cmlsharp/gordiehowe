-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Honest
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.HonestFull
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.ProofSystem
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Setting
public import GordieHowe.Applications.MLDSA44.Frontend.QField

@[expose] public section

/-!
# GordieHowe: the honest strategy's program facts of `MLDSA44.Native.ROMParams`

The program's instance of the honest strategy's class (`MldsaNativeHonest`), decided on the tables
of `GordieHowe.Generated.MLDSA44.Native.ROMParams.Program.program` (export `c825eb05`): the only cross-field
`equal` `mac.equal`, the blind's cells, the statement's values and the committed and node-typed
values' classes. The bound values' facts come from the realization condition
(`Realize.derivable`, `DerivationsValid.bound`).
-/

namespace GordieHowe.MLDSA44.Native.ROMParams.Honest

open RealizedProgram
open HashField (interp)

/-- The only cross-field `equal` is `mac.equal` (predicate `272`), decided. -/
theorem cross_only : (List.range Pg.predicates.length).all (fun q => q == 272 ||
    match (Pg.predicate q).body with
    | .cross _ _ _ _ _ _ => false
    | _ => true) = true := by
  decide +kernel

/-- The blind's cells, decided. -/
theorem blind_cells : (Pg.value 568).kind = .padCopy 571 "polynomialBits" ∧
    (Pg.value 568).domain < Pg.domains.length ∧
    (∀ j < 128, CellKey.val 568 j ∈ Pg.cellKeys (Pg.value 568).domain) ∧
    Pg.valueField 568 = 0 ∧ (Pg.value 568).size = 128 :=
  ⟨kind_of_isPadCopyB (by decide +kernel), by decide +kernel,
    fun j hj => (Pg.mem_cellKeys_val).2 ⟨by decide +kernel, by decide +kernel,
      by have : (Pg.value 568).size = 128 := by decide +kernel
         omega⟩, by decide +kernel, by decide +kernel⟩

/-! ## The program's instance of the honest strategy's class -/

theorem stmt67 (pk : MLDSA44.PublicKey44) (j : ℕ) (hj : j < 512) :
    (castElt (b := 1) (ROMParams.stmtOfKey pk 67 j) : (interp 1).K) =
      Bits.constBit (MLDSA44.PoP.Compose.trOf pk ⟨j / 8, by omega⟩).toNat (j % 8) := by
  have hf : Pg.valueField 67 = 1 := by decide +kernel
  unfold ROMParams.stmtOfKey ROMParams.stmtOfKeyWith
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos ⟨rfl, hj⟩]
  exact castElt_castElt_of_eq hf.symm _

theorem stmt56 (pk : MLDSA44.PublicKey44) (j : ℕ) (hj : j < 4096) :
    ∃ n : ℕ, (castElt (b := 0) (ROMParams.stmtOfKey pk 56 j) : (interp 0).K) = n := by
  have hf : Pg.valueField 56 = 0 := by decide +kernel
  unfold ROMParams.stmtOfKey ROMParams.stmtOfKeyWith
  rw [dif_pos ⟨rfl, hj⟩]
  exact ⟨_, castElt_castElt_of_eq hf.symm _⟩

theorem stmt57 (pk : MLDSA44.PublicKey44) (j : ℕ) (hj : j < 1024) :
    ∃ n : ℕ, (castElt (b := 0) (ROMParams.stmtOfKey pk 57 j) : (interp 0).K) = n := by
  have hf : Pg.valueField 57 = 0 := by decide +kernel
  unfold ROMParams.stmtOfKey ROMParams.stmtOfKeyWith
  rw [dif_neg (by omega), dif_pos ⟨rfl, hj⟩]
  exact ⟨_, castElt_castElt_of_eq hf.symm _⟩

set_option maxRecDepth 8192

/-- The committed source values' classes, decided. -/
theorem cell_classes : (List.range Pg.values.length).all (fun v =>
    !Pg.isCellValue (Pg.value v).domain v || !decide (Pg.IsSourceValue v) ||
      (Pg.valueField v == 1 && (Pg.value v).node.map (·.name) == some "GF(2^16)" &&
        ((ROMParams.wordsOwner? v).isSome || [70, 120, 558, 561, 563, 564, 565, 566].contains v)) ||
      (Pg.valueField v == 1 && (Pg.value v).node.map (·.name) == some "bit" &&
        [68, 69, 557, 562].contains v) ||
      (Pg.valueField v == 0 && (Pg.value v).node.map (·.name) == some "GF(p^1)" &&
        (ROMParams.AValues.contains v || v == 568))) = true := by
  decide +kernel

/-- Only the blind is a pad copy, decided. -/
theorem padCopy_only : (List.range Pg.values.length).all (fun w => w == 568 ||
    match (Pg.value w).kind with
    | .padCopy _ _ => false
    | _ => true) = true := by
  decide +kernel

/-- The node-typed values that are not late, decided. -/
theorem typed_classes : (List.range Pg.values.length).all (fun v =>
    !((Pg.value v).typeSource == .node) || decide (Pg.IsLate v) ||
      ((match (Pg.value v).kind with
        | .bits w _ => (match (Pg.value w).kind with
          | .priv => true
          | _ => false)
        | _ => false) && (Pg.value v).type == .bit) ||
      (Pg.privCellB v && Pg.isCellValue (Pg.value v).domain v &&
        (match (Pg.value v).type with
          | .sub S => (Pg.value v).node.map (·.name) == some S
          | .bit => (Pg.value v).node.map (·.name) == some "bit" && Pg.valueField v == 1
          | .field => true))) = true := by
  decide +kernel

/-- The program declares no statement bound. -/
theorem noBounds : Pg.declaredRanges = [] := by decide +kernel

/-- **`MLDSA44.Native.ROMParams`'s facts of the honest strategy** (`MldsaNativeHonest`), decided. -/
noncomputable instance honest : ROMParams.MldsaNativeHonest Pg RealizedProgram.fq6 gf128 where
  PN := PN
  noBounds := noBounds
  mac := mac
  macW := 128
  stmtOfKey := ROMParams.stmtOfKey
  bound := Generated.MLDSA44.Native.ROMParams.Realize.derivable.elim fun _ hD => hD.bound
  wellFormed := Generated.MLDSA44.Native.ROMParams.Valid.wellFormed
  registered := ROMParams.interpModel.registered
  lawful := ROMParams.interpModel.lawful
  macModel := ROMParams.interpModel.macModel
  keyOf := ROMParams.keyOf_stmtOfKey
  stmt56 := stmt56
  stmt57 := stmt57
  stmt67 := stmt67
  checks := by decide +kernel
  realPreds := by decide +kernel
  kinds5657 := ⟨rfl, rfl⟩
  a_cells := by decide +kernel
  a_kinds := ⟨rfl, rfl, rfl⟩
  a_bound := by decide +kernel
  blind_cells := blind_cells
  predicates_length := by decide +kernel
  len7 := by decide +kernel
  cross_vals := by decide +kernel
  hb := hb
  mac_shape := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  crossMac p hp dx x dy y k real' hb' := by
    obtain ⟨q, hq, rfl⟩ := exists_index_of_mem hp
    have := List.all_eq_true.1 cross_only q (List.mem_range.2 hq)
    rw [hb'] at this
    simp only [beq_iff_eq, Bool.or_false] at this
    subst this
    rfl
  cell_classes := cell_classes
  padCopy_only := padCopy_only
  typed_classes := typed_classes

end GordieHowe.MLDSA44.Native.ROMParams.Honest
