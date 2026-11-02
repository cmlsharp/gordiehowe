-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Generated.MLDSA44.Native.ROMParams.Realize
public import GordieHowe.Applications.MLDSA44.Native.HonestFull
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Setting
public import GordieHowe.Applications.MLDSA44.Frontend.QField

@[expose] public section

/-!
# GordieHowe: the gadget facts of `MLDSA44.Native.ROMParams`

The program's instance of the honest strategy's class (`MldsaNativeHonest`) and its hash and
SampleInBall facts, on the tables of `GordieHowe.Generated.MLDSA44.Native.ROMParams.Program.program`:
the crossing `mac.equal` and the operands of every cross-field `equal`, the statement's values and
the committed source cells' classes. These read the program's gadgets by index; the program-wide
facts the honest strategy reads are its honest roles (`Completion.rolesOk`). The bound values' facts
come from the realization condition (`Realize.derivable`, `DerivationsValid.bound`).
-/

namespace GordieHowe.MLDSA44.Native.ROMParams.Honest

open RealizedProgram
open Generated.MLDSA44.Native.ROMParams (interp)
open Generated.MLDSA44.Native.ROMParams.Facts (interpModel)

/-- **The realized program.** -/
noncomputable abbrev Pg : RealizedProgram := Generated.MLDSA44.Native.ROMParams.Program.program

/-- **The realized program's prime-subfield nodes.** -/
noncomputable abbrev PN : ℕ → List String :=
  primeNodesOf Generated.MLDSA44.Native.ROMParams.Plan.plan Generated.MLDSA44.Native.ROMParams.Program.program

/-- **The MAC realization** of `mac.equal` (predicate `272`). -/
noncomputable def macReal : MacRealization :=
  match (Pg.predicate 272).body with
  | .cross _ _ _ _ _ r => r
  | _ => default

/-! ## The program's instance of the honest strategy's class -/

-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
theorem stmt67 (pk : MLDSA44.PublicKey44) (j : ℕ) (hj : j < 512) :
    (castElt (b := 1) (ROMParams.stmtOfKey pk 66 j) : (interp 1).K) =
      Bits.constBit (MLDSA44.PoP.Compose.trOf pk ⟨j / 8, by omega⟩).toNat (j % 8) := by
  have hf : Pg.valueField 66 = 1 := by decide +kernel
  unfold ROMParams.stmtOfKey ROMParams.stmtOfKeyWith
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos ⟨rfl, hj⟩]
  exact castElt_castElt_of_eq hf.symm _

-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
theorem stmt56 (pk : MLDSA44.PublicKey44) (j : ℕ) (hj : j < 4096) :
    ∃ n : ℕ, (castElt (b := 0) (ROMParams.stmtOfKey pk 55 j) : (interp 0).K) = n := by
  have hf : Pg.valueField 55 = 0 := by decide +kernel
  unfold ROMParams.stmtOfKey ROMParams.stmtOfKeyWith
  rw [dif_pos ⟨rfl, hj⟩]
  exact ⟨_, castElt_castElt_of_eq hf.symm _⟩

-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
theorem stmt57 (pk : MLDSA44.PublicKey44) (j : ℕ) (hj : j < 1024) :
    ∃ n : ℕ, (castElt (b := 0) (ROMParams.stmtOfKey pk 56 j) : (interp 0).K) = n := by
  have hf : Pg.valueField 56 = 0 := by decide +kernel
  unfold ROMParams.stmtOfKey ROMParams.stmtOfKeyWith
  rw [dif_neg (by omega), dif_pos ⟨rfl, hj⟩]
  exact ⟨_, castElt_castElt_of_eq hf.symm _⟩

set_option maxRecDepth 8192

-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- The committed source cells' classes, decided. -/
theorem cell_classes : (List.range Pg.values.length).all (fun v =>
    !Pg.privCellB v || !decide (Pg.IsSourceValue v) ||
      (Pg.valueField v == 1 && (Pg.value v).node.map (·.name) == some "GF(2^16)" &&
        ((MLDSA44.wordsOwner? v).isSome || [69, 119, 557, 560, 562, 563, 564, 565].contains v)) ||
      (Pg.valueField v == 1 && (Pg.value v).node.map (·.name) == some "bit" &&
        [67, 68, 556, 561].contains v) ||
      (Pg.valueField v == 0 && (Pg.value v).node.map (·.name) == some "GF(p^1)" &&
        Native.AValues.contains v)) = true := by
  decide +kernel

-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- The program declares no statement bound. -/
theorem noBounds : Pg.declaredRanges = [] := by decide +kernel

-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- **`MLDSA44.Native.ROMParams`'s facts of the honest strategy** (`MldsaNativeHonest`), decided. -/
noncomputable instance honest : Native.MldsaNativeHonest Pg RealizedProgram.fq6 gf128 where
  PN := PN
  noBounds := noBounds
  stmtOfKey := ROMParams.stmtOfKey
  bound := Generated.MLDSA44.Native.ROMParams.Realize.derivable.elim fun _ hD => hD.bound
  wellFormed := Generated.MLDSA44.Native.ROMParams.Valid.wellFormed
  registered := interpModel.registered
  lawful := interpModel.lawful
  macModel := interpModel.macModel
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
  predicates_length := by decide +kernel
  len7 := by decide +kernel
  macReal := macReal
  hb := rfl
  crossOperands := by decide +kernel
  cell_classes := cell_classes

end GordieHowe.MLDSA44.Native.ROMParams.Honest
