-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Generated.MLDSA44.Emulated.QROMParams.Realize
public import GordieHowe.Applications.MLDSA44.Emulated.HonestFull
public import GordieHowe.Applications.MLDSA44.Emulated.QROMParams.Setting
public import GordieHowe.Applications.MLDSA44.Emulated.QROMParams.Frontend.Basic
public import GordieHowe.Applications.MLDSA44.Native.QROMParams.GadgetFacts

@[expose] public section

/-!
# GordieHowe: the gadget facts of `MLDSA44.Emulated.QROMParams`

The program's instance of the honest strategy's class (`MldsaEmulatedHonest`) at its digit layout
(`GordieHowe.MLDSA44.Emulated.QROMParams.layout`), on the tables of
`GordieHowe.Generated.MLDSA44.Emulated.QROMParams.Program.program`: the crossing `mac.equal` and the operands of every cross-field
`equal`, the statement's values and the committed source cells' classes. These read the program's
gadgets by index; the program-wide facts the honest strategy reads are its honest roles
(`Completion.rolesOk`). The bound values' facts come from the realization condition
(`Realize.derivable`, `DerivationsValid.bound`).
-/

namespace GordieHowe.MLDSA44.Emulated.QROMParams.Honest

open RealizedProgram
open Generated.MLDSA44.Emulated.QROMParams (interp)
open Generated.MLDSA44.Emulated.QROMParams.Facts (interpModel)

/-- **The realized program.** -/
noncomputable abbrev Pg : RealizedProgram := Generated.MLDSA44.Emulated.QROMParams.Program.program

/-- **The plan's prime-subfield nodes.** -/
noncomputable abbrev PN : ℕ → List String :=
  primeNodesOf Generated.MLDSA44.Emulated.QROMParams.Plan.plan Generated.MLDSA44.Emulated.QROMParams.Program.program

/-- **The MAC realization** of `mac.equal` (predicate `275`). -/
noncomputable def macReal : MacRealization :=
  match (Pg.predicate 275).body with
  | .cross _ _ _ _ _ r => r
  | _ => default

/-- **Goldilocks⁴'s prime subfield holds the naturals.** -/
instance : Emulated.MldsaANodes RealizedProgram.gold4 where
  natCast_mem n := by
    change (n : GoldilocksExt4) ∈ RealizedProgram.gold4Node "GF(p^1)"
    rw [RealizedProgram.gold4Node, if_pos rfl]
    have h : (n : GoldilocksExt4) ∈ Set.range (algebraMap (ZMod pGold) GoldilocksExt4) :=
      ⟨n, map_natCast _ n⟩
    rw [GordieHowe.range_algebraMap_eq_fixedField] at h
    exact h

/-- The native program's domain `H` honest facts at the emulated program's native program. -/
instance : MLDSA44.MldsaHHonest (Emulated.MldsaEmbed.nat Pg) :=
  inferInstanceAs (MLDSA44.MldsaHHonest Generated.MLDSA44.Native.QROMParams.Program.program)

/-- The native program's selection facts at the emulated program's native program. -/
instance : MLDSA44.MldsaHSelHonest (Emulated.MldsaEmbed.nat Pg) :=
  inferInstanceAs (MLDSA44.MldsaHSelHonest Generated.MLDSA44.Native.QROMParams.Program.program)

/-! ## The program's instance of the honest strategy's class -/

/-- A value read in the field it was cast to and back is itself. -/
theorem castElt_back {a b : ℕ} (h : b = a) (x : (interp a).K) :
    castElt (b := a) (castElt (a := a) (b := b) x) = x := by
  subst h
  simp

-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
theorem stmt68 (pk : MLDSA44.PublicKey44) (j : ℕ) (hj : j < 512) :
    (castElt (b := 1) (QROMParams.stmtOfKey pk 67 j) : (interp 1).K) =
      Bits.constBit (MLDSA44.PoP.Compose.trOf pk ⟨j / 8, by omega⟩).toNat (j % 8) := by
  unfold QROMParams.stmtOfKey QROMParams.stmtOfKeyWith
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos ⟨rfl, hj⟩]
  exact castElt_back (by decide +kernel) _

set_option maxRecDepth 8192

-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- The committed source values' classes, decided. -/
theorem cell_classes : (List.range Pg.values.length).all (fun v =>
    !Pg.privCellB v || !decide (Pg.IsSourceValue v) ||
      (Pg.valueField v == 1 && (Pg.value v).node.map (·.name) == some "GF(2^16)" &&
        decide (1 ≤ v) && decide (v - 1 ∈ Emulated.hV) &&
        ((MLDSA44.wordsOwner? (v - 1)).isSome ||
          [69, 119, 557, 560, 562, 563, 564, 565].contains (v - 1))) ||
      (Pg.valueField v == 1 && (Pg.value v).node.map (·.name) == some "bit" &&
        decide (1 ≤ v) && decide (v - 1 ∈ Emulated.hV) && [67, 68, 556, 561].contains (v - 1)) ||
      (Pg.valueField v == 0 && (Pg.value v).node.map (·.name) == some "GF(p^1)" &&
        (Emulated.aValues QROMParams.layout).contains v)) = true := by
  decide +kernel

end GordieHowe.MLDSA44.Emulated.QROMParams.Honest

namespace GordieHowe.MLDSA44.Emulated.QROMParams

open RealizedProgram
open Generated.MLDSA44.Emulated.QROMParams (interp)
open Generated.MLDSA44.Emulated.QROMParams.Facts (interpModel)
open Honest

/-- **The statement of an honest input**: its key and context, whose `ExpandA` finishes within the
byte budget since its signature verifies. -/
def keyStmtOf (i : MLDSA44.HonestInput) : KeyStmt :=
  ⟨i.y.pk, i.valid.verify.expandA⟩

set_option maxRecDepth 8192 in
-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- **`MLDSA44.Emulated.QROMParams`'s facts of the honest strategy** (`MldsaEmulatedHonest`), decided. -/
noncomputable instance honest :
    Emulated.MldsaEmulatedHonest Pg RealizedProgram.gold4 gf256 where
  stmtOfKey := stmtOfKey
  PN := PN
  bound := Generated.MLDSA44.Emulated.QROMParams.Realize.derivable.elim fun _ hD => hD.bound
  keyOf := keyOf_stmtOfKey
  stmt68 := Honest.stmt68
  hCells := by decide +kernel
  a_nodup := by decide +kernel
  a_cells := by decide +kernel
  kind59 := rfl
  kind62 := rfl
  kind66 := rfl
  kind67 := rfl
  boundVals := by decide +kernel
  digitSizes := by decide +kernel
  size60 := by decide +kernel
  size61 := by decide +kernel
  size64 := by decide +kernel
  size65 := by decide +kernel
  wFits := ⟨by decide, by decide, by decide⟩
  zFits := ⟨by decide, by decide, by decide⟩
  offsetFits := ⟨by decide, by decide, by decide⟩
  slackFits := ⟨by decide, by decide, by decide⟩
  offsetRoom := by decide
  wellFormed := Generated.MLDSA44.Emulated.QROMParams.Valid.wellFormed
  registered := interpModel.registered
  lawful := interpModel.lawful
  macModel := interpModel.macModel
  bounded i := stmtOf_eq (keyStmtOf i) ▸ stmtBounded_stmtOf (keyStmtOf i)
  checks := by decide +kernel
  realPreds := by decide +kernel
  predicates_length := by decide +kernel
  len6 := by decide +kernel
  macReal := macReal
  hb := rfl
  crossOperands := by decide +kernel
  cell_classes := cell_classes

end GordieHowe.MLDSA44.Emulated.QROMParams
