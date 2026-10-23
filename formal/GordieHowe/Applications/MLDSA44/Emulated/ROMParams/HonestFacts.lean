-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Emulated.ROMParams.Honest
public import GordieHowe.Applications.MLDSA44.Emulated.HonestFull
public import GordieHowe.Applications.MLDSA44.Emulated.ROMParams.Setting
public import GordieHowe.Applications.MLDSA44.Emulated.ROMParams.Frontend.Basic
public import GordieHowe.Applications.MLDSA44.Emulated.ROMParams.Frontend.Algebra

@[expose] public section

/-!
# GordieHowe: the honest strategy's program facts of `MLDSA44.Emulated.ROMParams`

The program's instance of the honest strategy's class (`MldsaEmulatedHonest`) at its digit layout
(`GordieHowe.MLDSA44.Emulated.ROMParams.layout`), decided on the tables of
`GordieHowe.Generated.MLDSA44.Emulated.ROMParams.Program.program` (export `c825eb05`): the only cross-field
`equal` `mac.equal`, the blind's cells, the statement's values and the committed and node-typed
values' classes. The bound values' facts come from the realization condition
(`Realize.derivable`, `DerivationsValid.bound`).
-/

namespace GordieHowe.MLDSA44.Emulated.ROMParams.Honest

open RealizedProgram
open HashField (interp)

/-- **Goldilocks²'s prime subfield holds the naturals.** -/
instance : Emulated.MldsaANodes RealizedProgram.gold2 where
  natCast_mem n := by
    change (n : GoldilocksExt2) ∈ RealizedProgram.gold2Node "GF(p^1)"
    rw [RealizedProgram.gold2Node, if_pos rfl]
    have h : (n : GoldilocksExt2) ∈ Set.range (algebraMap (ZMod pGold) GoldilocksExt2) :=
      ⟨n, map_natCast _ n⟩
    rw [GordieHowe.range_algebraMap_eq_fixedField] at h
    exact h

/-- The native program's domain `H` honest facts at the emulated program's native program. -/
instance : Native.ROMParams.MldsaHHonest (Emulated.MldsaEmbed.nat Pg) :=
  inferInstanceAs (Native.ROMParams.MldsaHHonest Generated.MLDSA44.Native.ROMParams.Program.program)

/-- The native program's selection facts at the emulated program's native program. -/
instance : Native.ROMParams.MldsaHSelHonest (Emulated.MldsaEmbed.nat Pg) :=
  inferInstanceAs (Native.ROMParams.MldsaHSelHonest Generated.MLDSA44.Native.ROMParams.Program.program)

/-- The only cross-field `equal` is `mac.equal` (predicate `275`), decided. -/
theorem cross_only : (List.range Pg.predicates.length).all (fun q => q == 275 ||
    match (Pg.predicate q).body with
    | .cross _ _ _ _ _ _ => false
    | _ => true) = true := by
  decide +kernel

/-- The blind's cells, decided. -/
theorem blind_cells : (Pg.value 569).kind = .padCopy 572 "polynomialBits" ∧
    (Pg.value 569).domain < Pg.domains.length ∧
    (∀ j < 128, CellKey.val 569 j ∈ Pg.cellKeys (Pg.value 569).domain) ∧
    Pg.valueField 569 = 0 ∧ (Pg.value 569).size = 128 :=
  ⟨kind_of_isPadCopyB (by decide +kernel), by decide +kernel,
    fun j hj => (Pg.mem_cellKeys_val).2 ⟨by decide +kernel, by decide +kernel,
      by have : (Pg.value 569).size = 128 := by decide +kernel
         omega⟩, by decide +kernel, by decide +kernel⟩

/-! ## The program's instance of the honest strategy's class -/

/-- A value read in the field it was cast to and back is itself. -/
theorem castElt_back {a b : ℕ} (h : b = a) (x : (interp a).K) :
    castElt (b := a) (castElt (a := a) (b := b) x) = x := by
  subst h
  simp

theorem stmt68 (pk : MLDSA44.PublicKey44) (j : ℕ) (hj : j < 512) :
    (castElt (b := 1) (ROMParams.stmtOfKey pk 68 j) : (interp 1).K) =
      Bits.constBit (MLDSA44.PoP.Compose.trOf pk ⟨j / 8, by omega⟩).toNat (j % 8) := by
  unfold ROMParams.stmtOfKey ROMParams.stmtOfKeyWith
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos ⟨rfl, hj⟩]
  exact castElt_back (by decide +kernel) _

set_option maxRecDepth 8192

/-- The committed source values' classes, decided. -/
theorem cell_classes : (List.range Pg.values.length).all (fun v =>
    !Pg.isCellValue (Pg.value v).domain v || !decide (Pg.IsSourceValue v) ||
      (Pg.valueField v == 1 && (Pg.value v).node.map (·.name) == some "GF(2^16)" &&
        decide (1 ≤ v) && decide (v - 1 ∈ Emulated.hV) &&
        ((Native.ROMParams.wordsOwner? (v - 1)).isSome ||
          [70, 120, 558, 561, 563, 564, 565, 566].contains (v - 1))) ||
      (Pg.valueField v == 1 && (Pg.value v).node.map (·.name) == some "bit" &&
        decide (1 ≤ v) && decide (v - 1 ∈ Emulated.hV) && [68, 69, 557, 562].contains (v - 1)) ||
      (Pg.valueField v == 0 && (Pg.value v).node.map (·.name) == some "GF(p^1)" &&
        ((Emulated.aValues ROMParams.layout).contains v || v == 569))) = true := by
  decide +kernel

/-- Only the blind is a pad copy, decided. -/
theorem padCopy_only : (List.range Pg.values.length).all (fun w => w == 569 ||
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

end GordieHowe.MLDSA44.Emulated.ROMParams.Honest

namespace GordieHowe.MLDSA44.Emulated.ROMParams

open RealizedProgram
open Honest

/-- **The statement of an honest input**: its key and context, whose `ExpandA` finishes within the
byte budget since its signature verifies. -/
def keyStmtOf (i : MLDSA44.HonestInput) : KeyStmt :=
  ⟨i.y.pk, i.valid.verify.expandA⟩

set_option maxRecDepth 8192 in
/-- **`MLDSA44.Emulated.ROMParams`'s facts of the honest strategy** (`MldsaEmulatedHonest`), decided. -/
noncomputable instance honest :
    Emulated.MldsaEmulatedHonest Pg RealizedProgram.gold2 gf128 where
  stmtOfKey := stmtOfKey
  PN := PN
  bound := Generated.MLDSA44.Emulated.ROMParams.Realize.derivable.elim fun _ hD => hD.bound
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
  wFits := ⟨by decide, by decide⟩
  zFits := ⟨by decide, by decide⟩
  offsetFits := ⟨by decide, by decide⟩
  slackFits := ⟨by decide, by decide⟩
  offsetRoom := by decide
  mac := mac
  macW := 128
  wellFormed := Generated.MLDSA44.Emulated.ROMParams.Valid.wellFormed
  registered := interpModel.registered
  lawful := interpModel.lawful
  macModel := interpModel.macModel
  bounded i := stmtOf_eq (keyStmtOf i) ▸ stmtBounded_stmtOf (keyStmtOf i)
  checks := by decide +kernel
  realPreds := by decide +kernel
  blind_cells := blind_cells
  predicates_length := by decide +kernel
  len6 := by decide +kernel
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

end GordieHowe.MLDSA44.Emulated.ROMParams
