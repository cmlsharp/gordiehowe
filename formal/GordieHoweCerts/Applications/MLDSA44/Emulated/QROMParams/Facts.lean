-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Generated.MLDSA44.Emulated.QROMParams.Certified
public import GordieHoweCerts.Applications.MLDSA44.Emulated.HonestFull
public import GordieHoweCerts.Applications.MLDSA44.Emulated.QROMParams.Setting
public import GordieHoweCerts.Applications.MLDSA44.Emulated.QROMParams.Frontend.Basic
public import GordieHoweCerts.Applications.MLDSA44.Native.QROMParams.Facts
public import GordieHoweCerts.Applications.MLDSA44.Emulated.QROMParams.SourceRoleCoverage
public import GordieHoweCerts.Applications.MLDSA44.Emulated.QROMParams.SourceCellCoverage
public import GordieHoweCerts.Applications.MLDSA44.Emulated.QROMParams.DigitFacts

@[expose] public section

/-!
# GordieHowe: the checked honest facts of `MLDSA44.Emulated.QROMParams`

The program's instance of the honest strategy's class (`MldsaEmulatedHonest`) at its digit layout
(`GordieHowe.MLDSA44.Emulated.QROMParams.layout`), on the tables of
`GordieHowe.Generated.MLDSA44.Emulated.QROMParams.Program.program`: the crossing `mac.equal` and the operands of every cross-field
`equal`, the statement's values and the committed source cells' classes. These read the program's
gadgets by index; the program-wide facts the honest strategy reads are its honest roles
(`GordieHowe.ProgramConditions.roles`). The bound values' facts come from the realization condition
(`GordieHowe.CoreConditions.derivable`, `DerivationsValid.bound`).
-/

namespace GordieHowe.MLDSA44.Emulated.QROMParams.Honest

open RealizedProgram
open Generated.MLDSA44.Emulated.QROMParams (interp)
open Generated.MLDSA44.Emulated.QROMParams (conditions)

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

theorem stmt68 (pk : MLDSA44.PublicKey44) (j : ℕ) (hj : j < 512) :
    (castElt (b := 1) (QROMParams.stmtOfKey pk 67 j) : (interp 1).K) =
      Bits.constBit (MLDSA44.PoP.Compose.trOf pk ⟨j / 8, by omega⟩).toNat (j % 8) := by
  unfold QROMParams.stmtOfKey QROMParams.stmtOfKeyWith
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos ⟨rfl, hj⟩]
  exact castElt_back (by shape_decide) _

/-- Each digit of the layout is a committed cell with the witness's size and field. -/
theorem digit_cells {u : ℕ} (hu : u ∈ QROMParams.layout.digitValues) :
    Pg.privCellB u = true ∧ (Pg.value u).size = 1024 ∧ Pg.valueField u = 0 := by
  change u ∈ [577, 578, 579, 580, 584, 585, 586, 587] at hu
  have hw : u ∈ [577, 578] ∨ u ∈ [579, 580] ∨ u ∈ [584, 585] ∨ u ∈ [586, 587] := by
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] using hu
  rcases hw with h | h | h | h
  · exact DigitFacts.w_cells h
  · exact DigitFacts.z_cells h
  · exact DigitFacts.offset_cells h
  · exact DigitFacts.slack_cells h

/-- The committed source cells' classes from checked source-role coverage. -/
theorem cell_classes : (List.range Pg.values.length).all (fun v =>
    !Pg.privCellB v || !decide (Pg.IsSourceValue v) ||
      (Pg.valueField v == 1 && (Pg.value v).node.map (·.name) == some "GF(2^16)" &&
        (Emulated.eOf Pg v).any fun u => (MLDSA44.wordsOwner? u).isSome ||
          [69, 119, 557, 560, 562, 563, 564, 565].contains u) ||
      (Pg.valueField v == 1 && (Pg.value v).node.map (·.name) == some "bit" &&
        (Emulated.eOf Pg v).any fun u => [67, 68, 556, 561].contains u) ||
      (Pg.valueField v == 0 && (Pg.value v).node.map (·.name) == some "GF(p^1)" &&
        (Emulated.aValues QROMParams.layout).contains v)) = true :=
  SourceCellCoverage.cell_classes

end GordieHowe.MLDSA44.Emulated.QROMParams.Honest

namespace GordieHowe.MLDSA44.Emulated.QROMParams

open RealizedProgram
open Generated.MLDSA44.Emulated.QROMParams (interp)
open Generated.MLDSA44.Emulated.QROMParams (conditions)
open Honest

/-- **The statement of an honest input**: its key and context, whose `ExpandA` finishes within the
byte budget since its signature verifies. -/
def keyStmtOf (i : MLDSA44.HonestInput) : KeyStmt :=
  ⟨i.y.pk, i.valid.verify.expandA⟩

/-- **`MLDSA44.Emulated.QROMParams`'s facts of the honest strategy** (`MldsaEmulatedHonest`), supplied by checked facts. -/
noncomputable instance honest :
    Emulated.MldsaEmulatedHonest Pg RealizedProgram.gold4 gf256 where
  stmtOfKey := stmtOfKey
  PN := PN
  bound := conditions.derivable.elim fun _ hD => hD.bound
  keyOf := keyOf_stmtOfKey
  stmt68 := Honest.stmt68
  hCells := SourceRoleCoverage.hCells
    (by rw [Generated.MLDSA44.Native.QROMParams.SourceRoles.roles_eq]; decide +kernel)
    Pg embedding conditions.wellFormed
  eOf_val := by decide +kernel
  a_nodup := by decide +kernel
  a_cells := by
    intro v hv
    change v ∈ [59, 60, 63, 64] ++ QROMParams.layout.digitValues at hv
    rcases List.mem_append.mp hv with h | h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl
      · exact ⟨conditions.wellFormed.privCellB_of_kind_priv Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.value_h_header.1 Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.value_h_kind, Reads.field59⟩
      · exact ⟨conditions.wellFormed.privCellB_of_kind_priv Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.value_challenge_2ec_header.1 Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.value_challenge_2ec_kind, Reads.field60⟩
      · exact ⟨conditions.wellFormed.privCellB_of_kind_priv Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.value_hint_2ew1_header.1 Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.value_hint_2ew1_kind, Reads.field63⟩
      · exact ⟨conditions.wellFormed.privCellB_of_kind_priv Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.value_hint_2enonpositive_header.1 Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.value_hint_2enonpositive_kind, Reads.field64⟩
    · exact ⟨(digit_cells h).1, (digit_cells h).2.2⟩
  kind59 := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.value_z_kind
  kind62 := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.value_signature_2ew_kind
  kind66 := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.value_hint_2eoffset_kind
  kind67 := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.value_hint_2eslack_kind
  boundVals := by shape_decide
  digitSizes := fun _ h => (digit_cells h).2.1
  size60 := by shape_decide
  size61 := by shape_decide
  size64 := by shape_decide
  size65 := by shape_decide
  wFits := ⟨by decide, by decide, by decide⟩
  zFits := ⟨by decide, by decide, by decide⟩
  offsetFits := ⟨by decide, by decide, by decide⟩
  slackFits := ⟨by decide, by decide, by decide⟩
  offsetRoom := by decide
  wellFormed := conditions.wellFormed
  registered := conditions.model.registered
  lawful := conditions.model.lawful
  macModel := conditions.model.macModel
  bounded i := stmtOf_eq (keyStmtOf i) ▸ stmtBounded_stmtOf (keyStmtOf i)
  checks := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.statement_checks
  realPreds := by
    unfold emulatedRealizationPreds
    shape_decide
  coverage := by
    -- The held pairs land on the run `20 … 272`, decided once as a list; the 23 predicates
    -- outside it are decided one by one against the short cases.
    have hheld : ∀ p ∈ Emulated.MldsaEmbed.held Pg, hPredLo ≤ p.1 ∧ p.1 ≤ hPredHi := by
      decide +kernel
    have htgt : (Emulated.MldsaEmbed.held Pg).map Prod.snd = List.range' 20 253 := by
      decide +kernel
    intro q hq
    rw [Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.predicates_length] at hq
    by_cases h : 20 ≤ q ∧ q < 273
    · left
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (htgt ▸ List.mem_range'_1.2 ⟨h.1, by omega⟩)
      exact ⟨p, hp, rfl, hheld p hp⟩
    · right
      have hm : q ∈ List.range 20 ++ [273, 274, 275] := by
        simp only [List.mem_append, List.mem_range, List.mem_cons, List.not_mem_nil]
        omega
      clear h hq
      revert q
      decide +kernel
  len6 := Reads.lenRef6
  macReal := macReal
  hb := by
    rw [show (Emulated.MldsaEmbed.σ Pg).ref 525 = 527 from ref525]
    change (Pg.predicate 275).body = _
    obtain ⟨c, h⟩ := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.predicate_mac_2eequal_body
    have hm : macReal = c := by simp only [macReal, Pg, h]
    rw [h, hm]
  crossOperands := by
    rw [show (Emulated.MldsaEmbed.σ Pg).ref 525 = 527 from ref525]
    apply crossOperandsB_of_operands
    intro p hp dx x dy y k real hb
    obtain ⟨q, hq, hqp⟩ := exists_index_of_mem hp
    have hc : (Pg.predicate q).body.isCross = true := by rw [hqp, hb]; rfl
    have hm := mem_crossPredicateIds_iff.mpr ⟨hq, hc⟩
    rw [Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.cross_predicates] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst q
    obtain ⟨r, hr⟩ := Generated.MLDSA44.Emulated.QROMParams.ShapeFacts.predicate_mac_2eequal_body
    rw [hqp, hb] at hr
    cases hr
    exact ⟨rfl, rfl, rfl, rfl⟩
  cell_classes := cell_classes

end GordieHowe.MLDSA44.Emulated.QROMParams
