-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Native.HonestFull
public import GordieHoweCerts.Applications.MLDSA44.Native.ROMParams.Setting
public import GordieHowe.Applications.MLDSA44.Frontend.QField
public import GordieHoweCerts.Applications.MLDSA44.Native.ROMParams.SourceRoleCoverage

public section

/-!
# Checked honest facts for `MLDSA44.Native.ROMParams`

The existing honest-strategy interfaces are supplied by named shape facts, completion checks,
and source-role coverage. Generated Program and Plan definitions are opaque here. Hash and
selection instances consume the separate checked word facts; no program table is evaluated.
-/

namespace GordieHowe.MLDSA44.Native.ROMParams.Honest


open RealizedProgram
open Generated.MLDSA44.Native.ROMParams (interp)
open Generated.MLDSA44.Native.ROMParams (conditions)
open Generated.MLDSA44.Native.ROMParams.ShapeFacts

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

theorem stmt67 (pk : MLDSA44.PublicKey44) (j : ℕ) (hj : j < 512) :
    (castElt (b := 1) (ROMParams.stmtOfKey pk 66 j) : (interp 1).K) =
      Bits.constBit (MLDSA44.PoP.Compose.trOf pk ⟨j / 8, by omega⟩).toNat (j % 8) := by
  have hf : Pg.valueField 66 = 1 := valueShape_field value_tr_header.2
  rw [ROMParams.stmtOfKey_apply, ROMParams.stmtOfKeyWith_apply]
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos ⟨rfl, hj⟩]
  exact castElt_castElt_of_eq hf.symm _

theorem stmt56 (pk : MLDSA44.PublicKey44) (j : ℕ) (hj : j < 4096) :
    ∃ n : ℕ, (castElt (b := 0) (ROMParams.stmtOfKey pk 55 j) : (interp 0).K) = n := by
  have hf : Pg.valueField 55 = 0 := valueShape_field value_key_2ea_5fhat_header.2
  rw [ROMParams.stmtOfKey_apply, ROMParams.stmtOfKeyWith_apply]
  rw [dif_pos ⟨rfl, hj⟩]
  exact ⟨_, castElt_castElt_of_eq hf.symm _⟩

theorem stmt57 (pk : MLDSA44.PublicKey44) (j : ℕ) (hj : j < 1024) :
    ∃ n : ℕ, (castElt (b := 0) (ROMParams.stmtOfKey pk 56 j) : (interp 0).K) = n := by
  have hf : Pg.valueField 56 = 0 := valueShape_field value_key_2et1_header.2
  rw [ROMParams.stmtOfKey_apply, ROMParams.stmtOfKeyWith_apply]
  rw [dif_neg (by omega), dif_pos ⟨rfl, hj⟩]
  exact ⟨_, castElt_castElt_of_eq hf.symm _⟩

/-- The committed source cells' classes from checked source-role coverage. -/
theorem cell_classes : (List.range Pg.values.length).all (fun v =>
    !Pg.privCellB v || !decide (Pg.IsSourceValue v) ||
      (Pg.valueField v == 1 && (Pg.value v).node.map (·.name) == some "GF(2^16)" &&
        ((MLDSA44.wordsOwner? v).isSome || [69, 119, 557, 560, 562, 563, 564, 565].contains v)) ||
      (Pg.valueField v == 1 && (Pg.value v).node.map (·.name) == some "bit" &&
        [67, 68, 556, 561].contains v) ||
      (Pg.valueField v == 0 && (Pg.value v).node.map (·.name) == some "GF(p^1)" &&
        Native.AValues.contains v)) = true := SourceRoleCoverage.cell_classes

/-- The program declares no statement bound. -/
theorem noBounds : Pg.declaredRanges = [] := statement_ranges

/-- Completion supplies the cell property for generated node-typed digits. -/
private theorem generatedCell {v owner : Nat} {header : ValueShape}
    (hh : v < Pg.values.length ∧ Pg.valueShape v = header)
    (ht : header.typeSource = .node) (hp : header.phase = 0)
    (hr : header.role = .realization owner) : Pg.privCellB v = true := by
  have hc := realTypeB_of_completionB conditions.completion hh.1
  exact privCellB_of_realTypeB Pg hc ((valueShape_typeSource hh.2).trans ht)
    (Pg.not_IsLate_of_phase_zero ((valueShape_phase hh.2).trans hp))
    (Pg.not_IsSourceValue_of_realization ((valueShape_role hh.2).trans hr))

/-- **`MLDSA44.Native.ROMParams`'s facts of the honest strategy** (`MldsaNativeHonest`), supplied by checked facts. -/
noncomputable instance honest : Native.MldsaNativeHonest Pg RealizedProgram.fq6 gf128 where
  PN := PN
  noBounds := noBounds
  stmtOfKey := ROMParams.stmtOfKey
  bound := conditions.derivable.elim fun _ hD => hD.bound
  wellFormed := conditions.wellFormed
  registered := conditions.model.registered
  lawful := conditions.model.lawful
  macModel := conditions.model.macModel
  keyOf := ROMParams.keyOf_stmtOfKey
  stmt56 := stmt56
  stmt57 := stmt57
  stmt67 := stmt67
  checks := statement_checks
  realPreds := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Pg.inSource_of_realization predicate_mac_2eA_role.2
    · exact Pg.inSource_of_realization predicate_range_2enorm_2ez_2etop_role.2
    · exact Pg.inSource_of_type_realization predicate_mac_2eblind_2eboolean_role.2
        (valueShape_role value_mac_2eblind_header.2)
    · exact Pg.inSource_of_realization predicate_mac_2elow_role.2
    · exact Pg.inSource_of_realization predicate_mac_2ehigh_role.2
    · exact Pg.inSource_of_realization predicate_mac_2enowrap_role.2
    · exact Pg.inSource_of_realization predicate_mac_role.2
  kinds5657 := ⟨Generated.MLDSA44.Native.ROMParams.ShapeFacts.value_key_2ea_5fhat_kind, Generated.MLDSA44.Native.ROMParams.ShapeFacts.value_key_2et1_kind⟩
  a_cells := by
    intro v hv
    change v ∈ [58, 59, 60, 62, 63, 575, 576, 580, 581, 582, 583] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨conditions.wellFormed.privCellB_of_kind_priv value_h_header.1 value_h_kind, valueShape_field value_h_header.2⟩
    · exact ⟨conditions.wellFormed.privCellB_of_kind_priv value_challenge_2ec_header.1 value_challenge_2ec_kind, valueShape_field value_challenge_2ec_header.2⟩
    · exact ⟨conditions.wellFormed.privCellB_of_kind_priv value_signature_2ew_header.1 value_signature_2ew_kind, valueShape_field value_signature_2ew_header.2⟩
    · exact ⟨conditions.wellFormed.privCellB_of_kind_priv value_hint_2ew1_header.1 value_hint_2ew1_kind, valueShape_field value_hint_2ew1_header.2⟩
    · exact ⟨conditions.wellFormed.privCellB_of_kind_priv value_hint_2enonpositive_header.1 value_hint_2enonpositive_kind, valueShape_field value_hint_2enonpositive_header.2⟩
    · exact ⟨generatedCell value_z_2edigit_2elow_header rfl rfl rfl, valueShape_field value_z_2edigit_2elow_header.2⟩
    · exact ⟨generatedCell value_z_2edigit_2ehigh_header rfl rfl rfl, valueShape_field value_z_2edigit_2ehigh_header.2⟩
    · exact ⟨generatedCell value_hint_2eoffset_2edigit_2elow_header rfl rfl rfl, valueShape_field value_hint_2eoffset_2edigit_2elow_header.2⟩
    · exact ⟨generatedCell value_hint_2eoffset_2edigit_2ehigh_header rfl rfl rfl, valueShape_field value_hint_2eoffset_2edigit_2ehigh_header.2⟩
    · exact ⟨generatedCell value_hint_2eslack_2edigit_2elow_header rfl rfl rfl, valueShape_field value_hint_2eslack_2edigit_2elow_header.2⟩
    · exact ⟨generatedCell value_hint_2eslack_2edigit_2ehigh_header rfl rfl rfl, valueShape_field value_hint_2eslack_2edigit_2ehigh_header.2⟩
  a_kinds := ⟨Generated.MLDSA44.Native.ROMParams.ShapeFacts.value_z_kind, Generated.MLDSA44.Native.ROMParams.ShapeFacts.value_hint_2eoffset_kind, Generated.MLDSA44.Native.ROMParams.ShapeFacts.value_hint_2eslack_kind⟩
  a_bound := by
    refine ⟨valueShape_field value_z_header.2, valueShape_field value_hint_2eoffset_header.2, valueShape_field value_hint_2eslack_header.2, value_z_header.1, value_hint_2eoffset_header.1, value_hint_2eslack_header.1, ?_, valueShape_size value_h_header.2, valueShape_size value_challenge_2ec_header.2, valueShape_size value_signature_2ew_header.2, valueShape_size value_hint_2ew1_header.2, valueShape_size value_hint_2enonpositive_header.2, valueShape_size value_z_2ecompletion_2elow_header.2, valueShape_size value_z_2ecompletion_2ehigh_header.2, valueShape_size value_range_2estatic_3aA_2e512_header.2⟩
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact valueShape_size value_z_2edigit_2elow_header.2
    · exact valueShape_size value_z_2edigit_2ehigh_header.2
    · exact valueShape_size value_hint_2eoffset_2edigit_2elow_header.2
    · exact valueShape_size value_hint_2eoffset_2edigit_2ehigh_header.2
    · exact valueShape_size value_hint_2eslack_2edigit_2elow_header.2
    · exact valueShape_size value_hint_2eslack_2edigit_2ehigh_header.2
  predicates_length := predicates_length
  len7 := by
    have hk : Pg.expr 7 ≠ default := by
      rw [expr_mac_2eequal_2eshape_2eright_eq]
      decide
    rw [exprLen_ref conditions.wellFormed.refsOrdered (expr_lt_of_ne_default hk),
      expr_mac_2eequal_2eshape_2eright_eq, exprLen_reindex,
      Generated.MLDSA44.Native.ROMParams.Program.idx10_eq]
    decide
  macReal := macReal
  hb := by
    obtain ⟨c, h⟩ := Generated.MLDSA44.Native.ROMParams.ShapeFacts.predicate_mac_2eequal_body
    have hm : macReal = c := by simp only [macReal, Pg, h]
    rw [h, hm]
  crossOperands := by
    apply crossOperandsB_of_operands
    intro p hp dx x dy y k real hb
    obtain ⟨q, hq, hqp⟩ := exists_index_of_mem hp
    have hc : (Pg.predicate q).body.isCross = true := by rw [hqp, hb]; rfl
    have hm := mem_crossPredicateIds_iff.mpr ⟨hq, hc⟩
    rw [cross_predicates] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    subst q
    obtain ⟨r, hr⟩ := predicate_mac_2eequal_body
    rw [hqp, hb] at hr
    cases hr
    exact ⟨rfl, rfl, rfl, rfl⟩
  cell_classes := cell_classes

end GordieHowe.MLDSA44.Native.ROMParams.Honest
