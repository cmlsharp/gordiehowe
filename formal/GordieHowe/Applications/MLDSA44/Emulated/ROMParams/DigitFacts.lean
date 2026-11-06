-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Generated.MLDSA44.Emulated.ROMParams.Certified
public import GordieHowe.Generated.MLDSA44.Emulated.ROMParams.ShapeFacts

public section

namespace GordieHowe.MLDSA44.Emulated.ROMParams.DigitFacts
open RealizedProgram
open Generated.MLDSA44.Emulated.ROMParams
open Program (program)
open ShapeFacts

/-- The checked completion records supply the existing bound-value interface. -/
private theorem bound_records : program.BoundRecs Cert.gens := by
  intro v hv hb
  exact program.boundRecsV_sound (boundRecsV_of_completionB conditions.completion hv) hb

/-- The checked completion predicates supply the existing generated-digit interface. -/
private theorem digit_lookups : program.DigitLookupsC Cert.gens := by
  intro q hq d rec N r hb hk hn
  exact digitLookupCB_noComm (digitLookupCB_of_completionB conditions.completion hq) hb hk hn

/-- The existing `w` bound expression's digits are committed cells with the witness size and field. -/
theorem w_cells {u : Nat} (hu : u ∈ [577, 578, 579]) :
    program.privCellB u = true ∧ (program.value u).size = 1024 ∧ program.valueField u = 0 := by
  have hf : program.valueField 61 = 0 := valueShape_field value_signature_2ew_header.2
  have hsz : (program.value 61).size = 1024 := valueShape_size value_signature_2ew_header.2
  have hfield : 0 < program.fields.length := by
    have h := valueField_lt conditions.wellFormed value_signature_2ew_header.1
    rwa [hf] at h
  have hchar : program.charOf 0 = 18446744069414584321 :=
    (conditions.model.registered.characteristic 0 hfield).symm
  have h := bound_digit_cells bound_records digit_lookups value_signature_2ew_header.1
    value_signature_2ew_kind (fun rest c v he => by
      have hc : c = 65536 := by
        simp only [Expr.add.injEq, Expr.scale.injEq, Coef.const.injEq, Expr.leaf.injEq] at he
        exact he.2.1.symm
      rw [hc, hf, hchar]
      decide) u (by simpa only [Expr.directNodes.eq_1, Expr.directNodes.eq_2,
        Expr.directNodes.eq_4, Coef.nodes.eq_1, List.nil_append, List.cons_append,
        List.nil_append] using hu)
  simpa only [hsz, hf] using h

/-- The checked `z` bound digits are committed cells with the witness size and field. -/
theorem z_cells {u : Nat} (hu : u ∈ [580, 581]) :
    program.privCellB u = true ∧ (program.value u).size = 1024 ∧ program.valueField u = 0 := by
  have hf : program.valueField 58 = 0 := valueShape_field value_z_header.2
  have hsz : (program.value 58).size = 1024 := valueShape_size value_z_header.2
  have h := bound_offset_digit_cells bound_records digit_lookups value_z_header.1
    value_z_kind u (by simpa only [Expr.directNodes.eq_1, Expr.directNodes.eq_2,
      Expr.directNodes.eq_4, Coef.nodes.eq_1, List.nil_append, List.cons_append,
      List.nil_append] using hu)
  simpa only [hsz, hf] using h

/-- The checked `offset` bound digits are committed cells with the witness size and field. -/
theorem offset_cells {u : Nat} (hu : u ∈ [585, 586]) :
    program.privCellB u = true ∧ (program.value u).size = 1024 ∧ program.valueField u = 0 := by
  have hf : program.valueField 65 = 0 := valueShape_field value_hint_2eoffset_header.2
  have hsz : (program.value 65).size = 1024 := valueShape_size value_hint_2eoffset_header.2
  have hfield : 0 < program.fields.length := by
    have h := valueField_lt conditions.wellFormed value_hint_2eoffset_header.1
    rwa [hf] at h
  have hchar : program.charOf 0 = 18446744069414584321 :=
    (conditions.model.registered.characteristic 0 hfield).symm
  have h := bound_digit_cells bound_records digit_lookups value_hint_2eoffset_header.1
    value_hint_2eoffset_kind (fun rest c v he => by
      have hc : c = 645 := by
        simp only [Expr.add.injEq, Expr.scale.injEq, Coef.const.injEq, Expr.leaf.injEq] at he
        exact he.2.1.symm
      rw [hc, hf, hchar]
      decide) u (by simpa only [Expr.directNodes.eq_1, Expr.directNodes.eq_2,
        Expr.directNodes.eq_4, Coef.nodes.eq_1, List.nil_append, List.cons_append,
        List.nil_append] using hu)
  simpa only [hsz, hf] using h

/-- The checked `slack` bound digits are committed cells with the witness size and field. -/
theorem slack_cells {u : Nat} (hu : u ∈ [587, 588]) :
    program.privCellB u = true ∧ (program.value u).size = 1024 ∧ program.valueField u = 0 := by
  have hf : program.valueField 66 = 0 := valueShape_field value_hint_2eslack_header.2
  have hsz : (program.value 66).size = 1024 := valueShape_size value_hint_2eslack_header.2
  have hfield : 0 < program.fields.length := by
    have h := valueField_lt conditions.wellFormed value_hint_2eslack_header.1
    rwa [hf] at h
  have hchar : program.charOf 0 = 18446744069414584321 :=
    (conditions.model.registered.characteristic 0 hfield).symm
  have h := bound_digit_cells bound_records digit_lookups value_hint_2eslack_header.1
    value_hint_2eslack_kind (fun rest c v he => by
      have hc : c = 645 := by
        simp only [Expr.add.injEq, Expr.scale.injEq, Coef.const.injEq, Expr.leaf.injEq] at he
        exact he.2.1.symm
      rw [hc, hf, hchar]
      decide) u (by simpa only [Expr.directNodes.eq_1, Expr.directNodes.eq_2,
        Expr.directNodes.eq_4, Coef.nodes.eq_1, List.nil_append, List.cons_append,
        List.nil_append] using hu)
  simpa only [hsz, hf] using h

end GordieHowe.MLDSA44.Emulated.ROMParams.DigitFacts
