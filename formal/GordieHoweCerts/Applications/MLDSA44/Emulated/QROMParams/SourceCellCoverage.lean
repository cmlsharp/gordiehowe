-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Emulated.HonestValues
public import GordieHoweCerts.Applications.MLDSA44.Emulated.QROMParams.Frontend.Basic
public import GordieHoweCerts.Generated.MLDSA44.Emulated.QROMParams.ShapeFacts
public import GordieHoweCerts.Generated.MLDSA44.Emulated.QROMParams.SourceRoleFacts

public section

open GordieHowe RealizedProgram
namespace GordieHowe.MLDSA44.Emulated.QROMParams.SourceCellCoverage
open _root_.GordieHowe.Generated.MLDSA44.Emulated.QROMParams.Program (program)
open _root_.GordieHowe.Generated.MLDSA44.Emulated.QROMParams

/-- The semantic field and packing classes of the finite source-role rows. -/
@[expose] def rowClass (r : SourceRoleEntry) : Prop :=
  r.value ∈ [56, 57, 67, 58, 61, 65, 66] ∨
  (((r.field = 1 ∧ r.node.map (·.name) = some "GF(2^16)") ∧
    (1 ≤ r.value ∧ r.value - 1 ∈ Emulated.hV ∧
      ((wordsOwner? (r.value - 1)).isSome = true ∨ r.value - 1 ∈ [69, 119, 557, 560, 562, 563, 564, 565]))) ∨
   ((r.field = 1 ∧ r.node.map (·.name) = some "bit") ∧ (1 ≤ r.value ∧ r.value - 1 ∈ Emulated.hV ∧ r.value - 1 ∈ [67, 68, 556, 561]))) ∨
  ((r.field = 0 ∧ r.node.map (·.name) = some "GF(p^1)") ∧ r.value ∈ Emulated.aValues layout)

instance (r : SourceRoleEntry) : Decidable (rowClass r) := by
  unfold rowClass
  repeat first | apply instDecidableOr | apply instDecidableAnd

theorem row_class {r : SourceRoleEntry} (hm : r ∈ SourceRoles.roles) : rowClass r := by
  have h : SourceRoles.roles.all (fun r => decide (rowClass r)) = true := by
    rw [SourceRoles.roles_eq]
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h r hm)

theorem cell_classes : (List.range program.values.length).all (fun v =>
    !program.privCellB v || !decide (program.IsSourceValue v) ||
      (program.valueField v == 1 && (program.value v).node.map (·.name) == some "GF(2^16)" &&
        decide (1 ≤ v) && decide (v - 1 ∈ Emulated.hV) &&
        ((wordsOwner? (v - 1)).isSome || [69, 119, 557, 560, 562, 563, 564, 565].contains (v - 1))) ||
      (program.valueField v == 1 && (program.value v).node.map (·.name) == some "bit" &&
        decide (1 ≤ v) && decide (v - 1 ∈ Emulated.hV) && [67, 68, 556, 561].contains (v - 1)) ||
      (program.valueField v == 0 && (program.value v).node.map (·.name) == some "GF(p^1)" &&
        (Emulated.aValues layout).contains v)) = true := by
  apply List.all_eq_true.mpr
  intro v hv
  by_cases hp : program.privCellB v = true
  · by_cases hs : program.IsSourceValue v
    · have hk := kind_of_privCellB hp
      have hn : (program.value v).needsSourceRole = true := by
        simp only [Value.needsSourceRole, show (program.value v).role = .source from hs,
          decide_true, hk, Bool.true_and]
      obtain ⟨r, hr⟩ := SourceRoleFacts.rolesOk.covered v (List.mem_range.mp hv) hn
      obtain ⟨hm, hrval⟩ := sourceRoleTable_mem hr
      have he := SourceRoleFacts.rolesOk.lookup hr
      have hc := row_class hm
      have hf := he.2.2.1
      have hnode := he.2.2.2
      rw [← hrval] at hp hs hk hf hnode ⊢
      rcases hc with hx | hx | hx
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with hx | hx | hx | hx | hx | hx | hx
        · rw [hx, ShapeFacts.value_key_2ea_kind] at hk; cases hk
        · rw [hx, ShapeFacts.value_key_2et1_kind] at hk; cases hk
        · rw [hx, ShapeFacts.value_tr_kind] at hk; cases hk
        · rw [hx, ShapeFacts.value_z_kind] at hk; cases hk
        · rw [hx, ShapeFacts.value_signature_2ew_kind] at hk; cases hk
        · rw [hx, ShapeFacts.value_hint_2eoffset_kind] at hk; cases hk
        · rw [hx, ShapeFacts.value_hint_2eslack_kind] at hk; cases hk
      · simp only [hp, hs, decide_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
          Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, decide_eq_true_eq, hf, hnode]
        rcases hx with ⟨⟨a, b⟩, c, d, e⟩ | ⟨⟨a, b⟩, c, d, e⟩
        · exact Or.inl (Or.inl ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩)
        · exact Or.inl (Or.inr ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩)
      · simp only [hp, hs, decide_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
          Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, decide_eq_true_eq, hf, hnode]
        exact Or.inr hx
    · simp only [hp, hs, decide_false, Bool.not_false, Bool.or_true, Bool.true_or]
  · have hp' : program.privCellB v = false := Bool.eq_false_iff.mpr hp
    simp only [hp', Bool.not_false, Bool.true_or]
end GordieHowe.MLDSA44.Emulated.QROMParams.SourceCellCoverage
