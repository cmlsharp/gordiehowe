-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Native.Frontend.Relation
public import GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts
public import GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.Program
public import GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.Certified

@[expose] public section

/-!
# GordieHowe frontend: the signature relation of `MLDSA44.Ring.Native.ROMParams`

The program facts of the signature relation (`GordieHowe.MLDSA44.Ring.Native.MldsaRingRelation`)
at the native ML-DSA-44 ring program at the ROM parameters
(`GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.Program.program`, fields `F_q^6` and `GF(2^128)`), decided
here: `member.a_hat` is value `55`, `member.t1` value `56`, `z` value `60`, `challenge.c` value `62`,
`signature.w` value `63`, `norm.z.offset` value `64`; `challenge.c.boolean` is predicate `13` and
`norm.z` predicate `17`. So `GordieHowe.MLDSA44.Ring.Native.algebra_eq` holds at this program.
-/

namespace GordieHowe.MLDSA44.Ring.Native.ROMParams

open Generated.MLDSA44.Ring.Native.ROMParams.Program (program)
open Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts RealizedProgram


/-- A prime-typed source value of field `0` from its checked shape. -/
theorem primeCell {v : ℕ} {h : ValueShape}
    (hh : v < program.values.length ∧ program.valueShape v = h)
    (ht : v < program.values.length ∧ (program.value v).type = .sub "GF(p^1)")
    (hr : h.role = .source := by rfl) (hs : h.typeSource = .node := by rfl)
    (hf : h.field = 0 := by rfl) :
    v < program.values.length ∧ program.IsSourceValue v ∧
      (program.value v).typeSource = .node ∧ (program.value v).type = .sub "GF(p^1)" ∧
      program.valueField v = 0 :=
  ⟨hh.1, (valueShape_role hh.2).trans hr, (valueShape_typeSource hh.2).trans hs, ht.2,
    (valueShape_field hh.2).trans hf⟩

/-- Row `i`'s `w` as the named shared expression. -/
theorem exprW_eq (i : Fin 4) : program.expr (refW i) = .reindex (rowSlice i) (.leaf 63) := by
  fin_cases i
  exacts [Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.expr_signature_2erelation_2e0_2eshape_2eleft_2efirst_2efirst_eq, Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.expr_signature_2erelation_2e1_2eshape_2eleft_2efirst_2efirst_eq, Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.expr_signature_2erelation_2e2_2eshape_2eleft_2efirst_2efirst_eq, Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.expr_signature_2erelation_2e3_2eshape_2eleft_2efirst_2efirst_eq]

/-- Each row has `256` coordinates. -/
theorem rowLen_eq (i : Fin 4) :
    program.exprLen (rowLhs (refW i) (refA i) (refT i)) = 256 := by
  have hk : refW i < program.exprs.length := expr_lt_of_ne_default (by
    rw [exprW_eq]
    exact fun h => by cases h)
  rw [rowLhs, exprLen_add, nttS, exprLen_apply,
    exprLen_ref Generated.MLDSA44.Ring.Native.ROMParams.conditions.wellFormed.refsOrdered hk,
    exprW_eq, exprLen_reindex]
  fin_cases i <;> rfl

set_option maxRecDepth 8192 in
/-- The native ML-DSA-44 ring program at the ROM parameters has the signature relation's facts. -/
instance : MldsaRingRelation program where
  aHat := 55
  t1 := 56
  z := 60
  c := 62
  w := 63
  zOff := 64
  cPred := 13
  normPred := 17
  domainField0 := Generated.MLDSA44.Ring.Native.ROMParams.conditions.fieldTable.domainField_eq 0 (by decide)
  refsOrdered := Generated.MLDSA44.Ring.Native.ROMParams.conditions.wellFormed.refsOrdered
  refsLt := expr_lt_of_ne_default (by
    rw [expr_signature_2erelation_2e3_2eshape_2eleft_2esecond_2efirst_2esecond_2efirst_2efirst_2efirst_2efirst_eq]
    decide)
  rows := fun i => by
    fin_cases i
    exacts [Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.predicate_signature_2erelation_2e0_body, Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.predicate_signature_2erelation_2e1_body, Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.predicate_signature_2erelation_2e2_body, Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.predicate_signature_2erelation_2e3_body]
  rowLen := rowLen_eq
  exprW := exprW_eq
  exprA := fun i => by
    fin_cases i
    exacts [Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.expr_signature_2erelation_2e0_2eshape_2eleft_2esecond_2efirst_2efirst_2esecond_2efirst_2efirst_2efirst_eq, Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.expr_signature_2erelation_2e1_2eshape_2eleft_2esecond_2efirst_2efirst_2esecond_2efirst_2efirst_2efirst_eq, Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.expr_signature_2erelation_2e2_2eshape_2eleft_2esecond_2efirst_2efirst_2esecond_2efirst_2efirst_2efirst_eq, Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.expr_signature_2erelation_2e3_2eshape_2eleft_2esecond_2efirst_2efirst_2esecond_2efirst_2efirst_2efirst_eq]
  exprT := fun i => by
    fin_cases i
    exacts [Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.expr_signature_2erelation_2e0_2eshape_2eleft_2esecond_2efirst_2esecond_2efirst_2efirst_2efirst_2efirst_eq, Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.expr_signature_2erelation_2e1_2eshape_2eleft_2esecond_2efirst_2esecond_2efirst_2efirst_2efirst_2efirst_eq, Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.expr_signature_2erelation_2e2_2eshape_2eleft_2esecond_2efirst_2esecond_2efirst_2efirst_2efirst_2efirst_eq, Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.expr_signature_2erelation_2e3_2eshape_2eleft_2esecond_2efirst_2esecond_2efirst_2efirst_2efirst_2efirst_eq]
  exprZ := Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.expr_signature_2erelation_2e0_2eshape_2eleft_2esecond_2efirst_2efirst_2esecond_2esecond_2efirst_2efirst_eq
  exprS := Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.expr_signature_2erelation_2e0_2eshape_2eleft_2esecond_2efirst_2esecond_2efirst_2esecond_2efirst_2efirst_2efirst_2efirst_eq
  exprG := Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.expr_signature_2erelation_2e0_2eshape_2eleft_2esecond_2efirst_2esecond_2efirst_2esecond_2efirst_2efirst_2efirst_2esecond_2efirst_eq
  const2 := ⟨isConstant_of_kind value_signature_2erelation_2e0_2eshape_2eright_kind,
    valueShape_field value_signature_2erelation_2e0_2eshape_2eright_header.2,
    (constEntries_of_kind value_signature_2erelation_2e0_2eshape_2eright_kind).trans (by decide +kernel)⟩
  inSource := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨predicate_signature_2erelation_2e0_role.1, program.inSource_of_source predicate_signature_2erelation_2e0_role.2⟩
    · exact ⟨predicate_signature_2erelation_2e1_role.1, program.inSource_of_source predicate_signature_2erelation_2e1_role.2⟩
    · exact ⟨predicate_signature_2erelation_2e2_role.1, program.inSource_of_source predicate_signature_2erelation_2e2_role.2⟩
    · exact ⟨predicate_signature_2erelation_2e3_role.1, program.inSource_of_source predicate_signature_2erelation_2e3_role.2⟩
    · exact ⟨predicate_challenge_2ec_2eboolean_role.1,
        program.inSource_of_type predicate_challenge_2ec_2eboolean_role.2
          (valueShape_role value_challenge_2ec_header.2)⟩
    · exact ⟨predicate_norm_2ez_role.1, program.inSource_of_source predicate_norm_2ez_role.2⟩
  cBool := by
    obtain ⟨t, ht⟩ := predicate_challenge_2ec_2eboolean_body
    rw [ht]
    rfl
  norm := Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts.predicate_norm_2ez_body
  offConst := ⟨isConstant_of_kind value_norm_2ez_2eoffset_kind,
    valueShape_field value_norm_2ez_2eoffset_header.2,
    (constEntries_of_kind value_norm_2ez_2eoffset_kind).trans (by decide +kernel)⟩
  primeVals := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact primeCell value_member_2ea_5fhat_header value_member_2ea_5fhat_type
    · exact primeCell value_member_2et1_header value_member_2et1_type
    · exact primeCell value_signature_2ew_header value_signature_2ew_type
  sizes := ⟨valueShape_size value_member_2ea_5fhat_header.2, valueShape_size value_member_2et1_header.2,
    valueShape_size value_signature_2ew_header.2, valueShape_size value_z_header.2,
    valueShape_size value_challenge_2ec_header.2⟩

end GordieHowe.MLDSA44.Ring.Native.ROMParams
