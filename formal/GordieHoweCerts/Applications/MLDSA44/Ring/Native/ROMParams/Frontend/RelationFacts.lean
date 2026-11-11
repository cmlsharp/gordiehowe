-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Native.Frontend.Relation
public import GordieHoweCerts.Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts
public import GordieHoweCerts.Generated.MLDSA44.Ring.Native.ROMParams.Program
public import GordieHoweCerts.Generated.MLDSA44.Ring.Native.ROMParams.Certified

@[expose] public section

/-!
# GordieHowe frontend: the signature relation of `MLDSA44.Ring.Native.ROMParams`

The program facts of the signature relation (`GordieHowe.MLDSA44.Ring.Native.MldsaRingRelation`)
at the native ML-DSA-44 ring program at the ROM parameters
(`GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.Program.program`, fields `F_q^6` and `GF(2^128)`), decided
here from the generated shape facts (the values' kinds, headers and definitions, the predicates'
bodies, the challenge `signature.r`) and the checked table of the program's first shared
expressions (`expr_table_holds`, through the last row's last block of `â`). So
`GordieHowe.MLDSA44.Ring.Native.algebra_eq` holds at this program.
-/

namespace GordieHowe.MLDSA44.Ring.Native.ROMParams

open Generated.MLDSA44.Ring.Native.ROMParams.Program (program)
open Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts Generated.MLDSA44.Ring.Native.ROMParams RealizedProgram


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

/-- A shared expression of the checked table. -/
theorem exprOfTable {k : ℕ} (hk : k < Shapes.exprTable.length) :
    program.expr k = Shapes.exprTable.getD k default :=
  expr_table_holds.2 k hk

/-- The native ML-DSA-44 ring program at the ROM parameters has the signature relation's facts. -/
instance : MldsaRingRelation program where
  aHat := 54
  t1 := 55
  z := 59
  c := 61
  w := 62
  q := 63
  zOff := 65
  cPred := 13
  normPred := 17
  rel0 := 1
  r := 64
  rChal := 1
  one := 1
  zero1 := 0
  pw := 530
  lam := 532
  rn := 531
  pwRef := 45
  r128Ref := 44
  refW := ![30, 64, 71, 78]
  refQ := ![46, 65, 72, 79]
  refT := ![48, 66, 73, 80]
  refA := ![![52, 55, 58, 61], ![67, 68, 69, 70], ![74, 75, 76, 77], ![81, 82, 83, 84]]
  refZrow := ![53, 56, 59, 62]
  refZ := ![54, 57, 60, 63]
  refPW1 := 47
  refCR := 51
  refSup := 49
  refSign := 50
  nRefs := 85
  rowE := fun i => .ref (![30, 64, 71, 78] i)
  psi := 1753
  nInv := 8347681
  psiInv := 731434
  mOne := 8380416
  mTwo := 8380415
  consts := ⟨rfl, rfl, rfl, rfl, rfl⟩
  rowE_eq := fun _ => rfl
  rowELen := fun _ => rfl
  rowSource := fun i => by
    fin_cases i
    · exact ⟨predicate_signature_2erelation_2e0_role.1, program.inSource_of_source predicate_signature_2erelation_2e0_role.2⟩
    · exact ⟨predicate_signature_2erelation_2e1_role.1, program.inSource_of_source predicate_signature_2erelation_2e1_role.2⟩
    · exact ⟨predicate_signature_2erelation_2e2_role.1, program.inSource_of_source predicate_signature_2erelation_2e2_role.2⟩
    · exact ⟨predicate_signature_2erelation_2e3_role.1, program.inSource_of_source predicate_signature_2erelation_2e3_role.2⟩
  domainField0 := Generated.MLDSA44.Ring.Native.ROMParams.conditions.fieldTable.domainField_eq 0 (by decide)
  refsOrdered := Generated.MLDSA44.Ring.Native.ROMParams.conditions.wellFormed.refsOrdered
  refsLt := ⟨by rw [exprs_length]; decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩
  rows := fun i => by
    fin_cases i
    exacts [predicate_signature_2erelation_2e0_body, predicate_signature_2erelation_2e1_body,
      predicate_signature_2erelation_2e2_body, predicate_signature_2erelation_2e3_body]
  exprW := fun i => by
    rw [exprOfTable (by fin_cases i <;> decide +kernel)]
    fin_cases i <;> decide +kernel
  exprQ := fun i => by
    rw [exprOfTable (by fin_cases i <;> decide +kernel)]
    fin_cases i <;> decide +kernel
  exprT := fun i => by
    rw [exprOfTable (by fin_cases i <;> decide +kernel)]
    fin_cases i <;> decide +kernel
  exprA := fun i j => by
    rw [exprOfTable (by fin_cases i <;> fin_cases j <;> decide +kernel)]
    fin_cases i <;> fin_cases j <;> decide +kernel
  exprZrow := fun j => by
    rw [exprOfTable (by fin_cases j <;> decide +kernel)]
    fin_cases j <;> decide +kernel
  exprZ := fun j => by
    rw [exprOfTable (by fin_cases j <;> decide +kernel)]
    fin_cases j <;> decide +kernel
  exprPW1 := by rw [exprOfTable (by decide +kernel)]; decide +kernel
  exprSup := by rw [exprOfTable (by decide +kernel)]; decide +kernel
  exprSign := by rw [exprOfTable (by decide +kernel)]; decide +kernel
  exprCR := by rw [exprOfTable (by decide +kernel)]; decide +kernel
  zeroConst := ⟨isConstant_of_kind value_signature_2erelation_2e0_2eshape_2eright_kind,
    valueShape_field value_signature_2erelation_2e0_2eshape_2eright_header.2,
    constEntries_of_kind value_signature_2erelation_2e0_2eshape_2eright_kind⟩
  inSource := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨predicate_challenge_2ec_2eboolean_role.1,
        program.inSource_of_type predicate_challenge_2ec_2eboolean_role.2
          (valueShape_role value_challenge_2ec_header.2)⟩
    · exact ⟨predicate_norm_2ez_role.1, program.inSource_of_source predicate_norm_2ez_role.2⟩
  cBool := by
    obtain ⟨t, ht⟩ := predicate_challenge_2ec_2eboolean_body
    rw [ht]
    rfl
  norm := predicate_norm_2ez_body
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
  rowFields := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact valueShape_field value_signature_2ew_header.2
    · exact valueShape_field value_z_header.2
    · exact valueShape_field value_challenge_2ec_header.2
    · exact valueShape_field value_signature_2eQ_header.2
    · exact valueShape_field value_signature_2erelation_2e0_2epublic0_header.2
    · exact valueShape_field value_signature_2elambda_header.2
    · exact valueShape_field value_signature_2erelation_2e0_2epublic1_header.2
  sizes := ⟨valueShape_size value_member_2ea_5fhat_header.2, valueShape_size value_member_2et1_header.2,
    valueShape_size value_signature_2ew_header.2, valueShape_size value_z_header.2,
    valueShape_size value_challenge_2ec_header.2, valueShape_size value_signature_2eQ_header.2⟩
  qPriv := value_signature_2eQ_kind
  rPow :=
    { consts := ⟨isConstant_of_kind value_hint_2edecompose_2eshape_2eone_kind,
        by rw [constEntries_of_kind value_hint_2edecompose_2eshape_2eone_kind]; rfl⟩
      kind := value_signature_2er_kind
      chalField := challenge_signature_2er_full.2.2.1
      fields := ⟨valueShape_field value_hint_2edecompose_2eshape_2eone_header.2,
        valueShape_field value_signature_2er_header.2⟩
      sizes := ⟨valueShape_size value_hint_2edecompose_2eshape_2eone_header.2,
        valueShape_size value_signature_2er_header.2⟩
      values_pos := Nat.lt_of_le_of_lt (Nat.zero_le _) value_hint_2edecompose_2eshape_2eone_header.1 }
  chalR := ⟨challenge_signature_2er_full.2.2.2, challenge_signature_2er_full.2.1⟩
  pwKind := value_signature_2erelation_2e0_2epublic0_definition
  lamKind := value_signature_2elambda_definition
  rnKind := value_signature_2erelation_2e0_2epublic1_definition
  powPw := by
    rw [powSym_congr (agreesBelow_replica expr_table_holds.2 (by decide +kernel)) _ _ _
      (by decide +kernel)]
    decide +kernel
  pow128 := by
    rw [powSym_congr (agreesBelow_replica expr_table_holds.2 (by decide +kernel)) _ _ _
      (by decide +kernel)]
    decide +kernel

end GordieHowe.MLDSA44.Ring.Native.ROMParams
