-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.Falcon512.Native.Frontend.Algebra
public import GordieHoweCerts.Applications.Falcon512.Native.ROMParams.Frontend.Facts
public import GordieHoweCerts.Generated.Falcon512.Native.ROMParams.SourceRoleFacts
public import GordieHoweCerts.Generated.Falcon512.Native.ROMParams.Certified
public import GordieHowe.Language.Honest.SourceRoles
public import GordieHowe.Applications.Falcon512.Frontend.Norm

@[expose] public section

/-!
# GordieHowe frontend: domain `A`'s facts of `Falcon512.Native.ROMParams`

The program facts domain `A` reads (`GordieHowe.Falcon512.Native.FalconAAlg`) for
`GordieHowe.Generated.Falcon512.Native.ROMParams.Program.program` (export `3ed06086`): the predicates by index
and body, the shared expressions, the values and the constants, read off the generated shape facts
(`ShapeFacts`) and by `decide`.
-/

namespace GordieHowe.Falcon512.Native.ROMParams

open Generated.Falcon512.Native.ROMParams.Program
open Generated.Falcon512.Native.ROMParams.ShapeFacts
open RealizedProgram
open Generated.Falcon512.Native.ROMParams (interp)


/-- `norm.center`. -/
theorem alg_center :
    ∃ t, (program.predicate 275).body = .equal 1 (.add (.mul (.ref 540) (.ref 540))
    (.scale (.const 12288) (.mul (.add (.add (.ref 541) (.scale (.const 64) (.ref 542)))
    (.scale (.const 4096) (.ref 543))) (.add (.add (.ref 541) (.scale (.const 64) (.ref 542)))
    (.scale (.const 4096) (.ref 543)))))) (.leaf 42) t :=
  predicate_norm_2ecenter_body

/-- `norm.top`. -/
theorem alg_top :
    ∃ t, (program.predicate 276).body = .equal 1 (.ref 544) (.leaf 41) t :=
  predicate_norm_2etop_body

/-- `norm.column0`. -/
theorem alg_col0 :
    ∃ real, (program.predicate 277).body =
    .mod 1 0 (.mul (.ref 545) (.ref 545)) (.add (.ref 546) (.scale (.const 64) (.ref 547))) real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2ecolumn0_body
  exact ⟨real, h⟩

/-- `norm.column1`. -/
theorem alg_col1 :
    ∃ real, (program.predicate 278).body = .mod 1 0
    (.add (.scale (.const 2) (.mul (.ref 545) (.ref 548))) (.ref 549))
    (.add (.ref 550) (.scale (.const 64) (.ref 551))) real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2ecolumn1_body
  exact ⟨real, h⟩

/-- `norm.column2`. -/
theorem alg_col2 :
    ∃ real, (program.predicate 279).body = .mod 1 0
    (.add (.add (.scale (.const 2) (.mul (.ref 545) (.ref 552))) (.mul (.ref 548) (.ref 548)))
    (.ref 553)) (.add (.ref 554) (.scale (.const 64) (.ref 555))) real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2ecolumn2_body
  exact ⟨real, h⟩

/-- `norm.column3`. -/
theorem alg_col3 :
    ∃ real, (program.predicate 280).body = .mod 1 0
    (.add (.scale (.const 2) (.mul (.ref 548) (.ref 552))) (.ref 556))
    (.add (.ref 557) (.scale (.const 64) (.ref 558))) real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2ecolumn3_body
  exact ⟨real, h⟩

/-- `norm.column4`. -/
theorem alg_col4 :
    ∃ real, (program.predicate 281).body = .mod 1 0 (.add (.mul (.ref 552) (.ref 552))
    (.ref 559)) (.add (.ref 560) (.scale (.const 64) (.ref 561))) real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2ecolumn4_body
  exact ⟨real, h⟩

/-- `norm.column5`. -/
theorem alg_col5 :
    ∃ real, (program.predicate 282).body = .mod 1 0 (.ref 562) (.ref 563) real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2ecolumn5_body
  exact ⟨real, h⟩

/-- `norm.normalize`. -/
theorem alg_normalize :
    ∃ real, (program.predicate 283).body = .mod 1 0
    (.add (.add (.ref 564) (.apply (.batched 102 (.sum 63)) (.ref 565))) (.ref 566))
    (.add (.leaf 600) (.scale (.const 64) (.ref 567))) real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2enormalize_body
  exact ⟨real, h⟩

/-- `norm.complement`. -/
theorem alg_complement :
    ∃ real, (program.predicate 284).body = .mod 1 0
    (.add (.add (.ref 568) (.leaf 602)) (.ref 569)) (.add (.leaf 604) (.scale (.const 64) (.leaf 603)))
    real := by
  obtain ⟨real, h, -⟩ := predicate_norm_2ecomplement_body
  exact ⟨real, h⟩

/-- `norm.Dc.boolean`. -/
theorem alg_dcBool :
    ∃ t, (program.predicate 293).body = .equal 1 (.mul (.leaf 603) (.leaf 603)) (.leaf 603) t :=
  predicate_norm_2eDc_2eboolean_body

/-- `encoding.b.boolean`. -/
theorem alg_encB :
    ∃ t, (program.predicate 295).body = .equal 1 (.mul (.ref 577) (.ref 577)) (.ref 577) t :=
  predicate_encoding_2eb_2eboolean_body

/-- `norm.a`. -/
theorem alg_rangeA :
    ∃ real, (program.predicate 297).body = .mem 1 [.leaf 597] (.range 64) real :=
  predicate_norm_2ea_body

/-- `norm.sq`. -/
theorem alg_rangeSq :
    ∃ real, (program.predicate (297 + 1)).body = .mem 1 [.leaf 598] (.range 64) real :=
  predicate_norm_2esq_body

/-- `norm.cc`. -/
theorem alg_rangeCc :
    ∃ real, (program.predicate (297 + 2)).body = .mem 1 [.leaf 599] (.range 189) real :=
  predicate_norm_2ecc_body

/-- `norm.nd`. -/
theorem alg_rangeNd :
    ∃ real, (program.predicate (297 + 3)).body = .mem 1 [.leaf 600] (.range 64) real :=
  predicate_norm_2end_body

/-- `norm.nc`. -/
theorem alg_rangeNc :
    ∃ real, (program.predicate (297 + 4)).body = .mem 1 [.leaf 601] (.range 64) real :=
  predicate_norm_2enc_body

/-- `norm.D`. -/
theorem alg_rangeD :
    ∃ real, (program.predicate (297 + 5)).body = .mem 1 [.leaf 602] (.range 64) real :=
  predicate_norm_2eD_body

/-- `encoding.high`. -/
theorem alg_high :
    ∃ real, (program.predicate 303).body = .mem 1 [.ref 574] (.range 16) real :=
  predicate_encoding_2ehigh_body

/-- `encoding.slack`. -/
theorem alg_slack :
    ∃ real, (program.predicate 304).body =
    .mem 1 [.add (.scale (.const 12288) (.apply (.sum 512) (.ref 574))) (.leaf 605)] (.range 393)
    real :=
  predicate_encoding_2eslack_body

/-- The field-form `signature.equation`. -/
theorem alg_sig :
    ∃ real, (program.predicate 308).body = .mod 1 12289
    (.add (.leaf 596) (.apply (.negacyclicConv 593 (.ntt 10302)) (.leaf 595)))
    (.apply (.batched 512 (.fromDigits 16 2)) (.leaf 594)) real := by
  obtain ⟨real, h, -⟩ := predicate_signature_2eequation_2esource_body
  exact ⟨real, h⟩

/-- The norm's shared expressions. -/
theorem alg_exprs_norm :
    program.expr 540 =
    .reindex idx41 (.concat (.leaf 596) (.leaf 595)) ∧
    program.expr 541 = .reindex idx42 (.leaf 597) ∧
    program.expr 542 = .reindex idx43 (.leaf 597) ∧
    program.expr 543 = .reindex idx44 (.concat (.leaf 597) (.leaf 41)) ∧
    program.expr 544 = .reindex idx45 (.leaf 603) ∧
    program.expr 545 = .reindex idx42 (.leaf 597) ∧
    program.expr 546 = .reindex idx46 (.leaf 598) ∧
    program.expr 547 = .reindex idx47 (.leaf 599) ∧
    program.expr 548 = .reindex idx43 (.leaf 597) ∧
    program.expr 549 = .reindex idx47 (.leaf 599) ∧
    program.expr 550 = .reindex idx48 (.leaf 598) ∧
    program.expr 551 = .reindex idx49 (.leaf 599) ∧
    program.expr 552 = .reindex idx44 (.concat (.leaf 597) (.leaf 41)) ∧
    program.expr 553 = .reindex idx49 (.leaf 599) ∧
    program.expr 554 = .reindex idx50 (.leaf 598) ∧
    program.expr 555 = .reindex idx51 (.leaf 599) ∧
    program.expr 556 = .reindex idx51 (.leaf 599) ∧
    program.expr 557 = .reindex idx52 (.leaf 598) ∧
    program.expr 558 = .reindex idx53 (.leaf 599) ∧
    program.expr 559 = .reindex idx53 (.leaf 599) ∧
    program.expr 560 = .reindex idx54 (.leaf 598) ∧
    program.expr 561 = .reindex idx55 (.leaf 599) ∧
    program.expr 562 = .reindex idx55 (.leaf 599) ∧
    program.expr 563 = .reindex idx56 (.leaf 598) ∧
    program.expr 564 = .reindex idx57 (.concat (.leaf 600) (.leaf 41)) ∧
    program.expr 565 = .reindex idx58 (.concat (.leaf 598) (.leaf 41)) ∧
    program.expr 566 = .reindex idx59 (.concat (.leaf 601) (.leaf 41)) ∧
    program.expr 567 = .reindex idx60 (.concat (.leaf 601) (.leaf 41)) ∧
    program.expr 568 = .reindex idx61 (.leaf 600) ∧
    program.expr 569 = .reindex idx62 (.concat (.leaf 603) (.leaf 41)) :=
  ⟨expr_norm_2ecenter_2eshape_2eleft_2efirst_2efirst_eq, expr_norm_2ecenter_2eshape_2eleft_2esecond_2efirst_2efirst_2efirst_2efirst_eq, expr_norm_2ecenter_2eshape_2eleft_2esecond_2efirst_2efirst_2efirst_2esecond_2efirst_eq, expr_norm_2ecenter_2eshape_2eleft_2esecond_2efirst_2efirst_2esecond_2efirst_eq, expr_norm_2etop_2eshape_2eleft_eq, expr_norm_2ecolumn0_2eshape_2eleft_2efirst_eq, expr_norm_2ecolumn0_2eshape_2eright_2efirst_eq, expr_norm_2ecolumn0_2eshape_2eright_2esecond_2efirst_eq, expr_norm_2ecolumn1_2eshape_2eleft_2efirst_2efirst_2esecond_eq, expr_norm_2ecolumn1_2eshape_2eleft_2esecond_eq, expr_norm_2ecolumn1_2eshape_2eright_2efirst_eq, expr_norm_2ecolumn1_2eshape_2eright_2esecond_2efirst_eq, expr_norm_2ecolumn4_2eshape_2eleft_2efirst_2efirst_eq, expr_norm_2ecolumn2_2eshape_2eleft_2esecond_eq, expr_norm_2ecolumn2_2eshape_2eright_2efirst_eq, expr_norm_2ecolumn2_2eshape_2eright_2esecond_2efirst_eq, expr_norm_2ecolumn3_2eshape_2eleft_2esecond_eq, expr_norm_2ecolumn3_2eshape_2eright_2efirst_eq, expr_norm_2ecolumn3_2eshape_2eright_2esecond_2efirst_eq, expr_norm_2ecolumn4_2eshape_2eleft_2esecond_eq, expr_norm_2ecolumn4_2eshape_2eright_2efirst_eq, expr_norm_2ecolumn4_2eshape_2eright_2esecond_2efirst_eq, expr_norm_2ecolumn5_2eshape_2eleft_eq, expr_norm_2ecolumn5_2eshape_2eright_eq, expr_norm_2enormalize_2eshape_2eleft_2efirst_2efirst_eq, expr_norm_2enormalize_2eshape_2eleft_2efirst_2esecond_2efirst_eq, expr_norm_2enormalize_2eshape_2eleft_2esecond_eq, expr_norm_2enormalize_2eshape_2eright_2esecond_2efirst_eq, expr_norm_2ecomplement_2eshape_2eleft_2efirst_2efirst_eq, expr_norm_2ecomplement_2eshape_2eleft_2esecond_eq⟩

/-- The encoding's shared expressions. -/
theorem alg_exprs_enc :
    program.expr 574 = .reindex idx75 (.leaf 597) ∧
    program.expr 576 = .reindex idx76 (.leaf 597) ∧
    program.expr 577 = .add (.ref 576) (.scale (.const 12287) (.ref 574)) :=
  ⟨expr_encoding_2eb_2eboolean_2eshape_2eright_2eshared_2esecond_2efirst_eq, expr_encoding_2eb_2eboolean_2eshape_2eright_2eshared_2efirst_eq, expr_encoding_2eb_2eboolean_2eshape_2eright_eq⟩

/-- The encoding's shared expressions are below `577`. -/
theorem alg_enc_le : 574 ≤ 577 ∧ 576 ≤ 577 ∧ 577 ≤ 577 := by
  decide

/-- The encoding's index maps. -/
theorem alg_idx_enc :
    (∀ j < 512, idx75.entry j = 3 * (512 + j) + 2) ∧
    (∀ j < 512, idx76.entry j = 3 * (512 + j) + 1) ∧ idx75.size = 512 ∧ idx76.size = 512 := by
  decide +kernel

/-- The shared expressions domain `A` reads are below the table's length. -/
theorem alg_exprs_length : 577 < program.exprs.length :=
  expr_lt_of_ne_default (by rw [expr_encoding_2eb_2eboolean_2eshape_2eright_eq]; intro hc; cases hc)

/-- The sizes of the values domain `A` reads. -/
theorem alg_sizes_A :
    (program.value 595).size = 512 ∧ (program.value 596).size = 512 ∧
    (program.value 597).size = 3072 ∧ (program.value 598).size = 6144 ∧
    (program.value 599).size = 5120 ∧ (program.value 600).size = 102 ∧
    (program.value 601).size = 85 ∧ (program.value 602).size = 6 ∧
    (program.value 603).size = 6 ∧ (program.value 41).size = 1 ∧
    (program.value 42).size = 1024 :=
  ⟨valueShape_size value_s2_header.2, valueShape_size value_signature_2es1_header.2, valueShape_size value_norm_2ea_header.2, valueShape_size value_norm_2esq_header.2, valueShape_size value_norm_2ecc_header.2, valueShape_size value_norm_2end_header.2, valueShape_size value_norm_2enc_header.2, valueShape_size value_norm_2eD_header.2, valueShape_size value_norm_2eDc_header.2, valueShape_size value_norm_2ezero_header.2, valueShape_size value_norm_2ecenter_2econstant_2eright_header.2⟩

/-- No source role reads a value bound to an expression. -/
private theorem role_not_bound {r : SourceRoleEntry} (hm : r ∈ Generated.Falcon512.Native.ROMParams.SourceRoles.roles) (e : Expr) :
    (program.value r.value).kind ≠ .bound e := by
  rcases HashShapeFacts.role_value_cases r hm with ho | hl
  · obtain ⟨⟨p, t⟩, hw⟩ := Option.isSome_iff_exists.1 ho
    rw [← wordsOwner?_eq hw, (HashShapeFacts.word_facts p t).2.1]
    intro hc
    cases hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl | hl
    · rw [hl, value_nonce_kind]; intro hc; cases hc
    · rw [hl, value_message_kind]; intro hc; cases hc
    · rw [hl, value_message_2ein_5fmessage_kind]; intro hc; cases hc
    · rw [hl, value_h2p_2eshake_2estate_2ewords_kind]; intro hc; cases hc
    · rw [hl, value_h2p_2eselect_2eraw_2ewords_kind]; intro hc; cases hc
    · rw [hl, value_h2p_2eselect_2ecount_kind]; intro hc; cases hc
    · rw [hl, value_h2p_2eselect_2efull_kind]; intro hc; cases hc
    · rw [hl, value_statement_2ehhat_kind]; intro hc; cases hc
    · rw [hl, value_crossing_2ec_5fA_kind]; intro hc; cases hc
    · rw [hl, value_s2_kind]; intro hc; cases hc
    · rw [hl, value_signature_2es1_kind]; intro hc; cases hc
    · rw [hl, value_norm_2ea_kind]; intro hc; cases hc
    · rw [hl, value_norm_2esq_kind]; intro hc; cases hc
    · rw [hl, value_norm_2ecc_kind]; intro hc; cases hc
    · rw [hl, value_norm_2end_kind]; intro hc; cases hc
    · rw [hl, value_norm_2enc_kind]; intro hc; cases hc
    · rw [hl, value_norm_2eD_kind]; intro hc; cases hc
    · rw [hl, value_norm_2eDc_kind]; intro hc; cases hc

/-- The program binds no value to an expression. -/
theorem alg_noBound :
    ∀ v < program.values.length,
    (match (program.value v).kind with
    | .bound _ => false
    | _ => true) = true := by
  intro v hv
  cases hk : (program.value v).kind with
  | bound e =>
    have hb : (program.value v).kind.isBound = true := by rw [hk]; rfl
    have hs := (program.boundRecsV_sound (boundRecsV_of_completionB Generated.Falcon512.Native.ROMParams.conditions.completion hv) hb).1
    obtain ⟨r, hr⟩ := Generated.Falcon512.Native.ROMParams.SourceRoleFacts.rolesOk.bound_covered hv hs hb
    obtain ⟨hm, he⟩ := sourceRoleTable_mem hr
    exact absurd (he ▸ hk) (role_not_bound hm e)
  | _ => rfl

/-- The zero constants `41`, `42` and the slack offset `605`. -/
theorem alg_consts_A :
    program.isConstant 41 = true ∧ program.valueField 41 = 1 ∧
    (program.constEntries 41).getD 0 0 = 0 ∧ program.isConstant 42 = true ∧
    program.valueField 42 = 1 ∧ program.constEntries 42 = List.replicate 1024 0 ∧
    program.isConstant 605 = true ∧ program.valueField 605 = 1 ∧
    (program.constEntries 605).getD 0 0 = 392 := by
  refine ⟨isConstant_of_kind value_norm_2ezero_kind, valueShape_field value_norm_2ezero_header.2, ?_, isConstant_of_kind value_norm_2ecenter_2econstant_2eright_kind, valueShape_field value_norm_2ecenter_2econstant_2eright_header.2, ?_,
    isConstant_of_kind value_encoding_2eslack_2eoffset_kind, valueShape_field value_encoding_2eslack_2eoffset_header.2, ?_⟩
  · rw [constEntries_of_kind value_norm_2ezero_kind]; rfl
  · rw [constEntries_of_kind value_norm_2ecenter_2econstant_2eright_kind]; decide +kernel
  · rw [constEntries_of_kind value_encoding_2eslack_2eoffset_kind]; rfl

/-- The constant `41` is zero. -/
theorem alg_const41 :
    ∃ es, (program.value 41).kind = .constant es ∧ es.getD 0 0 = 0 :=
  ⟨[0], value_norm_2ezero_kind, rfl⟩

/-- The constant `604` holds the base-`64` digits of `β² = 34034726`. -/
theorem alg_const604 :
    program.valueField 604 = 1 ∧ ∃ es, (program.value 604).kind = .constant es ∧
    ∀ m < 6, es.getD m 0 = NativeNorm.digit 34034726 m :=
  ⟨valueShape_field value_norm_2etarget_header.2, [38, 16, 53, 1, 2, 0], value_norm_2etarget_kind, by decide⟩

/-- `statement.hhat` is an opaque statement value of no argument. -/
theorem alg_hhatKind :
    (program.value 593).kind = .pub (.opaque "statement.hhat" []) :=
  value_statement_2ehhat_kind

/-- The named operators of `signature.equation`. -/
theorem alg_ops_sig :
    RealizedProgram.NamedOp.cols program (.negacyclicConv 593 (.ntt 10302)) = 512 ∧
    RealizedProgram.NamedOp.rows program (.negacyclicConv 593 (.ntt 10302)) = 512 ∧
    RealizedProgram.NamedOp.cols program (.batched 512 (.fromDigits 16 2)) = 8192 ∧
    RealizedProgram.NamedOp.rows program (.batched 512 (.fromDigits 16 2)) = 512 := by
  simp only [NamedOp.cols, NamedOp.rows, valueShape_size value_statement_2ehhat_header.2, and_self]

/-- The program's facts of domain `A` beyond the norm. -/
instance : FalconAAlg program where
  cA_eq := rfl
  s2_eq := rfl
  pSig := 308
  inSource_sig := ⟨predicate_signature_2eequation_2esource_role.1, program.inSource_of_source predicate_signature_2eequation_2esource_role.2⟩
  sig := alg_sig
  sizes_sig := ⟨valueShape_size value_s2_header.2, valueShape_size value_signature_2es1_header.2⟩
  primeA_sig := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact ⟨value_s2_header.1, valueShape_role value_s2_header.2, valueShape_typeSource value_s2_header.2, value_s2_type.2, valueShape_field value_s2_header.2, isConstant_of_priv value_s2_kind⟩
    · exact ⟨value_signature_2es1_header.1, valueShape_role value_signature_2es1_header.2, valueShape_typeSource value_signature_2es1_header.2, value_signature_2es1_type.2, valueShape_field value_signature_2es1_header.2, isConstant_of_priv value_signature_2es1_kind⟩
  fields_cA := ⟨valueShape_field value_crossing_2ec_5fA_header.2, isConstant_of_priv value_crossing_2ec_5fA_kind⟩
  noBound := alg_noBound
  hhatKind := alg_hhatKind
  ops_sig := alg_ops_sig

/-- The norm's index maps of the batches (`6426` entries, decided coordinate by coordinate). -/
theorem norm_i70_entry : ∀ b < 17, ∀ m < 6, ∀ s < 63, idx58.entry ((6 * b + m) * 63 + s) =
    if 63 * b + s < 1024 then 6 * (63 * b + s) + m else 6144 := by
  decide +kernel

/-- **The generic norm's identifiers and facts** at domain `A` (`FalconNorm`, domain and field
`1`). -/
instance : Norm.FalconNorm program where
  dA := 1
  fA := 1
  domainField := Generated.Falcon512.Native.ROMParams.conditions.fieldTable.domainField_eq 1 (by decide)
  s2 := 595
  s1 := 596
  a := 597
  sq := 598
  cc := 599
  nd := 600
  nc := 601
  D := 602
  Dc := 603
  tgt := 604
  off := 605
  z1 := 41
  z := 42
  e0 := 540
  p0 := 275
  eMax := 577
  pDc := 293
  pEncB := 295
  pRange := 297
  pHigh := 303
  pSlack := 304
  eHigh := 574
  eMid := 576
  eB := 577
  iHigh := idx75
  iMid := idx76
  i52 := idx41
  i54 := idx42
  i55 := idx43
  i56 := idx44
  i57 := idx45
  i58 := idx46
  i59 := idx47
  i60 := idx48
  i61 := idx49
  i62 := idx50
  i63 := idx51
  i64 := idx52
  i65 := idx53
  i66 := idx54
  i67 := idx55
  i68 := idx56
  i69 := idx57
  i70 := idx58
  i71 := idx59
  i72 := idx60
  i73 := idx61
  i74 := idx62
  refsOrdered := Generated.Falcon512.Native.ROMParams.conditions.wellFormed.refsOrdered
  inSource_A := by
    intro v hv
    change v ∈ [275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 293, 295, 297, 298, 299, 300, 301, 302, 303, 304] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨predicate_norm_2ecenter_role.1, program.inSource_of_source predicate_norm_2ecenter_role.2⟩
    · exact ⟨predicate_norm_2etop_role.1, program.inSource_of_source predicate_norm_2etop_role.2⟩
    · exact ⟨predicate_norm_2ecolumn0_role.1, program.inSource_of_source predicate_norm_2ecolumn0_role.2⟩
    · exact ⟨predicate_norm_2ecolumn1_role.1, program.inSource_of_source predicate_norm_2ecolumn1_role.2⟩
    · exact ⟨predicate_norm_2ecolumn2_role.1, program.inSource_of_source predicate_norm_2ecolumn2_role.2⟩
    · exact ⟨predicate_norm_2ecolumn3_role.1, program.inSource_of_source predicate_norm_2ecolumn3_role.2⟩
    · exact ⟨predicate_norm_2ecolumn4_role.1, program.inSource_of_source predicate_norm_2ecolumn4_role.2⟩
    · exact ⟨predicate_norm_2ecolumn5_role.1, program.inSource_of_source predicate_norm_2ecolumn5_role.2⟩
    · exact ⟨predicate_norm_2enormalize_role.1, program.inSource_of_source predicate_norm_2enormalize_role.2⟩
    · exact ⟨predicate_norm_2ecomplement_role.1, program.inSource_of_source predicate_norm_2ecomplement_role.2⟩
    · exact ⟨predicate_norm_2eDc_2eboolean_role.1, program.inSource_of_type predicate_norm_2eDc_2eboolean_role.2 (valueShape_role value_norm_2eDc_header.2)⟩
    · exact ⟨predicate_encoding_2eb_2eboolean_role.1, program.inSource_of_source predicate_encoding_2eb_2eboolean_role.2⟩
    · exact ⟨predicate_norm_2ea_role.1, program.inSource_of_source predicate_norm_2ea_role.2⟩
    · exact ⟨predicate_norm_2esq_role.1, program.inSource_of_source predicate_norm_2esq_role.2⟩
    · exact ⟨predicate_norm_2ecc_role.1, program.inSource_of_source predicate_norm_2ecc_role.2⟩
    · exact ⟨predicate_norm_2end_role.1, program.inSource_of_source predicate_norm_2end_role.2⟩
    · exact ⟨predicate_norm_2enc_role.1, program.inSource_of_source predicate_norm_2enc_role.2⟩
    · exact ⟨predicate_norm_2eD_role.1, program.inSource_of_source predicate_norm_2eD_role.2⟩
    · exact ⟨predicate_encoding_2ehigh_role.1, program.inSource_of_source predicate_encoding_2ehigh_role.2⟩
    · exact ⟨predicate_encoding_2eslack_role.1, program.inSource_of_source predicate_encoding_2eslack_role.2⟩
  center := alg_center
  top := alg_top
  col0 := alg_col0
  col1 := alg_col1
  col2 := alg_col2
  col3 := alg_col3
  col4 := alg_col4
  col5 := alg_col5
  normalize := alg_normalize
  complement := alg_complement
  dcBool := alg_dcBool
  encB := alg_encB
  rangeA := alg_rangeA
  rangeSq := alg_rangeSq
  rangeCc := alg_rangeCc
  rangeNd := alg_rangeNd
  rangeNc := alg_rangeNc
  rangeD := alg_rangeD
  high := alg_high
  slack := alg_slack
  exprs_norm := alg_exprs_norm
  exprs_enc := alg_exprs_enc
  norm_le := by decide
  enc_le := alg_enc_le
  idx_enc := alg_idx_enc
  exprs_length := alg_exprs_length
  sizes_A := alg_sizes_A
  primeA_all := by
    intro v hv
    change v ∈ [595, 596, 597, 598, 599, 600, 601, 602] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨value_s2_header.1, valueShape_role value_s2_header.2, valueShape_typeSource value_s2_header.2, value_s2_type.2, valueShape_field value_s2_header.2, isConstant_of_priv value_s2_kind⟩
    · exact ⟨value_signature_2es1_header.1, valueShape_role value_signature_2es1_header.2, valueShape_typeSource value_signature_2es1_header.2, value_signature_2es1_type.2, valueShape_field value_signature_2es1_header.2, isConstant_of_priv value_signature_2es1_kind⟩
    · exact ⟨value_norm_2ea_header.1, valueShape_role value_norm_2ea_header.2, valueShape_typeSource value_norm_2ea_header.2, value_norm_2ea_type.2, valueShape_field value_norm_2ea_header.2, isConstant_of_priv value_norm_2ea_kind⟩
    · exact ⟨value_norm_2esq_header.1, valueShape_role value_norm_2esq_header.2, valueShape_typeSource value_norm_2esq_header.2, value_norm_2esq_type.2, valueShape_field value_norm_2esq_header.2, isConstant_of_priv value_norm_2esq_kind⟩
    · exact ⟨value_norm_2ecc_header.1, valueShape_role value_norm_2ecc_header.2, valueShape_typeSource value_norm_2ecc_header.2, value_norm_2ecc_type.2, valueShape_field value_norm_2ecc_header.2, isConstant_of_priv value_norm_2ecc_kind⟩
    · exact ⟨value_norm_2end_header.1, valueShape_role value_norm_2end_header.2, valueShape_typeSource value_norm_2end_header.2, value_norm_2end_type.2, valueShape_field value_norm_2end_header.2, isConstant_of_priv value_norm_2end_kind⟩
    · exact ⟨value_norm_2enc_header.1, valueShape_role value_norm_2enc_header.2, valueShape_typeSource value_norm_2enc_header.2, value_norm_2enc_type.2, valueShape_field value_norm_2enc_header.2, isConstant_of_priv value_norm_2enc_kind⟩
    · exact ⟨value_norm_2eD_header.1, valueShape_role value_norm_2eD_header.2, valueShape_typeSource value_norm_2eD_header.2, value_norm_2eD_type.2, valueShape_field value_norm_2eD_header.2, isConstant_of_priv value_norm_2eD_kind⟩
  fields_A := ⟨valueShape_field value_norm_2eDc_header.2, isConstant_of_priv value_norm_2eDc_kind⟩
  noBound := alg_noBound
  consts_A := alg_consts_A
  const41 := alg_const41
  const555 := alg_const604
  i52_entry := by decide +kernel
  i54_entry := by decide +kernel
  i55_entry := by decide +kernel
  i56_entry := by decide +kernel
  i58_entry := by decide +kernel
  i59_entry := by decide +kernel
  i60_entry := by decide +kernel
  i61_entry := by decide +kernel
  i62_entry := by decide +kernel
  i63_entry := by decide +kernel
  i64_entry := by decide +kernel
  i65_entry := by decide +kernel
  i66_entry := by decide +kernel
  i67_entry := by decide +kernel
  i68_entry := by decide +kernel
  i52_size := by decide +kernel
  i54_size := by decide +kernel
  i55_size := by decide +kernel
  i56_size := by decide +kernel
  i67_size := by decide +kernel
  i69_entry := by decide +kernel
  i71_entry := by decide +kernel
  i72_entry := by decide +kernel
  i73_entry := by decide +kernel
  i74_entry := by decide +kernel
  i57_entry := by decide +kernel
  i70_entry := norm_i70_entry
  idx_sizes := by decide +kernel

section NormSound

variable {FH FA : RealizedProgram.FieldInterp} [HField FH] [AField FA]

/-- **The norm's obligation** (`Falcon512.Native.NormSound`): the generic norm's advice
(`Norm.algOf` at the slack's high digit) wherever the source program holds. -/
theorem normSound : Native.NormSound program FH FA := fun e hs => by
  obtain ⟨k, hk, hkv⟩ := Norm.slack_below (program := program) (I := RealizedProgram.falconInterpOf FH FA) hs
  have hs2 : s2Vals (program.reader e) = Norm.s2F (program := program) e :=
    funext fun i => Native.s2Vals_eq e i
  have hs1 : ∀ i, (Norm.algOf e ((k / 64 : ℕ) : (RealizedProgram.falconInterpOf FH FA 1).K)).s1 i =
      Native.rdA e 596 i := fun i => by
    rw [Norm.algOf_s1]
    rfl
  refine ⟨Norm.algOf e ((k / 64 : ℕ) : _), hs1, ?_, Norm.encodingBits hs _,
    ⟨Norm.digitsBelow hs, Norm.encodingRequests hs hk hkv⟩⟩
  rw [hs2]
  exact Norm.normHolds hs _

end NormSound

end GordieHowe.Falcon512.Native.ROMParams
