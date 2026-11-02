-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Native.Frontend.Algebra
public import GordieHowe.Applications.Falcon512.Native.QROMParams.Frontend.Facts
public import GordieHowe.Applications.Falcon512.Frontend.Norm

@[expose] public section

/-!
# GordieHowe frontend: domain `A`'s facts of `Falcon512.Native.QROMParams`

The program facts domain `A` reads (`GordieHowe.Falcon512.Native.FalconAAlg`) for
`GordieHowe.Generated.Falcon512.Native.QROMParams.Program.program` (export `3ed06086`): the predicates by index and
body, the shared expressions, the values and the constants, by `decide` and `rfl` (generated data:
reading entries several hundred deep raises `maxRecDepth` for the `rfl` facts).
-/

namespace GordieHowe.Falcon512.Native.QROMParams

open Generated.Falcon512.Native.QROMParams.Program

set_option maxRecDepth 4096 in
/-- `norm.center`. -/
theorem alg_center :
    ∃ t, (program.predicate 275).body = .equal 1 (.add (.mul (.ref 540) (.ref 540))
    (.scale (.const 12288) (.mul (.add (.add (.ref 541) (.scale (.const 64) (.ref 542)))
    (.scale (.const 4096) (.ref 543))) (.add (.add (.ref 541) (.scale (.const 64) (.ref 542)))
    (.scale (.const 4096) (.ref 543)))))) (.leaf 42) t :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.top`. -/
theorem alg_top :
    ∃ t, (program.predicate 276).body = .equal 1 (.ref 544) (.leaf 41) t :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.column0`. -/
theorem alg_col0 :
    ∃ real, (program.predicate 277).body =
    .mod 1 0 (.mul (.ref 545) (.ref 545)) (.add (.ref 546) (.scale (.const 64) (.ref 547))) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.column1`. -/
theorem alg_col1 :
    ∃ real, (program.predicate 278).body = .mod 1 0
    (.add (.scale (.const 2) (.mul (.ref 545) (.ref 548))) (.ref 549))
    (.add (.ref 550) (.scale (.const 64) (.ref 551))) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.column2`. -/
theorem alg_col2 :
    ∃ real, (program.predicate 279).body = .mod 1 0
    (.add (.add (.scale (.const 2) (.mul (.ref 545) (.ref 552))) (.mul (.ref 548) (.ref 548)))
    (.ref 553)) (.add (.ref 554) (.scale (.const 64) (.ref 555))) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.column3`. -/
theorem alg_col3 :
    ∃ real, (program.predicate 280).body = .mod 1 0
    (.add (.scale (.const 2) (.mul (.ref 548) (.ref 552))) (.ref 556))
    (.add (.ref 557) (.scale (.const 64) (.ref 558))) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.column4`. -/
theorem alg_col4 :
    ∃ real, (program.predicate 281).body = .mod 1 0 (.add (.mul (.ref 552) (.ref 552))
    (.ref 559)) (.add (.ref 560) (.scale (.const 64) (.ref 561))) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.column5`. -/
theorem alg_col5 :
    ∃ real, (program.predicate 282).body = .mod 1 0 (.ref 562) (.ref 563) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.normalize`. -/
theorem alg_normalize :
    ∃ real, (program.predicate 283).body = .mod 1 0
    (.add (.add (.ref 564) (.apply (.batched 102 (.sum 63)) (.ref 565))) (.ref 566))
    (.add (.leaf 600) (.scale (.const 64) (.ref 567))) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.complement`. -/
theorem alg_complement :
    ∃ real, (program.predicate 284).body = .mod 1 0
    (.add (.add (.ref 568) (.leaf 602)) (.ref 569)) (.add (.leaf 604) (.scale (.const 64) (.leaf 603)))
    real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.Dc.boolean`. -/
theorem alg_dcBool :
    ∃ t, (program.predicate 293).body = .equal 1 (.mul (.leaf 603) (.leaf 603)) (.leaf 603) t :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `encoding.b.boolean`. -/
theorem alg_encB :
    ∃ t, (program.predicate 295).body = .equal 1 (.mul (.ref 577) (.ref 577)) (.ref 577) t :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.a`. -/
theorem alg_rangeA :
    ∃ real, (program.predicate 297).body = .mem 1 [.leaf 597] (.range 64) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.sq`. -/
theorem alg_rangeSq :
    ∃ real, (program.predicate (297 + 1)).body = .mem 1 [.leaf 598] (.range 64) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.cc`. -/
theorem alg_rangeCc :
    ∃ real, (program.predicate (297 + 2)).body = .mem 1 [.leaf 599] (.range 189) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.nd`. -/
theorem alg_rangeNd :
    ∃ real, (program.predicate (297 + 3)).body = .mem 1 [.leaf 600] (.range 64) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.nc`. -/
theorem alg_rangeNc :
    ∃ real, (program.predicate (297 + 4)).body = .mem 1 [.leaf 601] (.range 64) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.D`. -/
theorem alg_rangeD :
    ∃ real, (program.predicate (297 + 5)).body = .mem 1 [.leaf 602] (.range 64) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `encoding.high`. -/
theorem alg_high :
    ∃ real, (program.predicate 303).body = .mem 1 [.ref 574] (.range 16) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `encoding.slack`. -/
theorem alg_slack :
    ∃ real, (program.predicate 304).body =
    .mem 1 [.add (.scale (.const 12288) (.apply (.sum 512) (.ref 574))) (.leaf 605)] (.range 393)
    real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- The field-form `signature.equation`. -/
theorem alg_sig :
    ∃ real, (program.predicate 308).body = .mod 1 12289
    (.add (.leaf 596) (.apply (.negacyclicConv 593 (.ntt 10302)) (.leaf 595)))
    (.apply (.batched 512 (.fromDigits 16 2)) (.leaf 594)) real ∧ real.form.isProduct = false :=
  ⟨_, rfl, rfl⟩

set_option maxRecDepth 4096 in
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
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 4096 in
/-- The encoding's shared expressions. -/
theorem alg_exprs_enc :
    program.expr 574 = .reindex idx75 (.leaf 597) ∧
    program.expr 576 = .reindex idx76 (.leaf 597) ∧
    program.expr 577 = .add (.ref 576) (.scale (.const 12287) (.ref 574)) :=
  ⟨rfl, rfl, rfl⟩

/-- The encoding's shared expressions are below `580`. -/
theorem alg_enc_le :
    574 ≤ 580 ∧ 576 ≤ 580 ∧ 577 ≤ 580 := by
  decide +kernel

/-- The encoding's index maps. -/
theorem alg_idx_enc :
    (∀ j < 512, idx75.entry j = 3 * (512 + j) + 2) ∧
    (∀ j < 512, idx76.entry j = 3 * (512 + j) + 1) ∧ idx75.size = 512 ∧ idx76.size = 512 := by
  decide +kernel

/-- The shared expressions domain `A` reads are below the table's length. -/
theorem alg_exprs_length :
    580 < program.exprs.length := by
  decide +kernel

/-- The sizes of the values domain `A` reads. -/
theorem alg_sizes_A :
    (program.value 595).size = 512 ∧ (program.value 596).size = 512 ∧
    (program.value 597).size = 3072 ∧ (program.value 598).size = 6144 ∧
    (program.value 599).size = 5120 ∧ (program.value 600).size = 102 ∧
    (program.value 601).size = 85 ∧ (program.value 602).size = 6 ∧
    (program.value 603).size = 6 ∧ (program.value 41).size = 1 ∧
    (program.value 42).size = 1024 := by
  decide +kernel

/-- The program binds no value to an expression. -/
theorem alg_noBound :
    ∀ v < program.values.length,
    (match (program.value v).kind with
    | .bound _ => false
    | _ => true) = true := by
  decide +kernel

/-- The zero constants `41`, `42` and the slack offset `605`. -/
theorem alg_consts_A :
    program.isConstant 41 = true ∧ program.valueField 41 = 1 ∧
    (program.constEntries 41).getD 0 0 = 0 ∧ program.isConstant 42 = true ∧
    program.valueField 42 = 1 ∧ program.constEntries 42 = List.replicate 1024 0 ∧
    program.isConstant 605 = true ∧ program.valueField 605 = 1 ∧
    (program.constEntries 605).getD 0 0 = 392 := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- The constant `41` is zero. -/
theorem alg_const41 :
    ∃ es, (program.value 41).kind = .constant es ∧ es.getD 0 0 = 0 :=
  ⟨_, rfl, rfl⟩

set_option maxRecDepth 4096 in
/-- The constant `604` holds the base-`64` digits of `β² = 34034726`. -/
theorem alg_const604 :
    program.valueField 604 = 1 ∧ ∃ es, (program.value 604).kind = .constant es ∧
    ∀ m < 6, es.getD m 0 = NativeNorm.digit 34034726 m :=
  ⟨by decide +kernel, _, rfl, by decide⟩

set_option maxRecDepth 4096 in
/-- `statement.hhat` is an opaque statement value of no argument. -/
theorem alg_hhatKind :
    (program.value 593).kind = .pub (.opaque "statement.hhat" []) :=
  rfl

/-- The named operators of `signature.equation`. -/
theorem alg_ops_sig :
    RealizedProgram.NamedOp.cols program (.negacyclicConv 593 (.ntt 10302)) = 512 ∧
    RealizedProgram.NamedOp.rows program (.negacyclicConv 593 (.ntt 10302)) = 512 ∧
    RealizedProgram.NamedOp.cols program (.batched 512 (.fromDigits 16 2)) = 8192 ∧
    RealizedProgram.NamedOp.rows program (.batched 512 (.fromDigits 16 2)) = 512 := by
  decide +kernel

/-- The program's facts of domain `A` beyond the norm. -/
instance : FalconAAlg program where
  cA_eq := rfl
  s2_eq := rfl
  pSig := 308
  inSource_sig := by decide +kernel
  sig := alg_sig
  sizes_sig := by decide +kernel
  primeA_sig := by decide +kernel
  fields_cA := by decide +kernel
  noBound := alg_noBound
  hhatKind := alg_hhatKind
  ops_sig := alg_ops_sig

/-- The norm's index maps of the batches (`6426` entries, decided coordinate by coordinate). -/
theorem norm_i70_entry : ∀ b < 17, ∀ m < 6, ∀ s < 63, idx58.entry ((6 * b + m) * 63 + s) =
    if 63 * b + s < 1024 then 6 * (63 * b + s) + m else 6144 := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- **The generic norm's identifiers and facts** at domain `A` (`FalconNorm`, domain and field
`1`). -/
instance : Norm.FalconNorm program where
  dA := 1
  fA := 1
  domainField := by decide +kernel
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
  eMax := 580
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
  refsOrdered := (RealizedProgram.refsOrderedB_iff program).1 (by decide +kernel)
  inSource_A := by decide +kernel
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
  primeA_all := by decide +kernel
  fields_A := by decide +kernel
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

end GordieHowe.Falcon512.Native.QROMParams
