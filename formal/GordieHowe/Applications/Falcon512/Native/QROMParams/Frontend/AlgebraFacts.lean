-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Native.ROMParams.Frontend.Algebra
public import GordieHowe.Applications.Falcon512.Native.QROMParams.Frontend.Facts
public import GordieHowe.Applications.Falcon512.Frontend.Norm

@[expose] public section

/-!
# GordieHowe frontend: domain `A`'s facts of `Falcon512.Native.QROMParams`

The program facts domain `A` reads (`GordieHowe.Falcon512.Native.ROMParams.FalconAAlg`) for
`GordieHowe.Generated.Falcon512.Native.QROMParams.Program.program` (export `c825eb05`): the predicates by index and
body, the shared expressions, the values and the constants, by `decide` and `rfl` (generated data:
reading entries several hundred deep raises `maxRecDepth` for the `rfl` facts).
-/

namespace GordieHowe.Falcon512.Native.QROMParams

open Generated.Falcon512.Native.QROMParams.Program
open ROMParams

set_option maxRecDepth 4096 in
/-- `norm.center`. -/
theorem alg_center :
    ∃ t, (program.predicate 251).body = .equal 1 (.add (.mul (.ref 492) (.ref 492))
    (.scale (.const 12288) (.mul (.add (.add (.ref 493) (.scale (.const 64) (.ref 494)))
    (.scale (.const 4096) (.ref 495))) (.add (.add (.ref 493) (.scale (.const 64) (.ref 494)))
    (.scale (.const 4096) (.ref 495)))))) (.leaf 42) t :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.top`. -/
theorem alg_top :
    ∃ t, (program.predicate 252).body = .equal 1 (.ref 496) (.leaf 41) t :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.column0`. -/
theorem alg_col0 :
    ∃ real, (program.predicate 253).body =
    .mod 1 0 (.mul (.ref 497) (.ref 497)) (.add (.ref 498) (.scale (.const 64) (.ref 499))) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.column1`. -/
theorem alg_col1 :
    ∃ real, (program.predicate 254).body = .mod 1 0
    (.add (.scale (.const 2) (.mul (.ref 497) (.ref 500))) (.ref 501))
    (.add (.ref 502) (.scale (.const 64) (.ref 503))) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.column2`. -/
theorem alg_col2 :
    ∃ real, (program.predicate 255).body = .mod 1 0
    (.add (.add (.scale (.const 2) (.mul (.ref 497) (.ref 504))) (.mul (.ref 500) (.ref 500)))
    (.ref 505)) (.add (.ref 506) (.scale (.const 64) (.ref 507))) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.column3`. -/
theorem alg_col3 :
    ∃ real, (program.predicate 256).body = .mod 1 0
    (.add (.scale (.const 2) (.mul (.ref 500) (.ref 504))) (.ref 508))
    (.add (.ref 509) (.scale (.const 64) (.ref 510))) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.column4`. -/
theorem alg_col4 :
    ∃ real, (program.predicate 257).body = .mod 1 0 (.add (.mul (.ref 504) (.ref 504))
    (.ref 511)) (.add (.ref 512) (.scale (.const 64) (.ref 513))) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.column5`. -/
theorem alg_col5 :
    ∃ real, (program.predicate 258).body = .mod 1 0 (.ref 514) (.ref 515) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.normalize`. -/
theorem alg_normalize :
    ∃ real, (program.predicate 259).body = .mod 1 0
    (.add (.add (.ref 516) (.apply (.batched 102 (.sum 63)) (.ref 517))) (.ref 518))
    (.add (.leaf 551) (.scale (.const 64) (.ref 519))) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.complement`. -/
theorem alg_complement :
    ∃ real, (program.predicate 260).body = .mod 1 0
    (.add (.add (.ref 520) (.leaf 553)) (.ref 521)) (.add (.leaf 555) (.scale (.const 64) (.leaf 554)))
    real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.Dc.boolean`. -/
theorem alg_dcBool :
    ∃ t, (program.predicate 269).body = .equal 1 (.mul (.leaf 554) (.leaf 554)) (.leaf 554) t :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `encoding.b.boolean`. -/
theorem alg_encB :
    ∃ t, (program.predicate 271).body = .equal 1 (.mul (.ref 529) (.ref 529)) (.ref 529) t :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.a`. -/
theorem alg_rangeA :
    ∃ real, (program.predicate 273).body = .mem 1 [.leaf 548] (.range 64) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.sq`. -/
theorem alg_rangeSq :
    ∃ real, (program.predicate (273 + 1)).body = .mem 1 [.leaf 549] (.range 64) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.cc`. -/
theorem alg_rangeCc :
    ∃ real, (program.predicate (273 + 2)).body = .mem 1 [.leaf 550] (.range 189) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.nd`. -/
theorem alg_rangeNd :
    ∃ real, (program.predicate (273 + 3)).body = .mem 1 [.leaf 551] (.range 64) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.nc`. -/
theorem alg_rangeNc :
    ∃ real, (program.predicate (273 + 4)).body = .mem 1 [.leaf 552] (.range 64) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `norm.D`. -/
theorem alg_rangeD :
    ∃ real, (program.predicate (273 + 5)).body = .mem 1 [.leaf 553] (.range 64) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `encoding.high`. -/
theorem alg_high :
    ∃ real, (program.predicate 279).body = .mem 1 [.ref 526] (.range 16) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- `encoding.slack`. -/
theorem alg_slack :
    ∃ real, (program.predicate 280).body =
    .mem 1 [.add (.scale (.const 12288) (.apply (.sum 512) (.ref 526))) (.leaf 556)] (.range 393)
    real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- The field-form `signature.equation`. -/
theorem alg_sig :
    ∃ real, (program.predicate 284).body = .mod 1 12289
    (.add (.leaf 547) (.apply (.negacyclicConv 544 (.ntt 10302)) (.leaf 546)))
    (.apply (.batched 512 (.fromDigits 16 2)) (.leaf 545)) real :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- The norm's shared expressions. -/
theorem alg_exprs_norm :
    program.expr 492 =
    .add (.reindex idx52 (.concat (.leaf 547) (.leaf 41)))
    (.reindex idx53 (.concat (.leaf 546) (.leaf 41))) ∧
    program.expr 493 = .reindex idx54 (.leaf 548) ∧
    program.expr 494 = .reindex idx55 (.leaf 548) ∧
    program.expr 495 = .reindex idx56 (.concat (.leaf 548) (.leaf 41)) ∧
    program.expr 496 = .reindex idx57 (.leaf 554) ∧
    program.expr 497 = .reindex idx54 (.leaf 548) ∧
    program.expr 498 = .reindex idx58 (.leaf 549) ∧
    program.expr 499 = .reindex idx59 (.leaf 550) ∧
    program.expr 500 = .reindex idx55 (.leaf 548) ∧
    program.expr 501 = .reindex idx59 (.leaf 550) ∧
    program.expr 502 = .reindex idx60 (.leaf 549) ∧
    program.expr 503 = .reindex idx61 (.leaf 550) ∧
    program.expr 504 = .reindex idx56 (.concat (.leaf 548) (.leaf 41)) ∧
    program.expr 505 = .reindex idx61 (.leaf 550) ∧
    program.expr 506 = .reindex idx62 (.leaf 549) ∧
    program.expr 507 = .reindex idx63 (.leaf 550) ∧
    program.expr 508 = .reindex idx63 (.leaf 550) ∧
    program.expr 509 = .reindex idx64 (.leaf 549) ∧
    program.expr 510 = .reindex idx65 (.leaf 550) ∧
    program.expr 511 = .reindex idx65 (.leaf 550) ∧
    program.expr 512 = .reindex idx66 (.leaf 549) ∧
    program.expr 513 = .reindex idx67 (.leaf 550) ∧
    program.expr 514 = .reindex idx67 (.leaf 550) ∧
    program.expr 515 = .reindex idx68 (.leaf 549) ∧
    program.expr 516 = .reindex idx69 (.concat (.leaf 551) (.leaf 41)) ∧
    program.expr 517 = .reindex idx70 (.concat (.leaf 549) (.leaf 41)) ∧
    program.expr 518 = .reindex idx71 (.concat (.leaf 552) (.leaf 41)) ∧
    program.expr 519 = .reindex idx72 (.concat (.leaf 552) (.leaf 41)) ∧
    program.expr 520 = .reindex idx73 (.leaf 551) ∧
    program.expr 521 = .reindex idx74 (.concat (.leaf 554) (.leaf 41)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 4096 in
/-- The encoding's shared expressions. -/
theorem alg_exprs_enc :
    program.expr 526 = .reindex idx87 (.leaf 548) ∧
    program.expr 528 = .reindex idx88 (.leaf 548) ∧
    program.expr 529 = .add (.ref 528) (.scale (.const 12287) (.ref 526)) :=
  ⟨rfl, rfl, rfl⟩

/-- The encoding's shared expressions are below `532`. -/
theorem alg_enc_le :
    526 ≤ 532 ∧ 528 ≤ 532 ∧ 529 ≤ 532 := by
  decide +kernel

/-- The encoding's index maps. -/
theorem alg_idx_enc :
    (∀ j < 512, idx87.entry j = 3 * (512 + j) + 2) ∧
    (∀ j < 512, idx88.entry j = 3 * (512 + j) + 1) ∧ idx87.size = 512 ∧ idx88.size = 512 := by
  decide +kernel

/-- The shared expressions domain `A` reads are below the table's length. -/
theorem alg_exprs_length :
    532 < program.exprs.length := by
  decide +kernel

/-- The sizes of the values domain `A` reads. -/
theorem alg_sizes_A :
    (program.value 546).size = 512 ∧ (program.value 547).size = 512 ∧
    (program.value 548).size = 3072 ∧ (program.value 549).size = 6144 ∧
    (program.value 550).size = 5120 ∧ (program.value 551).size = 102 ∧
    (program.value 552).size = 85 ∧ (program.value 553).size = 6 ∧
    (program.value 554).size = 6 ∧ (program.value 41).size = 1 ∧
    (program.value 42).size = 1024 := by
  decide +kernel

/-- The program binds no value to an expression. -/
theorem alg_noBound :
    ∀ v < program.values.length,
    (match (program.value v).kind with
    | .bound _ => false
    | _ => true) = true := by
  decide +kernel

/-- The zero constants `41`, `42` and the slack offset `556`. -/
theorem alg_consts_A :
    program.isConstant 41 = true ∧ program.valueField 41 = 1 ∧
    (program.constEntries 41).getD 0 0 = 0 ∧ program.isConstant 42 = true ∧
    program.valueField 42 = 1 ∧ program.constEntries 42 = List.replicate 1024 0 ∧
    program.isConstant 556 = true ∧ program.valueField 556 = 1 ∧
    (program.constEntries 556).getD 0 0 = 392 := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- The constant `41` is zero. -/
theorem alg_const41 :
    ∃ es, (program.value 41).kind = .constant es ∧ es.getD 0 0 = 0 :=
  ⟨_, rfl, rfl⟩

set_option maxRecDepth 4096 in
/-- The constant `555` holds the base-`64` digits of `β² = 34034726`. -/
theorem alg_const555 :
    program.valueField 555 = 1 ∧ ∃ es, (program.value 555).kind = .constant es ∧
    ∀ m < 6, es.getD m 0 = NativeNorm.digit 34034726 m :=
  ⟨by decide +kernel, _, rfl, by decide⟩

set_option maxRecDepth 4096 in
/-- `statement.hhat` is an opaque statement value of no argument. -/
theorem alg_hhatKind :
    (program.value 544).kind = .pub (.opaque "statement.hhat" []) :=
  rfl

/-- The named operators of `signature.equation`. -/
theorem alg_ops_sig :
    RealizedProgram.NamedOp.cols program (.negacyclicConv 544 (.ntt 10302)) = 512 ∧
    RealizedProgram.NamedOp.rows program (.negacyclicConv 544 (.ntt 10302)) = 512 ∧
    RealizedProgram.NamedOp.cols program (.batched 512 (.fromDigits 16 2)) = 8192 ∧
    RealizedProgram.NamedOp.rows program (.batched 512 (.fromDigits 16 2)) = 512 := by
  decide +kernel

/-- The program's facts of domain `A` beyond the norm. -/
instance : FalconAAlg program where
  cA_eq := rfl
  s2_eq := rfl
  pSig := 284
  inSource_sig := by decide +kernel
  sig := alg_sig
  sizes_sig := by decide +kernel
  primeA_sig := by decide +kernel
  fields_cA := by decide +kernel
  noBound := alg_noBound
  hhatKind := alg_hhatKind
  ops_sig := alg_ops_sig

/-- The norm's index maps of the batches (`6426` entries, decided coordinate by coordinate). -/
theorem norm_i70_entry : ∀ b < 17, ∀ m < 6, ∀ s < 63, idx70.entry ((6 * b + m) * 63 + s) =
    if 63 * b + s < 1024 then 6 * (63 * b + s) + m else 6144 := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- **The generic norm's identifiers and facts** at domain `A` (`FalconNorm`, domain and field
`1`). -/
instance : Norm.FalconNorm program where
  dA := 1
  fA := 1
  domainField := by decide +kernel
  s2 := 546
  s1 := 547
  a := 548
  sq := 549
  cc := 550
  nd := 551
  nc := 552
  D := 553
  Dc := 554
  tgt := 555
  off := 556
  z1 := 41
  z := 42
  e0 := 492
  p0 := 251
  eMax := 532
  pDc := 269
  pEncB := 271
  pRange := 273
  pHigh := 279
  pSlack := 280
  eHigh := 526
  eMid := 528
  eB := 529
  iHigh := idx87
  iMid := idx88
  i52 := idx52
  i53 := idx53
  i54 := idx54
  i55 := idx55
  i56 := idx56
  i57 := idx57
  i58 := idx58
  i59 := idx59
  i60 := idx60
  i61 := idx61
  i62 := idx62
  i63 := idx63
  i64 := idx64
  i65 := idx65
  i66 := idx66
  i67 := idx67
  i68 := idx68
  i69 := idx69
  i70 := idx70
  i71 := idx71
  i72 := idx72
  i73 := idx73
  i74 := idx74
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
  const555 := alg_const555
  i52_entry := by decide +kernel
  i53_entry := by decide +kernel
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

/-- **The norm's obligation** (`ROMParams.NormSound`): the generic norm's advice
(`Norm.algOf` at the slack's high digit) wherever the source program holds. -/
theorem normSound : ROMParams.NormSound program FH FA := fun e hs => by
  obtain ⟨k, hk, hkv⟩ := Norm.slack_below (program := program) (I := RealizedProgram.falconInterpOf FH FA) hs
  have hs2 : s2Vals (program.reader e) = Norm.s2F (program := program) e :=
    funext fun i => ROMParams.s2Vals_eq e i
  have hs1 : ∀ i, (Norm.algOf e ((k / 64 : ℕ) : (RealizedProgram.falconInterpOf FH FA 1).K)).s1 i =
      ROMParams.rdA e 547 i := fun i => by
    rw [Norm.algOf_s1]
    rfl
  refine ⟨Norm.algOf e ((k / 64 : ℕ) : _), hs1, ?_, Norm.encodingBits hs _,
    ⟨Norm.digitsBelow hs, Norm.encodingRequests hs hk hkv⟩⟩
  rw [hs2]
  exact Norm.normHolds hs _

end NormSound

end GordieHowe.Falcon512.Native.QROMParams
