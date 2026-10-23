-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Frontend.Cross
public import GordieHowe.Language.Library.Select
public import GordieHowe.Applications.MLDSA44.System.RisingSelection
public import GordieHowe.Applications.MLDSA44.System.Fields

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Native.ROMParams`, SampleInBall's selection

SampleInBall's rejection sampling (`examples/mldsa/sample_in_ball.h`, `sample_in_ball_select`:
`select_first` over the stream bytes `8 … 271` of `h2c.sib.out` with the scan `SampleInBallScan`)
read off the program's predicates `h2c.sample.select.start`, `.step` and `.route` (predicates
`264`–`266`), as the hand-built gadget `SelectFirstTau.run` (`selectRun`) on the candidate bytes,
the selected bytes `h2c.sample.select.j` (value `557`), the committed low threshold bits
`h2c.sample.select.threshold` (value `559`) and `δ = h2c.sample.select.delta` (value `560`), at the
selection field at the ROM parameters (`ROMParams.fieldData.sel`):

* the decoded thresholds (the shared expression `508`) are `SelectFirstTau.decode` of the low bits
  (`thrBits_eq`: bits `6` and `7` the `OR` of low bits `4` and `5`);
* the acceptance (`511`, `Logic::leq`) is `Bits.leVar`, the selection (`512`) is
  `SelectFirstTau.selected` (`full` from position `39` on, the threshold's top bit);
* `.start` is `SelectFirstTau.initialOk`, `.step` (the Sklansky prefix ANDs, `513`–`519`) is
  `SelectFirstTau.stepOk`, `.route` (the two products) is `SelectFirstTau.fingerprintOk`.
-/

namespace GordieHowe.MLDSA44.Native.ROMParams

open Generated.MLDSA44.Native.ROMParams.Program
open GordieHowe.Bits

/-- **The program facts of domain `H` SampleInBall's selection reads** (`MldsaHCross` and): the selection's predicates `264`–`266` and shared expressions `508`–`519` (with the index maps of the program at the ROM parameters), their constants, lengths and the selected bytes' type. Each program instantiates it by `decide`. -/
class MldsaHSelect (program : RealizedProgram) : Prop extends MldsaHCross program where
  /-- Value `555` is a bit view. -/
  bitView555 : program.isBitView 555 = true
  /-- Value `556` is a bit view. -/
  bitView556 : program.isBitView 556 = true
  /-- Value `559` is a bit view. -/
  bitView559 : program.isBitView 559 = true
  /-- `pred264`. -/
  pred264 : program.predicate 264 = «p.h2c.sample.select.start»
  /-- `pred265`. -/
  pred265 : program.predicate 265 = «p.h2c.sample.select.step»
  /-- `pred266`. -/
  pred266 : program.predicate 266 = «p.h2c.sample.select.route»
  /-- `expr508`. -/
  expr508 : program.expr 508 = .reindex idx51 (.concat (.leaf 559) (.reindex idx50 (.reindex idx49 (.logic .any 2 [.reindex idx48 (.leaf 559)]))))
  /-- `expr509`. -/
  expr509 : program.expr 509 = .reindex idx54 (.ref 508)
  /-- `expr510`. -/
  expr510 : program.expr 510 = .add (.reindex idx55 (.concat (.leaf 555) (.leaf 36))) (.reindex idx56 (.concat (.leaf 556) (.leaf 36)))
  /-- `expr511`. -/
  expr511 : program.expr 511 = .logic .leq 8 [.ref 510, .ref 508]
  /-- `expr512`. -/
  expr512 : program.expr 512 = .reindex idx49 (.concat (.reindex idx57 (.ref 511)) (.mul (.reindex idx58 (.ref 511)) (.sub (.leaf 45) (.sub (.leaf 45) (.reindex idx60 (.reindex idx59 (.ref 508)))))))
  /-- `expr513`. -/
  expr513 : program.expr 513 = .reindex idx61 (.ref 512)
  /-- `expr514`. -/
  expr514 : program.expr 514 = .reindex idx62 (.ref 509)
  /-- `expr515`. -/
  expr515 : program.expr 515 = .mul (.reindex idx64 (.ref 509)) (.ref 514)
  /-- `expr516`. -/
  expr516 : program.expr 516 = .reindex idx66 (.ref 509)
  /-- `expr517`. -/
  expr517 : program.expr 517 = .mul (.mul (.reindex idx68 (.ref 509)) (.ref 516)) (.ref 515)
  /-- `expr518`. -/
  expr518 : program.expr 518 = .reindex idx70 (.ref 509)
  /-- `expr519`. -/
  expr519 : program.expr 519 = .mul (.reindex idx72 (.ref 509)) (.ref 518)
  /-- The selection's shared expressions are in the table. -/
  refsSel : 519 < program.exprs.length
  /-- The constants of the thresholds and the acceptance. -/
  selConstsA : program.isConstant 36 = true ∧ program.constEntries 36 = [0] ∧ program.isConstant 45 = true ∧ program.constEntries 45 = List.replicate 225 1 ∧ program.valueField 36 = 1 ∧ program.valueField 45 = 1 ∧ (program.value 559).size = 1584 ∧ (program.value 555).size = 1088 ∧ (program.value 556).size = 1088
  /-- The facts of the selected bytes' type. -/
  jFacts : 557 < program.values.length ∧ program.IsSourceValue 557 ∧ (program.value 557).typeSource = .node ∧ (program.value 557).type = .bit ∧ (program.value 557).size = 312
  /-- The lengths of the selection's pieces. -/
  selLens : program.exprLen (.reindex idx57 (.ref 511)) = 39
  /-- The constants of the start and the steps. -/
  stepConsts : program.isConstant 43 = true ∧ program.constEntries 43 = [1, 0, 0, 1, 1, 0, 1, 1] ∧ program.isConstant 44 = true ∧ program.constEntries 44 = List.replicate 8 0 ∧ program.isConstant 46 = true ∧ program.constEntries 46 = List.replicate 2104 0 ∧ program.valueField 43 = 1 ∧ program.valueField 44 = 1 ∧ program.valueField 46 = 1
  /-- The constants of the route. -/
  routeConsts : program.isConstant 37 = true ∧ program.valueField 37 = 1 ∧ (program.constEntries 37).getD 0 0 = 1 ∧ program.isConstant 47 = true ∧ program.valueField 47 = 1 ∧ program.isConstant 7 = true ∧ program.valueField 7 = 1 ∧ program.constEntries 7 = [1] ∧ (∀ j < 39, (program.constEntries 47).getD j 0 = RealizedProgram.xorSel (217 + j) fun u => (program.constEntries 37).getD u 0)
  /-- The length of the route's candidate product's operand. -/
  routeLens : program.exprLen (.reindex idx76 (.leaf 560)) = 264

set_option maxRecDepth 4096 in
/-- The native program at the ROM parameters has these facts. -/
instance : MldsaHSelect program where
  bitView555 := by decide +kernel
  bitView556 := by decide +kernel
  bitView559 := by decide +kernel
  pred264 := rfl
  pred265 := rfl
  pred266 := rfl
  expr508 := rfl
  expr509 := rfl
  expr510 := rfl
  expr511 := rfl
  expr512 := rfl
  expr513 := rfl
  expr514 := rfl
  expr515 := rfl
  expr516 := rfl
  expr517 := rfl
  expr518 := rfl
  expr519 := rfl
  refsSel := by decide +kernel
  selConstsA := by
    decide +kernel
  jFacts := by
    decide +kernel
  selLens := by decide +kernel
  stepConsts := by
    decide +kernel
  routeConsts := by
    decide +kernel
  routeLens := by decide +kernel

open GF2_128Exec in
/-- **The embedding basis as spread products**: entry `j + 1` of the constant `37` is entry `j`
times `g`. -/
theorem gpow37_chain : ∀ j < 7, gf2_128Exec.mul
    (gf2_128Exec.ofBits (BitVec.ofNat 128 ((program.constEntries 37).getD j 0)).toNat)
    (gf2_128Exec.ofBits gf2_128SubfieldGenBV.toNat) =
    gf2_128Exec.ofBits (BitVec.ofNat 128 ((program.constEntries 37).getD (j + 1) 0)).toNat := by
  decide +kernel

open GF2_128Exec in
/-- **Entry `j` of the constant `37` is `g^j`** (`gpow37_chain`, from entry `0 = 1`). -/
theorem c37_eq : ∀ j < 8,
    gf2_128OfNat ((program.constEntries 37).getD j 0) = gf2_128SubfieldGen ^ j
  | 0, _ => by rw [MldsaHSelect.routeConsts.2.2.1, gf2_128OfNat_one, pow_zero]
  | j + 1, hj => by
    have hmul := gfMul_eq_of_spread (gpow37_chain j (by omega))
    have := congrArg gf2_128OfBitVec hmul
    rw [gf2_128OfBitVec_gfMul, gf2_128OfBitVec_subfieldGenBV] at this
    change gf2_128OfNat _ * _ = gf2_128OfNat _ at this
    rw [← this, c37_eq j (by omega), pow_succ]

/-- **The program-and-field facts of domain `H` SampleInBall's selection reads**: entry `j < 8` of
the constant `37` decodes to the selection field's embedding basis `e_j`. Each program and field
instantiates it once. -/
class MldsaHConstsSelect (program : RealizedProgram) (FH : RealizedProgram.FieldInterp) [HField FH] : Prop where
  /-- Entry `j < 8` of the constant `37` is `e_j`. -/
  c37 : ∀ j (hj : j < 8), FH.decode ((program.constEntries 37).getD j 0) =
    (HField.sel (FH := FH)).e ⟨j, by change j < 16; omega⟩

/-- The native program at the ROM parameters, over `GF(2^128)`: entry `j` of `37` is `g^j = e_j`. -/
instance : MldsaHConstsSelect program RealizedProgram.gf128 where
  c37 j hj := c37_eq j hj

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaHSelect program] {F0 FH : RealizedProgram.FieldInterp} [HField FH]
  [MldsaHConstsSelect program FH]

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

/-! ## The program's data -/

section Tables

set_option maxRecDepth 4096

theorem pred264 : program.predicate 264 = «p.h2c.sample.select.start» :=
  MldsaHSelect.pred264
theorem pred265 : program.predicate 265 = «p.h2c.sample.select.step» :=
  MldsaHSelect.pred265
theorem pred266 : program.predicate 266 = «p.h2c.sample.select.route» :=
  MldsaHSelect.pred266
theorem expr508 : program.expr 508 = .reindex idx51 (.concat (.leaf 559) (.reindex idx50 (.reindex idx49 (.logic .any 2 [.reindex idx48 (.leaf 559)])))) :=
  MldsaHSelect.expr508
theorem expr509 : program.expr 509 = .reindex idx54 (.ref 508) :=
  MldsaHSelect.expr509
theorem expr510 : program.expr 510 = .add (.reindex idx55 (.concat (.leaf 555) (.leaf 36))) (.reindex idx56 (.concat (.leaf 556) (.leaf 36))) :=
  MldsaHSelect.expr510
theorem expr511 : program.expr 511 = .logic .leq 8 [.ref 510, .ref 508] :=
  MldsaHSelect.expr511
theorem expr512 : program.expr 512 = .reindex idx49 (.concat (.reindex idx57 (.ref 511)) (.mul (.reindex idx58 (.ref 511)) (.sub (.leaf 45) (.sub (.leaf 45) (.reindex idx60 (.reindex idx59 (.ref 508))))))) :=
  MldsaHSelect.expr512
theorem expr513 : program.expr 513 = .reindex idx61 (.ref 512) :=
  MldsaHSelect.expr513
theorem expr514 : program.expr 514 = .reindex idx62 (.ref 509) :=
  MldsaHSelect.expr514
theorem expr515 : program.expr 515 = .mul (.reindex idx64 (.ref 509)) (.ref 514) :=
  MldsaHSelect.expr515
theorem expr516 : program.expr 516 = .reindex idx66 (.ref 509) :=
  MldsaHSelect.expr516
theorem expr517 : program.expr 517 = .mul (.mul (.reindex idx68 (.ref 509)) (.ref 516)) (.ref 515) :=
  MldsaHSelect.expr517
theorem expr518 : program.expr 518 = .reindex idx70 (.ref 509) :=
  MldsaHSelect.expr518
theorem expr519 : program.expr 519 = .mul (.reindex idx72 (.ref 509)) (.ref 518) :=
  MldsaHSelect.expr519
end Tables

/-- The selection's shared expressions are in the table. -/
theorem refsSel : 519 < program.exprs.length :=
  MldsaHSelect.refsSel
instance charP_interp1 : CharP (interp 1).K 2 := HField.charTwo

/-! ## Readings -/

/-- **The SampleInBall stream's bytes** (`h2c.sib.out`). -/
def sibByte (rd : program.Valuation interp) : Fin (264 + 8) → BitWires (interp 1).K 8 :=
  Falcon512.HashCircuit.byteWires (sibBits rd)

/-- **The candidate bytes**: bytes `8 … 271` of the stream (`HashCircuit.candidates`). -/
def candBits (rd : program.Valuation interp) : Fin 264 → BitWires (interp 1).K 8 :=
  HashCircuit.candidates (sibByte rd)

/-- **The selected bytes** (`h2c.sample.select.j`, value `557`, `39 × 8` bits). -/
def jBits (rd : program.Valuation interp) (j : Fin 39) : BitWires (interp 1).K 8 :=
  fun b => program.evalE rd 1 (.leaf 557) (8 * j + b)

/-- **The committed low threshold bits** (`h2c.sample.select.threshold`, value `559`, `264 × 6`). -/
def lowThr (rd : program.Valuation interp) (i : Fin 264) :
    BitWires (interp 1).K (SelectFirstTau.lowBits 39) :=
  fun b => program.evalE rd 1 (.leaf 559) (6 * i + b)

/-- **The decoded thresholds** (the shared expression `508`, `264 × 8` bits). -/
def thrBits (rd : program.Valuation interp) (i : Fin 264) : BitWires (interp 1).K 8 :=
  fun b => program.evalE rd 1 (.ref 508) (8 * i + b)

/-- **`δ` of the selection** (`h2c.sample.select.delta`, value `560`). -/
def selDelta (rd : program.Valuation interp) : (interp 1).K :=
  program.evalE rd 1 (.leaf 560) 0

theorem lowBits_39 : SelectFirstTau.lowBits 39 = 6 := by decide
theorem highFrom_39 : SelectFirstTau.highFrom 39 = 4 := by decide

/-! The index maps of the thresholds and the acceptance. -/

theorem idx48_eq {i t : ℕ} (hi : i < 264) (ht : t < 2) : idx48.entry (2 * i + t) = 6 * i + 4 + t := by
  unfold idx48
  rw [RealizedProgram.IndexMap.entry_rep (c := 2) (fun j => by simp [RealizedProgram.IndexMap.size, RealizedProgram.IdxSeg.shift]) hi ht]
  simp [RealizedProgram.IndexMap.entry, RealizedProgram.IdxSeg.shift, ht]
  omega
theorem idx49_eq {i : ℕ} (hi : i < 264) : idx49.entry i = i := by
  unfold idx49
  simp [RealizedProgram.IndexMap.ofSegs, RealizedProgram.IdxSeg.expand, RealizedProgram.IndexMap.entry, hi]
theorem idx50_eq {i t : ℕ} (hi : i < 264) (ht : t < 2) : idx50.entry (2 * i + t) = i := by
  unfold idx50
  rw [RealizedProgram.IndexMap.entry_rep (c := 2) (fun j => by simp [RealizedProgram.IndexMap.size, RealizedProgram.IdxSeg.shift]) hi ht]
  simp [RealizedProgram.IndexMap.entry, RealizedProgram.IdxSeg.shift, ht]
theorem idx51_eq {i b : ℕ} (hi : i < 264) (hb : b < 8) :
    idx51.entry (8 * i + b) = if b < 6 then 6 * i + b else 1584 + 2 * i + (b - 6) := by
  unfold idx51
  rw [RealizedProgram.IndexMap.entry_rep (c := 8) (fun j => by simp [RealizedProgram.IndexMap.size, RealizedProgram.IdxSeg.shift]) hi hb]
  simp only [List.map_cons, List.map_nil, RealizedProgram.IndexMap.entry, RealizedProgram.IdxSeg.shift]
  split_ifs <;> omega


/-- The constants of the thresholds and the acceptance. -/
theorem selConstsA : program.isConstant 36 = true ∧ program.constEntries 36 = [0] ∧ program.isConstant 45 = true ∧ program.constEntries 45 = List.replicate 225 1 ∧ program.valueField 36 = 1 ∧ program.valueField 45 = 1 ∧ (program.value 559).size = 1584 ∧ (program.value 555).size = 1088 ∧ (program.value 556).size = 1088 :=
  MldsaHSelect.selConstsA
/-- `OR` of bits `4` and `5`. -/
theorem orRange_4_6 (f : ℕ → (interp 1).K) :
    Bits.orRange f 4 (SelectFirstTau.lowBits 39) = Bits.bor (f 4) (f 5) := by
  rw [lowBits_39, Bits.orRange, if_neg (by norm_num), if_neg (by norm_num), Bits.orRange, if_neg (by norm_num),
    if_pos rfl, Bits.orRange, if_neg (by norm_num), if_pos rfl]

/-- **The decoded thresholds are `SelectFirstTau.decode` of the low bits** (the shared expression
`508`: the low bits, then the `OR` of low bits `4` and `5` twice). -/
theorem thrBits_eq (rd : program.Valuation interp) (i : Fin 264) :
    thrBits rd i = SelectFirstTau.decode 39 (lowThr rd i) := by
  funext b
  have hb := b.isLt
  have hi := i.isLt
  unfold thrBits
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsSel (program := program)); omega), (expr508 (program := program)), RealizedProgram.evalE_reindex,
    idx51_eq hi hb, RealizedProgram.evalE_concat, RealizedProgram.exprLen_leaf, (selConstsA (program := program)).2.2.2.2.2.2.1]
  unfold SelectFirstTau.decode
  by_cases h6 : (b : ℕ) < 6
  · rw [if_pos h6, if_pos (by omega), dif_pos (by rw [lowBits_39]; exact h6)]
    rfl
  · rw [if_neg h6, if_neg (by omega), dif_neg (by rw [lowBits_39]; exact h6), highFrom_39,
      orRange_4_6, show 1584 + 2 * (i : ℕ) + (b - 6) - 1584 = 2 * i + (b - 6) by omega,
      RealizedProgram.evalE_reindex, idx50_eq hi (by omega), RealizedProgram.evalE_reindex, idx49_eq hi,
      RealizedProgram.evalE_logic₁]
    simp only [RealizedProgram.LogicOp.eval, List.headD_cons]
    rw [RealizedProgram.Ops.orTree_two, RealizedProgram.Ops.lor]
    simp only [RealizedProgram.evalE_reindex]
    rw [show (i : ℕ) * 2 + (0 + 0) = 2 * i + 0 by ring, idx48_eq hi (by norm_num),
      show (i : ℕ) * 2 + (0 + 1) = 2 * i + 1 by ring, idx48_eq hi (by norm_num)]
    rw [dif_pos (show (4 : ℕ) < SelectFirstTau.lowBits 39 by decide),
      dif_pos (show (5 : ℕ) < SelectFirstTau.lowBits 39 by decide)]
    simp only [Bits.bor, Bits.bnot]
    rfl


/-! ## The candidates and the acceptance -/

theorem idx55_eq {t : ℕ} (ht : t < 2112) : idx55.entry t = if t < 1025 then 64 + t else 1088 := by
  unfold idx55
  simp only [RealizedProgram.IndexMap.ofSegs, RealizedProgram.IdxSeg.expand, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.singleton_append, RealizedProgram.IndexMap.entry]
  split_ifs <;> omega

theorem idx56_eq {t : ℕ} (ht : t < 2112) : idx56.entry t = if t < 1024 then 1088 else t - 1024 := by
  unfold idx56
  simp only [RealizedProgram.IndexMap.ofSegs, RealizedProgram.IdxSeg.expand, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.singleton_append, RealizedProgram.IndexMap.entry]
  split_ifs <;> omega

/-- The zero constant of `H` (value `36`) reads `0`. -/
theorem evalE_36 (rd : program.Valuation interp) (h : ∀ i, rd 36 i =
    (interp (program.valueField 36)).decode ((program.constEntries 36).getD i 0)) (i : ℕ) :
    program.evalE rd 1 (.leaf 36) i = 0 := by
  rw [RealizedProgram.evalE_leaf, h, (selConstsA (program := program)).2.1]
  have h0 : ([0] : List ℕ).getD i 0 = 0 := by cases i <;> simp
  rw [h0]
  generalize program.valueField 36 = a
  unfold RealizedProgram.castElt
  split
  · rename_i hab
    subst hab
    exact HField.decode_zero
  · rfl

/-- **The stream's bits** (the shared expression `510`): bit `t` is bit `64 + t` of `h2c.sib.out`
(the bytes from `8` on of the two squeezed blocks). -/
theorem evalE_ref510 (e : program.Env interp) {t : ℕ} (ht : t < 2112) :
    program.evalE (program.reader e) 1 (.ref 510) t = sibBits (program.reader e) ⟨64 + t, by omega⟩ := by
  have h36 := fun i => RealizedProgram.reader_of_constant e (RealizedProgram.kind_of_isConstant (selConstsA (program := program)).1) i
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsSel (program := program)); omega), (expr510 (program := program)), RealizedProgram.evalE_add,
    RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex]
  unfold sibBits
  by_cases h1 : t < 1024
  · have e55 : idx55.entry t = 64 + t := by rw [idx55_eq ht, if_pos (by omega)]
    have e56 : idx56.entry t = 1088 := by rw [idx56_eq ht, if_pos h1]
    rw [e55, e56, RealizedProgram.evalE_concat, RealizedProgram.evalE_concat, RealizedProgram.exprLen_leaf,
      RealizedProgram.exprLen_leaf, (selConstsA (program := program)).2.2.2.2.2.2.2.1, (selConstsA (program := program)).2.2.2.2.2.2.2.2,
      if_pos (show 64 + t < 1088 by omega), if_neg (lt_irrefl _), evalE_36 _ h36, add_zero,
      if_pos (show 64 + t < 1088 by omega)]
  · have e56 : idx56.entry t = t - 1024 := by rw [idx56_eq ht, if_neg h1]
    have e55 : idx55.entry t = 1088 ∨ (t = 1024 ∧ idx55.entry t = 1088) := by
      rw [idx55_eq ht]
      split_ifs <;> first | (left; rfl) | omega
    have e55' : idx55.entry t = 1088 := by rcases e55 with h | ⟨-, h⟩ <;> exact h
    rw [e55', e56, RealizedProgram.evalE_concat, RealizedProgram.evalE_concat, RealizedProgram.exprLen_leaf,
      RealizedProgram.exprLen_leaf, (selConstsA (program := program)).2.2.2.2.2.2.2.1, (selConstsA (program := program)).2.2.2.2.2.2.2.2,
      if_neg (lt_irrefl _), if_pos (show t - 1024 < 1088 by omega), evalE_36 _ h36, zero_add,
      if_neg (show ¬ 64 + t < 1088 by omega), show 64 + t - 1088 = t - 1024 by omega]

/-- **The candidate bytes' bits** read through the stream's shared expression. -/
theorem candBits_eq (e : program.Env interp) (i : Fin 264) (b : Fin 8) :
    candBits (program.reader e) i b = program.evalE (program.reader e) 1 (.ref 510) (8 * i + b) := by
  rw [evalE_ref510 e (by omega)]
  unfold candBits HashCircuit.candidates sibByte Falcon512.HashCircuit.byteWires
  congr 1
  apply Fin.ext
  change 8 * (8 + (i : ℕ)) + b = 64 + (8 * i + b)
  omega


/-! ## Bits -/

/-- The stream's bits are bits (bit views of the squeezed words). -/
theorem sibBits_bool (e : program.Env interp) (t : Fin (8 * 272)) :
    sibBits (program.reader e) t = 0 ∨ sibBits (program.reader e) t = 1 := by
  unfold sibBits
  split
  · exact RealizedProgram.evalE_leaf_bool_of_isBitView e MldsaHSelect.bitView555 1 _
  · exact RealizedProgram.evalE_leaf_bool_of_isBitView e MldsaHSelect.bitView556 1 _

/-- The candidate bytes are bits. -/
theorem candBits_bool (e : program.Env interp) (i : Fin 264) : AllBool (candBits (program.reader e) i) :=
  fun _ => sibBits_bool e _

/-- The low threshold bits are bits (a bit view). -/
theorem lowThr_bool (e : program.Env interp) (i : Fin 264) : AllBool (lowThr (program.reader e) i) :=
  fun _ => RealizedProgram.evalE_leaf_bool_of_isBitView e MldsaHSelect.bitView559 1 _

/-- The decoded thresholds are bits. -/
theorem thrBits_bool (e : program.Env interp) (i : Fin 264) : AllBool (thrBits (program.reader e) i) := by
  rw [thrBits_eq]
  exact SelectFirstTau.decode_allBool (lowThr_bool e i)

/-- The facts of the selected bytes' type. -/
theorem jFacts : 557 < program.values.length ∧ program.IsSourceValue 557 ∧ (program.value 557).typeSource = .node ∧ (program.value 557).type = .bit ∧ (program.value 557).size = 312 :=
  MldsaHSelect.jFacts
/-- A bit-typed source value of domain `H` (by its node) is `0` or `1` where the source program
holds. -/
theorem bool_of_bitTypedH {e : program.Env interp} (hs : HSat e) {v : ℕ} (hv : v ∈ hTyped)
    (hty : (program.value v).type = .bit) {i : ℕ} (hi : i < (program.value v).size) :
    program.evalE (program.reader e) 1 (.leaf v) i = 0 ∨
      program.evalE (program.reader e) 1 (.leaf v) i = 1 := by
  have h := hs.types v hv i hi
  rw [hty] at h
  exact RealizedProgram.castElt_bool h

/-- The selected bytes are bits where the source program holds (their node type). -/
theorem jBits_bool {e : program.Env interp} (hs : HSat e) (j : Fin 39) :
    AllBool (jBits (program.reader e) j) := fun b => by
  obtain ⟨-, -, -, hty, hsz⟩ := (jFacts (program := program))
  exact bool_of_bitTypedH hs (by decide) hty (by rw [hsz]; omega)

/-! ## The acceptance and the selection -/

/-- **The acceptance** (the shared expression `511`, `Logic::leq` of the candidate and the
threshold) is `Bits.leVar`. -/
theorem evalE_ref511 (e : program.Env interp) (i : Fin 264) :
    program.evalE (program.reader e) 1 (.ref 511) i =
      Bits.leVar (candBits (program.reader e) i) (thrBits (program.reader e) i) := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsSel (program := program)); omega), (expr511 (program := program)), RealizedProgram.evalE_logic]
  simp only [RealizedProgram.LogicOp.eval, List.headD_cons, List.getD_cons_succ, List.getD_cons_zero]
  have hc : ∀ (t : ℕ) (ht : t < 8), program.evalE (program.reader e) 1 (.ref 510) (i * 8 + t) =
      candBits (program.reader e) i ⟨t, ht⟩ := fun t ht => by
    rw [candBits_eq e i ⟨t, ht⟩, Nat.mul_comm]
  have ht : ∀ (t : ℕ) (ht : t < 8), program.evalE (program.reader e) 1 (.ref 508) (i * 8 + t) =
      thrBits (program.reader e) i ⟨t, ht⟩ := fun t ht => by
    unfold thrBits
    rw [Nat.mul_comm]
  rw [RealizedProgram.Ops.leqWord_eq_leVar (fun t ht' => by rw [hc t ht']; exact candBits_bool e i _)
    (fun t ht' => by rw [ht t ht']; exact thrBits_bool e i _)]
  have hc' : (fun t : Fin 8 => program.evalE (program.reader e) 1 (.ref 510) (i * 8 + t)) =
      candBits (program.reader e) i := funext fun t => hc t t.isLt
  have ht' : (fun t : Fin 8 => program.evalE (program.reader e) 1 (.ref 508) (i * 8 + t)) =
      thrBits (program.reader e) i := funext fun t => ht t t.isLt
  rw [hc', ht']

theorem idx57_eq {i : ℕ} (hi : i < 39) : idx57.entry i = i := by
  unfold idx57
  simp [RealizedProgram.IndexMap.ofSegs, RealizedProgram.IdxSeg.expand, RealizedProgram.IndexMap.entry, hi]
theorem idx58_eq {k : ℕ} (hk : k < 225) : idx58.entry k = 39 + k := by
  unfold idx58
  simp [RealizedProgram.IndexMap.ofSegs, RealizedProgram.IdxSeg.expand, RealizedProgram.IndexMap.entry, hk]
  omega
theorem idx59_eq {k : ℕ} (hk : k < 1800) : idx59.entry k = 312 + k := by
  unfold idx59
  simp [RealizedProgram.IndexMap.ofSegs, RealizedProgram.IdxSeg.expand, RealizedProgram.IndexMap.entry, hk]
  omega
theorem idx60_eq {k : ℕ} (hk : k < 225) : idx60.entry k = 7 + 8 * k := by
  unfold idx60
  simp [RealizedProgram.IndexMap.ofSegs, RealizedProgram.IdxSeg.expand, RealizedProgram.IndexMap.entry, hk]
  omega

/-- The lengths of the selection's pieces. -/
theorem selLens : program.exprLen (.reindex idx57 (.ref 511)) = 39 :=
  MldsaHSelect.selLens
/-- The ones constant of the selection (value `45`) reads `1`. -/
theorem evalE_45 (e : program.Env interp) {k : ℕ} (hk : k < 225) :
    program.evalE (program.reader e) 1 (.leaf 45) k = 1 := by
  rw [RealizedProgram.evalE_leaf_of_isConstant e (selConstsA (program := program)).2.2.1,
    RealizedProgram.constRead_of_valueField (selConstsA (program := program)).2.2.2.2.2.1, (selConstsA (program := program)).2.2.2.1,
    List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hk, Option.getD_some]
  exact HField.decode_one

/-- **The selection** (the shared expression `512`) is `SelectFirstTau.selected`: the acceptance,
and from position `39` on the threshold's top bit (`full` its complement). -/
theorem evalE_ref512 (e : program.Env interp) (i : Fin 264) :
    program.evalE (program.reader e) 1 (.ref 512) i =
      SelectFirstTau.selected 39 (candBits (program.reader e)) (thrBits (program.reader e)) i := by
  have hi := i.isLt
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsSel (program := program)); omega), (expr512 (program := program)), RealizedProgram.evalE_reindex,
    idx49_eq hi, RealizedProgram.evalE_concat, (selLens (program := program))]
  unfold SelectFirstTau.selected SelectFirstTau.full
  by_cases h39 : (i : ℕ) < 39
  · rw [if_pos h39, if_pos h39, RealizedProgram.evalE_reindex, idx57_eq h39,
      show ((i : ℕ)) = ((i : Fin 264) : ℕ) from rfl, evalE_ref511]
    simp [Bits.bnot]
  · rw [if_neg h39, if_neg h39, RealizedProgram.evalE_mul, RealizedProgram.evalE_reindex, idx58_eq (by omega),
      show 39 + ((i : ℕ) - 39) = i by omega, evalE_ref511, RealizedProgram.evalE_sub, RealizedProgram.evalE_sub,
      evalE_45 e (by omega), RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, idx60_eq (by omega),
      idx59_eq (by omega), show 312 + (7 + 8 * ((i : ℕ) - 39)) = 8 * i + 7 by omega]
    simp only [Bits.bnot]
    rfl


/-! ## `h2c.sample.select.start` and `.step` -/

/-- The constants of the start and the steps. -/
theorem stepConsts : program.isConstant 43 = true ∧ program.constEntries 43 = [1, 0, 0, 1, 1, 0, 1, 1] ∧ program.isConstant 44 = true ∧ program.constEntries 44 = List.replicate 8 0 ∧ program.isConstant 46 = true ∧ program.constEntries 46 = List.replicate 2104 0 ∧ program.valueField 43 = 1 ∧ program.valueField 44 = 1 ∧ program.valueField 46 = 1 :=
  MldsaHSelect.stepConsts
/-- A constant of `H` reads its entry decoded in domain `H`'s field. -/
theorem evalE_constH (e : program.Env interp) {v : ℕ} (hc : program.isConstant v = true)
    (hf : program.valueField v = 1) (j : ℕ) :
    program.evalE (program.reader e) 1 (.leaf v) j = (interp 1).decode ((program.constEntries v).getD j 0) := by
  rw [RealizedProgram.evalE_leaf_of_isConstant e hc, RealizedProgram.constRead_of_valueField hf]

/-- A replicated `0` reads `0`. -/
theorem getD_replicate_zero (n j : ℕ) : (List.replicate n 0).getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge j n with h | h
  · rw [List.getElem?_replicate, if_pos h, Option.getD_some]
  · rw [List.getElem?_eq_none (by rw [List.length_replicate]; exact h), Option.getD_none]

theorem decode_zero' : (interp 1).decode 0 = 0 := HField.decode_zero

/-- In characteristic two, `a + b = 0` is `a = b`. -/
theorem eq_of_add_eq_zero₂ {a b : (interp 1).K} (h : a + b = 0) : a = b :=
  (eq_neg_of_add_eq_zero_left h).trans (CharTwo.neg_eq b)

theorem idx52_eq {b : ℕ} (hb : b < 8) : idx52.entry b = b := by
  unfold idx52
  simp [RealizedProgram.IndexMap.ofSegs, RealizedProgram.IdxSeg.expand, RealizedProgram.IndexMap.entry, hb]

/-- **`h2c.sample.select.start`**: the first threshold is `256 − τ = 217`. -/
theorem initialOk_thr {e : program.Env interp} (hs : HSat e) :
    SelectFirstTau.initialOk 39 (thrBits (program.reader e)) = true := by
  have h := hs.preds 264 (by norm_num) (by norm_num)
  rw [(pred264 (program := program))] at h
  simp only [SelectFirstTau.initialOk, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, decide_eq_true_eq, ne_eq]
  intro i
  by_cases h0 : (i : ℕ) = 0
  · right
    intro b
    have hb := b.isLt
    have hh := h b (by
      rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_reindex]
      unfold idx52
      simp [RealizedProgram.IndexMap.ofSegs, RealizedProgram.IdxSeg.expand, RealizedProgram.IndexMap.size])
    change program.evalE _ (program.domainField 1) _ b = program.evalE _ (program.domainField 1) _ b
      at hh
    rw [MldsaHCross.domainField1, RealizedProgram.evalE_add, RealizedProgram.evalE_reindex, idx52_eq hb,
      evalE_constH e (stepConsts (program := program)).1 (stepConsts (program := program)).2.2.2.2.2.2.1,
      evalE_constH e (stepConsts (program := program)).2.2.1 (stepConsts (program := program)).2.2.2.2.2.2.2.1, (stepConsts (program := program)).2.1, (stepConsts (program := program)).2.2.2.1,
      getD_replicate_zero, decode_zero'] at hh
    have hthr := eq_of_add_eq_zero₂ hh
    unfold thrBits
    rw [show 8 * (i : ℕ) + b = b by omega, hthr]
    unfold Bits.constBit
    interval_cases (b : ℕ) <;> first | exact HField.decode_one | exact HField.decode_zero
  · exact Or.inl h0


/-! The index maps of the steps: the rows `0 … 262`, the next rows, the bit columns `c` of a row,
and the levels of the prefix ANDs (level `k` interleaves `k` columns of each row with one more). -/

theorem idx53_toList : idx53.toList = (List.range 2104).map fun n => 8 + n := by decide +kernel
theorem idx54_toList : idx54.toList = (List.range 2104).map fun n => n := by decide +kernel
theorem idx61_toList : idx61.toList = (List.range 263).map fun n => n := by decide +kernel

/-- The bit columns of the rows. -/
theorem idxCol_toList : idx62.toList = (List.range 263).map (fun n => 8 * n + 0) ∧
    idx64.toList = (List.range 263).map (fun n => 8 * n + 1) ∧
    idx66.toList = (List.range 263).map (fun n => 8 * n + 2) ∧
    idx68.toList = (List.range 263).map (fun n => 8 * n + 3) ∧
    idx70.toList = (List.range 263).map (fun n => 8 * n + 4) ∧
    idx72.toList = (List.range 263).map (fun n => 8 * n + 5) ∧
    idx74.toList = (List.range 263).map (fun n => 8 * n + 6) := by
  decide +kernel

/-- **The entries of level `k` of the prefix ANDs**: entry `(k + 1) i + c` is entry `k i + c` of
the previous level below `c = k`, entry `i` of the new column at `c = k`. -/
def levelMap (k : ℕ) : ℕ → ℕ := fun n =>
  if n % (k + 1) < k then k * (n / (k + 1)) + n % (k + 1) else 263 * k + n / (k + 1)

theorem idxLevel_toList : idx63.toList = (List.range (263 * 2)).map (levelMap 1) ∧
    idx65.toList = (List.range (263 * 3)).map (levelMap 2) ∧
    idx67.toList = (List.range (263 * 4)).map (levelMap 3) ∧
    idx69.toList = (List.range (263 * 5)).map (levelMap 4) ∧
    idx71.toList = (List.range (263 * 6)).map (levelMap 5) ∧
    idx73.toList = (List.range (263 * 7)).map (levelMap 6) ∧
    idx75.toList = (List.range (263 * 8)).map (levelMap 7) := by
  decide +kernel

/-- The sizes of the steps' index maps. -/
theorem stepSizes : idx61.size = 263 ∧ idx63.size = 263 * 2 ∧ idx65.size = 263 * 3 ∧
    idx67.size = 263 * 4 ∧ idx69.size = 263 * 5 ∧ idx71.size = 263 * 6 ∧ idx73.size = 263 * 7 ∧
    idx75.size = 263 * 8 ∧ idx53.size = 2104 := by
  decide +kernel

/-- **One level of the prefix ANDs**: coordinate `(k + 1) i + c` of the level is coordinate `k i + c`
of the previous level below `c = k`, coordinate `i` of the new column at `c = k`. -/
theorem evalE_level (rd : program.Valuation interp) {k : ℕ} {idx : RealizedProgram.IndexMap} {A B : RealizedProgram.Expr}
    (hidx : idx.toList = (List.range (263 * (k + 1))).map (levelMap k))
    (hA : program.exprLen A = 263 * k) {i c : ℕ} (hi : i < 263) (hc : c ≤ k) :
    program.evalE rd 1 (.reindex idx (.concat A B)) ((k + 1) * i + c) =
      if c < k then program.evalE rd 1 A (k * i + c) else program.evalE rd 1 B i := by
  have hn : (k + 1) * i + c < 263 * (k + 1) := by nlinarith
  have hdiv : ((k + 1) * i + c) / (k + 1) = i := by
    rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add]
  have hmod : ((k + 1) * i + c) % (k + 1) = c := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [RealizedProgram.evalE_reindex, RealizedProgram.IndexMap.entry_of_toList hidx hn, RealizedProgram.evalE_concat, hA]
  unfold levelMap
  rw [hdiv, hmod]
  by_cases hck : c < k
  · rw [if_pos hck, if_pos hck, if_pos (by nlinarith)]
  · rw [if_neg hck, if_neg hck, if_neg (by omega), Nat.add_sub_cancel_left]


/-- **The index map of level `k`** of the prefix ANDs (`k = 1 … 7`). -/
def levelIdx : ℕ → RealizedProgram.IndexMap
  | 1 => idx63
  | 2 => idx65
  | 3 => idx67
  | 4 => idx69
  | 5 => idx71
  | 6 => idx73
  | _ => idx75

/-- **The column level `k` adds**: the selection times the AND of the threshold's bits below `k`
(the shared expressions `514`–`519`). -/
def levelCol : ℕ → RealizedProgram.Expr
  | 1 => .reindex idx61 (.mul (.ref 513) (.ref 514))
  | 2 => .reindex idx61 (.mul (.ref 513) (.ref 515))
  | 3 => .reindex idx61 (.mul (.ref 513) (.mul (.ref 516) (.ref 515)))
  | 4 => .reindex idx61 (.mul (.ref 513) (.ref 517))
  | 5 => .reindex idx61 (.mul (.ref 513) (.mul (.ref 518) (.ref 517)))
  | 6 => .reindex idx61 (.mul (.ref 513) (.mul (.ref 519) (.ref 517)))
  | _ => .reindex idx61 (.mul (.ref 513) (.mul (.mul (.reindex idx74 (.ref 509)) (.ref 519)) (.ref 517)))

/-- **Level `k` of the prefix ANDs**: level `1` the selection, level `k + 1` interleaving level `k`
with `levelCol k`. -/
def chain : ℕ → RealizedProgram.Expr
  | 0 => .reindex idx61 (.ref 513)
  | 1 => .reindex idx61 (.ref 513)
  | k + 2 => .reindex (levelIdx (k + 1)) (.concat (chain (k + 1)) (levelCol (k + 1)))

theorem levelIdx_toList {k : ℕ} (h1 : 1 ≤ k) (h7 : k ≤ 7) :
    (levelIdx k).toList = (List.range (263 * (k + 1))).map (levelMap k) := by
  obtain ⟨h63, h65, h67, h69, h71, h73, h75⟩ := idxLevel_toList
  interval_cases k <;> assumption

theorem levelIdx_size {k : ℕ} (h1 : 1 ≤ k) (h7 : k ≤ 7) : (levelIdx k).size = 263 * (k + 1) := by
  interval_cases k <;> decide +kernel

theorem exprLen_chain : ∀ {k : ℕ}, 1 ≤ k → k ≤ 8 → program.exprLen (chain k) = 263 * k
  | 1, _, _ => by
    rw [chain, RealizedProgram.exprLen_reindex, stepSizes.1]
  | k + 2, _, h8 => by
    rw [chain, RealizedProgram.exprLen_reindex]
    exact levelIdx_size (by omega) (by omega)

/-- **The prefix ANDs read by level `k`**: below level `k`, coordinate `k i + b` of level `k` is
coordinate `i` of the column level `b` added, or of the selection at `b = 0`. -/
theorem evalE_chain (rd : program.Valuation interp) {i : ℕ} (hi : i < 263) :
    ∀ {k : ℕ}, 1 ≤ k → k ≤ 8 → ∀ {b : ℕ}, b < k →
      program.evalE rd 1 (chain k) (k * i + b) =
        if b = 0 then program.evalE rd 1 (.reindex idx61 (.ref 513)) i
        else program.evalE rd 1 (levelCol b) i
  | 1, _, _, b, hb => by
    obtain rfl : b = 0 := by omega
    rw [chain, if_pos rfl, Nat.one_mul, Nat.add_zero]
  | k + 2, _, h8, b, hb => by
    have hk := @evalE_chain rd i hi (k + 1) (by omega) (by omega)
    rw [chain, show k + 2 = (k + 1) + 1 from rfl, evalE_level rd (levelIdx_toList (by omega) (by omega))
      (exprLen_chain (by omega) (by omega)) hi (by omega)]
    by_cases hbk : b < k + 1
    · rw [if_pos hbk]
      exact hk hbk
    · obtain rfl : b = k + 1 := by omega
      rw [if_neg hbk, if_neg (by omega)]


/-! ### The columns of the prefix ANDs -/

/-- **Bit `c` of threshold `i`** (the shared expression `508` at `8 i + c`). -/
def thrAt (rd : program.Valuation interp) (i c : ℕ) : (interp 1).K :=
  program.evalE rd 1 (.ref 508) (8 * i + c)

theorem thrBits_apply (rd : program.Valuation interp) (i : Fin 264) (c : Fin 8) :
    thrBits rd i c = thrAt rd i c := rfl

section Columns

variable (e : program.Env interp) {i : ℕ} (hi : i < 263)
include hi

/-- The threshold of row `i` read through the steps' row view (`509`). -/
theorem evalE_ref509 {b : ℕ} (hb : b < 8) :
    program.evalE (program.reader e) 1 (.ref 509) (8 * i + b) = thrAt (program.reader e) i b := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsSel (program := program)); omega), (expr509 (program := program)), RealizedProgram.evalE_reindex,
    RealizedProgram.IndexMap.entry_of_toList idx54_toList (by omega)]
  rfl

/-- Column `c` of row `i` of the thresholds. -/
theorem evalE_col {idx : RealizedProgram.IndexMap} {c : ℕ}
    (hidx : idx.toList = (List.range 263).map (fun n => 8 * n + c)) (hc : c < 8) :
    program.evalE (program.reader e) 1 (.reindex idx (.ref 509)) i = thrAt (program.reader e) i c := by
  rw [RealizedProgram.evalE_reindex, RealizedProgram.IndexMap.entry_of_toList hidx hi, evalE_ref509 e hi hc]

theorem evalE_ref513 : program.evalE (program.reader e) 1 (.ref 513) i =
    program.evalE (program.reader e) 1 (.ref 512) i := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsSel (program := program)); omega), (expr513 (program := program)), RealizedProgram.evalE_reindex,
    RealizedProgram.IndexMap.entry_of_toList idx61_toList hi]

theorem evalE_ref514 :
    program.evalE (program.reader e) 1 (.ref 514) i = thrAt (program.reader e) i 0 := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsSel (program := program)); omega), (expr514 (program := program)),
    evalE_col e hi idxCol_toList.1 (by norm_num)]

theorem evalE_ref515 : program.evalE (program.reader e) 1 (.ref 515) i =
    thrAt (program.reader e) i 1 * thrAt (program.reader e) i 0 := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsSel (program := program)); omega), (expr515 (program := program)), RealizedProgram.evalE_mul,
    evalE_col e hi idxCol_toList.2.1 (by norm_num), evalE_ref514 e hi]

theorem evalE_ref516 :
    program.evalE (program.reader e) 1 (.ref 516) i = thrAt (program.reader e) i 2 := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsSel (program := program)); omega), (expr516 (program := program)),
    evalE_col e hi idxCol_toList.2.2.1 (by norm_num)]

theorem evalE_ref517 : program.evalE (program.reader e) 1 (.ref 517) i =
    thrAt (program.reader e) i 3 * thrAt (program.reader e) i 2 *
      (thrAt (program.reader e) i 1 * thrAt (program.reader e) i 0) := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsSel (program := program)); omega), (expr517 (program := program)), RealizedProgram.evalE_mul,
    RealizedProgram.evalE_mul, evalE_col e hi idxCol_toList.2.2.2.1 (by norm_num), evalE_ref516 e hi,
    evalE_ref515 e hi]

theorem evalE_ref518 :
    program.evalE (program.reader e) 1 (.ref 518) i = thrAt (program.reader e) i 4 := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsSel (program := program)); omega), (expr518 (program := program)),
    evalE_col e hi idxCol_toList.2.2.2.2.1 (by norm_num)]

theorem evalE_ref519 : program.evalE (program.reader e) 1 (.ref 519) i =
    thrAt (program.reader e) i 5 * thrAt (program.reader e) i 4 := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsSel (program := program)); omega), (expr519 (program := program)), RealizedProgram.evalE_mul,
    evalE_col e hi idxCol_toList.2.2.2.2.2.1 (by norm_num), evalE_ref518 e hi]

/-- **The column level `b` adds** is the selection times the AND of the threshold's bits below
`b` (`Bits.increment`'s carry). -/
theorem evalE_levelCol {b : ℕ} (hb1 : 1 ≤ b) (hb : b < 8) :
    program.evalE (program.reader e) 1 (levelCol b) i =
      program.evalE (program.reader e) 1 (.ref 512) i *
        ∏ j : Fin 8, if (j : ℕ) < b then thrAt (program.reader e) i j else 1 := by
  rw [Fin.prod_univ_eight]
  interval_cases b <;>
    simp only [levelCol, RealizedProgram.evalE_reindex, RealizedProgram.IndexMap.entry_of_toList idx61_toList hi,
      RealizedProgram.evalE_mul, evalE_ref513 e hi, evalE_ref514 e hi, evalE_ref515 e hi,
      evalE_ref516 e hi, evalE_ref517 e hi, evalE_ref518 e hi, evalE_ref519 e hi,
      evalE_col e hi idxCol_toList.2.2.2.2.2.2 (by norm_num)] <;>
    norm_num <;> first | ring1 | (left; ring1)

end Columns


/-! ### The steps -/

/-- **`h2c.sample.select.step`**: the next threshold is the threshold plus the prefix ANDs' flips
(`chain 8`). -/
theorem pred265_body : (program.predicate 265).body = .equal 1 (.add (.reindex idx53 (.ref 508))
    (.add (.ref 509) (chain 8))) (.leaf 46) (.gkr 1) := by
  rw [(pred265 (program := program))]
  rfl

/-- The zeros of the steps (value `46`) read `0`. -/
theorem evalE_46 (e : program.Env interp) (j : ℕ) : program.evalE (program.reader e) 1 (.leaf 46) j = 0 := by
  rw [evalE_constH e (stepConsts (program := program)).2.2.2.2.1 (stepConsts (program := program)).2.2.2.2.2.2.2.2, (stepConsts (program := program)).2.2.2.2.2.1,
    getD_replicate_zero]
  exact HField.decode_zero

/-- **The threshold recurrence** at row `i < 263`, bit `b`: the next threshold's bit is the bit
plus the selection times the carry. -/
theorem thr_succ {e : program.Env interp} (hs : HSat e) {i b : ℕ} (hi : i < 263)
    (hb : b < 8) :
    thrAt (program.reader e) (i + 1) b = thrAt (program.reader e) i b +
      program.evalE (program.reader e) 1 (.ref 512) i *
        ∏ j : Fin 8, if (j : ℕ) < b then thrAt (program.reader e) i j else 1 := by
  have h := hs.preds 265 (by norm_num) (by norm_num)
  rw [pred265_body] at h
  have hh := h (8 * i + b) (by
    rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_reindex, stepSizes.2.2.2.2.2.2.2.2]
    omega)
  change program.evalE _ (program.domainField 1) _ _ =
    program.evalE _ (program.domainField 1) _ _ at hh
  rw [MldsaHCross.domainField1, evalE_46, RealizedProgram.evalE_add, RealizedProgram.evalE_add, RealizedProgram.evalE_reindex,
    RealizedProgram.IndexMap.entry_of_toList idx53_toList (by omega), evalE_ref509 e hi hb,
    evalE_chain _ hi (by norm_num) le_rfl hb] at hh
  have hnext : thrAt (program.reader e) (i + 1) b =
      program.evalE (program.reader e) 1 (.ref 508) (8 + (8 * i + b)) := by
    unfold thrAt
    congr 1
    ring
  rw [hnext]
  have hsel : program.evalE (program.reader e) 1 (.reindex idx61 (.ref 513)) i =
      program.evalE (program.reader e) 1 (.ref 512) i := by
    rw [RealizedProgram.evalE_reindex, RealizedProgram.IndexMap.entry_of_toList idx61_toList hi, evalE_ref513 e hi]
  by_cases hb0 : b = 0
  · subst hb0
    rw [if_pos rfl, hsel] at hh
    have := eq_of_add_eq_zero₂ hh
    rw [this]
    simp
  · rw [if_neg hb0, evalE_levelCol e hi (by omega) hb] at hh
    exact eq_of_add_eq_zero₂ hh

/-- **`h2c.sample.select.step` is `SelectFirstTau.stepOk`**: the next threshold is
`mux(selected, thr + 1, thr)` bitwise (characteristic two: the carry's `XOR` is `+`). -/
theorem stepOk_thr {e : program.Env interp} (hs : HSat e) :
    SelectFirstTau.stepOk 39 (candBits (program.reader e)) (thrBits (program.reader e)) = true := by
  simp only [SelectFirstTau.stepOk, List.all_eq_true, List.mem_finRange, true_implies]
  intro i
  split_ifs with h
  · simp only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]
    intro b
    have hb := b.isLt
    rw [← evalE_ref512, thrBits_apply]
    change thrAt (program.reader e) ((i : ℕ) + 1) b = _
    rw [thr_succ hs (by omega) hb]
    unfold SelectFirstTau.next SelectScan.mux Bits.increment Bits.bxor
    have h2 : (2 : (interp 1).K) = 0 := CharTwo.two_eq_zero
    simp only [thrBits_apply]
    linear_combination (program.evalE (program.reader e) 1 (.ref 512) i *
      thrAt (program.reader e) i b *
        ∏ j : Fin 8, if (j : ℕ) < (b : ℕ) then thrAt (program.reader e) i j else 1) * h2
  · rfl


/-! ## `h2c.sample.select.route` -/

/-- The constants of the route. -/
theorem routeConsts : program.isConstant 37 = true ∧ program.valueField 37 = 1 ∧ (program.constEntries 37).getD 0 0 = 1 ∧ program.isConstant 47 = true ∧ program.valueField 47 = 1 ∧ program.isConstant 7 = true ∧ program.valueField 7 = 1 ∧ program.constEntries 7 = [1] ∧ (∀ j < 39, (program.constEntries 47).getD j 0 = RealizedProgram.xorSel (217 + j) fun u => (program.constEntries 37).getD u 0) :=
  MldsaHSelect.routeConsts
/-- **The selection field of domain `H`** (`HField.sel`). -/
abbrev selF : SelectionField (interp 1).K 264 := HField.sel

theorem selF_X : (interp 1).decode 2 = selF.X := HField.decode_two

/-- **Entry `u < 8` of the constant `37`** is the embedding basis `e_u`. -/
theorem evalE_37 (e : program.Env interp) {u : ℕ} (hu : u < 8) :
    program.evalE (program.reader e) 1 (.leaf 37) u = selF.e ⟨u, by change u < 16; omega⟩ := by
  rw [evalE_constH e (routeConsts (program := program)).1 (routeConsts (program := program)).2.1, MldsaHConstsSelect.c37 u hu]

theorem idx77_eq {t : ℕ} (ht : t < 2112) : idx77.entry t = t := by
  unfold idx77
  simp [RealizedProgram.IndexMap.ofSegs, RealizedProgram.IdxSeg.expand, RealizedProgram.IndexMap.entry, ht]
theorem idx78_eq {i u : ℕ} (hi : i < 264) (hu : u < 8) : idx78.entry (8 * i + u) = u := by
  unfold idx78
  rw [RealizedProgram.IndexMap.entry_rep (c := 8) (fun j => by simp [RealizedProgram.IndexMap.size, RealizedProgram.IdxSeg.shift]) hi hu]
  simp [RealizedProgram.IndexMap.entry, RealizedProgram.IdxSeg.shift, hu]
theorem idx80_eq {t : ℕ} (ht : t < 312) : idx80.entry t = t := by
  unfold idx80
  simp [RealizedProgram.IndexMap.ofSegs, RealizedProgram.IdxSeg.expand, RealizedProgram.IndexMap.entry, ht]
theorem idx81_eq {j u : ℕ} (hj : j < 39) (hu : u < 8) : idx81.entry (8 * j + u) = u := by
  unfold idx81
  rw [RealizedProgram.IndexMap.entry_rep (c := 8) (fun j => by simp [RealizedProgram.IndexMap.size, RealizedProgram.IdxSeg.shift]) hj hu]
  simp [RealizedProgram.IndexMap.entry, RealizedProgram.IdxSeg.shift, hu]
theorem idx76_eq {i : ℕ} (hi : i < 264) : idx76.entry i = 0 := by
  unfold idx76
  simp [RealizedProgram.IndexMap.ofSegs, RealizedProgram.IdxSeg.expand, RealizedProgram.IndexMap.entry, hi]
theorem idx79_eq {j : ℕ} (hj : j < 39) : idx79.entry j = 0 := by
  unfold idx79
  simp [RealizedProgram.IndexMap.ofSegs, RealizedProgram.IdxSeg.expand, RealizedProgram.IndexMap.entry, hj]

/-- **An embedding of eight bits through the basis constant** (`sum 8` of the bits times the
constant `37`): `F.embedBits` of the bits. -/
theorem evalE_embed8 (e : program.Env interp) {V : RealizedProgram.Expr} {i : ℕ} {idxA idxB : RealizedProgram.IndexMap}
    {n : ℕ} (hi : i < n)
    (hA : ∀ t < 8 * n, idxA.entry t = t) (hB : ∀ u < 8, idxB.entry (8 * i + u) = u)
    {bits : BitWires (interp 1).K 8}
    (hbits : ∀ u : Fin 8, program.evalE (program.reader e) 1 V (8 * i + u) = bits u) :
    program.evalE (program.reader e) 1
        (.apply (.sum 8) (.mul (.reindex idxA V) (.reindex idxB (.leaf 37)))) i =
      selF.embedBits (by decide) bits := by
  rw [RealizedProgram.evalE_apply_sum]
  unfold SelectionField.embedBits
  refine Finset.sum_congr rfl fun u _ => ?_
  have hu := u.isLt
  rw [RealizedProgram.evalE_mul, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex,
    show i * 8 + (u : ℕ) = 8 * i + u by ring, hA _ (by omega), hB u hu, hbits u, evalE_37 e hu]
  rfl


/-- **The claimed outputs' labels** (the constant `47`): entry `j` is the embedding of
`256 − τ + j = 217 + j`. -/
theorem evalE_47 (e : program.Env interp) {j : ℕ} (hj : j < 39) :
    program.evalE (program.reader e) 1 (.leaf 47) j = selF.embed (256 - 39 + j) := by
  rw [evalE_constH e (routeConsts (program := program)).2.2.2.1 (routeConsts (program := program)).2.2.2.2.1, (routeConsts (program := program)).2.2.2.2.2.2.2.2 j hj,
    RealizedProgram.decode_xorSel, SelectionField.embed_of_lt_256 _ (by omega)]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [MldsaHConstsSelect.c37 u u.isLt]

/-- The constant `1` (value `7`) reads `1`. -/
theorem evalE_7 (e : program.Env interp) : program.evalE (program.reader e) 1 (.leaf 7) 0 = 1 := by
  rw [evalE_constH e (routeConsts (program := program)).2.2.2.2.2.1 (routeConsts (program := program)).2.2.2.2.2.2.1, (routeConsts (program := program)).2.2.2.2.2.2.2.1]
  exact HField.decode_one


/-- The length of the route's candidate product's operand. -/
theorem routeLens : program.exprLen (.reindex idx76 (.leaf 560)) = 264 :=
  MldsaHSelect.routeLens
/-- **`h2c.sample.select.route` is `SelectFirstTau.fingerprintOk`**: in characteristic two the
candidates' product over the selected positions and the claims' product agree at `δ`. -/
theorem fingerprintOk_route {e : program.Env interp} (hs : HSat e) :
    SelectFirstTau.fingerprintOk selF 39 (candBits (program.reader e)) (jBits (program.reader e))
      (thrBits (program.reader e)) (selDelta (program.reader e)) = true := by
  have h36 := fun i => RealizedProgram.reader_of_constant e (RealizedProgram.kind_of_isConstant (selConstsA (program := program)).1) i
  have h := hs.preds 266 (by norm_num) (by norm_num)
  rw [(pred266 (program := program))] at h
  have h0 := h 0 (by
    rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_prod, RealizedProgram.exprLen_mux, RealizedProgram.exprLen_add,
      (routeLens (program := program))]
    norm_num)
  change program.evalE _ (program.domainField 1) (.prod 264 _) 0 +
    program.evalE _ (program.domainField 1) (.prod 39 _) 0 =
      program.evalE _ (program.domainField 1) _ 0 at h0
  rw [MldsaHCross.domainField1, RealizedProgram.evalE_prod, RealizedProgram.evalE_prod, List.prod_map_range,
    List.prod_map_range, evalE_36 _ h36] at h0
  unfold SelectFirstTau.fingerprintOk
  rw [decide_eq_true_iff, List.finRange_foldl_mul_eq_prod, List.finRange_foldl_mul_eq_prod]
  refine RealizedProgram.eq_of_add_eq_zero_charTwo (Eq.trans ?_ h0)
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hi := i.isLt
    rw [Nat.zero_mul, Nat.zero_add, RealizedProgram.evalE_mux, evalE_ref512 e i, RealizedProgram.evalE_add,
      RealizedProgram.evalE_reindex, idx76_eq hi, RealizedProgram.evalE_add,
      evalE_embed8 e hi (fun t ht => idx77_eq (by omega)) (fun u hu => idx78_eq hi hu)
        (bits := thrBits (program.reader e) i) (fun u => rfl),
      RealizedProgram.evalE_scale_const,
      evalE_embed8 e hi (fun t ht => idx77_eq (by omega)) (fun u hu => idx78_eq hi hu)
        (bits := candBits (program.reader e) i) (fun u => (candBits_eq e i u).symm),
      RealizedProgram.evalE_reindex, idx76_eq hi, evalE_7, selF_X, SelectScan.mux, SelectFirstTau.enc,
      CharTwo.sub_eq_add]
    rfl
  · refine Finset.prod_congr rfl fun j _ => ?_
    have hj := j.isLt
    rw [Nat.zero_mul, Nat.zero_add, RealizedProgram.evalE_add, RealizedProgram.evalE_reindex, idx79_eq hj,
      RealizedProgram.evalE_add, evalE_47 e hj, RealizedProgram.evalE_scale_const,
      evalE_embed8 e hj (fun t ht => idx80_eq (by omega)) (fun u hu => idx81_eq hj hu)
        (bits := jBits (program.reader e) j) (fun u => rfl),
      selF_X, SelectFirstTau.enc, CharTwo.sub_eq_add]
    rfl

/-- **The selection's predicates are the gadget**: where the source program holds,
`SelectFirstTau.run` holds on the candidate bytes, the selected bytes, the low threshold bits and
`δ` at the selection field at the ROM parameters. -/
theorem selectRun {e : program.Env interp} (hs : HSat e) :
    SelectFirstTau.run selF 39 (candBits (program.reader e)) (jBits (program.reader e))
      (lowThr (program.reader e)) (selDelta (program.reader e)) = true := by
  have hthr : (fun i => SelectFirstTau.decode 39 (lowThr (program.reader e) i)) =
      thrBits (program.reader e) := funext fun i => (thrBits_eq _ i).symm
  unfold SelectFirstTau.run
  simp only [hthr, initialOk_thr hs, fingerprintOk_route hs, stepOk_thr hs, Bool.and_true]

end GordieHowe.MLDSA44.Native.ROMParams
