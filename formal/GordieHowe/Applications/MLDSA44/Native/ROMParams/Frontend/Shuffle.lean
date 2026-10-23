-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Frontend.Select
public import GordieHowe.Applications.MLDSA44.System.SampleInBall
public import GordieHowe.Applications.MLDSA44.Fields.GF2_128

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Native.ROMParams`, SampleInBall's memory check

SampleInBall's Fisher–Yates swaps (`examples/mldsa/sample_in_ball.h`, `sample_in_ball_shuffle`: the
offline memory check of the swaps over `256` cells, records `(address, value, origin)` packed at
`κ = x`) read off the program's predicates `h2c.sample.mem.unit`, `.origin`, `h2c.sample.mem` and
`.fresh` (predicates `267`–`270`) as the hand-built `SampleInBall.Checks` (`checks`) at the memory
check's record (`(samM F0)`: the selection field at the ROM parameters, `θ = gf2_128Theta`, the
positions the selected bytes `h2c.sample.select.j`, the signs the stream's bits `0 … 38`, the
decoded challenge the shared expressions `523` and `522`) and the lowered cells (`samLowered`: the
read values `561`, read origins `562`, final cells `563`, final origins `564`, units `565`, origins
`566`) at `δ = h2c.sample.mem.delta` (value `567`).
-/

namespace GordieHowe.MLDSA44.Native.ROMParams

open Generated.MLDSA44.Native.ROMParams.Program
open GordieHowe.Bits

/-- **The read records** of `h2c.sample.mem` (`295` coordinates: per step `(j_t, read_value_t,
origin_t)`, then per cell `(k, c_enc_k, final_origin_k)`), shifted by `δ`. -/
def memR : RealizedProgram.Expr :=
  .add (.reindex idx84 (.leaf 567)) (.add (.add
    (.reindex idx85 (.concat (.reindex idx57 (.ref 521)) (.reindex idx47 (.leaf 50))))
    (.scale (.const 2) (.reindex idx85 (.concat (.reindex idx57 (.leaf 561)) (.reindex idx47 (.leaf 563))))))
    (.scale (.const 4) (.reindex idx85 (.concat (.reindex idx57 (.leaf 566)) (.reindex idx47 (.leaf 564))))))

/-- **The write records** of `h2c.sample.mem` (`295` coordinates: the initial cells `(k, 0, 0)`,
per step `(j_t, unit_t, t + 1)`, per step `(256 − τ + t, read_value_t, origin_t)`), shifted by
`δ`. -/
def memW : RealizedProgram.Expr :=
  .add (.reindex idx84 (.leaf 567)) (.add (.add
    (.reindex idx85 (.concat (.reindex idx47 (.concat (.leaf 51) (.reindex idx57 (.ref 521))))
      (.reindex idx57 (.leaf 47))))
    (.scale (.const 2) (.reindex idx85 (.concat (.reindex idx47 (.concat (.leaf 52)
      (.reindex idx57 (.leaf 565)))) (.reindex idx57 (.leaf 561))))))
    (.scale (.const 4) (.reindex idx85 (.concat (.reindex idx47 (.concat (.leaf 52)
      (.reindex idx57 (.leaf 53)))) (.reindex idx57 (.leaf 566))))))

/-- **The program facts of domain `H` SampleInBall's memory check reads** (`MldsaHSelect` and): the memory check's predicates `268`–`270` and shared expressions `520`–`522` (with the index maps of the program at the ROM parameters), the cells' types and the rows' constants. Each program instantiates it by `decide`. -/
class MldsaHShuffle (program : RealizedProgram) : Prop extends MldsaHSelect program where
  /-- The program has a phase. -/
  phases_pos : 0 < program.phases
  /-- `pred268`. -/
  pred268 : program.predicate 268 = «p.h2c.sample.mem.origin»
  /-- `pred269`. -/
  pred269 : program.predicate 269 = «p.h2c.sample.mem»
  /-- `pred270`. -/
  pred270 : program.predicate 270 = «p.h2c.sample.mem.fresh»
  /-- `expr520`. -/
  expr520 : program.expr 520 = .reindex idx57 (.leaf 555)
  /-- `expr521`. -/
  expr521 : program.expr 521 = .apply (.sum 8) (.mul (.reindex idx80 (.leaf 557)) (.reindex idx81 (.leaf 37)))
  /-- `expr522`. -/
  expr522 : program.expr 522 = .add (.mul (.leaf 563) (.leaf 563)) (.leaf 563)
  /-- The memory check's shared expressions are in the table. -/
  refsMem : 524 < program.exprs.length
  /-- The facts of the cells' types. -/
  cellFacts : (∀ v ∈ [561, 563, 564, 565, 566], v < program.values.length ∧ program.IsSourceValue v ∧ (program.value v).typeSource = .node ∧ (program.value v).type = .sub "GF(2^16)" ∧ program.valueField v = 1) ∧ (562 < program.values.length ∧ program.IsSourceValue 562 ∧ (program.value 562).typeSource = .node ∧ (program.value 562).type = .bit) ∧ (program.value 561).size = 39 ∧ (program.value 562).size = 234 ∧ (program.value 563).size = 256 ∧ (program.value 564).size = 256 ∧ (program.value 565).size = 39 ∧ (program.value 566).size = 39
  /-- The constants of the memory check's rows. -/
  memConsts : program.isConstant 48 = true ∧ program.constEntries 48 = List.replicate 39 0 ∧ program.valueField 48 = 1 ∧ program.isConstant 49 = true ∧ program.valueField 49 = 1 ∧ (∀ u < 6, (program.constEntries 49).getD u 0 = (program.constEntries 37).getD u 0) ∧ program.isConstant 54 = true ∧ program.valueField 54 = 1 ∧ (∀ t < 39, ∀ b < 6, (program.constEntries 54).getD (6 * t + b) 0 = (t + 1) / 2 ^ b % 2) ∧ program.isConstant 55 = true ∧ program.valueField 55 = 1 ∧ program.constEntries 55 = List.replicate 39 1
  /-- `freshLen`. -/
  freshLen : program.exprLen (.logic .lt 6 [.leaf 562, .leaf 54]) = 39
  /-- `pred269_body`. -/
  pred269_body : (program.predicate 269).body = .equal 1 (.add (.prod 295 memR) (.prod 295 memW)) (.leaf 36) (.gkr 1)
  /-- The constants of the records. -/
  recConsts : program.isConstant 50 = true ∧ program.valueField 50 = 1 ∧ (∀ k < 256, (program.constEntries 50).getD k 0 = RealizedProgram.xorSel k fun u => (program.constEntries 37).getD u 0) ∧ program.isConstant 51 = true ∧ program.valueField 51 = 1 ∧ (∀ k < 217, (program.constEntries 51).getD k 0 = RealizedProgram.xorSel k fun u => (program.constEntries 37).getD u 0) ∧ program.isConstant 52 = true ∧ program.valueField 52 = 1 ∧ program.constEntries 52 = List.replicate 217 0 ∧ program.isConstant 53 = true ∧ program.valueField 53 = 1 ∧ (∀ t < 39, (program.constEntries 53).getD t 0 = RealizedProgram.xorSel (t + 1) fun u => (program.constEntries 37).getD u 0)
  /-- The lengths of the records' parts. -/
  recLens : program.exprLen (.reindex idx57 (.ref 521)) = 39 ∧ program.exprLen (.reindex idx57 (.leaf 561)) = 39 ∧ program.exprLen (.reindex idx57 (.leaf 566)) = 39 ∧ program.exprLen (.reindex idx47 (.concat (.leaf 51) (.reindex idx57 (.ref 521)))) = 256 ∧ program.exprLen (.reindex idx47 (.concat (.leaf 52) (.reindex idx57 (.leaf 565)))) = 256 ∧ program.exprLen (.reindex idx47 (.concat (.leaf 52) (.reindex idx57 (.leaf 53)))) = 256 ∧ program.exprLen (.leaf 51) = 217 ∧ program.exprLen (.leaf 52) = 217 ∧ program.exprLen memR = 295

set_option maxRecDepth 4096 in
/-- The native program at the ROM parameters has these facts. -/
instance : MldsaHShuffle program where
  phases_pos := by decide
  pred268 := rfl
  pred269 := rfl
  pred270 := rfl
  expr520 := rfl
  expr521 := rfl
  expr522 := rfl
  refsMem := by decide +kernel
  cellFacts := by
    decide +kernel
  memConsts := by
    decide +kernel
  freshLen := by decide +kernel
  pred269_body := rfl
  recConsts := by
    decide +kernel
  recLens := by
    decide +kernel

/-- **`θ = g^21845`**, computed in the spread representation. -/
theorem thetaPow : GF2_128Exec.gfPow 15 21845 gf2_128SubfieldGenBV =
    BitVec.ofNat 128 (54969562866131847669016652494142573320 ^^^ 1) :=
  gfPow_eq_of_spread (by norm_num) (by decide +kernel)

/-- **The constant `54969562866131847669016652494142573320` is `θ + 1`.** -/
theorem decode_theta1 : gf2_128OfNat 54969562866131847669016652494142573320 =
    gf2_128Theta.θ + 1 := by
  change gf2_128OfNat 54969562866131847669016652494142573320 = gf2_128SubfieldGen ^ 21845 + 1
  have h := congrArg gf2_128OfBitVec thetaPow
  rw [gf2_128OfBitVec_gfPow (by norm_num), gf2_128OfBitVec_subfieldGenBV] at h
  rw [h, show (54969562866131847669016652494142573320 : ℕ) =
    (54969562866131847669016652494142573320 ^^^ 1) ^^^ 1 by decide, gf2_128OfNat_xor,
    gf2_128OfNat_one]
  rfl

/-- **`h2c.sample.mem.unit` at the constant `c`** (`θ + 1` in domain `H`'s field): the unit written
at step `t` is `1 + c · sign_t`. -/
def memUnitPred (c : ℕ) : RealizedProgram.Predicate :=
  { name := "h2c.sample.mem.unit",
    body := .equal 1 (.add (.leaf 565) (.add (.scale (.const c) (.ref 520)) (.reindex idx79 (.leaf 7))))
      (.leaf 48) .affine,
    reads := [], degree := [], role := .source }

/-- **The program-and-field facts of domain `H` SampleInBall's memory check reads**
(`MldsaHConstsSelect` and): predicate `267` and the shared expression `523` scale by a constant that
decodes to `θ + 1`. Each program and field instantiates it once. -/
class MldsaHConsts (program : RealizedProgram) (FH : RealizedProgram.FieldInterp) [HField FH] : Prop
    extends MldsaHConstsSelect program FH where
  /-- The constant `θ + 1` of predicate `267` and the shared expression `523`. -/
  theta : ∃ c, program.predicate 267 = memUnitPred c ∧
    program.expr 523 = .add (.leaf 563) (.scale (.const c) (.ref 522)) ∧
    FH.decode c = (HField.Θ (FH := FH)).θ + 1

set_option maxRecDepth 4096 in
/-- The native program at the ROM parameters, over `GF(2^128)`: the constant is `θ + 1 = g^21845 + 1`. -/
instance : MldsaHConsts program RealizedProgram.gf128 where
  theta := ⟨54969562866131847669016652494142573320, rfl, rfl, decode_theta1⟩

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaHShuffle program] {F0 FH : RealizedProgram.FieldInterp} [HField FH]
  [MldsaHConsts program FH]

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

/-! ## The program's data -/

section Tables

set_option maxRecDepth 4096

theorem pred268 : program.predicate 268 = «p.h2c.sample.mem.origin» :=
  MldsaHShuffle.pred268

theorem pred270 : program.predicate 270 = «p.h2c.sample.mem.fresh» :=
  MldsaHShuffle.pred270

theorem expr520 : program.expr 520 = .reindex idx57 (.leaf 555) :=
  MldsaHShuffle.expr520

theorem expr521 : program.expr 521 = .apply (.sum 8) (.mul (.reindex idx80 (.leaf 557)) (.reindex idx81 (.leaf 37))) :=
  MldsaHShuffle.expr521

theorem expr522 : program.expr 522 = .add (.mul (.leaf 563) (.leaf 563)) (.leaf 563) :=
  MldsaHShuffle.expr522

end Tables

/-- The memory check's shared expressions are in the table. -/
theorem refsMem : 524 < program.exprs.length :=
  MldsaHShuffle.refsMem

/-! ## The memory check's record -/

/-- **The signs** (bits `0 … 38` of `h2c.sib.out`, `HashCircuit.signWires`). -/
def signsH (rd : program.Valuation interp) : Fin 39 → (interp 1).K :=
  HashCircuit.signWires (sibByte rd)

/-- **H's decoded challenge** at coefficient `k`: the support (the shared expression `523`) and the
sign (`522`). -/
def chalPair (rd : program.Valuation interp) (k : Fin 256) :
    (interp 1).K × (interp 1).K :=
  (program.evalE rd 1 (.ref 523) k, program.evalE rd 1 (.ref 522) k)

variable (program F0 FH) in
/-- **SampleInBall's memory check** of `MLDSA44.Native.ROMParams` (`SampleInBall`): `256` cells, `39`
steps, the selection field at the ROM parameters, `θ = gf2_128Theta`, the packing constant
`κ = x` (injective on the subfield's records, `gf2_128_pack_injOn`), the selected
bytes, the signs and H's decoded challenge. Its phase layout and `delta` are unused here (the
frontend states the event at the program's challenge). -/
def samM : SampleInBall (program.layout interp) (program.Env interp) (interp 1).K where
  N := 256
  τ := 39
  S := 264
  field := selF
  Θ := HField.Θ
  θ_mem := HField.θ_mem
  κ := selF.X
  packing := HField.packing3
  positions e := jBits (program.reader e)
  signs e := signsH (program.reader e)
  chal e := chalPair (program.reader e)
  k := ⟨0, MldsaHShuffle.phases_pos⟩
  delta _ := 0
  τ_le := by decide
  N_le := by decide
  τ_lt := by decide

theorem samM_τ : (samM program F0 FH).τ = 39 := rfl
theorem samM_N : (samM program F0 FH).N = 256 := rfl
theorem samM_field : (samM program F0 FH).field = selF := rfl
theorem samM_positions (e : program.Env interp) : (samM program F0 FH).positions e = jBits (program.reader e) := by
  simp only [samM]
theorem samM_chal (e : program.Env interp) : (samM program F0 FH).chal e = chalPair (program.reader e) := by
  simp only [samM]
theorem samM_signs (e : program.Env interp) : (samM program F0 FH).signs e = signsH (program.reader e) := by
  simp only [samM]
/-- **The memory check's cells** at an environment: the read values (`561`), the read origins'
bits (`562`), the final cells (`563`), the final origins (`564`), the units (`565`) and the read
origins as subfield values (`566`). -/
def samLowered (e : program.Env interp) : (samM program F0 FH).Lowered where
  base := e
  readValue t := program.evalE (program.reader e) 1 (.leaf 561) t
  readOrigin t := fun b => program.evalE (program.reader e) 1 (.leaf 562) (6 * t + b)
  cEnc k := program.evalE (program.reader e) 1 (.leaf 563) k
  finalOrigin k := program.evalE (program.reader e) 1 (.leaf 564) k
  unit t := program.evalE (program.reader e) 1 (.leaf 565) t
  origin t := program.evalE (program.reader e) 1 (.leaf 566) t

/-- **`δ` of the memory check** (`h2c.sample.mem.delta`, value `567`). -/
def memDelta (rd : program.Valuation interp) : (interp 1).K :=
  program.evalE rd 1 (.leaf 567) 0

section Fields

variable (e : program.Env interp)

theorem samLowered_base : (samLowered e).base = e := by
  unfold samLowered
  rfl
theorem samLowered_readOrigin (t : Fin (samM program F0 FH).τ) (b : Fin 6) :
    (samLowered e).readOrigin t b = program.evalE (program.reader e) 1 (.leaf 562) (6 * t + b) := by
  simp only [samLowered]
theorem samLowered_readValue (t : Fin (samM program F0 FH).τ) :
    (samLowered e).readValue t = program.evalE (program.reader e) 1 (.leaf 561) t := by
  simp only [samLowered]
theorem samLowered_cEnc (k : Fin (samM program F0 FH).N) :
    (samLowered e).cEnc k = program.evalE (program.reader e) 1 (.leaf 563) k := by
  simp only [samLowered]
theorem samLowered_finalOrigin (k : Fin (samM program F0 FH).N) :
    (samLowered e).finalOrigin k = program.evalE (program.reader e) 1 (.leaf 564) k := by
  simp only [samLowered]
theorem samLowered_unit (t : Fin (samM program F0 FH).τ) :
    (samLowered e).unit t = program.evalE (program.reader e) 1 (.leaf 565) t := by
  simp only [samLowered]
theorem samLowered_origin (t : Fin (samM program F0 FH).τ) :
    (samLowered e).origin t = program.evalE (program.reader e) 1 (.leaf 566) t := by
  simp only [samLowered]

end Fields

/-! ## The cells' types -/

/-- The facts of the cells' types. -/
theorem cellFacts : (∀ v ∈ [561, 563, 564, 565, 566], v < program.values.length ∧ program.IsSourceValue v ∧ (program.value v).typeSource = .node ∧ (program.value v).type = .sub "GF(2^16)" ∧ program.valueField v = 1) ∧ (562 < program.values.length ∧ program.IsSourceValue 562 ∧ (program.value 562).typeSource = .node ∧ (program.value 562).type = .bit) ∧ (program.value 561).size = 39 ∧ (program.value 562).size = 234 ∧ (program.value 563).size = 256 ∧ (program.value 564).size = 256 ∧ (program.value 565).size = 39 ∧ (program.value 566).size = 39 :=
  MldsaHShuffle.cellFacts

/-- **A value of `H` typed `GF(2^16)` by its node** lies in the selection subfield where the source
program holds. -/
theorem mem_E_of_typed {e : program.Env interp} (hs : HSat e) {v : ℕ}
    (hv : v ∈ [561, 563, 564, 565, 566]) {i : ℕ} (hi : i < (program.value v).size) :
    program.evalE (program.reader e) 1 (.leaf v) i ∈ selF.E := by
  obtain ⟨-, -, -, hty, hf⟩ := (cellFacts (program := program)).1 v hv
  have h := hs.types v (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> decide) i hi
  rw [hty] at h
  rw [RealizedProgram.evalE_leaf]
  revert h
  generalize program.reader e v i = x
  generalize program.valueField v = a at hf x
  subst hf
  intro h
  rw [RealizedProgram.castElt_self]
  exact HField.mem_sel_of_node x h

/-! ## The unit, origin and freshness rows and the decoded challenge -/

/-- The constants of the memory check's rows. -/
theorem memConsts : program.isConstant 48 = true ∧ program.constEntries 48 = List.replicate 39 0 ∧ program.valueField 48 = 1 ∧ program.isConstant 49 = true ∧ program.valueField 49 = 1 ∧ (∀ u < 6, (program.constEntries 49).getD u 0 = (program.constEntries 37).getD u 0) ∧ program.isConstant 54 = true ∧ program.valueField 54 = 1 ∧ (∀ t < 39, ∀ b < 6, (program.constEntries 54).getD (6 * t + b) 0 = (t + 1) / 2 ^ b % 2) ∧ program.isConstant 55 = true ∧ program.valueField 55 = 1 ∧ program.constEntries 55 = List.replicate 39 1 :=
  MldsaHShuffle.memConsts

/-- The zeros of the memory check's rows (value `48`) read `0`. -/
theorem evalE_48 (e : program.Env interp) (j : ℕ) :
    program.evalE (program.reader e) 1 (.leaf 48) j = 0 := by
  rw [evalE_constH e (memConsts (program := program)).1 (memConsts (program := program)).2.2.1, (memConsts (program := program)).2.1, getD_replicate_zero]
  exact HField.decode_zero

/-- **The signs** read through the memory check's view of the stream (`520`): bit `t` of the stream. -/
theorem evalE_ref520 (e : program.Env interp) {t : ℕ} (ht : t < 39) :
    program.evalE (program.reader e) 1 (.ref 520) t = signsH (program.reader e) ⟨t, ht⟩ := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsMem (program := program)); omega), (expr520 (program := program)), RealizedProgram.evalE_reindex,
    idx57_eq ht]
  have hsg : signsH (program.reader e) ⟨t, ht⟩ = sibBits (program.reader e) ⟨t, by omega⟩ := by
    unfold signsH HashCircuit.signWires sibByte Falcon512.HashCircuit.byteWires
    exact congrArg (sibBits (program.reader e)) (Fin.ext (show 8 * (t / 8) + t % 8 = t by omega))
  rw [hsg]
  unfold sibBits
  rw [if_pos (show t < 1088 by omega)]

/-- **`h2c.sample.mem.unit`**: the unit written at step `t` is `1 + (θ + 1) sign_t`. -/
theorem unitRow {e : program.Env interp} (hs : HSat e) (t : Fin 39) :
    (samLowered e).unit t = MemoryShuffle.unit (samM program F0 FH).Θ (signsH (program.reader e) t) := by
  have ht := t.isLt
  have h := hs.preds 267 (by norm_num) (by norm_num)
  obtain ⟨c, hp, -, hc0⟩ := MldsaHConsts.theta (program := program) (FH := FH)
  rw [hp] at h
  have hh := h t (by rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_leaf, (cellFacts (program := program)).2.2.2.2.2.2.1]; exact ht)
  change program.evalE _ (program.domainField 1) _ _ =
    program.evalE _ (program.domainField 1) _ _ at hh
  rw [MldsaHCross.domainField1, evalE_48, RealizedProgram.evalE_add, RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const,
    evalE_ref520 e ht, RealizedProgram.evalE_reindex, idx79_eq ht, evalE_7] at hh
  have hc : (interp 1).decode c = (samM program F0 FH).Θ.θ + 1 := hc0
  rw [hc] at hh
  unfold MemoryShuffle.unit samLowered
  dsimp only
  rw [RealizedProgram.eq_of_add_eq_zero_charTwo hh, Fin.eta]
  ring

theorem idx82_eq {n : ℕ} (hn : n < 234) : idx82.entry n = n := by
  unfold idx82
  simp [RealizedProgram.IndexMap.ofSegs, RealizedProgram.IdxSeg.expand, RealizedProgram.IndexMap.entry, hn]
theorem idx83_eq {t b : ℕ} (ht : t < 39) (hb : b < 6) : idx83.entry (6 * t + b) = b := by
  unfold idx83
  rw [RealizedProgram.IndexMap.entry_rep (c := 6) (fun j => by simp [RealizedProgram.IndexMap.size, RealizedProgram.IdxSeg.shift]) ht hb]
  simp [RealizedProgram.IndexMap.entry, RealizedProgram.IdxSeg.shift, hb]

/-- **`h2c.sample.mem.origin`**: the read origin as a subfield value is the embedding of its bits. -/
theorem originRow {e : program.Env interp} (hs : HSat e) (t : Fin 39) :
    (samLowered e).origin t = (samM program F0 FH).originOf ((samLowered e).readOrigin t) := by
  have ht := t.isLt
  have h := hs.preds 268 (by norm_num) (by norm_num)
  rw [(pred268 (program := program))] at h
  have hh := h t (by rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_leaf, (cellFacts (program := program)).2.2.2.2.2.2.2]; exact ht)
  change program.evalE _ (program.domainField 1) _ _ =
    program.evalE _ (program.domainField 1) _ _ at hh
  rw [MldsaHCross.domainField1, evalE_48, RealizedProgram.evalE_add, RealizedProgram.evalE_apply_sum] at hh
  unfold samLowered SampleInBall.originOf SelectionField.embedBits
  dsimp only
  rw [RealizedProgram.eq_of_add_eq_zero_charTwo hh]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hb := b.isLt
  rw [RealizedProgram.evalE_mul, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex,
    show (t : ℕ) * 6 + b = 6 * t + b by ring, idx82_eq (by omega), idx83_eq ht hb,
    evalE_constH e (memConsts (program := program)).2.2.2.1 (memConsts (program := program)).2.2.2.2.1, (memConsts (program := program)).2.2.2.2.2.1 b hb,
    MldsaHConstsSelect.c37 b (by omega)]
  rfl

theorem freshLen : program.exprLen (.logic .lt 6 [.leaf 562, .leaf 54]) = 39 :=
  MldsaHShuffle.freshLen

/-- **`h2c.sample.mem.fresh`**: the origin read at step `t` is below `t + 1`. -/
theorem freshRow {e : program.Env interp} (hs : HSat e) (t : Fin 39) :
    Bits.ltConst ((samLowered e).readOrigin t) ((t : ℕ) + 1) = 1 := by
  have ht := t.isLt
  have h := hs.preds 270 (by norm_num) (by norm_num)
  rw [(pred270 (program := program))] at h
  have hh := h t (by rw [(freshLen (program := program))]; exact ht)
  change program.evalE _ (program.domainField 1) _ _ =
    program.evalE _ (program.domainField 1) _ _ at hh
  rw [MldsaHCross.domainField1, RealizedProgram.evalE_logic,
    evalE_constH e (memConsts (program := program)).2.2.2.2.2.2.2.2.2.1 (memConsts (program := program)).2.2.2.2.2.2.2.2.2.2.1,
    (memConsts (program := program)).2.2.2.2.2.2.2.2.2.2.2, List.getD_eq_getElem?_getD, List.getElem?_replicate,
    if_pos ht, Option.getD_some, HField.decode_one] at hh
  simp only [RealizedProgram.LogicOp.eval, List.headD_cons, List.getD_cons_succ, List.getD_cons_zero] at hh
  have hbits : ∀ b < 6, program.evalE (program.reader e) 1 (.leaf 562) (t * 6 + b) = 0 ∨
      program.evalE (program.reader e) 1 (.leaf 562) (t * 6 + b) = 1 := fun b hb => by
    obtain ⟨-, -, -, hty⟩ := (cellFacts (program := program)).2.1
    exact bool_of_bitTypedH hs (by decide) hty (by rw [(cellFacts (program := program)).2.2.2.1]; omega)
  rw [RealizedProgram.Ops.ltWord, RealizedProgram.Ops.ltReduce_congr 6 0 (a' := fun b => program.evalE (program.reader e) 1
    (.leaf 562) (t * 6 + b)) (b' := fun b => Bits.constBit ((t : ℕ) + 1) b)
    (fun b _ => by rw [Nat.zero_add]) (fun b hb => by
      simp only [Nat.zero_add]
      rw [evalE_constH e (memConsts (program := program)).2.2.2.2.2.2.1 (memConsts (program := program)).2.2.2.2.2.2.2.1,
        show (t : ℕ) * 6 + b = 6 * t + b by ring, (memConsts (program := program)).2.2.2.2.2.2.2.2.1 t ht b hb,
        HField.decode_lt_two (Nat.mod_lt _ (by norm_num))]
      rfl), ← RealizedProgram.Ops.ltWord, RealizedProgram.Ops.ltWord_eq_ltConst (fun b hb => hbits b hb) (by omega)] at hh
  have hf : (fun b : Fin 6 => program.evalE (program.reader e) 1 (.leaf 562) (6 * t + b)) =
      fun b : Fin 6 => program.evalE (program.reader e) 1 (.leaf 562) (t * 6 + b) :=
    funext fun b => by rw [Nat.mul_comm]
  unfold samLowered
  dsimp only
  exact (congrArg (fun f => Bits.ltConst f ((t : ℕ) + 1)) hf).trans hh

/-- **The decoded challenge** is `decodeTernary` of the final cell (the shared expressions `522`
and `523`, `θ + 1` the constant of `523`). -/
theorem decodeRow (e : program.Env interp) (k : Fin 256) :
    (samM program F0 FH).chal (samLowered e).base k = MemoryShuffle.decodeTernary (samM program F0 FH).Θ ((samLowered e).cEnc k) := by
  obtain ⟨c, -, he, hc0⟩ := MldsaHConsts.theta (program := program) (FH := FH)
  have hc : (interp 1).decode c = (samM program F0 FH).Θ.θ + 1 := hc0
  change chalPair (program.reader e) k = _
  unfold chalPair MemoryShuffle.decodeTernary samLowered
  dsimp only
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsMem (program := program)); omega), he, RealizedProgram.evalE_add,
    RealizedProgram.evalE_scale_const, hc, RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsMem (program := program)); omega),
    (expr522 (program := program)), RealizedProgram.evalE_add, RealizedProgram.evalE_mul, sq]

/-! ## The permutation -/

theorem pred269_body : (program.predicate 269).body = .equal 1 (.add (.prod 295 memR) (.prod 295 memW)) (.leaf 36) (.gkr 1) :=
  MldsaHShuffle.pred269_body

/-- The constants of the records. -/
theorem recConsts : program.isConstant 50 = true ∧ program.valueField 50 = 1 ∧ (∀ k < 256, (program.constEntries 50).getD k 0 = RealizedProgram.xorSel k fun u => (program.constEntries 37).getD u 0) ∧ program.isConstant 51 = true ∧ program.valueField 51 = 1 ∧ (∀ k < 217, (program.constEntries 51).getD k 0 = RealizedProgram.xorSel k fun u => (program.constEntries 37).getD u 0) ∧ program.isConstant 52 = true ∧ program.valueField 52 = 1 ∧ program.constEntries 52 = List.replicate 217 0 ∧ program.isConstant 53 = true ∧ program.valueField 53 = 1 ∧ (∀ t < 39, (program.constEntries 53).getD t 0 = RealizedProgram.xorSel (t + 1) fun u => (program.constEntries 37).getD u 0) :=
  MldsaHShuffle.recConsts

/-- The lengths of the records' parts. -/
theorem recLens : program.exprLen (.reindex idx57 (.ref 521)) = 39 ∧ program.exprLen (.reindex idx57 (.leaf 561)) = 39 ∧ program.exprLen (.reindex idx57 (.leaf 566)) = 39 ∧ program.exprLen (.reindex idx47 (.concat (.leaf 51) (.reindex idx57 (.ref 521)))) = 256 ∧ program.exprLen (.reindex idx47 (.concat (.leaf 52) (.reindex idx57 (.leaf 565)))) = 256 ∧ program.exprLen (.reindex idx47 (.concat (.leaf 52) (.reindex idx57 (.leaf 53)))) = 256 ∧ program.exprLen (.leaf 51) = 217 ∧ program.exprLen (.leaf 52) = 217 ∧ program.exprLen memR = 295 :=
  MldsaHShuffle.recLens

theorem idx47_eq {k : ℕ} (hk : k < 256) : idx47.entry k = k := by
  unfold idx47
  simp [RealizedProgram.IndexMap.ofSegs, RealizedProgram.IdxSeg.expand, RealizedProgram.IndexMap.entry, hk]
theorem idx84_eq {t : ℕ} (ht : t < 295) : idx84.entry t = 0 := by
  unfold idx84
  simp [RealizedProgram.IndexMap.ofSegs, RealizedProgram.IdxSeg.expand, RealizedProgram.IndexMap.entry, ht]
theorem idx85_eq {t : ℕ} (ht : t < 295) : idx85.entry t = t := by
  unfold idx85
  simp [RealizedProgram.IndexMap.ofSegs, RealizedProgram.IdxSeg.expand, RealizedProgram.IndexMap.entry, ht]

/-- **A constant of embedded addresses** reads the embedding of its index. -/
theorem evalE_embedConst (e : program.Env interp) {v k m : ℕ} (hc : program.isConstant v = true)
    (hf : program.valueField v = 1)
    (hk : (program.constEntries v).getD k 0 = RealizedProgram.xorSel m fun u => (program.constEntries 37).getD u 0)
    (hk' : m < 256) :
    program.evalE (program.reader e) 1 (.leaf v) k = selF.embed m := by
  rw [evalE_constH e hc hf, hk, RealizedProgram.decode_xorSel, SelectionField.embed_of_lt_256 _ hk']
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [MldsaHConstsSelect.c37 u u.isLt]

/-- **The selected bytes' addresses** (the shared expression `521`). -/
theorem evalE_ref521 (e : program.Env interp) {t : ℕ} (ht : t < 39) :
    program.evalE (program.reader e) 1 (.ref 521) t = (samM program F0 FH).addr (jBits (program.reader e) ⟨t, ht⟩) := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsMem (program := program)); omega), (expr521 (program := program))]
  exact evalE_embed8 e ht (fun t' ht' => idx80_eq (by omega)) (fun u hu => idx81_eq ht hu)
    (fun u => rfl)

/-- `κ² = x²` is the decoding of `4`. -/
theorem decode_four : (interp 1).decode 4 = selF.X ^ 2 := HField.decode_four

/-- **A packed record**, shifted by `δ`: `δ − (a + κ v + κ² o) = δ + a + x v + x² o`. -/
theorem sub_pack3 (δ a v o : (interp 1).K) :
    δ - (samM program F0 FH).pack3 a v o = δ + (a + (interp 1).decode 2 * v + (interp 1).decode 4 * o) := by
  rw [decode_four, selF_X, CharTwo.sub_eq_add]
  unfold SampleInBall.pack3 RecordPacking.pack
  simp only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, one_mul,
    pow_one, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rfl

/-- **The read record of coordinate `t`**: per step `(addr j_t, read_value_t, origin_t)`, then per
cell `(k, c_enc_k, final_origin_k)`, each packed at `x` and shifted by `δ`. -/
def readRec (rd : program.Valuation interp) (t : ℕ) : (interp 1).K :=
  program.evalE rd 1 (.leaf 567) 0 +
    (if t < 39 then
      program.evalE rd 1 (.ref 521) t + (interp 1).decode 2 * program.evalE rd 1 (.leaf 561) t +
        (interp 1).decode 4 * program.evalE rd 1 (.leaf 566) t
    else
      selF.embed (t - 39) + (interp 1).decode 2 * program.evalE rd 1 (.leaf 563) (t - 39) +
        (interp 1).decode 4 * program.evalE rd 1 (.leaf 564) (t - 39))

/-- **The read records' coordinates** (`memR`, coordinate `t < 295`). -/
theorem evalE_memR (e : program.Env interp) {t : ℕ} (ht : t < 295) :
    program.evalE (program.reader e) 1 memR t = readRec (program.reader e) t := by
  unfold memR readRec
  simp only [RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const, RealizedProgram.evalE_reindex, idx84_eq ht,
    idx85_eq ht, RealizedProgram.evalE_concat, (recLens (program := program)).1, (recLens (program := program)).2.1, (recLens (program := program)).2.2.1]
  by_cases h39 : t < 39
  · simp only [if_pos h39, idx57_eq h39]
  · simp only [if_neg h39, idx47_eq (show t - 39 < 256 by omega)]
    rw [evalE_embedConst e (recConsts (program := program)).1 (recConsts (program := program)).2.1 ((recConsts (program := program)).2.2.1 (t - 39) (by omega))
      (by omega)]

/-- A map over `List.finRange` is a map over `List.range` of the values. -/
theorem map_finRange_eq {α : Type*} {n : ℕ} (f : ℕ → α) :
    (List.finRange n).map (fun t : Fin n => f t) = (List.range n).map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem_finRange]

/-- **The read records are the packed reads**, shifted by `δ`. -/
theorem reads_eq (e : program.Env interp) :
    (List.range 295).map (readRec (program.reader e)) =
      ((samM program F0 FH).readsPacked (samLowered e)).map fun x => memDelta (program.reader e) - x := by
  unfold SampleInBall.readsPacked
  rw [List.map_append, List.map_map, List.map_map, show 295 = 39 + 256 from rfl, List.range_add,
    List.map_append, List.map_map]
  have h1 : (fun x => memDelta (program.reader e) - x) ∘ (fun t : Fin (samM program F0 FH).τ =>
      (samM program F0 FH).pack3 ((samM program F0 FH).addr ((samM program F0 FH).positions (samLowered e).base t)) ((samLowered e).readValue t)
        ((samLowered e).origin t)) = fun t : Fin (samM program F0 FH).τ => readRec (program.reader e) t := by
    funext t
    have ht : (t : ℕ) < 39 := t.isLt
    simp only [Function.comp_apply, samLowered_base, samLowered_readValue,
      samLowered_origin, samM_positions, readRec, if_pos ht, evalE_ref521 e ht, memDelta]
    rw [sub_pack3]
    rfl
  have h2 : (fun x => memDelta (program.reader e) - x) ∘ (fun k : Fin (samM program F0 FH).N =>
      (samM program F0 FH).pack3 ((samM program F0 FH).field.embed (k : ℕ)) ((samLowered e).cEnc k) ((samLowered e).finalOrigin k)) =
      fun k : Fin (samM program F0 FH).N => readRec (program.reader e) (39 + k) := by
    funext k
    simp only [Function.comp_apply, samLowered_cEnc, samLowered_finalOrigin, samM_field,
      readRec, if_neg (show ¬ 39 + (k : ℕ) < 39 by omega), Nat.add_sub_cancel_left, memDelta]
    rw [sub_pack3]
    rfl
  rw [h1, h2, map_finRange_eq (readRec (program.reader e)),
    map_finRange_eq (fun k => readRec (program.reader e) (39 + k)), samM_τ, samM_N]
  rfl

/-- **The write record of coordinate `t`**: the initial cells `(k, 0, 0)`, per step
`(addr j_t, unit_t, t + 1)`, per step `(256 − τ + t, read_value_t, origin_t)`, each packed at `x` and
shifted by `δ`. -/
def writeRec (rd : program.Valuation interp) (t : ℕ) : (interp 1).K :=
  program.evalE rd 1 (.leaf 567) 0 +
    (if t < 217 then selF.embed t + (interp 1).decode 2 * 0 + (interp 1).decode 4 * 0
    else if t < 256 then
      program.evalE rd 1 (.ref 521) (t - 217) +
        (interp 1).decode 2 * program.evalE rd 1 (.leaf 565) (t - 217) +
        (interp 1).decode 4 * selF.embed (t - 217 + 1)
    else
      selF.embed (256 - 39 + (t - 256)) +
        (interp 1).decode 2 * program.evalE rd 1 (.leaf 561) (t - 256) +
        (interp 1).decode 4 * program.evalE rd 1 (.leaf 566) (t - 256))

/-- The zeros of the initial cells (value `52`) read `0`. -/
theorem evalE_52 (e : program.Env interp) (j : ℕ) :
    program.evalE (program.reader e) 1 (.leaf 52) j = 0 := by
  rw [evalE_constH e (recConsts (program := program)).2.2.2.2.2.2.1 (recConsts (program := program)).2.2.2.2.2.2.2.1, (recConsts (program := program)).2.2.2.2.2.2.2.2.1,
    getD_replicate_zero]
  exact HField.decode_zero

/-- **The write records' coordinates** (`memW`, coordinate `t < 295`). -/
theorem evalE_memW (e : program.Env interp) {t : ℕ} (ht : t < 295) :
    program.evalE (program.reader e) 1 memW t = writeRec (program.reader e) t := by
  unfold memW writeRec
  simp only [RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const, RealizedProgram.evalE_reindex, idx84_eq ht,
    idx85_eq ht, RealizedProgram.evalE_concat, (recLens (program := program)).2.2.2.1, (recLens (program := program)).2.2.2.2.1, (recLens (program := program)).2.2.2.2.2.1,
    (recLens (program := program)).2.2.2.2.2.2.1, (recLens (program := program)).2.2.2.2.2.2.2.1]
  by_cases h256 : t < 256
  · simp only [if_pos h256, idx47_eq h256]
    by_cases h217 : t < 217
    · rw [if_pos h217, if_pos h217, if_pos h217, if_pos h217,
        evalE_embedConst e (recConsts (program := program)).2.2.2.1 (recConsts (program := program)).2.2.2.2.1 ((recConsts (program := program)).2.2.2.2.2.1 t h217)
          (by omega), evalE_52]
    · rw [if_neg h217, if_neg h217, if_neg h217, if_neg h217]
      simp only [idx57_eq (show t - 217 < 39 by omega)]
      rw [evalE_embedConst e (recConsts (program := program)).2.2.2.2.2.2.2.2.2.1 (recConsts (program := program)).2.2.2.2.2.2.2.2.2.2.1
        ((recConsts (program := program)).2.2.2.2.2.2.2.2.2.2.2 (t - 217) (by omega)) (by omega)]
  · rw [if_neg h256, if_neg h256, if_neg h256, if_neg (by omega), if_neg h256]
    simp only [idx57_eq (show t - 256 < 39 by omega)]
    rw [evalE_47 e (by omega)]

/-- **The write records are the packed writes**, shifted by `δ`. -/
theorem writes_eq (e : program.Env interp) :
    (List.range 295).map (writeRec (program.reader e)) =
      ((samM program F0 FH).writesPacked (samLowered e)).map fun x => memDelta (program.reader e) - x := by
  unfold SampleInBall.writesPacked
  rw [List.map_append, List.map_append, List.map_map, List.map_map, List.map_map,
    show 295 = (217 + 39) + 39 from rfl, List.range_add, List.range_add, List.map_append,
    List.map_append, List.map_map, List.map_map]
  have h0 : (fun x => memDelta (program.reader e) - x) ∘
      (fun k => (samM program F0 FH).pack3 ((samM program F0 FH).field.embed k) 0 0) =
        fun k => if k < 217 then writeRec (program.reader e) k else memDelta (program.reader e) -
          (samM program F0 FH).pack3 ((samM program F0 FH).field.embed k) 0 0 := by
    funext k
    simp only [Function.comp_apply]
    split_ifs with hk
    · simp only [samM_field, memDelta, writeRec, if_pos hk]
      rw [sub_pack3]
      rfl
    · rfl
  have h1 : (fun x => memDelta (program.reader e) - x) ∘ (fun t : Fin (samM program F0 FH).τ =>
      (samM program F0 FH).pack3 ((samM program F0 FH).addr ((samM program F0 FH).positions (samLowered e).base t)) ((samLowered e).unit t)
        ((samM program F0 FH).field.embed ((t : ℕ) + 1))) =
      fun t : Fin (samM program F0 FH).τ => writeRec (program.reader e) (217 + t) := by
    funext t
    have ht : (t : ℕ) < 39 := t.isLt
    simp only [Function.comp_apply, samLowered_base, samLowered_unit, samM_positions, samM_field,
      memDelta, writeRec, if_neg (show ¬ 217 + (t : ℕ) < 217 by omega),
      if_pos (show 217 + (t : ℕ) < 256 by omega), Nat.add_sub_cancel_left, evalE_ref521 e ht]
    rw [sub_pack3]
    rfl
  have h2 : (fun x => memDelta (program.reader e) - x) ∘ (fun t : Fin (samM program F0 FH).τ =>
      (samM program F0 FH).pack3 ((samM program F0 FH).field.embed ((samM program F0 FH).N - (samM program F0 FH).τ + (t : ℕ))) ((samLowered e).readValue t)
        ((samLowered e).origin t)) =
      fun t : Fin (samM program F0 FH).τ => writeRec (program.reader e) (217 + 39 + t) := by
    funext t
    rw [Function.comp_apply]
    simp only [samLowered_readValue, samLowered_origin, samM_field, samM_N,
      samM_τ, memDelta, writeRec, if_neg (show ¬ 217 + 39 + (t : ℕ) < 217 by omega),
      if_neg (show ¬ 217 + 39 + (t : ℕ) < 256 by omega),
      show 217 + 39 + (t : ℕ) - 256 = t by omega]
    rw [sub_pack3]
    rfl
  rw [h0, h1, h2, map_finRange_eq (fun t => writeRec (program.reader e) (217 + t)),
    map_finRange_eq (fun t => writeRec (program.reader e) (217 + 39 + t)), samM_N, samM_τ]
  have h3 : (List.range 217).map (fun k => if k < 217 then writeRec (program.reader e) k else
      memDelta (program.reader e) - (samM program F0 FH).pack3 ((samM program F0 FH).field.embed k) 0 0) =
      (List.range 217).map (writeRec (program.reader e)) :=
    List.map_congr_left fun k hk => if_pos (List.mem_range.1 hk)
  rw [show 256 - 39 = 217 from rfl, h3]
  rfl

/-- **`h2c.sample.mem`**: the read records' product and the write records' product agree at `δ`
(characteristic two). -/
theorem permRow {e : program.Env interp} (hs : HSat e) :
    (((samM program F0 FH).readsPacked (samLowered e)).map fun x => memDelta (program.reader e) - x).prod =
      (((samM program F0 FH).writesPacked (samLowered e)).map fun x => memDelta (program.reader e) - x).prod := by
  have h36 := fun i => RealizedProgram.reader_of_constant e (RealizedProgram.kind_of_isConstant (selConstsA (program := program)).1) i
  have h := hs.preds 269 (by norm_num) (by norm_num)
  rw [(pred269_body (program := program))] at h
  have h0 := h 0 (by
    rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_prod, (recLens (program := program)).2.2.2.2.2.2.2.2]
    norm_num)
  change program.evalE _ (program.domainField 1) (.prod 295 memR) 0 +
    program.evalE _ (program.domainField 1) (.prod 295 memW) 0 =
      program.evalE _ (program.domainField 1) _ 0 at h0
  rw [MldsaHCross.domainField1, RealizedProgram.evalE_prod, RealizedProgram.evalE_prod, evalE_36 _ h36] at h0
  have hR : (List.range 295).map (fun t => program.evalE (program.reader e) 1 memR (0 * 295 + t)) =
      (List.range 295).map (readRec (program.reader e)) :=
    List.map_congr_left fun t ht => by
      rw [Nat.zero_mul, Nat.zero_add, evalE_memR e (List.mem_range.1 ht)]
  have hW : (List.range 295).map (fun t => program.evalE (program.reader e) 1 memW (0 * 295 + t)) =
      (List.range 295).map (writeRec (program.reader e)) :=
    List.map_congr_left fun t ht => by
      rw [Nat.zero_mul, Nat.zero_add, evalE_memW e (List.mem_range.1 ht)]
  rw [hR, hW, reads_eq, writes_eq] at h0
  exact RealizedProgram.eq_of_add_eq_zero_charTwo h0

/-- **The memory check's constraints hold** (`SampleInBall.Checks`) at the program's cells and
`δ = h2c.sample.mem.delta`, where the source program holds. -/
theorem checks {e : program.Env interp} (hs : HSat e) :
    (samM program F0 FH).Checks (samLowered e) (memDelta (program.reader e)) where
  originBits t b := by
    obtain ⟨-, -, -, hty⟩ := (cellFacts (program := program)).2.1
    have ht := t.isLt
    have hb := b.isLt
    rw [samLowered_readOrigin]
    exact bool_of_bitTypedH hs (by decide) hty (by
      rw [(cellFacts (program := program)).2.2.2.1]
      change (t : ℕ) < 39 at ht
      omega)
  readValue_mem t := by
    rw [samLowered_readValue, samM_field]
    exact mem_E_of_typed hs (by simp) (by rw [(cellFacts (program := program)).2.2.1]; exact t.isLt)
  cEnc_mem k := by
    rw [samLowered_cEnc, samM_field]
    exact mem_E_of_typed hs (by simp) (by rw [(cellFacts (program := program)).2.2.2.2.1]; exact k.isLt)
  finalOrigin_mem k := by
    rw [samLowered_finalOrigin, samM_field]
    exact mem_E_of_typed hs (by simp) (by rw [(cellFacts (program := program)).2.2.2.2.2.1]; exact k.isLt)
  unitRow t := unitRow hs t
  originRow t := originRow hs t
  fresh t := freshRow hs t
  decode k := decodeRow e k
  perm := permRow hs

/-- **SampleInBall's memory check is sound** (`SampleInBall.shuffles_or_bad`): where the source
program holds, on checked positions H's decoded challenge is the ternary decoding of the shuffle,
or `δ` is a root of the permutation event. -/
theorem shuffles_or_bad {e : program.Env interp} (hs : HSat e) :
    (samM program F0 FH).Shuffles (samLowered e).base ∨
      ((samM program F0 FH).bad (samLowered e)).BadAt (memDelta (program.reader e)) :=
  (samM program F0 FH).shuffles_or_bad (checks hs)

end GordieHowe.MLDSA44.Native.ROMParams
