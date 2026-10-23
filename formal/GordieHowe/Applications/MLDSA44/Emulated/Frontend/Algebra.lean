-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Emulated.Frontend.Cross
public import GordieHowe.Applications.MLDSA44.Emulated.Frontend.Layout
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Frontend.Algebra
public import GordieHowe.Applications.MLDSA44.Emulated.System.Algebra
public import GordieHowe.Language.Realizations.Realize

@[expose] public section

/-!
# GordieHowe frontend: an emulated ML-DSA program, the algebra of domain `A`

Domain `A`'s obligation of the emulated frontend (`GordieHowe.MLDSA44.Emulated.ROMParams.AlgebraSound`,
`algebraSound`): wherever the source program holds, at every key whose preprocessing the statement
holds, the readings of domain `A` (domain `A`'s Goldilocks extension, in which every ML-DSA value is
an integer) satisfy `AlgebraAt`:

* the type checks (`h.boolean`, `challenge.c.boolean`, `hint.w1.boolean`,
  `hint.nonpositive.boolean`) make the hint, the challenge bits, the UseHint output bits and the
  sign advice bits;
* the ranges `signature.w`, `norm.z`, `hint.offset`, `hint.slack` and `hint_weight.weight` make `w'`
  a natural below `2^24`, `z + 130993` a natural below `261987`, the offset and the slack naturals
  below the layout's bound (`MldsaELayout.offsetBound`), and the hint weight below `81`;
* `hint.w1_bound`, `hint.interval` (an integer `mod_0`, read as its field equation) and
  `hint.decompose` (the wrap `e (e − q) = 0`) are `UseHint.WrapHolds` at every coefficient, so
  `UseHint.wrap_sound` gives UseHint;
* `signature.relation` (predicate `274`, a source `mod_q`) states that `q` divides the integer
  `w' + 2^d t1 · support − 2^(d+1) t1 · sign − A z` at every coefficient, `A` and `t1` the
  statement's in coefficient form (`KeyOf`); so `w' = computeWApprox(Â, c, z, t1)`
  (`GordieHowe.MLDSA44.Emulated.Rows.Congruent.computeWApprox`).
-/

namespace GordieHowe.MLDSA44.Emulated

open Generated.MLDSA44.Emulated.ROMParams.Program
open GordieHowe.Bits
open Native.ROMParams (MldsaHHash MldsaHSample MldsaHConsts)

/-- **The left side of the signature relation.** -/
abbrev sigL : RealizedProgram.Expr :=
  .add (.add (.leaf 62) (.scale (.const 8192) (.apply (.polyBroadcast 58 4 .coefficients) (.ref 7))))
    (.scale (.const 18446744069414567937) (.apply (.polyBroadcast 58 4 .coefficients) (.ref 8)))

/-- **The right side of the signature relation.** -/
abbrev sigR : RealizedProgram.Expr := .apply (.polyMatVec 57 4 4 .coefficients) (.leaf 59)

/-- **The program facts of an emulated program's domain `A`** (`MldsaECross` and): the program's
digit layout (`MldsaELayout`), the source predicates of `A` with their realization records free
and their shared expressions (with the index maps of the program at the ROM parameters), their lengths, constants and
types. Each emulated program instantiates it by `decide`. -/
class MldsaEAlgebra (program : RealizedProgram) extends MldsaECross program where
  /-- The program's digit layout. -/
  layout : MldsaELayout
  /-- The offset's and the slack's bound leaves room in the Goldilocks prime (`UseHint.wrap_sound`). -/
  offsetBound_lt : 2 * (layout.offsetBound - 1) < pGold
  /-- The hint's sum has a coordinate. -/
  lenWeight : 0 < program.exprLen (.apply (.sum 1024) (.leaf 60))
  /-- The left side of the signature relation has `1024` coordinates. -/
  lenSigL : program.exprLen sigL = 1024
  /-- `pred0`. -/
  pred0 : program.predicate 0 = «p.hint.w1_bound»
  /-- `pred1`. -/
  pred1 : program.predicate 1 = «p.hint.decompose»
  /-- `pred2`. -/
  pred2 : program.predicate 2 = «p.hint.interval»
  /-- `signature.w`: `w'` below `2^24`. -/
  pred11 : ∃ real, (program.predicate 11).body = .mem 0 [.leaf 62] (.range 16777216) real
  /-- `norm.z`: `z + 130993` below `261987`. -/
  pred12 : ∃ real, (program.predicate 12).body = .mem 0 [.add (.leaf 59) (.leaf 63)] (.range 261987) real
  /-- `hint.offset`: the offset below the layout's bound. -/
  pred13 : ∃ real, (program.predicate 13).body = .mem 0 [.leaf 66] (.range layout.offsetBound) real
  /-- `hint.slack`: the slack below the layout's bound. -/
  pred14 : ∃ real, (program.predicate 14).body = .mem 0 [.leaf 67] (.range layout.offsetBound) real
  /-- `hint_weight.weight`: the hint's sum below `81`. -/
  pred15 : ∃ real, (program.predicate 15).body = .mem 0 [.apply (.sum 1024) (.leaf 60)] (.range 81) real
  /-- `signature.relation`: `q` divides the sides' integer difference. -/
  pred274 : ∃ real, (program.predicate 274).body = .mod 0 8380417 sigL sigR real
  /-- `expr7`. -/
  expr7 : program.expr 7 = .reindex idx11 (.leaf 61)
  /-- `expr8`. -/
  expr8 : program.expr 8 = .reindex idx12 (.leaf 61)
  /-- `expr0`. -/
  expr0 : program.expr 0 = .mul (.leaf 60) (.leaf 65)
  /-- `expr1`. -/
  expr1 : program.expr 1 = .add (.leaf 60) (.scale (.const 18446744069414584320) (.ref 0))
  /-- `expr2`. -/
  expr2 : program.expr 2 = .logic .eq 6 [.leaf 64, .reindex idx6 (.leaf 2)]
  /-- `expr3`. -/
  expr3 : program.expr 3 = .mul (.ref 0) (.logic .eq 6 [.leaf 64, .reindex idx6 (.leaf 0)])
  /-- `expr4`. -/
  expr4 : program.expr 4 = .add (.mul (.add (.leaf 65) (.scale (.const 18446744069414584320) (.ref 0))) (.ref 2)) (.ref 3)
  /-- `expr5`. -/
  expr5 : program.expr 5 = .add (.add (.add (.leaf 62) (.scale (.const 18446744069414584320) (.scale (.const 190464) (.add (.add (.add (.apply (.batched 1024 (.fromDigits 6 2)) (.leaf 64)) (.scale (.const 18446744069414584320) (.ref 1))) (.ref 0)) (.scale (.const 44) (.add (.mul (.ref 1) (.ref 2)) (.scale (.const 18446744069414584320) (.ref 3)))))))) (.scale (.const 18446744069414584320) (.add (.add (.scale (.const 18446744069414584320) (.scale (.const 95232) (.leaf 65))) (.reindex idx7 (.leaf 3))) (.scale (.const 18446744069414584320) (.ref 4))))) (.scale (.const 18446744069414584320) (.leaf 66))
  /-- Domain `A`'s predicates are source predicates. -/
  inSource_A : ∀ p ∈ [0, 1, 2, 6, 7, 8, 9, 11, 12, 13, 14, 15, 274], p < program.predicates.length ∧ program.inSource (program.predicate p) = true
  /-- The lengths and field facts of domain `A`. -/
  lensA : (program.value 59).size = 1024 ∧ (program.value 60).size = 1024 ∧ (program.value 61).size = 512 ∧ (program.value 62).size = 1024 ∧ (program.value 64).size = 6144 ∧ (program.value 65).size = 1024 ∧ (program.value 66).size = 1024 ∧ (program.value 67).size = 1024 ∧ program.domainField 0 = 0
  /-- The type checks of `A` are Boolean checks of their values. -/
  boolChecks : (program.predicate 6).body.boolCheck? = some ⟨0, 60⟩ ∧ (program.predicate 7).body.boolCheck? = some ⟨0, 61⟩ ∧ (program.predicate 8).body.boolCheck? = some ⟨0, 64⟩ ∧ (program.predicate 9).body.boolCheck? = some ⟨0, 65⟩
  /-- The constants domain `A` reads. -/
  constsA : program.isConstant 63 = true ∧ program.valueField 63 = 0 ∧ program.constEntries 63 = List.replicate 1024 130993
  /-- The constants UseHint reads. -/
  constsU : program.isConstant 0 = true ∧ program.constEntries 0 = [1, 1, 0, 1, 0, 1] ∧ program.isConstant 1 = true ∧ program.constEntries 1 = List.replicate 1024 1 ∧ program.isConstant 2 = true ∧ program.constEntries 2 = [0, 0, 0, 0, 0, 0] ∧ program.isConstant 3 = true ∧ program.constEntries 3 = [1] ∧ program.isConstant 4 = true ∧ program.constEntries 4 = [18446744069406203904] ∧ program.isConstant 5 = true ∧ program.constEntries 5 = List.replicate 1024 0 ∧ program.isConstant 6 = true ∧ program.constEntries 6 = [95231] ∧ program.valueField 0 = 0 ∧ program.valueField 1 = 0 ∧ program.valueField 2 = 0 ∧ program.valueField 3 = 0 ∧ program.valueField 4 = 0 ∧ program.valueField 5 = 0 ∧ program.valueField 6 = 0
  /-- `refsA`. -/
  refsA : 5 < program.exprs.length
  /-- The lengths of UseHint's predicates. -/
  lensU : program.exprLen (.logic .leq 6 [.leaf 64, .reindex idx6 (.leaf 0)]) = 1024 ∧ program.exprLen (.mul (.ref 5) (.add (.ref 5) (.reindex idx7 (.leaf 4)))) = 1024 ∧ program.exprLen (.add (.leaf 66) (.leaf 67)) = 1024
  /-- The values UseHint reads are not constants, of field `0`. -/
  valsU : program.isConstant 60 = false ∧ program.isConstant 64 = false ∧ program.isConstant 65 = false ∧ program.isConstant 66 = false ∧ program.isConstant 67 = false ∧ program.valueField 60 = 0 ∧ program.valueField 64 = 0 ∧ program.valueField 65 = 0 ∧ program.valueField 66 = 0 ∧ program.valueField 67 = 0
  /-- The sizes, fields and kinds the signature relation reads. -/
  sigData : (program.value 57).size = 4096 ∧ (program.value 58).size = 1024 ∧ program.valueField 57 = 0 ∧ program.valueField 58 = 0 ∧ program.isConstant 59 = false ∧ program.isConstant 61 = false ∧ program.isConstant 62 = false ∧ program.valueField 59 = 0 ∧ program.valueField 61 = 0 ∧ program.valueField 62 = 0 ∧ 8 < program.exprs.length ∧ RealizedProgram.isOpaqueNil (program.value 57).kind = true ∧ RealizedProgram.isOpaqueNil (program.value 58).kind = true
  /-- The kinds of `z` and `w'` (values bound to their digits). -/
  boundZW : (program.value 59).kind.isBound = true ∧ (program.value 62).kind.isBound = true ∧ (program.value 61).kind.isPriv = true

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaEAlgebra program] {F0 FH : RealizedProgram.FieldInterp} [AField F0]
  [HField FH]

set_option hygiene false in
local notation "nat" => MldsaEmbed.nat program

variable [MldsaHHash nat] [MldsaHSample nat] [MldsaHConsts nat FH]

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

/-! ## The program's data -/

section Tables

set_option maxRecDepth 4096

theorem pred0 : program.predicate 0 = «p.hint.w1_bound» :=
  MldsaEAlgebra.pred0

theorem pred1 : program.predicate 1 = «p.hint.decompose» :=
  MldsaEAlgebra.pred1

theorem pred2 : program.predicate 2 = «p.hint.interval» :=
  MldsaEAlgebra.pred2

theorem pred11 : ∃ real, (program.predicate 11).body = .mem 0 [.leaf 62] (.range 16777216) real :=
  MldsaEAlgebra.pred11

theorem pred12 : ∃ real, (program.predicate 12).body =
    .mem 0 [.add (.leaf 59) (.leaf 63)] (.range 261987) real :=
  MldsaEAlgebra.pred12

theorem pred13 : ∃ real, (program.predicate 13).body =
    .mem 0 [.leaf 66] (.range (MldsaEAlgebra.layout program).offsetBound) real :=
  MldsaEAlgebra.pred13

theorem pred14 : ∃ real, (program.predicate 14).body =
    .mem 0 [.leaf 67] (.range (MldsaEAlgebra.layout program).offsetBound) real :=
  MldsaEAlgebra.pred14

theorem pred15 : ∃ real, (program.predicate 15).body =
    .mem 0 [.apply (.sum 1024) (.leaf 60)] (.range 81) real :=
  MldsaEAlgebra.pred15

theorem pred274 : ∃ real, (program.predicate 274).body = .mod 0 8380417 sigL sigR real :=
  MldsaEAlgebra.pred274

/-- **A natural below the offset's bound has room in the Goldilocks prime.** -/
theorem two_mul_lt_of_offset {k : ℕ} (hk : k < (MldsaEAlgebra.layout program).offsetBound) :
    2 * k < pGold := by
  have := MldsaEAlgebra.offsetBound_lt (program := program)
  omega

theorem expr7 : program.expr 7 = .reindex idx11 (.leaf 61) :=
  MldsaEAlgebra.expr7

theorem expr8 : program.expr 8 = .reindex idx12 (.leaf 61) :=
  MldsaEAlgebra.expr8

theorem expr0 : program.expr 0 = .mul (.leaf 60) (.leaf 65) :=
  MldsaEAlgebra.expr0

theorem expr1 : program.expr 1 = .add (.leaf 60) (.scale (.const 18446744069414584320) (.ref 0)) :=
  MldsaEAlgebra.expr1

theorem expr2 : program.expr 2 = .logic .eq 6 [.leaf 64, .reindex idx6 (.leaf 2)] :=
  MldsaEAlgebra.expr2

theorem expr3 : program.expr 3 = .mul (.ref 0) (.logic .eq 6 [.leaf 64, .reindex idx6 (.leaf 0)]) :=
  MldsaEAlgebra.expr3

theorem expr4 : program.expr 4 = .add (.mul (.add (.leaf 65) (.scale (.const 18446744069414584320) (.ref 0))) (.ref 2)) (.ref 3) :=
  MldsaEAlgebra.expr4

theorem expr5 : program.expr 5 = .add (.add (.add (.leaf 62) (.scale (.const 18446744069414584320) (.scale (.const 190464) (.add (.add (.add (.apply (.batched 1024 (.fromDigits 6 2)) (.leaf 64)) (.scale (.const 18446744069414584320) (.ref 1))) (.ref 0)) (.scale (.const 44) (.add (.mul (.ref 1) (.ref 2)) (.scale (.const 18446744069414584320) (.ref 3)))))))) (.scale (.const 18446744069414584320) (.add (.add (.scale (.const 18446744069414584320) (.scale (.const 95232) (.leaf 65))) (.reindex idx7 (.leaf 3))) (.scale (.const 18446744069414584320) (.ref 4))))) (.scale (.const 18446744069414584320) (.leaf 66)) :=
  MldsaEAlgebra.expr5

end Tables

/-- Domain `A`'s predicates are source predicates. -/
theorem inSource_A : ∀ p ∈ [0, 1, 2, 6, 7, 8, 9, 11, 12, 13, 14, 15, 274], p < program.predicates.length ∧ program.inSource (program.predicate p) = true :=
  MldsaEAlgebra.inSource_A

/-- **A source predicate of `A` holds** where the source program holds. -/
theorem holdsA {e : program.Env interp} (hs : program.SourceSatAt e) {p : ℕ}
    (hp : p ∈ [0, 1, 2, 6, 7, 8, 9, 11, 12, 13, 14, 15, 274]) :
    program.HoldsAt e (program.predicate p).body :=
  hs.preds _ (RealizedProgram.predicate_mem ((inSource_A (program := program)) p hp).1) ((inSource_A (program := program)) p hp).2

/-- **A value of domain `A`** read in domain `A`'s Goldilocks extension. -/
def rdA (e : program.Env interp) (v i : ℕ) : (interp 0).K :=
  program.evalE (program.reader e) 0 (.leaf v) i

/-- The lengths and field facts of domain `A`. -/
theorem lensA : (program.value 59).size = 1024 ∧ (program.value 60).size = 1024 ∧ (program.value 61).size = 512 ∧ (program.value 62).size = 1024 ∧ (program.value 64).size = 6144 ∧ (program.value 65).size = 1024 ∧ (program.value 66).size = 1024 ∧ (program.value 67).size = 1024 ∧ program.domainField 0 = 0 :=
  MldsaEAlgebra.lensA

/-! ## domain `A`'s Goldilocks extension -/

instance charP_interp0 : CharP (interp 0).K pGold := AField.charP

/-- The constants domain `A`'s Goldilocks extension decodes are casts. -/
theorem decode_gold (c : ℕ) : (interp 0).decode c = (c : (interp 0).K) := AField.decode_eq c

/-- The characteristic of domain `A`'s Goldilocks extension as the program reads it. -/
theorem gold_char : (interp 0).spec.characteristic = pGold := AField.char_spec

/-- The integer reading of domain `A`'s Goldilocks extension reads a natural below `p` as itself. -/
theorem toNat_gold_natCast {k : ℕ} (hk : k < pGold) : (interp 0).toNat (k : (interp 0).K) = k :=
  AField.toNat_natCast k hk

/-- **A small natural's centred reading** is itself. -/
theorem centered_small {c : ℕ} (hc : 2 * c < pGold) : (interp 0).centered c = c := by
  unfold RealizedProgram.FieldInterp.centered
  rw [gold_char, if_pos hc]

/-- **`p − 1`'s centred reading** is `−1`. -/
theorem centered_pm1 : (interp 0).centered 18446744069414584320 = -1 := by
  unfold RealizedProgram.FieldInterp.centered
  rw [gold_char, if_neg (by decide)]
  norm_num [pGold]

/-- The constant `p − 1` of domain `A`'s Goldilocks extension is `−1`. -/
theorem pm1 : ((18446744069414584320 : ℕ) : (interp 0).K) = -1 := by
  rw [eq_neg_iff_add_eq_zero, show ((18446744069414584320 : ℕ) : (interp 0).K) + 1 =
    ((pGold : ℕ) : (interp 0).K) by norm_num [pGold]]
  exact CharP.cast_eq_zero _ pGold

/-- **A constant multiple in `A`**: the constant cast times the coordinate. -/
theorem evalE_scaleA (rd : program.Valuation interp) (c : ℕ) (x : RealizedProgram.Expr) (i : ℕ) :
    program.evalE rd 0 (.scale (.const c) x) i = (c : (interp 0).K) * program.evalE rd 0 x i := by
  rw [RealizedProgram.evalE_scale_const, decode_gold]

/-- **The multiple by `p − 1` in `A`** is the negation. -/
theorem evalE_negA (rd : program.Valuation interp) (x : RealizedProgram.Expr) (i : ℕ) :
    program.evalE rd 0 (.scale (.const 18446744069414584320) x) i = -program.evalE rd 0 x i := by
  rw [evalE_scaleA, pm1, neg_one_mul]

/-- **The integer reading of a value of `A` that is a small natural's cast** is the natural, for a
value that is no constant. -/
theorem intOf_of_natCast {e : program.Env interp} {v i : ℕ} (hc : program.isConstant v = false)
    (hf : program.valueField v = 0) {k : ℕ} (hk : 2 * k < pGold) (hv : rdA e v i = k) :
    program.intOf (program.reader e) v i = k := by
  have htn : (interp (program.valueField v)).toNat (program.reader e v i) = k := by
    unfold rdA at hv
    rw [RealizedProgram.evalE_leaf] at hv
    revert hv
    generalize program.reader e v i = x
    generalize program.valueField v = a at hf x
    subst hf
    rw [RealizedProgram.castElt_self]
    intro hv
    rw [hv]
    exact toNat_gold_natCast (by omega)
  unfold RealizedProgram.intOf
  unfold RealizedProgram.isConstant at hc
  split
  · rename_i es h
    rw [h] at hc
    cases hc
  · rw [htn, hf]
    exact centered_small hk
  · rw [htn]

/-! ## The type checks -/

/-- The type checks of `A` are Boolean checks of their values. -/
theorem boolChecks : (program.predicate 6).body.boolCheck? = some ⟨0, 60⟩ ∧ (program.predicate 7).body.boolCheck? = some ⟨0, 61⟩ ∧ (program.predicate 8).body.boolCheck? = some ⟨0, 64⟩ ∧ (program.predicate 9).body.boolCheck? = some ⟨0, 65⟩ :=
  MldsaEAlgebra.boolChecks

/-- **A type-checked value of `A` is a bit** where the source program holds. -/
theorem boolA {e : program.Env interp} (hs : program.SourceSatAt e) {p v : ℕ}
    (hp : p ∈ [0, 1, 2, 6, 7, 8, 9, 11, 12, 13, 14, 15, 274])
    (hc : (program.predicate p).body.boolCheck? = some ⟨0, v⟩) {i : ℕ}
    (hi : i < (program.value v).size) : rdA e v i = 0 ∨ rdA e v i = 1 := by
  have h := RealizedProgram.bool_of_boolCheck hc (holdsA hs hp) hi
  rw [(lensA (program := program)).2.2.2.2.2.2.2.2] at h
  exact h

/-- The hint is Boolean. -/
theorem hBool {e : program.Env interp} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    rdA e 60 i = 0 ∨ rdA e 60 i = 1 :=
  boolA hs (by simp) (boolChecks (program := program)).1 (by rw [(lensA (program := program)).2.1]; exact hi)

/-- The challenge bits are Boolean. -/
theorem cBool {e : program.Env interp} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 512) :
    rdA e 61 i = 0 ∨ rdA e 61 i = 1 :=
  boolA hs (by simp) (boolChecks (program := program)).2.1 (by rw [(lensA (program := program)).2.2.1]; exact hi)

/-- The UseHint output bits are Boolean. -/
theorem w1Bool {e : program.Env interp} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 6144) :
    rdA e 64 i = 0 ∨ rdA e 64 i = 1 :=
  boolA hs (by simp) (boolChecks (program := program)).2.2.1 (by rw [(lensA (program := program)).2.2.2.2.1]; exact hi)

/-- The sign advice is Boolean. -/
theorem npBool {e : program.Env interp} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    rdA e 65 i = 0 ∨ rdA e 65 i = 1 :=
  boolA hs (by simp) (boolChecks (program := program)).2.2.2 (by rw [(lensA (program := program)).2.2.2.2.2.1]; exact hi)

/-! ## The ranges -/

/-- **A range membership of one record** gives a natural below the bound. -/
theorem natBelow_of_mem {rd : program.Valuation interp} {n : ℕ} {r : RealizedProgram.Expr} {real : RealizedProgram.InRealization}
    (h : program.HoldsWith rd (.mem 0 [r] (.range n) real)) {i : ℕ} (hi : i < program.exprLen r) :
    ∃ k < n, program.evalE rd 0 r i = k := by
  have hw : ∃ k < n, program.evalE rd (program.domainField 0) r i = k :=
    h i hi r (List.mem_singleton_self r)
  have h0 := (crossData (program := program)).2.2.2.2.1
  revert hw
  generalize program.domainField 0 = D at h0 ⊢
  subst h0
  exact id

/-- The constants domain `A` reads. -/
theorem constsA : program.isConstant 63 = true ∧ program.valueField 63 = 0 ∧ program.constEntries 63 = List.replicate 1024 130993 :=
  MldsaEAlgebra.constsA

/-- **`norm.z`'s offset** reads `130993 = γ₁ − β − 1`. -/
theorem rdA_63 (e : program.Env interp) {i : ℕ} (hi : i < 1024) :
    rdA e 63 i = ((130993 : ℕ) : (interp 0).K) := by
  unfold rdA
  rw [RealizedProgram.evalE_leaf_of_isConstant e (constsA (program := program)).1, RealizedProgram.constRead_of_valueField (constsA (program := program)).2.1,
    (constsA (program := program)).2.2, List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hi, Option.getD_some,
    decode_gold]

/-- **`signature.w` bounds `w'`** below `2^24`. -/
theorem w_range {e : program.Env interp} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    ∃ k : ℕ, k < 16777216 ∧ rdA e 62 i = k := by
  have h := holdsA hs (p := 11) (by simp)
  obtain ⟨_, hb⟩ := pred11 (program := program)
  rw [hb] at h
  exact natBelow_of_mem h (by rw [RealizedProgram.exprLen_leaf, (lensA (program := program)).2.2.2.1]; exact hi)

/-- **`norm.z` bounds `z`**: `z + 130993` is a natural below `261987`. -/
theorem norm_range {e : program.Env interp} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    ∃ k : ℕ, k < 261987 ∧ rdA e 59 i + ((130993 : ℕ) : (interp 0).K) = k := by
  have h := holdsA hs (p := 12) (by simp)
  obtain ⟨_, hb⟩ := pred12 (program := program)
  rw [hb] at h
  have hlen : i < program.exprLen (.add (.leaf 59) (.leaf 63)) := by
    rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_leaf, (lensA (program := program)).1]
    exact hi
  obtain ⟨k, hk, hkv⟩ := natBelow_of_mem h hlen
  refine ⟨k, hk, ?_⟩
  rw [← rdA_63 e hi]
  exact hkv

/-- **`hint.offset` bounds the offset** below the layout's bound. -/
theorem offset_range {e : program.Env interp} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    ∃ k : ℕ, k < (MldsaEAlgebra.layout program).offsetBound ∧ rdA e 66 i = k := by
  have h := holdsA hs (p := 13) (by simp)
  obtain ⟨_, hb⟩ := pred13 (program := program)
  rw [hb] at h
  exact natBelow_of_mem h (by rw [RealizedProgram.exprLen_leaf, (lensA (program := program)).2.2.2.2.2.2.1]; exact hi)

/-- **`hint.slack` bounds the slack** below the layout's bound. -/
theorem slack_range {e : program.Env interp} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    ∃ k : ℕ, k < (MldsaEAlgebra.layout program).offsetBound ∧ rdA e 67 i = k := by
  have h := holdsA hs (p := 14) (by simp)
  obtain ⟨_, hb⟩ := pred14 (program := program)
  rw [hb] at h
  exact natBelow_of_mem h (by rw [RealizedProgram.exprLen_leaf, (lensA (program := program)).2.2.2.2.2.2.2.1]; exact hi)

/-- **`hint_weight.weight` bounds the hint's sum** below `81`. -/
theorem weight_range {e : program.Env interp} (hs : program.SourceSatAt e) :
    ∃ k : ℕ, k < 81 ∧ ∑ t : Fin 1024, rdA e 60 t = k := by
  have h := holdsA hs (p := 15) (by simp)
  obtain ⟨_, hb⟩ := pred15 (program := program)
  rw [hb] at h
  obtain ⟨k, hk, hkv⟩ := natBelow_of_mem h (i := 0) MldsaEAlgebra.lenWeight
  refine ⟨k, hk, ?_⟩
  rw [RealizedProgram.evalE_apply_sum] at hkv
  simp only [Nat.zero_mul, Nat.zero_add] at hkv
  exact hkv

/-! ## Constants -/

/-- The constants UseHint reads. -/
theorem constsU : program.isConstant 0 = true ∧ program.constEntries 0 = [1, 1, 0, 1, 0, 1] ∧ program.isConstant 1 = true ∧ program.constEntries 1 = List.replicate 1024 1 ∧ program.isConstant 2 = true ∧ program.constEntries 2 = [0, 0, 0, 0, 0, 0] ∧ program.isConstant 3 = true ∧ program.constEntries 3 = [1] ∧ program.isConstant 4 = true ∧ program.constEntries 4 = [18446744069406203904] ∧ program.isConstant 5 = true ∧ program.constEntries 5 = List.replicate 1024 0 ∧ program.isConstant 6 = true ∧ program.constEntries 6 = [95231] ∧ program.valueField 0 = 0 ∧ program.valueField 1 = 0 ∧ program.valueField 2 = 0 ∧ program.valueField 3 = 0 ∧ program.valueField 4 = 0 ∧ program.valueField 5 = 0 ∧ program.valueField 6 = 0 :=
  MldsaEAlgebra.constsU

/-- **A constant of `A`** reads its entry, cast. -/
theorem rdA_const (e : program.Env interp) {v : ℕ} (hc : program.isConstant v = true)
    (hf : program.valueField v = 0) (i : ℕ) :
    rdA e v i = (((program.constEntries v).getD i 0 : ℕ) : (interp 0).K) := by
  unfold rdA
  rw [RealizedProgram.evalE_leaf_of_isConstant e hc, RealizedProgram.constRead_of_valueField hf, decode_gold]

/-- The constant `M − 1 = 43` (value `0`) reads its bits. -/
theorem rdA_0 (e : program.Env interp) {t : ℕ} (ht : t < 6) : rdA e 0 t = Bits.constBit 43 t := by
  rw [rdA_const e (constsU (program := program)).1 (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, (constsU (program := program)).2.1]
  interval_cases t <;> simp [Bits.constBit]

/-- The constant `1` (value `1`) reads `1`. -/
theorem rdA_1 (e : program.Env interp) {i : ℕ} (hi : i < 1024) : rdA e 1 i = 1 := by
  rw [rdA_const e (constsU (program := program)).2.2.1 (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, (constsU (program := program)).2.2.2.1,
    List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hi, Option.getD_some, Nat.cast_one]

/-- The constant `0` (value `2`) reads the bits of `0`. -/
theorem rdA_2 (e : program.Env interp) {t : ℕ} (ht : t < 6) : rdA e 2 t = Bits.constBit 0 t := by
  rw [rdA_const e (constsU (program := program)).2.2.2.2.1 (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, (constsU (program := program)).2.2.2.2.2.1]
  interval_cases t <;> simp [Bits.constBit]

/-- The constant `1` (value `3`) reads `1`. -/
theorem rdA_3 (e : program.Env interp) : rdA e 3 0 = 1 := by
  rw [rdA_const e (constsU (program := program)).2.2.2.2.2.2.1 (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    (constsU (program := program)).2.2.2.2.2.2.2.1]
  simp

/-- The constant `−q` (value `4`) reads `−q`. -/
theorem rdA_4 (e : program.Env interp) : rdA e 4 0 = -((_root_.MLDSA.modulus : ℕ) : (interp 0).K) := by
  rw [rdA_const e (constsU (program := program)).2.2.2.2.2.2.2.2.1 (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    (constsU (program := program)).2.2.2.2.2.2.2.2.2.1, eq_neg_iff_add_eq_zero]
  simp only [List.getD_cons_zero]
  rw [show ((18446744069406203904 : ℕ) : (interp 0).K) + ((_root_.MLDSA.modulus : ℕ) : (interp 0).K) =
    ((pGold : ℕ) : (interp 0).K) by rw [← Nat.cast_add]; rfl]
  exact CharP.cast_eq_zero _ pGold

/-- The zero constant (value `5`) reads `0`. -/
theorem rdA_5 (e : program.Env interp) (i : ℕ) : rdA e 5 i = 0 := by
  rw [rdA_const e (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.1 (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.1]
  have h0 : (List.replicate 1024 (0 : ℕ)).getD i 0 = 0 := by
    rw [List.getD_eq_getElem?_getD]
    rcases lt_or_ge i 1024 with h | h
    · rw [List.getElem?_replicate, if_pos h, Option.getD_some]
    · rw [List.getElem?_eq_none (by rw [List.length_replicate]; exact h), Option.getD_none]
  rw [h0, Nat.cast_zero]

/-! The index maps of UseHint. -/

theorem idx6_eq : idx6 = List.replicate 1024 (0, 1, 6) := by decide +kernel
theorem idx6_entry {m t : ℕ} (hm : m < 1024) (ht : t < 6) : idx6.entry (m * 6 + t) = t := by
  rw [idx6_eq, RealizedProgram.IndexMap.entry_replicate (by omega)]
  omega
theorem idx7_eq : idx7 = [(0, 0, 1024)] := by decide +kernel
theorem idx7_entry {m : ℕ} (hm : m < 1024) : idx7.entry m = 0 := by
  rw [idx7_eq, RealizedProgram.IndexMap.entry_step_zero hm]
theorem refsA : 5 < program.exprs.length :=
  MldsaEAlgebra.refsA

/-! ## UseHint -/

/-- **The UseHint output bits of coefficient `m`** (`hint.w1`, bits `6 m, …, 6 m + 5`). -/
def bitsA (e : program.Env interp) (m : ℕ) : BitWires (interp 0).K 6 :=
  fun b => rdA e 64 (6 * m + b)

/-- The output bits are bits. -/
theorem bitsA_bool {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    AllBool (bitsA e m) := fun b => w1Bool hs (by have := b.isLt; omega)

/-- **`down = h · s`** (the shared expression `0`). -/
theorem evalE_ref0 (e : program.Env interp) (m : ℕ) :
    program.evalE (program.reader e) 0 (.ref 0) m = rdA e 60 m * rdA e 65 m := by
  rw [RealizedProgram.evalE_ref (refsOrdered (program := program)) _ _ (by have := (refsA (program := program)); omega), (expr0 (program := program))]
  rfl

/-- **The word of the output bits against a constant's bits**: `Logic::eq` reads the output's
bits and the constant's. -/
theorem evalE_eqWord (e : program.Env interp) {m : ℕ} (hm : m < 1024) (hs : program.SourceSatAt e)
    {v c : ℕ} (hc : c < 64) (hv : ∀ t < 6, rdA e v t = Bits.constBit c t) :
    program.evalE (program.reader e) 0 (.logic .eq 6 [.leaf 64, .reindex idx6 (.leaf v)]) m =
      Bits.eqConst (bitsA e m) c := by
  rw [RealizedProgram.evalE_logic]
  simp only [RealizedProgram.LogicOp.eval, List.headD_cons, List.getD_cons_succ, List.getD_cons_zero,
    RealizedProgram.evalE_reindex]
  rw [RealizedProgram.Ops.eqWord, RealizedProgram.Ops.eqReduce_congr 6 0 (a' := fun t => rdA e 64 (6 * m + t))
    (b' := fun t => Bits.constBit c t)
    (fun t _ => by rw [Nat.mul_comm]; rfl)
    (fun t ht => by simp only [Nat.zero_add]; rw [idx6_entry hm ht]; exact hv t ht), ← RealizedProgram.Ops.eqWord]
  exact RealizedProgram.Ops.eqWord_eq_eqConst (fun t ht => w1Bool hs (by omega)) hc

/-- **`[y = 0]`** (the shared expression `2`). -/
theorem evalE_ref2 {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    program.evalE (program.reader e) 0 (.ref 2) m = Bits.eqConst (bitsA e m) 0 := by
  rw [RealizedProgram.evalE_ref (refsOrdered (program := program)) _ _ (by have := (refsA (program := program)); omega), (expr2 (program := program))]
  exact evalE_eqWord e hm hs (by decide) fun t ht => rdA_2 e ht

/-- **`h s [y = M − 1]`** (the shared expression `3`). -/
theorem evalE_ref3 {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    program.evalE (program.reader e) 0 (.ref 3) m =
      rdA e 60 m * rdA e 65 m * Bits.eqConst (bitsA e m) 43 := by
  rw [RealizedProgram.evalE_ref (refsOrdered (program := program)) _ _ (by have := (refsA (program := program)); omega), (expr3 (program := program)), RealizedProgram.evalE_mul,
    evalE_ref0, evalE_eqWord e hm hs (by decide) fun t ht => rdA_0 e ht]

/-- **The endpoint** (the shared expression `4`): `(s − h s) [y = 0] + h s [y = M − 1]`. -/
theorem evalE_ref4 {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    program.evalE (program.reader e) 0 (.ref 4) m =
      UseHint.endpoint (rdA e 60 m) (rdA e 65 m)
        (UseHint.outputFromBits (UseHint.hiCount mldsa44.γ₂) (bitsA e m)) := by
  rw [RealizedProgram.evalE_ref (refsOrdered (program := program)) _ _ (by have := (refsA (program := program)); omega), (expr4 (program := program))]
  rw [RealizedProgram.evalE_add, RealizedProgram.evalE_mul, RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const,
    evalE_ref0, evalE_ref2 hs hm, evalE_ref3 hs hm, decode_gold, pm1]
  have hM : UseHint.hiCount mldsa44.γ₂ - 1 = 43 := by decide
  simp only [UseHint.endpoint, UseHint.outputFromBits, hM]
  unfold rdA
  ring

/-- **`up = h − h s`** (the shared expression `1`). -/
theorem evalE_ref1 (e : program.Env interp) (m : ℕ) :
    program.evalE (program.reader e) 0 (.ref 1) m = rdA e 60 m - rdA e 60 m * rdA e 65 m := by
  rw [RealizedProgram.evalE_ref (refsOrdered (program := program)) _ _ (by have := (refsA (program := program)); omega), (expr1 (program := program)), RealizedProgram.evalE_add,
    RealizedProgram.evalE_scale_const, evalE_ref0, decode_gold, pm1]
  unfold rdA
  ring

/-- The lengths of UseHint's predicates. -/
theorem lensU : program.exprLen (.logic .leq 6 [.leaf 64, .reindex idx6 (.leaf 0)]) = 1024 ∧ program.exprLen (.mul (.ref 5) (.add (.ref 5) (.reindex idx7 (.leaf 4)))) = 1024 ∧ program.exprLen (.add (.leaf 66) (.leaf 67)) = 1024 :=
  MldsaEAlgebra.lensU

/-- **`hint.w1_bound`**: the output is at most `M − 1 = 43`. -/
theorem w1Bound {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    Bits.leConst (bitsA e m) (UseHint.hiCount mldsa44.γ₂ - 1) = 1 := by
  have h := holdsA hs (p := 0) (by simp)
  rw [(pred0 (program := program))] at h
  have hm' := h m (by rw [(lensU (program := program)).1]; exact hm)
  change program.evalE (program.reader e) (program.domainField 0) _ m =
    program.evalE (program.reader e) (program.domainField 0) _ m at hm'
  rw [(lensA (program := program)).2.2.2.2.2.2.2.2, RealizedProgram.evalE_logic] at hm'
  change _ = rdA e 1 m at hm'
  rw [rdA_1 e hm] at hm'
  simp only [RealizedProgram.LogicOp.eval, List.headD_cons, List.getD_cons_succ, List.getD_cons_zero,
    RealizedProgram.evalE_reindex] at hm'
  rw [RealizedProgram.Ops.leqWord, RealizedProgram.Ops.ltWord, RealizedProgram.Ops.ltReduce_congr 6 0 (a' := fun t => Bits.constBit 43 t)
    (b' := fun t => rdA e 64 (6 * m + t))
    (fun t ht => by simp only [Nat.zero_add]; rw [idx6_entry hm ht]; exact rdA_0 e ht)
    (fun t _ => by rw [Nat.mul_comm]; rfl), ← RealizedProgram.Ops.ltWord, ← RealizedProgram.Ops.leqWord,
    RealizedProgram.Ops.leqWord_eq_leConst (fun t ht => w1Bool hs (by omega)) (by decide)] at hm'
  have hM : UseHint.hiCount mldsa44.γ₂ - 1 = 43 := by decide
  rw [hM]
  exact hm'

/-- **The UseHint output** (the batched `fromDigits 6 2` of `hint.w1`) is the sum of its bits'
powers of two. -/
theorem evalE_outputValue (e : program.Env interp) (m : ℕ) :
    program.evalE (program.reader e) 0 (.apply (.batched 1024 (.fromDigits 6 2)) (.leaf 64)) m =
      ∑ b : Fin 6, (2 : (interp 0).K) ^ (b : ℕ) * bitsA e m b := by
  rw [RealizedProgram.evalE_apply_batched_fromDigits (hb := by norm_num)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [decode_gold, Nat.cast_ofNat, Nat.mul_comm]
  rfl

/-- **The decomposition's residual** (the shared expression `5`): `w' − (2 γ₂ raw_high + lower +
offset)`. -/
theorem evalE_ref5 {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    program.evalE (program.reader e) 0 (.ref 5) m = rdA e 62 m -
      UseHint.relationResult mldsa44.γ₂ (UseHint.hiCount mldsa44.γ₂) (rdA e 60 m) (rdA e 65 m)
        (rdA e 66 m) (UseHint.outputFromBits (UseHint.hiCount mldsa44.γ₂) (bitsA e m)) := by
  rw [RealizedProgram.evalE_ref (refsOrdered (program := program)) _ _ (refsA (program := program)), (expr5 (program := program))]
  simp only [RealizedProgram.evalE_add, ↓evalE_negA, evalE_scaleA, RealizedProgram.evalE_mul,
    RealizedProgram.evalE_reindex, evalE_outputValue, evalE_ref0, evalE_ref1, evalE_ref2 hs hm,
    evalE_ref3 hs hm, evalE_ref4 hs hm, idx7_entry hm]
  have hM' : UseHint.hiCount 95232 = 44 := by decide
  have hγ : mldsa44.γ₂ = 95232 := rfl
  have h3 : rdA e 3 0 = 1 := rdA_3 e
  simp only [UseHint.relationResult, UseHint.rawHigh, UseHint.lower, UseHint.outputFromBits,
    UseHint.endpoint, hM', hγ, Nat.cast_ofNat]
  unfold rdA at h3 ⊢
  rw [h3]
  push_cast
  ring

/-- **`hint.decompose`**: the residual is `0` or `q`, `e (e − q) = 0`. -/
theorem decompose {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    (rdA e 62 m - UseHint.relationResult mldsa44.γ₂ (UseHint.hiCount mldsa44.γ₂) (rdA e 60 m)
        (rdA e 65 m) (rdA e 66 m) (UseHint.outputFromBits (UseHint.hiCount mldsa44.γ₂) (bitsA e m))) *
      (rdA e 62 m - UseHint.relationResult mldsa44.γ₂ (UseHint.hiCount mldsa44.γ₂) (rdA e 60 m)
        (rdA e 65 m) (rdA e 66 m) (UseHint.outputFromBits (UseHint.hiCount mldsa44.γ₂) (bitsA e m)) -
        ((_root_.MLDSA.modulus : ℕ) : (interp 0).K)) = 0 := by
  have h := holdsA hs (p := 1) (by simp)
  rw [(pred1 (program := program))] at h
  have hm' := h m (by rw [(lensU (program := program)).2.1]; exact hm)
  change program.evalE (program.reader e) (program.domainField 0) _ m =
    program.evalE (program.reader e) (program.domainField 0) _ m at hm'
  rw [(lensA (program := program)).2.2.2.2.2.2.2.2] at hm'
  simp only [RealizedProgram.evalE_mul, RealizedProgram.evalE_add, RealizedProgram.evalE_reindex, idx7_entry hm,
    evalE_ref5 hs hm] at hm'
  change _ = rdA e 5 m at hm'
  have h4 : rdA e 4 0 = _ := rdA_4 e
  unfold rdA at h4 hm' ⊢
  rw [h4] at hm'
  rw [show program.evalE (program.reader e) 0 (.leaf 5) m = 0 from rdA_5 e m] at hm'
  rw [← hm']
  ring

/-! ### The interval row, on the integers -/

/-- **An integer `mod_q` with `q = 0`** is an integer equality at every coordinate. -/
theorem eq_of_modZero {rd : program.Valuation interp} {d : ℕ} {l r : RealizedProgram.Expr} {real : RealizedProgram.ModRealization}
    (h : program.HoldsWith rd (.mod d 0 l r real)) {i : ℕ} (hi : i < program.exprLen l) :
    program.evalIntWith rd d l i = program.evalIntWith rd d r i := by
  have := h i hi
  rwa [Nat.cast_zero, zero_dvd_iff, sub_eq_zero] at this

/-- The values UseHint reads are not constants, of field `0`. -/
theorem valsU : program.isConstant 60 = false ∧ program.isConstant 64 = false ∧ program.isConstant 65 = false ∧ program.isConstant 66 = false ∧ program.isConstant 67 = false ∧ program.valueField 60 = 0 ∧ program.valueField 64 = 0 ∧ program.valueField 65 = 0 ∧ program.valueField 66 = 0 ∧ program.valueField 67 = 0 :=
  MldsaEAlgebra.valsU

/-- **A constant's integer reading** where its entry is small. -/
theorem intOf_constA (rd : program.Valuation interp) {v : ℕ} (hc : program.isConstant v = true)
    (hf : program.valueField v = 0) {i : ℕ} (hs : 2 * (program.constEntries v).getD i 0 < pGold) :
    program.intOf rd v i = ((program.constEntries v).getD i 0 : ℕ) := by
  rw [RealizedProgram.intOf_of_constant rd (RealizedProgram.kind_of_isConstant hc), hf, centered_small hs]

/-- **A bit's integer reading casts to it.** -/
theorem cast_intOf_bool {e : program.Env interp} {v i : ℕ} (hc : program.isConstant v = false)
    (hf : program.valueField v = 0) (hb : rdA e v i = 0 ∨ rdA e v i = 1) :
    ((program.intOf (program.reader e) v i : ℤ) : (interp 0).K) = rdA e v i := by
  rcases hb with h | h
  · rw [intOf_of_natCast hc hf (k := 0) (by decide) (by rw [h]; simp), h]
    simp
  · rw [intOf_of_natCast hc hf (k := 1) (by decide) (by rw [h]; simp), h]
    simp

/-- **`down`'s integer reading casts to `h s`.** -/
theorem cast_evalIntWith_ref0 {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ}
    (hm : m < 1024) :
    ((program.evalIntWith (program.reader e) 0 (.ref 0) m : ℤ) : (interp 0).K) =
      rdA e 60 m * rdA e 65 m := by
  rw [RealizedProgram.evalIntWith_ref (refsOrdered (program := program)) _ _ (by have := (refsA (program := program)); omega), (expr0 (program := program)),
    RealizedProgram.evalIntWith_mul, RealizedProgram.evalIntWith_leaf, RealizedProgram.evalIntWith_leaf, Int.cast_mul,
    cast_intOf_bool (valsU (program := program)).1 (valsU (program := program)).2.2.2.2.2.1 (hBool hs hm),
    cast_intOf_bool (valsU (program := program)).2.2.1 (valsU (program := program)).2.2.2.2.2.2.2.1 (npBool hs hm)]

/-- **The output bits against a constant's bits, on the integers**, cast. -/
theorem cast_evalIntWith_eqWord {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ}
    (hm : m < 1024) {v c : ℕ} (hc : c < 64) (hvc : program.isConstant v = true)
    (hvf : program.valueField v = 0)
    (hv : ∀ t < 6, 2 * (program.constEntries v).getD t 0 < pGold ∧
      (((program.constEntries v).getD t 0 : ℕ) : (interp 0).K) = Bits.constBit c t) :
    ((program.evalIntWith (program.reader e) 0
        (.logic .eq 6 [.leaf 64, .reindex idx6 (.leaf v)]) m : ℤ) : (interp 0).K) =
      Bits.eqConst (bitsA e m) c := by
  rw [RealizedProgram.evalIntWith_logic]
  simp only [RealizedProgram.LogicOp.eval, List.headD_cons, List.getD_cons_succ, List.getD_cons_zero,
    RealizedProgram.evalIntWith_reindex, RealizedProgram.evalIntWith_leaf]
  rw [RealizedProgram.Ops.eqWord, ← eq_intCast (Int.castRingHom (interp 0).K), RealizedProgram.Ops.eqReduce_map,
    RealizedProgram.Ops.eqReduce_congr 6 0 (a' := fun t => rdA e 64 (6 * m + t))
    (b' := fun t => Bits.constBit c t)
    (fun t ht => by
      simp only [Nat.zero_add, eq_intCast]
      rw [Nat.mul_comm]
      exact cast_intOf_bool (valsU (program := program)).2.1 (valsU (program := program)).2.2.2.2.2.2.1 (w1Bool hs (by omega)))
    (fun t ht => by
      simp only [Nat.zero_add, eq_intCast]
      rw [idx6_entry hm ht, intOf_constA _ hvc hvf (hv t ht).1, Int.cast_natCast]
      exact (hv t ht).2), ← RealizedProgram.Ops.eqWord]
  exact RealizedProgram.Ops.eqWord_eq_eqConst (fun t ht => w1Bool hs (by omega)) hc

/-- **The endpoint's integer reading casts to the endpoint.** -/
theorem cast_evalIntWith_ref4 {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ}
    (hm : m < 1024) :
    ((program.evalIntWith (program.reader e) 0 (.ref 4) m : ℤ) : (interp 0).K) =
      UseHint.endpoint (rdA e 60 m) (rdA e 65 m)
        (UseHint.outputFromBits (UseHint.hiCount mldsa44.γ₂) (bitsA e m)) := by
  have h2 : ∀ t < 6, 2 * (program.constEntries 2).getD t 0 < pGold ∧
      (((program.constEntries 2).getD t 0 : ℕ) : (interp 0).K) = Bits.constBit 0 t := fun t ht => by
    rw [(constsU (program := program)).2.2.2.2.2.1]
    interval_cases t <;> simp [Bits.constBit, pGold]
  have h0 : ∀ t < 6, 2 * (program.constEntries 0).getD t 0 < pGold ∧
      (((program.constEntries 0).getD t 0 : ℕ) : (interp 0).K) = Bits.constBit 43 t := fun t ht => by
    rw [(constsU (program := program)).2.1]
    interval_cases t <;> simp [Bits.constBit, pGold]
  rw [RealizedProgram.evalIntWith_ref (k := 4) (refsOrdered (program := program)) _ _ (by have := (refsA (program := program)); omega), (expr4 (program := program)),
    RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_mul, RealizedProgram.evalIntWith_add,
    RealizedProgram.evalIntWith_scale_const, RealizedProgram.evalIntWith_leaf, (lensA (program := program)).2.2.2.2.2.2.2.2, centered_pm1,
    RealizedProgram.evalIntWith_ref (k := 2) (refsOrdered (program := program)) _ _ (by have := (refsA (program := program)); omega), (expr2 (program := program)),
    RealizedProgram.evalIntWith_ref (k := 3) (refsOrdered (program := program)) _ _ (by have := (refsA (program := program)); omega), (expr3 (program := program)),
    RealizedProgram.evalIntWith_mul]
  push_cast
  rw [cast_evalIntWith_ref0 hs hm,
    cast_evalIntWith_eqWord hs hm (by decide) (constsU (program := program)).2.2.2.2.1
      (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h2,
    cast_evalIntWith_eqWord hs hm (by decide) (constsU (program := program)).1 (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h0,
    cast_intOf_bool (valsU (program := program)).2.2.1 (valsU (program := program)).2.2.2.2.2.2.2.1 (npBool hs hm)]
  have hM : UseHint.hiCount mldsa44.γ₂ - 1 = 43 := by decide
  simp only [UseHint.endpoint, UseHint.outputFromBits, hM]
  ring

/-- **`hint.interval`**: `offset + slack = (γ₂ − 1) + endpoint`, the integer equation cast to the
field. -/
theorem interval {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    UseHint.IntervalEq mldsa44.γ₂ (rdA e 60 m) (rdA e 65 m) (rdA e 66 m) (rdA e 67 m)
      (UseHint.outputFromBits (UseHint.hiCount mldsa44.γ₂) (bitsA e m)) := by
  have h := holdsA hs (p := 2) (by simp)
  rw [(pred2 (program := program))] at h
  have hm' := congrArg (Int.cast : ℤ → (interp 0).K) (eq_of_modZero h (i := m) (by
    rw [(lensU (program := program)).2.2]
    exact hm))
  obtain ⟨ko, hko, hov⟩ := offset_range hs hm
  obtain ⟨ks, hks, hsv⟩ := slack_range hs hm
  rw [RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_leaf,
    RealizedProgram.evalIntWith_leaf, RealizedProgram.evalIntWith_reindex, RealizedProgram.evalIntWith_leaf, idx7_entry hm,
    intOf_constA _ (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.1 (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      (by rw [(constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.1]; decide),
    intOf_of_natCast (valsU (program := program)).2.2.2.1 (valsU (program := program)).2.2.2.2.2.2.2.2.1 (two_mul_lt_of_offset hko) hov,
    intOf_of_natCast (valsU (program := program)).2.2.2.2.1 (valsU (program := program)).2.2.2.2.2.2.2.2.2 (two_mul_lt_of_offset hks) hsv] at hm'
  push_cast at hm'
  rw [cast_evalIntWith_ref4 hs hm, (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.1] at hm'
  unfold UseHint.IntervalEq
  rw [hov, hsv, hm']
  have hγ : mldsa44.γ₂ = 95232 := rfl
  simp only [hγ, List.getD_cons_zero]
  push_cast
  ring

/-! ### UseHint at every coefficient -/

/-- **UseHint with the wrap at coefficient `m`** (`UseHint.WrapHolds`). -/
theorem wrapHolds {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    UseHint.WrapHolds mldsa44.γ₂ (rdA e 60 m) (rdA e 62 m) (rdA e 65 m) (rdA e 66 m) (rdA e 67 m)
      (bitsA e m) :=
  ⟨w1Bound hs hm, interval hs hm, decompose hs hm⟩

/-- **UseHint at coefficient `m`**: the output is `UseHint(h, w')` for every natural below `2^24`
`w'` is the cast of (`UseHint.wrap_sound`). -/
theorem emulatedHolds {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    UseHint.EmulatedHolds mldsa44.γ₂ 16777216 (rdA e 60 m) (rdA e 62 m) (natOfBits (bitsA e m)) := by
  obtain ⟨ko, hko, hov⟩ := offset_range hs hm
  obtain ⟨ks, hks, hsv⟩ := slack_range hs hm
  exact UseHint.wrap_sound (p := pGold) (B := (MldsaEAlgebra.layout program).offsetBound)
    (by decide) (by decide) MldsaEAlgebra.offsetBound_lt (by decide) (by rw [pGold]; decide) (wrapHolds hs hm) (hBool hs hm)
    (npBool hs hm) (bitsA_bool hs hm) ⟨ko, hko, hov.symm⟩ ⟨ks, hks, hsv.symm⟩

/-! ### The readings of the frontend -/

/-- The flat index of row `i`, coefficient `k`. -/
theorem flat_lt (i : Fin 4) (k : Fin 256) : (i : ℕ) * 256 + k < 1024 := by omega

/-- **The integer reading of a small integer's cast in domain `A`'s Goldilocks extension** is the integer. -/
theorem coefInt_gold {z : ℤ} (hz : 2 * |z| < pGold) : (interp 0).coefInt (z : (interp 0).K) = z :=
  RealizedProgram.FieldInterp.coefInt_intCast gold_char charP_interp0 (fun _ hk => toNat_gold_natCast hk) hz

/-- **A's `w1` coefficients are the output bits' naturals.** -/
theorem w1Coeff_eq (e : program.Env interp) (i : Fin Native.Rows.nRows)
    (k : Fin Native.Rows.deg) :
    NativeAlgebraCircuit.w1Coeff (w1ABits (program.reader e)) i k = natOfBits (bitsA e ((i : ℕ) * 256 + k)) := by
  unfold NativeAlgebraCircuit.w1Coeff NativeAlgebraCircuit.outputBits
  refine congrArg natOfBits (funext fun b => ?_)
  have hidx : mldsa44.r1_bits * (finProdFinEquiv (i, k) : ℕ) + (b : ℕ) =
      6 * ((i : ℕ) * 256 + k) + b := by
    rw [finProdFinEquiv_apply_val]
    change 6 * ((k : ℕ) + 256 * i) + b = _
    ring
  change program.evalE (program.reader e) 0 (.leaf 64)
    (mldsa44.r1_bits * (finProdFinEquiv (i, k) : ℕ) + b) = rdA e 64 (6 * ((i : ℕ) * 256 + k) + b)
  rw [hidx]
  rfl

/-- **`w'` is a natural below `2^24`**, and the extracted coefficient is its cast. -/
theorem w_nat {e : program.Env interp} (hs : program.SourceSatAt e) (i : Fin _root_.MLDSA.mldsa44.k)
    (k : Fin _root_.MLDSA.ringDegree) : ∃ n : ℕ, n < 16777216 ∧
      rdA e 62 ((i : ℕ) * 256 + k) = n ∧ MLDSA44.coeff ((wOf (program.reader e)).get i) k = n := by
  obtain ⟨n, hn, hv⟩ := w_range hs (flat_lt i k)
  refine ⟨n, hn, hv, ?_⟩
  unfold wOf
  erw [Vector.get_ofFn, MLDSA44.coeff_ofCoeff]
  change (((interp 0).coefInt (rdA e 62 ((i : ℕ) * 256 + k)) : ℤ) : _root_.MLDSA.Coeff) = _
  rw [hv, show ((n : ℕ) : (interp 0).K) = ((n : ℤ) : (interp 0).K) from (Int.cast_natCast n).symm,
    coefInt_gold (by rw [abs_of_nonneg (by positivity)]; norm_num [pGold]; omega), Int.cast_natCast]

/-- **`w1 = UseHint(h, w')`** coefficientwise. -/
theorem useHint_eq {e : program.Env interp} (hs : program.SourceSatAt e)
    (i : Fin Native.Rows.nRows) (k : Fin Native.Rows.deg) :
    NativeAlgebraCircuit.w1Coeff (w1ABits (program.reader e)) i k =
      _root_.MLDSA.Concrete.useHintCoeff (NativeAlgebraCircuit.decodeHint (hVals (program.reader e)) i k)
        (MLDSA44.coeff ((wOf (program.reader e)).get i) k) mldsa44.γ₂ := by
  obtain ⟨n, hn, hv, hc⟩ := w_nat hs i k
  have h := (emulatedHolds hs (flat_lt i k)).useHint n hn hv.symm
  rw [w1Coeff_eq, hc, ← h]
  rfl

/-- **`z` is a small integer** whose cast is `z`'s element: `norm.z` puts `z + 130993` below
`261987`. -/
theorem z_int {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    ∃ n : ℤ, n.natAbs < mldsa44.normBound ∧ (n : (interp 0).K) = rdA e 59 m := by
  obtain ⟨k, hk, hkv⟩ := norm_range hs hm
  refine ⟨(k : ℤ) - 130993, ?_, ?_⟩
  · change ((k : ℤ) - 130993).natAbs < 130994
    omega
  · push_cast
    rw [← hkv]
    push_cast
    ring

/-- **The extracted `z`'s coefficient** is the small integer of `z_int`. -/
theorem coeff_zOf {e : program.Env interp} {j : Fin _root_.MLDSA.mldsa44.l}
    {k : Fin _root_.MLDSA.ringDegree} {n : ℤ} (hn : n.natAbs < mldsa44.normBound)
    (hv : (n : (interp 0).K) = rdA e 59 ((j : ℕ) * 256 + k)) :
    MLDSA44.coeff ((zOf (program.reader e)).get j) k = (n : _root_.MLDSA.Coeff) := by
  unfold zOf
  erw [Vector.get_ofFn, MLDSA44.coeff_ofCoeff]
  change (((interp 0).coefInt (rdA e 59 ((j : ℕ) * 256 + k)) : ℤ) : _root_.MLDSA.Coeff) = _
  have hb : n.natAbs < 130994 := hn
  have ha : |n| < 130994 := by rw [Int.abs_eq_natAbs]; exact_mod_cast hb
  rw [← hv, coefInt_gold (by norm_num [pGold]; omega)]

/-- **`‖z‖∞ < γ₁ − β`.** -/
theorem norm_lt {e : program.Env interp} (hs : program.SourceSatAt e) (j : Fin _root_.MLDSA.mldsa44.l)
    (k : Fin _root_.MLDSA.ringDegree) :
    (LatticeCrypto.centeredRepr (MLDSA44.coeff ((zOf (program.reader e)).get j) k)).natAbs <
      mldsa44.normBound := by
  obtain ⟨n, hlt, hn⟩ := z_int hs (flat_lt j k)
  rw [coeff_zOf hlt hn, LatticeCrypto.centeredRepr_intCast_eq_of_natAbs_le n hlt.le (by decide)]
  exact hlt

/-- **The hint weight is at most `ω`** (`hint_weight.weight`: the hint's sum below `81`). -/
theorem hintWeight_le {e : program.Env interp} (hs : program.SourceSatAt e) :
    (Finset.univ.filter fun ik : Fin Native.Rows.nRows × Fin Native.Rows.deg =>
      NativeAlgebraCircuit.decodeHint (hVals (program.reader e)) ik.1 ik.2 = true).card ≤ mldsa44.ω := by
  obtain ⟨k, hk, hkv⟩ := weight_range hs
  have hbool : ∀ t : Fin 1024, rdA e 60 t = 0 ∨ rdA e 60 t = 1 := fun t => hBool hs t.isLt
  rw [HintWeight.sum_eq_card hbool] at hkv
  set c := (Finset.univ.filter fun t : Fin 1024 => rdA e 60 t = 1).card
  have hc : c ≤ 1024 := (Finset.card_filter_le _ _).trans (by simp)
  have heq : c = k := IntLift.natCast_inj_of_lt (K := (interp 0).K) (p := pGold)
    (by rw [pGold]; omega) (by rw [pGold]; omega) hkv
  have hcle : c ≤ mldsa44.ω := by
    change c ≤ 80
    omega
  let eqv : Fin Native.Rows.nRows × Fin Native.Rows.deg ≃ Fin 1024 := finProdFinEquiv
  refine le_of_eq_of_le (Finset.card_equiv eqv fun ik => ?_) hcle
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, NativeAlgebraCircuit.decodeHint, decide_eq_true_eq]
  change rdA e 60 ((ik.1 : ℕ) * 256 + ik.2) = 1 ↔ rdA e 60 (finProdFinEquiv ik : ℕ) = 1
  rw [finProdFinEquiv_apply_val]
  change rdA e 60 ((ik.1 : ℕ) * 256 + ik.2) = 1 ↔ rdA e 60 ((ik.2 : ℕ) + 256 * ik.1) = 1
  rw [show (ik.1 : ℕ) * 256 + ik.2 = ik.2 + 256 * ik.1 by ring]

/-! ## The signature relation

`signature.relation` (predicate `274`) is `mod_q(w' + 8192 B(t1)(support) − 16384 B(t1)(sign),
M(A)(z))` with `B` the `polyBroadcast` of `key.t1` and `M` the `polyMatVec` of `key.a`
(`NamedOp.applyInt_polyBroadcast`, `NamedOp.applyInt_polyMatVec`): the source semantics states that
`q` divides the integer difference of the sides' integer readings at every coefficient. With the
statement's entries the key's (`KeyOf`, casts of naturals below `q`), the integer readings are the
negacyclic products over the integers, so modulo `q` they are `Emulated.sigInt` and the
congruence `Rows.Congruent` holds. -/

/-- The sizes, fields and kinds the signature relation reads. -/
theorem sigData : (program.value 57).size = 4096 ∧ (program.value 58).size = 1024 ∧ program.valueField 57 = 0 ∧ program.valueField 58 = 0 ∧ program.isConstant 59 = false ∧ program.isConstant 61 = false ∧ program.isConstant 62 = false ∧ program.valueField 59 = 0 ∧ program.valueField 61 = 0 ∧ program.valueField 62 = 0 ∧ 8 < program.exprs.length ∧ RealizedProgram.isOpaqueNil (program.value 57).kind = true ∧ RealizedProgram.isOpaqueNil (program.value 58).kind = true :=
  MldsaEAlgebra.sigData

theorem idx11_entry {k : ℕ} (hk : k < 256) : idx11.entry k = 2 * k := by
  have h : idx11 = [(0, 2, 256)] := by decide +kernel
  rw [h]
  simp [RealizedProgram.IndexMap.entry, hk]
  omega

theorem idx12_entry {k : ℕ} (hk : k < 256) : idx12.entry k = 2 * k + 1 := by
  have h : idx12 = [(1, 2, 256)] := by decide +kernel
  rw [h]
  simp only [RealizedProgram.IndexMap.entry, hk, if_true]
  omega

/-- **A sum against a negacyclic coefficient row, modulo `q`**, is the negacyclic product's
coefficient of the casts (`Ops.negacyclic_eq_sum_negCoef`). -/
theorem cast_sum_negCoef {n : ℕ} (h x : ℕ → ℤ) {k : ℕ} (hk : k < n) :
    ((∑ k' : Fin n, RealizedProgram.Ops.negCoef n h k k' * x k' : ℤ) : _root_.MLDSA.Coeff) =
      LatticeCrypto.negacyclicConvCoeff (fun m : Fin n => (h m : _root_.MLDSA.Coeff))
        (fun m => (x m : _root_.MLDSA.Coeff)) ⟨k, hk⟩ := by
  push_cast
  have hmap : ∀ k', ((RealizedProgram.Ops.negCoef n h k k' : ℤ) : _root_.MLDSA.Coeff) =
      RealizedProgram.Ops.negCoef n (fun s => (h s : _root_.MLDSA.Coeff)) k k' := fun k' =>
    RealizedProgram.Ops.negCoef_map (Int.castAddHom _root_.MLDSA.Coeff) n h k k'
  simp only [hmap]
  rw [Fin.sum_univ_eq_sum_range (fun k' => RealizedProgram.Ops.negCoef n (fun s => (h s : _root_.MLDSA.Coeff)) k k' *
    (x k' : _root_.MLDSA.Coeff)) n, ← RealizedProgram.Ops.negacyclic_eq_sum_negCoef n _ _ hk, RealizedProgram.Ops.negacyclic,
    RealizedProgram.Ops.ofFin_of_lt _ hk]
  rfl

/-- **An opaque statement value reads the statement** in the source program's readings. -/
theorem reader_opaqueNil (e : program.Env interp) {v : ℕ}
    (h : RealizedProgram.isOpaqueNil (program.value v).kind = true) : program.reader e v = e.stmt v := by
  funext i
  rw [RealizedProgram.reader, RealizedProgram.fuel, RealizedProgram.read.eq_2]
  unfold RealizedProgram.isOpaqueNil at h
  split at h <;> simp_all

/-- **`t1`'s polynomial `i`** as integers (the key's coefficients). -/
def t1Z (pk : MLDSA44.PublicKey44) (i : Fin 4) (s : ℕ) : ℤ :=
  if hs : s < 256 then ((((pk.t1.get i).get ⟨s, hs⟩).val : ℕ) : ℤ) else 0

/-- **`A_ij`** as integers (the key's coefficients). -/
noncomputable def aZ (pk : MLDSA44.PublicKey44) (i j : Fin 4) (s : ℕ) : ℤ :=
  if hs : s < 256 then ((Rows.aKeyOf pk i j ⟨s, hs⟩ : ℕ) : ℤ) else 0

/-- **The broadcast of `t1` on the integers**: coefficient `k` of row `i` is the negacyclic sum of
`t1_i` against the operand. -/
theorem applyInt_broadcast {e : program.Env interp} {pk : MLDSA44.PublicKey44} (hk : KeyOf pk e.stmt)
    (x : ℕ → ℤ) (i : Fin 4) (k : Fin 256) :
    RealizedProgram.NamedOp.applyInt program 0 (program.reader e) (.polyBroadcast 58 4 .coefficients) x
        ((i : ℕ) * 256 + k) =
      ∑ k' : Fin 256, RealizedProgram.Ops.negCoef 256 (t1Z pk i) k k' * x k' := by
  rw [RealizedProgram.NamedOp.applyInt_polyBroadcast]
  have hn : (program.value 58).size / 4 = 256 := by rw [(sigData (program := program)).2.1]
  have hrows : RealizedProgram.NamedOp.rows program (.polyBroadcast 58 4 .coefficients) = 1024 := (sigData (program := program)).2.1
  have hcols : RealizedProgram.NamedOp.cols program (.polyBroadcast 58 4 .coefficients) = 256 := hn
  have hm : (i : ℕ) * 256 + k < 1024 := by omega
  rw [hrows, hcols, Nat.mod_eq_of_lt hm, Nat.div_eq_of_lt hm]
  simp only [Nat.zero_mul, Nat.zero_add]
  rw [Fin.sum_univ_eq_sum_range (fun k' => (interp 0).coefInt (RealizedProgram.NamedOp.pbEntry program
      (program.reader e) 58 4 ((i : ℕ) * 256 + k) k') * x k'),
    Fin.sum_univ_eq_sum_range (fun k' => RealizedProgram.Ops.negCoef 256 (t1Z pk i) k k' * x k') 256, hn]
  refine Finset.sum_congr rfl fun k' _ => ?_
  congr 1
  unfold RealizedProgram.NamedOp.pbEntry
  rw [hn, if_pos (by omega), show ((i : ℕ) * 256 + k) / 256 = i by omega,
    show ((i : ℕ) * 256 + k) % 256 = k by omega]
  refine RealizedProgram.FieldInterp.coefInt_negCoef gold_char charP_interp0 (fun _ h => toNat_gold_natCast h)
    (by rw [pGold]; norm_num) 256 (fun s hs => ⟨?_, ?_⟩) k k'
  · simp only [t1Z, dif_pos hs]
    have hv : (((pk.t1.get i).get ⟨s, hs⟩).val : ℕ) < 8380417 := ZMod.val_lt _
    have hp : ((pGold : ℕ) : ℤ) = 18446744069414584321 := by norm_num [pGold]
    rw [abs_of_nonneg (Int.natCast_nonneg _), hp]
    omega
  · simp only [RealizedProgram.NamedOp.pbPoly, t1Z, dif_pos hs, Int.cast_natCast, hn]
    have h := hk.t1 i ⟨s, hs⟩
    rw [RealizedProgram.evalE_leaf] at h
    rw [reader_opaqueNil e (sigData (program := program)).2.2.2.2.2.2.2.2.2.2.2.2]
    exact h

/-- **The product of `A` on the integers**: coefficient `k` of row `i` is the sum over the columns
of the negacyclic sums of `A_ij` against the operand's polynomial `j`. -/
theorem applyInt_matVec {e : program.Env interp} {pk : MLDSA44.PublicKey44} (hk : KeyOf pk e.stmt)
    (x : ℕ → ℤ) (i : Fin 4) (k : Fin 256) :
    RealizedProgram.NamedOp.applyInt program 0 (program.reader e) (.polyMatVec 57 4 4 .coefficients) x
        ((i : ℕ) * 256 + k) =
      ∑ l : Fin 4, ∑ k' : Fin 256, RealizedProgram.Ops.negCoef 256 (aZ pk i l) k k' * x (l * 256 + k') := by
  rw [RealizedProgram.NamedOp.applyInt_polyMatVec]
  have hn : (program.value 57).size / (4 * 4) = 256 := by rw [(sigData (program := program)).1]
  have hrows : RealizedProgram.NamedOp.rows program (.polyMatVec 57 4 4 .coefficients) = 1024 := by
    simp only [RealizedProgram.NamedOp.rows, hn]
  have hcols : RealizedProgram.NamedOp.cols program (.polyMatVec 57 4 4 .coefficients) = 1024 := by
    simp only [RealizedProgram.NamedOp.cols, hn]
  have hm : (i : ℕ) * 256 + k < 1024 := by omega
  rw [hrows, hcols, Nat.mod_eq_of_lt hm, Nat.div_eq_of_lt hm]
  simp only [Nat.zero_mul, Nat.zero_add]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Fin.sum_univ_eq_sum_range (fun k' => (interp 0).coefInt (RealizedProgram.Ops.negCoef ((program.value 57).size / (4 * 4))
      (RealizedProgram.NamedOp.pmvPoly program (program.reader e) 57 4 4 (((i : ℕ) * 256 + k) /
        ((program.value 57).size / (4 * 4))) l)
      (((i : ℕ) * 256 + k) % ((program.value 57).size / (4 * 4))) k') *
        x ((l : ℕ) * ((program.value 57).size / (4 * 4)) + k')),
    Fin.sum_univ_eq_sum_range (fun k' => RealizedProgram.Ops.negCoef 256 (aZ pk i l) k k' * x (l * 256 + k')) 256,
    hn]
  refine Finset.sum_congr rfl fun k' _ => ?_
  congr 1
  rw [show ((i : ℕ) * 256 + k) / 256 = i by omega, show ((i : ℕ) * 256 + k) % 256 = k by omega]
  refine RealizedProgram.FieldInterp.coefInt_negCoef gold_char charP_interp0 (fun _ h => toNat_gold_natCast h)
    (by rw [pGold]; norm_num) 256 (fun s hs => ⟨?_, ?_⟩) k k'
  · simp only [aZ, dif_pos hs]
    have hv : Rows.aKeyOf pk i l ⟨s, hs⟩ < 8380417 := Rows.aKeyOf_lt pk i l _
    have hp : ((pGold : ℕ) : ℤ) = 18446744069414584321 := by norm_num [pGold]
    rw [abs_of_nonneg (Int.natCast_nonneg _), hp]
    omega
  · simp only [RealizedProgram.NamedOp.pmvPoly, aZ, dif_pos hs, Int.cast_natCast, hn]
    have h := hk.a i l ⟨s, hs⟩
    rw [RealizedProgram.evalE_leaf] at h
    rw [reader_opaqueNil e (sigData (program := program)).2.2.2.2.2.2.2.2.2.2.2.1]
    exact h

/-- **The integer reading of a bound value of `A` whose element is a small integer's cast** is
the integer. -/
theorem intOf_of_boundInt {e : program.Env interp} {v i : ℕ} (hb : (program.value v).kind.isBound = true)
    (hf : program.valueField v = 0) {z : ℤ} (hz : 2 * |z| < pGold) (hv : rdA e v i = z) :
    program.intOf (program.reader e) v i = z := by
  obtain ⟨x, hx⟩ : ∃ x, (program.value v).kind = .bound x := by
    revert hb
    cases (program.value v).kind <;> simp [RealizedProgram.Kind.isBound]
  rw [RealizedProgram.intOf_of_bound _ hx]
  unfold rdA at hv
  rw [RealizedProgram.evalE_leaf] at hv
  revert hv
  generalize program.reader e v i = y
  generalize program.valueField v = a at hf y
  subst hf
  rw [RealizedProgram.castElt_self]
  intro hv
  rw [hv]
  exact coefInt_gold hz

/-- The kinds of `z` and `w'` (values bound to their digits). -/
theorem boundZW : (program.value 59).kind.isBound = true ∧ (program.value 62).kind.isBound = true ∧ (program.value 61).kind.isPriv = true :=
  MldsaEAlgebra.boundZW

/-- `−2^(d+1)`'s centred reading. -/
theorem centered_m16384 : (interp 0).centered 18446744069414567937 = -16384 := by
  unfold RealizedProgram.FieldInterp.centered
  rw [gold_char, if_neg (by norm_num [pGold])]
  norm_num [pGold]

/-- **The left side modulo `q`**: `w' + 8192 (t1_i ⊛ support) − 16384 (t1_i ⊛ sign)`. -/
theorem cast_sigL {e : program.Env interp} {pk : MLDSA44.PublicKey44} (hk : KeyOf pk e.stmt)
    (i : Fin 4) (k : Fin 256) :
    ((program.evalIntWith (program.reader e) 0 sigL ((i : ℕ) * 256 + k) : ℤ) :
        _root_.MLDSA.Coeff) =
      ((program.intOf (program.reader e) 62 ((i : ℕ) * 256 + k) : ℤ) : _root_.MLDSA.Coeff) +
        8192 * LatticeCrypto.negacyclicConvCoeff (fun m : Fin 256 => (t1Z pk i m : _root_.MLDSA.Coeff))
          (fun m => (program.evalIntWith (program.reader e) 0 (.ref 7) m : _root_.MLDSA.Coeff)) k -
        16384 * LatticeCrypto.negacyclicConvCoeff (fun m : Fin 256 => (t1Z pk i m : _root_.MLDSA.Coeff))
          (fun m => (program.evalIntWith (program.reader e) 0 (.ref 8) m : _root_.MLDSA.Coeff)) k := by
  rw [RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_leaf,
    RealizedProgram.evalIntWith_scale_const, RealizedProgram.evalIntWith_scale_const, RealizedProgram.evalIntWith_apply,
    RealizedProgram.evalIntWith_apply, (lensA (program := program)).2.2.2.2.2.2.2.2, centered_small (by norm_num [pGold]),
    centered_m16384, applyInt_broadcast hk, applyInt_broadcast hk, Int.cast_add, Int.cast_add,
    Int.cast_mul, Int.cast_mul, cast_sum_negCoef _ _ k.isLt, cast_sum_negCoef _ _ k.isLt]
  push_cast
  ring

/-- **The right side modulo `q`**: `Σ_l A_il ⊛ z_l`. -/
theorem cast_sigR {e : program.Env interp} {pk : MLDSA44.PublicKey44} (hk : KeyOf pk e.stmt)
    (i : Fin 4) (k : Fin 256) :
    ((program.evalIntWith (program.reader e) 0 sigR ((i : ℕ) * 256 + k) : ℤ) :
        _root_.MLDSA.Coeff) =
      ∑ l : Fin 4, LatticeCrypto.negacyclicConvCoeff
        (fun m : Fin 256 => (aZ pk i l m : _root_.MLDSA.Coeff))
        (fun m => (program.intOf (program.reader e) 59 ((l : ℕ) * 256 + m) : _root_.MLDSA.Coeff)) k := by
  rw [RealizedProgram.evalIntWith_apply, (lensA (program := program)).2.2.2.2.2.2.2.2, applyInt_matVec hk, Int.cast_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact cast_sum_negCoef (aZ pk i l) (fun m => program.evalIntWith (program.reader e) 0 (.leaf 59)
    ((l : ℕ) * 256 + m)) k.isLt

/-- **The naturals of `w'`** (its integer reading, a natural). -/
def wvE (e : program.Env interp) (i : Fin 4) (k : Fin 256) : ℕ :=
  (program.intOf (program.reader e) 62 ((i : ℕ) * 256 + k)).toNat

/-- **The shifted naturals of `z`** (`z + (γ₁ − β − 1)`, a natural). -/
def zvE (e : program.Env interp) (j : Fin 4) (m : Fin 256) : ℕ :=
  (program.intOf (program.reader e) 59 ((j : ℕ) * 256 + m) + 130993).toNat

/-- **`w'`'s integer reading is its natural.** -/
theorem intOf_w {e : program.Env interp} (hs : program.SourceSatAt e) (i : Fin 4) (k : Fin 256) :
    program.intOf (program.reader e) 62 ((i : ℕ) * 256 + k) = wvE e i k ∧
      (program.intOf (program.reader e) 62 ((i : ℕ) * 256 + k) : ℤ) =
        (interp 0).coefInt (wVals (program.reader e) i k) := by
  obtain ⟨n, hn, hv⟩ := w_range hs (flat_lt i k)
  have h : program.intOf (program.reader e) 62 ((i : ℕ) * 256 + k) = n :=
    intOf_of_boundInt (boundZW (program := program)).2.1 (sigData (program := program)).2.2.2.2.2.2.2.2.2.1
      (by rw [abs_of_nonneg (by positivity)]; norm_num [pGold]; omega) (by rw [hv]; simp)
  refine ⟨by rw [h, wvE, h]; simp, ?_⟩
  change _ = (interp 0).coefInt (rdA e 62 _)
  rw [h, hv, show ((n : ℕ) : (interp 0).K) = ((n : ℤ) : (interp 0).K) from (Int.cast_natCast n).symm,
    coefInt_gold (by rw [abs_of_nonneg (by positivity)]; norm_num [pGold]; omega)]

/-- **`z`'s integer reading is its shifted natural less the shift.** -/
theorem intOf_z {e : program.Env interp} (hs : program.SourceSatAt e) (j : Fin 4) (m : Fin 256) :
    program.intOf (program.reader e) 59 ((j : ℕ) * 256 + m) =
        Rows.signedZ (zvE e) j m ∧
      (program.intOf (program.reader e) 59 ((j : ℕ) * 256 + m) : ℤ) =
        (interp 0).coefInt (zVals (program.reader e) j m) := by
  obtain ⟨n, hlt, hn⟩ := z_int hs (flat_lt j m)
  have hb : n.natAbs < 130994 := hlt
  have ha : |n| < 130994 := by rw [Int.abs_eq_natAbs]; exact_mod_cast hb
  have h : program.intOf (program.reader e) 59 ((j : ℕ) * 256 + m) = n :=
    intOf_of_boundInt (boundZW (program := program)).1 (sigData (program := program)).2.2.2.2.2.2.2.1 (by norm_num [pGold]; omega) hn.symm
  refine ⟨?_, ?_⟩
  · have hsh : ((mldsa44.normBound - 1 : ℕ) : ℤ) = 130993 := by decide
    simp only [Rows.signedZ, Rows.shift, zvE, h, hsh]
    omega
  · change _ = (interp 0).coefInt (rdA e 59 _)
    rw [h, ← hn, coefInt_gold (by norm_num [pGold]; omega)]

/-- **The challenge bits' integer readings**: support at `ref 7`, sign at `ref 8`. -/
theorem evalInt_ref78 (e : program.Env interp) (k : Fin 256) :
    program.evalIntWith (program.reader e) 0 (.ref 7) k = program.intOf (program.reader e) 61 (2 * k) ∧
      program.evalIntWith (program.reader e) 0 (.ref 8) k =
        program.intOf (program.reader e) 61 (2 * k + 1) := by
  constructor
  · rw [RealizedProgram.evalIntWith_ref (refsOrdered (program := program)) _ _ (by have := (sigData (program := program)).2.2.2.2.2.2.2.2.2.2.1; omega),
      (expr7 (program := program)), RealizedProgram.evalIntWith_reindex, idx11_entry k.isLt]
    rfl
  · rw [RealizedProgram.evalIntWith_ref (refsOrdered (program := program)) _ _ (sigData (program := program)).2.2.2.2.2.2.2.2.2.2.1, (expr8 (program := program)),
      RealizedProgram.evalIntWith_reindex, idx12_entry k.isLt]
    rfl

/-- **The relation modulo `q`** at coefficient `k` of row `i`: `w' + 8192 (t1_i ⊛ support) −
16384 (t1_i ⊛ sign) − Σ_l A_il ⊛ z_l = 0`, where the source program holds, at a key whose
preprocessing the statement holds. -/
theorem sig_mod {e : program.Env interp} (hs : program.SourceSatAt e) {pk : MLDSA44.PublicKey44}
    (hk : KeyOf pk e.stmt) (i : Fin 4) (k : Fin 256) :
    ((program.intOf (program.reader e) 62 ((i : ℕ) * 256 + k) : ℤ) : _root_.MLDSA.Coeff) +
        8192 * LatticeCrypto.negacyclicConvCoeff (fun m : Fin 256 => (t1Z pk i m : _root_.MLDSA.Coeff))
          (fun m => (program.evalIntWith (program.reader e) 0 (.ref 7) m : _root_.MLDSA.Coeff)) k -
        16384 * LatticeCrypto.negacyclicConvCoeff (fun m : Fin 256 => (t1Z pk i m : _root_.MLDSA.Coeff))
          (fun m => (program.evalIntWith (program.reader e) 0 (.ref 8) m : _root_.MLDSA.Coeff)) k -
      ∑ l : Fin 4, LatticeCrypto.negacyclicConvCoeff
        (fun m : Fin 256 => (aZ pk i l m : _root_.MLDSA.Coeff))
        (fun m => (program.intOf (program.reader e) 59 ((l : ℕ) * 256 + m) : _root_.MLDSA.Coeff)) k =
      0 := by
  have h := holdsA hs (p := 274) (by simp)
  obtain ⟨_, hb⟩ := pred274 (program := program)
  rw [hb] at h
  have hd := h ((i : ℕ) * 256 + k) (by
    change _ < program.exprLen sigL
    have : program.exprLen sigL = 1024 := MldsaEAlgebra.lenSigL
    rw [this]
    exact flat_lt i k)
  change ((8380417 : ℕ) : ℤ) ∣ program.evalIntWith (program.reader e) 0 sigL _ -
    program.evalIntWith (program.reader e) 0 sigR _ at hd
  have h0 : ((program.evalIntWith (program.reader e) 0 sigL ((i : ℕ) * 256 + k) -
      program.evalIntWith (program.reader e) 0 sigR ((i : ℕ) * 256 + k) : ℤ) :
        _root_.MLDSA.Coeff) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
  rw [Int.cast_sub, cast_sigL hk, cast_sigR hk] at h0
  exact h0

/-- **The congruence** (`Rows.Congruent` at the keys of `pk`): `w' ≡ Σ_j A_ij z_j −
c t_i (mod q)` with `c = support − 2 sign` and `t_i = 2^d t1_i`, where the source program holds, at
a key whose preprocessing the statement holds. -/
theorem congruentE {e : program.Env interp} (hs : program.SourceSatAt e) {pk : MLDSA44.PublicKey44}
    (hk : KeyOf pk e.stmt) :
    Rows.Congruent (Rows.aKeyOf pk) (Rows.tKeyOf pk)
      (zvE e) (wvE e) (fun m => program.evalIntWith (program.reader e) 0 (.ref 7) m -
        2 * program.evalIntWith (program.reader e) 0 (.ref 8) m) := fun i k => by
  have hd : ((program.intOf (program.reader e) 62 ((i : ℕ) * 256 + k) : ℤ) : _root_.MLDSA.Coeff) +
        8192 * LatticeCrypto.negacyclicConvCoeff
          (fun m : Fin Native.Rows.deg => (t1Z pk i m : _root_.MLDSA.Coeff))
          (fun m => (program.evalIntWith (program.reader e) 0 (.ref 7) m : _root_.MLDSA.Coeff)) k -
        16384 * LatticeCrypto.negacyclicConvCoeff
          (fun m : Fin Native.Rows.deg => (t1Z pk i m : _root_.MLDSA.Coeff))
          (fun m => (program.evalIntWith (program.reader e) 0 (.ref 8) m : _root_.MLDSA.Coeff)) k -
      ∑ l : Fin 4, LatticeCrypto.negacyclicConvCoeff
        (fun m : Fin Native.Rows.deg => (aZ pk i l m : _root_.MLDSA.Coeff))
        (fun m => (program.intOf (program.reader e) 59 ((l : ℕ) * 256 + m) : _root_.MLDSA.Coeff)) k =
      0 := sig_mod hs hk i k
  have hW : ((wvE e i k : ℕ) : _root_.MLDSA.Coeff) =
      ((program.intOf (program.reader e) 62 ((i : ℕ) * 256 + k) : ℤ) : _root_.MLDSA.Coeff) := by
    rw [(intOf_w hs i k).1, Int.cast_natCast]
  have hA : ∀ l : Fin 4, (fun m : Fin Native.Rows.deg =>
      ((Rows.aKeyOf pk i l m : ℕ) : _root_.MLDSA.Coeff)) =
        fun m : Fin Native.Rows.deg => (aZ pk i l m : _root_.MLDSA.Coeff) :=
    fun l => funext fun m => by
      simp only [aZ, dif_pos (show (m : ℕ) < 256 from m.isLt), Int.cast_natCast]
  have hZ : ∀ l : Fin 4, (fun m : Fin Native.Rows.deg =>
      ((Rows.signedZ (zvE e) l m : ℤ) : _root_.MLDSA.Coeff)) =
        fun m : Fin Native.Rows.deg =>
          (program.intOf (program.reader e) 59 ((l : ℕ) * 256 + m) : _root_.MLDSA.Coeff) :=
    fun l => funext fun m => by rw [(intOf_z hs l m).1]
  have hT : (fun m : Fin Native.Rows.deg => ((Rows.tKeyOf pk i m : ℕ) : _root_.MLDSA.Coeff)) =
      fun m : Fin Native.Rows.deg => (8192 : _root_.MLDSA.Coeff) * (t1Z pk i m : _root_.MLDSA.Coeff) :=
    funext fun m => by
      rw [Emulated.tKeyOf_cast]
      simp only [Emulated.t1Key, t1Z, dif_pos (show (m : ℕ) < 256 from m.isLt),
        Int.cast_natCast, ZMod.natCast_zmod_val]
      norm_num [Native.Params.dBits]
      left
      decide
  have hc : (fun m : Fin Native.Rows.deg => ((program.evalIntWith (program.reader e) 0 (.ref 7) m -
      2 * program.evalIntWith (program.reader e) 0 (.ref 8) m : ℤ) : _root_.MLDSA.Coeff)) =
        fun m : Fin Native.Rows.deg =>
          (program.evalIntWith (program.reader e) 0 (.ref 7) m : _root_.MLDSA.Coeff) -
            2 * (program.evalIntWith (program.reader e) 0 (.ref 8) m : _root_.MLDSA.Coeff) :=
    funext fun m => by push_cast; ring
  have hsum : ∑ l : Fin Native.Rows.nCols, LatticeCrypto.negacyclicConvCoeff
      (fun m : Fin Native.Rows.deg => ((Rows.aKeyOf pk i l m : ℕ) : _root_.MLDSA.Coeff))
      (fun m : Fin Native.Rows.deg =>
        ((Rows.signedZ (zvE e) l m : ℤ) : _root_.MLDSA.Coeff)) k =
      ∑ l : Fin 4, LatticeCrypto.negacyclicConvCoeff
        (fun m : Fin Native.Rows.deg => (aZ pk i l m : _root_.MLDSA.Coeff))
        (fun m : Fin Native.Rows.deg =>
          (program.intOf (program.reader e) 59 ((l : ℕ) * 256 + m) : _root_.MLDSA.Coeff)) k :=
    Finset.sum_congr rfl fun l _ => by rw [hA l, hZ l]
  show ((wvE e i k : ℕ) : _root_.MLDSA.Coeff) = ∑ l : Fin Native.Rows.nCols,
      LatticeCrypto.negacyclicConvCoeff
        (fun m : Fin Native.Rows.deg => ((Rows.aKeyOf pk i l m : ℕ) : _root_.MLDSA.Coeff))
        (fun m : Fin Native.Rows.deg =>
          ((Rows.signedZ (zvE e) l m : ℤ) : _root_.MLDSA.Coeff)) k -
      LatticeCrypto.negacyclicConvCoeff
        (fun m : Fin Native.Rows.deg => ((program.evalIntWith (program.reader e) 0 (.ref 7) m -
          2 * program.evalIntWith (program.reader e) 0 (.ref 8) m : ℤ) : _root_.MLDSA.Coeff))
        (fun m : Fin Native.Rows.deg => ((Rows.tKeyOf pk i m : ℕ) : _root_.MLDSA.Coeff)) k
  rw [hW, hT, hc, DFT.negacyclicConvCoeff_ternary, hsum]
  rw [Falcon512.negacyclicConvCoeff_comm (fun m : Fin Native.Rows.deg =>
      (program.evalIntWith (program.reader e) 0 (.ref 7) m : _root_.MLDSA.Coeff)),
    Falcon512.negacyclicConvCoeff_comm (fun m : Fin Native.Rows.deg =>
      (program.evalIntWith (program.reader e) 0 (.ref 8) m : _root_.MLDSA.Coeff))]
  linear_combination hd

/-- **A private value of `A` reads as its integer reading.** -/
theorem intOf_priv (e : program.Env interp) {v i : ℕ} (hp : (program.value v).kind.isPriv = true)
    (hf : program.valueField v = 0) :
    program.intOf (program.reader e) v i = ((interp 0).toNat (rdA e v i) : ℤ) := by
  obtain hk : (program.value v).kind = .priv := by
    revert hp
    cases (program.value v).kind <;> simp [RealizedProgram.Kind.isPriv]
  unfold RealizedProgram.intOf rdA
  rw [hk, RealizedProgram.evalE_leaf]
  simp only
  revert hf
  generalize program.reader e v i = y
  generalize program.valueField v = a at y
  intro hf
  subst hf
  rw [RealizedProgram.castElt_self]

/-- **A's challenge polynomial's coefficients** are `support − 2 · sign` of the challenge bits'
integer readings. -/
theorem coeff_cPolyA {e : program.Env interp} (hs : program.SourceSatAt e) :
    MLDSA44.coeff (cPolyA (program.reader e)) = fun k : Fin _root_.MLDSA.ringDegree =>
      ((program.evalIntWith (program.reader e) 0 (.ref 7) k -
        2 * program.evalIntWith (program.reader e) 0 (.ref 8) k : ℤ) : _root_.MLDSA.Coeff) := by
  funext k
  rw [cPolyA, MLDSA44.coeff_ofCoeff, (evalInt_ref78 e k).1, (evalInt_ref78 e k).2,
    intOf_priv e (boundZW (program := program)).2.2 (sigData (program := program)).2.2.2.2.2.2.2.2.1,
    intOf_priv e (boundZW (program := program)).2.2 (sigData (program := program)).2.2.2.2.2.2.2.2.1]
  have hk : (k : ℕ) < 256 := k.isLt
  have h0 := cBool hs (i := 2 * k) (by omega)
  have h1 := cBool hs (i := 2 * k + 1) (by omega)
  rw [bitCoeff_eq_toNat (by simpa [cABits, rdA] using h0),
    bitCoeff_eq_toNat (by simpa [cABits, rdA] using h1)]
  push_cast
  rfl

/-- **The extracted `z` is the shifted naturals' `z`** (`Rows.zVec`). -/
theorem zOf_eq {e : program.Env interp} (hs : program.SourceSatAt e) :
    zOf (program.reader e) = Rows.zVec (zvE e) := by
  apply Vector.ext
  intro j hj
  unfold zOf Rows.zVec
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  refine congrArg MLDSA44.ofCoeff (funext fun m => ?_)
  exact congrArg (Int.cast : ℤ → _root_.MLDSA.Coeff)
    ((intOf_z hs ⟨j, hj⟩ m).2.symm.trans (intOf_z hs ⟨j, hj⟩ m).1)

/-- **`w' = computeWApprox(Â, c, z, t1)`**, where the source program holds, at a key whose
preprocessing the statement holds. -/
theorem algebra_eq {e : program.Env interp} (hs : program.SourceSatAt e) {pk : MLDSA44.PublicKey44}
    (hk : KeyOf pk e.stmt) :
    wOf (program.reader e) = _root_.MLDSA.computeWApprox _root_.MLDSA.mldsa44 Native.Rows.prims
      (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps) (Native.Rows.aHat pk)
      (cPolyA (program.reader e)) (zOf (program.reader e)) pk.t1 := by
  have hcong := congruentE hs hk
  apply Vector.ext
  intro i hi
  have key : (wOf (program.reader e)).get ⟨i, hi⟩ = (_root_.MLDSA.computeWApprox
      _root_.MLDSA.mldsa44 Native.Rows.prims (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps)
      (Native.Rows.aHat pk) (cPolyA (program.reader e)) (zOf (program.reader e)) pk.t1).get
        ⟨i, hi⟩ := by
    rw [← MLDSA44.ofCoeff_coeff (Vector.get (_root_.MLDSA.computeWApprox _root_.MLDSA.mldsa44
      Native.Rows.prims (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps)
      (Native.Rows.aHat pk) (cPolyA (program.reader e)) (zOf (program.reader e)) pk.t1)
        ⟨i, hi⟩)]
    unfold wOf
    rw [Vector.get_ofFn]
    refine congrArg MLDSA44.ofCoeff (funext fun k => ?_)
    rw [MLDSA44.coeff_computeWApprox, coeff_cPolyA hs, zOf_eq hs]
    have h := congrArg (Int.cast : ℤ → _root_.MLDSA.Coeff)
      ((intOf_w hs ⟨i, hi⟩ k).2.symm.trans (intOf_w hs ⟨i, hi⟩ k).1)
    rw [Int.cast_natCast] at h
    exact h.trans (hcong.computeWApprox ⟨i, hi⟩ k)
  simpa [Vector.get_eq_getElem] using key

/-! ## Domain `A`'s obligation -/

/-- **Domain `A`'s obligation** (`AlgebraSound`): the type checks, the ranges, UseHint with the wrap
and the signature relation give `AlgebraAt` wherever the source program holds, at every key whose
preprocessing the statement holds. -/
theorem algebraSound : AlgebraSound (program := program) (F0 := F0) (FH := FH) := by
  intro e hs pk hk
  refine ⟨fun k s => ?_, fun t => w1Bool hs t.isLt, algebra_eq hs hk, useHint_eq hs,
    norm_lt hs, hintWeight_le hs⟩
  have hk' := k.isLt
  have hd : _root_.MLDSA.ringDegree = 256 := rfl
  have := cBool hs (i := 2 * k + s) (by have := s.isLt; omega)
  simpa [cABits, rdA] using this

end GordieHowe.MLDSA44.Emulated
