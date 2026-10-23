-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Frontend.Cross
public import GordieHowe.Applications.MLDSA44.Frontend.Key
public import GordieHowe.Language.Library.Cross
public import GordieHowe.Language.Realizations.RealizeGrouped
import all LatticeCrypto.MLDSA.Concrete.NTT

@[expose] public section

/-!
# GordieHowe frontend: `MLDSA44.Native.ROMParams`, the algebra of domain `A`

Domain `A`'s obligation of the frontend (`GordieHowe.MLDSA44.Native.ROMParams.AlgebraSound`, `algebraSound`): wherever
the source program holds, at every key whose preprocessing the statement holds, the readings of
domain `A` satisfy `AlgebraAt`:

* the type checks (`h.boolean`, `challenge.c.boolean`, `hint.w1.boolean`,
  `hint.nonpositive.boolean`) make the hint, the challenge bits, the UseHint output bits and the
  sign advice bits;
* the ranges `norm.z`, `hint.offset`, `hint.slack` and `hint_weight.weight` bound `z`, the offset,
  the slack and the hint weight;
* `hint.w1_bound`, `hint.interval` (an integer `mod_0`, read as its field equation) and
  `hint.decompose` are the hand-built `GordieHowe.MLDSA44.Native.UseHintHolds` at every coefficient, so
  `GordieHowe.MLDSA44.Native.useHint_sound` gives UseHint;
* `signature.relation` is the field equation `w' − Â z + 2^d t1 (support − 2 sign) = 0`; its operands
  other than the statement's are in the prime subfield, so its constant coordinate (`coord0`) is
  the equation over `ZMod q` of the statement's readings, which are the key's `Â` and `t1`
  (`KeyOf`), `Â` read through the realized program's inverse transform, the vendored `invNTT`
  (`GordieHowe.MLDSA44.KeyNTT.inverseNtt_spectrum`); so `w' = computeWApprox(Â, c, z, t1)`.
-/

namespace GordieHowe.MLDSA44.Native.ROMParams

open Generated.MLDSA44.Native.ROMParams.Program
open GordieHowe.Bits

/-- **The program facts of a native program's domain `A`** (`MldsaACross` and): the source predicates of `A` and their shared expressions (with the index maps of the program at the ROM parameters), their lengths, constants and types. Each program instantiates it by `decide`. -/
class MldsaAAlgebra (program : RealizedProgram) : Prop extends MldsaACross program where
  /-- `key.a_hat` is an opaque statement value of no argument. -/
  kind56 : (program.value 56).kind = .pub (.opaque "key.a_hat" [])
  /-- `key.t1` is an opaque statement value of no argument. -/
  kind57 : (program.value 57).kind = .pub (.opaque "key.t1" [])
  /-- The hint's sum has a coordinate. -/
  lenWeight : 0 < program.exprLen (.apply (.sum 1024) (.leaf 59))
  /-- `pred0`. -/
  pred0 : program.predicate 0 = «p.signature.relation»
  /-- `pred1`. -/
  pred1 : program.predicate 1 = «p.hint.w1_bound»
  /-- `pred2`. -/
  pred2 : program.predicate 2 = «p.hint.decompose»
  /-- `pred3`. -/
  pred3 : program.predicate 3 = «p.hint.interval»
  /-- `pred6`. -/
  pred6 : program.predicate 6 = «p.h.boolean»
  /-- `pred7`. -/
  pred7 : program.predicate 7 = «p.challenge.c.boolean»
  /-- `pred8`. -/
  pred8 : program.predicate 8 = «p.hint.w1.boolean»
  /-- `pred9`. -/
  pred9 : program.predicate 9 = «p.hint.nonpositive.boolean»
  /-- `pred11`. -/
  pred11 : program.predicate 11 = «p.norm.z»
  /-- `pred12`. -/
  pred12 : program.predicate 12 = «p.hint.offset»
  /-- `pred13`. -/
  pred13 : program.predicate 13 = «p.hint.slack»
  /-- `pred14`. -/
  pred14 : program.predicate 14 = «p.hint_weight.weight»
  /-- `expr0`. -/
  expr0 : program.expr 0 = .reindex idx6 (.leaf 60)
  /-- `expr1`. -/
  expr1 : program.expr 1 = .reindex idx7 (.leaf 60)
  /-- `expr2`. -/
  expr2 : program.expr 2 = .mul (.leaf 59) (.leaf 64)
  /-- `expr3`. -/
  expr3 : program.expr 3 = .add (.leaf 59) (.scale (.const 8380416) (.ref 2))
  /-- `expr4`. -/
  expr4 : program.expr 4 = .logic .eq 6 [.leaf 63, .reindex idx8 (.leaf 3)]
  /-- `expr5`. -/
  expr5 : program.expr 5 = .mul (.ref 2) (.logic .eq 6 [.leaf 63, .reindex idx8 (.leaf 1)])
  /-- `expr6`. -/
  expr6 : program.expr 6 = .add (.mul (.add (.leaf 64) (.scale (.const 8380416) (.ref 2))) (.ref 4)) (.ref 5)
  /-- Domain `A`'s predicates are source predicates. -/
  inSource_A : ∀ p ∈ [0, 1, 2, 3, 6, 7, 8, 9, 11, 12, 13, 14], program.inSource (program.predicate p) = true
  /-- The program has `273` predicates. -/
  predicates_length : program.predicates.length = 273
  /-- The lengths and field facts of domain `A`. -/
  lensA : (program.value 58).size = 1024 ∧ (program.value 59).size = 1024 ∧ (program.value 60).size = 512 ∧ (program.value 61).size = 1024 ∧ (program.value 63).size = 6144 ∧ (program.value 64).size = 1024 ∧ (program.value 65).size = 1024 ∧ (program.value 66).size = 1024 ∧ program.domainField 0 = 0
  /-- The type checks of `A` are Boolean checks of their values. -/
  boolChecks : (program.predicate 6).body.boolCheck? = some ⟨0, 59⟩ ∧ (program.predicate 7).body.boolCheck? = some ⟨0, 60⟩ ∧ (program.predicate 8).body.boolCheck? = some ⟨0, 63⟩ ∧ (program.predicate 9).body.boolCheck? = some ⟨0, 64⟩
  /-- The constants domain `A` reads. -/
  constsA : program.isConstant 62 = true ∧ program.valueField 62 = 0 ∧ program.constEntries 62 = List.replicate 1024 130993
  /-- The constants UseHint reads. -/
  constsU : program.isConstant 0 = true ∧ program.constEntries 0 = List.replicate 1024 0 ∧ program.isConstant 1 = true ∧ program.constEntries 1 = [1, 1, 0, 1, 0, 1] ∧ program.isConstant 2 = true ∧ program.constEntries 2 = List.replicate 1024 1 ∧ program.isConstant 3 = true ∧ program.constEntries 3 = [0, 0, 0, 0, 0, 0] ∧ program.isConstant 4 = true ∧ program.constEntries 4 = [1] ∧ program.isConstant 5 = true ∧ program.constEntries 5 = [95231] ∧ program.valueField 0 = 0 ∧ program.valueField 1 = 0 ∧ program.valueField 2 = 0 ∧ program.valueField 3 = 0 ∧ program.valueField 4 = 0 ∧ program.valueField 5 = 0
  /-- `refsA`. -/
  refsA : 6 < program.exprs.length
  /-- The lengths of UseHint's predicates. -/
  lensU : program.exprLen (.logic .leq 6 [.leaf 63, .reindex idx8 (.leaf 1)]) = 1024 ∧ program.exprLen (.leaf 61) = 1024 ∧ program.exprLen (.leaf 65) = 1024
  /-- The values UseHint reads are not constants, of field `0`. -/
  valsU : program.isConstant 59 = false ∧ program.isConstant 63 = false ∧ program.isConstant 64 = false ∧ program.isConstant 65 = false ∧ program.isConstant 66 = false ∧ program.valueField 59 = 0 ∧ program.valueField 63 = 0 ∧ program.valueField 64 = 0 ∧ program.valueField 65 = 0 ∧ program.valueField 66 = 0
  /-- The data of `signature.relation`'s operators. -/
  sigData : (program.value 56).size = 4096 ∧ (program.value 57).size = 1024 ∧ program.exprLen (.leaf 61) = 1024

set_option maxRecDepth 4096 in
/-- The native program at the ROM parameters has these facts. -/
instance : MldsaAAlgebra program where
  kind56 := rfl
  kind57 := rfl
  lenWeight := by decide +kernel
  pred0 := rfl
  pred1 := rfl
  pred2 := rfl
  pred3 := rfl
  pred6 := rfl
  pred7 := rfl
  pred8 := rfl
  pred9 := rfl
  pred11 := rfl
  pred12 := rfl
  pred13 := rfl
  pred14 := rfl
  expr0 := rfl
  expr1 := rfl
  expr2 := rfl
  expr3 := rfl
  expr4 := rfl
  expr5 := rfl
  expr6 := rfl
  inSource_A := by
    decide +kernel
  predicates_length := by decide +kernel
  lensA := by
    decide +kernel
  boolChecks := by
    decide +kernel
  constsA := by
    decide +kernel
  constsU := by
    decide +kernel
  refsA := by decide +kernel
  lensU := by
    decide +kernel
  valsU := by
    decide +kernel
  sigData := by
    decide +kernel

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaAAlgebra program] {F0 FH : RealizedProgram.FieldInterp} [QField F0]
  [HField FH]

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

/-! ## The program's data -/

section Tables

set_option maxRecDepth 4096

theorem pred0 : program.predicate 0 = «p.signature.relation» :=
  MldsaAAlgebra.pred0

theorem pred1 : program.predicate 1 = «p.hint.w1_bound» :=
  MldsaAAlgebra.pred1

theorem pred2 : program.predicate 2 = «p.hint.decompose» :=
  MldsaAAlgebra.pred2

theorem pred3 : program.predicate 3 = «p.hint.interval» :=
  MldsaAAlgebra.pred3

theorem pred11 : program.predicate 11 = «p.norm.z» :=
  MldsaAAlgebra.pred11

theorem pred12 : program.predicate 12 = «p.hint.offset» :=
  MldsaAAlgebra.pred12

theorem pred13 : program.predicate 13 = «p.hint.slack» :=
  MldsaAAlgebra.pred13

theorem pred14 : program.predicate 14 = «p.hint_weight.weight» :=
  MldsaAAlgebra.pred14

theorem expr0 : program.expr 0 = .reindex idx6 (.leaf 60) :=
  MldsaAAlgebra.expr0

theorem expr1 : program.expr 1 = .reindex idx7 (.leaf 60) :=
  MldsaAAlgebra.expr1

theorem expr2 : program.expr 2 = .mul (.leaf 59) (.leaf 64) :=
  MldsaAAlgebra.expr2

theorem expr3 : program.expr 3 = .add (.leaf 59) (.scale (.const 8380416) (.ref 2)) :=
  MldsaAAlgebra.expr3

theorem expr4 : program.expr 4 = .logic .eq 6 [.leaf 63, .reindex idx8 (.leaf 3)] :=
  MldsaAAlgebra.expr4

theorem expr5 : program.expr 5 = .mul (.ref 2) (.logic .eq 6 [.leaf 63, .reindex idx8 (.leaf 1)]) :=
  MldsaAAlgebra.expr5

theorem expr6 : program.expr 6 = .add (.mul (.add (.leaf 64) (.scale (.const 8380416) (.ref 2))) (.ref 4)) (.ref 5) :=
  MldsaAAlgebra.expr6

end Tables

/-- Domain `A`'s predicates are source predicates. -/
theorem inSource_A : ∀ p ∈ [0, 1, 2, 3, 6, 7, 8, 9, 11, 12, 13, 14], program.inSource (program.predicate p) = true :=
  MldsaAAlgebra.inSource_A

/-- The program has `273` predicates. -/
theorem predicates_length : program.predicates.length = 273 :=
  MldsaAAlgebra.predicates_length

/-- **A source predicate of `A` holds** where the source program holds. -/
theorem holdsA {e : program.Env interp} (hs : program.SourceSatAt e) {p : ℕ}
    (hp : p ∈ [0, 1, 2, 3, 6, 7, 8, 9, 11, 12, 13, 14]) :
    program.HoldsAt e (program.predicate p).body :=
  hs.preds _ (RealizedProgram.predicate_mem (by rw [(predicates_length (program := program))]; simp at hp; omega))
    ((inSource_A (program := program)) p hp)

/-- **A value of domain `A`** read in `F_q^6`. -/
def rdA (e : program.Env interp) (v i : ℕ) : (interp 0).K :=
  program.evalE (program.reader e) 0 (.leaf v) i

/-- The lengths and field facts of domain `A`. -/
theorem lensA : (program.value 58).size = 1024 ∧ (program.value 59).size = 1024 ∧ (program.value 60).size = 512 ∧ (program.value 61).size = 1024 ∧ (program.value 63).size = 6144 ∧ (program.value 64).size = 1024 ∧ (program.value 65).size = 1024 ∧ (program.value 66).size = 1024 ∧ program.domainField 0 = 0 :=
  MldsaAAlgebra.lensA

/-! ## The type checks -/

/-- The type checks of `A` are Boolean checks of their values. -/
theorem boolChecks : (program.predicate 6).body.boolCheck? = some ⟨0, 59⟩ ∧ (program.predicate 7).body.boolCheck? = some ⟨0, 60⟩ ∧ (program.predicate 8).body.boolCheck? = some ⟨0, 63⟩ ∧ (program.predicate 9).body.boolCheck? = some ⟨0, 64⟩ :=
  MldsaAAlgebra.boolChecks

/-- **A type-checked value of `A` is a bit** where the source program holds. -/
theorem boolA {e : program.Env interp} (hs : program.SourceSatAt e) {p v : ℕ}
    (hp : p ∈ [0, 1, 2, 3, 6, 7, 8, 9, 11, 12, 13, 14])
    (hc : (program.predicate p).body.boolCheck? = some ⟨0, v⟩) {i : ℕ}
    (hi : i < (program.value v).size) : rdA e v i = 0 ∨ rdA e v i = 1 := by
  have h := RealizedProgram.bool_of_boolCheck hc (holdsA hs hp) hi
  rw [(lensA (program := program)).2.2.2.2.2.2.2.2] at h
  exact h

/-- The hint is Boolean. -/
theorem hBool {e : program.Env interp} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    rdA e 59 i = 0 ∨ rdA e 59 i = 1 :=
  boolA hs (by simp) (boolChecks (program := program)).1 (by rw [(lensA (program := program)).2.1]; exact hi)

/-- The challenge bits are Boolean. -/
theorem cBool {e : program.Env interp} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 512) :
    rdA e 60 i = 0 ∨ rdA e 60 i = 1 :=
  boolA hs (by simp) (boolChecks (program := program)).2.1 (by rw [(lensA (program := program)).2.2.1]; exact hi)

/-- The UseHint output bits are Boolean. -/
theorem w1Bool {e : program.Env interp} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 6144) :
    rdA e 63 i = 0 ∨ rdA e 63 i = 1 :=
  boolA hs (by simp) (boolChecks (program := program)).2.2.1 (by rw [(lensA (program := program)).2.2.2.2.1]; exact hi)

/-- The sign advice is Boolean. -/
theorem npBool {e : program.Env interp} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    rdA e 64 i = 0 ∨ rdA e 64 i = 1 :=
  boolA hs (by simp) (boolChecks (program := program)).2.2.2 (by rw [(lensA (program := program)).2.2.2.2.2.1]; exact hi)

/-! ## The ranges -/

/-- **A range membership of one record** gives a natural below the bound. -/
theorem natBelow_of_mem {rd : program.Valuation interp} {n : ℕ} {r : RealizedProgram.Expr} {real : RealizedProgram.InRealization}
    (h : program.HoldsWith rd (.mem 0 [r] (.range n) real)) {i : ℕ} (hi : i < program.exprLen r) :
    ∃ k < n, program.evalE rd 0 r i = k := by
  have hw : ∃ k < n, program.evalE rd (program.domainField 0) r i = k :=
    h i hi r (List.mem_singleton_self r)
  have h0 := MldsaACross.domainField0 (program := program)
  revert hw
  generalize program.domainField 0 = D at h0 ⊢
  subst h0
  exact id

/-- The constants `F_q^6` decodes are casts. -/
theorem decode_fq6 (c : ℕ) : (interp 0).decode c = (c : (interp 0).K) := QField.decode_eq c

/-- The constants domain `A` reads. -/
theorem constsA : program.isConstant 62 = true ∧ program.valueField 62 = 0 ∧ program.constEntries 62 = List.replicate 1024 130993 :=
  MldsaAAlgebra.constsA

/-- **`norm.z`'s offset** reads `130993 = γ₁ − β − 1`. -/
theorem rdA_62 (e : program.Env interp) {i : ℕ} (hi : i < 1024) :
    rdA e 62 i = ((130993 : ℕ) : (interp 0).K) := by
  unfold rdA
  rw [RealizedProgram.evalE_leaf_of_isConstant e (constsA (program := program)).1, RealizedProgram.constRead_of_valueField (constsA (program := program)).2.1,
    (constsA (program := program)).2.2, List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hi, Option.getD_some,
    decode_fq6]

/-- **`norm.z` bounds `z`**: `z + 130993` is a natural below `261987`. -/
theorem norm_range {e : program.Env interp} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    ∃ k : ℕ, k < 261987 ∧ rdA e 58 i + ((130993 : ℕ) : (interp 0).K) = k := by
  have h := holdsA hs (p := 11) (by simp)
  rw [(pred11 (program := program))] at h
  have hlen : i < program.exprLen (.add (.leaf 58) (.leaf 62)) := by
    rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_leaf, (lensA (program := program)).1]
    exact hi
  obtain ⟨k, hk, hkv⟩ := natBelow_of_mem h hlen
  refine ⟨k, hk, ?_⟩
  rw [← rdA_62 e hi]
  exact hkv

/-- **`hint.offset` bounds the offset** below `512^2`. -/
theorem offset_range {e : program.Env interp} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    ∃ k : ℕ, k < 262144 ∧ rdA e 65 i = k := by
  have h := holdsA hs (p := 12) (by simp)
  rw [(pred12 (program := program))] at h
  exact natBelow_of_mem h (by rw [RealizedProgram.exprLen_leaf, (lensA (program := program)).2.2.2.2.2.2.1]; exact hi)

/-- **`hint.slack` bounds the slack** below `512^2`. -/
theorem slack_range {e : program.Env interp} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    ∃ k : ℕ, k < 262144 ∧ rdA e 66 i = k := by
  have h := holdsA hs (p := 13) (by simp)
  rw [(pred13 (program := program))] at h
  exact natBelow_of_mem h (by rw [RealizedProgram.exprLen_leaf, (lensA (program := program)).2.2.2.2.2.2.2.1]; exact hi)

/-- **`hint_weight.weight` bounds the hint's sum** below `81`. -/
theorem weight_range {e : program.Env interp} (hs : program.SourceSatAt e) :
    ∃ k : ℕ, k < 81 ∧ ∑ t : Fin 1024, rdA e 59 t = k := by
  have h := holdsA hs (p := 14) (by simp)
  rw [(pred14 (program := program))] at h
  obtain ⟨k, hk, hkv⟩ := natBelow_of_mem h (i := 0) MldsaAAlgebra.lenWeight
  refine ⟨k, hk, ?_⟩
  rw [RealizedProgram.evalE_apply_sum] at hkv
  simp only [Nat.zero_mul, Nat.zero_add] at hkv
  exact hkv

/-! ## The prime subfield of `F_q^6` -/

instance instFactPrimeOfNatNat_pQ : Fact (Nat.Prime 8380417) := instFactPrimeMlDsaQ

instance charP_interp0 : CharP (interp 0).K 8380417 := QField.charP

instance charP_interp0_modulus : CharP (interp 0).K _root_.MLDSA.modulus :=
  QField.charP

/-- **An element of the prime subfield of `F_q^6`** is the cast of its integer reading. -/
theorem fq6_natCast_toNat {x : (interp 0).K} (hx : x ∈ (interp 0).node "GF(p^1)") :
    (((interp 0).toNat x : ℕ) : (interp 0).K) = x :=
  QField.natCast_toNat x hx

/-- `0` and `1` lie in the prime subfield. -/
theorem mem_prime_of_bool {x : (interp 0).K} (hx : x = 0 ∨ x = 1) :
    x ∈ (interp 0).node "GF(p^1)" := by
  rw [QField.node_prime]
  rcases hx with rfl | rfl
  · exact zero_mem _
  · exact Subring.one_mem _

/-- **The integer reading of a value of `A` in the prime subfield casts to its reading.** -/
theorem cast_intOf {e : program.Env interp} {v i : ℕ} (hc : program.isConstant v = false)
    (hf : program.valueField v = 0) (hp : rdA e v i ∈ (interp 0).node "GF(p^1)") :
    ((program.intOf (program.reader e) v i : ℤ) : (interp 0).K) = rdA e v i := by
  have hint : ((program.intOf (program.reader e) v i : ℤ) : (interp 0).K) =
      (((interp (program.valueField v)).toNat (program.reader e v i) : ℕ) : (interp 0).K) := by
    unfold RealizedProgram.intOf
    unfold RealizedProgram.isConstant at hc
    split
    · rename_i es h
      rw [h] at hc
      cases hc
    · rw [RealizedProgram.FieldInterp.centered_eq,
        show (interp (program.valueField v)).spec.characteristic = 8380417 by
          rw [hf]; exact QField.char_spec,
        RealizedProgram.centeredZ_cast]
    · rw [Int.cast_natCast]
  rw [hint]
  unfold rdA at hp ⊢
  rw [RealizedProgram.evalE_leaf] at hp ⊢
  revert hp
  generalize program.reader e v i = x
  generalize program.valueField v = a at hf x
  subst hf
  rw [RealizedProgram.castElt_self]
  exact fq6_natCast_toNat

/-! ## Constants -/

/-- The constants UseHint reads. -/
theorem constsU : program.isConstant 0 = true ∧ program.constEntries 0 = List.replicate 1024 0 ∧ program.isConstant 1 = true ∧ program.constEntries 1 = [1, 1, 0, 1, 0, 1] ∧ program.isConstant 2 = true ∧ program.constEntries 2 = List.replicate 1024 1 ∧ program.isConstant 3 = true ∧ program.constEntries 3 = [0, 0, 0, 0, 0, 0] ∧ program.isConstant 4 = true ∧ program.constEntries 4 = [1] ∧ program.isConstant 5 = true ∧ program.constEntries 5 = [95231] ∧ program.valueField 0 = 0 ∧ program.valueField 1 = 0 ∧ program.valueField 2 = 0 ∧ program.valueField 3 = 0 ∧ program.valueField 4 = 0 ∧ program.valueField 5 = 0 :=
  MldsaAAlgebra.constsU

/-- **A constant of `A`** reads its entry, cast. -/
theorem rdA_const (e : program.Env interp) {v : ℕ} (hc : program.isConstant v = true)
    (hf : program.valueField v = 0) (i : ℕ) :
    rdA e v i = (((program.constEntries v).getD i 0 : ℕ) : (interp 0).K) := by
  unfold rdA
  rw [RealizedProgram.evalE_leaf_of_isConstant e hc, RealizedProgram.constRead_of_valueField hf, decode_fq6]

/-- The zero constant of `A` (value `0`) reads `0`. -/
theorem rdA_0 (e : program.Env interp) (i : ℕ) : rdA e 0 i = 0 := by
  rw [rdA_const e (constsU (program := program)).1 (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.1, (constsU (program := program)).2.1]
  have h0 : (List.replicate 1024 (0 : ℕ)).getD i 0 = 0 := by
    rw [List.getD_eq_getElem?_getD]
    rcases lt_or_ge i 1024 with h | h
    · rw [List.getElem?_replicate, if_pos h, Option.getD_some]
    · rw [List.getElem?_eq_none (by rw [List.length_replicate]; exact h), Option.getD_none]
  rw [h0, Nat.cast_zero]

/-- The constant `M − 1 = 43` (value `1`) reads its bits. -/
theorem rdA_1 (e : program.Env interp) {t : ℕ} (ht : t < 6) :
    rdA e 1 t = Bits.constBit 43 t := by
  rw [rdA_const e (constsU (program := program)).2.2.1 (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.1, (constsU (program := program)).2.2.2.1]
  interval_cases t <;> simp [Bits.constBit]

/-- The constant `1` (value `2`) reads `1`. -/
theorem rdA_2 (e : program.Env interp) {i : ℕ} (hi : i < 1024) : rdA e 2 i = 1 := by
  rw [rdA_const e (constsU (program := program)).2.2.2.2.1 (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, (constsU (program := program)).2.2.2.2.2.1,
    List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hi, Option.getD_some, Nat.cast_one]

/-- The constant `0` (value `3`) reads the bits of `0`. -/
theorem rdA_3 (e : program.Env interp) {t : ℕ} (ht : t < 6) :
    rdA e 3 t = Bits.constBit 0 t := by
  rw [rdA_const e (constsU (program := program)).2.2.2.2.2.2.1 (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    (constsU (program := program)).2.2.2.2.2.2.2.1]
  interval_cases t <;> simp [Bits.constBit]

/-- The constant `1` (value `4`) reads `1`. -/
theorem rdA_4 (e : program.Env interp) : rdA e 4 0 = 1 := by
  rw [rdA_const e (constsU (program := program)).2.2.2.2.2.2.2.2.1 (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    (constsU (program := program)).2.2.2.2.2.2.2.2.2.1]
  simp

/-! The index maps of UseHint. -/

theorem idx8_eq : idx8 = List.replicate 1024 (0, 1, 6) := by decide +kernel
theorem idx8_entry {m t : ℕ} (hm : m < 1024) (ht : t < 6) : idx8.entry (m * 6 + t) = t := by
  rw [idx8_eq, RealizedProgram.IndexMap.entry_replicate (by omega)]
  omega
theorem idx9_eq : idx9 = [(0, 0, 1024)] := by decide +kernel
theorem idx9_entry {m : ℕ} (hm : m < 1024) : idx9.entry m = 0 := by
  rw [idx9_eq, RealizedProgram.IndexMap.entry_step_zero hm]
theorem refsA : 6 < program.exprs.length :=
  MldsaAAlgebra.refsA

/-! ## UseHint -/

/-- **The UseHint output bits of coefficient `m`** (`hint.w1`, bits `6 m, …, 6 m + 5`). -/
def bitsA (e : program.Env interp) (m : ℕ) : BitWires (interp 0).K 6 :=
  fun b => rdA e 63 (6 * m + b)

/-- The output bits are bits. -/
theorem bitsA_bool {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    AllBool (bitsA e m) := fun b => w1Bool hs (by have := b.isLt; omega)

/-- **`down = h · s`** (the shared expression `2`). -/
theorem evalE_ref2 (e : program.Env interp) (m : ℕ) :
    program.evalE (program.reader e) 0 (.ref 2) m = rdA e 59 m * rdA e 64 m := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsA (program := program)); omega), (expr2 (program := program))]
  rfl

/-- **The word of the output bits against a constant's bits**: `Logic::eq` reads the output's
bits and the constant's. -/
theorem evalE_eqWord (e : program.Env interp) {m : ℕ} (hm : m < 1024) (hs : program.SourceSatAt e)
    {v c : ℕ} (hc : c < 64) (hv : ∀ t < 6, rdA e v t = Bits.constBit c t) :
    program.evalE (program.reader e) 0 (.logic .eq 6 [.leaf 63, .reindex idx8 (.leaf v)]) m =
      Bits.eqConst (bitsA e m) c := by
  rw [RealizedProgram.evalE_logic]
  simp only [RealizedProgram.LogicOp.eval, List.headD_cons, List.getD_cons_succ, List.getD_cons_zero,
    RealizedProgram.evalE_reindex]
  rw [RealizedProgram.Ops.eqWord, RealizedProgram.Ops.eqReduce_congr 6 0 (a' := fun t => rdA e 63 (6 * m + t))
    (b' := fun t => Bits.constBit c t)
    (fun t _ => by rw [Nat.mul_comm]; rfl)
    (fun t ht => by simp only [Nat.zero_add]; rw [idx8_entry hm ht]; exact hv t ht), ← RealizedProgram.Ops.eqWord]
  exact RealizedProgram.Ops.eqWord_eq_eqConst (fun t ht => w1Bool hs (by omega)) hc

/-- **`[y = 0]`** (the shared expression `4`). -/
theorem evalE_ref4 {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    program.evalE (program.reader e) 0 (.ref 4) m = Bits.eqConst (bitsA e m) 0 := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsA (program := program)); omega), (expr4 (program := program))]
  exact evalE_eqWord e hm hs (by decide) fun t ht => rdA_3 e ht

/-- **`h s [y = M − 1]`** (the shared expression `5`). -/
theorem evalE_ref5 {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    program.evalE (program.reader e) 0 (.ref 5) m =
      rdA e 59 m * rdA e 64 m * Bits.eqConst (bitsA e m) 43 := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsA (program := program)); omega), (expr5 (program := program)), RealizedProgram.evalE_mul,
    evalE_ref2, evalE_eqWord e hm hs (by decide) fun t ht => rdA_1 e ht]

/-- The constant `q − 1` of `F_q^6` is `−1`. -/
theorem qm1 : ((8380416 : ℕ) : (interp 0).K) = -1 := by
  rw [eq_neg_iff_add_eq_zero, show ((8380416 : ℕ) : (interp 0).K) + 1 = ((8380417 : ℕ) :
    (interp 0).K) by push_cast; ring]
  exact CharP.cast_eq_zero _ 8380417

/-- **The endpoint** (the shared expression `6`): `(s − h s) [y = 0] + h s [y = M − 1]`. -/
theorem evalE_ref6 {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    program.evalE (program.reader e) 0 (.ref 6) m =
      UseHint.endpoint (rdA e 59 m) (rdA e 64 m)
        (UseHint.outputFromBits (UseHint.hiCount mldsa44.γ₂) (bitsA e m)) := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (refsA (program := program)), (expr6 (program := program))]
  rw [RealizedProgram.evalE_add, RealizedProgram.evalE_mul, RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const,
    evalE_ref2, evalE_ref4 hs hm, evalE_ref5 hs hm, decode_fq6, qm1]
  have hM : UseHint.hiCount mldsa44.γ₂ - 1 = 43 := by decide
  simp only [UseHint.endpoint, UseHint.outputFromBits, hM]
  unfold rdA
  ring

/-- **`up = h − h s`** (the shared expression `3`). -/
theorem evalE_ref3 (e : program.Env interp) (m : ℕ) :
    program.evalE (program.reader e) 0 (.ref 3) m = rdA e 59 m - rdA e 59 m * rdA e 64 m := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsA (program := program)); omega), (expr3 (program := program)), RealizedProgram.evalE_add,
    RealizedProgram.evalE_scale_const, evalE_ref2, decode_fq6, qm1]
  unfold rdA
  ring

/-- The lengths of UseHint's predicates. -/
theorem lensU : program.exprLen (.logic .leq 6 [.leaf 63, .reindex idx8 (.leaf 1)]) = 1024 ∧ program.exprLen (.leaf 61) = 1024 ∧ program.exprLen (.leaf 65) = 1024 :=
  MldsaAAlgebra.lensU

/-- **`hint.w1_bound`**: the output is at most `M − 1 = 43`. -/
theorem w1Bound {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    Bits.leConst (bitsA e m) (UseHint.hiCount mldsa44.γ₂ - 1) = 1 := by
  have h := holdsA hs (p := 1) (by simp)
  rw [(pred1 (program := program))] at h
  have hm' := h m (by rw [(lensU (program := program)).1]; exact hm)
  change program.evalE (program.reader e) (program.domainField 0) _ m =
    program.evalE (program.reader e) (program.domainField 0) _ m at hm'
  rw [(lensA (program := program)).2.2.2.2.2.2.2.2, RealizedProgram.evalE_logic] at hm'
  change _ = rdA e 2 m at hm'
  rw [rdA_2 e hm] at hm'
  simp only [RealizedProgram.LogicOp.eval, List.headD_cons, List.getD_cons_succ, List.getD_cons_zero,
    RealizedProgram.evalE_reindex] at hm'
  rw [RealizedProgram.Ops.leqWord, RealizedProgram.Ops.ltWord, RealizedProgram.Ops.ltReduce_congr 6 0 (a' := fun t => Bits.constBit 43 t)
    (b' := fun t => rdA e 63 (6 * m + t))
    (fun t ht => by simp only [Nat.zero_add]; rw [idx8_entry hm ht]; exact rdA_1 e ht)
    (fun t _ => by rw [Nat.mul_comm]; rfl), ← RealizedProgram.Ops.ltWord, ← RealizedProgram.Ops.leqWord,
    RealizedProgram.Ops.leqWord_eq_leConst (fun t ht => w1Bool hs (by omega)) (by decide)] at hm'
  have hM : UseHint.hiCount mldsa44.γ₂ - 1 = 43 := by decide
  rw [hM]
  exact hm'

/-- **A constant multiple in `A`**: the constant cast times the coordinate. -/
theorem evalE_scaleA (rd : program.Valuation interp) (c : ℕ) (x : RealizedProgram.Expr) (i : ℕ) :
    program.evalE rd 0 (.scale (.const c) x) i = (c : (interp 0).K) * program.evalE rd 0 x i := by
  rw [RealizedProgram.evalE_scale_const, decode_fq6]

/-- **The multiple by `q − 1` in `A`** is the negation. -/
theorem evalE_negA (rd : program.Valuation interp) (x : RealizedProgram.Expr) (i : ℕ) :
    program.evalE rd 0 (.scale (.const 8380416) x) i = -program.evalE rd 0 x i := by
  rw [evalE_scaleA, qm1, neg_one_mul]

/-- **The UseHint output** (the batched `fromDigits 6 2` of `hint.w1`) is the sum of its bits'
powers of two. -/
theorem evalE_outputValue (e : program.Env interp) (m : ℕ) :
    program.evalE (program.reader e) 0 (.apply (.batched 1024 (.fromDigits 6 2)) (.leaf 63)) m =
      ∑ b : Fin 6, (2 : (interp 0).K) ^ (b : ℕ) * bitsA e m b := by
  rw [RealizedProgram.evalE_apply_batched_fromDigits (hb := by norm_num)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [decode_fq6, Nat.cast_ofNat, Nat.mul_comm]
  rfl

/-- **`hint.decompose`**: `w' = 2 γ₂ raw_high + lower + offset`. -/
theorem decompose {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    rdA e 61 m = UseHint.relationResult mldsa44.γ₂ (UseHint.hiCount mldsa44.γ₂) (rdA e 59 m)
      (rdA e 64 m) (rdA e 65 m) (UseHint.outputFromBits (UseHint.hiCount mldsa44.γ₂) (bitsA e m)) := by
  have h := holdsA hs (p := 2) (by simp)
  rw [(pred2 (program := program))] at h
  have hm' := h m (by
    simp only [RealizedProgram.exprLen_add]
    rw [(lensU (program := program)).2.1]
    exact hm)
  change program.evalE (program.reader e) (program.domainField 0) _ m =
    program.evalE (program.reader e) (program.domainField 0) _ m at hm'
  rw [(lensA (program := program)).2.2.2.2.2.2.2.2] at hm'
  simp only [RealizedProgram.evalE_add, ↓evalE_negA, evalE_scaleA, RealizedProgram.evalE_mul,
    RealizedProgram.evalE_reindex, evalE_outputValue,
    evalE_ref2, evalE_ref3, evalE_ref4 hs hm, evalE_ref5 hs hm, evalE_ref6 hs hm,
    idx9_entry hm] at hm'
  change _ = rdA e 0 m at hm'
  rw [rdA_0] at hm'
  have hM' : UseHint.hiCount 95232 = 44 := by decide
  have hγ : mldsa44.γ₂ = 95232 := rfl
  simp only [UseHint.relationResult, UseHint.rawHigh, UseHint.lower, UseHint.outputFromBits,
    UseHint.endpoint, hM', hγ, Nat.cast_ofNat] at hm' ⊢
  have h4 : rdA e 4 0 = 1 := rdA_4 e
  unfold rdA at h4 hm' ⊢
  rw [h4] at hm'
  push_cast at hm' ⊢
  linear_combination hm'

/-! ### The interval row, on the integers -/

/-- **An integer `mod_q` with `q = 0`** is an integer equality at every coordinate. -/
theorem eq_of_modZero {rd : program.Valuation interp} {d : ℕ} {l r : RealizedProgram.Expr} {real : RealizedProgram.ModRealization}
    (h : program.HoldsWith rd (.mod d 0 l r real)) {i : ℕ} (hi : i < program.exprLen l) :
    program.evalIntWith rd d l i = program.evalIntWith rd d r i := by
  have := h i hi
  rwa [Nat.cast_zero, zero_dvd_iff, sub_eq_zero] at this

/-- The characteristic of `F_q^6` as the program reads it. -/
theorem fq6_char : (interp 0).spec.characteristic = 8380417 := QField.char_spec

/-- **A small constant's centred reading** is itself. -/
theorem centered_small {c : ℕ} (hc : 2 * c < 8380417) : (interp 0).centered c = c := by
  unfold RealizedProgram.FieldInterp.centered
  rw [fq6_char, if_pos hc]

/-- **`q − 1`'s centred reading** is `−1`. -/
theorem centered_qm1 : (interp 0).centered 8380416 = -1 := by
  unfold RealizedProgram.FieldInterp.centered
  rw [fq6_char, if_neg (by decide)]
  norm_num

/-- The values UseHint reads are not constants, of field `0`. -/
theorem valsU : program.isConstant 59 = false ∧ program.isConstant 63 = false ∧ program.isConstant 64 = false ∧ program.isConstant 65 = false ∧ program.isConstant 66 = false ∧ program.valueField 59 = 0 ∧ program.valueField 63 = 0 ∧ program.valueField 64 = 0 ∧ program.valueField 65 = 0 ∧ program.valueField 66 = 0 :=
  MldsaAAlgebra.valsU

/-- **A constant's integer reading** where its entry is small. -/
theorem intOf_constA (rd : program.Valuation interp) {v : ℕ} (hc : program.isConstant v = true)
    (hf : program.valueField v = 0) {i : ℕ} (hs : 2 * (program.constEntries v).getD i 0 < 8380417) :
    program.intOf rd v i = ((program.constEntries v).getD i 0 : ℕ) := by
  rw [RealizedProgram.intOf_of_constant rd (RealizedProgram.kind_of_isConstant hc), hf, centered_small hs]

/-- **`down`'s integer reading casts to `h s`.** -/
theorem cast_evalIntWith_ref2 {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ}
    (hm : m < 1024) :
    ((program.evalIntWith (program.reader e) 0 (.ref 2) m : ℤ) : (interp 0).K) =
      rdA e 59 m * rdA e 64 m := by
  rw [RealizedProgram.evalIntWith_ref MldsaHCross.refsOrdered _ _ (by have := (refsA (program := program)); omega), (expr2 (program := program)),
    RealizedProgram.evalIntWith_mul, RealizedProgram.evalIntWith_leaf, RealizedProgram.evalIntWith_leaf, Int.cast_mul,
    cast_intOf (valsU (program := program)).1 (valsU (program := program)).2.2.2.2.2.1 (mem_prime_of_bool (hBool hs hm)),
    cast_intOf (valsU (program := program)).2.2.1 (valsU (program := program)).2.2.2.2.2.2.2.1 (mem_prime_of_bool (npBool hs hm))]

/-- **The output bits against a constant's bits, on the integers**, cast: `Logic::eq` on the
integer readings casts to `Bits.eqConst`. -/
theorem cast_evalIntWith_eqWord {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ}
    (hm : m < 1024) {v c : ℕ} (hc : c < 64) (hvc : program.isConstant v = true)
    (hvf : program.valueField v = 0)
    (hv : ∀ t < 6, 2 * (program.constEntries v).getD t 0 < 8380417 ∧
      (((program.constEntries v).getD t 0 : ℕ) : (interp 0).K) = Bits.constBit c t) :
    ((program.evalIntWith (program.reader e) 0
        (.logic .eq 6 [.leaf 63, .reindex idx8 (.leaf v)]) m : ℤ) : (interp 0).K) =
      Bits.eqConst (bitsA e m) c := by
  rw [RealizedProgram.evalIntWith_logic]
  simp only [RealizedProgram.LogicOp.eval, List.headD_cons, List.getD_cons_succ, List.getD_cons_zero,
    RealizedProgram.evalIntWith_reindex, RealizedProgram.evalIntWith_leaf]
  rw [RealizedProgram.Ops.eqWord, ← eq_intCast (Int.castRingHom (interp 0).K), RealizedProgram.Ops.eqReduce_map,
    RealizedProgram.Ops.eqReduce_congr 6 0 (a' := fun t => rdA e 63 (6 * m + t))
    (b' := fun t => Bits.constBit c t)
    (fun t ht => by
      simp only [Nat.zero_add, eq_intCast]
      rw [Nat.mul_comm]
      exact cast_intOf (valsU (program := program)).2.1 (valsU (program := program)).2.2.2.2.2.2.1 (mem_prime_of_bool (w1Bool hs (by omega))))
    (fun t ht => by
      simp only [Nat.zero_add, eq_intCast]
      rw [idx8_entry hm ht, intOf_constA _ hvc hvf (hv t ht).1, Int.cast_natCast]
      exact (hv t ht).2), ← RealizedProgram.Ops.eqWord]
  exact RealizedProgram.Ops.eqWord_eq_eqConst (fun t ht => w1Bool hs (by omega)) hc

/-- **The endpoint's integer reading casts to the endpoint.** -/
theorem cast_evalIntWith_ref6 {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ}
    (hm : m < 1024) :
    ((program.evalIntWith (program.reader e) 0 (.ref 6) m : ℤ) : (interp 0).K) =
      UseHint.endpoint (rdA e 59 m) (rdA e 64 m)
        (UseHint.outputFromBits (UseHint.hiCount mldsa44.γ₂) (bitsA e m)) := by
  have h3 : ∀ t < 6, 2 * (program.constEntries 3).getD t 0 < 8380417 ∧
      (((program.constEntries 3).getD t 0 : ℕ) : (interp 0).K) = Bits.constBit 0 t := fun t ht => by
    rw [(constsU (program := program)).2.2.2.2.2.2.2.1]
    interval_cases t <;> simp [Bits.constBit]
  have h1 : ∀ t < 6, 2 * (program.constEntries 1).getD t 0 < 8380417 ∧
      (((program.constEntries 1).getD t 0 : ℕ) : (interp 0).K) = Bits.constBit 43 t := fun t ht => by
    rw [(constsU (program := program)).2.2.2.1]
    interval_cases t <;> simp [Bits.constBit]
  rw [RealizedProgram.evalIntWith_ref (k := 6) MldsaHCross.refsOrdered _ _ (refsA (program := program)), (expr6 (program := program)), RealizedProgram.evalIntWith_add,
    RealizedProgram.evalIntWith_mul, RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_scale_const,
    RealizedProgram.evalIntWith_leaf, (lensA (program := program)).2.2.2.2.2.2.2.2, centered_qm1,
    RealizedProgram.evalIntWith_ref (k := 4) MldsaHCross.refsOrdered _ _ (by have := (refsA (program := program)); omega), (expr4 (program := program)),
    RealizedProgram.evalIntWith_ref (k := 5) MldsaHCross.refsOrdered _ _ (by have := (refsA (program := program)); omega), (expr5 (program := program)),
    RealizedProgram.evalIntWith_mul]
  push_cast
  rw [cast_evalIntWith_ref2 hs hm,
    cast_evalIntWith_eqWord hs hm (by decide) (constsU (program := program)).2.2.2.2.2.2.1 (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h3,
    cast_evalIntWith_eqWord hs hm (by decide) (constsU (program := program)).2.2.1 (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.1 h1,
    cast_intOf (valsU (program := program)).2.2.1 (valsU (program := program)).2.2.2.2.2.2.2.1 (mem_prime_of_bool (npBool hs hm))]
  have hM : UseHint.hiCount mldsa44.γ₂ - 1 = 43 := by decide
  simp only [UseHint.endpoint, UseHint.outputFromBits, hM]
  ring

/-- **`hint.interval`**: `offset + slack = (γ₂ − 1) + endpoint`, the integer equation cast to the
field. -/
theorem interval {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    UseHint.IntervalEq mldsa44.γ₂ (rdA e 59 m) (rdA e 64 m) (rdA e 65 m) (rdA e 66 m)
      (UseHint.outputFromBits (UseHint.hiCount mldsa44.γ₂) (bitsA e m)) := by
  have h := holdsA hs (p := 3) (by simp)
  rw [(pred3 (program := program))] at h
  have hm' := congrArg (Int.cast : ℤ → (interp 0).K) (eq_of_modZero h (i := m) (by
    rw [RealizedProgram.exprLen_add, (lensU (program := program)).2.2]
    exact hm))
  obtain ⟨ko, hko, hov⟩ := offset_range hs hm
  obtain ⟨ks, hks, hsv⟩ := slack_range hs hm
  have hp : ∀ k : ℕ, ((k : ℕ) : (interp 0).K) ∈ (interp 0).node "GF(p^1)" := fun k => by
    rw [QField.node_prime]
    exact natCast_mem (RelativePacking.fixedField (interp 0).K 8380417 1).toSubring k
  rw [RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_leaf,
    RealizedProgram.evalIntWith_leaf, RealizedProgram.evalIntWith_reindex, RealizedProgram.evalIntWith_leaf, idx9_entry hm,
    intOf_constA _ (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.1 (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      (by rw [(constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.1]; decide)] at hm'
  push_cast at hm'
  rw [cast_intOf (valsU (program := program)).2.2.2.1 (valsU (program := program)).2.2.2.2.2.2.2.2.1 (hov ▸ hp ko),
    cast_intOf (valsU (program := program)).2.2.2.2.1 (valsU (program := program)).2.2.2.2.2.2.2.2.2 (hsv ▸ hp ks), cast_evalIntWith_ref6 hs hm,
    (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.1] at hm'
  unfold UseHint.IntervalEq
  rw [hm']
  have hγ : mldsa44.γ₂ = 95232 := rfl
  simp only [hγ, List.getD_cons_zero]
  push_cast
  ring

/-! ### UseHint at every coefficient -/

/-- **UseHint's constraints at coefficient `m`** (`Native.UseHintHolds`). -/
theorem useHintHolds {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    Native.UseHintHolds (rdA e 59 m) (rdA e 61 m) (rdA e 64 m) (rdA e 65 m) (rdA e 66 m)
      (bitsA e m) :=
  ⟨w1Bound hs hm, interval hs hm, decompose hs hm⟩

/-- **UseHint at coefficient `m`**: the output is `UseHint(h, w')` (`Native.useHint_sound`). -/
theorem nativeHolds {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    UseHint.NativeHolds mldsa44.γ₂ (rdA e 59 m) (rdA e 61 m) (natOfBits (bitsA e m)) := by
  obtain ⟨ko, hko, hov⟩ := offset_range hs hm
  obtain ⟨ks, hks, hsv⟩ := slack_range hs hm
  exact Native.useHint_sound (useHintHolds hs hm) (hBool hs hm) (npBool hs hm)
    (bitsA_bool hs hm) ⟨ko, hko, hov.symm⟩ ⟨ks, hks, hsv.symm⟩

/-! ### The readings of the frontend -/

/-- The flat index of row `i`, coefficient `k`. -/
theorem flat_lt (i : Fin 4) (k : Fin 256) : (i : ℕ) * 256 + k < 1024 := by omega

/-- **A's `w1` coefficients are the output bits' naturals.** -/
theorem w1Coeff_eq (e : program.Env interp) (i : Fin Rows.nRows)
    (k : Fin Rows.deg) :
    NativeAlgebraCircuit.w1Coeff (w1ABits (program.reader e)) i k = natOfBits (bitsA e ((i : ℕ) * 256 + k)) := by
  unfold NativeAlgebraCircuit.w1Coeff NativeAlgebraCircuit.outputBits
  refine congrArg natOfBits (funext fun b => ?_)
  have hidx : mldsa44.r1_bits * (finProdFinEquiv (i, k) : ℕ) + (b : ℕ) =
      6 * ((i : ℕ) * 256 + k) + b := by
    rw [finProdFinEquiv_apply_val]
    change 6 * ((k : ℕ) + 256 * i) + b = _
    ring
  change program.evalE (program.reader e) 0 (.leaf 63)
    (mldsa44.r1_bits * (finProdFinEquiv (i, k) : ℕ) + b) = rdA e 63 (6 * ((i : ℕ) * 256 + k) + b)
  rw [hidx]
  rfl

/-- The extracted `w'`'s coefficients. -/
theorem coeff_wOf (rd : program.Valuation interp) (i : Fin _root_.MLDSA.mldsa44.k)
    (k : Fin _root_.MLDSA.ringDegree) :
    MLDSA44.coeff ((wOf rd).get i) k = NativeAlgebraCircuit.coeffRep (wVals rd i k) := by
  unfold wOf
  erw [Vector.get_ofFn, MLDSA44.coeff_ofCoeff]

/-- The extracted `z`'s coefficients. -/
theorem coeff_zOf (rd : program.Valuation interp) (j : Fin _root_.MLDSA.mldsa44.l)
    (k : Fin _root_.MLDSA.ringDegree) :
    MLDSA44.coeff ((zOf rd).get j) k = NativeAlgebraCircuit.coeffRep (zVals rd j k) := by
  unfold zOf
  erw [Vector.get_ofFn, MLDSA44.coeff_ofCoeff]

/-- **`w'` is the cast of an integer** at every coefficient (UseHint's soundness). -/
theorem w_int {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    ∃ n : ℤ, (n : (interp 0).K) = rdA e 61 m :=
  (nativeHolds hs hm).exists_int

/-- **`w1 = UseHint(h, w')`** coefficientwise. -/
theorem useHint_eq {e : program.Env interp} (hs : program.SourceSatAt e)
    (i : Fin Rows.nRows) (k : Fin Rows.deg) :
    NativeAlgebraCircuit.w1Coeff (w1ABits (program.reader e)) i k =
      _root_.MLDSA.Concrete.useHintCoeff (NativeAlgebraCircuit.decodeHint (hVals (program.reader e)) i k)
        (MLDSA44.coeff ((wOf (program.reader e)).get i) k) mldsa44.γ₂ := by
  have hm := flat_lt i k
  obtain ⟨n, hn⟩ := w_int hs hm
  have h := (nativeHolds hs hm).useHint (NativeAlgebraCircuit.natRep (rdA e 61 ((i : ℕ) * 256 + k)) : ℤ)
    (by rw [Int.cast_natCast]; exact NativeAlgebraCircuit.natRep_cast hn)
  rw [Int.cast_natCast] at h
  rw [w1Coeff_eq, coeff_wOf]
  exact h.symm

/-- **`z` is the cast of a small integer**: `norm.z` puts `z + 130993` below `261987`. -/
theorem z_int {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    ∃ n : ℤ, n.natAbs < mldsa44.normBound ∧ (n : (interp 0).K) = rdA e 58 m := by
  obtain ⟨k, hk, hkv⟩ := norm_range hs hm
  refine ⟨(k : ℤ) - 130993, ?_, ?_⟩
  · change ((k : ℤ) - 130993).natAbs < 130994
    omega
  · push_cast
    rw [← hkv]
    push_cast
    ring

/-- **`‖z‖∞ < γ₁ − β`.** -/
theorem norm_lt {e : program.Env interp} (hs : program.SourceSatAt e) (j : Fin _root_.MLDSA.mldsa44.l)
    (k : Fin _root_.MLDSA.ringDegree) :
    (LatticeCrypto.centeredRepr (MLDSA44.coeff ((zOf (program.reader e)).get j) k)).natAbs <
      mldsa44.normBound := by
  obtain ⟨n, hlt, hn⟩ := z_int hs (flat_lt j k)
  rw [coeff_zOf]
  erw [NativeAlgebraCircuit.coeffRep_eq_intCast hn,
    LatticeCrypto.centeredRepr_intCast_eq_of_natAbs_le n hlt.le (by decide)]
  exact hlt

/-- **The hint weight is at most `ω`** (`hint_weight.weight`: the hint's sum below `81`). -/
theorem hintWeight_le {e : program.Env interp} (hs : program.SourceSatAt e) :
    (Finset.univ.filter fun ik : Fin Rows.nRows × Fin Rows.deg =>
      NativeAlgebraCircuit.decodeHint (hVals (program.reader e)) ik.1 ik.2 = true).card ≤ mldsa44.ω := by
  obtain ⟨k, hk, hkv⟩ := weight_range hs
  have hbool : ∀ t : Fin 1024, rdA e 59 t = 0 ∨ rdA e 59 t = 1 := fun t => hBool hs t.isLt
  rw [HintWeight.sum_eq_card hbool] at hkv
  set c := (Finset.univ.filter fun t : Fin 1024 => rdA e 59 t = 1).card
  have hc : c ≤ 1024 := (Finset.card_filter_le _ _).trans (by simp)
  have heq : c = k := IntLift.natCast_inj_of_lt (K := (interp 0).K) (p := 8380417) (by omega)
    (by omega) hkv
  have hcle : c ≤ mldsa44.ω := by
    change c ≤ 80
    omega
  let eqv : Fin Rows.nRows × Fin Rows.deg ≃ Fin 1024 := finProdFinEquiv
  refine le_of_eq_of_le (Finset.card_equiv eqv fun ik => ?_) hcle
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, NativeAlgebraCircuit.decodeHint, decide_eq_true_eq]
  change rdA e 59 ((ik.1 : ℕ) * 256 + ik.2) = 1 ↔ rdA e 59 (finProdFinEquiv ik : ℕ) = 1
  rw [finProdFinEquiv_apply_val]
  change rdA e 59 ((ik.1 : ℕ) * 256 + ik.2) = 1 ↔ rdA e 59 ((ik.2 : ℕ) + 256 * ik.1) = 1
  rw [show (ik.1 : ℕ) * 256 + ik.2 = ik.2 + 256 * ik.1 by ring]

/-! ## The signature relation

`signature.relation` is the field equation `w' − Â z + 2^d t1 · support − 2^(d+1) t1 · sign = 0` of
`F_q^6`, `Â` read through the realized program's inverse transform at `ψ = 1753`. The statement's `key.a_hat` and
`key.t1` may have coordinates other than the constant one; `w'`, `z` and the challenge bits lie in
the prime subfield, so the constant coordinate (`coord0`, an `F_q`-linear map) of the equation is
the equation over `ZMod q` of the statement's readings, which `KeyOf` makes the key's. -/

set_option hygiene false in
/-- **The constant coordinate of `F_q^6`** as an additive map to `F_q`. -/
local notation "coord0" => (QField.coord0 (F0 := F0))

set_option hygiene false in
/-- **The prime field `F_q` in `F_q^6`.** -/
local notation "φq" => (ZMod.castHom (dvd_refl _root_.MLDSA.modulus) (interp 0).K :
  _root_.MLDSA.Coeff →+* (interp 0).K)

theorem φq_apply (z : _root_.MLDSA.Coeff) : φq z = ((z.val : ℕ) : (interp 0).K) := by
  change (ZMod.cast z : (interp 0).K) = _
  rw [ZMod.cast_eq_val]

/-- The constant coordinate of a natural's cast. -/
theorem coord0_natCast (n : ℕ) : coord0 (n : (interp 0).K) = n := QField.coord0_natCast n

/-- The constant coordinate of an integer's cast. -/
theorem coord0_intCast (n : ℤ) : coord0 (n : (interp 0).K) = n := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [Int.cast_natCast, Int.cast_natCast, coord0_natCast]
  · rw [Int.cast_neg, Int.cast_natCast, map_neg, coord0_natCast, Int.cast_neg, Int.cast_natCast]

/-- The constant coordinate of an element of `F_q`. -/
theorem coord0_φq (z : _root_.MLDSA.Coeff) : coord0 (φq z) = z := by
  rw [φq_apply, coord0_natCast, ZMod.natCast_zmod_val]

/-- **The constant coordinate is `F_q`-linear.** -/
theorem coord0_φq_mul (z : _root_.MLDSA.Coeff) (y : (interp 0).K) : coord0 (φq z * y) = z * coord0 y := by
  rw [φq_apply, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

/-- The constant coordinate of a product with an element of `F_q`. -/
theorem coord0_mul_prime {x y : (interp 0).K} (hy : φq (coord0 y) = y) :
    coord0 (x * y) = coord0 x * coord0 y := by
  rw [← hy, mul_comm, coord0_φq_mul, coord0_φq, mul_comm]

/-- The integer reading of an element is the value of its constant coordinate. -/
theorem toNat_eq_val (x : (interp 0).K) : (interp 0).toNat x = (coord0 x).val := QField.toNat_eq x

/-- An integer's cast lies in `F_q`. -/
theorem φq_coord0_intCast (n : ℤ) : φq (coord0 (n : (interp 0).K)) = n := by
  rw [coord0_intCast, map_intCast]

/-- A bit lies in `F_q`. -/
theorem φq_coord0_bool {x : (interp 0).K} (hx : x = 0 ∨ x = 1) : φq (coord0 x) = x := by
  rcases hx with rfl | rfl
  · rw [map_zero, map_zero]
  · rw [show (1 : (interp 0).K) = ((1 : ℕ) : (interp 0).K) from Nat.cast_one.symm, coord0_natCast,
      map_natCast]

/-- **The constant coordinate of a bit** is its coefficient. -/
theorem coord0_bool {x : (interp 0).K} (hx : x = 0 ∨ x = 1) :
    coord0 x = Rows.bitCoeff x := by
  unfold Rows.bitCoeff
  rcases hx with rfl | rfl
  · rw [map_zero, if_neg zero_ne_one]
  · rw [if_pos rfl, show (1 : (interp 0).K) = ((1 : ℕ) : (interp 0).K) from Nat.cast_one.symm,
      coord0_natCast, Nat.cast_one]

/-- **The inverse transform commutes with the constant coordinate** at `ψ = 1753`. -/
theorem coord0_inverseNtt (h : ℕ → (interp 0).K) (s : ℕ) :
    coord0 (RealizedProgram.Ops.inverseNtt 256 ((1753 : ℕ) : (interp 0).K) h s) =
      RealizedProgram.Ops.inverseNtt 256 _root_.MLDSA.zeta (fun m => coord0 (h m)) s := by
  have h256 : ((256 : ℕ) : (interp 0).K)⁻¹ = φq ((256 : ℕ) : _root_.MLDSA.Coeff)⁻¹ := by
    rw [map_inv₀, map_natCast]
  have hψ : ((1753 : ℕ) : (interp 0).K)⁻¹ = φq _root_.MLDSA.zeta⁻¹ := by
    rw [map_inv₀, show _root_.MLDSA.zeta = ((1753 : ℕ) : _root_.MLDSA.Coeff) from rfl, map_natCast]
  unfold RealizedProgram.Ops.inverseNtt
  split_ifs with hs
  · rw [h256, hψ, coord0_φq_mul, map_sum]
    have hterm : ∀ (y : (interp 0).K) (k : ℕ),
        coord0 (y * φq _root_.MLDSA.zeta⁻¹ ^ k) = coord0 y * _root_.MLDSA.zeta⁻¹ ^ k := by
      intro y k
      rw [← map_pow, mul_comm, coord0_φq_mul, mul_comm]
    simp only [hterm]
  · exact map_zero _

/-- **The negacyclic convolution with a vector over `F_q` commutes with the constant
coordinate.** -/
theorem coord0_negacyclicConvCoeff {n : ℕ} (h y : Fin n → (interp 0).K)
    (hy : ∀ t, φq (coord0 (y t)) = y t) (k : Fin n) :
    coord0 (LatticeCrypto.negacyclicConvCoeff h y k) =
      LatticeCrypto.negacyclicConvCoeff (fun a => coord0 (h a)) (fun b => coord0 (y b)) k := by
  unfold LatticeCrypto.negacyclicConvCoeff
  rw [map_sum]
  refine Finset.sum_congr rfl fun ij _ => ?_
  split_ifs
  · exact coord0_mul_prime (hy _)
  · rw [map_neg, coord0_mul_prime (hy _)]
  · exact map_zero _

/-- **The statement's `Â` read in the constant coordinate** is the key's `Â`. -/
theorem coord0_aHat {e : program.Env interp} {pk : MLDSA44.PublicKey44} (hk : KeyOf pk e.stmt)
    (i : Fin _root_.MLDSA.mldsa44.k) (l : Fin _root_.MLDSA.mldsa44.l) (s : Fin 256) :
    coord0 (RealizedProgram.castElt (program.reader e 56 (((i : ℕ) * 4 + l) * 256 + s)) : (interp 0).K) =
      (((Rows.aHat pk).get i).get l).coeffs.get s := by
  rw [RealizedProgram.reader_of_opaque_nil e MldsaAAlgebra.kind56]
  have h := hk.aHat i l s
  unfold aHatAt at h
  rw [RealizedProgram.evalE_leaf, toNat_eq_val] at h
  rw [← ZMod.natCast_zmod_val (coord0 _), h, ZMod.natCast_zmod_val]

/-- **The statement's `t1` read in the constant coordinate** is the key's `t1`. -/
theorem coord0_t1 {e : program.Env interp} {pk : MLDSA44.PublicKey44} (hk : KeyOf pk e.stmt)
    (i : Fin _root_.MLDSA.mldsa44.k) (s : Fin _root_.MLDSA.ringDegree) :
    coord0 (RealizedProgram.castElt (program.reader e 57 ((i : ℕ) * 256 + s)) : (interp 0).K) =
      (pk.t1.get i).get s := by
  rw [RealizedProgram.reader_of_opaque_nil e MldsaAAlgebra.kind57]
  have h := hk.t1 i s
  unfold t1At at h
  rw [RealizedProgram.evalE_leaf, toNat_eq_val] at h
  rw [← ZMod.natCast_zmod_val (coord0 _), h, ZMod.natCast_zmod_val]

/-- The data of `signature.relation`'s operators. -/
theorem sigData : (program.value 56).size = 4096 ∧ (program.value 57).size = 1024 ∧ program.exprLen (.leaf 61) = 1024 :=
  MldsaAAlgebra.sigData

/-- **`Â z` at coordinate `m`** (`polyMatVec` of `key.a_hat` in NTT form at `ψ = 1753`). -/
theorem evalE_polyMatVec (rd : program.Valuation interp) {m : ℕ} (hm : m < 1024) :
    program.evalE rd 0 (.apply (.polyMatVec 56 4 4 (.ntt 1753)) (.leaf 58)) m =
      ∑ l : Fin _root_.MLDSA.mldsa44.l, RealizedProgram.Ops.negacyclic 256 (RealizedProgram.Ops.inverseNtt 256
        ((1753 : ℕ) : (interp 0).K)
        (fun s => RealizedProgram.castElt (rd 56 ((m / 256 * 4 + l) * 256 + s))))
        (fun s => program.evalE rd 0 (.leaf 58) (l * 256 + s)) (m % 256) := by
  simp only [RealizedProgram.evalE_apply, RealizedProgram.NamedOp.apply, RealizedProgram.NamedOp.block, RealizedProgram.NamedOp.rows, RealizedProgram.NamedOp.cols,
    RealizedProgram.NamedOp.formPoly, (sigData (program := program)).1]
  rw [Nat.div_eq_of_lt (show m < 4 * (4096 / (4 * 4)) by norm_num; exact hm),
    Nat.mod_eq_of_lt (show m < 4 * (4096 / (4 * 4)) by norm_num; exact hm),
    if_pos (show m < 4 * (4096 / (4 * 4)) by norm_num; exact hm)]
  norm_num
  erw [QField.decode_eq (F0 := F0) 1753]
  simp only [Nat.cast_ofNat]
  rfl

/-- **`t1 · x` at coordinate `m`** (`polyBroadcast` of `key.t1` in coefficient form). -/
theorem evalE_polyBroadcast (rd : program.Valuation interp) {m : ℕ} (hm : m < 1024) (x : RealizedProgram.Expr) :
    program.evalE rd 0 (.apply (.polyBroadcast 57 4 .coefficients) x) m =
      RealizedProgram.Ops.negacyclic 256 (fun s => RealizedProgram.castElt (rd 57 (m / 256 * 256 + s)))
        (fun s => program.evalE rd 0 x s) (m % 256) := by
  simp only [RealizedProgram.evalE_apply, RealizedProgram.NamedOp.apply, RealizedProgram.NamedOp.block, RealizedProgram.NamedOp.rows, RealizedProgram.NamedOp.cols,
    RealizedProgram.NamedOp.formPoly, (sigData (program := program)).2.1]
  rw [Nat.div_eq_of_lt hm, Nat.mod_eq_of_lt hm, if_pos (show m < 4 * (1024 / 4) by norm_num; exact hm)]
  norm_num

/-- The constant coordinate of a natural multiple. -/
theorem coord0_natCast_mul (c : ℕ) (y : (interp 0).K) : coord0 ((c : (interp 0).K) * y) = c * coord0 y := by
  rw [← map_natCast φq, coord0_φq_mul]

/-- **A negacyclic convolution at a coordinate below `256`**, over the ring degree. -/
theorem negacyclic_at (h x : ℕ → (interp 0).K) (k : Fin _root_.MLDSA.ringDegree) :
    RealizedProgram.Ops.negacyclic 256 h x k = LatticeCrypto.negacyclicConvCoeff (n := _root_.MLDSA.ringDegree)
      (fun a => h a) (fun a => x a) k := by
  rw [RealizedProgram.Ops.negacyclic, RealizedProgram.Ops.ofFin_of_lt _ (show (k : ℕ) < 256 from k.isLt)]
  rfl

theorem idx6_eq : idx6 = [(0, 2, 256)] := by decide +kernel
theorem idx7_eq : idx7 = [(1, 2, 256)] := by decide +kernel

/-- **The supports read by `signature.relation`** (the shared expression `0`). -/
theorem evalE_ref0 (e : program.Env interp) {s : ℕ} (hs : s < 256) :
    program.evalE (program.reader e) 0 (.ref 0) s = rdA e 60 (2 * s) := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsA (program := program)); omega), (expr0 (program := program)), RealizedProgram.evalE_reindex,
    idx6_eq, RealizedProgram.IndexMap.entry_single hs]
  congr 1
  omega

/-- **The signs read by `signature.relation`** (the shared expression `1`). -/
theorem evalE_ref1 (e : program.Env interp) {s : ℕ} (hs : s < 256) :
    program.evalE (program.reader e) 0 (.ref 1) s = rdA e 60 (2 * s + 1) := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsA (program := program)); omega), (expr1 (program := program)), RealizedProgram.evalE_reindex,
    idx7_eq, RealizedProgram.IndexMap.entry_single hs]
  congr 1
  omega

/-- **The coefficient of a challenge bit** read by `signature.relation`. -/
theorem coord0_chal {e : program.Env interp} (hs : program.SourceSatAt e) (r : ℕ) (hr : r < 2)
    (hx : ∀ s < 256, program.evalE (program.reader e) 0 (.ref r) s = rdA e 60 (2 * s + r))
    (t : Fin _root_.MLDSA.ringDegree) :
    coord0 (program.evalE (program.reader e) 0 (.ref r) t) =
      Rows.bitCoeff (cABits (program.reader e) t ⟨r, hr⟩) := by
  have ht : (t : ℕ) < 256 := t.isLt
  rw [hx t ht, coord0_bool (cBool hs (by omega))]
  rfl

/-- The concrete inverse transform of the NTT ring operations is the vendored `invNTT`. -/
private theorem fromHat_eq (x : _root_.MLDSA.Tq) :
    _root_.MLDSA.Concrete.concreteNTTRingOps.fromHat x = _root_.MLDSA.Concrete.invNTT x := rfl

/-- **The coefficient `k` of row `i` of `w' = computeWApprox(Â, c, z, t1)`**: the constant
coordinate of `signature.relation` at coordinate `256 i + k`. -/
theorem signature_coeff {e : program.Env interp} (hs : program.SourceSatAt e) {pk : MLDSA44.PublicKey44}
    (hk : KeyOf pk e.stmt) (i : Fin _root_.MLDSA.mldsa44.k) (k : Fin _root_.MLDSA.ringDegree) :
    MLDSA44.coeff ((wOf (program.reader e)).get i) k =
      ∑ j : Fin _root_.MLDSA.mldsa44.l, LatticeCrypto.negacyclicConvCoeff
          (MLDSA44.coeff (_root_.MLDSA.Concrete.concreteNTTRingOps.fromHat
            (((Rows.aHat pk).get i).get j)))
          (MLDSA44.coeff ((zOf (program.reader e)).get j)) k -
        LatticeCrypto.negacyclicConvCoeff (MLDSA44.coeff (cPolyA (program.reader e)))
          (fun k' => (2 ^ _root_.MLDSA.droppedBits : _root_.MLDSA.Coeff) *
            MLDSA44.coeff (pk.t1.get i) k') k := by
  have hm := flat_lt i k
  have hdiv : ((i : ℕ) * 256 + k) / 256 = i := by omega
  have hmod : ((i : ℕ) * 256 + k) % 256 = k := by omega
  have h := holdsA hs (p := 0) (by simp)
  rw [(pred0 (program := program))] at h
  have hm' := h ((i : ℕ) * 256 + k) (by
    simp only [RealizedProgram.exprLen_add]
    rw [(sigData (program := program)).2.2]
    exact hm)
  change program.evalE (program.reader e) (program.domainField 0) _ _ =
    program.evalE (program.reader e) (program.domainField 0) _ _ at hm'
  rw [(lensA (program := program)).2.2.2.2.2.2.2.2] at hm'
  simp only [RealizedProgram.evalE_add, ↓evalE_negA, evalE_scaleA, evalE_polyMatVec _ hm,
    evalE_polyBroadcast _ hm, hdiv, hmod] at hm'
  change _ = rdA e 0 _ at hm'
  rw [rdA_0] at hm'
  have hc := congrArg coord0 hm'
  rw [map_zero, map_add, map_add, map_add, map_neg, map_sum, coord0_natCast_mul,
    coord0_natCast_mul] at hc
  -- The prime-subfield operands.
  have hz : ∀ (l : Fin _root_.MLDSA.mldsa44.l) (t : Fin _root_.MLDSA.ringDegree),
      φq (coord0 (program.evalE (program.reader e) 0 (.leaf 58) (l * 256 + t))) =
        program.evalE (program.reader e) 0 (.leaf 58) (l * 256 + t) := fun l t => by
    obtain ⟨n, -, hn⟩ := z_int hs (flat_lt l t)
    change φq (coord0 (rdA e 58 _)) = rdA e 58 _
    rw [← hn, φq_coord0_intCast]
  have hb : ∀ (r : ℕ), r < 2 →
      (∀ s < 256, program.evalE (program.reader e) 0 (.ref r) s = rdA e 60 (2 * s + r)) →
      ∀ t : Fin _root_.MLDSA.ringDegree,
        φq (coord0 (program.evalE (program.reader e) 0 (.ref r) t)) =
          program.evalE (program.reader e) 0 (.ref r) t := fun r hr hx t => by
    have ht : (t : ℕ) < 256 := t.isLt
    rw [hx t ht]
    exact φq_coord0_bool (cBool hs (by omega))
  have hx0 : ∀ s < 256, program.evalE (program.reader e) 0 (.ref 0) s = rdA e 60 (2 * s + 0) :=
    fun s hs' => evalE_ref0 e hs'
  have hx1 : ∀ s < 256, program.evalE (program.reader e) 0 (.ref 1) s = rdA e 60 (2 * s + 1) :=
    fun s hs' => evalE_ref1 e hs'
  simp only [negacyclic_at _ _ k] at hc
  rw [coord0_negacyclicConvCoeff _ _ (hb 0 (by norm_num) hx0),
    coord0_negacyclicConvCoeff _ _ (hb 1 (by norm_num) hx1),
    Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => coord0_negacyclicConvCoeff _ _ (hz l) k] at hc
  -- The key's operands.
  have hA : ∀ l : Fin _root_.MLDSA.mldsa44.l, (fun a : Fin _root_.MLDSA.ringDegree => coord0 (RealizedProgram.Ops.inverseNtt 256
      ((1753 : ℕ) : (interp 0).K)
      (fun s => RealizedProgram.castElt (b := 0) (program.reader e 56 (((i : ℕ) * 4 + l) * 256 + s))) a)) =
      MLDSA44.coeff (_root_.MLDSA.Concrete.concreteNTTRingOps.fromHat
        (((Rows.aHat pk).get i).get l)) := fun l => by
    funext a
    rw [coord0_inverseNtt, RealizedProgram.Ops.inverseNtt_congr
      (y := RealizedProgram.Ops.ofFin fun s : Fin 256 => (((Rows.aHat pk).get i).get l).coeffs.get s)
      (fun s hs' => by rw [RealizedProgram.Ops.ofFin_of_lt _ hs']; exact coord0_aHat hk i l ⟨s, hs'⟩),
      KeyNTT.inverseNtt_spectrum _ a.isLt, fromHat_eq, MLDSA44.coeff_apply]
  have hZ : ∀ l : Fin _root_.MLDSA.mldsa44.l, (fun b : Fin _root_.MLDSA.ringDegree =>
      coord0 (program.evalE (program.reader e) 0 (.leaf 58) (l * 256 + b))) =
      MLDSA44.coeff ((zOf (program.reader e)).get l) := fun l => by
    funext b
    obtain ⟨n, -, hn⟩ := z_int hs (flat_lt l b)
    rw [coeff_zOf]
    change coord0 (rdA e 58 _) = NativeAlgebraCircuit.coeffRep (rdA e 58 _)
    rw [← hn, coord0_intCast, NativeAlgebraCircuit.coeffRep_eq_intCast rfl]
  have hT : (fun a : Fin _root_.MLDSA.ringDegree =>
      coord0 (RealizedProgram.castElt (program.reader e 57 ((i : ℕ) * 256 + a)) : (interp 0).K)) =
      MLDSA44.coeff (pk.t1.get i) := by
    funext a
    rw [coord0_t1 hk i a]
    rfl
  have hC0 : (fun t : Fin _root_.MLDSA.ringDegree =>
      coord0 (program.evalE (program.reader e) 0 (.ref 0) t)) =
      fun t => Rows.bitCoeff (cABits (program.reader e) t 0) :=
    funext (coord0_chal hs 0 (by norm_num) hx0)
  have hC1 : (fun t : Fin _root_.MLDSA.ringDegree =>
      coord0 (program.evalE (program.reader e) 0 (.ref 1) t)) =
      fun t => Rows.bitCoeff (cABits (program.reader e) t 1) :=
    funext (coord0_chal hs 1 (by norm_num) hx1)
  simp only [hA, hZ, hT, hC0, hC1] at hc
  -- `w'`.
  obtain ⟨n, hn⟩ := w_int hs hm
  have hW : coord0 (program.evalE (program.reader e) 0 (.leaf 61) ((i : ℕ) * 256 + k)) =
      MLDSA44.coeff ((wOf (program.reader e)).get i) k := by
    rw [coeff_wOf]
    change coord0 (rdA e 61 _) = NativeAlgebraCircuit.coeffRep (rdA e 61 _)
    rw [← hn, coord0_intCast, NativeAlgebraCircuit.coeffRep_eq_intCast rfl]
  rw [hW] at hc
  -- The challenge term.
  have hcoeffC : MLDSA44.coeff (cPolyA (program.reader e)) = fun t =>
      Rows.bitCoeff (cABits (program.reader e) t 0) -
        2 * Rows.bitCoeff (cABits (program.reader e) t 1) := by
    funext t
    unfold cPolyA
    rw [MLDSA44.coeff_ofCoeff]
  rw [hcoeffC, DFT.negacyclicConvCoeff_ternary
    (fun t => Rows.bitCoeff (cABits (program.reader e) t 0))
    (fun t => Rows.bitCoeff (cABits (program.reader e) t 1))
    (fun k' => MLDSA44.coeff (pk.t1.get i) k') (2 ^ _root_.MLDSA.droppedBits) k,
    Falcon512.negacyclicConvCoeff_comm
      (fun t => Rows.bitCoeff (cABits (program.reader e) t 0)),
    Falcon512.negacyclicConvCoeff_comm
      (fun t => Rows.bitCoeff (cABits (program.reader e) t 1))]
  have h16 : ((8364033 : ℕ) : _root_.MLDSA.Coeff) = -(2 * 2 ^ _root_.MLDSA.droppedBits) := by
    decide
  have h13 : ((8192 : ℕ) : _root_.MLDSA.Coeff) = 2 ^ _root_.MLDSA.droppedBits := by decide
  rw [h16, h13] at hc
  linear_combination hc

/-- **`w' = computeWApprox(Â, c, z, t1)`** at every key whose preprocessing the statement holds,
with `c` A's challenge polynomial (`signature_coeff`, `MLDSA44.coeff_computeWApprox`). -/
theorem algebra_eq {e : program.Env interp} (hs : program.SourceSatAt e) {pk : MLDSA44.PublicKey44}
    (hk : KeyOf pk e.stmt) :
    wOf (program.reader e) = _root_.MLDSA.computeWApprox _root_.MLDSA.mldsa44 Rows.prims
      (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps) (Rows.aHat pk)
      (cPolyA (program.reader e)) (zOf (program.reader e)) pk.t1 := by
  have key : ∀ i : Fin _root_.MLDSA.mldsa44.k, (wOf (program.reader e)).get i =
      (_root_.MLDSA.computeWApprox _root_.MLDSA.mldsa44 Rows.prims
        (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps) (Rows.aHat pk)
        (cPolyA (program.reader e)) (zOf (program.reader e)) pk.t1).get i := fun i => by
    refine (MLDSA44.ofCoeff_coeff _).symm.trans (Eq.trans ?_ (MLDSA44.ofCoeff_coeff _))
    refine congrArg MLDSA44.ofCoeff (funext fun k => ?_)
    rw [signature_coeff hs hk i k, MLDSA44.coeff_computeWApprox]
  apply Vector.ext
  intro i hi
  simpa [Vector.get_eq_getElem] using key ⟨i, hi⟩

/-! ## Domain `A`'s obligation -/

/-- **Domain `A`'s obligation of the frontend** (`AlgebraSound`): wherever the source program holds
and at every key whose preprocessing the statement holds, the readings of domain `A` satisfy
`AlgebraAt`: the challenge and UseHint output bits are bits (`challenge.c.boolean`,
`hint.w1.boolean`), `w' = computeWApprox(Â, c, z, t1)` (`algebra_eq`, `signature.relation`),
`w1 = UseHint(h, w')` (`useHint_eq`: `hint.*`), `‖z‖∞ < γ₁ − β` (`norm_lt`, `norm.z`) and the hint
weight at most `ω` (`hintWeight_le`, `hint_weight.weight`). -/
theorem algebraSound : AlgebraSound (program := program) (F0 := F0) (FH := FH) := by
  intro e hs pk hk
  refine ⟨fun k s => ?_, fun t => w1Bool hs t.isLt, algebra_eq hs hk, useHint_eq hs, norm_lt hs,
    hintWeight_le hs⟩
  have hk' : (k : ℕ) < 256 := k.isLt
  have hs' : (s : ℕ) < 2 := s.isLt
  exact cBool hs (by omega)

end GordieHowe.MLDSA44.Native.ROMParams
