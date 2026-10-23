-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Frontend.Algebra
import all LatticeCrypto.MLDSA.Concrete.NTT

@[expose] public section

/-!
# GordieHowe: the source predicates of an ML-DSA program's domain `A` at honest values

The converse of the frontend's algebra view (`GordieHowe/Applications/MLDSA44/Native/ROMParams/Frontend/Algebra.lean`) for a native ML-DSA
program (`MldsaAAlgebra`): where the readings of domain `A` satisfy the facts the frontend reads off
(the bits, the ranges, UseHint's constraints `GordieHowe.MLDSA44.Native.UseHintHolds`, the signature relation),
the predicates `0`–`3`, `6`–`9`, `11`–`14` hold.
-/

namespace GordieHowe

namespace RealizedProgram

variable {ir : RealizedProgram} {I : Interp}

/-- **A matched Boolean check holds** where its value reads bits (the converse of
`bool_of_boolCheck`). -/
theorem holdsWith_of_boolCheck {b : PredBody} {s : BoolCheck} (hs : b.boolCheck? = some s)
    {rd : ir.Valuation I}
    (h : ∀ i < (ir.value s.v).size, ir.evalE rd (ir.domainField s.d) (.leaf s.v) i = 0 ∨
      ir.evalE rd (ir.domainField s.d) (.leaf s.v) i = 1) :
    ir.HoldsWith rd b := by
  obtain ⟨t, rfl⟩ := PredBody.eq_of_boolCheck? hs
  intro i hi
  change ir.evalE rd (ir.domainField s.d) (.mul (.leaf s.v) (.leaf s.v)) i =
    ir.evalE rd (ir.domainField s.d) (.leaf s.v) i
  rw [evalE_mul]
  rcases h i hi with h0 | h1
  · rw [h0, mul_zero]
  · rw [h1, mul_one]

end RealizedProgram

namespace MLDSA44.Native.ROMParams

open Generated.MLDSA44.Native.ROMParams.Program
open GordieHowe.Bits

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaAAlgebra program] {F0 FH : RealizedProgram.FieldInterp} [QField F0]
  [HField FH]

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

variable (e : program.Env interp)

/-- **A type check of `A` holds** where its value reads bits. -/
theorem boolA_of {p v : ℕ} (hc : (program.predicate p).body.boolCheck? = some ⟨0, v⟩)
    (h : ∀ i < (program.value v).size, rdA e v i = 0 ∨ rdA e v i = 1) :
    program.HoldsWith (program.reader e) (program.predicate p).body := by
  refine RealizedProgram.holdsWith_of_boolCheck hc fun i hi => ?_
  have h0 := (lensA (program := program)).2.2.2.2.2.2.2.2
  change program.evalE _ (program.domainField 0) _ i = 0 ∨
    program.evalE _ (program.domainField 0) _ i = 1
  rw [h0]
  exact h i hi

/-- **A range membership of one record holds** where the record reads a natural below the
bound (the converse of `natBelow_of_mem`). -/
theorem mem_of_natBelow {rd : program.Valuation interp} {n : ℕ} {r : RealizedProgram.Expr} {real : RealizedProgram.InRealization}
    (h : ∀ i < program.exprLen r, ∃ k < n, program.evalE rd 0 r i = k) :
    program.HoldsWith rd (.mem 0 [r] (.range n) real) := by
  intro i hi r' hr'
  simp only [List.mem_singleton] at hr'
  subst hr'
  have h0 := MldsaACross.domainField0 (program := program)
  change ∃ k < n, program.evalE rd (program.domainField 0) r' i = k
  rw [h0]
  exact h i hi

/-- **`norm.z` holds** where `z + 130993` is a natural below `261987`. -/
theorem norm11_of (h : ∀ i < 1024, ∃ k : ℕ, k < 261987 ∧
      rdA e 58 i + ((130993 : ℕ) : (interp 0).K) = k) :
    program.HoldsWith (program.reader e) (program.predicate 11).body := by
  rw [(pred11 (program := program))]
  refine mem_of_natBelow fun i hi => ?_
  rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_leaf, (lensA (program := program)).1] at hi
  obtain ⟨k, hk, hkv⟩ := h i hi
  refine ⟨k, hk, ?_⟩
  rw [RealizedProgram.evalE_add]
  change rdA e 58 i + rdA e 62 i = _
  rw [rdA_62 e hi]
  exact hkv

/-- **`hint.offset` holds** where the offset is a natural below `512^2`. -/
theorem offset12_of (h : ∀ i < 1024, ∃ k : ℕ, k < 262144 ∧ rdA e 65 i = k) :
    program.HoldsWith (program.reader e) (program.predicate 12).body := by
  rw [(pred12 (program := program))]
  refine mem_of_natBelow fun i hi => ?_
  rw [RealizedProgram.exprLen_leaf, (lensA (program := program)).2.2.2.2.2.2.1] at hi
  exact h i hi

/-- **`hint.slack` holds** where the slack is a natural below `512^2`. -/
theorem slack13_of (h : ∀ i < 1024, ∃ k : ℕ, k < 262144 ∧ rdA e 66 i = k) :
    program.HoldsWith (program.reader e) (program.predicate 13).body := by
  rw [(pred13 (program := program))]
  refine mem_of_natBelow fun i hi => ?_
  rw [RealizedProgram.exprLen_leaf, (lensA (program := program)).2.2.2.2.2.2.2.1] at hi
  exact h i hi

/-- **`hint_weight.weight` holds** where the hint's sum is a natural below `81`. -/
theorem weight14_of (h : ∃ k : ℕ, k < 81 ∧ ∑ t : Fin 1024, rdA e 59 t = k) :
    program.HoldsWith (program.reader e) (program.predicate 14).body := by
  rw [(pred14 (program := program))]
  refine mem_of_natBelow fun i hi => ?_
  have hlen : program.exprLen (.apply (.sum 1024) (.leaf 59)) = 1 := by
    simp only [RealizedProgram.exprLen, RealizedProgram.Expr.len, (lensA (program := program)).2.1, RealizedProgram.NamedOp.cols,
      RealizedProgram.NamedOp.rows]
  rw [hlen] at hi
  obtain rfl : i = 0 := by omega
  obtain ⟨k, hk, hkv⟩ := h
  refine ⟨k, hk, ?_⟩
  rw [RealizedProgram.evalE_apply_sum]
  simp only [Nat.zero_mul, Nat.zero_add]
  exact hkv

/-- **`hint.w1_bound` holds** where every coefficient's output bits are bits at most `M − 1`. -/
theorem w1bound1_of (hb : ∀ m < 1024, ∀ t < 6, rdA e 63 (6 * m + t) = 0 ∨ rdA e 63 (6 * m + t) = 1)
    (h : ∀ m < 1024, Bits.leConst (bitsA e m) (UseHint.hiCount mldsa44.γ₂ - 1) = 1) :
    program.HoldsWith (program.reader e) (program.predicate 1).body := by
  rw [(pred1 (program := program))]
  intro m hm
  rw [(lensU (program := program)).1] at hm
  change program.evalE (program.reader e) (program.domainField 0) _ m =
    program.evalE (program.reader e) (program.domainField 0) _ m
  rw [(lensA (program := program)).2.2.2.2.2.2.2.2, RealizedProgram.evalE_logic]
  change _ = rdA e 2 m
  rw [rdA_2 e hm]
  simp only [RealizedProgram.LogicOp.eval, List.headD_cons, List.getD_cons_succ, List.getD_cons_zero,
    RealizedProgram.evalE_reindex]
  rw [RealizedProgram.Ops.leqWord, RealizedProgram.Ops.ltWord, RealizedProgram.Ops.ltReduce_congr 6 0 (a' := fun t => Bits.constBit 43 t)
    (b' := fun t => rdA e 63 (6 * m + t))
    (fun t ht => by simp only [Nat.zero_add]; rw [idx8_entry hm ht]; exact rdA_1 e ht)
    (fun t _ => by rw [Nat.mul_comm]; rfl), ← RealizedProgram.Ops.ltWord, ← RealizedProgram.Ops.leqWord,
    RealizedProgram.Ops.leqWord_eq_leConst (fun t ht => hb m hm t ht) (by decide)]
  have hM : UseHint.hiCount mldsa44.γ₂ - 1 = 43 := by decide
  rw [← hM]
  exact h m hm

section UseHint

variable {e} (hb : ∀ m < 1024, ∀ t < 6, rdA e 63 (6 * m + t) = 0 ∨ rdA e 63 (6 * m + t) = 1)
include hb

/-- **The output bits against a constant's bits** (`evalE_eqWord`), at Boolean output bits. -/
theorem evalE_eqWord_of {m : ℕ} (hm : m < 1024) {v c : ℕ} (hc : c < 64)
    (hv : ∀ t < 6, rdA e v t = Bits.constBit c t) :
    program.evalE (program.reader e) 0 (.logic .eq 6 [.leaf 63, .reindex idx8 (.leaf v)]) m =
      Bits.eqConst (bitsA e m) c := by
  rw [RealizedProgram.evalE_logic]
  simp only [RealizedProgram.LogicOp.eval, List.headD_cons, List.getD_cons_succ, List.getD_cons_zero,
    RealizedProgram.evalE_reindex]
  rw [RealizedProgram.Ops.eqWord, RealizedProgram.Ops.eqReduce_congr 6 0 (a' := fun t => rdA e 63 (6 * m + t))
    (b' := fun t => Bits.constBit c t)
    (fun t _ => by rw [Nat.mul_comm]; rfl)
    (fun t ht => by simp only [Nat.zero_add]; rw [idx8_entry hm ht]; exact hv t ht), ← RealizedProgram.Ops.eqWord]
  exact RealizedProgram.Ops.eqWord_eq_eqConst (fun t ht => hb m hm t ht) hc

theorem evalE_ref4_of {m : ℕ} (hm : m < 1024) :
    program.evalE (program.reader e) 0 (.ref 4) m = Bits.eqConst (bitsA e m) 0 := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsA (program := program)); omega),
    (expr4 (program := program))]
  exact evalE_eqWord_of hb hm (by decide) fun t ht => rdA_3 e ht

theorem evalE_ref5_of {m : ℕ} (hm : m < 1024) :
    program.evalE (program.reader e) 0 (.ref 5) m =
      rdA e 59 m * rdA e 64 m * Bits.eqConst (bitsA e m) 43 := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (by have := (refsA (program := program)); omega),
    (expr5 (program := program)), RealizedProgram.evalE_mul, evalE_ref2,
    evalE_eqWord_of hb hm (by decide) fun t ht => rdA_1 e ht]

theorem evalE_ref6_of {m : ℕ} (hm : m < 1024) :
    program.evalE (program.reader e) 0 (.ref 6) m =
      UseHint.endpoint (rdA e 59 m) (rdA e 64 m)
        (UseHint.outputFromBits (UseHint.hiCount mldsa44.γ₂) (bitsA e m)) := by
  rw [RealizedProgram.evalE_ref MldsaHCross.refsOrdered _ _ (refsA (program := program)),
    (expr6 (program := program))]
  rw [RealizedProgram.evalE_add, RealizedProgram.evalE_mul, RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const,
    evalE_ref2, evalE_ref4_of hb hm, evalE_ref5_of hb hm, decode_fq6, qm1]
  have hM : UseHint.hiCount mldsa44.γ₂ - 1 = 43 := by decide
  simp only [UseHint.endpoint, UseHint.outputFromBits, hM]
  unfold rdA
  ring

/-- **`hint.decompose` holds** where `w' = 2 γ₂ raw_high + lower + offset` at every coefficient
(`UseHintHolds.decompose`). -/
theorem decompose2_of (h : ∀ m < 1024, rdA e 61 m = UseHint.relationResult mldsa44.γ₂
      (UseHint.hiCount mldsa44.γ₂) (rdA e 59 m) (rdA e 64 m) (rdA e 65 m)
      (UseHint.outputFromBits (UseHint.hiCount mldsa44.γ₂) (bitsA e m))) :
    program.HoldsWith (program.reader e) (program.predicate 2).body := by
  rw [(pred2 (program := program))]
  intro m hm
  simp only [RealizedProgram.exprLen_add] at hm
  rw [(lensU (program := program)).2.1] at hm
  change program.evalE (program.reader e) (program.domainField 0) _ m =
    program.evalE (program.reader e) (program.domainField 0) _ m
  rw [(lensA (program := program)).2.2.2.2.2.2.2.2]
  simp only [RealizedProgram.evalE_add, ↓evalE_negA, evalE_scaleA, RealizedProgram.evalE_mul,
    RealizedProgram.evalE_reindex, evalE_outputValue,
    evalE_ref2, evalE_ref3, evalE_ref4_of hb hm, evalE_ref5_of hb hm, evalE_ref6_of hb hm,
    idx9_entry hm]
  change _ = rdA e 0 m
  rw [rdA_0]
  have hd := h m hm
  have hM' : UseHint.hiCount 95232 = 44 := by decide
  have hγ : mldsa44.γ₂ = 95232 := rfl
  simp only [UseHint.relationResult, UseHint.rawHigh, UseHint.lower, UseHint.outputFromBits,
    UseHint.endpoint, hM', hγ, Nat.cast_ofNat] at hd ⊢
  have h4 : rdA e 4 0 = 1 := rdA_4 e
  unfold rdA at h4 hd ⊢
  rw [h4]
  push_cast at hd ⊢
  linear_combination hd

end UseHint

/-- **The integer reading of a small natural** of `A` (not a constant): the natural (a bound value
reads it centred, which is itself). -/
theorem intOf_of_rdA {v i k : ℕ} (hc : program.isConstant v = false) (hf : program.valueField v = 0)
    (hk : 2 * k < 8380417) (hv : rdA e v i = k) : program.intOf (program.reader e) v i = k := by
  have hrd : (interp (program.valueField v)).toNat (program.reader e v i) = k := by
    unfold rdA at hv
    rw [RealizedProgram.evalE_leaf] at hv
    revert hv
    generalize program.reader e v i = x
    generalize program.valueField v = a at hf x
    subst hf
    rw [RealizedProgram.castElt_self]
    intro hv
    rw [hv]
    exact QField.toNat_natCast (by omega)
  have hchar : (interp (program.valueField v)).spec.characteristic = 8380417 := by
    rw [hf]
    exact QField.char_spec
  unfold RealizedProgram.intOf
  unfold RealizedProgram.isConstant at hc
  split
  · rename_i es h
    rw [h] at hc
    cases hc
  · rw [hrd]
    unfold RealizedProgram.FieldInterp.centered
    rw [hchar, if_pos hk]
  · rw [hrd]

/-- **The endpoint's integer reading is a bit** at Boolean `h`, `s` and output bits. -/
theorem evalInt_ref6_bool (hb : ∀ m < 1024, ∀ t < 6, rdA e 63 (6 * m + t) = 0 ∨ rdA e 63 (6 * m + t) = 1)
    {m : ℕ} (hm : m < 1024) (h59 : rdA e 59 m = 0 ∨ rdA e 59 m = 1)
    (h64 : rdA e 64 m = 0 ∨ rdA e 64 m = 1) :
    program.evalIntWith (program.reader e) 0 (.ref 6) m = 0 ∨
      program.evalIntWith (program.reader e) 0 (.ref 6) m = 1 := by
  rw [RealizedProgram.evalIntWith_ref (k := 6) MldsaHCross.refsOrdered _ _ (refsA (program := program)),
    (expr6 (program := program)), RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_mul,
    RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_scale_const, RealizedProgram.evalIntWith_leaf,
    (lensA (program := program)).2.2.2.2.2.2.2.2, centered_qm1,
    RealizedProgram.evalIntWith_ref (k := 4) MldsaHCross.refsOrdered _ _ (by have := (refsA (program := program)); omega),
    (expr4 (program := program)),
    RealizedProgram.evalIntWith_ref (k := 5) MldsaHCross.refsOrdered _ _ (by have := (refsA (program := program)); omega),
    (expr5 (program := program)), RealizedProgram.evalIntWith_mul,
    RealizedProgram.evalIntWith_ref (k := 2) MldsaHCross.refsOrdered _ _ (by have := (refsA (program := program)); omega),
    (expr2 (program := program)), RealizedProgram.evalIntWith_mul, RealizedProgram.evalIntWith_leaf,
    RealizedProgram.evalIntWith_leaf]
  have hbit : ∀ {v j : ℕ}, program.isConstant v = false → program.valueField v = 0 →
      (rdA e v j = 0 ∨ rdA e v j = 1) →
      program.intOf (program.reader e) v j = 0 ∨ program.intOf (program.reader e) v j = 1 := by
    intro v j hc hf h
    rcases h with h | h
    · left
      have := intOf_of_rdA e hc hf (k := 0) (by norm_num) (by rw [h]; simp)
      exact_mod_cast this
    · right
      have := intOf_of_rdA e hc hf (k := 1) (by norm_num) (by rw [h]; simp)
      exact_mod_cast this
  have i59 := hbit (valsU (program := program)).1 (valsU (program := program)).2.2.2.2.2.1 h59
  have i64 := hbit (valsU (program := program)).2.2.1 (valsU (program := program)).2.2.2.2.2.2.2.1 h64
  have hW : ∀ {v : ℕ}, (∀ t < 6, program.intOf (program.reader e) v t = 0 ∨
      program.intOf (program.reader e) v t = 1) →
      program.evalIntWith (program.reader e) 0
        (.logic .eq 6 [.leaf 63, .reindex idx8 (.leaf v)]) m = 0 ∨
      program.evalIntWith (program.reader e) 0
        (.logic .eq 6 [.leaf 63, .reindex idx8 (.leaf v)]) m = 1 := by
    intro v hv
    rw [RealizedProgram.evalIntWith_logic]
    simp only [RealizedProgram.LogicOp.eval, List.headD_cons, List.getD_cons_succ, List.getD_cons_zero,
      RealizedProgram.evalIntWith_reindex, RealizedProgram.evalIntWith_leaf]
    refine RealizedProgram.Ops.eqReduce_bool 6 _ (fun t ht => ?_) (fun t ht => ?_)
    · rw [show m * 6 + (0 + t) = 6 * m + t by ring]
      exact hbit (valsU (program := program)).2.1 (valsU (program := program)).2.2.2.2.2.2.1
        (hb m hm t ht)
    · rw [Nat.zero_add, idx8_entry hm ht]
      exact hv t ht
  have h3 : ∀ t < 6, program.intOf (program.reader e) 3 t = 0 ∨
      program.intOf (program.reader e) 3 t = 1 := fun t ht => by
    left
    rw [intOf_constA _ (constsU (program := program)).2.2.2.2.2.2.1
      (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      (by rw [(constsU (program := program)).2.2.2.2.2.2.2.1]; interval_cases t <;> decide),
      (constsU (program := program)).2.2.2.2.2.2.2.1]
    interval_cases t <;> rfl
  have h1 : ∀ t < 6, program.intOf (program.reader e) 1 t = 0 ∨
      program.intOf (program.reader e) 1 t = 1 := fun t ht => by
    rw [intOf_constA _ (constsU (program := program)).2.2.1
      (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.1
      (by rw [(constsU (program := program)).2.2.2.1]; interval_cases t <;> decide),
      (constsU (program := program)).2.2.2.1]
    interval_cases t <;> simp
  rcases hW h3 with w3 | w3 <;> rcases hW h1 with w1 | w1 <;> rw [w3, w1] <;>
    rcases i59 with a | a <;> rcases i64 with b | b <;> rw [a, b] <;> simp

section Interval

variable {e} (hb : ∀ m < 1024, ∀ t < 6, rdA e 63 (6 * m + t) = 0 ∨ rdA e 63 (6 * m + t) = 1)
  {m : ℕ} (hm : m < 1024) (h59 : rdA e 59 m = 0 ∨ rdA e 59 m = 1)
  (h64 : rdA e 64 m = 0 ∨ rdA e 64 m = 1)

include h59 h64 in
theorem cast_evalIntWith_ref2_of :
    ((program.evalIntWith (program.reader e) 0 (.ref 2) m : ℤ) : (interp 0).K) =
      rdA e 59 m * rdA e 64 m := by
  rw [RealizedProgram.evalIntWith_ref MldsaHCross.refsOrdered _ _ (by have := (refsA (program := program)); omega),
    (expr2 (program := program)), RealizedProgram.evalIntWith_mul, RealizedProgram.evalIntWith_leaf,
    RealizedProgram.evalIntWith_leaf, Int.cast_mul,
    cast_intOf (valsU (program := program)).1 (valsU (program := program)).2.2.2.2.2.1
      (mem_prime_of_bool h59),
    cast_intOf (valsU (program := program)).2.2.1 (valsU (program := program)).2.2.2.2.2.2.2.1
      (mem_prime_of_bool h64)]

include hb hm in
theorem cast_evalIntWith_eqWord_of {v c : ℕ} (hc : c < 64) (hvc : program.isConstant v = true)
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
      exact cast_intOf (valsU (program := program)).2.1 (valsU (program := program)).2.2.2.2.2.2.1
        (mem_prime_of_bool (hb m hm t ht)))
    (fun t ht => by
      simp only [Nat.zero_add, eq_intCast]
      rw [idx8_entry hm ht, intOf_constA _ hvc hvf (hv t ht).1, Int.cast_natCast]
      exact (hv t ht).2), ← RealizedProgram.Ops.eqWord]
  exact RealizedProgram.Ops.eqWord_eq_eqConst (fun t ht => hb m hm t ht) hc

include hb hm h59 h64 in
theorem cast_evalIntWith_ref6_of :
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
  rw [RealizedProgram.evalIntWith_ref (k := 6) MldsaHCross.refsOrdered _ _ (refsA (program := program)),
    (expr6 (program := program)), RealizedProgram.evalIntWith_add,
    RealizedProgram.evalIntWith_mul, RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_scale_const,
    RealizedProgram.evalIntWith_leaf, (lensA (program := program)).2.2.2.2.2.2.2.2, centered_qm1,
    RealizedProgram.evalIntWith_ref (k := 4) MldsaHCross.refsOrdered _ _ (by have := (refsA (program := program)); omega),
    (expr4 (program := program)),
    RealizedProgram.evalIntWith_ref (k := 5) MldsaHCross.refsOrdered _ _ (by have := (refsA (program := program)); omega),
    (expr5 (program := program)), RealizedProgram.evalIntWith_mul]
  push_cast
  rw [cast_evalIntWith_ref2_of h59 h64,
    cast_evalIntWith_eqWord_of hb hm (by decide) (constsU (program := program)).2.2.2.2.2.2.1
      (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h3,
    cast_evalIntWith_eqWord_of hb hm (by decide) (constsU (program := program)).2.2.1
      (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.1 h1,
    cast_intOf (valsU (program := program)).2.2.1 (valsU (program := program)).2.2.2.2.2.2.2.1
      (mem_prime_of_bool h64)]
  have hM : UseHint.hiCount mldsa44.γ₂ - 1 = 43 := by decide
  simp only [UseHint.endpoint, UseHint.outputFromBits, hM]
  ring

end Interval

/-- **`hint.interval` holds** where, at every coefficient, `h`, `s` and the output are bits, the
offset and the slack are naturals below `512^2` and the interval row holds in the field
(`UseHintHolds.interval`; the integer equation follows, no side wrapping). -/
theorem interval3_of (hb : ∀ m < 1024, ∀ t < 6, rdA e 63 (6 * m + t) = 0 ∨ rdA e 63 (6 * m + t) = 1)
    (h59 : ∀ m < 1024, rdA e 59 m = 0 ∨ rdA e 59 m = 1)
    (h64 : ∀ m < 1024, rdA e 64 m = 0 ∨ rdA e 64 m = 1)
    (hoff : ∀ m < 1024, ∃ k : ℕ, k < 262144 ∧ rdA e 65 m = k)
    (hsl : ∀ m < 1024, ∃ k : ℕ, k < 262144 ∧ rdA e 66 m = k)
    (h : ∀ m < 1024, UseHint.IntervalEq mldsa44.γ₂ (rdA e 59 m) (rdA e 64 m) (rdA e 65 m)
      (rdA e 66 m) (UseHint.outputFromBits (UseHint.hiCount mldsa44.γ₂) (bitsA e m))) :
    program.HoldsWith (program.reader e) (program.predicate 3).body := by
  rw [(pred3 (program := program))]
  intro m hm
  rw [RealizedProgram.exprLen_add, (lensU (program := program)).2.2] at hm
  obtain ⟨ko, hko, hov⟩ := hoff m hm
  obtain ⟨ks, hks, hsv⟩ := hsl m hm
  have hE := evalInt_ref6_bool e hb hm (h59 m hm) (h64 m hm)
  have hcast := cast_evalIntWith_ref6_of hb hm (h59 m hm) (h64 m hm)
  have hiv := h m hm
  unfold UseHint.IntervalEq at hiv
  rw [← hcast, hov, hsv] at hiv
  rw [Nat.cast_zero, zero_dvd_iff, sub_eq_zero, RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_add,
    RealizedProgram.evalIntWith_leaf, RealizedProgram.evalIntWith_leaf, RealizedProgram.evalIntWith_reindex,
    RealizedProgram.evalIntWith_leaf, idx9_entry hm,
    intOf_constA _ (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.1
      (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      (by rw [(constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.1]; decide),
    (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.1,
    intOf_of_rdA e (valsU (program := program)).2.2.2.1 (valsU (program := program)).2.2.2.2.2.2.2.2.1
      (by omega) hov,
    intOf_of_rdA e (valsU (program := program)).2.2.2.2.1 (valsU (program := program)).2.2.2.2.2.2.2.2.2
      (by omega) hsv]
  simp only [List.getD_cons_zero]
  have hγ : mldsa44.γ₂ - 1 = 95231 := rfl
  rw [hγ] at hiv
  rcases hE with hE | hE <;> rw [hE] at hiv ⊢
  · have hc : ((ko + ks : ℕ) : (interp 0).K) = ((95231 : ℕ) : (interp 0).K) := by
      push_cast at hiv ⊢
      linear_combination hiv
    rw [CharP.natCast_eq_natCast (interp 0).K 8380417, Nat.ModEq,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc
    push_cast
    omega
  · have hc : ((ko + ks : ℕ) : (interp 0).K) = ((95232 : ℕ) : (interp 0).K) := by
      push_cast at hiv ⊢
      linear_combination hiv
    rw [CharP.natCast_eq_natCast (interp 0).K 8380417, Nat.ModEq,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hc
    push_cast
    omega

/-! ## The signature relation, conversely -/

set_option hygiene false in
local notation "coord0" => (QField.coord0 (F0 := F0))

set_option hygiene false in
local notation "φq" => (ZMod.castHom (dvd_refl _root_.MLDSA.modulus) (interp 0).K :
  _root_.MLDSA.Coeff →+* (interp 0).K)

/-- **The prime field `F_q` in `F_q^6`**, as a subring. -/
noncomputable abbrev primeS : Subring (interp 0).K := (φq).range

theorem natCast_mem_primeS (n : ℕ) : (n : (interp 0).K) ∈ primeS (F0 := F0) (FH := FH) :=
  ⟨n, map_natCast _ n⟩

theorem intCast_mem_primeS (n : ℤ) : (n : (interp 0).K) ∈ primeS (F0 := F0) (FH := FH) :=
  ⟨n, map_intCast _ n⟩

theorem inv_natCast_mem_primeS (n : ℕ) : ((n : (interp 0).K))⁻¹ ∈ primeS (F0 := F0) (FH := FH) :=
  ⟨(n : _root_.MLDSA.Coeff)⁻¹, by rw [map_inv₀, map_natCast]⟩

theorem eq_of_mem_primeS {x : (interp 0).K} (hx : x ∈ primeS (F0 := F0) (FH := FH)) :
    φq (coord0 x) = x := by
  obtain ⟨z, rfl⟩ := hx
  rw [coord0_φq]

/-- **The inverse transform keeps `F_q`.** -/
theorem inverseNtt_mem_primeS {h : ℕ → (interp 0).K}
    (hh : ∀ s < 256, h s ∈ primeS (F0 := F0) (FH := FH))
    (i : ℕ) : RealizedProgram.Ops.inverseNtt 256 ((1753 : ℕ) : (interp 0).K) h i ∈ primeS (F0 := F0) (FH := FH) := by
  unfold RealizedProgram.Ops.inverseNtt
  split_ifs
  · refine Subring.mul_mem _ (inv_natCast_mem_primeS 256) (Subring.sum_mem _ fun m _ => ?_)
    exact Subring.mul_mem _ (hh _ m.isLt) (Subring.pow_mem _ (inv_natCast_mem_primeS 1753) _)
  · exact Subring.zero_mem _

/-- **The negacyclic convolution keeps `F_q`.** -/
theorem negacyclic_mem_primeS {h x : ℕ → (interp 0).K}
    (hh : ∀ s < 256, h s ∈ primeS (F0 := F0) (FH := FH))
    (hx : ∀ s < 256, x s ∈ primeS (F0 := F0) (FH := FH)) (j : ℕ) :
    RealizedProgram.Ops.negacyclic 256 h x j ∈ primeS (F0 := F0) (FH := FH) := by
  by_cases hj : j < 256
  · rw [RealizedProgram.Ops.negacyclic_apply _ _ _ hj]
    refine Subring.sub_mem _ (Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun k _ => ?_)
      (Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun k _ => ?_) <;>
    · split_ifs
      · exact Subring.mul_mem _ (hh _ i.isLt) (hx _ k.isLt)
      · exact Subring.zero_mem _
  · unfold RealizedProgram.Ops.negacyclic RealizedProgram.Ops.ofFin
    rw [dif_neg hj]
    exact Subring.zero_mem _

theorem zero_of_mem_primeS {x : (interp 0).K} (hx : x ∈ primeS (F0 := F0) (FH := FH))
    (h : coord0 x = 0) : x = 0 := by
  rw [← eq_of_mem_primeS hx, h, map_zero]

/-- **`signature.relation` holds** where the statement's `Â` and `t1` lie in `F_q` and are the key's
(`KeyOf`), `z` and `w'` are casts of integers, the challenge bits are bits, and `w'` is
`computeWApprox(Â, c, z, t1)` coefficientwise (the identity `signature_coeff` concludes). -/
theorem sig0_of {pk : MLDSA44.PublicKey44} (hk : KeyOf pk e.stmt)
    (h56 : ∀ j < 4096, (RealizedProgram.castElt (b := 0) (program.reader e 56 j) : (interp 0).K) ∈
      primeS (F0 := F0) (FH := FH))
    (h57 : ∀ j < 1024, (RealizedProgram.castElt (b := 0) (program.reader e 57 j) : (interp 0).K) ∈
      primeS (F0 := F0) (FH := FH))
    (hz : ∀ m < 1024, ∃ n : ℤ, (n : (interp 0).K) = rdA e 58 m)
    (hcb : ∀ s < 512, rdA e 60 s = 0 ∨ rdA e 60 s = 1)
    (hw : ∀ m < 1024, ∃ n : ℤ, (n : (interp 0).K) = rdA e 61 m)
    (hid : ∀ (i : Fin _root_.MLDSA.mldsa44.k) (k : Fin _root_.MLDSA.ringDegree),
      MLDSA44.coeff ((wOf (program.reader e)).get i) k =
        ∑ j : Fin _root_.MLDSA.mldsa44.l, LatticeCrypto.negacyclicConvCoeff
            (MLDSA44.coeff (_root_.MLDSA.Concrete.concreteNTTRingOps.fromHat
              (((Rows.aHat pk).get i).get j)))
            (MLDSA44.coeff ((zOf (program.reader e)).get j)) k -
          LatticeCrypto.negacyclicConvCoeff (MLDSA44.coeff (cPolyA (program.reader e)))
            (fun k' => (2 ^ _root_.MLDSA.droppedBits : _root_.MLDSA.Coeff) *
              MLDSA44.coeff (pk.t1.get i) k') k) :
    program.HoldsWith (program.reader e) (program.predicate 0).body := by
  rw [(pred0 (program := program))]
  intro m hm
  simp only [RealizedProgram.exprLen_add] at hm
  rw [(sigData (program := program)).2.2] at hm
  set i : Fin _root_.MLDSA.mldsa44.k := ⟨m / 256, by change m / 256 < 4; omega⟩
  set k : Fin _root_.MLDSA.ringDegree := ⟨m % 256, Nat.mod_lt _ (by norm_num)⟩
  have hmik : m = (i : ℕ) * 256 + k := by simp only [i, k]; omega
  change program.evalE (program.reader e) (program.domainField 0) _ _ =
    program.evalE (program.reader e) (program.domainField 0) _ _
  rw [(lensA (program := program)).2.2.2.2.2.2.2.2]
  simp only [RealizedProgram.evalE_add, ↓evalE_negA, evalE_scaleA, evalE_polyMatVec _ hm,
    evalE_polyBroadcast _ hm]
  change _ = rdA e 0 _
  rw [rdA_0]
  have hzS : ∀ j < 1024, program.evalE (program.reader e) 0 (.leaf 58) j ∈ primeS (F0 := F0) (FH := FH) :=
    fun j hj => by
      obtain ⟨n, hn⟩ := hz j hj
      change rdA e 58 j ∈ _
      rw [← hn]
      exact intCast_mem_primeS n
  have hbS : ∀ (r : ℕ), r < 2 →
      (∀ s < 256, program.evalE (program.reader e) 0 (.ref r) s = rdA e 60 (2 * s + r)) →
      ∀ s < 256, program.evalE (program.reader e) 0 (.ref r) s ∈ primeS (F0 := F0) (FH := FH) :=
    fun r hr hx s hs => by
      rw [hx s hs]
      rcases hcb (2 * s + r) (by omega) with h | h <;> rw [h]
      · exact Subring.zero_mem _
      · exact Subring.one_mem _
  have hx0 : ∀ s < 256, program.evalE (program.reader e) 0 (.ref 0) s = rdA e 60 (2 * s + 0) :=
    fun s hs' => evalE_ref0 e hs'
  have hx1 : ∀ s < 256, program.evalE (program.reader e) 0 (.ref 1) s = rdA e 60 (2 * s + 1) :=
    fun s hs' => evalE_ref1 e hs'
  refine zero_of_mem_primeS ?_ ?_
  · obtain ⟨n, hn⟩ := hw m hm
    refine Subring.add_mem _ (Subring.add_mem _ (Subring.add_mem _ ?_ ?_) ?_) ?_
    · change rdA e 61 m ∈ _
      rw [← hn]
      exact intCast_mem_primeS n
    · refine Subring.neg_mem _ (Subring.sum_mem _ fun l _ => ?_)
      have hl : (l : ℕ) < 4 := l.isLt
      exact negacyclic_mem_primeS
        (fun s hs => inverseNtt_mem_primeS (fun s' hs' => h56 _ (by omega)) s)
        (fun s hs => hzS _ (by omega)) _
    · exact Subring.mul_mem _ (natCast_mem_primeS _) (negacyclic_mem_primeS
        (fun s hs => h57 _ (by omega)) (hbS 0 (by norm_num) hx0) _)
    · exact Subring.mul_mem _ (natCast_mem_primeS _) (negacyclic_mem_primeS
        (fun s hs => h57 _ (by omega)) (hbS 1 (by norm_num) hx1) _)
  · have hdiv : m / 256 = (i : ℕ) := rfl
    have hmod : m % 256 = (k : ℕ) := rfl
    rw [map_add, map_add, map_add, map_neg, map_sum, coord0_natCast_mul, coord0_natCast_mul, hmod]
    simp only [hdiv]
    simp only [negacyclic_at _ _ k]
    have hz' : ∀ (l : Fin _root_.MLDSA.mldsa44.l) (t : Fin _root_.MLDSA.ringDegree),
        φq (coord0 (program.evalE (program.reader e) 0 (.leaf 58) (l * 256 + t))) =
          program.evalE (program.reader e) 0 (.leaf 58) (l * 256 + t) := fun l t =>
      eq_of_mem_primeS (hzS _ (flat_lt l t))
    have hb : ∀ (r : ℕ), r < 2 →
        (∀ s < 256, program.evalE (program.reader e) 0 (.ref r) s = rdA e 60 (2 * s + r)) →
        ∀ t : Fin _root_.MLDSA.ringDegree,
          φq (coord0 (program.evalE (program.reader e) 0 (.ref r) t)) =
            program.evalE (program.reader e) 0 (.ref r) t := fun r hr hx t =>
      eq_of_mem_primeS (hbS r hr hx t t.isLt)
    rw [coord0_negacyclicConvCoeff _ _ (hb 0 (by norm_num) hx0),
      coord0_negacyclicConvCoeff _ _ (hb 1 (by norm_num) hx1),
      Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => coord0_negacyclicConvCoeff _ _ (hz' l) k]
    have hA : ∀ l : Fin _root_.MLDSA.mldsa44.l, (fun a : Fin _root_.MLDSA.ringDegree =>
        coord0 (RealizedProgram.Ops.inverseNtt 256 ((1753 : ℕ) : (interp 0).K)
        (fun s => RealizedProgram.castElt (b := 0) (program.reader e 56 (((i : ℕ) * 4 + l) * 256 + s))) a)) =
        MLDSA44.coeff (_root_.MLDSA.Concrete.concreteNTTRingOps.fromHat
          (((Rows.aHat pk).get i).get l)) := fun l => by
      funext a
      rw [coord0_inverseNtt, RealizedProgram.Ops.inverseNtt_congr
        (y := RealizedProgram.Ops.ofFin fun s : Fin 256 => (((Rows.aHat pk).get i).get l).coeffs.get s)
        (fun s hs' => by rw [RealizedProgram.Ops.ofFin_of_lt _ hs']; exact coord0_aHat hk i l ⟨s, hs'⟩),
        KeyNTT.inverseNtt_spectrum _ a.isLt,
        show _root_.MLDSA.Concrete.concreteNTTRingOps.fromHat (((Rows.aHat pk).get i).get l) =
          _root_.MLDSA.Concrete.invNTT (((Rows.aHat pk).get i).get l) from rfl,
        MLDSA44.coeff_apply]
    have hZ : ∀ l : Fin _root_.MLDSA.mldsa44.l, (fun b : Fin _root_.MLDSA.ringDegree =>
        coord0 (program.evalE (program.reader e) 0 (.leaf 58) (l * 256 + b))) =
        MLDSA44.coeff ((zOf (program.reader e)).get l) := fun l => by
      funext b
      obtain ⟨n, hn⟩ := hz _ (flat_lt l b)
      rw [coeff_zOf]
      change coord0 (rdA e 58 _) = NativeAlgebraCircuit.coeffRep (rdA e 58 _)
      rw [← hn, coord0_intCast, NativeAlgebraCircuit.coeffRep_eq_intCast rfl]
    have hT : (fun a : Fin _root_.MLDSA.ringDegree =>
        coord0 (RealizedProgram.castElt (program.reader e 57 ((i : ℕ) * 256 + a)) : (interp 0).K)) =
        MLDSA44.coeff (pk.t1.get i) := by
      funext a
      rw [coord0_t1 hk i a]
      rfl
    have hcb' : ∀ (r : ℕ) (hr : r < 2)
        (hx : ∀ s < 256, program.evalE (program.reader e) 0 (.ref r) s = rdA e 60 (2 * s + r))
        (t : Fin _root_.MLDSA.ringDegree),
        coord0 (program.evalE (program.reader e) 0 (.ref r) t) =
          Rows.bitCoeff (cABits (program.reader e) t ⟨r, hr⟩) := fun r hr hx t => by
      have ht : (t : ℕ) < 256 := t.isLt
      rw [hx t ht, coord0_bool (hcb _ (by omega))]
      rfl
    have hC0 : (fun t : Fin _root_.MLDSA.ringDegree =>
        coord0 (program.evalE (program.reader e) 0 (.ref 0) t)) =
        fun t => Rows.bitCoeff (cABits (program.reader e) t 0) :=
      funext (hcb' 0 (by norm_num) hx0)
    have hC1 : (fun t : Fin _root_.MLDSA.ringDegree =>
        coord0 (program.evalE (program.reader e) 0 (.ref 1) t)) =
        fun t => Rows.bitCoeff (cABits (program.reader e) t 1) :=
      funext (hcb' 1 (by norm_num) hx1)
    simp only [hA, hZ, hT, hC0, hC1]
    obtain ⟨n, hn⟩ := hw m hm
    have hW : coord0 (program.evalE (program.reader e) 0 (.leaf 61) m) =
        MLDSA44.coeff ((wOf (program.reader e)).get i) k := by
      rw [coeff_wOf]
      change coord0 (rdA e 61 m) = NativeAlgebraCircuit.coeffRep (rdA e 61 ((i : ℕ) * 256 + k))
      rw [← hmik, ← hn, coord0_intCast, NativeAlgebraCircuit.coeffRep_eq_intCast rfl]
    rw [hW]
    have hcoeffC : MLDSA44.coeff (cPolyA (program.reader e)) = fun t =>
        Rows.bitCoeff (cABits (program.reader e) t 0) -
          2 * Rows.bitCoeff (cABits (program.reader e) t 1) := by
      funext t
      unfold cPolyA
      rw [MLDSA44.coeff_ofCoeff]
    have hident := hid i k
    rw [hcoeffC, DFT.negacyclicConvCoeff_ternary
      (fun t => Rows.bitCoeff (cABits (program.reader e) t 0))
      (fun t => Rows.bitCoeff (cABits (program.reader e) t 1))
      (fun k' => MLDSA44.coeff (pk.t1.get i) k') (2 ^ _root_.MLDSA.droppedBits) k,
      Falcon512.negacyclicConvCoeff_comm
        (fun t => Rows.bitCoeff (cABits (program.reader e) t 0)),
      Falcon512.negacyclicConvCoeff_comm
        (fun t => Rows.bitCoeff (cABits (program.reader e) t 1))] at hident
    have h16 : ((8364033 : ℕ) : _root_.MLDSA.Coeff) = -(2 * 2 ^ _root_.MLDSA.droppedBits) := by
      decide
    have h13 : ((8192 : ℕ) : _root_.MLDSA.Coeff) = 2 ^ _root_.MLDSA.droppedBits := by decide
    rw [h16, h13]
    linear_combination hident

end MLDSA44.Native.ROMParams

end GordieHowe
