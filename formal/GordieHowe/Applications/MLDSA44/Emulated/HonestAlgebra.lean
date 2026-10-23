-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Emulated.Frontend.Algebra
public import GordieHowe.Applications.MLDSA44.Honest.A

@[expose] public section

/-!
# GordieHowe: domain `A`'s predicates of an emulated ML-DSA program, conversely

The converse of the emulated frontend's algebra (`GordieHowe/Applications/MLDSA44/Emulated/Frontend/Algebra.lean`) for the honest prover:
each source predicate of domain `A` of an emulated ML-DSA program (`MldsaEAlgebra`) holds where its
readings have the properties the honest values have, stated on the readings alone: the type checks
where the values read bits (`boolA_of`), the ranges where the records read naturals below the bounds
(`w11_of`, `norm12_of`, `offset13_of`, `slack14_of`, `weight15_of`), UseHint's three rows where the
output bits are bits and UseHint holds with the wrap (`w1bound0_of`, `decompose1_of`,
`interval2_of`), and the signature relation where the readings are the key's and the honest
naturals' and they satisfy the congruence (`sig274_of`).
-/

namespace GordieHowe.MLDSA44.Emulated

open Generated.MLDSA44.Emulated.ROMParams.Program
open GordieHowe.Bits
open Native.ROMParams (MldsaHHash MldsaHSample MldsaHConsts)

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaEAlgebra program] {F0 FH : RealizedProgram.FieldInterp} [AField F0]
  [HField FH]

set_option hygiene false in
local notation "nat" => MldsaEmbed.nat program

variable [MldsaHHash nat] [MldsaHSample nat] [MldsaHConsts nat FH]

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

variable (e : program.Env interp)

/-! ## The type checks and the ranges -/

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
  have h0 := (crossData (program := program)).2.2.2.2.1
  change ∃ k < n, program.evalE rd (program.domainField 0) r' i = k
  rw [h0]
  exact h i hi

/-- **`signature.w` holds** where `w'` is a natural below `2^24`. -/
theorem w11_of (h : ∀ i < 1024, ∃ k : ℕ, k < 16777216 ∧ rdA e 62 i = k) :
    program.HoldsWith (program.reader e) (program.predicate 11).body := by
  obtain ⟨_, hb⟩ := pred11 (program := program)
  rw [hb]
  refine mem_of_natBelow fun i hi => ?_
  rw [RealizedProgram.exprLen_leaf, (lensA (program := program)).2.2.2.1] at hi
  exact h i hi

/-- **`norm.z` holds** where `z + 130993` is a natural below `261987`. -/
theorem norm12_of (h : ∀ i < 1024, ∃ k : ℕ, k < 261987 ∧
      rdA e 59 i + ((130993 : ℕ) : (interp 0).K) = k) :
    program.HoldsWith (program.reader e) (program.predicate 12).body := by
  obtain ⟨_, hb⟩ := pred12 (program := program)
  rw [hb]
  refine mem_of_natBelow fun i hi => ?_
  rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_leaf, (lensA (program := program)).1] at hi
  obtain ⟨k, hk, hkv⟩ := h i hi
  refine ⟨k, hk, ?_⟩
  rw [RealizedProgram.evalE_add]
  change rdA e 59 i + rdA e 63 i = _
  rw [rdA_63 e hi]
  exact hkv

/-- **`hint.offset` holds** where the offset is a natural below the layout's bound. -/
theorem offset13_of
    (h : ∀ i < 1024, ∃ k : ℕ, k < (MldsaEAlgebra.layout program).offsetBound ∧ rdA e 66 i = k) :
    program.HoldsWith (program.reader e) (program.predicate 13).body := by
  obtain ⟨_, hb⟩ := pred13 (program := program)
  rw [hb]
  refine mem_of_natBelow fun i hi => ?_
  rw [RealizedProgram.exprLen_leaf, (lensA (program := program)).2.2.2.2.2.2.1] at hi
  exact h i hi

/-- **`hint.slack` holds** where the slack is a natural below the layout's bound. -/
theorem slack14_of
    (h : ∀ i < 1024, ∃ k : ℕ, k < (MldsaEAlgebra.layout program).offsetBound ∧ rdA e 67 i = k) :
    program.HoldsWith (program.reader e) (program.predicate 14).body := by
  obtain ⟨_, hb⟩ := pred14 (program := program)
  rw [hb]
  refine mem_of_natBelow fun i hi => ?_
  rw [RealizedProgram.exprLen_leaf, (lensA (program := program)).2.2.2.2.2.2.2.1] at hi
  exact h i hi

/-- **`hint_weight.weight` holds** where the hint's sum is a natural below `81`. -/
theorem weight15_of (h : ∃ k : ℕ, k < 81 ∧ ∑ t : Fin 1024, rdA e 60 t = k) :
    program.HoldsWith (program.reader e) (program.predicate 15).body := by
  obtain ⟨_, hb⟩ := pred15 (program := program)
  rw [hb]
  refine mem_of_natBelow fun i hi => ?_
  have hlen : program.exprLen (.apply (.sum 1024) (.leaf 60)) = 1 := by
    simp only [RealizedProgram.exprLen, RealizedProgram.Expr.len, (lensA (program := program)).2.1, RealizedProgram.NamedOp.cols,
      RealizedProgram.NamedOp.rows]
  rw [hlen] at hi
  obtain rfl : i = 0 := by omega
  obtain ⟨k, hk, hkv⟩ := h
  refine ⟨k, hk, ?_⟩
  rw [RealizedProgram.evalE_apply_sum]
  simp only [Nat.zero_mul, Nat.zero_add]
  exact hkv

/-! ## UseHint, conversely -/

/-- **`hint.w1_bound` holds** where every coefficient's output bits are bits at most `M − 1`. -/
theorem w1bound0_of (hb : ∀ m < 1024, ∀ t < 6, rdA e 64 (6 * m + t) = 0 ∨ rdA e 64 (6 * m + t) = 1)
    (h : ∀ m < 1024, Bits.leConst (bitsA e m) (UseHint.hiCount mldsa44.γ₂ - 1) = 1) :
    program.HoldsWith (program.reader e) (program.predicate 0).body := by
  rw [(pred0 (program := program))]
  intro m hm
  rw [(lensU (program := program)).1] at hm
  change program.evalE (program.reader e) (program.domainField 0) _ m =
    program.evalE (program.reader e) (program.domainField 0) _ m
  rw [(lensA (program := program)).2.2.2.2.2.2.2.2, RealizedProgram.evalE_logic]
  change _ = rdA e 1 m
  rw [rdA_1 e hm]
  simp only [RealizedProgram.LogicOp.eval, List.headD_cons, List.getD_cons_succ, List.getD_cons_zero,
    RealizedProgram.evalE_reindex]
  rw [RealizedProgram.Ops.leqWord, RealizedProgram.Ops.ltWord, RealizedProgram.Ops.ltReduce_congr 6 0 (a' := fun t => Bits.constBit 43 t)
    (b' := fun t => rdA e 64 (6 * m + t))
    (fun t ht => by simp only [Nat.zero_add]; rw [idx6_entry hm ht]; exact rdA_0 e ht)
    (fun t _ => by rw [Nat.mul_comm]; rfl), ← RealizedProgram.Ops.ltWord, ← RealizedProgram.Ops.leqWord,
    RealizedProgram.Ops.leqWord_eq_leConst (fun t ht => hb m hm t ht) (by decide)]
  have hM : UseHint.hiCount mldsa44.γ₂ - 1 = 43 := by decide
  rw [← hM]
  exact h m hm

section UseHint

variable {e} (hb : ∀ m < 1024, ∀ t < 6, rdA e 64 (6 * m + t) = 0 ∨ rdA e 64 (6 * m + t) = 1)
include hb

/-- **The output bits against a constant's bits** (`evalE_eqWord`), at Boolean output bits. -/
theorem evalE_eqWord_of {m : ℕ} (hm : m < 1024) {v c : ℕ} (hc : c < 64)
    (hv : ∀ t < 6, rdA e v t = Bits.constBit c t) :
    program.evalE (program.reader e) 0 (.logic .eq 6 [.leaf 64, .reindex idx6 (.leaf v)]) m =
      Bits.eqConst (bitsA e m) c := by
  rw [RealizedProgram.evalE_logic]
  simp only [RealizedProgram.LogicOp.eval, List.headD_cons, List.getD_cons_succ, List.getD_cons_zero,
    RealizedProgram.evalE_reindex]
  rw [RealizedProgram.Ops.eqWord, RealizedProgram.Ops.eqReduce_congr 6 0 (a' := fun t => rdA e 64 (6 * m + t))
    (b' := fun t => Bits.constBit c t)
    (fun t _ => by rw [Nat.mul_comm]; rfl)
    (fun t ht => by simp only [Nat.zero_add]; rw [idx6_entry hm ht]; exact hv t ht), ← RealizedProgram.Ops.eqWord]
  exact RealizedProgram.Ops.eqWord_eq_eqConst (fun t ht => hb m hm t ht) hc

theorem evalE_ref2_of {m : ℕ} (hm : m < 1024) :
    program.evalE (program.reader e) 0 (.ref 2) m = Bits.eqConst (bitsA e m) 0 := by
  rw [RealizedProgram.evalE_ref (refsOrdered (program := program)) _ _
      (by have := (refsA (program := program)); omega), (expr2 (program := program))]
  exact evalE_eqWord_of hb hm (by decide) fun t ht => rdA_2 e ht

theorem evalE_ref3_of {m : ℕ} (hm : m < 1024) :
    program.evalE (program.reader e) 0 (.ref 3) m =
      rdA e 60 m * rdA e 65 m * Bits.eqConst (bitsA e m) 43 := by
  rw [RealizedProgram.evalE_ref (refsOrdered (program := program)) _ _
      (by have := (refsA (program := program)); omega), (expr3 (program := program)),
    RealizedProgram.evalE_mul, evalE_ref0, evalE_eqWord_of hb hm (by decide) fun t ht => rdA_0 e ht]

theorem evalE_ref4_of {m : ℕ} (hm : m < 1024) :
    program.evalE (program.reader e) 0 (.ref 4) m =
      UseHint.endpoint (rdA e 60 m) (rdA e 65 m)
        (UseHint.outputFromBits (UseHint.hiCount mldsa44.γ₂) (bitsA e m)) := by
  rw [RealizedProgram.evalE_ref (refsOrdered (program := program)) _ _
      (by have := (refsA (program := program)); omega), (expr4 (program := program))]
  rw [RealizedProgram.evalE_add, RealizedProgram.evalE_mul, RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const,
    evalE_ref0, evalE_ref2_of hb hm, evalE_ref3_of hb hm, decode_gold, pm1]
  have hM : UseHint.hiCount mldsa44.γ₂ - 1 = 43 := by decide
  simp only [UseHint.endpoint, UseHint.outputFromBits, hM]
  unfold rdA
  ring

theorem evalE_ref5_of {m : ℕ} (hm : m < 1024) :
    program.evalE (program.reader e) 0 (.ref 5) m = rdA e 62 m -
      UseHint.relationResult mldsa44.γ₂ (UseHint.hiCount mldsa44.γ₂) (rdA e 60 m) (rdA e 65 m)
        (rdA e 66 m) (UseHint.outputFromBits (UseHint.hiCount mldsa44.γ₂) (bitsA e m)) := by
  rw [RealizedProgram.evalE_ref (refsOrdered (program := program)) _ _ (refsA (program := program)),
    (expr5 (program := program))]
  simp only [RealizedProgram.evalE_add, ↓evalE_negA, evalE_scaleA, RealizedProgram.evalE_mul,
    RealizedProgram.evalE_reindex, evalE_outputValue, evalE_ref0, evalE_ref1, evalE_ref2_of hb hm,
    evalE_ref3_of hb hm, evalE_ref4_of hb hm, idx7_entry hm]
  have hM' : UseHint.hiCount 95232 = 44 := by decide
  have hγ : mldsa44.γ₂ = 95232 := rfl
  have h3 : rdA e 3 0 = 1 := rdA_3 e
  simp only [UseHint.relationResult, UseHint.rawHigh, UseHint.lower, UseHint.outputFromBits,
    UseHint.endpoint, hM', hγ, Nat.cast_ofNat]
  unfold rdA at h3 ⊢
  rw [h3]
  push_cast
  ring

/-- **`hint.decompose` holds** where the residual `e = w' − result` has `e (e − q) = 0` at every
coefficient (`UseHint.WrapHolds.wrap`). -/
theorem decompose1_of (h : ∀ m < 1024,
      (rdA e 62 m - UseHint.relationResult mldsa44.γ₂ (UseHint.hiCount mldsa44.γ₂) (rdA e 60 m)
        (rdA e 65 m) (rdA e 66 m) (UseHint.outputFromBits (UseHint.hiCount mldsa44.γ₂) (bitsA e m))) *
      (rdA e 62 m - UseHint.relationResult mldsa44.γ₂ (UseHint.hiCount mldsa44.γ₂) (rdA e 60 m)
        (rdA e 65 m) (rdA e 66 m) (UseHint.outputFromBits (UseHint.hiCount mldsa44.γ₂) (bitsA e m)) -
        ((_root_.MLDSA.modulus : ℕ) : (interp 0).K)) = 0) :
    program.HoldsWith (program.reader e) (program.predicate 1).body := by
  rw [(pred1 (program := program))]
  intro m hm
  rw [(lensU (program := program)).2.1] at hm
  change program.evalE (program.reader e) (program.domainField 0) _ m =
    program.evalE (program.reader e) (program.domainField 0) _ m
  rw [(lensA (program := program)).2.2.2.2.2.2.2.2]
  simp only [RealizedProgram.evalE_mul, RealizedProgram.evalE_add, RealizedProgram.evalE_reindex, idx7_entry hm,
    evalE_ref5_of hb hm]
  change _ = rdA e 5 m
  rw [rdA_5 e m]
  have h4 := rdA_4 e
  have hd := h m hm
  unfold rdA at h4 hd ⊢
  rw [h4]
  linear_combination hd

end UseHint

/-- **The endpoint's integer reading is a bit** at Boolean `h`, `s` and output bits. -/
theorem evalInt_ref4_bool (hb : ∀ m < 1024, ∀ t < 6, rdA e 64 (6 * m + t) = 0 ∨ rdA e 64 (6 * m + t) = 1)
    {m : ℕ} (hm : m < 1024) (h60 : rdA e 60 m = 0 ∨ rdA e 60 m = 1)
    (h65 : rdA e 65 m = 0 ∨ rdA e 65 m = 1) :
    program.evalIntWith (program.reader e) 0 (.ref 4) m = 0 ∨
      program.evalIntWith (program.reader e) 0 (.ref 4) m = 1 := by
  rw [RealizedProgram.evalIntWith_ref (k := 4) (refsOrdered (program := program)) _ _
      (by have := (refsA (program := program)); omega),
    (expr4 (program := program)), RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_mul,
    RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_scale_const, RealizedProgram.evalIntWith_leaf,
    (lensA (program := program)).2.2.2.2.2.2.2.2, centered_pm1,
    RealizedProgram.evalIntWith_ref (k := 2) (refsOrdered (program := program)) _ _
      (by have := (refsA (program := program)); omega),
    (expr2 (program := program)),
    RealizedProgram.evalIntWith_ref (k := 3) (refsOrdered (program := program)) _ _
      (by have := (refsA (program := program)); omega),
    (expr3 (program := program)), RealizedProgram.evalIntWith_mul,
    RealizedProgram.evalIntWith_ref (k := 0) (refsOrdered (program := program)) _ _
      (by have := (refsA (program := program)); omega),
    (expr0 (program := program)), RealizedProgram.evalIntWith_mul, RealizedProgram.evalIntWith_leaf,
    RealizedProgram.evalIntWith_leaf]
  have hbit : ∀ {v j : ℕ}, program.isConstant v = false → program.valueField v = 0 →
      (rdA e v j = 0 ∨ rdA e v j = 1) →
      program.intOf (program.reader e) v j = 0 ∨ program.intOf (program.reader e) v j = 1 := by
    intro v j hc hf h
    rcases h with h | h
    · left
      have := intOf_of_natCast hc hf (k := 0) (by decide) (by rw [h]; simp)
      exact_mod_cast this
    · right
      have := intOf_of_natCast hc hf (k := 1) (by decide) (by rw [h]; simp)
      exact_mod_cast this
  have i60 := hbit (valsU (program := program)).1 (valsU (program := program)).2.2.2.2.2.1 h60
  have i65 := hbit (valsU (program := program)).2.2.1 (valsU (program := program)).2.2.2.2.2.2.2.1 h65
  have hW : ∀ {v : ℕ}, (∀ t < 6, program.intOf (program.reader e) v t = 0 ∨
      program.intOf (program.reader e) v t = 1) →
      program.evalIntWith (program.reader e) 0
        (.logic .eq 6 [.leaf 64, .reindex idx6 (.leaf v)]) m = 0 ∨
      program.evalIntWith (program.reader e) 0
        (.logic .eq 6 [.leaf 64, .reindex idx6 (.leaf v)]) m = 1 := by
    intro v hv
    rw [RealizedProgram.evalIntWith_logic]
    simp only [RealizedProgram.LogicOp.eval, List.headD_cons, List.getD_cons_succ, List.getD_cons_zero,
      RealizedProgram.evalIntWith_reindex, RealizedProgram.evalIntWith_leaf]
    refine RealizedProgram.Ops.eqReduce_bool 6 _ (fun t ht => ?_) (fun t ht => ?_)
    · rw [show m * 6 + (0 + t) = 6 * m + t by ring]
      exact hbit (valsU (program := program)).2.1 (valsU (program := program)).2.2.2.2.2.2.1
        (hb m hm t ht)
    · rw [Nat.zero_add, idx6_entry hm ht]
      exact hv t ht
  have h2 : ∀ t < 6, program.intOf (program.reader e) 2 t = 0 ∨
      program.intOf (program.reader e) 2 t = 1 := fun t ht => by
    left
    rw [intOf_constA _ (constsU (program := program)).2.2.2.2.1
      (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      (by rw [(constsU (program := program)).2.2.2.2.2.1]; interval_cases t <;> decide),
      (constsU (program := program)).2.2.2.2.2.1]
    interval_cases t <;> rfl
  have h0 : ∀ t < 6, program.intOf (program.reader e) 0 t = 0 ∨
      program.intOf (program.reader e) 0 t = 1 := fun t ht => by
    rw [intOf_constA _ (constsU (program := program)).1
      (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      (by rw [(constsU (program := program)).2.1]; interval_cases t <;> decide),
      (constsU (program := program)).2.1]
    interval_cases t <;> simp
  rcases hW h2 with w2 | w2 <;> rcases hW h0 with w0 | w0 <;> rw [w2, w0] <;>
    rcases i60 with a | a <;> rcases i65 with b | b <;> rw [a, b] <;> simp

section Interval

variable {e} (hb : ∀ m < 1024, ∀ t < 6, rdA e 64 (6 * m + t) = 0 ∨ rdA e 64 (6 * m + t) = 1)
  {m : ℕ} (hm : m < 1024) (h60 : rdA e 60 m = 0 ∨ rdA e 60 m = 1)
  (h65 : rdA e 65 m = 0 ∨ rdA e 65 m = 1)

include h60 h65 in
theorem cast_evalIntWith_ref0_of :
    ((program.evalIntWith (program.reader e) 0 (.ref 0) m : ℤ) : (interp 0).K) =
      rdA e 60 m * rdA e 65 m := by
  rw [RealizedProgram.evalIntWith_ref (refsOrdered (program := program)) _ _
      (by have := (refsA (program := program)); omega), (expr0 (program := program)),
    RealizedProgram.evalIntWith_mul, RealizedProgram.evalIntWith_leaf, RealizedProgram.evalIntWith_leaf, Int.cast_mul,
    cast_intOf_bool (valsU (program := program)).1 (valsU (program := program)).2.2.2.2.2.1 h60,
    cast_intOf_bool (valsU (program := program)).2.2.1 (valsU (program := program)).2.2.2.2.2.2.2.1
      h65]

include hb hm in
theorem cast_evalIntWith_eqWord_of {v c : ℕ} (hc : c < 64) (hvc : program.isConstant v = true)
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
      exact cast_intOf_bool (valsU (program := program)).2.1
        (valsU (program := program)).2.2.2.2.2.2.1 (hb m hm t ht))
    (fun t ht => by
      simp only [Nat.zero_add, eq_intCast]
      rw [idx6_entry hm ht, intOf_constA _ hvc hvf (hv t ht).1, Int.cast_natCast]
      exact (hv t ht).2), ← RealizedProgram.Ops.eqWord]
  exact RealizedProgram.Ops.eqWord_eq_eqConst (fun t ht => hb m hm t ht) hc

include hb hm h60 h65 in
theorem cast_evalIntWith_ref4_of :
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
  rw [RealizedProgram.evalIntWith_ref (k := 4) (refsOrdered (program := program)) _ _
      (by have := (refsA (program := program)); omega), (expr4 (program := program)),
    RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_mul, RealizedProgram.evalIntWith_add,
    RealizedProgram.evalIntWith_scale_const, RealizedProgram.evalIntWith_leaf,
    (lensA (program := program)).2.2.2.2.2.2.2.2, centered_pm1,
    RealizedProgram.evalIntWith_ref (k := 2) (refsOrdered (program := program)) _ _
      (by have := (refsA (program := program)); omega), (expr2 (program := program)),
    RealizedProgram.evalIntWith_ref (k := 3) (refsOrdered (program := program)) _ _
      (by have := (refsA (program := program)); omega), (expr3 (program := program)),
    RealizedProgram.evalIntWith_mul]
  push_cast
  rw [cast_evalIntWith_ref0_of h60 h65,
    cast_evalIntWith_eqWord_of hb hm (by decide) (constsU (program := program)).2.2.2.2.1
      (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h2,
    cast_evalIntWith_eqWord_of hb hm (by decide) (constsU (program := program)).1
      (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 h0,
    cast_intOf_bool (valsU (program := program)).2.2.1 (valsU (program := program)).2.2.2.2.2.2.2.1
      h65]
  have hM : UseHint.hiCount mldsa44.γ₂ - 1 = 43 := by decide
  simp only [UseHint.endpoint, UseHint.outputFromBits, hM]
  ring

end Interval

/-- **`hint.interval` holds** where, at every coefficient, `h`, `s` and the output are bits, the
offset and the slack are naturals below the layout's bound and the interval row holds in the field
(`UseHint.IntervalEq`; the integer equation follows, no side wrapping). -/
theorem interval2_of (hb : ∀ m < 1024, ∀ t < 6, rdA e 64 (6 * m + t) = 0 ∨ rdA e 64 (6 * m + t) = 1)
    (h60 : ∀ m < 1024, rdA e 60 m = 0 ∨ rdA e 60 m = 1)
    (h65 : ∀ m < 1024, rdA e 65 m = 0 ∨ rdA e 65 m = 1)
    (hoff : ∀ m < 1024, ∃ k : ℕ, k < (MldsaEAlgebra.layout program).offsetBound ∧ rdA e 66 m = k)
    (hsl : ∀ m < 1024, ∃ k : ℕ, k < (MldsaEAlgebra.layout program).offsetBound ∧ rdA e 67 m = k)
    (h : ∀ m < 1024, UseHint.IntervalEq mldsa44.γ₂ (rdA e 60 m) (rdA e 65 m) (rdA e 66 m)
      (rdA e 67 m) (UseHint.outputFromBits (UseHint.hiCount mldsa44.γ₂) (bitsA e m))) :
    program.HoldsWith (program.reader e) (program.predicate 2).body := by
  rw [(pred2 (program := program))]
  intro m hm
  rw [(lensU (program := program)).2.2] at hm
  obtain ⟨ko, hko, hov⟩ := hoff m hm
  obtain ⟨ks, hks, hsv⟩ := hsl m hm
  have hB := MldsaEAlgebra.offsetBound_lt (program := program)
  have hE := evalInt_ref4_bool e hb hm (h60 m hm) (h65 m hm)
  have hcast := cast_evalIntWith_ref4_of hb hm (h60 m hm) (h65 m hm)
  have hiv := h m hm
  unfold UseHint.IntervalEq at hiv
  rw [← hcast, hov, hsv] at hiv
  rw [Nat.cast_zero, zero_dvd_iff, sub_eq_zero, RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_add,
    RealizedProgram.evalIntWith_leaf, RealizedProgram.evalIntWith_leaf, RealizedProgram.evalIntWith_reindex,
    RealizedProgram.evalIntWith_leaf, idx7_entry hm,
    intOf_constA _ (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.1
      (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      (by rw [(constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.1]; decide),
    (constsU (program := program)).2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    intOf_of_natCast (valsU (program := program)).2.2.2.1
      (valsU (program := program)).2.2.2.2.2.2.2.2.1 (by unfold pGold at hB ⊢; omega) hov,
    intOf_of_natCast (valsU (program := program)).2.2.2.2.1
      (valsU (program := program)).2.2.2.2.2.2.2.2.2 (by unfold pGold at hB ⊢; omega) hsv]
  simp only [List.getD_cons_zero]
  have hγ : mldsa44.γ₂ - 1 = 95231 := rfl
  rw [hγ] at hiv
  rcases hE with hE | hE <;> rw [hE] at hiv ⊢
  · have hc : ((ko + ks : ℕ) : (interp 0).K) = ((95231 : ℕ) : (interp 0).K) := by
      push_cast at hiv ⊢
      linear_combination hiv
    rw [CharP.natCast_eq_natCast (interp 0).K pGold, Nat.ModEq,
      Nat.mod_eq_of_lt (by unfold pGold at hB ⊢; omega), Nat.mod_eq_of_lt (by unfold pGold at hB ⊢; omega)] at hc
    push_cast
    omega
  · have hc : ((ko + ks : ℕ) : (interp 0).K) = ((95232 : ℕ) : (interp 0).K) := by
      push_cast at hiv ⊢
      linear_combination hiv
    rw [CharP.natCast_eq_natCast (interp 0).K pGold, Nat.ModEq,
      Nat.mod_eq_of_lt (by unfold pGold at hB ⊢; omega), Nat.mod_eq_of_lt (by unfold pGold at hB ⊢; omega)] at hc
    push_cast
    omega

/-! ## The signature relation, conversely -/

/-- **`signature.relation` holds** (predicate `274`, `q` divides the sides' integer difference at
every coefficient) where the statement holds the key's preprocessing, `w'` and `z` read as the
naturals `wv` and the shifted naturals `zv`, and they satisfy the congruence with the challenge's
integer readings (the converse of `congruentE`). -/
theorem sig274_of {pk : MLDSA44.PublicKey44} (hk : KeyOf pk e.stmt)
    {wv : Fin Native.Rows.nRows → Fin Native.Rows.deg → ℕ}
    {zv : Fin Native.Rows.nCols → Fin Native.Rows.deg → ℕ}
    (hw : ∀ (i : Fin Native.Rows.nRows) (k : Fin Native.Rows.deg),
      program.intOf (program.reader e) 62 ((i : ℕ) * 256 + k) = wv i k)
    (hz : ∀ (j : Fin Native.Rows.nCols) (m : Fin Native.Rows.deg),
      program.intOf (program.reader e) 59 ((j : ℕ) * 256 + m) = Rows.signedZ zv j m)
    (hc : Rows.Congruent (Rows.aKeyOf pk) (Rows.tKeyOf pk)
      zv wv (fun m => program.evalIntWith (program.reader e) 0 (.ref 7) m -
        2 * program.evalIntWith (program.reader e) 0 (.ref 8) m)) :
    program.HoldsWith (program.reader e) (program.predicate 274).body := by
  obtain ⟨_, hb⟩ := pred274 (program := program)
  rw [hb]
  intro m hm
  have hlen : program.exprLen sigL = 1024 := MldsaEAlgebra.lenSigL
  change m < program.exprLen sigL at hm
  rw [hlen] at hm
  set i : Fin Native.Rows.nRows := ⟨m / 256, by change m / 256 < 4; omega⟩
  set k : Fin Native.Rows.deg := ⟨m % 256, Nat.mod_lt _ (by norm_num)⟩
  have hmik : m = (i : ℕ) * 256 + k := by simp only [i, k]; omega
  change ((8380417 : ℕ) : ℤ) ∣ program.evalIntWith (program.reader e) 0 sigL m -
    program.evalIntWith (program.reader e) 0 sigR m
  rw [hmik]
  suffices h0 : ((program.evalIntWith (program.reader e) 0 sigL ((i : ℕ) * 256 + k) -
      program.evalIntWith (program.reader e) 0 sigR ((i : ℕ) * 256 + k) : ℤ) :
        _root_.MLDSA.Coeff) = 0 from (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
  rw [Int.cast_sub, cast_sigL hk i k, cast_sigR hk i k]
  show ((program.intOf (program.reader e) 62 ((i : ℕ) * 256 + k) : ℤ) : _root_.MLDSA.Coeff) +
        8192 * LatticeCrypto.negacyclicConvCoeff
          (fun m : Fin Native.Rows.deg => (t1Z pk i m : _root_.MLDSA.Coeff))
          (fun m => (program.evalIntWith (program.reader e) 0 (.ref 7) m : _root_.MLDSA.Coeff)) k -
        16384 * LatticeCrypto.negacyclicConvCoeff
          (fun m : Fin Native.Rows.deg => (t1Z pk i m : _root_.MLDSA.Coeff))
          (fun m => (program.evalIntWith (program.reader e) 0 (.ref 8) m : _root_.MLDSA.Coeff)) k -
      ∑ l : Fin 4, LatticeCrypto.negacyclicConvCoeff
        (fun m : Fin Native.Rows.deg => (aZ pk i l m : _root_.MLDSA.Coeff))
        (fun m => (program.intOf (program.reader e) 59 ((l : ℕ) * 256 + m) : _root_.MLDSA.Coeff)) k =
      0
  have h1 := hc i k
  have hW : ((wv i k : ℕ) : _root_.MLDSA.Coeff) =
      ((program.intOf (program.reader e) 62 ((i : ℕ) * 256 + k) : ℤ) : _root_.MLDSA.Coeff) := by
    rw [hw i k, Int.cast_natCast]
  have hA : ∀ l : Fin 4, (fun m : Fin Native.Rows.deg =>
      ((Rows.aKeyOf pk i l m : ℕ) : _root_.MLDSA.Coeff)) =
        fun m : Fin Native.Rows.deg => (aZ pk i l m : _root_.MLDSA.Coeff) :=
    fun l => funext fun m => by
      simp only [aZ, dif_pos (show (m : ℕ) < 256 from m.isLt), Int.cast_natCast]
  have hZ : ∀ l : Fin 4, (fun m : Fin Native.Rows.deg =>
      ((Rows.signedZ zv l m : ℤ) : _root_.MLDSA.Coeff)) =
        fun m : Fin Native.Rows.deg =>
          (program.intOf (program.reader e) 59 ((l : ℕ) * 256 + m) : _root_.MLDSA.Coeff) :=
    fun l => funext fun m => by rw [hz l m]
  have hT : (fun m : Fin Native.Rows.deg =>
      ((Rows.tKeyOf pk i m : ℕ) : _root_.MLDSA.Coeff)) =
      fun m : Fin Native.Rows.deg => (8192 : _root_.MLDSA.Coeff) * (t1Z pk i m : _root_.MLDSA.Coeff) :=
    funext fun m => by
      rw [Emulated.tKeyOf_cast]
      simp only [Emulated.t1Key, t1Z, dif_pos (show (m : ℕ) < 256 from m.isLt),
        Int.cast_natCast, ZMod.natCast_zmod_val]
      norm_num [Native.Params.dBits]
      left
      decide
  have hcc : (fun m : Fin Native.Rows.deg => ((program.evalIntWith (program.reader e) 0 (.ref 7) m -
      2 * program.evalIntWith (program.reader e) 0 (.ref 8) m : ℤ) : _root_.MLDSA.Coeff)) =
        fun m : Fin Native.Rows.deg =>
          (program.evalIntWith (program.reader e) 0 (.ref 7) m : _root_.MLDSA.Coeff) -
            2 * (program.evalIntWith (program.reader e) 0 (.ref 8) m : _root_.MLDSA.Coeff) :=
    funext fun m => by push_cast; ring
  have hsum : ∑ l : Fin Native.Rows.nCols, LatticeCrypto.negacyclicConvCoeff
      (fun m : Fin Native.Rows.deg => ((Rows.aKeyOf pk i l m : ℕ) : _root_.MLDSA.Coeff))
      (fun m : Fin Native.Rows.deg =>
        ((Rows.signedZ zv l m : ℤ) : _root_.MLDSA.Coeff)) k =
      ∑ l : Fin 4, LatticeCrypto.negacyclicConvCoeff
        (fun m : Fin Native.Rows.deg => (aZ pk i l m : _root_.MLDSA.Coeff))
        (fun m : Fin Native.Rows.deg =>
          (program.intOf (program.reader e) 59 ((l : ℕ) * 256 + m) : _root_.MLDSA.Coeff)) k :=
    Finset.sum_congr rfl fun l _ => by rw [hA l, hZ l]
  change ((wv i k : ℕ) : _root_.MLDSA.Coeff) = ∑ l : Fin Native.Rows.nCols,
      LatticeCrypto.negacyclicConvCoeff
        (fun m : Fin Native.Rows.deg => ((Rows.aKeyOf pk i l m : ℕ) : _root_.MLDSA.Coeff))
        (fun m : Fin Native.Rows.deg =>
          ((Rows.signedZ zv l m : ℤ) : _root_.MLDSA.Coeff)) k -
      LatticeCrypto.negacyclicConvCoeff
        (fun m : Fin Native.Rows.deg => ((program.evalIntWith (program.reader e) 0 (.ref 7) m -
          2 * program.evalIntWith (program.reader e) 0 (.ref 8) m : ℤ) : _root_.MLDSA.Coeff))
        (fun m : Fin Native.Rows.deg => ((Rows.tKeyOf pk i m : ℕ) : _root_.MLDSA.Coeff)) k
    at h1
  rw [hW, hT, hcc, DFT.negacyclicConvCoeff_ternary, hsum,
    Falcon512.negacyclicConvCoeff_comm (fun m : Fin Native.Rows.deg =>
      (program.evalIntWith (program.reader e) 0 (.ref 7) m : _root_.MLDSA.Coeff)),
    Falcon512.negacyclicConvCoeff_comm (fun m : Fin Native.Rows.deg =>
      (program.evalIntWith (program.reader e) 0 (.ref 8) m : _root_.MLDSA.Coeff))] at h1
  linear_combination h1

end GordieHowe.MLDSA44.Emulated
