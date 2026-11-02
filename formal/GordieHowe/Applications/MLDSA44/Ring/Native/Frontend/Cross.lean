-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Native.Frontend.Readings

@[expose] public section

/-!
# GordieHowe frontend: the crossing of the native ML-DSA-44 ring programs

`mac.equal` (predicate `248`; `ring_crossing` and the hash's copies of `μ` and `w1` in
`lib/gordiehowe/examples/rings/mldsa_ring.h`, merged into one MAC per domain pair) is
`cross(H, x, A, y)` with `x` the shared expression `513` (H's `μ`, H's `w1`, then H's decoded
support and sign of each coefficient alternately) and `y` the shared expression `50` (A's
`member.mu`, `hint.w1`, `challenge.c`, in order). The compiler's contract
(`GordieHowe.RealizedProgram.HoldsWith` of a cross-field `equal`) gives the readings' equality where
every reading of `x` is below `2`: `μ` and `w1` are bit views, the support and sign bits by
hypothesis (SampleInBall's soundness).

* `RingCrossAt`, `ringCross`: the crossing on the ring's readings.
* `crossAt_pull`: the native frontend's crossing (`MLDSA44.CrossAt`: `w1`, support, sign)
  in the environment read as the native program's.
-/

namespace GordieHowe.MLDSA44.Ring.Native

open GordieHowe.Bits GordieHowe.Ring RealizedProgram

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaRingEmbed program] [MldsaRingRelation program]
  [MldsaRingStmt program] [TableSelect program] [MldsaRingFront program]
  {F0 FH : RealizedProgram.FieldInterp}

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

set_option hygiene false in
local notation "nat" => MldsaRingEmbed.nat program

set_option hygiene false in
local notation "σ" => MldsaRingEmbed.σ program

set_option hygiene false in
local notation "vMuA" => MldsaRingFront.muA program

set_option hygiene false in
local notation "vW1A" => MldsaRingFront.w1A program

set_option hygiene false in
local notation "vMuH" => MldsaRingFront.muH program

set_option hygiene false in
local notation "vW1H" => MldsaRingFront.w1H program

set_option hygiene false in
local notation "vC" => MldsaRingRelation.c program

/-! ## The two operands' coordinates -/

section Operands

variable (rd : program.Valuation interp)

/-- The crossing's `x` read through its parts. -/
theorem x_part {i j k : ℕ} (hj : j < 4)
    (hk : k < program.exprLen (([.leaf vMuH, .leaf vW1H, .ref ((σ).ref 523), .ref ((σ).ref 524)] :
      List Expr)[j]'(by simpa using hj)))
    (he : ∀ m : IndexMap, (∀ t < 6656, m.entry t = t) →
      (∀ k < 256, m.entry (6656 + 2 * k) = 6656 + k) →
      (∀ k < 256, m.entry (6656 + (2 * k + 1)) = 6912 + k) →
      m.entry i = partBase program
        [.leaf vMuH, .leaf vW1H, .ref ((σ).ref 523), .ref ((σ).ref 524)] j + k) :
    program.evalE rd 1 (.ref 513) i = program.evalE rd 1
      (([.leaf vMuH, .leaf vW1H, .ref ((σ).ref 523), .ref ((σ).ref 524)] : List Expr)[j]'
        (by simpa using hj)) k := by
  obtain ⟨m, hm, hlo, hev, hod⟩ := MldsaRingFront.exprH (program := program)
  rw [RealizedProgram.evalE_ref MldsaRingRelation.refsOrdered _ _ MldsaRingFront.lt513, hm]
  exact RealizedProgram.evalE_wiring_part rd 1 m _ _ (by simpa using hj) hk (he m hlo hev hod)

/-- **`x` below `512`** is H's `μ` bit. -/
theorem x_mu {t : ℕ} (ht : t < 512) :
    program.evalE rd 1 (.ref 513) t = program.evalE rd 1 (.leaf vMuH) t :=
  x_part rd (j := 0) (by norm_num) (by simp [exprLen_leaf, MldsaRingFront.lens.2.1, ht])
    fun m hlo _ _ => by rw [hlo t (by omega)]; simp [partBase]

/-- **`x` at `512 + t`** is H's `w1` bit `t`. -/
theorem x_w1 {t : ℕ} (ht : t < 6144) :
    program.evalE rd 1 (.ref 513) (512 + t) = program.evalE rd 1 (.leaf vW1H) t :=
  x_part rd (j := 1) (by norm_num) (by simp [exprLen_leaf, MldsaRingFront.lens.2.2.1, ht])
    fun m hlo _ _ => by
      rw [hlo _ (by omega)]
      simp [partBase, exprLen_leaf, MldsaRingFront.lens.2.1]

/-- **`x` at `6656 + 2 k`** is H's decoded support of coefficient `k`. -/
theorem x_sup {k : ℕ} (hk : k < 256) :
    program.evalE rd 1 (.ref 513) (6656 + 2 * k) =
      program.evalE rd 1 (.ref ((σ).ref 523)) k :=
  x_part rd (j := 2) (by norm_num) (by simp [MldsaRingFront.lens.2.2.2.1, hk])
    fun m _ hev _ => by
      rw [hev k hk]
      simp [partBase, exprLen_leaf, MldsaRingFront.lens.2.1, MldsaRingFront.lens.2.2.1]

/-- **`x` at `6656 + 2 k + 1`** is H's decoded sign of coefficient `k`. -/
theorem x_sgn {k : ℕ} (hk : k < 256) :
    program.evalE rd 1 (.ref 513) (6656 + (2 * k + 1)) =
      program.evalE rd 1 (.ref ((σ).ref 524)) k :=
  x_part rd (j := 3) (by norm_num) (by simp [MldsaRingFront.lens.2.2.2.2.1, hk])
    fun m _ _ hod => by
      rw [hod k hk]
      simp [partBase, exprLen_leaf, MldsaRingFront.lens.2.1, MldsaRingFront.lens.2.2.1,
        MldsaRingFront.lens.2.2.2.1]

/-- The crossing's `y` read through its parts. -/
theorem y_part {i j k : ℕ} (hj : j < 3)
    (hk : k < program.exprLen (([.leaf vMuA, .leaf vW1A, .leaf vC] : List Expr)[j]'
      (by simpa using hj)))
    (he : i = partBase program [.leaf vMuA, .leaf vW1A, .leaf vC] j + k) (hi : i < 7168) :
    program.evalE rd 0 (.ref 50) i = program.evalE rd 0
      (([.leaf vMuA, .leaf vW1A, .leaf vC] : List Expr)[j]'(by simpa using hj)) k := by
  obtain ⟨m, hm, hid⟩ := MldsaRingFront.exprA (program := program)
  rw [RealizedProgram.evalE_ref MldsaRingRelation.refsOrdered _ _
    (by have := MldsaRingFront.lt513 (program := program); omega), hm]
  exact RealizedProgram.evalE_wiring_part rd 0 m _ _ (by simpa using hj) hk
    (by rw [hid i hi]; exact he)

/-- **`y` below `512`** is A's `μ` bit. -/
theorem y_mu {t : ℕ} (ht : t < 512) :
    program.evalE rd 0 (.ref 50) t = program.evalE rd 0 (.leaf vMuA) t :=
  y_part rd (j := 0) (by norm_num) (by simp [exprLen_leaf, MldsaRingFront.muSize, ht])
    (by simp [partBase]) (by omega)

/-- **`y` at `512 + t`** is A's `w1` bit `t`. -/
theorem y_w1 {t : ℕ} (ht : t < 6144) :
    program.evalE rd 0 (.ref 50) (512 + t) = program.evalE rd 0 (.leaf vW1A) t :=
  y_part rd (j := 1) (by norm_num) (by simp [exprLen_leaf, MldsaRingFront.lens.2.2.2.2.2, ht])
    (by simp [partBase, exprLen_leaf, MldsaRingFront.muSize]) (by omega)

/-- **`y` at `6656 + i`** is A's challenge bit `i`. -/
theorem y_c {i : ℕ} (hi : i < 512) :
    program.evalE rd 0 (.ref 50) (6656 + i) = program.evalE rd 0 (.leaf vC) i :=
  y_part rd (j := 2) (by norm_num)
    (by simp [exprLen_leaf, (MldsaRingRelation.sizes (program := program)).2.2.2.2, hi])
    (by simp [partBase, exprLen_leaf, MldsaRingFront.muSize, MldsaRingFront.lens.2.2.2.2.2])
    (by omega)

end Operands

/-! ## The crossing -/

variable [HField FH]

/-- **The crossing at a valuation** (`mac.equal`): A's `μ`, `w1` and challenge bits read as
naturals are H's `μ`, `w1`, decoded support and sign. -/
structure RingCrossAt (rd : program.Valuation interp) : Prop where
  /-- The `μ` bits agree. -/
  mu : ∀ t < 512, (interp 0).toNat (program.evalE rd 0 (.leaf vMuA) t) =
    (interp 1).toNat (program.evalE rd 1 (.leaf vMuH) t)
  /-- The `w1` bits agree. -/
  w1 : ∀ t < 6144, (interp 0).toNat (program.evalE rd 0 (.leaf vW1A) t) =
    (interp 1).toNat (program.evalE rd 1 (.leaf vW1H) t)
  /-- The supports agree. -/
  sup : ∀ k < 256, (interp 0).toNat (program.evalE rd 0 (.leaf vC) (2 * k)) =
    (interp 1).toNat (program.evalE rd 1 (.ref ((σ).ref 523)) k)
  /-- The signs agree. -/
  sgn : ∀ k < 256, (interp 0).toNat (program.evalE rd 0 (.leaf vC) (2 * k + 1)) =
    (interp 1).toNat (program.evalE rd 1 (.ref ((σ).ref 524)) k)

/-- An element of domain `H`'s field that is a bit is read below `2`. -/
theorem toNat_lt_two_of_bool1 {x : (interp 1).K} (h : x = 0 ∨ x = 1) :
    (interp 1).toNat x < 2 := by
  rcases h with rfl | rfl
  · exact (HField.toNat_zero (FH := FH)).symm ▸ Nat.two_pos
  · exact (HField.toNat_one (FH := FH)).symm ▸ Nat.one_lt_two

/-- **`mac.equal` gives the crossing** wherever the source program holds and H's decoded support
and sign are bits: the compiler's contract (`RealizedProgram.HoldsWith` of a cross-field `equal`)
at its premise, every reading of `x` below `2`. -/
theorem ringCross {e : program.Env interp} (hs : program.SourceSatAt e)
    (hsup : ∀ k < 256,
      (interp 1).toNat (program.evalE (program.reader e) 1 (.ref ((σ).ref 523)) k) < 2)
    (hsgn : ∀ k < 256,
      (interp 1).toNat (program.evalE (program.reader e) 1 (.ref ((σ).ref 524)) k) < 2) :
    RingCrossAt (program.reader e) := by
  obtain ⟨hl, hsrc, c, hc⟩ := MldsaRingFront.cross (program := program)
  have hmac : program.HoldsAt e (program.predicate 248).body :=
    hs.preds _ (RealizedProgram.predicate_mem hl) hsrc
  rw [hc] at hmac
  obtain ⟨-, hxy⟩ := hmac
  change (∀ i < program.exprLen (.ref 513),
      (interp (program.domainField 1)).toNat (program.evalE (program.reader e)
        (program.domainField 1) (.ref 513) i) < 2) → ∀ i < program.exprLen (.ref 513),
      (interp (program.domainField 1)).toNat (program.evalE (program.reader e)
        (program.domainField 1) (.ref 513) i) =
      (interp (program.domainField 0)).toNat (program.evalE (program.reader e)
        (program.domainField 0) (.ref 50) i) at hxy
  rw [MldsaRingFront.domains.2, MldsaRingFront.domains.1, MldsaRingFront.lens.1] at hxy
  set rd := program.reader e
  have hpre : ∀ i < 7168, (interp 1).toNat (program.evalE rd 1 (.ref 513) i) < 2 := by
    intro i hi
    by_cases h1 : i < 512
    · rw [x_mu rd h1]
      exact toNat_lt_two_of_bool1
        (RealizedProgram.evalE_leaf_bool_of_isBitView e MldsaRingFront.bitViews.1 1 i)
    by_cases h2 : i < 6656
    · obtain ⟨t, ht, rfl⟩ : ∃ t < 6144, i = 512 + t := ⟨i - 512, by omega, by omega⟩
      rw [x_w1 rd ht]
      exact toNat_lt_two_of_bool1
        (RealizedProgram.evalE_leaf_bool_of_isBitView e MldsaRingFront.bitViews.2 1 t)
    · obtain ⟨k, hk, rfl | rfl⟩ : ∃ k < 256, i = 6656 + 2 * k ∨ i = 6656 + (2 * k + 1) :=
        ⟨(i - 6656) / 2, by omega, by omega⟩
      · rw [x_sup rd hk]
        exact hsup k hk
      · rw [x_sgn rd hk]
        exact hsgn k hk
  have heq := hxy hpre
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · have h := heq t (by omega)
    rw [x_mu rd ht, y_mu rd ht] at h
    exact h.symm
  · have h := heq (512 + t) (by omega)
    rw [x_w1 rd ht, y_w1 rd ht] at h
    exact h.symm
  · have h := heq (6656 + 2 * k) (by omega)
    rw [x_sup rd hk, y_c rd (by omega)] at h
    exact h.symm
  · have h := heq (6656 + (2 * k + 1)) (by omega)
    rw [x_sgn rd hk, y_c rd (by omega)] at h
    exact h.symm

variable [QField F0] [MLDSA44.Native.MldsaAAlgebra nat]

/-- **The native frontend's crossing in the environment read as the native program's**
(`MLDSA44.CrossAt`): its `w1`, support and sign are the ring's. -/
theorem crossAt_pull {e : program.Env interp} (h : RingCrossAt (program.reader e)) :
    MLDSA44.CrossAt ((nat).reader (pull e)) where
  w1 t := by
    rw [w1ABits_pull, w1HBits_pull]
    exact h.w1 t t.isLt
  sup k := by
    rw [cABits_pull, supH_pull e k]
    unfold cBits
    simpa using h.sup k k.isLt
  sgn k := by
    rw [cABits_pull, sgnH_pull e k]
    unfold cBits
    simpa using h.sgn k k.isLt

end GordieHowe.MLDSA44.Ring.Native
