-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import GordieHowe.Applications.Keccak.BitWires

@[expose] public section

/-!
# Bit-level gadgets and their semantics

The circuits compare, increment and pack bit wires with Boolean logic.  Each
operation here is a gadget on `Fin m → K` bit wires computed with field
operations only, paired with a semantics lemma that reads the result as the
natural-number operation under a Booleanity hypothesis.  Soundness proofs of
the gadgets that use them consume the Booleanity hypothesis here and nowhere
else.

Boolean logic on field bits: AND is `a * b`, NOT is `1 - a`, XOR is
`a + b - 2ab`, which is `a + b` in characteristic two.
-/

namespace GordieHowe.Bits

variable {K : Type*} [Field K] [DecidableEq K]

/-- The natural number a Boolean bit vector denotes, little-endian. -/
-- spec-side
def natOfBits {m : ℕ} (bits : BitWires K m) : ℕ := ∑ i, if bits i = 1 then 2 ^ (i : ℕ) else 0

/-- Every wire is `0` or `1`. -/
def AllBool {m : ℕ} (bits : BitWires K m) : Prop := ∀ i, bits i = 0 ∨ bits i = 1

/-- Bit `i` of a constant, as a field element. -/
def constBit (c : ℕ) (i : ℕ) : K := if c / 2 ^ i % 2 = 1 then 1 else 0

def bnot (a : K) : K := 1 - a
def bxor (a b : K) : K := a + b - 2 * a * b

/-- `[bits = c]` for a constant `c`: the product over positions of the bit or
its complement according to `c`'s bit. -/
def eqConst {m : ℕ} (bits : BitWires K m) (c : ℕ) : K :=
  ∏ i : Fin m, if c / 2 ^ (i : ℕ) % 2 = 1 then bits i else bnot (bits i)

/-- `[bits < c]` for a constant `c`, scanning from the most significant bit:
the value is below `c` iff at the first position where they differ the bit is
`0` and `c`'s bit is `1`. -/
def ltConst {m : ℕ} (bits : BitWires K m) (c : ℕ) : K :=
  ∑ i : Fin m,
    (if c / 2 ^ (i : ℕ) % 2 = 1 then bnot (bits i) else 0)
    * ∏ j : Fin m, if (i : ℕ) < j then
        (if c / 2 ^ (j : ℕ) % 2 = 1 then bits j else bnot (bits j)) else 1

/-- `[bits ≤ c]`: `[bits < c + 1]`, and the constant `1` when `c + 1 ≥ 2^m`, where every
`m`-bit value is at most `c` (the test is on the parameter `c`, not on a wire). -/
def leConst {m : ℕ} (bits : BitWires K m) (c : ℕ) : K :=
  if c + 1 < 2 ^ m then ltConst bits (c + 1) else 1

/-- Increment a bit vector modulo `2^m` with carry logic; returns the new bits. -/
def increment {m : ℕ} (bits : BitWires K m) (i : Fin m) : K :=
  let carry : K := ∏ j : Fin m, if (j : ℕ) < i then bits j else 1
  bxor (bits i) carry

/-- Pack bits into a field element along a basis. -/
def packAlong {m : ℕ} (e : Fin m → K) (bits : BitWires K m) : K := ∑ i, bits i * e i

/-! ### Semantics -/

theorem natOfBits_castSucc {m : ℕ} (bits : Fin (m + 1) → K) :
    natOfBits bits = natOfBits (fun i : Fin m => bits i.castSucc) +
      if bits (Fin.last m) = 1 then 2 ^ m else 0 := by
  simp [natOfBits, Fin.sum_univ_castSucc]

theorem natOfBits_lt {m : ℕ} (bits : BitWires K m) : natOfBits bits < 2 ^ m := by
  induction m with
  | zero => simp [natOfBits]
  | succ m ih =>
    rw [natOfBits_castSucc]
    have h := ih (fun i => bits i.castSucc)
    split_ifs <;> simp only [pow_succ] <;> omega

theorem natOfBits_succ {m : ℕ} (bits : Fin (m + 1) → K) :
    natOfBits bits = (if bits 0 = 1 then 1 else 0) +
      2 * natOfBits (fun i : Fin m => bits i.succ) := by
  simp only [natOfBits, Fin.sum_univ_succ, Fin.val_zero, pow_zero,
    Fin.val_succ, pow_succ', Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

omit [DecidableEq K] in
theorem constBit_succ (c i : ℕ) :
    constBit (K := K) c (i + 1) = constBit (c / 2) i := by
  simp [constBit, pow_succ', Nat.div_div_eq_div_mul]

theorem natOfBits_constBit {m : ℕ} (c : ℕ) :
    natOfBits (fun i : Fin m => constBit (K := K) c i) = c % 2 ^ m := by
  induction m generalizing c with
  | zero => simp [natOfBits, Nat.mod_one]
  | succ m ih =>
    rw [natOfBits_succ]
    simp only [Fin.val_succ, constBit_succ, ih, pow_succ', Nat.mod_mul]
    have h := Nat.mod_lt c (by decide : 0 < 2)
    simp only [constBit, Fin.val_zero, pow_zero, Nat.div_one]
    split_ifs <;> simp_all

theorem natOfBits_div_two {m : ℕ} (bits : Fin (m + 1) → K) :
    natOfBits bits / 2 = natOfBits (fun i : Fin m => bits i.succ) := by
  rw [natOfBits_succ, Nat.add_mul_div_left _ _ (by decide)]
  split_ifs <;> simp

theorem constBit_natOfBits {m : ℕ} {bits : BitWires K m} (hb : AllBool bits)
    (i : Fin m) : constBit (natOfBits bits) i = bits i := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [natOfBits_succ]
      rcases hb 0 with h | h <;>
        simp [constBit, h, Nat.add_mul_mod_self_left]
    · rw [Fin.val_succ, constBit_succ, natOfBits_div_two]
      exact ih (fun j => hb j.succ) j

theorem natOfBits_injective {m : ℕ} {a b : BitWires K m}
    (ha : AllBool a) (hb : AllBool b) (h : natOfBits a = natOfBits b) : a = b := by
  funext i
  rw [← constBit_natOfBits ha i, h, constBit_natOfBits hb i]

omit [DecidableEq K] in
theorem constBit_eq_zero_of_lt {c i : ℕ} (h : c < 2 ^ i) :
    constBit (K := K) c i = 0 := by
  simp [constBit, Nat.div_eq_of_lt h]

omit [DecidableEq K] in
theorem constBit_bool (c i : ℕ) :
    constBit (K := K) c i = 0 ∨ constBit (K := K) c i = 1 := by
  unfold constBit
  split_ifs <;> simp

theorem eqConst_eq_indicator {m : ℕ} {bits : BitWires K m} (hb : AllBool bits) (c : ℕ) :
    eqConst bits c = if bits = (fun i : Fin m => constBit c i) then 1 else 0 := by
  classical
  unfold eqConst
  split_ifs with h
  · subst bits
    apply Finset.prod_eq_one
    intro i _
    unfold constBit
    split_ifs <;> simp_all [bnot]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rcases hb i with hzero | hone <;>
      simp_all [constBit, bnot]

theorem eqConst_eq {m : ℕ} {bits : BitWires K m} (hb : AllBool bits) (c : ℕ) :
    eqConst bits c = if natOfBits bits = c % 2 ^ m then 1 else 0 := by
  rw [eqConst_eq_indicator hb]
  congr 1
  apply propext
  constructor
  · intro h
    rw [h, natOfBits_constBit]
  · intro h
    apply natOfBits_injective hb (fun i => constBit_bool c i)
    rw [natOfBits_constBit, h]

omit [DecidableEq K] in
theorem ltConst_succ {m : ℕ} (bits : Fin (m + 1) → K) (c : ℕ) :
    ltConst bits c =
      (if c % 2 = 1 then bnot (bits 0) else 0) *
        eqConst (fun i : Fin m => bits i.succ) (c / 2) +
      ltConst (fun i : Fin m => bits i.succ) (c / 2) := by
  simp only [ltConst, Fin.sum_univ_succ, Fin.val_zero, pow_zero, Nat.div_one]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp [eqConst, pow_succ', Nat.div_div_eq_div_mul]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Fin.prod_univ_succ]
    simp [pow_succ', Nat.div_div_eq_div_mul]

theorem ltConst_eq {m : ℕ} {bits : BitWires K m} (hb : AllBool bits) {c : ℕ} (hc : c < 2 ^ m) :
    ltConst bits c = if natOfBits bits < c then 1 else 0 := by
  induction m generalizing c with
  | zero => simp_all [ltConst, natOfBits]
  | succ m ih =>
    have hc' : c / 2 < 2 ^ m := by
      rw [pow_succ'] at hc
      exact (Nat.div_lt_iff_lt_mul (by decide)).mpr (by simpa [Nat.mul_comm] using hc)
    rw [ltConst_succ, eqConst_eq (fun i => hb i.succ), ih (fun i => hb i.succ) hc',
      Nat.mod_eq_of_lt hc', natOfBits_succ]
    have hcmod := Nat.mod_lt c (by decide : 0 < 2)
    have hcdiv := Nat.mod_add_div c 2
    rcases hb 0 with h | h <;> simp only [h, bnot, sub_zero,
      sub_self, zero_ne_one, ite_false, ite_true, zero_add]
    all_goals split_ifs <;> simp_all <;> omega

/-- The comparator output satisfies the circuit's Booleanity assertion. -/
theorem ltConst_mul_sub_one {m : ℕ} {bits : BitWires K m} (hb : AllBool bits)
    {c : ℕ} (hc : c < 2 ^ m) : ltConst bits c * (ltConst bits c - 1) = 0 := by
  rw [ltConst_eq hb hc]
  split_ifs <;> simp

theorem leConst_eq {m : ℕ} {bits : BitWires K m} (hb : AllBool bits) (c : ℕ) :
    leConst bits c = if natOfBits bits ≤ c then 1 else 0 := by
  unfold leConst
  by_cases hc : c + 1 < 2 ^ m
  · rw [if_pos hc]
    simpa [Nat.lt_succ_iff] using ltConst_eq hb hc
  · have := natOfBits_lt bits
    rw [if_neg hc, if_pos (by omega)]

omit [DecidableEq K] in
theorem bxor_bool {a b : K} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    bxor a b = 0 ∨ bxor a b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [bxor, ← one_add_one_eq_two]

omit [DecidableEq K] in
theorem prod_bool {ι : Type*} (s : Finset ι) (f : ι → K)
    (h : ∀ i ∈ s, f i = 0 ∨ f i = 1) :
    (∏ i ∈ s, f i) = 0 ∨ (∏ i ∈ s, f i) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    rcases h a (by simp) with hzero | hone
    · simp [hzero]
    · simpa [hone] using ih (fun i hi => h i (by simp [hi]))

omit [DecidableEq K] in
theorem increment_allBool {m : ℕ} {bits : BitWires K m} (hb : AllBool bits) :
    AllBool (increment bits) := by
  intro i
  apply bxor_bool (hb i)
  apply prod_bool
  intro j _
  split_ifs
  · exact hb j
  · exact Or.inr rfl

omit [DecidableEq K] in
theorem increment_zero {m : ℕ} (bits : Fin (m + 1) → K) :
    increment bits 0 = 1 - bits 0 := by
  simp [increment, bxor, two_mul, sub_add_eq_sub_sub]

omit [DecidableEq K] in
theorem increment_succ_of_zero {m : ℕ} {bits : Fin (m + 1) → K}
    (h : bits 0 = 0) (i : Fin m) : increment bits i.succ = bits i.succ := by
  simp [increment, Fin.prod_univ_succ, h, bxor]

omit [DecidableEq K] in
theorem increment_succ_of_one {m : ℕ} {bits : Fin (m + 1) → K}
    (h : bits 0 = 1) (i : Fin m) :
    increment bits i.succ = increment (fun j : Fin m => bits j.succ) i := by
  simp [increment, Fin.prod_univ_succ, h]

theorem natOfBits_increment {m : ℕ} {bits : BitWires K m} (hb : AllBool bits) :
    natOfBits (increment bits) = (natOfBits bits + 1) % 2 ^ m := by
  induction m with
  | zero => simp [natOfBits]
  | succ m ih =>
    rw [natOfBits_succ, increment_zero, natOfBits_succ]
    rcases hb 0 with hzero | hone
    · simp only [hzero, sub_zero, ite_true, zero_ne_one, ite_false, zero_add]
      have htail : (fun i : Fin m => increment bits i.succ) =
          (fun i : Fin m => bits i.succ) := funext (increment_succ_of_zero hzero)
      rw [htail, Nat.mod_eq_of_lt]
      · omega
      · have h := natOfBits_lt (fun i : Fin m => bits i.succ)
        rw [pow_succ']
        omega
    · simp only [hone, sub_self, zero_ne_one, ite_false, ite_true, zero_add]
      have htail : (fun i : Fin m => increment bits i.succ) =
          increment (fun i : Fin m => bits i.succ) :=
        funext (increment_succ_of_one hone)
      rw [htail, ih (fun i => hb i.succ), pow_succ']
      have h : 1 + 2 * natOfBits (fun i : Fin m => bits i.succ) + 1 =
          2 * (natOfBits (fun i : Fin m => bits i.succ) + 1) := by omega
      rw [h, Nat.mul_mod_mul_left]

omit [DecidableEq K] in
theorem bxor_eq [CharP K 2] (a b : K) : bxor a b = a + b := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  simp [bxor, htwo]

theorem packAlong_eq_of_bool {m : ℕ} (e : Fin m → K) {bits : BitWires K m} (hb : AllBool bits) :
    packAlong e bits = ∑ i, if bits i = 1 then e i else 0 := by
  apply Finset.sum_congr rfl
  intro i _
  rcases hb i with hi | hi <;> simp [hi]

theorem natOfBits_add {m n : ℕ} (bits : BitWires K (m + n)) :
    natOfBits bits = natOfBits (fun i : Fin m => bits (Fin.castAdd n i)) +
      2 ^ m * natOfBits (fun i : Fin n => bits (Fin.natAdd m i)) := by
  simp only [natOfBits, Fin.sum_univ_add, Fin.val_castAdd, Fin.val_natAdd,
    pow_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-! ### Comparing two bit vectors, and the balanced OR -/

/-- `[a = b]` on one bit: `NOT (a XOR b)`, as `lt_reduce` in `logic.h` forms it. -/
def eqBit (a b : K) : K := bnot (bxor a b)

/-- `[a < b]` for two bit vectors of the same width, least significant bit first.
`lt_reduce` (`logic.h`) splits the range, returning `lt = lt_hi + eq_hi · lt_lo` and
`eq = eq_hi · eq_lo` with the one-bit leaves `lt = NOT(a_i) AND b_i` and `eq = eqBit`;
expanded, that recursion is this sum over the position `i` of the highest differing
bit. -/
def ltVar {m : ℕ} (a b : BitWires K m) : K :=
  ∑ i : Fin m, bnot (a i) * b i * ∏ j : Fin m, if (i : ℕ) < j then eqBit (a j) (b j) else 1

/-- `[a ≤ b]` as `leq` in `logic.h`: `NOT [b < a]`. -/
def leVar {m : ℕ} (a b : BitWires K m) : K := bnot (ltVar b a)

/-- `OR` as `lor` in `logic.h`: `NOT (NOT a AND NOT b)`. -/
def bor (a b : K) : K := bnot (bnot a * bnot b)

/-- `OR` of `f i` for `i0 ≤ i < i1`, with the balanced split of `lor(i0, i1, f)` in
`logic.h`. -/
def orRange (f : ℕ → K) (i0 i1 : ℕ) : K :=
  if i1 ≤ i0 then 0
  else if i1 = i0 + 1 then f i0
  else bor (orRange f i0 (i0 + (i1 - i0) / 2)) (orRange f (i0 + (i1 - i0) / 2) i1)
termination_by i1 - i0
decreasing_by all_goals omega

theorem eqBit_eq {a b : K} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    eqBit a b = if a = b then 1 else 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp [eqBit, bnot, bxor, ← one_add_one_eq_two]

theorem prod_eqBit_eq {m : ℕ} {a b : BitWires K m} (ha : AllBool a) (hb : AllBool b) :
    ∏ i, eqBit (a i) (b i) = if natOfBits a = natOfBits b then 1 else 0 := by
  by_cases h : a = b
  · subst h
    rw [ite_eq_left rfl]
    exact Finset.prod_eq_one fun i _ => by rw [eqBit_eq (ha i) (ha i), ite_eq_left rfl]
  · have hn : natOfBits a ≠ natOfBits b := fun hn => h (natOfBits_injective ha hb hn)
    rw [ite_eq_right hn]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [eqBit_eq (ha i) (hb i), ite_eq_right hi])

omit [DecidableEq K] in
/-- `ltVar` split at the least significant bit. -/
theorem ltVar_succ {m : ℕ} (a b : Fin (m + 1) → K) :
    ltVar a b = bnot (a 0) * b 0 * ∏ j : Fin m, eqBit (a j.succ) (b j.succ) +
      ltVar (fun i : Fin m => a i.succ) (fun i : Fin m => b i.succ) := by
  simp only [ltVar, Fin.sum_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp
  · apply Finset.sum_congr rfl
    intro i _
    rw [Fin.prod_univ_succ]
    simp [Fin.val_succ]

theorem ltVar_eq {m : ℕ} {a b : BitWires K m} (ha : AllBool a) (hb : AllBool b) :
    ltVar a b = if natOfBits a < natOfBits b then 1 else 0 := by
  induction m with
  | zero => simp [ltVar, natOfBits]
  | succ m ih =>
    rw [ltVar_succ, prod_eqBit_eq (fun i => ha i.succ) (fun i => hb i.succ),
      ih (fun i => ha i.succ) (fun i => hb i.succ), natOfBits_succ a, natOfBits_succ b]
    generalize natOfBits (fun i : Fin m => a i.succ) = A
    generalize natOfBits (fun i : Fin m => b i.succ) = B
    rcases ha 0 with h | h <;> rcases hb 0 with h' | h' <;>
      simp only [h, h', bnot, sub_zero, sub_self, zero_mul, mul_zero, one_mul, zero_add,
        zero_ne_one, ite_false, ite_true]
    all_goals split_ifs <;> first | omega | simp

theorem leVar_eq {m : ℕ} {a b : BitWires K m} (ha : AllBool a) (hb : AllBool b) :
    leVar a b = if natOfBits a ≤ natOfBits b then 1 else 0 := by
  rw [leVar, ltVar_eq hb ha, bnot]
  split_ifs <;> first | omega | simp

omit [DecidableEq K] in
theorem bor_ite (p q : Prop) [Decidable p] [Decidable q] :
    bor (if p then (1 : K) else 0) (if q then 1 else 0) = if p ∨ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, bor, bnot]

open Classical in
/-- On bits, the balanced `OR` is `1` exactly when some bit in the range is `1`. -/
theorem orRange_eq {f : ℕ → K} :
    ∀ {i0 i1 : ℕ}, (∀ i, i0 ≤ i → i < i1 → f i = 0 ∨ f i = 1) →
      orRange f i0 i1 = if ∃ i, i0 ≤ i ∧ i < i1 ∧ f i = 1 then 1 else 0 := by
  intro i0 i1
  induction h : i1 - i0 using Nat.strong_induction_on generalizing i0 i1 with
  | _ d ih =>
    intro hf
    rw [orRange]
    by_cases h3 : ∃ i, i0 ≤ i ∧ i < i1 ∧ f i = 1
    · rw [ite_eq_left h3]
      obtain ⟨i, hi, hi', hc⟩ := h3
      split_ifs with h1 h2
      · omega
      · obtain rfl : i = i0 := by omega
        exact hc
      · rw [ih _ (by omega) rfl (fun i hi hi' => hf i hi (by omega)),
          ih _ (by omega) rfl (fun i hi hi' => hf i (by omega) hi'), bor_ite, ite_eq_left]
        by_cases him : i < i0 + (i1 - i0) / 2
        · exact Or.inl ⟨i, hi, him, hc⟩
        · exact Or.inr ⟨i, by omega, hi', hc⟩
    · rw [ite_eq_right h3]
      split_ifs with h1 h2
      · rfl
      · rcases hf i0 le_rfl (by omega) with h0 | h0
        · exact h0
        · exact absurd ⟨i0, le_rfl, by omega, h0⟩ h3
      · rw [ih _ (by omega) rfl (fun i hi hi' => hf i hi (by omega)),
          ih _ (by omega) rfl (fun i hi hi' => hf i (by omega) hi'), bor_ite, ite_eq_right]
        rintro (⟨i, hi, hi', hc⟩ | ⟨i, hi, hi', hc⟩)
        · exact h3 ⟨i, hi, by omega, hc⟩
        · exact h3 ⟨i, by omega, hi', hc⟩

theorem natOfBits_inj {m : ℕ} {a b : BitWires K m} (ha : AllBool a) (hb : AllBool b) :
    natOfBits a = natOfBits b ↔ a = b :=
  ⟨natOfBits_injective ha hb, fun h => h ▸ rfl⟩

/-- A Boolean vector equals the bits of a constant exactly when it denotes the
constant modulo `2^m`. -/
theorem eq_constBit_iff {m : ℕ} {a : BitWires K m} (ha : AllBool a) (c : ℕ) :
    (∀ i, a i = constBit c i) ↔ natOfBits a = c % 2 ^ m := by
  rw [← natOfBits_constBit (K := K) c, natOfBits_inj ha (fun i => constBit_bool c i), funext_iff]

end GordieHowe.Bits
