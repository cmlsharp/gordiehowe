-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.Codes
public import Mathlib.Algebra.CharP.Defs
public import GordieHowe.Foundations.Fields.BinarySpread
public import GordieHowe.Foundations.Fields.PolyRep

@[expose] public section

/-!
# Code arithmetic of the fields of the GKR circuits

The relational check of the GKR circuits (`GordieHowe.GKR.Rel.relOk`) multiplies and adds field
constants as codes, the
naturals of the C++ encoding (`to_bytes_field`). This file gives the code arithmetic
(`GordieHowe.GKR.Fold.CodeArith`) of each family of fields and proves it is the field's under the
decoding (`CodeArith.Hom`):

* **a field of characteristic `p` decoding a code as the cast of a natural** (`primeArith p`):
  sum and product modulo `p` (`primeArith_hom`);
* **an extension `K[X] / (X^n - β)` decoding a code as its coefficient vector** (`ExtCode`,
  `extDecode`): coefficient `i` is digit `i` of `s` bits, read in `K`'s own code; the sum is
  coefficientwise, the product Horner's rule on the coefficients (`PolyRep.mul`), every coefficient
  operation `K`'s code arithmetic (`ExtCode.hom`). This is the C++ encoding of the odd extension
  fields of the programs (`to_bytes_field`, first byte least significant), a tower an extension of
  an extension (`ExtCode.overPrime` over `ZMod p`);
* **a binary field `GF(2)[X] / (f)` decoding a code as its polynomial-basis bits**
  (`BinCode.arith`): the sum is the exclusive or; the product is one product in the spread
  representation of `GordieHowe.BinarySpread` (`Exec.mul`, one `Nat.mul`, two folds and a mask),
  with digits of `k ≥ n + 2` bits so that a code is spread by one product and one mask
  (`BinCode.spread`: `v · Σ_{i<n} 2^((k-1) i)` repeats `v` every `k - 1` bits, and the mask keeps
  bit `j` of the `j`-th copy) and read back by one remainder (`BinCode.unspread`: `2^k ≡ 2` modulo
  `2^(k-1) - 1`). `BinCode.hom` proves it is the field's arithmetic; `Rep.widen` gives the facts of
  a representation with wider digits from those of the field's own.
-/

namespace GordieHowe.GKR.Fold

/-! ## Characteristic `p`, codes read as casts -/

/-- **The code arithmetic modulo `p`**: the sum and the product of the naturals, reduced modulo
`p`. -/
def primeArith (p : ℕ) : CodeArith where
  add a b := (a + b) % p
  mul a b := a * b % p

/-- **Casts of naturals into a ring of characteristic `p`** follow the arithmetic modulo `p`. -/
theorem primeArith_hom {K : Type*} [CommRing K] (p : ℕ) [CharP K p] :
    (primeArith p).Hom (fun n : ℕ => (n : K)) where
  add a b := by rw [primeArith, ← CharP.cast_eq_mod K p, Nat.cast_add]
  mul a b := by rw [primeArith, ← CharP.cast_eq_mod K p, Nat.cast_mul]
  zero := Nat.cast_zero
  one := Nat.cast_one

/-- **A code arithmetic stays below `2^s`**: every sum and product of codes is below `2^s`, so a
code fits a digit of `s` bits. -/
structure CodeArith.Bounded (ar : CodeArith) (s : ℕ) : Prop where
  /-- Sums are below `2^s`. -/
  add : ∀ a b, ar.add a b < 2 ^ s
  /-- Products are below `2^s`. -/
  mul : ∀ a b, ar.mul a b < 2 ^ s

/-- **The arithmetic modulo `p` stays below `2^s`** when `0 < p ≤ 2^s`. -/
theorem primeArith_bounded {p s : ℕ} (hp : 0 < p) (hps : p ≤ 2 ^ s) : (primeArith p).Bounded s where
  add _ _ := (Nat.mod_lt _ hp).trans_le hps
  mul _ _ := (Nat.mod_lt _ hp).trans_le hps

/-! ## Extension fields, codes read as coefficient vectors

An element of `K[X] / (X^n - β)` (`GordieHowe.PolyRep`, power basis `1, X, …, X^(n-1)`) is encoded
as the natural `Σ_{i<n} c_i 2^(s i)`, `c_i` the code of coefficient `i` in `K`'s own encoding:
coefficient `i` is digit `i` in base `2^s` (`digit`), read by `K`'s decoding (`extDecode`). This is
the C++ `to_bytes_field` of every odd extension field of the programs, read as a natural with the
first byte least significant: `Fp2`, `Fp64G2`, `Fp64G4`, `Fp24_6` and `Fp14_N` write coefficient
`i` as the base field's `kBytes` bytes at offset `i · kBytes` (`s = 8 · kBytes`); `NativeWide`
packs coefficient `i` in `kCoefficientBits` bits at bit `i · kCoefficientBits`. A tower is an
extension of an extension: the code of an element of the base is itself a digit string.

`ExtCode.arith` adds coefficientwise and multiplies by Horner's rule on the second factor's
coefficients, as `PolyRep.mul` does, every coefficient operation the base's code arithmetic, so
`ExtCode.hom` proves it is the field's from the base's (`CodeArith.Hom`), for every `K`, `n` and
`β`. Every step is a few natural-number divisions, remainders and products. -/

/-- **Digit `i` of `c` in base `2^s`**: bits `s i` to `s i + s - 1` of `c`. -/
def digit (s c i : ℕ) : ℕ := c / 2 ^ (s * i) % 2 ^ s

/-- **The natural with digits `g 0, …, g (n - 1)` in base `2^s`**: `Σ_{i<n} g i · 2^(s i)`. -/
def undigits (s : ℕ) (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => undigits s g n + g n * 2 ^ (s * n)

/-- Digits of `s` bits make a natural below `2^(s n)`. -/
theorem undigits_lt {s : ℕ} {g : ℕ → ℕ} (hg : ∀ i, g i < 2 ^ s) :
    ∀ n, undigits s g n < 2 ^ (s * n)
  | 0 => by simp [undigits]
  | n + 1 => by
    have h1 := undigits_lt hg n
    have h2 : g n + 1 ≤ 2 ^ s := hg n
    rw [undigits, mul_add, mul_one, pow_add]
    calc undigits s g n + g n * 2 ^ (s * n) < (g n + 1) * 2 ^ (s * n) := by
          rw [add_mul, one_mul]
          omega
      _ ≤ 2 ^ s * 2 ^ (s * n) := Nat.mul_le_mul_right _ h2
      _ = 2 ^ (s * n) * 2 ^ s := mul_comm _ _

/-- **The digits of `undigits`** are the given digits, below `n`, when each has `s` bits. -/
theorem digit_undigits {s : ℕ} {g : ℕ → ℕ} (hg : ∀ i, g i < 2 ^ s) :
    ∀ {n i : ℕ}, i < n → digit s (undigits s g n) i = g i
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, h => by
    have hU := undigits_lt hg n
    rw [undigits, digit]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with hi | rfl
    · obtain ⟨d, rfl⟩ : ∃ d, n = i + (d + 1) := ⟨n - i - 1, by omega⟩
      have hpow : 2 ^ (s * (i + (d + 1))) = 2 ^ (s * d) * 2 ^ s * 2 ^ (s * i) := by
        rw [← pow_add, ← pow_add]
        congr 1
        ring
      rw [hpow, ← mul_assoc, Nat.add_mul_div_right _ _ (by positivity), ← mul_assoc,
        Nat.add_mul_mod_self_right]
      exact digit_undigits hg hi
    · rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hU, zero_add,
        Nat.mod_eq_of_lt (hg i)]

/-- **The coefficient vector of a code**: coefficient `i` is digit `i` in base `2^s`, read by the
base field's decoding `κ`. -/
def extDecode {K : Type*} (κ : ℕ → K) (s n c : ℕ) : Vector K n :=
  Vector.ofFn fun i => κ (digit s c i)

/-- Coefficient `i` of a code's vector is its digit `i`, decoded. -/
@[simp] theorem extDecode_getElem {K : Type*} (κ : ℕ → K) (s n c : ℕ) (i : ℕ) (hi : i < n) :
    (extDecode κ s n c)[i] = κ (digit s c i) := by
  simp [extDecode]

/-- The vector of `undigits` is the vector of decoded digits, when each has `s` bits. -/
theorem extDecode_undigits {K : Type*} (κ : ℕ → K) {s n : ℕ} {g : ℕ → ℕ}
    (hg : ∀ i, g i < 2 ^ s) : extDecode κ s n (undigits s g n) = Vector.ofFn fun i => κ (g i) := by
  ext i hi
  simp [digit_undigits hg hi]

/-- **A code below `2^s` is a constant**: its vector is `PolyRep.const` of its decoding, when `κ`
decodes `0` to `0`. -/
theorem extDecode_of_lt {K : Type} [CommRing K] (κ : ℕ → K) (h0 : κ 0 = 0) {s n c : ℕ}
    (hc : c < 2 ^ s) : extDecode κ s n c = PolyRep.const (κ c) := by
  ext i hi
  rw [extDecode_getElem, PolyRep.const, Vector.getElem_ofFn, digit]
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp [Nat.mod_eq_of_lt hc]
  · have : c < 2 ^ (s * i) := hc.trans_le (Nat.pow_le_pow_right (by norm_num)
      (Nat.le_mul_of_pos_right s hpos))
    simp [Nat.div_eq_of_lt this, h0, hpos.ne']

/-- **The code arithmetic of an extension `K[X] / (X^n - β)`** over a base code arithmetic, codes
read as coefficient vectors (`extDecode`): `n` coefficients of `s` bits, `beta` the code of `β`. -/
structure ExtCode where
  /-- The code arithmetic of the base field `K`. -/
  base : CodeArith
  /-- The bits per coefficient. -/
  s : ℕ
  /-- The degree `n`. -/
  n : ℕ
  /-- The code of `β`, with `X^n = β`. -/
  beta : ℕ

namespace ExtCode

variable (E : ExtCode)

/-- The code of the sum: the coefficientwise sums. -/
def add (a b : ℕ) : ℕ :=
  undigits E.s (fun i => E.base.add (digit E.s a i) (digit E.s b i)) E.n

/-- Coefficient `i` of `X · acc + b_j · a` (`PolyRep.mulStep`): coefficient `i - 1` of `acc`, or
`β` times its top coefficient at `i = 0`, plus `b_j a_i`. -/
def stepDigit (a b j acc i : ℕ) : ℕ :=
  E.base.add (if i = 0 then E.base.mul E.beta (digit E.s acc (E.n - 1)) else digit E.s acc (i - 1))
    (E.base.mul (digit E.s b j) (digit E.s a i))

/-- One step of Horner's rule: the code of `X · acc + b_j · a`. -/
def step (a b j acc : ℕ) : ℕ := undigits E.s (E.stepDigit a b j acc) E.n

/-- The code of the product: Horner's rule on the coefficients of `b` from `X^(n-1)` down to `X^0`
(`PolyRep.mul`). -/
def mul (a b : ℕ) : ℕ := (List.range E.n).foldr (E.step a b) 0

/-- **The code arithmetic of the extension.** -/
def arith : CodeArith where
  add := E.add
  mul := E.mul

/-- **The extension's codes stay below `2^(s n)`** when the base's stay below `2^s`. -/
theorem arith_bounded (hb : E.base.Bounded E.s) : E.arith.Bounded (E.s * E.n) where
  add _ _ := undigits_lt (fun _ => hb.add _ _) _
  mul a b := by
    change (List.range E.n).foldr (E.step a b) 0 < _
    rcases h : List.range E.n with _ | ⟨j, l⟩
    · exact Nat.pos_of_ne_zero (by positivity)
    · exact undigits_lt (fun _ => hb.add _ _) _

variable {E} {K : Type} [Field K] {β : K} {card : ℕ} {f : Polynomial K} {κ : ℕ → K}

/-- One code step of Horner's rule decodes to `PolyRep.mulStep`. -/
theorem extDecode_step (hκ : E.base.Hom κ) (hβ : κ E.beta = β) (hb : E.base.Bounded E.s)
    (hn : 0 < E.n) (a b j acc : ℕ) (hj : j < E.n) :
    extDecode κ E.s E.n (E.step a b j acc) =
      PolyRep.mulStep (PolyRep.binomial β) (extDecode κ E.s E.n a) (extDecode κ E.s E.n b) j
        (extDecode κ E.s E.n acc) := by
  rw [step, extDecode_undigits κ (g := E.stepDigit a b j acc) fun _ => hb.add _ _]
  have hc : ∀ c k, k < E.n → PolyRep.coeff (extDecode κ E.s E.n c) k = κ (digit E.s c k) :=
    fun c k hk => by simp [PolyRep.coeff, hk]
  ext i hi
  rw [Vector.getElem_ofFn, PolyRep.mulStep, PolyRep.add, Vector.getElem_ofFn, PolyRep.timesX,
    PolyRep.getElem_ofFn_fin, PolyRep.smul, PolyRep.getElem_ofFn_fin, stepDigit, hκ.add, hκ.mul,
    hc _ _ (Nat.sub_lt hn Nat.one_pos), hc _ _ hj]
  simp only [PolyRep.binomial, Fin.getElem_fin, extDecode_getElem]
  split_ifs with h0
  · rw [hκ.mul, hβ, zero_add, mul_comm]
  · rw [hc _ _ (by omega), mul_zero, add_zero]

/-- **The extension's code arithmetic is the field's**: for `K[X] / (X^n - β)` with the operations
of `PolyRep` (`PolyRep.Spec` at `PolyRep.binomial β`), codes read as coefficient vectors
(`extDecode`), when the base's code arithmetic is `K`'s under `κ`, stays below `2^s`, and `beta`
decodes to `β`. -/
theorem hom (S : PolyRep.Spec (PolyRep.binomial β : Fin E.n → K) card f) (hκ : E.base.Hom κ)
    (hβ : κ E.beta = β) (hb : E.base.Bounded E.s) :
    letI := (PolyRep.ops (PolyRep.binomial β) card).field S.isField
    E.arith.Hom (extDecode κ E.s E.n) := by
  let _ := (PolyRep.ops (PolyRep.binomial β) card).field S.isField
  have hn := S.n_pos
  have h0 : extDecode κ E.s E.n 0 = PolyRep.zero := by
    ext i hi
    simp [digit, hκ.zero, PolyRep.zero]
  refine ⟨fun a b => ?_, fun a b => ?_, h0, ?_⟩
  · change extDecode κ E.s E.n (E.add a b) = PolyRep.add _ _
    rw [add, extDecode_undigits κ fun _ => hb.add _ _]
    ext i hi
    simp [PolyRep.add, hκ.add]
  · change extDecode κ E.s E.n (E.mul a b) = PolyRep.mul _ _ _
    rw [mul, PolyRep.mul]
    have key : ∀ l : List ℕ, (∀ j ∈ l, j < E.n) →
        extDecode κ E.s E.n (l.foldr (E.step a b) 0) =
          l.foldr (PolyRep.mulStep (PolyRep.binomial β) (extDecode κ E.s E.n a)
            (extDecode κ E.s E.n b)) PolyRep.zero := by
      intro l hl
      induction l with
      | nil => exact h0
      | cons j l ih =>
        rw [List.foldr_cons, List.foldr_cons, extDecode_step hκ hβ hb hn _ _ _ _
          (hl j List.mem_cons_self), ih fun x hx => hl x (List.mem_cons_of_mem _ hx)]
    exact key _ fun j hj => List.mem_range.mp hj
  · change extDecode κ E.s E.n 1 = PolyRep.const 1
    have hs : E.s ≠ 0 := by
      rintro hs
      have h := hb.mul 1 1
      rw [hs, pow_zero, Nat.lt_one_iff] at h
      have := hκ.mul 1 1
      rw [h, hκ.zero, hκ.one, mul_one] at this
      exact zero_ne_one this
    rw [extDecode_of_lt κ hκ.zero (Nat.one_lt_two_pow hs), hκ.one]

/-- **The code arithmetic of a binomial extension of `ZMod p`**: `n` coefficients of `s` bits, the
arithmetic modulo `p` on each, `X^n = β` with `beta` the code of `β`. -/
def overPrime (p s n beta : ℕ) : ExtCode := ⟨primeArith p, s, n, beta⟩

/-- **The code arithmetic of a binomial extension of `ZMod p` is the field's** (`ExtCode.hom` at the
arithmetic modulo `p`), when `p ≤ 2^s`. -/
theorem overPrime_hom {p : ℕ} [Fact p.Prime] {s n beta card : ℕ} {β : ZMod p}
    {f : Polynomial (ZMod p)} (S : PolyRep.Spec (PolyRep.binomial β : Fin n → ZMod p) card f)
    (hβ : (beta : ZMod p) = β) (hps : p ≤ 2 ^ s) :
    letI := (PolyRep.ops (PolyRep.binomial β) card).field S.isField
    (overPrime p s n beta).arith.Hom (extDecode (fun c : ℕ => (c : ZMod p)) s n) :=
  hom (E := overPrime p s n beta) S (primeArith_hom p) hβ
    (primeArith_bounded (Fact.out : p.Prime).pos hps)

/-- **A constant below `p` decodes to its cast** in a binomial extension of `ZMod p`, when
`p ≤ 2^s`. -/
theorem extDecode_natCast_of_lt {p s n c : ℕ} (hps : p ≤ 2 ^ s) (hc : c < p) :
    extDecode (fun c : ℕ => (c : ZMod p)) s n c = PolyRep.const (c : ZMod p) :=
  extDecode_of_lt _ Nat.cast_zero (hc.trans_le hps)

end ExtCode

/-! ## Binary fields, codes read as polynomial-basis bits -/

open Polynomial BinarySpread

/-- **A binary field's code arithmetic**: the spread representation `E` (digits of `E.k` bits, `E.n`
of them) and the repetition constant `rep = Σ_{i < n} 2^((k-1) i)` (`Nat.ones (k - 1) n`), kept as
data so the kernel does not recompute it. -/
structure BinCode where
  /-- The spread representation. -/
  E : Exec
  /-- `Nat.ones (E.k - 1) E.n`. -/
  rep : ℕ

/-- The spread representation of the `n` low bits of `v`: `v` repeated every `k - 1` bits, bit `j`
of the `j`-th copy kept. -/
def BinCode.spread (B : BinCode) (v : ℕ) : ℕ := (v % 2 ^ B.E.n * B.rep) &&& B.E.mask

/-- The code of a spread natural: its remainder modulo `2^(k-1) - 1`. -/
def BinCode.unspread (B : BinCode) (N : ℕ) : ℕ := N % (2 ^ (B.E.k - 1) - 1)

/-- **The code arithmetic of a binary field**: exclusive or, and the spread product. -/
def BinCode.arith (B : BinCode) : CodeArith where
  add a b := a ^^^ b
  mul a b := B.unspread (B.E.mul (B.spread a) (B.spread b))

/-- The bits of `u · Σ_{i<n} 2^(s i)`, for `u < 2^s`: bit `t` is bit `t mod s` of `u`, below
`s n`. -/
theorem testBit_mul_ones {s u : ℕ} (hs : 0 < s) (hu : u < 2 ^ s) :
    ∀ (n t : ℕ), (u * Nat.ones s n).testBit t = (decide (t / s < n) && u.testBit (t % s))
  | 0, t => by simp [Nat.ones]
  | n + 1, t => by
    rw [Nat.ones, mul_add, mul_one, mul_left_comm, add_comm, Nat.testBit_two_pow_mul_add _ hu]
    split_ifs with ht
    · rw [Nat.div_eq_of_lt ht, Nat.mod_eq_of_lt ht]
      simp
    · obtain ⟨t', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp ht)
      rw [Nat.add_sub_cancel_left, testBit_mul_ones hs hu n t', Nat.add_div_left _ hs,
        Nat.add_mod_left]
      simp

/-- The bits of a spread natural: bit `k q` is bit `q` of `v`, for `q < n`; the others are `0`. -/
theorem testBit_spread (E : Exec) (hk : 0 < E.k) :
    ∀ (n v t : ℕ), (E.spread n v).testBit t =
      (decide (t / E.k < n) && decide (t % E.k = 0) && v.testBit (t / E.k))
  | 0, v, t => by simp [Exec.spread]
  | n + 1, v, t => by
    have h2 : v % 2 < 2 ^ E.k :=
      (Nat.mod_lt _ (by norm_num)).trans_le (by simpa using Nat.pow_le_pow_right (by norm_num) hk)
    rw [Exec.spread, add_comm, Nat.testBit_two_pow_mul_add _ h2]
    split_ifs with ht
    · rw [Nat.div_eq_of_lt ht, Nat.mod_eq_of_lt ht]
      rcases Nat.eq_zero_or_pos t with rfl | h
      · rw [show v % 2 = v % 2 ^ 1 from rfl, Nat.testBit_mod_two_pow]
        simp
      · have : (v % 2).testBit t = false :=
          Nat.testBit_lt_two_pow ((Nat.mod_lt _ (by norm_num)).trans_le
            (by simpa using Nat.pow_le_pow_right (by norm_num) (Nat.succ_le_of_lt h)))
        simp [this, h.ne']
    · obtain ⟨t', rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp ht)
      rw [Nat.add_sub_cancel_left, testBit_spread E hk n (v / 2) t', Nat.add_div_left _ hk,
        Nat.add_mod_left, Nat.testBit_div_two]
      simp

/-- **One product and one mask spread a code** when the digits have at least `n + 1` bits. -/
theorem BinCode.spread_eq (B : BinCode) {f : (ZMod 2)[X]} (R : Rep B.E f)
    (hk : B.E.n + 1 < B.E.k) (hrep : B.rep = Nat.ones (B.E.k - 1) B.E.n) (v : ℕ) :
    B.spread v = B.E.ofBits v := by
  have hk0 : 0 < B.E.k := by omega
  obtain ⟨s, hs⟩ : ∃ s, B.E.k = s + 1 := ⟨B.E.k - 1, by omega⟩
  have hvs : v % 2 ^ B.E.n < 2 ^ (B.E.k - 1) :=
    (Nat.mod_lt _ (by positivity)).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine Nat.eq_of_testBit_eq fun t => ?_
  rw [BinCode.spread, Exec.ofBits, Nat.testBit_and, hrep, testBit_mul_ones (by omega) hvs, R.mask_eq,
    testBit_spread B.E hk0, ← one_mul (Nat.ones B.E.k B.E.n),
    testBit_mul_ones hk0 (u := 1) (Nat.one_lt_two_pow hk0.ne')]
  rw [hs] at hk ⊢
  simp only [Nat.add_sub_cancel, Nat.testBit_mod_two_pow]
  by_cases hm : t % (s + 1) = 0
  · obtain ⟨q, rfl⟩ : ∃ q, t = (s + 1) * q := ⟨t / (s + 1), by
      have := Nat.div_add_mod t (s + 1); omega⟩
    rw [Nat.mul_div_cancel_left _ (Nat.succ_pos s)]
    by_cases hq : q < B.E.n
    · have hqs : q < s := by omega
      have h1 : (s + 1) * q / s = q := by
        rw [add_mul, one_mul, Nat.mul_add_div (by omega : 0 < s), Nat.div_eq_of_lt hqs, add_zero]
      have h2 : (s + 1) * q % s = q := by
        rw [add_mul, one_mul, Nat.mul_add_mod, Nat.mod_eq_of_lt hqs]
      simp [h1, h2, hq]
    · simp [hq]
  · have h1 : Nat.testBit 1 (t % (s + 1)) = false := by
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hm
      rw [hj, Nat.testBit_succ]
      simp
    simp [h1, hm]

/-- A polynomial with binary coefficients, below degree `n`, evaluated at `2`: the natural whose
`n` low bits are its coefficients. -/
theorem bitsVal_eval_two {f : (ZMod 2)[X]} {n : ℕ} {P : ℕ[X]} (hP : Bounded 2 n P) :
    bitsVal f n (P.eval 2) = toAdjoin f P := by
  let E1 : Exec := ⟨1, n, 0, 0⟩
  have hsp : ∀ i v, E1.spread i v = v % 2 ^ i := by
    intro i
    induction i with
    | zero => intro v; simp [Exec.spread, Nat.mod_one]
    | succ i ih =>
      intro v
      rw [Exec.spread, ih, pow_succ' 2 i, Nat.mod_mul]
      simp [E1]
  obtain ⟨P', hP', hPe, hPv⟩ := Rep.spread_spec (E := E1) (f := f) n (P.eval 2)
  have hlt : P.eval 2 < 2 ^ n := hP.eval_lt
  rw [hsp, Nat.mod_eq_of_lt hlt] at hPe
  have h1 : Bounded (2 ^ E1.k) E1.n P := by simpa [E1] using hP
  have h2 : Bounded (2 ^ E1.k) E1.n P' := by simpa [E1] using hP'
  have hPP : P' = P := by
    have a := digitPoly_eval h1
    have b := digitPoly_eval h2
    simp only [E1, pow_one] at a b hPe
    rw [← a, ← b, hPe]
  rw [← hPv, hPP]

/-- **The remainder modulo `2^(k-1) - 1` reads a canonical spread natural** as its code. -/
theorem BinCode.unspread_eval (B : BinCode) (hk : B.E.n + 1 < B.E.k) {P : ℕ[X]}
    (hP : Bounded 2 B.E.n P) : B.unspread (P.eval (2 ^ B.E.k)) = P.eval 2 := by
  obtain ⟨s, hs⟩ : ∃ s, B.E.k = s + 1 := ⟨B.E.k - 1, by omega⟩
  have hlt : P.eval 2 < 2 ^ s - 1 := by
    have := hP.eval_lt
    have : 2 ^ (B.E.n + 1) ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ] at this
    omega
  rw [BinCode.unspread, hs, Nat.add_sub_cancel, ← Nat.mod_eq_of_lt hlt]
  rw [← ZMod.natCast_eq_natCast_iff']
  have key : ∀ a : ℕ, ((P.eval a : ℕ) : ZMod (2 ^ s - 1)) =
      (P.map (Nat.castRingHom _)).eval (a : ZMod (2 ^ s - 1)) := fun a => by
    rw [Polynomial.eval_natCast_map, Nat.cast_id]
    rfl
  rw [key, key]
  congr 1
  have h1 : (2 ^ s - 1 : ℕ) + 1 = 2 ^ s := Nat.sub_add_cancel Nat.one_le_two_pow
  have : ((2 ^ s : ℕ) : ZMod (2 ^ s - 1)) = 1 := by
    rw [← h1, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
  push_cast at this ⊢
  rw [pow_succ, this, one_mul]

/-- **The binary code arithmetic is the field's**: with digits of `k ≥ n + 2` bits, under any
decoding `κc` whose image in `AdjoinRoot f` is the polynomial-basis reading `bitsVal f n`. -/
theorem BinCode.hom (B : BinCode) {f : (ZMod 2)[X]} (R : Rep B.E f) (hk : B.E.n + 1 < B.E.k)
    (hrep : B.rep = Nat.ones (B.E.k - 1) B.E.n) {L : Type*} [CommRing L] (e : L ≃+* AdjoinRoot f)
    {κc : ℕ → L} (hκ : ∀ c, e (κc c) = bitsVal f B.E.n c) : B.arith.Hom κc where
  add a b := by
    apply e.injective
    rw [map_add, hκ, hκ, hκ, BinCode.arith, bitsVal, bitsVal, bitsVal, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.testBit_xor]
    exact BinaryRep.ite_xor_eq_add_of_add_self BinaryRep.adjoinRoot_add_self _ _ _
  mul a b := by
    apply e.injective
    have hsa := B.spread_eq R hk hrep a
    have hsb := B.spread_eq R hk hrep b
    obtain ⟨P, hP, hPe⟩ := R.canon_mul (Rep.canon_ofBits (E := B.E) a) (Rep.canon_ofBits b)
    rw [map_mul, hκ, hκ, hκ, BinCode.arith]
    dsimp only
    rw [hsa, hsb, ← hPe, B.unspread_eval hk hP, bitsVal_eval_two hP, ← R.val_eval hP, hPe,
      R.val_mul (Rep.canon_ofBits a) (Rep.canon_ofBits b), R.val_ofBits, R.val_ofBits]
  zero := by
    apply e.injective
    rw [hκ, map_zero, bitsVal]
    simp
  one := by
    apply e.injective
    rw [hκ, map_one, bitsVal, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr R.n_pos)]
    · simp
    · intro j _ hj
      simp [Nat.testBit_one_eq_true_iff_self_eq_zero, hj]

/-- **The facts of a representation with wider digits**: the same tap polynomial and degree, digits
of `E'.k ≥ E.k` bits, the tap natural and mask at the new width. -/
noncomputable def Rep.widen {E : Exec} {f : (ZMod 2)[X]} (R : Rep E f) (E' : Exec) (hn : E'.n = E.n)
    (hk : E.k ≤ E'.k) (htap : E'.tapN = R.tap.eval (2 ^ E'.k))
    (hmask : E'.mask = Nat.ones E'.k E'.n) : Rep E' f where
  tap := R.tap
  d := R.d
  two_le_k := R.two_le_k.trans hk
  tap_bounded := R.tap_bounded
  tapN_eq := htap
  mask_eq := hmask
  root_pow := hn ▸ R.root_pow
  natDegree_eq := hn ▸ R.natDegree_eq
  n_pos := hn ▸ R.n_pos
  deg_le := hn ▸ R.deg_le
  coeff_le := hn ▸ R.coeff_le.trans (Nat.pow_le_pow_right (by norm_num) hk)

/-! ## The prime-subfield fast path of a code arithmetic -/

/-- **A code arithmetic is arithmetic modulo `p` on the codes below `p`** (its prime subfield, when
the field's characteristic is `p`). Every arithmetic has it at `p = 0`. -/
structure CodeArith.PrimeOn (ar : CodeArith) (p : ℕ) : Prop where
  /-- Sums of codes below `p`. -/
  add : ∀ a b, a < p → b < p → ar.add a b = (a + b) % p
  /-- Products of codes below `p`. -/
  mul : ∀ a b, a < p → b < p → ar.mul a b = a * b % p

/-- **The arithmetic with the fast path**: codes below `p` by arithmetic modulo `p`, any other pair
by `ar`. -/
def CodeArith.withPrime (ar : CodeArith) (p : ℕ) : CodeArith where
  add a b := cond (Nat.blt a p && Nat.blt b p) ((a + b) % p) (ar.add a b)
  mul a b := cond (Nat.blt a p && Nat.blt b p) (a * b % p) (ar.mul a b)

/-- **The fast path is the arithmetic.** -/
theorem CodeArith.withPrime_eq {ar : CodeArith} {p : ℕ} (h : ar.PrimeOn p) : ar.withPrime p = ar := by
  cases ar with
  | mk add mul =>
    unfold CodeArith.withPrime
    congr 1
    · funext a b
      cases hab : (Nat.blt a p && Nat.blt b p)
      · rfl
      · simp only [Bool.and_eq_true, Nat.blt_eq] at hab
        exact (h.add a b hab.1 hab.2).symm
    · funext a b
      cases hab : (Nat.blt a p && Nat.blt b p)
      · rfl
      · simp only [Bool.and_eq_true, Nat.blt_eq] at hab
        exact (h.mul a b hab.1 hab.2).symm

/-- **The fast path keeps the field's arithmetic.** -/
theorem CodeArith.Hom.withPrime {F : Type*} [CommSemiring F] {ar : CodeArith} {κc : ℕ → F}
    (hA : ar.Hom κc) {p : ℕ} (h : ar.PrimeOn p) : (ar.withPrime p).Hom κc := by
  rw [CodeArith.withPrime_eq h]
  exact hA

/-- **No fast path**: every arithmetic is arithmetic modulo `0` below `0`. -/
theorem CodeArith.primeOn_zero (ar : CodeArith) : ar.PrimeOn 0 where
  add _ _ h := absurd h (Nat.not_lt_zero _)
  mul _ _ h := absurd h (Nat.not_lt_zero _)

/-- **The arithmetic modulo `p`** is itself on every code. -/
theorem primeArith_primeOn (p : ℕ) : (primeArith p).PrimeOn p where
  add _ _ _ _ := rfl
  mul _ _ _ _ := rfl

/-- Digit `0` of a code below `2^s` is the code. -/
theorem digit_zero_of_lt {s c : ℕ} (hc : c < 2 ^ s) : digit s c 0 = c := by
  simp [digit, Nat.mod_eq_of_lt hc]

/-- Digits `i ≥ 1` of a code below `2^s` are `0`. -/
theorem digit_eq_zero_of_lt {s c i : ℕ} (hc : c < 2 ^ s) (hi : 0 < i) : digit s c i = 0 := by
  have : c < 2 ^ (s * i) :=
    hc.trans_le (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right s hi))
  simp [digit, Nat.div_eq_of_lt this]

/-- Digits of `0` are `0`. -/
@[simp] theorem digit_zero_left (s i : ℕ) : digit s 0 i = 0 := by simp [digit]

/-- A digit string zero above position `0` is its digit `0`. -/
theorem undigits_of_eq_zero {s : ℕ} {g : ℕ → ℕ} (hg : ∀ i, 0 < i → g i = 0) :
    ∀ n, undigits s g (n + 1) = g 0
  | 0 => by simp [undigits]
  | n + 1 => by rw [undigits, undigits_of_eq_zero hg n, hg _ n.succ_pos, zero_mul, add_zero]

namespace ExtCode

theorem overPrime_add_of_lt {p s n beta a b : ℕ} (hps : p ≤ 2 ^ s) (hn : 0 < n)
    (ha : a < p) (hb : b < p) : (overPrime p s n beta).add a b = (a + b) % p := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have ha' := ha.trans_le hps
  have hb' := hb.trans_le hps
  change undigits s (fun i => (digit s a i + digit s b i) % p) (m + 1) = _
  rw [undigits_of_eq_zero, digit_zero_of_lt ha', digit_zero_of_lt hb']
  intro i hi
  simp [digit_eq_zero_of_lt ha' hi, digit_eq_zero_of_lt hb' hi]

theorem overPrime_mul_of_lt {p s n beta a b : ℕ} (hps : p ≤ 2 ^ s) (hn : 0 < n)
    (ha : a < p) (hb : b < p) : (overPrime p s n beta).mul a b = a * b % p := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have ha' := ha.trans_le hps
  have hb' := hb.trans_le hps
  set E := overPrime p s (m + 1) beta
  -- steps `j ≥ 1` keep the accumulator `0`
  have hstep : ∀ j, 0 < j → E.step a b j 0 = 0 := by
    intro j hj
    change undigits s (E.stepDigit a b j 0) (m + 1) = 0
    rw [undigits_of_eq_zero]
    · simp [E, stepDigit, overPrime, primeArith, digit_eq_zero_of_lt hb' hj]
    · intro i _
      simp [E, stepDigit, overPrime, primeArith, digit_eq_zero_of_lt hb' hj]
  have hfold : ∀ l : List ℕ, (∀ j ∈ l, 0 < j) → l.foldr (E.step a b) 0 = 0 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons j l ih =>
      rw [List.foldr_cons, ih fun x hx => hl x (List.mem_cons_of_mem _ hx),
        hstep j (hl j List.mem_cons_self)]
  change (List.range (m + 1)).foldr (E.step a b) 0 = _
  rw [List.range_succ_eq_map, List.foldr_cons, hfold _ (by simp)]
  change undigits s (E.stepDigit a b 0 0) (m + 1) = _
  rw [undigits_of_eq_zero]
  · simp [E, stepDigit, overPrime, primeArith, digit_zero_of_lt ha', digit_zero_of_lt hb', mul_comm]
  · intro i hi
    simp [E, stepDigit, overPrime, primeArith, digit_eq_zero_of_lt ha' hi, hi.ne']

/-- **A binomial extension of `ZMod p` is arithmetic modulo `p` on its prime subfield**, when
`p ≤ 2^s` and the degree is positive. -/
theorem overPrime_primeOn {p s n beta : ℕ} (hps : p ≤ 2 ^ s) (hn : 0 < n) :
    (overPrime p s n beta).arith.PrimeOn p where
  add _ _ ha hb := overPrime_add_of_lt hps hn ha hb
  mul _ _ ha hb := overPrime_mul_of_lt hps hn ha hb

end ExtCode

/-! ## Towers -/

/-- **The code `0` absorbs**: a product with `0` is `0`, and `0 + 0` is `0`. -/
structure CodeArith.Absorbs (ar : CodeArith) : Prop where
  /-- A product with a right factor `0`. -/
  mul_zero : ∀ a, ar.mul a 0 = 0
  /-- A product with a left factor `0`. -/
  zero_mul : ∀ a, ar.mul 0 a = 0
  /-- The sum of two `0`s. -/
  add_zero : ar.add 0 0 = 0

/-- **The arithmetic modulo `p` absorbs.** -/
theorem primeArith_absorbs (p : ℕ) : (primeArith p).Absorbs where
  mul_zero _ := by simp [primeArith]
  zero_mul _ := by simp [primeArith]
  add_zero := by simp [primeArith]

/-- Digits all `0` make `0`. -/
theorem undigits_eq_zero {s : ℕ} {g : ℕ → ℕ} (hg : ∀ i, g i = 0) : ∀ n, undigits s g n = 0
  | 0 => rfl
  | n + 1 => by rw [undigits, undigits_eq_zero hg n, hg, zero_mul, add_zero]

namespace ExtCode

variable {E : ExtCode}

/-- A step from the accumulator `0` with every coefficient `0` is `0`. -/
theorem step_zero {a b j : ℕ} (h : ∀ i, E.stepDigit a b j 0 i = 0) : E.step a b j 0 = 0 :=
  undigits_eq_zero h _

/-- Horner's rule with every step from `0` to `0` is `0`. -/
theorem foldr_step_zero {a b : ℕ} (h : ∀ j, E.step a b j 0 = 0) :
    ∀ l : List ℕ, l.foldr (E.step a b) 0 = 0
  | [] => rfl
  | j :: l => by rw [List.foldr_cons, foldr_step_zero h l, h]

/-- **An extension over an absorbing base absorbs.** -/
theorem absorbs (hz : E.base.Absorbs) : E.arith.Absorbs where
  mul_zero a := by
    refine foldr_step_zero (fun j => step_zero fun i => ?_) _
    unfold stepDigit
    split_ifs <;> simp [hz.mul_zero, hz.zero_mul, hz.add_zero]
  zero_mul a := by
    refine foldr_step_zero (fun j => step_zero fun i => ?_) _
    unfold stepDigit
    split_ifs <;> simp [hz.mul_zero, hz.zero_mul, hz.add_zero]
  add_zero := undigits_eq_zero (fun _ => by simp [hz.add_zero]) _

/-- **An extension over a base that is arithmetic modulo `p` on the codes below `p` is too** (its
prime subfield), when the base absorbs, `0 < p ≤ 2^s` and the degree is positive: a tower of any
depth over `ZMod p` (`overPrime_primeOn` at the bottom, `absorbs` at every step). -/
theorem primeOn {p : ℕ} (hb : E.base.PrimeOn p) (hz : E.base.Absorbs) (hp : 0 < p)
    (hps : p ≤ 2 ^ E.s) (hn : 0 < E.n) : E.arith.PrimeOn p := by
  obtain ⟨m, hm⟩ : ∃ m, E.n = m + 1 := ⟨E.n - 1, by omega⟩
  constructor
  · intro a b ha hb'
    have ha' := ha.trans_le hps
    have hb'' := hb'.trans_le hps
    change undigits E.s (fun i => E.base.add (digit E.s a i) (digit E.s b i)) E.n = _
    rw [hm, undigits_of_eq_zero, digit_zero_of_lt ha', digit_zero_of_lt hb'', hb.add a b ha hb']
    intro i hi
    simp [digit_eq_zero_of_lt ha' hi, digit_eq_zero_of_lt hb'' hi, hz.add_zero]
  · intro a b ha hb'
    have ha' := ha.trans_le hps
    have hb'' := hb'.trans_le hps
    have hstep : ∀ j, 0 < j → E.step a b j 0 = 0 := fun j hj => step_zero fun i => by
      unfold stepDigit
      split_ifs <;> simp [digit_eq_zero_of_lt hb'' hj, hz.mul_zero, hz.zero_mul, hz.add_zero]
    have hfold : ∀ l : List ℕ, (∀ j ∈ l, 0 < j) → l.foldr (E.step a b) 0 = 0 := by
      intro l hl
      induction l with
      | nil => rfl
      | cons j l ih =>
        rw [List.foldr_cons, ih fun x hx => hl x (List.mem_cons_of_mem _ hx),
          hstep j (hl j List.mem_cons_self)]
    change (List.range E.n).foldr (E.step a b) 0 = _
    rw [hm, List.range_succ_eq_map, List.foldr_cons, hfold _ (by simp)]
    change undigits E.s (E.stepDigit a b 0 0) E.n = _
    have hlt : a * b % p < p := Nat.mod_lt _ hp
    rw [hm, undigits_of_eq_zero]
    · simp only [stepDigit, if_pos rfl, digit_zero_left, hz.mul_zero, digit_zero_of_lt ha',
        digit_zero_of_lt hb'', hb.mul b a hb' ha, Nat.mul_comm b a, ite_self]
      rw [hb.add 0 _ hp hlt, Nat.zero_add, Nat.mod_eq_of_lt hlt]
    · intro i hi
      simp [stepDigit, hi.ne', digit_eq_zero_of_lt ha' hi, hz.mul_zero, hz.add_zero]

end ExtCode

end GordieHowe.GKR.Fold
