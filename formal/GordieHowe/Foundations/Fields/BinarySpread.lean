-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.AdjoinRoot
public import GordieHowe.Foundations.ToMathlib.NatPolyDigits
public import GordieHowe.Foundations.Fields.BinaryRep

@[expose] public section

/-!
# Kernel-checkable arithmetic in `GF(2)[X] / (f)` by spread naturals

A certificate about a concrete binary field `AdjoinRoot f`, `f = X^n + (lower terms)`,
is checked by evaluating field arithmetic in the kernel. The kernel's natural numbers
are arbitrary-precision (GMP), so an element is represented by one natural whose base
`2 ^ k` digits are its polynomial-basis coordinates: bit `i` of the element sits at bit
`k * i` of the natural (`Exec.spread`). With `k` large enough, the integer product of
two such naturals has as digits the coefficients of the product polynomial over `ℕ`
(no carry crosses a digit), so one multiplication in the field is one `Nat.mul`, two
folds of the high digits by the reduction rule `X^n = tap` (`Exec.fold`) and one bitwise
and that keeps the parity of each digit (`Exec.mul`). A 256-bit multiplication costs
about `0.3 ms` of kernel time, against about `60 ms` for bit-serial shift-and-add on
`BitVec 256`.

`Exec` holds the executable parameters, `Rep E f` the facts that tie them to `f`
(the tap polynomial and the bounds that exclude carries), `val E f N` the element a
natural represents and `Canon E N` the naturals of the representation (binary digits,
fewer than `n` of them). The theorems carry `Exec.mul`, `Exec.add`, `Exec.sqPow`,
`Exec.pow`, `Exec.sum` and `Exec.trace` to the field operations, `val_ofBits` gives the
element of a bit string, and `val_injective` turns a kernel-checked inequality of
naturals into an inequality of field elements.
-/

namespace GordieHowe.BinarySpread

open Polynomial

/-- The executable parameters: digit width `k`, degree `n`, the natural `tapN` whose
digits are the low coefficients of `f`, and the parity mask `mask` (one in the lowest bit
of each of the `n` digits). -/
structure Exec where
  k : ℕ
  n : ℕ
  tapN : ℕ
  mask : ℕ

namespace Exec

variable (E : Exec)

/-- Replace the digits from position `n` on, `H`, by `H * tap`. -/
def fold (N : ℕ) : ℕ := N % 2 ^ (E.k * E.n) + N / 2 ^ (E.k * E.n) * E.tapN

/-- Multiplication: integer product, two folds, parity of each digit. -/
def mul (a b : ℕ) : ℕ := E.fold (E.fold (a * b)) &&& E.mask

/-- Addition: integer sum, parity of each digit. -/
def add (a b : ℕ) : ℕ := (a + b) &&& E.mask

/-- `r ^ (2 ^ j)`, by `j` squarings. -/
def sqPow : ℕ → ℕ → ℕ
  | 0, r => r
  | j + 1, r => sqPow j (E.mul r r)

/-- `b ^ e` for `e < 2 ^ j`, by square-and-multiply over the `j` low bits of `e`. -/
def pow : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | j + 1, e, b =>
    if e % 2 = 1 then E.mul b (pow j (e / 2) (E.mul b b)) else pow j (e / 2) (E.mul b b)

/-- The `i` low bits of `v`, bit `j` moved to bit `k * j`. -/
def spread : ℕ → ℕ → ℕ
  | 0, _ => 0
  | i + 1, v => v % 2 + 2 ^ E.k * spread i (v / 2)

/-- The representation of the element with polynomial-basis coordinates the bits of `v`. -/
def ofBits (v : ℕ) : ℕ := E.spread E.n v

/-- The sum of `g 0, …, g (m - 1)`. -/
def sum : (m : ℕ) → (Fin m → ℕ) → ℕ
  | 0, _ => 0
  | m + 1, g => E.add (g 0) (sum m fun j => g j.succ)

/-- `trace s m y = ∑_{j < m} y ^ (2 ^ (s * j))`. -/
def trace (s : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | m + 1, y => E.add y (trace s m (E.sqPow s y))

end Exec

variable {f : (ZMod 2)[X]}

/-- Reduce a natural-coefficient polynomial mod `2` and then mod `f`. -/
noncomputable def toAdjoin (f : (ZMod 2)[X]) : ℕ[X] →+* AdjoinRoot f :=
  (AdjoinRoot.mk f).comp (mapRingHom (Nat.castRingHom (ZMod 2)))

theorem toAdjoin_X : toAdjoin f X = AdjoinRoot.root f := by
  simp [toAdjoin]

theorem toAdjoin_eq_of_mod_two {P Q : ℕ[X]} (h : ∀ i, P.coeff i % 2 = Q.coeff i % 2) :
    toAdjoin f P = toAdjoin f Q := by
  simp only [toAdjoin, RingHom.comp_apply, coe_mapRingHom]
  congr 1
  ext i
  simp only [coeff_map, eq_natCast]
  exact (ZMod.natCast_eq_natCast_iff' _ _ 2).mpr (h i)

/-- The element with polynomial-basis coordinates the `n` low bits of `v`. -/
noncomputable def bitsVal (f : (ZMod 2)[X]) (n v : ℕ) : AdjoinRoot f :=
  ∑ j ∈ Finset.range n, if v.testBit j then AdjoinRoot.root f ^ j else 0

theorem bitsVal_two_pow {n j : ℕ} (hj : j < n) : bitsVal f n (2 ^ j) = AdjoinRoot.root f ^ j := by
  rw [bitsVal, Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr hj)]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]

/-- The bit-vector representation of `GordieHowe.Foundations.Fields.BinaryRep` reads the same element: the `n` low
bits of `v` as power-basis coordinates. -/
theorem toSpec_ofNat (n v : ℕ) : BinaryRep.toSpec f (BitVec.ofNat n v) = bitsVal f n v := by
  rw [BinaryRep.toSpec, bitsVal, ← Fin.sum_univ_eq_sum_range
    (fun j => if v.testBit j then AdjoinRoot.root f ^ j else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [BitVec.getLsbD_ofNat]
  simp [i.isLt]

/-- The facts that tie the executable parameters `E` to `f`: the tap polynomial
`tap = f - X^n` over `ℕ` with its digit natural `tapN` and degree bound `d`, the mask,
and the bounds under which no carry crosses a digit (products of two representations
have coefficients at most `n`; each fold multiplies the bound by at most `1 + d`). -/
structure Rep (E : Exec) (f : (ZMod 2)[X]) where
  tap : ℕ[X]
  d : ℕ
  two_le_k : 2 ≤ E.k
  tap_bounded : Bounded 2 d tap
  tapN_eq : E.tapN = tap.eval (2 ^ E.k)
  mask_eq : E.mask = Nat.ones E.k E.n
  root_pow : toAdjoin f (X ^ E.n) = toAdjoin f tap
  natDegree_eq : f.natDegree = E.n
  n_pos : 0 < E.n
  deg_le : 2 * d ≤ E.n + 1
  coeff_le : E.n + 1 + d * E.n + d * (E.n + d * E.n) ≤ 2 ^ E.k

variable {E : Exec}

/-- The polynomial with the `n` low base-`2 ^ k` digits of `N` as coefficients. -/
noncomputable def digitPoly (E : Exec) (N : ℕ) : ℕ[X] :=
  ∑ i ∈ Finset.range E.n, C (N / (2 ^ E.k) ^ i % 2 ^ E.k) * X ^ i

/-- The element of `AdjoinRoot f` a natural represents. -/
noncomputable def val (E : Exec) (f : (ZMod 2)[X]) (N : ℕ) : AdjoinRoot f :=
  toAdjoin f (digitPoly E N)

/-- The element of a ring `L` isomorphic to `AdjoinRoot f` (by `e`) that a natural represents. -/
noncomputable def valVia {L : Type*} [CommRing L] (e : L ≃+* AdjoinRoot f) (E : Exec) (N : ℕ) :
    L :=
  e.symm (val E f N)

/-- The naturals of the representation: binary digits, fewer than `n` of them. -/
def Canon (E : Exec) (N : ℕ) : Prop :=
  ∃ P : ℕ[X], Bounded 2 E.n P ∧ P.eval (2 ^ E.k) = N

theorem digitPoly_eval {P : ℕ[X]} (h : Bounded (2 ^ E.k) E.n P) :
    digitPoly E (P.eval (2 ^ E.k)) = P := by
  ext i
  rw [digitPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hi
  · exact h.digit i
  · exact (h.coeff_eq_zero i (by simpa using hi)).symm

namespace Rep

variable (R : Rep E f)
include R

theorem two_le_two_pow : 2 ≤ 2 ^ E.k :=
  (Nat.le_self_pow (by omega) 2).trans (Nat.pow_le_pow_right (by norm_num) R.two_le_k)

theorem val_eval {P : ℕ[X]} (hP : Bounded 2 E.n P) : val E f (P.eval (2 ^ E.k)) = toAdjoin f P := by
  rw [val, digitPoly_eval (hP.mono R.two_le_two_pow le_rfl)]

/-- One fold: the low part plus the high part times `tap`, with the given output bounds. -/
theorem fold_spec {c m c' m' : ℕ} {P : ℕ[X]} (hP : Bounded c m P) (hc : c ≤ 2 ^ E.k)
    (hc' : c + R.d * (c - 1) ≤ c') (hm : E.n ≤ m') (hm' : R.d + (m - E.n) - 1 ≤ m') :
    ∃ Q : ℕ[X], Bounded c' m' Q ∧ Q.eval (2 ^ E.k) = E.fold (P.eval (2 ^ E.k)) ∧
      toAdjoin f Q = toAdjoin f P := by
  obtain ⟨L, H, hPLH, hL, hH⟩ := exists_split E.n P
  have hc0 : 0 < c := (Nat.zero_le _).trans_lt (hP.coeff_lt 0)
  have hLb := hP.low hL hc0
  have hTH := R.tap_bounded.mul (hP.high hH)
  have hsimp : R.d * ((2 - 1) * (c - 1)) = R.d * (c - 1) := by norm_num
  rw [hsimp] at hTH
  refine ⟨L + R.tap * H, ((hLb.mono le_rfl hm).add (hTH.mono le_rfl hm')).mono (by omega) le_rfl,
    ?_, ?_⟩
  · obtain ⟨hmod, hdiv⟩ := (hP.mono hc le_rfl).eval_split hPLH hL
    rw [Exec.fold, pow_mul, hmod, hdiv, R.tapN_eq, eval_add, eval_mul, mul_comm (R.tap.eval _)]
  · conv_rhs => rw [hPLH]
    rw [map_add, map_add, map_mul, map_mul, R.root_pow, mul_comm]

theorem canon_mul_val {a b : ℕ} (ha : Canon E a) (hb : Canon E b) :
    Canon E (E.mul a b) ∧ val E f (E.mul a b) = val E f a * val E f b := by
  obtain ⟨A, hA, rfl⟩ := ha
  obtain ⟨B, hB, rfl⟩ := hb
  have hk := R.coeff_le
  have hd := R.deg_le
  have hAB : Bounded (E.n + 1) (E.n + E.n - 1) (A * B) :=
    (hA.mul hB).mono (by norm_num) le_rfl
  obtain ⟨Q1, hQ1, hQ1e, hQ1v⟩ := R.fold_spec hAB (c' := E.n + 1 + R.d * E.n)
    (m' := E.n + R.d) (by omega) (by simp) (by omega) (by omega)
  obtain ⟨Q2, hQ2, hQ2e, hQ2v⟩ := R.fold_spec hQ1
    (c' := E.n + 1 + R.d * E.n + R.d * (E.n + R.d * E.n)) (m' := E.n) (by omega)
    (by rw [show E.n + 1 + R.d * E.n - 1 = E.n + R.d * E.n by omega]) le_rfl (by omega)
  obtain ⟨Q, hQ, hQc, hQe⟩ := (hQ2.mono hk le_rfl).land_ones (by have := R.two_le_k; omega)
  have heq : E.mul (A.eval (2 ^ E.k)) (B.eval (2 ^ E.k)) = Q.eval (2 ^ E.k) := by
    rw [Exec.mul, ← eval_mul, ← hQ1e, ← hQ2e, R.mask_eq, hQe]
  refine ⟨⟨Q, hQ, heq.symm⟩, ?_⟩
  rw [heq, R.val_eval hQ, R.val_eval hA, R.val_eval hB, toAdjoin_eq_of_mod_two hQc, hQ2v, hQ1v,
    map_mul]

theorem canon_mul {a b : ℕ} (ha : Canon E a) (hb : Canon E b) : Canon E (E.mul a b) :=
  (R.canon_mul_val ha hb).1

theorem val_mul {a b : ℕ} (ha : Canon E a) (hb : Canon E b) :
    val E f (E.mul a b) = val E f a * val E f b :=
  (R.canon_mul_val ha hb).2

theorem canon_add_val {a b : ℕ} (ha : Canon E a) (hb : Canon E b) :
    Canon E (E.add a b) ∧ val E f (E.add a b) = val E f a + val E f b := by
  obtain ⟨A, hA, rfl⟩ := ha
  obtain ⟨B, hB, rfl⟩ := hb
  have h4 : 2 + 2 - 1 ≤ 2 ^ E.k :=
    (show 2 + 2 - 1 ≤ 2 ^ 2 by norm_num).trans (Nat.pow_le_pow_right (by norm_num) R.two_le_k)
  obtain ⟨Q, hQ, hQc, hQe⟩ := ((hA.add hB).mono h4 le_rfl).land_ones
    (by have := R.two_le_k; omega)
  have heq : E.add (A.eval (2 ^ E.k)) (B.eval (2 ^ E.k)) = Q.eval (2 ^ E.k) := by
    rw [Exec.add, ← eval_add, R.mask_eq, hQe]
  refine ⟨⟨Q, hQ, heq.symm⟩, ?_⟩
  rw [heq, R.val_eval hQ, R.val_eval hA, R.val_eval hB, toAdjoin_eq_of_mod_two hQc, map_add]

theorem canon_add {a b : ℕ} (ha : Canon E a) (hb : Canon E b) : Canon E (E.add a b) :=
  (R.canon_add_val ha hb).1

theorem val_add {a b : ℕ} (ha : Canon E a) (hb : Canon E b) :
    val E f (E.add a b) = val E f a + val E f b :=
  (R.canon_add_val ha hb).2

omit R in
theorem bounded_zero : Bounded 2 E.n 0 := ⟨fun i => by simp, fun i _ => by simp⟩

theorem bounded_one : Bounded 2 E.n (C 1) :=
  ⟨fun i => by rw [coeff_C]; split_ifs <;> norm_num,
    fun i hi => by rw [coeff_C, ite_eq_right (by have := R.n_pos; omega)]⟩

omit R in
theorem canon_zero : Canon E 0 := ⟨0, bounded_zero, by simp⟩

theorem val_zero : val E f 0 = 0 := by
  rw [show (0 : ℕ) = (0 : ℕ[X]).eval (2 ^ E.k) by simp, R.val_eval bounded_zero, map_zero]

theorem canon_one : Canon E 1 := ⟨C 1, R.bounded_one, by simp⟩

theorem val_one : val E f 1 = 1 := by
  rw [show (1 : ℕ) = (C 1 : ℕ[X]).eval (2 ^ E.k) by simp, R.val_eval R.bounded_one, C_1, map_one]

omit R in
theorem canon_ite (p : Prop) [Decidable p] {a b : ℕ} (ha : Canon E a) (hb : Canon E b) :
    Canon E (if p then a else b) := by
  split_ifs
  exacts [ha, hb]

omit R in
theorem val_ite (p : Prop) [Decidable p] (a b : ℕ) :
    val E f (if p then a else b) = if p then val E f a else val E f b := by
  split_ifs <;> rfl

omit R in
theorem spread_spec (i v : ℕ) : ∃ P : ℕ[X], Bounded 2 i P ∧ P.eval (2 ^ E.k) = E.spread i v ∧
    toAdjoin f P = bitsVal f i v := by
  induction i generalizing v with
  | zero => exact ⟨0, ⟨fun i => by simp, fun i _ => by simp⟩, by simp [Exec.spread],
      by simp [bitsVal]⟩
  | succ i ih =>
    obtain ⟨P, hP, hPe, hPv⟩ := ih (v / 2)
    refine ⟨C (v % 2) + X * P, ⟨fun j => ?_, fun j hj => ?_⟩, ?_, ?_⟩
    · rcases j with _ | j
      · simp only [coeff_add, coeff_C_zero, mul_coeff_zero, coeff_X_zero, zero_mul, add_zero]
        exact Nat.mod_lt v (by norm_num)
      · rw [coeff_add, coeff_C, ite_eq_right (Nat.succ_ne_zero j), zero_add, coeff_X_mul]
        exact hP.coeff_lt j
    · rcases j with _ | j
      · omega
      · rw [coeff_add, coeff_C, ite_eq_right (Nat.succ_ne_zero j), zero_add, coeff_X_mul]
        exact hP.coeff_eq_zero j (by omega)
    · rw [Exec.spread, eval_add, eval_C, eval_mul, eval_X, hPe]
    · rw [map_add, map_mul, toAdjoin_X, hPv, bitsVal, bitsVal, Finset.sum_range_succ',
        Finset.mul_sum, add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [Nat.testBit_div_two, mul_ite, mul_zero, pow_succ']
      · rcases Nat.mod_two_eq_zero_or_one v with h | h
        · have hb : v.testBit 0 = false := by rw [Nat.testBit_zero, h]; rfl
          simp [toAdjoin, h, hb]
        · have hb : v.testBit 0 = true := by rw [Nat.testBit_zero, h]; rfl
          simp [toAdjoin, h, hb]

omit R in
theorem canon_ofBits (v : ℕ) : Canon E (E.ofBits v) := by
  obtain ⟨P, hP, hPe, _⟩ := spread_spec (E := E) (f := 0) E.n v
  exact ⟨P, hP, hPe⟩

theorem val_ofBits (v : ℕ) : val E f (E.ofBits v) = bitsVal f E.n v := by
  obtain ⟨P, hP, hPe, hPv⟩ := spread_spec (E := E) (f := f) E.n v
  rw [Exec.ofBits, ← hPe, R.val_eval hP, hPv]

/-- The spread natural of the bits of a bit vector of width `n` represents the element
`BinaryRep.toSpec` gives the bit vector. -/
theorem val_ofBits_toNat {w : ℕ} (hw : E.n = w) (x : BitVec w) :
    val E f (E.ofBits x.toNat) = BinaryRep.toSpec f x := by
  rw [R.val_ofBits, hw, ← toSpec_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- Distinct representations are distinct elements. -/
theorem val_injective {a b : ℕ} (ha : Canon E a) (hb : Canon E b) (h : val E f a = val E f b) :
    a = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA, rfl⟩ := ha
  obtain ⟨B, hB, rfl⟩ := hb
  rw [R.val_eval hA, R.val_eval hB] at h
  simp only [toAdjoin, RingHom.comp_apply, coe_mapRingHom] at h
  rw [AdjoinRoot.mk_eq_mk] at h
  have hdeg : (map (Nat.castRingHom (ZMod 2)) A - map (Nat.castRingHom (ZMod 2)) B).natDegree <
      f.natDegree := by
    rw [R.natDegree_eq]
    refine lt_of_le_of_lt (natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_)
      (Nat.sub_lt R.n_pos one_pos)
    rw [coeff_sub, coeff_map, coeff_map, hA.coeff_eq_zero N (by omega),
      hB.coeff_eq_zero N (by omega), map_zero, sub_zero]
  have h0 := eq_zero_of_dvd_of_natDegree_lt h hdeg
  have hAB : A = B := by
    ext i
    have hi := congrArg (fun p => p.coeff i) h0
    simp only [coeff_sub, coeff_map, coeff_zero, sub_eq_zero, eq_natCast] at hi
    have := (ZMod.natCast_eq_natCast_iff' _ _ 2).mp hi
    rwa [Nat.mod_eq_of_lt (hA.coeff_lt i), Nat.mod_eq_of_lt (hB.coeff_lt i)] at this
  rw [hAB]

theorem canon_sqPow_val {r : ℕ} (hr : Canon E r) (j : ℕ) :
    Canon E (E.sqPow j r) ∧ val E f (E.sqPow j r) = val E f r ^ 2 ^ j := by
  induction j generalizing r with
  | zero => exact ⟨hr, by simp [Exec.sqPow]⟩
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih (R.canon_mul hr hr)
    refine ⟨h1, ?_⟩
    rw [Exec.sqPow, h2, R.val_mul hr hr, ← sq, ← pow_mul, pow_succ']

theorem canon_sqPow {r : ℕ} (hr : Canon E r) (j : ℕ) : Canon E (E.sqPow j r) :=
  (R.canon_sqPow_val (f := f) hr j).1

theorem val_sqPow {r : ℕ} (hr : Canon E r) (j : ℕ) : val E f (E.sqPow j r) = val E f r ^ 2 ^ j :=
  (R.canon_sqPow_val hr j).2

theorem canon_pow_val {b : ℕ} (hb : Canon E b) (j e : ℕ) (he : e < 2 ^ j) :
    Canon E (E.pow j e b) ∧ val E f (E.pow j e b) = val E f b ^ e := by
  induction j generalizing e b with
  | zero =>
    obtain rfl : e = 0 := by simpa using he
    exact ⟨R.canon_one, by rw [Exec.pow, R.val_one, pow_zero]⟩
  | succ j ih =>
    have hdiv : e / 2 < 2 ^ j := by rw [pow_succ] at he; omega
    obtain ⟨h1, h2⟩ := ih (R.canon_mul hb hb) (e / 2) hdiv
    have hsq : val E f (E.pow j (e / 2) (E.mul b b)) = val E f b ^ (2 * (e / 2)) := by
      rw [h2, R.val_mul hb hb, ← sq, ← pow_mul]
    rw [Exec.pow]
    split_ifs with h
    · refine ⟨R.canon_mul hb h1, ?_⟩
      rw [R.val_mul hb h1, hsq, ← pow_succ', show 2 * (e / 2) + 1 = e by omega]
    · refine ⟨h1, ?_⟩
      rw [hsq, show 2 * (e / 2) = e by omega]

theorem canon_pow {b : ℕ} (hb : Canon E b) (j e : ℕ) (he : e < 2 ^ j) : Canon E (E.pow j e b) :=
  (R.canon_pow_val (f := f) hb j e he).1

theorem val_pow {b : ℕ} (hb : Canon E b) {j e : ℕ} (he : e < 2 ^ j) :
    val E f (E.pow j e b) = val E f b ^ e :=
  (R.canon_pow_val hb j e he).2

theorem canon_sum_val (m : ℕ) (g : Fin m → ℕ) (hg : ∀ j, Canon E (g j)) :
    Canon E (E.sum m g) ∧ val E f (E.sum m g) = ∑ j, val E f (g j) := by
  induction m with
  | zero => exact ⟨canon_zero, by rw [Exec.sum, R.val_zero, Fin.sum_univ_zero]⟩
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih (fun j => g j.succ) fun j => hg j.succ
    exact ⟨R.canon_add (hg 0) h1, by rw [Exec.sum, R.val_add (hg 0) h1, h2, Fin.sum_univ_succ]⟩

theorem canon_sum (m : ℕ) (g : Fin m → ℕ) (hg : ∀ j, Canon E (g j)) : Canon E (E.sum m g) :=
  (R.canon_sum_val (f := f) m g hg).1

theorem val_sum (m : ℕ) (g : Fin m → ℕ) (hg : ∀ j, Canon E (g j)) :
    val E f (E.sum m g) = ∑ j, val E f (g j) :=
  (R.canon_sum_val m g hg).2

theorem canon_trace_val (s : ℕ) {y : ℕ} (hy : Canon E y) (m : ℕ) :
    Canon E (E.trace s m y) ∧
      val E f (E.trace s m y) = ∑ j : Fin m, val E f y ^ 2 ^ (s * (j : ℕ)) := by
  induction m generalizing y with
  | zero => exact ⟨canon_zero, by rw [Exec.trace, R.val_zero, Fin.sum_univ_zero]⟩
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih (R.canon_sqPow hy s)
    refine ⟨R.canon_add hy h1, ?_⟩
    rw [Exec.trace, R.val_add hy h1, h2, R.val_sqPow hy, Fin.sum_univ_succ]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [← pow_mul, ← pow_add, Fin.val_succ, mul_add, mul_one, add_comm]

theorem val_trace (s : ℕ) {y : ℕ} (hy : Canon E y) (m : ℕ) :
    val E f (E.trace s m y) = ∑ j : Fin m, val E f y ^ 2 ^ (s * (j : ℕ)) :=
  (R.canon_trace_val s hy m).2

/-! ### Reading the representation in an isomorphic ring

A concrete field with its own carrier (`GordieHowe.Foundations.Fields.BinaryRep`) is isomorphic to `AdjoinRoot f`
by some `e`; `valVia e E N` reads the spread natural `N` there, and the lemmas below carry the
spread arithmetic to it. -/

section Via

variable {L : Type*} [CommRing L] (e : L ≃+* AdjoinRoot f)

theorem valVia_mul {a b : ℕ} (ha : Canon E a) (hb : Canon E b) :
    valVia e E (E.mul a b) = valVia e E a * valVia e E b := by
  unfold valVia
  rw [R.val_mul ha hb, map_mul]

theorem valVia_add {a b : ℕ} (ha : Canon E a) (hb : Canon E b) :
    valVia e E (E.add a b) = valVia e E a + valVia e E b := by
  unfold valVia
  rw [R.val_add ha hb, map_add]

theorem valVia_zero : valVia e E 0 = 0 := by
  unfold valVia
  rw [R.val_zero, map_zero]

theorem valVia_one : valVia e E 1 = 1 := by
  unfold valVia
  rw [R.val_one, map_one]

theorem valVia_ite (p : Prop) [Decidable p] (a b : ℕ) :
    valVia e E (if p then a else b) = if p then valVia e E a else valVia e E b := by
  split_ifs <;> rfl

theorem valVia_ofBits (v : ℕ) : valVia e E (E.ofBits v) = e.symm (bitsVal f E.n v) := by
  unfold valVia
  rw [R.val_ofBits]

theorem valVia_injective {a b : ℕ} (ha : Canon E a) (hb : Canon E b)
    (h : valVia e E a = valVia e E b) : a = b :=
  R.val_injective ha hb (e.symm.injective h)

theorem valVia_sqPow {r : ℕ} (hr : Canon E r) (j : ℕ) :
    valVia e E (E.sqPow j r) = valVia e E r ^ 2 ^ j := by
  unfold valVia
  rw [R.val_sqPow hr, map_pow]

theorem valVia_pow {b : ℕ} (hb : Canon E b) {j e' : ℕ} (he : e' < 2 ^ j) :
    valVia e E (E.pow j e' b) = valVia e E b ^ e' := by
  unfold valVia
  rw [R.val_pow hb he, map_pow]

theorem valVia_sum (m : ℕ) (g : Fin m → ℕ) (hg : ∀ j, Canon E (g j)) :
    valVia e E (E.sum m g) = ∑ j, valVia e E (g j) := by
  unfold valVia
  rw [R.val_sum m g hg, map_sum]

theorem valVia_trace (s : ℕ) {y : ℕ} (hy : Canon E y) (m : ℕ) :
    valVia e E (E.trace s m y) = ∑ j : Fin m, valVia e E y ^ 2 ^ (s * (j : ℕ)) := by
  unfold valVia
  rw [R.val_trace s hy m, map_sum]
  simp only [map_pow]

end Via

end Rep

end GordieHowe.BinarySpread
