-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-!
# Record packing at a constant

A record `(r_0, …, r_{A-1})` of subfield values packed at a constant `κ`, `Σ_i κ^i r_i`
(`lib/gordiehowe/lib/permutation.h`, `record_packing`: the fixed `X = kappa` of `selection_kappa`).
The packing is injective on `E^A` when `1, κ, …, κ^(A-1)` are independent over `E`, which holds when
`κ` lies in no extension of `E` of degree below `A`. `pack_injOn` states it for a subfield `E` fixed
by the `p^k`-power Frobenius map (`E ⊆ GF(p^k)`), with the criterion `κ^((p^k)^m) ≠ κ` for
`0 < m < A`: a nonzero relation of degree below `A` over `E` would make the Frobenius orbit of `κ` a
set of roots of one polynomial, so two of its first `A` points coincide.
-/

namespace GordieHowe.RecordPacking

open Polynomial

variable {K : Type*} [Field K]

/-- **The packing of a record** at `κ`: `Σ_i κ^i r_i`. -/
def pack (κ : K) {A : ℕ} (r : Fin A → K) : K := ∑ i : Fin A, κ ^ (i : ℕ) * r i

/-- The packing is additive in the record. -/
theorem pack_sub (κ : K) {A : ℕ} (a b : Fin A → K) : pack κ (a - b) = pack κ a - pack κ b := by
  simp only [pack, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- The polynomial `Σ_i C(c_i) X^i` of a coefficient vector. -/
noncomputable def poly {A : ℕ} (c : Fin A → K) : K[X] := ∑ i : Fin A, C (c i) * X ^ (i : ℕ)

theorem eval_poly (κ : K) {A : ℕ} (c : Fin A → K) : (poly c).eval κ = pack κ c := by
  simp only [poly, pack, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem coeff_poly {A : ℕ} (c : Fin A → K) (i : Fin A) : (poly c).coeff i = c i := by
  simp only [poly, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Fin.val_injective.ne (Ne.symm hj)]
  · simp

theorem natDegree_poly_lt {A : ℕ} (hA : 0 < A) (c : Fin A → K) : (poly c).natDegree < A := by
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := A - 1) fun i _ => ?_) (by omega)
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_X_pow]
  omega

/-- **The Frobenius orbit of a root**: if the coefficients of `P` are fixed by `y ↦ y^(p^n)`, then
with `x` a root of `P`, so is `x^(p^n)`. -/
theorem eval_pow_char_pow {p n : ℕ} [Fact p.Prime] [CharP K p] {A : ℕ} {c : Fin A → K}
    (hc : ∀ i, c i ^ p ^ n = c i) {x : K} (hx : (poly c).eval x = 0) :
    (poly c).eval (x ^ p ^ n) = 0 := by
  rw [eval_poly] at hx ⊢
  have h : pack (x ^ p ^ n) c = pack x c ^ p ^ n := by
    rw [pack, pack, sum_pow_char_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, hc i, ← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [h, hx, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]

/-- **Injectivity of the packing on `E^A`** (`lib/gordiehowe/lib/permutation.h`, `record_packing`):
for a subfield `E` fixed by the `p^k`-power Frobenius map (`hE`) and a constant `κ` with
`κ^((p^k)^m) ≠ κ` for `0 < m < A` (`hκ`: `κ` lies in no extension of degree below `A` of `GF(p^k)`),
records of elements of `E` with equal packings are equal. -/
theorem pack_injOn [DecidableEq K] {p k : ℕ} [hp : Fact p.Prime] [CharP K p] {E : Subfield K}
    (hE : ∀ y ∈ E, y ^ p ^ k = y) {A : ℕ} {κ : K}
    (hκ : ∀ m, 0 < m → m < A → κ ^ (p ^ k) ^ m ≠ κ) {a b : Fin A → K}
    (ha : ∀ i, a i ∈ E) (hb : ∀ i, b i ∈ E) (h : pack κ a = pack κ b) : a = b := by
  by_contra hne
  have hA : 0 < A := by
    rcases Nat.eq_zero_or_pos A with h0 | h0
    · subst h0
      exact absurd (funext fun i => Fin.elim0 i) hne
    · exact h0
  set c := a - b with hcdef
  have hcE : ∀ i, c i ∈ E := fun i => E.sub_mem (ha i) (hb i)
  have hc0 : ∃ i, c i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (funext fun i => sub_eq_zero.mp (hall i))
  obtain ⟨i₀, hi₀⟩ := hc0
  have hP0 : poly c ≠ 0 := fun h0 => hi₀ (by rw [← coeff_poly c i₀, h0, coeff_zero])
  have hroot : (poly c).eval κ = 0 := by rw [eval_poly, hcdef, pack_sub, h, sub_self]
  -- Iterates of the `p^k`-power map fix `E`.
  have hfix : ∀ j : ℕ, ∀ i, c i ^ p ^ (k * j) = c i := by
    intro j i
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.mul_succ, pow_add, pow_mul, ih, hE _ (hcE i)]
  -- The orbit points are roots.
  let f : Fin A → K := fun j => κ ^ p ^ (k * j)
  have hf : ∀ j, f j ∈ (poly c).roots.toFinset := by
    intro j
    rw [Multiset.mem_toFinset, mem_roots hP0, IsRoot.def]
    exact eval_pow_char_pow (hfix j) hroot
  have hcard : (poly c).roots.toFinset.card < Fintype.card (Fin A) := by
    rw [Fintype.card_fin]
    exact lt_of_le_of_lt ((Multiset.toFinset_card_le _).trans (card_roots' _))
      (natDegree_poly_lt hA c)
  obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun j => (⟨f j, hf j⟩ : (poly c).roots.toFinset)) (by rwa [Fintype.card_coe])
  have hfij' : f i = f j := congrArg Subtype.val hfij
  -- The `p^k`-power map is injective, so the orbit returns to `κ`.
  have hinj : ∀ n : ℕ, Function.Injective fun y : K => y ^ p ^ n := fun n =>
    (iterateFrobenius K p n).injective
  have key : ∀ {u v : Fin A}, (u : ℕ) < v → f u = f v → False := by
    intro u v huv he
    have hm : κ ^ p ^ (k * ((v : ℕ) - u)) = κ := by
      apply hinj (k * u)
      change (κ ^ p ^ (k * ((v : ℕ) - u))) ^ p ^ (k * u) = κ ^ p ^ (k * u)
      have hfv : f v = (κ ^ p ^ (k * ((v : ℕ) - u))) ^ p ^ (k * u) := by
        change κ ^ p ^ (k * v) = _
        rw [← pow_mul, ← Nat.pow_add, ← Nat.mul_add]
        congr 3
        omega
      rw [← hfv]
      exact he.symm
    exact hκ ((v : ℕ) - u) (by omega) (by omega) (by rwa [← Nat.pow_mul])
  rcases Nat.lt_or_gt_of_ne (Fin.val_injective.ne hij) with hlt | hlt
  · exact key hlt hfij'
  · exact key hlt hfij'.symm

end GordieHowe.RecordPacking
