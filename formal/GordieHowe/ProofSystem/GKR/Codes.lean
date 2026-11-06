-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.Certificate
public import Mathlib.Tactic.Ring
public import GordieHoweNative.Data
public import GordieHoweNative.ProofSystem.GKR.Codes

@[expose] public section

/-!
# Codes of field elements, the constant table, and sorted-list inclusion

The GKR checkers compute on the *codes* of field elements (the natural numbers of the C++
`to_bytes_field` bytes): `GordieHowe.GKR.Fold.CodeArith` adds and multiplies codes, and
`GordieHowe.GKR.Fold.CodeArith.Hom` states that it is the field's arithmetic under a decoding.
The constant table (`GordieHowe.GKR.Fold.Consts`) gives the code of every constant index of a
circuit's DAG. `GordieHowe.GKR.Fold.subsetSorted` is a merge-join test of inclusion between
increasing lists of naturals (`GordieHowe.GKR.Fold.mem_of_subsetSorted`).

The definitions are in `GordieHoweNative/ProofSystem/GKR/Codes.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.GKR.Fold

open GordieHowe.GKR.Certificate

/-! ## Codes -/

/-- **The code arithmetic is the field's** under the decoding `κc`: it decodes sums and products to
sums and products, and `0` and `1` to `0` and `1`. -/
structure CodeArith.Hom {F : Type*} [CommSemiring F] (ar : CodeArith) (κc : ℕ → F) : Prop where
  /-- Sums decode to sums. -/
  add : ∀ a b, κc (ar.add a b) = κc a + κc b
  /-- Products decode to products. -/
  mul : ∀ a b, κc (ar.mul a b) = κc a * κc b
  /-- `0` decodes to zero. -/
  zero : κc 0 = 0
  /-- `1` decodes to one. -/
  one : κc 1 = 1

/-- **A code whose sum with the code `1` is the code `0` decodes to `−1`.** -/
theorem CodeArith.Hom.neg_one {F : Type*} [CommRing F] {ar : CodeArith} {κc : ℕ → F}
    (h : ar.Hom κc) {c : ℕ} (hc : ar.add c 1 = 0) : κc c = -1 := by
  have := h.add c 1
  rw [hc, h.zero, h.one] at this
  exact eq_neg_of_add_eq_zero_left this.symm

/-- The field constant of index `i` under the decoding `κc`. -/
def Consts.decode {F : Type*} (Kc : Consts) (κc : ℕ → F) (i : ℕ) : F := κc (Kc.code i)

/-! ## Sorted lists -/

section Soundness

variable {F : Type*} [CommSemiring F] {ar : CodeArith} {κc : ℕ → F}

/-- `cmul` decodes to the product. -/
theorem cmul_hom (hA : ar.Hom κc) (a b : ℕ) : κc (cmul ar a b) = κc a * κc b := by
  unfold cmul
  simp only [Bool.cond_eq_ite, Bool.or_eq_true, Nat.beq_eq]
  split_ifs with h1 h2 h3
  · rcases h1 with rfl | rfl <;> simp [hA.zero]
  · rw [h2, hA.one, one_mul]
  · rw [h3, hA.one, mul_one]
  · exact hA.mul a b

end Soundness

/-- The kept elements of `dropLt` are elements. -/
theorem mem_of_mem_dropLt {x m : ℕ} : ∀ {ys : List ℕ}, m ∈ dropLt x ys → m ∈ ys
  | [], h => h
  | y :: ys, h => by
    simp only [dropLt] at h
    cases hy : Nat.blt y x
    · rw [hy, Bool.cond_false] at h
      exact h
    · rw [hy, Bool.cond_true] at h
      exact List.mem_cons_of_mem _ (mem_of_mem_dropLt h)

/-- The merge-join's elements are elements of the second list. -/
theorem mem_of_subsetSorted : ∀ {xs ys : List ℕ}, subsetSorted xs ys = true → ∀ m ∈ xs, m ∈ ys
  | [], _, _, m, hm => by simp at hm
  | x :: xs, ys, h, m, hm => by
    simp only [subsetSorted] at h
    generalize hd : dropLt x ys = d at h
    match d, h with
    | y :: ys', h =>
      dsimp only at h
      simp only [Bool.and_eq_true, Nat.beq_eq] at h
      have hy : y ∈ ys := mem_of_mem_dropLt (hd ▸ List.mem_cons_self ..)
      have hys' : ∀ z ∈ ys', z ∈ ys := fun z hz =>
        mem_of_mem_dropLt (hd ▸ List.mem_cons_of_mem _ hz)
      rcases List.mem_cons.mp hm with rfl | hm
      · exact h.1 ▸ hy
      · rcases List.mem_cons.mp (mem_of_subsetSorted h.2 m hm) with rfl | hz
        · exact hy
        · exact hys' _ hz
    | [], h => simp at h


/-- **`dropLt` drops a prefix of elements below `x`.** -/
theorem dropLt_split (x : ℕ) : ∀ ys : List ℕ, ∃ pre, ys = pre ++ dropLt x ys ∧ ∀ y ∈ pre, y < x
  | [] => ⟨[], rfl, by simp⟩
  | y :: ys => by
    cases hy : Nat.blt y x
    · refine ⟨[], ?_, by simp⟩
      simp only [dropLt, hy, Bool.cond_false, List.nil_append]
    · obtain ⟨pre, h1, h2⟩ := dropLt_split x ys
      refine ⟨y :: pre, ?_, fun z hz => ?_⟩
      · simp only [dropLt, hy, Bool.cond_true, List.cons_append]
        exact congrArg (y :: ·) h1
      · rcases List.mem_cons.mp hz with rfl | hz
        · simpa [Nat.blt_eq] using hy
        · exact h2 z hz

/-- **An element of an increasing list at or above `x` survives `dropLt x`.** -/
theorem mem_dropLt_of {x m : ℕ} {ys : List ℕ} (hm : m ∈ ys) (hx : x ≤ m) : m ∈ dropLt x ys := by
  obtain ⟨pre, h1, h2⟩ := dropLt_split x ys
  rw [h1] at hm
  rcases List.mem_append.mp hm with hm | hm
  · exact absurd (h2 m hm) (Nat.not_lt.mpr hx)
  · exact hm

/-- **What `dropLt x` keeps of an increasing list is at or above `x`.** -/
theorem le_of_mem_dropLt {x : ℕ} : ∀ {ys : List ℕ}, ys.Pairwise (· ≤ ·) → ∀ y ∈ dropLt x ys, x ≤ y
  | [], _, y, h => by simp [dropLt] at h
  | z :: zs, hs, y, h => by
    cases hz : Nat.blt z x
    · simp only [dropLt, hz, Bool.cond_false] at h
      have hzx : x ≤ z := by
        have : ¬ z < x := fun hlt => by simp [Nat.blt_eq.mpr hlt] at hz
        omega
      rcases List.mem_cons.mp h with rfl | h
      · exact hzx
      · exact Nat.le_trans hzx (List.rel_of_pairwise_cons hs h)
    · simp only [dropLt, hz, Bool.cond_true] at h
      exact le_of_mem_dropLt hs.of_cons y h

/-- **The merge-join accepts an increasing list whose elements lie in a nondecreasing list**
(`mem_of_subsetSorted`'s converse). -/
theorem subsetSorted_of_mem : ∀ {xs ys : List ℕ}, xs.Pairwise (· < ·) → ys.Pairwise (· ≤ ·) →
    (∀ m ∈ xs, m ∈ ys) → subsetSorted xs ys = true
  | [], _, _, _, _ => rfl
  | x :: xs, ys, hx, hy, hm => by
    have hxd : x ∈ dropLt x ys := mem_dropLt_of (hm x List.mem_cons_self) (Nat.le_refl x)
    have hds : (dropLt x ys).Pairwise (· ≤ ·) := by
      obtain ⟨pre, hsplit, -⟩ := dropLt_split x ys
      rw [hsplit] at hy
      exact (List.pairwise_append.mp hy).2.1
    have hge : ∀ y ∈ dropLt x ys, x ≤ y := le_of_mem_dropLt hy
    have hrest : ∀ m ∈ xs, m ∈ dropLt x ys := fun m hm' =>
      mem_dropLt_of (hm m (List.mem_cons_of_mem _ hm')) (Nat.le_of_lt (List.rel_of_pairwise_cons hx hm'))
    simp only [subsetSorted]
    generalize dropLt x ys = d at hxd hds hge hrest ⊢
    match d, hxd, hds, hge, hrest with
    | y :: ys', hxd, hds, hge, hrest =>
      have hyx : y = x := by
        rcases List.mem_cons.mp hxd with h | h
        · exact h.symm
        · exact Nat.le_antisymm (List.rel_of_pairwise_cons hds h) (hge y List.mem_cons_self)
      subst hyx
      simp only [Nat.beq_refl, Bool.true_and]
      exact subsetSorted_of_mem hx.of_cons hds hrest
    | [], hxd, _, _, _ => simp at hxd

end GordieHowe.GKR.Fold
