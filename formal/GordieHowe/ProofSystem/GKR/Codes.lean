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

end GordieHowe.GKR.Fold
