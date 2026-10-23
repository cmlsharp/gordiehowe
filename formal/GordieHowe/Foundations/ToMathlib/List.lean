-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

/-!
# Folding multiplication over `List.finRange` as a product

Candidate for upstreaming; see Mathlib's `List.prod_ofFn`.
-/

/-- Applying a list of module homomorphisms at a point distributes over
`List.sum`. -/
theorem List.sum_linearMap_apply {R M M₂ : Type*} [Semiring R] [AddCommMonoid M]
    [AddCommMonoid M₂] [Module R M] [Module R M₂] (l : List (M →ₗ[R] M₂)) (x : M) :
    l.sum x = (l.map fun f => f x).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- Multiplying a `List.sum` by a constant on the left distributes over
`List.map`. -/
theorem List.mul_sum_map {α M : Type*} [NonUnitalNonAssocSemiring M] (c : M) (l : List α)
    (f : α → M) : c * (l.map f).sum = (l.map fun a => c * f a).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [mul_add, ih]

/-- A `Fintype`-indexed sum of `List.sum`s commutes with mapping the finite sum
into each list element. -/
theorem List.sum_comm_finset_sum {α M ι : Type*} [AddCommMonoid M] [Fintype ι]
    (l : List α) (f : α → ι → M) :
    ∑ i : ι, (l.map fun a => f a i).sum = (l.map fun a => ∑ i, f a i).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- A list sum, mapped through `f`, as a `Fintype`-indexed sum of the sums over
the fibers of `key`: partitioning the list by a finite-valued key does not
change the total. -/
theorem List.sum_map_eq_sum_filter_fiber {α M ι : Type*} [AddCommMonoid M] [Fintype ι]
    [DecidableEq ι] (l : List α) (key : α → ι) (f : α → M) :
    (l.map f).sum = ∑ i : ι, ((l.filter fun a => key a = i).map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hstep : ∀ i : ι,
        (((a :: l).filter fun x => key x = i).map f).sum =
          (if key a = i then f a else 0) + ((l.filter fun x => key x = i).map f).sum := by
      intro i
      by_cases h : key a = i
      · rw [List.filter_cons_of_pos (by simpa using h), List.map_cons, List.sum_cons, if_pos h]
      · rw [List.filter_cons_of_neg (by simpa using h), if_neg h, zero_add]
    simp only [hstep, Finset.sum_add_distrib]
    rw [Fintype.sum_ite_eq (key a) fun _ => f a, ← ih]

/-- Left-folding multiplication over `List.finRange n` against `f`, starting from
`1`, computes the product `∏ i, f i`. -/
theorem List.finRange_foldl_mul_eq_prod {M : Type*} [CommMonoid M] {n : ℕ} (f : Fin n → M) :
    (List.finRange n).foldl (fun acc i => acc * f i) 1 = ∏ i, f i := by
  rw [← List.prod_ofFn, List.ofFn_eq_map, List.prod_eq_foldl, List.foldl_map]

/-! Interleaving lists while retaining the tail of the longer list. -/

variable {α : Type*}

def List.interleavePairs : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => x :: y :: List.interleavePairs xs ys

@[simp] theorem List.interleavePairs_nil_left (ys : List α) :
    List.interleavePairs [] ys = ys := rfl

@[simp] theorem List.interleavePairs_nil_right (xs : List α) :
    List.interleavePairs xs [] = xs := by
  cases xs <;> rfl

theorem List.interleavePairs_perm_append (lo hi : List α) :
    (List.interleavePairs lo hi).Perm (lo ++ hi) := by
  induction lo generalizing hi with
  | nil => simp
  | cons x lo ih =>
      cases hi with
      | nil => simp
      | cons y hi =>
          simp only [List.interleavePairs]
          exact List.Perm.cons x (List.perm_cons_append_cons y (ih hi))

@[simp] theorem List.interleavePairs_length (lo hi : List α) :
    (List.interleavePairs lo hi).length = lo.length + hi.length := by
  simpa only [List.length_append] using
    (List.interleavePairs_perm_append lo hi).length_eq

theorem List.map_interleavePairs {β : Type*} (f : α → β) (lo hi : List α) :
    (List.interleavePairs lo hi).map f =
      List.interleavePairs (lo.map f) (hi.map f) := by
  induction lo generalizing hi with
  | nil => simp
  | cons x lo ih =>
      cases hi with
      | nil => simp
      | cons y hi => simp [List.interleavePairs, ih]

/-- The first `n + 1` entries of `List.finRange N` are the first `n` followed by `n`. -/
theorem List.take_succ_finRange {N n : ℕ} (hn : n < N) :
    (List.finRange N).take (n + 1) = (List.finRange N).take n ++ [⟨n, hn⟩] := by
  rw [List.take_succ_eq_append_getElem (by simpa using hn), List.getElem_finRange]
  rfl
