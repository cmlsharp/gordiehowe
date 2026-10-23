-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Data.List.TakeDrop
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Balanced addition of formal fractions, including zero denominators. -/
namespace GordieHowe.FractionTree

variable {K : Type*} [CommSemiring K]

/-- Cross multiplication without division. -/
def combine (x y : K × K) : K × K :=
  (x.1 * y.2 + y.1 * x.2, x.2 * y.2)

@[simp] theorem combine_zero (x : K × K) : combine (0, 1) x = x := by
  cases x
  simp [combine]

@[simp] theorem combine_zero_right (x : K × K) : combine x (0, 1) = x := by
  cases x
  simp [combine]

theorem combine_assoc (x y z : K × K) :
    combine (combine x y) z = combine x (combine y z) := by
  ext <;> simp only [combine] <;> ring

/-- Sequential accumulator, used in proofs. -/
def fold (ds : List K) : K × K :=
  ds.foldl (fun a d => (a.1 * d + a.2, a.2 * d)) (0, 1)

theorem foldl_eq_combine (ds : List K) (a : K × K) :
    ds.foldl (fun a d => (a.1 * d + a.2, a.2 * d)) a = combine a (fold ds) := by
  induction ds generalizing a with
  | nil => simp [fold]
  | cons d ds ih =>
    rw [List.foldl_cons, ih]
    have h := ih (1, d)
    simp only [fold, List.foldl_cons, zero_mul, zero_add, one_mul] at h ⊢
    rw [h, ← combine_assoc]
    simp [combine]

@[simp] theorem fold_nil : fold ([] : List K) = (0, 1) := rfl

@[simp] theorem fold_singleton (d : K) : fold [d] = (1, d) := by
  simp [fold]

theorem fold_append (xs ys : List K) : fold (xs ++ ys) = combine (fold xs) (fold ys) := by
  simp only [fold, List.foldl_append]
  exact foldl_eq_combine ys _

/-- The implementation's balanced tree, splitting at half the list length. -/
def balanced (ds : List K) : K × K :=
  match ds with
  | [] => (0, 1)
  | [d] => (1, d)
  | a :: b :: tail =>
    let ds := a :: b :: tail
    combine (balanced (ds.take (ds.length / 2))) (balanced (ds.drop (ds.length / 2)))
termination_by ds.length
 decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_cons]
  all_goals omega

@[simp] theorem balanced_nil : balanced ([] : List K) = (0, 1) := by
  rw [balanced]

@[simp] theorem balanced_singleton (d : K) : balanced [d] = (1, d) := by
  rw [balanced]

theorem balanced_split (ds : List K) (h : 2 ≤ ds.length) :
    balanced ds = combine (balanced (ds.take (ds.length / 2)))
      (balanced (ds.drop (ds.length / 2))) := by
  match ds with
  | [] => simp at h
  | [_] => simp at h
  | _ :: _ :: _ => rw [balanced]

/-- The two addition orders agree over any commutative semiring. -/
theorem balanced_eq_fold (ds : List K) : balanced ds = fold ds := by
  match ds with
  | [] => simp
  | [d] => simp
  | a :: b :: ds =>
    rw [balanced_split _ (by simp)]
    rw [balanced_eq_fold, balanced_eq_fold, ← fold_append, List.take_append_drop]
termination_by ds.length
 decreasing_by
  all_goals simp only [List.length_take, List.length_drop, List.length_cons]
  all_goals omega

end GordieHowe.FractionTree
