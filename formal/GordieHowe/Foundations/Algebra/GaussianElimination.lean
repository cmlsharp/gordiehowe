-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Executable Gaussian elimination

`solve A b` decides whether the linear system `A *ᵥ x = b` over a field with decidable
equality is consistent and returns a solution when it is. It eliminates one unknown at a
time: if some row has a nonzero coefficient on the first unknown, that row is the pivot,
the first unknown is expressed through the others, and the pivot row is subtracted from
every other row (`eliminate`); otherwise the first unknown is free and set to zero. Both
steps preserve the solution set of the remaining unknowns (`mulVec_eq_iff_eliminate`,
`mulVec_eq_iff_dropFirst`), which gives `solve_eq_some` (any returned vector solves the
system) and `solve_isSome_iff` (a vector is returned iff the system is consistent).

This is the textbook elimination (e.g. Trefethen–Bau, *Numerical Linear Algebra*, Lecture 20,
without pivoting for size: over an exact field any nonzero pivot works). Every intermediate
matrix is stored in an array (`solveArr`), so no entry is recomputed through a chain of closures.
-/

namespace GordieHowe.GaussianElimination

open Matrix

variable {F : Type*}

/-- The function view of a row-major array matrix. -/
def toMat {m n : ℕ} (M : Vector (Vector F n) m) : Fin m → Fin n → F :=
  fun r j => M[r][j]

/-- The row-major array holding the entries of `A`. -/
def ofMat {m n : ℕ} (A : Fin m → Fin n → F) : Vector (Vector F n) m :=
  Vector.ofFn fun r => Vector.ofFn (A r)

@[simp] theorem toMat_ofMat {m n : ℕ} (A : Fin m → Fin n → F) : toMat (ofMat A) = A := by
  funext r j
  simp [toMat, ofMat]

@[simp] theorem get_ofFn' {n : ℕ} (v : Fin n → F) : (Vector.ofFn v).get = v := by
  funext i
  simp only [Vector.get, Vector.toArray_ofFn, Array.getElem_ofFn]
  exact congrArg v (Fin.ext rfl)

variable [Field F]

section Steps

variable {m n : ℕ}

/-- The pivot row `i`'s expression for the first unknown in terms of the others `y`. -/
def pivotValue (A : Fin (m + 1) → Fin (n + 1) → F) (b : Fin (m + 1) → F) (i : Fin (m + 1))
    (y : Fin n → F) : F :=
  (b i - ∑ j : Fin n, A i j.succ * y j) / A i 0

/-- Coefficients of the system left after eliminating the first unknown with pivot row `i`:
row `r` is row `i.succAbove r` minus `A (i.succAbove r) 0 / A i 0` times row `i`, restricted to
the remaining unknowns. -/
def eliminate (A : Fin (m + 1) → Fin (n + 1) → F) (i : Fin (m + 1)) : Fin m → Fin n → F :=
  fun r j => A (i.succAbove r) j.succ - A (i.succAbove r) 0 / A i 0 * A i j.succ

/-- Right-hand side matching `eliminate`. -/
def eliminateRhs (A : Fin (m + 1) → Fin (n + 1) → F) (b : Fin (m + 1) → F) (i : Fin (m + 1)) :
    Fin m → F :=
  fun r => b (i.succAbove r) - A (i.succAbove r) 0 / A i 0 * b i

/-- Coefficients of the remaining unknowns, when the first unknown is dropped. -/
def dropFirst (A : Fin m → Fin (n + 1) → F) : Fin m → Fin n → F :=
  fun r j => A r j.succ

theorem mulVec_apply_succ (A : Fin m → Fin (n + 1) → F) (x : Fin (n + 1) → F) (r : Fin m) :
    (A *ᵥ x) r = A r 0 * x 0 + ∑ j : Fin n, A r j.succ * x j.succ := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem eliminate_mulVec_apply (A : Fin (m + 1) → Fin (n + 1) → F) (i : Fin (m + 1))
    (y : Fin n → F) (r : Fin m) :
    (eliminate A i *ᵥ y) r = (∑ j : Fin n, A (i.succAbove r) j.succ * y j)
      - A (i.succAbove r) 0 / A i 0 * ∑ j : Fin n, A i j.succ * y j := by
  simp only [Matrix.mulVec, dotProduct, eliminate, sub_mul, Finset.sum_sub_distrib,
    Finset.mul_sum, mul_assoc]

/-- Eliminating the first unknown with a pivot row whose first coefficient is nonzero
preserves the solution set: `x` solves the system iff its first entry is the pivot row's
expression in the others and the others solve the eliminated system. -/
theorem mulVec_eq_iff_eliminate {A : Fin (m + 1) → Fin (n + 1) → F} {b : Fin (m + 1) → F}
    {i : Fin (m + 1)} (ha : A i 0 ≠ 0) (x : Fin (n + 1) → F) :
    A *ᵥ x = b ↔
      x 0 = pivotValue A b i (Fin.tail x) ∧ eliminate A i *ᵥ Fin.tail x = eliminateRhs A b i := by
  have row : ∀ r, (A *ᵥ x) r = b r ↔ A r 0 * x 0 + ∑ j : Fin n, A r j.succ * x j.succ = b r :=
    fun r => by rw [mulVec_apply_succ]
  constructor
  · intro h
    have hr : ∀ r, A r 0 * x 0 + ∑ j : Fin n, A r j.succ * x j.succ = b r :=
      fun r => (row r).mp (congrFun h r)
    have hx0 : x 0 = pivotValue A b i (Fin.tail x) := by
      unfold pivotValue
      rw [eq_div_iff ha]
      simp only [Fin.tail]
      linear_combination hr i
    refine ⟨hx0, funext fun r => ?_⟩
    have hrr := hr (i.succAbove r)
    rw [hx0] at hrr
    unfold pivotValue at hrr
    rw [eliminate_mulVec_apply]
    simp only [eliminateRhs, Fin.tail] at hrr ⊢
    linear_combination hrr
  · rintro ⟨hx0, h⟩
    funext r
    rw [row]
    revert r
    rw [Fin.forall_iff_succAbove i]
    refine ⟨?_, fun r => ?_⟩
    · rw [hx0]
      unfold pivotValue
      simp only [Fin.tail]
      field_simp
      ring
    · have hr := congrFun h r
      rw [eliminate_mulVec_apply] at hr
      rw [hx0]
      unfold pivotValue
      simp only [eliminateRhs, Fin.tail] at hr ⊢
      linear_combination hr

/-- When no row has a nonzero first coefficient, the first unknown does not occur: `x` solves
the system iff its other entries solve the system without it. -/
theorem mulVec_eq_iff_dropFirst {A : Fin m → Fin (n + 1) → F} {b : Fin m → F}
    (h0 : ∀ r, A r 0 = 0) (x : Fin (n + 1) → F) :
    A *ᵥ x = b ↔ dropFirst A *ᵥ Fin.tail x = b := by
  have hx : A *ᵥ x = dropFirst A *ᵥ Fin.tail x := by
    funext r
    rw [mulVec_apply_succ, h0, zero_mul, zero_add]
    rfl
  rw [hx]

end Steps

variable [DecidableEq F]

/-- `solve` on arrays: every intermediate system is stored in an array, so each entry is computed
once (`solve` is the function interface).

Running time: one elimination step per unknown. A step scans the first column for a nonzero
entry (at most `m` equality tests). With a pivot it computes the eliminated system, `m` divisions
and `2·m·n` multiplications and subtractions, and the row count drops by one; without a pivot it
copies the remaining columns and does no field operation. At most `min(m, n)` steps have a pivot,
and the recursion stops once no rows are left, so the total is `O(m · n · min(m, n))` field
operations and `O(m · n)` equality tests, plus `O(m · n²)` element copies; back-substitution adds
`O(n · min(m, n))` field operations. This running time is argued here, not proved in Lean. -/
def solveArr : {m n : ℕ} → Vector (Vector F n) m → Vector F m → Option (Vector F n)
  | m, 0, _, b => if ∀ r : Fin m, b.get r = 0 then some (Vector.ofFn Fin.elim0) else none
  | 0, n + 1, _, _ => some (Vector.replicate (n + 1) 0)
  | m + 1, _ + 1, A, b =>
    match (List.finRange (m + 1)).find? (fun r => decide (toMat A r 0 ≠ 0)) with
    | some i =>
      (solveArr (ofMat (eliminate (toMat A) i)) (Vector.ofFn (eliminateRhs (toMat A) b.get i))).map
        fun y => Vector.ofFn (Fin.cons (pivotValue (toMat A) b.get i y.get) y.get)
    | none => (solveArr (ofMat (dropFirst (toMat A))) b).map fun y => Vector.ofFn (Fin.cons 0 y.get)

/-- A solution of `A *ᵥ x = b` if the system is consistent, `none` otherwise
(`solve_eq_some`, `solve_isSome_iff`).

Running time: `solveArr` on the arrays of `A` and `b`, `O(m · n · min(m, n))` field operations
(its docstring), after `m · n` reads of `A` to fill the array.
This running time is argued here, not proved in Lean. -/
def solve {m n : ℕ} (A : Fin m → Fin n → F) (b : Fin m → F) : Option (Fin n → F) :=
  (solveArr (ofMat A) (Vector.ofFn b)).map Vector.get

theorem solveArr_zero_cols {m : ℕ} (A : Vector (Vector F 0) m) (b : Vector F m) :
    solveArr A b = if ∀ r : Fin m, b.get r = 0 then some (Vector.ofFn Fin.elim0) else none := by
  cases m <;> rfl

theorem solveArr_pivot {m n : ℕ} (A : Vector (Vector F (n + 1)) (m + 1)) (b : Vector F (m + 1))
    {i : Fin (m + 1)}
    (hi : (List.finRange (m + 1)).find? (fun r => decide (toMat A r 0 ≠ 0)) = some i) :
    solveArr A b =
      (solveArr (ofMat (eliminate (toMat A) i)) (Vector.ofFn (eliminateRhs (toMat A) b.get i))).map
        fun y => Vector.ofFn (Fin.cons (pivotValue (toMat A) b.get i y.get) y.get) := by
  simp only [solveArr, hi]

theorem solveArr_noPivot {m n : ℕ} (A : Vector (Vector F (n + 1)) (m + 1)) (b : Vector F (m + 1))
    (hi : (List.finRange (m + 1)).find? (fun r => decide (toMat A r 0 ≠ 0)) = none) :
    solveArr A b =
      (solveArr (ofMat (dropFirst (toMat A))) b).map fun y => Vector.ofFn (Fin.cons 0 y.get) := by
  simp only [solveArr, hi]

/-- Every array `solveArr` returns solves the system. -/
theorem solveArr_eq_some : ∀ {m n : ℕ} {A : Vector (Vector F n) m} {b : Vector F m}
    {x : Vector F n}, solveArr A b = some x → toMat A *ᵥ x.get = b.get
  | m, 0, A, b, x, h => by
    rw [solveArr_zero_cols] at h
    split_ifs at h with hb
    funext r
    simp [Matrix.mulVec, dotProduct, hb r]
  | 0, _ + 1, A, b, x, _ => funext fun r => r.elim0
  | m + 1, n + 1, A, b, x, h => by
    cases hi : (List.finRange (m + 1)).find? (fun r => decide (toMat A r 0 ≠ 0)) with
    | some i =>
      rw [solveArr_pivot A b hi] at h
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp h
      have ha : toMat A i 0 ≠ 0 := by simpa using List.find?_some hi
      rw [mulVec_eq_iff_eliminate ha]
      have := solveArr_eq_some hy
      simp only [toMat_ofMat, get_ofFn'] at this
      exact ⟨by simp, by simpa [Fin.tail] using this⟩
    | none =>
      rw [solveArr_noPivot A b hi] at h
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp h
      have h0 : ∀ r, toMat A r 0 = 0 := fun r => by
        simpa using List.find?_eq_none.mp hi r (List.mem_finRange r)
      rw [mulVec_eq_iff_dropFirst h0]
      have := solveArr_eq_some hy
      simp only [toMat_ofMat] at this
      simpa [Fin.tail] using this

/-- `solveArr` returns an array whenever the system is consistent. -/
theorem solveArr_isSome_of_mulVec_eq : ∀ {m n : ℕ} {A : Vector (Vector F n) m} {b : Vector F m}
    {x : Fin n → F}, toMat A *ᵥ x = b.get → (solveArr A b).isSome
  | m, 0, A, b, x, h => by
    have hb : ∀ r, b.get r = 0 := fun r => by
      rw [← congrFun h r]
      simp [Matrix.mulVec, dotProduct]
    simp [solveArr_zero_cols, hb]
  | 0, _ + 1, A, b, x, _ => rfl
  | m + 1, n + 1, A, b, x, h => by
    cases hi : (List.finRange (m + 1)).find? (fun r => decide (toMat A r 0 ≠ 0)) with
    | some i =>
      rw [solveArr_pivot A b hi, Option.isSome_map]
      have ha : toMat A i 0 ≠ 0 := by simpa using List.find?_some hi
      refine solveArr_isSome_of_mulVec_eq (x := Fin.tail x) ?_
      simpa using ((mulVec_eq_iff_eliminate ha x).mp h).2
    | none =>
      rw [solveArr_noPivot A b hi, Option.isSome_map]
      have h0 : ∀ r, toMat A r 0 = 0 := fun r => by
        simpa using List.find?_eq_none.mp hi r (List.mem_finRange r)
      refine solveArr_isSome_of_mulVec_eq (x := Fin.tail x) ?_
      simpa using (mulVec_eq_iff_dropFirst h0 x).mp h

/-- Every vector `solve` returns solves the system. -/
theorem solve_eq_some {m n : ℕ} {A : Fin m → Fin n → F} {b : Fin m → F} {x : Fin n → F}
    (h : solve A b = some x) : A *ᵥ x = b := by
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp h
  simpa using solveArr_eq_some hy

/-- `solve` returns a vector whenever the system is consistent. -/
theorem solve_isSome_of_mulVec_eq {m n : ℕ} {A : Fin m → Fin n → F} {b : Fin m → F}
    {x : Fin n → F} (h : A *ᵥ x = b) : (solve A b).isSome := by
  rw [solve, Option.isSome_map]
  exact solveArr_isSome_of_mulVec_eq (x := x) (by simpa using h)

/-- `solve` returns a vector iff the system is consistent. -/
theorem solve_isSome_iff {m n : ℕ} {A : Fin m → Fin n → F} {b : Fin m → F} :
    (solve A b).isSome ↔ ∃ x, A *ᵥ x = b := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
    exact ⟨x, solve_eq_some hx⟩
  · rintro ⟨x, hx⟩
    exact solve_isSome_of_mulVec_eq hx

/-- `solve` returns `none` iff the system is inconsistent. -/
theorem solve_eq_none_iff {m n : ℕ} {A : Fin m → Fin n → F} {b : Fin m → F} :
    solve A b = none ↔ ¬ ∃ x, A *ᵥ x = b := by
  rw [← solve_isSome_iff, Option.not_isSome_iff_eq_none]

end GordieHowe.GaussianElimination
