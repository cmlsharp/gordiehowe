-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.AffineCoordinates
public import GordieHowe.Foundations.Algebra.QuadraticSystem
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Affine forms as lists of terms

An affine form on `ι → F` is `x ↦ ∑ (c, i) ∈ terms, c * x i + const`, stored as the list of its
terms, each a coefficient and a variable, and its constant (`AffineForm`); the C++ stores a
linear constraint the same way, as a list of (coefficient, variable) triples. Every operation on
forms is a computable definition that needs no decidable equality on the variables: the constant
`ofConst`, the variable `var`, sums (`+`, `sumFin`), scalar multiples and renaming of the
variables (`rename`). The verifier of a commit-and-prove system computes its rows this way from
the public transcript; a form is used only through its values (`eval` and the `eval_*` lemmas).

The bridge to `MvPolynomial` serves only the proofs: `toMvPolynomial` (with the `toMvPolynomial_*`
lemmas, `weight_toMvPolynomial` and `constantCoeff_toMvPolynomial`) relates the forms to the
quadratic systems that the Ligero constraint test consumes (`QuadraticSystem`,
`Ligero.Routing.sourceSystem`).
-/

namespace GordieHowe

open MvPolynomial

/-- **An affine form** `x ↦ ∑ (c, i) ∈ terms, c * x i + const` on the assignments `ι → F`: the
list of its terms, each a coefficient and a variable, and its constant. A variable may occur in
several terms. -/
structure AffineForm (F ι : Type*) where
  /-- The terms `c * x i`, each as the pair of the coefficient `c` and the variable `i`. -/
  terms : List (F × ι)
  /-- The constant term. -/
  const : F

namespace AffineForm

variable {F ι κ : Type*}

section CommRing

variable [CommRing F]

/-- The value of the form at the assignment `x`. -/
def eval (a : AffineForm F ι) (x : ι → F) : F :=
  (a.terms.map fun t => t.1 * x t.2).sum + a.const

/-- An affine form at an assignment: `a x` is `a.eval x`. -/
instance : CoeFun (AffineForm F ι) (fun _ => (ι → F) → F) := ⟨eval⟩

/-- The constant form `c`. -/
def ofConst (c : F) : AffineForm F ι := ⟨[], c⟩

/-- The variable `x i`. -/
def var (i : ι) : AffineForm F ι := ⟨[(1, i)], 0⟩

instance : Zero (AffineForm F ι) := ⟨⟨[], 0⟩⟩
instance : Add (AffineForm F ι) := ⟨fun a b => ⟨a.terms ++ b.terms, a.const + b.const⟩⟩
instance : SMul F (AffineForm F ι) :=
  ⟨fun c a => ⟨a.terms.map fun t => (c * t.1, t.2), c * a.const⟩⟩
instance : Neg (AffineForm F ι) := ⟨fun a => ⟨a.terms.map fun t => (-t.1, t.2), -a.const⟩⟩
instance : Sub (AffineForm F ι) := ⟨fun a b => a + -b⟩

/-- The form with its variables renamed along `f`: `x ↦ a (x ∘ f)`. -/
def rename (f : ι → κ) (a : AffineForm F ι) : AffineForm F κ :=
  ⟨a.terms.map fun t => (t.1, f t.2), a.const⟩

/-- The form whose terms are the images under `f` of the terms of `a` on which `f` is defined,
with the constant `c`. -/
def filterMapTerms (f : F × ι → Option (F × κ)) (a : AffineForm F ι) (c : F) : AffineForm F κ :=
  ⟨a.terms.filterMap f, c⟩

/-- The sum of a family of forms indexed by `Fin n`. -/
def sumFin {n : ℕ} (f : Fin n → AffineForm F ι) : AffineForm F ι :=
  (List.ofFn f).foldr (· + ·) 0

/-- The sum of the forms `f a` over the list `l`. -/
def sumList {α : Type*} (l : List α) (f : α → AffineForm F ι) : AffineForm F ι :=
  (l.map f).foldr (· + ·) 0

/-- The sum of the forms `f a` over a finite set of a linearly ordered type, in increasing
order. -/
def sumFinset {α : Type*} [LinearOrder α] (s : Finset α) (f : α → AffineForm F ι) :
    AffineForm F ι :=
  sumList (s.sort (· ≤ ·)) f

@[simp] theorem eval_ofConst (c : F) (x : ι → F) : (ofConst c : AffineForm F ι).eval x = c := by
  simp [eval, ofConst]

@[simp] theorem eval_var (i : ι) (x : ι → F) : (var i : AffineForm F ι).eval x = x i := by
  simp [eval, var]

@[simp] theorem eval_zero (x : ι → F) : (0 : AffineForm F ι).eval x = 0 := by
  change ([] : List F).sum + 0 = 0
  simp

@[simp] theorem eval_add (a b : AffineForm F ι) (x : ι → F) :
    (a + b).eval x = a.eval x + b.eval x := by
  change ((a.terms ++ b.terms).map fun t => t.1 * x t.2).sum + (a.const + b.const) = _
  simp only [eval, List.map_append, List.sum_append]
  ring

@[simp] theorem eval_smul (c : F) (a : AffineForm F ι) (x : ι → F) :
    (c • a).eval x = c * a.eval x := by
  have h : ∀ l : List (F × ι), ((l.map fun t => (c * t.1, t.2)).map fun t => t.1 * x t.2).sum =
      c * (l.map fun t => t.1 * x t.2).sum := fun l => by
    induction l with
    | nil => simp
    | cons t l ih =>
      simp only [List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      ring
  change ((a.terms.map fun t => (c * t.1, t.2)).map fun t => t.1 * x t.2).sum + c * a.const = _
  rw [h, eval, mul_add]

@[simp] theorem eval_neg (a : AffineForm F ι) (x : ι → F) : (-a).eval x = -a.eval x := by
  have h : ∀ l : List (F × ι), ((l.map fun t => (-t.1, t.2)).map fun t => t.1 * x t.2).sum =
      -(l.map fun t => t.1 * x t.2).sum := fun l => by
    induction l with
    | nil => simp
    | cons t l ih =>
      simp only [List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      simp only [map_neg, neg_mul, neg_add]
  change ((a.terms.map fun t => (-t.1, t.2)).map fun t => t.1 * x t.2).sum + -a.const = _
  rw [h, eval, neg_add]

@[simp] theorem eval_sub (a b : AffineForm F ι) (x : ι → F) :
    (a - b).eval x = a.eval x - b.eval x := by
  change (a + -b).eval x = _
  rw [eval_add, eval_neg, sub_eq_add_neg]

@[simp] theorem eval_rename (f : ι → κ) (a : AffineForm F ι) (x : κ → F) :
    (a.rename f).eval x = a.eval (x ∘ f) := by
  simp [eval, rename, Function.comp_def]

theorem eval_filterMapTerms (f : F × ι → Option (F × κ)) (a : AffineForm F ι) (c : F)
    (x : κ → F) :
    (filterMapTerms f a c).eval x =
      (a.terms.map fun t => (f t).elim 0 fun u => u.1 * x u.2).sum + c := by
  simp only [eval, filterMapTerms]
  congr 1
  induction a.terms with
  | nil => simp
  | cons t l ih =>
    rw [List.filterMap_cons, List.map_cons, List.sum_cons]
    cases f t with
    | none => simpa using ih
    | some u => simpa using ih

theorem eval_foldr_add (l : List (AffineForm F ι)) (x : ι → F) :
    (l.foldr (· + ·) 0).eval x = (l.map fun a => a.eval x).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

@[simp] theorem eval_sumFin {n : ℕ} (f : Fin n → AffineForm F ι) (x : ι → F) :
    (sumFin f).eval x = ∑ i, (f i).eval x := by
  rw [sumFin, eval_foldr_add, List.map_ofFn, Fin.sum_ofFn]
  rfl

@[simp] theorem eval_sumList {α : Type*} (l : List α) (f : α → AffineForm F ι) (x : ι → F) :
    (sumList l f).eval x = (l.map fun a => (f a).eval x).sum := by
  rw [sumList, eval_foldr_add, List.map_map]
  rfl

@[simp] theorem eval_sumFinset {α : Type*} [LinearOrder α] (s : Finset α)
    (f : α → AffineForm F ι) (x : ι → F) :
    (sumFinset s f).eval x = ∑ a ∈ s, (f a).eval x := by
  rw [sumFinset, eval_sumList, ← List.sum_toFinset _ (s.sort_nodup _), Finset.sort_toFinset]

/-! ### The polynomial of a form, for the proofs -/

/-- The form as a polynomial of total degree at most one (`totalDegree_toMvPolynomial_le`), the
representation of `QuadraticSystem`. -/
noncomputable def toMvPolynomial (a : AffineForm F ι) : MvPolynomial ι F :=
  (a.terms.map fun t => C t.1 * X t.2).sum + C a.const

@[simp] theorem eval_toMvPolynomial (a : AffineForm F ι) (x : ι → F) :
    MvPolynomial.eval x a.toMvPolynomial = a.eval x := by
  simp [toMvPolynomial, eval, map_list_sum, List.map_map, Function.comp_def]

@[simp] theorem toMvPolynomial_ofConst (c : F) :
    (ofConst c : AffineForm F ι).toMvPolynomial = C c := by
  simp [toMvPolynomial, ofConst]

@[simp] theorem toMvPolynomial_var (i : ι) : (var i : AffineForm F ι).toMvPolynomial = X i := by
  simp [toMvPolynomial, var]

@[simp] theorem toMvPolynomial_zero : (0 : AffineForm F ι).toMvPolynomial = 0 := by
  change (([] : List (MvPolynomial ι F)).sum + C 0) = 0
  simp

@[simp] theorem toMvPolynomial_add (a b : AffineForm F ι) :
    (a + b).toMvPolynomial = a.toMvPolynomial + b.toMvPolynomial := by
  change ((a.terms ++ b.terms).map fun t => C t.1 * X t.2).sum + C (a.const + b.const) = _
  simp only [toMvPolynomial, List.map_append, List.sum_append, map_add]
  ring

@[simp] theorem toMvPolynomial_smul (c : F) (a : AffineForm F ι) :
    (c • a).toMvPolynomial = C c * a.toMvPolynomial := by
  have h : ∀ l : List (F × ι),
      ((l.map fun t => (c * t.1, t.2)).map fun t => (C t.1 * X t.2 : MvPolynomial ι F)).sum =
        C c * (l.map fun t => C t.1 * X t.2).sum := fun l => by
    induction l with
    | nil => simp
    | cons t l ih =>
      simp only [List.map_cons, List.sum_cons] at ih ⊢
      rw [ih, map_mul]
      ring
  change ((a.terms.map fun t => (c * t.1, t.2)).map fun t => C t.1 * X t.2).sum +
    C (c * a.const) = _
  rw [h, toMvPolynomial, mul_add, map_mul]

@[simp] theorem toMvPolynomial_neg (a : AffineForm F ι) :
    (-a).toMvPolynomial = -a.toMvPolynomial := by
  have h : ∀ l : List (F × ι),
      ((l.map fun t => (-t.1, t.2)).map fun t => (C t.1 * X t.2 : MvPolynomial ι F)).sum =
        -(l.map fun t => C t.1 * X t.2).sum := fun l => by
    induction l with
    | nil => simp
    | cons t l ih =>
      simp only [List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      simp only [map_neg, neg_mul, neg_add]
  change ((a.terms.map fun t => (-t.1, t.2)).map fun t => C t.1 * X t.2).sum + C (-a.const) = _
  rw [h, toMvPolynomial, neg_add, map_neg]

@[simp] theorem toMvPolynomial_sub (a b : AffineForm F ι) :
    (a - b).toMvPolynomial = a.toMvPolynomial - b.toMvPolynomial := by
  change (a + -b).toMvPolynomial = _
  rw [toMvPolynomial_add, toMvPolynomial_neg, sub_eq_add_neg]

@[simp] theorem toMvPolynomial_rename (f : ι → κ) (a : AffineForm F ι) :
    (a.rename f).toMvPolynomial = MvPolynomial.rename f a.toMvPolynomial := by
  simp [toMvPolynomial, rename, map_list_sum, List.map_map, Function.comp_def]

theorem toMvPolynomial_foldr_add (l : List (AffineForm F ι)) :
    (l.foldr (· + ·) 0).toMvPolynomial = (l.map toMvPolynomial).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

@[simp] theorem toMvPolynomial_sumFin {n : ℕ} (f : Fin n → AffineForm F ι) :
    (sumFin f).toMvPolynomial = ∑ i, (f i).toMvPolynomial := by
  rw [sumFin, toMvPolynomial_foldr_add, List.map_ofFn, Fin.sum_ofFn]
  rfl

@[simp] theorem toMvPolynomial_sumList {α : Type*} (l : List α) (f : α → AffineForm F ι) :
    (sumList l f).toMvPolynomial = (l.map fun a => (f a).toMvPolynomial).sum := by
  rw [sumList, toMvPolynomial_foldr_add, List.map_map]
  rfl

@[simp] theorem toMvPolynomial_sumFinset {α : Type*} [LinearOrder α] (s : Finset α)
    (f : α → AffineForm F ι) :
    (sumFinset s f).toMvPolynomial = ∑ a ∈ s, (f a).toMvPolynomial := by
  rw [sumFinset, toMvPolynomial_sumList, ← List.sum_toFinset _ (s.sort_nodup _),
    Finset.sort_toFinset]

@[simp] theorem constantCoeff_toMvPolynomial (a : AffineForm F ι) :
    a.toMvPolynomial.constantCoeff = a.const := by
  simp [toMvPolynomial, map_list_sum, List.map_map, Function.comp_def]

theorem totalDegree_toMvPolynomial_le (a : AffineForm F ι) :
    a.toMvPolynomial.totalDegree ≤ 1 := by
  classical
  unfold toMvPolynomial
  refine (totalDegree_add _ _).trans (max_le ?_ (by simp))
  induction a.terms with
  | nil => simp
  | cons t l ih =>
    rw [List.map_cons, List.sum_cons]
    refine (totalDegree_add _ _).trans (max_le ?_ ih)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add, X]
    exact (totalDegree_monomial_le _ _).trans (by simp)

/-! ### Affine forms of linear maps -/

/-- **The affine form of a linear form and a constant** on `Fin N`: the term `f (e_k) · x_k` for
every coordinate `k` in order, and the constant (computable). -/
def ofLinear {F : Type} [CommRing F] {N : ℕ} (f : (Fin N → F) →ₗ[F] F) (c : F) :
    AffineForm F (Fin N) :=
  ⟨(List.finRange N).map fun k => (f fun j => if k = j then 1 else 0, k), c⟩

/-- The affine form of a linear form and a constant evaluates to `f x + c`. -/
@[simp] theorem eval_ofLinear {F : Type} [CommRing F] {N : ℕ}
    (f : (Fin N → F) →ₗ[F] F) (c : F) (x : Fin N → F) : (ofLinear f c).eval x = f x + c := by
  rw [ofLinear, eval, List.map_map, f.pi_apply_eq_sum_univ x,
    Fin.sum_univ_def]
  congr 2
  exact List.map_congr_left fun k _ => by simp [smul_eq_mul, mul_comm]

end CommRing

/-- **A finite family of affine forms as a quadratic system**: the forms' polynomials, of total
degree at most one. It holds exactly when every form vanishes (`ofForms_holds_iff`). -/
noncomputable def _root_.GordieHowe.QuadraticSystem.ofForms {F ι : Type} [CommRing F] (E : Type)
    [Fintype E] (forms : E → AffineForm F ι) : QuadraticSystem F ι where
  Eq := E
  polynomial e := (forms e).toMvPolynomial
  degree e := (forms e).totalDegree_toMvPolynomial_le.trans (by decide)

@[simp] theorem _root_.GordieHowe.QuadraticSystem.ofForms_holds_iff {F ι : Type} [CommRing F] [Fintype ι]
    (E : Type) [Fintype E] (forms : E → AffineForm F ι) (w : ι → F) :
    (QuadraticSystem.ofForms E forms).Holds w ↔ ∀ e, (forms e).eval w = 0 := by
  simp [QuadraticSystem.Holds, QuadraticSystem.ofForms]

section Field

variable [Field F]

open Classical in
/-- The coefficient of the variable `j` in the polynomial of a form: the sum of the coefficients
of the terms on `j`. -/
theorem weight_toMvPolynomial (a : AffineForm F ι) (j : ι) :
    AffineCoordinates.weight a.toMvPolynomial j =
      (a.terms.map fun t => if t.2 = j then t.1 else 0).sum := by
  have h0 : (0 : ι →₀ ℕ) ≠ Finsupp.single j 1 := (Finsupp.single_ne_zero.mpr one_ne_zero).symm
  unfold AffineCoordinates.weight toMvPolynomial
  rw [MvPolynomial.coeff_add, coeff_C, if_neg h0, add_zero]
  induction a.terms with
  | nil => simp
  | cons t l ih =>
    rw [List.map_cons, List.sum_cons, MvPolynomial.coeff_add, ih, List.map_cons, List.sum_cons,
      coeff_C_mul, coeff_X']
    simp only [Finsupp.single_left_inj one_ne_zero]
    split_ifs <;> simp

/-- **A sum over the terms is a sum over the variables of the coefficients**: for maps `ψ i`
additive in the coefficient, the sum over the terms `(c, i)` of `ψ i c * g i` is the sum over
the variables `i` of `ψ i` of the coefficient of `i` in the polynomial, times `g i`. -/
theorem sum_terms_eq_sum_weight [Fintype ι] (a : AffineForm F ι) (ψ : ι → F →+ F) (g : ι → F) :
    (a.terms.map fun t => ψ t.2 t.1 * g t.2).sum =
      ∑ i, ψ i (AffineCoordinates.weight a.toMvPolynomial i) * g i := by
  classical
  simp only [weight_toMvPolynomial]
  induction a.terms with
  | nil => simp
  | cons t l ih =>
    have hsplit : ∀ i, ψ i ((if t.2 = i then t.1 else 0) +
        (l.map fun t => if t.2 = i then t.1 else 0).sum) * g i =
        (if t.2 = i then ψ i t.1 * g i else 0) +
          ψ i ((l.map fun t => if t.2 = i then t.1 else 0).sum) * g i := fun i => by
      rw [map_add, add_mul]
      split_ifs <;> simp
    simp only [List.map_cons, List.sum_cons, hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, ih]

/-- **The coefficient a form puts at an array location**, for variables placed at locations by
`loc`: the sum of the coefficients of the terms whose variable sits at `(row, col)`. Computable:
it compares locations only. -/
def coeffAt {Row Col : Type*} [DecidableEq Row] [DecidableEq Col] (loc : ι → Row × Col)
    (a : AffineForm F ι) (row : Row) (col : Col) : F :=
  (a.terms.map fun t => if loc t.2 = (row, col) then t.1 else 0).sum

variable [Fintype ι]

/-- A form's coefficient at a location is the location's accumulated coefficient of its
polynomial (`AffineCoordinates.coeffAt`). -/
theorem coeffAt_eq {Row Col : Type*} [Fintype Row] [Fintype Col] [DecidableEq Row]
    [DecidableEq Col] (loc : ι → Row × Col) (a : AffineForm F ι) (row : Row) (col : Col) :
    a.coeffAt loc row col =
      AffineCoordinates.coeffAt loc (AffineCoordinates.weight a.toMvPolynomial) row col := by
  classical
  unfold coeffAt AffineCoordinates.coeffAt
  simp only [weight_toMvPolynomial]
  induction a.terms with
  | nil => simp
  | cons t l ih =>
    have hsplit : ∀ j : ι, (if loc j = (row, col) then
        ((if t.2 = j then t.1 else 0) + (l.map fun t => if t.2 = j then t.1 else 0).sum) else 0) =
        (if t.2 = j then (if loc j = (row, col) then t.1 else 0) else 0) +
          (if loc j = (row, col) then (l.map fun t => if t.2 = j then t.1 else 0).sum else 0) :=
      fun j => by split_ifs <;> simp
    simp only [List.map_cons, List.sum_cons, hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, ih]

end Field

end AffineForm

end GordieHowe
