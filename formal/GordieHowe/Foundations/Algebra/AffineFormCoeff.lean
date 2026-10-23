-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.AffineForm

@[expose] public section

/-!
# The coefficients of an affine form and the variables it reads

The coefficient of an affine form at a variable is the change of its value along that variable's
unit vector (`AffineForm.coeff`); for an affine form it is the sum of the coefficients of the terms
on that variable (`coeff_eq_sum_terms`). A form **reads only** the variables of a predicate `S`
(`AffineForm.ReadsOnly`) when its coefficient at every other variable is zero; on finitely many
variables its value then depends only on the variables of `S` (`eval_eq_of_readsOnly`).

The library: the coefficients of sums, scalar multiples, constants, variables, finite sums and
renamed forms, and the matching closure lemmas of `ReadsOnly`.
-/

namespace GordieHowe.AffineForm

variable {F ι κ : Type*} [CommRing F] [DecidableEq ι]

/-- **The coefficient of a form at a variable**: its change along the variable's unit vector. -/
def coeff (a : AffineForm F ι) (i : ι) : F := a.eval (Pi.single i 1) - a.eval 0

/-- The coefficient at `i` is the sum of the coefficients of the terms on `i`. -/
theorem coeff_eq_sum_terms (a : AffineForm F ι) (i : ι) :
    a.coeff i = (a.terms.map fun t => if t.2 = i then t.1 else 0).sum := by
  simp only [coeff, eval, Pi.zero_apply, mul_zero, List.map_const', List.sum_replicate,
    smul_zero, zero_add, add_sub_cancel_right]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  by_cases h : t.2 = i
  · subst h
    simp
  · simp [h]

@[simp] theorem coeff_zero (i : ι) : (0 : AffineForm F ι).coeff i = 0 := by
  simp [coeff]

@[simp] theorem coeff_ofConst (c : F) (i : ι) : (ofConst c : AffineForm F ι).coeff i = 0 := by
  simp [coeff]

@[simp] theorem coeff_var (j i : ι) :
    (var j : AffineForm F ι).coeff i = if j = i then 1 else 0 := by
  simp only [coeff, eval_var, Pi.single_apply, Pi.zero_apply, sub_zero]

@[simp] theorem coeff_add (a b : AffineForm F ι) (i : ι) :
    (a + b).coeff i = a.coeff i + b.coeff i := by
  simp only [coeff, eval_add]
  ring

@[simp] theorem coeff_smul (c : F) (a : AffineForm F ι) (i : ι) :
    (c • a).coeff i = c * a.coeff i := by
  simp only [coeff, eval_smul]
  ring

@[simp] theorem coeff_neg (a : AffineForm F ι) (i : ι) : (-a).coeff i = -a.coeff i := by
  simp only [coeff, eval_neg]
  ring

@[simp] theorem coeff_sub (a b : AffineForm F ι) (i : ι) :
    (a - b).coeff i = a.coeff i - b.coeff i := by
  simp only [coeff, eval_sub]
  ring

@[simp] theorem coeff_sumFin {n : ℕ} (f : Fin n → AffineForm F ι) (i : ι) :
    (sumFin f).coeff i = ∑ k, (f k).coeff i := by
  simp only [coeff, eval_sumFin, Finset.sum_sub_distrib]

/-- **A form on finitely many variables is its coefficients and its value at zero.** -/
theorem eval_eq_sum_coeff [Fintype ι] (a : AffineForm F ι) (x : ι → F) :
    a.eval x = ∑ i, a.coeff i * x i + a.eval 0 := by
  simp only [coeff_eq_sum_terms]
  have h0 : a.eval 0 = a.const := by simp [eval]
  rw [h0, eval]
  congr 1
  induction a.terms with
  | nil => simp
  | cons t l ih =>
    have ht : ∑ i, (if t.2 = i then t.1 else 0) * x i = t.1 * x t.2 := by
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq]
      simp
    simp only [List.map_cons, List.sum_cons, ih, add_mul, Finset.sum_add_distrib, ht]

/-- **The coefficient of a renamed form** at `k`: the sum of the coefficients at the variables
renamed to `k`. -/
theorem coeff_rename [Fintype ι] [DecidableEq κ] (f : ι → κ) (a : AffineForm F ι) (k : κ) :
    (a.rename f).coeff k = ∑ i, if f i = k then a.coeff i else 0 := by
  have h1 := eval_eq_sum_coeff a (Pi.single k 1 ∘ f)
  have h2 := eval_eq_sum_coeff a (fun _ => 0)
  simp only [coeff, eval_rename]
  have hz : (0 : κ → F) ∘ f = fun _ => 0 := rfl
  rw [h1, hz, h2]
  simp only [Function.comp_apply, Pi.single_apply, mul_zero, Finset.sum_const_zero, zero_add,
    mul_ite, mul_one]
  rw [add_sub_cancel_right]
  rfl

/-! ### The variables a form reads -/

/-- **A form reads only the variables of `S`**: its coefficient at every other variable is zero. -/
def ReadsOnly (S : ι → Prop) (a : AffineForm F ι) : Prop := ∀ i, a.coeff i ≠ 0 → S i

namespace ReadsOnly

variable {S T : ι → Prop}

theorem mono {a : AffineForm F ι} (h : a.ReadsOnly S) (hST : ∀ i, S i → T i) : a.ReadsOnly T :=
  fun i hi => hST i (h i hi)

/-- The coefficient off `S` is zero. -/
theorem coeff_eq_zero {a : AffineForm F ι} (h : a.ReadsOnly S) {i : ι} (hi : ¬ S i) :
    a.coeff i = 0 := by
  by_contra h'
  exact hi (h i h')

theorem zero : (0 : AffineForm F ι).ReadsOnly S := fun i h => absurd (coeff_zero i) h

theorem ofConst (c : F) : (AffineForm.ofConst c : AffineForm F ι).ReadsOnly S :=
  fun i h => absurd (coeff_ofConst c i) h

theorem var {j : ι} (hj : S j) : (AffineForm.var j : AffineForm F ι).ReadsOnly S := fun i h => by
  rw [coeff_var] at h
  split_ifs at h with hji
  · exact hji ▸ hj
  · exact absurd rfl h

theorem add {a b : AffineForm F ι} (ha : a.ReadsOnly S) (hb : b.ReadsOnly S) :
    (a + b).ReadsOnly S := fun i h => by
  by_contra hi
  rw [coeff_add, ha.coeff_eq_zero hi, hb.coeff_eq_zero hi, add_zero] at h
  exact h rfl

theorem smul (c : F) {a : AffineForm F ι} (ha : a.ReadsOnly S) : (c • a).ReadsOnly S :=
  fun i h => by
  by_contra hi
  rw [coeff_smul, ha.coeff_eq_zero hi, mul_zero] at h
  exact h rfl

/-- **A scalar multiple reads nothing when the scalar is zero.** -/
theorem smul_of {c : F} {a : AffineForm F ι} (ha : c ≠ 0 → a.ReadsOnly S) : (c • a).ReadsOnly S :=
  fun i h => by
  by_cases hc : c = 0
  · rw [hc, coeff_smul, zero_mul] at h
    exact absurd rfl h
  · by_contra hi
    rw [coeff_smul, (ha hc).coeff_eq_zero hi, mul_zero] at h
    exact h rfl

theorem neg {a : AffineForm F ι} (ha : a.ReadsOnly S) : (-a).ReadsOnly S := fun i h => by
  by_contra hi
  rw [coeff_neg, ha.coeff_eq_zero hi, neg_zero] at h
  exact h rfl

theorem sub {a b : AffineForm F ι} (ha : a.ReadsOnly S) (hb : b.ReadsOnly S) :
    (a - b).ReadsOnly S := fun i h => by
  by_contra hi
  rw [coeff_sub, ha.coeff_eq_zero hi, hb.coeff_eq_zero hi, sub_zero] at h
  exact h rfl

theorem sumFin {n : ℕ} {f : Fin n → AffineForm F ι} (hf : ∀ k, (f k).ReadsOnly S) :
    (AffineForm.sumFin f).ReadsOnly S := fun i h => by
  by_contra hi
  rw [coeff_sumFin, Finset.sum_eq_zero fun k _ => (hf k).coeff_eq_zero hi] at h
  exact h rfl

/-- **A renamed form reads the images of what it reads.** -/
theorem rename [Fintype ι] [DecidableEq κ] {f : ι → κ} {a : AffineForm F ι} (ha : a.ReadsOnly S)
    {T : κ → Prop} (hT : ∀ i, S i → T (f i)) : (a.rename f).ReadsOnly T := fun k h => by
  by_contra hk
  rw [coeff_rename, Finset.sum_eq_zero fun i _ => ?_] at h
  · exact h rfl
  · split_ifs with hik
    · exact ha.coeff_eq_zero fun hi => hk (hik ▸ hT i hi)
    · rfl

/-- **Every form on finitely many variables reads only the variables of `S`** when `S` holds
everywhere. -/
theorem of_forall {a : AffineForm F ι} (hS : ∀ i, S i) : a.ReadsOnly S := fun i _ => hS i

end ReadsOnly

/-- **A form reading only `S` has the same value at assignments agreeing on `S`.** -/
theorem eval_eq_of_readsOnly [Fintype ι] {S : ι → Prop} {a : AffineForm F ι} (h : a.ReadsOnly S)
    {x y : ι → F} (hxy : ∀ i, S i → x i = y i) : a.eval x = a.eval y := by
  rw [eval_eq_sum_coeff a x, eval_eq_sum_coeff a y]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : S i
  · rw [hxy i hi]
  · rw [h.coeff_eq_zero hi, zero_mul, zero_mul]

end GordieHowe.AffineForm
