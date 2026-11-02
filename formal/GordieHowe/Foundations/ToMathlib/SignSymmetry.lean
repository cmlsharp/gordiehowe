-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Signs of independent coordinates, given their positions

Coordinates `t : ι → α` with product weight `∏ i, w (t i)` (independent coordinates when `w` is a
probability mass function on `α`). A value `a` is an *edge* when `edge a` holds, and then carries
the sign `σ a`. The edge set `edgeSet edge t` is the set of coordinates holding an edge. Suppose the
signed weight of an edge is `m` times its weight, `∑_{edge a} w a · σ a = m · ∑_{edge a} w a`; for a
probability mass function, `m` is the mean sign of one edge.

* `sum_prod_mul_prod_sign_eq`: a test that depends on `t` only through the edge set `D` and the
  product of the signs at a set `S D ⊆ D` of positions has the same average as the test with that
  product replaced by `m ^ |S D|`. Given the positions, the signs are independent with mean `m`.
* `abs_sum_prod_mul_prod_sign_le`: if moreover the factor in front of the sign product has
  absolute value at most `1` on an event `E` of the edge set and vanishes off it, and `|S D| = 2`
  on `E`, the average has absolute value at most `m² · Pr[E]`.
-/

open Finset

namespace SignSymmetry

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- The set of coordinates of `t` holding an edge. -/
def edgeSet (edge : α → Prop) [DecidablePred edge] (t : ι → α) : Finset ι :=
  univ.filter fun i => edge (t i)

omit [DecidableEq ι] [Fintype α] in
/-- A coordinate is in the edge set exactly when it holds an edge. -/
theorem mem_edgeSet {edge : α → Prop} [DecidablePred edge] {t : ι → α} {i : ι} :
    i ∈ edgeSet edge t ↔ edge (t i) := by
  simp [edgeSet]

omit [DecidableEq ι] [Fintype α] in
/-- The edge set of `t` is `D` exactly when every coordinate holds an edge iff it is in `D`. -/
theorem edgeSet_eq_iff {edge : α → Prop} [DecidablePred edge] {t : ι → α} {D : Finset ι} :
    edgeSet edge t = D ↔ ∀ i, edge (t i) ↔ i ∈ D := by
  simp [Finset.ext_iff, mem_edgeSet]

variable (w σ : α → ℝ) (edge : α → Prop) [DecidablePred edge]

/-- **Expansion of one fibre.** The weight of the coordinates with edge set `D`, times the sign
product over `S`, is a product over coordinates of single-coordinate sums. -/
theorem sum_prod_mul_indicator_eq_prod (D S : Finset ι) :
    ∑ t : ι → α, (∏ i, w (t i)) * ((if edgeSet edge t = D then 1 else 0) * ∏ i ∈ S, σ (t i)) =
      ∏ i, ∑ a, w a * ((if (edge a ↔ i ∈ D) then 1 else 0) * if i ∈ S then σ a else 1) := by
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Fintype.prod_ite_mem, Finset.prod_boole]
  congr 2
  simp only [Finset.mem_univ, true_implies]
  exact if_congr edgeSet_eq_iff rfl rfl

/-- **Signs given the positions.** If the signed weight of an edge is `m` times its weight, the
sign product over a set `S ⊆ D` of edge positions averages, over the coordinates with edge set
`D`, to `m ^ |S|` times their weight. -/
theorem sum_prod_mul_indicator_mul_prod_sign (m : ℝ)
    (hm : ∑ a with edge a, w a * σ a = m * ∑ a with edge a, w a) (D S : Finset ι) (hS : S ⊆ D) :
    ∑ t : ι → α, (∏ i, w (t i)) * ((if edgeSet edge t = D then 1 else 0) * ∏ i ∈ S, σ (t i)) =
      m ^ S.card * ∑ t : ι → α, (∏ i, w (t i)) * (if edgeSet edge t = D then 1 else 0) := by
  have h0 := sum_prod_mul_indicator_eq_prod w σ edge D ∅
  simp only [Finset.prod_empty, mul_one, Finset.notMem_empty, ite_false] at h0
  rw [sum_prod_mul_indicator_eq_prod, h0]
  have hfactor : ∀ i, ∑ a, w a * ((if (edge a ↔ i ∈ D) then 1 else 0) * if i ∈ S then σ a else 1) =
      (if i ∈ S then m else 1) * ∑ a, w a * (if (edge a ↔ i ∈ D) then 1 else 0) := by
    intro i
    by_cases hi : i ∈ S
    · have hiD : i ∈ D := hS hi
      simp only [hi, hiD, iff_true, ite_true]
      rw [Finset.sum_filter, Finset.sum_filter] at hm
      calc ∑ a, w a * ((if edge a then (1 : ℝ) else 0) * σ a)
          = ∑ a, if edge a then w a * σ a else 0 :=
            Finset.sum_congr rfl fun a _ => by split_ifs <;> ring
        _ = m * ∑ a, (if edge a then w a else 0) := hm
        _ = m * ∑ a, w a * (if edge a then 1 else 0) := by
            congr 1
            exact Finset.sum_congr rfl fun a _ => by split_ifs <;> ring
    · simp only [hi, ite_false, mul_one, one_mul]
  simp only [hfactor, Finset.prod_mul_distrib, Fintype.prod_ite_mem, Finset.prod_const]

/-- **The sign symmetry.** A test of the form `f(D) · ∏_{i ∈ S(D)} σ(t i)`, with `D` the edge set
of `t` and `S(D) ⊆ D`, has the same average as `f(D) · m ^ |S(D)|`. -/
theorem sum_prod_mul_prod_sign_eq (m : ℝ)
    (hm : ∑ a with edge a, w a * σ a = m * ∑ a with edge a, w a) (f : Finset ι → ℝ)
    (S : Finset ι → Finset ι) (hS : ∀ D, S D ⊆ D) :
    ∑ t : ι → α, (∏ i, w (t i)) * (f (edgeSet edge t) * ∏ i ∈ S (edgeSet edge t), σ (t i)) =
      ∑ t : ι → α, (∏ i, w (t i)) * (f (edgeSet edge t) * m ^ (S (edgeSet edge t)).card) := by
  have hsplit : ∀ G : Finset ι → (ι → α) → ℝ, ∀ t : ι → α,
      G (edgeSet edge t) t = ∑ D, (if edgeSet edge t = D then 1 else 0) * G D t := by
    intro G t
    simp
  calc ∑ t : ι → α, (∏ i, w (t i)) * (f (edgeSet edge t) * ∏ i ∈ S (edgeSet edge t), σ (t i))
      = ∑ D, f D * ∑ t : ι → α,
          (∏ i, w (t i)) * ((if edgeSet edge t = D then 1 else 0) * ∏ i ∈ S D, σ (t i)) := by
        simp_rw [hsplit (fun D t => (∏ i, w (t i)) * (f D * ∏ i ∈ S D, σ (t i))), Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun D _ => Finset.sum_congr rfl fun t _ => by ring
    _ = ∑ D, f D * (m ^ (S D).card *
          ∑ t : ι → α, (∏ i, w (t i)) * (if edgeSet edge t = D then 1 else 0)) := by
        refine Finset.sum_congr rfl fun D _ => ?_
        rw [sum_prod_mul_indicator_mul_prod_sign w σ edge m hm D (S D) (hS D)]
    _ = ∑ t : ι → α, (∏ i, w (t i)) * (f (edgeSet edge t) * m ^ (S (edgeSet edge t)).card) := by
        simp_rw [hsplit (fun D t => (∏ i, w (t i)) * (f D * m ^ (S D).card)) _, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun D _ => Finset.sum_congr rfl fun t _ => by ring

/-- **The sign symmetry, as a bound.** If the factor `f` has absolute value at most `1` on an
event `E` of the edge set and vanishes off `E`, and `|S(D)| = 2` on `E`, then for nonnegative
weights the test averages to at most `m² · Pr[E]` in absolute value. -/
theorem abs_sum_prod_mul_prod_sign_le (m : ℝ)
    (hm : ∑ a with edge a, w a * σ a = m * ∑ a with edge a, w a) (hw : ∀ a, 0 ≤ w a)
    (E : Finset ι → Prop) [DecidablePred E] (f : Finset ι → ℝ)
    (hf : ∀ D, |f D| ≤ if E D then 1 else 0) (S : Finset ι → Finset ι) (hS : ∀ D, S D ⊆ D)
    (hS2 : ∀ D, E D → (S D).card = 2) :
    |∑ t : ι → α, (∏ i, w (t i)) * (f (edgeSet edge t) * ∏ i ∈ S (edgeSet edge t), σ (t i))| ≤
      m ^ 2 * ∑ t : ι → α, (∏ i, w (t i)) * (if E (edgeSet edge t) then 1 else 0) := by
  rw [sum_prod_mul_prod_sign_eq w σ edge m hm f S hS, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => ?_)
  have hW : 0 ≤ ∏ i, w (t i) := Finset.prod_nonneg fun i _ => hw (t i)
  rw [abs_mul, abs_mul, abs_of_nonneg hW, abs_pow]
  have hfD := hf (edgeSet edge t)
  by_cases hE : E (edgeSet edge t)
  · simp only [hE, ↓reduceIte] at hfD ⊢
    rw [hS2 _ hE, sq_abs]
    have hle : |f (edgeSet edge t)| * m ^ 2 ≤ m ^ 2 := mul_le_of_le_one_left (sq_nonneg m) hfD
    calc (∏ i, w (t i)) * (|f (edgeSet edge t)| * m ^ 2) ≤ (∏ i, w (t i)) * m ^ 2 :=
          mul_le_mul_of_nonneg_left hle hW
      _ = m ^ 2 * ((∏ i, w (t i)) * 1) := by ring
  · simp only [hE, ↓reduceIte] at hfD ⊢
    have h0 : |f (edgeSet edge t)| = 0 := le_antisymm hfD (abs_nonneg _)
    simp [h0]

end SignSymmetry
