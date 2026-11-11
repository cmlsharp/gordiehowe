-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.PMFOracleLoop

public section

/-!
# A fresh attempt with a keep factor

The signer's attempt with a fresh challenge (`freshAttempt`), extended by fresh side data `z` and
an extra keep factor `g (v, c, z) ∈ [0, 1]` that reads the commitment `v`, the challenge `c` and
`z` (`freshAttemptWith`): draw `y ← P`, a uniform `(c, z)`, reject unless `acc y c`, and keep
`(w1 y, c, z)` with probability `κ (w1 y, c) · g (w1 y, c, z)`.

* `freshAttemptWith_apply_some`: it keeps `(v, c, z)` with probability
  `Pr_y[w1 y = v ∧ acc y c] · |C × Z|⁻¹ · κ (v, c) · g (v, c, z)`.
* `map_freshAttemptWith_unit`: with no side data and `g = 1` it is `freshAttempt`.
* `map_equiv_apply`, `condSomeOr_map_optionMap`: conditioning on acceptance commutes with
  relabelling the accepted values by an equivalence.

About Mathlib objects only.
-/

open Finset
open scoped ENNReal BigOperators

namespace PMF

variable {Y V C Z : Type*} [Fintype Y] [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  [Nonempty C] [Fintype Z] [DecidableEq Z] [Nonempty Z] (P : PMF Y) (w1 : Y → V)
  (acc : Y → C → Bool) (κ : V × C → ℝ≥0∞) (hκ : ∀ a, κ a ≤ 1) (g : V × C × Z → ℝ≥0∞)
  (hg : ∀ a, g a ≤ 1)

/-- **The fresh attempt with side data and a keep factor**: `y ← P`, a uniform `(c, z)`, and keep
`(w1 y, c, z)` with probability `κ (w1 y, c) · g (w1 y, c, z)` if `acc y c`. -/
noncomputable def freshAttemptWith : PMF (Option (V × C × Z)) :=
  P.bind fun y => (uniformOfFintype (C × Z)).bind fun cz =>
    if acc y cz.1 = true then
      keepOrReject (w1 y, cz) (κ (w1 y, cz.1) * g (w1 y, cz)) (mul_le_one' (hκ _) (hg _))
    else pure none

/-- The fresh attempt with a keep factor keeps `(v, c, z)` with probability
`signerMass v c · |C × Z|⁻¹ · κ (v, c) · g (v, c, z)`. -/
theorem freshAttemptWith_apply_some (v : V) (c : C) (z : Z) :
    freshAttemptWith P w1 acc κ hκ g hg (some (v, c, z)) =
      signerMass P w1 acc v c * (Fintype.card (C × Z) : ℝ≥0∞)⁻¹ * (κ (v, c) * g (v, c, z)) := by
  rw [freshAttemptWith, bind_apply, tsum_fintype, signerMass, sum_mul, sum_mul]
  refine sum_congr rfl fun y _ => ?_
  rw [bind_apply, tsum_fintype, sum_eq_single (c, z) (fun cz _ hcz => by
    split_ifs
    · rw [keepOrReject_apply_some, ite_eq_right fun h => hcz (Prod.ext_iff.1 h).2.symm, mul_zero]
    · simp) (by simp), uniformOfFintype_apply]
  by_cases hv : w1 y = v
  · subst hv
    by_cases ha : acc y c = true <;> simp [ha, keepOrReject_apply_some]
    ring
  · by_cases ha : acc y c = true <;> simp [ha, hv, keepOrReject_apply_some, Ne.symm hv]

section Relabel

variable {α β : Type*} [Fintype α] [Fintype β]

omit [Fintype α] [Fintype β] in
/-- The image of a law under an equivalence, at a point. -/
theorem map_equiv_apply (e : α ≃ β) (q : PMF α) (b : β) : q.map e b = q (e.symm b) := by
  classical
  rw [map_apply, tsum_eq_single (e.symm b) fun a ha => ite_eq_right fun h =>
    ha (by rw [h, Equiv.symm_apply_apply])]
  simp

/-- **Conditioning commutes with relabelling** by an equivalence: the attempt with its accepted
values relabelled, conditioned on acceptance with the relabelled default, is the conditioned
attempt relabelled. -/
theorem condSomeOr_map_optionMap (e : α ≃ β) (A : PMF (Option α)) (d : PMF α) :
    condSomeOr (A.map (Option.map e)) (d.map e) = (condSomeOr A d).map e := by
  classical
  let e' : Option α ≃ Option β := Equiv.optionCongr e
  have hnone : A.map (Option.map e) none = A none := by
    rw [show (Option.map e : Option α → Option β) = e' from rfl, map_equiv_apply]
    rfl
  by_cases h : A none = 1
  · rw [condSomeOr, dite_eq_left (hnone.trans h), condSomeOr, dite_eq_left h]
  · rw [condSomeOr_of_ne _ (hnone ▸ h), condSomeOr_of_ne _ h]
    ext b
    rw [condSome_apply, map_equiv_apply, condSome_apply, hnone,
      show (Option.map e : Option α → Option β) = e' from rfl, map_equiv_apply]
    rfl

end Relabel

section Unit

variable {Y V C : Type*} [Fintype Y] [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  [Nonempty C] (P : PMF Y) (w1 : Y → V) (acc : Y → C → Bool) (κ : V × C → ℝ≥0∞)
  (hκ : ∀ a, κ a ≤ 1)

/-- Dropping trivial side data. -/
def dropUnitEquiv (V C : Type*) : V × C × Unit ≃ V × C where
  toFun a := (a.1, a.2.1)
  invFun a := (a.1, a.2, ())
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] [Nonempty C] in
@[simp]
theorem dropUnitEquiv_apply (a : V × C × Unit) : dropUnitEquiv V C a = (a.1, a.2.1) := by
  unfold dropUnitEquiv
  rfl

omit [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] [Nonempty C] in
@[simp]
theorem dropUnitEquiv_symm_apply (a : V × C) : (dropUnitEquiv V C).symm a = (a.1, a.2, ()) := by
  unfold dropUnitEquiv
  rfl

/-- **With no side data and the unit factor**, the fresh attempt with a keep factor is the fresh
attempt, up to dropping the side data. -/
theorem map_freshAttemptWith_unit :
    (freshAttemptWith P w1 acc κ hκ (Z := Unit) (fun _ => 1) fun _ => le_rfl).map
        (Option.map (dropUnitEquiv V C)) = freshAttempt P w1 acc κ hκ := by
  classical
  have hsome : ∀ a : V × C, (freshAttemptWith P w1 acc κ hκ (Z := Unit) (fun _ => 1)
      fun _ => le_rfl).map (Option.map (dropUnitEquiv V C)) (some a) =
        freshAttempt P w1 acc κ hκ (some a) := fun a => by
    rw [show (Option.map (dropUnitEquiv V C) : Option (V × C × Unit) → Option (V × C)) =
      Equiv.optionCongr (dropUnitEquiv V C) from rfl, map_equiv_apply]
    obtain ⟨v, c⟩ := a
    change freshAttemptWith P w1 acc κ hκ (fun _ => 1) _ (some (v, c, ())) = _
    rw [freshAttemptWith_apply_some, freshAttempt_apply_some, mul_one, Fintype.card_prod,
      Fintype.card_unit, mul_one]
  ext o
  cases o with
  | some a => exact hsome a
  | none =>
    rw [apply_none_eq_one_sub, apply_none_eq_one_sub]
    congr 1
    exact sum_congr rfl fun a _ => hsome a

end Unit

end PMF
