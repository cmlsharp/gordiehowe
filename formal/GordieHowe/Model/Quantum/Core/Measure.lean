-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Core.State

@[expose] public section

/-!
# Close states give close measurement probabilities

For a coordinate measurement with outcome set `A` and two states `ψ`, `φ`:

- `abs_sqrt_prob_sub_le`: `|√(prob A ψ) - √(prob A φ)| ≤ ‖ψ - φ‖`;
- `abs_prob_sub_le`: `|prob A ψ - prob A φ| ≤ ‖ψ - φ‖` when `ψ` and `φ` are unit vectors.

The second uses the reflection `reflect A = mask A - mask Aᶜ`, a self-adjoint unitary:
`2 * (prob A ψ - prob A φ) = re ⟪ψ - φ, reflect A (ψ + φ)⟫` for unit vectors, and
`‖ψ + φ‖ ≤ 2`. These two lemmas replace AHU19 Lemmas 3–4 (fidelity and Bures distance;
ePrint 2018/904, p. 28) in the proof of AHU19 Theorem 3, since the model has pure states only.
-/

open Finset RCLike
open scoped BigOperators InnerProductSpace

namespace GordieHowe.Quantum

variable {ι : Type*} [Fintype ι]

/-- The reflection that negates the coordinates outside `A`. -/
noncomputable def reflect (A : Set ι) : QState ι →L[ℂ] QState ι :=
  mask A - mask Aᶜ

theorem reflect_apply (A : Set ι) (v : QState ι) : reflect A v = mask A v - mask Aᶜ v :=
  rfl

/-- The reflection preserves the norm. -/
@[simp]
theorem norm_reflect (A : Set ι) (v : QState ι) : ‖reflect A v‖ = ‖v‖ := by
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  refine sum_congr rfl fun i _ => ?_
  by_cases h : i ∈ A <;> simp [reflect_apply, h]

/-- The reflection is self-adjoint. -/
theorem inner_reflect_left (A : Set ι) (v w : QState ι) :
    ⟪reflect A v, w⟫_ℂ = ⟪v, reflect A w⟫_ℂ := by
  rw [reflect_apply, reflect_apply, inner_sub_left, inner_sub_right, inner_mask_left,
    inner_mask_left]

/-- The expectation of the reflection is `‖mask A v‖ ^ 2 - ‖mask Aᶜ v‖ ^ 2`. -/
theorem re_inner_reflect (A : Set ι) (v : QState ι) :
    re ⟪v, reflect A v⟫_ℂ = ‖mask A v‖ ^ 2 - ‖mask Aᶜ v‖ ^ 2 := by
  have hM : ∀ B : Set ι, re ⟪v, mask B v⟫_ℂ = ‖mask B v‖ ^ 2 := fun B => by
    rw [← mask_mask B v, ← inner_mask_left, mask_mask, inner_self_eq_norm_sq]
  rw [reflect_apply, inner_sub_right, map_sub, hM, hM]

/-- Close states have close square roots of measurement probabilities. -/
theorem abs_sqrt_prob_sub_le (A : Set ι) (ψ φ : QState ι) :
    |√(prob A ψ) - √(prob A φ)| ≤ ‖ψ - φ‖ := by
  rw [sqrt_prob, sqrt_prob]
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [← map_sub]
  exact norm_mask_le A _

/-- Close unit vectors have close measurement probabilities. -/
theorem abs_prob_sub_le (A : Set ι) {ψ φ : QState ι} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    |prob A ψ - prob A φ| ≤ ‖ψ - φ‖ := by
  have hp : ∀ v : QState ι, ‖v‖ = 1 → re ⟪v, reflect A v⟫_ℂ = 2 * prob A v - 1 := fun v hv => by
    have := norm_sq_eq_norm_mask_sq_add A v
    rw [hv, one_pow] at this
    rw [re_inner_reflect, prob]
    linarith
  have hcross : re ⟪ψ, reflect A φ⟫_ℂ = re ⟪φ, reflect A ψ⟫_ℂ := by
    rw [← inner_reflect_left, ← inner_conj_symm, conj_re]
  have key : 2 * (prob A ψ - prob A φ) = re ⟪ψ - φ, reflect A (ψ + φ)⟫_ℂ := by
    rw [map_add, inner_sub_left, inner_add_right, inner_add_right, map_sub, map_add, map_add,
      hp ψ hψ, hp φ hφ, hcross]
    ring
  have hbound : |re ⟪ψ - φ, reflect A (ψ + φ)⟫_ℂ| ≤ ‖ψ - φ‖ * 2 := by
    refine (abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    rw [norm_reflect]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (norm_nonneg _)
    rw [hψ, hφ]
    norm_num
  rw [← key, abs_mul, abs_two] at hbound
  linarith

end GordieHowe.Quantum
