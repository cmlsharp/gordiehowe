-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Pure states, basis permutations and coordinate measurements

The state space of a quantum system whose computational basis is a finite type `ι` is
`QState ι = EuclideanSpace ℂ ι`, the functions `ι → ℂ` with the `L²` norm. A pure state is a
unit vector, and `v i` is its amplitude on the basis state `|i⟩`.

- `permOp π` is the unitary that maps `|i⟩` to `|π i⟩` for a permutation `π` of the basis.
  Oracles of a quantum oracle algorithm are of this form (`GordieHowe/Model/Quantum/Core/Oracle.lean`).
- `mask A` is the orthogonal projection onto the span of the basis states in a set `A`: it keeps
  the coordinates in `A` and sets the others to `0`.
- `prob A v = ‖mask A v‖ ^ 2` is the Born probability that measuring `v` in the computational
  basis gives an outcome in `A`. `prob_preimage` says that measuring a function `g` of the
  outcome and testing `g i ∈ B` gives the same probability, as a sum over the values in `B`;
  `sum_prob_fiber` says the probabilities of all values sum to the squared norm.

Everything here is about Mathlib objects only.
-/

open Finset
open scoped BigOperators InnerProductSpace

namespace GordieHowe.Quantum

variable {ι : Type*} [Fintype ι]

/-- The state space of a quantum system with computational basis `ι`. -/
abbrev QState (ι : Type*) [Fintype ι] := EuclideanSpace ℂ ι

/-! ### Basis permutations -/

/-- The unitary that maps the basis state `|i⟩` to `|π i⟩`. -/
noncomputable def permOp (π : Equiv.Perm ι) : QState ι ≃ₗᵢ[ℂ] QState ι :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ π

@[simp]
theorem permOp_apply (π : Equiv.Perm ι) (v : QState ι) (i : ι) :
    permOp π v i = v (π.symm i) :=
  rfl

/-! ### Coordinate masks -/

/-- The orthogonal projection onto the span of the basis states in `A`: it keeps the
coordinates in `A` and sets the others to `0`. -/
noncomputable def mask (A : Set ι) : QState ι →L[ℂ] QState ι :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (A.indicator fun i => v i)
      map_add' := fun v w => by
        ext i
        by_cases h : i ∈ A <;> simp [h]
      map_smul' := fun c v => by
        ext i
        by_cases h : i ∈ A <;> simp [h] }

theorem mask_apply (A : Set ι) (v : QState ι) (i : ι) :
    mask A v i = A.indicator (fun i => v i) i :=
  rfl

@[simp]
theorem mask_apply_of_mem {A : Set ι} (v : QState ι) {i : ι} (h : i ∈ A) : mask A v i = v i := by
  simp [mask_apply, h]

@[simp]
theorem mask_apply_of_notMem {A : Set ι} (v : QState ι) {i : ι} (h : i ∉ A) :
    mask A v i = 0 := by
  simp [mask_apply, h]

/-- A mask is idempotent. -/
@[simp]
theorem mask_mask (A : Set ι) (v : QState ι) : mask A (mask A v) = mask A v := by
  ext i
  by_cases h : i ∈ A <;> simp [h]

/-- A mask is self-adjoint. -/
theorem inner_mask_left (A : Set ι) (v w : QState ι) : ⟪mask A v, w⟫_ℂ = ⟪v, mask A w⟫_ℂ := by
  simp only [PiLp.inner_apply]
  refine sum_congr rfl fun i _ => ?_
  by_cases h : i ∈ A <;> simp [h]

/-- The masks of a set and of its complement add up to the identity. -/
theorem mask_add_mask_compl (A : Set ι) (v : QState ι) : mask A v + mask Aᶜ v = v := by
  ext i
  by_cases h : i ∈ A <;> simp [h]

/-- The squared norm of a mask is the sum of the squared amplitudes in the set. -/
theorem norm_mask_sq (A : Set ι) [DecidablePred (· ∈ A)] (v : QState ι) :
    ‖mask A v‖ ^ 2 = ∑ i with i ∈ A, ‖v i‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, sum_filter]
  refine sum_congr rfl fun i _ => ?_
  by_cases h : i ∈ A <;> simp [h]

/-- The squared norm splits into the squared norms of the masks of a set and of its
complement. -/
theorem norm_sq_eq_norm_mask_sq_add (A : Set ι) (v : QState ι) :
    ‖v‖ ^ 2 = ‖mask A v‖ ^ 2 + ‖mask Aᶜ v‖ ^ 2 := by
  classical
  rw [norm_mask_sq, norm_mask_sq, EuclideanSpace.norm_sq_eq]
  simp only [Set.mem_compl_iff]
  exact (sum_filter_add_sum_filter_not _ _ _).symm

theorem norm_mask_le (A : Set ι) (v : QState ι) : ‖mask A v‖ ≤ ‖v‖ := by
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [norm_sq_eq_norm_mask_sq_add A v]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- Two permutations that agree on every basis state outside `A` act equally on vectors
supported outside `A`. -/
theorem permOp_mask_compl {A : Set ι} {π π' : Equiv.Perm ι} (h : ∀ i ∉ A, π i = π' i)
    (v : QState ι) : permOp π (mask Aᶜ v) = permOp π' (mask Aᶜ v) := by
  have key : ∀ {σ τ : Equiv.Perm ι}, (∀ i ∉ A, σ i = τ i) → ∀ j, σ.symm j ∉ A →
      τ.symm j = σ.symm j := fun {σ τ} h j hj => by
    rw [Equiv.symm_apply_eq, ← h _ hj, Equiv.apply_symm_apply]
  ext j
  simp only [permOp_apply]
  by_cases h1 : π.symm j ∈ A
  · by_cases h2 : π'.symm j ∈ A
    · simp [h1, h2]
    · rw [key (fun i hi => (h i hi).symm) j h2] at h1
      exact absurd h1 h2
  · rw [key h j h1]

/-! ### Born probabilities -/

/-- The Born probability that measuring `v` in the computational basis gives an outcome in
`A`. For a unit vector `v` this is a probability. -/
noncomputable def prob (A : Set ι) (v : QState ι) : ℝ :=
  ‖mask A v‖ ^ 2

theorem prob_nonneg (A : Set ι) (v : QState ι) : 0 ≤ prob A v :=
  sq_nonneg _

theorem sqrt_prob (A : Set ι) (v : QState ι) : √(prob A v) = ‖mask A v‖ :=
  Real.sqrt_sq (norm_nonneg _)

/-- The probability of every outcome is the squared norm. -/
@[simp]
theorem prob_univ (v : QState ι) : prob Set.univ v = ‖v‖ ^ 2 := by
  have h : mask Set.univ v = v := by
    ext i
    simp
  rw [prob, h]

/-- Measuring the computational basis and then testing whether a function `g` of the outcome
lies in `B` has the probability of the event `g ⁻¹' B`, which is the sum over the values
`k ∈ B` of the probability that `g` of the outcome equals `k`. -/
theorem prob_preimage {κ : Type*} [Fintype κ] (g : ι → κ) (B : Set κ) [DecidablePred (· ∈ B)]
    (v : QState ι) : prob (g ⁻¹' B) v = ∑ k with k ∈ B, prob (g ⁻¹' {k}) v := by
  classical
  simp only [prob, norm_mask_sq, Set.mem_preimage, Set.mem_singleton_iff]
  rw [← sum_fiberwise_of_maps_to (s := univ.filter fun i => g i ∈ B) (t := univ.filter (· ∈ B))
    (g := g) (by simp)]
  refine sum_congr rfl fun k hk => ?_
  rw [filter_filter]
  refine sum_congr (filter_congr fun i _ => ?_) fun _ _ => rfl
  rw [mem_filter] at hk
  constructor
  · exact fun h => h.2
  · rintro rfl
    exact ⟨hk.2, rfl⟩

/-- The probabilities of the values of a function `g` of the outcome sum to the squared norm. -/
theorem sum_prob_fiber {κ : Type*} [Fintype κ] (g : ι → κ) (v : QState ι) :
    ∑ k, prob (g ⁻¹' {k}) v = ‖v‖ ^ 2 := by
  classical
  have h := prob_preimage g Set.univ v
  rw [Set.preimage_univ, prob_univ] at h
  rw [h]
  simp

end GordieHowe.Quantum
