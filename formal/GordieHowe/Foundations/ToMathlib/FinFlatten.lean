-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.SetLike.Basic

@[expose] public section

/-!
# Flattening a `Fin m → Fin n → α` matrix along `finProdFinEquiv`

The row-major flattening used by the A input layouts: entry `(i, j)` sits at
`finProdFinEquiv (i, j)`, whose value is `j + n * i`. Candidate for upstreaming next to
`finProdFinEquiv`. `append_mem` and `flatten_mem`: every entry lies in a set-like object when
every block does (used for subfield-valued vectors).
-/

namespace Fin

/-- Row-major flattening: entry `(i, j)` of `v` at `finProdFinEquiv (i, j)`. -/
def flatten {α : Type*} {m n : ℕ} (v : Fin m → Fin n → α) : Fin (m * n) → α :=
  Function.uncurry v ∘ finProdFinEquiv.symm

@[simp] theorem flatten_apply {α : Type*} {m n : ℕ} (v : Fin m → Fin n → α) (i : Fin m)
    (j : Fin n) : flatten v (finProdFinEquiv (i, j)) = v i j := by
  simp [flatten]

/-! ### Membership of the blocks in a set-like object -/

section SetLike

variable {α σ : Type*} [SetLike σ α] {s : σ}

/-- Every entry of `append u v` lies in `s` when every entry of `u` and of `v` does. -/
theorem append_mem {m n : ℕ} {u : Fin m → α} {v : Fin n → α} (hu : ∀ i, u i ∈ s)
    (hv : ∀ i, v i ∈ s) (i : Fin (m + n)) : append u v i ∈ s := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [append_left]
    exact hu i
  · rw [append_right]
    exact hv i

/-- Every entry of `flatten v` lies in `s` when every entry of `v` does. -/
theorem flatten_mem {m n : ℕ} {v : Fin m → Fin n → α} (h : ∀ i j, v i j ∈ s)
    (k : Fin (m * n)) : flatten v k ∈ s := by
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
  rw [flatten_apply]
  exact h i j

end SetLike

end Fin
