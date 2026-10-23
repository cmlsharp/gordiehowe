-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Core.State

@[expose] public section

/-!
# The hybrid argument for oracles that are basis permutations

An alternating run applies a unitary, then an oracle, then a unitary, and so on. Replacing
every oracle by another one changes the final state by at most the sum, over the oracle steps,
of how much the two oracles differ on the state just before that step (`norm_hybrid_sub_le`).

When the oracles are basis permutations `π k` and `π' k` that agree on every basis state
outside a set `A k`, the difference at step `k` is at most `2 * ‖mask (A k) v‖`
(`norm_permOp_sub_le`), so the final states differ by at most
`2 * ∑ k, ‖mask (A k) (state before step k)‖` (`norm_hybrid_permOp_sub_le`).

This is the pure-state core of AHU19 Lemma 8 (Ambainis, Hamburg, Unruh, "Quantum security
proofs using semi-classical oracles", CRYPTO 2019, ePrint 2018/904, pp. 26–27: the inequality
`√D_i ≤ √D_{i-1} + 2 √B_i`, with `(O_H - O_G) P_S = O_H - O_G` the step marked `(∗∗∗)`), in the
fixed-permutation form of Jaeger, Song and Tessaro (ePrint 2021/579, Theorem 1). Here the
triangle inequality replaces AHU's expansion of the squared norm.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

variable {ι : Type*} [Fintype ι]

/-- Two basis permutations that agree outside `A` differ on `v` by at most twice the norm of
the part of `v` inside `A`. -/
theorem norm_permOp_sub_le {A : Set ι} {π π' : Equiv.Perm ι} (h : ∀ i ∉ A, π i = π' i)
    (v : QState ι) : ‖permOp π v - permOp π' v‖ ≤ 2 * ‖mask A v‖ := by
  have hv : permOp π v - permOp π' v = permOp π (mask A v) - permOp π' (mask A v) := by
    conv_lhs => rw [← mask_add_mask_compl A v]
    rw [map_add, map_add, permOp_mask_compl h]
    abel
  rw [hv, two_mul]
  refine (norm_sub_le _ _).trans ?_
  rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]

/-- The alternating run `U 0`, `O 0`, `U 1`, `O 1`, … from `ψ`: `hybrid U O ψ k` is the state
after `U k`, that is, just before the oracle step `O k`. -/
def hybrid (U O : ℕ → QState ι ≃ₗᵢ[ℂ] QState ι) (ψ : QState ι) : ℕ → QState ι
  | 0 => U 0 ψ
  | k + 1 => U (k + 1) (O k (hybrid U O ψ k))

@[simp]
theorem hybrid_zero (U O : ℕ → QState ι ≃ₗᵢ[ℂ] QState ι) (ψ : QState ι) :
    hybrid U O ψ 0 = U 0 ψ :=
  rfl

theorem hybrid_succ (U O : ℕ → QState ι ≃ₗᵢ[ℂ] QState ι) (ψ : QState ι) (k : ℕ) :
    hybrid U O ψ (k + 1) = U (k + 1) (O k (hybrid U O ψ k)) :=
  rfl

/-- The run up to step `n` depends only on the unitaries `U 0, …, U n`. -/
theorem hybrid_congr_le {U U' : ℕ → QState ι ≃ₗᵢ[ℂ] QState ι} (O : ℕ → QState ι ≃ₗᵢ[ℂ] QState ι)
    (ψ : QState ι) (n : ℕ) (h : ∀ i ≤ n, U i = U' i) : hybrid U O ψ n = hybrid U' O ψ n := by
  induction n with
  | zero => rw [hybrid_zero, hybrid_zero, h 0 le_rfl]
  | succ n ih =>
    rw [hybrid_succ, hybrid_succ, ih fun i hi => h i (hi.trans n.le_succ), h (n + 1) le_rfl]

/-- An alternating run of unitaries preserves the norm. -/
@[simp]
theorem norm_hybrid (U O : ℕ → QState ι ≃ₗᵢ[ℂ] QState ι) (ψ : QState ι) (k : ℕ) :
    ‖hybrid U O ψ k‖ = ‖ψ‖ := by
  induction k with
  | zero => simp
  | succ k ih => simp [hybrid_succ, ih]

/-- **Hybrid argument.** Replacing the oracles `O` by `O'` moves the state after `k` oracle
steps by at most the sum of `‖O i v_i - O' i v_i‖`, where `v_i` is the state just before
oracle step `i` in the run with `O`. -/
theorem norm_hybrid_sub_le (U O O' : ℕ → QState ι ≃ₗᵢ[ℂ] QState ι) (ψ : QState ι) (k : ℕ) :
    ‖hybrid U O ψ k - hybrid U O' ψ k‖ ≤
      ∑ i ∈ range k, ‖O i (hybrid U O ψ i) - O' i (hybrid U O ψ i)‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [hybrid_succ, hybrid_succ, ← map_sub, LinearIsometryEquiv.norm_map, sum_range_succ,
      add_comm]
    calc ‖O k (hybrid U O ψ k) - O' k (hybrid U O' ψ k)‖
        ≤ ‖O k (hybrid U O ψ k) - O' k (hybrid U O ψ k)‖ +
            ‖O' k (hybrid U O ψ k) - O' k (hybrid U O' ψ k)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by
        rw [← map_sub, LinearIsometryEquiv.norm_map]
        exact add_le_add_right ih _

/-- **Hybrid argument for basis-permutation oracles** (AHU19 Lemma 8, pure-state core). If the
oracle permutations `π k` and `π' k` agree on every basis state outside `A k`, the states after
`k` oracle steps differ by at most `2 * ∑ i < k, ‖mask (A i) v_i‖`, where `v_i` is the state
just before oracle step `i` in the run with `π`. -/
theorem norm_hybrid_permOp_sub_le (U : ℕ → QState ι ≃ₗᵢ[ℂ] QState ι) {π π' : ℕ → Equiv.Perm ι}
    {A : ℕ → Set ι} (h : ∀ k, ∀ i ∉ A k, π k i = π' k i) (ψ : QState ι) (k : ℕ) :
    ‖hybrid U (fun j => permOp (π j)) ψ k - hybrid U (fun j => permOp (π' j)) ψ k‖ ≤
      2 * ∑ i ∈ range k, ‖mask (A i) (hybrid U (fun j => permOp (π j)) ψ i)‖ := by
  refine (norm_hybrid_sub_le _ _ _ ψ k).trans ?_
  rw [mul_sum]
  exact sum_le_sum fun i _ => norm_permOp_sub_le (h i) _

end GordieHowe.Quantum
