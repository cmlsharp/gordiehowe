-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.McDiarmid
public import GordieHowe.Foundations.ToMathlib.PMFOracleQuenched

@[expose] public section

/-!
# Hoeffding's inequality for the average of a uniform random function, and layered averages

For a uniform random function `G : X → Y` on finite types and `f : Y → [a, b]` with mean
`m = 𝔼_y f y`, the average `A(G) = 𝔼_x f (G x)` is a mean of `|X|` independent copies of `f`:

* `expect_exp_expect_sub_le`: `𝔼_G exp(θ (A(G) - m)) ≤ exp(θ² (b - a)² / (8 |X|))`, from the
  product identity `𝔼_G ∏_x φ(G x) = ∏_x 𝔼_y φ y` (`PMF.expect_prod_apply`) and Hoeffding's lemma
  (`expect_exp_sub_le_of_mem_Icc`);
* `expect_indicator_le_expect_le`: `Pr_G[A(G) ≥ m + t] ≤ exp(-2 |X| t² / (b - a)²)` for `t ≥ 0`
  (Hoeffding's inequality, W. Hoeffding, *Probability inequalities for sums of bounded random
  variables*, JASA 58 (1963), Theorem 2), with `θ = 4 |X| t / (b - a)²`.

`expect_le_add_sum_layers` bounds the average of a monotone function `φ ≥ 0` of a variable `Y` by a
grid `a 0, …, a n` with `Y ≤ a n`: `𝔼 φ(Y) ≤ φ(a 0) + ∑_{i < n} Pr[a i < Y] φ(a (i + 1))`.

The statements are about Mathlib objects only and are candidates for upstreaming.
-/

open Finset Real
open scoped BigOperators

namespace GordieHowe

section Hoeffding

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [Nonempty Y]

/-- **The moment generating function of the average of a uniform function**: for
`f : Y → [a, b]`, `𝔼_G exp(θ (𝔼_x f(G x) - 𝔼_y f y)) ≤ exp(θ² (b - a)² / (8 |X|))`. -/
theorem expect_exp_expect_sub_le (f : Y → ℝ) {a b : ℝ} (hf : ∀ y, f y ∈ Set.Icc a b) (θ : ℝ) :
    𝔼 G : X → Y, exp (θ * (𝔼 x, f (G x) - 𝔼 y, f y)) ≤
      exp (θ ^ 2 * (b - a) ^ 2 / (8 * Fintype.card X)) := by
  set N : ℝ := (Fintype.card X : ℝ) with hNdef
  set m := 𝔼 y, f y
  have hN : 0 < N := by rw [hNdef]; exact_mod_cast Fintype.card_pos
  have hprod : ∀ G : X → Y, exp (θ * (𝔼 x, f (G x) - m)) =
      ∏ x, exp (θ / N * (f (G x) - m)) := fun G => by
    rw [← exp_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Fintype.expect_eq_sum_div_card]
    congr 1
    rw [← hNdef]
    field_simp
  simp_rw [hprod]
  rw [PMF.expect_prod_apply (fun _ y => exp (θ / N * (f y - m)))]
  calc ∏ _x : X, 𝔼 y, exp (θ / N * (f y - m))
      ≤ ∏ _x : X, exp ((θ / N) ^ 2 * (b - a) ^ 2 / 8) :=
        Finset.prod_le_prod₀ (fun _ _ => Finset.expect_nonneg fun _ _ => (exp_pos _).le)
          fun _ _ => expect_exp_sub_le_of_mem_Icc hf _
    _ = exp (θ ^ 2 * (b - a) ^ 2 / (8 * N)) := by
        rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul, ← hNdef]
        congr 1
        field_simp

/-- **Hoeffding's inequality for the average of a uniform function**: for `f : Y → [a, b]`,
`a < b`, and `t ≥ 0`, `Pr_G[𝔼_y f y + t ≤ 𝔼_x f(G x)] ≤ exp(-2 |X| t² / (b - a)²)`. -/
theorem expect_indicator_le_expect_le (f : Y → ℝ) {a b t : ℝ} (hf : ∀ y, f y ∈ Set.Icc a b)
    (hab : a < b) (ht : 0 ≤ t) :
    𝔼 G : X → Y, (if 𝔼 y, f y + t ≤ 𝔼 x, f (G x) then (1 : ℝ) else 0) ≤
      exp (-(2 * Fintype.card X * t ^ 2 / (b - a) ^ 2)) := by
  set N : ℝ := (Fintype.card X : ℝ) with hNdef
  set m := 𝔼 y, f y
  have hN : 0 < N := by rw [hNdef]; exact_mod_cast Fintype.card_pos
  have hH : 0 < (b - a) ^ 2 := by have := sub_pos.2 hab; positivity
  set θ := 4 * N * t / (b - a) ^ 2
  have hθ : 0 ≤ θ := by positivity
  have hpt : ∀ G : X → Y, (if m + t ≤ 𝔼 x, f (G x) then (1 : ℝ) else 0) ≤
      exp (θ * (𝔼 x, f (G x) - m)) * exp (-(θ * t)) := fun G => by
    rw [← exp_add]
    split_ifs with h
    · exact one_le_exp (by nlinarith)
    · exact (exp_pos _).le
  calc 𝔼 G : X → Y, (if m + t ≤ 𝔼 x, f (G x) then (1 : ℝ) else 0)
      ≤ 𝔼 G : X → Y, exp (θ * (𝔼 x, f (G x) - m)) * exp (-(θ * t)) :=
        Finset.expect_le_expect fun G _ => hpt G
    _ = (𝔼 G : X → Y, exp (θ * (𝔼 x, f (G x) - m))) * exp (-(θ * t)) := by
        rw [Finset.expect_mul]
    _ ≤ exp (θ ^ 2 * (b - a) ^ 2 / (8 * N)) * exp (-(θ * t)) := by
        gcongr
        exact expect_exp_expect_sub_le f hf θ
    _ = exp (-(2 * N * t ^ 2 / (b - a) ^ 2)) := by
        rw [← exp_add]
        congr 1
        simp only [θ]
        field_simp
        ring

end Hoeffding

section Layers

variable {Ω : Type*} [Fintype Ω]

/-- **An average by layers**: for a monotone `φ ≥ 0`, a grid `a 0, …, a n` and `Y ≤ a n`,
`𝔼 φ(Y) ≤ φ(a 0) + ∑_{i < n} Pr[a i < Y] · φ(a (i + 1))`. -/
theorem expect_le_add_sum_layers [Nonempty Ω] (Y : Ω → ℝ) {φ : ℝ → ℝ} (hφ : Monotone φ)
    (hφ0 : ∀ y, 0 ≤ φ y) (a : ℕ → ℝ) (n : ℕ) (hY : ∀ ω, Y ω ≤ a n) :
    𝔼 ω, φ (Y ω) ≤ φ (a 0) + ∑ i ∈ range n,
      (𝔼 ω, if a i < Y ω then (1 : ℝ) else 0) * φ (a (i + 1)) := by
  classical
  have hpt : ∀ ω, φ (Y ω) ≤ φ (a 0) + ∑ i ∈ range n,
      (if a i < Y ω then (1 : ℝ) else 0) * φ (a (i + 1)) := fun ω => by
    have hex : ∃ j, Y ω ≤ a j := ⟨n, hY ω⟩
    have hjn : Nat.find hex ≤ n := Nat.find_min' hex (hY ω)
    have hnn : 0 ≤ ∑ i ∈ range n, (if a i < Y ω then (1 : ℝ) else 0) * φ (a (i + 1)) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (by split_ifs <;> norm_num) (hφ0 _)
    rcases hj : Nat.find hex with _ | i
    · have h0 := Nat.find_spec hex
      rw [hj] at h0
      linarith [hφ h0]
    · have hi1 := Nat.find_spec hex
      rw [hj] at hi1 hjn
      have hi : a i < Y ω := by
        have := Nat.find_min hex (show i < Nat.find hex by omega)
        exact lt_of_not_ge this
      have hmem : i ∈ range n := Finset.mem_range.2 (by omega)
      have hsingle := Finset.single_le_sum (f := fun i =>
        (if a i < Y ω then (1 : ℝ) else 0) * φ (a (i + 1)))
        (fun j _ => mul_nonneg (by split_ifs <;> norm_num) (hφ0 _)) hmem
      rw [ite_eq_left hi, one_mul] at hsingle
      linarith [hφ hi1, hφ0 (a 0)]
  calc 𝔼 ω, φ (Y ω) ≤ 𝔼 ω, (φ (a 0) + ∑ i ∈ range n,
        (if a i < Y ω then (1 : ℝ) else 0) * φ (a (i + 1))) :=
        Finset.expect_le_expect fun ω _ => hpt ω
    _ = _ := by
        rw [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty,
          Finset.expect_sum_comm]
        simp_rw [Finset.expect_mul]

end Layers

end GordieHowe
