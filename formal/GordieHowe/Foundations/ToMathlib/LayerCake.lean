-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.Order.BigOperators.Expect

@[expose] public section

/-!
# Layer-cake and inclusion-probability bounds for finite expectations

Expectations are uniform averages `𝔼 ω, _` over a nonempty finite type.

- **Layer cake.** A monotone function of a bounded random variable, bounded through tail
  probabilities on a grid, each tail by Chernoff's bound: for monotone `f` and a monotone grid
  `a 0 ≤ a 1 ≤ … ≤ a N` with `X ≤ a N`,
  `𝔼 f X ≤ f (a 0) + ∑ i < N, (f (a (i+1)) - f (a i)) · P[a i < X]`
  (`expect_le_layers`); with upper bounds `f (a i) ≤ U i` at the grid points in place of the
  values, `U 0 + ∑ i < N, (U (i+1) - U i) · P[a i < X]` (`expect_le_layers_of_le`); and
  `P[a < X] ≤ exp (-λ a) · 𝔼 exp (λ X)` for `λ ≥ 0`
  (`expect_indicator_lt_le_exp_mul_expect_exp`), combined in `expect_le_layers_exp`. Pointwise,
  `y ≤ U 0 + ∑ i < N, (U (i+1) - U i) · [a i < x]` whenever `x ≤ a i` implies `y ≤ U i`
  (`le_add_sum_layers_of_imp`); on an event `E`, for a double average,
  `𝔼 𝔼 [E] · (U 0 + ∑ …) ≤ U 0 · P[E] + ∑ i < N, (U (i+1) - U i) · P[E, a i < X]`
  (`expect_expect_indicator_mul_layers_le`).
- **Random sets.** The expectation of `(1 + x) ^ |Z|` from inclusion probabilities: if every
  `D` lies inside the random set `Z` with probability at most `p ^ |D|`, then
  `𝔼 (1 + x) ^ |Z| ≤ (1 + x p) ^ |ι|` for `x ≥ 0` (`expect_one_add_pow_card_le`), and
  `P[d₀ ≤ |Z|] ≤ (|ι| choose d₀) p ^ d₀` (`expect_indicator_le_card_le_choose_mul_pow`).
-/

open Finset
open scoped BigOperators

namespace GordieHowe

/-- Pointwise layer cake: a monotone `f` at `x ≤ a N` is at most `f (a 0)` plus the increments
of `f` along the monotone grid `a` over the grid points strictly below `x`. -/
theorem le_add_sum_layers {f : ℝ → ℝ} (hf : Monotone f) {a : ℕ → ℝ} (ha : Monotone a)
    {N : ℕ} {x : ℝ} (hx : x ≤ a N) :
    f x ≤ f (a 0) + ∑ i ∈ range N, (f (a (i + 1)) - f (a i)) * (if a i < x then 1 else 0) := by
  induction N with
  | zero => simpa using hf hx
  | succ N ih =>
    by_cases hN : x ≤ a N
    · rw [sum_range_succ]
      have hinc : 0 ≤ f (a (N + 1)) - f (a N) := sub_nonneg.2 (hf (ha (Nat.le_succ N)))
      have hterm : 0 ≤ (f (a (N + 1)) - f (a N)) * (if a N < x then 1 else 0) :=
        mul_nonneg hinc (by split_ifs <;> norm_num)
      linarith [ih hN]
    · push Not at hN
      have hsum : ∑ i ∈ range (N + 1), (f (a (i + 1)) - f (a i)) * (if a i < x then 1 else 0)
          = ∑ i ∈ range (N + 1), (f (a (i + 1)) - f (a i)) := by
        refine sum_congr rfl fun i hi => ?_
        have : a i < x := lt_of_le_of_lt (ha (Nat.lt_succ_iff.1 (mem_range.1 hi))) hN
        simp [this]
      rw [hsum, sum_range_sub (fun i => f (a i))]
      linarith [hf hx]

/-- Pointwise layer cake with upper bounds at the grid points: for a monotone `f`, a grid `a`
increasing up to `a N ≥ x`, and bounds `f (a i) ≤ U i` with `U` increasing up to `N`,
`f x ≤ U 0 + ∑ i < N, (U (i + 1) - U i) · [a i < x]`. -/
theorem le_add_sum_layers_of_le {f : ℝ → ℝ} (hf : Monotone f) {a U : ℕ → ℝ} {N : ℕ}
    (ha : ∀ i < N, a i ≤ a (i + 1)) (hU : ∀ i < N, U i ≤ U (i + 1))
    (hfU : ∀ i ≤ N, f (a i) ≤ U i) {x : ℝ} (hx : x ≤ a N) :
    f x ≤ U 0 + ∑ i ∈ range N, (U (i + 1) - U i) * (if a i < x then 1 else 0) := by
  induction N with
  | zero => simpa using (hf hx).trans (hfU 0 le_rfl)
  | succ N ih =>
    have ih' := fun hxN : x ≤ a N => ih (fun i hi => ha i (by omega))
      (fun i hi => hU i (by omega)) (fun i hi => hfU i (by omega)) hxN
    by_cases hN : x ≤ a N
    · rw [sum_range_succ]
      have hterm : 0 ≤ (U (N + 1) - U N) * (if a N < x then 1 else 0) :=
        mul_nonneg (sub_nonneg.2 (hU N (by omega))) (by split_ifs <;> norm_num)
      linarith [ih' hN]
    · push Not at hN
      have hdown : ∀ j ≤ N, a (N - j) ≤ a N := by
        intro j
        induction j with
        | zero => intro; simp
        | succ j ih =>
          intro hj
          have h1 := ha (N - (j + 1)) (by omega)
          rw [show N - (j + 1) + 1 = N - j by omega] at h1
          exact h1.trans (ih (by omega))
      have hmono : ∀ i ≤ N, a i ≤ a N := fun i hi => by
        simpa [Nat.sub_sub_self hi] using hdown (N - i) (by omega)
      have hsum : ∑ i ∈ range (N + 1), (U (i + 1) - U i) * (if a i < x then 1 else 0)
          = ∑ i ∈ range (N + 1), (U (i + 1) - U i) := by
        refine sum_congr rfl fun i hi => ?_
        have : a i < x := lt_of_le_of_lt (hmono i (Nat.lt_succ_iff.1 (mem_range.1 hi))) hN
        simp [this]
      rw [hsum, sum_range_sub U]
      linarith [(hf hx).trans (hfU (N + 1) le_rfl)]

/-- Pointwise layer cake from implications: for a grid `a` increasing up to `a N ≥ x`, bounds
`U` increasing up to `N`, and `y ≤ U i` whenever `x ≤ a i`,
`y ≤ U 0 + ∑ i < N, (U (i + 1) - U i) · [a i < x]`. -/
theorem le_add_sum_layers_of_imp {a U : ℕ → ℝ} {N : ℕ} (ha : ∀ i < N, a i ≤ a (i + 1))
    (hU : ∀ i < N, U i ≤ U (i + 1)) {x y : ℝ} (hx : x ≤ a N)
    (hy : ∀ i ≤ N, x ≤ a i → y ≤ U i) :
    y ≤ U 0 + ∑ i ∈ range N, (U (i + 1) - U i) * (if a i < x then 1 else 0) := by
  induction N with
  | zero => simpa using hy 0 le_rfl hx
  | succ N ih =>
    by_cases hN : x ≤ a N
    · have ih' := ih (fun i hi => ha i (by omega)) (fun i hi => hU i (by omega)) hN
        (fun i hi => hy i (by omega))
      rw [sum_range_succ]
      have hterm : 0 ≤ (U (N + 1) - U N) * (if a N < x then 1 else 0) :=
        mul_nonneg (sub_nonneg.2 (hU N (by omega))) (by split_ifs <;> norm_num)
      linarith
    · push Not at hN
      have hdown : ∀ j ≤ N, a (N - j) ≤ a N := by
        intro j
        induction j with
        | zero => intro; simp
        | succ j ih =>
          intro hj
          have h1 := ha (N - (j + 1)) (by omega)
          rw [show N - (j + 1) + 1 = N - j by omega] at h1
          exact h1.trans (ih (by omega))
      have hmono : ∀ i ≤ N, a i ≤ a N := fun i hi => by
        simpa [Nat.sub_sub_self hi] using hdown (N - i) (by omega)
      have hsum : ∑ i ∈ range (N + 1), (U (i + 1) - U i) * (if a i < x then 1 else 0)
          = ∑ i ∈ range (N + 1), (U (i + 1) - U i) := by
        refine sum_congr rfl fun i hi => ?_
        have : a i < x := lt_of_le_of_lt (hmono i (Nat.lt_succ_iff.1 (mem_range.1 hi))) hN
        simp [this]
      rw [hsum, sum_range_sub U]
      linarith [hy (N + 1) le_rfl hx]

/-- **A layer cake on an event, for a double average**: for an event `E`, bounds `U` increasing
up to `N` with `U 0 ≥ 0`, `𝔼 𝔼 [E] ≤ P` and `𝔼 𝔼 [E ∧ a i < X] ≤ t i`,
`𝔼_x 𝔼_y [E] · (U 0 + ∑ i < N, (U (i + 1) - U i) · [a i < X]) ≤
U 0 · P + ∑ i < N, (U (i + 1) - U i) · t i`. -/
theorem expect_expect_indicator_mul_layers_le {A B : Type*} [Fintype A] [Fintype B]
    (E : A → B → Prop) [∀ x y, Decidable (E x y)] (X : A → B → ℝ) {a U t : ℕ → ℝ} {N : ℕ}
    {P : ℝ} (hU : ∀ i < N, U i ≤ U (i + 1)) (hU0 : 0 ≤ U 0)
    (hP : 𝔼 x, 𝔼 y, (if E x y then 1 else 0 : ℝ) ≤ P)
    (ht : ∀ i < N, 𝔼 x, 𝔼 y, (if E x y ∧ a i < X x y then 1 else 0 : ℝ) ≤ t i) :
    𝔼 x, 𝔼 y, (if E x y then 1 else 0 : ℝ) *
        (U 0 + ∑ i ∈ range N, (U (i + 1) - U i) * (if a i < X x y then 1 else 0)) ≤
      U 0 * P + ∑ i ∈ range N, (U (i + 1) - U i) * t i := by
  have hpt : ∀ x y, (if E x y then 1 else 0 : ℝ) *
      (U 0 + ∑ i ∈ range N, (U (i + 1) - U i) * (if a i < X x y then 1 else 0)) =
      U 0 * (if E x y then 1 else 0 : ℝ) +
        ∑ i ∈ range N, (U (i + 1) - U i) * (if E x y ∧ a i < X x y then 1 else 0 : ℝ) :=
    fun x y => by
      rw [mul_add, mul_sum, mul_comm]
      congr 1
      refine sum_congr rfl fun i _ => ?_
      by_cases h1 : E x y <;> by_cases h2 : a i < X x y <;> simp [h1, h2]
  simp_rw [hpt, expect_add_distrib, expect_sum_comm, ← mul_expect]
  refine add_le_add (mul_le_mul_of_nonneg_left hP hU0) (sum_le_sum fun i hi => ?_)
  exact mul_le_mul_of_nonneg_left (ht i (mem_range.1 hi)) (sub_nonneg.2 (hU i (mem_range.1 hi)))

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- Layer cake in expectation: for monotone `f`, a monotone grid `a` and `X ≤ a N`, the mean of
`f X` is at most `f (a 0)` plus the increments of `f` weighted by the tails `P[a i < X]`. -/
theorem expect_le_layers {f : ℝ → ℝ} (hf : Monotone f) {a : ℕ → ℝ} (ha : Monotone a)
    {N : ℕ} {X : Ω → ℝ} (hX : ∀ ω, X ω ≤ a N) :
    𝔼 ω, f (X ω) ≤ f (a 0) + ∑ i ∈ range N,
      (f (a (i + 1)) - f (a i)) * 𝔼 ω, (if a i < X ω then 1 else 0 : ℝ) := by
  calc 𝔼 ω, f (X ω)
      ≤ 𝔼 ω, (f (a 0) + ∑ i ∈ range N,
          (f (a (i + 1)) - f (a i)) * (if a i < X ω then 1 else 0 : ℝ)) :=
        expect_le_expect fun ω _ => le_add_sum_layers hf ha (hX ω)
    _ = _ := by
        rw [expect_add_distrib, expect_const univ_nonempty, expect_sum_comm]
        simp_rw [← mul_expect]

/-- Layer cake in expectation with upper bounds at the grid points
(`le_add_sum_layers_of_le`): `𝔼 f X ≤ U 0 + ∑ i < N, (U (i + 1) - U i) · P[a i < X]`. -/
theorem expect_le_layers_of_le {f : ℝ → ℝ} (hf : Monotone f) {a U : ℕ → ℝ} {N : ℕ}
    (ha : ∀ i < N, a i ≤ a (i + 1)) (hU : ∀ i < N, U i ≤ U (i + 1))
    (hfU : ∀ i ≤ N, f (a i) ≤ U i) {X : Ω → ℝ} (hX : ∀ ω, X ω ≤ a N) :
    𝔼 ω, f (X ω) ≤ U 0 + ∑ i ∈ range N,
      (U (i + 1) - U i) * 𝔼 ω, (if a i < X ω then 1 else 0 : ℝ) := by
  calc 𝔼 ω, f (X ω)
      ≤ 𝔼 ω, (U 0 + ∑ i ∈ range N,
          (U (i + 1) - U i) * (if a i < X ω then 1 else 0 : ℝ)) :=
        expect_le_expect fun ω _ => le_add_sum_layers_of_le hf ha hU hfU (hX ω)
    _ = _ := by
        rw [expect_add_distrib, expect_const univ_nonempty, expect_sum_comm]
        simp_rw [← mul_expect]

omit [Nonempty Ω] in
/-- Chernoff's bound: for `λ ≥ 0`, `P[a < X] ≤ exp (-(λ a)) · 𝔼 exp (λ X)`. -/
theorem expect_indicator_lt_le_exp_mul_expect_exp {X : Ω → ℝ} (a : ℝ) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    𝔼 ω, (if a < X ω then 1 else 0 : ℝ) ≤ Real.exp (-(lam * a)) * 𝔼 ω, Real.exp (lam * X ω) := by
  rw [mul_expect]
  refine expect_le_expect fun ω _ => ?_
  rw [← Real.exp_add]
  split_ifs with h
  · exact Real.one_le_exp (by nlinarith)
  · exact (Real.exp_pos _).le

/-- Layer cake with Chernoff tails: as `expect_le_layers`, each tail `P[a i < X]` bounded by
`exp (-(λ i · a i)) · Φ i` from a bound `Φ i` on the moment generating function at `λ i ≥ 0`. -/
theorem expect_le_layers_exp {f : ℝ → ℝ} (hf : Monotone f) {a : ℕ → ℝ} (ha : Monotone a)
    {N : ℕ} {X : Ω → ℝ} (hX : ∀ ω, X ω ≤ a N) {lam Φ : ℕ → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (hΦ : ∀ i < N, 𝔼 ω, Real.exp (lam i * X ω) ≤ Φ i) :
    𝔼 ω, f (X ω) ≤ f (a 0) + ∑ i ∈ range N,
      (f (a (i + 1)) - f (a i)) * (Real.exp (-(lam i * a i)) * Φ i) := by
  refine (expect_le_layers hf ha hX).trans (add_le_add_right (sum_le_sum fun i hi => ?_) _)
  refine mul_le_mul_of_nonneg_left ?_ (sub_nonneg.2 (hf (ha (Nat.le_succ i))))
  exact (expect_indicator_lt_le_exp_mul_expect_exp (a i) (hlam i)).trans
    (mul_le_mul_of_nonneg_left (hΦ i (mem_range.1 hi)) (Real.exp_pos _).le)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Nonempty Ω] in
/-- The expectation of `(1 + x) ^ |Z|` from inclusion probabilities: if each `D` lies inside the
random set `Z` with probability at most `p ^ |D|`, then `𝔼 (1 + x) ^ |Z| ≤ (1 + x p) ^ |ι|`. -/
theorem expect_one_add_pow_card_le {Z : Ω → Finset ι} {x p : ℝ} (hx : 0 ≤ x)
    (hZ : ∀ D : Finset ι, 𝔼 ω, (if D ⊆ Z ω then 1 else 0 : ℝ) ≤ p ^ #D) :
    𝔼 ω, (1 + x) ^ #(Z ω) ≤ (1 + x * p) ^ Fintype.card ι := by
  have hpt : ∀ ω, (1 + x) ^ #(Z ω)
      = ∑ D : Finset ι, x ^ #D * (if D ⊆ Z ω then 1 else 0 : ℝ) := by
    intro ω
    rw [add_comm, ← sum_pow_mul_eq_add_pow x 1 (Z ω)]
    simp only [one_pow, mul_one, mul_ite, mul_zero]
    rw [← sum_filter]
    congr 1
    ext D
    simp
  simp_rw [hpt]
  rw [expect_sum_comm]
  calc ∑ D : Finset ι, 𝔼 ω, x ^ #D * (if D ⊆ Z ω then 1 else 0 : ℝ)
      ≤ ∑ D : Finset ι, x ^ #D * p ^ #D := sum_le_sum fun D _ => by
        rw [← mul_expect]
        exact mul_le_mul_of_nonneg_left (hZ D) (pow_nonneg hx _)
    _ = (1 + x * p) ^ Fintype.card ι := by
        rw [add_comm, ← card_univ, ← sum_pow_mul_eq_add_pow (x * p) 1 univ, powerset_univ]
        simp [mul_pow]

omit [Nonempty Ω] in
/-- Union bound for a random set: if each `D` lies inside `Z` with probability at most
`p ^ |D|`, then `P[d₀ ≤ |Z|] ≤ (|ι| choose d₀) · p ^ d₀`. -/
theorem expect_indicator_le_card_le_choose_mul_pow {Z : Ω → Finset ι} {p : ℝ} (d₀ : ℕ)
    (hZ : ∀ D : Finset ι, 𝔼 ω, (if D ⊆ Z ω then 1 else 0 : ℝ) ≤ p ^ #D) :
    𝔼 ω, (if d₀ ≤ #(Z ω) then 1 else 0 : ℝ)
      ≤ (Fintype.card ι).choose d₀ * p ^ d₀ := by
  calc 𝔼 ω, (if d₀ ≤ #(Z ω) then 1 else 0 : ℝ)
      ≤ 𝔼 ω, ∑ D ∈ powersetCard d₀ (univ : Finset ι), (if D ⊆ Z ω then 1 else 0 : ℝ) :=
        expect_le_expect fun ω _ => by
          split_ifs with h
          · obtain ⟨D, hDZ, hD⟩ := exists_subset_card_eq h
            have hmem : D ∈ powersetCard d₀ (univ : Finset ι) :=
              mem_powersetCard.2 ⟨subset_univ _, hD⟩
            refine le_trans ?_ (single_le_sum (f := fun D => (if D ⊆ Z ω then 1 else 0 : ℝ))
              (fun _ _ => by split_ifs <;> norm_num) hmem)
            simp [hDZ]
          · exact sum_nonneg fun _ _ => by split_ifs <;> norm_num
    _ = ∑ D ∈ powersetCard d₀ (univ : Finset ι), 𝔼 ω, (if D ⊆ Z ω then 1 else 0 : ℝ) :=
        expect_sum_comm _ _ _
    _ ≤ ∑ D ∈ powersetCard d₀ (univ : Finset ι), p ^ d₀ :=
        sum_le_sum fun D hD => (mem_powersetCard.1 hD).2 ▸ hZ D
    _ = (Fintype.card ι).choose d₀ * p ^ d₀ := by
        rw [sum_const, card_powersetCard, card_univ, nsmul_eq_mul]

end GordieHowe
