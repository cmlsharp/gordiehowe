-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.O2H.Basic
public import GordieHowe.Foundations.ToMathlib.PMFTV
public import GordieHowe.Foundations.ToMathlib.PMFUnion

@[expose] public section

/-!
# The guessing probability of a fresh secret

The guessing probability `pGuess` of AHU19 Theorem 3 (`GordieHowe/Model/Quantum/O2H/Basic.lean`) is small when the
set `S` on which the two oracles differ is determined by a secret that the algorithm has not
seen before its oracle steps. Here the outcome is a pair `(v, σ)` drawn from a product
distribution `μ (v, σ) = μV v * ν σ`, the set is `S (v, σ) w = T σ` for every content `w` of
the work register, and the states of `B^F` just before each oracle step depend on `v` only
(`OracleAlg.PreDependsOnlyOnFst`). The input `z` may depend on `σ`: only the steps up to the
last oracle step must ignore it.

- `sum_mul_prob_queried_eq`: for a fixed state `ψ`, averaging the probability of `queried (T σ)`
  over `σ ← ν` is the same as measuring the query inputs `t` of `ψ` and then drawing `σ`, so it
  is `∑ t, Pr[measured inputs = t] * Pr_σ[some t j ∈ T σ]`.
- `O2HSetting.pGuess_le_of_fresh_secret`: `pGuess ≤ ε` if `Pr_σ[some t j ∈ T σ] ≤ ε` for every
  tuple `t` of query inputs; `pGuess_le_mul_of_fresh_secret`: `pGuess ≤ n * ε` if
  `Pr_σ[x ∈ T σ] ≤ ε` for every input `x`, by the union bound over the `n` query registers.
- `O2HSetting.o2h_fresh_secret`: AHU19 Theorem 3 with that bound,
  `|P_left - P_right| ≤ 2 * d * √(n * ε)`.

The bound that charges each branch only for the oracle steps at which it queries is
`O2HSetting.o2h_fresh_secret_of_count` (`GordieHowe/Model/Quantum/O2H/Budget.lean`).
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

variable {W X Y R : Type*} [Fintype W] [Fintype X] [Fintype Y] {n : ℕ}

section Average

variable [Fintype R]

/-- Averaging the probability of `queried (T σ)` in a fixed state `ψ` over `σ ← ν` equals
measuring the query inputs `t` of `ψ` first and then drawing `σ`:
`∑ t, prob (queryInputs ⁻¹' {t}) ψ * Pr_σ[∃ j, t j ∈ T σ]`. -/
theorem sum_mul_prob_queried_eq (ν : PMF R) (T : R → Set X) (ψ : QState (QueryReg W n X Y)) :
    ∑ σ, (ν σ).toReal * prob (queried (T σ)) ψ =
      ∑ t, prob (queryInputs ⁻¹' {t}) ψ * (ν.toOuterMeasure {σ | ∃ j, t j ∈ T σ}).toReal := by
  classical
  simp_rw [prob_queried, PMF.toReal_toOuterMeasure_apply, sum_filter, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => sum_congr rfl fun σ _ => ?_
  by_cases h : ∃ j, t j ∈ T σ
  · simp [h, mul_comm]
  · simp [h]

/-- If every tuple `t` of query inputs meets `T σ` with probability at most `ε` over `σ ← ν`, the
probability of `queried (T σ)` in a unit vector `ψ`, averaged over `σ ← ν`, is at most `ε`. -/
theorem sum_mul_prob_queried_le (ν : PMF R) (T : R → Set X) {ψ : QState (QueryReg W n X Y)}
    (hψ : ‖ψ‖ = 1) {ε : ℝ}
    (hε : ∀ t : Fin n → X, (ν.toOuterMeasure {σ | ∃ j, t j ∈ T σ}).toReal ≤ ε) :
    ∑ σ, (ν σ).toReal * prob (queried (T σ)) ψ ≤ ε := by
  rw [sum_mul_prob_queried_eq]
  calc ∑ t, prob (queryInputs ⁻¹' {t}) ψ * (ν.toOuterMeasure {σ | ∃ j, t j ∈ T σ}).toReal
      ≤ ∑ t, prob (queryInputs ⁻¹' {t}) ψ * ε :=
        sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hε t) (prob_nonneg _ _)
    _ = ε := by rw [← sum_mul, sum_prob_fiber, hψ, one_pow, one_mul]

end Average

namespace OracleAlg

variable {Z V : Type*} {d : ℕ} [AddGroup Y]

/-- The states of `A` with oracle `F ω` on input `z ω`, just before each oracle step, depend only
on the first component of `ω = (v, σ)`. -/
def PreDependsOnlyOnFst (A : OracleAlg Z (QueryReg W n X Y) d) (F : V × R → W → X → Y)
    (z : V × R → Z) : Prop :=
  ∀ v σ σ' i, A.pre (queryPermOf (F (v, σ))) (z (v, σ)) i =
    A.pre (queryPermOf (F (v, σ'))) (z (v, σ')) i

/-- The states before the oracle steps depend only on `v` if the oracle does, and the initial
state and the steps before the last oracle step on input `z (v, σ)` do. -/
theorem preDependsOnlyOnFst_of (A : OracleAlg Z (QueryReg W n X Y) d) {F : V × R → W → X → Y}
    {z : V × R → Z} (hF : ∀ v σ σ', F (v, σ) = F (v, σ'))
    (hinit : ∀ v σ σ', A.init (z (v, σ)) = A.init (z (v, σ')))
    (hstep : ∀ v σ σ' (k : Fin (d + 1)), (k : ℕ) < d →
      A.step (z (v, σ)) k = A.step (z (v, σ')) k) :
    A.PreDependsOnlyOnFst F z := fun v σ σ' i => by
  rw [hF v σ σ']
  exact A.pre_congr _ (hinit v σ σ') (hstep v σ σ') i

end OracleAlg

namespace O2HSetting

variable {Z V : Type*} [Fintype R] [Fintype V] [AddGroup Y] {d : ℕ}
  (s : O2HSetting (V × R) Z W X Y) (A : OracleAlg Z (QueryReg W n X Y) d)

/-- **The guessing probability of a fresh secret.** Let the outcome be `(v, σ)` with
`μ (v, σ) = μV v * ν σ`, the set be `S (v, σ) w = T σ` for every `w`, and the states of `A^F`
before its oracle steps depend only on `v`. If every tuple `t` of query inputs meets `T σ` with
probability at most `ε` over `σ ← ν`, then `pGuess A F ≤ ε`.

For each `v` and each oracle step the measured state is the same for every `σ`, so averaging
over `σ` gives `sum_mul_prob_queried_le`. -/
theorem pGuess_le_of_fresh_secret {F : V × R → W → X → Y} {μV : PMF V} {ν : PMF R}
    {T : R → Set X} {ε : ℝ} (hμ : ∀ v σ, s.μ (v, σ) = μV v * ν σ)
    (hS : ∀ v σ w, s.S (v, σ) w = T σ) (hpre : A.PreDependsOnlyOnFst F s.z)
    (hε : ∀ t : Fin n → X, (ν.toOuterMeasure {σ | ∃ j, t j ∈ T σ}).toReal ≤ ε) :
    s.pGuess A F ≤ ε := by
  obtain ⟨σ₀, -⟩ := ν.support_nonempty
  obtain ⟨v₀, -⟩ := μV.support_nonempty
  have hε0 : 0 ≤ ε :=
    (sum_nonneg fun σ _ => mul_nonneg ENNReal.toReal_nonneg (prob_nonneg _ _)).trans
      (sum_mul_prob_queried_le ν T (A.norm_init (s.z (v₀, σ₀))) hε)
  have inner : ∀ v, ∑ σ, (ν σ).toReal *
      A.guessProb (queried (T σ)) (queryPermOf (F (v, σ))) (s.z (v, σ)) ≤ ε := fun v => by
    calc ∑ σ, (ν σ).toReal * A.guessProb (queried (T σ)) (queryPermOf (F (v, σ))) (s.z (v, σ))
        = 𝔼 i, ∑ σ, (ν σ).toReal *
            prob (queried (T σ)) (A.pre (queryPermOf (F (v, σ₀))) (s.z (v, σ₀)) i) := by
          rw [expect_sum_comm]
          refine sum_congr rfl fun σ _ => ?_
          rw [OracleAlg.guessProb, mul_expect]
          simp only [hpre v σ σ₀]
      _ ≤ 𝔼 _i : Fin d, ε :=
          expect_le_expect fun i _ => sum_mul_prob_queried_le ν T (A.norm_pre _ _ _) hε
      _ ≤ ε := by
          rcases isEmpty_or_nonempty (Fin d) with h | h
          · simp [hε0]
          · rw [Fintype.expect_const]
  rw [pGuess, Fintype.sum_prod_type]
  have hS' : ∀ v σ, s.S (v, σ) = fun _ => T σ := fun v σ => funext (hS v σ)
  simp_rw [hμ, hS', queriedOf_const, ENNReal.toReal_mul, mul_assoc, ← mul_sum]
  calc ∑ v, (μV v).toReal * ∑ σ, (ν σ).toReal *
        A.guessProb (queried (T σ)) (queryPermOf (F (v, σ))) (s.z (v, σ))
      ≤ ∑ v, (μV v).toReal * ε :=
        sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (inner v) ENNReal.toReal_nonneg
    _ = ε := by rw [← sum_mul, μV.sum_toReal, one_mul]

/-- **The guessing probability of a fresh secret, per query input.** In the setting of
`pGuess_le_of_fresh_secret`, if every single input `x` lies in `T σ` with probability at most
`ε` over `σ ← ν`, then `pGuess A F ≤ n * ε` (the union bound over the `n` query registers). -/
theorem pGuess_le_mul_of_fresh_secret {F : V × R → W → X → Y} {μV : PMF V} {ν : PMF R}
    {T : R → Set X} {ε : ℝ} (hμ : ∀ v σ, s.μ (v, σ) = μV v * ν σ)
    (hS : ∀ v σ w, s.S (v, σ) w = T σ) (hpre : A.PreDependsOnlyOnFst F s.z)
    (hε : ∀ x, (ν.toOuterMeasure {σ | x ∈ T σ}).toReal ≤ ε) :
    s.pGuess A F ≤ n * ε := by
  refine s.pGuess_le_of_fresh_secret A hμ hS hpre fun t => ?_
  rw [Set.ofPred_exists]
  refine (ν.toReal_toOuterMeasure_iUnion_le _).trans ?_
  calc ∑ j, (ν.toOuterMeasure {σ | t j ∈ T σ}).toReal ≤ ∑ _j : Fin n, ε :=
        sum_le_sum fun j _ => hε (t j)
    _ = n * ε := by simp


/-- **O2H for a fresh secret.** AHU19 Theorem 3 (`o2h`) when the oracles `G` and `H` differ only
on inputs in `T σ`, for a secret `σ ← ν` drawn independently of `v` (`μ (v, σ) = μV v * ν σ`),
and the states of `A^H` before its oracle steps depend only on `v`: if every input lies in
`T σ` with probability at most `ε`, then `|P_left - P_right| ≤ 2 * d * √(n * ε)`.

This is the step "the distinguisher has not touched the fresh salt's slice before the proof":
`T σ` is the set of oracle inputs that carry the salt `σ`, the counted oracle steps are the
queries before the proof, and everything after them (the proof, which uses `σ`, the later
oracle and the later proofs) is part of `step z d` and of the final measurement, through the
input `z`. For a uniform `λ`-bit salt in a fixed position of the input, an input `x` lies in
`T σ` only for the one salt written in that position, so `ε = 2^-λ`.

Hypotheses: `hμ` and `hS` say how the game draws its randomness and defines the set; `hpre` is
a fact about the algorithm's steps, usually discharged by `OracleAlg.preDependsOnlyOnFst_of`. -/
theorem o2h_fresh_secret {μV : PMF V} {ν : PMF R} {T : R → Set X} {ε : ℝ}
    (hμ : ∀ v σ, s.μ (v, σ) = μV v * ν σ) (hS : ∀ v σ w, s.S (v, σ) w = T σ)
    (hpre : A.PreDependsOnlyOnFst s.H s.z)
    (hε : ∀ x, (ν.toOuterMeasure {σ | x ∈ T σ}).toReal ≤ ε) :
    GordieHowe.advantage (s.pLeft A) (s.pRight A) ≤ 2 * d * √(n * ε) := by
  refine (s.o2h A).trans ?_
  gcongr
  exact s.pGuess_le_mul_of_fresh_secret A hμ hS hpre hε

end O2HSetting

end GordieHowe.Quantum
