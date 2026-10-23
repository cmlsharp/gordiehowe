-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Algebra.BigOperators.Expect

@[expose] public section

/-!
# Distinguishing advantage

Every distinguishing advantage in the development (zero knowledge, witness indistinguishability,
O2H, anonymity games) is the absolute difference of two probabilities, written with the one
definition `GordieHowe.advantage`, and its bounds are stated in `ℝ`. `GordieHowe.gameAdvantage` is the same
quantity for a winning event under two output distributions.

The probability and expectation notation for general distributions lives here, beside the uniform
form `Pr[c ← C : E]` of `GordieHowe/Foundations/Probability/Probability.lean`:
* `Pr[x ~ μ : E]`: the probability of the event `E` for `x` drawn from the `PMF` `μ`, in `ℝ≥0∞`
  (`μ.toOuterMeasure {x | E}`);
* `𝔼[x ~ μ : f]`: the expectation of `f` for `x` drawn from `μ`, in `ℝ`
  (`∑' x, (μ x).toReal * f`);
* `𝔼[x ← C : f]`: the uniform average of `f` over the finite type `C`, Mathlib's `Finset.expect`
  (`𝔼 x : C, f`).
-/

namespace GordieHowe

/-- `Pr[x ~ μ : E]`: the probability of the event `E` for `x` drawn from the distribution `μ`. -/
syntax "Pr[" ident " ~ " term " : " term "]" : term

macro_rules
  | `(Pr[$x:ident ~ $μ : $E]) => `(PMF.toOuterMeasure $μ (Set.ofPred fun $x => $E))

/-- `𝔼[x ~ μ : f]`: the expectation of `f`, in `ℝ`, for `x` drawn from the distribution `μ`. -/
syntax "𝔼[" ident " ~ " term " : " term "]" : term

macro_rules
  | `(𝔼[$x:ident ~ $μ : $f]) => `(∑' $x:ident, ($μ $x).toReal * $f)

/-- `𝔼[x ← C : f]`: the uniform average of `f` over the finite type `C` (`Finset.expect`). -/
syntax "𝔼[" ident " ← " term " : " term "]" : term

macro_rules
  | `(𝔼[$x:ident ← $C : $f]) => `(Finset.expect Finset.univ fun ($x : $C) => $f)

/-- The distinguishing advantage between two probabilities: `|p₀ - p₁|`. Every advantage in the
development (zero knowledge, witness indistinguishability, O2H) is this one definition, with
bounds in `ℝ`. -/
def advantage (p₀ p₁ : ℝ) : ℝ := |p₀ - p₁|

theorem advantage_def (p₀ p₁ : ℝ) : advantage p₀ p₁ = |p₀ - p₁| := rfl

theorem advantage_nonneg (p₀ p₁ : ℝ) : 0 ≤ advantage p₀ p₁ := abs_nonneg _

theorem advantage_comm (p₀ p₁ : ℝ) : advantage p₀ p₁ = advantage p₁ p₀ := abs_sub_comm _ _

@[simp] theorem advantage_self (p : ℝ) : advantage p p = 0 := by simp [advantage]

/-- Triangle inequality for advantages (hybrid arguments). -/
theorem advantage_le_add (p₀ p₁ p₂ : ℝ) :
    advantage p₀ p₂ ≤ advantage p₀ p₁ + advantage p₁ p₂ := abs_sub_le _ _ _

/-- An advantage bound is a two-sided bound on the difference. -/
theorem advantage_le_iff {p₀ p₁ ε : ℝ} :
    advantage p₀ p₁ ≤ ε ↔ p₀ - p₁ ≤ ε ∧ p₁ - p₀ ≤ ε := by
  rw [advantage, abs_sub_le_iff]

/-- The advantage of distinguishing two output distributions `μ₀`, `μ₁` by the winning event
`win`: `|Pr_{μ₀}[win] - Pr_{μ₁}[win]|`. -/
noncomputable def gameAdvantage {α : Type*} (μ₀ μ₁ : PMF α) (win : Set α) : ℝ :=
  advantage (Pr[x ~ μ₀ : x ∈ win]).toReal (Pr[x ~ μ₁ : x ∈ win]).toReal

end GordieHowe
