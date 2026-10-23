-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.AffineBatching
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Basic.NNReal.Basic

@[expose] public section

/-!
# Longfellow layer assertions and shared alpha/beta batching

`Quad::prep_v` (`lib/sumcheck/quad.h:216-223`) replaces every zero coefficient
by the same beta, while ordinary coefficients remain unchanged. This tests the
sum of assertion products at each output gate, the grouped assertion table
`assertions` (the paper's `A_j(g)`, def:layered-circuit), which is what the
circuit relation constrains. The compiler's ordinary `assert0` node has one
zero-coefficient corner at its own gate; under that circuit invariant
(`UniqueAssertions`) the grouped table vanishes exactly when every individual
assertion product does (`assertions_zero_iff`).

Alpha combines the two output evaluations; beta weights the assertion
residual. The resulting residual is bilinear in the two fresh challenges,
not a batch with an independent coefficient for every assertion.
-/

namespace GordieHowe.GKR.Layer

open scoped Classical
open MvPolynomial

variable {F : Type} [Field F] {G W T : ℕ}

structure Corner (F : Type) (G W : ℕ) where
  gate : Fin G
  left : Fin W
  right : Fin W
  coefficient : F

abbrev _root_.GordieHowe.GKR.Layer (F : Type) (G W T : ℕ) := Fin T → Corner F G W

def product (Q : Layer F G W T) (w : Fin W → F) (i : Fin T) : F :=
  w (Q i).left * w (Q i).right

/-- Distinct assertion corners have distinct output gate indices, as for the compiler's `assert0`
nodes. It concerns the circuit, never prover values, and the GKR relation does not require it:
it only relates the grouped assertion table to the individual assertion products
(`assertions_zero_iff`). -/
def UniqueAssertions (Q : Layer F G W T) : Prop :=
  ∀ i j, (Q i).coefficient = 0 → (Q j).coefficient = 0 → (Q i).gate = (Q j).gate → i = j

noncomputable def assertions (Q : Layer F G W T) (w : Fin W → F) (g : Fin G) : F :=
  ∑ i, if (Q i).coefficient = 0 ∧ (Q i).gate = g then product Q w i else 0

/-- The grouped assertion at an output gate is exactly its single assertion
product when the layer has unique assertion gates. -/
theorem assertions_at (Q : Layer F G W T) (hQ : UniqueAssertions Q)
    (w : Fin W → F) (i : Fin T) (hi : (Q i).coefficient = 0) :
    assertions Q w (Q i).gate = product Q w i := by
  unfold assertions
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro j _ hji
    split_ifs with hj
    · exact (hji (hQ j i hj.1 hi hj.2)).elim
    · rfl
  · simp

/-- The grouped assertion table vanishes exactly when every individual assertion product does,
for a layer with unique assertion gates. -/
theorem assertions_zero_iff (Q : Layer F G W T) (hQ : UniqueAssertions Q)
    (w : Fin W → F) :
    (∀ g, assertions Q w g = 0) ↔ ∀ i, (Q i).coefficient = 0 → product Q w i = 0 := by
  constructor
  · intro h i hi
    rw [← assertions_at Q hQ w i hi]
    exact h _
  · intro h g
    apply Finset.sum_eq_zero
    intro i _
    split_ifs with hi
    · exact h i hi.1
    · rfl

/-- A weighted gate evaluation of the ordinary output contribution. -/
def ordinary (Q : Layer F G W T) (w : Fin W → F) (weight : Fin G → F) : F :=
  ∑ i, (Q i).coefficient * weight (Q i).gate * product Q w i

/-- A weighted evaluation of all assertion products. -/
noncomputable def asserted (Q : Layer F G W T) (w : Fin W → F) (weight : Fin G → F) : F :=
  ∑ i, if (Q i).coefficient = 0 then weight (Q i).gate * product Q w i else 0

/-- A weighted evaluation of the assertion products is the weighted sum of the grouped assertion
table: `Σ_i [coefficient i = 0] weight(gate i) · product i = Σ_g weight g · assertions g`. -/
theorem asserted_eq_sum (Q : Layer F G W T) (w : Fin W → F) (weight : Fin G → F) :
    asserted Q w weight = ∑ g, weight g * assertions Q w g := by
  simp only [asserted, assertions, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (Q i).gate]
  · by_cases hi : (Q i).coefficient = 0 <;> simp [hi]
  · intro g _ hg
    simp [Ne.symm hg]
  · simp

/-- Direct transcription of `prep_v` and the output-weight binding. -/
noncomputable def bind (Q : Layer F G W T) (w : Fin W → F)
    (weight : Fin G → F) (beta : F) : F :=
  ∑ i, (if (Q i).coefficient = 0 then beta * weight (Q i).gate
    else (Q i).coefficient * weight (Q i).gate) * product Q w i

theorem bind_eq (Q : Layer F G W T) (w : Fin W → F)
    (weight : Fin G → F) (beta : F) :
    bind Q w weight beta = ordinary Q w weight + beta * asserted Q w weight := by
  simp only [bind, ordinary, asserted, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h <;> simp [h, mul_assoc]

theorem ordinary_combine (Q : Layer F G W T) (w : Fin W → F)
    (weight0 weight1 : Fin G → F) (alpha : F) :
    ordinary Q w (fun g => weight0 g + alpha * weight1 g) =
      ordinary Q w weight0 + alpha * ordinary Q w weight1 := by
  simp only [ordinary, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem asserted_combine (Q : Layer F G W T) (w : Fin W → F)
    (weight0 weight1 : Fin G → F) (alpha : F) :
    asserted Q w (fun g => weight0 g + alpha * weight1 g) =
      asserted Q w weight0 + alpha * asserted Q w weight1 := by
  simp only [asserted, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

/-- Exact algebra of `raw_eq2` followed by `prep_v`: two output evaluation
weights combined with alpha, and one shared beta for every assertion corner. -/
theorem bind_combined (Q : Layer F G W T) (w : Fin W → F)
    (weight0 weight1 : Fin G → F) (alpha beta : F) :
    bind Q w (fun g => weight0 g + alpha * weight1 g) beta =
      ordinary Q w weight0 + alpha * ordinary Q w weight1 +
        beta * (asserted Q w weight0 + alpha * asserted Q w weight1) := by
  rw [bind_eq, ordinary_combine, asserted_combine]

/-- Difference between the combined incoming claims and the beta-weighted
layer polynomial: alpha and beta are shared exactly as in Longfellow. -/
def residual (d0 d1 a0 a1 alpha beta : F) : F :=
  d0 + alpha * d1 - beta * (a0 + alpha * a1)

theorem incoming_residual (Q : Layer F G W T) (w : Fin W → F)
    (weight0 weight1 : Fin G → F) (claim0 claim1 alpha beta : F) :
    claim0 + alpha * claim1 - bind Q w (fun g => weight0 g + alpha * weight1 g) beta =
      residual (claim0 - ordinary Q w weight0) (claim1 - ordinary Q w weight1)
        (asserted Q w weight0) (asserted Q w weight1) alpha beta := by
  rw [bind_combined]
  unfold residual
  ring

noncomputable def residualPolynomial (d0 d1 a0 a1 : F) : MvPolynomial (Fin 2) F :=
  C d0 + C d1 * X 0 - X 1 * (C a0 + C a1 * X 0)

@[simp] theorem residualPolynomial_eval (d0 d1 a0 a1 : F) (r : Fin 2 → F) :
    eval r (residualPolynomial d0 d1 a0 a1) = residual d0 d1 a0 a1 (r 0) (r 1) := by
  simp [residualPolynomial, residual, mul_comm]

theorem residualPolynomial_degree (d0 d1 a0 a1 : F) :
    (residualPolynomial d0 d1 a0 a1).totalDegree ≤ 2 := by
  have ha : ∀ x y : F, (C x + C y * X (0 : Fin 2)).totalDegree ≤ 1 := by
    intro x y
    apply (totalDegree_add _ _).trans
    exact max_le (by simp) ((totalDegree_mul _ _).trans (by simp))
  apply (totalDegree_sub _ _).trans
  apply max_le ((ha d0 d1).trans (by decide))
  exact (totalDegree_mul _ _).trans (by simpa using Nat.add_le_add_left (ha a0 a1) 1)

/-- If either ordinary evaluation is wrong or either assertion evaluation is
nonzero, the shared-alpha/beta residual is a nonzero polynomial. -/
theorem residualPolynomial_ne_zero (d0 d1 a0 a1 : F)
    (hbad : d0 ≠ 0 ∨ d1 ≠ 0 ∨ a0 ≠ 0 ∨ a1 ≠ 0) :
    residualPolynomial d0 d1 a0 a1 ≠ 0 := by
  intro h
  have h00 := congrArg (eval ![0, 0]) h
  have h10 := congrArg (eval ![1, 0]) h
  have h01 := congrArg (eval ![0, 1]) h
  have h11 := congrArg (eval ![1, 1]) h
  simp [residualPolynomial] at h00 h10 h01 h11
  have hd1 : d1 = 0 := by simpa [h00] using h10
  have ha0 : a0 = 0 := by simpa [h00] using h01
  have ha1 : a1 = 0 := by simpa [h00, hd1, ha0] using h11
  rcases hbad with hbad | hbad | hbad | hbad <;> contradiction

/-- Uniform independent alpha and beta incur at most 2/|F| error; no
independent per-assertion randomizers are postulated. -/
theorem batching_count [Fintype F] (d0 d1 a0 a1 : F)
    (hbad : d0 ≠ 0 ∨ d1 ≠ 0 ∨ a0 ≠ 0 ∨ a1 ≠ 0) :
    (Finset.univ.filter fun r : Fin 2 → F => residual d0 d1 a0 a1 (r 0) (r 1) = 0).card *
      Fintype.card F ≤ 2 * Fintype.card F ^ 2 := by
  have h := schwartz_zippel_totalDegree (residualPolynomial_ne_zero d0 d1 a0 a1 hbad)
    (Finset.univ : Finset F)
  rw [Fintype.piFinset_univ, Finset.card_univ] at h
  have hpos : (0 : ℚ≥0) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff₀ (by positivity) hpos] at h
  have hnat :
      (Finset.univ.filter fun r : Fin 2 → F => residual d0 d1 a0 a1 (r 0) (r 1) = 0).card *
      Fintype.card F ≤ (residualPolynomial d0 d1 a0 a1).totalDegree * Fintype.card F ^ 2 := by
    simpa only [residualPolynomial_eval] using (show
      (Finset.univ.filter fun r => eval r (residualPolynomial d0 d1 a0 a1) = 0).card *
        Fintype.card F ≤ (residualPolynomial d0 d1 a0 a1).totalDegree * Fintype.card F ^ 2 by
      exact_mod_cast h)
  exact hnat.trans (Nat.mul_le_mul_right _ (residualPolynomial_degree d0 d1 a0 a1))

/-- Shared-alpha/beta batching in the round-error convention. -/
theorem batching_count_nnreal [Fintype F] (d0 d1 a0 a1 : F)
    (hbad : d0 ≠ 0 ∨ d1 ≠ 0 ∨ a0 ≠ 0 ∨ a1 ≠ 0) :
    ((Finset.univ.filter fun r : Fin 2 → F => residual d0 d1 a0 a1 (r 0) (r 1) = 0).card : NNReal) ≤
      (2 / Fintype.card F : NNReal) * Fintype.card (Fin 2 → F) := by
  have hpos : (0 : NNReal) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  simp only [Fintype.card_fun, Fintype.card_fin]
  exact_mod_cast batching_count d0 d1 a0 a1 hbad

/-- Source-facing form of the bound, stated on the actual `prep_v` binding. -/
theorem bound_claim_count [Fintype F] (Q : Layer F G W T) (w : Fin W → F)
    (weight0 weight1 : Fin G → F) (claim0 claim1 : F)
    (hbad : claim0 ≠ ordinary Q w weight0 ∨ claim1 ≠ ordinary Q w weight1 ∨
      asserted Q w weight0 ≠ 0 ∨ asserted Q w weight1 ≠ 0) :
    ((Finset.univ.filter fun r : Fin 2 → F => claim0 + r 0 * claim1 =
      bind Q w (fun g => weight0 g + r 0 * weight1 g) (r 1)).card : NNReal) ≤
      (2 / Fintype.card F : NNReal) * Fintype.card (Fin 2 → F) := by
  have h := batching_count_nnreal
    (claim0 - ordinary Q w weight0) (claim1 - ordinary Q w weight1)
    (asserted Q w weight0) (asserted Q w weight1)
    (by simpa only [sub_ne_zero] using hbad)
  simpa only [← incoming_residual, sub_eq_zero] using h

end GordieHowe.GKR.Layer
