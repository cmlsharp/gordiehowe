-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.AdaptiveCompleteness

@[expose] public section

/-!
# Adaptive completeness of the compiled arguments: the quantum oracle read as the chain oracle

The generic theorem of `GordieHowe/Model/QROM/AdaptiveCompleteness.lean` is stated for a quantum oracle
`H : Bits (queryBits k kN kS L) → XOut k e` on bit strings. The honest parties of the compiled
arguments read it through the query encoding and the byte reading of answers,
`q ↦ outEquiv k e (H (Query.toBits q))`. This file moves its fresh-slice hypothesis to the
classical oracle `Query k kN kS L → Out k e` of the compilers:

- `comp_toBits_replaceSlice`: the replaced slice of a bit-string oracle, read as a chain oracle,
  is the replaced slice of the chain oracle, when the salt slots correspond (`hs`).
- `probUniform_comp_toBits`: a uniform bit-string oracle read as a chain oracle is uniform.
- `freshSlice_coins_comp_toBits`: the fresh-slice bound on the chain oracle gives the one on bit
  strings, with the honest prover's coins.
- `ofReal_two_mul_div_sqrt_card`: the O2H term `2 t / √|Sd|` at the Fiat–Shamir salts of `kS` bytes
  is `2 t / 2^(4 kS)`.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP
open GordieHowe.QROM (replaceSlice)
open scoped ENNReal

variable {k kN kS L e : ℕ} {Sd : Type} [DecidableEq Sd]

/-- **The replaced slice of a bit-string oracle, read as a chain oracle**, is the replaced slice
of the chain oracle, when the salt of a query is the salt of its encoding (`hs`). -/
theorem comp_toBits_replaceSlice {saltB : Bits (queryBits k kN kS L) → Option Sd}
    {saltQ : Query k kN kS L → Option Sd} (hs : ∀ q, saltB (Query.toBits q) = saltQ q) (σ : Sd)
    (g F : Bits (queryBits k kN kS L) → XOut k e) :
    (outEquiv k e ∘ replaceSlice saltB σ g F) ∘ Query.toBits =
      replaceSlice saltQ σ (outEquiv k e ∘ g ∘ Query.toBits) (outEquiv k e ∘ F ∘ Query.toBits) := by
  funext q
  by_cases h : saltQ q = some σ
  · simp [replaceSlice, hs, h]
  · simp [replaceSlice, hs, h]

/-- **A uniform bit-string oracle read as a chain oracle is uniform** (the encoding `Query.toBits`
is injective and `outEquiv` a bijection). -/
theorem probUniform_comp_toBits (P : (Query k kN kS L → Out k e) → Prop) :
    Pr[F ← (Bits (queryBits k kN kS L) → XOut k e) : P (outEquiv k e ∘ F ∘ Query.toBits)] =
      Pr[F ← (Query k kN kS L → Out k e) : P F] := by
  classical
  exact (probUniform_comp_embedding Query.toBits fun g => P (outEquiv k e ∘ g)).trans
    (QROM.probUniform_equiv (Equiv.arrowCongr (Equiv.refl _) (outEquiv k e)) P)

/-- **The fresh-slice bound with coins moves from the chain oracle to bit strings**: if the event
`Bad r σ h o` has probability at most `δ` over uniform coins `r` when the slice of `σ` of the chain
oracle is fresh, so does the event read through the encoding when the slice of `σ` of the
bit-string oracle is fresh. -/
theorem freshSlice_coins_comp_toBits {saltB : Bits (queryBits k kN kS L) → Option Sd}
    {saltQ : Query k kN kS L → Option Sd} (hs : ∀ q, saltB (Query.toBits q) = saltQ q) {O : Type}
    {R : Type} [Fintype R] [Nonempty R] {Bad : R → Sd → (Query k kN kS L → Out k e) → O → Prop}
    {δ : ℝ≥0∞}
    (h : ∀ σ g o,
      Pr[q ← R × (Query k kN kS L → Out k e) : Bad q.1 σ (replaceSlice saltQ σ g q.2) o] ≤ δ)
    (σ : Sd) (g : Bits (queryBits k kN kS L) → XOut k e) (o : O) :
    Pr[q ← R × (Bits (queryBits k kN kS L) → XOut k e) :
        Bad q.1 σ ((outEquiv k e ∘ replaceSlice saltB σ g q.2) ∘ Query.toBits) o] ≤ δ := by
  simp_rw [comp_toBits_replaceSlice hs]
  refine le_of_eq_of_le ?_ (h σ (outEquiv k e ∘ g ∘ Query.toBits) o)
  rw [ROM.probUniform_prod_eq_sum, ROM.probUniform_prod_eq_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [probUniform_comp_toBits
    (fun F => Bad r σ (replaceSlice saltQ σ (outEquiv k e ∘ g ∘ Query.toBits) F) o)]

/-- **The O2H term at the Fiat–Shamir salts of `kS` bytes**: `2 t / √(2^(8 kS)) = 2 t / 2^(4 kS)`. -/
theorem ofReal_two_mul_div_sqrt_card (t : ℕ) :
    ENNReal.ofReal (2 * t / √(Fintype.card (FiatShamirSalt kS) : ℝ)) = 2 * t / 2 ^ (4 * kS) := by
  have hsalt : (Fintype.card (FiatShamirSalt kS) : ℝ) = 2 ^ (8 * kS) := by
    rw [show Fintype.card (FiatShamirSalt kS) = 2 ^ (8 * kS) from Out.card_digest]
    push_cast
    rfl
  have hsqrt : √(Fintype.card (FiatShamirSalt kS) : ℝ) = 2 ^ (4 * kS) := by
    rw [hsalt, show (2 : ℝ) ^ (8 * kS) = (2 ^ (4 * kS)) ^ 2 by rw [← pow_mul]; ring_nf,
      Real.sqrt_sq (by positivity)]
  rw [hsqrt, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_pow (by norm_num)]
  norm_num

end GordieHowe.SPBCS
