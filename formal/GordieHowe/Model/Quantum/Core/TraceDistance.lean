-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Core.State
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section

/-!
# Trace distance of classical–quantum states, in operational form

The trace distance of two classical–quantum states `Σ_i |i⟩⟨i| ⊗ ρ i` and `Σ_i |i⟩⟨i| ⊗ σ i` is the
largest bias with which a measurement distinguishes them (Holevo–Helstrom; Watrous18 Theorem 3.4,
p. 128: for states of equal trace, `½ ‖ρ - σ‖₁ = max_{0 ≤ Π ≤ 1} tr(Π (ρ - σ))`). For states that are
block diagonal in the classical label every measurement acts as a two-outcome measurement
`(M i, 1 - M i)` on each block. `TraceDistLE ρ σ ε` states this bound in that form: every family of
effects `0 ≤ M i ≤ 1` and every finite set of labels give bias at most `ε`.

- `TraceDistLE.of_eq`: equal states are at distance `0`.
- `TraceDistLE.sum_re_trace_le`: the measurement of the label alone (`M i = 1`): on every finite
  set of labels the total weight of `σ` exceeds that of `ρ` by at most `ε`.
- `AvgTraceDistLE aux ρ σ ε`: the trace distance averaged over an auxiliary input `a ← aux`, with a
  register type that may depend on `a`, is at most `ε`.
-/

open Matrix
open scoped ComplexOrder

namespace GordieHowe.Quantum

variable {κ ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The trace distance of two classical–quantum states is at most `ε`**, in the operational
form of the Holevo–Helstrom theorem (Watrous18 Theorem 3.4, p. 128): for every family of
measurement effects `0 ≤ M i ≤ 1` on the blocks and every finite set `s` of classical labels,
`|Σ_{i ∈ s} tr (M i (ρ i - σ i))| ≤ ε`. -/
def TraceDistLE (ρ σ : κ → Matrix ι ι ℂ) (ε : ℝ) : Prop :=
  ∀ M : κ → Matrix ι ι ℂ, (∀ i, (M i).PosSemidef ∧ (1 - M i).PosSemidef) →
    ∀ s : Finset κ, |∑ i ∈ s, (M i * (ρ i - σ i)).trace.re| ≤ ε

namespace TraceDistLE

/-- Equal states are at trace distance `0`. -/
theorem of_eq {ρ σ : κ → Matrix ι ι ℂ} (h : ρ = σ) : TraceDistLE ρ σ 0 := fun M _ s => by
  subst h
  simp

/-- A bound at a smaller error is a bound at a larger one. -/
theorem mono {ρ σ : κ → Matrix ι ι ℂ} {ε ε' : ℝ} (h : TraceDistLE ρ σ ε) (hε : ε ≤ ε') :
    TraceDistLE ρ σ ε' :=
  fun M hM s => (h M hM s).trans hε

/-- **Measuring the label alone**: on every finite set of labels, the total weight of `σ` exceeds
that of `ρ` by at most `ε` (the effects `M i = 1`). -/
theorem sum_re_trace_le {ρ σ : κ → Matrix ι ι ℂ} {ε : ℝ} (h : TraceDistLE ρ σ ε) (s : Finset κ) :
    ∑ i ∈ s, (σ i).trace.re ≤ ∑ i ∈ s, (ρ i).trace.re + ε := by
  have h1 := h (fun _ => 1) (fun _ => ⟨PosSemidef.one, by simpa using PosSemidef.zero⟩) s
  simp only [one_mul, trace_sub, Complex.sub_re, Finset.sum_sub_distrib] at h1
  linarith [neg_abs_le (∑ i ∈ s, (ρ i).trace.re - ∑ i ∈ s, (σ i).trace.re)]

end TraceDistLE

open scoped NNReal ENNReal

/-- **The trace distance averaged over an auxiliary input `a ← aux` is at most `ε`**: some bounds
`δ a` on the trace distance of `ρ a` and `σ a` (`TraceDistLE`) at every auxiliary input have
average `Σ_a aux a · δ a` at most `ε`. The register type `R a` of the states may depend on `a`. -/
def AvgTraceDistLE {α : Type*} (aux : PMF α) {R : α → Type*} [∀ a, Fintype (R a)]
    [∀ a, DecidableEq (R a)] (ρ σ : (a : α) → κ → Matrix (R a) (R a) ℂ) (ε : ℝ≥0∞) : Prop :=
  ∃ δ : α → ℝ≥0, (∀ a, TraceDistLE (ρ a) (σ a) (δ a)) ∧ ∑' a, aux a * (δ a : ℝ≥0∞) ≤ ε

namespace AvgTraceDistLE

variable {α : Type*} {aux : PMF α} {R : α → Type*} [∀ a, Fintype (R a)] [∀ a, DecidableEq (R a)]
  {ρ σ : (a : α) → κ → Matrix (R a) (R a) ℂ}

/-- A bound at a smaller error is a bound at a larger one. -/
theorem mono {ε ε' : ℝ≥0∞} (h : AvgTraceDistLE aux ρ σ ε) (hε : ε ≤ ε') :
    AvgTraceDistLE aux ρ σ ε' :=
  let ⟨δ, hδ, hsum⟩ := h
  ⟨δ, hδ, hsum.trans hε⟩

/-- Equal states are at average trace distance `0`. -/
theorem of_eq (h : ∀ a, ρ a = σ a) : AvgTraceDistLE aux ρ σ 0 :=
  ⟨0, fun a => TraceDistLE.of_eq (h a), by simp⟩

end AvgTraceDistLE

end GordieHowe.Quantum
