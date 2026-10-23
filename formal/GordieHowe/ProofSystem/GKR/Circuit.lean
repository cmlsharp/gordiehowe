-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.LayerPolynomial

@[expose] public section

/-!
# Padded no-copy Longfellow circuit semantics

Layers are ordered from output to input. Zero-coefficient corners are
assertions, as in `Quad::prep_v`; their ordinary output contribution is zero.
The complete table of intermediate wire values is computed from the input,
not supplied as a soundness hypothesis. Satisfaction is grouped per gate, as in
the paper's def:layered-circuit: the assertion table `A_j(g)`, the sum of the
assertion products at gate `g`, vanishes at every gate (`Layer.assertions`).
-/
namespace GordieHowe.GKR.Circuit

open LayerPolynomial
open scoped Classical

variable (F : Type) [Field F]

/-- Source circuit shape. Each layer uses its own padded input/output widths.
The labels identify the padded integer positions with their Boolean addresses.
Their concrete little-endian realization is a separate representation lemma. -/
inductive _root_.GordieHowe.GKR.Circuit : ℕ → Type
  | input (d : ℕ) : Circuit d
  | layer {outDim inDim T : ℕ}
      (Q : GKR.Layer F (2 ^ outDim) (2 ^ inDim) T)
      (tail : Circuit inDim) : Circuit outDim

variable {F}

def inputDim {d : ℕ} : Circuit F d → ℕ
  | .input d => d
  | .layer _ tail => tail.inputDim

/-- Number of sumcheck layers, excluding the terminal input table. -/
def depth {d : ℕ} : Circuit F d → ℕ
  | .input _ => 0
  | .layer _ tail => tail.depth + 1

/-- Ordinary layer evaluation, before beta is substituted for assertion corners. -/
def output {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2 ^ outDim) (2 ^ inDim) T)
    (w : Fin (2 ^ inDim) → F) (g : Fin (2 ^ outDim)) : F :=
  ∑ i, if (Q i).gate = g then (Q i).coefficient * Layer.product Q w i else 0

def eval {d : ℕ} (C : Circuit F d)
    (input : Fin (2 ^ C.inputDim) → F) : Fin (2 ^ d) → F :=
  match C with
  | .input _ => input
  | .layer Q tail => output Q (tail.eval input)

/-- Assertion satisfaction throughout the circuit: every layer's assertion table vanishes at
every gate (the paper's `A_j = 0`, def:layered-circuit). All internal values are those obtained by
deterministic evaluation from the terminal input. -/
def AssertionsHold {d : ℕ} (C : Circuit F d)
    (input : Fin (2 ^ C.inputDim) → F) : Prop :=
  match C with
  | .input _ => True
  | .layer Q tail =>
    (∀ g, Layer.assertions Q (tail.eval input) g = 0) ∧ tail.AssertionsHold input

/-- The source relation checked by the zero-output GKR path. -/
def Satisfied {d : ℕ} (C : Circuit F d)
    (input : Fin (2 ^ C.inputDim) → F) : Prop :=
  (∀ g, C.eval input g = 0) ∧ C.AssertionsHold input

/-- Evaluating the computed output with arbitrary weights recovers exactly the
ordinary part of Longfellow's layer binding. -/
theorem output_weighted {outDim inDim T : ℕ}
    (Q : GKR.Layer F (2 ^ outDim) (2 ^ inDim) T)
    (w : Fin (2 ^ inDim) → F) (weight : Fin (2 ^ outDim) → F) :
    (∑ g, weight g * output Q w g) = Layer.ordinary Q w weight := by
  simp only [output, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold Layer.ordinary
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_eq_single (Q i).gate]
  · simp only [ite_true]
    ring
  · intro g _ hg
    simp [Ne.symm hg]
  · simp

end GordieHowe.GKR.Circuit
