-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.SourceBudget

@[expose] public section

/-!
# Fixed source-circuit interface

This interface exposes the input dimension required by an application while
retaining the complete source layers as data. Its only semantic premise is
functional compiler soundness. Protocol rounds, equations and error bounds
are supplied by the proved source-derived GKR construction.
-/
namespace GordieHowe.GKR.CircuitBudget
open IOP
open GKR.Circuit

variable {F : Type} [Field F]

/-- The GKR transcript of a circuit has `2 · depth + 4 · dimensions + 1` moves: per layer the
two batching moves and two moves for each of the `2 · inDim` sumcheck rounds, and the final
input-binding challenge. -/
theorem circuitLength_eq {d : ℕ} (C : Circuit F d) :
    Schedule.circuitLength F C = 2 * C.depth + 4 * dimensions C + 1 := by
  induction C with
  | input => rfl
  | layer Q tail ih =>
    simp only [Schedule.circuitLength, Schedule.roundLength_eq, ih,
      Circuit.depth, dimensions]
    ring

/-- A circuit of depth at most `depth` whose layers have at most `2^bound` inputs has a GKR
transcript of at most `(2 + 4 · bound) · depth + 1` moves. -/
theorem circuitLength_le {d : ℕ} (C : Circuit F d) {bound depth : ℕ}
    (hw : WidthsAtMost C bound) (hl : C.depth ≤ depth) :
    Schedule.circuitLength F C ≤ (2 + 4 * bound) * depth + 1 := by
  have := dimensions_le C bound hw
  rw [circuitLength_eq]
  nlinarith

end GordieHowe.GKR.CircuitBudget

namespace GordieHowe.GKR.LayeredCircuit
open IOP
open GKR.Circuit CircuitFlatten
open scoped Classical NNReal

structure _root_.GordieHowe.GKR.LayeredCircuit (F : Type) [Field F] (d : ℕ) where
  outDim : ℕ
  inDim : ℕ
  terms : ℕ
  layer : GKR.Layer F (2^outDim) (2^inDim) terms
  tail : Circuit F inDim
  inputDim : tail.inputDim = d

variable {F Pub Wit : Type} [Field F] {d : ℕ}

def circuit (S : LayeredCircuit F d) : Circuit F S.outDim := .layer S.layer S.tail

/-- **A bound on the shape of a source circuit**: every wire layer, the output included, has at
most `2^width` wires (each layer at most `2^width` inputs and the output at most `2^width` gates),
and there are at most `depth` layers. -/
structure ShapeAtMost (S : LayeredCircuit F d) (width depth : ℕ) : Prop where
  outDim_le : S.outDim ≤ width
  widths : CircuitBudget.WidthsAtMost S.circuit width
  depth_le : S.circuit.depth ≤ depth

/-- A source circuit of shape at most `(width, depth)` has a GKR transcript of at most
`(2 + 4 · width) · depth + 1` moves. -/
theorem ShapeAtMost.circuitLength_le {S : LayeredCircuit F d} {width depth : ℕ}
    (h : S.ShapeAtMost width depth) :
    Schedule.circuitLength F S.circuit ≤ (2 + 4 * width) * depth + 1 :=
  CircuitBudget.circuitLength_le _ h.widths h.depth_le
def PadIdx (S : LayeredCircuit F d) : Type := PadIndex S.circuit
def padLayout (S : LayeredCircuit F d) : Transcript.Layout S.PadIdx S.tail.depth :=
  layout S.layer S.tail

def inputIndex (S : LayeredCircuit F d) : Fin (2^S.tail.inputDim) → Fin (2^d) :=
  Fin.cast (congrArg (fun n => 2^n) S.inputDim)

def Satisfied (S : LayeredCircuit F d) (input : Fin (2^d) → F) : Prop :=
  S.circuit.Satisfied (input ∘ S.inputIndex)

variable [Fintype F] [DecidableEq F]

/-- **The GKR interaction of a source circuit** (computable): the protocol and transcript
readouts of `SourceReduction.ofCircuit`. -/
def interaction (S : LayeredCircuit F d) (nodes : Sumcheck.Nodes F) :
    Transcript.Interaction F S.PadIdx d S.padLayout := by
  cases S with
  | mk outDim inDim terms Q tail hdim =>
    cases hdim
    exact SourceReduction.ofCircuit nodes Q tail

/-- The per-round errors of the source GKR interaction (`ProtocolReduction.error`). -/
noncomputable def error (S : LayeredCircuit F d) (nodes : Sumcheck.Nodes F) :
    (S.interaction nodes).spec.ChallengeIdx → ℝ≥0 := by
  cases S with
  | mk outDim inDim terms Q tail hdim =>
    cases hdim
    exact ProtocolReduction.error F (.layer Q tail)

/-- **Soundness of the source GKR interaction**: the compiler interface identifies the fixed
source circuit with the desired relation (`hcompile`). No statistical protocol property is
supplied by the caller. -/
noncomputable def sound (S : LayeredCircuit F d) (nodes : Sumcheck.Nodes F)
    (input : Pub → Wit → Fin (2^d) → F) (pad : Wit → S.PadIdx → F)
    (sat : Pub → Wit → Prop) (hcompile : ∀ pub w, S.Satisfied (input pub w) → sat pub w) :
    (S.interaction nodes).Sound input pad sat (S.error nodes) := by
  cases S with
  | mk outDim inDim terms Q tail hdim =>
    cases hdim
    exact SourceReduction.ofCircuitSound nodes Q tail input pad sat hcompile

theorem error_sum (S : LayeredCircuit F d) (nodes : Sumcheck.Nodes F) :
    (∑ i, S.error nodes i) =
      (CircuitBudget.numerator S.circuit : NNReal) / Fintype.card F := by
  cases S with
  | mk outDim inDim terms Q tail hdim =>
    cases hdim
    exact SourceReduction.protocol_error_sum (.layer Q tail)

/-- **The GKR error at a shape bound**: a source circuit of shape at most `(width, depth)` has
summed error at most `shapeBudget width depth / |F|`, the paper's `errgkr` at `m_j = width` for
every wire layer and `depth` layers. -/
theorem ShapeAtMost.error_sum_le {S : LayeredCircuit F d} {width depth : ℕ}
    (h : S.ShapeAtMost width depth) (nodes : Sumcheck.Nodes F) :
    (∑ i, S.error nodes i) ≤
      (CircuitBudget.shapeBudget width depth : NNReal) / (Fintype.card F : NNReal) := by
  rw [S.error_sum]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast CircuitBudget.numerator_le S.circuit width depth h.outDim_le h.widths h.depth_le

/-- **Per-round error of a source-derived GKR interaction**: at most `δ` when the initial
round `2·outDim/|F|` and every circuit round are. -/
theorem error_le (S : LayeredCircuit F d) (nodes : Sumcheck.Nodes F)
    {δ : ℝ≥0} (hinit : ((2 * S.outDim : ℕ) : ℝ≥0) / Fintype.card F ≤ δ)
    (hround : ∀ i, CircuitEvents.error S.circuit i ≤ δ) (i) :
    S.error nodes i ≤ δ := by
  cases S with
  | mk outDim inDim terms Q tail hdim =>
    cases hdim
    exact ProtocolReduction.error_le_of F _ (by exact_mod_cast hinit) hround i

/-- **Every round of a source-derived GKR interaction of shape at most `(width, depth)` is at most
`max 3 (2 · width)/|F|`** (the paper's lem:gkr(1), each challenge charged alone): the initial
point's `2 · outDim/|F|` with `outDim ≤ width`, and every later challenge's at most `3/|F|`
(`CircuitBudget.error_le_three`). -/
theorem ShapeAtMost.error_le {S : LayeredCircuit F d} {width depth : ℕ}
    (h : S.ShapeAtMost width depth) (nodes : Sumcheck.Nodes F) (i) :
    S.error nodes i ≤ ((max 3 (2 * width) : ℕ) : ℝ≥0) / Fintype.card F :=
  S.error_le nodes
    (div_le_div_of_nonneg_right
      (by exact_mod_cast (Nat.mul_le_mul_left 2 h.outDim_le).trans (le_max_right _ _))
      (by positivity))
    (fun j => (CircuitBudget.error_le_three _ j).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast le_max_left 3 (2 * width))
        (by positivity))) i

/-- **The round count of a source-derived GKR interaction**: the initial challenge and the
circuit's transcript. -/
theorem interaction_n (S : LayeredCircuit F d) (nodes : Sumcheck.Nodes F) :
    (S.interaction nodes).n = 1 + Schedule.circuitLength F S.circuit := by
  cases S with
  | mk outDim inDim terms Q tail hdim =>
    cases hdim
    rfl

/-- **The GKR transcript of a source circuit of bounded shape, by its input dimension**: a source
circuit of at most `depth` layers of at most `2^width` inputs reading a `2^d`-element input has a
GKR transcript of at most `(2 + 4 · width) · depth + 4 · d + 1 − 4 · width` moves (the deepest
layer reads `d` dimensions). -/
theorem ShapeAtMost.circuitLength_add_le {S : LayeredCircuit F d} {width depth : ℕ}
    (h : S.ShapeAtMost width depth) :
    Schedule.circuitLength F S.circuit + 4 * width ≤ (2 + 4 * width) * depth + 4 * d + 1 := by
  have hw : CircuitBudget.WidthsAtMost S.circuit width := h.widths
  have hl : S.circuit.depth ≤ depth := h.depth_le
  have ht := CircuitBudget.add_dimensions_le S.tail hw.1 hw.2
  have hd : S.tail.inputDim = d := S.inputDim
  have hdim : CircuitBudget.dimensions S.circuit = S.inDim + CircuitBudget.dimensions S.tail := rfl
  have hdep : S.circuit.depth = S.tail.depth + 1 := rfl
  rw [CircuitBudget.circuitLength_eq, hdim]
  rw [hdep] at hl
  rw [hd] at ht
  have hm : width * S.tail.depth + width ≤ width * depth := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ hl
  nlinarith

end GordieHowe.GKR.LayeredCircuit
