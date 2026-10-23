-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.OutputLaw
public import GordieHowe.Model.QROM.OutputState
public import GordieHowe.Model.QROM.CoherentBridgeCore

@[expose] public section

/-!
# The adversary's own register after its run

Tracing the ancilla of a dilation out of the pure form's register, at every value of the output,
gives the state of the algorithm's own register after its final measurement:

- `ptraceAlong_ketBra_relabel`, `mask_relabel`, `reduce_mask_fst`: relabelling, masks and partial
  traces of pure states;
- `MixedAlg.reduce_mask_dilRun`: the reduced state of a masked dilated run;
- `Alg.pureToMixed`: the map from the pure form's register to the algorithm's own register;
  `Alg.outputState`: the block of the final state on the basis states of an outcome, only the
  output measured; `Alg.ffBlock_blockOn`, `Alg.ffBlock_blockOn_halting_final`.

The state clause of online extractability (`GordieHowe.NARG.QROM.Verifier.CohOnlineExtracts.traceDist_le`,
`GordieHowe/Model/NARG/QROM.lean`) is stated with them.
-/

open Finset Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

/-! ### Relabelling, masks and partial traces -/

section Relabel

variable {ι κ A : Type*} [Fintype ι] [Fintype κ] [Fintype A]

/-- Tracing out `A` along `σ.symm` from the projector onto a vector relabelled by `σ` is the
reduced density matrix of the vector. -/
theorem ptraceAlong_ketBra_relabel (σ : ι × A ≃ κ) (φ : QState (ι × A)) :
    ptraceAlong σ.symm (ketBra (relabel σ φ)) = reduce φ := by
  ext i j
  simp [ptraceAlong_apply]

/-- A mask commutes with a relabelling, along the preimage of its set. -/
theorem mask_relabel (σ : ι ≃ κ) (S : Set κ) (φ : QState ι) :
    mask S (relabel σ φ) = relabel σ (mask (σ ⁻¹' S) φ) := by
  classical
  ext j
  by_cases h : j ∈ S
  · rw [mask_apply_of_mem _ h, relabel_apply, relabel_apply, mask_apply_of_mem]
    simpa using h
  · rw [mask_apply_of_notMem _ h, relabel_apply, mask_apply_of_notMem]
    simpa using h

open Classical in
/-- Masking a vector on `ι × A` to the basis states whose system part lies in `T` and reducing is
the block on `T` of its reduced state. -/
theorem reduce_mask_fst (T : Set ι) (ψ : QState (ι × A)) :
    reduce (mask {p | p.1 ∈ T} ψ) = blockOn T (reduce ψ) := by
  ext i j
  rw [blockOn_apply, reduce_apply, reduce_apply]
  by_cases hi : i ∈ T <;> by_cases hj : j ∈ T <;>
    simp [hi, hj, mask_apply_of_mem, mask_apply_of_notMem]

end Relabel

/-! ### The dilation of a computational-basis measurement -/

namespace MixedAlg

variable {Z ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R] {d : ℕ}
  (G : MixedAlg Z ι d R ι) [Nonempty R] [Nonempty ι]

/-- **The run of the dilation before any final measurement, masked on the system**: the reduced
state of the dilation's vector after the last Kraus step, masked to the system basis states in
`T`, is the block on `T` of `G`'s final state, the state after measuring only whether the system
lies in `T`. -/
theorem reduce_mask_dilRun (π : Equiv.Perm ι) (z : Z) (T : Set ι) :
    reduce (mask {p | p.1 ∈ T} (G.dilRun π z d)) = blockOn T (G.final π z).mat := by
  rw [reduce_mask_fst, (G.dilRun_spec π z d).2]
  rfl

end MixedAlg

/-! ### Core algorithms -/

namespace Alg

variable {X Y O : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  (A : Alg X Y O)

/-- **From the pure form's register to the adversary's register**: trace out the ancilla of the
dilation (`haltRelabel` splits it off), then keep the block at halting flag `false`, the block
on which the run of `A` lives (`ffBlock_halting_stage`). Both maps are trace non-increasing and
completely positive, so they do not increase trace distance. -/
noncomputable def pureToMixed :
    Matrix (QueryReg A.toQueryAlgCoh.W 1 X Y) (QueryReg A.toQueryAlgCoh.W 1 X Y) ℂ →ₗ[ℂ]
      Matrix (QueryReg A.V 1 X Y) (QueryReg A.V 1 X Y) ℂ where
  toFun M := KrausMap.ffBlock (ptraceAlong (haltRelabel A.V A.HaltAnc X Y).symm M)
  map_add' M N := by
    rw [map_add]
    rfl
  map_smul' c M := by
    rw [map_smul]
    rfl

/-- **From the pure form's register to the adversary's register, the trace does not grow**, on
matrices with a nonnegative diagonal. -/
theorem re_trace_pureToMixed_le {M : Matrix (QueryReg A.toQueryAlgCoh.W 1 X Y)
    (QueryReg A.toQueryAlgCoh.W 1 X Y) ℂ} (h : ∀ i, 0 ≤ (M i i).re) :
    (A.pureToMixed M).trace.re ≤ M.trace.re :=
  (KrausMap.re_trace_ffBlock_le (re_ptraceAlong_apply_self_nonneg _ h)).trans
    (congrArg Complex.re (trace_ptraceAlong _ M)).le

variable [AddGroup Y]

/-- **The adversary's register after measuring only its output, on the outputs in `T`**: the
block on the basis states in `T` of the final state `A(ρ_init)` with oracle `f`. The rest of the
register stays coherent; this is the state of `(output, Z)` of DFMS22 Definition 3.1 (p. 10) at
the outputs in `T`. -/
noncomputable def outputState (f : X → Y) (T : Set (QueryReg A.V 1 X Y)) :
    Matrix (QueryReg A.V 1 X Y) (QueryReg A.V 1 X Y) ℂ :=
  blockOn T (A.final f)

omit [AddGroup Y] in
open Classical in
/-- The flag-`false` block of a block on `T'` is the block on the basis states `i` with
`(i, false) ∈ T'`. -/
theorem ffBlock_blockOn {ι : Type*} (T' : Set (ι × Bool)) (M : Matrix (ι × Bool) (ι × Bool) ℂ) :
    KrausMap.ffBlock (blockOn T' M) = blockOn {i | (i, false) ∈ T'} (KrausMap.ffBlock M) := by
  ext i j
  simp [KrausMap.ffBlock, blockOn_apply]

/-- **The halting completion, measured on its output only**: the flag-`false` block of the block of
the completed final state on the outcomes whose output (`haltOut`) satisfies `P` is the output
state of `A` on the basis states whose output satisfies `P`. -/
theorem ffBlock_blockOn_halting_final (P : Option O → Prop) (f : X → Y) :
    KrausMap.ffBlock (blockOn {m | P (A.haltOut m)}
        (A.halting.final (MixedAlg.liftPerm (queryPerm f)) ()).mat) =
      A.outputState f {i | P (some (A.out i.1))} := by
  rw [ffBlock_blockOn, MixedAlg.final, A.ffBlock_halting_stage f A.depth]
  rfl

end Alg

end GordieHowe.Quantum
