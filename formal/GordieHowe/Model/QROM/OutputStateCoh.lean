-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.OutputStateMixed
public import GordieHowe.Model.QROM.CoherentBridgeCore

@[expose] public section

/-!
# The coherent pure form and the algorithm's own register

- `MixedAlg.final_dilateCoh`, `Alg.final_toQueryAlgCoh`: the final vector of the coherent pure
  form (`Alg.toQueryAlgCoh`);
- `Alg.pureToMixed_ketBra_mask_finalCoh`: its register, masked to an outcome and mapped to the
  algorithm's own register, is the algorithm's output state at that outcome.
-/

open Finset Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

namespace MixedAlg

variable {Z ι R M : Type*} [Fintype ι] [DecidableEq ι] [Fintype R] [Fintype M] {d : ℕ}
  (G : MixedAlg Z ι d R M) [Nonempty R] [Nonempty M]

/-- The final vector of the dilation without the final measurement is the run of the dilation. -/
theorem final_dilateCoh (E : Z → Set M) (π : Equiv.Perm ι) (z : Z) :
    (G.dilateCoh E).final (liftPerm π) z = G.dilRun π z d := by
  refine hybrid_congr_le _ _ d fun i hi => ?_
  rw [OracleAlg.stepAt_of_lt _ (by omega)]
  rfl

end MixedAlg

namespace Alg

variable {X Y O : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] [AddGroup Y]
  (A : Alg X Y O)

/-- The final vector of the coherent pure form is the run of the dilation of the halting
completion, relabelled by `haltRelabel`. -/
theorem final_toQueryAlgCoh (f : X → Y) :
    haveI := A.init.nonempty
    A.toQueryAlgCoh.final f = Quantum.relabel (haltRelabel A.V A.HaltAnc X Y)
      (A.halting.dilRun (MixedAlg.liftPerm (queryPerm f)) () A.depth) := by
  have := A.init.nonempty
  rw [QueryAlg.final, OracleAlg.final]
  exact (OracleAlg.stage_relabel (A.halting.dilateCoh fun _ => ∅)
    (haltRelabel A.V A.HaltAnc X Y) (π' := queryPerm f) (fun _ => rfl) () A.depth).trans
    (congrArg _ (A.halting.final_dilateCoh _ _ ()))

/-- **The coherent pure form's register, traced down to the adversary's register**: masking the
final vector of `A.toQueryAlgCoh` to the outputs satisfying `P` and tracing out the ancilla
(`pureToMixed`) gives the output state of `A` on the basis states whose output satisfies `P`:
the block of `A`'s final state there, with the rest of the register unmeasured. -/
theorem pureToMixed_ketBra_mask_finalCoh (P : Option O → Prop) (f : X → Y) :
    A.pureToMixed (ketBra (mask {r | P (A.toQueryAlgCoh.out r.1)} (A.toQueryAlgCoh.final f))) =
      A.outputState f {i | P (some (A.out i.1))} := by
  classical
  have := A.init.nonempty
  have hset : (haltRelabel A.V A.HaltAnc X Y) ⁻¹' {r | P (A.toQueryAlgCoh.out r.1)} =
      {p | p.1 ∈ {m | P (A.haltOut m)}} := rfl
  simp only [pureToMixed, LinearMap.coe_mk, AddHom.coe_mk]
  rw [A.final_toQueryAlgCoh f, mask_relabel, hset, ptraceAlong_ketBra_relabel,
    MixedAlg.reduce_mask_dilRun]
  exact A.ffBlock_blockOn_halting_final P f

end Alg

end GordieHowe.Quantum
