-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Emulated.ROMParams.GadgetFacts
public import GordieHowe.ProofSystem.Program.HonestReady
public import GordieHowe.Generated.Falcon512.Emulated.ROMParams.Facts
public import GordieHowe.Generated.Falcon512.Emulated.ROMParams.Completion

@[expose] public section

/-!
# GordieHowe: the honest strategy of `Falcon512.Emulated.ROMParams`

The honest strategy (`honestStrategy`): `GordieHowe.RealizedProgram.HonestStrategy.ofCompletionReady`
at the execution of the source program (`GordieHowe.Falcon512.Emulated.sourceExecution`), with no
completeness event (`δ = 0`, `honestStrategy_delta`), on the honest inputs
`GordieHowe.Falcon512.Native.HonestIn` (a valid Falcon-512 honest input with a message of at most
`32` bytes, at its key); the realization's facts and the honest roles come from the generated
checks (`completionReady`).
-/

namespace GordieHowe.Falcon512.Emulated.ROMParams

open Generated.Falcon512.Emulated.ROMParams.Program (program)
open Generated.Falcon512.Emulated.ROMParams (interp)
open Generated.Falcon512.Emulated.ROMParams.Facts (interpModel sourceValid)

/-- **The ready data of the honest strategy of `Falcon512.Emulated.ROMParams`**
(`RealizedProgram.CompletionReady.ofGenerated`): the honest nodes, which contain `1` (`oneNodes`),
and the generated facts: validity, the interpretation's model, the realizations, the source part,
and the checks of the completeness certificate and the honest roles
(`GordieHowe.Generated.Falcon512.Emulated.ROMParams.Completion.completionOk`, `GordieHowe.Generated.Falcon512.Emulated.ROMParams.Completion.rolesOk`). -/
def completionReady : program.CompletionReady interp
    (RealizedProgram.primeNodesOf Generated.Falcon512.Emulated.ROMParams.Plan.plan program)
    Generated.Falcon512.Emulated.ROMParams.Structure.records
    Generated.Falcon512.Emulated.ROMParams.Cert.gens
    Generated.Falcon512.Emulated.ROMParams.Cert.cderivs :=
  .ofGenerated (oneNodes (FH := RealizedProgram.gf128) (FA := RealizedProgram.gold2)) Generated.Falcon512.Emulated.ROMParams.Valid.wellFormed interpModel
    Generated.Falcon512.Emulated.ROMParams.Realize.derivable sourceValid Generated.Falcon512.Emulated.ROMParams.Completion.completionOk
    Generated.Falcon512.Emulated.ROMParams.Completion.rolesOk

/-- **The honest strategy of `Falcon512.Emulated.ROMParams`**
(`RealizedProgram.HonestStrategy.ofCompletionReady` at the execution `sourceExecution` at the
program's honest roles `completionReady.roles`): the honest valuation `honestVal` read off by
`execOf`, the generated late values, no completeness event. -/
noncomputable def honestStrategy :
    program.HonestStrategy interp (relH program RealizedProgram.gf128 RealizedProgram.gold2) :=
  RealizedProgram.HonestStrategy.ofCompletionReady completionReady
    (sourceExecution program RealizedProgram.gf128 RealizedProgram.gold2 _
      Generated.Falcon512.Emulated.ROMParams.Valid.wellFormed interpModel.registered
      interpModel.lawful completionReady.facts.committed completionReady.facts.boundNoCopy
      completionReady.roles completionReady.oneNodes interpModel.bitNodes
      Generated.Falcon512.Emulated.ROMParams.Completion.noFieldForm)

/-- **The honest strategy's completeness errors are `0`.** -/
theorem honestStrategy_delta : ∑ k, honestStrategy.δ k = 0 := by
  rw [honestStrategy, RealizedProgram.HonestStrategy.ofCompletionReady_δ, sourceExecution_δ]
  simp

end GordieHowe.Falcon512.Emulated.ROMParams
