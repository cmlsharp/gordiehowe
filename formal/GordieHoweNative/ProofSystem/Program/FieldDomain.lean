-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.WithPlan

/-!
# GordieHowe: the compiled definitions of `GordieHowe.ProofSystem.Program.FieldDomain`

The plan's packing edges of a domain, which the domain's checks (`RealizedProgram.fieldOkB`)
read, in the Mathlib-free library `GordieHoweNative`. The declaration keeps its name; the checks
and their lemmas are in `GordieHowe/ProofSystem/Program/FieldDomain.lean`, which imports this
module.
-/

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- **The packing edges of the plan's domain of `d`**, the plan's domain at position `d`
(`Export.Plan.domainAt`; none when the plan has no domain there). -/
def planPacking (_ : RealizedProgram) (P : Export.Plan) (d : Nat) : List PackingEdge :=
  ((P.domainAt d).map (·.packing)).getD []

end GordieHowe.RealizedProgram
