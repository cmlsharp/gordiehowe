-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHoweCerts.Applications.Falcon512.Ring.Carrier.ROMParams.Setting

@[expose] public section

/-!
# GordieHowe: the key relations of `Falcon512.Ring.Carrier.ROMParams`

The relations the statements of `Falcon512.Ring.Carrier.ROMParams` read
(`GordieHoweCerts/Applications/Falcon512/Ring/Carrier/ROMParams.lean`) at the key (`keyWitRel`, `keyHonestRel`)
and the completeness error of the honest-prover statements (`honestBound`).
-/

namespace GordieHowe.Falcon512.Ring.Carrier.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Ring
open Generated.Falcon512.Ring.Carrier.ROMParams.Program (program)
open Generated.Falcon512.Ring.Carrier.ROMParams (interp ProofSystems)
open Native (CoreWit scheme)
open scoped NNReal ENNReal

variable {G : Signer 32} (C : ProofSystems)

/-! ## The figures -/


/-! ## The knowledge statements at the ring signature relation -/

/-- **The relation of the BCS transformation gives the ring signature relation**: at a statement
that passes the check, the realized program's relation at its program statement gives the ring relation at
the signature encoded from the extracted `s2` with the statement's salt
(`Ring.ringRel_of_rel`). -/
theorem mem_ringRel64 {x : Ring.RStmt G} {g : program.Valuation interp → CoreWit}
    (h : (x, g) ∈ ringStmtRel) :
    (x, (g (Ring.stmtOf x)).withSalt (G := G) x.pub) ∈ Ring.ringRel64 G :=
  Ring.ringRel_of_rel h.1 h.2

end GordieHowe.Falcon512.Ring.Carrier.ROMParams
