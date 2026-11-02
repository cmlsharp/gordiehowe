-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHowe.Applications.MLDSA44.Ring.Native.ROMParams.Setting

@[expose] public section

/-!
# GordieHowe: the ring relation of `MLDSA44.Ring.Native.ROMParams`

The soundness half of the ring statements' verification of ML-DSA-44
signatures (`ringWit`, `ringStmtRel_sound`: a witness of `ringStmtRel msgLen` at a checked
statement gives the ring relation `ringRel64 msgLen`, `Native.ringRel_of_rel`).
-/

namespace GordieHowe.MLDSA44.Ring.Native.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking
  GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations
open Generated.MLDSA44.Ring.Native.ROMParams.Program (program)
open Generated.MLDSA44.Ring.Native.ROMParams (interp)
open scoped NNReal ENNReal

/-! ## The ring relation -/

variable {msgLen : ℕ}

/-- **The ring witness of a witness map at a ring statement**: the position and the signature of
the witness the map reads at the statement's program statement (`Native.RingW.toWit`). -/
def ringWit (x : RStmt msgLen) (f : program.Valuation interp → Native.RingW) :
    GordieHowe.Ring.RingWit (scheme msgLen) :=
  (f (Native.stmtOf (program := program) (I := interp) x)).toWit msgLen

/-- **A witness of the relation of the BCS transformation at a checked statement gives the ring
relation** (`GordieHowe.Ring.SchemeVerifies.sound` at `ringOk`, `ringWit`): FIPS 204 verification
of the read signature on the statement's message representative under the key at the read position,
on a supported ring (`Native.ringRel_of_rel`). -/
theorem ringStmtRel_sound (x : RStmt msgLen) (f : program.Valuation interp → Native.RingW)
    (hok : ringOk x = true) (h : (x, f) ∈ ringStmtRel msgLen) :
    (x, ringWit x f) ∈ ringRel64 msgLen :=
  Native.ringRel_of_rel (program := program) (F0 := RealizedProgram.fq6)
    (FH := RealizedProgram.gf128) hok h.2

end GordieHowe.MLDSA44.Ring.Native.ROMParams
