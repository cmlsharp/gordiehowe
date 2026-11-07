-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHoweCerts.Applications.MLDSA44.Ring.Carrier.QROMParams.Theorem
public import GordieHowe.Applications.MLDSA44.Ring.Codecs
public import GordieHowe.ProofSystem.Program.BCSFormat
public import GordieHowe.ProofSystem.Program.Transcript.ReaderLoads

@[expose] public section

/-!
# GordieHowe: the compiled circuits and transcript data of `MLDSA44.Ring.Carrier.QROMParams`

The data the series–parallel transcript of the BCS transformation is built from, for the protocol
at the realized program of the ML-DSA-44 ring carrier at the QROM parameters
(`GordieHowe.MLDSA44.Ring.Carrier.QROMParams.proofSystem`), with the statement a ring statement
`(R, M′, ())` of rings of at most `64` keys and `msgLen`-byte message representatives
(`GordieHowe.MLDSA44.Ring.RStmt msgLen`), read through the program's statement
(`GordieHowe.MLDSA44.Ring.Carrier.stmtOf`: the keys' rows and every member's `μ` limbs, which the
verifier computes) and checked (`GordieHowe.MLDSA44.Ring.ringOk`: `64` keys, each with an `ExpandA`
within the byte budget). The transcript is in
`GordieHoweCerts/Applications/MLDSA44/Ring/Carrier/QROMParams.lean`.

* **The proof systems** (`ProofSystems`, `ProofSystem.lean`): the definitions below are generic over
  them; the statements are at `proofSystem` (`GordieHoweCerts/Generated/MLDSA44/Ring/Carrier/QROMParams/Certified.lean`).
* **The relation** (`ringStmtRel msgLen`): the statement passes the check and the realized
  program's relation holds at its program statement.
* **The transcript data**: the phases' codecs (`GordieHowe.RealizedProgram.appWrites`: `32` bytes in
  `Goldilocks^4`, `32` bytes in `GF(2^256)`), the C++ challenge readers of both fields and LogUp's `α`
  outside the table values; the label (`GordieHowe.MLDSA44.Ring.labelCarrier`) and the ring
  statement's writes (`GordieHowe.MLDSA44.Ring.stmtCodecN`) are the rings' shared ones.
-/

namespace GordieHowe.MLDSA44.Ring.Carrier.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking
  GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations
open Generated.MLDSA44.Ring.Carrier.QROMParams.Program (program)
open Generated.MLDSA44.Ring.Carrier.QROMParams (interp)
open scoped NNReal ENNReal

/-! ## The compiled circuits and the relation -/

variable (msgLen : ℕ) in
/-- **The relation of the BCS transformation** at `msgLen`-byte message representatives: the
statement passes the check (`ringOk`) and the realized program's relation `Carrier.rel` holds at its
program statement (`Carrier.stmtOf`), on the witness read from that statement. -/
abbrev ringStmtRel : Set (RStmt msgLen × (program.Valuation interp → Native.RingW)) :=
  {p | ringOk p.1 = true ∧
    (Carrier.stmtOf (program := program) (I := interp) p.1, p.2) ∈
      RealizedProgram.ProofSystem.relOf
        (Carrier.rel (program := program) (F0 := RealizedProgram.gold4) (FH := RealizedProgram.gf256))}

end GordieHowe.MLDSA44.Ring.Carrier.QROMParams
