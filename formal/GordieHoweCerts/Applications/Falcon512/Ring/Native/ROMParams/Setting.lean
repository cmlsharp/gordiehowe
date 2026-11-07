-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHoweCerts.Applications.Falcon512.Ring.Native.ROMParams.Theorem
public import GordieHowe.Applications.Falcon512.Ring.Frontend.Statement
public import GordieHowe.ProofSystem.Program.BCSFormat
public import GordieHowe.Applications.Falcon512.Ring.Native.System.Codecs
public import GordieHowe.ProofSystem.Program.Transcript.ReaderLoads

@[expose] public section

/-!
# GordieHowe: the compiled circuits and transcript data of `Falcon512.Ring.Native.ROMParams`

The data the series–parallel transcript of the BCS transformation is built from, for the protocol at the realized program
of the native Falcon ring at the ROM parameters (`GordieHowe.Falcon512.Ring.Native.ROMParams.proofSystem`), with the
statement a ring signature statement `(R, m, r)` of rings of at most `64` keys (`GordieHowe.Falcon512.Ring.RStmt`)
read through the program's statement (`GordieHowe.Falcon512.Ring.stmtOf`: the keys' coefficients and the
coefficients of `HashToPoint(r ‖ m)`, which the verifier computes) and checked (`GordieHowe.Falcon512.Ring.ringOk`:
`64` keys and a successful hash), as the hand-built native ring's statement (`iop`: the soundness
IOP of the proof system at the frontend's round-by-round knowledge soundness, `RealizedProgram.ProofSystem.IOP.comapWith
stmtOf ringOk`). The transcript and the statements are in
`GordieHoweCerts/Applications/Falcon512/Ring/Native/ROMParams.lean`.

* **The proof systems** (`ProofSystems`): the definitions below are generic over them; the
  statements are at `proofSystem` (`GordieHoweCerts/Applications/Falcon512/Ring/Native/ROMParams/Certified.lean`).
* **The transcript data**: the label `gordiehowe:falcon-ring-native`, the ring statement's writes
  (`GordieHowe.Falcon512.Ring.Native.stmtCodecN` at `64` keys: the keys, the message bytes and the salt), the
  phase's codecs (no late value), the C++ challenge readers of `F_q^9` and LogUp's `α` outside
  `[0, 189)`; domain `A`'s codecs and readers are the generic per-field domain proof's
  (`GordieHoweCerts/Applications/Falcon512/Ring/Native/ROMParams.lean`).
-/

namespace GordieHowe.Falcon512.Ring.Native.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Ring
open Generated.Falcon512.Ring.Native.ROMParams.Program (program)
open Generated.Falcon512.Ring.Native.ROMParams (interp ProofSystems)
open Native (Signer CoreWit scheme)
open scoped NNReal ENNReal

variable (G : Signer 32)

/-! ## The compiled circuits and the multi-circuit IOP -/

variable {G} (C : ProofSystems)

/-- **The relation of the BCS transformation**: the statement passes the check (`ringOk`) and the
realized program's relation holds at its program statement, on the witness read from that statement. -/
abbrev ringStmtRel : Set (Ring.RStmt G × (program.Valuation interp → CoreWit)) :=
  {p | Ring.ringOk p.1 = true ∧
    (Ring.stmtOf p.1, p.2) ∈ RealizedProgram.ProofSystem.relOf Ring.rel}

end GordieHowe.Falcon512.Ring.Native.ROMParams
