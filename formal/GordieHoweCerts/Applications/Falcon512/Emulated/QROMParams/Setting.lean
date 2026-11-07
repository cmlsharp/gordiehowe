-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHoweCerts.Applications.Falcon512.Emulated.QROMParams.Theorem
public import GordieHowe.ProofSystem.Program.BCSFormat
public import GordieHowe.ProofSystem.Program.Transcript.ReaderLoads

@[expose] public section

/-!
# GordieHowe: the compiled circuits and transcript data of `Falcon512.Emulated.QROMParams`

The data the series–parallel transcript of spBCS is built from, for the protocol at the realized
program of the emulated Falcon proof of possession at the QROM parameters (`GordieHowe.Falcon512.Emulated.QROMParams.proofSystem`), with
the statement a Falcon public key read through its statement value (`iop`: the soundness IOP of the
proof system at the frontend's round-by-round knowledge soundness, `MultiCircuitIOP.comap stmtOf`; the
program's statement is a valuation, which has no codec). The transcript and the statements are in
`GordieHoweCerts/Applications/Falcon512/Emulated/QROMParams.lean`.

* **The proof systems** (`ProofSystems`): the definitions below are generic over them; the
  statements are at `proofSystem` (`GordieHoweCerts/Applications/Falcon512/Emulated/QROMParams/Certified.lean`).
* **The transcript data**: the label `gordiehowe:falcon-emulated-possession`, the phases' codecs
  (`GordieHowe.RealizedProgram.appWrites`: the late values as elements of their fields, `32` bytes in `GF(2^256)`, `32`
  bytes in Goldilocks⁴), the C++ challenge readers of both fields and LogUp's `α` outside
  `[0, 2048)` (`samplerReaders`, `GordieHowe.RealizedProgram.appReaders`); the domains' codecs and
  readers are the generic per-field domain proofs' (`GordieHoweCerts/Applications/Falcon512/Emulated/QROMParams.lean`).
-/

namespace GordieHowe.Falcon512.Emulated.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations
open Generated.Falcon512.Emulated.QROMParams.Program (program)
open Generated.Falcon512.Emulated.QROMParams (interp ProofSystems)
open scoped NNReal ENNReal

/-! ## The compiled circuits and the multi-circuit IOP -/

variable (C : ProofSystems)

/-- **The relation of spBCS**: the relation `rel` of the realized program at the statement of
the key, on the witness read from that statement. -/
abbrev keyRel : Set (PublicKey × (program.Valuation interp → VarWitness)) :=
  {p | (stmtOf p.1, p.2) ∈ RealizedProgram.ProofSystem.relOf rel}

/-! ## The transcript -/

/-- **The label write of `Falcon512.Emulated.QROMParams`**: `gordiehowe:falcon-emulated-possession`
(`system.h`, `"gordiehowe:" + s.name()`, `falcon_emulated` in
`lib/gordiehowe/examples/falcon/falcon_emulated.h`: `S::kTag + "-emulated-possession"`). -/
def label : List Byte :=
  TranscriptEncoding.labelBytes (asciiBytes "gordiehowe:falcon-emulated-possession")

end GordieHowe.Falcon512.Emulated.QROMParams
