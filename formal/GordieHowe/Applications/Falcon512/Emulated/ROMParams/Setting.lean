-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHowe.Applications.Falcon512.Emulated.ROMParams.Theorem
public import GordieHowe.ProofSystem.Program.BCSFormat
public import GordieHowe.ProofSystem.Program.Transcript.ReaderLoads

@[expose] public section

/-!
# GordieHowe: the compiled circuits and transcript data of `Falcon512.Emulated.ROMParams`

The data the series–parallel transcript of spBCS is built from, for the protocol at the realized
program of the emulated Falcon proof of possession at the ROM parameters (`GordieHowe.Falcon512.Emulated.ROMParams.proofSystem`), with
the statement a Falcon public key read through its statement value (`iop`: the soundness IOP of the
proof system at the frontend's round-by-round knowledge soundness, `MultiCircuitIOP.comap stmtOf`; the
program's statement is a valuation, which has no codec). The transcript and the statements are in
`GordieHowe/Applications/Falcon512/Emulated/ROMParams.lean`.

* **The proof systems** (`ProofSystems`): the definitions below are generic over them; the
  statements are at `proofSystem` (`GordieHowe/Applications/Falcon512/Emulated/ROMParams/Certified.lean`).
* **The transcript data**: the label `gordiehowe:falcon-emulated-possession`, the phases' codecs
  (`GordieHowe.RealizedProgram.appWrites`: the late values as elements of their fields, `16` bytes in `GF(2^128)`, `16`
  bytes in Goldilocks²), the C++ challenge readers of both fields and LogUp's `α` outside
  `[0, 2048)` (`samplerReaders`, `GordieHowe.RealizedProgram.appReaders`); the domains' codecs and
  readers are the generic per-field domain proofs' (`GordieHowe/Applications/Falcon512/Emulated/ROMParams.lean`).
-/

namespace GordieHowe.Falcon512.Emulated.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations
open Generated.Falcon512.Emulated.ROMParams.Program (program)
open Generated.Falcon512.Emulated.ROMParams (interp ProofSystems)
open scoped NNReal ENNReal

/-! ## The compiled circuits and the multi-circuit IOP -/

variable (C : ProofSystems)

/-- **The relation of spBCS**: the relation `rel` of the realized program at the statement of
the key, on the witness read from that statement. -/
abbrev keyRel : Set (PublicKey × (program.Valuation interp → VarWitness)) :=
  {p | (stmtOf p.1, p.2) ∈ RealizedProgram.ProofSystem.relOf rel}

/-! ## The transcript -/

/-- **The label write of `Falcon512.Emulated.ROMParams`**: `gordiehowe:falcon-emulated-possession`
(`system.h`, `"gordiehowe:" + s.name()`, `falcon_emulated` in
`lib/gordiehowe/examples/falcon/falcon_emulated.h`: `S::kTag + "-emulated-possession"`). -/
def label : List Byte :=
  TranscriptEncoding.labelBytes (asciiBytes "gordiehowe:falcon-emulated-possession")

end GordieHowe.Falcon512.Emulated.ROMParams
