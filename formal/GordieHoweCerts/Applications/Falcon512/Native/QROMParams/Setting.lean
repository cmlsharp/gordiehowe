-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHoweCerts.Applications.Falcon512.Native.QROMParams.Theorem
public import GordieHowe.ProofSystem.Program.BCSFormat
public import GordieHowe.ProofSystem.Program.Transcript.ReaderLoads

@[expose] public section

/-!
# GordieHowe: the compiled circuits and transcript data of `Falcon512.Native.QROMParams`

The data the series–parallel transcript of spBCS is built from, for the protocol at the realized
program of the native Falcon proof of possession at the QROM parameters (`GordieHowe.Falcon512.Native.QROMParams.proofSystem`), with the
statement a Falcon public key read through its statement value (`iop`: the soundness IOP of the
proof system at the frontend's round-by-round knowledge soundness, `MultiCircuitIOP.comap stmtOf`). The
transcript is in `GordieHoweCerts/Applications/Falcon512/Native/QROMParams.lean`, its statements in
`GordieHoweCerts/Applications/Falcon512/Native/QROMParams.lean`.

* **The proof systems** (`ProofSystems`): the definitions below are generic over them; the
  statements are at `proofSystem` (`GordieHoweCerts/Applications/Falcon512/Native/QROMParams/Certified.lean`).
* **The transcript data**: the label `gordiehowe:falcon-native-possession`, the phases' codecs
  (`GordieHowe.RealizedProgram.appWrites`: `32` bytes in `GF(2^256)`, `35` bytes in `F_q^20`), the C++ challenge
  readers of both fields and LogUp's `α` outside `[0, 189)`; the domains' codecs and readers are
  the generic per-field domain proofs' (`GordieHoweCerts/Applications/Falcon512/Native/QROMParams.lean`).
-/

namespace GordieHowe.Falcon512.Native.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations
open Generated.Falcon512.Native.QROMParams.Program (program)
open Generated.Falcon512.Native.QROMParams (interp ProofSystems)
open scoped NNReal ENNReal

/-! ## The compiled circuits and the multi-circuit IOP -/

variable (C : ProofSystems)

/-- **The relation of spBCS**: the relation `rel` of the realized program at the statement of
the key, on the witness read from that statement. -/
abbrev keyRel : Set (PublicKey × (program.Valuation interp → VarWitness)) :=
  {p | (stmtOf p.1, p.2) ∈ RealizedProgram.ProofSystem.relOf rel}

/-! ## The transcript -/

/-- **The label write of `Falcon512.Native.QROMParams`**: `gordiehowe:falcon-native-possession`
(`system.h`, `"gordiehowe:" + s.name()`, the plan's system name). -/
def label : List Byte :=
  TranscriptEncoding.labelBytes (asciiBytes "gordiehowe:falcon-native-possession")

end GordieHowe.Falcon512.Native.QROMParams
