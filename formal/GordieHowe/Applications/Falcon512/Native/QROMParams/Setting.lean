-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHowe.Applications.Falcon512.Native.QROMParams.Theorem
public import GordieHowe.ProofSystem.Program.BCSFormat
public import GordieHowe.ProofSystem.Program.Transcript.ReaderLoads

@[expose] public section

/-!
# GordieHowe: the compiled circuits and transcript data of `Falcon512.Native.QROMParams`

The data the series–parallel transcript of spBCS is built from, for the protocol at the realized
program of the native Falcon proof of possession at the QROM parameters (`GordieHowe.Falcon512.Native.QROMParams.proofSystem`), with the
statement a Falcon public key read through its statement value (`iop`: the soundness IOP of the
proof system at the frontend's round-by-round knowledge soundness, `MultiCircuitIOP.comap stmtOf`). The
transcript is in `GordieHowe/Applications/Falcon512/Native/QROMParams/Transcript.lean`, its statements in
`GordieHowe/Applications/Falcon512/Native/QROMParams.lean`.

* **The compiled circuits** (`Compiled`): the GKR sources of the program's circuits with the trust
  bundle `CircuitsEnforce`; the circuits' shapes (`CircuitsEnforce.shape`: `17`-dimensional
  layers, `15` and `16` layers).
* **The transcript data**: the label `gordiehowe:falcon-native-possession`, the phases' codecs
  (`GordieHowe.RealizedProgram.appWrites`: `32` bytes in `GF(2^256)`, `35` bytes in `F_q^20`), the C++ challenge
  readers of both fields and LogUp's `α` outside `[0, 189)`; the domains' codecs and readers are
  the generic per-field domain proofs' (`GordieHowe/Applications/Falcon512/Native/QROMParams/Transcript.lean`).
-/

namespace GordieHowe.Falcon512.Native.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations
open Generated.Falcon512.Native.QROMParams.Program (program)
open ROMParams (VarWitness rel stmtOf keyOf_stmtOf proj extractor)
open GordieHowe.Falcon512.Emulated (PublicKey)
open scoped NNReal ENNReal

/-! ## The compiled circuits and the multi-circuit IOP -/

/-- **The compiled circuits of `Falcon512.Native.QROMParams`** (`RealizedProgram.Compiled` at `QROMParams.proofSystem`): the GKR sources of
the program's circuits with the trust bundle `CircuitsEnforce`. -/
abbrev Compiled : Type := RealizedProgram.Compiled proofSystem

variable (C : Compiled)

/-- **The relation of spBCS**: the relation `rel` of the realized program at the statement of
the key, on the witness read from that statement. -/
abbrev keyRel : Set (PublicKey × (program.Valuation interp → VarWitness)) :=
  {p | (stmtOf p.1, p.2) ∈ RealizedProgram.ProofSystem.relOf rel}

/-! ## The transcript -/

/-- **The bytes of the fields' elements**: `32` bytes for `GF(2^256)` (field `0`), `35` bytes for
`F_q^20` (every other field), the C++ layouts (`Codec.FieldBytes.gf2_256`,
`Codec.FieldBytes.falconNative20`). -/
def fieldBytes : RealizedProgram.FieldBytesOf interp where
  fb
    | 0 => 32
    | _ + 1 => 35
  bytes
    | 0 => Codec.FieldBytes.gf2_256
    | _ + 1 => Codec.FieldBytes.falconNative20

/-- **The phases' messages fit in `2^20` bytes.** -/
theorem msgB_le : ∀ k, program.msgB fieldBytes k ≤ 2 ^ 20 := by
  decide +kernel

/-- The program has three challenges. -/
theorem challenges_length : program.challenges.length = 3 := by decide

/-- **The C++ samplers of the fields' elements**: `CReader.gf2_256` for field `0`, `CReader.falconNative20` for every
other field. -/
def fieldReader : ∀ f, CReader (interp f).K
  | 0 => CReader.gf2_256
  | _ + 1 => CReader.falconNative20

/-- **The fields' sizes**: `2 ^ 256` for field `0`, `12289 ^ 20` for every other field. -/
theorem fieldCard : ∀ f, Fintype.card (interp f).K = if f = 0 then 2 ^ 256 else 12289 ^ 20
  | 0 => by convert gf2_256_card <;> rfl
  | _ + 1 => by convert falconNativeField20_card <;> rfl

/-- **The readers of the challenges' values** (`RealizedProgram.stdReaders`): every challenge's field's
sampler, repeated until its value is outside the table values for LogUp's `α` (decided). -/
def samplerReaders : RealizedProgram.SamplerReaders interp program :=
  RealizedProgram.stdReaders fieldReader fieldCard (by decide +kernel)

/-- The largest load of a challenge: the `22` draws of `RealizedProgram.stdReaders`, the `32` bytes of an element
of `GF(2^256)`. -/
def chalLoadMax : Load := ⟨22, 32⟩

/-- Every challenge's draws are within `chalLoadMax` (`RealizedProgram.chalLoad_stdReaders_le`, decided). -/
theorem chalLoad_le (k : Fin program.phases) (j : program.ChalAt k) :
    program.chalLoad samplerReaders j.1 ≤ chalLoadMax :=
  RealizedProgram.chalLoad_stdReaders_le fieldReader fieldCard _ (by decide +kernel) k j

/-- **The label write of `Falcon512.Native.QROMParams`**: `gordiehowe:falcon-native-possession`
(`system.h`, `"gordiehowe:" + s.name()`, the plan's system name). -/
def label : List Byte :=
  TranscriptEncoding.labelBytes (asciiBytes "gordiehowe:falcon-native-possession")

end GordieHowe.Falcon512.Native.QROMParams
