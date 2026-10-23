-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHowe.Applications.Falcon512.Native.ROMParams.Theorem
public import GordieHowe.ProofSystem.Program.BCSFormat
public import GordieHowe.ProofSystem.Program.Transcript.ReaderLoads

@[expose] public section

/-!
# GordieHowe: the compiled circuits and transcript data of `Falcon512.Native.ROMParams`

The data the series–parallel transcript of spBCS is built from, for the protocol at the realized
program of the native Falcon proof of possession at the ROM parameters (`GordieHowe.Falcon512.Native.ROMParams.proofSystem`), with
the statement a Falcon public key read through its statement value (`iop`: the soundness IOP of the
proof system at the frontend's round-by-round knowledge soundness, `MultiCircuitIOP.comap stmtOf`; the
program's statement is a valuation, which has no codec). The transcript is in
`GordieHowe/Applications/Falcon512/Native/ROMParams/Transcript.lean`, its statements in
`GordieHowe/Applications/Falcon512/Native/ROMParams.lean`.

* **The compiled circuits** (`Compiled`): the GKR sources of the program's circuits with the trust
  bundle `CircuitsEnforce`; the circuits' shapes (`CircuitsEnforce.shape`: `17`-dimensional
  layers, `15` and `16` layers).
* **The transcript data**: the label `gordiehowe:falcon-native-possession`, the phases' codecs
  (`GordieHowe.RealizedProgram.appWrites`: the late values as elements of their fields, `16` bytes in `GF(2^128)`, `18`
  bytes in `F_q^9`), the C++ challenge readers of both fields and LogUp's `α` outside `[0, 189)`
  (`samplerReaders`, `GordieHowe.RealizedProgram.appReaders`); the domains' codecs and readers are the generic
  per-field domain proofs' (`GordieHowe/Applications/Falcon512/Native/ROMParams/Transcript.lean`).
-/

namespace GordieHowe.Falcon512.Native.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations
open Generated.Falcon512.Native.ROMParams.Program (program)
open GordieHowe.Falcon512.Emulated (PublicKey)
open scoped NNReal ENNReal

/-! ## The compiled circuits and the multi-circuit IOP -/

/-- **The compiled circuits of `Falcon512.Native.ROMParams`** (`RealizedProgram.Compiled` at `proofSystem`): the GKR sources of
the program's circuits with the trust bundle `CircuitsEnforce`. -/
abbrev Compiled : Type := RealizedProgram.Compiled proofSystem

variable (C : Compiled)

/-- **The relation of spBCS**: the relation `rel` of the realized program at the statement of
the key, on the witness read from that statement. -/
abbrev keyRel : Set (PublicKey × (program.Valuation interp → VarWitness)) :=
  {p | (stmtOf p.1, p.2) ∈ RealizedProgram.ProofSystem.relOf rel}

/-! ## The transcript -/

/-- **The bytes of the fields' elements**: `16` bytes for `GF(2^128)` (field `0`), `18` bytes for
`F_q^9` (every other field), the C++ layouts (`Codec.FieldBytes.gf2_128`,
`Codec.FieldBytes.falconNative`). -/
def fieldBytes : RealizedProgram.FieldBytesOf interp where
  fb
    | 0 => 16
    | _ + 1 => 18
  bytes
    | 0 => Codec.FieldBytes.gf2_128
    | _ + 1 => Codec.FieldBytes.falconNative

/-- **The phases' messages fit in `2^20` bytes**: phase `1`'s late values `mac.value` (one element
of `GF(2^128)`), `mac.acc`, `mac.gq` and the multiplicities of `range.dynamic:A.64` (`512 + 1024 +
64` elements of `F_q^9`); phase `2` has none. -/
theorem msgB_le : ∀ k, program.msgB fieldBytes k ≤ 2 ^ 20 := by
  decide +kernel

/-- The program has three challenges. -/
theorem challenges_length : program.challenges.length = 3 := by decide

/-- **The C++ samplers of the fields' elements**: `CReader.gf2_128` for field `0`, `CReader.falconNative` for every
other field. -/
def fieldReader : ∀ f, CReader (interp f).K
  | 0 => CReader.gf2_128
  | _ + 1 => CReader.falconNative

/-- **The fields' sizes**: `2 ^ 128` for field `0`, `12289 ^ 9` for every other field. -/
theorem fieldCard : ∀ f, Fintype.card (interp f).K = if f = 0 then 2 ^ 128 else 12289 ^ 9
  | 0 => by convert gf2_128_card <;> rfl
  | _ + 1 => by convert falconNativeField_card <;> rfl

/-- **The readers of the challenges' values** (`RealizedProgram.stdReaders`): every challenge's field's
sampler, repeated until its value is outside the table values for LogUp's `α` (decided). -/
def samplerReaders : RealizedProgram.SamplerReaders interp program :=
  RealizedProgram.stdReaders fieldReader fieldCard (by decide +kernel)

/-- The largest load of a challenge: the `11` draws of `4` bytes of `RealizedProgram.stdReaders`, the `16` bytes of
an element of `GF(2^128)`. -/
def chalLoadMax : Load := ⟨11, 16⟩

/-- Every challenge's draws are within `chalLoadMax` (`RealizedProgram.chalLoad_stdReaders_le`, decided). -/
theorem chalLoad_le (k : Fin program.phases) (j : program.ChalAt k) :
    program.chalLoad samplerReaders j.1 ≤ chalLoadMax :=
  RealizedProgram.chalLoad_stdReaders_le fieldReader fieldCard _ (by decide +kernel) k j

/-- **The label write of `Falcon512.Native.ROMParams`**: `gordiehowe:falcon-native-possession`
(`system.h`, `"gordiehowe:" + s.name()`), as the hand-built native Falcon system's. -/
def label : List Byte :=
  TranscriptEncoding.labelBytes (asciiBytes "gordiehowe:falcon-native-possession")

end GordieHowe.Falcon512.Native.ROMParams
