-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHowe.Applications.Falcon512.Ring.Carrier.ROMParams.Theorem
public import GordieHowe.ProofSystem.Program.BCSFormat
public import GordieHowe.Applications.Falcon512.Ring.Native.System.Codecs
public import GordieHowe.ProofSystem.Program.Transcript.ReaderLoads

@[expose] public section

/-!
# GordieHowe: the compiled circuits and transcript data of `Falcon512.Ring.Carrier.ROMParams`

The data the series–parallel transcript of the BCS transformation is built from, for the protocol at the realized program
of the Falcon ring carrier at the ROM parameters (`GordieHowe.Falcon512.Ring.Carrier.ROMParams.proofSystem`), with the
statement a ring signature statement `(R, m, r)` of rings of at most `64` keys (`GordieHowe.Falcon512.Ring.RStmt`)
read through the program's statement (`GordieHowe.Falcon512.Ring.stmtOf`: the keys' coefficients and the
coefficients of `HashToPoint(r ‖ m)`, which the verifier computes) and checked (`GordieHowe.Falcon512.Ring.ringOk`:
`64` keys and a successful hash), as the native rings' (`iop`: the soundness IOP of the proof system at
the frontend's round-by-round knowledge soundness, `RealizedProgram.ProofSystem.IOP.comapWith stmtOf ringOk`). The
transcript with forked domains is in `GordieHowe/Applications/Falcon512/Ring/Carrier/ROMParams/Transcript.lean`, its statements in
`GordieHowe/Applications/Falcon512/Ring/Carrier/ROMParams.lean`.

* **The compiled circuits** (`Compiled`): the GKR source of the program's circuit with the trust
  bundle `CircuitsEnforce`; the circuit's shape (`CircuitsEnforce.shape`).
* **The transcript data**: the label `gordiehowe:falcon-ring-carrier`, the ring statement's
  writes are in `GordieHowe.Falcon512.Ring.Native.stmtCodecN`; the phase's codecs (no late value, Goldilocks² in
  `16` bytes), the C++ challenge readers of Goldilocks² and LogUp's `α` outside `[0, 2048)`.
-/

namespace GordieHowe.Falcon512.Ring.Carrier.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Ring
open Generated.Falcon512.Ring.Carrier.ROMParams.Program (program)
open Native (Signer CoreWit scheme)
open scoped NNReal ENNReal

variable (G : Signer 32)

/-! ## The compiled circuits and the multi-circuit IOP -/

/-- **The compiled circuit of `Falcon512.Ring.Carrier.ROMParams`** (`RealizedProgram.Compiled` at `proofSystem`): the GKR source of
the program's circuit with the trust bundle `CircuitsEnforce`. -/
abbrev Compiled : Type := RealizedProgram.Compiled proofSystem

variable {G} (C : Compiled)

/-- **The relation of the BCS transformation**: the statement passes the check (`ringOk`) and the
realized program's relation holds at its program statement, on the witness read from that statement. -/
abbrev ringStmtRel : Set (Ring.RStmt G × (program.Valuation interpROM → CoreWit)) :=
  {p | Ring.ringOk p.1 = true ∧
    (Ring.stmtOf p.1, p.2) ∈ RealizedProgram.ProofSystem.relOf Ring.rel}

/-! ## The phase's codecs and readers -/

/-- **The bytes of the fields' elements**: `16` bytes for Goldilocks², the C++ layout
(`Codec.FieldBytes.goldilocksExt2`). -/
def fieldBytes : RealizedProgram.FieldBytesOf interpROM where
  fb _ := 16
  bytes _ := Codec.FieldBytes.goldilocksExt2

/-- **The phase's messages fit in `2^20` bytes**: the program has no late value. -/
theorem msgB_le : ∀ k, program.msgB fieldBytes k ≤ 2 ^ 20 := by
  decide +kernel

/-- The program has two challenges. -/
theorem challenges_length : program.challenges.length = 2 := by decide

/-- **The C++ sampler of the field's elements**: `CReader.goldilocksExt2`. -/
def fieldReader : ∀ f, CReader (interpROM f).K := fun _ => CReader.goldilocksExt2

/-- **The field's size**: `pGold ^ 2`. -/
theorem fieldCard : ∀ f, Fintype.card (interpROM f).K = pGold ^ 2 := fun _ => by convert goldilocksExt2_card <;> rfl

/-- **The readers of the challenges' values** (`RealizedProgram.stdReaders`): every challenge's field's
sampler, repeated until its value is outside the table values for LogUp's `α` (decided). -/
def samplerReaders : RealizedProgram.SamplerReaders interpROM program :=
  RealizedProgram.stdReaders fieldReader fieldCard (by decide +kernel)

/-- The largest load of a challenge: the `4` draws of `16` bytes of `RealizedProgram.stdReaders`. -/
def chalLoadMax : Load := ⟨4, 16⟩

/-- Every challenge's draws are within `chalLoadMax` (`RealizedProgram.chalLoad_stdReaders_le`, decided). -/
theorem chalLoad_le (k : Fin program.phases) (j : program.ChalAt k) :
    program.chalLoad samplerReaders j.1 ≤ chalLoadMax :=
  RealizedProgram.chalLoad_stdReaders_le fieldReader fieldCard _ (by decide +kernel) k j

/-! ## The transcript -/

/-- **The label write of the Falcon ring carriers**: `gordiehowe:falcon-ring-carrier` (`system.h`,
`"gordiehowe:" + s.name()`, `examples/rings/falcon_ring.h`). -/
def label : List Byte :=
  TranscriptEncoding.labelBytes (asciiBytes "gordiehowe:falcon-ring-carrier")

end GordieHowe.Falcon512.Ring.Carrier.ROMParams
