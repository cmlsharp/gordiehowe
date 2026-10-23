-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHowe.Applications.Falcon512.Ring.Native.QROMParams.Theorem
public import GordieHowe.Applications.Falcon512.Ring.Frontend.Statement
public import GordieHowe.ProofSystem.Program.BCSFormat
public import GordieHowe.Applications.Falcon512.Ring.Native.System.Codecs
public import GordieHowe.ProofSystem.Program.Transcript.ReaderLoads

@[expose] public section

/-!
# GordieHowe: the compiled circuits and transcript data of `Falcon512.Ring.Native.QROMParams`

The data the series–parallel transcript of the BCS transformation is built from, for the protocol at the realized program
of the native Falcon ring at the QROM parameters (`GordieHowe.Falcon512.Ring.Native.QROMParams.proofSystem`), with the statement a
ring signature statement `(R, m, r)` of rings of at most `64` keys (`GordieHowe.Falcon512.Ring.RStmt`) read through
the program's statement (`GordieHowe.Falcon512.Ring.stmtOf`: the keys' coefficients and the coefficients of
`HashToPoint(r ‖ m)`, which the verifier computes) and checked (`GordieHowe.Falcon512.Ring.ringOk`: `64` keys and a
successful hash) (`iop`: the soundness IOP of the proof system at the frontend's round-by-round knowledge
soundness, `RealizedProgram.ProofSystem.IOP.comapWith stmtOf ringOk`). The series–parallel transcript is in
`GordieHowe/Applications/Falcon512/Ring/Native/QROMParams/Transcript.lean`, its statements in
`GordieHowe/Applications/Falcon512/Ring/Native/QROMParams.lean`.

* **The compiled circuits** (`Compiled`): the GKR source of the program's circuit with the trust
  bundle `CircuitsEnforce`; the circuit's shape (`CircuitsEnforce.shape`: `17`-dimensional layers,
  `14` layers).
* **The transcript data**: the label `gordiehowe:falcon-ring-native`, the ring statement's writes
  (`GordieHowe.Falcon512.Ring.Native.stmtCodecN` at `64` keys), the phase's codecs (`35` bytes in `F_q^20`, no
  late value), the C++ challenge readers of `F_q^20` and LogUp's `α` outside `[0, 189)`, and
  domain `A`'s extended points granted the plan's stream rows (`1154`, `1158` and `6`); domain
  `A`'s codecs and readers are the generic per-field domain proof's
  (`GordieHowe/Applications/Falcon512/Ring/Native/QROMParams/Transcript.lean`).
-/

namespace GordieHowe.Falcon512.Ring.Native.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Ring
open Generated.Falcon512.Ring.Native.QROMParams.Program (program)
open Native (Signer CoreWit scheme)
open scoped NNReal ENNReal

variable (G : Signer 32)

/-! ## The compiled circuits and the multi-circuit IOP -/

/-- **The compiled circuit of `Falcon512.Ring.Native.QROMParams`** (`RealizedProgram.Compiled` at `proofSystem`): the GKR source of
the program's circuit with the trust bundle `CircuitsEnforce`. -/
abbrev Compiled : Type := RealizedProgram.Compiled proofSystem

variable {G} (C : Compiled)

/-- **The relation of the BCS transformation**: the statement passes the check (`ringOk`) and the
realized program's relation holds at its program statement, on the witness read from that statement. -/
abbrev ringStmtRel : Set (Ring.RStmt G × (program.Valuation interpQROM → CoreWit)) :=
  {p | Ring.ringOk p.1 = true ∧
    (Ring.stmtOf p.1, p.2) ∈ RealizedProgram.ProofSystem.relOf Ring.rel}

/-! ## The phase's codecs and readers -/

/-- **The bytes of the fields' elements**: `35` bytes for `F_q^20`, the C++ layout
(`Codec.FieldBytes.falconNative20`). -/
def fieldBytes : RealizedProgram.FieldBytesOf interpQROM where
  fb _ := 35
  bytes _ := Codec.FieldBytes.falconNative20

/-- **The phase's messages fit in `2^20` bytes**: the program has no late value. -/
theorem msgB_le : ∀ k, program.msgB fieldBytes k ≤ 2 ^ 20 := by
  decide +kernel

/-- The program has two challenges. -/
theorem challenges_length : program.challenges.length = 2 := by decide

/-- **The C++ sampler of the field's elements**: `CReader.falconNative20`. -/
def fieldReader : ∀ f, CReader (interpQROM f).K := fun _ => CReader.falconNative20

/-- **The field's size**: `12289 ^ 20`. -/
theorem fieldCard : ∀ f, Fintype.card (interpQROM f).K = 12289 ^ 20 := fun _ => by convert falconNativeField20_card <;> rfl

/-- **The readers of the challenges' values** (`RealizedProgram.stdReaders`): every challenge's field's
sampler, repeated until its value is outside the table values for LogUp's `α` (decided). -/
def samplerReaders : RealizedProgram.SamplerReaders interpQROM program :=
  RealizedProgram.stdReaders fieldReader fieldCard (by decide +kernel)

/-- The largest load of a challenge: the `22` draws of `4` bytes of `RealizedProgram.stdReaders`. -/
def chalLoadMax : Load := ⟨22, 4⟩

/-- Every challenge's draws are within `chalLoadMax` (`RealizedProgram.chalLoad_stdReaders_le`, decided). -/
theorem chalLoad_le (k : Fin program.phases) (j : program.ChalAt k) :
    program.chalLoad samplerReaders j.1 ≤ chalLoadMax :=
  RealizedProgram.chalLoad_stdReaders_le fieldReader fieldCard _ (by decide +kernel) k j

/-! ## Domain `A`'s codecs and readers -/

/-- **The stream grants of domain `A`'s extended points** (`StreamRows.grants` at `35`-byte
elements): the plan's stream points `stage:1`, `root` and `ligero.alphal` with `1154`, `1158` and
`6` rows (`GordieHowe.Generated.Falcon512.Ring.Native.QROMParams.Plan.plan`); the inner combination's `1138` elements
need the `161560` granted bytes (`QROMParams.good_stage_at`). -/
def aGrants : StreamGrants := StreamRows.grants { stage := 1154, root := 1158, linear := 6 } 35

end GordieHowe.Falcon512.Ring.Native.QROMParams
