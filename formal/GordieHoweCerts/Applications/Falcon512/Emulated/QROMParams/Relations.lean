-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHoweCerts.Applications.Falcon512.Emulated.QROMParams.Setting

@[expose] public section

/-!
# GordieHowe: the key relations of `Falcon512.Emulated.QROMParams`

The relations the statements of `Falcon512.Emulated.QROMParams` read
(`GordieHoweCerts/Applications/Falcon512/Emulated/QROMParams.lean`) at the key (`keyWitRel`).
-/

namespace GordieHowe.Falcon512.Emulated.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations
open Generated.Falcon512.Emulated.QROMParams.Program (program)
open Generated.Falcon512.Emulated.QROMParams (interp ProofSystems)
open scoped NNReal ENNReal

variable (C : ProofSystems)

/-! ## The knowledge statements at the key -/

/-- **The Falcon-512 proof-of-possession relation at the key**: the witness is a message of some
length `L ≤ 32` and a signature on it under the key (`Falcon512.PoP.rel L`). -/
abbrev keyWitRel : Set (PublicKey × VarWitness) :=
  Falcon512.PoP.relUpTo Falcon512.msgLenMax

/-- **The relation of the realized program at the key's statement gives the relation at the key**: the key's
statement decodes to the key (`keyOf_stmtOf`). -/
theorem mem_keyWitRel {pk : PublicKey} {g : program.Valuation interp → VarWitness}
    (h : (pk, g) ∈ keyRel) : (pk, g (stmtOf pk)) ∈ keyWitRel := by
  obtain ⟨pk', hk, hr⟩ := h
  rw [keyOf_stmtOf, Option.some_inj] at hk
  subst hk
  exact hr

end GordieHowe.Falcon512.Emulated.QROMParams
