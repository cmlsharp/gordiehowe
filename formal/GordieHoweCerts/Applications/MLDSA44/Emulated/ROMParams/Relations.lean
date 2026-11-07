-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHoweCerts.Applications.MLDSA44.Emulated.ROMParams.Setting

@[expose] public section

/-!
# GordieHowe: the key relations of `MLDSA44.Emulated.ROMParams`

The relations the statements of `MLDSA44.Emulated.ROMParams` read
(`GordieHoweCerts/Applications/MLDSA44/Emulated/ROMParams.lean`) at the key (`keyWitRel`).
-/

namespace GordieHowe.MLDSA44.Emulated.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations
open Generated.MLDSA44.Emulated.ROMParams.Program (program)
open Generated.MLDSA44.Emulated.ROMParams (interp ProofSystems)
open scoped NNReal ENNReal

variable (C : ProofSystems)

/-! ## The knowledge statements at the key -/

/-- **The ML-DSA-44 proof-of-possession relation at the key**: the paper's relation for messages
of at most `32` bytes (`PoP.MLDSA44.relUpTo 32`): the witness is a message of some length `L ≤ 32`
and a signature on it that verifies under the key at the empty context (FIPS 204 Algorithm 3, with
`ExpandA` within `1008` SHAKE128 bytes per `RejNTTPoly` call (`ExpandAWithin`) and `SampleInBall`
within `272` SHAKE256 bytes). The maximal length `32` is the exported program's. -/
abbrev keyWitRel : Set (KeyStmt × MLDSA44.VarWitness) :=
  {p | (p.1.1, p.2) ∈ MLDSA44.PoP.relUpTo 32}

/-- **The relation at the realized program, at the key's statement values, gives the relation at the key**: at
the key's preprocessing (`keyOf_stmtOf`), and the key's `ExpandA`
finishes within the byte budget. -/
theorem mem_keyWitRel {s : KeyStmt} {g : program.Valuation interp → MLDSA44.VarWitness}
    (h : (s, g) ∈ keyRel) : (s, g (stmtOf s)) ∈ keyWitRel :=
  h s.1 s.2 (keyOf_stmtOf s)

end GordieHowe.MLDSA44.Emulated.ROMParams
