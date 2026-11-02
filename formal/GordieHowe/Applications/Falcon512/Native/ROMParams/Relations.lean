-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHowe.Applications.Falcon512.Native.ROMParams.Setting

@[expose] public section

/-!
# GordieHowe: the key relations of `Falcon512.Native.ROMParams`

The relations the statements of `Falcon512.Native.ROMParams` read
(`GordieHowe/Applications/Falcon512/Native/ROMParams.lean`) at the key (`keyWitRel`, `keyHonestRel`)
and the completeness error of the honest-prover statements (`honestBound`).
-/

namespace GordieHowe.Falcon512.Native.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations
open Generated.Falcon512.Native.ROMParams.Program (program)
open Generated.Falcon512.Native.ROMParams (interp ProofSystems)
open GordieHowe.Falcon512.Emulated (PublicKey)
open scoped NNReal ENNReal

variable (C : ProofSystems)

/-! ## The completeness error -/

/-- The completeness error of the honest-prover statements: `0`, the honest strategy of
`Falcon512.Native.ROMParams` has no completeness event (`honestStrategy_delta`). -/
noncomputable abbrev honestBound : ℝ≥0 := 0

/-! ## The knowledge statements at the key -/

/-- **The Falcon-512 proof-of-possession relation at the key**: the witness is a message of some
length `L ≤ 32` and a signature on it under the key (`PoP.Falcon512.rel L`). -/
abbrev keyWitRel : Set (PublicKey × VarWitness) :=
  {p | (p.1, p.2.2) ∈ Falcon512.PoP.rel p.2.1}

/-- **The relation of the realized program at the key's statement gives the relation at the key**: the key's
statement decodes to the key (`keyOf_stmtOf`). -/
theorem mem_keyWitRel {pk : PublicKey} {g : program.Valuation interp → VarWitness}
    (h : (pk, g) ∈ keyRel) : (pk, g (stmtOf pk)) ∈ keyWitRel := by
  obtain ⟨pk', hk, hr⟩ := h
  rw [keyOf_stmtOf, Option.some_inj] at hk
  subst hk
  exact hr

/-! ## The honest-prover statements -/

variable {Inp : Type}
  {relH : Set (program.Valuation interp × Inp)} (H : program.HonestStrategy interp relH)

/-- **The honest inputs at the key**: the strategy's honest inputs at the key's statement. -/
abbrev keyHonestRel (relH : Set (program.Valuation interp × Inp)) : Set (PublicKey × Inp) :=
  {p | (stmtOf p.1, p.2) ∈ relH}

end GordieHowe.Falcon512.Native.ROMParams
