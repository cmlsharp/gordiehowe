-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHowe.Applications.Falcon512.Native.ROMParams.Setting

@[expose] public section

/-!
# GordieHowe: the round errors and the key relations of `Falcon512.Native.ROMParams`

The bounds the statements of `Falcon512.Native.ROMParams` read
(`GordieHowe/Applications/Falcon512/Native/ROMParams.lean`): every round error at most `errorMax` at the
configuration's dyadic scale (the domains' knowledge errors and the phases' errors, from the
circuits' shapes), and the relations at the key (`keyWitRel`, `keyHonestRel`, `honestBound`).
-/

namespace GordieHowe.Falcon512.Native.ROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations
open Generated.Falcon512.Native.ROMParams.Program (program)
open GordieHowe.Falcon512.Emulated (PublicKey)
open scoped NNReal ENNReal

variable (C : Compiled)

/-! ## The round errors -/

/-- The largest round error, in units of `2^-140`: LogUp's error at the second phase,
`16448/(q^9 − 189)` (`phaseError_le`). -/
abbrev errorMax : ℕ := 3586440187

/-- Division by `2^140` is monotone. -/
theorem div_two_pow_le {a b : ℝ≥0} (h : a ≤ b) : a / 2 ^ 140 ≤ b / 2 ^ 140 :=
  div_le_div_of_nonneg_right h (by positivity)

/-- **The phases' errors** are at most `errorMax / 2^140` (`RealizedProgram.phaseError_le_of`): every phase's
source and realization errors summed as one fraction (decided). -/
theorem phaseError_le (_C : Compiled) (k : Fin program.phases) :
    program.phaseError interp (program.roundError interp (selectEps (FH := RealizedProgram.gf128))) k ≤ (errorMax : ℝ≥0) / 2 ^ 140 :=
  RealizedProgram.phaseError_le_of (selectEps (FH := RealizedProgram.gf128))
    (src := fun _ => (639, 2 ^ 128))
    fieldCard
    (fun j _ => by
      unfold selectEps
      split_ifs
      · show (639 : ℝ≥0) / 2 ^ 128 ≤ _
        norm_num
      · exact zero_le')
    (by decide +kernel) k

/-! ## The figures -/

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

variable (TA : (proofSystem C.src).CircuitsAccept) {Inp : Type}
  {relH : Set (program.Valuation interp × Inp)} (H : program.HonestStrategy interp relH)

/-- **The honest inputs at the key**: the strategy's honest inputs at the key's statement. -/
abbrev keyHonestRel (relH : Set (program.Valuation interp × Inp)) : Set (PublicKey × Inp) :=
  {p | (stmtOf p.1, p.2) ∈ relH}

end GordieHowe.Falcon512.Native.ROMParams
