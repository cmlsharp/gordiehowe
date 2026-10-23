-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHowe.Applications.MLDSA44.Native.QROMParams.Setting

@[expose] public section

/-!
# GordieHowe: the round errors and the key relations of `MLDSA44.Native.QROMParams`

The bounds the statements of `MLDSA44.Native.QROMParams` read
(`GordieHowe/Applications/MLDSA44/Native/QROMParams.lean`): every round error at most `errorMax` at the
configuration's dyadic scale (the domains' knowledge errors and the phases' errors, from the
circuits' shapes), and the relations at the key (`keyWitRel`, `keyHonestRel`, `honestBound`).
-/

namespace GordieHowe.MLDSA44.Native.QROMParams
open ROMParams (VarWitness KeyOf rel proj extractor)

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations
open Generated.MLDSA44.Native.QROMParams.Program (program)
open HashField (interp)
open scoped NNReal ENNReal

variable (C : Compiled)

/-! ## The round errors -/

/-- The largest round error, in units of `2^-260`: domain `H`'s column round with the
joint subfield term (`Tableau.gf256K339R2Column_le`, about `2^-236.329`). -/
abbrev errorMax : ℕ := 13358901

/-- **A dyadic of scale `2^260` below the largest round error**: `x/2^260 ≤ errorMax/2^260` for
`x ≤ errorMax`. -/
theorem le_errorMax {x : ℝ≥0} (h : x ≤ errorMax) : x / 2 ^ 260 ≤ (errorMax : ℝ≥0) / 2 ^ 260 :=
  div_le_div_of_nonneg_right h (by positivity)

/-- **The phases' errors** are at most `errorMax / 2^260` (`RealizedProgram.phaseError_le_of`): SampleInBall's
`264/2^256` and `295/2^256` and the MAC's `26/2^256` at the first phase, LogUp's `9216/(q^11 − 512)`
at the second, summed as one fraction (decided). -/
theorem phaseError_le (_C : Compiled) (k : Fin program.phases) :
    program.phaseError interp (program.roundError interp sampleEps) k ≤
      (errorMax : ℝ≥0) / 2 ^ 260 :=
  RealizedProgram.phaseError_le_of sampleEps
    (src := fun j => (if j = 0 then 264 else 295, 2 ^ 256))
    fieldCard
    (fun j _ => by
      unfold sampleEps ROMParams.sampleEpsOf
      split_ifs <;> norm_num)
    (by decide +kernel) k

/-! ## The figures -/

/-- The completeness error of the honest-prover headlines: the honest strategies have no completeness
error (`RealizedProgram.HonestStrategy.ofCompletion`, `δ = 0`). -/
noncomputable abbrev honestBound : ℝ≥0 := 0

/-! ## The knowledge statements at the key -/

/-- **The ML-DSA-44 proof-of-possession relation at the key**: the paper's relation for messages
of at most `32` bytes (`PoP.MLDSA44.relUpTo 32`): the witness is a message of some length `L ≤ 32`
and a signature on it that verifies under the key at the empty context (FIPS 204 Algorithm 3, with
`ExpandA` within `1008` SHAKE128 bytes per `RejNTTPoly` call (`ExpandAWithin`) and `SampleInBall`
within `272` SHAKE256 bytes). The maximal length `32` is the exported program's. -/
abbrev keyWitRel : Set (KeyStmt × VarWitness) :=
  {p | (p.1.1, p.2) ∈ MLDSA44.PoP.relUpTo 32}

/-- **The realized program's relation at the key's statement values gives the relation at the key**: the
statement values hold the key's preprocessing (`keyOf_stmtOf`), and the key's `ExpandA`
finishes within the byte budget. -/
theorem mem_keyWitRel {s : KeyStmt} {g : program.Valuation interp → VarWitness}
    (h : (s, g) ∈ keyRel) : (s, g (stmtOf s)) ∈ keyWitRel :=
  h s.1 s.2 (keyOf_stmtOf s)

/-! ## The honest-prover statements -/

variable (TA : (proofSystem C.src).CircuitsAccept) {Inp : Type}
  {relH : Set (program.Valuation interp × Inp)} (H : program.HonestStrategy interp relH)

/-- **The honest inputs at the key**: the strategy's honest inputs at the key's statement
values. -/
abbrev keyHonestRel (relH : Set (program.Valuation interp × Inp)) : Set (KeyStmt × Inp) :=
  {p | (stmtOf p.1, p.2) ∈ relH}

end GordieHowe.MLDSA44.Native.QROMParams
