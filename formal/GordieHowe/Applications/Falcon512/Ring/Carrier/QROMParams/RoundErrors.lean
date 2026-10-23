-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHowe.Applications.Falcon512.Ring.Carrier.QROMParams.Setting

@[expose] public section

/-!
# GordieHowe: the round errors and the key relations of `Falcon512.Ring.Carrier.QROMParams`

The bounds the statements of `Falcon512.Ring.Carrier.QROMParams` read
(`GordieHowe/Applications/Falcon512/Ring/Carrier/QROMParams.lean`): every round error at most `errorMax` at the
configuration's dyadic scale (the domains' knowledge errors and the phases' errors, from the
circuits' shapes), and the relations at the key (`keyWitRel`, `keyHonestRel`, `honestBound`).
-/

namespace GordieHowe.Falcon512.Ring.Carrier.QROMParams

open RealizedProgram.Export RealizedProgram.ProofSystem.PhaseLayout IOP RelativePacking GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations GordieHowe.Ring
open Generated.Falcon512.Ring.Carrier.QROMParams.Program (program)
open Native (Signer CoreWit scheme)
open scoped NNReal ENNReal

variable {G : Signer 32} (C : Compiled)

/-! ## The round errors -/

/-- The largest round error, in units of `2^-260`: domain `A`'s commit bound, `16484193/2^260`
(`2^-236.03`). -/
abbrev errorMax : ℕ := 16484193

/-- **A dyadic in units of `2^-260` below the largest round error**: `x/2^260 ≤ errorMax/2^260` for
`x ≤ errorMax`. -/
theorem le_errorMax {x : ℝ≥0} (h : x ≤ errorMax) : x / 2 ^ 260 ≤ (errorMax : ℝ≥0) / 2 ^ 260 :=
  div_le_div_of_nonneg_right h (by positivity)

/-- **The phases' errors** are at most `errorMax / 2^260` (`RealizedProgram.phaseError_le_of`): every phase's
source and realization errors summed as one fraction (decided). -/
theorem phaseError_le (_C : Compiled) (k : Fin program.phases) :
    program.phaseError interpQROM
        (program.roundError interpQROM (Ring.ringEps interpQROM)) k ≤
      (errorMax : ℝ≥0) / 2 ^ 260 :=
  RealizedProgram.phaseError_le_of (Ring.ringEps interpQROM)
    (src := fun _ => (511, pGold ^ 4))
    fieldCard
    (fun j _ => by
      unfold Ring.ringEps
      split_ifs
      · rw [show Fintype.card _ = pGold ^ 4 from by convert goldilocksExt4_card <;> rfl]
        norm_num
      · exact zero_le')
    (by decide +kernel) k

/-! ## The figures -/

/-- The completeness error of the honest-prover statements: `0`. -/
noncomputable abbrev honestBound : ℝ≥0 := 0

/-! ## The knowledge statements at the ring signature relation -/

/-- **The relation of the BCS transformation gives the ring signature relation**: at a statement
that passes the check, the realized program's relation at its program statement gives the ring relation at
the signature encoded from the extracted `s2` with the statement's salt
(`Ring.ringRel_of_rel`). -/
theorem mem_ringRel64 {x : Ring.RStmt G} {g : program.Valuation interpQROM → CoreWit}
    (h : (x, g) ∈ ringStmtRel) :
    (x, (g (Ring.stmtOf x)).withSalt (G := G) x.pub) ∈ Ring.ringRel64 G :=
  Ring.ringRel_of_rel h.1 h.2

/-! ## The honest-prover statements -/

variable (TA : (proofSystem C.src).CircuitsAccept) {Inp : Type}
  {relH : Set (program.Valuation interpQROM × Inp)} (H : program.HonestStrategy interpQROM relH)

/-- **The honest inputs at the ring statement**: statements that pass the check and whose program
statement is the strategy's. -/
abbrev ringHonestRel (relH : Set (program.Valuation interpQROM × Inp)) :
    Set (Ring.RStmt G × Inp) :=
  {p | Ring.ringOk p.1 = true ∧ (Ring.stmtOf p.1, p.2) ∈ relH}

end GordieHowe.Falcon512.Ring.Carrier.QROMParams
