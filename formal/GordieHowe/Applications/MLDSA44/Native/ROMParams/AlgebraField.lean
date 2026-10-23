-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.ROMParams.HashField
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Locality
public import GordieHowe.Applications.Shared.Tableaux
public import GordieHowe.Applications.Shared.MACProfiles
public import GordieHowe.Applications.Params
public import GordieHowe.Language.Realizations.Lowering
public import GordieHowe.Foundations.Algebra.IntLift
public import GordieHowe.ProofSystem.Ligero.MaskTest.Pieces
public import GordieHowe.ProofSystem.Ligero.RelativeLayout
public import GordieHowe.ProofSystem.Ligero.SubfieldTest
public import GordieHowe.Foundations.ToMathlib.NNRealDyadic
public import GordieHowe.Foundations.Fields.Goldilocks
public import GordieHowe.Foundations.Fields.GoldilocksQuartic
public import GordieHowe.Foundations.Fields.GF2_256
public import GordieHowe.Foundations.Fields.GF2_128
public import GordieHowe.Applications.MLDSA44.System.Params
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative11
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative6
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative6Relative

@[expose] public section

/-!
# GordieHowe: the tableau of domain A of `MLDSA44.Native.ROMParams`

The Ligero numbers of domain `A` of the realized program of the native ML-DSA-44 proof of possession at the ROM parameters
(`GordieHowe.Generated.MLDSA44.Native.ROMParams.Program.program`, export `c825eb05`: domain `A` over `F_q^6`,
`q = 8380417`, the GKR circuit `c.A`, the batch `A.boolean`), whose domain proof is the generic
per-field one (`GordieHowe/Applications/MLDSA44/Native/ROMParams/ProofSystem.lean`): the compiler's
`(rate, t, block_enc) = (9, 74, 3376)`, `(N, k) = (2763, 307)` (`aShape`), the casts of the naturals
as evaluation points (`Shape.natPoints`), split masks at agreement threshold `975` with `17258473`
exceptional challenges (`aMaskTest`) and the round bounds (`aBounds`, `aCommit_le`, `aTest_le`,
`aColumn_le`).
-/

namespace GordieHowe.MLDSA44.Native.ROMParams.AlgebraField

open RealizedProgram.Export RelativePacking Ligero.MaskRow
open Generated.MLDSA44.Native.ROMParams.Program (program)
open HashField (interp)
open scoped NNReal

/-! ## The Ligero numbers -/

/-- The rate of A's code: `9` (the compiler's choice, recorded in
`GordieHowe.Generated.MLDSA44.Native.ROMParams.Plan`). -/
abbrev aRate : ℕ := 9

/-- `block_enc` of A's code: `3376`. -/
abbrev aBlockEnc : ℕ := 3376

/-- The opened columns of A's tableau: `t = 74`. -/
abbrev aT : ℕ := 74

/-- The message length of A's code: `k = (block_enc + 1) / (2 + rate) = 307`. -/
abbrev aK : ℕ := (aBlockEnc + 1) / (2 + aRate)

/-- The block length of A's code: `N = block_enc − (2k − 1) = 2763`. -/
abbrev aN : ℕ := aBlockEnc - (2 * aK - 1)

/-- The agreement threshold of A's line certificate: `A = 975`, the C++ compiler's choice. -/
abbrev aAgree : ℕ := 975

/-- The exceptional count of A's line certificate: `B = 17258473` (`2^24.04`). -/
abbrev aExceptions : ℕ := 17258473

/-- **The Ligero numbers of A's tableau**: `(rate, t, block_enc) = (9, 74, 3376)`. -/
def aShape : Ligero.Relative.Shape := ⟨aRate, aT, aBlockEnc, 1, aT⟩

/-- **The line certificate of A's code**, at agreement threshold `A = 975`: the weighted Johnson
certificate `(m, B, H) = (8, 24, 163)` for degree `306` on `2763` points
(`lib/gordiehowe/compiler/ligero_choice.h`, `best_line_exhaustive`). -/
theorem aLine {F : Type} [Field F] (C : GordieHowe.RSCode F aN) (hk : C.k = aK) :
    RSCode.LineCertificate C aAgree (aExceptions : ℕ) :=
  RSCode.lineCertificate_of_weightedJohnson C (D := 306) (m := 8) (B := 24)
    (H := 163)
    (by unfold ReedSolomon.HiddenDerivative.IsJohnsonWeightedCertificate; decide +kernel)
    hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [ReedSolomon.HiddenDerivative.johnsonWeightedRefinedExceptionCount])

/-- **The code parameters of A's tableau with split masks**: `k ≤ A` and the line certificate
`aLine`. -/
theorem aMaskTest {F : Type} [Field F] (C : GordieHowe.RSCode F aN) (hk : C.k = aK) :
    Ligero.MaskTest.Pieces.Parameters C aAgree aExceptions :=
  ⟨by rw [hk]; decide, aLine C hk⟩

/-- The round bounds of A's tableau (`Ligero.MaskTest.Pieces.bounds`). -/
noncomputable abbrev aBounds : Ligero.AgreementThreshold.Bounds :=
  Ligero.MaskTest.Pieces.bounds MLDSANativeField6 aN aAgree aExceptions 1 aK aT

/-- The commit round of A's tableau: `17258473/(|F| − 1)`, `2^-113.951`. -/
theorem aCommit_le : aBounds.commit ≤ (69439724 : ℝ≥0) / 2 ^ 140 := by
  show (((17258473 : ℕ) : ℝ≥0) / (Fintype.card MLDSANativeField6 - 1)) ^ 1 ≤ _
  rw [pow_one]
  rw [mldsaNativeField_card]
  exact ratio_pred_le_dyadic (by decide +kernel)

/-- The test round of A's tableau with split masks: `1/|F|`, `2^-137.99`. -/
theorem aTest_le : aBounds.test ≤ (5 : ℝ≥0) / 2 ^ 140 := by
  show (1 : ℝ≥0) / (Fintype.card MLDSANativeField6 : ℝ≥0) ≤ _
  rw [mldsaNativeField_card]
  exact_mod_cast ratio_le_dyadic (num := 1) (c := 5) (by decide +kernel) (by decide +kernel)

/-- The column round of A's tableau with split masks at `t = 74`, with the joint subfield term:
`((975 − 1)_74 + (2 · 307 − 1)_74)/(2763)_74 + (307 − 1)_74/(2763)_74`, `2^-113.996`. -/
theorem aColumn_le : aBounds.column + Ligero.SubfieldTest.jointSubfieldError aK aN aT ≤
    (67283340 : ℝ≥0) / 2 ^ 140 :=
  column_le_dyadic (by decide +kernel) (by decide +kernel)

end GordieHowe.MLDSA44.Native.ROMParams.AlgebraField
