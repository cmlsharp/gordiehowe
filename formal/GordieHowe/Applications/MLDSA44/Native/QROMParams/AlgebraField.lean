-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.QROMParams.HashField
public import GordieHowe.Applications.MLDSA44.Native.QROMParams.Locality
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
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative11Relative

@[expose] public section

/-!
# GordieHowe: the tableau of domain A of `MLDSA44.Native.QROMParams`

The Ligero numbers of domain `A` of the realized program of the native ML-DSA-44 proof of possession at the QROM parameters
(`GordieHowe.Generated.MLDSA44.Native.QROMParams.Program.program`, export `c825eb05`: domain `A` over `F_q^11`,
`q = 8380417`, the GKR circuit `c.A`, the batch `A.boolean`), whose domain proof is the generic
per-field one (`GordieHowe/Applications/MLDSA44/Native/QROMParams/ProofSystem.lean`): the compiler's
`(rate, t, block_enc) = (9, 144, 4274)`, `(N, k) = (3499, 388)`, two low-degree repetitions
(`aShape`), the casts of the naturals as evaluation points (`Shape.natPoints`), split masks at
agreement threshold `1169` with `74189372805` exceptional challenges (`aMaskTest`) and the round
bounds (`aBounds`, `aCommit_le`, `aTest_le`, `aColumn_le`).
-/

namespace GordieHowe.MLDSA44.Native.QROMParams.AlgebraField

open RealizedProgram.Export RelativePacking Ligero.MaskRow
open Generated.MLDSA44.Native.QROMParams.Program (program)
open HashField (interp)
open scoped NNReal

/-! ## The Ligero numbers -/

/-- The rate of A's code: `9` (the compiler's choice, recorded in
`GordieHowe.Generated.MLDSA44.Native.QROMParams.Plan`). -/
abbrev aRate : ℕ := 9

/-- `block_enc` of A's code: `4274`. -/
abbrev aBlockEnc : ℕ := 4274

/-- The opened columns of A's tableau: `t = 144`. -/
abbrev aT : ℕ := 144

/-- The low-degree repetitions of A's tableau: `2` (the realized program's `ldtReps`). -/
abbrev aReps : ℕ := 2

/-- The message length of A's code: `k = (block_enc + 1) / (2 + rate) = 388`. -/
abbrev aK : ℕ := (aBlockEnc + 1) / (2 + aRate)

/-- The block length of A's code: `N = block_enc − (2k − 1) = 3499`. -/
abbrev aN : ℕ := aBlockEnc - (2 * aK - 1)

/-- The agreement threshold of A's line certificate: `A = 1169`, the C++ compiler's choice. -/
abbrev aAgree : ℕ := 1169

/-- The exceptional count of A's line certificate: `B = 74189372805` (`2^36.11`). -/
abbrev aExceptions : ℕ := 74189372805

/-- **The Ligero numbers of A's tableau**: `(rate, t, block_enc) = (9, 144, 4274)` at two
low-degree repetitions. -/
def aShape : Ligero.Relative.Shape := ⟨aRate, aT, aBlockEnc, aReps, aT⟩

/-- **The line certificate of A's code**, at agreement threshold `A = 1169`: the weighted Johnson
certificate `(m, B, H) = (83, 250, 48315)` for degree `387` on `3499` points
(`lib/gordiehowe/compiler/ligero_choice.h`, `best_line_exhaustive`). -/
theorem aLine {F : Type} [Field F] (C : GordieHowe.RSCode F aN) (hk : C.k = aK) :
    RSCode.LineCertificate C aAgree (aExceptions : ℕ) :=
  RSCode.lineCertificate_of_weightedJohnson C (D := 387) (m := 83) (B := 250)
    (H := 48315)
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
  Ligero.MaskTest.Pieces.bounds MLDSANativeField11 aN aAgree aExceptions aReps aK aT

/-- The commit round of A's tableau: `(74189372805/(|F| − 1))^2`, `2^-433.7`. -/
theorem aCommit_le : aBounds.commit ≤ (1 : ℝ≥0) / 2 ^ 260 := by
  show (((74189372805 : ℕ) : ℝ≥0) / (Fintype.card MLDSANativeField11 - 1)) ^ 2 ≤ _
  rw [mldsaNativeField11_card]
  have h := ratio_pred_pow_le_dyadic (num := 74189372805) (q := 8380417 ^ 11) (c := 1) (e := 260)
    (nrep := 2) (by decide +kernel)
  rwa [Nat.cast_one] at h

/-- The test round of A's tableau with split masks: `1/|F|`, `2^-253.0`. -/
theorem aTest_le : aBounds.test ≤ (130 : ℝ≥0) / 2 ^ 260 := by
  show (1 : ℝ≥0) / (Fintype.card MLDSANativeField11 : ℝ≥0) ≤ _
  rw [mldsaNativeField11_card]
  exact_mod_cast ratio_le_dyadic (num := 1) (c := 130) (by decide +kernel) (by decide +kernel)

/-- The column round of A's tableau with split masks at `t = 144`, with the joint subfield term:
`((1169 − 1)_144 + (2 · 388 − 1)_144)/(3499)_144 + (388 − 1)_144/(3499)_144`, `2^-236.91`. -/
theorem aColumn_le : aBounds.column + Ligero.SubfieldTest.jointSubfieldError aK aN aT ≤
    (8951389 : ℝ≥0) / 2 ^ 260 :=
  column_le_dyadic (by decide +kernel) (by decide +kernel)

end GordieHowe.MLDSA44.Native.QROMParams.AlgebraField
