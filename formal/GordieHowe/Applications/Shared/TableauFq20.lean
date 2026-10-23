-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.NNRealDyadic
public import GordieHowe.ProofSystem.Ligero.MaskTest.Pieces
public import GordieHowe.ProofSystem.Ligero.RelativeLayout
public import GordieHowe.ProofSystem.Ligero.MaskRow.Layout
public import GordieHowe.ProofSystem.Ligero.SubfieldTest
public import GordieHowe.Foundations.Algebra.RelativePacking
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative20Relative
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative20Tower

@[expose] public section

/-!
# The `F_q^20` tableau of the native Falcon configurations at the QROM parameters

Ligero at an agreement threshold, with the mask test, over `F_q^20`, `q = 12289`, at the tableau the
compiler chooses for domain A of `Falcon512.Native.QROMParams` and of `Falcon512.Ring.Native.QROMParams`
(`GordieHowe/Generated/`): `(rate, block_enc) = (12, 3799)`,
`(N, k) = (3258, 271)`, `t = 127`, one low-degree repetition, and the compiler's agreement threshold
`A = 944`.

The code is `k = (block_enc + 1) / (2 + rate)` (`lib/ligero/ligero_param.h:275`) and
`N = block_enc − (2k − 1)` (`lib/ligero/ligero_param.h:303`, `:313`). The line certificate is the
weighted Johnson certificate `lib/gordiehowe/compiler/ligero_choice.h` (`best_line_exhaustive`)
returns at threshold `A`, checked by `decide`. Each per-round error is proved below `c / 2^260` for
an explicit natural `c`; the docstrings give `-log₂` of the bound. The tree layout's numbers
(`fq20K271Numbers`) evaluate at the casts of the naturals below `q`.
-/

namespace GordieHowe.Tableau

open RelativePacking Ligero.MaskRow
open scoped NNReal

/-- The rate of the tableau: `12`. -/
abbrev fq20K271Rate : ℕ := 12

/-- `block_enc` of the tableau: `3799`. -/
abbrev fq20K271BlockEnc : ℕ := 3799

/-- The opened columns of the tableau: `t = 127`. -/
abbrev fq20K271T : ℕ := 127

/-- The message length of the code: `k = (block_enc + 1) / (2 + rate) = 271`. -/
abbrev fq20K271K : ℕ := (fq20K271BlockEnc + 1) / (2 + fq20K271Rate)

/-- The block length of the code: `N = block_enc − (2k − 1) = 3258`. -/
abbrev fq20K271N : ℕ := fq20K271BlockEnc - (2 * fq20K271K - 1)

/-- The agreement threshold of the line certificate: `A = 944`. -/
abbrev fq20K271Agree : ℕ := 944

/-- The exceptional count of the line certificate: `B = 23020764629` (`2^34.42`). -/
abbrev fq20K271Exceptions : ℕ := 23020764629

/-- **The Ligero numbers of the tableau**: `(rate, t, block_enc) = (12, 127, 3799)`. -/
def fq20K271Shape : Ligero.Relative.Shape := ⟨fq20K271Rate, fq20K271T, fq20K271BlockEnc, 1, fq20K271T⟩

theorem fq20K271K_eq : fq20K271K = 271 := rfl

theorem fq20K271N_eq : fq20K271N = 3258 := rfl

/-- **The line certificate of the code**, at agreement threshold `A = 944`: the weighted Johnson
certificate `(m, B, H) = (72, 250, 19298)` for degree `270` on `3258` points
(`lib/gordiehowe/compiler/ligero_choice.h`, `best_line_exhaustive`). -/
theorem fq20K271Line {F : Type} [Field F] (C : GordieHowe.RSCode F fq20K271N)
    (hk : C.k = fq20K271K) :
    RSCode.LineCertificate C fq20K271Agree (fq20K271Exceptions : ℕ) :=
  RSCode.lineCertificate_of_weightedJohnson C (D := 270) (m := 72) (B := 250)
    (H := 19298) (by unfold ReedSolomon.HiddenDerivative.IsJohnsonWeightedCertificate; decide +kernel)
    hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [ReedSolomon.HiddenDerivative.johnsonWeightedRefinedExceptionCount])

/-- **The code parameters of the tableau with the mask test**: `k ≤ A` and the line certificate
`fq20K271Line`. -/
theorem fq20K271MaskTest {F : Type} [Field F] (C : GordieHowe.RSCode F fq20K271N)
    (hk : C.k = fq20K271K) :
    Ligero.MaskTest.Pieces.Parameters C fq20K271Agree fq20K271Exceptions :=
  ⟨by rw [hk]; decide, fq20K271Line C hk⟩

/-- The round bounds of the tableau (`Ligero.MaskTest.Pieces.bounds`). -/
noncomputable abbrev fq20K271Bounds : Ligero.AgreementThreshold.Bounds :=
  Ligero.MaskTest.Pieces.bounds FalconNativeField20 fq20K271N fq20K271Agree fq20K271Exceptions 1
    fq20K271K fq20K271T

/-- The commit round of the tableau: `23020764629/(|F| − 1)`, `2^-237.28`. -/
theorem fq20K271Commit_le : fq20K271Bounds.commit ≤ (6911746 : ℝ≥0) / 2 ^ 260 := by
  show (((23020764629 : ℕ) : ℝ≥0) / (Fintype.card FalconNativeField20 - 1)) ^ 1 ≤ _
  rw [pow_one, falconNativeField20_card]
  exact ratio_pred_le_dyadic (by decide +kernel)

/-- The test round of the tableau with the mask test: `1/|F|`, `2^-271.70`. -/
theorem fq20K271Test_le : fq20K271Bounds.test ≤ (1 : ℝ≥0) / 2 ^ 260 := by
  show (1 : ℝ≥0) / (Fintype.card FalconNativeField20 : ℝ≥0) ≤ _
  rw [falconNativeField20_card]
  exact_mod_cast ratio_le_dyadic (num := 1) (c := 1) (by decide +kernel) (by decide +kernel)

/-- The column round of the tableau with the mask test at `t = 127`, with the joint subfield term:
`((944 − 1)_127 + (2 · 271 − 1)_127)/(3258)_127 + (271 − 1)_127/(3258)_127`, `2^-236.40`. -/
theorem fq20K271Column_le : fq20K271Bounds.column +
    Ligero.SubfieldTest.jointSubfieldError fq20K271K fq20K271N fq20K271T ≤
      (12734825 : ℝ≥0) / 2 ^ 260 :=
  column_le_dyadic (by decide +kernel) (by decide +kernel)

end GordieHowe.Tableau
