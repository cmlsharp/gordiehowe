-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.NNRealDyadic
public import GordieHowe.ProofSystem.Ligero.MaskTest.Pieces
public import GordieHowe.ProofSystem.Ligero.RelativeLayout
public import GordieHowe.ProofSystem.Ligero.MaskRow.Layout
public import GordieHowe.ProofSystem.Ligero.SubfieldTest
public import GordieHowe.Foundations.Fields.Goldilocks
public import GordieHowe.Foundations.Fields.GoldilocksQuartic
public import GordieHowe.Foundations.Fields.GF2_128
public import GordieHowe.Foundations.Fields.GF2_256

@[expose] public section

/-!
# Ligero tableaus shared by several configurations

Ligero at an agreement threshold, with the mask test, over a relatively packed commitment, at the
tableaus that
more than one configuration uses:

* **Goldilocks⁴ with `k = 512`** (`gold4K512…`): `(rate, block_enc) = (6, 4095)`, `(N, k) =
  (3072, 512)`, `t = 201`, the compiler's choice for domain A of `Falcon512.Ring.Carrier.QROMParams`
  (`GordieHowe/Generated/`);
* **Goldilocks⁴ with `k = 512` at two low-degree repetitions** (`gold4K512R2…`): `(rate,
  block_enc) = (6, 4095)`, `(N, k) = (3072, 512)`, `t = 175`, `nrep = 2`, the compiler's choice for
  domain A of `MLDSA44.Emulated.QROMParams` (`GordieHowe/Generated/`);
* **`GF(2^128)` with `k = 282` at two low-degree repetitions** (`gf128K282R2…`): `(rate,
  block_enc) = (12, 3955)`, `(N, k) = (3392, 282)`, `t = 63`, `nrep = 2`, the compiler's choice for
  domain H of `Falcon512.Native.ROMParams`, `MLDSA44.Native.ROMParams` and
  `MLDSA44.Emulated.ROMParams` (the same export);
* **Goldilocks² with `k = 512` at two low-degree repetitions** (`gold2K512R2…`): `(rate,
  block_enc) = (5, 3583)`, `(N, k) = (2560, 512)`, `t = 96`, `nrep = 2`, the compiler's choice for
  domain A of `MLDSA44.Emulated.ROMParams` (the same export) and `Falcon512.Ring.Carrier.ROMParams` (at
  `b65a4929`);
* **`GF(2^256)` with `k = 339` at two low-degree repetitions** (`gf256K339R2…`): `(rate,
  block_enc) = (12, 4746)`, `(N, k) = (4069, 339)`, `t = 128`, `nrep = 2`, the compiler's choice for
  domain H of `Falcon512.Native.QROMParams`, `MLDSA44.Native.QROMParams` and
  `MLDSA44.Emulated.QROMParams` (the same export).

The compiler's choices are its Ligero parameters (`rate`, `block_enc`, `t`, the low-degree
repetitions) and the agreement threshold `A`. The line certificate is a weighted Johnson certificate
at threshold `A`, of the kind `lib/gordiehowe/compiler/ligero_choice.h` (`best_line_exhaustive`)
searches for.

The code is `k = (block_enc + 1) / (2 + rate)` (`lib/ligero/ligero_param.h:275`) and
`N = block_enc − (2k − 1)` (`lib/ligero/ligero_param.h:303`, `:313`). The exceptional count `B` is
the line certificate's at threshold `A` (checked by `decide`). Each per-round error is proved below
`c / 2^260` (Goldilocks⁴, `GF(2^256)`) or `c / 2^140` (`GF(2^128)`, Goldilocks²) for an explicit
natural `c`; the docstrings give `-log₂` of the bound. A configuration's setting uses these
values by name (for example `Tableau.gf256K339R2Shape` in
`GordieHowe/Applications/Falcon512/Native/QROMParams/Setting.lean`).
-/

namespace GordieHowe.Tableau

open scoped NNReal

/-! ### Goldilocks⁴, `(N, k) = (3072, 512)`, `t = 201` -/

/-- The rate of the tableau: `6`. -/
abbrev gold4K512Rate : ℕ := 6

/-- `block_enc` of the tableau: `4095`. -/
abbrev gold4K512BlockEnc : ℕ := 4095

/-- The opened columns of the tableau: `t = 201`. -/
abbrev gold4K512T : ℕ := 201

/-- The message length of the code: `k = (block_enc + 1) / (2 + rate) = 512`. -/
abbrev gold4K512K : ℕ := (gold4K512BlockEnc + 1) / (2 + gold4K512Rate)

/-- The block length of the code: `N = block_enc − (2k − 1) = 3072`. -/
abbrev gold4K512N : ℕ := gold4K512BlockEnc - (2 * gold4K512K - 1)

/-- The agreement threshold of the line certificate: `A = 1418`. -/
abbrev gold4K512Agree : ℕ := 1418

/-- The exceptional count of the line certificate: `B = 1030262` (`2^19.97`). -/
abbrev gold4K512Exceptions : ℕ := 1030262

/-- **The Ligero numbers of the tableau**: `(rate, t, block_enc) = (6, 201, 4095)`. -/
def gold4K512Shape : Ligero.Relative.Shape := ⟨gold4K512Rate, gold4K512T, gold4K512BlockEnc, 1, gold4K512T⟩

theorem gold4K512K_eq : gold4K512K = 512 := rfl

theorem gold4K512N_eq : gold4K512N = 3072 := rfl

/-- **The line certificate of the code**, at agreement threshold `A = 1418`: the weighted
Johnson certificate `(m, B, H) = (3, 7, 27)` for degree `511` on `3072` points. -/
theorem gold4K512Line {F : Type} [Field F] (C : GordieHowe.RSCode F gold4K512N)
    (hk : C.k = gold4K512K) :
    RSCode.LineCertificate C gold4K512Agree (gold4K512Exceptions : ℕ) :=
  RSCode.lineCertificate_of_weightedJohnson C (D := 511) (m := 3) (B := 7) (H := 27)
    (by unfold ReedSolomon.HiddenDerivative.IsJohnsonWeightedCertificate; decide +kernel) hk
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [ReedSolomon.HiddenDerivative.johnsonWeightedRefinedExceptionCount])

/-- **The code parameters of the tableau with the mask test** (`Ligero.MaskTest.Pieces.Parameters`):
`k ≤ A` and the line certificate `gold4K512Line`. -/
theorem gold4K512MaskTest {F : Type} [Field F] (C : GordieHowe.RSCode F gold4K512N)
    (hk : C.k = gold4K512K) : Ligero.MaskTest.Pieces.Parameters C gold4K512Agree gold4K512Exceptions :=
  ⟨by rw [hk]; decide, gold4K512Line C hk⟩

/-- The round bounds of the tableau (`Ligero.MaskTest.Pieces.bounds`). -/
noncomputable abbrev gold4K512Bounds : Ligero.AgreementThreshold.Bounds :=
  Ligero.MaskTest.Pieces.bounds GoldilocksExt4 gold4K512N gold4K512Agree gold4K512Exceptions 1 gold4K512K
    gold4K512T

/-- The commit round of the tableau: `1030262/(|F| − 1)`, `2^-236.025`. -/
theorem gold4K512Commit_le : gold4K512Bounds.commit ≤ (16484193 : ℝ≥0) / 2 ^ 260 := by
  show (((1030262 : ℕ) : ℝ≥0) / (Fintype.card GoldilocksExt4 - 1)) ^ 1 ≤ _
  rw [pow_one]
  rw [goldilocksExt4_card, pGold]
  exact ratio_pred_le_dyadic (by decide +kernel)

/-- The test round of the tableau with the mask test: `1/|F|`, `2^-256.000`. -/
theorem gold4K512Test_le : gold4K512Bounds.test ≤ (17 : ℝ≥0) / 2 ^ 260 := by
  show (1 : ℝ≥0) / (Fintype.card GoldilocksExt4 : ℝ≥0) ≤ _
  rw [goldilocksExt4_card, pGold]
  exact_mod_cast ratio_le_dyadic (num := 1) (c := 17) (by decide +kernel) (by decide +kernel)

/-- The column round of the tableau with the mask test at `t = 201`, with the joint subfield
term of the prefix-row subfield test: `((1418 − 1)_201 + (2 · 512 − 1)_201)/(3072)_201 +
(512 − 1)_201/(3072)_201`, `2^-236.237`. -/
theorem gold4K512Column_le : gold4K512Bounds.column +
    Ligero.SubfieldTest.jointSubfieldError gold4K512K gold4K512N gold4K512T ≤
      (14239825 : ℝ≥0) / 2 ^ 260 :=
  column_le_dyadic (by decide +kernel) (by decide +kernel)

/-! ### Goldilocks⁴, `(N, k) = (3072, 512)`, `t = 175`, two low-degree repetitions -/

/-- The opened columns of the tableau at two low-degree repetitions: `t = 175`. -/
abbrev gold4K512R2T : ℕ := 175

/-- The low-degree repetitions of the tableau: `2`. -/
abbrev gold4K512R2Reps : ℕ := 2

/-- The agreement threshold of the line certificate: `A = 1257`. -/
abbrev gold4K512R2Agree : ℕ := 1257

/-- The exceptional count of the line certificate: `B = 118174498727` (`2^36.78`). -/
abbrev gold4K512R2Exceptions : ℕ := 118174498727

/-- **The Ligero numbers of the tableau**: `(rate, t, block_enc) = (6, 175, 4095)` at two
low-degree repetitions. -/
def gold4K512R2Shape : Ligero.Relative.Shape :=
  ⟨gold4K512Rate, gold4K512R2T, gold4K512BlockEnc, gold4K512R2Reps, gold4K512R2T⟩

/-- **The line certificate of the code**, at agreement threshold `A = 1257`: the weighted
Johnson certificate `(m, B, H) = (102, 250, 67546)` for degree `511` on `3072` points. -/
theorem gold4K512R2Line {F : Type} [Field F] (C : GordieHowe.RSCode F gold4K512N)
    (hk : C.k = gold4K512K) :
    RSCode.LineCertificate C gold4K512R2Agree (gold4K512R2Exceptions : ℕ) :=
  RSCode.lineCertificate_of_weightedJohnson C (D := 511) (m := 102) (B := 250)
    (H := 67546) (by unfold ReedSolomon.HiddenDerivative.IsJohnsonWeightedCertificate; decide +kernel)
    hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [ReedSolomon.HiddenDerivative.johnsonWeightedRefinedExceptionCount])

/-- **The code parameters of the tableau with the mask test** (`Ligero.MaskTest.Pieces.Parameters`):
`k ≤ A` and the line certificate `gold4K512R2Line`. -/
theorem gold4K512R2MaskTest {F : Type} [Field F] (C : GordieHowe.RSCode F gold4K512N)
    (hk : C.k = gold4K512K) :
    Ligero.MaskTest.Pieces.Parameters C gold4K512R2Agree gold4K512R2Exceptions :=
  ⟨by rw [hk]; decide, gold4K512R2Line C hk⟩

/-- The round bounds of the tableau (`Ligero.MaskTest.Pieces.bounds`). -/
noncomputable abbrev gold4K512R2Bounds : Ligero.AgreementThreshold.Bounds :=
  Ligero.MaskTest.Pieces.bounds GoldilocksExt4 gold4K512N gold4K512R2Agree gold4K512R2Exceptions
    gold4K512R2Reps gold4K512K gold4K512R2T

/-- The commit round of the tableau: `(118174498727/(|F| − 1))^2`, `2^-438.44`. -/
theorem gold4K512R2Commit_le : gold4K512R2Bounds.commit ≤ (1 : ℝ≥0) / 2 ^ 260 := by
  show (((118174498727 : ℕ) : ℝ≥0) / (Fintype.card GoldilocksExt4 - 1)) ^ 2 ≤ _
  rw [goldilocksExt4_card]
  have h := ratio_pred_pow_le_dyadic (num := 118174498727) (q := pGold ^ 4) (c := 1) (e := 260)
    (nrep := 2) (by decide +kernel)
  rwa [Nat.cast_one] at h

/-- The test round of the tableau with the mask test: `1/|F|`, `2^-256.000`. -/
theorem gold4K512R2Test_le : gold4K512R2Bounds.test ≤ (17 : ℝ≥0) / 2 ^ 260 := by
  show (1 : ℝ≥0) / (Fintype.card GoldilocksExt4 : ℝ≥0) ≤ _
  rw [goldilocksExt4_card, pGold]
  exact_mod_cast ratio_le_dyadic (num := 1) (c := 17) (by decide +kernel) (by decide +kernel)

/-- The column round of the tableau with the mask test at `t = 175`, with the joint subfield
term of the prefix-row subfield test: `((1257 − 1)_175 + (2 · 512 − 1)_175)/(3072)_175 +
(512 − 1)_175/(3072)_175`, `2^-236.880`. -/
theorem gold4K512R2Column_le : gold4K512R2Bounds.column +
    Ligero.SubfieldTest.jointSubfieldError gold4K512K gold4K512N gold4K512R2T ≤
      (9117626 : ℝ≥0) / 2 ^ 260 :=
  column_le_dyadic (by decide +kernel) (by decide +kernel)

/-! ### `GF(2^128)`, `(N, k) = (3392, 282)`, `t = 63`, two low-degree repetitions -/

/-- The rate of the tableau: `12`. -/
abbrev gf128K282R2Rate : ℕ := 12

/-- `block_enc` of the tableau: `3955`. -/
abbrev gf128K282R2BlockEnc : ℕ := 3955

/-- The opened columns of the tableau: `t = 63`. -/
abbrev gf128K282R2T : ℕ := 63

/-- The low-degree repetitions of the tableau: `2`. -/
abbrev gf128K282R2Reps : ℕ := 2

/-- The message length of the code: `k = 282`. -/
abbrev gf128K282R2K : ℕ := (gf128K282R2BlockEnc + 1) / (2 + gf128K282R2Rate)

/-- The block length of the code: `N = 3392`. -/
abbrev gf128K282R2N : ℕ := gf128K282R2BlockEnc - (2 * gf128K282R2K - 1)

/-- The agreement threshold of the line certificate: `A = 982`. -/
abbrev gf128K282R2Agree : ℕ := 982

/-- The exceptional count of the line certificate: `B = 41166706213` (`2^35.26`). -/
abbrev gf128K282R2Exceptions : ℕ := 41166706213

/-- **The Ligero numbers of the tableau**: `(rate, t, block_enc) = (12, 63, 3955)` at two
low-degree repetitions. -/
def gf128K282R2Shape : Ligero.Relative.Shape :=
  ⟨gf128K282R2Rate, gf128K282R2T, gf128K282R2BlockEnc, gf128K282R2Reps, gf128K282R2T⟩

theorem gf128K282R2K_eq : gf128K282R2K = 282 := rfl

theorem gf128K282R2N_eq : gf128K282R2N = 3392 := rfl

/-- **The line certificate of the code**, at agreement threshold `A = 982`: the weighted
Johnson certificate `(m, B, H) = (72, 250, 33122)` for degree `281` on `3392` points
(`lib/gordiehowe/compiler/ligero_choice.h`, `best_line_exhaustive`). -/
theorem gf128K282R2Line {F : Type} [Field F] (C : GordieHowe.RSCode F gf128K282R2N)
    (hk : C.k = gf128K282R2K) :
    RSCode.LineCertificate C gf128K282R2Agree (gf128K282R2Exceptions : ℕ) :=
  RSCode.lineCertificate_of_weightedJohnson C (D := 281) (m := 72) (B := 250)
    (H := 33122) (by unfold ReedSolomon.HiddenDerivative.IsJohnsonWeightedCertificate; decide +kernel)
    hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [ReedSolomon.HiddenDerivative.johnsonWeightedRefinedExceptionCount])

/-- **The code parameters of the tableau with the mask test**. -/
theorem gf128K282R2MaskTest {F : Type} [Field F] (C : GordieHowe.RSCode F gf128K282R2N)
    (hk : C.k = gf128K282R2K) :
    Ligero.MaskTest.Pieces.Parameters C gf128K282R2Agree gf128K282R2Exceptions :=
  ⟨by rw [hk]; decide, gf128K282R2Line C hk⟩

/-- The round bounds of the tableau (`Ligero.MaskTest.Pieces.bounds`). -/
noncomputable abbrev gf128K282R2Bounds : Ligero.AgreementThreshold.Bounds :=
  Ligero.MaskTest.Pieces.bounds GF2_128 gf128K282R2N gf128K282R2Agree gf128K282R2Exceptions
    gf128K282R2Reps gf128K282R2K gf128K282R2T

/-- The commit round of the tableau: `(41166706213/(|K| − 1))^2`, `2^-185.48`. -/
theorem gf128K282R2Commit_le : gf128K282R2Bounds.commit ≤ (1 : ℝ≥0) / 2 ^ 140 := by
  show (((41166706213 : ℕ) : ℝ≥0) / (Fintype.card GF2_128 - 1)) ^ 2 ≤ _
  rw [gf2_128_card]
  have h := ratio_pred_pow_le_dyadic (num := 41166706213) (q := 2 ^ 128) (c := 1) (e := 140)
    (nrep := 2) (by decide +kernel)
  rwa [Nat.cast_one] at h

/-- The test round of the tableau with the mask test: `1/|K|`, `2^-128.000`. -/
theorem gf128K282R2Test_le : gf128K282R2Bounds.test ≤ (4096 : ℝ≥0) / 2 ^ 140 := by
  show (1 : ℝ≥0) / (Fintype.card GF2_128 : ℝ≥0) ≤ _
  rw [gf2_128_card]
  exact_mod_cast ratio_le_dyadic (num := 1) (c := 4096) (by decide +kernel) (by decide +kernel)

/-- The column round of the tableau with the mask test at `t = 63`, with the joint subfield
term: `((982 − 1)_63 + (2 · 282 − 1)_63)/(3392)_63 + (282 − 1)_63/(3392)_63`, `2^-114.857`. -/
theorem gf128K282R2Column_le : gf128K282R2Bounds.column +
    Ligero.SubfieldTest.jointSubfieldError gf128K282R2K gf128K282R2N gf128K282R2T ≤
      (37038786 : ℝ≥0) / 2 ^ 140 :=
  column_le_dyadic (by decide +kernel) (by decide +kernel)

/-! ### Goldilocks², `(N, k) = (2560, 512)`, `t = 96`, two low-degree repetitions -/

/-- The rate of the tableau: `5`. -/
abbrev gold2K512R2Rate : ℕ := 5

/-- `block_enc` of the tableau: `3583`. -/
abbrev gold2K512R2BlockEnc : ℕ := 3583

/-- The opened columns of the tableau: `t = 96`. -/
abbrev gold2K512R2T : ℕ := 96

/-- The low-degree repetitions of the tableau: `2`. -/
abbrev gold2K512R2Reps : ℕ := 2

/-- The message length of the code: `k = 512`. -/
abbrev gold2K512R2K : ℕ := (gold2K512R2BlockEnc + 1) / (2 + gold2K512R2Rate)

/-- The block length of the code: `N = 2560`. -/
abbrev gold2K512R2N : ℕ := gold2K512R2BlockEnc - (2 * gold2K512R2K - 1)

/-- The agreement threshold of the line certificate: `A = 1147`. -/
abbrev gold2K512R2Agree : ℕ := 1147

/-- The exceptional count of the line certificate: `B = 101777974921` (`2^36.57`). -/
abbrev gold2K512R2Exceptions : ℕ := 101777974921

/-- **The Ligero numbers of the tableau**: `(rate, t, block_enc) = (5, 96, 3583)` at two
low-degree repetitions. -/
def gold2K512R2Shape : Ligero.Relative.Shape :=
  ⟨gold2K512R2Rate, gold2K512R2T, gold2K512R2BlockEnc, gold2K512R2Reps, gold2K512R2T⟩

theorem gold2K512R2K_eq : gold2K512R2K = 512 := rfl

theorem gold2K512R2N_eq : gold2K512R2N = 2560 := rfl

/-- **The line certificate of the code**, at agreement threshold `A = 1147`: the weighted
Johnson certificate `(m, B, H) = (112, 250, 61988)` for degree `511` on `2560` points
(`lib/gordiehowe/compiler/ligero_choice.h`, `best_line_exhaustive`). -/
theorem gold2K512R2Line {F : Type} [Field F] (C : GordieHowe.RSCode F gold2K512R2N)
    (hk : C.k = gold2K512R2K) :
    RSCode.LineCertificate C gold2K512R2Agree (gold2K512R2Exceptions : ℕ) :=
  RSCode.lineCertificate_of_weightedJohnson C (D := 511) (m := 112) (B := 250)
    (H := 61988) (by unfold ReedSolomon.HiddenDerivative.IsJohnsonWeightedCertificate; decide +kernel)
    hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [ReedSolomon.HiddenDerivative.johnsonWeightedRefinedExceptionCount])

/-- **The code parameters of the tableau with the mask test**. -/
theorem gold2K512R2MaskTest {F : Type} [Field F] (C : GordieHowe.RSCode F gold2K512R2N)
    (hk : C.k = gold2K512R2K) :
    Ligero.MaskTest.Pieces.Parameters C gold2K512R2Agree gold2K512R2Exceptions :=
  ⟨by rw [hk]; decide, gold2K512R2Line C hk⟩

/-- The round bounds of the tableau (`Ligero.MaskTest.Pieces.bounds`). -/
noncomputable abbrev gold2K512R2Bounds : Ligero.AgreementThreshold.Bounds :=
  Ligero.MaskTest.Pieces.bounds GoldilocksExt2 gold2K512R2N gold2K512R2Agree gold2K512R2Exceptions
    gold2K512R2Reps gold2K512R2K gold2K512R2T

/-- The commit round of the tableau: `(101777974921/(|F| − 1))^2`, `2^-182.87`. -/
theorem gold2K512R2Commit_le : gold2K512R2Bounds.commit ≤ (1 : ℝ≥0) / 2 ^ 140 := by
  show (((101777974921 : ℕ) : ℝ≥0) / (Fintype.card GoldilocksExt2 - 1)) ^ 2 ≤ _
  rw [goldilocksExt2_card]
  have h := ratio_pred_pow_le_dyadic (num := 101777974921) (q := pGold ^ 2) (c := 1) (e := 140)
    (nrep := 2) (by decide +kernel)
  rwa [Nat.cast_one] at h

/-- The test round of the tableau with the mask test: `1/|F|`, `2^-128.000`. -/
theorem gold2K512R2Test_le : gold2K512R2Bounds.test ≤ (4097 : ℝ≥0) / 2 ^ 140 := by
  show (1 : ℝ≥0) / (Fintype.card GoldilocksExt2 : ℝ≥0) ≤ _
  rw [goldilocksExt2_card, pGold]
  exact_mod_cast ratio_le_dyadic (num := 1) (c := 4097) (by decide +kernel) (by decide +kernel)

/-- The column round of the tableau with the mask test at `t = 96`, with the joint subfield
term: `((1147 − 1)_96 + (2 · 512 − 1)_96)/(2560)_96 + (512 − 1)_96/(2560)_96`, `2^-114.620`. -/
theorem gold2K512R2Column_le : gold2K512R2Bounds.column +
    Ligero.SubfieldTest.jointSubfieldError gold2K512R2K gold2K512R2N gold2K512R2T ≤
      (43660620 : ℝ≥0) / 2 ^ 140 :=
  column_le_dyadic (by decide +kernel) (by decide +kernel)

/-! ### `GF(2^256)`, `(N, k) = (4069, 339)`, `t = 128`, two low-degree repetitions -/

/-- The rate of the tableau: `12`. -/
abbrev gf256K339R2Rate : ℕ := 12

/-- `block_enc` of the tableau: `4746`. -/
abbrev gf256K339R2BlockEnc : ℕ := 4746

/-- The opened columns of the tableau: `t = 128`. -/
abbrev gf256K339R2T : ℕ := 128

/-- The low-degree repetitions of the tableau: `2`. -/
abbrev gf256K339R2Reps : ℕ := 2

/-- The message length of the code: `k = 339`. -/
abbrev gf256K339R2K : ℕ := (gf256K339R2BlockEnc + 1) / (2 + gf256K339R2Rate)

/-- The block length of the code: `N = 4069`. -/
abbrev gf256K339R2N : ℕ := gf256K339R2BlockEnc - (2 * gf256K339R2K - 1)

/-- The agreement threshold of the line certificate: `A = 1179`. -/
abbrev gf256K339R2Agree : ℕ := 1179

/-- The exceptional count of the line certificate: `B = 108518123392` (`2^36.66`). -/
abbrev gf256K339R2Exceptions : ℕ := 108518123392

/-- **The Ligero numbers of the tableau**: `(rate, t, block_enc) = (12, 128, 4746)` at two
low-degree repetitions. -/
def gf256K339R2Shape : Ligero.Relative.Shape :=
  ⟨gf256K339R2Rate, gf256K339R2T, gf256K339R2BlockEnc, gf256K339R2Reps, gf256K339R2T⟩

theorem gf256K339R2K_eq : gf256K339R2K = 339 := rfl

theorem gf256K339R2N_eq : gf256K339R2N = 4069 := rfl

/-- **The line certificate of the code**, at agreement threshold `A = 1179`: the weighted
Johnson certificate `(m, B, H) = (72, 250, 72597)` for degree `338` on `4069` points
(`lib/gordiehowe/compiler/ligero_choice.h`, `best_line_exhaustive`). -/
theorem gf256K339R2Line {F : Type} [Field F] (C : GordieHowe.RSCode F gf256K339R2N)
    (hk : C.k = gf256K339R2K) :
    RSCode.LineCertificate C gf256K339R2Agree (gf256K339R2Exceptions : ℕ) :=
  RSCode.lineCertificate_of_weightedJohnson C (D := 338) (m := 72) (B := 250)
    (H := 72597) (by unfold ReedSolomon.HiddenDerivative.IsJohnsonWeightedCertificate; decide +kernel)
    hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [ReedSolomon.HiddenDerivative.johnsonWeightedRefinedExceptionCount])

/-- **The code parameters of the tableau with the mask test**. -/
theorem gf256K339R2MaskTest {F : Type} [Field F] (C : GordieHowe.RSCode F gf256K339R2N)
    (hk : C.k = gf256K339R2K) :
    Ligero.MaskTest.Pieces.Parameters C gf256K339R2Agree gf256K339R2Exceptions :=
  ⟨by rw [hk]; decide, gf256K339R2Line C hk⟩

/-- The round bounds of the tableau (`Ligero.MaskTest.Pieces.bounds`). -/
noncomputable abbrev gf256K339R2Bounds : Ligero.AgreementThreshold.Bounds :=
  Ligero.MaskTest.Pieces.bounds GF2_256 gf256K339R2N gf256K339R2Agree gf256K339R2Exceptions
    gf256K339R2Reps gf256K339R2K gf256K339R2T

/-- The commit round of the tableau: `(108518123392/(|K| − 1))^2`, `2^-438.68`. -/
theorem gf256K339R2Commit_le : gf256K339R2Bounds.commit ≤ (1 : ℝ≥0) / 2 ^ 260 := by
  show (((108518123392 : ℕ) : ℝ≥0) / (Fintype.card GF2_256 - 1)) ^ 2 ≤ _
  rw [gf2_256_card]
  have h := ratio_pred_pow_le_dyadic (num := 108518123392) (q := 2 ^ 256) (c := 1) (e := 260)
    (nrep := 2) (by decide +kernel)
  rwa [Nat.cast_one] at h

/-- The test round of the tableau with the mask test: `1/|K|`, `2^-256.000`. -/
theorem gf256K339R2Test_le : gf256K339R2Bounds.test ≤ (16 : ℝ≥0) / 2 ^ 260 := by
  show (1 : ℝ≥0) / (Fintype.card GF2_256 : ℝ≥0) ≤ _
  rw [gf2_256_card]
  exact_mod_cast ratio_le_dyadic (num := 1) (c := 16) (by decide +kernel) (by decide +kernel)

/-- The column round of the tableau with the mask test at `t = 128`, with the joint subfield
term: `((1179 − 1)_128 + (2 · 339 − 1)_128)/(4069)_128 + (339 − 1)_128/(4069)_128`, `2^-236.329`. -/
theorem gf256K339R2Column_le : gf256K339R2Bounds.column +
    Ligero.SubfieldTest.jointSubfieldError gf256K339R2K gf256K339R2N gf256K339R2T ≤
      (13358901 : ℝ≥0) / 2 ^ 260 :=
  column_le_dyadic (by decide +kernel) (by decide +kernel)

end GordieHowe.Tableau
