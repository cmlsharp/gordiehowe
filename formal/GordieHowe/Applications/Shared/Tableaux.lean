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
  domain H of `MLDSA44.Native.ROMParams` and `MLDSA44.Emulated.ROMParams` (the same export);
* **`GF(2^128)` with `k = 300` at two low-degree repetitions** (`gf128K300R2…`): `(rate,
  block_enc) = (12, 4203)`, `(N, k) = (3604, 300)`, `t = 63`, `nrep = 2`, the compiler's choice for
  domain H of `Falcon512.Native.ROMParams` and `Falcon512.Emulated.ROMParams` (the same export);
* **Goldilocks² with `k = 512` at two low-degree repetitions** (`gold2K512R2…`): `(rate,
  block_enc) = (5, 3583)`, `(N, k) = (2560, 512)`, `t = 96`, `nrep = 2`, the compiler's choice for
  domain A of `MLDSA44.Emulated.ROMParams` (the same export) and `Falcon512.Ring.Carrier.ROMParams` (at
  `5d775ae1`);
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
the line certificate's at threshold `A` (checked by `decide`). The round errors are the certificates' fractions
(`GordieHowe.RealizedProgram.FieldRoundsLe.of_ok`), checked once per program in its generated module
`Figures`. A configuration's setting uses these
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

/-! ### `GF(2^128)`, `(N, k) = (3604, 300)`, `t = 63`, two low-degree repetitions -/

/-- The rate of the tableau: `12`. -/
abbrev gf128K300R2Rate : ℕ := 12

/-- `block_enc` of the tableau: `4203`. -/
abbrev gf128K300R2BlockEnc : ℕ := 4203

/-- The opened columns of the tableau: `t = 63`. -/
abbrev gf128K300R2T : ℕ := 63

/-- The low-degree repetitions of the tableau: `2`. -/
abbrev gf128K300R2Reps : ℕ := 2

/-- The message length of the code: `k = 300`. -/
abbrev gf128K300R2K : ℕ := (gf128K300R2BlockEnc + 1) / (2 + gf128K300R2Rate)

/-- The block length of the code: `N = 3604`. -/
abbrev gf128K300R2N : ℕ := gf128K300R2BlockEnc - (2 * gf128K300R2K - 1)

/-- The agreement threshold of the line certificate: `A = 1044`. -/
abbrev gf128K300R2Agree : ℕ := 1044

/-- The exceptional count of the line certificate: `B = 50940304454` (`2^35.56`). -/
abbrev gf128K300R2Exceptions : ℕ := 50940304454

/-- **The Ligero numbers of the tableau**: `(rate, t, block_enc) = (12, 63, 4203)` at two
low-degree repetitions. -/
def gf128K300R2Shape : Ligero.Relative.Shape :=
  ⟨gf128K300R2Rate, gf128K300R2T, gf128K300R2BlockEnc, gf128K300R2Reps, gf128K300R2T⟩

theorem gf128K300R2K_eq : gf128K300R2K = 300 := rfl

theorem gf128K300R2N_eq : gf128K300R2N = 3604 := rfl

/-- **The line certificate of the code**, at agreement threshold `A = 1044`: the weighted
Johnson certificate `(m, B, H) = (72, 250, 38530)` for degree `299` on `3604` points
(`lib/gordiehowe/compiler/ligero_choice.h`, `best_line_exhaustive`). -/
theorem gf128K300R2Line {F : Type} [Field F] (C : GordieHowe.RSCode F gf128K300R2N)
    (hk : C.k = gf128K300R2K) :
    RSCode.LineCertificate C gf128K300R2Agree (gf128K300R2Exceptions : ℕ) :=
  RSCode.lineCertificate_of_weightedJohnson C (D := 299) (m := 72) (B := 250)
    (H := 38530) (by unfold ReedSolomon.HiddenDerivative.IsJohnsonWeightedCertificate; decide +kernel)
    hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [ReedSolomon.HiddenDerivative.johnsonWeightedRefinedExceptionCount])

/-- **The code parameters of the tableau with the mask test**. -/
theorem gf128K300R2MaskTest {F : Type} [Field F] (C : GordieHowe.RSCode F gf128K300R2N)
    (hk : C.k = gf128K300R2K) :
    Ligero.MaskTest.Pieces.Parameters C gf128K300R2Agree gf128K300R2Exceptions :=
  ⟨by rw [hk]; decide, gf128K300R2Line C hk⟩

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

end GordieHowe.Tableau
