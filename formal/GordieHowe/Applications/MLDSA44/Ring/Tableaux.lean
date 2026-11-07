-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.NNRealDyadic
public import GordieHowe.ProofSystem.Ligero.MaskTest.Pieces
public import GordieHowe.ProofSystem.Ligero.RelativeLayout
public import GordieHowe.ProofSystem.Ligero.MaskRow.Layout
public import GordieHowe.ProofSystem.Ligero.SubfieldTest
public import GordieHowe.ProofSystem.Program.FieldPacking
public import GordieHowe.Foundations.Fields.GoldilocksQuartic
public import GordieHowe.Foundations.Fields.GF2_128

@[expose] public section

/-!
# Ligero tableaus of the ML-DSA-44 rings

Ligero at an agreement threshold, with the mask test, over a relatively packed commitment, at the
two tableaus of the compiled ML-DSA-44 rings (`GordieHoweCerts/Generated/MLDSA44/Ring/`) that no
earlier configuration uses (the rings' other domains reuse `Tableau.gold2K512R2…` and
`Tableau.gf256K339R2…`, `GordieHowe/Applications/Shared/Tableaux.lean`):

* **`GF(2^128)` with `k = 265` at two low-degree repetitions** (`gf128K265R2…`): `(rate,
  block_enc) = (12, 3722)`, `(N, k) = (3193, 265)`, `t = 63`, `nrep = 2`, the compiler's choice for
  domain H of `MLDSA44.Ring.Native.ROMParams` and `MLDSA44.Ring.Carrier.ROMParams` (the same
  export), at agreement threshold `A = 923`;
* **Goldilocks⁴ with `k = 1024`** (`gold4K1024…`): `(rate, block_enc) = (6, 8191)`, `(N, k) =
  (6144, 1024)`, `t = 214`, one low-degree repetition, the compiler's choice for domain A of
  `MLDSA44.Ring.Carrier.QROMParams`, at agreement threshold `A = 2918`.

The agreement thresholds and the weighted Johnson certificates are the ones the C++ compiler
chooses for these programs (`lib/gordiehowe/compiler/ligero_choice.h`, `best_line_exhaustive`,
through `choose_ligero_half`; printed by the compile report of
`lib/gordiehowe/examples/rings/mldsa_ring_bench.cc report`, ring size `64`). The code is
`k = (block_enc + 1) / (2 + rate)` (`lib/ligero/ligero_param.h:275`) and
`N = block_enc − (2k − 1)` (`lib/ligero/ligero_param.h:303`, `:313`). The round errors are the
certificates' fractions (`GordieHowe.RealizedProgram.FieldRoundsLe.of_ok`).

The certified shapes (`GordieHowe.RealizedProgram.LigeroCert`) are `gf128K265R2Cert` and
`gold4K1024Cert`.
-/

namespace GordieHowe.Tableau

open scoped NNReal

/-! ### `GF(2^128)`, `(N, k) = (3193, 265)`, `t = 63`, two low-degree repetitions -/

/-- The rate of the tableau: `12`. -/
abbrev gf128K265R2Rate : ℕ := 12

/-- `block_enc` of the tableau: `3722`. -/
abbrev gf128K265R2BlockEnc : ℕ := 3722

/-- The opened columns of the tableau: `t = 63`. -/
abbrev gf128K265R2T : ℕ := 63

/-- The low-degree repetitions of the tableau: `2`. -/
abbrev gf128K265R2Reps : ℕ := 2

/-- The message length of the code: `k = 265`. -/
abbrev gf128K265R2K : ℕ := (gf128K265R2BlockEnc + 1) / (2 + gf128K265R2Rate)

/-- The block length of the code: `N = 3193`. -/
abbrev gf128K265R2N : ℕ := gf128K265R2BlockEnc - (2 * gf128K265R2K - 1)

/-- The agreement threshold of the line certificate: `A = 923`, the C++ compiler's choice. -/
abbrev gf128K265R2Agree : ℕ := 923

/-- The exceptional count of the line certificate: `B = 94114354793` (`2^36.45`). -/
abbrev gf128K265R2Exceptions : ℕ := 94114354793

/-- **The Ligero numbers of the tableau**: `(rate, t, block_enc) = (12, 63, 3722)` at two
low-degree repetitions. -/
def gf128K265R2Shape : Ligero.Relative.Shape :=
  ⟨gf128K265R2Rate, gf128K265R2T, gf128K265R2BlockEnc, gf128K265R2Reps, gf128K265R2T⟩

theorem gf128K265R2K_eq : gf128K265R2K = 265 := rfl

theorem gf128K265R2N_eq : gf128K265R2N = 3193 := rfl

/-- **The line certificate of the code**, at agreement threshold `A = 923`: the weighted
Johnson certificate `(m, B, H) = (72, 250, 80486)` for degree `264` on `3193` points
(`lib/gordiehowe/compiler/ligero_choice.h`, `best_line_exhaustive`). -/
theorem gf128K265R2Line {F : Type} [Field F] (C : GordieHowe.RSCode F gf128K265R2N)
    (hk : C.k = gf128K265R2K) :
    RSCode.LineCertificate C gf128K265R2Agree (gf128K265R2Exceptions : ℕ) :=
  RSCode.lineCertificate_of_weightedJohnson C (D := 264) (m := 72) (B := 250)
    (H := 80486) (by unfold ReedSolomon.HiddenDerivative.IsJohnsonWeightedCertificate; decide +kernel)
    hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [ReedSolomon.HiddenDerivative.johnsonWeightedRefinedExceptionCount])

/-- **The code parameters of the tableau with the mask test**. -/
theorem gf128K265R2MaskTest {F : Type} [Field F] (C : GordieHowe.RSCode F gf128K265R2N)
    (hk : C.k = gf128K265R2K) :
    Ligero.MaskTest.Pieces.Parameters C gf128K265R2Agree gf128K265R2Exceptions :=
  ⟨by rw [hk]; decide, gf128K265R2Line C hk⟩

/-! ### Goldilocks⁴, `(N, k) = (6144, 1024)`, `t = 214` -/

/-- The rate of the tableau: `6`. -/
abbrev gold4K1024Rate : ℕ := 6

/-- `block_enc` of the tableau: `8191`. -/
abbrev gold4K1024BlockEnc : ℕ := 8191

/-- The opened columns of the tableau: `t = 214`. -/
abbrev gold4K1024T : ℕ := 214

/-- The message length of the code: `k = 1024`. -/
abbrev gold4K1024K : ℕ := (gold4K1024BlockEnc + 1) / (2 + gold4K1024Rate)

/-- The block length of the code: `N = 6144`. -/
abbrev gold4K1024N : ℕ := gold4K1024BlockEnc - (2 * gold4K1024K - 1)

/-- The agreement threshold of the line certificate: `A = 2918`, the C++ compiler's choice. -/
abbrev gold4K1024Agree : ℕ := 2918

/-- The exceptional count of the line certificate: `B = 1020592` (`2^19.96`). -/
abbrev gold4K1024Exceptions : ℕ := 1020592

/-- **The Ligero numbers of the tableau**: `(rate, t, block_enc) = (6, 214, 8191)`. -/
def gold4K1024Shape : Ligero.Relative.Shape :=
  ⟨gold4K1024Rate, gold4K1024T, gold4K1024BlockEnc, 1, gold4K1024T⟩

theorem gold4K1024K_eq : gold4K1024K = 1024 := rfl

theorem gold4K1024N_eq : gold4K1024N = 6144 := rfl

/-- **The line certificate of the code**, at agreement threshold `A = 2918`: the weighted
Johnson certificate `(m, B, H) = (2, 5, 20)` for degree `1023` on `6144` points
(`lib/gordiehowe/compiler/ligero_choice.h`, `best_line_exhaustive`). -/
theorem gold4K1024Line {F : Type} [Field F] (C : GordieHowe.RSCode F gold4K1024N)
    (hk : C.k = gold4K1024K) :
    RSCode.LineCertificate C gold4K1024Agree (gold4K1024Exceptions : ℕ) :=
  RSCode.lineCertificate_of_weightedJohnson C (D := 1023) (m := 2) (B := 5) (H := 20)
    (by unfold ReedSolomon.HiddenDerivative.IsJohnsonWeightedCertificate; decide +kernel) hk
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [ReedSolomon.HiddenDerivative.johnsonWeightedRefinedExceptionCount])

/-- **The code parameters of the tableau with the mask test** (`Ligero.MaskTest.Pieces.Parameters`):
`k ≤ A` and the line certificate `gold4K1024Line`. -/
theorem gold4K1024MaskTest {F : Type} [Field F] (C : GordieHowe.RSCode F gold4K1024N)
    (hk : C.k = gold4K1024K) :
    Ligero.MaskTest.Pieces.Parameters C gold4K1024Agree gold4K1024Exceptions :=
  ⟨by rw [hk]; decide, gold4K1024Line C hk⟩

end GordieHowe.Tableau

namespace GordieHowe.RealizedProgram

/-- **The `GF(2^128)` tableau** `(12, 63, 3722)` at two low-degree repetitions, the mask test at
`A = 923` with `94114354793` exceptional challenges (`Tableau.gf128K265R2MaskTest`). -/
def gf128K265R2Cert : LigeroCert where
  Sh := Tableau.gf128K265R2Shape
  agree := Tableau.gf128K265R2Agree
  exceptions := Tableau.gf128K265R2Exceptions
  line C hk := Tableau.gf128K265R2MaskTest C hk
  masking := .split

/-- **The Goldilocks⁴ tableau** `(6, 214, 8191)`, the mask test at `A = 2918` with `1020592`
exceptional challenges (`Tableau.gold4K1024MaskTest`). -/
def gold4K1024Cert : LigeroCert where
  Sh := Tableau.gold4K1024Shape
  agree := Tableau.gold4K1024Agree
  exceptions := Tableau.gold4K1024Exceptions
  line C hk := Tableau.gold4K1024MaskTest C hk
  masking := .split

end GordieHowe.RealizedProgram
