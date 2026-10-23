-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Ligero.LongfellowOrder
public import GordieHowe.Foundations.ToMathlib.NNRealRpow
public import GordieHowe.Foundations.Fields.GF2_128

@[expose] public section

/-!
# Ligero in Longfellow's order of challenges at the parameters of Longfellow version 7

The two Ligero tableaus of Longfellow version 7's mDL proof with one attribute, at rate `1/7` and
`t = 132` queried columns (LF draft-03 §5.1, p. 38: `(p256, 132, 7)` and `(GF(2^128), 132, 7)`),
with untested masks and one low-degree repetition, analysed in Longfellow's order of challenges
(`GordieHowe.Ligero.LongfellowOrder.rbr_knowledge_soundness`):

* the **hash tableau**, `(N, k) = (3230, 461)` over `GF(2^128)`, at agreement threshold
  `A = 1810`: the weighted Johnson certificate `(m, B, H) = (1, 2, 3)` gives the exceptional count
  `22529`; the list size of the interleaved code is `L = 2`, the Johnson agreement of degree
  `2k − 2 = 920` is `a = 1724` with mask list size `l = 646`. The joint round is at most
  `2^-113.46` (`hashJoint_le`) and the column round at most `2^-113.54` (`hashColumn_le`);
* the **signature tableau**, `(N, k) = (3187, 455)` over the P-256 base field (any field with
  `p256` elements), at `A = 1213`: the weighted Johnson certificate `(m, B, H) = (40, 106, 15925)`
  gives the exceptional count `10977760134`; `L = 98`, `a = 1701`, `l = 841`. The joint round is
  at most `2^-222.64` (`sigJoint_le`) and the column round at most `2^-123.12`
  (`sigColumn_le`), set by the mask term `a.descFactorial t / N.descFactorial t`.

Every Ligero round error of a setup at these numbers is therefore at most `2^-113.4` for the hash
tableau (`hash_error_le`) and `2^-123` for the signature tableau (`sig_error_le`).

The numbers are those printed by `experiments/pq-migration/lf-per-round/lf_rbr.py` (`T4 hash1`:
joint 113.46, column 113.55 bits, `A = 1810`; `T3 P256`: joint 222.65, column 123.13 bits,
`A = 1213`), from exact rationals: joint `113.46005`, column `113.5486` (hash), joint `222.6461`,
column `123.1285` (signature). The script's column figure `113.55` is `113.5486` rounded; the
bounds proved here are the exact figures rounded down. Each bound is checked by `decide +kernel`
on naturals (`GordieHowe.ratio_le_two_rpow`: `num^n · 2^e ≤ den^n` for the exponent `−e/n`).
-/

namespace GordieHowe.Ligero.LongfellowOrder.V7

open scoped NNReal

/-- The queried columns of both tableaus: `t = 132` (LF draft-03 §5.1, p. 38). -/
abbrev t : ℕ := 132

/-! ### The hash tableau, `(N, k) = (3230, 461)` over `GF(2^128)` -/

/-- The block length of the hash tableau: `N = 3230`. -/
abbrev hashN : ℕ := 3230

/-- The message length of the hash tableau: `k = 461`. -/
abbrev hashK : ℕ := 461

/-- The agreement threshold of the hash tableau: `A = 1810`. -/
abbrev hashAgree : ℕ := 1810

/-- The exceptional count of the line certificate of the hash tableau: `B = 22529`. -/
abbrev hashExceptions : ℕ := 22529

/-- The mask agreement threshold of the hash tableau: `a = 1724`. -/
abbrev hashMaskAgree : ℕ := 1724

/-- The mask list size of the hash tableau: `l = 646`. -/
abbrev hashMaskList : ℕ := 646

/-- The list size of the interleaved code of the hash tableau at `A = 1810`: `L = 2`. -/
abbrev hashList : ℕ := 2

/-- The mask agreement threshold is the Johnson agreement of degree `2k − 2 = 920`. -/
theorem hashMaskAgree_eq :
    MaskedConstraintList.johnsonAgreement hashN (2 * hashK - 2) = hashMaskAgree := by
  decide +kernel

/-- **The line certificate of the hash code** at `A = 1810`: the weighted Johnson certificate
`(m, B, H) = (1, 2, 3)` for degree `460` on `3230` points, with exceptional count `22529`. -/
theorem hashLine {F : Type} [Field F] (C : GordieHowe.RSCode F hashN) (hk : C.k = hashK) :
    RSCode.LineCertificate C hashAgree (hashExceptions : ℕ) :=
  RSCode.lineCertificate_of_weightedJohnson C (D := 460) (m := 1) (B := 2) (H := 3)
    (by unfold ReedSolomon.HiddenDerivative.IsJohnsonWeightedCertificate; decide +kernel) hk
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [ReedSolomon.HiddenDerivative.johnsonWeightedRefinedExceptionCount])

/-- **The code parameters of the hash tableau** (`LongfellowOrder.Parameters`): `k ≤ A`, the line
certificate `hashLine`, the untested-mask list hypotheses at `a = 1724`, `l = 646`, and the
interleaved list hypotheses at `L = 2`. -/
theorem hashParameters {F : Type} [Field F] (C : GordieHowe.RSCode F hashN) (hk : C.k = hashK) :
    Parameters C hashAgree hashExceptions hashMaskAgree hashMaskList hashList where
  k_le_A := by rw [hk]; decide
  line := hashLine C hk
  list := ⟨by decide, by rw [hk]; decide +kernel, by rw [hk]; decide +kernel⟩
  interleaved := ⟨by decide, by rw [hk]; decide +kernel, by rw [hk]; decide +kernel⟩

/-- The round bounds of the hash tableau (`AgreementThreshold.bounds`). -/
noncomputable abbrev hashBounds : AgreementThreshold.Bounds :=
  AgreementThreshold.bounds GF2_128 hashN hashAgree hashExceptions 1 t hashMaskAgree hashMaskList

/-- **The joint round of the hash tableau**: `22529/(2^128 − 1) + 2 · 646/2^128 ≤ 2^-113.46`
(`113.46005` bits). -/
theorem hashJoint_le : hashBounds.commit + hashList * hashBounds.test ≤ (2 : ℝ≥0) ^ (-113.46 : ℝ) := by
  show (((hashExceptions : ℕ) : ℝ≥0) / (Fintype.card GF2_128 - 1)) ^ 1 +
    ((hashList : ℕ) : ℝ≥0) * (((hashMaskList : ℕ) : ℝ≥0) / Fintype.card GF2_128) ≤ _
  rw [pow_one, gf2_128_card, ratio_pred_add_mul_ratio (by decide)]
  exact ratio_le_two_rpow (n := 50) (e := 5673) (by decide) (by decide) (by norm_num)
    (by decide +kernel)

/-- **The column round of the hash tableau**: `(1809_132 + 1724_132)/3230_132 ≤ 2^-113.54`
(`113.5486` bits). -/
theorem hashColumn_le : hashBounds.column ≤ (2 : ℝ≥0) ^ (-113.54 : ℝ) := by
  show (((hashAgree - 1).descFactorial t : ℝ≥0) + (hashMaskAgree.descFactorial t : ℝ≥0)) /
    (hashN.descFactorial t : ℝ≥0) ≤ _
  rw [← Nat.cast_add]
  exact ratio_le_two_rpow (n := 50) (e := 5677) (by decide +kernel) (by decide) (by norm_num)
    (by decide +kernel)

/-- **Every Ligero round of the hash tableau in Longfellow's order of challenges is at most
`2^-113.4`**: at a setup over `GF(2^128)` with the hash tableau's numbers, the joint round is at
most `2^-113.46` (`hashJoint_le`) and the column round at most `2^-113.54` (`hashColumn_le`). -/
@[headline]
theorem hash_error_le {ι Q Lin : Type} [Fintype ι] [Fintype Q] {R nL nQ : ℕ}
    {C : GordieHowe.RSCode GF2_128 hashN} {P : Tableau.Parameters (R := R) (nQ := nQ) C}
    {products : Routing.ProductLayout ι Q} (S : Setup C P products Lin nL)
    (h : S.Numbers hashAgree hashExceptions 1 t hashMaskAgree hashMaskList hashList)
    (i : (spec GF2_128 hashN R nL nQ C.k S.t S.nrep).ChallengeIdx) :
    error S i ≤ (2 : ℝ≥0) ^ (-113.4 : ℝ) :=
  error_le_of_numbers S h
    (hashJoint_le.trans (two_rpow_le_two_rpow (by norm_num)))
    (hashColumn_le.trans (two_rpow_le_two_rpow (by norm_num))) i

/-! ### The signature tableau, `(N, k) = (3187, 455)` over the P-256 base field -/

/-- The P-256 base-field prime `p256 = 2^256 − 2^224 + 2^192 + 2^96 − 1`. -/
abbrev p256 : ℕ := 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1

/-- The block length of the signature tableau: `N = 3187`. -/
abbrev sigN : ℕ := 3187

/-- The message length of the signature tableau: `k = 455`. -/
abbrev sigK : ℕ := 455

/-- The agreement threshold of the signature tableau: `A = 1213`. -/
abbrev sigAgree : ℕ := 1213

/-- The exceptional count of the line certificate of the signature tableau: `B = 10977760134`. -/
abbrev sigExceptions : ℕ := 10977760134

/-- The mask agreement threshold of the signature tableau: `a = 1701`. -/
abbrev sigMaskAgree : ℕ := 1701

/-- The mask list size of the signature tableau: `l = 841`. -/
abbrev sigMaskList : ℕ := 841

/-- The list size of the interleaved code of the signature tableau at `A = 1213`: `L = 98`. -/
abbrev sigList : ℕ := 98

/-- The mask agreement threshold is the Johnson agreement of degree `2k − 2 = 908`. -/
theorem sigMaskAgree_eq :
    MaskedConstraintList.johnsonAgreement sigN (2 * sigK - 2) = sigMaskAgree := by
  decide +kernel

/-- **The line certificate of the signature code** at `A = 1213`: the weighted Johnson certificate
`(m, B, H) = (40, 106, 15925)` for degree `454` on `3187` points, with exceptional count
`10977760134`. -/
theorem sigLine {F : Type} [Field F] (C : GordieHowe.RSCode F sigN) (hk : C.k = sigK) :
    RSCode.LineCertificate C sigAgree (sigExceptions : ℕ) :=
  RSCode.lineCertificate_of_weightedJohnson C (D := 454) (m := 40) (B := 106)
    (H := 15925)
    (by unfold ReedSolomon.HiddenDerivative.IsJohnsonWeightedCertificate; decide +kernel) hk
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [ReedSolomon.HiddenDerivative.johnsonWeightedRefinedExceptionCount])

/-- **The code parameters of the signature tableau** (`LongfellowOrder.Parameters`): `k ≤ A`, the line
certificate `sigLine`, the untested-mask list hypotheses at `a = 1701`, `l = 841`, and the
interleaved list hypotheses at `L = 98`. -/
theorem sigParameters {F : Type} [Field F] (C : GordieHowe.RSCode F sigN) (hk : C.k = sigK) :
    Parameters C sigAgree sigExceptions sigMaskAgree sigMaskList sigList where
  k_le_A := by rw [hk]; decide
  line := sigLine C hk
  list := ⟨by decide, by rw [hk]; decide +kernel, by rw [hk]; decide +kernel⟩
  interleaved := ⟨by decide, by rw [hk]; decide +kernel, by rw [hk]; decide +kernel⟩

/-- The round bounds of the signature tableau over a field `F` (`AgreementThreshold.bounds`). -/
noncomputable abbrev sigBounds (F : Type) [Fintype F] : AgreementThreshold.Bounds :=
  AgreementThreshold.bounds F sigN sigAgree sigExceptions 1 t sigMaskAgree sigMaskList

/-- **The joint round of the signature tableau** over a field of `p256` elements:
`10977760134/(p256 − 1) + 98 · 841/p256 ≤ 2^-222.64` (`222.6461` bits). -/
theorem sigJoint_le {F : Type} [Fintype F] (hF : Fintype.card F = p256) :
    (sigBounds F).commit + sigList * (sigBounds F).test ≤ (2 : ℝ≥0) ^ (-222.64 : ℝ) := by
  show (((sigExceptions : ℕ) : ℝ≥0) / (Fintype.card F - 1)) ^ 1 +
    ((sigList : ℕ) : ℝ≥0) * (((sigMaskList : ℕ) : ℝ≥0) / Fintype.card F) ≤ _
  rw [pow_one, hF, ratio_pred_add_mul_ratio (by decide)]
  exact ratio_le_two_rpow (n := 25) (e := 5566) (by decide +kernel) (by decide) (by norm_num)
    (by decide +kernel)

/-- **The column round of the signature tableau**: `(1212_132 + 1701_132)/3187_132 ≤ 2^-123.12`
(`123.1285` bits). -/
theorem sigColumn_le (F : Type) [Fintype F] : (sigBounds F).column ≤ (2 : ℝ≥0) ^ (-123.12 : ℝ) := by
  show (((sigAgree - 1).descFactorial t : ℝ≥0) + (sigMaskAgree.descFactorial t : ℝ≥0)) /
    (sigN.descFactorial t : ℝ≥0) ≤ _
  rw [← Nat.cast_add]
  exact ratio_le_two_rpow (n := 25) (e := 3078) (by decide +kernel) (by decide) (by norm_num)
    (by decide +kernel)

/-- **Every Ligero round of the signature tableau in Longfellow's order of challenges is at most
`2^-123`**: at a setup over a field of `p256` elements with the signature tableau's numbers, the
joint round is at most `2^-222.64` (`sigJoint_le`) and the column round at most `2^-123.12`
(`sigColumn_le`). -/
@[headline]
theorem sig_error_le {F ι Q Lin : Type} [Field F] [Fintype F] [Fintype ι] [Fintype Q]
    (hF : Fintype.card F = p256) {R nL nQ : ℕ} {C : GordieHowe.RSCode F sigN}
    {P : Tableau.Parameters (R := R) (nQ := nQ) C} {products : Routing.ProductLayout ι Q}
    (S : Setup C P products Lin nL)
    (h : S.Numbers sigAgree sigExceptions 1 t sigMaskAgree sigMaskList sigList)
    (i : (spec F sigN R nL nQ C.k S.t S.nrep).ChallengeIdx) :
    error S i ≤ (2 : ℝ≥0) ^ (-123 : ℝ) :=
  error_le_of_numbers S h
    ((sigJoint_le hF).trans (two_rpow_le_two_rpow (by norm_num)))
    ((sigColumn_le F).trans (two_rpow_le_two_rpow (by norm_num))) i

end GordieHowe.Ligero.LongfellowOrder.V7
