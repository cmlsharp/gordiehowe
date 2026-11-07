-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Configuration.SoundnessBits
public import GordieHoweCerts.Applications.MLDSA44.Ring.Carrier.QROMParams

@[expose] public section

/-!
# The bit-security figures of `MLDSA44.Ring.Carrier.QROMParams`

The bit security of the carrier ML-DSA-44 ring signature at the QROM parameters, in the paper's
measure `λ(err) = min over t ≥ 1 of log₂ (t / min(1, err(t)))` (`sec:eval-params`), certified from
the generated figures (`GordieHowe.Generated.MLDSA44.Ring.Carrier.QROMParams.figures`).

Zero knowledge: for every `t ≥ 1` hash queries and `Q ≤ 2^64` proof queries, the error of
`everlasting_zero_knowledge_qrom` is at most `Q · t · 2^-λ`.

Knowledge soundness: for every `t ≥ 1` hash queries, the quantum knowledge error of
`knowledge_soundness_qrom_at` and `soundness_qrom_at` against `t`-query adversaries,
`knowledgeErrorQROM (t + kq)`, satisfies `min(1, err) ≤ t · 2^-λ`. The error is evaluated at `t +
kq`, the adversary's and the verifier's queries, as in the paper's `errks(t)` and in
`analysis/eval_params.py`.

| figure | `λ` |
|---|---|
| everlasting zero knowledge, one proof (`zero_knowledge_bits_qrom`) | `179.68` |
| knowledge soundness and soundness (`soundness_bits_qrom`) | `116.72` |

Each `λ` is rounded down to two decimals. The budgets (`GordieHowe.Configuration.zkBudget`,
`GordieHowe.Configuration.knowledgeBudgetQROM`) are bounded at the figures
(`GordieHowe.Configuration.ofCertifiedWith_readsFigures`) by a dyadic ratio `M / 2^E` and compared
with `2^-λ` through `M^100 · 2^(100 λ) ≤ 2^(100 E)`.
-/

namespace GordieHowe.MLDSA44.Ring.Carrier.QROMParams

open GordieHowe.Configuration

-- The budget's exponents (up to `2^940`) exceed `norm_num`'s default evaluation threshold.
set_option exponentiation.threshold 3000 in
/-- **The QROM zero-knowledge budget of `MLDSA44.Ring.Carrier.QROMParams`** is at most `2^-179.68`:
at most `639/2^189` (`zkBudget_le_two_rpow` at the generated figures). -/
theorem zkBudget_le : configuration.zkBudget ≤ (2 : ℝ) ^ (-179.68 : ℝ) :=
  zkBudget_le_two_rpow
    (ofCertifiedWith_readsFigures Generated.MLDSA44.Ring.Carrier.QROMParams.figures_eq)
    (M := 639) (E := 189) (e := 17968) (by norm_num) (by norm_num [Nat.choose_two_right])
    (by decide +kernel)

/-- **The bit security of everlasting zero knowledge of the carrier ML-DSA-44 ring signature at the
QROM parameters**: for every `t ≥ 1` hash queries and `Q ≤ 2^64` proof queries, the error of
`everlasting_zero_knowledge_qrom` is at most `Q · t · 2^-179.68`. -/
@[headline]
theorem zero_knowledge_bits_qrom {t Q : ℕ} (ht : 1 ≤ t) (hQ : Q ≤ 2 ^ 64) :
    (Configuration.Common.setting configuration configurationFacts proofSystem).model.zkError 0 t Q ≤
      Q * t * (2 : ℝ) ^ (-179.68 : ℝ) :=
  Configuration.ZKBits.zkError_le_bits configuration configurationFacts proofSystem
    zkBudget_le ht hQ

-- The budget's exponents (up to `2^384`) exceed `norm_num`'s default evaluation threshold.
set_option exponentiation.threshold 400 in
/-- **The quantum knowledge budget of `MLDSA44.Ring.Carrier.QROMParams` below `6747 * 2 ^ 104`
queries** is at most `2^-116.72`: at most `77/2^123` (`knowledgeBudgetQROM_le_two_rpow` at the
generated figures). -/
theorem knowledgeBudgetQROM_le :
    configuration.knowledgeBudgetQROM (6747 * 2 ^ 104) ≤ (2 : ℝ) ^ (-116.72 : ℝ) :=
  knowledgeBudgetQROM_le_two_rpow
    (ofCertifiedWith_readsFigures Generated.MLDSA44.Ring.Carrier.QROMParams.figures_eq)
    (M := 77) (E := 123) (e := 11672) (by norm_num) (by norm_num) (by decide +kernel)

/-- **The bit security of knowledge soundness of the carrier ML-DSA-44 ring signature at the QROM
parameters**: for every `t ≥ 1` hash queries, the quantum knowledge error of
`knowledge_soundness_qrom_at` and `soundness_qrom_at` against `t`-query adversaries, evaluated at `t
+ kq` as in the paper's `errks(t)` and `analysis/eval_params.py`, satisfies `min(1, err) ≤ t ·
2^-116.72`, so `λ(errks) ≥ 116.72`. -/
@[headline]
theorem soundness_bits_qrom {t : ℕ} (ht : 1 ≤ t) :
    (min 1 (Configuration.Common.knowledgeErrorQROM configuration configurationFacts
      (t + configuration.kq))).toReal ≤ t * (2 : ℝ) ^ (-116.72 : ℝ) :=
  SoundnessBits.knowledgeErrorQROM_le_bits configuration configurationFacts (e := 11672)
    (by norm_num) (by decide +kernel) (knowledgeBudgetQROM_le) ht

end GordieHowe.MLDSA44.Ring.Carrier.QROMParams
