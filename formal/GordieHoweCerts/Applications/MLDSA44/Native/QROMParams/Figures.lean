-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Configuration.SoundnessBits
public import GordieHoweCerts.Applications.MLDSA44.Native.QROMParams

@[expose] public section

/-!
# The bit-security figures of `MLDSA44.Native.QROMParams`

The bit security of the native ML-DSA-44 proof of possession at the QROM parameters, in the paper's
measure `λ(err) = min over t ≥ 1 of log₂ (t / min(1, err(t)))` (`sec:eval-params`), certified from
the generated figures (`GordieHowe.Generated.MLDSA44.Native.QROMParams.figures`).

Zero knowledge: for every `t ≥ 1` hash queries and `Q ≤ proofQueryCap = 2^64` proof queries, the error `zkError 0` of
`everlasting_zero_knowledge_honest_qrom` is at most `Q · t · 2^-λ`.

Knowledge soundness: for every `t ≥ 1` hash queries, the quantum knowledge error of
`knowledge_soundness_qrom_at` and `soundness_qrom_at` against `t`-query adversaries,
`knowledgeErrorQROM (t + kq)`, satisfies `min(1, err) ≤ t · 2^-λ`. The error is evaluated at `t +
kq`, the adversary's and the verifier's queries, as in the paper's `errks(t)` and in
`analysis/eval_params.py`.

| figure | `λ` |
|---|---|
| everlasting zero knowledge, one proof (`zero_knowledge_bits_qrom`) | `180.11` |
| knowledge soundness and soundness (`soundness_bits_qrom`) | `116.87` |

Each `λ` is rounded down to two decimals. The budgets (`GordieHowe.Configuration.zkBudget`,
`GordieHowe.Configuration.knowledgeBudgetQROM`) are bounded at the figures
(`GordieHowe.Configuration.ofCertified_readsFigures`) by a dyadic ratio `M / 2^E` and compared with
`2^-λ` through `M^100 · 2^(100 λ) ≤ 2^(100 E)`.
-/

namespace GordieHowe.MLDSA44.Native.QROMParams

open GordieHowe.Configuration

-- The budget's exponents (up to `2^990`) exceed `norm_num`'s default evaluation threshold.
set_option exponentiation.threshold 3000 in
/-- **The QROM zero-knowledge budget of `MLDSA44.Native.QROMParams`** is at most `2^-180.11`: at
most `237/2^188` (`zkBudget_le_two_rpow` at the generated figures). -/
theorem zkBudget_le : configuration.zkBudget ≤ (2 : ℝ) ^ (-180.11 : ℝ) :=
  zkBudget_le_two_rpow
    (ofCertified_readsFigures Generated.MLDSA44.Native.QROMParams.figures_eq)
    (M := 237) (E := 188) (e := 18011) (by norm_num) (by norm_num [Nat.choose_two_right, ParamSet.rom, ParamSet.qrom])
    (by decide +kernel)

/-- **The bit security of everlasting zero knowledge of the native ML-DSA-44 proof of possession at
the QROM parameters**: for every `t ≥ 1` hash queries and `Q ≤ proofQueryCap = 2^64` proof queries, the error `zkError 0` of
`everlasting_zero_knowledge_honest_qrom` is at most `Q · t · 2^-180.11`. -/
theorem zero_knowledge_bits_qrom :
    ZKBitSecurityAtLeast ((argument proofSystem).zkError 0) 180.11 :=
  Configuration.ZKBits.zkError_le_bits configuration configurationFacts proofSystem
    zkBudget_le

-- The budget's exponents (up to `2^384`) exceed `norm_num`'s default evaluation threshold.
set_option exponentiation.threshold 400 in
/-- **The quantum knowledge budget of `MLDSA44.Native.QROMParams` below `7487 * 2 ^ 104` queries**
is at most `2^-116.87`: at most `35/2^122` (`knowledgeBudgetQROM_le_two_rpow` at the generated
figures). -/
theorem knowledgeBudgetQROM_le :
    configuration.knowledgeBudgetQROM (7487 * 2 ^ 104) ≤ (2 : ℝ) ^ (-116.87 : ℝ) :=
  knowledgeBudgetQROM_le_two_rpow
    (ofCertified_readsFigures Generated.MLDSA44.Native.QROMParams.figures_eq)
    (M := 35) (E := 122) (e := 11687) (by norm_num) (by norm_num) (by decide +kernel)

/-- **The bit security of knowledge soundness of the native ML-DSA-44 proof of possession at the
QROM parameters**: for every `t ≥ 1` hash queries, the quantum knowledge error of
`knowledge_soundness_qrom_at` and `soundness_qrom_at` against `t`-query adversaries, evaluated at `t
+ kq` as in the paper's `errks(t)` and `analysis/eval_params.py`, satisfies `min(1, err) ≤ t ·
2^-116.87`, so `λ(errks) ≥ 116.87`. -/
theorem soundness_bits_qrom :
    BitSecurityAtLeast extractionErrorQROM 116.87 :=
  SoundnessBits.knowledgeErrorQROM_le_bits configuration configurationFacts (e := 11687)
    (by norm_num) (by decide +kernel) (knowledgeBudgetQROM_le)

end GordieHowe.MLDSA44.Native.QROMParams
