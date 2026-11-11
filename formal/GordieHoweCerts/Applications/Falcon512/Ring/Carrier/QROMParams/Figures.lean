-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Configuration.SoundnessBits
public import GordieHoweCerts.Applications.Falcon512.Ring.Carrier.QROMParams

@[expose] public section

/-!
# The bit-security figures of `Falcon512.Ring.Carrier.QROMParams`

The bit security of the carrier Falcon-512 ring signature at the QROM parameters, in the paper's
measure `λ(err) = min over t ≥ 1 of log₂ (t / min(1, err(t)))` (`sec:eval-params`), certified from
the generated figures (`GordieHowe.Generated.Falcon512.Ring.Carrier.QROMParams.figures`).

Zero knowledge: for every `t ≥ 1` hash queries and `Q ≤ proofQueryCap = 2^64` proof queries, the error `zkError 0` of
`everlasting_zero_knowledge_honest_qrom` is at most `Q · t · 2^-λ`.

Knowledge soundness: for every `t ≥ 1` hash queries, the quantum knowledge error of
`knowledge_soundness_qrom_at` and `soundness_qrom_at` against `t`-query adversaries,
`knowledgeErrorQROM (t + kq)`, satisfies `min(1, err) ≤ t · 2^-λ`. The error is evaluated at `t +
kq`, the adversary's and the verifier's queries, as in the paper's `errks(t)` and in
`analysis/eval_params.py`.

| figure | `λ` |
|---|---|
| everlasting zero knowledge, one proof (`zero_knowledge_bits_qrom`) | `181.41` |
| knowledge soundness and soundness (`soundness_bits_qrom`) | `116.72` |

Each `λ` is rounded down to two decimals. The budgets (`GordieHowe.Configuration.zkBudget`,
`GordieHowe.Configuration.knowledgeBudgetQROM`) are bounded at the figures
(`GordieHowe.Configuration.ofCertifiedWith_readsFigures`) by a dyadic ratio `M / 2^E` and compared
with `2^-λ` through `M^100 · 2^(100 λ) ≤ 2^(100 E)`.
-/

namespace GordieHowe.Falcon512.Ring.Carrier.QROMParams

open GordieHowe.Configuration

-- The budget's exponents (up to `2^3700`) exceed `norm_num`'s default evaluation threshold.
set_option exponentiation.threshold 3800 in
/-- **The QROM zero-knowledge budget of `Falcon512.Ring.Carrier.QROMParams`** is at most
`2^-181.41`: at most `1541/2^192` (`zkBudget_le_two_rpow` at the generated figures). -/
theorem zkBudget_le (G : Falcon512.Signer 32) :
    (configuration G).zkBudget ≤ (2 : ℝ) ^ (-181.41 : ℝ) :=
  zkBudget_le_two_rpow
    (ofCertifiedWith_readsFigures Generated.Falcon512.Ring.Carrier.QROMParams.figures_eq)
    (M := 1541) (E := 192) (e := 18141) (by norm_num) (by norm_num [Nat.choose_two_right, ParamSet.rom, ParamSet.qrom])
    (by decide +kernel)

/-- **The bit security of everlasting zero knowledge of the carrier Falcon-512 ring signature at the
QROM parameters**: for every `t ≥ 1` hash queries and `Q ≤ proofQueryCap = 2^64` proof queries, the error `zkError 0` of
`everlasting_zero_knowledge_honest_qrom` is at most `Q · t · 2^-181.41`. -/
theorem zero_knowledge_bits_qrom (G : Falcon512.Signer 32) :
    ZKBitSecurityAtLeast ((argument G proofSystem).zkError 0) 181.41 :=
  Configuration.ZKBits.zkError_le_bits (configuration G) (configurationFacts G) proofSystem
    (zkBudget_le G)

-- The budget's exponents (up to `2^384`) exceed `norm_num`'s default evaluation threshold.
set_option exponentiation.threshold 400 in
/-- **The quantum knowledge budget of `Falcon512.Ring.Carrier.QROMParams` below `6747 * 2 ^ 104`
queries** is at most `2^-116.72`: at most `1243/2^127` (`knowledgeBudgetQROM_le_two_rpow` at the
generated figures). -/
theorem knowledgeBudgetQROM_le (G : Falcon512.Signer 32) :
    (configuration G).knowledgeBudgetQROM (6747 * 2 ^ 104) ≤ (2 : ℝ) ^ (-116.72 : ℝ) :=
  knowledgeBudgetQROM_le_two_rpow
    (ofCertifiedWith_readsFigures Generated.Falcon512.Ring.Carrier.QROMParams.figures_eq)
    (M := 1243) (E := 127) (e := 11672) (by norm_num) (by norm_num) (by decide +kernel)

/-- **The bit security of knowledge soundness of the carrier Falcon-512 ring signature at the QROM
parameters**: for every `t ≥ 1` hash queries, the quantum knowledge error of
`knowledge_soundness_qrom_at` and `soundness_qrom_at` against `t`-query adversaries, evaluated at `t
+ kq` as in the paper's `errks(t)` and `analysis/eval_params.py`, satisfies `min(1, err) ≤ t ·
2^-116.72`, so `λ(errks) ≥ 116.72`. -/
theorem soundness_bits_qrom (G : Falcon512.Signer 32) :
    BitSecurityAtLeast (extractionErrorQROM G) 116.72 :=
  SoundnessBits.knowledgeErrorQROM_le_bits (configuration G) (configurationFacts G) (e := 11672)
    (by norm_num) (by decide +kernel) (knowledgeBudgetQROM_le G)

end GordieHowe.Falcon512.Ring.Carrier.QROMParams
