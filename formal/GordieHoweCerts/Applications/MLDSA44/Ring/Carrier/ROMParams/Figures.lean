-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Configuration.SoundnessBits
public import GordieHoweCerts.Applications.MLDSA44.Ring.Carrier.ROMParams

@[expose] public section

/-!
# The bit-security figures of `MLDSA44.Ring.Carrier.ROMParams`

The bit security of the carrier ML-DSA-44 ring signature at the ROM parameters, in the paper's
measure `λ(err) = min over t ≥ 1 of log₂ (t / min(1, err(t)))` (`sec:eval-params`), certified from
the generated figures (`GordieHowe.Generated.MLDSA44.Ring.Carrier.ROMParams.figures`).

Zero knowledge: for every `t ≥ 1` hash queries and `Q ≤ 2^64` proof queries, the error of
`everlasting_zero_knowledge_rom` is at most `Q · t · 2^-λ`.

Knowledge soundness: for every `t ≥ 1` hash queries, the classical knowledge error of
`knowledge_soundness_rom_at` and `soundness_rom_at` against `t`-query adversaries,
`knowledgeErrorROM (t + kq)`, satisfies `min(1, err) ≤ t · 2^-λ`. The error is evaluated at `t +
kq`, the adversary's and the verifier's queries, as in the paper's `errks^C(t)` and in
`analysis/eval_params.py`.

| figure | `λ` |
|---|---|
| everlasting zero knowledge, one proof (`zero_knowledge_bits_rom`) | `116.50` |
| knowledge soundness and soundness (`soundness_bits_rom`) | `101.34` |

Each `λ` is rounded down to two decimals. The budgets (`GordieHowe.Configuration.zkBudgetROM`,
`GordieHowe.Configuration.knowledgeBudgetROM`) are bounded at the figures
(`GordieHowe.Configuration.ofCertifiedWith_readsFigures`) by a dyadic ratio `M / 2^E` and compared
with `2^-λ` through `M^100 · 2^(100 λ) ≤ 2^(100 E)`.
-/

namespace GordieHowe.MLDSA44.Ring.Carrier.ROMParams

open GordieHowe.Configuration

-- The budget's exponents (up to `2^2780`) exceed `norm_num`'s default evaluation threshold.
set_option exponentiation.threshold 3000 in
/-- **The ROM zero-knowledge budget of `MLDSA44.Ring.Carrier.ROMParams`** is at most `2^-116.50`: at
most `45/2^122` (`zkBudgetROM_le_two_rpow` at the generated figures). -/
theorem zkBudgetROM_le : configuration.zkBudgetROM ≤ (2 : ℝ) ^ (-116.50 : ℝ) :=
  zkBudgetROM_le_two_rpow
    (ofCertifiedWith_readsFigures Generated.MLDSA44.Ring.Carrier.ROMParams.figures_eq)
    (M := 45) (E := 122) (e := 11650) (by norm_num) (by norm_num [Nat.choose_two_right])
    (by decide +kernel)

/-- **The bit security of everlasting zero knowledge of the carrier ML-DSA-44 ring signature at the
ROM parameters**: for every `t ≥ 1` hash queries and `Q ≤ 2^64` proof queries, the error of
`everlasting_zero_knowledge_rom` is at most `Q · t · 2^-116.50`. -/
@[headline]
theorem zero_knowledge_bits_rom {t Q : ℕ} (ht : 1 ≤ t) (hQ : Q ≤ 2 ^ 64) :
    (Configuration.Common.setting configuration configurationFacts proofSystem).model.zkErrorROM 0 t Q ≤
      Q * t * (2 : ℝ) ^ (-116.50 : ℝ) :=
  Configuration.ZKBits.zkErrorROM_le_bits configuration configurationFacts proofSystem
    zkBudgetROM_le ht hQ

/-- **The classical knowledge budget of `MLDSA44.Ring.Carrier.ROMParams` below `2 ^ 102` queries**
is at most `2^-101.34`: at most `101/2^108` (`knowledgeBudgetROM_le_two_rpow` at the generated
figures). -/
theorem knowledgeBudgetROM_le :
    configuration.knowledgeBudgetROM (2 ^ 102) ≤ (2 : ℝ) ^ (-101.34 : ℝ) :=
  knowledgeBudgetROM_le_two_rpow
    (ofCertifiedWith_readsFigures Generated.MLDSA44.Ring.Carrier.ROMParams.figures_eq)
    (M := 101) (E := 108) (e := 10134) (by norm_num) (by norm_num) (by decide +kernel)

/-- **The bit security of knowledge soundness of the carrier ML-DSA-44 ring signature at the ROM
parameters**: for every `t ≥ 1` hash queries, the classical knowledge error of
`knowledge_soundness_rom_at` and `soundness_rom_at` against `t`-query adversaries, evaluated at `t +
kq` as in the paper's `errks^C(t)` and `analysis/eval_params.py`, satisfies `min(1, err) ≤ t ·
2^-101.34`, so `λ(errks^C) ≥ 101.34`. -/
@[headline]
theorem soundness_bits_rom {t : ℕ} (ht : 1 ≤ t) :
    (min 1 (Configuration.Common.knowledgeErrorROM configuration configurationFacts
      (t + configuration.kq))).toReal ≤ t * (2 : ℝ) ^ (-101.34 : ℝ) :=
  SoundnessBits.knowledgeErrorROM_le_bits configuration configurationFacts (e := 10134)
    (by norm_num) (by decide +kernel) (knowledgeBudgetROM_le) ht

end GordieHowe.MLDSA44.Ring.Carrier.ROMParams
