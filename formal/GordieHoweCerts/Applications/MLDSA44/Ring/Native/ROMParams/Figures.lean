-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Configuration.SoundnessBits
public import GordieHoweCerts.Applications.MLDSA44.Ring.Native.ROMParams

@[expose] public section

/-!
# The bit-security figures of `MLDSA44.Ring.Native.ROMParams`

The bit security of the native ML-DSA-44 ring signature at the ROM parameters, in the paper's
measure `λ(err) = min over t ≥ 1 of log₂ (t / min(1, err(t)))` (`sec:eval-params`), certified from
the generated figures (`GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.figures`).

Zero knowledge: for every `t ≥ 1` hash queries and `Q ≤ 2^64` proof queries, the error of
`everlasting_zero_knowledge_rom` is at most `Q · t · 2^-λ`.

Knowledge soundness: for every `t ≥ 1` hash queries, the classical knowledge error of
`knowledge_soundness_rom_at` and `soundness_rom_at` against `t`-query adversaries,
`knowledgeErrorROM (t + kq)`, satisfies `min(1, err) ≤ t · 2^-λ`. The error is evaluated at `t +
kq`, the adversary's and the verifier's queries, as in the paper's `errks^C(t)` and in
`analysis/eval_params.py`.

| figure | `λ` |
|---|---|
| everlasting zero knowledge, one proof (`zero_knowledge_bits_rom`) | `116.37` |
| knowledge soundness and soundness (`soundness_bits_rom`) | `101.09` |

Each `λ` is rounded down to two decimals. The budgets (`GordieHowe.Configuration.zkBudgetROM`,
`GordieHowe.Configuration.knowledgeBudgetROM`) are bounded at the figures
(`GordieHowe.Configuration.ofCertifiedWith_readsFigures`) by a dyadic ratio `M / 2^E` and compared
with `2^-λ` through `M^100 · 2^(100 λ) ≤ 2^(100 E)`.
-/

namespace GordieHowe.MLDSA44.Ring.Native.ROMParams

open GordieHowe.Configuration

-- The budget's exponents (up to `2^2800`) exceed `norm_num`'s default evaluation threshold.
set_option exponentiation.threshold 3000 in
/-- **The ROM zero-knowledge budget of `MLDSA44.Ring.Native.ROMParams`** is at most `2^-116.37`: at
most `99/2^123` (`zkBudgetROM_le_two_rpow` at the generated figures). -/
theorem zkBudgetROM_le : configuration.zkBudgetROM ≤ (2 : ℝ) ^ (-116.37 : ℝ) :=
  zkBudgetROM_le_two_rpow
    (ofCertifiedWith_readsFigures Generated.MLDSA44.Ring.Native.ROMParams.figures_eq)
    (M := 99) (E := 123) (e := 11637) (by norm_num) (by norm_num [Nat.choose_two_right])
    (by decide +kernel)

/-- **The bit security of everlasting zero knowledge of the native ML-DSA-44 ring signature at the
ROM parameters**: for every `t ≥ 1` hash queries and `Q ≤ 2^64` proof queries, the error of
`everlasting_zero_knowledge_rom` is at most `Q · t · 2^-116.37`. -/
@[headline]
theorem zero_knowledge_bits_rom {t Q : ℕ} (ht : 1 ≤ t) (hQ : Q ≤ 2 ^ 64) :
    (Configuration.Common.setting configuration configurationFacts proofSystem).model.zkErrorROM 0 t Q ≤
      Q * t * (2 : ℝ) ^ (-116.37 : ℝ) :=
  Configuration.ZKBits.zkErrorROM_le_bits configuration configurationFacts proofSystem
    zkBudgetROM_le ht hQ

/-- **The classical knowledge budget of `MLDSA44.Ring.Native.ROMParams` below `2 ^ 102` queries** is
at most `2^-101.09`: at most `15/2^105` (`knowledgeBudgetROM_le_two_rpow` at the generated figures).
-/
theorem knowledgeBudgetROM_le :
    configuration.knowledgeBudgetROM (2 ^ 102) ≤ (2 : ℝ) ^ (-101.09 : ℝ) :=
  knowledgeBudgetROM_le_two_rpow
    (ofCertifiedWith_readsFigures Generated.MLDSA44.Ring.Native.ROMParams.figures_eq)
    (M := 15) (E := 105) (e := 10109) (by norm_num) (by norm_num) (by decide +kernel)

/-- **The bit security of knowledge soundness of the native ML-DSA-44 ring signature at the ROM
parameters**: for every `t ≥ 1` hash queries, the classical knowledge error of
`knowledge_soundness_rom_at` and `soundness_rom_at` against `t`-query adversaries, evaluated at `t +
kq` as in the paper's `errks^C(t)` and `analysis/eval_params.py`, satisfies `min(1, err) ≤ t ·
2^-101.09`, so `λ(errks^C) ≥ 101.09`. -/
@[headline]
theorem soundness_bits_rom {t : ℕ} (ht : 1 ≤ t) :
    (min 1 (Configuration.Common.knowledgeErrorROM configuration configurationFacts
      (t + configuration.kq))).toReal ≤ t * (2 : ℝ) ^ (-101.09 : ℝ) :=
  SoundnessBits.knowledgeErrorROM_le_bits configuration configurationFacts (e := 10109)
    (by norm_num) (by decide +kernel) (knowledgeBudgetROM_le) ht

end GordieHowe.MLDSA44.Ring.Native.ROMParams
