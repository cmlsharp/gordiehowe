-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Configuration.SoundnessBits
public import GordieHoweCerts.Applications.MLDSA44.Emulated.ROMParams

@[expose] public section

/-!
# The bit-security figures of `MLDSA44.Emulated.ROMParams`

The bit security of the emulated ML-DSA-44 proof of possession at the ROM parameters, in the paper's
measure `λ(err) = min over t ≥ 1 of log₂ (t / min(1, err(t)))` (`sec:eval-params`), certified from
the generated figures (`GordieHowe.Generated.MLDSA44.Emulated.ROMParams.figures`).

Zero knowledge: for every `t ≥ 1` hash queries and `Q ≤ proofQueryCap = 2^64` proof queries, the error `zkErrorROM 0` of
`everlasting_zero_knowledge_honest_rom` is at most `Q · t · 2^-λ`.

Knowledge soundness: for every `t ≥ 1` hash queries, the classical knowledge error of
`knowledge_soundness_rom_at` and `soundness_rom_at` against `t`-query adversaries,
`knowledgeErrorROM (t + kq)`, satisfies `min(1, err) ≤ t · 2^-λ`. The error is evaluated at `t +
kq`, the adversary's and the verifier's queries, as in the paper's `errks^C(t)` and in
`analysis/eval_params.py`.

| figure | `λ` |
|---|---|
| everlasting zero knowledge, one proof (`zero_knowledge_bits_rom`) | `116.46` |
| knowledge soundness and soundness (`soundness_bits_rom`) | `101.36` |

Each `λ` is rounded down to two decimals. The budgets (`GordieHowe.Configuration.zkBudgetROM`,
`GordieHowe.Configuration.knowledgeBudgetROM`) are bounded at the figures
(`GordieHowe.Configuration.ofCertified_readsFigures`) by a dyadic ratio `M / 2^E` and compared with
`2^-λ` through `M^100 · 2^(100 λ) ≤ 2^(100 E)`.
-/

namespace GordieHowe.MLDSA44.Emulated.ROMParams

open GordieHowe.Configuration

-- The budget's exponents (up to `2^2780`) exceed `norm_num`'s default evaluation threshold.
set_option exponentiation.threshold 3000 in
/-- **The ROM zero-knowledge budget of `MLDSA44.Emulated.ROMParams`** is at most `2^-116.46`: at
most `5953/2^129` (`zkBudgetROM_le_two_rpow` at the generated figures). -/
theorem zkBudgetROM_le : configuration.zkBudgetROM ≤ (2 : ℝ) ^ (-116.46 : ℝ) :=
  zkBudgetROM_le_two_rpow
    (ofCertified_readsFigures Generated.MLDSA44.Emulated.ROMParams.figures_eq)
    (M := 5953) (E := 129) (e := 11646) (by norm_num) (by norm_num [Nat.choose_two_right, ParamSet.rom, ParamSet.qrom])
    (by decide +kernel)

/-- **The bit security of everlasting zero knowledge of the emulated ML-DSA-44 proof of possession
at the ROM parameters** (`tab:eval-params`): for every `t ≥ 1` hash queries and `Q ≤ proofQueryCap = 2^64` proof
queries, the error `zkErrorROM 0` of `everlasting_zero_knowledge_honest_rom` is at most `Q · t · 2^-116.46`. -/
@[headline]
theorem zero_knowledge_bits_rom :
    ZKBitSecurityAtLeast ((argument proofSystem).zkErrorROM 0) 116.46 :=
  Configuration.ZKBits.zkErrorROM_le_bits configuration configurationFacts proofSystem
    zkBudgetROM_le

/-- **The classical knowledge budget of `MLDSA44.Emulated.ROMParams` below `2 ^ 102` queries** is at
most `2^-101.36`: at most `797/2^111` (`knowledgeBudgetROM_le_two_rpow` at the generated figures).
-/
theorem knowledgeBudgetROM_le :
    configuration.knowledgeBudgetROM (2 ^ 102) ≤ (2 : ℝ) ^ (-101.36 : ℝ) :=
  knowledgeBudgetROM_le_two_rpow
    (ofCertified_readsFigures Generated.MLDSA44.Emulated.ROMParams.figures_eq)
    (M := 797) (E := 111) (e := 10136) (by norm_num) (by norm_num) (by decide +kernel)

/-- **The bit security of knowledge soundness of the emulated ML-DSA-44 proof of possession at the
ROM parameters** (`tab:eval-params`, the extraction column): for every `t ≥ 1` hash queries, the
classical knowledge error of `knowledge_soundness_rom_at` and `soundness_rom_at` against `t`-query
adversaries, evaluated at `t + kq` as in the paper's `errks^C(t)` and `analysis/eval_params.py`,
satisfies `min(1, err) ≤ t · 2^-101.36`, so `λ(errks^C) ≥ 101.36`. -/
@[headline]
theorem soundness_bits_rom :
    BitSecurityAtLeast extractionErrorROM 101.36 :=
  SoundnessBits.knowledgeErrorROM_le_bits configuration configurationFacts (e := 10136)
    (by norm_num) (by decide +kernel) (knowledgeBudgetROM_le)

end GordieHowe.MLDSA44.Emulated.ROMParams
