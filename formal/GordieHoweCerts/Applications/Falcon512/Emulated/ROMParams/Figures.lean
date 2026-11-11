-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Configuration.SoundnessBits
public import GordieHoweCerts.Applications.Falcon512.Emulated.ROMParams

@[expose] public section

/-!
# The bit-security figures of `Falcon512.Emulated.ROMParams`

The bit security of the emulated Falcon-512 proof of possession at the ROM parameters, in the
paper's measure `λ(err) = min over t ≥ 1 of log₂ (t / min(1, err(t)))` (`sec:eval-params`),
certified from the generated figures (`GordieHowe.Generated.Falcon512.Emulated.ROMParams.figures`).

Zero knowledge: for every `t ≥ 1` hash queries and `Q ≤ proofQueryCap = 2^64` proof queries, the error `zkErrorROM 0` of
`everlasting_zero_knowledge_honest_rom` is at most `Q · t · 2^-λ`.

Knowledge soundness: for every `t ≥ 1` hash queries, the classical knowledge error of
`knowledge_soundness_rom_at` and `soundness_rom_at` against `t`-query adversaries,
`knowledgeErrorROM (t + kq)`, satisfies `min(1, err) ≤ t · 2^-λ`. The error is evaluated at `t +
kq`, the adversary's and the verifier's queries, as in the paper's `errks^C(t)` and in
`analysis/eval_params.py`.

| figure | `λ` |
|---|---|
| everlasting zero knowledge, one proof (`zero_knowledge_bits_rom`) | `116.41` |
| knowledge soundness and soundness (`soundness_bits_rom`) | `102.00` |

Each `λ` is rounded down to two decimals. The budgets (`GordieHowe.Configuration.zkBudgetROM`,
`GordieHowe.Configuration.knowledgeBudgetROM`) are bounded at the figures
(`GordieHowe.Configuration.ofCertified_readsFigures`) by a dyadic ratio `M / 2^E` and compared with
`2^-λ` through `M^100 · 2^(100 λ) ≤ 2^(100 E)`.
-/

namespace GordieHowe.Falcon512.Emulated.ROMParams

open GordieHowe.Configuration

-- The budget's exponents (up to `2^3730`) exceed `norm_num`'s default evaluation threshold.
set_option exponentiation.threshold 3900 in
/-- **The ROM zero-knowledge budget of `Falcon512.Emulated.ROMParams`** is at most `2^-116.41`: at
most `6165/2^129` (`zkBudgetROM_le_two_rpow` at the generated figures). -/
theorem zkBudgetROM_le : configuration.zkBudgetROM ≤ (2 : ℝ) ^ (-116.41 : ℝ) :=
  zkBudgetROM_le_two_rpow
    (ofCertified_readsFigures Generated.Falcon512.Emulated.ROMParams.figures_eq)
    (M := 6165) (E := 129) (e := 11641) (by norm_num) (by norm_num [Nat.choose_two_right, ParamSet.rom, ParamSet.qrom])
    (by decide +kernel)

/-- **The bit security of everlasting zero knowledge of the emulated Falcon-512 proof of possession
at the ROM parameters**: for every `t ≥ 1` hash queries and `Q ≤ proofQueryCap = 2^64` proof queries, the error `zkErrorROM 0` of
`everlasting_zero_knowledge_honest_rom` is at most `Q · t · 2^-116.41`. -/
theorem zero_knowledge_bits_rom :
    ZKBitSecurityAtLeast ((argument proofSystem).zkErrorROM 0) 116.41 :=
  Configuration.ZKBits.zkErrorROM_le_bits configuration configurationFacts proofSystem
    zkBudgetROM_le

/-- **The classical knowledge budget of `Falcon512.Emulated.ROMParams` below `2 ^ 102` queries** is
at most `2^-102.00`: at most `2/2^103` (`knowledgeBudgetROM_le_two_rpow` at the generated figures).
-/
theorem knowledgeBudgetROM_le :
    configuration.knowledgeBudgetROM (2 ^ 102) ≤ (2 : ℝ) ^ (-102.00 : ℝ) :=
  knowledgeBudgetROM_le_two_rpow
    (ofCertified_readsFigures Generated.Falcon512.Emulated.ROMParams.figures_eq)
    (M := 2) (E := 103) (e := 10200) (by norm_num) (by norm_num) (by decide +kernel)

/-- **The bit security of knowledge soundness of the emulated Falcon-512 proof of possession at the
ROM parameters**: for every `t ≥ 1` hash queries, the classical knowledge error of
`knowledge_soundness_rom_at` and `soundness_rom_at` against `t`-query adversaries, evaluated at `t +
kq` as in the paper's `errks^C(t)` and `analysis/eval_params.py`, satisfies `min(1, err) ≤ t ·
2^-102.00`, so `λ(errks^C) ≥ 102.00`. -/
theorem soundness_bits_rom :
    BitSecurityAtLeast extractionErrorROM 102.00 :=
  SoundnessBits.knowledgeErrorROM_le_bits configuration configurationFacts (e := 10200)
    (by norm_num) (by decide +kernel) (knowledgeBudgetROM_le)

end GordieHowe.Falcon512.Emulated.ROMParams
