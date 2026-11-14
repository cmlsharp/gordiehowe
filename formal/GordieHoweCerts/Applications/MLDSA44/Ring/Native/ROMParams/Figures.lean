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

Zero knowledge: for every `t ≥ 1` hash queries and `Q ≤ proofQueryCap = 2^64` proof queries, the error `zkErrorROM 0` of
`everlasting_zero_knowledge_honest_rom` is at most `Q · t · 2^-λ`.

Knowledge soundness: for every `t ≥ 1` hash queries, the classical knowledge error of
`knowledge_soundness_rom_at` and `soundness_rom_at` against `t`-query adversaries,
`extractionErrorROMTyped t`, at most `knowledgeErrorROM (t + kq)`, satisfies
`min(1, err) ≤ t · 2^-λ`. The error is evaluated at `t +
kq`, the adversary's and the verifier's queries, as in the paper's `errks^C(t)` and in
`analysis/eval_params.py`.

| figure | `λ` |
|---|---|
| everlasting zero knowledge, one proof (`zero_knowledge_bits_rom`) | `116.29` |
| knowledge soundness and soundness (`soundness_bits_rom`) | `111.40` |

Each `λ` is rounded down to two decimals. The budgets (`GordieHowe.Configuration.zkBudgetROM`,
`GordieHowe.Configuration.knowledgeBudgetROMTyped`) are bounded at the figures
(`GordieHowe.Configuration.ofCertifiedWith_readsFigures`) by a dyadic ratio `M / 2^E` and compared
with `2^-λ` through `M^100 · 2^(100 λ) ≤ 2^(100 E)`.
-/

namespace GordieHowe.MLDSA44.Ring.Native.ROMParams

open GordieHowe.Configuration

-- The budget's exponents (up to `2^2800`) exceed `norm_num`'s default evaluation threshold.
set_option exponentiation.threshold 3000 in
/-- **The ROM zero-knowledge budget of `MLDSA44.Ring.Native.ROMParams`** is at most `2^-116.29`: at
most `837/2^126` (`zkBudgetROM_le_two_rpow` at the generated figures). -/
theorem zkBudgetROM_le : configuration.zkBudgetROM ≤ (2 : ℝ) ^ (-116.29 : ℝ) :=
  zkBudgetROM_le_two_rpow
    (ofCertifiedWith_readsFigures Generated.MLDSA44.Ring.Native.ROMParams.figures_eq)
    (M := 837) (E := 126) (e := 11629) (by norm_num) (by norm_num [Nat.choose_two_right, ParamSet.rom, ParamSet.qrom])
    (by decide +kernel)

/-- **The bit security of everlasting zero knowledge of the native ML-DSA-44 ring signature at the
ROM parameters**: for every `t ≥ 1` hash queries and `Q ≤ proofQueryCap = 2^64` proof queries, the error `zkErrorROM 0` of
`everlasting_zero_knowledge_honest_rom` is at most `Q · t · 2^-116.29`. -/
theorem zero_knowledge_bits_rom :
    ZKBitSecurityAtLeast ((argument proofSystem).zkErrorROM 0) 116.29 :=
  Configuration.ZKBits.zkErrorROM_le_bits configuration configurationFacts proofSystem
    zkBudgetROM_le

/-- **The typed classical knowledge budget of `MLDSA44.Ring.Native.ROMParams` below `2 ^ 113`
queries** is at most `2^-111.40`: at most `12381/2^125` (`knowledgeBudgetROMTyped_le_two_rpow` at
the generated figures and the configuration's `errorSum`). -/
theorem knowledgeBudgetROMTyped_le :
    configuration.knowledgeBudgetROMTyped (2 ^ 113) 2 ≤ (2 : ℝ) ^ (-111.40 : ℝ) :=
  knowledgeBudgetROMTyped_le_two_rpow
    (ofCertifiedWith_readsFigures Generated.MLDSA44.Ring.Native.ROMParams.figures_eq) rfl
    (es := 221788612) (M := 12381) (E := 125) (e := 11140) (by norm_num) (by norm_num)
    (by decide +kernel)

/-- **The bit security of knowledge soundness of the native ML-DSA-44 ring signature at the ROM
parameters**: for every `t ≥ 1` hash queries, the typed extraction error `extractionErrorROMTyped`
of `knowledge_soundness_rom_at` and `soundness_rom_at` against `t`-query adversaries, at most the
classical knowledge error at `t + kq` as in the paper's `errks^C(t)` and `analysis/eval_params.py`
(`extractionErrorROMTyped_le`), satisfies `min(1, err) ≤ t · 2^-111.40`, so `λ(errks^C) ≥ 111.40`.
-/
theorem soundness_bits_rom :
    BitSecurityAtLeast (extractionErrorROMTyped proofSystem) 111.40 :=
  SoundnessBits.knowledgeErrorROMTyped_le_bits configuration configurationFacts proofSystem
    (m := 2) domains_length.le (e := 11140) (by norm_num) (by decide +kernel)
    (knowledgeBudgetROMTyped_le)

end GordieHowe.MLDSA44.Ring.Native.ROMParams
