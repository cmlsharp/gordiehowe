-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Configuration.SoundnessBits
public import GordieHoweCerts.Applications.Falcon512.Ring.Carrier.ROMParams

@[expose] public section

/-!
# The bit-security figures of `Falcon512.Ring.Carrier.ROMParams`

The bit security of the carrier Falcon-512 ring signature at the ROM parameters, in the paper's
measure `λ(err) = min over t ≥ 1 of log₂ (t / min(1, err(t)))` (`sec:eval-params`), certified from
the generated figures (`GordieHowe.Generated.Falcon512.Ring.Carrier.ROMParams.figures`).

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
| everlasting zero knowledge, one proof (`zero_knowledge_bits_rom`) | `117.67` |
| knowledge soundness and soundness (`soundness_bits_rom`) | `112.64` |

Each `λ` is rounded down to two decimals. The budgets (`GordieHowe.Configuration.zkBudgetROM`,
`GordieHowe.Configuration.knowledgeBudgetROMTyped`) are bounded at the figures
(`GordieHowe.Configuration.ofCertifiedWith_readsFigures`) by a dyadic ratio `M / 2^E` and compared
with `2^-λ` through `M^100 · 2^(100 λ) ≤ 2^(100 E)`.
-/

namespace GordieHowe.Falcon512.Ring.Carrier.ROMParams

open GordieHowe.Configuration

-- The budget's exponents (up to `2^4160`) exceed `norm_num`'s default evaluation threshold.
set_option exponentiation.threshold 4300 in
/-- **The ROM zero-knowledge budget of `Falcon512.Ring.Carrier.ROMParams`** is at most `2^-117.67`:
at most `321/2^126` (`zkBudgetROM_le_two_rpow` at the generated figures). -/
theorem zkBudgetROM_le (G : Falcon512.Signer 32) :
    (configuration G).zkBudgetROM ≤ (2 : ℝ) ^ (-117.67 : ℝ) :=
  zkBudgetROM_le_two_rpow
    (ofCertifiedWith_readsFigures Generated.Falcon512.Ring.Carrier.ROMParams.figures_eq)
    (M := 321) (E := 126) (e := 11767) (by norm_num) (by norm_num [Nat.choose_two_right, ParamSet.rom, ParamSet.qrom])
    (by decide +kernel)

/-- **The bit security of everlasting zero knowledge of the carrier Falcon-512 ring signature at the
ROM parameters**: for every `t ≥ 1` hash queries and `Q ≤ proofQueryCap = 2^64` proof queries, the error `zkErrorROM 0` of
`everlasting_zero_knowledge_honest_rom` is at most `Q · t · 2^-117.67`. -/
theorem zero_knowledge_bits_rom (G : Falcon512.Signer 32) :
    ZKBitSecurityAtLeast ((argument G proofSystem).zkErrorROM 0) 117.67 :=
  Configuration.ZKBits.zkErrorROM_le_bits (configuration G) (configurationFacts G) proofSystem
    (zkBudgetROM_le G)

/-- **The typed classical knowledge budget of `Falcon512.Ring.Carrier.ROMParams` below `2 ^ 113`
queries** is at most `2^-112.64`: at most `5255/2^125` (`knowledgeBudgetROMTyped_le_two_rpow` at the
generated figures and the configuration's `errorSum`). -/
theorem knowledgeBudgetROMTyped_le (G : Falcon512.Signer 32) :
    (configuration G).knowledgeBudgetROMTyped (2 ^ 113) 1 ≤ (2 : ℝ) ^ (-112.64 : ℝ) :=
  knowledgeBudgetROMTyped_le_two_rpow
    (ofCertifiedWith_readsFigures Generated.Falcon512.Ring.Carrier.ROMParams.figures_eq) rfl
    (es := 84845906) (M := 5255) (E := 125) (e := 11264) (by norm_num) (by norm_num)
    (by decide +kernel)

/-- **The bit security of knowledge soundness of the carrier Falcon-512 ring signature at the ROM
parameters**: for every `t ≥ 1` hash queries, the typed extraction error `extractionErrorROMTyped`
of `knowledge_soundness_rom_at` and `soundness_rom_at` against `t`-query adversaries, at most the
classical knowledge error at `t + kq` as in the paper's `errks^C(t)` and `analysis/eval_params.py`
(`extractionErrorROMTyped_le`), satisfies `min(1, err) ≤ t · 2^-112.64`, so `λ(errks^C) ≥ 112.64`.
-/
theorem soundness_bits_rom (G : Falcon512.Signer 32) :
    BitSecurityAtLeast (extractionErrorROMTyped G proofSystem) 112.64 :=
  SoundnessBits.knowledgeErrorROMTyped_le_bits (configuration G) (configurationFacts G) proofSystem
    (m := 1) domains_length.le (e := 11264) (by norm_num) (by decide +kernel)
    (knowledgeBudgetROMTyped_le G)

end GordieHowe.Falcon512.Ring.Carrier.ROMParams
