-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Configuration.ZKBits
public import GordieHowe.Foundations.ToMathlib.NNRealRpow
public import GordieHowe.Applications.MLDSA44.Emulated.ROMParams
public import GordieHowe.Applications.MLDSA44.Emulated.QROMParams
public import GordieHowe.Applications.Falcon512.Native.ROMParams
public import GordieHowe.Applications.Falcon512.Native.QROMParams

@[expose] public section

/-!
# The zero-knowledge figures of the proofs of possession

The bit security of everlasting zero knowledge for one proof (`tab:eval-params`, the column
`λ(errzk)`), certified for the proofs of possession of ML-DSA-44 (`GordieHowe.MLDSA44.Emulated.ROMParams` at the ROM
parameters, `GordieHowe.MLDSA44.Emulated.QROMParams` at the QROM parameters) and of Falcon-512 (`GordieHowe.Falcon512.Native.ROMParams`,
`GordieHowe.Falcon512.Native.QROMParams`): for every `t ≥ 1` hash queries and `Q ≤ 2^64` proof queries, the
everlasting zero-knowledge error is at most `Q · t · 2^-λ`, in the ROM (`zkErrorROM 0`, the
error of `everlasting_zero_knowledge_rom`) at the ROM parameters and in the QROM (`zkError 0`, the error of
`everlasting_zero_knowledge_qrom`) at the QROM parameters. At `Q = 1` the paper's
`λ(err) = min over t ≥ 1 of log₂ (t / min(1, err(t)))` is at least `λ`; at `Q = 2^64` it is at
least `λ − 64`.

| configuration | parameters | `λ` |
|---|---|---|
| `GordieHowe.MLDSA44.Emulated.ROMParams` | ROM | `116.46` |
| `GordieHowe.MLDSA44.Emulated.QROMParams` | QROM | `180.19` |
| `GordieHowe.Falcon512.Native.ROMParams` | ROM | `116.68` |
| `GordieHowe.Falcon512.Native.QROMParams` | QROM | `180.15` |

The statements name the setting as `Configuration.Common.setting mergeConfig mergeFacts C`, which the
configuration's `setting C` abbreviates (`instantiate_config`), so the errors are those of the
configuration's `everlasting_zero_knowledge_rom` and `everlasting_zero_knowledge_qrom`.

Each figure comes from the configuration's budget (`GordieHowe.Configuration.zkBudgetROM`,
`GordieHowe.Configuration.zkBudget`) at its figures (rounds, Chernoff exponent, positions, digest and salt
lengths), bounded by a dyadic ratio `M / 2^E` and compared with `2^-λ` through
`M^100 · 2^(100 λ) ≤ 2^(100 E)` (`real_le_two_rpow_of_le_ratio`).
-/

namespace GordieHowe

open GordieHowe.Configuration

namespace MLDSA44.Emulated.ROMParams

-- The budget's exponents (up to `2^2780`) exceed `norm_num`'s default evaluation threshold.
set_option exponentiation.threshold 3000 in
/-- **The ROM zero-knowledge budget of `MLDSA44.Emulated.ROMParams`** is at most `2^-116.46`: at most
`5953/2^129`, dominated by the leaf term of the `5952` positions. -/
theorem zkBudgetROM_le : configuration.zkBudgetROM ≤ (2 : ℝ) ^ (-116.46 : ℝ) := by
  refine real_le_two_rpow_of_le_ratio (M := 5953) (E := 129) (n := 100) (e := 11646)
    (by norm_num) (by norm_num) ?_ (by decide +kernel)
  simp only [Configuration.zkBudgetROM, configuration, Nat.choose_two_right]
  norm_num

/-- **The bit security of everlasting zero knowledge of the ML-DSA-44 proof of possession at the ROM
parameters** (`tab:eval-params`): for every `t ≥ 1` hash queries and `Q ≤ 2^64` proof queries, the
error of `everlasting_zero_knowledge_rom` is at most `Q · t · 2^-116.46`. -/
@[headline]
theorem zero_knowledge_bits_rom (C : Compiled) {t Q : ℕ} (ht : 1 ≤ t) (hQ : Q ≤ 2 ^ 64) :
    (Configuration.Common.setting configuration configurationFacts C).model.zkErrorROM 0 t Q ≤
      Q * t * (2 : ℝ) ^ (-116.46 : ℝ) :=
  Configuration.ZKBits.zkErrorROM_le_bits configuration configurationFacts C
    zkBudgetROM_le ht hQ

end MLDSA44.Emulated.ROMParams

namespace MLDSA44.Emulated.QROMParams

-- The budget's exponents (up to `2^2780`) exceed `norm_num`'s default evaluation threshold.
set_option exponentiation.threshold 3000 in
/-- **The QROM zero-knowledge budget of `MLDSA44.Emulated.QROMParams`** is at most `2^-180.19`: at most
`7150/2^193`, the leaf term of the `7141` positions and the reprogramming term `4/2^192`. -/
theorem zkBudget_le : configuration.zkBudget ≤ (2 : ℝ) ^ (-180.19 : ℝ) := by
  refine real_le_two_rpow_of_le_ratio (M := 7150) (E := 193) (n := 100) (e := 18019)
    (by norm_num) (by norm_num) ?_ (by decide +kernel)
  simp only [Configuration.zkBudget, configuration, Nat.choose_two_right]
  norm_num

/-- **The bit security of everlasting zero knowledge of the ML-DSA-44 proof of possession at the QROM
parameters** (`tab:eval-params`): for every `t ≥ 1` hash queries and `Q ≤ 2^64` proof queries, the
error of `everlasting_zero_knowledge_qrom` is at most `Q · t · 2^-180.19`. -/
@[headline]
theorem zero_knowledge_bits_qrom (C : Compiled) {t Q : ℕ} (ht : 1 ≤ t) (hQ : Q ≤ 2 ^ 64) :
    (Configuration.Common.setting configuration configurationFacts C).model.zkError 0 t Q ≤
      Q * t * (2 : ℝ) ^ (-180.19 : ℝ) :=
  Configuration.ZKBits.zkError_le_bits configuration configurationFacts C
    zkBudget_le ht hQ

end MLDSA44.Emulated.QROMParams

namespace Falcon512.Native.ROMParams

-- The budget's exponents (up to `2^2780`) exceed `norm_num`'s default evaluation threshold.
set_option exponentiation.threshold 3000 in
/-- **The ROM zero-knowledge budget of `Falcon512.Native.ROMParams`** is at most `2^-116.68`: at most
`5087/2^129`, dominated by the leaf term of the `5086` positions. -/
theorem zkBudgetROM_le : configuration.zkBudgetROM ≤ (2 : ℝ) ^ (-116.68 : ℝ) := by
  refine real_le_two_rpow_of_le_ratio (M := 5087) (E := 129) (n := 100) (e := 11668)
    (by norm_num) (by norm_num) ?_ (by decide +kernel)
  simp only [Configuration.zkBudgetROM, configuration, Nat.choose_two_right]
  norm_num

/-- **The bit security of everlasting zero knowledge of the Falcon-512 proof of possession at the ROM
parameters**: for every `t ≥ 1` hash queries and `Q ≤ 2^64` proof queries, the error of
`everlasting_zero_knowledge_rom` is at most `Q · t · 2^-116.68`. -/
@[headline]
theorem zero_knowledge_bits_rom (C : Compiled) {t Q : ℕ} (ht : 1 ≤ t) (hQ : Q ≤ 2 ^ 64) :
    (Configuration.Common.setting configuration configurationFacts C).model.zkErrorROM 0 t Q ≤
      Q * t * (2 : ℝ) ^ (-116.68 : ℝ) :=
  Configuration.ZKBits.zkErrorROM_le_bits configuration configurationFacts C
    zkBudgetROM_le ht hQ

end Falcon512.Native.ROMParams

namespace Falcon512.Native.QROMParams

-- The budget's exponents (up to `2^2780`) exceed `norm_num`'s default evaluation threshold.
set_option exponentiation.threshold 3000 in
/-- **The QROM zero-knowledge budget of `Falcon512.Native.QROMParams`** is at most `2^-180.15`: at most
`7336/2^193`, the leaf term of the `7327` positions and the reprogramming term `4/2^192`. -/
theorem zkBudget_le : configuration.zkBudget ≤ (2 : ℝ) ^ (-180.15 : ℝ) := by
  refine real_le_two_rpow_of_le_ratio (M := 7336) (E := 193) (n := 100) (e := 18015)
    (by norm_num) (by norm_num) ?_ (by decide +kernel)
  simp only [Configuration.zkBudget, configuration, Nat.choose_two_right]
  norm_num

/-- **The bit security of everlasting zero knowledge of the Falcon-512 proof of possession at the QROM
parameters**: for every `t ≥ 1` hash queries and `Q ≤ 2^64` proof queries, the error of
`everlasting_zero_knowledge_qrom` is at most `Q · t · 2^-180.15`. -/
@[headline]
theorem zero_knowledge_bits_qrom (C : Compiled) {t Q : ℕ} (ht : 1 ≤ t) (hQ : Q ≤ 2 ^ 64) :
    (Configuration.Common.setting configuration configurationFacts C).model.zkError 0 t Q ≤
      Q * t * (2 : ℝ) ^ (-180.15 : ℝ) :=
  Configuration.ZKBits.zkError_le_bits configuration configurationFacts C zkBudget_le ht hQ

end Falcon512.Native.QROMParams

end GordieHowe
