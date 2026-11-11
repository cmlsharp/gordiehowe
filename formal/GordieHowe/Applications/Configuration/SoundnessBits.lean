-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Configuration.ZKBits

@[expose] public section

/-!
# The knowledge-soundness figures of a configuration under spBCS

The paper's bit security of an error bound `err(t)` against adversaries with `t` hash queries is
`λ(err) = min over t ≥ 1 of log₂ (t / min(1, err(t)))` (`sec:eval-params`), so `λ(err) ≥ λ` holds
exactly when `min(1, err(t)) ≤ t · 2^-λ` for every `t ≥ 1`. The extraction errors of a
configuration are `knowledgeErrorROM (t + kq)` and `knowledgeErrorQROM (t + kq)`, the errors of
`knowledge_soundness_rom_at`, `soundness_rom_at`, `knowledge_soundness_qrom_at` and
`soundness_qrom_at` against `t`-query adversaries (the paper's `errks^C(t)` and `errks(t)`, which
charge the verifier's `kq` queries with the adversary's). This module bounds them in that form:

* `GordieHowe.Configuration.knowledgeBudgetROM`, `GordieHowe.Configuration.knowledgeBudgetQROM`:
  the per-query budgets of the errors below a query count `U` at least `2^λ`;
* `GordieHowe.Configuration.SoundnessBits.knowledgeErrorROM_le_bits`,
  `GordieHowe.Configuration.SoundnessBits.knowledgeErrorQROM_le_bits`: if `2^λ ≤ U` and the budget
  at `U` is at most `2^-λ`, then the extraction errors `extractionErrorROM` and
  `extractionErrorQROM` (the knowledge errors at `t + kq`) have bit security at least `λ`
  (`GordieHowe.Configuration.BitSecurityAtLeast`: `min(1, err(t + kq)) ≤ t · 2^-λ` for every
  `t ≥ 1`). Above `2^λ` queries the
  bound `t · 2^-λ` exceeds `1`; below, the error divided by `t` is at most the budget;
* `GordieHowe.Configuration.knowledgeBudgetROM_le_two_rpow`,
  `GordieHowe.Configuration.knowledgeBudgetQROM_le_two_rpow`: the budget below `2^s` from its
  value at the figures (`ReadsFigures`) bounded by a dyadic ratio `M / 2^E`.
-/

namespace GordieHowe.Configuration

open GordieHowe.SPBCS
open scoped NNReal ENNReal

/-- **Bit security at least `lam`** (paper `sec:eval-params`): for every `t ≥ 1` hash queries,
`min(1, err t) ≤ t · 2^-lam`, that is, the paper's `λ(err) = min over t ≥ 1 of
log₂ (t / min(1, err t))` is at least `lam`. -/
def BitSecurityAtLeast (err : ℕ → ℝ≥0∞) (lam : ℝ) : Prop :=
  ∀ t, 1 ≤ t → (min 1 (err t)).toReal ≤ t * 2 ^ (-lam)

section

variable (R : Configuration)

/-- **The classical knowledge budget below `U` queries**:
`(1 + kq) (errorMax/2^errorExp + D (U + kq)/2^(8k))`. For `1 ≤ t ≤ U`,
`knowledgeErrorROM (t + kq) ≤ t ·` this budget (`knowledgeErrorROM_le_bits`). -/
noncomputable def knowledgeBudgetROM (U : ℕ) : ℝ :=
  (1 + R.kq) * ((R.errorMax : ℝ) / 2 ^ R.errorExp + R.D * (U + R.kq) / 2 ^ (8 * R.k))

/-- **The quantum knowledge budget below `U` queries**:
`2^9/2^(4k) + 6 (U + 2 kq + kq²) (errorMax/2^errorExp + D (U + kq)/2^(8k))`. For `1 ≤ t ≤ U`,
`knowledgeErrorQROM (t + kq) ≤ t ·` this budget (`knowledgeErrorQROM_le_bits`). -/
noncomputable def knowledgeBudgetQROM (U : ℕ) : ℝ :=
  2 ^ 9 / 2 ^ (4 * R.k) + 6 * (U + 2 * R.kq + R.kq ^ 2) *
    ((R.errorMax : ℝ) / 2 ^ R.errorExp + R.D * (U + R.kq) / 2 ^ (8 * R.k))

end

namespace Common

variable (R : Configuration) (F : R.GrantedFacts)

/-- **The classical knowledge error as a real number**:
`T (errorMax/2^errorExp + D T/2^(8k))`. -/
theorem knowledgeErrorROM_toReal (T : ℕ) :
    (knowledgeErrorROM R F T).toReal =
      T * ((R.errorMax : ℝ) / 2 ^ R.errorExp + (R.D * T : ℕ) / 2 ^ (8 * R.k)) := by
  rw [knowledgeErrorROM, ENNReal.toReal_mul,
    ENNReal.toReal_add ENNReal.coe_ne_top
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)),
    ENNReal.toReal_div, ENNReal.coe_toReal, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast,
    NNReal.coe_ofNat]

/-- **The quantum knowledge error as a real number**:
`2^9/2^(4k) + 6 T² (errorMax/2^errorExp + D T/2^(8k))`. -/
theorem knowledgeErrorQROM_toReal (T : ℕ) :
    (knowledgeErrorQROM R F T).toReal =
      2 ^ 9 / 2 ^ (4 * R.k) + 6 * (T : ℝ) ^ 2 *
        ((R.errorMax : ℝ) / 2 ^ R.errorExp + (R.D * T : ℕ) / 2 ^ (8 * R.k)) := by
  have h1 : (2 : ℝ≥0∞) ^ 9 / 2 ^ (4 * R.k) ≠ ⊤ :=
    ENNReal.div_ne_top (by simp) (by positivity)
  have h2 : (((R.errorMax : ℝ≥0) / 2 ^ R.errorExp : ℝ≥0) : ℝ≥0∞) +
      ((R.D * T : ℕ) : ℝ≥0∞) / 2 ^ (8 * R.k) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.coe_ne_top,
      ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)⟩
  rw [knowledgeErrorQROM, ENNReal.toReal_add h1
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) h2),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_add ENNReal.coe_ne_top
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)),
    ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.coe_toReal, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat, ENNReal.toReal_ofNat, NNReal.coe_div, NNReal.coe_pow,
    NNReal.coe_natCast, NNReal.coe_ofNat]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofNat]

/-- The classical knowledge error is finite. -/
theorem knowledgeErrorROM_ne_top (T : ℕ) : knowledgeErrorROM R F T ≠ ⊤ :=
  ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.add_ne_top.2 ⟨ENNReal.coe_ne_top,
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)⟩)

/-- The quantum knowledge error is finite. -/
theorem knowledgeErrorQROM_ne_top (T : ℕ) : knowledgeErrorQROM R F T ≠ ⊤ :=
  ENNReal.add_ne_top.2 ⟨ENNReal.div_ne_top (by simp) (by positivity),
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp))
      (ENNReal.add_ne_top.2 ⟨ENNReal.coe_ne_top,
        ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)⟩)⟩

end Common

namespace SoundnessBits

open Common

variable (R : Configuration) (F : R.GrantedFacts)

/-- **Below `2^λ` queries**: if `1 ≤ t`, `t · 2^-λ < 1` and `2^λ ≤ U`, then `t ≤ U`. -/
theorem le_of_mul_two_rpow_lt {lam : ℝ} {U t : ℕ} (hU : (2 : ℝ) ^ lam ≤ U)
    (h : (t : ℝ) * 2 ^ (-lam) < 1) : (t : ℝ) ≤ U := by
  have h2 : (t : ℝ) * 2 ^ (-lam) * 2 ^ lam = t := by
    rw [mul_assoc, ← Real.rpow_add zero_lt_two, neg_add_cancel, Real.rpow_zero, mul_one]
  have h3 : (t : ℝ) < 2 ^ lam := by
    have := mul_lt_mul_of_pos_right h (by positivity : (0 : ℝ) < 2 ^ lam)
    rwa [h2, one_mul] at this
  exact h3.le.trans hU

/-- **The bit security of knowledge soundness in the ROM** (the errors of
`knowledge_soundness_rom_at` and `soundness_rom_at`): if `λ · 100 = e`, `2^e ≤ U^100` and the
classical budget at `U` is at most `2^-λ`, then for every `t ≥ 1` hash queries,
`min(1, knowledgeErrorROM (t + kq)) ≤ t · 2^-λ`: the paper's `λ(errks^C)` is at least `λ`. -/
theorem knowledgeErrorROM_le_bits {U e : ℕ} {lam : ℝ} (hs : lam * 100 = e)
    (hU : 2 ^ e ≤ U ^ 100) (hB : R.knowledgeBudgetROM U ≤ 2 ^ (-lam)) :
    BitSecurityAtLeast (extractionErrorROM R F) lam := by
  intro t ht
  show (min 1 (knowledgeErrorROM R F (t + R.kq))).toReal ≤ t * 2 ^ (-lam)
  rw [ENNReal.toReal_min ENNReal.one_ne_top (knowledgeErrorROM_ne_top R F _), ENNReal.toReal_one, knowledgeErrorROM_toReal]
  rcases le_or_gt 1 ((t : ℝ) * 2 ^ (-lam)) with h1 | h1
  · exact (min_le_left _ _).trans h1
  refine (min_le_right _ _).trans ?_
  have htU := le_of_mul_two_rpow_lt (two_rpow_le_of_le_pow (by norm_num) (by exact_mod_cast hs)
    hU) h1
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hK : (0 : ℝ) ≤ R.kq := Nat.cast_nonneg _
  have hi : (R.errorMax : ℝ) / 2 ^ R.errorExp + ((R.D * (t + R.kq) : ℕ) : ℝ) / 2 ^ (8 * R.k) ≤
      (R.errorMax : ℝ) / 2 ^ R.errorExp + R.D * (U + R.kq) / 2 ^ (8 * R.k) := by
    push_cast
    gcongr
  have hi0 : (0 : ℝ) ≤ (R.errorMax : ℝ) / 2 ^ R.errorExp +
      ((R.D * (t + R.kq) : ℕ) : ℝ) / 2 ^ (8 * R.k) := by positivity
  have hT : ((t + R.kq : ℕ) : ℝ) ≤ t * (1 + R.kq) := by
    push_cast
    nlinarith
  calc ((t + R.kq : ℕ) : ℝ) * ((R.errorMax : ℝ) / 2 ^ R.errorExp +
        ((R.D * (t + R.kq) : ℕ) : ℝ) / 2 ^ (8 * R.k))
      ≤ t * (1 + R.kq) * ((R.errorMax : ℝ) / 2 ^ R.errorExp + R.D * (U + R.kq) / 2 ^ (8 * R.k)) :=
        mul_le_mul hT hi hi0 (by positivity)
    _ = t * R.knowledgeBudgetROM U := by
        rw [knowledgeBudgetROM]
        ring
    _ ≤ t * 2 ^ (-lam) := mul_le_mul_of_nonneg_left hB (by positivity)

/-- **The bit security of knowledge soundness in the QROM** (the errors of
`knowledge_soundness_qrom_at` and `soundness_qrom_at`): if `λ · 100 = e`, `2^e ≤ U^100` and the
quantum budget at `U` is at most `2^-λ`, then for every `t ≥ 1` hash queries,
`min(1, knowledgeErrorQROM (t + kq)) ≤ t · 2^-λ`: the paper's `λ(errks)` is at least `λ`. -/
theorem knowledgeErrorQROM_le_bits {U e : ℕ} {lam : ℝ} (hs : lam * 100 = e)
    (hU : 2 ^ e ≤ U ^ 100) (hB : R.knowledgeBudgetQROM U ≤ 2 ^ (-lam)) :
    BitSecurityAtLeast (extractionErrorQROM R F) lam := by
  intro t ht
  show (min 1 (knowledgeErrorQROM R F (t + R.kq))).toReal ≤ t * 2 ^ (-lam)
  rw [ENNReal.toReal_min ENNReal.one_ne_top (knowledgeErrorQROM_ne_top R F _), ENNReal.toReal_one, knowledgeErrorQROM_toReal]
  rcases le_or_gt 1 ((t : ℝ) * 2 ^ (-lam)) with h1 | h1
  · exact (min_le_left _ _).trans h1
  refine (min_le_right _ _).trans ?_
  have htU := le_of_mul_two_rpow_lt (two_rpow_le_of_le_pow (by norm_num) (by exact_mod_cast hs)
    hU) h1
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hK : (0 : ℝ) ≤ R.kq := Nat.cast_nonneg _
  have hi : (R.errorMax : ℝ) / 2 ^ R.errorExp + ((R.D * (t + R.kq) : ℕ) : ℝ) / 2 ^ (8 * R.k) ≤
      (R.errorMax : ℝ) / 2 ^ R.errorExp + R.D * (U + R.kq) / 2 ^ (8 * R.k) := by
    push_cast
    gcongr
  have hi0 : (0 : ℝ) ≤ (R.errorMax : ℝ) / 2 ^ R.errorExp +
      ((R.D * (t + R.kq) : ℕ) : ℝ) / 2 ^ (8 * R.k) := by positivity
  have hT : ((t + R.kq : ℕ) : ℝ) ^ 2 ≤ t * (U + 2 * R.kq + R.kq ^ 2) := by
    push_cast
    nlinarith
  have hA : (2 : ℝ) ^ 9 / 2 ^ (4 * R.k) ≤ t * (2 ^ 9 / 2 ^ (4 * R.k)) :=
    le_mul_of_one_le_left (by positivity) ht1
  calc (2 : ℝ) ^ 9 / 2 ^ (4 * R.k) + 6 * ((t + R.kq : ℕ) : ℝ) ^ 2 *
        ((R.errorMax : ℝ) / 2 ^ R.errorExp + ((R.D * (t + R.kq) : ℕ) : ℝ) / 2 ^ (8 * R.k))
      ≤ t * (2 ^ 9 / 2 ^ (4 * R.k)) + 6 * (t * (U + 2 * R.kq + R.kq ^ 2)) *
        ((R.errorMax : ℝ) / 2 ^ R.errorExp + R.D * (U + R.kq) / 2 ^ (8 * R.k)) := by
        gcongr
    _ = t * R.knowledgeBudgetQROM U := by
        rw [knowledgeBudgetQROM]
        ring
    _ ≤ t * 2 ^ (-lam) := mul_le_mul_of_nonneg_left hB (by positivity)

end SoundnessBits

section Numerals

variable {R : Configuration} {kS : ℕ} {f : RealizedProgram.ProgramFigures}

/-- **The classical knowledge budget below a real power of two**, from its value at the figures
`f` (`ReadsFigures`) bounded by a dyadic ratio `M / 2^E`, with `s · 100 = −e` and
`M^100 · 2^e ≤ (2^E)^100` (`real_le_two_rpow_of_le_ratio`). -/
theorem knowledgeBudgetROM_le_two_rpow (hR : R.ReadsFigures kS f) {U M E e : ℕ} {s : ℝ}
    (hs : s * 100 = -(e : ℝ))
    (hx : (1 + f.kq) * ((f.errorMax : ℝ) / 2 ^ f.errorExp + f.D * (U + f.kq) / 2 ^ (8 * f.k)) ≤
      M / 2 ^ E)
    (h : M ^ 100 * 2 ^ e ≤ (2 ^ E) ^ 100) : R.knowledgeBudgetROM U ≤ 2 ^ s := by
  refine real_le_two_rpow_of_le_ratio (n := 100) (by norm_num) (by exact_mod_cast hs) ?_ h
  rw [knowledgeBudgetROM, hR.kq_eq, hR.errorMax_eq, hR.errorExp_eq, hR.D_eq, hR.k_eq]
  exact hx

/-- **The quantum knowledge budget below a real power of two**, from its value at the figures
`f` (`ReadsFigures`) bounded by a dyadic ratio `M / 2^E`, with `s · 100 = −e` and
`M^100 · 2^e ≤ (2^E)^100` (`real_le_two_rpow_of_le_ratio`). -/
theorem knowledgeBudgetQROM_le_two_rpow (hR : R.ReadsFigures kS f) {U M E e : ℕ} {s : ℝ}
    (hs : s * 100 = -(e : ℝ))
    (hx : 2 ^ 9 / 2 ^ (4 * f.k) + 6 * (U + 2 * f.kq + f.kq ^ 2) *
      ((f.errorMax : ℝ) / 2 ^ f.errorExp + f.D * (U + f.kq) / 2 ^ (8 * f.k)) ≤ M / 2 ^ E)
    (h : M ^ 100 * 2 ^ e ≤ (2 ^ E) ^ 100) : R.knowledgeBudgetQROM U ≤ 2 ^ s := by
  refine real_le_two_rpow_of_le_ratio (n := 100) (by norm_num) (by exact_mod_cast hs) ?_ h
  rw [knowledgeBudgetQROM, hR.kq_eq, hR.errorMax_eq, hR.errorExp_eq, hR.D_eq, hR.k_eq]
  exact hx

end Numerals

end GordieHowe.Configuration
