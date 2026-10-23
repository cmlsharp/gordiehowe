-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Configuration
public import GordieHowe.SPBCS.Merkle.LeafBoundBits

@[expose] public section

/-!
# The zero-knowledge figures of a configuration under spBCS

The paper's bit security of an error bound `err(t)` against adversaries with `t` hash queries is
`λ(err) = min over t ≥ 1 of log₂ (t / min(1, err(t)))` (`sec:eval-params`), so `λ(err) ≥ λ` holds
exactly when `err(t) ≤ t · 2^-λ` for every `t ≥ 1`. This module bounds the everlasting
zero-knowledge errors of a configuration in that form, for `Q ≤ 2^64` proof queries:

* `GordieHowe.Configuration.zkBudgetROM`, `GordieHowe.Configuration.zkBudget`: the per-query, per-proof-query budgets in the
  configuration's figures (salt, digest, rounds, Chernoff exponent, positions), with the leaf term
  bounded by `GordieHowe.SPBCS.leafBound_two_mul_le`;
* `GordieHowe.Configuration.ZKBits.zkErrorROM_le_bits`, `GordieHowe.Configuration.ZKBits.zkError_le_bits`: if the budget is at most
  `2^-λ`, then `zkErrorROM 0 t Q` and `zkError 0 t Q` are at most `Q · t · 2^-λ` for `t ≥ 1` and
  `Q ≤ 2^64`. At `Q = 1` this is `λ(err) ≥ λ`; at `Q` proof queries the bit security loses at most
  `log₂ Q` bits.
-/

namespace GordieHowe.Configuration

open IOP IOP.ProtocolSpec IOP.SPTerm GordieHowe.SPBCS GordieHowe.SPBCS GordieHowe.QROM SPBCS.Configurations
open scoped NNReal ENNReal

section

variable (R : Configuration)

/-- **The zero-knowledge budget in the ROM** of a configuration, per query and proof query:
`1/2^(8 kS) + 2^64/(2 · 2^(8 kS)) + C(rounds, 2)/2^(8k) + rounds/2^chernoff +
pos · (1/(2 · 2^(4k)) + 2^21/2^(8k))`. The second summand charges the proof-salt collisions of
up to `2^64 + 1` proof queries; the last is the positions' leaf term (`SPBCS.leafBound_two_mul_le`). -/
noncomputable def zkBudgetROM : ℝ :=
  1 / 2 ^ (8 * R.kS) + 2 ^ 64 / (2 * 2 ^ (8 * R.kS)) + (R.rounds.choose 2 : ℝ) / 2 ^ (8 * R.k) +
    R.rounds / 2 ^ R.chernoff + R.pos * (1 / (2 * 2 ^ (4 * R.k)) + 2 ^ 21 / 2 ^ (8 * R.k))

/-- **The zero-knowledge budget in the QROM** of a configuration, per query and proof query:
`4/2^(4 kS) + 2^64/2^(8 kS) + C(rounds, 2)/2^(8k) + rounds/2^chernoff +
pos · (1/(2 · 2^(4k)) + 2^21/2^(8k))` (as `zkBudgetROM`, with the QROM's reprogramming term). -/
noncomputable def zkBudget : ℝ :=
  4 / 2 ^ (4 * R.kS) + 2 ^ 64 / 2 ^ (8 * R.kS) + (R.rounds.choose 2 : ℝ) / 2 ^ (8 * R.k) +
    R.rounds / 2 ^ R.chernoff + R.pos * (1 / (2 * 2 ^ (4 * R.k)) + 2 ^ 21 / 2 ^ (8 * R.k))

end

namespace ZKBits

open Common

variable (R : Configuration) (F : R.GrantedFacts)

/-- **The per-proof-query terms of the zero-knowledge errors**: the key-collision, overrun and
leaf terms of the spBCS setting are at most `C(rounds, 2)/2^(8k) + rounds/2^chernoff +
pos · (1/(2 · 2^(4k)) + 2^21/2^(8k))` (`overrun_le`, `card_pos`,
`SPBCS.leafBound_two_mul_le` at the setting's `2k`-byte Merkle salts and `2^40`-byte inputs). -/
theorem request_terms_le (C : R.Compiled) :
    (SPBCS.keyCollision ((R.iop C).term.size (R.iop C).rounds) (setting R F C).k).toReal +
        (setting R F C).model.overrun.toReal +
        Fintype.card (setting R F C).model.Pos *
          SPBCS.leafBound (setting R F C).k (setting R F C).kN (setting R F C).L ≤
      (R.rounds.choose 2 : ℝ) / 2 ^ (8 * R.k) + R.rounds / 2 ^ R.chernoff +
        R.pos * (1 / (2 * 2 ^ (4 * R.k)) + 2 ^ 21 / 2 ^ (8 * R.k)) := by
  have hkc : (SPBCS.keyCollision ((R.iop C).term.size (R.iop C).rounds) (R.T C).k).toReal ≤
      (R.rounds.choose 2 : ℝ) / 2 ^ (8 * R.k) := by
    have h := ENNReal.toReal_mono (SPBCS.keyCollision_ne_top _ _)
      (SPBCS.keyCollision_mono (F.rounds_le C) (R.T C).k)
    rw [← F.k_eq C, SPTerm.size_eq_sum]
    refine h.trans (le_of_eq ?_)
    rw [SPBCS.keyCollision, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat]
  have hov : (setting R F C).model.overrun.toReal ≤ R.rounds / 2 ^ R.chernoff := by
    have h := ENNReal.toReal_mono (ENNReal.div_lt_top (by simp) (by simp)).ne
      (overrun_le R F C)
    rwa [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat] at h
  have hU : (Fintype.card (setting R F C).model.Pos : ℝ) = R.pos := by
    exact_mod_cast card_pos R F C
  have hleaf : SPBCS.leafBound (setting R F C).k (setting R F C).kN (setting R F C).L ≤
      1 / (2 * 2 ^ (4 * R.k)) + 2 ^ 21 / 2 ^ (8 * R.k) := by
    change SPBCS.leafBound (R.T C).k (2 * (R.T C).k) (2 ^ 40) ≤ _
    rw [F.k_eq C]
    exact SPBCS.leafBound_two_mul_le le_rfl
  rw [hU]
  exact add_le_add (add_le_add hkc hov)
    (mul_le_mul_of_nonneg_left hleaf (Nat.cast_nonneg _))

/-- **The bit security of zero knowledge in the ROM** (`everlasting_zero_knowledge_rom`'s error): if the
ROM budget is at most `2^-λ`, then for every `t ≥ 1` hash queries and `Q ≤ 2^64` proof queries,
`zkErrorROM 0 t Q ≤ Q · t · 2^-λ`. At `Q = 1` the paper's `λ(errzk^C)` is at least `λ`. -/
theorem zkErrorROM_le_bits (C : R.Compiled) {lam : ℝ} (hB : R.zkBudgetROM ≤ 2 ^ (-lam))
    {t Q : ℕ} (ht : 1 ≤ t) (hQ : Q ≤ 2 ^ 64) :
    (setting R F C).model.zkErrorROM 0 t Q ≤ Q * t * 2 ^ (-lam) := by
  have hreq := request_terms_le R F C
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hQ1 : (Q : ℝ) - 1 ≤ 2 ^ 64 * t := by
    have : (Q : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hQ
    nlinarith
  have hS : (0 : ℝ) < 2 * 2 ^ (8 * R.kS) := by positivity
  set c : ℝ := (R.rounds.choose 2 : ℝ) / 2 ^ (8 * R.k) + R.rounds / 2 ^ R.chernoff +
    R.pos * (1 / (2 * 2 ^ (4 * R.k)) + 2 ^ 21 / 2 ^ (8 * R.k)) with hc
  have hc0 : 0 ≤ c := by
    rw [hc]
    positivity
  have hsalt : (Q : ℝ) * (Q - 1) / (2 * 2 ^ (8 * R.kS)) ≤
      Q * t * (2 ^ 64 / (2 * 2 ^ (8 * R.kS))) := by
    calc (Q : ℝ) * (Q - 1) / (2 * 2 ^ (8 * R.kS)) ≤ Q * (2 ^ 64 * t) / (2 * 2 ^ (8 * R.kS)) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hQ1 hQ0) hS.le
      _ = Q * t * (2 ^ 64 / (2 * 2 ^ (8 * R.kS))) := by ring
  have hreq' : (Q : ℝ) * ((SPBCS.keyCollision ((R.iop C).term.size (R.iop C).rounds)
        (setting R F C).k).toReal + (setting R F C).model.overrun.toReal + 0 +
        Fintype.card (setting R F C).model.Pos *
          SPBCS.leafBound (setting R F C).k (setting R F C).kN (setting R F C).L) ≤
      Q * t * c := by
    rw [add_zero]
    calc _ ≤ (Q : ℝ) * c := mul_le_mul_of_nonneg_left hreq hQ0
      _ ≤ Q * t * c := by
          have h := mul_le_mul_of_nonneg_left ht1 (mul_nonneg hQ0 hc0)
          linarith
  calc (setting R F C).model.zkErrorROM 0 t Q
      ≤ Q * t * (1 / 2 ^ (8 * R.kS)) + Q * t * (2 ^ 64 / (2 * 2 ^ (8 * R.kS))) + Q * t * c := by
        rw [Base.zkErrorROM, NNReal.coe_zero]
        refine add_le_add (add_le_add (le_of_eq ?_) hsalt) hreq'
        change (Q : ℝ) * t / 2 ^ (8 * R.kS) = _
        ring
    _ = Q * t * R.zkBudgetROM := by
        rw [Configuration.zkBudgetROM, hc]
        ring
    _ ≤ Q * t * 2 ^ (-lam) := mul_le_mul_of_nonneg_left hB (by positivity)

/-- **The bit security of zero knowledge in the QROM** (`everlasting_zero_knowledge_qrom`'s error): if the
QROM budget is at most `2^-λ`, then for every `t ≥ 1` hash queries and `Q ≤ 2^64` proof queries,
`zkError 0 t Q ≤ Q · t · 2^-λ`. At `Q = 1` the paper's `λ(errzk)` is at least `λ`. -/
theorem zkError_le_bits (C : R.Compiled) {lam : ℝ} (hB : R.zkBudget ≤ 2 ^ (-lam))
    {t Q : ℕ} (ht : 1 ≤ t) (hQ : Q ≤ 2 ^ 64) :
    (setting R F C).model.zkError 0 t Q ≤ Q * t * 2 ^ (-lam) := by
  have hreq := request_terms_le R F C
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hQ1 : (Q : ℝ) - 1 ≤ 2 ^ 64 * t := by
    have : (Q : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hQ
    nlinarith
  have hS : (0 : ℝ) < 2 ^ (8 * R.kS) := by positivity
  set c : ℝ := (R.rounds.choose 2 : ℝ) / 2 ^ (8 * R.k) + R.rounds / 2 ^ R.chernoff +
    R.pos * (1 / (2 * 2 ^ (4 * R.k)) + 2 ^ 21 / 2 ^ (8 * R.k)) with hc
  have hc0 : 0 ≤ c := by
    rw [hc]
    positivity
  have hsalt : (Q : ℝ) * (Q - 1) / 2 ^ (8 * R.kS) ≤ Q * t * (2 ^ 64 / 2 ^ (8 * R.kS)) := by
    calc (Q : ℝ) * (Q - 1) / 2 ^ (8 * R.kS) ≤ Q * (2 ^ 64 * t) / 2 ^ (8 * R.kS) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hQ1 hQ0) hS.le
      _ = Q * t * (2 ^ 64 / 2 ^ (8 * R.kS)) := by ring
  have hreq' : (Q : ℝ) * ((SPBCS.keyCollision ((R.iop C).term.size (R.iop C).rounds)
        (setting R F C).k).toReal + (setting R F C).model.overrun.toReal + 0 +
        Fintype.card (setting R F C).model.Pos *
          SPBCS.leafBound (setting R F C).k (setting R F C).kN (setting R F C).L) ≤
      Q * t * c := by
    rw [add_zero]
    calc _ ≤ (Q : ℝ) * c := mul_le_mul_of_nonneg_left hreq hQ0
      _ ≤ Q * t * c := by
          have h := mul_le_mul_of_nonneg_left ht1 (mul_nonneg hQ0 hc0)
          linarith
  calc (setting R F C).model.zkError 0 t Q
      ≤ Q * t * (4 / 2 ^ (4 * R.kS)) + Q * t * (2 ^ 64 / 2 ^ (8 * R.kS)) + Q * t * c := by
        rw [Base.zkError, NNReal.coe_zero]
        refine add_le_add (add_le_add (le_of_eq ?_) hsalt) hreq'
        change 4 * (Q : ℝ) * t / 2 ^ (4 * R.kS) = _
        ring
    _ = Q * t * R.zkBudget := by
        rw [Configuration.zkBudget, hc]
        ring
    _ ≤ Q * t * 2 ^ (-lam) := mul_le_mul_of_nonneg_left hB (by positivity)

end ZKBits

end GordieHowe.Configuration
