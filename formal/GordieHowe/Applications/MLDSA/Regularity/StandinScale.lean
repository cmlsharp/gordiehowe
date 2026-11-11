-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.Instances

public section

/-!
# The stand-in scale at the approved parameter sets

`one_div_sixteen_le_standinScale_mul_card_mldsa44`, `_mldsa65`, `_mldsa87`: the stand-in scale
`K = standinScale` times the number of bucket vectors is at least `1/16`. `K |V|` is a product of
two powers `(1 - x)^m`, each bounded below by Bernoulli's inequality `(1 - x)^m ≥ 1 - m x`
(`one_add_mul_le_pow`), on half the exponent and squared where `m x > 1`.
-/

namespace GordieHowe.MLDSA.Regularity

open _root_.MLDSA GordieHowe.MLDSA
open scoped ENNReal BigOperators

/-- **The stand-in scale at ML-DSA-44**: `K |V| ≥ 1/16`, with `K |V| =
(261987/2^18)^1024 · (44 · 190307/q)^1024` and Bernoulli's inequality (`one_add_mul_le_pow`). -/
theorem one_div_sixteen_le_standinScale_mul_card_mldsa44 :
    1 / 16 ≤ (standinScale _root_.MLDSA.mldsa44).toReal *
      Fintype.card (BucketVec _root_.MLDSA.mldsa44) := by
  obtain ⟨-, hl, hg1, -, hb, -⟩ := mldsa44_vals
  have hV : (Fintype.card (BucketVec _root_.MLDSA.mldsa44) : ℝ) = 44 ^ 1024 := by
    rw [card_bucketVec_coeffIndex, bucketCount_mldsa44, card_coeffIndex_mldsa44,
      Nat.cast_pow, Nat.cast_ofNat]
  have hz : (zAcceptFraction _root_.MLDSA.mldsa44).toReal = (261987 / 262144 : ℝ) ^ 1024 := by
    rw [zAcceptFraction, ENNReal.toReal_ofReal
      (pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _), hg1, hb, hl]
    congr 1
  have hu : (uniformScale _root_.MLDSA.mldsa44).toReal = (190307 / 8380417 : ℝ) ^ 1024 := by
    rw [toReal_uniformScale, cellSize_mldsa44, card_coeffIndex_mldsa44]
    congr 1
  rw [standinScale, ENNReal.toReal_mul, hz, hu, hV, mul_assoc, ← mul_pow]
  have h1 : (1 : ℝ) - 1024 * (157 / 262144) ≤ (261987 / 262144 : ℝ) ^ 1024 := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(157 / 262144) by norm_num) 1024
    rw [show (1 : ℝ) + -(157 / 262144) = 261987 / 262144 by norm_num,
      show ((1024 : ℕ) : ℝ) = 1024 by norm_num] at h
    generalize (261987 / 262144 : ℝ) ^ 1024 = P at h ⊢
    linarith
  have h2 : ((1 : ℝ) - 512 * (6909 / 8380417)) ^ 2 ≤ (190307 / 8380417 * 44 : ℝ) ^ 1024 := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(6909 / 8380417) by norm_num) 512
    rw [show (1 : ℝ) + -(6909 / 8380417) = 190307 / 8380417 * 44 by norm_num,
      show ((512 : ℕ) : ℝ) = 512 by norm_num] at h
    rw [show (1024 : ℕ) = 512 * 2 by norm_num, pow_mul]
    generalize (190307 / 8380417 * 44 : ℝ) ^ 512 = P at h ⊢
    exact pow_le_pow_left₀ (by norm_num) (by linarith) 2
  calc (1 : ℝ) / 16 ≤ (1 - 1024 * (157 / 262144)) * (1 - 512 * (6909 / 8380417)) ^ 2 := by
        norm_num
    _ ≤ (261987 / 262144 : ℝ) ^ 1024 * (190307 / 8380417 * 44 : ℝ) ^ 1024 :=
        mul_le_mul h1 h2 (by norm_num) (by positivity)

/-- **The stand-in scale at ML-DSA-65**: `K |V| ≥ 1/16`, with `K |V| =
(1048183/2^20)^1280 · (16 · 523383/q)^1536` and Bernoulli's inequality `(1 - x)^m ≥ 1 - m x`
(`one_add_mul_le_pow`). -/
theorem one_div_sixteen_le_standinScale_mul_card_mldsa65 :
    1 / 16 ≤ (standinScale mldsa65).toReal * Fintype.card (BucketVec mldsa65) := by
  obtain ⟨-, hl, hg1, -, hb, -⟩ := mldsa65_vals
  have hV : (Fintype.card (BucketVec mldsa65) : ℝ) = 16 ^ 1536 := by
    rw [card_bucketVec_coeffIndex, bucketCount_mldsa65, card_coeffIndex_mldsa65,
      Nat.cast_pow, Nat.cast_ofNat]
  have hz : (zAcceptFraction mldsa65).toReal = (1048183 / 1048576 : ℝ) ^ 1280 := by
    rw [zAcceptFraction, ENNReal.toReal_ofReal
      (pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _), hg1, hb, hl]
    congr 1
  have hu : (uniformScale mldsa65).toReal = (523383 / 8380417 : ℝ) ^ 1536 := by
    rw [toReal_uniformScale, cellSize_mldsa65, card_coeffIndex_mldsa65]
    congr 1
  rw [standinScale, ENNReal.toReal_mul, hz, hu, hV, mul_assoc, ← mul_pow]
  have h1 : (1 : ℝ) - 1280 * (393 / 1048576) ≤ (1048183 / 1048576 : ℝ) ^ 1280 := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(393 / 1048576) by norm_num) 1280
    rw [show (1 : ℝ) + -(393 / 1048576) = 1048183 / 1048576 by norm_num,
      show ((1280 : ℕ) : ℝ) = 1280 by norm_num] at h
    generalize (1048183 / 1048576 : ℝ) ^ 1280 = P at h ⊢
    linarith
  have h2 : ((1 : ℝ) - 768 * (6289 / 8380417)) ^ 2 ≤ (523383 / 8380417 * 16 : ℝ) ^ 1536 := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(6289 / 8380417) by norm_num) 768
    rw [show (1 : ℝ) + -(6289 / 8380417) = 523383 / 8380417 * 16 by norm_num,
      show ((768 : ℕ) : ℝ) = 768 by norm_num] at h
    rw [show (1536 : ℕ) = 768 * 2 by norm_num, pow_mul]
    generalize (523383 / 8380417 * 16 : ℝ) ^ 768 = P at h ⊢
    exact pow_le_pow_left₀ (by norm_num) (by linarith) 2
  calc (1 : ℝ) / 16 ≤ (1 - 1280 * (393 / 1048576)) * (1 - 768 * (6289 / 8380417)) ^ 2 := by
        norm_num
    _ ≤ (1048183 / 1048576 : ℝ) ^ 1280 * (523383 / 8380417 * 16 : ℝ) ^ 1536 :=
        mul_le_mul h1 h2 (by norm_num) (by positivity)

/-- **The stand-in scale at ML-DSA-87**: `K |V| ≥ 1/16`, with `K |V| =
(1048335/2^20)^1792 · (16 · 523535/q)^2048` and Bernoulli's inequality (`one_add_mul_le_pow`). -/
theorem one_div_sixteen_le_standinScale_mul_card_mldsa87 :
    1 / 16 ≤ (standinScale mldsa87).toReal * Fintype.card (BucketVec mldsa87) := by
  obtain ⟨-, hl, hg1, -, hb, -⟩ := mldsa87_vals
  have hV : (Fintype.card (BucketVec mldsa87) : ℝ) = 16 ^ 2048 := by
    rw [card_bucketVec_coeffIndex, bucketCount_mldsa87, card_coeffIndex_mldsa87,
      Nat.cast_pow, Nat.cast_ofNat]
  have hz : (zAcceptFraction mldsa87).toReal = (1048335 / 1048576 : ℝ) ^ 1792 := by
    rw [zAcceptFraction, ENNReal.toReal_ofReal
      (pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _), hg1, hb, hl]
    congr 1
  have hu : (uniformScale mldsa87).toReal = (523535 / 8380417 : ℝ) ^ 2048 := by
    rw [toReal_uniformScale, cellSize_mldsa87, card_coeffIndex_mldsa87]
    congr 1
  rw [standinScale, ENNReal.toReal_mul, hz, hu, hV, mul_assoc, ← mul_pow]
  have h1 : (1 : ℝ) - 1792 * (241 / 1048576) ≤ (1048335 / 1048576 : ℝ) ^ 1792 := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(241 / 1048576) by norm_num) 1792
    rw [show (1 : ℝ) + -(241 / 1048576) = 1048335 / 1048576 by norm_num,
      show ((1792 : ℕ) : ℝ) = 1792 by norm_num] at h
    generalize (1048335 / 1048576 : ℝ) ^ 1792 = P at h ⊢
    linarith
  have h2 : ((1 : ℝ) - 1024 * (3857 / 8380417)) ^ 2 ≤ (523535 / 8380417 * 16 : ℝ) ^ 2048 := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ -(3857 / 8380417) by norm_num) 1024
    rw [show (1 : ℝ) + -(3857 / 8380417) = 523535 / 8380417 * 16 by norm_num,
      show ((1024 : ℕ) : ℝ) = 1024 by norm_num] at h
    rw [show (2048 : ℕ) = 1024 * 2 by norm_num, pow_mul]
    generalize (523535 / 8380417 * 16 : ℝ) ^ 1024 = P at h ⊢
    exact pow_le_pow_left₀ (by norm_num) (by linarith) 2
  calc (1 : ℝ) / 16 ≤ (1 - 1792 * (241 / 1048576)) * (1 - 1024 * (3857 / 8380417)) ^ 2 := by
        norm_num
    _ ≤ (1048335 / 1048576 : ℝ) ^ 1792 * (523535 / 8380417 * 16 : ℝ) ^ 2048 :=
        mul_le_mul h1 h2 (by norm_num) (by positivity)

end GordieHowe.MLDSA.Regularity
