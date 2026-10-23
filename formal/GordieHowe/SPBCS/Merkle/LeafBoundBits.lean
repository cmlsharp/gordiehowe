-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Merkle.LeafHidingAdaptive

@[expose] public section

/-!
# A numerical bound on the leaf term

`leafBound_two_mul_le`: at `k`-byte digests, `2k`-byte Merkle salts and leaves of at most `2^40`
bytes, the leaf term `leafBound k (2k) L` is at most `1/(2 · 2^(4k)) + 2^21/2^(8k)`. The first
summand is exact; the second bounds `√(log |Bytes L| / (2 · 2^(16k)))` through
`|Bytes L| ≤ 256^(L + 1)` (`QROM.card_bytes_le`) and `log 2 < 0.6931471808`.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM

/-- **The leaf term at `2k`-byte Merkle salts** and leaves of at most `2^40` bytes:
`leafBound k (2k) L ≤ 1/(2 · 2^(4k)) + 2^21/2^(8k)`. -/
theorem leafBound_two_mul_le {k L : ℕ} (hL : L ≤ 2 ^ 40) :
    leafBound k (2 * k) L ≤ 1 / (2 * 2 ^ (4 * k)) + 2 ^ 21 / 2 ^ (8 * k) := by
  have h16 : (2 : ℝ) ^ (8 * (2 * k)) = 2 ^ (8 * k) * 2 ^ (8 * k) := by
    rw [← pow_add]
    congr 1
    ring
  have h8 : (2 : ℝ) ^ (8 * k) = 2 ^ (4 * k) * 2 ^ (4 * k) := by
    rw [← pow_add]
    congr 1
    ring
  have hpos4 : (0 : ℝ) < 2 ^ (4 * k) := by positivity
  have hpos8 : (0 : ℝ) < 2 ^ (8 * k) := by positivity
  have hfirst : √((2 : ℝ) ^ (8 * k) / 2 ^ (8 * (2 * k))) = 1 / 2 ^ (4 * k) := by
    rw [show (2 : ℝ) ^ (8 * k) / 2 ^ (8 * (2 * k)) = (1 / 2 ^ (4 * k)) ^ 2 by
      rw [h16, h8]
      field_simp]
    exact Real.sqrt_sq (by positivity)
  have hcard : (0 : ℝ) < Fintype.card (Bytes L) := by
    exact_mod_cast Fintype.card_pos
  have hlog : Real.log (Fintype.card (Bytes L)) ≤ 2 ^ 43 := by
    have hle : (Fintype.card (Bytes L) : ℝ) ≤ 2 ^ (8 * (L + 1)) := by
      rw [pow_mul]
      exact_mod_cast card_bytes_le L
    have hL' : ((L + 1 : ℕ) : ℝ) ≤ 2 ^ 40 + 1 := by
      have : (L : ℝ) ≤ 2 ^ 40 := by exact_mod_cast hL
      push_cast
      linarith
    calc Real.log (Fintype.card (Bytes L)) ≤ Real.log (2 ^ (8 * (L + 1))) :=
          Real.log_le_log hcard hle
      _ = (8 * (L + 1) : ℕ) * Real.log 2 := by rw [Real.log_pow]
      _ ≤ 8 * (2 ^ 40 + 1) * 0.6931471808 := by
          have h2 := Real.log_two_lt_d9
          have h0 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
          push_cast at hL' ⊢
          nlinarith [mul_le_mul_of_nonneg_right hL' h0]
      _ ≤ 2 ^ 43 := by norm_num
  have hsecond : √(Real.log (Fintype.card (Bytes L)) / (2 * 2 ^ (8 * (2 * k)))) ≤
      2 ^ 21 / 2 ^ (8 * k) := by
    rw [show (2 : ℝ) ^ 21 / 2 ^ (8 * k) = √((2 ^ 21 / 2 ^ (8 * k)) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    refine Real.sqrt_le_sqrt ?_
    rw [h16, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_right hlog (sq_nonneg ((2 : ℝ) ^ (8 * k)))
    nlinarith [this]
  unfold leafBound
  rw [hfirst, div_div, mul_comm ((2 : ℝ) ^ (4 * k)) 2]
  exact add_le_add le_rfl hsecond

end GordieHowe.SPBCS
