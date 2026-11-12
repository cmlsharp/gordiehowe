-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1
public import GordieHowe.Applications.MLDSA.Regularity.CommitCollision
public import GordieHowe.Applications.MLDSA.Regularity.StandinScale

@[expose] public section

/-!
# The McDiarmid numbers of the ring publishing `w₁`

The numerical facts that bound the McDiarmid terms of the anonymity bound of the ML-DSA ring
publishing `w₁` (`w1Scheme.expect_anonAdvantage_le`, `MLDSAW1AnonOracle.lean`).

* `sqrt_add_sqrt_le_of_le`: the two square roots of the McDiarmid terms are at most
  `2c · √(N n log (C + 1)) / (θ (1 - θ) (1 - s) β_min)` when `4ε / L² + 4 / |V| ≤ c²` and
  `β |V| ≥ L β_min`.
* `four_mul_div_add_four_div_le`: `4ε / L² + 4 / |V| ≤ c²` at `ε = 2^-4352`, `L = 1/16`,
  `|V| ≥ 2^4100` and `c = 2^-2001`.
* `two_pow_le_card_bucketVec_mldsa44`, `_mldsa65`, `_mldsa87`: `|V| ≥ 2^4100`, `|V|` the number
  of bucket vectors.
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.MLDSA.Regularity PMF Finset
open scoped ENNReal BigOperators
open IOP GordieHowe.SPBCS GordieHowe.QROM

/-! ### The variance proxies at fixed users' coins -/


/-! ### The variance proxies with `ExpandA` a random oracle -/


/-! ### The explicit bound -/

/-- **The two square roots of the McDiarmid terms, explicitly**: for `n ≥ 1`, `θ ∈ (0, 1)`,
`s < 1`, `β ∈ (0, 1]`, `0 ≤ a ≤ a'`, `X ≥ L β` and `4ε / L² + 4 / W ≤ c²`,
`√(4N / (θ (1 - s))² · (2 n ε / X² + 2 / W) · a / 2) + √(N / ((1 - θ)² (1 - s)² W) · a' / 2)
≤ 2c · √(N n a') / (θ (1 - θ) (1 - s) β)`. -/
theorem sqrt_add_sqrt_le_of_le {N n θ s β W ε L X a a' c : ℝ} (hN : 0 ≤ N) (hn : 1 ≤ n)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (ha : 0 ≤ a)
    (haa : a ≤ a') (hW : 0 < W) (hL : 0 < L) (hε : 0 ≤ ε) (hc : 0 ≤ c)
    (hbound : 4 * ε / L ^ 2 + 4 / W ≤ c ^ 2) (hX : L * β ≤ X) :
    √(4 * N / (θ * (1 - s)) ^ 2 * (2 * n * ε / X ^ 2 + 2 / W) * a / 2) +
        √(N / ((1 - θ) ^ 2 * (1 - s) ^ 2 * W) * a' / 2) ≤
      2 * c * √(N * n * a') / (θ * (1 - θ) * (1 - s) * β) := by
  have hs : 0 < 1 - s := by linarith
  have hθ' : 0 < 1 - θ := by linarith
  have hn0 : 0 < n := by linarith
  have ha' : 0 ≤ a' := ha.trans haa
  set t := θ * (1 - θ) * (1 - s) * β with ht_def
  have ht : 0 < t := by positivity
  set u := θ * (1 - s) * β with hu_def
  have hu : 0 < u := by positivity
  have htu : t ≤ u := by
    have : t = u * (1 - θ) := by rw [ht_def, hu_def]; ring
    rw [this]
    exact mul_le_of_le_one_right hu.le (by linarith)
  have hY : 0 ≤ N * n * a' := by positivity
  have hR0 : 0 ≤ c * √(N * n * a') / t := by positivity
  have hR : (c * √(N * n * a') / t) ^ 2 = c ^ 2 * (N * n * a') / t ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hY]
  have hsq : ∀ x : ℝ, x ≤ c ^ 2 * (N * n * a') / t ^ 2 → √x ≤ c * √(N * n * a') / t :=
    fun x hx => (Real.sqrt_le_sqrt (hx.trans_eq hR.symm)).trans_eq (Real.sqrt_sq hR0)
  have hX0 : 0 < X := lt_of_lt_of_le (mul_pos hL hβ0) hX
  have hnβ : 1 ≤ n / β ^ 2 := by
    rw [le_div_iff₀ (by positivity), one_mul]
    exact (pow_le_one₀ hβ0.le hβ1).trans hn
  have hdev : 2 * n * ε / X ^ 2 + 2 / W ≤ n / β ^ 2 * (2 * ε / L ^ 2 + 2 / W) := by
    rw [mul_add]
    refine add_le_add ?_ (le_mul_of_one_le_left (by positivity) hnβ)
    calc 2 * n * ε / X ^ 2 ≤ 2 * n * ε / (L * β) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (pow_le_pow_left₀ (by positivity) hX 2)
      _ = n / β ^ 2 * (2 * ε / L ^ 2) := by field_simp
  have h1 : 4 * N / (θ * (1 - s)) ^ 2 * (2 * n * ε / X ^ 2 + 2 / W) * a / 2 ≤
      c ^ 2 * (N * n * a') / t ^ 2 :=
    calc 4 * N / (θ * (1 - s)) ^ 2 * (2 * n * ε / X ^ 2 + 2 / W) * a / 2
        ≤ 4 * N / (θ * (1 - s)) ^ 2 * (n / β ^ 2 * (2 * ε / L ^ 2 + 2 / W)) * a / 2 := by
          gcongr
      _ = N * n * a * (4 * ε / L ^ 2 + 4 / W) / u ^ 2 := by
          rw [hu_def]
          field_simp
      _ ≤ N * n * a' * c ^ 2 / u ^ 2 := by
          gcongr
      _ ≤ c ^ 2 * (N * n * a') / t ^ 2 := by
          rw [mul_comm (N * n * a')]
          exact div_le_div_of_nonneg_left (by positivity) (by positivity)
            (pow_le_pow_left₀ ht.le htu 2)
  have hW2 : 1 / (2 * W) ≤ c ^ 2 := by
    refine le_trans ?_ hbound
    have : 0 ≤ 4 * ε / L ^ 2 := by positivity
    have : 1 / (2 * W) ≤ 4 / W := by
      rw [div_le_div_iff₀ (by positivity) hW]
      linarith
    linarith
  have hθβ : 1 ≤ n / (θ * β) ^ 2 := by
    rw [le_div_iff₀ (by positivity), one_mul]
    exact (pow_le_one₀ (mul_pos hθ0 hβ0).le (mul_le_one₀ hθ1.le hβ0.le hβ1)).trans hn
  have h2 : N / ((1 - θ) ^ 2 * (1 - s) ^ 2 * W) * a' / 2 ≤ c ^ 2 * (N * n * a') / t ^ 2 :=
    calc N / ((1 - θ) ^ 2 * (1 - s) ^ 2 * W) * a' / 2
        = N * a' * (1 / (2 * W)) / ((1 - θ) ^ 2 * (1 - s) ^ 2) := by
          field_simp
      _ ≤ N * a' * c ^ 2 / ((1 - θ) ^ 2 * (1 - s) ^ 2) := by
          gcongr
      _ ≤ N * a' * c ^ 2 / ((1 - θ) ^ 2 * (1 - s) ^ 2) * (n / (θ * β) ^ 2) :=
          le_mul_of_one_le_right (by positivity) hθβ
      _ = c ^ 2 * (N * n * a') / t ^ 2 := by
          rw [ht_def]
          field_simp
  have := hsq _ h1
  have := hsq _ h2
  have e : 2 * c * √(N * n * a') / t = c * √(N * n * a') / t + c * √(N * n * a') / t := by ring
  rw [e]
  exact add_le_add (hsq _ h1) (hsq _ h2)

/-- At ML-DSA-44 there are `44^1024 ≥ 2^5120 ≥ 2^4100` bucket vectors. -/
theorem two_pow_le_card_bucketVec_mldsa44 :
    (2 : ℝ) ^ 4100 ≤ Fintype.card (BucketVec _root_.MLDSA.mldsa44) := by
  rw [card_bucketVec_coeffIndex, bucketCount_mldsa44, card_coeffIndex_mldsa44,
    Nat.cast_pow, Nat.cast_ofNat]
  calc (2 : ℝ) ^ 4100 ≤ 2 ^ (5 * 1024) := pow_le_pow_right₀ (by norm_num) (by norm_num)
    _ = (2 ^ 5) ^ 1024 := pow_mul 2 5 1024
    _ ≤ 44 ^ 1024 := pow_le_pow_left₀ (by norm_num) (by norm_num) _

/-- At ML-DSA-65 there are `16^1536 = 2^6144 ≥ 2^4100` bucket vectors. -/
theorem two_pow_le_card_bucketVec_mldsa65 :
    (2 : ℝ) ^ 4100 ≤ Fintype.card (BucketVec mldsa65) := by
  rw [card_bucketVec_coeffIndex, bucketCount_mldsa65, card_coeffIndex_mldsa65,
    Nat.cast_pow, Nat.cast_ofNat, show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul]
  exact pow_le_pow_right₀ (by norm_num) (by norm_num)

/-- At ML-DSA-87 there are `16^2048 = 2^8192 ≥ 2^4100` bucket vectors. -/
theorem two_pow_le_card_bucketVec_mldsa87 :
    (2 : ℝ) ^ 4100 ≤ Fintype.card (BucketVec mldsa87) := by
  rw [card_bucketVec_coeffIndex, bucketCount_mldsa87, card_coeffIndex_mldsa87,
    Nat.cast_pow, Nat.cast_ofNat, show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_mul]
  exact pow_le_pow_right₀ (by norm_num) (by norm_num)

/-- **The numbers of the explicit bound**: `4 · 2^-4352 / (1/16)² + 4 · 2^-4100 ≤ (2^-2001)²`. -/
theorem four_mul_div_add_four_div_le :
    4 * ((1 / 2 ^ 17 : ℝ) ^ 256) / (1 / 16) ^ 2 + 4 / 2 ^ 4100 ≤ (1 / 2 ^ 2001 : ℝ) ^ 2 := by
  have e1 : 4 * ((1 / 2 ^ 17 : ℝ) ^ 256) / (1 / 16) ^ 2 = 1 / 2 ^ 4342 := by
    rw [div_pow, one_pow, ← pow_mul, show 17 * 256 = 4342 + 10 from rfl, pow_add]
    field_simp
    norm_num
  have e2 : (1 / 2 ^ 2001 : ℝ) ^ 2 = 1 / 2 ^ 4002 := by
    rw [div_pow, one_pow, ← pow_mul]
  rw [e1, e2]
  have h3 : (1 : ℝ) / 2 ^ 4342 ≤ 1 / 2 ^ 4003 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num))
  have h4 : (4 : ℝ) / 2 ^ 4100 ≤ 1 / 2 ^ 4003 := by
    have h : (4 : ℝ) ≤ 2 ^ 97 :=
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ 97 := pow_le_pow_right₀ (by norm_num) (by norm_num)
    rw [div_le_div_iff₀ (by positivity) (by positivity), show 4100 = 4003 + 97 from rfl,
      pow_add, one_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left h (by positivity)
  have h5 : (1 : ℝ) / 2 ^ 4003 + 1 / 2 ^ 4003 = 1 / 2 ^ 4002 := by
    rw [show 4003 = 4002 + 1 from rfl, pow_succ]
    field_simp
    norm_num
  exact (add_le_add h3 h4).trans_eq h5

/-! ### The McDiarmid terms with `ExpandA` a random oracle, explicitly -/


end GordieHowe.Ring.MLDSAW1
