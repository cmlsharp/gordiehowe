-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.ChallengeMoments
public import GordieHowe.Foundations.ToMathlib.RademacherAbs

@[expose] public section

/-!
# The first absolute moment of a uniform challenge times a fixed polynomial

For `c` uniform on the challenge set `B_τ` of FIPS 204 (§2.3, §7.3; `ChallengeBall τ`) and a
fixed integer vector `x` with `‖x‖∞ ≤ R`, each coefficient of `c ⋆ x` is, given the support `S`
of `c`, a Rademacher sum with weights `±x_m / R` of absolute value at most `1`
(`negacyclicConvCoeff_eq_sum_weight`). The first absolute moment is bounded by the concave
function `h = Real.absMomentBound` of the variance (`Real.expect_abs_rademacher_le`), then by
Jensen's inequality over the support (`Real.expect_absMomentBound_le`):
`𝔼_c |(c ⋆ x)_k| ≤ R · h(τ/256 · ∑_m x_m² / R²)`. This is sharper than the bound
`√(τ/256 · ∑_m x_m²)` from the second moment (`expect_challengeBall_negacyclicConvCoeff_sq`).

* `signedCoeff_mul_eq_ite`, `expect_signs_abs_le`: the signed sum over a fixed support;
* `expect_seed_eq`, `expect_subset_sum_sq`: the seed average as the support average of the sign
  average, and the support average of `∑_{j ∈ S} w_j²`;
* `expect_seed_abs_le`, `expect_seed_abs_negacyclicConvCoeff_le`: the bound for a uniform seed;
* `expect_challengeBall_abs_negacyclicConvCoeff_le`: the bound for `c` uniform on `B_τ`;
* `expect_challengeBall_abs_centeredCoeffs_le`: for the shift `b = c·t₀` of `t0Weight`, when
  `‖t₀‖∞ ≤ R` and `2τR < q`;
* `sum_expect_challengeBall_abs_centeredCoeffs_le`: summed over all `256 k` coefficients, with
  Jensen's inequality over the coefficients:
  `∑_{j,i} 𝔼_c |b_{j,i}| ≤ 256 k · R · h(τ S / (256 k R²))` for `‖t₀‖₂² ≤ S`;
* `expect_challengeBall_sum_hintProb_le`: the hint mean,
  `𝔼_c ∑_i hintProb ≤ 256 k · R · h(τ S / (256 k R²)) / (2(γ₂ - β) - 1)` (`sum_hintProb_le`).
-/

open Finset Real
open scoped BigOperators

namespace GordieHowe.MLDSA

/-! ### Signed subset sums -/

section SignedSubset

variable {n τ : ℕ}

/-- A signed coefficient times a weight, as a Rademacher term: `±a_j` with `a_j = w_j` on `S`
and `0` off `S`. -/
theorem signedCoeff_mul_eq_ite (S : Finset (Fin n)) (ε : Fin n → Bool) (w : Fin n → ℝ)
    (j : Fin n) :
    (signedCoeff S ε j : ℝ) * w j =
      if ε j then (if j ∈ S then w j else 0) else -(if j ∈ S then w j else 0) := by
  unfold signedCoeff
  by_cases hj : j ∈ S <;> by_cases he : ε j <;> simp [hj, he]

/-- **The first absolute moment over the signs**: for a fixed support `S`, `R > 0` and
`|w_j| ≤ R` on `S`, `𝔼_ε |∑_j s_j w_j| ≤ R · h(∑_{j ∈ S} w_j² / R²)`. -/
theorem expect_signs_abs_le (S : Finset (Fin n)) (w : Fin n → ℝ) {R : ℝ} (hR : 0 < R)
    (hw : ∀ j ∈ S, |w j| ≤ R) :
    𝔼 ε : Fin n → Bool, |∑ j, (signedCoeff S ε j : ℝ) * w j| ≤
      R * absMomentBound (∑ j ∈ S, w j ^ 2 / R ^ 2) := by
  set a : Fin n → ℝ := fun j => if j ∈ S then w j / R else 0 with ha
  have hterm : ∀ ε : Fin n → Bool, |∑ j, (signedCoeff S ε j : ℝ) * w j| =
      R * |∑ j, if ε j then a j else -a j| := fun ε => by
    have : ∑ j, (signedCoeff S ε j : ℝ) * w j = R * ∑ j, if ε j then a j else -a j := by
      rw [mul_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [signedCoeff_mul_eq_ite]
      simp only [ha]
      by_cases hj : j ∈ S <;> cases ε j <;>
        simp only [hj, ↓reduceIte, Bool.false_eq_true, mul_neg, mul_zero, neg_zero] <;>
        field_simp
    rw [this, abs_mul, abs_of_pos hR]
  have ha1 : ∀ j, |a j| ≤ 1 := fun j => by
    simp only [ha]
    split_ifs with hj
    · rw [abs_div, abs_of_pos hR, div_le_one hR]
      exact hw j hj
    · simp
  have hsq : ∑ j, a j ^ 2 = ∑ j ∈ S, w j ^ 2 / R ^ 2 := by
    simp only [ha, ite_pow, div_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    rw [sum_ite_mem, univ_inter]
  simp_rw [hterm]
  rw [← Finset.mul_expect, ← hsq]
  exact mul_le_mul_of_nonneg_left (expect_abs_rademacher_le a ha1) hR.le

/-- **The seed average is the support average of the sign average**. -/
theorem expect_seed_eq (F : Finset (Fin n) → (Fin n → Bool) → ℝ) :
    𝔼 ω : ChallengeSeed n τ, F ω.1.1 ω.2 =
      𝔼 S : {S : Finset (Fin n) // S ∈ (univ : Finset (Fin n)).powersetCard τ},
        𝔼 ε : Fin n → Bool, F S.1 ε := by
  rw [← Finset.univ_product_univ]
  exact Finset.expect_product'
    (univ : Finset {S : Finset (Fin n) // S ∈ (univ : Finset (Fin n)).powersetCard τ})
    (univ : Finset (Fin n → Bool)) fun S ε => F S.1 ε

/-- **The support average of a sum of squares**: for a uniform `τ`-subset `S` with `τ ≤ n`,
`𝔼_S ∑_{j ∈ S} w_j² = τ/n · ∑_j w_j²`. -/
theorem expect_subset_sum_sq (hτ : τ ≤ n) (w : Fin n → ℝ) :
    𝔼 S : {S : Finset (Fin n) // S ∈ (univ : Finset (Fin n)).powersetCard τ},
        ∑ j ∈ S.1, w j ^ 2 = τ / n * ∑ j, w j ^ 2 := by
  rw [← expect_seed_sq hτ w]
  simp only [ChallengeSeed.coeff]
  rw [expect_seed_eq (fun S ε => (∑ j, (signedCoeff S ε j : ℝ) * w j) ^ 2)]
  refine Finset.expect_congr rfl fun S _ => ?_
  rw [Fintype.expect_eq_sum_div_card, sum_signs_sq, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  have : (2 : ℝ) ^ n ≠ 0 := by positivity
  push_cast
  field_simp

/-- **The first absolute moment of a signed subset sum**: for a uniform seed with `τ ≤ n`,
`R > 0` and `|w_j| ≤ R`, `𝔼_ω |∑_j c_j w_j| ≤ R · h(τ/n · ∑_j w_j² / R²)`. -/
theorem expect_seed_abs_le (hτ : τ ≤ n) (w : Fin n → ℝ) {R : ℝ} (hR : 0 < R)
    (hw : ∀ j, |w j| ≤ R) :
    𝔼 ω : ChallengeSeed n τ, |∑ j, (ω.coeff j : ℝ) * w j| ≤
      R * absMomentBound (τ / n * ∑ j, w j ^ 2 / R ^ 2) := by
  have hne : Nonempty {S : Finset (Fin n) // S ∈ (univ : Finset (Fin n)).powersetCard τ} := by
    obtain ⟨S, hS⟩ := powersetCard_nonempty.2 (by simpa using hτ :
      τ ≤ (univ : Finset (Fin n)).card)
    exact ⟨⟨S, hS⟩⟩
  simp only [ChallengeSeed.coeff]
  rw [expect_seed_eq (fun S ε => |∑ j, (signedCoeff S ε j : ℝ) * w j|)]
  have hmean := expect_subset_sum_sq hτ fun j => w j / R
  simp only [div_pow] at hmean
  calc 𝔼 S : {S : Finset (Fin n) // S ∈ (univ : Finset (Fin n)).powersetCard τ},
          𝔼 ε : Fin n → Bool, |∑ j, (signedCoeff S.1 ε j : ℝ) * w j|
        ≤ 𝔼 S : {S : Finset (Fin n) // S ∈ (univ : Finset (Fin n)).powersetCard τ},
          R * absMomentBound (∑ j ∈ S.1, w j ^ 2 / R ^ 2) :=
        Finset.expect_le_expect fun S _ => expect_signs_abs_le S.1 w hR fun j _ => hw j
    _ = R * 𝔼 S : {S : Finset (Fin n) // S ∈ (univ : Finset (Fin n)).powersetCard τ},
          absMomentBound (∑ j ∈ S.1, w j ^ 2 / R ^ 2) := by rw [Finset.mul_expect]
    _ ≤ R * absMomentBound (τ / n * ∑ j, w j ^ 2 / R ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hR.le
        refine (expect_absMomentBound_le _).trans_eq ?_
        rw [hmean]

end SignedSubset

/-! ### The negacyclic product -/

section Negacyclic

variable {n τ : ℕ}

/-- The weights of one coefficient of `c ⋆ t` are the entries of `t` up to sign. -/
theorem abs_negacyclicWeight [NeZero n] (t : Fin n → ℤ) (k j : Fin n) :
    |(negacyclicWeight t k j : ℝ)| = |(t (k - j) : ℝ)| := by
  unfold negacyclicWeight
  split_ifs
  · rfl
  · push_cast; rw [abs_neg]

/-- **The first absolute moment of a coefficient of `c ⋆ x`**: for a uniform seed with
`τ ≤ n`, `R > 0` and `|x_m| ≤ R`, `𝔼_ω |(c ⋆ x)_k| ≤ R · h(τ/n · ∑_m x_m² / R²)`. -/
theorem expect_seed_abs_negacyclicConvCoeff_le [NeZero n] (hτ : τ ≤ n) (x : Fin n → ℤ)
    (k : Fin n) {R : ℝ} (hR : 0 < R) (hx : ∀ m, |(x m : ℝ)| ≤ R) :
    𝔼 ω : ChallengeSeed n τ, |((LatticeCrypto.negacyclicConvCoeff ω.coeff x k : ℤ) : ℝ)| ≤
      R * absMomentBound (τ / n * ∑ m, (x m : ℝ) ^ 2 / R ^ 2) := by
  simp_rw [negacyclicConvCoeff_cast]
  refine (expect_seed_abs_le hτ _ hR fun j => ?_).trans_eq ?_
  · rw [abs_negacyclicWeight]; exact hx _
  · rw [sum_even_negacyclicWeight x k (fun y => y ^ 2 / R ^ 2) fun y => by ring]

end Negacyclic

/-! ### The challenge set `B_τ` -/

section Ball

open _root_.MLDSA _root_.MLDSA.Concrete LatticeCrypto TransformOps

/-- **The first absolute moment over `B_τ`**: for `c` uniform on `B_τ` with `τ ≤ 256`, `R > 0`
and `|x_m| ≤ R`, `𝔼_c |(c ⋆ x)_k| ≤ R · h(τ/256 · ∑_m x_m² / R²)`, with `c` read through its
centered coefficients. -/
theorem expect_challengeBall_abs_negacyclicConvCoeff_le {τ : ℕ} (hτ : τ ≤ ringDegree)
    (x : Fin ringDegree → ℤ) (k : Fin ringDegree) {R : ℝ} (hR : 0 < R)
    (hx : ∀ m, |(x m : ℝ)| ≤ R) :
    𝔼 c : ChallengeBall τ, |((negacyclicConvCoeff (centeredPoly c.1) x k : ℤ) : ℝ)| ≤
      R * absMomentBound (τ / ringDegree * ∑ m, (x m : ℝ) ^ 2 / R ^ 2) := by
  rw [expect_challengeBall_centered (fun c => |((negacyclicConvCoeff c x k : ℤ) : ℝ)|)]
  exact expect_seed_abs_negacyclicConvCoeff_le hτ x k hR hx

variable [nttOps : NTTRingOps] [NTTRingLaws nttOps]

/-- **The first absolute moment of the shift `b = c·t₀`**: for `c` uniform on `B_τ`,
`τ ≤ 256`, `0 < B`, `‖t₀‖∞ ≤ B` and `2τB < q`,
`𝔼_c |b_{m,i}| ≤ B · h(τ/256 · ‖t₀,m‖₂² / B²)` with `b = centeredCoeffs (c • t₀)`. -/
theorem expect_challengeBall_abs_centeredCoeffs_le {τ B k : ℕ} (hτ : τ ≤ ringDegree)
    (hB : 0 < B) (t0 : RqVec k) (ht0 : polyVecNorm t0 ≤ B) (hq : 2 * (τ * B) < modulus)
    (mi : Fin k × Fin ringDegree) :
    𝔼 c : ChallengeBall τ, |((centeredCoeffs (c.1 • t0) mi : ℤ) : ℝ)| ≤
      B * absMomentBound (τ / ringDegree * ∑ m, (centeredVec t0 mi.1 m : ℝ) ^ 2 / (B : ℝ) ^ 2) := by
  have hrow : polyNorm (t0.get mi.1) ≤ B :=
    (LatticeCrypto.PolyVec.component_cInfNorm_le normOps t0 mi.1).trans ht0
  have hx : ∀ m, |(centeredVec t0 mi.1 m : ℝ)| ≤ B := fun m => by
    have := abs_centeredPoly_le hrow m
    rw [← Int.cast_abs]
    exact_mod_cast this
  refine le_of_eq_of_le (Finset.expect_congr rfl fun c _ => ?_)
    (expect_challengeBall_abs_negacyclicConvCoeff_le hτ (centeredVec t0 mi.1) mi.2
      (by exact_mod_cast hB) hx)
  rw [centeredCoeffs_smul c.1 t0 c.2.1 c.2.2.le ht0 hq mi]

/-- **The first absolute moment of the shift, summed over the coefficients**: for `c` uniform
on `B_τ`, `τ ≤ 256`, `0 < k`, `0 < B`, `‖t₀‖∞ ≤ B`, `2τB < q` and `‖t₀‖₂² ≤ S`,
`∑_{j,i} 𝔼_c |b_{j,i}| ≤ 256 k · B · h(τ S / (256 k B²))`. Jensen's inequality for the concave
`h` over the `256 k` coefficients, and `h` increasing. -/
theorem sum_expect_challengeBall_abs_centeredCoeffs_le {τ B k : ℕ} (hτ : τ ≤ ringDegree)
    (hk : 0 < k) (hB : 0 < B) (t0 : RqVec k) (ht0 : polyVecNorm t0 ≤ B)
    (hq : 2 * (τ * B) < modulus) {S : ℝ}
    (hS : ∑ x : Fin k × Fin ringDegree, (centeredVec t0 x.1 x.2 : ℝ) ^ 2 ≤ S) :
    ∑ x : Fin k × Fin ringDegree, 𝔼 c : ChallengeBall τ, |((centeredCoeffs (c.1 • t0) x : ℤ) : ℝ)| ≤
      (ringDegree * k : ℕ) * B * absMomentBound (τ * S / ((ringDegree * k : ℕ) * (B : ℝ) ^ 2)) := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  set u : Fin k × Fin ringDegree → ℝ := fun x =>
    τ / ringDegree * ∑ m, (centeredVec t0 x.1 m : ℝ) ^ 2 / (B : ℝ) ^ 2 with hu
  have hN : ((Fintype.card (Fin k × Fin ringDegree) : ℕ) : ℝ) = (ringDegree * k : ℕ) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, mul_comm]
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hmean : 𝔼 x : Fin k × Fin ringDegree, u x =
      τ * (∑ x : Fin k × Fin ringDegree, (centeredVec t0 x.1 x.2 : ℝ) ^ 2) /
        ((ringDegree * k : ℕ) * (B : ℝ) ^ 2) := by
    rw [Fintype.expect_eq_sum_div_card, hN, hu]
    simp only
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← sum_div, ← mul_sum]
    have : (ringDegree : ℝ) ≠ 0 := by norm_num [ringDegree]
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    push_cast
    field_simp
  calc _ ≤ ∑ x : Fin k × Fin ringDegree, B * absMomentBound (u x) :=
        sum_le_sum fun x _ => expect_challengeBall_abs_centeredCoeffs_le hτ hB t0 ht0 hq x
    _ = (ringDegree * k : ℕ) * B * 𝔼 x : Fin k × Fin ringDegree, absMomentBound (u x) := by
        rw [← mul_sum, Fintype.expect_eq_sum_div_card, hN]
        have : ((ringDegree * k : ℕ) : ℝ) ≠ 0 := by
          have : 0 < ringDegree * k := Nat.mul_pos (by norm_num [ringDegree]) hk
          exact_mod_cast this.ne'
        field_simp
    _ ≤ (ringDegree * k : ℕ) * B * absMomentBound (𝔼 x : Fin k × Fin ringDegree, u x) :=
        mul_le_mul_of_nonneg_left (expect_absMomentBound_le u) (by positivity)
    _ ≤ (ringDegree * k : ℕ) * B *
          absMomentBound (τ * S / ((ringDegree * k : ℕ) * (B : ℝ) ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (monotone_absMomentBound ?_) (by positivity)
        rw [hmean]
        gcongr

/-- **The hint mean over `B_τ`**: under the hypotheses of
`sum_expect_challengeBall_abs_centeredCoeffs_le`, for every bucket vector `v`,
`𝔼_c ∑_i hintProb(v_i, b_i) ≤ 256 k · B · h(τ S / (256 k B²)) / (2(γ₂ - β) - 1)`
(`sum_hintProb_le`). -/
theorem expect_challengeBall_sum_hintProb_le {γ₂ β τ B k : ℕ} (hτ : τ ≤ ringDegree)
    (hk : 0 < k) (hB : 0 < B) (t0 : RqVec k) (ht0 : polyVecNorm t0 ≤ B)
    (hq : 2 * (τ * B) < modulus) {S : ℝ}
    (hS : ∑ x : Fin k × Fin ringDegree, (centeredVec t0 x.1 x.2 : ℝ) ^ 2 ≤ S)
    (v : Fin k × Fin ringDegree → ℕ) :
    𝔼 c : ChallengeBall τ, ∑ x, hintProb γ₂ β (v x) (centeredCoeffs (c.1 • t0) x) ≤
      (ringDegree * k : ℕ) * B * absMomentBound (τ * S / ((ringDegree * k : ℕ) * (B : ℝ) ^ 2)) /
        ((2 * (γ₂ - β) - 1 : ℕ) : ℝ) := by
  have hne := challengeBall_nonempty hτ
  refine (Finset.expect_le_expect fun c _ =>
    sum_hintProb_le γ₂ β (centeredCoeffs (c.1 • t0)) v).trans ?_
  rw [← Finset.expect_div, Finset.expect_sum_comm]
  exact div_le_div_of_nonneg_right
    (sum_expect_challengeBall_abs_centeredCoeffs_le hτ hk hB t0 ht0 hq hS) (Nat.cast_nonneg _)

end Ball

end GordieHowe.MLDSA
