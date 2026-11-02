-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.ChallengeAbsMoment
public import GordieHowe.Foundations.ToMathlib.RademacherConvex
public import GordieHowe.Foundations.ToMathlib.SamplingWithoutReplacement

@[expose] public section

/-!
# Tails of a uniform challenge times a fixed polynomial

For `c` uniform on the challenge set `B_τ` of FIPS 204 (§2.3, §7.3; `ChallengeBall τ`) and a fixed
integer vector `x` with `‖x‖∞ ≤ R`, each coefficient of `c ⋆ x` is, given the support `S` of `c`,
a sum `∑_{j ∈ S} ε_j w_j` with independent uniform signs `ε_j` and weights `|w_j| ≤ R`
(`negacyclicConvCoeff_eq_sum_weight`). Two tail bounds for the coefficients of the shift
`b = c·t₀` of the ct₀-check (FIPS 204 Algorithm 7 line 28, `|b_i| < γ₂`):

**A bound through the norm of `t₀`** (Chernoff with the cosh chord).

* `expect_seed_exp_eq`: given the support the signs are independent, so
  `𝔼_ω exp(λ ∑_j c_j w_j) = 𝔼_S ∏_{j ∈ S} cosh(λ w_j)`;
* `expect_subset_prod_le`: Maclaurin's inequality for the elementary symmetric function of degree
  `τ` (`Finset.subsetProdSum_le`), `𝔼_S ∏_{j ∈ S} g_j ≤ (mean_j g_j)^τ` for `g ≥ 0`;
* `expect_seed_exp_le_chord`: with `cosh(u a) ≤ 1 + (cosh u - 1) a²`
  (`Real.cosh_mul_le_one_add_mul_sq`),
  `𝔼_ω exp(u/R ∑_j c_j w_j) ≤ (mean_j (1 + (cosh u - 1) (w_j/R)²))^τ`;
* `expect_indicator_le_two_mul_exp`: Chernoff's bound for `|X|` from both exponential moments;
* `expect_challengeBall_exp_centeredCoeffs_le_chord`,
  `expect_challengeBall_indicator_centeredCoeffs_le_chord`: for `‖t₀‖∞ ≤ B`, `2τB < q` and
  `u ≥ 0`, `Pr_c[|b_{m,i}| ≥ γ] ≤ 2 e^{-u γ / B} (1 + (cosh u - 1) s_m)^τ` with
  `s_m = ‖t₀,m‖₂² / (256 B²)`.

**A bound for every `t₀`** (the convex comparison).

* `expect_seed_convex_le`: for convex `g` and `|w_j| ≤ R`,
  `𝔼_ω g(∑_j c_j w_j / R) ≤ 𝔼 g(S_τ)` with `S_τ` the simple random walk with `τ` steps
  (`Real.sum_bool_convex_le`, `Real.expect_bool_sum_mask`);
* `expect_challengeBall_convex_centeredCoeffs_le`: the same for the shift `b = c·t₀`;
* `expect_challengeBall_indicator_centeredCoeffs_le_hinge`: with the hinge
  `g(y) = max(|y| - θ, 0)` and `θ < γ/B`, `Pr_c[|b_{m,i}| ≥ γ] ≤ 𝔼 g(S_τ) / (γ/B - θ)`.

**The ct₀-check** (a union over the `256 k` coefficients).

* `one_sub_sum_indicator_le_indicator_forall`: `1 - ∑_i 1[γ ≤ |b_i|] ≤ 1[∀ i, |b_i| < γ]`;
* `one_sub_le_expect_challengeBall_ct0_chord`, `one_sub_le_expect_challengeBall_ct0_hinge`: the
  ct₀-check passes with probability at least `1 - 256 k δ` for the per-coefficient bounds `δ`
  above.
-/

open Finset Real
open scoped BigOperators

namespace GordieHowe.MLDSA

/-! ### Chernoff's bound for an absolute value -/

/-- **Chernoff's bound for `|X|` from both exponential moments**: for `λ ≥ 0`, if
`𝔼 exp(λ X) ≤ M` and `𝔼 exp(-λ X) ≤ M`, then `Pr[γ ≤ |X|] ≤ 2 e^{-λ γ} M`
(`indicator_le_exp_add_exp`). -/
theorem expect_indicator_le_two_mul_exp {Ω : Type*} [Fintype Ω] (X : Ω → ℝ) {lam M : ℝ}
    (hlam : 0 ≤ lam) (γ : ℝ) (hpos : 𝔼 ω, exp (lam * X ω) ≤ M)
    (hneg : 𝔼 ω, exp (-(lam * X ω)) ≤ M) :
    𝔼 ω, (if γ ≤ |X ω| then 1 else 0 : ℝ) ≤ 2 * exp (-(lam * γ)) * M := by
  calc 𝔼 ω, (if γ ≤ |X ω| then 1 else 0 : ℝ)
      ≤ 𝔼 ω, exp (-(lam * γ)) * (exp (lam * X ω) + exp (-(lam * X ω))) :=
        Finset.expect_le_expect fun ω _ => indicator_le_exp_add_exp hlam
    _ = exp (-(lam * γ)) * ((𝔼 ω, exp (lam * X ω)) + 𝔼 ω, exp (-(lam * X ω))) := by
        rw [← Finset.mul_expect, Finset.expect_add_distrib]
    _ ≤ exp (-(lam * γ)) * (M + M) := by gcongr
    _ = 2 * exp (-(lam * γ)) * M := by ring

/-! ### Signed subset sums -/

section SignedSubset

variable {n τ : ℕ}

/-- **Given the support, the signs are independent**: for a uniform seed and every `λ`,
`𝔼_ω exp(λ ∑_j c_j w_j) = 𝔼_S ∏_{j ∈ S} cosh(λ w_j)` with `S` a uniform `τ`-subset
(`sum_signs_exp`). -/
theorem expect_seed_exp_eq (w : Fin n → ℝ) (lam : ℝ) :
    𝔼 ω : ChallengeSeed n τ, exp (lam * ∑ j, (ω.coeff j : ℝ) * w j) =
      𝔼 S : {S : Finset (Fin n) // S ∈ (univ : Finset (Fin n)).powersetCard τ},
        ∏ j ∈ S.1, cosh (lam * w j) := by
  simp only [ChallengeSeed.coeff]
  rw [expect_seed_eq (fun S ε => exp (lam * ∑ j, (signedCoeff S ε j : ℝ) * w j))]
  refine Finset.expect_congr rfl fun S _ => ?_
  rw [Fintype.expect_eq_sum_div_card, sum_signs_exp, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  have : (2 : ℝ) ^ n ≠ 0 := by positivity
  push_cast
  exact mul_div_cancel_left₀ _ this

/-- **Maclaurin's inequality as an expectation**: for a uniform `τ`-subset `S` and `g ≥ 0`,
`𝔼_S ∏_{j ∈ S} g_j ≤ (mean_j g_j)^τ` (`Finset.subsetProdSum_le`: the elementary symmetric function
of degree `τ` is at most `C(n, τ)` times the `τ`-th power of the mean). -/
theorem expect_subset_prod_le {g : Fin n → ℝ} (hg : ∀ j, 0 ≤ g j) :
    𝔼 S : {S : Finset (Fin n) // S ∈ (univ : Finset (Fin n)).powersetCard τ},
        ∏ j ∈ S.1, g j ≤ ((∑ j, g j) / n) ^ τ := by
  rw [Fintype.expect_eq_sum_div_card,
    Finset.sum_coe_sort (univ.powersetCard τ) fun S => ∏ j ∈ S, g j,
    Fintype.card_coe, card_powersetCard, card_univ, Fintype.card_fin]
  have hR : 0 ≤ ((∑ j, g j) / n) ^ τ :=
    pow_nonneg (div_nonneg (sum_nonneg fun j _ => hg j) (Nat.cast_nonneg _)) _
  rcases Nat.eq_zero_or_pos (n.choose τ) with h0 | hpos
  · simp [h0, hR]
  rw [div_le_iff₀ (by exact_mod_cast hpos)]
  have := subsetProdSum_le (s := (univ : Finset (Fin n))) (a := g) (fun j _ => hg j) τ
  rw [card_univ, Fintype.card_fin] at this
  unfold subsetProdSum at this
  linarith

/-- The chord weight `1 + (cosh u - 1) a²` is nonnegative. -/
theorem one_add_cosh_sub_one_mul_nonneg (u a : ℝ) : 0 ≤ 1 + (cosh u - 1) * a ^ 2 :=
  add_nonneg zero_le_one (mul_nonneg (sub_nonneg.2 (one_le_cosh u)) (sq_nonneg a))

/-- **The exponential moment of a signed subset sum, through the cosh chord**: for a uniform seed,
`R > 0`, `|w_j| ≤ R` and every `u`,
`𝔼_ω exp(u/R ∑_j c_j w_j) ≤ (mean_j (1 + (cosh u - 1) (w_j/R)²))^τ`. -/
theorem expect_seed_exp_le_chord (w : Fin n → ℝ) {R : ℝ} (hR : 0 < R) (hw : ∀ j, |w j| ≤ R)
    (u : ℝ) :
    𝔼 ω : ChallengeSeed n τ, exp (u / R * ∑ j, (ω.coeff j : ℝ) * w j) ≤
      ((∑ j, (1 + (cosh u - 1) * (w j / R) ^ 2)) / n) ^ τ := by
  rw [expect_seed_exp_eq]
  refine (Finset.expect_le_expect fun S _ =>
    prod_le_prod₀ (fun j _ => (cosh_pos _).le) fun j _ => ?_).trans
    (expect_subset_prod_le fun j => one_add_cosh_sub_one_mul_nonneg u _)
  rw [show u / R * w j = u * (w j / R) by ring]
  refine cosh_mul_le_one_add_mul_sq u ?_
  rw [abs_div, abs_of_pos hR, div_le_one hR]
  exact hw j

/-- **The convex comparison for a signed subset sum**: for a uniform seed with `τ ≤ n`, convex
`g`, `R > 0` and `|w_j| ≤ R`, `𝔼_ω g(∑_j c_j w_j / R) ≤ 𝔼 g(S_τ)` with
`𝔼 g(S_τ) = 2^(-τ) ∑_{k ≤ τ} C(τ, k) g(k - (τ - k))` (`Real.sum_bool_convex_le`,
`Real.expect_bool_sum_mask`). -/
theorem expect_seed_convex_le (hτ : τ ≤ n) {g : ℝ → ℝ} (hg : ConvexOn ℝ Set.univ g)
    (w : Fin n → ℝ) {R : ℝ} (hR : 0 < R) (hw : ∀ j, |w j| ≤ R) :
    𝔼 ω : ChallengeSeed n τ, g ((∑ j, (ω.coeff j : ℝ) * w j) / R) ≤
      (∑ j ∈ range (τ + 1), (τ.choose j : ℝ) * g (j - ((τ - j : ℕ) : ℝ))) / 2 ^ τ := by
  have hne : Nonempty {S : Finset (Fin n) // S ∈ (univ : Finset (Fin n)).powersetCard τ} := by
    obtain ⟨S, hS⟩ := powersetCard_nonempty.2 (by simpa using hτ :
      τ ≤ (univ : Finset (Fin n)).card)
    exact ⟨⟨S, hS⟩⟩
  simp only [ChallengeSeed.coeff]
  rw [expect_seed_eq (fun S ε => g ((∑ j, (signedCoeff S ε j : ℝ) * w j) / R))]
  refine (Finset.expect_le_expect fun S _ => ?_).trans_eq
    (Finset.expect_const univ_nonempty _)
  have hS : #S.1 = τ := (mem_powersetCard.1 S.2).2
  set a : Fin n → ℝ := fun j => if j ∈ S.1 then w j / R else 0 with ha
  set b : Fin n → ℝ := fun j => if j ∈ S.1 then 1 else 0 with hb
  have hεa : ∀ ε : Fin n → Bool, (∑ j, (signedCoeff S.1 ε j : ℝ) * w j) / R =
      ∑ j, if ε j then a j else -a j := fun ε => by
    rw [sum_div]
    refine sum_congr rfl fun j _ => ?_
    rw [signedCoeff_mul_eq_ite]
    simp only [ha]
    by_cases hj : j ∈ S.1 <;> cases ε j <;> simp [hj, neg_div]
  have hεb : ∀ ε : Fin n → Bool, (∑ j, if ε j then b j else -b j) =
      0 + ∑ j ∈ S.1, if ε j then (1 : ℝ) else -1 := fun ε => by
    rw [zero_add, ← sum_filter_add_sum_filter_not univ (· ∈ S.1)]
    have h1 : ∑ j ∈ univ.filter (· ∈ S.1), (if ε j then b j else -b j) =
        ∑ j ∈ S.1, if ε j then (1 : ℝ) else -1 := by
      rw [filter_mem_eq_inter, univ_inter]
      exact sum_congr rfl fun j hj => by simp [hb, hj]
    have h2 : ∑ j ∈ univ.filter (· ∉ S.1), (if ε j then b j else -b j) = 0 :=
      sum_eq_zero fun j hj => by simp [hb, (mem_filter.1 hj).2]
    rw [h1, h2, add_zero]
  have hab : ∀ j, |a j| ≤ |b j| := fun j => by
    simp only [ha, hb]
    split_ifs
    · rw [abs_div, abs_of_pos hR, abs_one, div_le_one hR]
      exact hw j
    · simp
  have hcard : ((Fintype.card (Fin n → Bool) : ℕ) : ℝ) ≠ 0 := by positivity
  simp_rw [hεa]
  rw [Fintype.expect_eq_sum_div_card]
  refine (div_le_div_of_nonneg_right (sum_bool_convex_le hg hab) (Nat.cast_nonneg _)).trans_eq ?_
  rw [← Fintype.expect_eq_sum_div_card]
  simp_rw [hεb]
  rw [expect_bool_sum_mask g S.1 0, hS]
  simp only [zero_add]

end SignedSubset

/-! ### The negacyclic product -/

section Negacyclic

variable {n τ : ℕ}

/-- **The exponential moment of a coefficient of `c ⋆ x`, through the cosh chord**: for a uniform
seed, `R > 0`, `|x_m| ≤ R` and every `u`,
`𝔼_ω exp(u/R (c ⋆ x)_k) ≤ (mean_m (1 + (cosh u - 1) (x_m/R)²))^τ`. -/
theorem expect_seed_exp_negacyclicConvCoeff_le_chord [NeZero n] (x : Fin n → ℤ) (k : Fin n)
    {R : ℝ} (hR : 0 < R) (hx : ∀ m, |(x m : ℝ)| ≤ R) (u : ℝ) :
    𝔼 ω : ChallengeSeed n τ,
        exp (u / R * ((LatticeCrypto.negacyclicConvCoeff ω.coeff x k : ℤ) : ℝ)) ≤
      ((∑ m, (1 + (cosh u - 1) * ((x m : ℝ) / R) ^ 2)) / n) ^ τ := by
  simp_rw [negacyclicConvCoeff_cast]
  refine (expect_seed_exp_le_chord _ hR (fun j => by rw [abs_negacyclicWeight]; exact hx _)
    u).trans_eq ?_
  rw [sum_even_negacyclicWeight x k (fun y => 1 + (cosh u - 1) * (y / R) ^ 2) fun y => by ring]

/-- **The convex comparison for a coefficient of `c ⋆ x`**: for a uniform seed with `τ ≤ n`,
convex `g`, `R > 0` and `|x_m| ≤ R`, `𝔼_ω g((c ⋆ x)_k / R) ≤ 𝔼 g(S_τ)`. -/
theorem expect_seed_convex_negacyclicConvCoeff_le [NeZero n] (hτ : τ ≤ n) {g : ℝ → ℝ}
    (hg : ConvexOn ℝ Set.univ g) (x : Fin n → ℤ) (k : Fin n) {R : ℝ} (hR : 0 < R)
    (hx : ∀ m, |(x m : ℝ)| ≤ R) :
    𝔼 ω : ChallengeSeed n τ, g (((LatticeCrypto.negacyclicConvCoeff ω.coeff x k : ℤ) : ℝ) / R) ≤
      (∑ j ∈ range (τ + 1), (τ.choose j : ℝ) * g (j - ((τ - j : ℕ) : ℝ))) / 2 ^ τ := by
  simp_rw [negacyclicConvCoeff_cast]
  exact expect_seed_convex_le hτ hg _ hR fun j => by rw [abs_negacyclicWeight]; exact hx _

end Negacyclic

/-! ### The challenge set `B_τ` -/

section Ball

open _root_.MLDSA _root_.MLDSA.Concrete LatticeCrypto TransformOps

/-- The mean of the chord weights is the chord weight of the mean square:
`mean_m (1 + C (x_m/R)²) = 1 + C ∑_m x_m² / (256 R²)`. -/
theorem sum_chordWeight_div (x : Fin ringDegree → ℤ) (C : ℝ) {R : ℝ} (hR : 0 < R) :
    (∑ m, (1 + C * ((x m : ℝ) / R) ^ 2)) / ringDegree =
      1 + C * (∑ m, (x m : ℝ) ^ 2 / (ringDegree * R ^ 2)) := by
  have h256 : (ringDegree : ℝ) ≠ 0 := by norm_num [ringDegree]
  have h : ∑ m, (1 + C * ((x m : ℝ) / R) ^ 2) =
      ringDegree + C * ((∑ m, (x m : ℝ) ^ 2) / R ^ 2) := by
    rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, ← mul_sum]
    simp only [div_pow]
    rw [← sum_div]
  rw [h, ← sum_div]
  field_simp

/-- `‖t₀‖∞ ≤ B` bounds every centered coefficient of every component of `t₀`. -/
theorem abs_centeredVec_le {k B : ℕ} (t0 : RqVec k) (ht0 : polyVecNorm t0 ≤ B) (m : Fin k)
    (i : Fin ringDegree) : |(centeredVec t0 m i : ℝ)| ≤ B := by
  have hrow : polyNorm (t0.get m) ≤ B :=
    (LatticeCrypto.PolyVec.component_cInfNorm_le normOps t0 m).trans ht0
  have := abs_centeredPoly_le hrow i
  rw [← Int.cast_abs]
  exact_mod_cast this

/-- **The union bound for the ct₀-check**: `1 - ∑_i 1[γ ≤ |b_i|] ≤ 1[∀ i, |b_i| < γ]`. -/
theorem one_sub_sum_indicator_le_indicator_forall {ι : Type*} [Fintype ι] (b : ι → ℤ) (γ : ℕ) :
    1 - ∑ i, (if (γ : ℝ) ≤ |(b i : ℝ)| then 1 else 0 : ℝ) ≤
      (if ∀ i, |b i| < γ then 1 else 0 : ℝ) := by
  have h0 : 0 ≤ ∑ i, (if (γ : ℝ) ≤ |(b i : ℝ)| then 1 else 0 : ℝ) :=
    sum_nonneg fun i _ => by split_ifs <;> norm_num
  split_ifs with h
  · linarith
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hi' : (γ : ℝ) ≤ |(b i : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast hi
    have := single_le_sum (f := fun i => (if (γ : ℝ) ≤ |(b i : ℝ)| then 1 else 0 : ℝ))
      (fun j _ => by split_ifs <;> norm_num) (mem_univ i)
    simp only [hi', ↓reduceIte] at this
    linarith

variable [nttOps : NTTRingOps] [NTTRingLaws nttOps]

/-- **The exponential moment of the shift `b = c·t₀`, through the cosh chord**: for `c` uniform
on `B_τ`, `0 < B`, `‖t₀‖∞ ≤ B`, `2τB < q` and every `u`,
`𝔼_c exp(u/B · b_{m,i}) ≤ (1 + (cosh u - 1) s_m)^τ` with `s_m = ‖t₀,m‖₂² / (256 B²)`. -/
theorem expect_challengeBall_exp_centeredCoeffs_le_chord {τ B k : ℕ} (hB : 0 < B)
    (t0 : RqVec k) (ht0 : polyVecNorm t0 ≤ B) (hq : 2 * (τ * B) < modulus)
    (mi : Fin k × Fin ringDegree) (u : ℝ) :
    𝔼 c : ChallengeBall τ, exp (u / B * (centeredCoeffs (c.1 • t0) mi : ℝ)) ≤
      (1 + (cosh u - 1) *
        (∑ m, (centeredVec t0 mi.1 m : ℝ) ^ 2 / (ringDegree * (B : ℝ) ^ 2))) ^ τ := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  rw [← sum_chordWeight_div _ _ hBR]
  have h := expect_seed_exp_negacyclicConvCoeff_le_chord (τ := τ) (centeredVec t0 mi.1) mi.2 hBR
    (abs_centeredVec_le t0 ht0 mi.1) u
  refine le_of_eq_of_le ((Finset.expect_congr rfl fun c _ => ?_).trans
    (expect_challengeBall_centered (fun c => exp (u / B *
      ((negacyclicConvCoeff c (centeredVec t0 mi.1) mi.2 : ℤ) : ℝ))))) h
  rw [centeredCoeffs_smul c.1 t0 c.2.1 c.2.2.le ht0 hq mi]

/-- **The per-coefficient tail of the shift `b = c·t₀`, through the norm of `t₀`**: for `c`
uniform on `B_τ`, `0 < B`, `‖t₀‖∞ ≤ B`, `2τB < q`, `u ≥ 0` and every `γ`,
`Pr_c[|b_{m,i}| ≥ γ] ≤ 2 e^{-u γ / B} (1 + (cosh u - 1) s_m)^τ` with
`s_m = ‖t₀,m‖₂² / (256 B²)`. Chernoff's bound with the rate `u / B`
(`expect_challengeBall_exp_centeredCoeffs_le_chord` at `±u`). -/
theorem expect_challengeBall_indicator_centeredCoeffs_le_chord {τ B k : ℕ} (hB : 0 < B)
    (t0 : RqVec k) (ht0 : polyVecNorm t0 ≤ B) (hq : 2 * (τ * B) < modulus)
    (mi : Fin k × Fin ringDegree) {u : ℝ} (hu : 0 ≤ u) (γ : ℝ) :
    𝔼 c : ChallengeBall τ, (if γ ≤ |(centeredCoeffs (c.1 • t0) mi : ℝ)| then 1 else 0 : ℝ) ≤
      2 * exp (-(u * γ / B)) * (1 + (cosh u - 1) *
        (∑ m, (centeredVec t0 mi.1 m : ℝ) ^ 2 / (ringDegree * (B : ℝ) ^ 2))) ^ τ := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have h := expect_indicator_le_two_mul_exp (fun c : ChallengeBall τ =>
    (centeredCoeffs (c.1 • t0) mi : ℝ)) (div_nonneg hu hBR.le) γ
    (expect_challengeBall_exp_centeredCoeffs_le_chord hB t0 ht0 hq mi u) ?_
  · refine h.trans_eq ?_
    rw [div_mul_eq_mul_div]
  · have hn := expect_challengeBall_exp_centeredCoeffs_le_chord hB t0 ht0 hq mi (-u)
    rw [cosh_neg] at hn
    refine le_of_eq_of_le (Finset.expect_congr rfl fun c _ => ?_) hn
    rw [neg_div, neg_mul]

/-- **The convex comparison for the shift `b = c·t₀`**: for `c` uniform on `B_τ` with
`τ ≤ 256`, convex `g`, `0 < B`, `‖t₀‖∞ ≤ B` and `2τB < q`,
`𝔼_c g(b_{m,i} / B) ≤ 𝔼 g(S_τ) = 2^(-τ) ∑_{k ≤ τ} C(τ, k) g(k - (τ - k))`, for every `t₀`. -/
theorem expect_challengeBall_convex_centeredCoeffs_le {τ B k : ℕ} (hτ : τ ≤ ringDegree)
    {g : ℝ → ℝ} (hg : ConvexOn ℝ Set.univ g) (hB : 0 < B) (t0 : RqVec k)
    (ht0 : polyVecNorm t0 ≤ B) (hq : 2 * (τ * B) < modulus) (mi : Fin k × Fin ringDegree) :
    𝔼 c : ChallengeBall τ, g ((centeredCoeffs (c.1 • t0) mi : ℝ) / B) ≤
      (∑ j ∈ range (τ + 1), (τ.choose j : ℝ) * g (j - ((τ - j : ℕ) : ℝ))) / 2 ^ τ := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have h := expect_seed_convex_negacyclicConvCoeff_le hτ hg (centeredVec t0 mi.1) mi.2 hBR
    (abs_centeredVec_le t0 ht0 mi.1)
  refine le_of_eq_of_le ((Finset.expect_congr rfl fun c _ => ?_).trans
    (expect_challengeBall_centered (fun c => g
      (((negacyclicConvCoeff c (centeredVec t0 mi.1) mi.2 : ℤ) : ℝ) / B)))) h
  rw [centeredCoeffs_smul c.1 t0 c.2.1 c.2.2.le ht0 hq mi]

/-- **The per-coefficient tail of the shift for every `t₀`**: for `c` uniform on `B_τ` with
`τ ≤ 256`, `0 < B`, `‖t₀‖∞ ≤ B`, `2τB < q` and `θ < γ / B`,
`Pr_c[|b_{m,i}| ≥ γ] ≤ 𝔼 max(|S_τ| - θ, 0) / (γ/B - θ)`
(`expect_challengeBall_convex_centeredCoeffs_le` with the hinge, `Real.convexOn_hinge`). -/
theorem expect_challengeBall_indicator_centeredCoeffs_le_hinge {τ B k : ℕ} (hτ : τ ≤ ringDegree)
    (hB : 0 < B) (t0 : RqVec k) (ht0 : polyVecNorm t0 ≤ B) (hq : 2 * (τ * B) < modulus)
    (mi : Fin k × Fin ringDegree) {γ θ : ℝ} (hθ : θ < γ / B) :
    𝔼 c : ChallengeBall τ, (if γ ≤ |(centeredCoeffs (c.1 • t0) mi : ℝ)| then 1 else 0 : ℝ) ≤
      (∑ j ∈ range (τ + 1), (τ.choose j : ℝ) * max (|(j : ℝ) - ((τ - j : ℕ) : ℝ)| - θ) 0) /
        2 ^ τ / (γ / B - θ) := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hD : 0 < γ / B - θ := sub_pos.2 hθ
  have hpt : ∀ y : ℝ, (if γ ≤ |y| then 1 else 0 : ℝ) ≤ max (|y / B| - θ) 0 / (γ / B - θ) :=
    fun y => by
      split_ifs with h
      · rw [le_div_iff₀ hD, one_mul]
        refine le_max_of_le_left ?_
        rw [abs_div, abs_of_pos hBR]
        exact sub_le_sub_right (div_le_div_of_nonneg_right h hBR.le) θ
      · exact div_nonneg (le_max_right _ _) hD.le
  refine (Finset.expect_le_expect fun c _ => hpt _).trans ?_
  rw [← Finset.expect_div]
  exact div_le_div_of_nonneg_right
    (expect_challengeBall_convex_centeredCoeffs_le hτ (convexOn_hinge θ) hB t0 ht0 hq mi) hD.le

/-! ### The ct₀-check -/

omit [NTTRingLaws nttOps] in
/-- **The ct₀-check from per-coefficient tails**: if `Pr_c[|b_x| ≥ γ] ≤ δ` for each of the
`256 k` coefficients of `b = c·t₀`, the check `‖b‖∞ < γ` passes with probability at least
`1 - 256 k δ`. -/
theorem one_sub_le_expect_challengeBall_ct0 {τ k : ℕ} (t0 : RqVec k) (γ : ℕ) {δ : ℝ}
    (hδ : ∀ x : Fin k × Fin ringDegree, 𝔼 c : ChallengeBall τ,
      (if (γ : ℝ) ≤ |(centeredCoeffs (c.1 • t0) x : ℝ)| then 1 else 0 : ℝ) ≤ δ)
    (hτ : τ ≤ ringDegree) :
    1 - (ringDegree * k : ℕ) * δ ≤
      𝔼 c : ChallengeBall τ, (if ∀ x, |centeredCoeffs (c.1 • t0) x| < γ then 1 else 0 : ℝ) := by
  have hne := challengeBall_nonempty hτ
  have hcard : ((Fintype.card (Fin k × Fin ringDegree) : ℕ) : ℝ) = (ringDegree * k : ℕ) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, mul_comm]
  calc 1 - (ringDegree * k : ℕ) * δ
      ≤ 1 - ∑ x : Fin k × Fin ringDegree, 𝔼 c : ChallengeBall τ,
          (if (γ : ℝ) ≤ |(centeredCoeffs (c.1 • t0) x : ℝ)| then 1 else 0 : ℝ) := by
        refine sub_le_sub_left ((sum_le_sum fun x _ => hδ x).trans_eq ?_) 1
        rw [sum_const, card_univ, nsmul_eq_mul, hcard]
    _ = 𝔼 c : ChallengeBall τ, (1 - ∑ x : Fin k × Fin ringDegree,
          (if (γ : ℝ) ≤ |(centeredCoeffs (c.1 • t0) x : ℝ)| then 1 else 0 : ℝ)) := by
        rw [Finset.expect_sub_distrib, Finset.expect_const univ_nonempty, Finset.expect_sum_comm]
    _ ≤ _ := Finset.expect_le_expect fun c _ =>
        one_sub_sum_indicator_le_indicator_forall (centeredCoeffs (c.1 • t0)) γ

/-- **The ct₀-check through the norms of the components of `t₀`**: for `c` uniform on `B_τ`
with `τ ≤ 256`, `0 < B`, `‖t₀‖∞ ≤ B`, `2τB < q`, `u ≥ 0` and `‖t₀,m‖₂² / (256 B²) ≤ s` for every
component `m`, the check `‖c·t₀‖∞ < γ` passes with probability at least
`1 - 256 k · 2 e^{-u γ / B} (1 + (cosh u - 1) s)^τ`. -/
theorem one_sub_le_expect_challengeBall_ct0_chord {τ B k : ℕ} (hτ : τ ≤ ringDegree) (hB : 0 < B)
    (t0 : RqVec k) (ht0 : polyVecNorm t0 ≤ B) (hq : 2 * (τ * B) < modulus) {u : ℝ} (hu : 0 ≤ u)
    (γ : ℕ) {s : ℝ}
    (hs : ∀ m, ∑ i, (centeredVec t0 m i : ℝ) ^ 2 / (ringDegree * (B : ℝ) ^ 2) ≤ s) :
    1 - (ringDegree * k : ℕ) * (2 * exp (-(u * γ / B)) * (1 + (cosh u - 1) * s) ^ τ) ≤
      𝔼 c : ChallengeBall τ, (if ∀ x, |centeredCoeffs (c.1 • t0) x| < γ then 1 else 0 : ℝ) := by
  refine one_sub_le_expect_challengeBall_ct0 t0 γ (fun x => ?_) hτ
  refine (expect_challengeBall_indicator_centeredCoeffs_le_chord hB t0 ht0 hq x hu γ).trans ?_
  have h0 : 0 ≤ ∑ i, (centeredVec t0 x.1 i : ℝ) ^ 2 / (ringDegree * (B : ℝ) ^ 2) :=
    sum_nonneg fun i _ => by positivity
  have hC := sub_nonneg.2 (one_le_cosh u)
  have hb0 : 0 ≤ 1 + (cosh u - 1) *
      ∑ i, (centeredVec t0 x.1 i : ℝ) ^ 2 / (ringDegree * (B : ℝ) ^ 2) :=
    add_nonneg zero_le_one (mul_nonneg hC h0)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0
    (by linarith [mul_le_mul_of_nonneg_left (hs x.1) hC]) τ) (by positivity)

/-- **The ct₀-check for every `t₀`**: for `c` uniform on `B_τ` with `τ ≤ 256`, `0 < B`,
`‖t₀‖∞ ≤ B`, `2τB < q` and `θ < γ / B`, the check `‖c·t₀‖∞ < γ` passes with probability at
least `1 - 256 k · 𝔼 max(|S_τ| - θ, 0) / (γ/B - θ)`. -/
theorem one_sub_le_expect_challengeBall_ct0_hinge {τ B k : ℕ} (hτ : τ ≤ ringDegree) (hB : 0 < B)
    (t0 : RqVec k) (ht0 : polyVecNorm t0 ≤ B) (hq : 2 * (τ * B) < modulus) {γ : ℕ} {θ : ℝ}
    (hθ : θ < γ / B) :
    1 - (ringDegree * k : ℕ) *
        ((∑ j ∈ range (τ + 1), (τ.choose j : ℝ) * max (|(j : ℝ) - ((τ - j : ℕ) : ℝ)| - θ) 0) /
          2 ^ τ / (γ / B - θ)) ≤
      𝔼 c : ChallengeBall τ, (if ∀ x, |centeredCoeffs (c.1 • t0) x| < γ then 1 else 0 : ℝ) :=
  one_sub_le_expect_challengeBall_ct0 t0 γ
    (fun x => expect_challengeBall_indicator_centeredCoeffs_le_hinge hτ hB t0 ht0 hq x hθ) hτ

end Ball

end GordieHowe.MLDSA
