-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.StandinError
public import GordieHowe.Foundations.ToMathlib.LogOneSub
public import GordieHowe.Foundations.ToMathlib.UniformFunctionHoeffding

@[expose] public section

/-!
# The acceptance weight from below, with `SampleInBall` a random oracle

The member weight of a published `t₀` in bucket vector `v` is at least the acceptance weight
`acceptWeight(c·t₀, v)`, the Poisson-binomial CDF at `ω` of the hint fractions
`p_i = hintProb(v_i, b_i)`, `b = c·t₀` (when the ct₀ check passes). This file bounds its average
over the challenge from below by the **acceptance floor**

    acceptFloor ω κ m m₂ = max(1 - m / (ω + 1), exp(-m - κ m₂))

with `m ≥ 𝔼_c ∑_i p_i` and `m₂ ≥ 𝔼_c ∑_i p_i²`, and averages its inverse square over the
oracle `G = SampleInBall`.

* **Markov** (`one_sub_sum_div_le_poissonBinomialCdf`): for `X` Poisson-binomial with
  parameters `p`, `Pr[X ≤ ω] ≥ 1 - 𝔼X / (ω + 1)`, `𝔼X = ∑_i p_i`
  (`sum_card_mul_poissonBinomialWeight`).
* **Floor**: `Pr[X ≤ ω] ≥ ∏_i (1 - p_i) ≥ exp(-∑ p_i - κ ∑ p_i²)` for `p_i ≤ x₀` and
  `exp(-x - κx²) ≤ 1 - x` on `[0, x₀]` (`Real.exp_neg_sub_mul_sq_le_one_sub`); Jensen for `exp`.
* **Any finite average** (`acceptFloor_le_expect_acceptWeight`): the two bounds averaged over
  a uniform `c` of any finite type. The bucket-uniform form
  (`acceptFloor_le_expect_acceptWeight_of_hintFractionBound`) uses the hint fraction bound
  `hintFractionBound(b) = max(|b| - β, 0) / L ≥ hintProb(r, b)` for every bucket `r`
  (`hintProb_le`), `L = 2(γ₂ - β) - 1`, so `m` and `m₂` do not depend on `v`.
* **A line with the ct₀ indicator** (`line_le_expect_acceptWeight`): for a line
  `α - σ N x₀ ≤ Pr[Bin(N, x₀) ≤ ω]` at every `N ≤ |ι|`, `σ ≥ 0` and hint fraction bounds at most
  `x₀`, `α 𝔼_c 1[‖b_c‖∞ < γ₂] - σ 𝔼_c ∑_i hintFractionBound(b_{c,i}) ≤ 𝔼_c acceptWeight(b_c, v)`
  (the vertex reduction `sub_sum_le_poissonBinomialCdf`). The ct₀ check need not pass.
* **A uniform challenge** (`expect_hintBoundSum_le_sqrt`, `expect_hintBoundSqSum_le`): for `c`
  uniform on `B_τ`, `𝔼_c ∑ hintFractionBound ≤ (16 √τ / L) ∑_j ‖t₀,j‖₂` (from
  `𝔼|b| ≤ √(𝔼 b²)` and `expect_challengeBall_centeredCoeffs_sq`) and
  `𝔼_c ∑ hintFractionBound² ≤ τ ‖t₀‖₂² / L²`. `expect_hintBoundSum_le_expect_abs` turns any bound
  on `𝔼_c ∑_i |b_i|` into a bound on `𝔼_c ∑ hintFractionBound`.
* **The oracle average** (`expect_inv_sq_oracleAcceptFloor_le`): for `G` uniform among the
  functions from commitment hashes to `B_τ`, `oracleAcceptFloor p κ G t₀` is the acceptance floor
  at the `c̃`-averages of `∑ hintFractionBound` and `∑ hintFractionBound²` under `G`. By Hoeffding's
  inequality over the `256^(λ/4)` independent values of `G`
  (`GordieHowe.expect_indicator_le_expect_le`), for all bounds `Mb`, `Qb` on the uniform-`c`
  means and deviations `t, t₂ ≥ 0`:
  `𝔼_G w_G⁻² ≤ acceptFloor(Mb + t, Qb + t₂)⁻² + (e^{-2N t²/H²} + e^{-2N t₂²/H₂²}) e^{2(H + κ H₂)}`
  with `N = 256^(λ/4)`, `H = 256 k x₀` and `H₂ = 256 k x₀²` the largest values of the two sums,
  and `e^{-H - κ H₂}` the floor on the bad event.
* **The member weight** (`oracleAcceptFloor_le_expect_memberWeight`): for `β_min ≤ 1` and every
  `v`, `w_G(t₀) ≤ 𝔼_c̃ memberWeight(t₀, (v, c̃))`.
* **ML-DSA-65 and ML-DSA-87** (`floorParams_mldsa65`, `floorParams_mldsa87`,
  `expect_inv_sq_oracleAcceptFloor_le_mldsa65`, `_mldsa87`): `x₀ = 48/125`, `κ = 341/500`
  (resp. `x₀ = 47/100`, `κ = 747/1000`) and `t = t₂ = 2^-64` give
  `𝔼_G w_G⁻² ≤ acceptFloor(Mb + 2^-64, Qb + 2^-64)⁻² + 2^-1000`.
-/

open Finset Real
open scoped BigOperators ENNReal

namespace GordieHowe.MLDSA.Regularity

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA
open LatticeCrypto TransformOps

/-! ### The Poisson-binomial law: total mass, mean, Markov -/

section PoissonBinomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Expanding a product of sums over subsets**:
`∑_S ∏_i (if i ∈ S then a i else b i) = ∏_i (a i + b i)`. -/
theorem sum_prod_ite_mem (a b : ι → ℝ) :
    ∑ S : Finset ι, ∏ i, (if i ∈ S then a i else b i) = ∏ i, (a i + b i) := by
  rw [Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Finset.prod_ite]
  congr 1
  · exact Finset.prod_congr (by ext; simp) fun _ _ => rfl
  · exact Finset.prod_congr (by ext; simp) fun _ _ => rfl

/-- **The Poisson-binomial weight of a set of successes** `S`:
`∏_{i ∈ S} p_i · ∏_{i ∉ S} (1 - p_i)`, the summand of `poissonBinomialCdf`. -/
noncomputable def poissonBinomialWeight (p : ι → ℝ) (S : Finset ι) : ℝ :=
  ∏ i, if i ∈ S then p i else 1 - p i

/-- The Poisson-binomial CDF is the total weight of the sets of at most `ω` successes. -/
theorem poissonBinomialCdf_eq_sum_weight (p : ι → ℝ) (ω : ℕ) :
    poissonBinomialCdf p ω =
      ∑ S ∈ univ.filter (fun S : Finset ι => S.card ≤ ω), poissonBinomialWeight p S :=
  rfl

/-- The Poisson-binomial weights are nonnegative for `p_i ∈ [0, 1]`. -/
theorem poissonBinomialWeight_nonneg {p : ι → ℝ} (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1)
    (S : Finset ι) : 0 ≤ poissonBinomialWeight p S :=
  prod_nonneg fun i _ => by
    split_ifs
    · exact h0 i
    · linarith [h1 i]

/-- **The Poisson-binomial weights have total mass `1`.** -/
theorem sum_poissonBinomialWeight (p : ι → ℝ) : ∑ S, poissonBinomialWeight p S = 1 := by
  simp only [poissonBinomialWeight]
  rw [sum_prod_ite_mem]
  simp

/-- **Trial `j` succeeds with probability `p j`**: `∑_{S ∋ j} w(S) = p j`. -/
theorem sum_mem_mul_poissonBinomialWeight (p : ι → ℝ) (j : ι) :
    ∑ S, (if j ∈ S then (1 : ℝ) else 0) * poissonBinomialWeight p S = p j := by
  have h : ∀ S : Finset ι, (if j ∈ S then (1 : ℝ) else 0) * poissonBinomialWeight p S =
      ∏ i, (if i ∈ S then p i else if i = j then 0 else 1 - p i) := fun S => by
    by_cases hj : j ∈ S
    · simp only [hj, ↓reduceIte, one_mul, poissonBinomialWeight]
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : i ∈ S
      · simp [hi]
      · have : i ≠ j := fun h => hi (h ▸ hj)
        simp [hi, this]
    · simp only [hj, ↓reduceIte, zero_mul]
      refine (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])).symm
  simp_rw [h]
  rw [sum_prod_ite_mem]
  have h2 : ∀ i, p i + (if i = j then 0 else 1 - p i) = if i = j then p i else 1 := fun i => by
    split_ifs <;> ring
  simp_rw [h2]
  simp

/-- **The mean of the Poisson-binomial law**: `∑_S |S| w(S) = ∑_i p_i`. -/
theorem sum_card_mul_poissonBinomialWeight (p : ι → ℝ) :
    ∑ S, (S.card : ℝ) * poissonBinomialWeight p S = ∑ i, p i := by
  have h : ∀ S : Finset ι, (S.card : ℝ) * poissonBinomialWeight p S =
      ∑ j, (if j ∈ S then (1 : ℝ) else 0) * poissonBinomialWeight p S := fun S => by
    rw [← Finset.sum_mul, Finset.sum_boole,
      show (univ.filter fun j => j ∈ S) = S by ext; simp]
  simp_rw [h]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => sum_mem_mul_poissonBinomialWeight p j

/-- **Markov's inequality for the Poisson-binomial law**: for `p_i ∈ [0, 1]`,
`Pr[X₁ + ⋯ + X_n ≤ ω] ≥ 1 - (∑_i p_i) / (ω + 1)`. -/
theorem one_sub_sum_div_le_poissonBinomialCdf (p : ι → ℝ) (h0 : ∀ i, 0 ≤ p i)
    (h1 : ∀ i, p i ≤ 1) (ω : ℕ) :
    1 - (∑ i, p i) / (ω + 1) ≤ poissonBinomialCdf p ω := by
  have hω : (0 : ℝ) < ω + 1 := by positivity
  have hw0 := poissonBinomialWeight_nonneg h0 h1
  rw [poissonBinomialCdf_eq_sum_weight, Finset.sum_filter]
  have key : (∑ S, poissonBinomialWeight p S -
      ∑ S, (if S.card ≤ ω then poissonBinomialWeight p S else 0)) * (ω + 1) ≤ ∑ i, p i := by
    rw [← Finset.sum_sub_distrib, Finset.sum_mul, ← sum_card_mul_poissonBinomialWeight p]
    refine Finset.sum_le_sum fun S _ => ?_
    split_ifs with h
    · simp only [sub_self, zero_mul]
      exact mul_nonneg (Nat.cast_nonneg _) (hw0 S)
    · have hc : (ω : ℝ) + 1 ≤ S.card := by exact_mod_cast (by omega : ω + 1 ≤ S.card)
      nlinarith [hw0 S]
  rw [sum_poissonBinomialWeight] at key
  have := (le_div_iff₀ hω).2 key
  linarith

end PoissonBinomial

/-! ### The acceptance floor -/

section Floor

/-- **The acceptance floor** `max(1 - y / (ω + 1), exp(-y - κ y₂))`: the Markov bound and the
exponential floor of the Poisson-binomial CDF at `ω`, at a hint mean `y` and hint second moment
`y₂`. -/
noncomputable def acceptFloor (ω : ℕ) (κ y y₂ : ℝ) : ℝ :=
  max (1 - y / (ω + 1)) (exp (-y - κ * y₂))

/-- The acceptance floor is positive. -/
theorem acceptFloor_pos (ω : ℕ) (κ y y₂ : ℝ) : 0 < acceptFloor ω κ y y₂ :=
  lt_max_of_lt_right (exp_pos _)

/-- The acceptance floor is at least its exponential term. -/
theorem exp_le_acceptFloor (ω : ℕ) (κ y y₂ : ℝ) : exp (-y - κ * y₂) ≤ acceptFloor ω κ y y₂ :=
  le_max_right _ _

/-- The acceptance floor is antitone in the hint moments for `κ ≥ 0`. -/
theorem acceptFloor_anti (ω : ℕ) {κ y y' y₂ y₂' : ℝ} (hκ : 0 ≤ κ) (hy : y ≤ y')
    (hy₂ : y₂ ≤ y₂') : acceptFloor ω κ y' y₂' ≤ acceptFloor ω κ y y₂ := by
  refine max_le_max (by gcongr) (exp_le_exp.2 ?_)
  nlinarith

/-- **The mean acceptance weight from below** over any finite uniform average. For shifts
`b : C → ι → ℤ` passing the ct₀ check (`|b_{c,i}| < γ₂`), hint fractions
`p_{c,i} = hintProb(v_i, b_{c,i}) ≤ x₀ ≤ 1`, `κ ≥ 0` with `exp(-x - κx²) ≤ 1 - x` on `[0, x₀]`,
`m ≥ 𝔼_c ∑_i p_{c,i}` and `m₂ ≥ 𝔼_c ∑_i p_{c,i}²`:
`max(1 - m / (ω + 1), exp(-m - κ m₂)) ≤ 𝔼_c acceptWeight(b_c, v)`. -/
theorem acceptFloor_le_expect_acceptWeight {ι C : Type*} [Fintype ι] [DecidableEq ι] [Fintype C]
    [Nonempty C] {γ₂ β ω : ℕ} (b : C → ι → ℤ) (v : ι → ℕ) {x₀ κ m m₂ : ℝ}
    (hct0 : ∀ c i, |b c i| < γ₂) (hx : ∀ c i, hintProb γ₂ β (v i) (b c i) ≤ x₀) (hx₀ : x₀ ≤ 1)
    (hκ0 : 0 ≤ κ) (hκ : ∀ x, 0 ≤ x → x ≤ x₀ → exp (-x - κ * x ^ 2) ≤ 1 - x)
    (hm : 𝔼 c, ∑ i, hintProb γ₂ β (v i) (b c i) ≤ m)
    (hm₂ : 𝔼 c, ∑ i, hintProb γ₂ β (v i) (b c i) ^ 2 ≤ m₂) :
    acceptFloor ω κ m m₂ ≤ 𝔼 c, acceptWeight γ₂ β ω (b c) v := by
  set q : C → ι → ℝ := fun c i => hintProb γ₂ β (v i) (b c i) with hqdef
  have hq0 : ∀ c i, 0 ≤ q c i := fun c i => hintProb_nonneg _ _ _ _
  have hq1 : ∀ c i, q c i ≤ 1 := fun c i => (hx c i).trans hx₀
  have haw : ∀ c, acceptWeight γ₂ β ω (b c) v = poissonBinomialCdf (q c) ω := fun c => by
    rw [acceptWeight, ite_eq_left (hct0 c), one_mul]
  have hω : (0 : ℝ) < ω + 1 := by positivity
  refine max_le ?_ ?_
  · calc 1 - m / (ω + 1) ≤ 𝔼 c, (1 - (∑ i, q c i) / (ω + 1)) := by
          rw [Finset.expect_sub_distrib, Finset.expect_const Finset.univ_nonempty,
            ← Finset.expect_div]
          gcongr
      _ ≤ _ := Finset.expect_le_expect fun c _ => by
          rw [haw]
          exact one_sub_sum_div_le_poissonBinomialCdf _ (hq0 c) (hq1 c) ω
  · have hpt : ∀ c, exp (-(∑ i, q c i) - κ * ∑ i, q c i ^ 2) ≤
        acceptWeight γ₂ β ω (b c) v := fun c => by
      rw [haw]
      calc exp (-(∑ i, q c i) - κ * ∑ i, q c i ^ 2)
          = ∏ i, exp (-q c i - κ * q c i ^ 2) := by
            rw [← exp_sum]
            congr 1
            rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum]
        _ ≤ ∏ i, (1 - q c i) :=
            Finset.prod_le_prod₀ (fun i _ => (exp_pos _).le) fun i _ => hκ _ (hq0 c i) (hx c i)
        _ ≤ _ := prod_one_sub_le_poissonBinomialCdf _ (hq0 c) (hq1 c) ω
    calc exp (-m - κ * m₂) ≤ exp (𝔼 c, (-(∑ i, q c i) - κ * ∑ i, q c i ^ 2)) := by
          apply exp_le_exp.2
          rw [Finset.expect_sub_distrib, Finset.expect_neg_distrib, ← Finset.mul_expect]
          have := mul_le_mul_of_nonneg_left hm₂ hκ0
          linarith
      _ ≤ 𝔼 c, exp (-(∑ i, q c i) - κ * ∑ i, q c i ^ 2) := exp_expect_le_expect_exp _
      _ ≤ _ := Finset.expect_le_expect fun c _ => hpt c

/-- **The mean acceptance weight from below, uniformly in the bucket vector.** As
`acceptFloor_le_expect_acceptWeight`, with `m`, `m₂` and `x₀` bounding the moments and the values
of `hintFractionBound`, which do not depend on `v`. -/
theorem acceptFloor_le_expect_acceptWeight_of_hintFractionBound {ι C : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype C] [Nonempty C] {γ₂ β ω : ℕ} (b : C → ι → ℤ) {x₀ κ m m₂ : ℝ}
    (hct0 : ∀ c i, |b c i| < γ₂) (hx : ∀ c i, hintFractionBound γ₂ β (b c i) ≤ x₀)
    (hx₀ : x₀ ≤ 1) (hκ0 : 0 ≤ κ) (hκ : ∀ x, 0 ≤ x → x ≤ x₀ → exp (-x - κ * x ^ 2) ≤ 1 - x)
    (hm : 𝔼 c, ∑ i, hintFractionBound γ₂ β (b c i) ≤ m)
    (hm₂ : 𝔼 c, ∑ i, hintFractionBound γ₂ β (b c i) ^ 2 ≤ m₂) (v : ι → ℕ) :
    acceptFloor ω κ m m₂ ≤ 𝔼 c, acceptWeight γ₂ β ω (b c) v := by
  have hle : ∀ c i, hintProb γ₂ β (v i) (b c i) ≤ hintFractionBound γ₂ β (b c i) := fun c i =>
    hintProb_le_hintFractionBound _ _ _ _
  refine acceptFloor_le_expect_acceptWeight b v hct0 (fun c i => (hle c i).trans (hx c i)) hx₀
    hκ0 hκ ((Finset.expect_le_expect fun c _ => Finset.sum_le_sum fun i _ => hle c i).trans hm)
    ((Finset.expect_le_expect fun c _ => Finset.sum_le_sum fun i _ => ?_).trans hm₂)
  exact pow_le_pow_left₀ (hintProb_nonneg _ _ _ _) (hle c i) 2

/-- **The bucket-free acceptance weight from a line below the binomial CDF.** For hint fraction
bounds `hintFractionBound(b_i) ≤ x₀`, `σ ≥ 0` and a line `α - σ N x₀ ≤ Pr[Bin(N, x₀) ≤ ω]` at
every `N ≤ |ι|`: `α · 1[‖b‖∞ < γ₂] - σ ∑_i hintFractionBound(b_i) ≤ acceptWeightLower(b)`
(`sub_sum_le_poissonBinomialCdf`). -/
theorem line_le_acceptWeightLower {ι : Type*} [Fintype ι] [DecidableEq ι] {γ₂ β ω : ℕ}
    (b : ι → ℤ) {x₀ α σ : ℝ} (hx : ∀ i, hintFractionBound γ₂ β (b i) ≤ x₀) (hσ : 0 ≤ σ)
    (hline : ∀ N ≤ Fintype.card ι, α - σ * N * x₀ ≤ binomialCdf x₀ N ω) :
    α * (if ∀ i, |b i| < γ₂ then 1 else 0) - σ * ∑ i, hintFractionBound γ₂ β (b i) ≤
      acceptWeightLower γ₂ β ω b := by
  have hs : 0 ≤ σ * ∑ i, hintFractionBound γ₂ β (b i) :=
    mul_nonneg hσ (sum_nonneg fun i _ => hintFractionBound_nonneg _ _ _)
  unfold acceptWeightLower
  split_ifs
  · rw [mul_one, one_mul]
    exact sub_sum_le_poissonBinomialCdf (fun i => hintFractionBound_nonneg _ _ _) hx hline
  · linarith

/-- **The mean acceptance weight from a line below the binomial CDF**, over any finite uniform
average and uniformly in the bucket vector. For shifts `b : C → ι → ℤ` with hint fraction bounds
`hintFractionBound(b_{c,i}) ≤ x₀`, `σ ≥ 0` and a line `α - σ N x₀ ≤ Pr[Bin(N, x₀) ≤ ω]` at every
`N ≤ |ι|`:
`α 𝔼_c 1[‖b_c‖∞ < γ₂] - σ 𝔼_c ∑_i hintFractionBound(b_{c,i}) ≤ 𝔼_c acceptWeight(b_c, v)`
(`line_le_acceptWeightLower`, `acceptWeightLower_le_acceptWeight`). -/
theorem line_le_expect_acceptWeight {ι C : Type*} [Fintype ι] [DecidableEq ι] [Fintype C]
    {γ₂ β ω : ℕ} (hβ : β < γ₂) (b : C → ι → ℤ) {x₀ α σ : ℝ}
    (hx : ∀ c i, hintFractionBound γ₂ β (b c i) ≤ x₀) (hσ : 0 ≤ σ)
    (hline : ∀ N ≤ Fintype.card ι, α - σ * N * x₀ ≤ binomialCdf x₀ N ω) (v : ι → ℕ) :
    α * 𝔼 c, (if ∀ i, |b c i| < γ₂ then 1 else 0 : ℝ) -
        σ * 𝔼 c, ∑ i, hintFractionBound γ₂ β (b c i) ≤
      𝔼 c, acceptWeight γ₂ β ω (b c) v := by
  rw [mul_expect, mul_expect, ← expect_sub_distrib]
  exact expect_le_expect fun c _ => (line_le_acceptWeightLower (b c) (hx c) hσ hline).trans
    (acceptWeightLower_le_acceptWeight hβ ω (b c) v)

end Floor

/-! ### The hint moments of `c·t₀` -/

section Moments

variable [nttOps : NTTRingOps]

/-- **The hint mean bound of `c·t₀`**: `∑_{j,i} hintFractionBound((c·t₀)_{j,i})`. -/
noncomputable def hintBoundSum (γ₂ β : ℕ) {k : ℕ} (c : Rq) (t0 : RqVec k) : ℝ :=
  ∑ x : Fin k × Fin ringDegree, hintFractionBound γ₂ β (centeredCoeffs (c • t0) x)

/-- **The hint second-moment bound of `c·t₀`**: `∑_{j,i} hintFractionBound((c·t₀)_{j,i})²`. -/
noncomputable def hintBoundSqSum (γ₂ β : ℕ) {k : ℕ} (c : Rq) (t0 : RqVec k) : ℝ :=
  ∑ x : Fin k × Fin ringDegree, hintFractionBound γ₂ β (centeredCoeffs (c • t0) x) ^ 2

/-- **A hint mean bound from a bound on the mean `ℓ¹` norm of the shift**: for any finite average
of polynomials `F c`, `𝔼_c hintBoundSum(F c) ≤ 𝔼_c ∑_x |(F c · t₀)_x| / (2(γ₂ - β) - 1)`. -/
theorem expect_hintBoundSum_le_expect_abs {C : Type*} [Fintype C] (γ₂ β : ℕ) {k : ℕ}
    (F : C → Rq) (t0 : RqVec k) :
    𝔼 c, hintBoundSum γ₂ β (F c) t0 ≤
      (𝔼 c, ∑ x, |((centeredCoeffs (F c • t0) x : ℤ) : ℝ)|) / ((2 * (γ₂ - β) - 1 : ℕ) : ℝ) := by
  rw [Finset.expect_div]
  refine Finset.expect_le_expect fun c _ => ?_
  rw [Finset.sum_div]
  exact Finset.sum_le_sum fun x _ => by
    have := hintFractionBound_le_abs γ₂ β (centeredCoeffs (F c • t0) x)
    simpa using this

variable [NTTRingLaws nttOps]

/-- **The shift of a challenge**: `|(c·t₀)_x| ≤ τ 2^12` for `c ∈ B_τ` and `‖t₀‖∞ ≤ 2^12`. -/
theorem abs_centeredCoeffs_smul_le {τ k : ℕ} (c : ChallengeBall τ) (t0 : RqVec k)
    (ht0 : polyVecNorm t0 ≤ 4096) (x : Fin k × Fin ringDegree) :
    |((centeredCoeffs (c.1 • t0) x : ℤ) : ℝ)| ≤ ((τ * 4096 : ℕ) : ℝ) := by
  have hn := norm_challenge_coeffScalarVecMul_le nttOps c.1 t0 c.2.1 c.2.2.le ht0
  have h := GordieHowe.MLDSA44.natAbs_centeredRepr_le_polyVecNorm (c.1 • t0) x.1 x.2
  have h' : (centeredCoeffs (c.1 • t0) x).natAbs ≤ τ * 4096 := h.trans hn
  rw [← Int.cast_abs, Int.abs_eq_natAbs]
  exact_mod_cast h'

/-- **The hint mean over a uniform challenge, by `𝔼|b| ≤ √(𝔼 b²)`**: for `c` uniform on `B_τ`
(`τ ≤ 256`), `‖t₀‖∞ ≤ 2^12` and `2τ 2^12 < q`,
`𝔼_c hintBoundSum(c, t₀) ≤ (16 √τ / L) ∑_j ‖t₀,j‖₂`, `L = 2(γ₂ - β) - 1`. -/
theorem expect_hintBoundSum_le_sqrt {γ₂ β τ k : ℕ} (hτ : τ ≤ ringDegree) (t0 : RqVec k)
    (ht0 : polyVecNorm t0 ≤ 4096) (hq : 2 * (τ * 4096) < modulus) :
    𝔼 c : ChallengeBall τ, hintBoundSum γ₂ β c.1 t0 ≤
      16 * √(τ : ℝ) / ((2 * (γ₂ - β) - 1 : ℕ) : ℝ) *
        ∑ j, √(∑ m, (centeredVec t0 j m : ℝ) ^ 2) := by
  have := challengeBall_nonempty hτ
  set L : ℝ := ((2 * (γ₂ - β) - 1 : ℕ) : ℝ)
  have hL : 0 ≤ L := Nat.cast_nonneg _
  refine (expect_hintBoundSum_le_expect_abs γ₂ β (fun c : ChallengeBall τ => c.1) t0).trans ?_
  rw [Finset.expect_sum_comm]
  have hx : ∀ x : Fin k × Fin ringDegree,
      𝔼 c : ChallengeBall τ, |((centeredCoeffs (c.1 • t0) x : ℤ) : ℝ)| ≤
        √(τ : ℝ) * √(∑ m, (centeredVec t0 x.1 m : ℝ) ^ 2) / 16 := fun x => by
    have h2 := expect_challengeBall_centeredCoeffs_sq hτ t0 ht0 hq x
    have h1 := Finset.sq_expect_le_expect_sq univ_nonempty (fun c : ChallengeBall τ =>
      |((centeredCoeffs (c.1 • t0) x : ℤ) : ℝ)|)
    simp only [sq_abs] at h1
    rw [h2] at h1
    have hs : 0 ≤ ∑ m, (centeredVec t0 x.1 m : ℝ) ^ 2 := by positivity
    have hr : (√(τ : ℝ) * √(∑ m, (centeredVec t0 x.1 m : ℝ) ^ 2) / 16) ^ 2 =
        τ / ringDegree * ∑ m, (centeredVec t0 x.1 m : ℝ) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt hs]
      norm_num [ringDegree]
      ring
    rw [← hr] at h1
    exact (pow_le_pow_iff_left₀ (Finset.expect_nonneg fun _ _ => abs_nonneg _)
      (by positivity) two_ne_zero).1 h1
  calc (∑ x : Fin k × Fin ringDegree, 𝔼 c : ChallengeBall τ,
        |((centeredCoeffs (c.1 • t0) x : ℤ) : ℝ)|) / L
      ≤ (∑ x : Fin k × Fin ringDegree,
          √(τ : ℝ) * √(∑ m, (centeredVec t0 x.1 m : ℝ) ^ 2) / 16) / L := by
        gcongr with x
        exact hx x
    _ = _ := by
        rw [Fintype.sum_prod_type]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => ?_
        norm_num [ringDegree]
        ring

/-- **The hint second moment over a uniform challenge**: for `c` uniform on `B_τ`,
`𝔼_c hintBoundSqSum(c, t₀) ≤ τ ‖t₀‖₂² / L²`, `L = 2(γ₂ - β) - 1`. -/
theorem expect_hintBoundSqSum_le {γ₂ β τ k : ℕ} (hτ : τ ≤ ringDegree) (t0 : RqVec k)
    (ht0 : polyVecNorm t0 ≤ 4096) (hq : 2 * (τ * 4096) < modulus) :
    𝔼 c : ChallengeBall τ, hintBoundSqSum γ₂ β c.1 t0 ≤
      τ * t0SqNorm t0 / ((2 * (γ₂ - β) - 1 : ℕ) : ℝ) ^ 2 := by
  have := challengeBall_nonempty hτ
  set L : ℝ := ((2 * (γ₂ - β) - 1 : ℕ) : ℝ)
  have hM := expect_challengeBall_sum_centeredCoeffs_sq hτ t0 ht0 hq
  rw [← hM, Finset.expect_div]
  refine Finset.expect_le_expect fun c _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun x _ => ?_
  have h := hintFractionBound_le_abs γ₂ β (centeredCoeffs (c.1 • t0) x)
  have h' := pow_le_pow_left₀ (hintFractionBound_nonneg _ _ _) h 2
  rw [div_pow] at h'
  refine h'.trans_eq ?_
  simp only [L, sq_abs]

end Moments

/-! ### The parameter conditions -/

/-- **The parameter conditions of the acceptance floor at `p`**: `τ ≤ 256`, the ct₀ check always
passes (`τ 2^12 < γ₂`), `2γ₂ < q`, `β < γ₂`, `k > 0`, the hint fraction bound of a shift
`|b| ≤ τ 2^12` is at most `x₀ ∈ (0, 1)`, and `κ ≥ 0` with `exp(-x - κx²) ≤ 1 - x` on `[0, x₀]`. -/
structure FloorParams (p : Params) (x₀ κ : ℝ) : Prop where
  tau_le : p.tau ≤ ringDegree
  ct0 : p.tau * 4096 < p.gamma2
  gamma2_lt : 2 * p.gamma2 < modulus
  beta_lt : p.beta < p.gamma2
  k_pos : 0 < p.k
  x0_ge : ((p.tau * 4096 : ℕ) : ℝ) / ((2 * (p.gamma2 - p.beta) - 1 : ℕ) : ℝ) ≤ x₀
  x0_pos : 0 < x₀
  x0_lt : x₀ < 1
  kappa_nonneg : 0 ≤ κ
  kappa : ∀ x, 0 ≤ x → x ≤ x₀ → exp (-x - κ * x ^ 2) ≤ 1 - x

/-! ### The acceptance floor with `SampleInBall` a random oracle -/

section Oracle

variable {p : Params} [nttOps : NTTRingOps]

/-- **The acceptance floor of `t₀` under the oracle `G`**: `acceptFloor` at the averages over the
commitment hash `c̃` of `hintBoundSum` and `hintBoundSqSum` at the challenge `G(c̃)`. A lower bound
on the mean member weight of `t₀` in every bucket vector
(`oracleAcceptFloor_le_expect_memberWeight`). -/
noncomputable def oracleAcceptFloor (p : Params) (κ : ℝ)
    (G : CommitHashBytes p → ChallengeBall p.tau) (t0 : RqVec p.k) : ℝ :=
  acceptFloor p.omega κ (𝔼 cTilde, hintBoundSum p.gamma2 p.beta (G cTilde).1 t0)
    (𝔼 cTilde, hintBoundSqSum p.gamma2 p.beta (G cTilde).1 t0)

variable [NTTRingLaws nttOps] {x₀ κ : ℝ}

/-- The ct₀ check passes at every challenge: `|(c·t₀)_x| < γ₂`. -/
theorem FloorParams.abs_lt (hf : FloorParams p x₀ κ) (c : ChallengeBall p.tau)
    (t0 : RqVec p.k) (ht0 : polyVecNorm t0 ≤ 4096) (x : Fin p.k × Fin ringDegree) :
    |centeredCoeffs (c.1 • t0) x| < p.gamma2 := by
  have h := (abs_centeredCoeffs_smul_le c t0 ht0 x).trans_lt
    (show ((p.tau * 4096 : ℕ) : ℝ) < p.gamma2 by exact_mod_cast hf.ct0)
  exact_mod_cast h

/-- The hint fraction bound at every challenge is at most `x₀`. -/
theorem FloorParams.hintFractionBound_le (hf : FloorParams p x₀ κ) (c : ChallengeBall p.tau)
    (t0 : RqVec p.k) (ht0 : polyVecNorm t0 ≤ 4096) (x : Fin p.k × Fin ringDegree) :
    hintFractionBound p.gamma2 p.beta (centeredCoeffs (c.1 • t0) x) ≤ x₀ := by
  refine (hintFractionBound_le_abs _ _ _).trans (le_trans ?_ hf.x0_ge)
  gcongr
  simpa using abs_centeredCoeffs_smul_le c t0 ht0 x

/-- `hintBoundSum ≤ 256 k x₀` at every challenge. -/
theorem FloorParams.hintBoundSum_mem (hf : FloorParams p x₀ κ) (c : ChallengeBall p.tau)
    (t0 : RqVec p.k) (ht0 : polyVecNorm t0 ≤ 4096) :
    hintBoundSum p.gamma2 p.beta c.1 t0 ∈
      Set.Icc 0 (((p.k * ringDegree : ℕ) : ℝ) * x₀) := by
  refine ⟨Finset.sum_nonneg fun x _ => hintFractionBound_nonneg _ _ _, ?_⟩
  refine (Finset.sum_le_sum fun x _ => hf.hintFractionBound_le c t0 ht0 x).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul]

/-- `hintBoundSqSum ≤ 256 k x₀²` at every challenge. -/
theorem FloorParams.hintBoundSqSum_mem (hf : FloorParams p x₀ κ) (c : ChallengeBall p.tau)
    (t0 : RqVec p.k) (ht0 : polyVecNorm t0 ≤ 4096) :
    hintBoundSqSum p.gamma2 p.beta c.1 t0 ∈
      Set.Icc 0 (((p.k * ringDegree : ℕ) : ℝ) * x₀ ^ 2) := by
  refine ⟨Finset.sum_nonneg fun x _ => sq_nonneg _, ?_⟩
  refine (Finset.sum_le_sum fun x _ => pow_le_pow_left₀ (hintFractionBound_nonneg _ _ _)
    (hf.hintFractionBound_le c t0 ht0 x) 2).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul]

/-- **The mean acceptance weight over a uniform challenge from below**: for `c` uniform on `B_τ`,
`m ≥ 𝔼_c hintBoundSum(c, t₀)`, `m₂ ≥ 𝔼_c hintBoundSqSum(c, t₀)` and every bucket vector `v`:
`acceptFloor(m, m₂) ≤ 𝔼_c acceptWeight(c·t₀, v)`. -/
theorem acceptFloor_le_expect_challengeBall_acceptWeight (hf : FloorParams p x₀ κ)
    (t0 : RqVec p.k) (ht0 : polyVecNorm t0 ≤ 4096) {m m₂ : ℝ}
    (hm : 𝔼 c : ChallengeBall p.tau, hintBoundSum p.gamma2 p.beta c.1 t0 ≤ m)
    (hm₂ : 𝔼 c : ChallengeBall p.tau, hintBoundSqSum p.gamma2 p.beta c.1 t0 ≤ m₂)
    (v : Fin p.k × Fin ringDegree → ℕ) :
    acceptFloor p.omega κ m m₂ ≤
      𝔼 c : ChallengeBall p.tau, acceptWeight p.gamma2 p.beta p.omega
        (centeredCoeffs (c.1 • t0)) v := by
  have := challengeBall_nonempty hf.tau_le
  exact acceptFloor_le_expect_acceptWeight_of_hintFractionBound
    (fun c : ChallengeBall p.tau => centeredCoeffs (c.1 • t0)) (fun c x => hf.abs_lt c t0 ht0 x)
    (fun c x => hf.hintFractionBound_le c t0 ht0 x) hf.x0_lt.le hf.kappa_nonneg hf.kappa hm hm₂ v

/-- **The acceptance floor under the oracle bounds the member weight**: for `prims` with
`SampleInBall = G`, `β_min ≤ 1`, `‖t₀‖∞ ≤ 2^12` and every bucket vector `v`,
`oracleAcceptFloor p κ G t₀ ≤ 𝔼_c̃ memberWeight(t₀, (v, c̃))`. -/
theorem oracleAcceptFloor_le_expect_memberWeight [NeZero (bucketCount p)]
    (hf : FloorParams p x₀ κ) (prims : Primitives p)
    (G : CommitHashBytes p → ChallengeBall p.tau)
    (hG : ∀ cTilde, prims.sampleInBall cTilde = (G cTilde).1) {βmin : ℚ≥0} (hβ : (βmin : ℝ≥0∞) ≤ 1)
    (t0 : RqVec p.k) (ht0 : polyVecNorm t0 ≤ 4096) (v : BucketVec p) :
    oracleAcceptFloor p κ G t0 ≤
      𝔼 cTilde, (memberWeight prims βmin t0 (v, cTilde) : ℝ≥0∞).toReal := by
  have hfl := acceptFloor_le_expect_acceptWeight_of_hintFractionBound (ω := p.omega)
    (fun cTilde : CommitHashBytes p => centeredCoeffs ((G cTilde).1 • t0))
    (fun c x => hf.abs_lt (G c) t0 ht0 x) (fun c x => hf.hintFractionBound_le (G c) t0 ht0 x)
    hf.x0_lt.le hf.kappa_nonneg hf.kappa le_rfl le_rfl (fun x => (v x).val)
  refine hfl.trans (Finset.expect_le_expect fun cTilde _ => ?_)
  have haw1 := acceptWeight_le_one (ω := p.omega) hf.beta_lt
    (centeredCoeffs ((G cTilde).1 • t0)) fun x => (v x).val
  have haw0 := acceptWeight_nonneg hf.beta_lt p.omega
    (centeredCoeffs ((G cTilde).1 • t0)) fun x => (v x).val
  have ht : (t0Weight prims t0 (v, cTilde) : ℝ≥0∞).toReal = acceptWeight p.gamma2 p.beta p.omega
      (centeredCoeffs ((G cTilde).1 • t0)) fun x => (v x).val := by
    rw [coe_t0Weight, ENNReal.toReal_ofReal (by rw [hG]; exact haw0)]
    simp only [hG]
  rw [← ht]
  refine ENNReal.toReal_mono (ENNReal.nnratCast_ne_top _) ?_
  rw [coe_memberWeight]
  refine le_min ?_ ((div_one _).symm.le.trans (ENNReal.div_le_div_left hβ _))
  rw [coe_t0Weight]
  exact ENNReal.ofReal_le_one.2 (by rw [hG]; exact haw1)

/-- **The inverse square of the oracle acceptance floor, averaged over the oracle.** For `G`
uniform among the functions from commitment hashes to `B_τ`, `‖t₀‖∞ ≤ 2^12`, bounds
`Mb ≥ 𝔼_{c ∈ B_τ} hintBoundSum(c, t₀)`, `Qb ≥ 𝔼_{c ∈ B_τ} hintBoundSqSum(c, t₀)` and deviations
`t, t₂ ≥ 0`: `𝔼_G (oracleAcceptFloor p κ G t₀)⁻² ≤ acceptFloor(Mb + t, Qb + t₂)⁻² +
(e^{-2N t²/H²} + e^{-2N t₂²/H₂²}) e^{2(H + κ H₂)}`, with `N = 256^(λ/4)` commitment hashes,
`H = 256 k x₀` and `H₂ = 256 k x₀²` (Hoeffding's inequality over the values of `G`, and the floor
`e^{-H - κH₂}` on the bad event). -/
theorem expect_inv_sq_oracleAcceptFloor_le (hf : FloorParams p x₀ κ) (t0 : RqVec p.k)
    (ht0 : polyVecNorm t0 ≤ 4096) {Mb Qb t t₂ : ℝ}
    (hMb : 𝔼 c : ChallengeBall p.tau, hintBoundSum p.gamma2 p.beta c.1 t0 ≤ Mb)
    (hQb : 𝔼 c : ChallengeBall p.tau, hintBoundSqSum p.gamma2 p.beta c.1 t0 ≤ Qb)
    (ht : 0 ≤ t) (ht₂ : 0 ≤ t₂) :
    𝔼 G : CommitHashBytes p → ChallengeBall p.tau, (oracleAcceptFloor p κ G t0)⁻¹ ^ 2 ≤
      (acceptFloor p.omega κ (Mb + t) (Qb + t₂))⁻¹ ^ 2 +
        (exp (-(2 * ((256 ^ (p.lambda / 4) : ℕ) : ℝ) * t ^ 2 /
            (((p.k * ringDegree : ℕ) : ℝ) * x₀) ^ 2)) +
          exp (-(2 * ((256 ^ (p.lambda / 4) : ℕ) : ℝ) * t₂ ^ 2 /
            (((p.k * ringDegree : ℕ) : ℝ) * x₀ ^ 2) ^ 2))) *
          exp (2 * (((p.k * ringDegree : ℕ) : ℝ) * x₀ +
            κ * (((p.k * ringDegree : ℕ) : ℝ) * x₀ ^ 2))) := by
  have := challengeBall_nonempty hf.tau_le
  set n : ℝ := ((p.k * ringDegree : ℕ) : ℝ) with hn
  have hn0 : 0 < n := by
    rw [hn]
    have := hf.k_pos
    exact_mod_cast Nat.mul_pos this (by norm_num [ringDegree])
  have hx₀ := hf.x0_pos
  have hκ0 := hf.kappa_nonneg
  set H := n * x₀
  set H₂ := n * x₀ ^ 2
  have hH : 0 < H := by positivity
  have hH₂ : 0 < H₂ := by positivity
  set f : ChallengeBall p.tau → ℝ := fun c => hintBoundSum p.gamma2 p.beta c.1 t0
  set f₂ : ChallengeBall p.tau → ℝ := fun c => hintBoundSqSum p.gamma2 p.beta c.1 t0
  have hf1 : ∀ c, f c ∈ Set.Icc 0 H := fun c => hf.hintBoundSum_mem c t0 ht0
  have hf2 : ∀ c, f₂ c ∈ Set.Icc 0 H₂ := fun c => hf.hintBoundSqSum_mem c t0 ht0
  set A := (acceptFloor p.omega κ (Mb + t) (Qb + t₂))⁻¹ ^ 2
  set B := exp (2 * (H + κ * H₂))
  have hA : 0 ≤ A := by positivity
  have hB : 0 ≤ B := (exp_pos _).le
  set I1 : (CommitHashBytes p → ChallengeBall p.tau) → ℝ := fun G =>
    if 𝔼 c, f c + t ≤ 𝔼 cTilde, f (G cTilde) then 1 else 0
  set I2 : (CommitHashBytes p → ChallengeBall p.tau) → ℝ := fun G =>
    if 𝔼 c, f₂ c + t₂ ≤ 𝔼 cTilde, f₂ (G cTilde) then 1 else 0
  have hpt : ∀ G, (oracleAcceptFloor p κ G t0)⁻¹ ^ 2 ≤ A + (I1 G + I2 G) * B := fun G => by
    have hY : 𝔼 cTilde, f (G cTilde) ≤ H :=
      (Finset.expect_le_expect fun c _ => (hf1 (G c)).2).trans_eq
        (Finset.expect_const Finset.univ_nonempty _)
    have hY₂ : 𝔼 cTilde, f₂ (G cTilde) ≤ H₂ :=
      (Finset.expect_le_expect fun c _ => (hf2 (G c)).2).trans_eq
        (Finset.expect_const Finset.univ_nonempty _)
    have hpos := acceptFloor_pos p.omega κ (𝔼 cTilde, f (G cTilde)) (𝔼 cTilde, f₂ (G cTilde))
    have hfloor : (oracleAcceptFloor p κ G t0)⁻¹ ^ 2 ≤ B := by
      have h1 : exp (-H - κ * H₂) ≤ oracleAcceptFloor p κ G t0 :=
        (exp_le_exp.2 (by nlinarith)).trans (exp_le_acceptFloor _ _ _ _)
      calc (oracleAcceptFloor p κ G t0)⁻¹ ^ 2 ≤ (exp (-H - κ * H₂))⁻¹ ^ 2 := by
            gcongr
        _ = B := by
            rw [← Real.exp_neg, ← Real.exp_nat_mul]
            congr 1
            push_cast
            ring
    have hI1 : 0 ≤ I1 G := by simp only [I1]; split_ifs <;> norm_num
    have hI2 : 0 ≤ I2 G := by simp only [I2]; split_ifs <;> norm_num
    by_cases h1 : 𝔼 c, f c + t ≤ 𝔼 cTilde, f (G cTilde)
    · have : I1 G = 1 := by simp only [I1, h1, ↓reduceIte]
      rw [this]
      nlinarith
    by_cases h2 : 𝔼 c, f₂ c + t₂ ≤ 𝔼 cTilde, f₂ (G cTilde)
    · have : I2 G = 1 := by simp only [I2, h2, ↓reduceIte]
      rw [this]
      nlinarith
    have hgood : acceptFloor p.omega κ (Mb + t) (Qb + t₂) ≤ oracleAcceptFloor p κ G t0 :=
      acceptFloor_anti p.omega hκ0 (by linarith) (by linarith)
    have : (oracleAcceptFloor p κ G t0)⁻¹ ^ 2 ≤ A := by
      change _ ≤ (acceptFloor p.omega κ (Mb + t) (Qb + t₂))⁻¹ ^ 2
      gcongr
      exact acceptFloor_pos _ _ _ _
    nlinarith
  have hcard : (Fintype.card (CommitHashBytes p) : ℝ) = ((256 ^ (p.lambda / 4) : ℕ) : ℝ) := by
    rw [card_commitHashBytes]
  have he1 := GordieHowe.expect_indicator_le_expect_le (X := CommitHashBytes p) f hf1 hH ht
  have he2 := GordieHowe.expect_indicator_le_expect_le (X := CommitHashBytes p) f₂ hf2 hH₂ ht₂
  rw [hcard, sub_zero] at he1 he2
  calc 𝔼 G : CommitHashBytes p → ChallengeBall p.tau, (oracleAcceptFloor p κ G t0)⁻¹ ^ 2
      ≤ 𝔼 G : CommitHashBytes p → ChallengeBall p.tau, (A + (I1 G + I2 G) * B) :=
        Finset.expect_le_expect fun G _ => hpt G
    _ = A + ((𝔼 G, I1 G) + 𝔼 G, I2 G) * B := by
        rw [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty,
          ← Finset.expect_mul, Finset.expect_add_distrib]
    _ ≤ _ := by
        gcongr

end Oracle

/-! ### ML-DSA-65 and ML-DSA-87 -/

section Instances

attribute [local instance] concreteNTTRingOps

/-- `exp(C - E) ≤ 2^-1001` when `C - E ≤ -1001`. -/
private theorem exp_neg_mul_exp_le {E C : ℝ} (h : C - E ≤ -1001) :
    exp (-E) * exp C ≤ (2 : ℝ)⁻¹ ^ 1001 := by
  have h2 : exp (-1) ≤ (2 : ℝ)⁻¹ := by
    rw [Real.exp_neg]
    have := Real.add_one_le_exp (1 : ℝ)
    gcongr
    linarith
  calc exp (-E) * exp C = exp (C - E) := by rw [← exp_add]; ring_nf
    _ ≤ exp ((1001 : ℕ) * (-1)) := exp_le_exp.2 (by push_cast; linarith)
    _ = exp (-1) ^ 1001 := Real.exp_nat_mul _ _
    _ ≤ (2 : ℝ)⁻¹ ^ 1001 := pow_le_pow_left₀ (exp_pos _).le h2 _

/-- **The acceptance floor parameters at ML-DSA-65**: `x₀ = 48/125 ≥ 49 · 2^12 / 523383` and
`κ = 341/500 ≥ κ₁₂(x₀)` (`Real.logOneSubCoeff`). -/
theorem floorParams_mldsa65 : FloorParams mldsa65 (48 / 125) (341 / 500) := by
  obtain ⟨hk, -, -, hg2, hb, -⟩ := mldsa65_vals
  obtain ⟨hτ, -⟩ := mldsa65_tau_lambda
  refine ⟨by rw [hτ]; norm_num [ringDegree], by rw [hτ, hg2]; norm_num,
    by rw [hg2]; norm_num [modulus], by rw [hb, hg2]; norm_num, by rw [hk]; norm_num,
    by rw [hτ, hg2, hb]; norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro x hx hxx
  exact Real.exp_neg_sub_mul_sq_le_one_sub 12
    (by norm_num [Real.logOneSubCoeff, Finset.sum_range_succ]) hx hxx (by norm_num)

/-- **The acceptance floor parameters at ML-DSA-87**: `x₀ = 47/100 ≥ 60 · 2^12 / 523535` and
`κ = 747/1000 ≥ κ₁₂(x₀)` (`Real.logOneSubCoeff`). -/
theorem floorParams_mldsa87 : FloorParams mldsa87 (47 / 100) (747 / 1000) := by
  obtain ⟨hk, -, -, hg2, hb, -⟩ := mldsa87_vals
  obtain ⟨hτ, -⟩ := mldsa87_tau_lambda
  refine ⟨by rw [hτ]; norm_num [ringDegree], by rw [hτ, hg2]; norm_num,
    by rw [hg2]; norm_num [modulus], by rw [hb, hg2]; norm_num, by rw [hk]; norm_num,
    by rw [hτ, hg2, hb]; norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  intro x hx hxx
  exact Real.exp_neg_sub_mul_sq_le_one_sub 12
    (by norm_num [Real.logOneSubCoeff, Finset.sum_range_succ]) hx hxx (by norm_num)

/-- **The oracle average at ML-DSA-65**: for `‖t₀‖∞ ≤ 2^12` and bounds `Mb`, `Qb` on the
uniform-challenge means of `hintBoundSum` and `hintBoundSqSum`,
`𝔼_G (oracleAcceptFloor)⁻² ≤ acceptFloor(Mb + 2^-64, Qb + 2^-64)⁻² + 2^-1000`. -/
theorem expect_inv_sq_oracleAcceptFloor_le_mldsa65 (t0 : RqVec mldsa65.k)
    (ht0 : polyVecNorm t0 ≤ 4096) {Mb Qb : ℝ}
    (hMb : 𝔼 c : ChallengeBall mldsa65.tau, hintBoundSum mldsa65.gamma2 mldsa65.beta c.1 t0 ≤ Mb)
    (hQb : 𝔼 c : ChallengeBall mldsa65.tau,
      hintBoundSqSum mldsa65.gamma2 mldsa65.beta c.1 t0 ≤ Qb) :
    𝔼 G : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
        (oracleAcceptFloor mldsa65 (341 / 500) G t0)⁻¹ ^ 2 ≤
      (acceptFloor mldsa65.omega (341 / 500) (Mb + 2⁻¹ ^ 64) (Qb + 2⁻¹ ^ 64))⁻¹ ^ 2 +
        2⁻¹ ^ 1000 := by
  have := concreteNTTRingLaws
  have h := expect_inv_sq_oracleAcceptFloor_le floorParams_mldsa65 t0 ht0 hMb hQb
    (t := 2⁻¹ ^ 64) (t₂ := 2⁻¹ ^ 64) (by positivity) (by positivity)
  refine h.trans (add_le_add le_rfl ?_)
  obtain ⟨hk, -⟩ := mldsa65_vals
  obtain ⟨-, hlam⟩ := mldsa65_tau_lambda
  rw [hk, hlam, add_mul]
  have e1 := exp_neg_mul_exp_le (E := 2 * ((256 ^ (192 / 4) : ℕ) : ℝ) * ((2 : ℝ)⁻¹ ^ 64) ^ 2 /
      (((6 * ringDegree : ℕ) : ℝ) * (48 / 125)) ^ 2)
    (C := 2 * (((6 * ringDegree : ℕ) : ℝ) * (48 / 125) +
      341 / 500 * (((6 * ringDegree : ℕ) : ℝ) * (48 / 125) ^ 2))) (by norm_num [ringDegree])
  have e2 := exp_neg_mul_exp_le (E := 2 * ((256 ^ (192 / 4) : ℕ) : ℝ) * ((2 : ℝ)⁻¹ ^ 64) ^ 2 /
      (((6 * ringDegree : ℕ) : ℝ) * (48 / 125) ^ 2) ^ 2)
    (C := 2 * (((6 * ringDegree : ℕ) : ℝ) * (48 / 125) +
      341 / 500 * (((6 * ringDegree : ℕ) : ℝ) * (48 / 125) ^ 2))) (by norm_num [ringDegree])
  have h2 : (2 : ℝ)⁻¹ ^ 1001 + (2 : ℝ)⁻¹ ^ 1001 = 2⁻¹ ^ 1000 := by
    rw [pow_succ, ← two_mul, mul_left_comm, show (2 : ℝ) * 2⁻¹ = 1 by norm_num, mul_one]
  generalize (2 : ℝ)⁻¹ ^ 1001 = a at e1 e2 h2
  generalize (2 : ℝ)⁻¹ ^ 1000 = a' at h2 ⊢
  linarith

/-- **The oracle average at ML-DSA-87**: for `‖t₀‖∞ ≤ 2^12` and bounds `Mb`, `Qb` on the
uniform-challenge means of `hintBoundSum` and `hintBoundSqSum`,
`𝔼_G (oracleAcceptFloor)⁻² ≤ acceptFloor(Mb + 2^-64, Qb + 2^-64)⁻² + 2^-1000`. -/
theorem expect_inv_sq_oracleAcceptFloor_le_mldsa87 (t0 : RqVec mldsa87.k)
    (ht0 : polyVecNorm t0 ≤ 4096) {Mb Qb : ℝ}
    (hMb : 𝔼 c : ChallengeBall mldsa87.tau, hintBoundSum mldsa87.gamma2 mldsa87.beta c.1 t0 ≤ Mb)
    (hQb : 𝔼 c : ChallengeBall mldsa87.tau,
      hintBoundSqSum mldsa87.gamma2 mldsa87.beta c.1 t0 ≤ Qb) :
    𝔼 G : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
        (oracleAcceptFloor mldsa87 (747 / 1000) G t0)⁻¹ ^ 2 ≤
      (acceptFloor mldsa87.omega (747 / 1000) (Mb + 2⁻¹ ^ 64) (Qb + 2⁻¹ ^ 64))⁻¹ ^ 2 +
        2⁻¹ ^ 1000 := by
  have := concreteNTTRingLaws
  have h := expect_inv_sq_oracleAcceptFloor_le floorParams_mldsa87 t0 ht0 hMb hQb
    (t := 2⁻¹ ^ 64) (t₂ := 2⁻¹ ^ 64) (by positivity) (by positivity)
  refine h.trans (add_le_add le_rfl ?_)
  obtain ⟨hk, -⟩ := mldsa87_vals
  obtain ⟨-, hlam⟩ := mldsa87_tau_lambda
  rw [hk, hlam, add_mul]
  have e1 := exp_neg_mul_exp_le (E := 2 * ((256 ^ (256 / 4) : ℕ) : ℝ) * ((2 : ℝ)⁻¹ ^ 64) ^ 2 /
      (((8 * ringDegree : ℕ) : ℝ) * (47 / 100)) ^ 2)
    (C := 2 * (((8 * ringDegree : ℕ) : ℝ) * (47 / 100) +
      747 / 1000 * (((8 * ringDegree : ℕ) : ℝ) * (47 / 100) ^ 2))) (by norm_num [ringDegree])
  have e2 := exp_neg_mul_exp_le (E := 2 * ((256 ^ (256 / 4) : ℕ) : ℝ) * ((2 : ℝ)⁻¹ ^ 64) ^ 2 /
      (((8 * ringDegree : ℕ) : ℝ) * (47 / 100) ^ 2) ^ 2)
    (C := 2 * (((8 * ringDegree : ℕ) : ℝ) * (47 / 100) +
      747 / 1000 * (((8 * ringDegree : ℕ) : ℝ) * (47 / 100) ^ 2))) (by norm_num [ringDegree])
  have h2 : (2 : ℝ)⁻¹ ^ 1001 + (2 : ℝ)⁻¹ ^ 1001 = 2⁻¹ ^ 1000 := by
    rw [pow_succ, ← two_mul, mul_left_comm, show (2 : ℝ) * 2⁻¹ = 1 by norm_num, mul_one]
  generalize (2 : ℝ)⁻¹ ^ 1001 = a at e1 e2 h2
  generalize (2 : ℝ)⁻¹ ^ 1000 = a' at h2 ⊢
  linarith

end Instances

end GordieHowe.MLDSA.Regularity
