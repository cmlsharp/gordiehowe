-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.Floor
public import GordieHowe.Applications.MLDSA.Signing.Flatten
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

@[expose] public section

/-!
# Moments of a uniform challenge times a fixed polynomial

The challenge set `B_τ` of FIPS 204 (§2.3 and §7.3: the polynomials of `R_q` with coefficients in
`{-1, 0, 1}`, exactly `τ` of them nonzero; Algorithm 29, `SampleInBall`, samples it) is
`ChallengeBall τ`, the subtype of `IsChallenge τ`. For a uniform `c ∈ B_τ` and a fixed integer
vector `x`, each coefficient of the negacyclic product `c ⋆ x` is a sum `∑_{j ∈ S} s_j w_j` over a
uniform `τ`-subset `S` with independent uniform signs `s_j`, where the weights `w_j = ±x_{k-j}`
are the entries of `x` permuted and signed (`negacyclicConvCoeff_eq_sum_weight`).

**Signed subset sums** (`ChallengeSeed n τ`: a `τ`-subset and a sign at every position):

* `sum_signs_mul`, `sum_signs_sq`: `∑_ε s_i s_j = 2^n [i = j ∈ S]`, so
  `∑_ε (∑_j s_j w_j)² = 2^n ∑_{j ∈ S} w_j²`;
* `sum_powersetCard_sum`: `∑_{#T = k} ∑_{j ∈ T} a_j = C(#s - 1, k - 1) ∑_j a_j` for `k ≥ 1`;
* `expect_seed_sq`: `𝔼_ω (∑_j c_j w_j)² = τ/n · ∑_j w_j²` for `τ ≤ n`;
* `sum_signs_exp_le`, `expect_seed_exp_le`: `𝔼_ω exp(λ ∑_j c_j w_j) ≤ 𝔼_S exp(λ²/2 ∑_{j ∈ S} w_j²)`
  (`cosh y ≤ exp(y²/2)`);
* `expect_subset_exp_le`: `𝔼_S exp(μ ∑_{j ∈ S} a_j) ≤ (mean_j exp(μ a_j))^τ` (Hoeffding's
  comparison for sampling without replacement, `Finset.sum_powersetCard_exp_le`).

**The negacyclic product** (`x : Fin n → ℤ`, coefficient `k`):

* `expect_seed_negacyclicConvCoeff_sq`: `𝔼_ω (c ⋆ x)_k² = τ/n · ∑_m x_m²`;
* `expect_seed_exp_negacyclicConvCoeff_le_subset`:
  `𝔼_ω exp(λ (c ⋆ x)_k) ≤ 𝔼_S exp(λ²/2 ∑_{m ∈ S} x_m²)`;
* `expect_seed_exp_negacyclicConvCoeff_le`: `𝔼_ω exp(λ (c ⋆ x)_k) ≤ (mean_m exp(λ² x_m²/2))^τ`.

**The challenge set** (`n = 256`):

* `ChallengeBall`, `expect_challengeBall_eq_seed`: the uniform challenge of `B_τ` is the
  polynomial of a uniform seed;
* `expect_challengeBall_negacyclicConvCoeff_sq`, `expect_challengeBall_exp_le_subset`,
  `expect_challengeBall_exp_le`: the three statements above for `c` uniform on `B_τ`;
* `centeredCoeffs_smul`: the centered coefficients of `c • t₀` over `R_q` are the integer
  negacyclic products of the centered coefficients, when `2τ‖t₀‖∞ < q`;
* `expect_challengeBall_centeredCoeffs_sq`, `expect_challengeBall_exp_centeredCoeffs_le`: the
  second moment and the exponential moment of the shift `b = c·t₀` of `t0Weight`.
-/

open Finset Real PMF
open scoped BigOperators

namespace GordieHowe.MLDSA

/-! ### Signed subset sums -/

section SignedSubset

variable {n τ : ℕ}

/-- Flipping the sign at `i` negates the signed coefficient at `i` and keeps the others. -/
theorem signedCoeff_update_not (S : Finset (Fin n)) (ε : Fin n → Bool) (i j : Fin n) :
    signedCoeff S (Function.update ε i (!ε i)) j =
      if j = i then -signedCoeff S ε j else signedCoeff S ε j := by
  unfold signedCoeff
  by_cases hji : j = i
  · subst hji
    by_cases hj : j ∈ S <;> by_cases he : ε j <;> simp [hj, he]
  · simp [hji]

/-- Flipping the sign at `i` is an involution of the sign vectors. -/
theorem update_not_involutive (i : Fin n) :
    Function.Involutive fun ε : Fin n → Bool => Function.update ε i (!ε i) := fun ε => by
  funext j
  by_cases hji : j = i
  · subst hji; simp
  · simp [Function.update_of_ne hji]

/-- **Sign correlations**: `∑_ε s_i s_j = 2^n` if `i = j ∈ S`, and `0` otherwise, for the signed
coefficients `s = signedCoeff S ε`. -/
theorem sum_signs_mul (S : Finset (Fin n)) (i j : Fin n) :
    ∑ ε : Fin n → Bool, (signedCoeff S ε i : ℝ) * signedCoeff S ε j =
      if i = j ∧ i ∈ S then 2 ^ n else 0 := by
  by_cases hij : i = j
  · subst hij
    have : ∀ ε : Fin n → Bool, (signedCoeff S ε i : ℝ) * signedCoeff S ε i =
        if i ∈ S then 1 else 0 := fun ε => by
      unfold signedCoeff
      by_cases hi : i ∈ S <;> by_cases he : ε i <;> simp [hi, he]
    simp only [this, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      true_and]
    split_ifs <;> simp
  · have hc : ¬(i = j ∧ i ∈ S) := fun h => hij h.1
    simp only [hc, ↓reduceIte]
    set F : (Fin n → Bool) → ℝ := fun ε => (signedCoeff S ε i : ℝ) * signedCoeff S ε j
    have hflip := Fintype.sum_equiv (Function.Involutive.toPerm _ (update_not_involutive i)) F
      (fun ε => -F ε) fun ε => by
        simp [F, signedCoeff_update_not, Ne.symm hij]
    rw [sum_neg_distrib] at hflip
    linarith

/-- **Averaging the signs of a square**: `∑_ε (∑_j s_j w_j)² = 2^n ∑_{j ∈ S} w_j²`. -/
theorem sum_signs_sq (S : Finset (Fin n)) (w : Fin n → ℝ) :
    ∑ ε : Fin n → Bool, (∑ j, (signedCoeff S ε j : ℝ) * w j) ^ 2 = 2 ^ n * ∑ j ∈ S, w j ^ 2 := by
  have hexp : ∀ ε : Fin n → Bool, (∑ j, (signedCoeff S ε j : ℝ) * w j) ^ 2 =
      ∑ i, ∑ j, w i * w j * ((signedCoeff S ε i : ℝ) * signedCoeff S ε j) := fun ε => by
    rw [sq, sum_mul_sum]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have hi : ∀ i, ∑ ε : Fin n → Bool, ∑ j, w i * w j * ((signedCoeff S ε i : ℝ) *
      signedCoeff S ε j) = if i ∈ S then 2 ^ n * w i ^ 2 else 0 := fun i => by
    rw [sum_comm]
    simp_rw [← mul_sum, sum_signs_mul]
    rw [sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
    by_cases hiS : i ∈ S
    · simp only [hiS, and_self, ↓reduceIte]
      ring
    · simp [hiS]
  simp_rw [hexp]
  rw [sum_comm, sum_congr rfl fun i _ => hi i, sum_ite_mem, univ_inter, mul_sum]

/-- **The sum over `k`-subsets of a subset sum**: every element lies in `C(#s - 1, k - 1)` of the
`k`-subsets of `s`, so `∑_{T ⊆ s, #T = k} ∑_{j ∈ T} a_j = C(#s - 1, k - 1) ∑_{j ∈ s} a_j` for
`k ≥ 1`. -/
theorem sum_powersetCard_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ) {k : ℕ}
    (hk : 1 ≤ k) :
    ∑ T ∈ s.powersetCard k, ∑ j ∈ T, a j = ((s.card - 1).choose (k - 1) : ℝ) * ∑ j ∈ s, a j := by
  have hT : ∀ T ∈ s.powersetCard k, ∑ j ∈ T, a j = ∑ j ∈ s, if j ∈ T then a j else 0 :=
    fun T hT => by
      rw [← sum_filter]
      congr 1
      ext j
      simp only [mem_filter]
      exact ⟨fun h => ⟨(mem_powersetCard.1 hT).1 h, h⟩, fun h => h.2⟩
  rw [sum_congr rfl hT, sum_comm, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  congr 1
  have hc := card_filter_powersetCard_subset {j} s k (singleton_subset_iff.2 hj)
    (by simpa using hk)
  simp only [singleton_subset_iff, card_singleton] at hc
  exact_mod_cast hc

/-- The expectation over seeds as the average over subsets of the sums over signs. -/
theorem sum_seed_eq (F : Finset (Fin n) → (Fin n → Bool) → ℝ) :
    ∑ ω : ChallengeSeed n τ, F ω.1.1 ω.2 = ∑ S ∈ univ.powersetCard τ, ∑ ε, F S ε := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_coe_sort (univ.powersetCard τ) fun S => ∑ ε, F S ε

/-- **The second moment of a signed subset sum**: for a uniform seed with `τ ≤ n`,
`𝔼_ω (∑_j c_j w_j)² = τ/n · ∑_j w_j²`. -/
theorem expect_seed_sq (hτ : τ ≤ n) (w : Fin n → ℝ) :
    𝔼 ω : ChallengeSeed n τ, (∑ j, (ω.coeff j : ℝ) * w j) ^ 2 = τ / n * ∑ j, w j ^ 2 := by
  rw [Fintype.expect_eq_sum_div_card, card_challengeSeed]
  simp only [ChallengeSeed.coeff]
  rw [sum_seed_eq (fun S ε => (∑ j, (signedCoeff S ε j : ℝ) * w j) ^ 2)]
  simp_rw [sum_signs_sq]
  rw [← mul_sum]
  rcases Nat.eq_zero_or_pos τ with rfl | hτ0
  · simp
  have hn : 0 < n := lt_of_lt_of_le hτ0 hτ
  rw [sum_powersetCard_sum _ _ hτ0, card_univ, Fintype.card_fin]
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨τ', rfl⟩ : ∃ τ', τ = τ' + 1 := ⟨τ - 1, by omega⟩
  have hc := Nat.add_one_mul_choose_eq n' τ'
  have hc' : ((n' : ℝ) + 1) * (n'.choose τ' : ℝ) = ((n' + 1).choose (τ' + 1) : ℝ) * (τ' + 1) := by
    exact_mod_cast hc
  have hpos : (0 : ℝ) < ((n' + 1).choose (τ' + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos hτ
  have hC : (n'.choose τ' : ℝ) = ((n' + 1).choose (τ' + 1) : ℝ) * (τ' + 1) / (n' + 1) := by
    rw [eq_div_iff (by positivity)]
    linarith
  simp only [Nat.add_sub_cancel]
  push_cast
  rw [hC]
  field_simp

/-- **The exponential moment over the signs**: `∑_ε exp(λ ∑_j s_j w_j) ≤ 2^n exp(λ²/2 ∑_{j ∈ S}
w_j²)`, from `cosh y ≤ exp(y²/2)`. -/
theorem sum_signs_exp_le (S : Finset (Fin n)) (w : Fin n → ℝ) (lam : ℝ) :
    ∑ ε : Fin n → Bool, exp (lam * ∑ j, (signedCoeff S ε j : ℝ) * w j) ≤
      2 ^ n * exp (lam ^ 2 / 2 * ∑ j ∈ S, w j ^ 2) := by
  rw [sum_signs_exp]
  gcongr
  rw [mul_sum, exp_sum]
  refine prod_le_prod₀ (fun j _ => (cosh_pos _).le) fun j _ => ?_
  refine (cosh_le_exp_half_sq _).trans_eq ?_
  congr 1
  ring

/-- **The sub-Gaussian bound for a signed subset sum**: for a uniform seed and every `λ`,
`𝔼_ω exp(λ ∑_j c_j w_j) ≤ 𝔼_S exp(λ²/2 ∑_{j ∈ S} w_j²)` with `S` a uniform `τ`-subset. -/
theorem expect_seed_exp_le (w : Fin n → ℝ) (lam : ℝ) :
    𝔼 ω : ChallengeSeed n τ, exp (lam * ∑ j, (ω.coeff j : ℝ) * w j) ≤
      𝔼 S : {S : Finset (Fin n) // S ∈ (univ : Finset (Fin n)).powersetCard τ},
        exp (lam ^ 2 / 2 * ∑ j ∈ S.1, w j ^ 2) := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card, card_challengeSeed]
  simp only [ChallengeSeed.coeff]
  rw [sum_seed_eq (fun S ε => exp (lam * ∑ j, (signedCoeff S ε j : ℝ) * w j)),
    Finset.sum_coe_sort (univ.powersetCard τ) fun S => exp (lam ^ 2 / 2 * ∑ j ∈ S, w j ^ 2),
    Fintype.card_coe, card_powersetCard, card_univ, Fintype.card_fin]
  rcases Nat.eq_zero_or_pos (n.choose τ) with h0 | hpos
  · simp [h0]
  rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast hpos)]
  have := sum_le_sum fun S (_ : S ∈ univ.powersetCard τ) => sum_signs_exp_le S w lam
  rw [← mul_sum] at this
  push_cast
  nlinarith [this, (by positivity : (0 : ℝ) ≤ (n.choose τ : ℝ))]

/-- **Hoeffding's comparison as an expectation**: for a uniform `τ`-subset `S`,
`𝔼_S exp(μ ∑_{j ∈ S} a_j) ≤ (mean_j exp(μ a_j))^τ`. -/
theorem expect_subset_exp_le (a : Fin n → ℝ) (μ : ℝ) :
    𝔼 S : {S : Finset (Fin n) // S ∈ (univ : Finset (Fin n)).powersetCard τ},
        exp (μ * ∑ j ∈ S.1, a j) ≤ ((∑ j, exp (μ * a j)) / n) ^ τ := by
  rw [Fintype.expect_eq_sum_div_card,
    Finset.sum_coe_sort (univ.powersetCard τ) fun S => exp (μ * ∑ j ∈ S, a j),
    Fintype.card_coe, card_powersetCard, card_univ, Fintype.card_fin]
  have hR : 0 ≤ ((∑ j, exp (μ * a j)) / n) ^ τ :=
    pow_nonneg (div_nonneg (sum_nonneg fun j _ => (exp_pos _).le) (Nat.cast_nonneg _)) _
  rcases Nat.eq_zero_or_pos (n.choose τ) with h0 | hpos
  · simp [h0, hR]
  rw [div_le_iff₀ (by exact_mod_cast hpos)]
  have := sum_powersetCard_exp_le (univ : Finset (Fin n)) a μ τ
  rw [card_univ, Fintype.card_fin] at this
  linarith

end SignedSubset

/-! ### The negacyclic product -/

section Negacyclic

variable {n τ : ℕ}

/-- An even function of the weights of one coefficient sums to the same function of the entries
of `t`: the weights are the entries of `t`, permuted and signed. -/
theorem sum_even_negacyclicWeight [NeZero n] (t : Fin n → ℤ) (k : Fin n) (g : ℝ → ℝ)
    (hg : ∀ y, g (-y) = g y) :
    ∑ j, g (negacyclicWeight t k j : ℝ) = ∑ i, g (t i : ℝ) := by
  have hj : ∀ j, g (negacyclicWeight t k j : ℝ) = g (t (k - j) : ℝ) := fun j => by
    unfold negacyclicWeight
    split_ifs
    · rfl
    · push_cast; rw [hg]
  simp_rw [hj]
  exact Fintype.sum_equiv (Equiv.subLeft k) _ _ fun j => rfl

/-- A coefficient of `c ⋆ t`, cast to `ℝ`, is the signed sum of its weights. -/
theorem negacyclicConvCoeff_cast (c t : Fin n → ℤ) (k : Fin n) :
    ((LatticeCrypto.negacyclicConvCoeff c t k : ℤ) : ℝ) =
      ∑ j, (c j : ℝ) * (negacyclicWeight t k j : ℝ) := by
  rw [negacyclicConvCoeff_eq_sum_weight]
  push_cast
  rfl

/-- **The exact second moment of a coefficient of `c ⋆ x`**: for a uniform seed with `τ ≤ n`,
`𝔼_ω (c ⋆ x)_k² = τ/n · ∑_m x_m²`. -/
theorem expect_seed_negacyclicConvCoeff_sq [NeZero n] (hτ : τ ≤ n) (x : Fin n → ℤ) (k : Fin n) :
    𝔼 ω : ChallengeSeed n τ, ((LatticeCrypto.negacyclicConvCoeff ω.coeff x k : ℤ) : ℝ) ^ 2 =
      τ / n * ∑ m, (x m : ℝ) ^ 2 := by
  simp_rw [negacyclicConvCoeff_cast]
  rw [expect_seed_sq hτ, sum_even_negacyclicWeight x k (· ^ 2) fun y => by ring]

/-- **The sub-Gaussian bound for a coefficient of `c ⋆ x`, through a uniform subset**: for a
uniform seed and every `λ`, `𝔼_ω exp(λ (c ⋆ x)_k) ≤ 𝔼_S exp(λ²/2 ∑_{m ∈ S} x_m²)` with `S` a
uniform `τ`-subset. -/
theorem expect_seed_exp_negacyclicConvCoeff_le_subset [NeZero n] (x : Fin n → ℤ) (k : Fin n)
    (lam : ℝ) :
    𝔼 ω : ChallengeSeed n τ, exp (lam * ((LatticeCrypto.negacyclicConvCoeff ω.coeff x k : ℤ) : ℝ)) ≤
      𝔼 S : {S : Finset (Fin n) // S ∈ (univ : Finset (Fin n)).powersetCard τ},
        exp (lam ^ 2 / 2 * ∑ m ∈ S.1, (x m : ℝ) ^ 2) := by
  simp_rw [negacyclicConvCoeff_cast]
  refine (expect_seed_exp_le _ lam).trans_eq ?_
  let e : Fin n ≃ Fin n := Equiv.subLeft k
  let E : {S : Finset (Fin n) // S ∈ (univ : Finset (Fin n)).powersetCard τ} ≃
      {S : Finset (Fin n) // S ∈ (univ : Finset (Fin n)).powersetCard τ} :=
    Equiv.subtypeEquiv (Equiv.finsetCongr e) fun S => by simp
  refine Fintype.expect_equiv E _ _ fun S => ?_
  congr 2
  simp only [E, Equiv.subtypeEquiv_apply, Equiv.finsetCongr_apply, sum_map,
    Equiv.coe_toEmbedding]
  refine sum_congr rfl fun j _ => ?_
  simp only [e, Equiv.subLeft_apply, negacyclicWeight]
  split_ifs
  · rfl
  · push_cast; ring

/-- **The sub-Gaussian bound for a coefficient of `c ⋆ x`**: for a uniform seed and every `λ`,
`𝔼_ω exp(λ (c ⋆ x)_k) ≤ (mean_m exp(λ² x_m² / 2))^τ`. -/
theorem expect_seed_exp_negacyclicConvCoeff_le [NeZero n] (x : Fin n → ℤ) (k : Fin n) (lam : ℝ) :
    𝔼 ω : ChallengeSeed n τ, exp (lam * ((LatticeCrypto.negacyclicConvCoeff ω.coeff x k : ℤ) : ℝ)) ≤
      ((∑ m, exp (lam ^ 2 / 2 * (x m : ℝ) ^ 2)) / n) ^ τ :=
  (expect_seed_exp_negacyclicConvCoeff_le_subset x k lam).trans
    (expect_subset_exp_le (fun m => (x m : ℝ) ^ 2) _)

end Negacyclic

/-! ### The challenge set `B_τ` -/

section Ball

open _root_.MLDSA _root_.MLDSA.Concrete LatticeCrypto TransformOps

instance : NeZero ringDegree :=
  ⟨by norm_num [ringDegree]⟩

/-- **The challenge set `B_τ`** of FIPS 204 (§2.3, §7.3): the polynomials of `R_q` with
coefficients in `{-1, 0, 1}`, exactly `τ` of them nonzero, the outputs of `SampleInBall`
(Algorithm 29). -/
abbrev ChallengeBall (τ : ℕ) : Type := {c : Rq // IsChallenge τ c}

/-- `B_τ` is nonempty for `τ ≤ 256`. -/
theorem challengeBall_nonempty {τ : ℕ} (hτ : τ ≤ ringDegree) : Nonempty (ChallengeBall τ) := by
  obtain ⟨S, hS⟩ := powersetCard_nonempty.2 (by simpa using hτ :
    τ ≤ (univ : Finset (Fin ringDegree)).card)
  let ω : ChallengeSeed ringDegree τ := (⟨S, hS⟩, fun _ => true)
  exact ⟨⟨ω.poly, isChallenge_seedPoly ω⟩⟩

/-- **Summing through a map with fibers of equal size**: if `f` lands in `Q` and every `b ∈ Q`
has exactly `k` preimages, then `∑_a F (f a) = k · ∑_{b ∈ Q} F b`. -/
theorem sum_comp_eq_mul {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (Q : β → Prop) [DecidablePred Q] {k : ℕ} (hf : ∀ a, Q (f a))
    (hfib : ∀ b, Q b → (univ.filter fun a => f a = b).card = k) (F : β → ℝ) :
    ∑ a, F (f a) = k * ∑ b ∈ univ.filter Q, F b := by
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ.filter Q) (g := f)
    (fun a _ => by simpa using hf a), mul_sum]
  refine sum_congr rfl fun b hb => ?_
  rw [sum_congr rfl fun a ha => by rw [(mem_filter.1 ha).2], sum_const, nsmul_eq_mul,
    hfib b (mem_filter.1 hb).2]

/-- **The uniform challenge of `B_τ` is the polynomial of a uniform seed**: for every `F`,
`𝔼_{c ∈ B_τ} F c = 𝔼_ω F (ω.poly)`. -/
theorem expect_challengeBall_eq_seed {τ : ℕ} (F : Rq → ℝ) :
    𝔼 c : ChallengeBall τ, F c.1 = 𝔼 ω : ChallengeSeed ringDegree τ, F ω.poly := by
  have hsum := sum_comp_eq_mul (fun ω : ChallengeSeed ringDegree τ => ω.poly) (IsChallenge τ)
    isChallenge_seedPoly (fun _ hc => card_seedPoly_eq hc) F
  have hcard := sum_comp_eq_mul (fun ω : ChallengeSeed ringDegree τ => ω.poly) (IsChallenge τ)
    isChallenge_seedPoly (fun _ hc => card_seedPoly_eq hc) fun _ => 1
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at hcard
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card, hsum, hcard,
    Fintype.card_subtype,
    Finset.sum_subtype (univ.filter (IsChallenge τ)) (p := IsChallenge τ) (fun c => by simp) F]
  have : (2 : ℝ) ^ (ringDegree - τ) ≠ 0 := by positivity
  push_cast
  rw [mul_div_mul_left _ _ this]

/-- The centered coefficients of a challenge of `B_τ` are those of a seed's challenge. -/
theorem expect_challengeBall_centered {τ : ℕ} (F : (Fin ringDegree → ℤ) → ℝ) :
    𝔼 c : ChallengeBall τ, F (centeredPoly c.1) = 𝔼 ω : ChallengeSeed ringDegree τ, F ω.coeff := by
  rw [expect_challengeBall_eq_seed (fun c => F (centeredPoly c))]
  simp_rw [centeredPoly_seedPoly]

/-- **The exact second moment over `B_τ`**: for `c` uniform on `B_τ` with `τ ≤ 256`,
`𝔼_c (c ⋆ x)_k² = τ/256 · ∑_m x_m²`, with `c` read through its centered coefficients. -/
theorem expect_challengeBall_negacyclicConvCoeff_sq {τ : ℕ} (hτ : τ ≤ ringDegree)
    (x : Fin ringDegree → ℤ) (k : Fin ringDegree) :
    𝔼 c : ChallengeBall τ, ((negacyclicConvCoeff (centeredPoly c.1) x k : ℤ) : ℝ) ^ 2 =
      τ / ringDegree * ∑ m, (x m : ℝ) ^ 2 := by
  rw [expect_challengeBall_centered (fun c => ((negacyclicConvCoeff c x k : ℤ) : ℝ) ^ 2)]
  exact expect_seed_negacyclicConvCoeff_sq hτ x k

/-- **The sub-Gaussian bound over `B_τ`, through a uniform subset**: for `c` uniform on `B_τ`
and every `λ`, `𝔼_c exp(λ (c ⋆ x)_k) ≤ 𝔼_S exp(λ²/2 ∑_{m ∈ S} x_m²)`, `S` a uniform
`τ`-subset. -/
theorem expect_challengeBall_exp_le_subset {τ : ℕ} (x : Fin ringDegree → ℤ) (k : Fin ringDegree)
    (lam : ℝ) :
    𝔼 c : ChallengeBall τ, exp (lam * ((negacyclicConvCoeff (centeredPoly c.1) x k : ℤ) : ℝ)) ≤
      𝔼 S : {S : Finset (Fin ringDegree) // S ∈ (univ : Finset (Fin ringDegree)).powersetCard τ},
        exp (lam ^ 2 / 2 * ∑ m ∈ S.1, (x m : ℝ) ^ 2) := by
  rw [expect_challengeBall_centered (fun c => exp (lam * ((negacyclicConvCoeff c x k : ℤ) : ℝ)))]
  exact expect_seed_exp_negacyclicConvCoeff_le_subset x k lam

/-- **The sub-Gaussian bound over `B_τ`**: for `c` uniform on `B_τ` and every `λ`,
`𝔼_c exp(λ (c ⋆ x)_k) ≤ (mean_m exp(λ² x_m² / 2))^τ`. -/
theorem expect_challengeBall_exp_le {τ : ℕ} (x : Fin ringDegree → ℤ) (k : Fin ringDegree)
    (lam : ℝ) :
    𝔼 c : ChallengeBall τ, exp (lam * ((negacyclicConvCoeff (centeredPoly c.1) x k : ℤ) : ℝ)) ≤
      ((∑ m, exp (lam ^ 2 / 2 * (x m : ℝ) ^ 2)) / ringDegree) ^ τ := by
  rw [expect_challengeBall_centered (fun c => exp (lam * ((negacyclicConvCoeff c x k : ℤ) : ℝ)))]
  exact expect_seed_exp_negacyclicConvCoeff_le x k lam

variable [nttOps : NTTRingOps] [NTTRingLaws nttOps]

/-- **The centered coefficients of `c • t₀` are the integer negacyclic products**: for `c` with
at most `τ` nonzero coefficients of norm at most `1`, `‖t₀‖∞ ≤ B` and `2τB < q`, coefficient `i`
of component `m` of `c • t₀`, centered, is `(c ⋆ t₀,m)_i` over `ℤ` (no coefficient wraps mod
`q`). -/
theorem centeredCoeffs_smul {τ B k : ℕ} (c : Rq) (t0 : RqVec k) (hc1 : polyNorm c ≤ 1)
    (hcw : (univ.filter fun i : Fin ringDegree => c.get i ≠ 0).card ≤ τ)
    (ht0 : polyVecNorm t0 ≤ B) (hq : 2 * (τ * B) < modulus) (mi : Fin k × Fin ringDegree) :
    centeredCoeffs (c • t0) mi =
      negacyclicConvCoeff (centeredPoly c) (centeredVec t0 mi.1) mi.2 := by
  have hrow : polyNorm (t0.get mi.1) ≤ B :=
    (LatticeCrypto.PolyVec.component_cInfNorm_le normOps t0 mi.1).trans ht0
  change centeredRepr (((c • t0).get mi.1).get mi.2) = _
  rw [smul_eq_coeffScalarVecMul, LatticeCrypto.TransformOps.coeffScalarVecMul_get]
  exact congrFun (centeredPoly_mul c (t0.get mi.1) hc1 hcw hrow hq) mi.2

/-- **The second moment of the shift `b = c·t₀`**: for `c` uniform on `B_τ`, `τ ≤ 256`,
`‖t₀‖∞ ≤ B` and `2τB < q`, `𝔼_c b_{m,i}² = τ/256 · ‖t₀,m‖₂²` with `b = centeredCoeffs (c • t₀)`
(the shift of `t0Weight`). -/
theorem expect_challengeBall_centeredCoeffs_sq {τ B k : ℕ} (hτ : τ ≤ ringDegree) (t0 : RqVec k)
    (ht0 : polyVecNorm t0 ≤ B) (hq : 2 * (τ * B) < modulus) (mi : Fin k × Fin ringDegree) :
    𝔼 c : ChallengeBall τ, ((centeredCoeffs (c.1 • t0) mi : ℤ) : ℝ) ^ 2 =
      τ / ringDegree * ∑ m, (centeredVec t0 mi.1 m : ℝ) ^ 2 := by
  rw [← expect_challengeBall_negacyclicConvCoeff_sq hτ (centeredVec t0 mi.1) mi.2]
  refine Finset.expect_congr rfl fun c _ => ?_
  rw [centeredCoeffs_smul c.1 t0 c.2.1 c.2.2.le ht0 hq mi]

/-- **The exponential moment of the shift `b = c·t₀`**: for `c` uniform on `B_τ`, `‖t₀‖∞ ≤ B`,
`2τB < q` and every `λ`, `𝔼_c exp(λ b_{m,i}) ≤ (mean_j exp(λ² t₀,m,j² / 2))^τ`. -/
theorem expect_challengeBall_exp_centeredCoeffs_le {τ B k : ℕ} (t0 : RqVec k)
    (ht0 : polyVecNorm t0 ≤ B) (hq : 2 * (τ * B) < modulus) (mi : Fin k × Fin ringDegree)
    (lam : ℝ) :
    𝔼 c : ChallengeBall τ, exp (lam * (centeredCoeffs (c.1 • t0) mi : ℝ)) ≤
      ((∑ j, exp (lam ^ 2 / 2 * (centeredVec t0 mi.1 j : ℝ) ^ 2)) / ringDegree) ^ τ := by
  refine le_of_eq_of_le (Finset.expect_congr rfl fun c _ => ?_)
    (expect_challengeBall_exp_le (centeredVec t0 mi.1) mi.2 lam)
  rw [centeredCoeffs_smul c.1 t0 c.2.1 c.2.2.le ht0 hq mi]

end Ball

end GordieHowe.MLDSA
