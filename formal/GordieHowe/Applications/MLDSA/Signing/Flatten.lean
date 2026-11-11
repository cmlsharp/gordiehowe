-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.Ideal
public import GordieHowe.Applications.MLDSA.Signing.Cutoff
public import GordieHowe.Applications.MLDSA.Signing.Surrogate
public import GordieHowe.Foundations.ToMathlib.PMFOracleSide
public import GordieHowe.Foundations.ToMathlib.NNRatENNReal
import all LatticeCrypto.MLDSA.Concrete.Rounding

@[expose] public section

/-!
# The flattened ring prover for ML-DSA

A ring of `N` members; the signer `i` runs the idealized FIPS 204 attempt of `Ideal.lean` (mask
`y` uniform on the mask box) with commitment hash read from a random oracle. The verifier
recomputes every member's challenge from the one accepted commitment `w₁`, so the oracle is
modelled on the ring's points `(j, w₁)`, standing for `µ_j ‖ w1Encode(w₁)` (distinct for members
with distinct `tr_j`, since `w1Encode` is injective on commitments). Member `j` may publish its
`t₀` (FIPS 204 §6.1: `t₀` need not be secret), and then excludes the hashes failing its
ct₀-check (`exclSet`, `ringExclSets`).

The flattened ring prover (`flatRingProver`) repeats until it keeps: one idealized attempt; reject
if some other member's hash `H (j, w₁)` is excluded; keep with probability
`min 1 (val c̃ / signerWeight)`, `signerWeight` the uniform-`w` acceptance weight of the ct₀ and
hint checks (`acceptWeight`) and `val` a public cut-off (`Cutoff`). It outputs the oracle with the
kept `w₁`. The cut-off, the weight and the coin are rational (`ℚ≥0`, computed by
`acceptWeightQ`), so that a signer comparing them has compiled code; the laws read them cast to
`ℝ≥0∞` (`coe_signerWeight`, `coe_flattenCoin`).

* `poissonBinomialCdf_anti`, `hintFractionBound`, `acceptWeightLower`,
  `acceptWeightLower_le_acceptWeight`: the Poisson-binomial CDF is antitone in each success
  probability, so the ct₀ indicator times the CDF of the bucket-uniform hint fraction bounds is at
  most the acceptance weight in every bucket vector.
* `binomialCdf`, `poissonBinomialCdf_indicator_eq`, `binomialCdf_anti`,
  `sub_sum_le_poissonBinomialCdf`: the Poisson-binomial CDF at a vertex `x₀ 1_T` of the box
  `[0, x₀]^ι` is the binomial CDF `Pr[Bin(|T|, x₀) ≤ ω]`, antitone in `|T|`; the CDF plus
  `σ ∑_i p_i` is affine in each `p_a`, so a line `α - σ N x₀` below every vertex CDF gives
  `α - σ ∑_i p_i ≤ Pr_p[X ≤ ω]` on the box. `sub_le_binomialCdf_of_checks` reduces such a line to
  finitely many checks.
* `tvDist_flatRingProver_le`: within `ringOracleError + regError + flatError` of the ring target
  (`w₁` uniform over bucket vectors, the oracle uniform except that every member's value at `w₁`
  is uniform off its excluded set), the same for every honest signer; `regError` is the distance
  between the real and the uniform-`w` stand-in accepted laws (`realKeptLaw`, `standinKeptLaw`),
  `flatError` the flattening term, `ringOracleError` the oracle concentration term, at most
  `√(w1MaxProb / ringKeepProb) / 2` (`ringOracleError_le`).
* `tvDist_flatRingProver_signers_le`: two honest signers of one ring are within the sum of their
  error terms.
* `tvDist_flatRingProver_published_le`: rings where every member publishes `t₀` (ML-DSA-44).
* `tvDist_flatRingProver_floor_le`, `tvDist_flatRingProver_mldsa65_le`,
  `tvDist_flatRingProver_mldsa87_le`: rings of standard keys under the floor `τ · 2^(d-1) < γ₂`,
  where nothing is excluded and the target is a uniform oracle with `w₁` uniform.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA44 Finset PMF
open scoped ENNReal
open LatticeCrypto TransformOps

/-! ### Bounds on the acceptance weight -/

/-- A product over a set `t` of successes and its complement of failures. -/
theorem prod_ite_mem_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ι → ℝ) (t : Finset ι) :
    ∏ i, (if i ∈ t then q i else 1 - q i) = (∏ i ∈ t, q i) * ∏ i ∈ tᶜ, (1 - q i) := by
  rw [prod_ite]
  congr 2 <;> ext <;> simp

/-- The Poisson-binomial CDF is at most `1`. -/
theorem poissonBinomialCdf_le_one {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) (ω : ℕ) : poissonBinomialCdf q ω ≤ 1 := by
  have hnn : ∀ t : Finset ι, 0 ≤ ∏ i, (if i ∈ t then q i else 1 - q i) := fun t =>
    prod_nonneg fun i _ => by split_ifs <;> linarith [hq0 i, hq1 i]
  calc poissonBinomialCdf q ω ≤ ∑ t : Finset ι, ∏ i, (if i ∈ t then q i else 1 - q i) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun t _ _ => hnn t
    _ = ∏ i, (q i + (1 - q i)) := by
        rw [Fintype.prod_add]; exact sum_congr rfl fun t _ => prod_ite_mem_eq q t
    _ = 1 := by simp

/-- The Poisson-binomial CDF is positive when every success probability is below `1`. -/
theorem poissonBinomialCdf_pos {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℝ}
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i < 1) (ω : ℕ) : 0 < poissonBinomialCdf q ω := by
  have hnn : ∀ t : Finset ι, 0 ≤ ∏ i, (if i ∈ t then q i else 1 - q i) := fun t =>
    prod_nonneg fun i _ => by split_ifs <;> linarith [hq0 i, hq1 i]
  have h0 : 0 < ∏ i, (if i ∈ (∅ : Finset ι) then q i else 1 - q i) :=
    prod_pos fun i _ => by simp only [notMem_empty, ite_false]; linarith [hq1 i]
  exact h0.trans_le (single_le_sum (f := fun t => ∏ i, (if i ∈ t then q i else 1 - q i))
    (fun t _ => hnn t) (by simp))

/-- Fewer than `2(γ₂ - β) - 1` residues of a bucket fire the hint, for `|b| < γ₂`. -/
theorem hintCount_lt {γ₂ β r1 : ℕ} (hβ : β < γ₂) {b : ℤ} (hb : |b| < γ₂) :
    hintCount β r1 b < 2 * (γ₂ - β) - 1 := by
  unfold hintCount
  rcases abs_cases b with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1] at hb <;> split_ifs <;> omega

/-- The hint fraction is a probability. -/
theorem hintProb_nonneg (γ₂ β r1 : ℕ) (b : ℤ) : 0 ≤ hintProb γ₂ β r1 b :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The hint fraction is below `1` for `|b| < γ₂`. -/
theorem hintProb_lt_one {γ₂ β r1 : ℕ} (hβ : β < γ₂) {b : ℤ} (hb : |b| < γ₂) :
    hintProb γ₂ β r1 b < 1 := by
  have h := hintCount_lt (r1 := r1) hβ hb
  have hpos : (0 : ℝ) < ((2 * (γ₂ - β) - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  rw [hintProb, div_lt_one hpos]
  exact_mod_cast h

/-- The acceptance weight is positive when the ct₀-check passes. -/
theorem acceptWeight_pos {ι : Type*} [Fintype ι] [DecidableEq ι] {γ₂ β : ℕ} (hβ : β < γ₂)
    (ω : ℕ) {b : ι → ℤ} (hb : ∀ i, |b i| < γ₂) (v : ι → ℕ) : 0 < acceptWeight γ₂ β ω b v := by
  rw [acceptWeight, if_pos hb, one_mul]
  exact poissonBinomialCdf_pos (fun i => hintProb_nonneg _ _ _ _)
    (fun i => hintProb_lt_one hβ (hb i)) ω

/-- The acceptance weight is `0` when the ct₀-check fails. -/
theorem acceptWeight_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {γ₂ β ω : ℕ} {b : ι → ℤ}
    (hb : ¬ ∀ i, |b i| < γ₂) (v : ι → ℕ) : acceptWeight γ₂ β ω b v = 0 := by
  rw [acceptWeight, if_neg hb, zero_mul]

/-- The acceptance weight is nonnegative. -/
theorem acceptWeight_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {γ₂ β : ℕ} (hβ : β < γ₂)
    (ω : ℕ) (b : ι → ℤ) (v : ι → ℕ) : 0 ≤ acceptWeight γ₂ β ω b v := by
  by_cases hb : ∀ i, |b i| < γ₂
  · exact (acceptWeight_pos hβ ω hb v).le
  · rw [acceptWeight_eq_zero hb]

/-- The acceptance weight is a probability. -/
theorem acceptWeight_le_one {ι : Type*} [Fintype ι] [DecidableEq ι] {γ₂ β : ℕ} (hβ : β < γ₂)
    (ω : ℕ) (b : ι → ℤ) (v : ι → ℕ) : acceptWeight γ₂ β ω b v ≤ 1 := by
  by_cases hb : ∀ i, |b i| < γ₂
  · rw [acceptWeight, if_pos hb, one_mul]
    exact poissonBinomialCdf_le_one (fun i => hintProb_nonneg _ _ _ _)
      (fun i => (hintProb_lt_one hβ (hb i)).le) ω
  · rw [acceptWeight_eq_zero hb]; exact zero_le_one

/-! ### The acceptance weight from below, uniformly in the bucket vector -/

/-- **One coordinate of the Poisson-binomial CDF**: with success probability `x` at coordinate
`a` and `p` elsewhere, the CDF at `ω` is
`∑_{t ⊆ ι \ {a}} W(t) · ((1 - x) · 1[|t| ≤ ω] + x · 1[|t ∪ {a}| ≤ ω])`, with
`W(t) = ∏_{i ≠ a} (p_i if i ∈ t else 1 - p_i)`. -/
theorem poissonBinomialCdf_update_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ) (a : ι)
    (x : ℝ) (ω : ℕ) :
    poissonBinomialCdf (Function.update p a x) ω =
      ∑ t ∈ (univ.erase a).powerset, (∏ i ∈ univ.erase a, if i ∈ t then p i else 1 - p i) *
        ((1 - x) * (if t.card ≤ ω then 1 else 0) +
          x * (if (insert a t).card ≤ ω then 1 else 0)) := by
  have hu : (univ : Finset (Finset ι)) = (insert a (univ.erase a)).powerset := by
    rw [insert_erase (mem_univ a), powerset_univ]
  rw [poissonBinomialCdf, sum_filter, hu, sum_powerset_insert (notMem_erase a _),
    ← sum_add_distrib]
  refine sum_congr rfl fun t ht => ?_
  have hat : a ∉ t := fun h => notMem_erase a univ (mem_powerset.1 ht h)
  rw [← mul_prod_erase univ _ (mem_univ a), ← mul_prod_erase univ _ (mem_univ a)]
  have hW : ∏ i ∈ univ.erase a, (if i ∈ t then Function.update p a x i
      else 1 - Function.update p a x i) = ∏ i ∈ univ.erase a, if i ∈ t then p i else 1 - p i :=
    prod_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_erase hi)]
  have hW' : ∏ i ∈ univ.erase a, (if i ∈ insert a t then Function.update p a x i
      else 1 - Function.update p a x i) = ∏ i ∈ univ.erase a, if i ∈ t then p i else 1 - p i :=
    prod_congr rfl fun i hi => by
      simp only [Function.update_of_ne (ne_of_mem_erase hi), mem_insert, ne_of_mem_erase hi,
        false_or]
  rw [hW, hW', if_neg hat, if_pos (mem_insert_self a t), Function.update_self]
  split_ifs <;> ring

/-- **Raising one success probability lowers the Poisson-binomial CDF**: for `p_i ∈ [0, 1]` and
`p_a ≤ x`, the CDF with `x` at coordinate `a` is at most the CDF of `p`. -/
theorem poissonBinomialCdf_update_le {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → ℝ}
    (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1) (a : ι) {x : ℝ} (hx : p a ≤ x) (ω : ℕ) :
    poissonBinomialCdf (Function.update p a x) ω ≤ poissonBinomialCdf p ω := by
  have hp : poissonBinomialCdf p ω = poissonBinomialCdf (Function.update p a (p a)) ω := by
    rw [Function.update_eq_self]
  rw [hp, poissonBinomialCdf_update_eq, poissonBinomialCdf_update_eq]
  refine sum_le_sum fun t _ => mul_le_mul_of_nonneg_left ?_
    (prod_nonneg fun i _ => by split_ifs <;> linarith [h0 i, h1 i])
  have hc := card_le_card (subset_insert a t)
  have hmono : (if (insert a t).card ≤ ω then (1 : ℝ) else 0) ≤ if t.card ≤ ω then 1 else 0 := by
    split_ifs <;> first | (exfalso; omega) | norm_num
  nlinarith

/-- **The Poisson-binomial CDF is antitone in the success probabilities**: for
`0 ≤ p_i ≤ q_i ≤ 1`, `Pr_q[X ≤ ω] ≤ Pr_p[X ≤ ω]`. -/
theorem poissonBinomialCdf_anti {ι : Type*} [Fintype ι] [DecidableEq ι] {p q : ι → ℝ}
    (h0 : ∀ i, 0 ≤ p i) (hpq : ∀ i, p i ≤ q i) (hq1 : ∀ i, q i ≤ 1) (ω : ℕ) :
    poissonBinomialCdf q ω ≤ poissonBinomialCdf p ω := by
  have key : ∀ s : Finset ι,
      poissonBinomialCdf (fun i => if i ∈ s then q i else p i) ω ≤ poissonBinomialCdf p ω := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      have hr : (fun i => if i ∈ insert a s then q i else p i) =
          Function.update (fun i => if i ∈ s then q i else p i) a (q a) := by
        funext i
        by_cases hi : i = a
        · subst hi; simp
        · simp [hi]
      rw [hr]
      refine (poissonBinomialCdf_update_le (fun i => ?_) (fun i => ?_) a ?_ ω).trans ih
      · split_ifs <;> linarith [h0 i, hpq i]
      · split_ifs <;> linarith [hq1 i, hpq i]
      · simp [ha, hpq a]
  simpa using key univ

/-- **The bucket-uniform hint fraction bound** `max(|b| - β, 0) / (2(γ₂ - β) - 1)`: at least the
hint fraction `hintProb(r, b)` of every bucket `r` (`hintProb_le_hintFractionBound`). -/
noncomputable def hintFractionBound (γ₂ β : ℕ) (b : ℤ) : ℝ :=
  ((|b| - β).toNat : ℝ) / ((2 * (γ₂ - β) - 1 : ℕ) : ℝ)

/-- `hintProb(r, b) ≤ hintFractionBound(b)` in every bucket `r` (`hintProb_le`). -/
theorem hintProb_le_hintFractionBound (γ₂ β r1 : ℕ) (b : ℤ) :
    hintProb γ₂ β r1 b ≤ hintFractionBound γ₂ β b :=
  hintProb_le γ₂ β r1 b

/-- The hint fraction bound is nonnegative. -/
theorem hintFractionBound_nonneg (γ₂ β : ℕ) (b : ℤ) : 0 ≤ hintFractionBound γ₂ β b := by
  unfold hintFractionBound
  positivity

/-- The hint fraction bound is at most `1` for `|b| < γ₂`. -/
theorem hintFractionBound_le_one {γ₂ β : ℕ} (hβ : β < γ₂) {b : ℤ} (hb : |b| < γ₂) :
    hintFractionBound γ₂ β b ≤ 1 := by
  unfold hintFractionBound
  refine div_le_one_of_le₀ ?_ (Nat.cast_nonneg _)
  have h : (|b| - β).toNat ≤ 2 * (γ₂ - β) - 1 := by
    rw [Int.toNat_le]
    omega
  exact_mod_cast h

/-- `hintFractionBound(b) ≤ |b| / (2(γ₂ - β) - 1)`. -/
theorem hintFractionBound_le_abs (γ₂ β : ℕ) (b : ℤ) :
    hintFractionBound γ₂ β b ≤ (|b| : ℝ) / ((2 * (γ₂ - β) - 1 : ℕ) : ℝ) := by
  unfold hintFractionBound
  gcongr
  have h : ((|b| - β).toNat : ℤ) ≤ |b| := by
    rw [Int.toNat_eq_max]
    exact max_le (by omega) (abs_nonneg b)
  have h' : ((((|b| - β).toNat : ℤ)) : ℝ) ≤ ((|b| : ℤ) : ℝ) := Int.cast_le.2 h
  simpa using h'

/-- **The bucket-free acceptance weight**: the ct₀ indicator `‖b‖∞ < γ₂` times the
Poisson-binomial CDF at `ω` of the hint fraction bounds `hintFractionBound(b_i)`. It does not
depend on the bucket vector and is at most the acceptance weight in every bucket vector
(`acceptWeightLower_le_acceptWeight`). -/
noncomputable def acceptWeightLower {ι : Type*} [Fintype ι] [DecidableEq ι] (γ₂ β ω : ℕ)
    (b : ι → ℤ) : ℝ :=
  (if ∀ i, |b i| < γ₂ then 1 else 0) *
    poissonBinomialCdf (fun i => hintFractionBound γ₂ β (b i)) ω

/-- **The bucket-free acceptance weight is at most the acceptance weight in every bucket vector**
(`poissonBinomialCdf_anti` with `hintProb ≤ hintFractionBound ≤ 1`). -/
theorem acceptWeightLower_le_acceptWeight {ι : Type*} [Fintype ι] [DecidableEq ι] {γ₂ β : ℕ}
    (hβ : β < γ₂) (ω : ℕ) (b : ι → ℤ) (v : ι → ℕ) :
    acceptWeightLower γ₂ β ω b ≤ acceptWeight γ₂ β ω b v := by
  unfold acceptWeightLower acceptWeight
  split_ifs with hb
  · rw [one_mul, one_mul]
    exact poissonBinomialCdf_anti (fun i => hintProb_nonneg _ _ _ _)
      (fun i => hintProb_le_hintFractionBound _ _ _ _)
      (fun i => hintFractionBound_le_one hβ (hb i)) ω
  · simp

-- Irreducible so that unification does not evaluate the rational arithmetic.
/-- `hintFractionBound` in `ℚ`. -/
@[irreducible] def hintFractionBoundQ (γ₂ β : ℕ) (b : ℤ) : ℚ :=
  ((|b| - β).toNat : ℚ) / ((2 * (γ₂ - β) - 1 : ℕ) : ℚ)

@[simp, norm_cast] theorem cast_hintFractionBoundQ (γ₂ β : ℕ) (b : ℤ) :
    (hintFractionBoundQ γ₂ β b : ℝ) = hintFractionBound γ₂ β b := by
  simp [hintFractionBoundQ, hintFractionBound]

-- Irreducible so that unification does not evaluate the rational arithmetic.
/-- `acceptWeightLower` in `ℚ`. -/
@[irreducible] def acceptWeightLowerQ {ι : Type*} [Fintype ι] [DecidableEq ι] (γ₂ β ω : ℕ)
    (b : ι → ℤ) : ℚ :=
  (if ∀ i, |b i| < γ₂ then 1 else 0) *
    poissonBinomialCdfQ (fun i => hintFractionBoundQ γ₂ β (b i)) ω

@[simp, norm_cast] theorem cast_acceptWeightLowerQ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ₂ β ω : ℕ) (b : ι → ℤ) :
    (acceptWeightLowerQ γ₂ β ω b : ℝ) = acceptWeightLower γ₂ β ω b := by
  rw [acceptWeightLowerQ, acceptWeightLower, Rat.cast_mul, cast_poissonBinomialCdfQ]
  simp only [cast_hintFractionBoundQ]
  split_ifs <;> simp

/-! ### The binomial CDF and the vertices of the Poisson-binomial CDF -/

/-- **The binomial CDF** `Pr[Bin(N, x) ≤ ω] = ∑_{j ≤ ω} C(N, j) x^j (1 - x)^(N - j)` (the
binomial distribution, W. Feller, *An Introduction to Probability Theory and Its Applications*,
Vol. I, 3rd ed. (1968), Ch. VI, §2, eq. (2.1)): the Poisson-binomial CDF with every success
probability `x` (`poissonBinomialCdf_indicator_eq`). -/
noncomputable def binomialCdf (x : ℝ) (N ω : ℕ) : ℝ :=
  ∑ j ∈ range (ω + 1), (N.choose j : ℝ) * x ^ j * (1 - x) ^ (N - j)

/-- The binomial probabilities sum to `1`. -/
theorem sum_range_choose_mul_pow_mul_pow (x : ℝ) (N : ℕ) :
    ∑ j ∈ range (N + 1), (N.choose j : ℝ) * x ^ j * (1 - x) ^ (N - j) = 1 := by
  have h := (add_pow x (1 - x) N).symm
  rw [add_sub_cancel, one_pow] at h
  exact (sum_congr rfl fun j _ => by ring).trans h

/-- The binomial CDF at `ω` plus the upper tail `∑_{ω < j ≤ N}` is `1`, for `ω ≤ N`. -/
theorem binomialCdf_add_tail (x : ℝ) {N ω : ℕ} (h : ω ≤ N) :
    binomialCdf x N ω +
      ∑ j ∈ Ico (ω + 1) (N + 1), (N.choose j : ℝ) * x ^ j * (1 - x) ^ (N - j) = 1 := by
  rw [binomialCdf, sum_range_add_sum_Ico _ (by omega), sum_range_choose_mul_pow_mul_pow]

/-- The binomial CDF at `ω = N` is `1`. -/
theorem binomialCdf_self (x : ℝ) (N : ℕ) : binomialCdf x N N = 1 :=
  sum_range_choose_mul_pow_mul_pow x N

/-- The binomial CDF is nonnegative. -/
theorem binomialCdf_nonneg {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (N ω : ℕ) :
    0 ≤ binomialCdf x N ω := by
  have : 0 ≤ 1 - x := by linarith
  exact sum_nonneg fun j _ => by positivity

/-- One term of the binomial CDF: `C(N, j) x^j (1 - x)^(N - j) ≤ Pr[Bin(N, x) ≤ ω]` for
`j ≤ ω`. -/
theorem choose_mul_pow_mul_pow_le_binomialCdf {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) {j ω : ℕ}
    (hj : j ≤ ω) (N : ℕ) : (N.choose j : ℝ) * x ^ j * (1 - x) ^ (N - j) ≤ binomialCdf x N ω := by
  have : 0 ≤ 1 - x := by linarith
  exact single_le_sum (f := fun j => (N.choose j : ℝ) * x ^ j * (1 - x) ^ (N - j))
    (fun j _ => by positivity) (mem_range.2 (by omega))

/-- **The Poisson-binomial CDF is affine in each success probability**:
`Pr_{p[a ↦ x]}[X ≤ ω] = (1 - x) Pr_{p[a ↦ 0]}[X ≤ ω] + x Pr_{p[a ↦ 1]}[X ≤ ω]`
(`poissonBinomialCdf_update_eq`). -/
theorem poissonBinomialCdf_update_eq_add {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ)
    (a : ι) (x : ℝ) (ω : ℕ) :
    poissonBinomialCdf (Function.update p a x) ω =
      (1 - x) * poissonBinomialCdf (Function.update p a 0) ω +
        x * poissonBinomialCdf (Function.update p a 1) ω := by
  rw [poissonBinomialCdf_update_eq, poissonBinomialCdf_update_eq, poissonBinomialCdf_update_eq,
    mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun t _ => by ring

/-- **The Poisson-binomial CDF at a vertex is binomial**: with success probability `x` on `T`
and `0` off `T`, `Pr[X ≤ ω] = Pr[Bin(|T|, x) ≤ ω]`. -/
theorem poissonBinomialCdf_indicator_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Finset ι)
    (x : ℝ) (ω : ℕ) :
    poissonBinomialCdf (fun i => if i ∈ T then x else 0) ω = binomialCdf x T.card ω := by
  set g : ℕ → ℝ := fun m => (T.card.choose m : ℝ) * (if m ≤ ω then x ^ m * (1 - x) ^ (T.card - m)
    else 0) with hg
  have hprod : ∀ S : Finset ι, (∏ i, if i ∈ S then (if i ∈ T then x else 0)
      else 1 - (if i ∈ T then x else 0)) =
      if S ⊆ T then x ^ S.card * (1 - x) ^ (T.card - S.card) else 0 := by
    intro S
    split_ifs with hS
    · have hsplit : ∀ i, (if i ∈ S then (if i ∈ T then x else 0)
          else 1 - (if i ∈ T then x else 0)) =
          (if i ∈ S then x else 1) * (if i ∈ T \ S then 1 - x else 1) := fun i => by
        by_cases hiS : i ∈ S
        · simp [hiS, hS hiS]
        · by_cases hiT : i ∈ T <;> simp [hiS, hiT]
      rw [Fintype.prod_congr _ _ hsplit, prod_mul_distrib, prod_ite_mem, prod_ite_mem,
        univ_inter, univ_inter, prod_const, prod_const, card_sdiff_of_subset hS]
    · obtain ⟨i, hiS, hiT⟩ := not_subset.1 hS
      exact prod_eq_zero (mem_univ i) (by simp [hiS, hiT])
  rw [poissonBinomialCdf, sum_filter]
  simp_rw [hprod]
  calc ∑ S : Finset ι, (if S.card ≤ ω then
        (if S ⊆ T then x ^ S.card * (1 - x) ^ (T.card - S.card) else 0) else 0)
      = ∑ S ∈ T.powerset, (if S.card ≤ ω then x ^ S.card * (1 - x) ^ (T.card - S.card)
          else 0) := by
        rw [← sum_subset (subset_univ T.powerset)]
        · exact sum_congr rfl fun S hS => by simp [mem_powerset.1 hS]
        · intro S _ hS
          have hST : ¬ S ⊆ T := fun h => hS (mem_powerset.2 h)
          simp [hST]
    _ = ∑ m ∈ range (T.card + 1), g m := by
        rw [sum_powerset_apply_card (f := fun m => if m ≤ ω then x ^ m * (1 - x) ^ (T.card - m)
          else 0)]
        exact sum_congr rfl fun m _ => by rw [nsmul_eq_mul]
    _ = ∑ m ∈ range (T.card + ω + 1), g m := by
        refine sum_subset (range_subset_range.2 (by omega)) fun m _ hm => ?_
        rw [mem_range, not_lt] at hm
        simp [hg, Nat.choose_eq_zero_of_lt (by omega : T.card < m)]
    _ = ∑ m ∈ range (ω + 1), g m := by
        refine (sum_subset (range_subset_range.2 (by omega)) fun m _ hm => ?_).symm
        rw [mem_range, not_lt] at hm
        simp [hg, show ¬ m ≤ ω by omega]
    _ = binomialCdf x T.card ω := sum_congr rfl fun m hm => by
        simp only [hg, Nat.lt_succ_iff.1 (mem_range.1 hm), ite_true, mul_assoc]

/-- **The binomial CDF is antitone in the number of trials**:
`Pr[Bin(N + 1, x) ≤ ω] ≤ Pr[Bin(N, x) ≤ ω]` (`poissonBinomialCdf_anti` at the vertices of
`poissonBinomialCdf_indicator_eq`). -/
theorem binomialCdf_succ_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (N ω : ℕ) :
    binomialCdf x (N + 1) ω ≤ binomialCdf x N ω := by
  have hT : (univ.erase (Fin.last N)).card = N := by simp
  have hU : (univ : Finset (Fin (N + 1))).card = N + 1 := by simp
  have e1 := poissonBinomialCdf_indicator_eq (univ.erase (Fin.last N)) x ω
  have e2 := poissonBinomialCdf_indicator_eq (univ : Finset (Fin (N + 1))) x ω
  rw [hT] at e1
  rw [hU] at e2
  rw [← e1, ← e2]
  refine poissonBinomialCdf_anti (fun i => ?_) (fun i => ?_) (fun i => ?_) ω
  · split_ifs <;> simp [h0]
  · split_ifs <;> simp_all
  · simp [h1]

/-- The binomial CDF is antitone in the number of trials. -/
theorem binomialCdf_anti {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (ω : ℕ) :
    Antitone fun N => binomialCdf x N ω :=
  antitone_nat_of_succ_le fun N => binomialCdf_succ_le h0 h1 N ω

/-- **The vertex reduction for the Poisson-binomial CDF.** For success probabilities
`p_i ∈ [0, x₀]` and a line `α - σ N x₀` below the binomial CDF
`Pr[Bin(N, x₀) ≤ ω]` at every `N ≤ |ι|`: `α - σ ∑_i p_i ≤ Pr_p[X ≤ ω]`. The CDF plus
`σ ∑_i p_i` is affine in each `p_a` (`poissonBinomialCdf_update_eq_add`), so its minimum over the
box `[0, x₀]^ι` is at a vertex `x₀ 1_T`, where it is `Pr[Bin(|T|, x₀) ≤ ω] + σ |T| x₀`
(`poissonBinomialCdf_indicator_eq`). -/
theorem sub_sum_le_poissonBinomialCdf {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → ℝ}
    {x₀ α σ : ℝ} (hp0 : ∀ i, 0 ≤ p i) (hpx : ∀ i, p i ≤ x₀) {ω : ℕ}
    (hline : ∀ N ≤ Fintype.card ι, α - σ * N * x₀ ≤ binomialCdf x₀ N ω) :
    α - σ * ∑ i, p i ≤ poissonBinomialCdf p ω := by
  set F : (ι → ℝ) → ℝ := fun q => poissonBinomialCdf q ω + σ * ∑ i, q i with hF
  have key : ∀ s : Finset ι, ∃ q : ι → ℝ, (∀ i, 0 ≤ q i ∧ q i ≤ x₀) ∧
      (∀ i ∈ s, q i = 0 ∨ q i = x₀) ∧ F q ≤ F p := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨p, fun i => ⟨hp0 i, hpx i⟩, by simp, le_rfl⟩
    | insert a s ha ih =>
      obtain ⟨q, hq, hqs, hqF⟩ := ih
      have hx0 : 0 ≤ x₀ := (hq a).1.trans (hq a).2
      have hsum : ∀ y, ∑ i, Function.update q a y i = y + ∑ i ∈ univ \ {a}, q i := fun y =>
        sum_update_of_mem (mem_univ a) _ _
      set A := poissonBinomialCdf (Function.update q a 0) ω + σ * ∑ i ∈ univ \ {a}, q i
      set D := poissonBinomialCdf (Function.update q a 1) ω -
        poissonBinomialCdf (Function.update q a 0) ω + σ
      have hlin : ∀ y, F (Function.update q a y) = A + y * D := fun y => by
        simp only [hF, hsum, A, D]
        rw [poissonBinomialCdf_update_eq_add]
        ring
      have hFq : F q = A + q a * D := by rw [← hlin, Function.update_eq_self]
      have hbox : ∀ y, 0 ≤ y → y ≤ x₀ → ∀ i, 0 ≤ Function.update q a y i ∧
          Function.update q a y i ≤ x₀ := fun y hy0 hy1 i => by
        by_cases hi : i = a
        · subst hi; simp [hy0, hy1]
        · simp [Function.update_of_ne hi, hq i]
      have hvert : ∀ y, (y = 0 ∨ y = x₀) → ∀ i ∈ insert a s,
          Function.update q a y i = 0 ∨ Function.update q a y i = x₀ := fun y hy i hi => by
        by_cases hia : i = a
        · subst hia; simpa using hy
        · rw [Function.update_of_ne hia]
          exact hqs i ((mem_insert.1 hi).resolve_left hia)
      rcases le_or_gt 0 D with hD | hD
      · refine ⟨Function.update q a 0, hbox 0 le_rfl hx0, hvert 0 (Or.inl rfl), ?_⟩
        refine le_trans ?_ hqF
        rw [hlin, hFq]
        nlinarith [(hq a).1]
      · refine ⟨Function.update q a x₀, hbox x₀ hx0 le_rfl, hvert x₀ (Or.inr rfl), ?_⟩
        refine le_trans ?_ hqF
        rw [hlin, hFq]
        nlinarith [(hq a).2]
  obtain ⟨q, -, hqv, hqF⟩ := key univ
  set T := univ.filter fun i => q i = x₀
  have hqT : q = fun i => if i ∈ T then x₀ else 0 := funext fun i => by
    by_cases h : q i = x₀
    · simp [T, h]
    · simp only [T, mem_filter, mem_univ, true_and, h, ite_false]
      exact (hqv i (mem_univ i)).resolve_right h
  have hFq : F q = binomialCdf x₀ T.card ω + σ * (T.card * x₀) := by
    simp only [hF]
    rw [hqT, poissonBinomialCdf_indicator_eq, sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
  have hT := hline T.card (card_le_univ T)
  simp only [hF] at hqF
  rw [hF] at hFq
  nlinarith

/-- **A line below the binomial CDF from finitely many checks.** For `x₀ ∈ [0, 1]`, `σ ≥ 0`,
`α ≤ Pr[Bin(N_a, x₀) ≤ ω]`, the line `α - σ N x₀` below the CDF at every `N_a < N < N_z`, and
`α - σ N_z x₀ ≤ 0`: the line is below `Pr[Bin(N, x₀) ≤ ω]` at every `N`. Below `N_a` by
`binomialCdf_anti`, above `N_z` by `binomialCdf_nonneg`. -/
theorem sub_le_binomialCdf_of_checks {x₀ α σ : ℝ} (hx0 : 0 ≤ x₀) (hx1 : x₀ ≤ 1) (hσ : 0 ≤ σ)
    {ω Na Nz : ℕ} (ha : α ≤ binomialCdf x₀ Na ω)
    (hmid : ∀ N, Na < N → N < Nz → α - σ * N * x₀ ≤ binomialCdf x₀ N ω)
    (hz : α - σ * Nz * x₀ ≤ 0) (N : ℕ) : α - σ * N * x₀ ≤ binomialCdf x₀ N ω := by
  rcases le_or_gt N Na with h | h
  · have : 0 ≤ σ * N * x₀ := by positivity
    linarith [binomialCdf_anti hx0 hx1 ω h]
  rcases lt_or_ge N Nz with h' | h'
  · exact hmid N h h'
  · have : σ * Nz * x₀ ≤ σ * N * x₀ := by gcongr
    linarith [binomialCdf_nonneg hx0 hx1 N ω]

/-! ### Bucket vectors -/

/-- The number `(q - 1)/(2γ₂)` of `HighBits` buckets (FIPS 204 Algorithm 37). -/
def bucketCount (p : Params) : ℕ := (modulus - 1) / (2 * p.gamma2)

/-- There is at least one bucket. -/
theorem SigningParams.bucketCount_pos {p : Params} (hp : SigningParams p) : 0 < bucketCount p :=
  Nat.div_pos (by have := hp.two_buckets; omega) (by have := hp.gamma2_pos; omega)

/-- The coefficients of `R_q^k`, indexed by `(component, coefficient)`. -/
abbrev CoeffIndex (p : Params) := Fin p.k × Fin ringDegree

/-- A vector of `HighBits` buckets, one per coefficient of `w ∈ R_q^k`: the commitment `w₁`. A
named type with one-step instances, so instance search and type comparisons stop at it. -/
def BucketVec (p : Params) : Type := CoeffIndex p → Fin (bucketCount p)

instance instFintypeBucketVec (p : Params) : Fintype (BucketVec p) :=
  inferInstanceAs (Fintype (CoeffIndex p → Fin (bucketCount p)))

instance instDecidableEqBucketVec (p : Params) : DecidableEq (BucketVec p) :=
  inferInstanceAs (DecidableEq (CoeffIndex p → Fin (bucketCount p)))

instance instNonemptyBucketVec (p : Params) [NeZero (bucketCount p)] : Nonempty (BucketVec p) :=
  inferInstanceAs (Nonempty (CoeffIndex p → Fin (bucketCount p)))

instance instInhabitedBucketVec (p : Params) [NeZero (bucketCount p)] : Inhabited (BucketVec p) :=
  inferInstanceAs (Inhabited (CoeffIndex p → Fin (bucketCount p)))

/-- The number of bucket vectors: `bucketCount` to the number of coefficients. -/
theorem card_bucketVec_coeffIndex (p : Params) :
    Fintype.card (BucketVec p) = bucketCount p ^ Fintype.card (CoeffIndex p) := by
  change Fintype.card (CoeffIndex p → Fin (bucketCount p)) = _
  rw [Fintype.card_fun, Fintype.card_fin]

/-- The number of bucket vectors: `bucketCount ^ (k · 256)`. -/
theorem card_bucketVec (p : Params) :
    Fintype.card (BucketVec p) = bucketCount p ^ (p.k * ringDegree) := by
  change Fintype.card (CoeffIndex p → Fin (bucketCount p)) = _
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- Every `HighBits` value is a bucket. -/
theorem highBitsCoeff_lt_bucketCount {p : Params} (hp : SigningParams p) (x : Coeff) :
    highBitsCoeff x p.gamma2 < bucketCount p := by
  unfold highBitsCoeff bucketCount
  exact (decomposeCoeff_repr hp.gamma2_pos hp.gamma2_dvd x).high_lt

variable {p : Params} [NeZero (bucketCount p)]

/-- The bucket vector `HighBits(w)` of a coefficient vector (FIPS 204 Algorithm 37,
coefficientwise). -/
def bucketsOf (w : CoeffIndex p → Coeff) : BucketVec p :=
  fun x => Fin.ofNat (bucketCount p) (highBitsCoeff (w x) p.gamma2)

theorem val_bucketsOf (hp : SigningParams p) (w : CoeffIndex p → Coeff) (x : CoeffIndex p) :
    (bucketsOf w x).val = highBitsCoeff (w x) p.gamma2 := by
  rw [bucketsOf, Fin.val_ofNat, Nat.mod_eq_of_lt (highBitsCoeff_lt_bucketCount hp _)]

/-! ### The signer's attempt, the stand-in, and the flattening weight -/

section Signer

variable (prims : Primitives p) [nttOps : NTTRingOps] [Nonempty (MaskBox p)]

/-- The centered coefficients of `w ∈ R_q^k`, indexed by `(component, coefficient)`. -/
def centeredCoeffs {k : ℕ} (w : RqVec k) : Fin k × Fin ringDegree → ℤ :=
  fun x => LatticeCrypto.centeredRepr (rqVecCoeffs w x)

/-- **The excluded commitment hashes of `t₀`**: the `c̃` failing the ct₀-check of FIPS 204
Algorithm 7 line 28, `‖SampleInBall(c̃) · t₀‖∞ ≥ γ₂`. Empty for honest `t₀` at ML-DSA-65 and
ML-DSA-87 (`ct0_check_passes`). -/
def exclSet (t0 : RqVec p.k) : Finset (CommitHashBytes p) :=
  univ.filter fun cTilde => p.gamma2 ≤ polyVecNorm (prims.sampleInBall cTilde • t0)

variable (sk : SecretKey p) (aHat : TqMatrix p.k p.l)

/-- The shift `b = c·t₀` of the ct₀ and hint checks, coefficientwise and centered. -/
def ct0Shift (cTilde : CommitHashBytes p) : CoeffIndex p → ℤ :=
  centeredCoeffs (prims.sampleInBall cTilde • sk.t0)

/-- The shift `a = c·s₂` of the r0-check, coefficientwise and centered. -/
def cs2Shift (cTilde : CommitHashBytes p) : CoeffIndex p → ℤ :=
  centeredCoeffs (prims.sampleInBall cTilde • sk.s2)

/-- **The flattening weight** of a commitment `w₁ = v` and hash `c̃`: the acceptance weight of the
ct₀ and hint checks for a uniform `w` (`acceptWeight`, `card_acceptSet`), with `b = c·t₀`. It
depends on the signer only through `t₀`. -/
def signerWeight (vc : BucketVec p × CommitHashBytes p) : ℚ≥0 :=
  (acceptWeightQ p.gamma2 p.beta p.omega (ct0Shift prims sk vc.2) fun x => (vc.1 x).val).toNNRat

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- The flattening weight in `ℝ≥0∞` is the real acceptance weight. -/
theorem coe_signerWeight (vc : BucketVec p × CommitHashBytes p) :
    (signerWeight prims sk vc : ℝ≥0∞) =
      ENNReal.ofReal (acceptWeight p.gamma2 p.beta p.omega (ct0Shift prims sk vc.2)
        fun x => (vc.1 x).val) := by
  rw [signerWeight, ← ENNReal.ofReal_ratCast, cast_acceptWeightQ]

/-- **The flattening coin**: keep `(v, c̃)` with probability `min 1 (val c̃ / signerWeight)` for
the cut-off `val` (`NNRat.minOneDiv`, the value of `ℝ≥0∞` at a zero weight). -/
def flattenCoin (cut : Cutoff p) (vc : BucketVec p × CommitHashBytes p) : ℚ≥0 :=
  NNRat.minOneDiv (cut.val vc.2) (signerWeight prims sk vc)

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
theorem flattenCoin_le_one (cut : Cutoff p) (vc : BucketVec p × CommitHashBytes p) :
    flattenCoin prims sk cut vc ≤ 1 :=
  NNRat.minOneDiv_le_one _ _

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- The flattening coin in `ℝ≥0∞` is `min 1 (val c̃ / signerWeight)`; at a constant cut-off it is
`flattenKeep` of the flattening weight. -/
theorem coe_flattenCoin (cut : Cutoff p) (vc : BucketVec p × CommitHashBytes p) :
    (flattenCoin prims sk cut vc : ℝ≥0∞) =
      min 1 ((cut.val vc.2 : ℝ≥0∞) / (signerWeight prims sk vc : ℝ≥0∞)) := by
  rw [flattenCoin, ENNReal.nnratCast_minOneDiv]

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- The flattening coin in `ℝ≥0∞` is a probability. -/
theorem coe_flattenCoin_le_one (cut : Cutoff p) (vc : BucketVec p × CommitHashBytes p) :
    (flattenCoin prims sk cut vc : ℝ≥0∞) ≤ 1 :=
  ENNReal.nnratCast_le_one.2 (flattenCoin_le_one prims sk cut vc)

include nttOps in
/-- The commitment `w₁ = HighBits(Â·y)` of a mask, as a bucket vector. -/
def realBuckets (y : MaskBox p) : BucketVec p :=
  bucketsOf (rqVecCoeffs (aHat * y.1))

/-- **The stand-in acceptance** of a uniform `w`: the r0, ct₀ and hint checks of FIPS 204
Algorithm 7 (lines 21–28) on the coefficients of `w`, with `a = c·s₂` and `b = c·t₀`
(`acceptSet`). It has no z-check. -/
def standinAccept (w : CoeffIndex p → Coeff) (cTilde : CommitHashBytes p) : Bool :=
  decide (w ∈ acceptSet p.gamma2 p.beta p.omega (cs2Shift prims sk cTilde)
    (ct0Shift prims sk cTilde) fun x => (bucketsOf w x).val)

/-- **The real flattened accepted law** of `(w₁, c̃)`: one idealized attempt (`y` uniform on the
mask box, `c̃` a fresh uniform hash, the four checks of `signAccept`) followed by the flattening
coin, conditioned on keeping. -/
noncomputable def realKeptLaw (cut : Cutoff p) : PMF (BucketVec p × CommitHashBytes p) :=
  condSomeOr (freshAttempt (maskUniform p) (realBuckets aHat) (attemptAccept prims sk aHat)
    (fun a => (flattenCoin prims sk cut a : ℝ≥0∞)) (coe_flattenCoin_le_one prims sk cut))
    (uniformOfFintype _)

/-- **The stand-in flattened accepted law** of `(w₁, c̃)`: `w` uniform on the coefficient vectors,
`c̃` uniform, the stand-in checks, the flattening coin, conditioned on keeping. -/
noncomputable def standinKeptLaw (cut : Cutoff p) : PMF (BucketVec p × CommitHashBytes p) :=
  condSomeOr (freshAttempt (uniformOfFintype (CoeffIndex p → Coeff)) bucketsOf
    (standinAccept prims sk) (fun a => (flattenCoin prims sk cut a : ℝ≥0∞))
    (coe_flattenCoin_le_one prims sk cut)) (uniformOfFintype _)

/-- **The regularity term**: the distance between the real and the stand-in flattened accepted
laws of `(w₁, c̃)`, for the signer's key. It measures how far `w = Â·y` for `y` uniform on the mask
box, jointly with the z-check, is from a uniform `w`. -/
noncomputable def regError (cut : Cutoff p) : ℝ :=
  tvDist (realKeptLaw prims sk aHat cut) (standinKeptLaw prims sk cut)

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- The ct₀-check passes on every coefficient exactly when `c̃` is not excluded. -/
theorem forall_abs_ct0Shift_lt_iff (hp : SigningParams p) (cTilde : CommitHashBytes p) :
    (∀ x, |ct0Shift prims sk cTilde x| < p.gamma2) ↔ cTilde ∉ exclSet prims sk.t0 := by
  simp only [exclSet, mem_filter, mem_univ, true_and, not_le]
  rw [polyVecNorm_lt_iff _ hp.gamma2_pos]
  constructor
  · intro h j i
    have := h (j, i)
    rw [ct0Shift, centeredCoeffs, rqVecCoeffs_apply, Int.abs_eq_natAbs] at this
    exact_mod_cast this
  · intro h x
    rw [ct0Shift, centeredCoeffs, rqVecCoeffs_apply, Int.abs_eq_natAbs]
    exact_mod_cast h x.1 x.2

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- The r0-check shift is in the `β`-box, from the primitive laws and `‖s₂‖∞ ≤ η`. -/
theorem SigningLaws.abs_cs2Shift_le (h_laws : SigningLaws prims)
    (hs2 : polyVecBounded sk.s2 p.eta) (cTilde : CommitHashBytes p) (x : CoeffIndex p) :
    |cs2Shift prims sk cTilde x| ≤ p.beta := by
  have h := polyVecNorm_sampleInBall_smul_le prims h_laws cTilde sk.s2 hs2
  have h' : polyVecNorm (prims.sampleInBall cTilde • sk.s2) < p.beta + 1 := by omega
  rw [polyVecNorm_lt_iff _ (Nat.succ_pos _)] at h'
  have := h' x.1 x.2
  rw [cs2Shift, centeredCoeffs, rqVecCoeffs_apply, Int.abs_eq_natAbs]
  exact_mod_cast Nat.lt_succ_iff.1 this

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- `SigningLaws.abs_cs2Shift_le` from the full primitive laws. -/
theorem abs_cs2Shift_le (h_laws : Primitives.Laws prims nttOps)
    (hs2 : polyVecBounded sk.s2 p.eta) (cTilde : CommitHashBytes p) (x : CoeffIndex p) :
    |cs2Shift prims sk cTilde x| ≤ p.beta :=
  SigningLaws.abs_cs2Shift_le prims sk h_laws.toSigningLaws hs2 cTilde x

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- The flattening weight is a probability. -/
theorem signerWeight_le_one (hp : SigningParams p) (vc : BucketVec p × CommitHashBytes p) :
    signerWeight prims sk vc ≤ 1 := by
  rw [← ENNReal.nnratCast_le_one, coe_signerWeight]
  exact ENNReal.ofReal_le_one.2 (acceptWeight_le_one hp.beta_lt_gamma2 _ _ _)

omit [Nonempty (MaskBox p)] in
/-- **The stand-in accepted mass is the acceptance weight**: for a uniform `w` and a fixed `c̃`,
`Pr_w[HighBits(w) = v ∧ the stand-in checks pass] = ((2(γ₂ - β) - 1)/q)^|ι| · signerWeight`
(`uniform_acceptSet`). -/
theorem SigningLaws.signerMass_standin (hp : SigningParams p) (h_laws : SigningLaws prims)
    (hs2 : polyVecBounded sk.s2 p.eta) (v : BucketVec p) (cTilde : CommitHashBytes p) :
    signerMass (uniformOfFintype (CoeffIndex p → Coeff)) bucketsOf (standinAccept prims sk) v
        cTilde =
      ENNReal.ofReal ((((2 * (p.gamma2 - p.beta) - 1 : ℕ) : ℝ) / modulus) ^
        Fintype.card (CoeffIndex p)) * signerWeight prims sk (v, cTilde) := by
  set S := acceptSet p.gamma2 p.beta p.omega (cs2Shift prims sk cTilde) (ct0Shift prims sk cTilde)
    fun x => (v x).val
  have hiff : ∀ w, (bucketsOf w = v ∧ standinAccept prims sk w cTilde = true) ↔ w ∈ S := by
    intro w
    constructor
    · rintro ⟨rfl, h⟩
      simpa [standinAccept] using h
    · intro h
      refine ⟨funext fun x => Fin.ext ?_, ?_⟩
      · rw [val_bucketsOf hp]
        exact ((mem_filter.1 h).2.1) x
      · have hb : bucketsOf w = v := funext fun x => Fin.ext (by
          rw [val_bucketsOf hp]; exact ((mem_filter.1 h).2.1) x)
        simp [standinAccept, hb, h, S]
  have hmass : signerMass (uniformOfFintype (CoeffIndex p → Coeff)) bucketsOf
      (standinAccept prims sk) v cTilde =
      (uniformOfFintype (CoeffIndex p → Coeff)).toOuterMeasure (S : Set _) := by
    rw [toOuterMeasure_apply_finset, signerMass, ← sum_filter]
    congr 1
    ext w
    simp only [mem_filter, mem_univ, true_and]
    exact hiff w
  rw [hmass, ← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
      (toOuterMeasure_apply_le_one _ _)),
    uniform_acceptSet hp.roundingParams p.omega (abs_cs2Shift_le prims sk h_laws hs2 cTilde)
      _ (fun x => (v x).isLt), coe_signerWeight,
    ENNReal.ofReal_mul (pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _)]

omit [Nonempty (MaskBox p)] in
/-- `SigningLaws.signerMass_standin` from the full primitive laws. -/
theorem signerMass_standin (hp : SigningParams p) (h_laws : Primitives.Laws prims nttOps)
    (hs2 : polyVecBounded sk.s2 p.eta) (v : BucketVec p) (cTilde : CommitHashBytes p) :
    signerMass (uniformOfFintype (CoeffIndex p → Coeff)) bucketsOf (standinAccept prims sk) v
        cTilde =
      ENNReal.ofReal ((((2 * (p.gamma2 - p.beta) - 1 : ℕ) : ℝ) / modulus) ^
        Fintype.card (CoeffIndex p)) * signerWeight prims sk (v, cTilde) :=
  SigningLaws.signerMass_standin prims sk hp h_laws.toSigningLaws hs2 v cTilde

end Signer

/-! ### The ring -/

section Ring

variable (prims : Primitives p) [nttOps : NTTRingOps] [Nonempty (MaskBox p)] {N : ℕ}

/-- **The excluded sets of a ring**: member `j` with a published `t₀` (`t0s j = some t₀`, FIPS 204
§6.1: `t₀` need not be secret) excludes `exclSet t₀`; a member without one excludes nothing.
Each published `t₀` must leave some hash unexcluded. -/
def ringExclSets (t0s : Fin N → Option (RqVec p.k))
    (hne : ∀ j t0, t0s j = some t0 → (exclSet prims t0)ᶜ.Nonempty) :
    ExclSets (Fin N) (CommitHashBytes p) where
  excl j := (t0s j).elim ∅ (exclSet prims)
  compl_nonempty j := by
    cases h : t0s j with
    | none => simp
    | some t0 => simpa using hne j t0 h

variable (sk : SecretKey p) (aHat : TqMatrix p.k p.l) (E : ExclSets (Fin N) (CommitHashBytes p))
  (i : Fin N)

/-- **The flattened ring prover** with signer `i`: a random oracle `H` on the ring's points
`(j, w₁)` (standing for `µ_j ‖ w1Encode(w₁)`, distinct for distinct `tr_j`), drawn once; then
attempts until one keeps: an idealized FIPS 204 attempt with challenge `H (i, w₁)`, rejected if
some other member `j` has `H (j, w₁)` in its excluded set, kept with the flattening coin. The
output is `H` with the kept `w₁`. -/
noncomputable def flatRingProver (cut : Cutoff p) :
    PMF ((Fin N × BucketVec p → CommitHashBytes p) × Option (BucketVec p)) :=
  ringProver E i (maskUniform p) (realBuckets aHat) (attemptAccept prims sk aHat)
    (fun a => (flattenCoin prims sk cut a : ℝ≥0∞)) (coe_flattenCoin_le_one prims sk cut)

/-- **The oracle concentration term** of the flattened ring prover with signer `i`:
`E_H[(q H / q̄ - 1)⁺]`, `q H` the keep probability of one attempt against the oracle `H`. -/
noncomputable def ringOracleError (cut : Cutoff p) : ℝ :=
  oracleConcError E i (maskUniform p) (realBuckets aHat) (attemptAccept prims sk aHat)
    (fun a => (flattenCoin prims sk cut a : ℝ≥0∞)) (coe_flattenCoin_le_one prims sk cut)

/-- **The flattening term** for signer `i`: `E_u[(val - w)⁺] / E_u[min(w, val)]` with `u` the
uniform law on bucket vectors and hashes off the signer's excluded set and `w` the flattening
weight (`FlattenHyp.tvDist_condSome_thin_le`). -/
noncomputable def flatError (cut : Cutoff p) : ℝ :=
  ((∑ a, signerTarget E i a * ((cut.val a.2 : ℝ≥0∞) - (signerWeight prims sk a : ℝ≥0∞))) /
    ∑ a, signerTarget E i a * min (signerWeight prims sk a : ℝ≥0∞) (cut.val a.2 : ℝ≥0∞)).toReal

/-- The signer's real fresh attempt keeps with positive probability. -/
def SignerKeeps (cut : Cutoff p) : Prop :=
  freshAttempt (maskUniform p) (realBuckets aHat) (attemptAccept prims sk aHat)
    (fun a => (flattenCoin prims sk cut a : ℝ≥0∞)) (coe_flattenCoin_le_one prims sk cut) none ≠ 1

/-- The largest probability of one commitment `w₁ = HighBits(Â·y)` for `y` uniform on the mask
box (the min-entropy of `w₁`). -/
noncomputable def w1MaxProb : ℝ :=
  univ.sup' univ_nonempty fun v => ((maskUniform p).map (realBuckets aHat) v).toReal

/-- The keep probability of one attempt of the flattened ring prover against a uniform oracle. -/
noncomputable def ringKeepProb (cut : Cutoff p) : ℝ :=
  (1 - jointAttempt (uniformOfFintype _) (ringAttempt E i (maskUniform p) (realBuckets aHat)
    (attemptAccept prims sk aHat) (fun a => (flattenCoin prims sk cut a : ℝ≥0∞))
    (coe_flattenCoin_le_one prims sk cut)) none).toReal

/-- **The oracle concentration term is at most `√(δ / q̄) / 2`**, with `δ` the largest probability
of one commitment `w₁` and `q̄` the keep probability of one attempt (`oracleConcError_le`). -/
theorem ringOracleError_le {cut : Cutoff p} (hkeep : SignerKeeps prims sk aHat cut) :
    ringOracleError prims sk aHat E i cut ≤
      √(w1MaxProb aHat / ringKeepProb prims sk aHat E i cut) / 2 :=
  oracleConcError_le E i _ _ _ _ _ (fun v => le_sup' (fun v => ((maskUniform p).map
    (realBuckets aHat) v).toReal) (mem_univ v))
    (jointAttempt_ringAttempt_ne_one E i _ _ _ _ _ hkeep)

/-- **The flattened ring prover's law** (signer `i`): the joint law of the oracle and the kept
commitment is within the oracle concentration term, the regularity term and the flattening term of
the ring target (`w₁` uniform over bucket vectors; the oracle uniform, except that every member's
value at `w₁` is uniform off its excluded set). The target depends on the ring only, not on `i`.
Hypotheses: the signer's excluded set is that of its own `t₀`, and its attempt keeps with positive
probability. -/
theorem SigningLaws.tvDist_flatRingProver_le (hp : SigningParams p) (h_laws : SigningLaws prims)
    (hs2 : polyVecBounded sk.s2 p.eta) (hEi : E.excl i = exclSet prims sk.t0) {βmin : ℚ≥0}
    (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1) (hkeep : SignerKeeps prims sk aHat
        (Cutoff.const βmin)) :
    tvDist (flatRingProver prims sk aHat E i (Cutoff.const βmin)) (ringTarget (BucketVec p) E) ≤
      ringOracleError prims sk aHat E i (Cutoff.const βmin) + regError prims sk aHat
          (Cutoff.const βmin) +
        flatError prims sk E i (Cutoff.const βmin) := by
  refine (tvDist_ringProver_ringTarget_le E i _ _ _ _ _ hkeep).trans ?_
  rw [add_assoc]
  refine add_le_add le_rfl ?_
  have hreal : condSome _ hkeep = realKeptLaw prims sk aHat (Cutoff.const βmin) :=
    (condSomeOr_of_ne _ hkeep).symm
  rw [hreal]
  refine (tvDist_triangle _ (standinKeptLaw prims sk (Cutoff.const βmin)) _).trans (add_le_add
      le_rfl ?_)
  -- the stand-in is proportional to `u · w`
  set u := signerTarget (V := BucketVec p) E i
  set w : BucketVec p × CommitHashBytes p → ℝ≥0∞ := fun a => (signerWeight prims sk a : ℝ≥0∞)
  set K : ℝ := (((2 * (p.gamma2 - p.beta) - 1 : ℕ) : ℝ) / modulus) ^ Fintype.card (CoeffIndex p)
  set m : ℕ := (E.excl i)ᶜ.card
  have hK : 0 < K := by
    have h1 : 0 < 2 * (p.gamma2 - p.beta) - 1 := by have := hp.beta_lt_gamma2; omega
    exact pow_pos (div_pos (by exact_mod_cast h1) (by norm_num [modulus])) _
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by
    simpa [m] using (E.compl_nonempty i).card_pos.ne'
  have hV0 : (Fintype.card (BucketVec p) : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hu : ∀ v c, u (v, c) =
      (Fintype.card (BucketVec p) : ℝ≥0∞)⁻¹ * (if c ∈ E.excl i then 0 else (m : ℝ≥0∞)⁻¹) :=
    fun v c => by
      rw [show u = signerTarget (V := BucketVec p) E i from rfl, signerTarget, bind_map_prodMk_apply,
        uniformOfFintype_apply]
      by_cases hc : c ∈ E.excl i
      · rw [if_pos hc, uniformOfFinset_apply_of_notMem _ (by simpa using hc)]
      · rw [if_neg hc, uniformOfFinset_apply_of_mem _ (by simpa using hc)]
  have hw0 : ∀ v c, c ∈ E.excl i → w (v, c) = 0 := fun v c hc => by
    have hn : ¬ ∀ x, |ct0Shift prims sk c x| < p.gamma2 := by
      rw [forall_abs_ct0Shift_lt_iff prims sk hp, not_not, ← hEi]; exact hc
    simp [w, coe_signerWeight, acceptWeight_eq_zero hn]
  set r : ℝ≥0∞ := ENNReal.ofReal K * (Fintype.card (CommitHashBytes p) : ℝ≥0∞)⁻¹ *
    (Fintype.card (BucketVec p) : ℝ≥0∞) * m
  have hr0 : r ≠ 0 := by
    simp only [r, ne_eq, mul_eq_zero, not_or]
    exact ⟨⟨⟨by simpa using hK, by simp⟩, hV0⟩, hm0⟩
  have hS : ∀ v c, signerMass (uniformOfFintype (CoeffIndex p → Coeff)) bucketsOf
      (standinAccept prims sk) v c * (Fintype.card (CommitHashBytes p) : ℝ≥0∞)⁻¹ =
      r * (u (v, c) * w (v, c)) := fun v c => by
    rw [signerMass_standin prims sk hp h_laws hs2, hu]
    by_cases hc : c ∈ E.excl i
    · have h0 : signerWeight prims sk (v, c) = 0 := by simpa [w] using hw0 v c hc
      simp [h0, hc]
    · rw [if_neg hc]
      calc ENNReal.ofReal K * w (v, c) * (Fintype.card (CommitHashBytes p) : ℝ≥0∞)⁻¹
          = ENNReal.ofReal K * (Fintype.card (CommitHashBytes p) : ℝ≥0∞)⁻¹ * w (v, c) *
              ((Fintype.card (BucketVec p) : ℝ≥0∞) * (Fintype.card (BucketVec p) : ℝ≥0∞)⁻¹) *
              ((m : ℝ≥0∞) * (m : ℝ≥0∞)⁻¹) := by
            rw [ENNReal.mul_inv_cancel hV0 (ENNReal.natCast_ne_top _),
              ENNReal.mul_inv_cancel hm0 (ENNReal.natCast_ne_top _)]
            ring
        _ = r * ((Fintype.card (BucketVec p) : ℝ≥0∞)⁻¹ * (m : ℝ≥0∞)⁻¹ * w (v, c)) := by
            simp only [r]; ring
  have hmass : ∑ a, u a * min (w a) (βmin : ℝ≥0∞) ≠ 0 := by
    obtain ⟨c₀, hc₀⟩ := E.compl_nonempty i
    have hc₀' : c₀ ∉ E.excl i := by simpa using hc₀
    let v₀ : BucketVec p := fun _ => 0
    intro h
    have h0 := (Finset.sum_eq_zero_iff.1 h) (v₀, c₀) (mem_univ _)
    have hpass : ∀ x, |ct0Shift prims sk c₀ x| < p.gamma2 := by
      rw [forall_abs_ct0Shift_lt_iff prims sk hp, ← hEi]; exact hc₀'
    have hwpos : w (v₀, c₀) ≠ 0 := by
      simp only [w, coe_signerWeight, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact acceptWeight_pos hp.beta_lt_gamma2 _ hpass _
    rw [hu, if_neg hc₀'] at h0
    simp only [mul_eq_zero, ENNReal.inv_eq_zero, ENNReal.natCast_ne_top, false_or] at h0
    rcases min_eq_iff.1 h0 with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hwpos h1
    · exact hβ0 h1
  have hκ : (fun a => (flattenCoin prims sk (Cutoff.const βmin) a : ℝ≥0∞)) =
      flattenKeep w βmin :=
    funext (coe_flattenCoin prims sk (Cutoff.const βmin))
  rw [standinKeptLaw]
  simp only [hκ]
  exact tvDist_condSomeOr_freshAttempt_flatten_le _ _ _ u
    (fun a => ENNReal.nnratCast_le_one.2 (signerWeight_le_one prims sk hp a)) hβ1
    hmass hr0 hS _

/-- `SigningLaws.tvDist_flatRingProver_le` from the full primitive laws. -/
theorem tvDist_flatRingProver_le (hp : SigningParams p) (h_laws : Primitives.Laws prims nttOps)
    (hs2 : polyVecBounded sk.s2 p.eta) (hEi : E.excl i = exclSet prims sk.t0) {βmin : ℚ≥0}
    (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1) (hkeep : SignerKeeps prims sk aHat
        (Cutoff.const βmin)) :
    tvDist (flatRingProver prims sk aHat E i (Cutoff.const βmin)) (ringTarget (BucketVec p) E) ≤
      ringOracleError prims sk aHat E i (Cutoff.const βmin) + regError prims sk aHat
          (Cutoff.const βmin) +
        flatError prims sk E i (Cutoff.const βmin) :=
  SigningLaws.tvDist_flatRingProver_le prims sk aHat E i hp h_laws.toSigningLaws
    hs2 hEi hβ0 hβ1 hkeep

/-- **A ring where every member publishes `t₀`** (the ML-DSA-44 setting, where the ct₀-check can
reject): member `j` excludes `exclSet (t0s j)`. Members other than the signer may be adversarial;
each `t0s j` must leave some hash unexcluded. -/
def publishedRing (t0s : Fin N → RqVec p.k) (hne : ∀ j, (exclSet prims (t0s j))ᶜ.Nonempty) :
    ExclSets (Fin N) (CommitHashBytes p) :=
  ringExclSets prims (fun j => some (t0s j)) fun j t0 h => by
    cases h; exact hne j

/-- **The flattened ring prover for a ring of published `t₀`** (ML-DSA-44): with signer `i`
whose published `t₀` is its own, the law is within the three error terms of the ring target,
which depends on the published `t₀` of all members and not on `i`. -/
theorem SigningLaws.tvDist_flatRingProver_published_le (hp : SigningParams p)
    (h_laws : SigningLaws prims) (hs2 : polyVecBounded sk.s2 p.eta)
    (t0s : Fin N → RqVec p.k) (hne : ∀ j, (exclSet prims (t0s j))ᶜ.Nonempty)
    (hi : t0s i = sk.t0) {βmin : ℚ≥0} (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hkeep : SignerKeeps prims sk aHat (Cutoff.const βmin)) :
    tvDist (flatRingProver prims sk aHat (publishedRing prims t0s hne) i (Cutoff.const βmin))
        (ringTarget (BucketVec p) (publishedRing prims t0s hne)) ≤
      ringOracleError prims sk aHat (publishedRing prims t0s hne) i (Cutoff.const βmin) +
        regError prims sk aHat (Cutoff.const βmin) + flatError prims sk (publishedRing prims t0s
            hne) i (Cutoff.const βmin) :=
  tvDist_flatRingProver_le prims sk aHat _ i hp h_laws hs2 (by
    change exclSet prims (t0s i) = _; rw [hi]) hβ0 hβ1 hkeep

/-- `SigningLaws.tvDist_flatRingProver_published_le` from the full primitive laws. -/
theorem tvDist_flatRingProver_published_le (hp : SigningParams p)
    (h_laws : Primitives.Laws prims nttOps) (hs2 : polyVecBounded sk.s2 p.eta)
    (t0s : Fin N → RqVec p.k) (hne : ∀ j, (exclSet prims (t0s j))ᶜ.Nonempty)
    (hi : t0s i = sk.t0) {βmin : ℚ≥0} (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hkeep : SignerKeeps prims sk aHat (Cutoff.const βmin)) :
    tvDist (flatRingProver prims sk aHat (publishedRing prims t0s hne) i (Cutoff.const βmin))
        (ringTarget (BucketVec p) (publishedRing prims t0s hne)) ≤
      ringOracleError prims sk aHat (publishedRing prims t0s hne) i (Cutoff.const βmin) +
        regError prims sk aHat (Cutoff.const βmin) + flatError prims sk (publishedRing prims t0s
            hne) i (Cutoff.const βmin) :=
  SigningLaws.tvDist_flatRingProver_published_le prims sk aHat i hp h_laws.toSigningLaws
    hs2 t0s hne hi hβ0 hβ1 hkeep

/-- **Two honest signers of one ring are close**: the flattened ring provers with signers `i₀`
and `i₁` (each with its own key and matrix) are within the sum of both signers' error terms, since
both are close to the same ring target. -/
theorem SigningLaws.tvDist_flatRingProver_signers_le (hp : SigningParams p)
    (h_laws : SigningLaws prims) {sk₀ sk₁ : SecretKey p} {aHat₀ aHat₁ : TqMatrix p.k p.l}
    (hs₀ : polyVecBounded sk₀.s2 p.eta) (hs₁ : polyVecBounded sk₁.s2 p.eta) {i₀ i₁ : Fin N}
    (hE₀ : E.excl i₀ = exclSet prims sk₀.t0) (hE₁ : E.excl i₁ = exclSet prims sk₁.t0)
    {βmin : ℚ≥0} (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hk₀ : SignerKeeps prims sk₀ aHat₀ (Cutoff.const βmin))
    (hk₁ : SignerKeeps prims sk₁ aHat₁ (Cutoff.const βmin)) :
    tvDist (flatRingProver prims sk₀ aHat₀ E i₀ (Cutoff.const βmin)) (flatRingProver prims sk₁
        aHat₁ E i₁ (Cutoff.const βmin)) ≤
      (ringOracleError prims sk₀ aHat₀ E i₀ (Cutoff.const βmin) + regError prims sk₀ aHat₀
          (Cutoff.const βmin) +
          flatError prims sk₀ E i₀ (Cutoff.const βmin)) +
        (ringOracleError prims sk₁ aHat₁ E i₁ (Cutoff.const βmin) + regError prims sk₁ aHat₁
            (Cutoff.const βmin) +
          flatError prims sk₁ E i₁ (Cutoff.const βmin)) := by
  refine (tvDist_triangle _ (ringTarget (BucketVec p) E) _).trans (add_le_add
    (tvDist_flatRingProver_le prims sk₀ aHat₀ E i₀ hp h_laws hs₀ hE₀ hβ0 hβ1 hk₀) ?_)
  rw [tvDist_comm]
  exact tvDist_flatRingProver_le prims sk₁ aHat₁ E i₁ hp h_laws hs₁ hE₁ hβ0 hβ1 hk₁

/-- `SigningLaws.tvDist_flatRingProver_signers_le` from the full primitive laws. -/
theorem tvDist_flatRingProver_signers_le (hp : SigningParams p)
    (h_laws : Primitives.Laws prims nttOps) {sk₀ sk₁ : SecretKey p} {aHat₀ aHat₁ : TqMatrix p.k p.l}
    (hs₀ : polyVecBounded sk₀.s2 p.eta) (hs₁ : polyVecBounded sk₁.s2 p.eta) {i₀ i₁ : Fin N}
    (hE₀ : E.excl i₀ = exclSet prims sk₀.t0) (hE₁ : E.excl i₁ = exclSet prims sk₁.t0)
    {βmin : ℚ≥0} (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hk₀ : SignerKeeps prims sk₀ aHat₀ (Cutoff.const βmin))
    (hk₁ : SignerKeeps prims sk₁ aHat₁ (Cutoff.const βmin)) :
    tvDist (flatRingProver prims sk₀ aHat₀ E i₀ (Cutoff.const βmin)) (flatRingProver prims sk₁
        aHat₁ E i₁ (Cutoff.const βmin)) ≤
      (ringOracleError prims sk₀ aHat₀ E i₀ (Cutoff.const βmin) + regError prims sk₀ aHat₀
          (Cutoff.const βmin) +
          flatError prims sk₀ E i₀ (Cutoff.const βmin)) +
        (ringOracleError prims sk₁ aHat₁ E i₁ (Cutoff.const βmin) + regError prims sk₁ aHat₁
            (Cutoff.const βmin) +
          flatError prims sk₁ E i₁ (Cutoff.const βmin)) :=
  SigningLaws.tvDist_flatRingProver_signers_le prims E hp h_laws.toSigningLaws
    hs₀ hs₁ hE₀ hE₁ hβ0 hβ1 hk₀ hk₁

/-- **The shape of `SampleInBall` outputs that the floor reads**: centered coefficients in
`{-1, 0, 1}` and at most `τ` nonzero coefficients. FIPS 204 Algorithm 29 returns exactly `τ`
nonzero coefficients; this hypothesis asks for the upper bound only. -/
structure SampleInBallShape : Prop where
  /-- Every coefficient has centered absolute value at most `1`. -/
  norm_le_one : ∀ cTilde, polyNorm (prims.sampleInBall cTilde) ≤ 1
  /-- At most `τ` coefficients are nonzero. -/
  weight_le : ∀ cTilde,
    (univ.filter fun j : Fin ringDegree => (prims.sampleInBall cTilde).get j ≠ 0).card ≤ p.tau

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- **Nothing is excluded under the floor** `τ · 2^(d-1) < γ₂` (ML-DSA-65 and ML-DSA-87,
`ct0_floor_mldsa65`, `ct0_floor_mldsa87`) for `‖t₀‖∞ ≤ 2^(d-1)` (`ct0_check_passes`). -/
theorem exclSet_eq_empty_of_floor (hfloor : p.tau * 2 ^ (droppedBits - 1) < p.gamma2)
    (h_ntt : NTTRingLaws nttOps) (hshape : SampleInBallShape prims) {t0 : RqVec p.k}
    (ht0 : polyVecNorm t0 ≤ 2 ^ (droppedBits - 1)) : exclSet prims t0 = ∅ := by
  ext cTilde
  simp only [exclSet, mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_le]
  exact lt_of_le_of_lt (polyVecNorm_challenge_smul_le h_ntt _ t0 (hshape.norm_le_one cTilde)
    (hshape.weight_le cTilde) ht0) hfloor

/-- **A ring of standard keys** `(ρ, t₁)`: no member publishes `t₀`, so nothing is excluded. -/
def standardRing (N : ℕ) : ExclSets (Fin N) (CommitHashBytes p) :=
  ringExclSets prims (fun _ => none) (fun _ _ h => by simp at h)

/-- **The flattened ring prover under the floor** (ML-DSA-65 and ML-DSA-87): for a ring of
standard keys there is no exclusion step, the signer's excluded set is empty, and the target is a
uniform oracle with `w₁` uniform over bucket vectors. -/
theorem SigningLaws.tvDist_flatRingProver_floor_le (hp : SigningParams p)
    (hfloor : p.tau * 2 ^ (droppedBits - 1) < p.gamma2) (h_laws : SigningLaws prims)
    (hshape : SampleInBallShape prims)
    (hs2 : polyVecBounded sk.s2 p.eta) (ht0 : polyVecNorm sk.t0 ≤ 2 ^ (droppedBits - 1))
    (i : Fin N) {βmin : ℚ≥0} (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hkeep : SignerKeeps prims sk aHat (Cutoff.const βmin)) :
    tvDist (flatRingProver prims sk aHat (standardRing prims N) i (Cutoff.const βmin))
        ((uniformOfFintype (BucketVec p)).bind fun v =>
          (uniformOfFintype (Fin N × BucketVec p → CommitHashBytes p)).map fun H => (H, some v)) ≤
      ringOracleError prims sk aHat (standardRing prims N) i (Cutoff.const βmin) + regError prims
          sk aHat (Cutoff.const βmin) +
        flatError prims sk (standardRing prims N) i (Cutoff.const βmin) := by
  rw [← ringTarget_of_excl_eq_empty (standardRing prims N) fun _ => rfl]
  refine tvDist_flatRingProver_le prims sk aHat _ i hp h_laws hs2 ?_ hβ0 hβ1 hkeep
  rw [exclSet_eq_empty_of_floor prims hfloor h_laws.transform hshape ht0]
  rfl

/-- `SigningLaws.tvDist_flatRingProver_floor_le` from the full primitive laws (which contain
the transform laws, so `_h_ntt` is redundant; it is kept for existing callers). -/
theorem tvDist_flatRingProver_floor_le (hp : SigningParams p)
    (hfloor : p.tau * 2 ^ (droppedBits - 1) < p.gamma2) (h_laws : Primitives.Laws prims nttOps)
    (_h_ntt : NTTRingLaws nttOps) (hshape : SampleInBallShape prims)
    (hs2 : polyVecBounded sk.s2 p.eta) (ht0 : polyVecNorm sk.t0 ≤ 2 ^ (droppedBits - 1))
    (i : Fin N) {βmin : ℚ≥0} (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hkeep : SignerKeeps prims sk aHat (Cutoff.const βmin)) :
    tvDist (flatRingProver prims sk aHat (standardRing prims N) i (Cutoff.const βmin))
        ((uniformOfFintype (BucketVec p)).bind fun v =>
          (uniformOfFintype (Fin N × BucketVec p → CommitHashBytes p)).map fun H => (H, some v)) ≤
      ringOracleError prims sk aHat (standardRing prims N) i (Cutoff.const βmin) + regError prims
          sk aHat (Cutoff.const βmin) +
        flatError prims sk (standardRing prims N) i (Cutoff.const βmin) :=
  SigningLaws.tvDist_flatRingProver_floor_le prims sk aHat hp hfloor h_laws.toSigningLaws
    hshape hs2 ht0 i hβ0 hβ1 hkeep

end Ring

/-! ### ML-DSA-65 and ML-DSA-87 -/

instance : NeZero (bucketCount mldsa65) :=
  ⟨(SigningParams.of_isApproved (Or.inr (Or.inl rfl))).bucketCount_pos.ne'⟩

instance : NeZero (bucketCount mldsa87) :=
  ⟨(SigningParams.of_isApproved (Or.inr (Or.inr rfl))).bucketCount_pos.ne'⟩

/-- **The flattened ring prover at ML-DSA-65** for a ring of standard keys: within the oracle
concentration, regularity and flattening terms of a uniform oracle with `w₁` uniform over bucket
vectors (the floor `ct0_floor_mldsa65`). -/
theorem SigningLaws.tvDist_flatRingProver_mldsa65_le (prims : Primitives mldsa65)
    [nttOps : NTTRingOps]
    [Nonempty (MaskBox mldsa65)] (h_laws : SigningLaws prims)
    (hshape : SampleInBallShape prims) (sk : SecretKey mldsa65)
    (aHat : TqMatrix mldsa65.k mldsa65.l) (hs2 : polyVecBounded sk.s2 mldsa65.eta)
    (ht0 : polyVecNorm sk.t0 ≤ 2 ^ (droppedBits - 1)) {N : ℕ} (i : Fin N) {βmin : ℚ≥0}
    (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1) (hkeep : SignerKeeps prims sk aHat
        (Cutoff.const βmin)) :
    tvDist (flatRingProver prims sk aHat (standardRing prims N) i (Cutoff.const βmin))
        ((uniformOfFintype (BucketVec mldsa65)).bind fun v =>
          (uniformOfFintype (Fin N × BucketVec mldsa65 → CommitHashBytes mldsa65)).map
            fun H => (H, some v)) ≤
      ringOracleError prims sk aHat (standardRing prims N) i (Cutoff.const βmin) + regError prims
          sk aHat (Cutoff.const βmin) +
        flatError prims sk (standardRing prims N) i (Cutoff.const βmin) :=
  tvDist_flatRingProver_floor_le prims sk aHat (SigningParams.of_isApproved (Or.inr (Or.inl rfl))) ct0_floor_mldsa65 h_laws
    hshape hs2 ht0 i hβ0 hβ1 hkeep

/-- `SigningLaws.tvDist_flatRingProver_mldsa65_le` from the full primitive laws (which contain
the transform laws, so `_h_ntt` is redundant; it is kept for existing callers). -/
theorem tvDist_flatRingProver_mldsa65_le (prims : Primitives mldsa65) [nttOps : NTTRingOps]
    [Nonempty (MaskBox mldsa65)] (h_laws : Primitives.Laws prims nttOps)
    (_h_ntt : NTTRingLaws nttOps) (hshape : SampleInBallShape prims) (sk : SecretKey mldsa65)
    (aHat : TqMatrix mldsa65.k mldsa65.l) (hs2 : polyVecBounded sk.s2 mldsa65.eta)
    (ht0 : polyVecNorm sk.t0 ≤ 2 ^ (droppedBits - 1)) {N : ℕ} (i : Fin N) {βmin : ℚ≥0}
    (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1) (hkeep : SignerKeeps prims sk aHat
        (Cutoff.const βmin)) :
    tvDist (flatRingProver prims sk aHat (standardRing prims N) i (Cutoff.const βmin))
        ((uniformOfFintype (BucketVec mldsa65)).bind fun v =>
          (uniformOfFintype (Fin N × BucketVec mldsa65 → CommitHashBytes mldsa65)).map
            fun H => (H, some v)) ≤
      ringOracleError prims sk aHat (standardRing prims N) i (Cutoff.const βmin) + regError prims
          sk aHat (Cutoff.const βmin) +
        flatError prims sk (standardRing prims N) i (Cutoff.const βmin) :=
  SigningLaws.tvDist_flatRingProver_mldsa65_le prims h_laws.toSigningLaws
    hshape sk aHat hs2 ht0 i hβ0 hβ1 hkeep

/-- **The flattened ring prover at ML-DSA-87** for a ring of standard keys: within the oracle
concentration, regularity and flattening terms of a uniform oracle with `w₁` uniform over bucket
vectors (the floor `ct0_floor_mldsa87`). -/
theorem SigningLaws.tvDist_flatRingProver_mldsa87_le (prims : Primitives mldsa87)
    [nttOps : NTTRingOps]
    [Nonempty (MaskBox mldsa87)] (h_laws : SigningLaws prims)
    (hshape : SampleInBallShape prims) (sk : SecretKey mldsa87)
    (aHat : TqMatrix mldsa87.k mldsa87.l) (hs2 : polyVecBounded sk.s2 mldsa87.eta)
    (ht0 : polyVecNorm sk.t0 ≤ 2 ^ (droppedBits - 1)) {N : ℕ} (i : Fin N) {βmin : ℚ≥0}
    (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1) (hkeep : SignerKeeps prims sk aHat
        (Cutoff.const βmin)) :
    tvDist (flatRingProver prims sk aHat (standardRing prims N) i (Cutoff.const βmin))
        ((uniformOfFintype (BucketVec mldsa87)).bind fun v =>
          (uniformOfFintype (Fin N × BucketVec mldsa87 → CommitHashBytes mldsa87)).map
            fun H => (H, some v)) ≤
      ringOracleError prims sk aHat (standardRing prims N) i (Cutoff.const βmin) + regError prims
          sk aHat (Cutoff.const βmin) +
        flatError prims sk (standardRing prims N) i (Cutoff.const βmin) :=
  tvDist_flatRingProver_floor_le prims sk aHat (SigningParams.of_isApproved (Or.inr (Or.inr rfl))) ct0_floor_mldsa87 h_laws
    hshape hs2 ht0 i hβ0 hβ1 hkeep

/-- `SigningLaws.tvDist_flatRingProver_mldsa87_le` from the full primitive laws (which contain
the transform laws, so `_h_ntt` is redundant; it is kept for existing callers). -/
theorem tvDist_flatRingProver_mldsa87_le (prims : Primitives mldsa87) [nttOps : NTTRingOps]
    [Nonempty (MaskBox mldsa87)] (h_laws : Primitives.Laws prims nttOps)
    (_h_ntt : NTTRingLaws nttOps) (hshape : SampleInBallShape prims) (sk : SecretKey mldsa87)
    (aHat : TqMatrix mldsa87.k mldsa87.l) (hs2 : polyVecBounded sk.s2 mldsa87.eta)
    (ht0 : polyVecNorm sk.t0 ≤ 2 ^ (droppedBits - 1)) {N : ℕ} (i : Fin N) {βmin : ℚ≥0}
    (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1) (hkeep : SignerKeeps prims sk aHat
        (Cutoff.const βmin)) :
    tvDist (flatRingProver prims sk aHat (standardRing prims N) i (Cutoff.const βmin))
        ((uniformOfFintype (BucketVec mldsa87)).bind fun v =>
          (uniformOfFintype (Fin N × BucketVec mldsa87 → CommitHashBytes mldsa87)).map
            fun H => (H, some v)) ≤
      ringOracleError prims sk aHat (standardRing prims N) i (Cutoff.const βmin) + regError prims
          sk aHat (Cutoff.const βmin) +
        flatError prims sk (standardRing prims N) i (Cutoff.const βmin) :=
  SigningLaws.tvDist_flatRingProver_mldsa87_le prims h_laws.toSigningLaws
    hshape sk aHat hs2 ht0 i hβ0 hβ1 hkeep

end GordieHowe.MLDSA
