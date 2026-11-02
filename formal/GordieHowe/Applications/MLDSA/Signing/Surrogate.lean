-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.Counting
public import Mathlib.Probability.Distributions.Uniform
import all LatticeCrypto.MLDSA.Concrete.Rounding

@[expose] public section

/-!
# The r0, ct₀ and hint checks for a uniform `w`

The exact acceptance law of the r0-check, the ct₀-check and the hint-count check of FIPS 204
Algorithm 7 (ML-DSA.Sign_internal, lines 21–28) when `w` is uniform over `Coeff^ι`, as a function
of the shifts `a = cs₂` and `b = ct₀`. The real signer's `w = Ay` is close to uniform only up to a
separate regularity term, which this file does not treat; here `w` ranges over all of `Coeff^ι`.

* `hintCount`, `hintProb`: in bucket `r1` with shift `b`, the number of the `2(γ₂ - β) - 1`
  r0-passing residues whose hint fires (`bucket_hint_card`), and that number as a fraction.
* `hintCount_le`, `hintProb_le`, `hintProb_le_abs`, `sum_hintProb_le`: in every bucket at most
  `|b| - β` residues fire, so `hintProb ≤ |b| / (2(γ₂ - β) - 1)` and the hint mean is at most
  `∑_i |b_i| / (2(γ₂ - β) - 1)` for every bucket vector.
* `poissonBinomialCdf p ω`: `Pr[Σ_i X_i ≤ ω]` for independent `X_i ~ Bernoulli(p_i)`, written as
  the sum over the sets `S` of firing coordinates with `|S| ≤ ω`.
* `acceptWeight`: the ct₀ indicator `‖b‖∞ < γ₂` times `poissonBinomialCdf` of the per-coordinate
  hint fractions. This is the weight the flattened prover divides by.
* `hintProbQ`, `poissonBinomialCdfQ`, `acceptWeightQ`: the same in `ℚ`, with compiled code; their
  casts to `ℝ` are the real forms (`cast_acceptWeightQ`).
* `card_acceptSet`: the residue vectors `w` with `HighBits(w) = v` passing all three checks number
  `(2(γ₂ - β) - 1)^|ι| · acceptWeight b v`, for every shift `‖a‖∞ ≤ β`.
* `card_acceptSet_indep_shift`, `uniform_acceptSet`: the count does not depend on `a`; for uniform
  `w` the probability is `((2(γ₂ - β) - 1)/q)^|ι| · acceptWeight b v`.
* `rqVecCoeffEquiv`, `ct0Factor_eq_one_of_floor`: the bridge from `R_q^k` to `Fin k × Fin 256`
  indexed coefficients, and the ct₀ factor is `1` for `b = ct₀` with honest `t₀` when
  `τ · 2^(d-1) < γ₂` (ML-DSA-65 and ML-DSA-87).
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA44 Finset

/-! ### Counting coordinatewise splits -/

/-- **Counting vectors by the number of coordinates in a marked part.** For finite sets
`A i ⊆ α` and predicates `P i`, the vectors `w ∈ ∏ A i` with at most `ω` coordinates satisfying
`P i (w i)` number `Σ_{|S| ≤ ω} ∏_i (#{x ∈ A i | P i x} if i ∈ S else #{x ∈ A i | ¬ P i x})`. -/
theorem card_piFinset_filter_card_le {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (A : ι → Finset α) (P : ι → α → Prop) [∀ i, DecidablePred (P i)] (ω : ℕ) :
    ((Fintype.piFinset A).filter fun w => (univ.filter fun i => P i (w i)).card ≤ ω).card =
      ∑ S ∈ univ.filter (fun S : Finset ι => S.card ≤ ω),
        ∏ i, (if i ∈ S then ((A i).filter (P i)).card else ((A i).filter fun x => ¬ P i x).card) := by
  rw [card_eq_sum_card_fiberwise (f := fun w => univ.filter fun i => P i (w i))
    (t := univ.filter (fun S : Finset ι => S.card ≤ ω))
    (fun w hw => by
      rw [mem_coe, mem_filter] at hw ⊢; exact ⟨mem_univ _, hw.2⟩)]
  refine sum_congr rfl fun S hS => ?_
  rw [mem_filter] at hS
  have : ((Fintype.piFinset A).filter fun w => (univ.filter fun i => P i (w i)).card ≤ ω).filter
      (fun w => (univ.filter fun i => P i (w i)) = S) =
      Fintype.piFinset fun i => if i ∈ S then (A i).filter (P i) else (A i).filter fun x => ¬ P i x := by
    ext w
    simp only [mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨⟨hA, -⟩, rfl⟩ i
      by_cases h : P i (w i) <;> simp [h, hA i]
    · intro h
      have hA : ∀ i, w i ∈ A i := fun i => by
        have := h i; split_ifs at this <;> exact (mem_filter.mp this).1
      have hSeq : (univ.filter fun i => P i (w i)) = S := by
        ext i
        have := h i
        simp only [mem_filter, mem_univ, true_and]
        split_ifs at this with hi
        · exact ⟨fun _ => hi, fun _ => (mem_filter.mp this).2⟩
        · exact ⟨fun hp => absurd hp (mem_filter.mp this).2, fun h' => absurd h' hi⟩
      exact ⟨⟨hA, hSeq ▸ hS.2⟩, hSeq⟩
  rw [this, Fintype.card_piFinset]
  exact prod_congr rfl fun i _ => by split_ifs <;> rfl

/-! ### The Poisson-binomial law -/

/-- **The Poisson-binomial CDF.** `Pr[X_1 + ⋯ + X_n ≤ ω]` for independent `X_i ~ Bernoulli(p_i)`
(the Poisson-binomial distribution, Y. H. Wang, *On the number of successes in independent
trials*, Statistica Sinica 3 (1993), eq. (1.1)), written as the sum over the sets `S` of
successful trials with `|S| ≤ ω` of `∏_{i ∈ S} p_i · ∏_{i ∉ S} (1 - p_i)`. -/
noncomputable def poissonBinomialCdf {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ)
    (ω : ℕ) : ℝ :=
  ∑ S ∈ univ.filter (fun S : Finset ι => S.card ≤ ω), ∏ i, if i ∈ S then p i else 1 - p i

/-! ### Per-coordinate hint counts -/

/-- The number of the `2(γ₂ - β) - 1` r0-passing residues of `HighBits` bucket `r1` whose FIPS 204
hint `MakeHint(-b, x - a + b)` (Algorithm 7 line 26) fires, for `|b| < γ₂` (`bucket_hint_card`):
`|b| - β` when `b < 0` and `r1 ≠ 0`, and `|b| - β - 1` otherwise, truncated at `0`. -/
def hintCount (β r1 : ℕ) (b : ℤ) : ℕ :=
  (if b < 0 ∧ r1 ≠ 0 then -b - β else |b| - β - 1).toNat

/-- The fraction of r0-passing residues of bucket `r1` whose hint fires with shift `b`:
`hintCount / (2(γ₂ - β) - 1)`. -/
noncomputable def hintProb (γ₂ β r1 : ℕ) (b : ℤ) : ℝ :=
  (hintCount β r1 b : ℝ) / ((2 * (γ₂ - β) - 1 : ℕ) : ℝ)

/-- **Bucket uniformity of the hint count**: in every bucket `r1`, at most `|b| - β` (truncated
at `0`) of the r0-passing residues fire the hint. -/
theorem hintCount_le (β r1 : ℕ) (b : ℤ) : hintCount β r1 b ≤ (|b| - β).toNat := by
  unfold hintCount
  split_ifs with h
  · exact Int.toNat_le_toNat (by rw [abs_of_neg h.1])
  · exact Int.toNat_le_toNat (by omega)

/-- **The hint fraction in every bucket**: `hintProb ≤ max(|b| - β, 0) / (2(γ₂ - β) - 1)`. -/
theorem hintProb_le (γ₂ β r1 : ℕ) (b : ℤ) :
    hintProb γ₂ β r1 b ≤ ((|b| - β).toNat : ℝ) / ((2 * (γ₂ - β) - 1 : ℕ) : ℝ) := by
  unfold hintProb
  gcongr
  exact_mod_cast hintCount_le β r1 b

/-- **The hint fraction in every bucket, by `|b|`**: `hintProb ≤ |b| / (2(γ₂ - β) - 1)`. -/
theorem hintProb_le_abs (γ₂ β r1 : ℕ) (b : ℤ) :
    hintProb γ₂ β r1 b ≤ (|b| : ℝ) / ((2 * (γ₂ - β) - 1 : ℕ) : ℝ) := by
  refine (hintProb_le γ₂ β r1 b).trans ?_
  gcongr
  have h : ((|b| - β).toNat : ℤ) ≤ |b| := by
    rw [Int.toNat_eq_max]
    exact max_le (by omega) (abs_nonneg b)
  have h' : ((((|b| - β).toNat : ℤ)) : ℝ) ≤ ((|b| : ℤ) : ℝ) := Int.cast_le.2 h
  simpa using h'

/-- **The hint mean in every bucket vector**: for every `v`,
`∑_i hintProb(v_i, b_i) ≤ ∑_i |b_i| / (2(γ₂ - β) - 1)`. -/
theorem sum_hintProb_le {ι : Type*} [Fintype ι] (γ₂ β : ℕ) (b : ι → ℤ) (v : ι → ℕ) :
    ∑ i, hintProb γ₂ β (v i) (b i) ≤ (∑ i, (|b i| : ℝ)) / ((2 * (γ₂ - β) - 1 : ℕ) : ℝ) := by
  rw [sum_div]
  exact sum_le_sum fun i _ => hintProb_le_abs γ₂ β (v i) (b i)

/-- **The acceptance weight of a uniform `w`.** The ct₀ indicator `‖b‖∞ < γ₂` (Algorithm 7
line 28) times the Poisson-binomial CDF at `ω` of the per-coordinate hint fractions in buckets
`v`. This is the conditional acceptance probability of the ct₀ and hint checks given `HighBits(w)
= v` and the r0-check, for uniform `w` (`card_acceptSet`), and the weight the flattened prover
divides by. -/
noncomputable def acceptWeight {ι : Type*} [Fintype ι] [DecidableEq ι] (γ₂ β ω : ℕ) (b : ι → ℤ)
    (v : ι → ℕ) : ℝ :=
  (if ∀ i, |b i| < γ₂ then 1 else 0) *
    poissonBinomialCdf (fun i => hintProb γ₂ β (v i) (b i)) ω

/-! ### Rational forms

The hint fraction, the Poisson-binomial CDF and the acceptance weight are rational: computed in
`ℚ` (`hintProbQ`, `poissonBinomialCdfQ`, `acceptWeightQ`), with compiled code, their casts to `ℝ`
are the real forms (`cast_hintProbQ`, `cast_poissonBinomialCdfQ`, `cast_acceptWeightQ`). A signer
that compares weights computes them in `ℚ`. -/

-- Irreducible so that unification does not evaluate the rational arithmetic.
/-- `hintProb` in `ℚ`: `hintCount / (2(γ₂ - β) - 1)`. -/
@[irreducible] def hintProbQ (γ₂ β r1 : ℕ) (b : ℤ) : ℚ :=
  (hintCount β r1 b : ℚ) / ((2 * (γ₂ - β) - 1 : ℕ) : ℚ)

@[simp, norm_cast] theorem cast_hintProbQ (γ₂ β r1 : ℕ) (b : ℤ) :
    (hintProbQ γ₂ β r1 b : ℝ) = hintProb γ₂ β r1 b := by
  simp [hintProbQ, hintProb]

-- Irreducible so that unification does not evaluate the rational arithmetic.
/-- `poissonBinomialCdf` in `ℚ`. -/
@[irreducible] def poissonBinomialCdfQ {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℚ)
    (ω : ℕ) : ℚ :=
  ∑ S ∈ univ.filter (fun S : Finset ι => S.card ≤ ω), ∏ i, if i ∈ S then p i else 1 - p i

@[simp, norm_cast] theorem cast_poissonBinomialCdfQ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℚ) (ω : ℕ) :
    (poissonBinomialCdfQ p ω : ℝ) = poissonBinomialCdf (fun i => (p i : ℝ)) ω := by
  simp only [poissonBinomialCdfQ, poissonBinomialCdf, Rat.cast_sum, Rat.cast_prod]
  refine Finset.sum_congr rfl fun S _ => Finset.prod_congr rfl fun i _ => ?_
  split_ifs <;> push_cast <;> rfl

-- Irreducible so that unification does not evaluate the rational arithmetic.
/-- `acceptWeight` in `ℚ`. -/
@[irreducible] def acceptWeightQ {ι : Type*} [Fintype ι] [DecidableEq ι] (γ₂ β ω : ℕ) (b : ι → ℤ)
    (v : ι → ℕ) : ℚ :=
  (if ∀ i, |b i| < γ₂ then 1 else 0) *
    poissonBinomialCdfQ (fun i => hintProbQ γ₂ β (v i) (b i)) ω

@[simp, norm_cast] theorem cast_acceptWeightQ {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ₂ β ω : ℕ) (b : ι → ℤ) (v : ι → ℕ) :
    (acceptWeightQ γ₂ β ω b v : ℝ) = acceptWeight γ₂ β ω b v := by
  rw [acceptWeightQ, acceptWeight, Rat.cast_mul, cast_poissonBinomialCdfQ]
  simp only [cast_hintProbQ]
  split_ifs <;> simp

/-- The residue vectors `w : Coeff^ι` in `HighBits` bucket vector `v` passing the r0-check
`|LowBits(w_i - a_i)| < γ₂ - β`, the ct₀-check `|b_i| < γ₂`, and the hint-count check
`#{i | MakeHint(-b_i, w_i - a_i + b_i)} ≤ ω` (FIPS 204 Algorithm 7 lines 21–28, coordinatewise,
with `a = cs₂` and `b = ct₀`). -/
def acceptSet {ι : Type*} [Fintype ι] [DecidableEq ι] (γ₂ β ω : ℕ) (a b : ι → ℤ) (v : ι → ℕ) :
    Finset (ι → Coeff) :=
  univ.filter fun w =>
    (∀ i, highBitsCoeff (w i) γ₂ = v i) ∧
    (∀ i, |lowBitsCoeff (w i - (a i : Coeff)) γ₂| < (γ₂ : ℤ) - β) ∧
    (∀ i, |b i| < γ₂) ∧
    (univ.filter fun i =>
      makeHintCoeff (-(b i : Coeff)) (w i - (a i : Coeff) + (b i : Coeff)) γ₂ = true).card ≤ ω

/-- The parameter side conditions of the counting: `γ₂ > 0`, `2γ₂ ∣ q - 1`, at least two
`HighBits` buckets, and `β < γ₂`. -/
structure RoundingParams (γ₂ β : ℕ) : Prop where
  gamma2_pos : 0 < γ₂
  gamma2_dvd : 2 * γ₂ ∣ modulus - 1
  two_buckets : 2 * γ₂ < modulus - 1
  beta_lt : β < γ₂

/-- `SigningParams` gives the rounding side conditions at `(γ₂, β)`. -/
theorem SigningParams.roundingParams {p : Params} (h : SigningParams p) :
    RoundingParams p.gamma2 p.beta :=
  ⟨h.gamma2_pos, h.gamma2_dvd, h.two_buckets, h.beta_lt_gamma2⟩

/-- **The exact law of the r0, ct₀ and hint checks for a uniform `w`.** For every shift
`‖a‖∞ ≤ β`, every `b` and every bucket vector `v` with `v_i < (q - 1)/(2γ₂)`, the residue vectors
`w : Coeff^ι` with `HighBits(w) = v` passing the r0, ct₀ and hint-count checks number
`(2(γ₂ - β) - 1)^|ι| · acceptWeight γ₂ β ω b v`. -/
theorem card_acceptSet {ι : Type*} [Fintype ι] [DecidableEq ι] {γ₂ β : ℕ}
    (hp : RoundingParams γ₂ β) (ω : ℕ) {a : ι → ℤ} (ha : ∀ i, |a i| ≤ β) (b : ι → ℤ)
    {v : ι → ℕ} (hv : ∀ i, v i < (modulus - 1) / (2 * γ₂)) :
    ((acceptSet γ₂ β ω a b v).card : ℝ) =
      ((2 * (γ₂ - β) - 1 : ℕ) : ℝ) ^ Fintype.card ι * acceptWeight γ₂ β ω b v := by
  by_cases hb : ∀ i, |b i| < γ₂
  swap
  · rw [show acceptSet γ₂ β ω a b v = ∅ from
      filter_false_of_mem fun w _ h => hb h.2.2.1, acceptWeight, ite_eq_right_iff.mpr (fun h => absurd h hb)]
    simp
  set N := 2 * (γ₂ - β) - 1 with hN
  have hNpos : (0 : ℝ) < N := by have := hp.beta_lt; norm_cast; omega
  set A : ι → Finset Coeff := fun i => rejectionBucket γ₂ β (v i) (a i)
  set P : ι → Coeff → Prop := fun i x =>
    makeHintCoeff (-(b i : Coeff)) (x - (a i : Coeff) + (b i : Coeff)) γ₂ = true
  have hset : acceptSet γ₂ β ω a b v =
      (Fintype.piFinset A).filter fun w => (univ.filter fun i => P i (w i)).card ≤ ω := by
    ext w
    simp only [acceptSet, A, P, rejectionBucket, mem_filter, mem_univ, true_and,
      Fintype.mem_piFinset]
    exact ⟨fun h => ⟨fun i => ⟨h.1 i, h.2.1 i⟩, h.2.2.2⟩,
      fun h => ⟨fun i => (h.1 i).1, fun i => (h.1 i).2, hb, h.2⟩⟩
  have hA : ∀ i, (A i).card = N := fun i => bucket_r0_card hp.gamma2_pos hp.gamma2_dvd (hv i) (ha i)
  have hH : ∀ i, ((A i).filter (P i)).card = hintCount β (v i) (b i) := fun i =>
    bucket_hint_card hp.gamma2_pos hp.gamma2_dvd hp.two_buckets (hv i) (ha i) (hb i)
  have hHle : ∀ i, hintCount β (v i) (b i) ≤ N := fun i =>
    (hH i) ▸ (hA i) ▸ card_filter_le _ _
  have hnH : ∀ i, ((A i).filter fun x => ¬ P i x).card = N - hintCount β (v i) (b i) := by
    intro i
    have := card_filter_add_card_filter_not (s := A i) (P i)
    rw [hA i, hH i] at this
    omega
  have hc : (acceptSet γ₂ β ω a b v).card = ∑ S ∈ univ.filter (fun S : Finset ι => S.card ≤ ω),
      ∏ i, (if i ∈ S then ((A i).filter (P i)).card else ((A i).filter fun x => ¬ P i x).card) := by
    rw [hset]; convert card_piFinset_filter_card_le A P ω
  rw [hc, acceptWeight, ite_eq_left_iff.mpr (fun h => absurd hb h), one_mul, poissonBinomialCdf,
    Nat.cast_sum, mul_sum]
  refine sum_congr rfl fun S _ => ?_
  rw [Nat.cast_prod, show (N : ℝ) ^ Fintype.card ι = ∏ _i : ι, (N : ℝ) by simp,
    ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [hH i, hnH i, hintProb, ← hN]
  split_ifs
  · field_simp
  · rw [Nat.cast_sub (hHle i)]; field_simp

/-- **The count does not depend on the shift `a = cs₂`.** Two shifts in the `β`-box give the
same number of accepted `w` in every bucket vector. -/
theorem card_acceptSet_indep_shift {ι : Type*} [Fintype ι] [DecidableEq ι] {γ₂ β : ℕ}
    (hp : RoundingParams γ₂ β) (ω : ℕ) {a a' : ι → ℤ} (ha : ∀ i, |a i| ≤ β)
    (ha' : ∀ i, |a' i| ≤ β) (b : ι → ℤ) {v : ι → ℕ}
    (hv : ∀ i, v i < (modulus - 1) / (2 * γ₂)) :
    (acceptSet γ₂ β ω a b v).card = (acceptSet γ₂ β ω a' b v).card := by
  exact_mod_cast (card_acceptSet hp ω ha b hv).trans (card_acceptSet hp ω ha' b hv).symm

/-- **The law for a uniform `w`.** For `w` uniform over `Coeff^ι`,
`Pr[HighBits(w) = v ∧ r0, ct₀ and hint checks pass] = ((2(γ₂ - β) - 1)/q)^|ι| · acceptWeight b v`.
The r0 factor is the same for every bucket vector `v` and every shift `a`; the challenge enters
only through `acceptWeight`. -/
theorem uniform_acceptSet {ι : Type*} [Fintype ι] [DecidableEq ι] {γ₂ β : ℕ}
    (hp : RoundingParams γ₂ β) (ω : ℕ) {a : ι → ℤ} (ha : ∀ i, |a i| ≤ β) (b : ι → ℤ)
    {v : ι → ℕ} (hv : ∀ i, v i < (modulus - 1) / (2 * γ₂)) :
    ((PMF.uniformOfFintype (ι → Coeff)).toOuterMeasure (acceptSet γ₂ β ω a b v : Set _)).toReal =
      (((2 * (γ₂ - β) - 1 : ℕ) : ℝ) / modulus) ^ Fintype.card ι * acceptWeight γ₂ β ω b v := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast]
  simp only [Finset.coe_sort_coe, Fintype.card_coe, Fintype.card_fun, ZMod.card]
  rw [card_acceptSet hp ω ha b hv, div_pow, Nat.cast_pow]
  have : ((modulus : ℝ)) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ (by norm_num [modulus])
  field_simp

/-! ### Polynomial vectors and the ct₀ factor -/

/-- A vector of length-`n` vectors is a function on `Fin k × Fin n`. -/
def vectorVectorEquiv (α : Type*) (k n : ℕ) : Vector (Vector α n) k ≃ (Fin k × Fin n → α) where
  toFun w ji := (w.get ji.1).get ji.2
  invFun f := Vector.ofFn fun j => Vector.ofFn fun i => f (j, i)
  left_inv w := Vector.ext fun j hj => Vector.ext fun i hi => by simp [Vector.get]; rfl
  right_inv f := funext fun ji => by simp

/-- `R_q^k` is `Coeff^(Fin k × Fin 256)`: coefficient `i` of component `j` at `(j, i)`. -/
def rqVecCoeffEquiv (k : ℕ) : RqVec k ≃ (Fin k × Fin ringDegree → Coeff) :=
  vectorVectorEquiv Coeff k ringDegree

/-- The coefficients of `w ∈ R_q^k`, indexed by `(component, coefficient)`. -/
def rqVecCoeffs {k : ℕ} (w : RqVec k) : Fin k × Fin ringDegree → Coeff :=
  rqVecCoeffEquiv k w

/-- The coefficient of `rqVecCoeffs w` at `(j, i)` is coefficient `i` of component `j`. -/
theorem rqVecCoeffs_apply {k : ℕ} (w : RqVec k) (ji : Fin k × Fin ringDegree) :
    rqVecCoeffs w ji = (w.get ji.1).get ji.2 :=
  rfl

/-- **The ct₀ factor is `1` under the floor.** If `τ · 2^(d-1) < γ₂` (ML-DSA-65 and ML-DSA-87,
`ct0_floor_mldsa65`, `ct0_floor_mldsa87`), `c` is challenge-shaped and `‖t₀‖∞ ≤ 2^(d-1)`, the
centered coefficients `b` of `ct₀` satisfy `‖b‖∞ < γ₂`, so `acceptWeight` is the Poisson-binomial
CDF alone. -/
theorem ct0Factor_eq_one_of_floor {τ γ₂ β ω k : ℕ} (hfloor : τ * 2 ^ (droppedBits - 1) < γ₂)
    (c : Rq) (t0 : RqVec k) (hc1 : polyNorm c ≤ 1)
    (hcw : (univ.filter fun i : Fin ringDegree => c.get i ≠ 0).card ≤ τ)
    (ht0 : polyVecNorm t0 ≤ 2 ^ (droppedBits - 1)) (v : Fin k × Fin ringDegree → ℕ) :
    acceptWeight γ₂ β ω
        (fun ji => LatticeCrypto.centeredRepr (rqVecCoeffs (t0.map (c * ·)) ji)) v =
      poissonBinomialCdf (fun ji => hintProb γ₂ β (v ji)
        (LatticeCrypto.centeredRepr (rqVecCoeffs (t0.map (c * ·)) ji))) ω := by
  have hn : polyVecNorm (t0.map (c * ·)) < γ₂ :=
    lt_of_le_of_lt (norm_challenge_mul_vec_le c t0 hc1 hcw ht0) hfloor
  have hpos : 0 < γ₂ := by omega
  rw [polyVecNorm_lt_iff _ hpos] at hn
  have hb : ∀ ji : Fin k × Fin ringDegree,
      |LatticeCrypto.centeredRepr (rqVecCoeffs (t0.map (c * ·)) ji)| < γ₂ := fun ji => by
    have := hn ji.1 ji.2
    rw [Int.abs_eq_natAbs]; exact_mod_cast this
  rw [acceptWeight, ite_eq_left_iff.mpr (fun h => absurd hb h), one_mul]

end GordieHowe.MLDSA
