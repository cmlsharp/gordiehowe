-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.PMFChiSquare
public import GordieHowe.Foundations.ToMathlib.SamplingWithoutReplacement
public import GordieHowe.Foundations.Algebra.DFT
public import GordieHowe.Applications.MLDSA.Signing.Counting
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds
public import GordieHowe.Applications.MLDSA.Signing.Ideal
public import LatticeCrypto.MLDSA.Concrete.LawBounds
import all LatticeCrypto.MLDSA.Concrete.Rounding

@[expose] public section

/-!
# The ct₀ floor of ML-DSA-44

ML-DSA-44's signer rejects every attempt whose challenge `c` has `‖c · t₀‖∞ ≥ γ₂` (FIPS 204
Algorithm 7, line 28); at ML-DSA-44 `τ · 2^12 = 159744 > γ₂ = 95232`, so this can happen
(`ct0_floor_mldsa44_fails`). Call that set of challenges the floor `E_{t₀}` and
`p(t₀) = Pr_c[c ∈ E_{t₀}]` for a uniform challenge. A kept challenge has law `U(· | c ∉ E_{t₀})`,
which is at distance exactly `p(t₀)` from `U`. This file bounds `p`.

**General facts about uniform laws conditioned on an event** (namespace `PMF`):

* `tvDist_uniformOfFinset`: `tvDist (U(· | s)) U = 1 − #s / #α`, so the kept law is at distance
  `p` from `U` (`tvDist_condNot`);
* `tvDist_bind_pi_const_le`: `Q` kept values from a hidden parameter `θ ← μ` are within
  `Q · E_θ tvDist (P θ) q` of `q^{⊗Q}` (the hybrid bound);
* `chiSqCorr_condNot`: `ρ(E, E') = (Pr[E ∩ E'] − p p') / ((1 − p)(1 − p'))` for the conditioned
  laws `P = U(· | ¬E)`, `P' = U(· | ¬E')`, and `chiSqCorr_condNot_le`;
* `tvDist_bind_pi_const_le_sqrt`: the chi-square mixture bound
  `tvDist ≤ ½ √((1 + ρ)^Q − 1 + δ (1 + R)^Q)` when `chiSqCorr ≤ ρ` on a set of good parameter
  pairs, `chiSqCorr ≤ R` everywhere, and `δ` is the mass of the bad pairs.

**Signed subset sums** (namespace `GordieHowe.MLDSA`):

* `ChallengeSeed n τ`: a `τ`-subset `S` of the positions and a sign at every position; its
  coefficient vector `ChallengeSeed.coeff` is `±1` on `S` and `0` elsewhere. Under the uniform
  seed this vector is uniform on the challenges of weight `τ` with `±1` coefficients, the law of
  SampleInBall (FIPS 204 Algorithm 29), which this file takes as the challenge law;
* `prob_le_abs_signedSum_le`: the Chernoff bound
  `Pr[|∑_{j ∈ S} s_j w_j| ≥ a] ≤ 2 e^{−λa} (mean_j cosh(λ w_j))^τ`, through Hoeffding's
  comparison for sampling without replacement (`Finset.subsetProdSum_le`);
* `cosh_le_one_add_sq_mul`, `mean_cosh_le`: the closed form
  `mean_j cosh(λ w_j) ≤ 1 + (m₂ / M²)(cosh(λ M) − 1)` for `|w_j| ≤ M` with mean square `m₂`.

**The floor**:

* `negacyclicConvCoeff_eq_sum_weight`: `(c · t)_k = ∑_j c_j · (±t_{k−j})`, so each coefficient of
  `c · t` is a signed subset sum of the entries of `t`;
* `floorProb_le`: for a fixed key `t : Fin K → Fin n → ℤ`,
  `p(t) ≤ ∑_m n · 2 e^{−λγ₂} (mean_i cosh(λ t_{m,i}))^τ`;
* `sum_floorProb_le`: for a key with independent coordinates `v(x)`, `x` uniform on a finite
  type `X`, whose exponential moments `E e^{±λ v(x)}` are at most `A`, the average of `p(t)` over
  keys is at most `K n · 2 e^{−λγ₂} A^τ`. Averaging over the key replaces Hoeffding's comparison
  by exact independence of the `τ` entries of `t` that one coefficient reads.

**ML-DSA-44** (`K = 4`, `n = 256`, `τ = 39`, `γ₂ = 95232`, `t₀` coordinates uniform on
`(−2^12, 2^12]`): `floorProb_mldsa44_avg_le`: the average floor probability is at most `2^−23`
(at `λ = 19/32768`, with both exponential moments of a coordinate at most `2.2455`,
`t0Coord_mgf_le`).

**The signer's ct₀-check** (section `Signer`):

* `centeredPoly_mul`: for `c` with at most `τ` nonzero coefficients of norm at most `1`,
  `‖t‖∞ ≤ B` and `2τB < q`, the centered coefficients of the `R_q` product `c · t` are the integer
  negacyclic convolution of the centered coefficients (no coefficient wraps mod `q`);
* `ct0Check_eq_false_iff`: under the same hypotheses for `t₀ : R_q^k`, Ideal's `ct0Check (c • t₀)`
  (FIPS 204 Algorithm 7 line 28) fails exactly when `FloorEvent γ₂ (centeredVec t₀) (centeredPoly c)`;
* `IsChallenge τ`: the challenge ball, polynomials with exactly `τ` coefficients `±1` (the outputs
  of SampleInBall, Algorithm 29); `ChallengeSeed.poly`, `card_seed_filter`: every challenge of the
  ball is the polynomial of exactly `2^(256 − τ)` seeds, so the uniform seed gives the uniform
  challenge of the ball (`probUnif_seedPoly`);
* `probUnif_floorEvent_eq_ct0Reject`: the floor probability of this file is the fraction of the
  ball whose ct₀-check fails. The bounds here are about a challenge uniform on the ball; that
  SampleInBall of a random-oracle output is uniform on the ball is the standard idealization of
  its XOF stream and is not proved here.

**Uniform-t keys** (section `UniformT`): `power2RoundLowCoeff` is the low part of the vendored
`power2RoundCoeff` (Algorithm 35). Since `q = 1023 · 2^13 + 1`, the low part of a uniform
`t ∈ Z_q` hits every value of `(−2^12, 2^12]` `1023` times and `0` once more
(`sum_power2RoundLowCoeff`); its exponential moments at `λ = 19/32768` are still at most `2.2455`
(`power2RoundLowCoeff_mgf_le`), and `floorProb_mldsa44_uniformT_le` gives the average floor
probability `≤ 2^−23` for `t` uniform on `Z_q^{4 × 256}`. `centeredPoly_power2RoundLow` identifies
these values with the centered coefficients of the vendored `power2RoundLow`. This is the uniform-t
key model; the honest `t = A s₁ + s₂` is not exactly uniform.

**A per-key certificate** (section `Certificate`): `floorBound Nc Ne λ γ₂ τ t : ℚ` is the bound of
`floorProb_le` with `cosh` replaced by `coshUB` (Taylor bound of `Real.exp_bound` at `x/4`, then
the doubling formula twice) and `e^{−λγ₂}` by `expNegUB` (one over a Taylor partial sum);
`probUnif_floorEvent_le_floorBound` proves it bounds the floor probability of the fixed key `t`
when `|λ t_{m,i}| ≤ 4`.
-/

open Finset Real
open scoped BigOperators

namespace PMF

section Condition

variable {α : Type*} [Fintype α]

/-- **The probability of an event under the uniform law** on a finite type, in `ℝ`. -/
noncomputable def probUnif (E : α → Prop) [DecidablePred E] : ℝ :=
  (univ.filter E).card / Fintype.card α

/-- `probUnif` as an average of indicators. -/
theorem probUnif_eq_sum (E : α → Prop) [DecidablePred E] :
    probUnif E = (∑ a, if E a then (1 : ℝ) else 0) / Fintype.card α := by
  rw [probUnif, ← natCast_card_filter]

/-- `probUnif` is nonnegative. -/
theorem probUnif_nonneg (E : α → Prop) [DecidablePred E] : 0 ≤ probUnif E := by
  unfold probUnif; positivity

/-- `probUnif` is at most `1`. -/
theorem probUnif_le_one (E : α → Prop) [DecidablePred E] : probUnif E ≤ 1 := by
  unfold probUnif
  rcases Nat.eq_zero_or_pos (Fintype.card α) with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast card_le_univ _

/-- **The union bound** for `probUnif`. -/
theorem probUnif_exists_le {ι : Type*} [Fintype ι] (E : ι → α → Prop) [∀ i, DecidablePred (E i)] :
    probUnif (fun a => ∃ i, E i a) ≤ ∑ i, probUnif (E i) := by
  simp only [probUnif_eq_sum, ← sum_div]
  gcongr
  rw [sum_comm]
  refine sum_le_sum fun a _ => ?_
  split_ifs with h
  · obtain ⟨i, hi⟩ := h
    exact (single_le_sum (f := fun i => if E i a then (1 : ℝ) else 0)
      (fun i _ => by split_ifs <;> norm_num) (mem_univ i)).trans_eq' (by simp [hi])
  · exact sum_nonneg fun i _ => by split_ifs <;> norm_num

omit [Fintype α] in
/-- The real value of a uniform law on a finset. -/
theorem toReal_uniformOfFinset_apply [DecidableEq α] (s : Finset α) (hs : s.Nonempty) (a : α) :
    (uniformOfFinset s hs a).toReal = if a ∈ s then (s.card : ℝ)⁻¹ else 0 := by
  by_cases ha : a ∈ s
  · simp [uniformOfFinset_apply_of_mem hs ha, ha]
  · simp [uniformOfFinset_apply_of_notMem hs ha, ha]

variable [Nonempty α]

/-- **A uniform law on `s` is at distance `1 − #s / #α` from the uniform law.** -/
theorem tvDist_uniformOfFinset (s : Finset α) (hs : s.Nonempty) :
    tvDist (uniformOfFinset s hs) (uniformOfFintype α) = 1 - s.card / Fintype.card α := by
  classical
  have hcN : s.card ≤ Fintype.card α := card_le_univ s
  have hcR : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hNR : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hle : (Fintype.card α : ℝ)⁻¹ ≤ (s.card : ℝ)⁻¹ := inv_anti₀ hcR (by exact_mod_cast hcN)
  rw [tvDist_eq_sum, ← sum_add_sum_compl s]
  have h1 : ∀ a ∈ s, |(uniformOfFinset s hs a).toReal - (uniformOfFintype α a).toReal| =
      (s.card : ℝ)⁻¹ - (Fintype.card α : ℝ)⁻¹ := fun a ha => by
    rw [toReal_uniformOfFinset_apply]
    simp only [ha, ↓reduceIte]
    rw [toReal_uniformOfFintype_apply, abs_of_nonneg (sub_nonneg.2 hle)]
  have h2 : ∀ a ∈ sᶜ, |(uniformOfFinset s hs a).toReal - (uniformOfFintype α a).toReal| =
      (Fintype.card α : ℝ)⁻¹ := fun a ha => by
    rw [toReal_uniformOfFinset_apply]
    simp only [mem_compl.1 ha, ↓reduceIte]
    rw [toReal_uniformOfFintype_apply, zero_sub, abs_neg, abs_of_pos (inv_pos.2 hNR)]
  rw [sum_congr rfl h1, sum_congr rfl h2, sum_const, sum_const, card_compl, nsmul_eq_mul,
    nsmul_eq_mul, Nat.cast_sub hcN]
  field_simp
  ring

/-- **The kept law is at distance `p` from uniform**: `U(· | ¬E)` is at distance exactly
`Pr[E]` from `U`. -/
theorem tvDist_condNot (E : α → Prop) [DecidablePred E] (h : (univ.filter fun a => ¬E a).Nonempty) :
    tvDist (uniformOfFinset _ h) (uniformOfFintype α) = probUnif E := by
  rw [tvDist_uniformOfFinset, probUnif]
  have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hc := card_filter_add_card_filter_not (s := univ) E
  rw [card_univ] at hc
  field_simp
  rw [← hc]
  push_cast
  ring

/-- **`1 + ρ` for two uniform laws on finsets**, relative to the uniform law:
`1 + chiSqCorr (U_s) (U_{s'}) U = #α · #(s ∩ s') / (#s · #s')`. -/
theorem one_add_chiSqCorr_uniformOfFinset [DecidableEq α] (s s' : Finset α) (hs : s.Nonempty)
    (hs' : s'.Nonempty) :
    1 + chiSqCorr (uniformOfFinset s hs) (uniformOfFinset s' hs') (uniformOfFintype α) =
      Fintype.card α * (s ∩ s').card / (s.card * s'.card) := by
  have hcR : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hcR' : (0 : ℝ) < s'.card := by exact_mod_cast hs'.card_pos
  rw [one_add_chiSqCorr]
  simp only [toReal_uniformOfFinset_apply, toReal_uniformOfFintype_apply]
  have hterm : ∀ a, (if a ∈ s then (s.card : ℝ)⁻¹ else 0) * (if a ∈ s' then (s'.card : ℝ)⁻¹ else 0) /
      (Fintype.card α : ℝ)⁻¹ =
      if a ∈ s ∩ s' then (Fintype.card α : ℝ) / (s.card * s'.card) else 0 := fun a => by
    by_cases ha : a ∈ s <;> by_cases ha' : a ∈ s' <;> simp [ha, ha']
    field_simp
  rw [sum_congr rfl fun a _ => hterm a, sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
  ring

/-- **The chi-square correlation of two kept laws**: for `P = U(· | ¬E)` and `P' = U(· | ¬E')`,
`chiSqCorr P P' U = (Pr[E ∧ E'] − Pr[E] Pr[E']) / ((1 − Pr[E]) (1 − Pr[E']))`. -/
theorem chiSqCorr_condNot [DecidableEq α] (E E' : α → Prop) [DecidablePred E] [DecidablePred E']
    (h : (univ.filter fun a => ¬E a).Nonempty) (h' : (univ.filter fun a => ¬E' a).Nonempty) :
    chiSqCorr (uniformOfFinset _ h) (uniformOfFinset _ h') (uniformOfFintype α) =
      (probUnif (fun a => E a ∧ E' a) - probUnif E * probUnif E') /
        ((1 - probUnif E) * (1 - probUnif E')) := by
  have h1 := one_add_chiSqCorr_uniformOfFinset _ _ h h'
  have hN : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hcount : ∀ (F : α → Prop) [DecidablePred F],
      ((univ.filter fun a => ¬F a).card : ℝ) = Fintype.card α - (univ.filter F).card := by
    intro F _
    have := card_filter_add_card_filter_not (s := univ) F
    rw [card_univ] at this
    rw [← this]
    push_cast
    ring
  have hint : (((univ.filter fun a => ¬E a) ∩ (univ.filter fun a => ¬E' a)).card : ℝ) =
      Fintype.card α - ((univ.filter E).card + (univ.filter E').card -
        (univ.filter fun a => E a ∧ E' a).card) := by
    rw [← filter_and]
    have h2 := card_filter_add_card_filter_not (s := univ) (fun a => ¬E a ∧ ¬E' a)
    have h3 := card_union_add_card_inter (univ.filter E) (univ.filter E')
    rw [← filter_or, ← filter_and] at h3
    have h4 : (univ.filter fun a => ¬(¬E a ∧ ¬E' a)) = univ.filter fun a => E a ∨ E' a :=
      filter_congr fun a _ => by tauto
    rw [h4, card_univ] at h2
    have h2' : ((univ.filter fun a => ¬E a ∧ ¬E' a).card : ℝ) +
        (univ.filter fun a => E a ∨ E' a).card = Fintype.card α := by exact_mod_cast h2
    have h3' : ((univ.filter fun a => E a ∨ E' a).card : ℝ) +
        (univ.filter fun a => E a ∧ E' a).card = (univ.filter E).card + (univ.filter E').card := by
      exact_mod_cast h3
    linarith
  have hpos : (0 : ℝ) < Fintype.card α - (univ.filter E).card := by
    rw [← hcount E]; exact_mod_cast h.card_pos
  have hpos' : (0 : ℝ) < Fintype.card α - (univ.filter E').card := by
    rw [← hcount E']; exact_mod_cast h'.card_pos
  have hcorr : chiSqCorr (uniformOfFinset _ h) (uniformOfFinset _ h') (uniformOfFintype α) =
      Fintype.card α * ((univ.filter fun a => ¬E a) ∩ (univ.filter fun a => ¬E' a)).card /
        ((univ.filter fun a => ¬E a).card * (univ.filter fun a => ¬E' a).card) - 1 := by
    linarith
  rw [hcorr, hint, hcount E, hcount E']
  simp only [probUnif]
  field_simp
  ring

/-- **The upper bound on `ρ`** used in the mixture bound: `ρ ≤ Pr[E ∧ E'] / ((1 − p)(1 − p'))`. -/
theorem chiSqCorr_condNot_le [DecidableEq α] (E E' : α → Prop) [DecidablePred E]
    [DecidablePred E'] (h : (univ.filter fun a => ¬E a).Nonempty)
    (h' : (univ.filter fun a => ¬E' a).Nonempty) :
    chiSqCorr (uniformOfFinset _ h) (uniformOfFinset _ h') (uniformOfFintype α) ≤
      probUnif (fun a => E a ∧ E' a) / ((1 - probUnif E) * (1 - probUnif E')) := by
  rw [chiSqCorr_condNot]
  have h0 : 0 ≤ (1 - probUnif E) * (1 - probUnif E') :=
    mul_nonneg (sub_nonneg.2 (probUnif_le_one E)) (sub_nonneg.2 (probUnif_le_one E'))
  gcongr
  linarith [mul_nonneg (probUnif_nonneg E) (probUnif_nonneg E')]

end Condition

section Mixture

variable {β : Type*} [Fintype β]

/-- **`Q` independent copies**: `tvDist (p^⊗Q) (q^⊗Q) ≤ Q · tvDist p q`. -/
theorem tvDist_pi_const_le (p q : PMF β) (Q : ℕ) :
    tvDist (pi fun _ : Fin Q => p) (pi fun _ : Fin Q => q) ≤ Q * tvDist p q := by
  simpa using tvDist_pi_le (fun _ : Fin Q => p) (fun _ => q)

/-- **The hybrid bound for a hidden parameter**: `Q` independent draws from `P θ`, for one
`θ ← μ`, are within `Q · E_θ tvDist (P θ) q` of `Q` draws from `q`. -/
theorem tvDist_bind_pi_const_le {Θ : Type*} [Fintype Θ] (μ : PMF Θ) (P : Θ → PMF β) (q : PMF β)
    (Q : ℕ) :
    tvDist (μ.bind fun θ => pi fun _ : Fin Q => P θ) (pi fun _ : Fin Q => q) ≤
      Q * ∑ θ, (μ θ).toReal * tvDist (P θ) q := by
  have h := tvDist_bind_left_le μ (fun θ => pi fun _ : Fin Q => P θ)
    (fun _ => pi fun _ : Fin Q => q)
  rw [bind_const] at h
  refine h.trans ?_
  rw [mul_sum]
  refine sum_le_sum fun θ _ => ?_
  calc (μ θ).toReal * tvDist (pi fun _ : Fin Q => P θ) (pi fun _ : Fin Q => q)
      ≤ (μ θ).toReal * (Q * tvDist (P θ) q) :=
        mul_le_mul_of_nonneg_left (tvDist_pi_const_le _ _ Q) ENNReal.toReal_nonneg
    _ = Q * ((μ θ).toReal * tvDist (P θ) q) := by ring

/-- `1 + chiSqCorr` is nonnegative. -/
theorem one_add_chiSqCorr_nonneg (p p' q : PMF β) : 0 ≤ 1 + chiSqCorr p p' q := by
  rw [one_add_chiSqCorr]
  exact sum_nonneg fun a _ => by positivity

/-- **The chi-square mixture bound with good parameter pairs**: if `chiSqCorr (P θ) (P θ') q ≤ ρ`
whenever `G θ θ'`, and `≤ R` always, then `Q` draws from `P θ` for one `θ ← μ` are within
`½ √((1 + ρ)^Q − 1 + δ (1 + R)^Q)` of `q^{⊗Q}`, where `δ = Pr_{θ, θ' ← μ}[¬G θ θ']`. -/
theorem tvDist_bind_pi_const_le_sqrt {Θ : Type*} [Fintype Θ] (μ : PMF Θ) {P : Θ → PMF β}
    {q : PMF β} (hpq : ∀ θ b, q b = 0 → P θ b = 0) (Q : ℕ) (G : Θ → Θ → Prop) [DecidableRel G]
    {ρ R : ℝ} (hρ : -1 ≤ ρ) (hG : ∀ θ θ', G θ θ' → chiSqCorr (P θ) (P θ') q ≤ ρ)
    (hR : ∀ θ θ', chiSqCorr (P θ) (P θ') q ≤ R) :
    tvDist (μ.bind fun θ => pi fun _ : Fin Q => P θ) (pi fun _ : Fin Q => q) ≤
      √((1 + ρ) ^ Q - 1 +
        (∑ θ, ∑ θ', if G θ θ' then 0 else (μ θ).toReal * (μ θ').toReal) * (1 + R) ^ Q) / 2 := by
  have hM : ∀ f, (pi fun _ : Fin Q => q) f = 0 → (μ.bind fun θ => pi fun _ : Fin Q => P θ) f = 0 :=
    fun f hf => by
      rw [bind_apply, ENNReal.tsum_eq_zero]
      exact fun θ => by rw [pi_apply_eq_zero_of (fun _ => hpq θ) f hf, mul_zero]
  refine (tvDist_le_sqrt_chiSq hM).trans ?_
  gcongr
  have h := one_add_chiSq_bind_pi_const μ hpq Q
  have hρ0 : 0 ≤ 1 + ρ := by linarith
  have hterm : ∀ θ θ', (μ θ).toReal * (μ θ').toReal * (1 + chiSqCorr (P θ) (P θ') q) ^ Q ≤
      (μ θ).toReal * (μ θ').toReal * (1 + ρ) ^ Q +
        (if G θ θ' then 0 else (μ θ).toReal * (μ θ').toReal) * (1 + R) ^ Q := fun θ θ' => by
    have hw : 0 ≤ (μ θ).toReal * (μ θ').toReal := by positivity
    have h0 := one_add_chiSqCorr_nonneg (P θ) (P θ') q
    split_ifs with hg
    · have := pow_le_pow_left₀ h0
        (show 1 + chiSqCorr (P θ) (P θ') q ≤ 1 + ρ by linarith [hG θ θ' hg]) Q
      nlinarith [mul_le_mul_of_nonneg_left this hw]
    · have := pow_le_pow_left₀ h0
        (show 1 + chiSqCorr (P θ) (P θ') q ≤ 1 + R by linarith [hR θ θ']) Q
      have := mul_le_mul_of_nonneg_left this hw
      have : 0 ≤ (μ θ).toReal * (μ θ').toReal * (1 + ρ) ^ Q := by positivity
      linarith
  have hsum : ∑ θ, ∑ θ', (μ θ).toReal * (μ θ').toReal = 1 := by
    rw [← sum_mul_sum, sum_toReal, one_mul]
  have := sum_le_sum fun θ (_ : θ ∈ univ) => sum_le_sum fun θ' (_ : θ' ∈ univ) => hterm θ θ'
  simp only [sum_add_distrib, ← sum_mul] at this
  rw [hsum, one_mul] at this
  linarith

end Mixture

end PMF

namespace GordieHowe.MLDSA

open PMF

/-! ### Challenges as signed subsets -/

/-- **The randomness of a challenge**: a `τ`-subset of the `n` positions and a sign at every
position (only the signs on the subset matter). -/
abbrev ChallengeSeed (n τ : ℕ) :=
  {S : Finset (Fin n) // S ∈ (univ : Finset (Fin n)).powersetCard τ} × (Fin n → Bool)

/-- The `±1` coefficient at a position of the subset `S` with signs `ε`, `0` off `S`. -/
def signedCoeff {n : ℕ} (S : Finset (Fin n)) (ε : Fin n → Bool) (j : Fin n) : ℤ :=
  if j ∈ S then (if ε j then 1 else -1) else 0

/-- **The challenge of a seed**: `±1` on the subset, `0` elsewhere. For a uniform seed it is
uniform on the vectors with exactly `τ` nonzero coefficients, each `±1`: the challenge law of
SampleInBall (FIPS 204 Algorithm 29). -/
def ChallengeSeed.coeff {n τ : ℕ} (ω : ChallengeSeed n τ) : Fin n → ℤ :=
  signedCoeff ω.1.1 ω.2

/-- The number of seeds: `C(n, τ) · 2^n`. -/
theorem card_challengeSeed (n τ : ℕ) : Fintype.card (ChallengeSeed n τ) = n.choose τ * 2 ^ n := by
  simp [Fintype.card_prod]

/-- **Averaging the signs**: `∑_ε exp(λ ∑_j c_j w_j) = 2^n ∏_{j ∈ S} cosh(λ w_j)` for the signed
coefficients `c = signedCoeff S ε`. -/
theorem sum_signs_exp {n : ℕ} (S : Finset (Fin n)) (w : Fin n → ℝ) (lam : ℝ) :
    ∑ ε : Fin n → Bool, exp (lam * ∑ j, (signedCoeff S ε j : ℝ) * w j) =
      2 ^ n * ∏ j ∈ S, cosh (lam * w j) := by
  let g : Fin n → Bool → ℝ := fun j b =>
    exp (lam * ((if j ∈ S then (if b then 1 else -1) else 0 : ℤ) : ℝ) * w j)
  have hexp : ∀ ε : Fin n → Bool, exp (lam * ∑ j, (signedCoeff S ε j : ℝ) * w j) =
      ∏ j, g j (ε j) :=
    fun ε => by
      rw [mul_sum, exp_sum]
      exact prod_congr rfl fun j _ => by simp only [g, signedCoeff, mul_assoc]
  rw [Fintype.sum_congr _ _ hexp, ← Fintype.prod_sum g]
  have hj : ∀ j : Fin n, ∑ b : Bool, g j b =
      2 * (if j ∈ S then cosh (lam * w j) else 1) := fun j => by
    simp only [g]
    by_cases hjS : j ∈ S
    · simp only [hjS, ↓reduceIte, Fintype.sum_bool, cosh_eq]
      push_cast
      ring_nf
    · simp only [hjS, ↓reduceIte, Fintype.sum_bool]
      push_cast
      simp
      ring
  simp_rw [hj, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_ite_mem]
  rw [univ_inter]

/-- **Markov's inequality for `cosh`**: `1[a ≤ |L|] ≤ e^{−λa} (e^{λL} + e^{−λL})` for `λ ≥ 0`. -/
theorem indicator_le_exp_add_exp {L a lam : ℝ} (hlam : 0 ≤ lam) :
    (if a ≤ |L| then (1 : ℝ) else 0) ≤ exp (-(lam * a)) * (exp (lam * L) + exp (-(lam * L))) := by
  split_ifs with h
  · have h1 : exp (lam * a) ≤ exp (lam * |L|) := exp_le_exp.2 (mul_le_mul_of_nonneg_left h hlam)
    have h2 : exp (lam * |L|) ≤ exp (lam * L) + exp (-(lam * L)) := by
      rcases abs_choice L with hL | hL <;> rw [hL]
      · linarith [exp_pos (-(lam * L))]
      · rw [mul_neg]; linarith [exp_pos (lam * L)]
    rw [exp_neg]
    rw [← div_eq_inv_mul, le_div_iff₀ (exp_pos _), one_mul]
    linarith
  · positivity

/-- **The Chernoff bound for a signed subset sum, as a count**: the seeds with
`a ≤ |∑_j c_j w_j|` number at most `2 e^{−λa} · 2^n · e_τ(cosh(λ w))`. -/
theorem card_le_abs_signedSum_le {n τ : ℕ} (w : Fin n → ℝ) (a : ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    (∑ ω : ChallengeSeed n τ, if a ≤ |∑ j, (ω.coeff j : ℝ) * w j| then (1 : ℝ) else 0) ≤
      2 * exp (-(lam * a)) *
        (2 ^ n * subsetProdSum univ (fun j => cosh (lam * w j)) τ) := by
  refine (sum_le_sum fun ω _ => indicator_le_exp_add_exp (L := ∑ j, (ω.coeff j : ℝ) * w j)
    (a := a) hlam).trans_eq ?_
  have hS : ∀ S : Finset (Fin n), (∑ ε : Fin n → Bool,
      (exp (lam * ∑ j, (signedCoeff S ε j : ℝ) * w j) +
        exp (-(lam * ∑ j, (signedCoeff S ε j : ℝ) * w j)))) =
      2 * (2 ^ n * ∏ j ∈ S, cosh (lam * w j)) := fun S => by
    have h2 := sum_signs_exp S w (-lam)
    simp only [neg_mul, cosh_neg] at h2
    rw [sum_add_distrib, sum_signs_exp, h2]
    ring
  rw [← mul_sum, Fintype.sum_prod_type]
  simp only [ChallengeSeed.coeff]
  simp_rw [hS]
  rw [Finset.sum_coe_sort (univ.powersetCard τ)
    (fun S => 2 * (2 ^ n * ∏ j ∈ S, cosh (lam * w j))), subsetProdSum, ← mul_sum, ← mul_sum]
  ring

/-- **The Chernoff bound for a signed subset sum** (via Hoeffding's comparison for sampling
without replacement): for a uniform seed and `λ ≥ 0`,
`Pr[a ≤ |∑_{j ∈ S} s_j w_j|] ≤ 2 e^{−λa} (mean_j cosh(λ w_j))^τ`. -/
theorem prob_le_abs_signedSum_le {n τ : ℕ} (w : Fin n → ℝ) (a : ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    probUnif (fun ω : ChallengeSeed n τ => a ≤ |∑ j, (ω.coeff j : ℝ) * w j|) ≤
      2 * exp (-(lam * a)) * ((∑ j, cosh (lam * w j)) / n) ^ τ := by
  rw [probUnif_eq_sum, card_challengeSeed]
  have hB : 0 ≤ 2 * exp (-(lam * a)) * ((∑ j, cosh (lam * w j)) / n) ^ τ := by
    have : 0 ≤ ∑ j, cosh (lam * w j) := sum_nonneg fun j _ => (cosh_pos _).le
    positivity
  rcases Nat.eq_zero_or_pos (n.choose τ) with h0 | hpos
  · simp [h0, hB]
  rw [div_le_iff₀ (by positivity)]
  refine (card_le_abs_signedSum_le w a hlam).trans ?_
  have hM := subsetProdSum_le (s := (univ : Finset (Fin n))) (a := fun j => cosh (lam * w j))
    (fun j _ => (cosh_pos _).le) τ
  rw [card_univ, Fintype.card_fin] at hM
  have : 0 ≤ 2 * exp (-(lam * a)) * 2 ^ n := by positivity
  calc 2 * exp (-(lam * a)) * (2 ^ n * subsetProdSum univ (fun j => cosh (lam * w j)) τ)
      = (2 * exp (-(lam * a)) * 2 ^ n) * subsetProdSum univ (fun j => cosh (lam * w j)) τ := by
        ring
    _ ≤ (2 * exp (-(lam * a)) * 2 ^ n) *
          ((n.choose τ : ℝ) * ((∑ j, cosh (lam * w j)) / n) ^ τ) :=
        mul_le_mul_of_nonneg_left hM this
    _ = _ := by push_cast; ring

/-- **The chord bound for `cosh`**: `cosh y ≤ 1 + (y / Y)^2 (cosh Y − 1)` for `|y| ≤ Y`
(convexity of `u ↦ cosh(√u)`, termwise on the power series). -/
theorem cosh_le_one_add_sq_mul {y Y : ℝ} (hY : 0 < Y) (hy : |y| ≤ Y) :
    cosh y ≤ 1 + (y / Y) ^ 2 * (cosh Y - 1) := by
  have hexp : ∀ x : ℝ, HasSum (fun n => x ^ n / (n.factorial : ℝ)) (exp x) := fun x => by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp x
  have hcosh : ∀ x : ℝ,
      HasSum (fun n => (x ^ n + (-x) ^ n) / (2 * n.factorial)) (cosh x) := fun x => by
    rw [cosh_eq]
    convert ((hexp x).add (hexp (-x))).div_const 2 using 1
    funext n
    field_simp
  set r := (y / Y) ^ 2
  have hR : HasSum (fun n : ℕ => (if n = 0 then 1 - r else 0) +
      r * ((Y ^ n + (-Y) ^ n) / (2 * n.factorial))) ((1 - r) + r * cosh Y) :=
    (hasSum_ite_eq 0 (1 - r)).add ((hcosh Y).mul_left r)
  have hyY : y ^ 2 ≤ Y ^ 2 := sq_le_sq.2 (by rwa [abs_of_pos hY])
  have hle := hasSum_le (fun n => ?_) (hcosh y) hR
  · linarith
  rcases n with _ | m
  · simp
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, zero_add]
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rcases Nat.even_or_odd (m + 1) with ⟨k, hk⟩ | ho
    · rw [Even.neg_pow ⟨k, hk⟩, Even.neg_pow ⟨k, hk⟩]
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have e1 : y ^ (m + 1) = y ^ 2 * (y ^ 2) ^ j := by rw [hk]; ring
      have e2 : r * (Y ^ (m + 1) + Y ^ (m + 1)) = 2 * (y ^ 2 * (Y ^ 2) ^ j) := by
        rw [hk]; simp only [r]; field_simp; ring
      rw [e2, e1]
      have h1 : (y ^ 2) ^ j ≤ (Y ^ 2) ^ j := pow_le_pow_left₀ (sq_nonneg y) hyY j
      nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg y)]
    · rw [Odd.neg_pow ho, Odd.neg_pow ho]
      simp

/-- **The closed form for the mean of `cosh`**: for `|w_j| ≤ M` and `λ ≥ 0`,
`mean_j cosh(λ w_j) ≤ 1 + (mean_j w_j² / M²)(cosh(λ M) − 1)`. -/
theorem mean_cosh_le {n : ℕ} (w : Fin n → ℝ) {M lam : ℝ} (hM : 0 < M) (hlam : 0 ≤ lam)
    (hw : ∀ j, |w j| ≤ M) :
    (∑ j, cosh (lam * w j)) / n ≤ 1 + ((∑ j, w j ^ 2) / n / M ^ 2) * (cosh (lam * M) - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rcases hlam.eq_or_lt with rfl | hlam
  · simp [div_self hnR.ne']
  have hj : ∀ j, cosh (lam * w j) ≤ 1 + (w j / M) ^ 2 * (cosh (lam * M) - 1) := fun j => by
    have := cosh_le_one_add_sq_mul (y := lam * w j) (Y := lam * M) (by positivity)
      (by rw [abs_mul, abs_of_pos hlam]; exact mul_le_mul_of_nonneg_left (hw j) hlam.le)
    rwa [mul_div_mul_left _ _ hlam.ne'] at this
  rw [div_le_iff₀ hnR]
  refine (sum_le_sum fun j _ => hj j).trans_eq ?_
  rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← sum_mul]
  simp_rw [div_pow, ← sum_div]
  field_simp

/-! ### The coefficients of `c · t` -/

/-- The weight of `c_j` in the coefficient `k` of the negacyclic product `c · t`: `t_{k−j}`, with
the sign `−1` when the index wraps (`X^n = −1`). -/
def negacyclicWeight {n : ℕ} (t : Fin n → ℤ) (k j : Fin n) : ℤ :=
  if j ≤ k then t (k - j) else -t (k - j)

/-- **Each coefficient of `c · t` is a signed sum of the entries of `t`**:
`(c · t)_k = ∑_j c_j · negacyclicWeight t k j`. -/
theorem negacyclicConvCoeff_eq_sum_weight {n : ℕ} (c t : Fin n → ℤ) (k : Fin n) :
    LatticeCrypto.negacyclicConvCoeff c t k = ∑ j, c j * negacyclicWeight t k j := by
  rw [DFT.negacyclicConvCoeff_eq_sum]
  refine sum_congr rfl fun j _ => ?_
  unfold negacyclicWeight
  split_ifs <;> ring

/-- `cosh` of the weights of one coefficient sums to `cosh` of the entries of `t`: the weights
are the entries of `t`, permuted and signed. -/
theorem sum_cosh_negacyclicWeight {n : ℕ} [NeZero n] (t : Fin n → ℤ) (k : Fin n) (lam : ℝ) :
    ∑ j, cosh (lam * (negacyclicWeight t k j : ℝ)) = ∑ i, cosh (lam * (t i : ℝ)) := by
  have hj : ∀ j, cosh (lam * (negacyclicWeight t k j : ℝ)) = cosh (lam * (t (k - j) : ℝ)) :=
    fun j => by
      unfold negacyclicWeight
      split_ifs
      · rfl
      · push_cast; rw [mul_neg, cosh_neg]
  simp_rw [hj]
  exact Fintype.sum_equiv (Equiv.subLeft k) _ _ fun j => rfl

/-! ### The floor for a fixed key -/

/-- **The floor event**: some coefficient of `c · t_m` has absolute value at least `γ₂`, for a key
`t : Fin K → Fin n → ℤ` (the centered `t₀` of FIPS 204, one polynomial per row). The signer
rejects these challenges at line 28 of Algorithm 7. -/
def FloorEvent {K n : ℕ} (γ₂ : ℤ) (t : Fin K → Fin n → ℤ) (c : Fin n → ℤ) : Prop :=
  ∃ mk : Fin K × Fin n, γ₂ ≤ |LatticeCrypto.negacyclicConvCoeff c (t mk.1) mk.2|

instance {K n : ℕ} (γ₂ : ℤ) (t : Fin K → Fin n → ℤ) : DecidablePred (FloorEvent γ₂ t) :=
  fun _ => by unfold FloorEvent; infer_instance

/-- The floor event at one coefficient, read in `ℝ` as a signed subset sum. -/
theorem floorCoord_iff {n τ : ℕ} (γ₂ : ℤ) (t : Fin n → ℤ) (k : Fin n) (ω : ChallengeSeed n τ) :
    γ₂ ≤ |LatticeCrypto.negacyclicConvCoeff ω.coeff t k| ↔
      (γ₂ : ℝ) ≤ |∑ j, (ω.coeff j : ℝ) * (negacyclicWeight t k j : ℝ)| := by
  rw [negacyclicConvCoeff_eq_sum_weight]
  have : ((∑ j, ω.coeff j * negacyclicWeight t k j : ℤ) : ℝ) =
      ∑ j, (ω.coeff j : ℝ) * (negacyclicWeight t k j : ℝ) := by push_cast; rfl
  rw [← this, ← Int.cast_abs, Int.cast_le]

/-- **The floor probability for a fixed key**: for a uniform challenge and `λ ≥ 0`,
`p(t) ≤ ∑_m n · 2 e^{−λγ₂} (mean_i cosh(λ t_{m,i}))^τ`. With `mean_cosh_le` this is in terms of
`max |t| ≤ M` and the mean squares of the rows of `t`. -/
theorem floorProb_le {K n τ : ℕ} [NeZero n] (γ₂ : ℤ) (t : Fin K → Fin n → ℤ) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    probUnif (fun ω : ChallengeSeed n τ => FloorEvent γ₂ t ω.coeff) ≤
      ∑ m, n * (2 * exp (-(lam * γ₂)) * ((∑ i, cosh (lam * (t m i : ℝ))) / n) ^ τ) := by
  refine (probUnif_exists_le (fun (mk : Fin K × Fin n) (ω : ChallengeSeed n τ) =>
    γ₂ ≤ |LatticeCrypto.negacyclicConvCoeff ω.coeff (t mk.1) mk.2|)).trans ?_
  rw [Fintype.sum_prod_type]
  refine sum_le_sum fun m _ => ?_
  have hk : ∀ k, probUnif (fun ω : ChallengeSeed n τ =>
      γ₂ ≤ |LatticeCrypto.negacyclicConvCoeff ω.coeff (t m) k|) ≤
      2 * exp (-(lam * γ₂)) * ((∑ i, cosh (lam * (t m i : ℝ))) / n) ^ τ := fun k => by
    simp_rw [floorCoord_iff]
    refine (prob_le_abs_signedSum_le _ _ hlam).trans_eq ?_
    rw [sum_cosh_negacyclicWeight]
  refine (sum_le_sum fun k _ => hk k).trans_eq ?_
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### The floor averaged over a key with independent uniform coordinates -/

/-- **Summing a function of one row**: if `∑_y F y ≤ #Y · B`, then summing `F (t m)` over all
`t : ι → Y` gives at most `#(ι → Y) · B`. -/
theorem sum_apply_le {ι Y : Type*} [Fintype ι] [DecidableEq ι] [Fintype Y] (m : ι) (F : Y → ℝ)
    {B : ℝ} (hF : ∑ y, F y ≤ Fintype.card Y * B) :
    ∑ t : ι → Y, F (t m) ≤ Fintype.card (ι → Y) * B := by
  let e := Equiv.piSplitAt m (fun _ : ι => Y)
  rw [Fintype.sum_equiv e (fun t => F (t m)) (fun p => F p.1) (fun _ => rfl),
    Fintype.sum_prod_type, Fintype.card_congr e, Fintype.card_prod]
  simp only [sum_const, card_univ, nsmul_eq_mul, ← mul_sum]
  push_cast
  rw [mul_comm (Fintype.card Y : ℝ), mul_assoc]
  exact mul_le_mul_of_nonneg_left hF (by positivity)

/-- **The exponential moment of a signed sum of independent coordinates**: for `u` uniform on
`Fin n → X`, signs `σ_i ∈ {−1, 0, 1}` and `E e^{±λ v(x)} ≤ A`,
`E_u exp(λ ∑_i σ_i v(u_i)) ≤ A^{#{i | σ_i ≠ 0}}`, written as sums. -/
theorem sum_exp_signed_le {n : ℕ} {X : Type*} [Fintype X] (v : X → ℤ) {lam A : ℝ}
    (hA1 : ∑ x, exp (lam * v x) ≤ Fintype.card X * A)
    (hA2 : ∑ x, exp (-(lam * v x)) ≤ Fintype.card X * A)
    (σ : Fin n → ℤ) (hσ : ∀ i, σ i = 0 ∨ σ i = 1 ∨ σ i = -1) :
    ∑ u : Fin n → X, exp (lam * ∑ i, (σ i : ℝ) * v (u i)) ≤
      Fintype.card (Fin n → X) * A ^ (univ.filter fun i => σ i ≠ 0).card := by
  let g : Fin n → X → ℝ := fun i x => exp (lam * ((σ i : ℝ) * v x))
  have hexp : ∀ u : Fin n → X, exp (lam * ∑ i, (σ i : ℝ) * v (u i)) = ∏ i, g i (u i) :=
    fun u => by rw [mul_sum, exp_sum]
  rw [Fintype.sum_congr _ _ hexp, ← Fintype.prod_sum g]
  have hi : ∀ i, ∑ x, g i x ≤ Fintype.card X * (if σ i ≠ 0 then A else 1) := fun i => by
    rcases hσ i with h | h | h
    · simp [g, h]
    · have : ∀ x, g i x = exp (lam * v x) := fun x => by simp [g, h]
      simpa [this, h] using hA1
    · have : ∀ x, g i x = exp (-(lam * v x)) := fun x => by simp [g, h]
      simpa [this, h] using hA2
  calc ∏ i, ∑ x, g i x ≤ ∏ i, ((Fintype.card X : ℝ) * (if σ i ≠ 0 then A else 1)) :=
        by gcongr with i; exact hi i
    _ = _ := by
        rw [prod_mul_distrib, prod_const, prod_ite, prod_const, prod_const_one, mul_one,
          card_univ, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin]
        push_cast
        rfl

/-- The weight sum of one coefficient, reindexed by the entries of the key row:
`∑_j c_j · negacyclicWeight t k j = ∑_i σ_i t_i` with `σ_i = ±c_{k−i}`. -/
theorem sum_mul_negacyclicWeight {n : ℕ} [NeZero n] (c t : Fin n → ℤ) (k : Fin n) :
    ∑ j, (c j : ℝ) * (negacyclicWeight t k j : ℝ) =
      ∑ i, ((if k - i ≤ k then c (k - i) else -c (k - i) : ℤ) : ℝ) * (t i : ℝ) := by
  refine (Fintype.sum_equiv (Equiv.subLeft k) _ _ fun j => ?_)
  simp only [Equiv.subLeft_apply, negacyclicWeight, sub_sub_cancel]
  split_ifs <;> push_cast <;> ring

/-- A seed's challenge has exactly `τ` nonzero coefficients. -/
theorem card_coeff_ne_zero {n τ : ℕ} (ω : ChallengeSeed n τ) :
    (univ.filter fun j => ω.coeff j ≠ 0).card = τ := by
  have : (univ.filter fun j => ω.coeff j ≠ 0) = ω.1.1 := by
    ext j
    by_cases h1 : j ∈ ω.1.1 <;> by_cases h2 : ω.2 j <;>
      simp [ChallengeSeed.coeff, signedCoeff, h1, h2]
  rw [this]
  exact (mem_powersetCard.1 ω.1.2).2

/-- A seed's challenge has coefficients in `{−1, 0, 1}`. -/
theorem coeff_mem {n τ : ℕ} (ω : ChallengeSeed n τ) (j : Fin n) :
    ω.coeff j = 0 ∨ ω.coeff j = 1 ∨ ω.coeff j = -1 := by
  simp only [ChallengeSeed.coeff, signedCoeff]
  split_ifs <;> simp

/-- **One coefficient, averaged over the key**: for a seed `ω`, a key `t` uniform on
`Fin K → Fin n → X` read through `v`, and `s = ±1`,
`E_t exp(s λ (c · t_m)_k) ≤ A^τ`, written as sums. -/
theorem sum_key_exp_coord_le {K n τ : ℕ} [NeZero n] {X : Type*} [Fintype X] (v : X → ℤ)
    {lam A : ℝ} (hA1 : ∑ x, exp (lam * v x) ≤ Fintype.card X * A)
    (hA2 : ∑ x, exp (-(lam * v x)) ≤ Fintype.card X * A) (ω : ChallengeSeed n τ) (m : Fin K)
    (k : Fin n) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    ∑ t : Fin K → Fin n → X, exp ((s : ℝ) * (lam * ∑ j, (ω.coeff j : ℝ) *
      (negacyclicWeight (fun i => v (t m i)) k j : ℝ))) ≤
      Fintype.card (Fin K → Fin n → X) * A ^ τ := by
  refine sum_apply_le m (fun u : Fin n → X => exp ((s : ℝ) * (lam * ∑ j, (ω.coeff j : ℝ) *
    (negacyclicWeight (fun i => v (u i)) k j : ℝ)))) ?_
  let σ : Fin n → ℤ := fun i => s * (if k - i ≤ k then ω.coeff (k - i) else -ω.coeff (k - i))
  have hσ : ∀ i, σ i = 0 ∨ σ i = 1 ∨ σ i = -1 := fun i => by
    simp only [σ]
    rcases coeff_mem ω (k - i) with h | h | h <;> rcases hs with rfl | rfl <;>
      split_ifs <;> simp [h]
  have hcard : (univ.filter fun i => σ i ≠ 0).card = τ := by
    rw [← card_coeff_ne_zero ω]
    refine card_equiv (Equiv.subLeft k) fun i => ?_
    simp only [mem_filter, mem_univ, true_and, Equiv.subLeft_apply, σ]
    have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
    split_ifs <;> simp [hs0]
  have hsum : ∀ u : Fin n → X, exp ((s : ℝ) * (lam * ∑ j, (ω.coeff j : ℝ) *
      (negacyclicWeight (fun i => v (u i)) k j : ℝ))) =
      exp (lam * ∑ i, (σ i : ℝ) * v (u i)) := fun u => by
    rw [sum_mul_negacyclicWeight]
    congr 1
    simp only [σ, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    push_cast
    ring
  rw [Fintype.sum_congr _ _ hsum, ← hcard]
  exact sum_exp_signed_le v hA1 hA2 σ hσ

/-- **The floor probability averaged over the key**: for a key with independent coordinates
`v(x)`, `x` uniform on `X`, whose exponential moments `E e^{±λ v(x)}` are at most `A`, and
`λ ≥ 0`, the sum over keys of `p(t)` is at most `#keys · K n · 2 e^{−λγ₂} A^τ`: the average floor
probability is at most `K n · 2 e^{−λγ₂} A^τ`. -/
theorem sum_floorProb_le {K n τ : ℕ} [NeZero n] [Nonempty (ChallengeSeed n τ)] {X : Type*}
    [Fintype X] (v : X → ℤ) (γ₂ : ℤ) {lam A : ℝ} (hlam : 0 ≤ lam)
    (hA1 : ∑ x, exp (lam * v x) ≤ Fintype.card X * A)
    (hA2 : ∑ x, exp (-(lam * v x)) ≤ Fintype.card X * A) :
    ∑ t : Fin K → Fin n → X,
        probUnif (fun ω : ChallengeSeed n τ => FloorEvent γ₂ (fun m i => v (t m i)) ω.coeff) ≤
      Fintype.card (Fin K → Fin n → X) * (K * n * (2 * exp (-(lam * γ₂)) * A ^ τ)) := by
  simp only [probUnif_eq_sum, ← sum_div]
  have hΩ : (0 : ℝ) < Fintype.card (ChallengeSeed n τ) := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hΩ, sum_comm]
  have hω : ∀ ω : ChallengeSeed n τ, (∑ t : Fin K → Fin n → X,
      if FloorEvent γ₂ (fun m i => v (t m i)) ω.coeff then (1 : ℝ) else 0) ≤
      Fintype.card (Fin K → Fin n → X) * (K * n * (2 * exp (-(lam * γ₂)) * A ^ τ)) := by
    intro ω
    have hcoord : ∀ mk : Fin K × Fin n, (∑ t : Fin K → Fin n → X,
        if (γ₂ : ℝ) ≤ |∑ j, (ω.coeff j : ℝ) * (negacyclicWeight (fun i => v (t mk.1 i)) mk.2 j : ℝ)|
          then (1 : ℝ) else 0) ≤
        Fintype.card (Fin K → Fin n → X) * (2 * exp (-(lam * γ₂)) * A ^ τ) := fun mk => by
      refine (sum_le_sum fun t _ => indicator_le_exp_add_exp hlam).trans ?_
      rw [← mul_sum, sum_add_distrib]
      have h1 := sum_key_exp_coord_le (K := K) v hA1 hA2 ω mk.1 mk.2 (s := 1) (by norm_num)
      have h2 := sum_key_exp_coord_le (K := K) v hA1 hA2 ω mk.1 mk.2 (s := -1) (by norm_num)
      simp only [Int.cast_one, one_mul, Int.cast_neg, neg_mul] at h1 h2
      have he : 0 ≤ exp (-(lam * γ₂)) := (exp_pos _).le
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add h1 h2) he]
    calc (∑ t : Fin K → Fin n → X,
          if FloorEvent γ₂ (fun m i => v (t m i)) ω.coeff then (1 : ℝ) else 0)
        ≤ ∑ t : Fin K → Fin n → X, ∑ mk : Fin K × Fin n,
            if (γ₂ : ℝ) ≤ |∑ j, (ω.coeff j : ℝ) *
              (negacyclicWeight (fun i => v (t mk.1 i)) mk.2 j : ℝ)| then (1 : ℝ) else 0 := by
          refine sum_le_sum fun t _ => ?_
          split_ifs with h
          · obtain ⟨mk, hmk⟩ := h
            rw [floorCoord_iff] at hmk
            exact (single_le_sum (f := fun mk : Fin K × Fin n =>
              if (γ₂ : ℝ) ≤ |∑ j, (ω.coeff j : ℝ) *
                (negacyclicWeight (fun i => v (t mk.1 i)) mk.2 j : ℝ)| then (1 : ℝ) else 0)
              (fun _ _ => by split_ifs <;> norm_num) (mem_univ mk)).trans_eq' (by simp [hmk])
          · exact sum_nonneg fun _ _ => by split_ifs <;> norm_num
      _ = ∑ mk : Fin K × Fin n, ∑ t : Fin K → Fin n → X,
            if (γ₂ : ℝ) ≤ |∑ j, (ω.coeff j : ℝ) *
              (negacyclicWeight (fun i => v (t mk.1 i)) mk.2 j : ℝ)| then (1 : ℝ) else 0 :=
          sum_comm
      _ ≤ ∑ _mk : Fin K × Fin n,
            Fintype.card (Fin K → Fin n → X) * (2 * exp (-(lam * γ₂)) * A ^ τ) :=
          sum_le_sum fun mk _ => hcoord mk
      _ = _ := by
          rw [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          ring
  refine (sum_le_sum fun ω _ => hω ω).trans_eq ?_
  rw [sum_const, card_univ, nsmul_eq_mul]
  ring

/-! ### ML-DSA-44 -/

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA44 in
/-- At ML-DSA-44 (FIPS 204 Table 1), `τ = 39` and `γ₂ = (q − 1)/88 = 95232`. -/
theorem mldsa44_tau_gamma2 : mldsa44.tau = 39 ∧ mldsa44.gamma2 = 95232 := by
  simp only [mldsa44, ParameterSet.params, modulus]
  decide

/-- **A `t₀` coordinate**: `x ↦ x − 4095` maps `Fin 8192` onto `(−2^12, 2^12]`, the range of
Power2Round's low part with `d = 13` (FIPS 204 Algorithm 35). A uniform `x` models a `t₀`
coordinate uniform on that range. -/
def t0Coord (x : Fin 8192) : ℤ := (x : ℤ) - 4095

/-- **A geometric sum of exponentials**: `∑_{x < N} e^{λ (x − c)} ≤ (e^{λ (N − c)} − e^{−λ c}) / λ`
for `λ > 0`, from `e^λ − 1 ≥ λ`. -/
theorem sum_fin_exp_le (N : ℕ) (c : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    ∑ x : Fin N, exp (lam * ((x : ℝ) - c)) ≤ (exp (lam * (N - c)) - exp (-(lam * c))) / lam := by
  rw [Fin.sum_univ_eq_sum_range (fun i => exp (lam * ((i : ℝ) - c))) N]
  have h1 : ∀ i : ℕ, exp (lam * ((i : ℝ) - c)) = exp (-(lam * c)) * exp lam ^ i := fun i => by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    ring_nf
  simp_rw [h1]
  have hne : exp lam ≠ 1 := by have := Real.add_one_lt_exp hlam.ne'; linarith
  rw [← mul_sum, geom_sum_eq hne]
  have hl : lam ≤ exp lam - 1 := by linarith [Real.add_one_le_exp lam]
  have hnum : 0 ≤ exp lam ^ N - 1 := by
    have := one_le_pow₀ (n := N) (Real.one_le_exp hlam.le)
    linarith
  calc exp (-(lam * c)) * ((exp lam ^ N - 1) / (exp lam - 1))
      ≤ exp (-(lam * c)) * ((exp lam ^ N - 1) / lam) := by gcongr
    _ = (exp (-(lam * c)) * exp (N * lam) - exp (-(lam * c))) / lam := by
        rw [Real.exp_nat_mul]
        ring
    _ = _ := by
        rw [← Real.exp_nat_mul, ← Real.exp_add,
          show -(lam * c) + N * lam = lam * (N - c) by ring]

/-- `e^{77843/32768} ≤ 1.81105^4` (Taylor's bound at `77843/131072`, FIPS-free arithmetic). -/
theorem exp_upper_mldsa44 : exp (77843 / 32768 : ℝ) ≤ (181105 / 100000) ^ 4 := by
  have h := Real.exp_bound' (x := (77843 / 131072 : ℝ)) (by norm_num) (by norm_num)
    (n := 10) (by norm_num)
  have e : exp (77843 / 32768 : ℝ) = exp (77843 / 131072) ^ 4 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [e]
  gcongr
  refine h.trans ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- `1767/32 = λ γ₂` at `λ = 19/32768`, and `e^{1767/32} ≥ 5.61^32`. -/
theorem exp_lower_mldsa44 : (561 / 100 : ℝ) ^ 32 ≤ exp (1767 / 32) := by
  have h := Real.sum_le_exp_of_nonneg (x := (1767 / 1024 : ℝ)) (by norm_num) 14
  have e : exp (1767 / 32 : ℝ) = exp (1767 / 1024) ^ 32 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [e]
  gcongr
  refine le_trans ?_ h
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- `(U − 1/U)/λ ≤ 8192 A` for `e^{4097 λ} ≤ U`, the common bound behind both exponential
moments of `t0Coord`. -/
theorem mgf_aux_mldsa44 {a b : ℝ} (ha : a ≤ 77843 / 32768) (hb' : b ≤ 77843 / 32768) :
    (exp a - exp (-b)) / (19 / 32768) ≤ (8192 : ℝ) * (22455 / 10000) := by
  set U : ℝ := (181105 / 100000) ^ 4 with hUdef
  have hU : exp (77843 / 32768 : ℝ) ≤ U := exp_upper_mldsa44
  have hX : U - 1 / U ≤ (8192 : ℝ) * (22455 / 10000) * (19 / 32768) := by
    rw [hUdef]
    norm_num
  clear_value U
  have h1 : exp a ≤ U := (exp_le_exp.2 ha).trans hU
  have h2 : 1 / U ≤ exp (-b) := by
    rw [exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (exp_pos b) ((exp_le_exp.2 hb').trans hU)
  rw [div_le_iff₀ (by norm_num)]
  linarith

/-- **The exponential moments of a `t₀` coordinate** at `λ = 19/32768`: both
`E e^{λ x}` and `E e^{−λ x}`, `x` uniform on `(−2^12, 2^12]`, are at most `2.2455`. -/
theorem t0Coord_mgf_le :
    (∑ x, exp ((19 / 32768 : ℝ) * t0Coord x) ≤ Fintype.card (Fin 8192) * (22455 / 10000)) ∧
      ∑ x, exp (-((19 / 32768 : ℝ) * t0Coord x)) ≤ Fintype.card (Fin 8192) * (22455 / 10000) := by
  have hlam : (0 : ℝ) < 19 / 32768 := by norm_num
  rw [Fintype.card_fin]
  push_cast
  constructor
  · have h := sum_fin_exp_le 8192 4095 hlam
    simp only [t0Coord]
    push_cast
    refine h.trans ?_
    exact mgf_aux_mldsa44 (by norm_num) (by norm_num)
  · have hrev : ∑ x : Fin 8192, exp (-((19 / 32768 : ℝ) * ((x : ℤ) - 4095 : ℤ))) =
        ∑ x : Fin 8192, exp ((19 / 32768 : ℝ) * ((x : ℝ) - 4096)) := by
      refine Fintype.sum_equiv Fin.revPerm _ _ fun x => ?_
      rw [Fin.revPerm_apply, Fin.val_rev]
      have hx := x.isLt
      have hc : ((8191 - (x : ℕ) : ℕ) : ℝ) = 8191 - (x : ℝ) := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      congr 1
      push_cast
      rw [hc]
      ring
    simp only [t0Coord]
    rw [hrev]
    refine (sum_fin_exp_le 8192 4096 hlam).trans ?_
    exact mgf_aux_mldsa44 (by norm_num) (by norm_num)

instance : Nonempty (ChallengeSeed 256 39) := by
  obtain ⟨S, -, hS⟩ := exists_subset_card_eq (s := (univ : Finset (Fin 256))) (n := 39)
    (by simp)
  exact ⟨(⟨S, mem_powersetCard.2 ⟨subset_univ S, hS⟩⟩, fun _ => true)⟩

/-- **The constant of the averaged ML-DSA-44 floor bound**:
`K n · 2 e^{−λγ₂} A^τ ≤ 2^−23` at `K = 4`, `n = 256`, `τ = 39`, `γ₂ = 95232`, `λ = 19/32768`,
`A = 2.2455`. -/
theorem floorConst_mldsa44_le :
    ((4 : ℕ) : ℝ) * ((256 : ℕ) : ℝ) *
        (2 * exp (-((19 / 32768 : ℝ) * ((95232 : ℤ) : ℝ))) * (22455 / 10000) ^ 39) ≤
      1 / 2 ^ 23 := by
  have hl : (19 / 32768 : ℝ) * ((95232 : ℤ) : ℝ) = 1767 / 32 := by norm_num
  rw [hl, exp_neg]
  have hpos : (0 : ℝ) < (561 / 100) ^ 32 := by positivity
  have hinv : (exp (1767 / 32))⁻¹ ≤ ((561 / 100 : ℝ) ^ 32)⁻¹ := inv_anti₀ hpos exp_lower_mldsa44
  calc ((4 : ℕ) : ℝ) * ((256 : ℕ) : ℝ) * (2 * (exp (1767 / 32))⁻¹ * (22455 / 10000) ^ 39)
      ≤ ((4 : ℕ) : ℝ) * ((256 : ℕ) : ℝ) * (2 * ((561 / 100 : ℝ) ^ 32)⁻¹ * (22455 / 10000) ^ 39) := by
        gcongr
    _ ≤ 1 / 2 ^ 23 := by norm_num

/-- **The floor probability at ML-DSA-44, averaged over the key**: for `t₀` with independent
coordinates uniform on `(−2^12, 2^12]` (`K = 4` rows of `n = 256`) and a uniform challenge of
weight `τ = 39`, the average over keys of `p(t₀) = Pr_c[‖c · t₀‖∞ ≥ γ₂ = 95232]` is at most
`2^−23` (`sum_floorProb_le` at `λ = 19/32768`, `A = 2.2455`). -/
theorem floorProb_mldsa44_avg_le :
    (∑ t : Fin 4 → Fin 256 → Fin 8192, probUnif (fun ω : ChallengeSeed 256 39 =>
        FloorEvent 95232 (fun m i => t0Coord (t m i)) ω.coeff)) /
      Fintype.card (Fin 4 → Fin 256 → Fin 8192) ≤ 1 / 2 ^ 23 := by
  have h := sum_floorProb_le (K := 4) (n := 256) (τ := 39) t0Coord 95232
    (lam := 19 / 32768) (A := 22455 / 10000) (by norm_num) t0Coord_mgf_le.1 t0Coord_mgf_le.2
  have hT : (0 : ℝ) < Fintype.card (Fin 4 → Fin 256 → Fin 8192) := by
    exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hT]
  refine h.trans ?_
  rw [mul_comm]
  gcongr
  exact floorConst_mldsa44_le

section Signer

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA44 LatticeCrypto TransformOps


/-- A ring homomorphism commutes with `negacyclicConvCoeff`. -/
theorem map_negacyclicConvCoeff {R S : Type*} [Ring R] [Ring S] (φ : R →+* S) {n : ℕ}
    (f g : Fin n → R) (k : Fin n) :
    φ (negacyclicConvCoeff f g k) = negacyclicConvCoeff (fun i => φ (f i)) (fun i => φ (g i)) k := by
  simp only [negacyclicConvCoeff, map_sum]
  refine sum_congr rfl fun ij _ => ?_
  split_ifs <;> simp

/-- **The size of a coefficient of `c · t`** for `c` with at most `τ` nonzero coefficients, each
in `[−1, 1]`, and `|t_i| ≤ B`: at most `τ B`. -/
theorem abs_negacyclicConvCoeff_le {n τ B : ℕ} (c t : Fin n → ℤ) (hc : ∀ j, |c j| ≤ 1)
    (hcw : (univ.filter fun j => c j ≠ 0).card ≤ τ) (ht : ∀ i, |t i| ≤ B) (k : Fin n) :
    |negacyclicConvCoeff c t k| ≤ τ * B := by
  rw [negacyclicConvCoeff_eq_sum_weight]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hw : ∀ j, |negacyclicWeight t k j| ≤ B := fun j => by
    unfold negacyclicWeight
    split_ifs
    · exact ht _
    · rw [abs_neg]; exact ht _
  calc ∑ j, |c j * negacyclicWeight t k j|
      ≤ ∑ j, if c j ≠ 0 then (B : ℤ) else 0 := sum_le_sum fun j _ => by
        split_ifs with h
        · rw [abs_mul]
          nlinarith [hc j, hw j, abs_nonneg (c j), abs_nonneg (negacyclicWeight t k j)]
        · simp [not_not.1 h]
    _ = ((univ.filter fun j => c j ≠ 0).card : ℤ) * B := by
        rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ τ * B := by gcongr

/-- The centered integer coefficients of a polynomial of `R_q`. -/
def centeredPoly (f : Rq) : Fin ringDegree → ℤ := fun i => centeredRepr (f.get i)

/-- The centered integer coefficients of a vector over `R_q`, one row per component. -/
def centeredVec {k : ℕ} (v : RqVec k) : Fin k → Fin ringDegree → ℤ :=
  fun m => centeredPoly (v.get m)

/-- `‖f‖∞ ≤ B` bounds every centered coefficient of `f`. -/
theorem abs_centeredPoly_le {f : Rq} {B : ℕ} (hf : polyNorm f ≤ B) (i : Fin ringDegree) :
    |centeredPoly f i| ≤ B := by
  have h := LatticeCrypto.coeff_le_cInfNorm f i
  rw [← polyNorm_eq_cInfNorm] at h
  unfold centeredPoly
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h.trans hf

/-- A coefficient is zero exactly when its centered representative is. -/
theorem centeredPoly_ne_zero_iff (f : Rq) (i : Fin ringDegree) :
    centeredPoly f i ≠ 0 ↔ f.get i ≠ 0 := by
  simp [centeredPoly, centeredRepr, ZMod.valMinAbs_eq_zero]

/-- **The coefficients of `c · t` in `R_q` are the integer negacyclic convolution of the centered
coefficients** when no coefficient wraps mod `q`: for `c` with at most `τ` nonzero coefficients of
norm at most `1`, `‖t‖∞ ≤ B` and `2τB < q`. -/
theorem centeredPoly_mul {τ B : ℕ} (c t : Rq) (hc1 : polyNorm c ≤ 1)
    (hcw : (univ.filter fun i : Fin ringDegree => c.get i ≠ 0).card ≤ τ) (ht : polyNorm t ≤ B)
    (hq : 2 * (τ * B) < modulus) :
    centeredPoly (c * t) = negacyclicConvCoeff (centeredPoly c) (centeredPoly t) := by
  funext k
  have hmul : (c * t).get k = negacyclicConvCoeff c.get t.get k := by
    rw [vectorRing_mul_apply]
    exact vectorKernel_mul_get c t k
  have hcast : ∀ f : Rq, f.get = fun i => ((centeredPoly f i : ℤ) : Coeff) := fun f => by
    funext i
    exact centeredRepr_intCast (f.get i)
  have hbound := abs_negacyclicConvCoeff_le (τ := τ) (B := B) (centeredPoly c) (centeredPoly t)
    (fun j => by exact_mod_cast abs_centeredPoly_le hc1 j)
    (by simpa only [centeredPoly_ne_zero_iff] using hcw) (abs_centeredPoly_le ht) k
  have hmap := map_negacyclicConvCoeff (Int.castRingHom Coeff) (centeredPoly c) (centeredPoly t) k
  simp only [eq_intCast] at hmap
  rw [centeredPoly, hmul, hcast c, hcast t, ← hmap]
  refine centeredRepr_intCast_eq_of_natAbs_le _ (b := τ * B) ?_ hq
  rw [Int.abs_eq_natAbs] at hbound
  exact_mod_cast hbound


/-- **The ct₀-check rejects exactly on the floor event.** For a challenge `c` with at most `τ`
nonzero coefficients of norm at most `1`, `‖t₀‖∞ ≤ B` and `2τB < q`, the check
`‖c • t₀‖∞ < γ₂` of FIPS 204 Algorithm 7 line 28 fails exactly when `FloorEvent γ₂` holds for the
centered coefficients of `t₀` and `c`. -/
theorem ct0Check_eq_false_iff {p : Params} [nttOps : NTTRingOps] [NTTRingLaws nttOps] {τ B : ℕ}
    (c : Rq) (t0 : RqVec p.k) (hc1 : polyNorm c ≤ 1)
    (hcw : (univ.filter fun i : Fin ringDegree => c.get i ≠ 0).card ≤ τ)
    (ht0 : polyVecNorm t0 ≤ B) (hq : 2 * (τ * B) < modulus) (hγ : 0 < p.gamma2) :
    ct0Check (c • t0) = false ↔ FloorEvent (p.gamma2 : ℤ) (centeredVec t0) (centeredPoly c) := by
  have hrow : ∀ m, polyNorm (t0.get m) ≤ B := fun m =>
    (LatticeCrypto.PolyVec.component_cInfNorm_le normOps t0 m).trans ht0
  have hget : ∀ m i, centeredRepr (((c • t0).get m).get i) =
      negacyclicConvCoeff (centeredPoly c) (centeredVec t0 m) i := fun m i => by
    rw [smul_eq_coeffScalarVecMul, LatticeCrypto.TransformOps.coeffScalarVecMul_get]
    exact congrFun (centeredPoly_mul c (t0.get m) hc1 hcw (hrow m) hq) i
  rw [ct0Check, decide_eq_false_iff_not, polyVecNorm_lt_iff _ hγ, FloorEvent]
  push Not
  simp only [hget, Prod.exists]
  refine exists_congr fun m => exists_congr fun i => ?_
  rw [Int.abs_eq_natAbs]
  omega

/-- **The challenge ball**: a polynomial of `R_q` with exactly `τ` nonzero coefficients, each of
centered absolute value at most `1` (so `±1`). These are the outputs of SampleInBall (FIPS 204
Algorithm 29). -/
def IsChallenge (τ : ℕ) (c : Rq) : Prop :=
  polyNorm c ≤ 1 ∧ (univ.filter fun i : Fin ringDegree => c.get i ≠ 0).card = τ

instance (τ : ℕ) : DecidablePred (IsChallenge τ) := fun _ => by
  unfold IsChallenge; infer_instance

/-- The polynomial of `R_q` whose coefficients are the challenge of a seed. -/
def ChallengeSeed.poly {τ : ℕ} (ω : ChallengeSeed ringDegree τ) : Rq :=
  Vector.ofFn fun i => ((ω.coeff i : ℤ) : Coeff)

/-- The centered coefficients of a seed's polynomial are the seed's challenge. -/
theorem centeredPoly_seedPoly {τ : ℕ} (ω : ChallengeSeed ringDegree τ) :
    centeredPoly ω.poly = ω.coeff := by
  funext i
  simp only [centeredPoly, ChallengeSeed.poly, Vector.get_ofFn]
  refine centeredRepr_intCast_eq_of_natAbs_le _ (b := 1) ?_ (by decide)
  rcases coeff_mem ω i with h | h | h <;> simp [h]

/-- The sign vectors agreeing with `b` on `S` number `2^(n − #S)`. -/
theorem card_signs_eq_on {n : ℕ} (S : Finset (Fin n)) (b : Fin n → Bool) :
    (univ.filter fun ε : Fin n → Bool => ∀ j ∈ S, ε j = b j).card = 2 ^ (n - S.card) := by
  have h : (univ.filter fun ε : Fin n → Bool => ∀ j ∈ S, ε j = b j) =
      Fintype.piFinset fun j => if j ∈ S then {b j} else univ := by
    ext ε
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    refine ⟨fun h j => ?_, fun h j hj => ?_⟩
    · split_ifs with hj
      · exact mem_singleton.2 (h j hj)
      · exact mem_univ _
    · simpa [hj] using h j
  rw [h, Fintype.card_piFinset]
  have : ∀ j, (if j ∈ S then ({b j} : Finset Bool) else univ).card = if j ∈ S then 1 else 2 :=
    fun j => by split_ifs <;> simp
  simp_rw [this]
  rw [prod_ite, prod_const_one, one_mul, prod_const]
  congr 1
  rw [filter_not, card_sdiff_of_subset (filter_subset _ _), card_univ, Fintype.card_fin]
  simp

/-- **The seeds of one challenge**: a vector `w` with entries in `{−1, 0, 1}` and exactly `τ`
nonzero entries is the challenge of exactly `2^(n − τ)` seeds (the signs off the support are
free). -/
theorem card_seed_coeff_eq {n τ : ℕ} (w : Fin n → ℤ) (hw : ∀ j, w j = 0 ∨ w j = 1 ∨ w j = -1)
    (hcard : (univ.filter fun j => w j ≠ 0).card = τ) :
    (univ.filter fun ω : ChallengeSeed n τ => ω.coeff = w).card = 2 ^ (n - τ) := by
  set S0 := univ.filter fun j => w j ≠ 0 with hS0
  have hmem : S0 ∈ (univ : Finset (Fin n)).powersetCard τ :=
    mem_powersetCard.2 ⟨subset_univ _, hcard⟩
  have hiff : ∀ ω : ChallengeSeed n τ, ω.coeff = w ↔
      ω.1.1 = S0 ∧ ∀ j ∈ S0, ω.2 j = decide (w j = 1) := fun ω => by
    constructor
    · rintro rfl
      refine ⟨?_, fun j hj => ?_⟩
      · ext j
        by_cases h1 : j ∈ ω.1.1 <;> by_cases h2 : ω.2 j <;>
          simp [hS0, ChallengeSeed.coeff, signedCoeff, h1, h2]
      · have hj' : j ∈ ω.1.1 := by
          by_contra h1
          simp [hS0, ChallengeSeed.coeff, signedCoeff, h1] at hj
        by_cases h2 : ω.2 j <;> simp [ChallengeSeed.coeff, signedCoeff, hj', h2]
    · rintro ⟨hS, hε⟩
      funext j
      simp only [ChallengeSeed.coeff, signedCoeff, hS]
      by_cases hj : j ∈ S0
      · simp only [hj, ↓reduceIte, hε j hj]
        have : w j ≠ 0 := by simpa [hS0] using hj
        rcases hw j with h | h | h <;> simp_all
      · simp only [hj, ↓reduceIte]
        exact (by simpa [hS0] using hj : w j = 0).symm
  have hprod : (univ.filter fun ω : ChallengeSeed n τ => ω.coeff = w) =
      (univ.filter fun S : {S : Finset (Fin n) // S ∈ (univ : Finset (Fin n)).powersetCard τ} =>
        S.1 = S0) ×ˢ (univ.filter fun ε : Fin n → Bool => ∀ j ∈ S0, ε j = decide (w j = 1)) := by
    ext ω
    simp only [mem_filter, mem_univ, true_and, mem_product, hiff]
  rw [hprod, card_product, card_signs_eq_on, hcard]
  have h1 : (univ.filter fun S : {S : Finset (Fin n) // S ∈ (univ : Finset (Fin n)).powersetCard τ} =>
      S.1 = S0).card = 1 :=
    card_eq_one.2 ⟨⟨S0, hmem⟩, by ext S; simp [Subtype.ext_iff]⟩
  rw [h1, one_mul]

/-- A polynomial of `R_q` is determined by its centered coefficients. -/
theorem centeredPoly_injective : Function.Injective centeredPoly := fun f g h => by
  have hf : ∀ f : Rq, ∀ i, f.get i = ((centeredPoly f i : ℤ) : Coeff) := fun f i =>
    centeredRepr_intCast (f.get i)
  refine Vector.ext fun i hi => ?_
  have := hf f ⟨i, hi⟩
  rw [h, ← hf g] at this
  exact this

/-- A seed's polynomial lies in the challenge ball. -/
theorem isChallenge_seedPoly {τ : ℕ} (ω : ChallengeSeed ringDegree τ) :
    IsChallenge τ ω.poly := by
  refine ⟨?_, ?_⟩
  · rw [polyNorm_eq_cInfNorm, LatticeCrypto.cInfNorm_le_iff]
    intro i
    have h := congrFun (centeredPoly_seedPoly ω) i
    simp only [centeredPoly] at h
    rw [h]
    rcases coeff_mem ω i with h' | h' | h' <;> simp [h']
  · refine Eq.trans ?_ (card_coeff_ne_zero ω)
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, ← centeredPoly_ne_zero_iff,
      centeredPoly_seedPoly]

/-- **Each challenge of the ball has `2^(256 − τ)` seeds.** -/
theorem card_seedPoly_eq {τ : ℕ} {c : Rq} (hc : IsChallenge τ c) :
    (univ.filter fun ω : ChallengeSeed ringDegree τ => ω.poly = c).card = 2 ^ (ringDegree - τ) := by
  have hiff : ∀ ω : ChallengeSeed ringDegree τ, ω.poly = c ↔ ω.coeff = centeredPoly c := fun ω =>
    ⟨fun h => by rw [← h, centeredPoly_seedPoly],
      fun h => centeredPoly_injective (by rw [centeredPoly_seedPoly, h])⟩
  rw [filter_congr fun ω _ => hiff ω]
  refine card_seed_coeff_eq _ (fun j => ?_) ?_
  · have := abs_centeredPoly_le hc.1 j
    rw [abs_le] at this
    omega
  · rw [← hc.2]
    congr 1
    ext i
    simp [centeredPoly_ne_zero_iff]

/-- **Counting through a map with fibers of equal size**: if `f` lands in `Q` and every
`b ∈ Q` has exactly `k` preimages, then `#{a | P (f a)} = k · #{b | Q b ∧ P b}`. -/
theorem card_filter_comp_eq_mul {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (Q : β → Prop) [DecidablePred Q] {k : ℕ} (hf : ∀ a, Q (f a))
    (hfib : ∀ b, Q b → (univ.filter fun a => f a = b).card = k) (P : β → Prop)
    [DecidablePred P] :
    (univ.filter fun a => P (f a)).card = k * (univ.filter fun b => Q b ∧ P b).card := by
  have hmaps : ∀ a ∈ (univ.filter fun a => P (f a)), f a ∈ (univ.filter fun b => Q b ∧ P b) :=
    fun a ha => by
      simp only [mem_filter, mem_univ, true_and] at ha ⊢
      exact ⟨hf a, ha⟩
  rw [card_eq_sum_card_fiberwise hmaps, mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun b hb => ?_
  simp only [mem_filter, mem_univ, true_and] at hb
  rw [filter_filter, ← hfib b hb.1]
  congr 1
  ext a
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨h ▸ hb.2, h⟩⟩

/-- **Seeds count challenges of the ball uniformly**: the seeds whose polynomial satisfies `P`
number `2^(256 − τ)` times the challenges of the ball satisfying `P`. -/
theorem card_seed_filter {τ : ℕ} (P : Rq → Prop) [DecidablePred P] :
    (univ.filter fun ω : ChallengeSeed ringDegree τ => P ω.poly).card =
      2 ^ (ringDegree - τ) * (univ.filter fun c => IsChallenge τ c ∧ P c).card :=
  card_filter_comp_eq_mul (fun ω : ChallengeSeed ringDegree τ => ω.poly) (IsChallenge τ)
    isChallenge_seedPoly (fun _ hc => card_seedPoly_eq hc) P

/-- **The uniform seed gives the uniform challenge of the ball**: for every predicate `P` on
challenges, `Pr_ω[P(ω.poly)] = #{c ∈ ball | P c} / #ball`. -/
theorem probUnif_seedPoly {τ : ℕ} (P : Rq → Prop) [DecidablePred P] :
    probUnif (fun ω : ChallengeSeed ringDegree τ => P ω.poly) =
      (univ.filter fun c => IsChallenge τ c ∧ P c).card / (univ.filter (IsChallenge τ)).card := by
  have hall := card_seed_filter (τ := τ) (fun _ => True)
  simp only [filter_true_of_mem (fun _ _ => trivial), and_true] at hall
  rw [probUnif, card_seed_filter, ← card_univ, hall]
  push_cast
  have : (2 : ℝ) ^ (ringDegree - τ) ≠ 0 := by positivity
  rw [mul_div_mul_left _ _ this]

/-- **The floor probability is the ct₀ rejection probability of a uniform challenge of the
ball.** For `‖t₀‖∞ ≤ B` with `2τB < q`, the probability over a uniform seed of `FloorEvent` for
the centered `t₀` equals the fraction of the challenges `c` of the ball (exactly `τ` coefficients
`±1`) whose ct₀-check `‖c • t₀‖∞ < γ₂` (FIPS 204 Algorithm 7 line 28) fails. -/
theorem probUnif_floorEvent_eq_ct0Reject {p : Params} [nttOps : NTTRingOps] [NTTRingLaws nttOps]
    {B : ℕ} (t0 : RqVec p.k) (ht0 : polyVecNorm t0 ≤ B) (hq : 2 * (p.tau * B) < modulus)
    (hγ : 0 < p.gamma2) :
    probUnif (fun ω : ChallengeSeed ringDegree p.tau =>
        FloorEvent (p.gamma2 : ℤ) (centeredVec t0) ω.coeff) =
      (univ.filter fun c => IsChallenge p.tau c ∧ ct0Check (c • t0) = false).card /
        (univ.filter (IsChallenge p.tau)).card := by
  rw [← probUnif_seedPoly]
  unfold probUnif
  congr 3
  ext ω
  simp only [mem_filter, mem_univ, true_and]
  have hb := isChallenge_seedPoly ω
  rw [ct0Check_eq_false_iff ω.poly t0 hb.1 hb.2.le ht0 hq hγ, centeredPoly_seedPoly]

end Signer

/-! ### Uniform-t keys -/

section UniformT

open _root_.MLDSA _root_.MLDSA.Concrete LatticeCrypto

/-- **Summing a function of `i mod m` over `i < m c`** gives `c` copies of the sum over `i < m`. -/
theorem sum_range_mul_mod {M : Type*} [AddCommMonoid M] (H : ℕ → M) (m c : ℕ) :
    ∑ i ∈ range (m * c), H (i % m) = c • ∑ i ∈ range m, H i := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Nat.mul_succ, sum_range_add, ih, succ_nsmul]
    congr 1
    refine sum_congr rfl fun i hi => ?_
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (mem_range.1 hi)]

/-- A sum over `ZMod q` of a function of the canonical representative is the sum over `i < q`. -/
theorem sum_zmod_val {q : ℕ} [NeZero q] {M : Type*} [AddCommMonoid M] (G : ℕ → M) :
    ∑ r : ZMod q, G r.val = ∑ i ∈ range q, G i := by
  rw [← Fin.sum_univ_eq_sum_range]
  have hinj : Function.Injective (fun i : Fin q => ((i : ℕ) : ZMod q)) := fun i j h => by
    have := congrArg ZMod.val h
    simp only [ZMod.val_cast_of_lt i.isLt, ZMod.val_cast_of_lt j.isLt] at this
    exact Fin.ext this
  have hbij : Function.Bijective (fun i : Fin q => ((i : ℕ) : ZMod q)) :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, by simp [ZMod.card]⟩
  exact (Fintype.sum_bijective _ hbij (fun i : Fin q => G i) (fun r => G r.val)
    fun i => by simp only [ZMod.val_cast_of_lt i.isLt]).symm

/-- **The low part of Power2Round on one coefficient** (FIPS 204 Algorithm 35, `d = 13`): the
second component of the vendored `power2RoundCoeff`. -/
def power2RoundLowCoeff (r : Coeff) : ℤ := (power2RoundCoeff r).2

/-- Power2Round's low part read from a natural number: `v mod 2^13`, minus `2^13` above `2^12`. -/
def power2RoundLowNat (v : ℕ) : ℤ :=
  if v % 8192 ≤ 4096 then ((v % 8192 : ℕ) : ℤ) else ((v % 8192 : ℕ) : ℤ) - 8192

/-- `power2RoundLowCoeff r` is `power2RoundLowNat` of the canonical representative of `r`. -/
theorem power2RoundLowCoeff_eq (r : Coeff) : power2RoundLowCoeff r = power2RoundLowNat r.val := by
  have h : power2Scale = 8192 := by simp [power2Scale, droppedBits]
  simp only [power2RoundLowCoeff, power2RoundCoeff, power2RoundLowNat, h]
  split_ifs <;> simp

/-- Power2Round's low part is `t0Coord (v + 4095)` on `Fin 8192`: the same values. -/
theorem power2RoundLowNat_eq_t0Coord (x : Fin 8192) :
    power2RoundLowNat x = t0Coord (x + 4095) := by
  have hx := x.isLt
  have hv : ((x + 4095 : Fin 8192) : ℕ) = ((x : ℕ) + 4095) % 8192 := by
    rw [Fin.val_add]
    rfl
  simp only [power2RoundLowNat, t0Coord, hv, Nat.mod_eq_of_lt hx]
  split_ifs <;> omega

/-- **The law of Power2Round's low part of a uniform `t ∈ Z_q`**, as a sum: since
`q = 1023 · 2^13 + 1`, every value of `(−2^12, 2^12]` is hit `1023` times and `0` once more. -/
theorem sum_power2RoundLowCoeff (F : ℤ → ℝ) :
    ∑ r : Coeff, F (power2RoundLowCoeff r) = 1023 * ∑ x : Fin 8192, F (t0Coord x) + F 0 := by
  simp_rw [power2RoundLowCoeff_eq]
  rw [sum_zmod_val (fun v => F (power2RoundLowNat v))]
  have hq : modulus = 8192 * 1023 + 1 := rfl
  rw [hq, sum_range_succ]
  have hmod : ∀ i, power2RoundLowNat i = power2RoundLowNat (i % 8192) := fun i => by
    simp [power2RoundLowNat]
  rw [sum_congr rfl fun i _ => congrArg F (hmod i)]
  rw [sum_range_mul_mod (fun v => F (power2RoundLowNat v)), nsmul_eq_mul, ← Fin.sum_univ_eq_sum_range]
  simp_rw [power2RoundLowNat_eq_t0Coord]
  rw [Fintype.sum_equiv (Equiv.addRight (4095 : Fin 8192)) (fun x => F (t0Coord (x + 4095)))
    (fun x => F (t0Coord x)) (fun _ => rfl)]
  norm_num [power2RoundLowNat]

/-- **The exponential moments of a uniform-t `t₀` coordinate** at `λ = 19/32768`: both
`E e^{λ x}` and `E e^{−λ x}`, `x` the Power2Round low part of `t` uniform on `Z_q`, are at most
`2.2455`. -/
theorem power2RoundLowCoeff_mgf_le :
    (∑ r : Coeff, exp ((19 / 32768 : ℝ) * power2RoundLowCoeff r) ≤
        Fintype.card Coeff * (22455 / 10000)) ∧
      ∑ r : Coeff, exp (-((19 / 32768 : ℝ) * power2RoundLowCoeff r)) ≤
        Fintype.card Coeff * (22455 / 10000) := by
  have hc : (Fintype.card Coeff : ℝ) = 1023 * 8192 + 1 := by
    rw [ZMod.card]; norm_num [modulus]
  obtain ⟨h1, h2⟩ := t0Coord_mgf_le
  rw [Fintype.card_fin] at h1 h2
  push_cast at h1 h2
  rw [hc]
  constructor
  · rw [sum_power2RoundLowCoeff (fun z => exp ((19 / 32768 : ℝ) * z))]
    norm_num
    linarith
  · rw [sum_power2RoundLowCoeff (fun z => exp (-((19 / 32768 : ℝ) * z)))]
    norm_num
    linarith

/-- Power2Round's low part lies in `[−2^12, 2^12]`. -/
theorem abs_power2RoundLowCoeff_le (r : Coeff) : |power2RoundLowCoeff r| ≤ 4096 := by
  rw [power2RoundLowCoeff_eq, power2RoundLowNat]
  have := Nat.mod_lt r.val (show 0 < 8192 by norm_num)
  split_ifs <;> rw [abs_le] <;> constructor <;> omega

/-- **The centered `t₀` of the vendored Power2Round** (FIPS 204 Algorithm 35) is the integer low
part of each coefficient: `centeredPoly (power2RoundLow r) i = power2RoundLowCoeff (r_i)`. -/
theorem centeredPoly_power2RoundLow (r : Rq) :
    centeredPoly (power2RoundLow r) = fun i => power2RoundLowCoeff (r.get i) := by
  funext i
  simp only [centeredPoly, power2RoundLow, Vector.get_ofFn]
  refine centeredRepr_intCast_eq_of_natAbs_le _ (b := 4096) ?_ (by decide)
  have := abs_power2RoundLowCoeff_le (r.get i)
  rw [Int.abs_eq_natAbs] at this
  exact_mod_cast this

/-- **The floor probability at ML-DSA-44 for uniform-t keys**: for `t₀` the Power2Round low parts
(FIPS 204 Algorithm 35) of `t` uniform on `Z_q^{4 × 256}`, and a uniform challenge of weight
`τ = 39`, the average over `t` of `p(t₀) = Pr_c[‖c · t₀‖∞ ≥ γ₂ = 95232]` is at most `2^−23`.
This is the uniform-t key model: the honest `t = A s₁ + s₂` is not exactly uniform. -/
theorem floorProb_mldsa44_uniformT_le :
    (∑ t : Fin 4 → Fin 256 → Coeff, probUnif (fun ω : ChallengeSeed 256 39 =>
        FloorEvent 95232 (fun m i => power2RoundLowCoeff (t m i)) ω.coeff)) /
      Fintype.card (Fin 4 → Fin 256 → Coeff) ≤ 1 / 2 ^ 23 := by
  have h := sum_floorProb_le (K := 4) (n := 256) (τ := 39) power2RoundLowCoeff 95232
    (lam := 19 / 32768) (A := 22455 / 10000) (by norm_num) power2RoundLowCoeff_mgf_le.1
    power2RoundLowCoeff_mgf_le.2
  have hT : (0 : ℝ) < Fintype.card (Fin 4 → Fin 256 → Coeff) := by
    exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hT]
  refine h.trans ?_
  rw [mul_comm]
  gcongr
  exact floorConst_mldsa44_le

end UniformT

/-! ### A per-key certificate -/

section Certificate

/-- **A rational upper bound for `cosh u`, `|u| ≤ 1`**: the degree-`N` Taylor polynomials of
`e^u` and `e^{−u}`, averaged, plus the remainder bound `|u|^N (N + 1)/(N! N)` of
`Real.exp_bound`. -/
def coshTaylorUB (N : ℕ) (u : ℚ) : ℚ :=
  (∑ i ∈ range N, (u ^ i + (-u) ^ i) / (2 * i.factorial)) +
    |u| ^ N * (N + 1) / (N.factorial * N)

/-- `cosh u ≤ coshTaylorUB N u` for `|u| ≤ 1` and `N > 0`. -/
theorem cosh_le_coshTaylorUB {N : ℕ} (hN : 0 < N) {u : ℚ} (hu : |u| ≤ 1) :
    cosh (u : ℝ) ≤ coshTaylorUB N u := by
  have hu' : |(u : ℝ)| ≤ 1 := by exact_mod_cast hu
  have h1 := Real.exp_bound hu' hN
  have h2 := Real.exp_bound (x := -(u : ℝ)) (by rwa [abs_neg]) hN
  rw [abs_neg] at h2
  have e1 := (abs_le.1 h1).2
  have e2 := (abs_le.1 h2).2
  have hS : ∑ i ∈ range N, (((u : ℝ) ^ i + (-(u : ℝ)) ^ i) / (2 * i.factorial)) =
      ((∑ i ∈ range N, (u : ℝ) ^ i / i.factorial) +
        ∑ i ∈ range N, (-(u : ℝ)) ^ i / i.factorial) / 2 := by
    rw [← sum_add_distrib, sum_div]
    refine sum_congr rfl fun i _ => ?_
    field_simp
  have hR : |(u : ℝ)| ^ N * ((N.succ : ℝ) / (N.factorial * N)) =
      |(u : ℝ)| ^ N * (N + 1) / (N.factorial * N) := by
    push_cast
    ring
  rw [cosh_eq, coshTaylorUB]
  push_cast
  rw [hS]
  rw [hR] at e1 e2
  linarith

/-- `cosh (2y) = 2 cosh² y − 1`. -/
theorem cosh_two_mul_eq (y : ℝ) : cosh (2 * y) = 2 * cosh y ^ 2 - 1 := by
  rw [cosh_two_mul, cosh_sq]
  ring

/-- `1 ≤ cosh y`, from `cosh² y = sinh² y + 1` and `cosh y > 0`. -/
theorem one_le_cosh_of_sq (y : ℝ) : 1 ≤ cosh y := by
  nlinarith [cosh_sq y, cosh_pos y, sq_nonneg (sinh y)]

/-- **A rational upper bound for `cosh x`, `|x| ≤ 4`**: `coshTaylorUB N (x/4)` pushed through the
doubling formula `cosh 2y = 2 cosh² y − 1` twice. -/
def coshUB (N : ℕ) (x : ℚ) : ℚ :=
  2 * (2 * coshTaylorUB N (x / 4) ^ 2 - 1) ^ 2 - 1

/-- `cosh x ≤ coshUB N x` for `|x| ≤ 4` and `N > 0`. -/
theorem cosh_le_coshUB {N : ℕ} (hN : 0 < N) {x : ℚ} (hx : |x| ≤ 4) :
    cosh (x : ℝ) ≤ coshUB N x := by
  have hu : |x / 4| ≤ 1 := by rw [abs_div]; norm_num; linarith
  have hc := cosh_le_coshTaylorUB hN hu
  push_cast at hc
  set c : ℝ := ((coshTaylorUB N (x / 4) : ℚ) : ℝ) with hcdef
  have h1 : 1 ≤ cosh ((x : ℝ) / 4) := one_le_cosh_of_sq _
  have h2 : cosh ((x : ℝ) / 2) = 2 * cosh ((x : ℝ) / 4) ^ 2 - 1 := by
    rw [← cosh_two_mul_eq]; ring_nf
  have h3 : cosh (x : ℝ) = 2 * cosh ((x : ℝ) / 2) ^ 2 - 1 := by
    rw [← cosh_two_mul_eq]; ring_nf
  have h4 : 1 ≤ cosh ((x : ℝ) / 2) := one_le_cosh_of_sq _
  have h5 : cosh ((x : ℝ) / 2) ≤ 2 * c ^ 2 - 1 := by rw [h2]; nlinarith
  rw [coshUB]
  push_cast
  rw [← hcdef, h3]
  nlinarith

/-- **A rational upper bound for `e^{−a}`, `a ≥ 0`**: `1 / ∑_{i < N} a^i / i!`. -/
def expNegUB (N : ℕ) (a : ℚ) : ℚ :=
  1 / ∑ i ∈ range N, a ^ i / i.factorial

/-- `e^{−a} ≤ expNegUB N a` for `a ≥ 0` and `N > 0`. -/
theorem exp_neg_le_expNegUB {N : ℕ} (hN : 0 < N) {a : ℚ} (ha : 0 ≤ a) :
    exp (-(a : ℝ)) ≤ expNegUB N a := by
  have hS := Real.sum_le_exp_of_nonneg (x := (a : ℝ)) (by exact_mod_cast ha) N
  have hpos : (0 : ℝ) < ∑ i ∈ range N, (a : ℝ) ^ i / i.factorial := by
    obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_lt hN
    have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
    rw [sum_range_succ']
    positivity
  rw [expNegUB, exp_neg, ← one_div]
  push_cast
  exact one_div_le_one_div_of_le hpos hS

/-- **The per-key floor certificate**: the fixed-key Chernoff bound of `floorProb_le` with
`cosh` and `e^{−λγ₂}` replaced by their rational upper bounds `coshUB Nc` and `expNegUB Ne`,
`∑_m n · 2 · expNegUB(λγ₂) · (mean_i coshUB(λ t_{m,i}))^τ`. It is an exact rational the signer
evaluates from its own `t₀`. -/
def floorBound {K n : ℕ} (Nc Ne : ℕ) (lam : ℚ) (γ₂ : ℤ) (τ : ℕ) (t : Fin K → Fin n → ℤ) : ℚ :=
  ∑ m, n * (2 * expNegUB Ne (lam * γ₂) * ((∑ i, coshUB Nc (lam * t m i)) / n) ^ τ)

/-- **The per-key certificate bounds the floor probability**: for a fixed key `t` with
`|λ t_{m,i}| ≤ 4`, `λ ≥ 0`, `γ₂ ≥ 0`, the probability over a uniform seed of `FloorEvent γ₂ t` is
at most `floorBound Nc Ne λ γ₂ τ t`. -/
theorem probUnif_floorEvent_le_floorBound {K n τ : ℕ} [NeZero n] {Nc Ne : ℕ} (hNc : 0 < Nc)
    (hNe : 0 < Ne) {lam : ℚ} (hlam : 0 ≤ lam) {γ₂ : ℤ} (hγ : 0 ≤ γ₂) (t : Fin K → Fin n → ℤ)
    (ht : ∀ m i, |lam * t m i| ≤ 4) :
    probUnif (fun ω : ChallengeSeed n τ => FloorEvent γ₂ t ω.coeff) ≤
      floorBound Nc Ne lam γ₂ τ t := by
  refine (floorProb_le (τ := τ) γ₂ t (lam := (lam : ℝ)) (by exact_mod_cast hlam)).trans ?_
  rw [floorBound]
  push_cast
  refine sum_le_sum fun m _ => ?_
  have hE : exp (-((lam : ℝ) * (γ₂ : ℝ))) ≤ (expNegUB Ne (lam * γ₂) : ℝ) := by
    have := exp_neg_le_expNegUB hNe (a := lam * γ₂) (mul_nonneg hlam (by exact_mod_cast hγ))
    push_cast at this
    exact this
  have hC : ∀ i, cosh ((lam : ℝ) * (t m i : ℝ)) ≤ (coshUB Nc (lam * t m i) : ℝ) := fun i => by
    have := cosh_le_coshUB hNc (ht m i)
    push_cast at this
    exact this
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have h0 : 0 ≤ (∑ i, cosh ((lam : ℝ) * (t m i : ℝ))) / n :=
    div_nonneg (sum_nonneg fun i _ => (cosh_pos _).le) hn.le
  have hM : (∑ i, cosh ((lam : ℝ) * (t m i : ℝ))) / n ≤ (∑ i, (coshUB Nc (lam * t m i) : ℝ)) / n :=
    div_le_div_of_nonneg_right (sum_le_sum fun i _ => hC i) hn.le
  have hE0 : 0 ≤ (expNegUB Ne (lam * γ₂) : ℝ) := (exp_pos _).le.trans hE
  gcongr

end Certificate

end GordieHowe.MLDSA
