-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Regularity.InstancesFive
public import GordieHowe.Applications.MLDSA.Signing.ChallengeMoments
public import GordieHowe.Foundations.ToMathlib.PMFOracleQuenched
public import GordieHowe.Foundations.ToMathlib.PMFTV
public import GordieHowe.Foundations.ToMathlib.FintypeBytes
public import GordieHowe.Applications.MLDSA.Signing.HybridKeyLaw
import all LatticeCrypto.MLDSA.ConcretePrimitives

@[expose] public section

/-!
# The stand-in error of the ML-DSA signer, without a mean-weight hypothesis

The real signer's law of `(w₁, c̃)` (`realMass`, normalized) and the stand-in law (density
`acceptWeight` against the uniform law, normalized) are close for typical keys, with
`SampleInBall` a random oracle `G` onto the challenge set `B_τ`
(`concreteWithSampleInBall p G`).

* **Plain-law distance** (`tvDist_le_numerator_div`): for one key and one oracle,
  `tvDist ≤ n / A`, with `n = ∑_v 𝔼_c̃ |realMass - ρ_z standinMass| / (K |V|)` the numerator of
  `sum_expect_abs_realMass_sub_le_mldsa65_five` and `A = 𝔼_{v,c̃} acceptWeight` the mean
  acceptance weight (`tvDist_le_sum_abs_sub_div_sum`).
* **Acceptance lower bound** (`exp_le_expect_acceptWeight`): the Poisson-binomial CDF is at least
  its `S = ∅` term `∏ (1 - p_i)`; `log(1 - p) ≥ -p - p²/(1 - x₀)` on `[0, x₀]`; Jensen for
  `exp`; `p_i ≤ |b_i| / (2(γ₂ - β) - 1)` in every bucket (`hintProb_le_abs`); and
  Cauchy–Schwarz, so `𝔼_c acceptWeight ≥ exp(-√(N M)/L - M/(L²(1 - x₀)))` for `M ≥ 𝔼_c ‖b‖²`.
  With `b = c·t₀` and `c` uniform on `B_τ`, `𝔼_c ‖b‖² = τ ‖t₀‖²`
  (`expect_challengeBall_centeredCoeffs_sq`), giving `exp_le_expect_challengeBall_acceptWeight`.
* **Concentration over the oracle** (`expect_indicator_expect_lt_le`): the mean over the
  commitment hash of a `[0, 1]`-valued function of `G(c̃)` falls below half its mean with
  probability at most `4 / (|C| m²)` (Chebyshev, `expect_sq_expect_sub_le`).
* **Key typicality** (`expect_atypical_uniform_le`, `hybridEventProb_atypical_le`): for `t`
  uniform on `R_q^k` (`hybridKeyLaw`) and `t₀ = Power2Round(t)` low part, the atypical event
  `Atypical Sₜ t₀ : ‖t₀‖₂² > Sₜ` has probability at most
  `e^{-λ Sₜ/2^24} (1 + m(e^λ - 1))^{256k}` with `m = t0SqMean = 46866684530688 / (q · 2^24)`, the
  mean of `t₀,coord² / 2^24` (Chernoff, the chord bound of `exp` on `[0, λ]`).
* **Assembly** (`expect_tvDist_standin_le`): for one key `sk₀`, with real laws `R`
  (`IsRealCommitLaw`) and stand-in laws `Q` as functions of `t₀` (`IsStandinCommitLaw`),
  `𝔼_Â 𝔼_G tvDist ≤ Pr_Â[t₀ atypical] + 4 / (|C| a²) + 2 ε / a`, where `a` is the acceptance
  lower bound of typical keys and `ε` the numerator bound. `sum_expect_tvDist_standin_le`
  averages over a secret law `S` and turns `Pr[t₀ atypical]` into
  `hybridEventProb + mlweAdvantage S B_typ` (`mlweRealMean_atypicalTest_le`).
* **ML-DSA-65 and ML-DSA-87** (`sum_expect_tvDist_standin_le_mldsa65`, `_mldsa87`): with
  `Sₜ = (9/20) · 1536 · 2^24`, `a = e^-60` (resp. `Sₜ = (1/2) · 2048 · 2^24`, `a = e^-95`) and the
  numerators `11 · 2^-148` (resp. `12 · 2^-244`), the averaged stand-in error is at most
  `2^-60 + Adv^MLWE_S(B_typ) + 2^-56` (resp. `2^-100 + Adv^MLWE_S(B_typ) + 2^-100`).

At ML-DSA-44 this route does not close: `τ 2^12 = 159744 > γ₂ = 95232`, so the ct₀ check can fail
and the hint fractions can exceed `1`, and the numerator `11 · 2^-63` is far above any acceptance
lower bound of this form. `StandinError44.lean` bounds the ML-DSA-44 stand-in error through a
weight that may vanish, averaged over keys, matrices and oracles.
-/

open Finset Real
open scoped BigOperators ENNReal

namespace GordieHowe.MLDSA.Regularity

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA
open LatticeCrypto TransformOps
open PMF (tvDist tvDist_le_one tvDist_le_sum_abs_sub_div_sum)

/-! ### Elementary bounds -/

section Elementary

/-- **The `S = ∅` term of the Poisson-binomial CDF**: `∏_i (1 - p_i) ≤ Pr[X₁ + ⋯ + X_n ≤ ω]`
for probabilities `p_i ∈ [0, 1]`. -/
theorem prod_one_sub_le_poissonBinomialCdf {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → ℝ)
    (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1) (ω : ℕ) :
    ∏ i, (1 - p i) ≤ poissonBinomialCdf p ω := by
  unfold poissonBinomialCdf
  have hmem : (∅ : Finset ι) ∈ univ.filter (fun S : Finset ι => S.card ≤ ω) := by simp
  have h := Finset.single_le_sum (f := fun S : Finset ι => ∏ i, if i ∈ S then p i else 1 - p i)
    (fun S _ => prod_nonneg fun i _ => by
      split_ifs
      · exact h0 i
      · linarith [h1 i]) hmem
  simpa using h

/-- **`log(1 - x) ≥ -x - x²/(1 - x₀)`**, as `exp(-x - x²/(1 - x₀)) ≤ 1 - x`, for
`0 ≤ x ≤ x₀ < 1` (`Real.abs_log_sub_add_sum_range_le` at order one). -/
theorem exp_neg_sub_sq_div_le_one_sub {x x₀ : ℝ} (hx : 0 ≤ x) (hxx : x ≤ x₀) (hx₀ : x₀ < 1) :
    exp (-x - x ^ 2 / (1 - x₀)) ≤ 1 - x := by
  have hx1 : x < 1 := hxx.trans_lt hx₀
  have habs : |x| < 1 := by rw [abs_of_nonneg hx]; exact hx1
  have h := Real.abs_log_sub_add_sum_range_le habs 1
  simp only [Finset.sum_range_one, pow_one, Nat.cast_zero, zero_add, div_one,
    abs_of_nonneg hx] at h
  have hq : x ^ 2 / (1 - x) ≤ x ^ 2 / (1 - x₀) :=
    div_le_div_of_nonneg_left (sq_nonneg x) (by linarith) (by linarith)
  have hlog : -x - x ^ 2 / (1 - x₀) ≤ log (1 - x) := by
    have := (abs_le.1 h).1
    linarith
  calc exp (-x - x ^ 2 / (1 - x₀)) ≤ exp (log (1 - x)) := exp_le_exp.2 hlog
    _ = 1 - x := exp_log (by linarith)

/-- **Jensen's inequality for `exp`** under a uniform average: `exp(𝔼 X) ≤ 𝔼 exp(X)`. -/
theorem exp_expect_le_expect_exp {C : Type*} [Fintype C] [Nonempty C] (X : C → ℝ) :
    exp (𝔼 c, X c) ≤ 𝔼 c, exp (X c) := by
  set m := 𝔼 c, X c
  have h : ∀ c, exp m + exp m * (X c - m) ≤ exp (X c) := fun c => by
    have h1 := add_one_le_exp (X c - m)
    have h2 : exp m * exp (X c - m) = exp (X c) := by rw [← exp_add]; ring_nf
    nlinarith [exp_pos m]
  have hmean : 𝔼 c, (exp m + exp m * (X c - m)) = exp m := by
    rw [Finset.expect_add_distrib, ← Finset.mul_expect, Finset.expect_sub_distrib,
      Finset.expect_const Finset.univ_nonempty, Finset.expect_const Finset.univ_nonempty]
    ring
  calc exp m = 𝔼 c, (exp m + exp m * (X c - m)) := hmean.symm
    _ ≤ _ := Finset.expect_le_expect fun c _ => h c

/-- **The mean `ℓ¹` norm is at most `√(N · mean ‖·‖₂²)`**: for `b : C → ι → ℝ`,
`𝔼_c ∑_i |b_{c,i}| ≤ √(|ι| · 𝔼_c ∑_i b_{c,i}²)` (Cauchy–Schwarz twice). -/
theorem expect_sum_abs_le_sqrt {ι C : Type*} [Fintype ι] [Fintype C] [Nonempty C]
    (b : C → ι → ℝ) :
    𝔼 c, ∑ i, |b c i| ≤ √(Fintype.card ι * 𝔼 c, ∑ i, b c i ^ 2) := by
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  refine (Finset.sq_expect_le_expect_sq univ_nonempty _).trans ?_
  rw [Finset.mul_expect]
  refine Finset.expect_le_expect fun c _ => ?_
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset ι)) (f := fun i => |b c i|)
  simpa [Finset.card_univ, sq_abs] using h

/-- **The chord bound of `exp`** on `[0, λ]`: `exp(λ y) ≤ 1 + y (e^λ - 1)` for `y ∈ [0, 1]`. -/
theorem exp_mul_le_one_add_mul {y lam : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    exp (lam * y) ≤ 1 + y * (exp lam - 1) := by
  have h := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ lam) (sub_nonneg.2 hy1) hy0
    (by ring : (1 - y) + y = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, exp_zero, mul_one] at h
  calc exp (lam * y) = exp (y * lam) := by rw [mul_comm]
    _ ≤ 1 - y + y * exp lam := h
    _ = 1 + y * (exp lam - 1) := by ring

end Elementary

/-! ### The acceptance weight from below -/

section Acceptance

/-- **The mean acceptance weight from below.** For shifts `b : C → ι → ℤ` with `|b_{c,i}| ≤ B`,
`0 ≤ B < γ₂` (the ct₀ check passes) and `B < L = 2(γ₂ - β) - 1`, every bucket vector `v` and every
bound `M ≥ 𝔼_c ∑_i b_{c,i}²`:
`exp(-√(|ι| M)/L - M/(L²(1 - B/L))) ≤ 𝔼_c acceptWeight γ₂ β ω (b c) v`. -/
theorem exp_le_expect_acceptWeight {ι C : Type*} [Fintype ι] [DecidableEq ι] [Fintype C]
    [Nonempty C] {γ₂ β ω : ℕ} (b : C → ι → ℤ) (v : ι → ℕ) {B M L : ℝ}
    (hL : ((2 * (γ₂ - β) - 1 : ℕ) : ℝ) = L) (hB0 : 0 ≤ B) (hb : ∀ c i, |(b c i : ℝ)| ≤ B)
    (hBγ : B < γ₂) (hBL : B < L) (hM : 𝔼 c, ∑ i, (b c i : ℝ) ^ 2 ≤ M) :
    exp (-(√(Fintype.card ι * M) / L) - M / (L ^ 2 * (1 - B / L))) ≤
      𝔼 c, acceptWeight γ₂ β ω (b c) v := by
  have hLpos : 0 < L := hB0.trans_lt hBL
  set x₀ := B / L
  have hx₀ : x₀ < 1 := (div_lt_one hLpos).2 hBL
  have hx₀0 : 0 ≤ x₀ := div_nonneg hB0 hLpos.le
  set Z : C → ℝ := fun c => -(∑ i, |(b c i : ℝ)|) / L - (∑ i, (b c i : ℝ) ^ 2) / (L ^ 2 * (1 - x₀))
  -- Each challenge: the acceptance weight is at least `exp (Z c)`.
  have hpt : ∀ c, exp (Z c) ≤ acceptWeight γ₂ β ω (b c) v := by
    intro c
    set q : ι → ℝ := fun i => hintProb γ₂ β (v i) (b c i)
    have hq0 : ∀ i, 0 ≤ q i := fun i => by
      simp only [q, hintProb]; positivity
    have hqb : ∀ i, q i ≤ |(b c i : ℝ)| / L := fun i => by
      have := hintProb_le_abs γ₂ β (v i) (b c i)
      rw [hL] at this
      simpa [q] using this
    have hqx : ∀ i, q i ≤ x₀ := fun i =>
      (hqb i).trans (div_le_div_of_nonneg_right (hb c i) hLpos.le)
    have hct0 : ∀ i, |b c i| < γ₂ := fun i => by
      have h := (hb c i).trans_lt hBγ
      exact_mod_cast h
    have hsq : ∀ i, q i ^ 2 ≤ (b c i : ℝ) ^ 2 / L ^ 2 := fun i => by
      have h := pow_le_pow_left₀ (hq0 i) (hqb i) 2
      rwa [div_pow, sq_abs] at h
    have hZ : Z c ≤ ∑ i, (-q i - q i ^ 2 / (1 - x₀)) := by
      simp only [Z, sum_sub_distrib, sum_neg_distrib]
      rw [neg_div, sum_div, sum_div]
      have h1 : ∑ i, q i ≤ ∑ i, |(b c i : ℝ)| / L := sum_le_sum fun i _ => hqb i
      have h2 : ∑ i, q i ^ 2 / (1 - x₀) ≤ ∑ i, (b c i : ℝ) ^ 2 / (L ^ 2 * (1 - x₀)) :=
        sum_le_sum fun i _ => by
          rw [← div_div]
          exact div_le_div_of_nonneg_right (hsq i) (by linarith)
      linarith
    calc exp (Z c) ≤ exp (∑ i, (-q i - q i ^ 2 / (1 - x₀))) := exp_le_exp.2 hZ
      _ = ∏ i, exp (-q i - q i ^ 2 / (1 - x₀)) := exp_sum _ _
      _ ≤ ∏ i, (1 - q i) := by
          gcongr with i
          exact exp_neg_sub_sq_div_le_one_sub (hq0 i) (hqx i) hx₀
      _ ≤ poissonBinomialCdf q ω := prod_one_sub_le_poissonBinomialCdf q hq0
          (fun i => (hqx i).trans hx₀.le) ω
      _ = acceptWeight γ₂ β ω (b c) v := by
          rw [acceptWeight, ite_eq_left hct0, one_mul]
  -- The mean of `Z` is bounded below.
  have hZmean : -(√(Fintype.card ι * M) / L) - M / (L ^ 2 * (1 - x₀)) ≤ 𝔼 c, Z c := by
    have hD : 0 < L ^ 2 * (1 - x₀) := by have := sub_pos.2 hx₀; positivity
    have hEZ : 𝔼 c, Z c = -(𝔼 c, ∑ i, |(b c i : ℝ)|) / L -
        (𝔼 c, ∑ i, (b c i : ℝ) ^ 2) / (L ^ 2 * (1 - x₀)) := by
      simp only [Z]
      rw [Finset.expect_sub_distrib, ← Finset.expect_div, ← Finset.expect_div,
        Finset.expect_neg_distrib]
    rw [hEZ]
    have h1 := expect_sum_abs_le_sqrt (fun c i => (b c i : ℝ))
    have h1' : √(Fintype.card ι * 𝔼 c, ∑ i, (b c i : ℝ) ^ 2) ≤ √(Fintype.card ι * M) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg _))
    have h2 : (𝔼 c, ∑ i, (b c i : ℝ) ^ 2) / (L ^ 2 * (1 - x₀)) ≤ M / (L ^ 2 * (1 - x₀)) :=
      div_le_div_of_nonneg_right hM hD.le
    have h3 : (𝔼 c, ∑ i, |(b c i : ℝ)|) / L ≤ √(Fintype.card ι * M) / L :=
      div_le_div_of_nonneg_right (h1.trans h1') hLpos.le
    rw [neg_div]
    linarith
  calc exp (-(√(Fintype.card ι * M) / L) - M / (L ^ 2 * (1 - B / L)))
      ≤ exp (𝔼 c, Z c) := exp_le_exp.2 hZmean
    _ ≤ 𝔼 c, exp (Z c) := exp_expect_le_expect_exp Z
    _ ≤ _ := Finset.expect_le_expect fun c _ => hpt c

/-- **The squared norm of `t₀`**: `‖t₀‖₂² = ∑_{j,i} t₀,j,i²` over the centered coefficients. -/
noncomputable def t0SqNorm {k : ℕ} (t0 : RqVec k) : ℝ :=
  ∑ x : Fin k × Fin ringDegree, (centeredVec t0 x.1 x.2 : ℝ) ^ 2

variable [nttOps : NTTRingOps] [NTTRingLaws nttOps]

/-- **The second moment of the shift over `B_τ`**, summed over the coefficients:
`𝔼_{c ∈ B_τ} ∑_{j,i} (c·t₀)_{j,i}² = τ ‖t₀‖₂²` (`expect_challengeBall_centeredCoeffs_sq`). -/
theorem expect_challengeBall_sum_centeredCoeffs_sq {τ B k : ℕ} (hτ : τ ≤ ringDegree)
    (t0 : RqVec k) (ht0 : polyVecNorm t0 ≤ B) (hq : 2 * (τ * B) < modulus) :
    𝔼 c : ChallengeBall τ, ∑ x : Fin k × Fin ringDegree, ((centeredCoeffs (c.1 • t0) x : ℤ) : ℝ) ^ 2 =
      τ * t0SqNorm t0 := by
  rw [Finset.expect_sum_comm]
  simp_rw [expect_challengeBall_centeredCoeffs_sq hτ t0 ht0 hq]
  rw [t0SqNorm, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  dsimp only
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (ringDegree : ℝ) ≠ 0 := by norm_num [ringDegree]
  field_simp

/-- **The acceptance weight of `t₀` over a uniform challenge, from below.** For `c` uniform on
`B_τ` (`τ ≤ 256`), `‖t₀‖∞ ≤ 2^12`, `τ 2^12 < γ₂` (the ct₀ check always passes),
`τ 2^12 < L = 2(γ₂ - β) - 1`, `‖t₀‖₂² ≤ S` and every bucket vector `v`:
`exp(-√(N τ S)/L - τS/(L²(1 - τ 2^12/L))) ≤ 𝔼_c acceptWeight(c·t₀, v)`, `N = 256k`. -/
theorem exp_le_expect_challengeBall_acceptWeight {γ₂ β ω τ k : ℕ} (hτ : τ ≤ ringDegree)
    (t0 : RqVec k) (ht0 : polyVecNorm t0 ≤ 4096) (hγ : τ * 4096 < γ₂)
    (hγq : 2 * γ₂ < modulus) {L : ℝ} (hL : ((2 * (γ₂ - β) - 1 : ℕ) : ℝ) = L)
    (hBL : ((τ * 4096 : ℕ) : ℝ) < L) {S : ℝ} (hS : t0SqNorm t0 ≤ S)
    (v : Fin k × Fin ringDegree → ℕ) :
    exp (-(√((k * ringDegree : ℕ) * (τ * S)) / L) -
        τ * S / (L ^ 2 * (1 - ((τ * 4096 : ℕ) : ℝ) / L))) ≤
      𝔼 c : ChallengeBall τ, acceptWeight γ₂ β ω (centeredCoeffs (c.1 • t0)) v := by
  have hq : 2 * (τ * 4096) < modulus := by omega
  have hb : ∀ (c : ChallengeBall τ) (x : Fin k × Fin ringDegree),
      |((centeredCoeffs (c.1 • t0) x : ℤ) : ℝ)| ≤ ((τ * 4096 : ℕ) : ℝ) := fun c x => by
    have hn := norm_challenge_coeffScalarVecMul_le nttOps c.1 t0 c.2.1 c.2.2.le ht0
    have h := GordieHowe.MLDSA44.natAbs_centeredRepr_le_polyVecNorm (c.1 • t0) x.1 x.2
    have h' : (centeredCoeffs (c.1 • t0) x).natAbs ≤ τ * 4096 := h.trans hn
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast h'
  have hM := expect_challengeBall_sum_centeredCoeffs_sq hτ t0 ht0 hq
  have hτS : (τ : ℝ) * t0SqNorm t0 ≤ τ * S := mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg _)
  have := challengeBall_nonempty hτ
  have h := exp_le_expect_acceptWeight (ω := ω) (fun c : ChallengeBall τ => centeredCoeffs (c.1 • t0))
    v hL (Nat.cast_nonneg _) hb (by exact_mod_cast hγ) hBL (hM.le.trans hτS)
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
  push_cast at h ⊢
  exact h

end Acceptance

/-! ### Concentration over the oracle -/

section Oracle

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

/-- **Two coordinates of a uniform function are independent**: for `x ≠ y`,
`𝔼_G g(G x) h(G y) = 𝔼 g · 𝔼 h`. -/
theorem expect_apply_mul_apply {x y : X} (hxy : x ≠ y) (g h : Y → ℝ) :
    𝔼 G : X → Y, g (G x) * h (G y) = (𝔼 b, g b) * 𝔼 b, h b := by
  have hφ : ∀ G : X → Y, g (G x) * h (G y) =
      ∏ j, (if j = x then g (G j) else if j = y then h (G j) else 1) := fun G => by
    rw [Finset.prod_ite, Finset.prod_ite, Finset.prod_const_one, mul_one]
    have hx : univ.filter (fun j => j = x) = {x} := by ext; simp
    have hy : (univ.filter fun j => ¬j = x).filter (fun j => j = y) = {y} := by
      ext j; simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨hxy.symm, rfl⟩
    rw [hx, hy, Finset.prod_singleton, Finset.prod_singleton]
  simp_rw [hφ]
  have hprod := PMF.expect_prod_apply (fun j b => if j = x then g b else if j = y then h b else 1)
  rw [hprod]
  have hF : ∀ j, (𝔼 b, if j = x then g b else if j = y then h b else 1) =
      if j = x then 𝔼 b, g b else if j = y then 𝔼 b, h b else 1 := fun j => by
    split_ifs <;> simp [Finset.expect_const Finset.univ_nonempty]
  simp_rw [hF]
  rw [Finset.prod_ite, Finset.prod_ite, Finset.prod_const_one, mul_one]
  have hx : univ.filter (fun j => j = x) = {x} := by ext; simp
  have hy : (univ.filter fun j => ¬j = x).filter (fun j => j = y) = {y} := by
    ext j; simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl; exact ⟨hxy.symm, rfl⟩
  rw [hx, hy, Finset.prod_singleton, Finset.prod_singleton]

/-- **The variance of an average over independent uniform coordinates**: for `f` with
`|f - m| ≤ 1`, `m = 𝔼 f`, `𝔼_G (𝔼_x f(G x) - m)² ≤ 1 / |X|`. -/
theorem expect_sq_expect_sub_le [Nonempty X] (f : Y → ℝ) (hf : ∀ b, |f b - 𝔼 b', f b'| ≤ 1) :
    𝔼 G : X → Y, (𝔼 x, f (G x) - 𝔼 b, f b) ^ 2 ≤ 1 / Fintype.card X := by
  set m := 𝔼 b, f b
  set g : Y → ℝ := fun b => f b - m
  have hg0 : 𝔼 b, g b = 0 := by
    simp only [g]; rw [Finset.expect_sub_distrib, Finset.expect_const Finset.univ_nonempty]; ring
  have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hsplit : ∀ G : X → Y, (𝔼 x, f (G x) - m) ^ 2 = 𝔼 x, 𝔼 y, g (G x) * g (G y) := fun G => by
    have : 𝔼 x, f (G x) - m = 𝔼 x, g (G x) := by
      simp only [g]; rw [Finset.expect_sub_distrib, Finset.expect_const Finset.univ_nonempty]
    rw [this, sq, Finset.expect_mul_expect]
  simp_rw [hsplit]
  rw [Finset.expect_comm]
  have hterm : ∀ x y : X, 𝔼 G : X → Y, g (G x) * g (G y) =
      if x = y then 𝔼 b, g b ^ 2 else 0 := fun x y => by
    split_ifs with h
    · subst h
      simp_rw [← sq]
      exact PMF.expect_apply_eval x (fun b => g b ^ 2)
    · rw [expect_apply_mul_apply h g g, hg0, zero_mul]
  calc 𝔼 x, 𝔼 G : X → Y, 𝔼 y, g (G x) * g (G y)
      = 𝔼 x : X, 𝔼 y : X, (if x = y then 𝔼 b, g b ^ 2 else 0) := by
        refine Finset.expect_congr rfl fun x _ => ?_
        rw [Finset.expect_comm]
        exact Finset.expect_congr rfl fun y _ => hterm x y
    _ = (𝔼 b, g b ^ 2) / Fintype.card X := by
        simp only [Fintype.expect_eq_sum_div_card, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
    _ ≤ 1 / Fintype.card X := by
        refine div_le_div_of_nonneg_right ?_ hX.le
        refine (Finset.expect_le_expect (g := fun _ => (1 : ℝ)) fun b _ => ?_).trans_eq
          (Finset.expect_const Finset.univ_nonempty _)
        have := hf b
        rw [← sq_abs]
        nlinarith [abs_nonneg (g b)]

/-- **Chebyshev over the oracle**: for `f : Y → [0, 1]` with mean `m ≥ a > 0`, the average
`A(G) = 𝔼_x f(G x)` over a uniform `G : X → Y` falls below `a / 2` with probability at most
`4 / (|X| a²)`. -/
theorem expect_indicator_expect_lt_le [Nonempty X] (f : Y → ℝ) (hf0 : ∀ b, 0 ≤ f b)
    (hf1 : ∀ b, f b ≤ 1) {a : ℝ} (ha : 0 < a) (ham : a ≤ 𝔼 b, f b) :
    𝔼 G : X → Y, (if 𝔼 x, f (G x) < a / 2 then (1 : ℝ) else 0) ≤
      4 / (Fintype.card X * a ^ 2) := by
  set m := 𝔼 b, f b
  have hm0 : 0 ≤ m := Finset.expect_nonneg fun b _ => hf0 b
  have hm1 : m ≤ 1 := (Finset.expect_le_expect (g := fun _ => (1 : ℝ)) fun b _ => hf1 b).trans_eq
    (Finset.expect_const Finset.univ_nonempty _)
  have hfm : ∀ b, |f b - m| ≤ 1 := fun b => by
    rw [abs_le]; constructor <;> linarith [hf0 b, hf1 b]
  have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hind : ∀ G : X → Y, (if 𝔼 x, f (G x) < a / 2 then (1 : ℝ) else 0) ≤
      4 / a ^ 2 * (𝔼 x, f (G x) - m) ^ 2 := fun G => by
    split_ifs with h
    · have h1 : a / 2 ≤ m - 𝔼 x, f (G x) := by linarith
      have h2 : (a / 2) ^ 2 ≤ (𝔼 x, f (G x) - m) ^ 2 := by
        have he : (𝔼 x, f (G x) - m) ^ 2 = (m - 𝔼 x, f (G x)) ^ 2 := by ring
        rw [he]
        exact pow_le_pow_left₀ (by positivity) h1 2
      calc (1 : ℝ) = 4 / a ^ 2 * (a / 2) ^ 2 := by field_simp; ring
        _ ≤ _ := by gcongr
    · positivity
  calc 𝔼 G : X → Y, (if 𝔼 x, f (G x) < a / 2 then (1 : ℝ) else 0)
      ≤ 𝔼 G : X → Y, 4 / a ^ 2 * (𝔼 x, f (G x) - m) ^ 2 :=
        Finset.expect_le_expect fun G _ => hind G
    _ = 4 / a ^ 2 * 𝔼 G : X → Y, (𝔼 x, f (G x) - m) ^ 2 := by rw [Finset.mul_expect]
    _ ≤ 4 / a ^ 2 * (1 / Fintype.card X) := by
        gcongr
        exact expect_sq_expect_sub_le f hfm
    _ = 4 / (Fintype.card X * a ^ 2) := by field_simp

end Oracle

/-! ### The plain-law distance for one key and one oracle -/

section PlainLaw

variable {p : Params} [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Nonempty (MaskBox p)]

omit [Nonempty (MaskBox p)] in
/-- **The stand-in mass is `K` times the acceptance weight**: `ρ_z · standinMass = K · aw`
(`SigningLaws.signerMass_standin`). -/
theorem zAcceptFraction_mul_standinMass_eq (hp : SigningParams p) (prims : Primitives p)
    (h_laws : SigningLaws prims) (sk : SecretKey p) (hs2 : polyVecBounded sk.s2 p.eta)
    (v : BucketVec p) (c : CommitHashBytes p) :
    (zAcceptFraction p * standinMass prims sk v c).toReal =
      (standinScale p).toReal * (t0Weight prims sk.t0 (v, c) : ℝ≥0∞).toReal := by
  have hS : zAcceptFraction p * standinMass prims sk v c =
      standinScale p * signerWeight prims sk (v, c) := by
    rw [standinMass, SigningLaws.signerMass_standin prims sk hp h_laws hs2 v c, standinScale,
      mul_assoc]
    rfl
  rw [hS, ENNReal.toReal_mul]
  rfl

/-- **The plain-law distance from the numerator** (`tvDist_le_sum_abs_sub_div_sum`): if `P` is
the normalized real accepted mass of `(w₁, c̃)` (when that mass is positive; otherwise `P` is
arbitrary and the bound is `1`) and `Q` the normalized acceptance weight, then
`tvDist P Q ≤ n / A` with `n = ∑_v 𝔼_c̃ |realMass - ρ_z standinMass| / (K |V|)` and
`A = 𝔼_{v,c̃} aw > 0`. -/
theorem tvDist_le_numerator_div (hp : SigningParams p) (prims : Primitives p)
    (h_laws : SigningLaws prims) (sk : SecretKey p) (hs2 : polyVecBounded sk.s2 p.eta)
    (aHat : TqMatrix p.k p.l) (P Q : PMF (BucketVec p × CommitHashBytes p))
    (hP : 0 < ∑ vc' : BucketVec p × CommitHashBytes p, (realMass prims sk aHat vc'.1 vc'.2).toReal →
      ∀ vc, (P vc).toReal = (realMass prims sk aHat vc.1 vc.2).toReal /
        ∑ vc' : BucketVec p × CommitHashBytes p, (realMass prims sk aHat vc'.1 vc'.2).toReal)
    (hQ : ∀ vc, (Q vc).toReal = (t0Weight prims sk.t0 vc : ℝ≥0∞).toReal /
      ∑ vc', (t0Weight prims sk.t0 vc' : ℝ≥0∞).toReal)
    (hA : 0 < 𝔼 vc, (t0Weight prims sk.t0 vc : ℝ≥0∞).toReal) :
    tvDist P Q ≤ (∑ v, 𝔼 c, |(realMass prims sk aHat v c).toReal -
        (zAcceptFraction p * standinMass prims sk v c).toReal|) /
      ((standinScale p).toReal * Fintype.card (BucketVec p)) /
      𝔼 vc, (t0Weight prims sk.t0 vc : ℝ≥0∞).toReal := by
  by_cases hpos : 0 < ∑ vc' : BucketVec p × CommitHashBytes p,
    (realMass prims sk aHat vc'.1 vc'.2).toReal
  swap
  -- No real mass: the bound is `1`.
  · have hsum : ∑ vc' : BucketVec p × CommitHashBytes p,
        (realMass prims sk aHat vc'.1 vc'.2).toReal = 0 :=
      le_antisymm (not_lt.1 hpos) (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
    have h0 : ∀ v c, (realMass prims sk aHat v c).toReal = 0 := fun v c =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)).1 hsum (v, c)
        (Finset.mem_univ _)
    have hK : 0 < (standinScale p).toReal := standinScale_pos hp
    have hV : (0 : ℝ) < Fintype.card (BucketVec p) := by exact_mod_cast Fintype.card_pos
    have hnum : ∑ v, 𝔼 c, |(realMass prims sk aHat v c).toReal -
        (zAcceptFraction p * standinMass prims sk v c).toReal| =
        (standinScale p).toReal * Fintype.card (BucketVec p) *
          𝔼 vc, (t0Weight prims sk.t0 vc : ℝ≥0∞).toReal := by
      simp_rw [h0, zero_sub, abs_neg, abs_of_nonneg ENNReal.toReal_nonneg,
        zAcceptFraction_mul_standinMass_eq hp prims h_laws sk hs2]
      rw [← Finset.univ_product_univ, Finset.expect_product, Fintype.expect_eq_sum_div_card
        (fun v : BucketVec p => 𝔼 c : CommitHashBytes p, (t0Weight prims sk.t0 (v,
          c) : ℝ≥0∞).toReal)]
      simp_rw [← Finset.mul_expect]
      rw [← Finset.mul_sum]
      field_simp
    rw [hnum]
    have : (standinScale p).toReal * Fintype.card (BucketVec p) *
        (𝔼 vc, (t0Weight prims sk.t0 vc : ℝ≥0∞).toReal) /
        ((standinScale p).toReal * Fintype.card (BucketVec p)) /
        (𝔼 vc, (t0Weight prims sk.t0 vc : ℝ≥0∞).toReal) = 1 := by
      field_simp
    rw [this]
    exact tvDist_le_one P Q
  replace hP := hP hpos
  set K := (standinScale p).toReal
  have hK : 0 < K := standinScale_pos hp
  set w : BucketVec p × CommitHashBytes p → ℝ := fun vc => (t0Weight prims sk.t0 vc : ℝ≥0∞).toReal
  set s : BucketVec p × CommitHashBytes p → ℝ := fun vc =>
    (zAcceptFraction p * standinMass prims sk vc.1 vc.2).toReal
  have hs : ∀ vc, s vc = K * w vc := fun vc =>
    zAcceptFraction_mul_standinMass_eq hp prims h_laws sk hs2 vc.1 vc.2
  have hV : (0 : ℝ) < Fintype.card (BucketVec p) := by exact_mod_cast Fintype.card_pos
  have hC : (0 : ℝ) < Fintype.card (CommitHashBytes p) := by exact_mod_cast Fintype.card_pos
  have hcard : (Fintype.card (BucketVec p × CommitHashBytes p) : ℝ) =
      Fintype.card (BucketVec p) * Fintype.card (CommitHashBytes p) := by
    rw [Fintype.card_prod]; push_cast; rfl
  have hsumw : ∑ vc, w vc = Fintype.card (BucketVec p) * Fintype.card (CommitHashBytes p) *
      𝔼 vc, w vc := by
    rw [Fintype.expect_eq_sum_div_card, hcard]
    field_simp
  have hsums : ∑ vc, s vc = K * ∑ vc, w vc := by simp_rw [hs, ← Finset.mul_sum]
  have hspos : 0 < ∑ vc, s vc := by
    rw [hsums, hsumw]; positivity
  have hQ' : ∀ vc, (Q vc).toReal = s vc / ∑ vc', s vc' := fun vc => by
    rw [hQ, hs, hsums]
    field_simp
    rfl
  have h := tvDist_le_sum_abs_sub_div_sum P Q (fun _ => ENNReal.toReal_nonneg) hspos hP hQ'
  refine h.trans_eq ?_
  rw [hsums, hsumw, Fintype.sum_prod_type]
  simp only [s]
  have hcol : ∀ v : BucketVec p, ∑ c, |(realMass prims sk aHat v c).toReal -
      (zAcceptFraction p * standinMass prims sk v c).toReal| =
      Fintype.card (CommitHashBytes p) * 𝔼 c, |(realMass prims sk aHat v c).toReal -
        (zAcceptFraction p * standinMass prims sk v c).toReal| := fun v => by
    rw [Fintype.expect_eq_sum_div_card]
    field_simp
  simp_rw [hcol]
  rw [← Finset.mul_sum]
  field_simp

end PlainLaw

/-! ### Key typicality for a uniform `t` -/

section Typical

/-- `6 ∑_{i < n} (i - a)² = n(n-1)(2n-1) - 6 a n(n-1) + 6 n a²`. -/
theorem sum_range_sub_sq (n : ℕ) (a : ℝ) :
    6 * ∑ i ∈ range n, ((i : ℝ) - a) ^ 2 =
      n * (n - 1) * (2 * n - 1) - 6 * a * n * (n - 1) + 6 * n * a ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast
    ring

/-- **The second moment of a uniform-t `t₀` coordinate**: `∑_{r ∈ Z_q} t₀(r)² = 46866684530688`,
with `t₀(r)` the Power2Round low part (FIPS 204 Algorithm 35), so that
`𝔼 t₀(r)² / 2^24 = t0SqMean`. -/
theorem sum_power2RoundLowCoeff_sq :
    ∑ r : Coeff, ((power2RoundLowCoeff r : ℤ) : ℝ) ^ 2 = 46866684530688 := by
  rw [sum_power2RoundLowCoeff (fun z => ((z : ℤ) : ℝ) ^ 2)]
  have he : ∑ x : Fin 8192, ((t0Coord x : ℤ) : ℝ) ^ 2 =
      ∑ i ∈ range 8192, ((i : ℝ) - 4095) ^ 2 := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => ((i : ℝ) - 4095) ^ 2) 8192]
    refine Fintype.sum_congr _ _ fun x => ?_
    simp [t0Coord]
  have h := sum_range_sub_sq 8192 4095
  rw [he]
  generalize ∑ i ∈ range 8192, ((i : ℝ) - 4095) ^ 2 = X at h ⊢
  push_cast at h ⊢
  linarith

/-- The mean of `t₀(r)² / 2^24` for `r` uniform on `Z_q`. -/
noncomputable def t0SqMean : ℝ := 46866684530688 / (8380417 * 4096 ^ 2)


/-- **Chernoff for the squared norm of a uniform `t₀`.** For `f` uniform on `ι → Z_q`, `t₀` its
Power2Round low parts (FIPS 204 Algorithm 35), `λ ≥ 0` and a threshold `Sₜ`:
`Pr[Sₜ < ‖t₀‖₂²] ≤ exp(-λ Sₜ/2^24) · (1 + t0SqMean (e^λ - 1))^|ι|`, through the exponential
moment `𝔼 exp(λ ‖t₀‖₂²/2^24)` of independent coordinates and the chord bound of `exp`. -/
theorem expect_atypical_uniform_le (ι : Type*) [Fintype ι] [DecidableEq ι] {lam : ℝ}
    (hlam : 0 ≤ lam) (Sₜ : ℝ) :
    𝔼 f : ι → Coeff,
        (if Sₜ < ∑ x, ((power2RoundLowCoeff (f x) : ℤ) : ℝ) ^ 2 then (1 : ℝ) else 0) ≤
      exp (-(lam * (Sₜ / 4096 ^ 2))) * (1 + t0SqMean * (exp lam - 1)) ^ Fintype.card ι := by
  set D : ℝ := 4096 ^ 2
  have hD : 0 < D := by positivity
  set φ : Coeff → ℝ := fun r => exp (lam * (((power2RoundLowCoeff r : ℤ) : ℝ) ^ 2 / D))
  have hind : ∀ f : ι → Coeff,
      (if Sₜ < ∑ x, ((power2RoundLowCoeff (f x) : ℤ) : ℝ) ^ 2 then (1 : ℝ) else 0) ≤
        exp (-(lam * (Sₜ / D))) * ∏ x, φ (f x) := fun f => by
    have hprod : exp (-(lam * (Sₜ / D))) * ∏ x, φ (f x) =
        exp (lam * ((∑ x, ((power2RoundLowCoeff (f x) : ℤ) : ℝ) ^ 2 - Sₜ) / D)) := by
      simp only [φ, ← exp_sum, ← exp_add]
      congr 1
      rw [sub_div, Finset.sum_div, mul_sub, Finset.mul_sum]
      ring
    rw [hprod]
    split_ifs with h
    · exact one_le_exp (mul_nonneg hlam (div_nonneg (by linarith) hD.le))
    · exact (exp_pos _).le
  have hφ : 𝔼 r, φ r ≤ 1 + t0SqMean * (exp lam - 1) := by
    have hle : ∀ r, φ r ≤ 1 + ((power2RoundLowCoeff r : ℤ) : ℝ) ^ 2 / D * (exp lam - 1) := by
      intro r
      have hb := abs_power2RoundLowCoeff_le r
      have hb' : ((power2RoundLowCoeff r : ℤ) : ℝ) ^ 2 ≤ D := by
        have : |((power2RoundLowCoeff r : ℤ) : ℝ)| ≤ 4096 := by exact_mod_cast hb
        simp only [D]
        nlinarith [abs_nonneg ((power2RoundLowCoeff r : ℤ) : ℝ),
          sq_abs ((power2RoundLowCoeff r : ℤ) : ℝ)]
      exact exp_mul_le_one_add_mul (div_nonneg (sq_nonneg _) hD.le) ((div_le_one hD).2 hb')
    refine (Finset.expect_le_expect fun r _ => hle r).trans_eq ?_
    rw [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty, ← Finset.expect_mul,
      ← Finset.expect_div, Fintype.expect_eq_sum_div_card, sum_power2RoundLowCoeff_sq, ZMod.card]
    simp only [t0SqMean, D]
    norm_num [modulus]
  have hexp : 𝔼 f : ι → Coeff, ∏ x, φ (f x) = (𝔼 r, φ r) ^ Fintype.card ι := by
    rw [PMF.expect_prod_apply (fun (_ : ι) (r : Coeff) => φ r), Finset.prod_const,
      Finset.card_univ]
  have hφ0 : 0 ≤ 𝔼 r, φ r := Finset.expect_nonneg fun r _ => (exp_pos _).le
  calc 𝔼 f : ι → Coeff,
        (if Sₜ < ∑ x, ((power2RoundLowCoeff (f x) : ℤ) : ℝ) ^ 2 then (1 : ℝ) else 0)
      ≤ 𝔼 f : ι → Coeff, exp (-(lam * (Sₜ / D))) * ∏ x, φ (f x) :=
        Finset.expect_le_expect fun f _ => hind f
    _ = exp (-(lam * (Sₜ / D))) * (𝔼 r, φ r) ^ Fintype.card ι := by
        rw [← Finset.mul_expect, hexp]
    _ ≤ _ := by gcongr

end Typical

/-! ### The key's `t₀` -/

section Keys

variable {p : Params}

attribute [local instance] concreteNTTRingOps

/-- The centered `t₀ = Power2Round(t)` low part (`GordieHowe.MLDSA.t0Of`, FIPS 204
Algorithm 35) is the integer low part of each coefficient of `t`. -/
theorem centeredVec_edgeT0Of (t : RqVec p.k) (m : Fin p.k) (i : Fin ringDegree) :
    centeredVec (GordieHowe.MLDSA.t0Of p t) m i = power2RoundLowCoeff ((t.get m).get i) := by
  have h : (GordieHowe.MLDSA.t0Of p t).get m = power2RoundLow (t.get m) := by
    simp [GordieHowe.MLDSA.t0Of, Primitives.power2RoundVec, Spec.concretePrimitivesKeyGen,
      concretePrimitives, power2Round, Vector.get_map]
  rw [centeredVec, h, centeredPoly_power2RoundLow]

/-- `‖t₀‖₂²` of `t₀ = Power2Round(t)` low part, through the coefficients of `t`. -/
theorem t0SqNorm_edgeT0Of (t : RqVec p.k) :
    t0SqNorm (GordieHowe.MLDSA.t0Of p t) =
      ∑ x : CoeffIndex p, ((power2RoundLowCoeff (rqVecCoeffs t x) : ℤ) : ℝ) ^ 2 := by
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [centeredVec_edgeT0Of, rqVecCoeffs_apply]

/-- `‖t₀‖∞ ≤ 2^12` for `t₀ = Power2Round(t)` low part. -/
theorem polyVecNorm_edgeT0Of_le (t : RqVec p.k) :
    polyVecNorm (GordieHowe.MLDSA.t0Of p t) ≤ 4096 := by
  have h : polyVecNorm (GordieHowe.MLDSA.t0Of p t) < 4097 := by
    rw [polyVecNorm_lt_iff _ (by norm_num)]
    intro m i
    have hc := centeredVec_edgeT0Of t m i
    have hb := abs_power2RoundLowCoeff_le ((t.get m).get i)
    simp only [centeredVec, centeredPoly] at hc
    rw [hc]
    rw [Int.abs_eq_natAbs] at hb
    omega
  omega

/-- **The `t₀` of the regularity key is the `t₀` of `t = Â s₁ + s₂`.** -/
theorem matrixKey_t0 [NeZero (bucketCount p)] (sk₀ : SecretKey p) (aHat : TqMatrix p.k p.l) :
    (keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))).t0 =
      GordieHowe.MLDSA.t0Of p (aHat * sk₀.s1 + sk₀.s2) := by
  change ((concretePrimitives p).power2RoundVec (Vector.ofFn _ + sk₀.s2)).2 =
    ((concretePrimitives p).power2RoundVec (aHat * sk₀.s1 + sk₀.s2)).2
  rw [mul_eq_ofFn_keyMap]

/-- **The atypical-key event** at the threshold `Sₜ`: `‖t₀‖₂² > Sₜ`. -/
def Atypical (Sₜ : ℝ) {k : ℕ} (t0 : RqVec k) : Prop := Sₜ < t0SqNorm t0

noncomputable instance (Sₜ : ℝ) {k : ℕ} : DecidablePred (Atypical Sₜ (k := k)) :=
  fun _ => Classical.dec _

/-- **The hybrid probability of an atypical key** (`t` uniform on `R_q^k`):
`Pr[‖t₀‖₂² > Sₜ] ≤ exp(-λ Sₜ/2^24) · (1 + t0SqMean (e^λ - 1))^(256k)`. -/
theorem hybridEventProb_atypical_le (Sₜ : ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    hybridEventProb p (Atypical Sₜ) ≤
      exp (-(lam * (Sₜ / 4096 ^ 2))) * (1 + t0SqMean * (exp lam - 1)) ^ (p.k * ringDegree) := by
  set G : (CoeffIndex p → Coeff) → ℝ := fun f =>
    if Sₜ < ∑ x, ((power2RoundLowCoeff (f x) : ℤ) : ℝ) ^ 2 then 1 else 0
  have hG : ∀ t : RqVec p.k, (if Atypical Sₜ (GordieHowe.MLDSA.t0Of p t) then (1 : ℝ) else 0) =
      G (rqVecCoeffs t) := fun t => by
    simp only [Atypical, t0SqNorm_edgeT0Of, G]
  rw [hybridEventProb]
  simp_rw [hG]
  rw [sum_hybridKeyLaw_eq p G]
  have h := expect_atypical_uniform_le (CoeffIndex p) hlam Sₜ
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at h
  refine le_of_eq_of_le ?_ h
  rw [Fintype.expect_eq_sum_div_card, Finset.sum_div]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fun, ZMod.card]
  simp only [G]
  rw [one_div, inv_pow]
  push_cast
  ring

end Keys

/-! ### Assembly -/

section Assembly

variable {p : Params} [NeZero (bucketCount p)] [Nonempty (MaskBox p)]

attribute [local instance] concreteNTTRingOps

/-- **The primitives with `SampleInBall` a random oracle onto `B_τ`**: the concrete primitives
with `SampleInBall(c̃) = G(c̃)` for `G : CommitHashBytes → B_τ`
(`concreteWithSampleInBall`). -/
abbrev oraclePrims (G : CommitHashBytes p → ChallengeBall p.tau) : Primitives p :=
  concreteWithSampleInBall p fun c => (G c).1

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- An oracle onto `B_τ` has the challenge shape. -/
theorem sampleInBallShape_oraclePrims (G : CommitHashBytes p → ChallengeBall p.tau) :
    SampleInBallShape (oraclePrims G) :=
  ⟨fun c => (G c).2.1, fun c => (G c).2.2.le⟩

/-- **The key of the regularity argument at the matrix `Â`**: `sk₀` with `t₀` recomputed from
`Â s₁ + s₂` (`keyOf`, `A = NTT⁻¹(Â)`). -/
noncomputable abbrev matrixKey (sk₀ : SecretKey p) (aHat : TqMatrix p.k p.l) : SecretKey p :=
  keyOf sk₀ (keyMap (fun b => sk₀.s1.get b) (matOfHat aHat))

omit [Nonempty (MaskBox p)] in
/-- The `t₀` of the regularity key has `‖t₀‖∞ ≤ 2^12` at every matrix. -/
theorem polyVecNorm_matrixKey_t0_le (sk₀ : SecretKey p)
    (aHat : TqMatrix p.k p.l) : polyVecNorm (matrixKey sk₀ aHat).t0 ≤ 4096 := by
  rw [matrixKey_t0]
  exact polyVecNorm_edgeT0Of_le _

/-- **A real commitment law**: for every oracle `G` and matrix `Â`, `R G Â` is the real signer's
law of `(w₁, c̃)` under the key `matrixKey sk₀ Â`, the normalized `realMass`, whenever the real
accepted mass is positive. Where it is zero the signer never accepts, and `R G Â` is arbitrary. -/
def IsRealCommitLaw (sk₀ : SecretKey p)
    (R : (CommitHashBytes p → ChallengeBall p.tau) → TqMatrix p.k p.l →
      PMF (BucketVec p × CommitHashBytes p)) : Prop :=
  ∀ G aHat, 0 < ∑ vc' : BucketVec p × CommitHashBytes p,
      (realMass (oraclePrims G) (matrixKey sk₀ aHat) aHat vc'.1 vc'.2).toReal →
    ∀ vc, (R G aHat vc).toReal =
    (realMass (oraclePrims G) (matrixKey sk₀ aHat) aHat vc.1 vc.2).toReal /
      ∑ vc' : BucketVec p × CommitHashBytes p,
        (realMass (oraclePrims G) (matrixKey sk₀ aHat) aHat vc'.1 vc'.2).toReal

omit [Nonempty (MaskBox p)] in
/-- **A stand-in commitment law**: for every oracle `G` and every `t₀` with `‖t₀‖∞ ≤ 2^12`,
`Q G t₀` is the law of `(w₁, c̃)` with density proportional to the acceptance weight
`t0Weight` (the stand-in score) against the uniform law, whenever the total weight is positive.
Where it is zero `Q G t₀` is arbitrary. It is a function of `t₀`. -/
def IsStandinCommitLaw
    (Q : (CommitHashBytes p → ChallengeBall p.tau) → RqVec p.k →
      PMF (BucketVec p × CommitHashBytes p)) : Prop :=
  ∀ G t0, polyVecNorm t0 ≤ 4096 →
    0 < ∑ vc' : BucketVec p × CommitHashBytes p, (t0Weight (oraclePrims G) t0 vc' : ℝ≥0∞).toReal →
    ∀ vc, (Q G t0 vc).toReal =
    (t0Weight (oraclePrims G) t0 vc : ℝ≥0∞).toReal /
      ∑ vc' : BucketVec p × CommitHashBytes p, (t0Weight (oraclePrims G) t0 vc' : ℝ≥0∞).toReal

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- There are `256^(λ/4)` commitment hashes. -/
theorem card_commitHashBytes (p : Params) :
    Fintype.card (CommitHashBytes p) = 256 ^ (p.lambda / 4) := by
  rw [Fintype.card_congr (Vector.equivFun _ _), Fintype.card_fun, Fintype.card_fin,
    Fintype.card_congr UInt8.equivFin, Fintype.card_fin]

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
/-- **The mean acceptance weight as a mean over the oracle's values**: with `SampleInBall = G`,
`𝔼_{v,c̃} aw = 𝔼_c̃ f(G c̃)` with `f(c) = 𝔼_v acceptWeight(c·t₀, v)`. -/
theorem expect_t0Weight_oraclePrims (hp : SigningParams p)
    (G : CommitHashBytes p → ChallengeBall p.tau) (t0 : RqVec p.k) :
    𝔼 vc : BucketVec p × CommitHashBytes p, (t0Weight (oraclePrims G) t0 vc : ℝ≥0∞).toReal =
      𝔼 c, 𝔼 v : BucketVec p, acceptWeight p.gamma2 p.beta p.omega
        (centeredCoeffs ((G c).1 • t0)) fun x => (v x).val := by
  rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  refine Finset.expect_congr rfl fun c _ => Finset.expect_congr rfl fun v _ => ?_
  rw [coe_t0Weight, ENNReal.toReal_ofReal (acceptWeight_nonneg hp.beta_lt_gamma2 _ _ _)]
  rfl

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] in
theorem tau_le_ringDegree (hp : p.isApproved) : p.tau ≤ ringDegree := by
  rcases hp with rfl | rfl | rfl <;> decide

/-- **The averaged stand-in error from the three ingredients.** For a key `sk₀` with `s₂` in the
`η`-box, a threshold `Sₜ`, `a > 0` with `a ≤ 𝔼_{c ∈ B_τ} acceptWeight(c·t₀, v)` for every typical
`t₀` (`‖t₀‖∞ ≤ 2^12`, `‖t₀‖₂² ≤ Sₜ`) and every `v`, and the numerator bound `ε` for every oracle,
the real laws `R` and the stand-in laws `Q` satisfy
`𝔼_Â 𝔼_G tvDist(R G Â, Q G t₀(Â)) ≤ Pr_Â[t₀(Â) atypical] + 4 / (|C| a²) + 2 ε / a`, with `G`
uniform onto `B_τ`. -/
theorem expect_tvDist_standin_le (hp : p.isApproved) (sk₀ : SecretKey p)
    (hs2 : polyVecBounded sk₀.s2 p.eta) (Sₜ : ℝ) {a ε : ℝ} (ha : 0 < a)
    (hacc : ∀ t0 : RqVec p.k, polyVecNorm t0 ≤ 4096 → ¬Atypical Sₜ t0 → ∀ v : BucketVec p,
      a ≤ 𝔼 c : ChallengeBall p.tau, acceptWeight p.gamma2 p.beta p.omega
        (centeredCoeffs (c.1 • t0)) fun x => (v x).val)
    (hε : ∀ G : CommitHashBytes p → ChallengeBall p.tau,
      ∑ aHat : TqMatrix p.k p.l, ∑ v : BucketVec p, 𝔼 c,
        |(realMass (oraclePrims G) (matrixKey sk₀ aHat) aHat v c).toReal -
          (zAcceptFraction p * standinMass (oraclePrims G) (matrixKey sk₀ aHat) v c).toReal| ≤
        Fintype.card (TqMatrix p.k p.l) *
          ((standinScale p).toReal * Fintype.card (BucketVec p) * ε))
    (R : (CommitHashBytes p → ChallengeBall p.tau) → TqMatrix p.k p.l →
      PMF (BucketVec p × CommitHashBytes p)) (hR : IsRealCommitLaw sk₀ R)
    (Q : (CommitHashBytes p → ChallengeBall p.tau) → RqVec p.k →
      PMF (BucketVec p × CommitHashBytes p)) (hQ : IsStandinCommitLaw Q) :
    𝔼 aHat : TqMatrix p.k p.l, 𝔼 G : CommitHashBytes p → ChallengeBall p.tau,
        tvDist (R G aHat) (Q G (matrixKey sk₀ aHat).t0) ≤
      𝔼 aHat : TqMatrix p.k p.l, (if Atypical Sₜ (matrixKey sk₀ aHat).t0 then (1 : ℝ) else 0) +
        4 / (Fintype.card (CommitHashBytes p) * a ^ 2) + 2 * ε / a := by
  have hsp := SigningParams.of_isApproved hp
  have := challengeBall_nonempty (tau_le_ringDegree hp)
  set K := (standinScale p).toReal
  have hK : 0 < K := standinScale_pos hsp
  have hV : (0 : ℝ) < Fintype.card (BucketVec p) := by exact_mod_cast Fintype.card_pos
  have hT : (0 : ℝ) < Fintype.card (TqMatrix p.k p.l) := by exact_mod_cast Fintype.card_pos
  set n : (CommitHashBytes p → ChallengeBall p.tau) → TqMatrix p.k p.l → ℝ := fun G aHat =>
    (∑ v, 𝔼 c, |(realMass (oraclePrims G) (matrixKey sk₀ aHat) aHat v c).toReal -
      (zAcceptFraction p * standinMass (oraclePrims G) (matrixKey sk₀ aHat) v c).toReal|) /
      (K * Fintype.card (BucketVec p))
  have hn0 : ∀ G aHat, 0 ≤ n G aHat := fun G aHat =>
    div_nonneg (sum_nonneg fun v _ => Finset.expect_nonneg fun c _ => abs_nonneg _)
      (by positivity)
  set f : TqMatrix p.k p.l → ChallengeBall p.tau → ℝ := fun aHat c =>
    𝔼 v : BucketVec p, acceptWeight p.gamma2 p.beta p.omega
      (centeredCoeffs (c.1 • (matrixKey sk₀ aHat).t0)) fun x => (v x).val
  have hf0 : ∀ aHat c, 0 ≤ f aHat c := fun aHat c =>
    Finset.expect_nonneg fun v _ => acceptWeight_nonneg hsp.beta_lt_gamma2 _ _ _
  have hf1 : ∀ aHat c, f aHat c ≤ 1 := fun aHat c =>
    (Finset.expect_le_expect (g := fun _ => (1 : ℝ)) fun v _ =>
      acceptWeight_le_one hsp.beta_lt_gamma2 _ _ _).trans_eq
      (Finset.expect_const Finset.univ_nonempty _)
  have hA : ∀ G aHat, 𝔼 vc, (t0Weight (oraclePrims G) (matrixKey sk₀ aHat).t0 vc : ℝ≥0∞).toReal =
      𝔼 c, f aHat (G c) := fun G aHat =>
    expect_t0Weight_oraclePrims hsp G _
  have ht0 : ∀ aHat, polyVecNorm (matrixKey sk₀ aHat).t0 ≤ 4096 :=
    polyVecNorm_matrixKey_t0_le sk₀
  -- The pointwise bound on the distance.
  have hpt : ∀ G aHat, tvDist (R G aHat) (Q G (matrixKey sk₀ aHat).t0) ≤
      (if Atypical Sₜ (matrixKey sk₀ aHat).t0 then 1 else
        (if 𝔼 c, f aHat (G c) < a / 2 then (1 : ℝ) else 0)) + 2 / a * n G aHat := fun G aHat => by
    have h2n : 0 ≤ 2 / a * n G aHat := mul_nonneg (by positivity) (hn0 G aHat)
    split_ifs with hat hlow
    · linarith [tvDist_le_one (R G aHat) (Q G (matrixKey sk₀ aHat).t0)]
    · linarith [tvDist_le_one (R G aHat) (Q G (matrixKey sk₀ aHat).t0)]
    · have hge : a / 2 ≤ 𝔼 c, f aHat (G c) := not_lt.1 hlow
      have hpos : 0 < 𝔼 vc, (t0Weight (oraclePrims G) (matrixKey sk₀ aHat).t0 vc : ℝ≥0∞).toReal :=
        by
        rw [hA]; linarith
      have hsum : 0 < ∑ vc' : BucketVec p × CommitHashBytes p,
          (t0Weight (oraclePrims G) (matrixKey sk₀ aHat).t0 vc' : ℝ≥0∞).toReal := by
        rw [Fintype.expect_eq_sum_div_card] at hpos
        exact (div_pos_iff_of_pos_right (by exact_mod_cast Fintype.card_pos)).1 hpos
      have h := tvDist_le_numerator_div hsp (oraclePrims G)
        (signingLaws_concreteWithSampleInBall p hp (sampleInBallShape_oraclePrims G))
        (matrixKey sk₀ aHat) hs2 aHat (R G aHat) (Q G (matrixKey sk₀ aHat).t0) (hR G aHat)
        (hQ G _ (ht0 aHat) hsum) hpos
      rw [hA] at h
      refine h.trans ?_
      rw [zero_add]
      calc n G aHat / 𝔼 c, f aHat (G c) ≤ n G aHat / (a / 2) :=
            div_le_div_of_nonneg_left (hn0 G aHat) (by positivity) hge
        _ = 2 / a * n G aHat := by field_simp
  -- Averages.
  have hcheb : ∀ aHat, ¬Atypical Sₜ (matrixKey sk₀ aHat).t0 →
      𝔼 G : CommitHashBytes p → ChallengeBall p.tau,
        (if 𝔼 c, f aHat (G c) < a / 2 then (1 : ℝ) else 0) ≤
          4 / (Fintype.card (CommitHashBytes p) * a ^ 2) := fun aHat htyp => by
    refine expect_indicator_expect_lt_le (f aHat) (hf0 aHat) (hf1 aHat) ha ?_
    rw [Finset.expect_comm]
    exact (Finset.expect_const Finset.univ_nonempty a).symm.le.trans
      (Finset.expect_le_expect fun v _ => hacc _ (ht0 aHat) htyp v)
  have hnavg : ∀ G, 𝔼 aHat : TqMatrix p.k p.l, n G aHat ≤ ε := fun G => by
    have h := hε G
    rw [Fintype.expect_eq_sum_div_card, div_le_iff₀ hT]
    simp only [n, ← Finset.sum_div]
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hC4 : 0 ≤ 4 / ((Fintype.card (CommitHashBytes p) : ℝ) * a ^ 2) := by positivity
  have hstep : ∀ aHat, 𝔼 G : CommitHashBytes p → ChallengeBall p.tau,
      tvDist (R G aHat) (Q G (matrixKey sk₀ aHat).t0) ≤
        (if Atypical Sₜ (matrixKey sk₀ aHat).t0 then (1 : ℝ) else 0) +
          4 / (Fintype.card (CommitHashBytes p) * a ^ 2) +
          2 / a * 𝔼 G : CommitHashBytes p → ChallengeBall p.tau, n G aHat := fun aHat => by
    refine (Finset.expect_le_expect fun G _ => hpt G aHat).trans ?_
    rw [Finset.expect_add_distrib, ← Finset.mul_expect]
    gcongr
    split_ifs with hat
    · rw [Finset.expect_const Finset.univ_nonempty]; linarith
    · rw [zero_add]; exact hcheb aHat hat
  calc 𝔼 aHat : TqMatrix p.k p.l, 𝔼 G : CommitHashBytes p → ChallengeBall p.tau,
        tvDist (R G aHat) (Q G (matrixKey sk₀ aHat).t0)
      ≤ 𝔼 aHat : TqMatrix p.k p.l, ((if Atypical Sₜ (matrixKey sk₀ aHat).t0 then (1 : ℝ) else 0) +
          4 / (Fintype.card (CommitHashBytes p) * a ^ 2) +
          2 / a * 𝔼 G : CommitHashBytes p → ChallengeBall p.tau, n G aHat) :=
        Finset.expect_le_expect fun aHat _ => hstep aHat
    _ = 𝔼 aHat : TqMatrix p.k p.l, (if Atypical Sₜ (matrixKey sk₀ aHat).t0 then (1 : ℝ) else 0) +
          4 / (Fintype.card (CommitHashBytes p) * a ^ 2) +
          2 / a * 𝔼 G : CommitHashBytes p → ChallengeBall p.tau, 𝔼 aHat : TqMatrix p.k p.l,
            n G aHat := by
        rw [Finset.expect_add_distrib, Finset.expect_add_distrib, ← Finset.mul_expect,
          Finset.expect_const Finset.univ_nonempty, Finset.expect_comm]
    _ ≤ _ := by
        have : 𝔼 G : CommitHashBytes p → ChallengeBall p.tau, 𝔼 aHat : TqMatrix p.k p.l,
            n G aHat ≤ ε := (Finset.expect_le_expect fun G _ => hnavg G).trans_eq
              (Finset.expect_const Finset.univ_nonempty _)
        have h2a : 0 ≤ 2 / a := by positivity
        have := mul_le_mul_of_nonneg_left this h2a
        have h2 : 2 / a * ε = 2 * ε / a := by ring
        linarith

omit [Nonempty (MaskBox p)] in
/-- **Averaging over the secret.** If the stand-in error of every key in the support of a
secret law `S` is at most its atypical-matrix probability plus `C`, then the error averaged over
`(s₁, s₂) ← S`, `Â` and `G` is at most the real mean of the typicality test `B_typ` plus `C`, so
at most `Pr_hybrid[atypical] + Adv^MLWE_S(B_typ) + C` (`mlweRealMean_atypicalTest_le`). -/
theorem sum_expect_tvDist_standin_le (S : PMF (RqVec p.l × RqVec p.k))
    (key : RqVec p.l × RqVec p.k → SecretKey p) (h1 : ∀ s, (key s).s1 = s.1)
    (h2 : ∀ s, (key s).s2 = s.2) (Sₜ C : ℝ)
    (D : RqVec p.l × RqVec p.k → ℝ)
    (hD : ∀ s, S s ≠ 0 → D s ≤ 𝔼 aHat : TqMatrix p.k p.l,
      (if Atypical Sₜ (matrixKey (key s) aHat).t0 then (1 : ℝ) else 0) + C) :
    ∑ s, (S s).toReal * D s ≤
      hybridEventProb p (Atypical Sₜ) + mlweAdvantage S (atypicalTest p (Atypical Sₜ)) + C := by
  have hreal : ∑ s, (S s).toReal * 𝔼 aHat : TqMatrix p.k p.l,
      (if Atypical Sₜ (matrixKey (key s) aHat).t0 then (1 : ℝ) else 0) =
      mlweRealMean S (atypicalTest p (Atypical Sₜ)) := by
    rw [mlweRealMean, Lattice.mlweRealMean, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Fintype.expect_eq_sum_div_card, mul_div_assoc', Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun aHat _ => ?_
    rw [matrixKey_t0, h1, h2, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
    simp only [atypicalTest]
    field_simp
  have hle : ∑ s, (S s).toReal * D s ≤ ∑ s, (S s).toReal * (𝔼 aHat : TqMatrix p.k p.l,
      (if Atypical Sₜ (matrixKey (key s) aHat).t0 then (1 : ℝ) else 0) + C) :=
    Finset.sum_le_sum fun s _ => by
      by_cases hs : S s = 0
      · simp [hs]
      · exact mul_le_mul_of_nonneg_left (hD s hs) ENNReal.toReal_nonneg
  refine hle.trans ?_
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, hreal, ← Finset.sum_mul, PMF.sum_toReal_eq_one, one_mul]
  linarith [mlweRealMean_atypicalTest_le p S (Atypical Sₜ)]

end Assembly

/-! ### Numerical constants -/

section Numerics

/-- `e^60 ≤ 2^87` (`Real.exp_one_lt_d9`). -/
theorem exp_sixty_le : exp 60 ≤ 2 ^ 87 := by
  have h : exp 60 = exp 1 ^ 60 := by rw [← exp_nat_mul]; norm_num
  rw [h]
  calc exp 1 ^ 60 ≤ 2.7182818286 ^ 60 := by
        gcongr; exact exp_one_lt_d9.le
    _ ≤ 2 ^ 87 := by norm_num

/-- `e^95 ≤ 2^138` (`Real.exp_one_lt_d9`). -/
theorem exp_ninetyfive_le : exp 95 ≤ 2 ^ 138 := by
  have h : exp 95 = exp 1 ^ 95 := by rw [← exp_nat_mul]; norm_num
  rw [h]
  calc exp 1 ^ 95 ≤ 2.7182818286 ^ 95 := by
        gcongr; exact exp_one_lt_d9.le
    _ ≤ 2 ^ 138 := by norm_num

/-- An upper bound on `exp x` for `|x| ≤ 1` from the order-6 Taylor polynomial
(`Real.exp_bound`). -/
theorem exp_le_taylor6 {x : ℝ} (hx : |x| ≤ 1) :
    exp x ≤ ∑ m ∈ range 6, x ^ m / m.factorial + |x| ^ 6 * (7 / (720 * 6)) := by
  have h := Real.exp_bound hx (n := 6) (by norm_num)
  have h' := (abs_le.1 h).2
  norm_num [Nat.factorial] at h' ⊢
  linarith

/-- **The atypical-key probability at ML-DSA-65 in the hybrid**: for `t` uniform on `R_q^6`,
`Pr[‖t₀‖₂² > (9/20) · 1536 · 2^24] ≤ 2^-60` (`hybridEventProb_atypical_le` at `λ = 12/25`). -/
theorem hybridEventProb_atypical_le_mldsa65 :
    hybridEventProb mldsa65 (Atypical (9 / 20 * (1536 * 4096 ^ 2))) ≤ 1 / 2 ^ 60 := by
  refine (hybridEventProb_atypical_le (p := mldsa65) _ (lam := 12 / 25) (by norm_num)).trans ?_
  have he1 : exp (12 / 25 : ℝ) ≤ 16161 / 10000 := by
    refine (exp_le_taylor6 (by norm_num [abs_of_pos])).trans ?_
    norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos]
  have he2 : exp (-(27 / 125) : ℝ) ≤ 80574 / 100000 := by
    refine (exp_le_taylor6 (by norm_num [abs_of_neg])).trans ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hk : mldsa65.k = 6 := mldsa65_vals.1
  have hsplit : exp (-((12 / 25 : ℝ) * (9 / 20 * (1536 * 4096 ^ 2) / 4096 ^ 2))) =
      exp (-(27 / 125)) ^ (mldsa65.k * ringDegree) := by
    rw [hk, ← exp_nat_mul]; norm_num [ringDegree]
  rw [hsplit, ← mul_pow]
  have hm : t0SqMean = 46866684530688 / (8380417 * 4096 ^ 2) := rfl
  have hm0 : (0 : ℝ) ≤ t0SqMean := by rw [hm]; positivity
  have hr : exp (-(27 / 125) : ℝ) * (1 + t0SqMean * (exp (12 / 25) - 1)) ≤ 9725 / 10000 := by
    calc exp (-(27 / 125) : ℝ) * (1 + t0SqMean * (exp (12 / 25) - 1))
        ≤ 80574 / 100000 * (1 + t0SqMean * (16161 / 10000 - 1)) := by
          gcongr
          nlinarith [add_one_le_exp (12 / 25 : ℝ)]
      _ ≤ 9725 / 10000 := by rw [hm]; norm_num
  have h0 : (0 : ℝ) ≤ exp (-(27 / 125) : ℝ) * (1 + t0SqMean * (exp (12 / 25) - 1)) := by
    have : 0 ≤ exp (12 / 25 : ℝ) - 1 := by linarith [add_one_le_exp (12 / 25 : ℝ)]
    positivity
  rw [hk]
  calc (exp (-(27 / 125) : ℝ) * (1 + t0SqMean * (exp (12 / 25) - 1))) ^ (6 * ringDegree)
      ≤ (9725 / 10000 : ℝ) ^ (6 * ringDegree) := pow_le_pow_left₀ h0 hr _
    _ = ((9725 / 10000 : ℝ) ^ 32) ^ 48 := by rw [← pow_mul]; norm_num [ringDegree]
    _ ≤ (41 / 100 : ℝ) ^ 48 := by gcongr; norm_num
    _ ≤ 1 / 2 ^ 60 := by norm_num

/-- **The atypical-key probability at ML-DSA-87 in the hybrid**: for `t` uniform on `R_q^8`,
`Pr[‖t₀‖₂² > (1/2) · 2048 · 2^24] ≤ 2^-100` (`hybridEventProb_atypical_le` at `λ = 7/10`). -/
theorem hybridEventProb_atypical_le_mldsa87 :
    hybridEventProb mldsa87 (Atypical (1 / 2 * (2048 * 4096 ^ 2))) ≤ 1 / 2 ^ 100 := by
  refine (hybridEventProb_atypical_le (p := mldsa87) _ (lam := 7 / 10) (by norm_num)).trans ?_
  have he1 : exp (7 / 10 : ℝ) ≤ 20138 / 10000 := by
    refine (exp_le_taylor6 (by norm_num [abs_of_pos])).trans ?_
    norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_pos]
  have he2 : exp (-(7 / 20) : ℝ) ≤ 7047 / 10000 := by
    refine (exp_le_taylor6 (by norm_num [abs_of_neg])).trans ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hk : mldsa87.k = 8 := mldsa87_vals.1
  have hsplit : exp (-((7 / 10 : ℝ) * (1 / 2 * (2048 * 4096 ^ 2) / 4096 ^ 2))) =
      exp (-(7 / 20)) ^ (mldsa87.k * ringDegree) := by
    rw [hk, ← exp_nat_mul]; norm_num [ringDegree]
  rw [hsplit, ← mul_pow]
  have hm : t0SqMean = 46866684530688 / (8380417 * 4096 ^ 2) := rfl
  have hm0 : (0 : ℝ) ≤ t0SqMean := by rw [hm]; positivity
  have hr : exp (-(7 / 20) : ℝ) * (1 + t0SqMean * (exp (7 / 10) - 1)) ≤ 95 / 100 := by
    calc exp (-(7 / 20) : ℝ) * (1 + t0SqMean * (exp (7 / 10) - 1))
        ≤ 7047 / 10000 * (1 + t0SqMean * (20138 / 10000 - 1)) := by
          gcongr
          nlinarith [add_one_le_exp (7 / 10 : ℝ)]
      _ ≤ 95 / 100 := by rw [hm]; norm_num
  have h0 : (0 : ℝ) ≤ exp (-(7 / 20) : ℝ) * (1 + t0SqMean * (exp (7 / 10) - 1)) := by
    have : 0 ≤ exp (7 / 10 : ℝ) - 1 := by linarith [add_one_le_exp (7 / 10 : ℝ)]
    positivity
  rw [hk]
  calc (exp (-(7 / 20) : ℝ) * (1 + t0SqMean * (exp (7 / 10) - 1))) ^ (8 * ringDegree)
      ≤ (95 / 100 : ℝ) ^ (8 * ringDegree) := pow_le_pow_left₀ h0 hr _
    _ = ((95 / 100 : ℝ) ^ 32) ^ 64 := by rw [← pow_mul]; norm_num [ringDegree]
    _ ≤ (1 / 5 : ℝ) ^ 64 := by gcongr; norm_num
    _ ≤ 1 / 2 ^ 100 := by norm_num

end Numerics

/-! ### The stand-in error at ML-DSA-65 and ML-DSA-87 -/

section Instances

attribute [local instance] concreteNTTRingOps

/-- `τ` and `λ` at ML-DSA-65. -/
theorem mldsa65_tau_lambda : mldsa65.tau = 49 ∧ mldsa65.lambda = 192 := ⟨rfl, rfl⟩

/-- **The acceptance weight of a typical key at ML-DSA-65**: for `‖t₀‖∞ ≤ 2^12`,
`‖t₀‖₂² ≤ (9/20) · 1536 · 2^24` and every bucket vector `v`,
`e^-60 ≤ 𝔼_{c ∈ B_τ} acceptWeight(c·t₀, v)`
(`exp_le_expect_challengeBall_acceptWeight`). -/
theorem exp_neg_le_expect_acceptWeight_mldsa65 (t0 : RqVec mldsa65.k) (ht0 : polyVecNorm t0 ≤ 4096)
    (hS : t0SqNorm t0 ≤ 9 / 20 * (1536 * 4096 ^ 2)) (v : BucketVec mldsa65) :
    exp (-60) ≤ 𝔼 c : ChallengeBall mldsa65.tau, acceptWeight mldsa65.gamma2 mldsa65.beta mldsa65.omega
      (centeredCoeffs (c.1 • t0)) fun x => (v x).val := by
  obtain ⟨hk, -, -, hg2, hb, -⟩ := mldsa65_vals
  obtain ⟨hτ, -⟩ := mldsa65_tau_lambda
  have := concreteNTTRingLaws
  have hL : ((2 * (mldsa65.gamma2 - mldsa65.beta) - 1 : ℕ) : ℝ) = 523383 := by rw [hg2, hb]; norm_num
  have h := exp_le_expect_challengeBall_acceptWeight (ω := mldsa65.omega) (τ := mldsa65.tau)
    (by rw [hτ]; norm_num [ringDegree]) t0 ht0 (by rw [hτ, hg2]; norm_num)
    (by rw [hg2]; norm_num [modulus]) hL (by rw [hτ]; norm_num) hS (fun x => (v x).val)
  refine le_trans ?_ h
  rw [hk, hτ]
  apply exp_le_exp.2
  have hsq : √(((6 * ringDegree : ℕ) : ℝ) * ((49 : ℕ) * (9 / 20 * (1536 * 4096 ^ 2)))) ≤ 29543059 := by
    calc √(((6 * ringDegree : ℕ) : ℝ) * ((49 : ℕ) * (9 / 20 * (1536 * 4096 ^ 2)))) ≤ √((29543059 : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (by norm_num [ringDegree])
      _ = 29543059 := Real.sqrt_sq (by norm_num)
  have h1 : √(((6 * ringDegree : ℕ) : ℝ) * ((49 : ℕ) * (9 / 20 * (1536 * 4096 ^ 2)))) / 523383 ≤ 29543059 / 523383 :=
    div_le_div_of_nonneg_right hsq (by norm_num)
  have h2 : ((49 : ℕ) : ℝ) * (9 / 20 * (1536 * 4096 ^ 2)) / ((523383 : ℝ) ^ 2 * (1 - ((49 * 4096 : ℕ) : ℝ) / 523383)) ≤
      337 / 100 := by norm_num
  have h3 : (29543059 : ℝ) / 523383 + 337 / 100 ≤ 60 := by norm_num
  linarith

/-- **The stand-in error at ML-DSA-65, for one key.** For a key with `s₁, s₂` in the `η`-box,
`SampleInBall` a uniform random oracle `G` onto `B_τ`, real laws `R` and stand-in laws `Q`:
`𝔼_Â 𝔼_G tvDist(R G Â, Q G t₀(Â)) ≤ Pr_Â[‖t₀(Â)‖₂² > (9/20) · 1536 · 2^24] + 2^-56`. -/
theorem expect_tvDist_standin_le_mldsa65 (sk₀ : SecretKey mldsa65)
    (hs1 : polyVecBounded sk₀.s1 mldsa65.eta) (hs2 : polyVecBounded sk₀.s2 mldsa65.eta)
    (R : (CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau) → TqMatrix mldsa65.k mldsa65.l →
      PMF (BucketVec mldsa65 × CommitHashBytes mldsa65)) (hR : IsRealCommitLaw sk₀ R)
    (Q : (CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau) → RqVec mldsa65.k →
      PMF (BucketVec mldsa65 × CommitHashBytes mldsa65)) (hQ : IsStandinCommitLaw Q) :
    𝔼 aHat : TqMatrix mldsa65.k mldsa65.l, 𝔼 G : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
        tvDist (R G aHat) (Q G (matrixKey sk₀ aHat).t0) ≤
      𝔼 aHat : TqMatrix mldsa65.k mldsa65.l,
        (if Atypical (9 / 20 * (1536 * 4096 ^ 2)) (matrixKey sk₀ aHat).t0 then (1 : ℝ) else 0) + 1 / 2 ^ 56 := by
  have h := expect_tvDist_standin_le (Or.inr (Or.inl rfl)) sk₀ hs2 (9 / 20 * (1536 * 4096 ^ 2)) (a := exp (-60))
    (ε := 11 / 2 ^ 148) (exp_pos _)
    (fun t0 ht0 htyp v => exp_neg_le_expect_acceptWeight_mldsa65 t0 ht0 (not_lt.1 htyp) v)
    (fun G => sum_expect_abs_realMass_sub_le_mldsa65_five sk₀ hs1 hs2
      (sampleInBallShape_oraclePrims G)) R hR Q hQ
  refine h.trans ?_
  rw [add_assoc]
  gcongr
  rw [card_commitHashBytes, mldsa65_tau_lambda.2, exp_neg, inv_pow]
  have hE := exp_sixty_le
  have hE0 : 0 < exp (60 : ℝ) := exp_pos _
  have e1 : (4 : ℝ) / (((256 ^ (192 / 4) : ℕ) : ℝ) * (exp 60 ^ 2)⁻¹) =
      4 * exp 60 ^ 2 / ((256 : ℝ) ^ (192 / 4)) := by
    push_cast
    field_simp
    norm_num
  rw [e1, div_inv_eq_mul]
  calc 4 * exp 60 ^ 2 / ((256 : ℝ) ^ (192 / 4)) + 2 * (11 / 2 ^ 148) * exp 60
      ≤ 4 * (2 ^ 87) ^ 2 / ((256 : ℝ) ^ (192 / 4)) + 2 * (11 / 2 ^ 148) * 2 ^ 87 := by
        gcongr
    _ ≤ 1 / 2 ^ 56 := by norm_num

/-- **The stand-in error at ML-DSA-65, over real keys.** For a secret law `S` on `(s₁, s₂)`
supported on the `η`-box, keys `key s` with these `s₁, s₂`, `Â` uniform, `SampleInBall` a
uniform random oracle onto `B_τ`, real laws `R s` and stand-in laws `Q`:
`𝔼_{s ← S} 𝔼_Â 𝔼_G tvDist(R s G Â, Q G t₀) ≤ 2^-60 + Adv^MLWE_S(B_typ) + 2^-56`, with
`B_typ` the typicality test at `‖t₀‖₂² > (9/20) · 1536 · 2^24`. -/
theorem sum_expect_tvDist_standin_le_mldsa65 (S : PMF (RqVec mldsa65.l × RqVec mldsa65.k))
    (hS : ∀ s, S s ≠ 0 → polyVecBounded s.1 mldsa65.eta ∧ polyVecBounded s.2 mldsa65.eta)
    (key : RqVec mldsa65.l × RqVec mldsa65.k → SecretKey mldsa65) (h1 : ∀ s, (key s).s1 = s.1)
    (h2 : ∀ s, (key s).s2 = s.2)
    (R : RqVec mldsa65.l × RqVec mldsa65.k → (CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau) →
      TqMatrix mldsa65.k mldsa65.l → PMF (BucketVec mldsa65 × CommitHashBytes mldsa65))
    (hR : ∀ s, IsRealCommitLaw (key s) (R s))
    (Q : (CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau) → RqVec mldsa65.k →
      PMF (BucketVec mldsa65 × CommitHashBytes mldsa65)) (hQ : IsStandinCommitLaw Q) :
    ∑ s, (S s).toReal * 𝔼 aHat : TqMatrix mldsa65.k mldsa65.l,
        𝔼 G : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
          tvDist (R s G aHat) (Q G (matrixKey (key s) aHat).t0) ≤
      1 / 2 ^ 60 + mlweAdvantage S (atypicalTest mldsa65 (Atypical (9 / 20 * (1536 * 4096 ^ 2)))) + 1 / 2 ^ 56 := by
  have h := sum_expect_tvDist_standin_le S key h1 h2 (9 / 20 * (1536 * 4096 ^ 2)) (1 / 2 ^ 56) _ fun s hs =>
    expect_tvDist_standin_le_mldsa65 (key s) (by rw [h1]; exact (hS s hs).1)
      (by rw [h2]; exact (hS s hs).2) (R s) (hR s) Q hQ
  linarith [hybridEventProb_atypical_le_mldsa65]

/-- `τ` and `λ` at ML-DSA-87. -/
theorem mldsa87_tau_lambda : mldsa87.tau = 60 ∧ mldsa87.lambda = 256 := ⟨rfl, rfl⟩

/-- **The acceptance weight of a typical key at ML-DSA-87**: for `‖t₀‖∞ ≤ 2^12`,
`‖t₀‖₂² ≤ (1/2) · 2048 · 2^24` and every bucket vector `v`,
`e^-95 ≤ 𝔼_{c ∈ B_τ} acceptWeight(c·t₀, v)`
(`exp_le_expect_challengeBall_acceptWeight`). -/
theorem exp_neg_le_expect_acceptWeight_mldsa87 (t0 : RqVec mldsa87.k) (ht0 : polyVecNorm t0 ≤ 4096)
    (hS : t0SqNorm t0 ≤ 1 / 2 * (2048 * 4096 ^ 2)) (v : BucketVec mldsa87) :
    exp (-95) ≤ 𝔼 c : ChallengeBall mldsa87.tau, acceptWeight mldsa87.gamma2 mldsa87.beta mldsa87.omega
      (centeredCoeffs (c.1 • t0)) fun x => (v x).val := by
  obtain ⟨hk, -, -, hg2, hb, -⟩ := mldsa87_vals
  obtain ⟨hτ, -⟩ := mldsa87_tau_lambda
  have := concreteNTTRingLaws
  have hL : ((2 * (mldsa87.gamma2 - mldsa87.beta) - 1 : ℕ) : ℝ) = 523535 := by rw [hg2, hb]; norm_num
  have h := exp_le_expect_challengeBall_acceptWeight (ω := mldsa87.omega) (τ := mldsa87.tau)
    (by rw [hτ]; norm_num [ringDegree]) t0 ht0 (by rw [hτ, hg2]; norm_num)
    (by rw [hg2]; norm_num [modulus]) hL (by rw [hτ]; norm_num) hS (fun x => (v x).val)
  refine le_trans ?_ h
  rw [hk, hτ]
  apply exp_le_exp.2
  have hsq : √(((8 * ringDegree : ℕ) : ℝ) * ((60 : ℕ) * (1 / 2 * (2048 * 4096 ^ 2)))) ≤ 45946299 := by
    calc √(((8 * ringDegree : ℕ) : ℝ) * ((60 : ℕ) * (1 / 2 * (2048 * 4096 ^ 2)))) ≤ √((45946299 : ℝ) ^ 2) :=
          Real.sqrt_le_sqrt (by norm_num [ringDegree])
      _ = 45946299 := Real.sqrt_sq (by norm_num)
  have h1 : √(((8 * ringDegree : ℕ) : ℝ) * ((60 : ℕ) * (1 / 2 * (2048 * 4096 ^ 2)))) / 523535 ≤ 45946299 / 523535 :=
    div_le_div_of_nonneg_right hsq (by norm_num)
  have h2 : ((60 : ℕ) : ℝ) * (1 / 2 * (2048 * 4096 ^ 2)) / ((523535 : ℝ) ^ 2 * (1 - ((60 * 4096 : ℕ) : ℝ) / 523535)) ≤
      709 / 100 := by norm_num
  have h3 : (45946299 : ℝ) / 523535 + 709 / 100 ≤ 95 := by norm_num
  linarith

/-- **The stand-in error at ML-DSA-87, for one key.** For a key with `s₁, s₂` in the `η`-box,
`SampleInBall` a uniform random oracle `G` onto `B_τ`, real laws `R` and stand-in laws `Q`:
`𝔼_Â 𝔼_G tvDist(R G Â, Q G t₀(Â)) ≤ Pr_Â[‖t₀(Â)‖₂² > (1/2) · 2048 · 2^24] + 2^-100`. -/
theorem expect_tvDist_standin_le_mldsa87 (sk₀ : SecretKey mldsa87)
    (hs1 : polyVecBounded sk₀.s1 mldsa87.eta) (hs2 : polyVecBounded sk₀.s2 mldsa87.eta)
    (R : (CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau) → TqMatrix mldsa87.k mldsa87.l →
      PMF (BucketVec mldsa87 × CommitHashBytes mldsa87)) (hR : IsRealCommitLaw sk₀ R)
    (Q : (CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau) → RqVec mldsa87.k →
      PMF (BucketVec mldsa87 × CommitHashBytes mldsa87)) (hQ : IsStandinCommitLaw Q) :
    𝔼 aHat : TqMatrix mldsa87.k mldsa87.l, 𝔼 G : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
        tvDist (R G aHat) (Q G (matrixKey sk₀ aHat).t0) ≤
      𝔼 aHat : TqMatrix mldsa87.k mldsa87.l,
        (if Atypical (1 / 2 * (2048 * 4096 ^ 2)) (matrixKey sk₀ aHat).t0 then (1 : ℝ) else 0) + 1 / 2 ^ 100 := by
  have h := expect_tvDist_standin_le (Or.inr (Or.inr rfl)) sk₀ hs2 (1 / 2 * (2048 * 4096 ^ 2)) (a := exp (-95))
    (ε := 12 / 2 ^ 244) (exp_pos _)
    (fun t0 ht0 htyp v => exp_neg_le_expect_acceptWeight_mldsa87 t0 ht0 (not_lt.1 htyp) v)
    (fun G => sum_expect_abs_realMass_sub_le_mldsa87_five sk₀ hs1 hs2
      (sampleInBallShape_oraclePrims G)) R hR Q hQ
  refine h.trans ?_
  rw [add_assoc]
  gcongr
  rw [card_commitHashBytes, mldsa87_tau_lambda.2, exp_neg, inv_pow]
  have hE := exp_ninetyfive_le
  have hE0 : 0 < exp (95 : ℝ) := exp_pos _
  have e1 : (4 : ℝ) / (((256 ^ (256 / 4) : ℕ) : ℝ) * (exp 95 ^ 2)⁻¹) =
      4 * exp 95 ^ 2 / ((256 : ℝ) ^ (256 / 4)) := by
    push_cast
    field_simp
    norm_num
  rw [e1, div_inv_eq_mul]
  calc 4 * exp 95 ^ 2 / ((256 : ℝ) ^ (256 / 4)) + 2 * (12 / 2 ^ 244) * exp 95
      ≤ 4 * (2 ^ 138) ^ 2 / ((256 : ℝ) ^ (256 / 4)) + 2 * (12 / 2 ^ 244) * 2 ^ 138 := by
        gcongr
    _ ≤ 1 / 2 ^ 100 := by norm_num

/-- **The stand-in error at ML-DSA-87, over real keys.** For a secret law `S` on `(s₁, s₂)`
supported on the `η`-box, keys `key s` with these `s₁, s₂`, `Â` uniform, `SampleInBall` a
uniform random oracle onto `B_τ`, real laws `R s` and stand-in laws `Q`:
`𝔼_{s ← S} 𝔼_Â 𝔼_G tvDist(R s G Â, Q G t₀) ≤ 2^-100 + Adv^MLWE_S(B_typ) + 2^-100`, with
`B_typ` the typicality test at `‖t₀‖₂² > (1/2) · 2048 · 2^24`. -/
theorem sum_expect_tvDist_standin_le_mldsa87 (S : PMF (RqVec mldsa87.l × RqVec mldsa87.k))
    (hS : ∀ s, S s ≠ 0 → polyVecBounded s.1 mldsa87.eta ∧ polyVecBounded s.2 mldsa87.eta)
    (key : RqVec mldsa87.l × RqVec mldsa87.k → SecretKey mldsa87) (h1 : ∀ s, (key s).s1 = s.1)
    (h2 : ∀ s, (key s).s2 = s.2)
    (R : RqVec mldsa87.l × RqVec mldsa87.k → (CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau) →
      TqMatrix mldsa87.k mldsa87.l → PMF (BucketVec mldsa87 × CommitHashBytes mldsa87))
    (hR : ∀ s, IsRealCommitLaw (key s) (R s))
    (Q : (CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau) → RqVec mldsa87.k →
      PMF (BucketVec mldsa87 × CommitHashBytes mldsa87)) (hQ : IsStandinCommitLaw Q) :
    ∑ s, (S s).toReal * 𝔼 aHat : TqMatrix mldsa87.k mldsa87.l,
        𝔼 G : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
          tvDist (R s G aHat) (Q G (matrixKey (key s) aHat).t0) ≤
      1 / 2 ^ 100 + mlweAdvantage S (atypicalTest mldsa87 (Atypical (1 / 2 * (2048 * 4096 ^ 2)))) + 1 / 2 ^ 100 := by
  have h := sum_expect_tvDist_standin_le S key h1 h2 (1 / 2 * (2048 * 4096 ^ 2)) (1 / 2 ^ 100) _ fun s hs =>
    expect_tvDist_standin_le_mldsa87 (key s) (by rw [h1]; exact (hS s hs).1)
      (by rw [h2]; exact (hS s hs).2) (R s) (hR s) Q hQ
  linarith [hybridEventProb_atypical_le_mldsa87]

end Instances

end GordieHowe.MLDSA.Regularity
