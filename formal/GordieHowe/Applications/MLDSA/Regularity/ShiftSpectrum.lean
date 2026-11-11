-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.BinomialFloor
public import GordieHowe.Applications.MLDSA.Regularity.WeightLowerBound
public import GordieHowe.Foundations.Algebra.NegacyclicParseval
public import GordieHowe.Foundations.Algebra.NegacyclicSpectrumFix
public import GordieHowe.Foundations.ToMathlib.SortedSum

public section

/-!
# The shift `c · t₀` through the negacyclic spectrum

The squared norm of the shift `b = c · t₀` is `(1 / n) ∑ j, specSq c j · keySpec t₀ j`, the
challenge's squared spectrum against the key spectrum (`sum_sq_centeredCoeffs_smul`, by Parseval).
Under a **spectrum envelope** `E` of the key (every sum of `m` values of the key spectrum is at
most `E m`), the sorted-sum bound gives `∑ b² ≤ shiftBound E c`, a quantity of the challenge and
the public table `E` alone (`sum_sq_centeredCoeffs_smul_le_shiftBound`). With the flat vector
minimizing the Poisson-binomial CDF, every `x ∈ [0, 1]` with `shiftBound E c ≤ N D² x²` gives
`binomialCdf x N ω` as a lower bound on the acceptance weight of `c · t₀`
(`binomialCdf_le_acceptWeightLower_of_spectrumEnvelope`), `N = 256 k`, `D = 2 (γ₂ − β) − 1`, and
at a commitment hash the rational binomial lower bound on the check weight
(`toNNRat_binomialCdfQ_le_checkWeight`). The statements hold for every polynomial with centered
coefficients in `{-1, 0, 1}` and at most `τ` of them nonzero, the shape of `SampleInBall`; such a
polynomial is a challenge of its own weight (`ChallengeBall.ofWeight`). Under a concave table
with `E M ≤ E (M + 1)`, `shiftBoundMax E τ M` bounds the shift bound of every such polynomial
(`shiftBound_le_shiftBoundMax`), so one `x` serves every challenge
(`toNNRat_binomialCdfQ_le_checkWeight_of_shiftBoundMax`).

The computable forms use the fixed-point squared spectrum `DFT.specSqFix 8 P` at scale `2^P`:
`spectrumCheck P l t₀` tests the key against the table of the increments `l`
(`spectrumEnvelope_of_spectrumCheck`), `shiftBoundFix P l f` bounds `2^(2P) · n · shiftBound`
(`shiftBound_le_shiftBoundFix`), and `xhatFix p P L l f`, a rational with denominator `2^L`,
satisfies `shiftBound E f ≤ N D² (xhatFix p P L l f)²` (`shiftBound_le_xhatFix`).
-/

open Finset

namespace GordieHowe.MLDSA.Regularity

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA
open LatticeCrypto TransformOps

/-- The key spectrum: at frequency `j`, the sum over the components of `t₀` of the squared norm of
the component's value at the `j`-th odd power of the root. -/
noncomputable def keySpec {k : ℕ} (t0 : RqVec k) (j : Fin ringDegree) : ℝ :=
  ∑ m : Fin k, DFT.specSq (centeredVec t0 m) j

/-- **The spectrum envelope of a key**: every sum of `m` values of the key spectrum is at most
`E m`. A condition on the key alone. -/
def SpectrumEnvelope {k : ℕ} (E : ℕ → ℝ) (t0 : RqVec k) : Prop :=
  ∀ T : Finset (Fin ringDegree), ∑ j ∈ T, keySpec t0 j ≤ E T.card

/-- The bound on the squared norm of `c · t₀` from the challenge's spectrum and the public table
`E` alone. -/
noncomputable def shiftBound (E : ℕ → ℝ) (f : Fin ringDegree → ℤ) : ℝ :=
  (1 / ringDegree) * sortedSumBound (DFT.specSq f) E

/-- A challenge's centered coefficients lie in `{-1, 0, 1}`. -/
theorem abs_centeredPoly_challenge_le {τ : ℕ} (c : ChallengeBall τ) (i : Fin ringDegree) :
    |centeredPoly c.1 i| ≤ 1 := by
  exact_mod_cast abs_centeredPoly_le c.2.1 i

/-- A challenge has exactly `τ` nonzero centered coefficients. -/
theorem card_centeredPoly_challenge_ne_zero {τ : ℕ} (c : ChallengeBall τ) :
    (univ.filter fun i => centeredPoly c.1 i ≠ 0).card = τ := by
  simp only [centeredPoly_ne_zero_iff]
  exact c.2.2

/-- **A challenge's squared spectrum is at most `τ²`**: `specSq c j ≤ τ²` for `c ∈ B_τ`. -/
theorem specSq_centeredPoly_le {τ : ℕ} (c : ChallengeBall τ) (j : Fin ringDegree) :
    DFT.specSq (centeredPoly c.1) j ≤ (τ : ℝ) ^ 2 :=
  DFT.specSq_le_sq (abs_centeredPoly_challenge_le c) (card_centeredPoly_challenge_ne_zero c) j

/-- **A challenge's squared spectrum sums to `256 τ`**: `∑ j, specSq c j = 256 τ` for `c ∈ B_τ`. -/
theorem sum_specSq_centeredPoly {τ : ℕ} (c : ChallengeBall τ) :
    ∑ j, DFT.specSq (centeredPoly c.1) j = ringDegree * τ :=
  DFT.sum_specSq_of_ternary (abs_centeredPoly_challenge_le c)
    (card_centeredPoly_challenge_ne_zero c)

/-- `2 τ 2^12 < q` under the floor parameters. -/
theorem FloorParams.two_mul_tau_mul_lt {p : Params} {x₀ κ : ℝ} (hf : FloorParams p x₀ κ) :
    2 * (p.tau * 4096) < modulus := by
  have h1 := hf.ct0
  have h2 := hf.gamma2_lt
  omega

/-- **The shift bound at the fill point `M`**: `(τ² · E M + (n τ − M τ²) · (E (M + 1) − E M)) / n`,
an upper bound on the shift bound of every challenge of weight `τ` under a concave table. -/
@[expose] noncomputable def shiftBoundMax (E : ℕ → ℝ) (τ M : ℕ) : ℝ :=
  (τ ^ 2 * E M + (ringDegree * τ - M * τ ^ 2) * (E (M + 1) - E M)) / ringDegree

/-- **The shift bound of every ternary polynomial of weight at most `τ`**: under a concave table
`E` with `E M ≤ E (M + 1)` and `M < n`, `shiftBound E c ≤ shiftBoundMax E τ M`. -/
theorem shiftBound_le_shiftBoundMax {τ : ℕ} {c : Rq} (hc1 : polyNorm c ≤ 1)
    (hcw : (univ.filter fun j : Fin ringDegree => c.get j ≠ 0).card ≤ τ) {E : ℕ → ℝ}
    (hE : ConcaveTable E ringDegree) {M : ℕ} (hM : M < ringDegree) (hinc : E M ≤ E (M + 1)) :
    shiftBound E (centeredPoly c) ≤ shiftBoundMax E τ M := by
  set w := (univ.filter fun j : Fin ringDegree => c.get j ≠ 0).card with hw
  have hwτ : (w : ℝ) ≤ τ := by exact_mod_cast hcw
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have h := sortedSumBound_le_fill (A := (τ : ℝ) ^ 2) (DFT.specSq_nonneg _)
    (fun j => (specSq_centeredPoly_le (ChallengeBall.ofWeight c hc1) j).trans
      (pow_le_pow_left₀ hw0 hwτ 2)) hE hM
  rw [sum_specSq_centeredPoly (ChallengeBall.ofWeight c hc1)] at h
  have hn : ((ringDegree : ℕ) : ℝ) * w ≤ ringDegree * τ :=
    mul_le_mul_of_nonneg_left hwτ (Nat.cast_nonneg _)
  have h' : sortedSumBound (DFT.specSq (centeredPoly c)) E ≤
      τ ^ 2 * E M + (ringDegree * τ - M * τ ^ 2) * (E (M + 1) - E M) := by
    refine h.trans ?_
    have := mul_le_mul_of_nonneg_right hn (sub_nonneg.2 hinc)
    nlinarith
  rw [shiftBound, shiftBoundMax, one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right h' (Nat.cast_nonneg _)

/-! ### Computable forms at scale `2^P` -/

/-- `ringDegree = 2^8`. -/
theorem ringDegree_eq_two_pow : ringDegree = 2 ^ 8 := by norm_num [ringDegree]

/-- The fixed-point key spectrum at frequency `j`: `∑ m, specSqFix 8 P (t₀ m) j`. -/
def keySpecFix {k : ℕ} (P : ℕ) (t0 : RqVec k) (j : Fin ringDegree) : ℕ :=
  ∑ m : Fin k, DFT.specSqFix 8 P (centeredVec t0 m) j

/-- The key spectrum is at most the fixed-point key spectrum divided by `2^(2P)`. -/
theorem keySpec_le_keySpecFix {k : ℕ} (P : ℕ) (t0 : RqVec k) (j : Fin ringDegree) :
    keySpec t0 j ≤ (keySpecFix P t0 j : ℝ) / (2 ^ (2 * P) : ℕ) := by
  rw [le_div_iff₀ (by positivity), keySpec, keySpecFix, Finset.sum_mul, Nat.cast_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  rw [mul_comm]
  exact_mod_cast DFT.specSq_le_specSqFix P ringDegree_eq_two_pow (centeredVec t0 m) j

/-- **The spectrum check of a key**: every sum of `m` values of the fixed-point key spectrum is at
most `2^(2P)` times the sum of the first `m` increments `l`. -/
def spectrumCheck {k : ℕ} (P : ℕ) (l : List ℕ) (t0 : RqVec k) : Bool :=
  envelopeCheck l (2 ^ (2 * P)) (List.ofFn (keySpecFix P t0))

/-- **The spectrum check is sound**: a key passing it is under the spectrum envelope
`incrementTable l`. -/
theorem spectrumEnvelope_of_spectrumCheck {k : ℕ} {P : ℕ} {l : List ℕ} {t0 : RqVec k}
    (h : spectrumCheck P l t0 = true) : SpectrumEnvelope (incrementTable l) t0 :=
  sum_le_incrementTable_of_envelopeCheck h (keySpec_le_keySpecFix P t0)

/-- **The shift bound in fixed point**: the sorted fixed-point squared spectrum of `f` against
the increments `l`. -/
def shiftBoundFix (P : ℕ) (l : List ℕ) (f : Fin ringDegree → ℤ) : ℕ :=
  sortedDot l (List.ofFn (DFT.specSqFix 8 P f))

/-- **The fixed-point shift bound bounds the shift bound**: for antitone increments `l`,
`2^(2P) · n · shiftBound (incrementTable l) f ≤ shiftBoundFix P l f`. -/
theorem shiftBound_le_shiftBoundFix (P : ℕ) {l : List ℕ} (hl : l.antitoneB = true)
    (f : Fin ringDegree → ℤ) :
    ((2 ^ (2 * P) : ℕ) : ℝ) * ringDegree * shiftBound (incrementTable l) f ≤
      shiftBoundFix P l f := by
  have h := mul_sortedSumBound_le_sortedDot (s := 2 ^ (2 * P)) hl (DFT.specSq_nonneg f)
    (u := DFT.specSqFix 8 P f) fun j => by
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact_mod_cast DFT.specSq_le_specSqFix P ringDegree_eq_two_pow f j
  have hn : (ringDegree : ℝ) ≠ 0 := by norm_num [ringDegree]
  rw [shiftBound, shiftBoundFix]
  refine le_of_eq_of_le ?_ h
  field_simp

/-- **The computed shape**: `(⌊√q⌋ + 1) / 2^L` with
`q = ⌊shiftBoundFix P l f · 2^(2L) / (2^(2P) · n · N · D²)⌋`, `N = k n`, `D = 2 (γ₂ − β) − 1`. -/
def xhatFix (p : Params) (P L : ℕ) (l : List ℕ) (f : Fin ringDegree → ℤ) : ℚ≥0 :=
  ((Nat.sqrt (shiftBoundFix P l f * 2 ^ (2 * L) / (2 ^ (2 * P) * ringDegree *
    (p.k * ringDegree) * (2 * (p.gamma2 - p.beta) - 1) ^ 2)) + 1 : ℕ) : ℚ≥0) / 2 ^ L

/-- **The computed shape bounds the shift bound**: for antitone increments `l`, `0 < k` and
`β < γ₂`, `shiftBound (incrementTable l) f ≤ N · D² · (xhatFix p P L l f)²`. -/
theorem shiftBound_le_xhatFix {p : Params} (hk : 0 < p.k) (hβ : p.beta < p.gamma2) (P L : ℕ)
    {l : List ℕ} (hl : l.antitoneB = true) (f : Fin ringDegree → ℤ) :
    shiftBound (incrementTable l) f ≤
      (p.k * ringDegree : ℕ) * ((2 * (p.gamma2 - p.beta) - 1 : ℕ) : ℝ) ^ 2 *
        ((xhatFix p P L l f : ℚ) : ℝ) ^ 2 := by
  set S := shiftBoundFix P l f
  set ND := (p.k * ringDegree) * (2 * (p.gamma2 - p.beta) - 1) ^ 2 with hND
  set den := 2 ^ (2 * P) * ringDegree * (p.k * ringDegree) * (2 * (p.gamma2 - p.beta) - 1) ^ 2
  set q := S * 2 ^ (2 * L) / den
  set r := Nat.sqrt q + 1
  have hNDpos : 0 < ND := by
    have hD : 0 < 2 * (p.gamma2 - p.beta) - 1 := by omega
    have hn : 0 < ringDegree := by norm_num [ringDegree]
    exact Nat.mul_pos (Nat.mul_pos hk hn) (pow_pos hD 2)
  have hden : den = 2 ^ (2 * P) * ringDegree * ND := by rw [hND]; ring
  have hdenpos : 0 < den := by rw [hden]; norm_num [ringDegree]; positivity
  -- `S · 4^L < den · r²` over `ℕ`
  have h1 : S * 2 ^ (2 * L) < den * (q + 1) := Nat.lt_mul_div_succ _ hdenpos
  have h2 : q + 1 ≤ r * r := Nat.lt_succ_sqrt q
  have h3 : S * 2 ^ (2 * L) < den * (r * r) :=
    h1.trans_le (Nat.mul_le_mul_left _ h2)
  have h3' : (S : ℝ) * 2 ^ (2 * L) < 2 ^ (2 * P) * ringDegree * ND * (r * r) := by
    rw [hden] at h3; exact_mod_cast h3
  have hS := shiftBound_le_shiftBoundFix P hl f
  have hx : ((xhatFix p P L l f : ℚ) : ℝ) = (r : ℝ) / 2 ^ L := by
    simp [xhatFix, r, q, S, den]
  have hNDr : ((p.k * ringDegree : ℕ) : ℝ) * ((2 * (p.gamma2 - p.beta) - 1 : ℕ) : ℝ) ^ 2 =
      (ND : ℝ) := by rw [hND]; push_cast; ring
  rw [hx, hNDr]
  have hsn : (0 : ℝ) < 2 ^ (2 * P) * ringDegree := by norm_num [ringDegree]
  have hL : (0 : ℝ) < 2 ^ L := by positivity
  rw [div_pow, mul_div_assoc', le_div_iff₀ (by positivity)]
  push_cast at hS
  have h4 : (2 : ℝ) ^ (2 * L) = (2 ^ L) ^ 2 := by ring
  rw [h4] at h3'
  nlinarith [mul_le_mul_of_nonneg_right hS (le_of_lt (pow_pos hL 2))]

variable [nttOps : NTTRingOps] [NTTRingLaws nttOps]

/-- **The shift's norm through the spectrum**: for a challenge `c ∈ B_τ`, `‖t₀‖∞ ≤ 2^12` and
`2 τ 2^12 < q`, `∑ x, (c · t₀)_x² = (1 / n) ∑ j, specSq c j · keySpec t₀ j`. -/
theorem sum_sq_centeredCoeffs_smul {τ k : ℕ} (c : ChallengeBall τ) (t0 : RqVec k)
    (ht0 : polyVecNorm t0 ≤ 4096) (hq : 2 * (τ * 4096) < modulus) :
    ∑ x, ((centeredCoeffs (c.1 • t0) x : ℤ) : ℝ) ^ 2 =
      (1 / ringDegree) * ∑ j, DFT.specSq (centeredPoly c.1) j * keySpec t0 j := by
  rw [Fintype.sum_prod_type]
  simp only [fun m i => centeredCoeffs_smul c.1 t0 c.2.1 c.2.2.le ht0 hq (m, i),
    DFT.sum_sq_negacyclicConvCoeff, keySpec, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- **The shift's norm under a spectrum envelope**: `∑ x, (c · t₀)_x² ≤ shiftBound E c`. -/
theorem sum_sq_centeredCoeffs_smul_le_shiftBound {τ k : ℕ} (c : ChallengeBall τ) (t0 : RqVec k)
    (ht0 : polyVecNorm t0 ≤ 4096) (hq : 2 * (τ * 4096) < modulus) {E : ℕ → ℝ}
    (hE : SpectrumEnvelope E t0) :
    ∑ x, ((centeredCoeffs (c.1 • t0) x : ℤ) : ℝ) ^ 2 ≤ shiftBound E (centeredPoly c.1) := by
  rw [sum_sq_centeredCoeffs_smul c t0 ht0 hq, shiftBound]
  exact mul_le_mul_of_nonneg_left (sum_mul_le_sortedSumBound (DFT.specSq_nonneg _) hE)
    (by positivity)

variable {p : Params}

/-- **The check weight under a spectrum envelope**: for a key under the envelope `E` and a
ternary `c` of weight at most `τ`, every `x ∈ [0, 1]` with `shiftBound E c ≤ N · D² · x²` gives
the binomial lower bound on the acceptance weight of `c · t₀`. -/
theorem binomialCdf_le_acceptWeightLower_of_spectrumEnvelope {x₀ κ : ℝ}
    (hf : FloorParams p x₀ κ) (hx₀ : x₀ ≤ 1 / 2) {c : Rq} (hc1 : polyNorm c ≤ 1)
    (hcw : (univ.filter fun j : Fin ringDegree => c.get j ≠ 0).card ≤ p.tau) (t0 : RqVec p.k)
    (ht0 : polyVecNorm t0 ≤ 4096) {E : ℕ → ℝ} (hE : SpectrumEnvelope E t0) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hx : shiftBound E (centeredPoly c) ≤
      (p.k * ringDegree : ℕ) * ((2 * (p.gamma2 - p.beta) - 1 : ℕ) : ℝ) ^ 2 * x ^ 2) :
    binomialCdf x (p.k * ringDegree) p.omega ≤
      acceptWeightLower p.gamma2 p.beta p.omega (centeredCoeffs (c • t0)) := by
  have habs := abs_centeredCoeffs_smul_le_of_weight_le hc1 hcw t0 ht0
  have hlt : ∀ y, |centeredCoeffs (c • t0) y| < p.gamma2 := fun y => by
    have h := (habs y).trans_lt
      (show ((p.tau * 4096 : ℕ) : ℝ) < p.gamma2 by exact_mod_cast hf.ct0)
    exact_mod_cast h
  have hfr : ∀ y, hintFractionBound p.gamma2 p.beta (centeredCoeffs (c • t0) y) ≤ x₀ :=
    fun y => by
      refine (hintFractionBound_le_abs _ _ _).trans (le_trans ?_ hf.x0_ge)
      gcongr
      simpa using habs y
  simp only [acceptWeightLower, hlt, implies_true, ite_true, one_mul]
  have hN : Fintype.card (Fin p.k × Fin ringDegree) = p.k * ringDegree := by simp
  set D : ℝ := ((2 * (p.gamma2 - p.beta) - 1 : ℕ) : ℝ) with hD
  have hDpos : 0 < D := by
    have := hf.beta_lt
    rw [hD, Nat.cast_pos]
    omega
  have hq : 2 * ((univ.filter fun j : Fin ringDegree => c.get j ≠ 0).card * 4096) < modulus :=
    lt_of_le_of_lt (by gcongr) hf.two_mul_tau_mul_lt
  have hS : ∑ x, ((centeredCoeffs (c • t0) x : ℤ) : ℝ) ^ 2 ≤ shiftBound E (centeredPoly c) :=
    sum_sq_centeredCoeffs_smul_le_shiftBound (ChallengeBall.ofWeight c hc1) t0 ht0 hq hE
  rw [← hN]
  refine binomialCdf_le_poissonBinomialCdf_of_sum_sq_le
    (fun y => hintFractionBound_nonneg _ _ _)
    (fun y => (hfr y).trans hx₀) hx0 hx1 ?_ _
  rw [hN]
  have hterm : ∀ y, hintFractionBound p.gamma2 p.beta (centeredCoeffs (c • t0) y) ^ 2 ≤
      ((centeredCoeffs (c • t0) y : ℤ) : ℝ) ^ 2 / D ^ 2 := fun y => by
    rw [← sq_abs (((centeredCoeffs (c • t0) y : ℤ) : ℝ)), ← div_pow]
    exact pow_le_pow_left₀ (hintFractionBound_nonneg _ _ _)
      (by simpa using hintFractionBound_le_abs p.gamma2 p.beta (centeredCoeffs (c • t0) y)) 2
  refine (Finset.sum_le_sum fun y _ => hterm y).trans ?_
  rw [← Finset.sum_div, div_le_iff₀ (by positivity)]
  linarith

/-- **The check weight at the fill point**: under a concave table `E` with `E M ≤ E (M + 1)` and
`M < n`, every `x ∈ [0, 1]` with `shiftBoundMax E τ M ≤ N · D² · x²` gives the binomial lower
bound on the acceptance weight of `c · t₀` at every ternary `c` of weight at most `τ`. -/
theorem binomialCdf_le_acceptWeightLower_of_shiftBoundMax {x₀ κ : ℝ}
    (hf : FloorParams p x₀ κ) (hx₀ : x₀ ≤ 1 / 2) {c : Rq} (hc1 : polyNorm c ≤ 1)
    (hcw : (univ.filter fun j : Fin ringDegree => c.get j ≠ 0).card ≤ p.tau) (t0 : RqVec p.k)
    (ht0 : polyVecNorm t0 ≤ 4096) {E : ℕ → ℝ} (hE : SpectrumEnvelope E t0)
    (hEc : ConcaveTable E ringDegree) {M : ℕ} (hM : M < ringDegree) (hinc : E M ≤ E (M + 1))
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hx : shiftBoundMax E p.tau M ≤
      (p.k * ringDegree : ℕ) * ((2 * (p.gamma2 - p.beta) - 1 : ℕ) : ℝ) ^ 2 * x ^ 2) :
    binomialCdf x (p.k * ringDegree) p.omega ≤
      acceptWeightLower p.gamma2 p.beta p.omega (centeredCoeffs (c • t0)) :=
  binomialCdf_le_acceptWeightLower_of_spectrumEnvelope hf hx₀ hc1 hcw t0 ht0 hE hx0 hx1
    ((shiftBound_le_shiftBoundMax hc1 hcw hEc hM hinc).trans hx)

/-- **The check weight at a commitment hash under a spectrum envelope**: for `SampleInBall` of
the shape of FIPS 204 and a key under the envelope `E`, every rational `x ∈ [0, 1]` with
`shiftBound E c ≤ N · D² · x²` at the challenge `c` of `c̃` gives the binomial lower bound on the
check weight at `c̃`. -/
theorem toNNRat_binomialCdfQ_le_checkWeight [NeZero (bucketCount p)] [Nonempty (MaskBox p)]
    {x₀ κ : ℝ} (hf : FloorParams p x₀ κ) (hx₀ : x₀ ≤ 1 / 2) (prims : Primitives p)
    (hshape : SampleInBallShape prims) (t0 : RqVec p.k) (ht0 : polyVecNorm t0 ≤ 4096)
    {E : ℕ → ℝ} (hE : SpectrumEnvelope E t0) (cTilde : CommitHashBytes p) {x : ℚ} (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1)
    (hx : shiftBound E (centeredPoly (prims.sampleInBall cTilde)) ≤
      (p.k * ringDegree : ℕ) * ((2 * (p.gamma2 - p.beta) - 1 : ℕ) : ℝ) ^ 2 * (x : ℝ) ^ 2) :
    (binomialCdfQ x (p.k * ringDegree) p.omega).toNNRat ≤ checkWeight prims t0 cTilde := by
  rw [checkWeight]
  have h := binomialCdf_le_acceptWeightLower_of_spectrumEnvelope hf hx₀
    (hshape.norm_le_one cTilde) (hshape.weight_le cTilde) t0 ht0 hE
    (x := (x : ℝ)) (by exact_mod_cast hx0) (by exact_mod_cast hx1) hx
  have h0 := binomialCdf_nonneg (x := (x : ℝ)) (by exact_mod_cast hx0) (by exact_mod_cast hx1)
    (p.k * ringDegree) p.omega
  rw [← cast_binomialCdfQ, ← cast_acceptWeightLowerQ] at h
  rw [← cast_binomialCdfQ] at h0
  have hq : binomialCdfQ x (p.k * ringDegree) p.omega ≤ acceptWeightLowerQ p.gamma2 p.beta
      p.omega (centeredCoeffs (prims.sampleInBall cTilde • t0)) := by exact_mod_cast h
  have hq0 : 0 ≤ binomialCdfQ x (p.k * ringDegree) p.omega := by exact_mod_cast h0
  exact (Rat.toNNRat_le_toNNRat_iff (hq0.trans hq)).2 hq

/-- **The check weight at a commitment hash at the fill point**: for `SampleInBall` of the shape
of FIPS 204, under a concave envelope `E` with `E M ≤ E (M + 1)` and `M < n`, every rational
`x ∈ [0, 1]` with `shiftBoundMax E τ M ≤ N · D² · x²` gives the binomial lower bound on the check
weight at every `c̃`. -/
theorem toNNRat_binomialCdfQ_le_checkWeight_of_shiftBoundMax [NeZero (bucketCount p)]
    [Nonempty (MaskBox p)] {x₀ κ : ℝ} (hf : FloorParams p x₀ κ)
    (hx₀ : x₀ ≤ 1 / 2) (prims : Primitives p) (hshape : SampleInBallShape prims)
    (t0 : RqVec p.k) (ht0 : polyVecNorm t0 ≤ 4096) {E : ℕ → ℝ} (hE : SpectrumEnvelope E t0)
    (hEc : ConcaveTable E ringDegree) {M : ℕ} (hM : M < ringDegree) (hinc : E M ≤ E (M + 1))
    {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hx : shiftBoundMax E p.tau M ≤
      (p.k * ringDegree : ℕ) * ((2 * (p.gamma2 - p.beta) - 1 : ℕ) : ℝ) ^ 2 * (x : ℝ) ^ 2)
    (cTilde : CommitHashBytes p) :
    (binomialCdfQ x (p.k * ringDegree) p.omega).toNNRat ≤ checkWeight prims t0 cTilde :=
  toNNRat_binomialCdfQ_le_checkWeight hf hx₀ prims hshape t0 ht0 hE cTilde hx0 hx1
    ((shiftBound_le_shiftBoundMax (hshape.norm_le_one cTilde) (hshape.weight_le cTilde) hEc hM
      hinc).trans hx)

end GordieHowe.MLDSA.Regularity
