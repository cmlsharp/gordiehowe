-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1
public import GordieHowe.Applications.MLDSA.Regularity.CommitCollision
public import GordieHowe.Applications.MLDSA.Regularity.StandinScale

@[expose] public section

/-!
# The McDiarmid terms of the public-`w₁` ring signature

`advantage_le_ideal` carries the McDiarmid terms
`𝔼_{G_A, keys} (√(maxDevVar · log C / 2) + √(maxCountVar · log (C + 1) / 2))`. Both variance
proxies are of order `1/|V|`, `|V| = bucketCount^(256 k)` the number of bucket vectors.

* `maxCountVar_le`: a ring of defect at most `s < 1` has mass at least `(1 - s) |V|`
  (`one_sub_le_colMass_of_ringDefect_le`, `RingWeights.mul_card_le_mass`) and at most `N`
  members, so `maxCountVar ≤ N / ((1 - θ)² (1 - s)² |V|)` (`RingPair.countVar_le`).
* `maxDevVar_le`: both signers have the level `β = K · β_min` (`flatLoopSigner`, `K` the stand-in
  scale), so `RingPair.devVar_le` and the sum over all `n` users give
  `maxDevVar ≤ 4N / (θ (1 - s))² · (2 ∑_u CP(Â_u) / (β |V|)² + 2 / |V|)` with
  `CP(Â_u)` the collision probability of user `u`'s commitment (`commitCollision`) at its matrix
  `Â_u = ExpandA(ρ_u)`.
* `expect_sqrt_maxDevVar_le`, `expect_sqrt_maxCountVar_le`, `expect_mcDiarmidTerms_le`: with
  `ExpandA` a random oracle `G_A` (`withExpandA`), each `Â_u` is uniform
  (`PMF.expect_apply_eval`), so `𝔼_{G_A} ∑_u CP(Â_u) ≤ n ε` for any bound `ε` on `𝔼_Â CP(Â)`
  (`expect_commitCollision_le`), and Jensen's inequality for `√`
  (`Real.expect_sqrt_le_sqrt_expect`) bounds the McDiarmid terms by
  `√(4N / (θ (1 - s))² · (2 n ε / (β |V|)² + 2 / |V|) · log C / 2) +
  √(N / ((1 - θ)² (1 - s)² |V|) · log (C + 1) / 2)`.
* `sqrt_add_sqrt_le_of_le`: the two square roots are at most `2c · √(N n log (C + 1)) /
  (θ (1 - θ) (1 - s) β_min)` when `4ε / L² + 4 / |V| ≤ c²` and `β |V| ≥ L β_min`.
* `two_pow_le_card_bucketVec_mldsa44`, `_mldsa65`, `_mldsa87`: `|V| ≥ 2^4100`; `K |V| ≥ 1/16` is
  `one_div_sixteen_le_standinScale_mul_card_mldsa44`, `_mldsa65`, `_mldsa87` of
  `GordieHowe/Applications/MLDSA/Regularity/StandinScale.lean`.
* `expect_mcDiarmidTerms_le_of`: if the collision bound is at most `2^-4352`
  (`commitCollisionBound_le_mldsa44`, `_mldsa65`, `_mldsa87`), `K |V| ≥ 1/16` and
  `|V| ≥ 2^4100`, the McDiarmid terms are at most
  `√(N n log (C + 1)) / (2^2000 · θ (1 - θ) (1 - s) β_min)` (`ε = 2^-4352`, `L = 1/16`,
  `c = 2^-2001`, `four_mul_div_add_four_div_le`). The three hypotheses hold at ML-DSA-44, 65
  and 87.
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.MLDSA.Regularity PMF Finset
open scoped ENNReal BigOperators
open IOP GordieHowe.SPBCS GordieHowe.QROM

/-! ### The variance proxies at fixed users' coins -/

section Pointwise

variable {p : Params} (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)] {Msg : Type} [Fintype Msg] [DecidableEq Msg] [Inhabited prims.Hint]
  [Fintype prims.Hint] [Fintype prims.Power2High] [DecidableEq prims.Power2High]
  [DecidableEq prims.Hint]
  {N : ℕ} {βmin : ℚ≥0} {reps tol : ℕ} {enc : Vector prims.High p.k → BucketVec p}
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)]
  {M : SPBCS Mg P (pubSigner prims (Msg := Msg) N βmin reps tol enc).Stmt k kN kS L e} {n Q : ℕ}
  (A : PubAnonAdversary (pubSigner prims (Msg := Msg) N βmin reps tol enc) M n Q)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The largest weight variance proxy**: for a defect budget `s < 1` and `θ < 1`,
`maxCountVar ≤ N / ((1 - θ)² (1 - s)² |V|)`. -/
theorem maxCountVar_le (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    {s θ : ℝ}
    (hθ1 : θ < 1) (hs1 : s < 1) (keys : Fin n → _root_.MLDSA.Bytes 32) :
    maxCountVar prims A hp hβ0 hβt s θ keys ≤
      N / ((1 - θ) ^ 2 * (1 - s) ^ 2 * Fintype.card (BucketVec p)) := by
  unfold maxCountVar
  split_ifs with h
  · refine Finset.sup'_le _ _ fun c _ => ?_
    exact (family prims A hp hβ0 hβt s keys c).countVar_le
      ((Fintype.card_fin _).trans_le c.1.1.ring.2) hθ1 (by linarith)
      (RingWeights.mul_card_le_mass _ fun v =>
        one_sub_le_colMass_of_ringDefect_le prims hp hβ0 hβt c.2.2 v)
  · positivity

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The largest deviation variance proxy**: for a defect budget `s < 1` and `θ > 0`, with
`β = K · β_min` the level of every signer,
`maxDevVar ≤ 4N / (θ (1 - s))² · (2 ∑_u CP(Â_u) / (β |V|)² + 2 / |V|)`, `CP(Â_u)` the
collision probability of user `u`'s commitment at its matrix `Â_u = ExpandA(ρ_u)`. -/
theorem maxDevVar_le (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    {s θ : ℝ}
    (hθ0 : 0 < θ) (hs1 : s < 1) (keys : Fin n → _root_.MLDSA.Bytes 32) :
    maxDevVar prims A hp hβ0 hβt s θ keys ≤ 4 * N / (θ * (1 - s)) ^ 2 *
      (2 * (∑ u, commitCollision (prims.expandA (keyGen prims (keys u)).2.rho)) /
          ((standinScale p * βmin).toReal * Fintype.card (BucketVec p)) ^ 2 +
        2 / Fintype.card (BucketVec p)) := by
  set β := (standinScale p * βmin).toReal
  set W : ℝ := (Fintype.card (BucketVec p) : ℝ)
  set S := ∑ u, commitCollision (prims.expandA (keyGen prims (keys u)).2.rho)
  have hS : ∀ u, commitCollision (prims.expandA (keyGen prims (keys u)).2.rho) ≤ S := fun u =>
    Finset.single_le_sum (f := fun u => commitCollision (prims.expandA (keyGen prims (keys u)).2.rho))
      (fun u _ => commitCollision_nonneg _) (mem_univ u)
  have hK : 0 ≤ 4 * (N : ℝ) / (θ * (1 - s)) ^ 2 := by positivity
  unfold maxDevVar
  split_ifs with h
  · refine Finset.sup'_le _ _ fun c _ => ?_
    refine ((family prims A hp hβ0 hβt s keys c).devVar_le (β := β)
      ((Fintype.card_fin _).trans_le c.1.1.ring.2) hθ0 (by linarith)
      (RingWeights.mul_card_le_mass _ fun v =>
        one_sub_le_colMass_of_ringDefect_le prims hp hβ0 hβt c.2.2 v)
      fun b => rfl).trans (mul_le_mul_of_nonneg_left ?_ hK)
    have h0 := hS (c.1.1.user false)
    have h1 := hS (c.1.1.user true)
    rw [Fintype.sum_bool]
    change (commitCollision (prims.expandA (keyGen prims (keys (c.1.1.user true))).2.rho) /
        (β * W) ^ 2 + 1 / W) + (commitCollision (prims.expandA
          (keyGen prims (keys (c.1.1.user false))).2.rho) / (β * W) ^ 2 + 1 / W) ≤
      2 * S / (β * W) ^ 2 + 2 / W
    have hB : 0 ≤ (β * W) ^ 2 := sq_nonneg _
    have e1 := div_le_div_of_nonneg_right h0 hB
    have e2 := div_le_div_of_nonneg_right h1 hB
    have e3 : 2 * S / (β * W) ^ 2 = S / (β * W) ^ 2 + S / (β * W) ^ 2 := by ring
    have e4 : (2 : ℝ) / W = 1 / W + 1 / W := by ring
    rw [e3, e4]
    linarith
  · exact mul_nonneg hK (add_nonneg (div_nonneg (mul_nonneg zero_le_two
      (Finset.sum_nonneg fun u _ => commitCollision_nonneg _)) (sq_nonneg _)) (by positivity))

end Pointwise

/-! ### The variance proxies with `ExpandA` a random oracle -/

section Oracle

variable {p : Params} (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)] {Msg : Type} [Fintype Msg] [DecidableEq Msg] [Inhabited prims.Hint]
  [Fintype prims.Hint] [Fintype prims.Power2High] [DecidableEq prims.Power2High]
  [DecidableEq prims.Hint]
  {N : ℕ} {βmin : ℚ≥0} {reps tol : ℕ} {enc : Vector prims.High p.k → BucketVec p}
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)]
  {M : ∀ GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l,
    SPBCS Mg P (pubSigner (withExpandA prims GA) (Msg := Msg) N βmin reps tol enc).Stmt k kN kS L e}
  {n Q : ℕ}
  (A : ∀ GA, PubAnonAdversary (pubSigner (withExpandA prims GA) (Msg := Msg) N βmin reps tol enc)
    (M GA) n Q)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The deviation term with `ExpandA` a random oracle**: for any bound `ε` on `𝔼_Â CP(Â)` and
`a ≥ 0`, `𝔼_{G_A, keys} √(maxDevVar · a / 2) ≤ √(4N / (θ (1 - s))² · (2 n ε / (β |V|)² + 2/|V|) ·
a / 2)`: each user's matrix `G_A(ρ_u)` is uniform (`PMF.expect_apply_eval`), and Jensen's
inequality for `√` over the users' coins and the oracle. -/
theorem expect_sqrt_maxDevVar_le [NTTRingLaws nttOps] (hp : SigningParams p)
    (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) {s θ : ℝ} (hθ0 : 0 < θ) (hs1 : s < 1) {ε : ℝ}
    (hε : 𝔼 aHat : TqMatrix p.k p.l, commitCollision aHat ≤ ε) {a : ℝ} (ha : 0 ≤ a) :
    𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l, 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
        √(maxDevVar (withExpandA prims GA) (A GA) hp hβ0 hβt s θ keys * a / 2) ≤
      √(4 * N / (θ * (1 - s)) ^ 2 * (2 * n * ε /
          ((standinScale p * βmin).toReal * Fintype.card (BucketVec p)) ^ 2 +
        2 / Fintype.card (BucketVec p)) * a / 2) := by
  set B := ((standinScale p * βmin).toReal * Fintype.card (BucketVec p)) ^ 2
  set W : ℝ := (Fintype.card (BucketVec p) : ℝ)
  set K := 4 * (N : ℝ) / (θ * (1 - s)) ^ 2
  set S : (_root_.MLDSA.Bytes 32 → TqMatrix p.k p.l) → (Fin n → _root_.MLDSA.Bytes 32) → ℝ :=
    fun GA keys => ∑ u, commitCollision (GA (prims.expandSeed (keys u)).1)
  have hK : 0 ≤ K := by positivity
  have hB : 0 ≤ B := sq_nonneg _
  have hS0 : ∀ GA keys, 0 ≤ S GA keys := fun GA keys =>
    Finset.sum_nonneg fun u _ => commitCollision_nonneg _
  have hD0 : ∀ GA keys, 0 ≤ K * (2 * S GA keys / B + 2 / W) * a / 2 := fun GA keys =>
    div_nonneg (mul_nonneg (mul_nonneg hK (add_nonneg (div_nonneg (mul_nonneg zero_le_two
      (hS0 GA keys)) hB) (by positivity))) ha) zero_le_two
  have hpt : ∀ GA keys, maxDevVar (withExpandA prims GA) (A GA) hp hβ0 hβt s θ keys ≤
      K * (2 * S GA keys / B + 2 / W) := fun GA keys =>
    maxDevVar_le (withExpandA prims GA) (A GA) hp hβ0 hβt hθ0 hs1 keys
  have hES : ∀ keys, 𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l, S GA keys ≤ n * ε :=
    fun keys => by
      simp only [S]
      rw [Finset.expect_sum_comm]
      calc ∑ u, 𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l,
            commitCollision (GA (prims.expandSeed (keys u)).1)
          = ∑ _u : Fin n, 𝔼 aHat : TqMatrix p.k p.l, commitCollision aHat :=
            Finset.sum_congr rfl fun u _ =>
              PMF.expect_apply_eval (prims.expandSeed (keys u)).1 commitCollision
        _ ≤ ∑ _u : Fin n, ε := Finset.sum_le_sum fun u _ => hε
        _ = n * ε := by rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hlin : ∀ keys, 𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l,
      K * (2 * S GA keys / B + 2 / W) * a / 2 =
        K * a / B * 𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l, S GA keys + K * a / W :=
    fun keys => by
      have h : ∀ GA, K * (2 * S GA keys / B + 2 / W) * a / 2 = K * a / B * S GA keys + K * a / W :=
        fun GA => by ring
      simp_rw [h]
      rw [Finset.expect_add_distrib, ← Finset.mul_expect, Finset.expect_const univ_nonempty]
  calc 𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l, 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
        √(maxDevVar (withExpandA prims GA) (A GA) hp hβ0 hβt s θ keys * a / 2)
      ≤ 𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l, 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
          √(K * (2 * S GA keys / B + 2 / W) * a / 2) :=
        Finset.expect_le_expect fun GA _ => Finset.expect_le_expect fun keys _ =>
          Real.sqrt_le_sqrt (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hpt GA keys) ha) zero_le_two)
    _ ≤ 𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l,
          √(𝔼 keys : Fin n → _root_.MLDSA.Bytes 32, K * (2 * S GA keys / B + 2 / W) * a / 2) :=
        Finset.expect_le_expect fun GA _ =>
          Real.expect_sqrt_le_sqrt_expect _ fun keys => hD0 GA keys
    _ ≤ √(𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l,
          𝔼 keys : Fin n → _root_.MLDSA.Bytes 32, K * (2 * S GA keys / B + 2 / W) * a / 2) :=
        Real.expect_sqrt_le_sqrt_expect _ fun GA =>
          Finset.expect_nonneg fun keys _ => hD0 GA keys
    _ ≤ √(K * (2 * n * ε / B + 2 / W) * a / 2) := by
        refine Real.sqrt_le_sqrt ?_
        rw [Finset.expect_comm]
        refine (Finset.expect_le_expect fun keys _ => ?_).trans_eq
          (Finset.expect_const univ_nonempty _)
        rw [hlin keys]
        have hc : 0 ≤ K * a / B := div_nonneg (mul_nonneg hK ha) hB
        calc K * a / B * 𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l, S GA keys + K * a / W
            ≤ K * a / B * (n * ε) + K * a / W :=
              add_le_add (mul_le_mul_of_nonneg_left (hES keys) hc) le_rfl
          _ = K * (2 * n * ε / B + 2 / W) * a / 2 := by ring

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The weight term with `ExpandA` a random oracle**: for `a ≥ 0`,
`𝔼_{G_A, keys} √(maxCountVar · a / 2) ≤ √(N / ((1 - θ)² (1 - s)² |V|) · a / 2)`
(`maxCountVar_le`). -/
theorem expect_sqrt_maxCountVar_le (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    {s θ : ℝ} (hθ1 : θ < 1) (hs1 : s < 1) {a : ℝ} (ha : 0 ≤ a) :
    𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l, 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
        √(maxCountVar (withExpandA prims GA) (A GA) hp hβ0 hβt s θ keys * a / 2) ≤
      √(N / ((1 - θ) ^ 2 * (1 - s) ^ 2 * Fintype.card (BucketVec p)) * a / 2) := by
  refine (Finset.expect_le_expect fun GA _ => (Finset.expect_le_expect fun keys _ =>
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (maxCountVar_le (withExpandA prims GA) (A GA) hp hβ0 hβt hθ1 hs1 keys) ha)
        zero_le_two)).trans_eq (Finset.expect_const univ_nonempty _)).trans_eq
    (Finset.expect_const univ_nonempty _)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The McDiarmid terms with `ExpandA` a random oracle**: for any bound `ε` on `𝔼_Â CP(Â)`,
`𝔼_{G_A, keys} (√(maxDevVar · log C / 2) + √(maxCountVar · log (C + 1) / 2))` is at most
`√(4N / (θ (1 - s))² · (2 n ε / (β |V|)² + 2/|V|) · log C / 2) +
√(N / ((1 - θ)² (1 - s)² |V|) · log (C + 1) / 2)` (`expect_sqrt_maxDevVar_le`,
`expect_sqrt_maxCountVar_le`). -/
theorem expect_mcDiarmidTerms_le [NTTRingLaws nttOps] (hp : SigningParams p)
    (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) {s θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) {ε : ℝ}
    (hε : 𝔼 aHat : TqMatrix p.k p.l, commitCollision aHat ≤ ε) (C : ℕ) :
    𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l, 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
        (√(maxDevVar (withExpandA prims GA) (A GA) hp hβ0 hβt s θ keys * Real.log C / 2) +
          √(maxCountVar (withExpandA prims GA) (A GA) hp hβ0 hβt s θ keys *
            Real.log (C + 1) / 2)) ≤
      √(4 * N / (θ * (1 - s)) ^ 2 * (2 * n * ε /
          ((standinScale p * βmin).toReal * Fintype.card (BucketVec p)) ^ 2 +
        2 / Fintype.card (BucketVec p)) * Real.log C / 2) +
      √(N / ((1 - θ) ^ 2 * (1 - s) ^ 2 * Fintype.card (BucketVec p)) * Real.log (C + 1) / 2) := by
  have ha : 0 ≤ Real.log C := Real.log_natCast_nonneg C
  have ha' : 0 ≤ Real.log (C + 1) := by exact_mod_cast Real.log_natCast_nonneg (C + 1)
  simp only [Finset.expect_add_distrib]
  exact add_le_add (expect_sqrt_maxDevVar_le prims A hp hβ0 hβt hθ0 hs1 hε ha)
    (expect_sqrt_maxCountVar_le prims A hp hβ0 hβt hθ1 hs1 ha')

end Oracle

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

section Explicit

variable {p : Params} (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)] {Msg : Type} [Fintype Msg] [DecidableEq Msg] [Inhabited prims.Hint]
  [Fintype prims.Hint] [Fintype prims.Power2High] [DecidableEq prims.Power2High]
  [DecidableEq prims.Hint]
  {N : ℕ} {βmin : ℚ≥0} {reps tol : ℕ} {enc : Vector prims.High p.k → BucketVec p}
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)]
  {M : ∀ GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l,
    SPBCS Mg P (pubSigner (withExpandA prims GA) (Msg := Msg) N βmin reps tol enc).Stmt k kN kS L e}
  {n Q : ℕ}
  (A : ∀ GA, PubAnonAdversary (pubSigner (withExpandA prims GA) (Msg := Msg) N βmin reps tol enc)
    (M GA) n Q)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The McDiarmid terms below `2^-2000`**: if the collision bound is at most `2^-4352`, the
stand-in scale satisfies `K |V| ≥ 1/16` and `|V| ≥ 2^4100`, then for `β_min ∈ (0, 1]`,
`θ ∈ (0, 1)`, `s < 1` and `n ≥ 1`,
`𝔼_{G_A, keys} (√(maxDevVar · log C / 2) + √(maxCountVar · log (C + 1) / 2)) ≤
√(N n log (C + 1)) / (2^2000 · θ (1 - θ) (1 - s) β_min)` (`expect_mcDiarmidTerms_le`,
`expect_commitCollision_le`, `sqrt_add_sqrt_le_of_le` with `ε = 2^-4352`, `L = 1/16` and
`c = 2^-2001`). -/
theorem expect_mcDiarmidTerms_le_of [NTTRingLaws nttOps] (hp : SigningParams p)
    (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1) (hβt : (βmin : ℝ≥0∞) ≠ ⊤) {s θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hs1 : s < 1) [NeZero n] (C : ℕ) (hCP : commitCollisionBound p ≤ (1 / 2 ^ 17) ^ ringDegree)
    (hK : 1 / 16 ≤ (standinScale p).toReal * Fintype.card (BucketVec p))
    (hV : (2 : ℝ) ^ 4100 ≤ Fintype.card (BucketVec p)) :
    𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix p.k p.l, 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
        (√(maxDevVar (withExpandA prims GA) (A GA) hp hβ0 hβt s θ keys * Real.log C / 2) +
          √(maxCountVar (withExpandA prims GA) (A GA) hp hβ0 hβt s θ keys *
            Real.log (C + 1) / 2)) ≤
      √(N * n * Real.log (C + 1)) / (2 ^ 2000 * (θ * (1 - θ) * (1 - s) * (βmin : ℝ≥0∞).toReal)) :=
        by
  have hW : (0 : ℝ) < Fintype.card (BucketVec p) := lt_of_lt_of_le (by positivity) hV
  have hb0 : 0 < (βmin : ℝ≥0∞).toReal := ENNReal.toReal_pos hβ0 hβt
  have hb1 : (βmin : ℝ≥0∞).toReal ≤ 1 := ENNReal.toReal_le_one_of_le_one hβ1
  have hn : (1 : ℝ) ≤ n := Nat.one_le_cast.2 (Nat.pos_of_ne_zero (NeZero.ne n))
  have hlog : Real.log C ≤ Real.log (C + 1) := by
    rcases Nat.eq_zero_or_pos C with rfl | hC
    · simp
    · exact Real.log_le_log (by exact_mod_cast hC) (by linarith)
  have hbound : 4 * ((1 / 2 ^ 17) ^ ringDegree) / (1 / 16) ^ 2 +
      4 / (Fintype.card (BucketVec p) : ℝ) ≤ (1 / 2 ^ 2001 : ℝ) ^ 2 := by
    have h4 : 4 / (Fintype.card (BucketVec p) : ℝ) ≤ 4 / 2 ^ 4100 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hV
    have hnum := four_mul_div_add_four_div_le
    change 4 * ((1 / 2 ^ 17 : ℝ) ^ 256) / (1 / 16) ^ 2 + 4 / (Fintype.card (BucketVec p) : ℝ) ≤
      (1 / 2 ^ 2001 : ℝ) ^ 2
    exact (add_le_add le_rfl h4).trans hnum
  have hX : 1 / 16 * (βmin : ℝ≥0∞).toReal ≤
      (standinScale p * βmin).toReal * Fintype.card (BucketVec p) := by
    rw [ENNReal.toReal_mul, mul_right_comm]
    exact mul_le_mul_of_nonneg_right hK hb0.le
  refine (expect_mcDiarmidTerms_le prims A hp hβ0 hβt hθ0 hθ1 hs1
    ((expect_commitCollision_le hp).trans hCP) C).trans ?_
  refine (sqrt_add_sqrt_le_of_le (Nat.cast_nonneg N) hn hθ0 hθ1 hs1 hb0 hb1
    (Real.log_natCast_nonneg C) hlog hW (by norm_num) (by positivity) (by positivity) hbound
    hX).trans_eq ?_
  field_simp

end Explicit

end GordieHowe.Ring.MLDSAW1
