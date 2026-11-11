-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1RefusalLoop
public import GordieHowe.Applications.Ring.MLDSAW1Completeness
public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1Refusal

@[expose] public section

/-!
# The refusal rate of the ML-DSA ring signature publishing `w₁`

The base signer of the ring publishing `w₁` refuses an honest ring when the public ring check
fails, when two members' message representatives `µ_j` collide, or when all `k` calls of the ring
loop reject. This file bounds the refusal probability of completeness (`BaseSigner.refuseProb`)
by these three terms, at concrete key generation, with the regularity and collision terms as the
averages `regGapAt` and `collAt` of one honest key (as in the anonymity headlines of
`MLDSAW1IdealDist.lean`), and two named hypotheses.

- `checkDefectMgf`, `W1CheckDefectMgf`, `w1CheckDefectMgf_pow`: **a conjecture**. The moment
  `𝔼_seed (1 + (x - 1) δ(seed))^reps` of an honest key's check defect `δ` (`checkDefect`, the
  probability over a uniform commitment hash that the key's check weight is below `β_min`) is at
  most `B`. This is the quantity that `expect_not_ringCheck_honestRing_le` reads. It is satisfiable
  at `B = x^reps` (`δ ≤ 1`).
- `HonestTrDistinct`, `honestTrDistinct_one`: **a named assumption**. Over `r` independent uniform
  key seeds, two members share the hash `tr = H(pkEncode(ρ, t₁), 64)` of their public keys with
  probability at most `ε`. It is satisfiable at `ε = 1`.
- `w1RefusalError`, `refuseProb_hedgedBase_le`: the refusal probability of the hedged base signer
  for `r` members is at most the check term `x^-(tol+1) B^r`, the collision term
  `ε + r² / 2^512`, the nonce-collision term `C(k, 2) / 2^256`, the family term (twice the
  regularity and McDiarmid terms of `expect_lowError_le` at `r` users, averaged over the keys),
  `k / D + (1 - Lk)^k` for the loop, and the defect term `r · (B - 1) / (reps (x - 1) s)` for a ring
  of defect above `s`.

## The conjecture `W1CheckDefectMgf`

It is a statement about this construction's own public check, and no published source states
it. Its only support is the numerical estimate in
`GordieHowe/Applications/Ring/PublicW1/README.md` (section "The check parameters"): an honest
check sample fails with probability about `7·10^-9` at ML-DSA-44 (the exact 39-fold convolution of
the ct₀ tail), and about `10^-23` at ML-DSA-65 by extrapolating the measured tail of the honest
check weights. The formalized bounds control only the mean over the challenge of the hint-count
bound that the check weight reads, and that mean alone does not bound `δ`.

## The assumption `HonestTrDistinct`

Two honest keys share `tr` when their seeds collide (probability `2^-256` per pair) or through a
collision of SHAKE256: of `H(ξ ‖ k ‖ ℓ, 128)` (FIPS 204 Algorithm 6 line 1) or of
`tr = H(pkEncode(ρ, t₁), 64)` (line 9). NIST FIPS 202, Appendix A.1, Table 4 ("Security strengths
of the SHA-1, SHA-2, and SHA-3 functions") gives SHAKE256 with output size `d` a collision
strength of `min(d/2, 256)` bits (checked against the NIST publication), which is 256 bits at the
512-bit `tr` and at the 1024-bit output of line 1. The named instances take
`ε = C(r, 2) · 2^-255`.
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.MLDSA.Regularity GordieHowe.RingSignature PMF
open scoped ENNReal NNReal BigOperators

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}

/-! ### The two named hypotheses -/

section Hypotheses

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint]

/-- **The check-defect moment of an honest key**: `𝔼_seed (1 + (x - 1) δ(seed))^reps`, with
`δ(seed)` the check defect of the published `t₀` of the key of `seed`. -/
noncomputable def checkDefectMgf (βmin : ℚ≥0) (x : ℝ) (reps : ℕ) : ℝ :=
  𝔼 seed : Bytes 32, (1 + (x - 1) * checkDefect prims (Cutoff.const βmin) (keyGen prims
      seed).1.2.2) ^ reps

omit [NeZero (bucketCount p)] [Fintype prims.Hint] [DecidableEq prims.Hint] in
/-- The check-defect moment is nonnegative for `x ≥ 1`. -/
theorem checkDefectMgf_nonneg (βmin : ℚ≥0) {x : ℝ} (hx : 1 ≤ x) (reps : ℕ) :
    0 ≤ checkDefectMgf prims βmin x reps :=
  Finset.expect_nonneg fun seed _ => pow_nonneg (by
    have := checkDefect_nonneg prims (Cutoff.const βmin) (keyGen prims seed).1.2.2
    nlinarith) _

/-- **The check-defect conjecture** (see the module docstring): the check-defect moment of an
honest key is at most `B`. A conjecture about this construction, supported only by the numerical
estimate of `GordieHowe/Applications/Ring/PublicW1/README.md`. -/
def W1CheckDefectMgf (βmin : ℚ≥0) (x : ℝ) (reps : ℕ) (B : ℝ) : Prop :=
  checkDefectMgf prims βmin x reps ≤ B

omit [NeZero (bucketCount p)] [Fintype prims.Hint] [DecidableEq prims.Hint] in
/-- The check-defect conjecture holds at `B = x^reps`, since the check defect is at most `1`. -/
theorem w1CheckDefectMgf_pow (βmin : ℚ≥0) {x : ℝ} (hx : 1 ≤ x) (reps : ℕ) :
    W1CheckDefectMgf prims βmin x reps (x ^ reps) := by
  refine (Finset.expect_le_expect fun seed _ => ?_).trans_eq
    (Finset.expect_const Finset.univ_nonempty _)
  have h0 := checkDefect_nonneg prims (Cutoff.const βmin) (keyGen prims seed).1.2.2
  have h1 := checkDefect_le_one prims (Cutoff.const βmin) (keyGen prims seed).1.2.2
  refine pow_le_pow_left₀ (by nlinarith) ?_ reps
  nlinarith

/-- **Honest keys have distinct public-key hashes** except with probability `ε`: over `r`
independent uniform key seeds, the hashes `tr_j` of the members' public keys are pairwise distinct
except with probability at most `ε` (a named assumption, see the module docstring). Its
justification is the collision strength of SHAKE256 in NIST FIPS 202, Appendix A.1, Table 4
("Security strengths of the SHA-1, SHA-2, and SHA-3 functions"): `min(d/2, 256)` bits at output
size `d` (checked against the NIST publication). -/
def HonestTrDistinct (r : ℕ) (ε : ℝ) : Prop :=
  𝔼 seeds : Fin r → Bytes 32,
    (if (List.ofFn fun j => pubTr prims (keyGen prims (seeds j)).1).Nodup then 0 else 1 : ℝ) ≤ ε

omit [NeZero (bucketCount p)] [Fintype prims.Power2High] [DecidableEq prims.Power2High]
  [Fintype prims.Hint] [DecidableEq prims.Hint] in
/-- `HonestTrDistinct` is monotone in `ε`. -/
theorem HonestTrDistinct.mono {r : ℕ} {ε ε' : ℝ} (h : HonestTrDistinct prims r ε) (hε : ε ≤ ε') :
    HonestTrDistinct prims r ε' :=
  le_trans h hε

omit [NeZero (bucketCount p)] [Fintype prims.Power2High] [DecidableEq prims.Power2High]
  [Fintype prims.Hint] [DecidableEq prims.Hint] in
/-- `HonestTrDistinct` holds at `ε = 1`. -/
theorem honestTrDistinct_one (r : ℕ) : HonestTrDistinct prims r 1 :=
  (Finset.expect_le_expect fun _ _ => by split_ifs <;> norm_num).trans_eq
    (Finset.expect_const Finset.univ_nonempty _)

end Hypotheses

/-! ### Refusal probabilities as averages -/

section Averages

variable {X' Y' : Type} [Fintype X'] [DecidableEq X'] [Fintype Y'] [Nonempty Y'] {N' : ℕ}

/-- **The refusal probability of completeness as an average**: over a uniform oracle and uniform
key coins of the `r` members, the refusal mass of the signer `s` on the honest ring when the ring
is supported, and `0` otherwise. -/
theorem _root_.GordieHowe.RingSignature.BaseSigner.toReal_refuseProb_eq
    {TB : BaseTypes} [DecidableEq TB.PK]
    [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [Nonempty TB.KeyCoins]
    [Fintype TB.Coins] [Nonempty TB.Coins] (B : BaseSigner X' Y' N' TB)
    (adm : KeyRing B.PK N' → Prop) [DecidablePred adm] {r : ℕ}
    (hr : r ≤ N') (s : Fin r) (m : B.Msg) :
    (B.refuseProb adm hr s m).toReal =
      𝔼 H : X' → Y', 𝔼 keys : Fin r → B.KeyCoins, if adm (B.honestRing hr keys) then
        (B.refusalPubLaw H (keys s) (B.honestRing hr keys) m none).toReal else 0 := by
  classical
  unfold BaseSigner.refuseProb
  change (IOP.probUniform _ fun d : B.RefusalDraw r => adm (B.honestRing hr d.2.1) ∧
    (B.bsign (B.sk (d.2.1 s)) (B.honestRing hr d.2.1)
      ((B.honestRing hr d.2.1).1.idxOf (B.pk (d.2.1 s))) m d.2.2).run d.1 = none).toReal = _
  rw [IOP.toReal_probUniform, ← Finset.univ_product_univ, Finset.expect_product]
  refine Finset.expect_congr rfl fun H _ => ?_
  rw [← Finset.univ_product_univ, Finset.expect_product]
  refine Finset.expect_congr rfl fun keys _ => ?_
  by_cases ha : adm (B.honestRing hr keys)
  · simp only [ha, ↓reduceIte, true_and, BaseSigner.toReal_refusalPubLaw_none,
      Option.isNone_iff_eq_none]
  · simp only [ha, false_and, ↓reduceIte, Finset.expect_const_zero]

end Averages

/-! ### The refusal bound -/

section Bound

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg]
  [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-- **The refusal error of the ring publishing `w₁`** for `r` members, rings of at most `N` keys,
at most `C` valid challenges per key vector of the `r` members, `k` calls with keep coins on
`Fin D`, the defect budget `s`, the threshold fraction `θ`, the keep level `Lk`, the check
parameters `(reps, tol, x)`, a bound `B` on the check-defect moment and `ε` on the collisions of
the members' `tr`: the check term, the `µ` collision term, the nonce-collision term, the family and
loop terms, and the defect term. -/
noncomputable def w1RefusalError (βmin : ℚ≥0) (N r : ℕ) (s θ : ℝ) (C k D : ℕ) (Lk : ℝ)
    (reps tol : ℕ) (x B ε : ℝ) : ℝ :=
  (x ^ (tol + 1))⁻¹ * B ^ r + (ε + r ^ 2 / Fintype.card (Bytes 64)) +
    (k.choose 2 : ℝ) / 2 ^ 256 +
    (2 * (2 * (1 - s)⁻¹ / θ * (r * regGapAt prims βmin) +
        √(4 * N / (θ * (1 - s)) ^ 2 *
            (2 * (r * collAt prims) /
                ((standinScale p * βmin).toReal * Fintype.card (BucketVec p)) ^ 2 +
              2 / Fintype.card (BucketVec p)) * Real.log C / 2) +
        √(N / ((1 - θ) ^ 2 * (1 - s) ^ 2 * Fintype.card (BucketVec p)) * Real.log (C + 1) / 2)) +
      k * (D : ℝ)⁻¹ + (1 - Lk) ^ k) +
    r * ((B - 1) / (reps * (x - 1))) / s

/-! #### The check, collision and defect terms -/

section Terms

variable [Fintype X] [DecidableEq X] (O : W1Oracles X Y p prims Msg N reps) (βmin : ℚ≥0)
  (tol : ℕ)

omit [NeZero (bucketCount p)] [Fintype prims.Hint] [DecidableEq prims.Hint] [Inhabited prims.Hint]
  [Nonempty (MaskBox p)] [DecidableEq Y] in
open Classical in
/-- **An honest ring fails the check at a uniform oracle with probability at most
`x^-(tol+1) B^r`** under the check-defect conjecture at `B`: the check oracle read off a uniform
oracle is uniform (`W1Oracles.expect_gameOrc`), and `expect_not_ringCheck_honestRing_le`. -/
theorem expect_not_ringCheck_gOrc_le (hO : O.UniformSplit) {r : ℕ} (hr : r ≤ N) {x B : ℝ}
    (hx : 1 ≤ x) (hB : W1CheckDefectMgf prims βmin x reps B) :
    𝔼 H : X → Y, 𝔼 keys : Fin r → Bytes 32,
      (if RingCheck prims βmin tol (O.gOrc H) (honestRing prims keys hr) then 0 else 1 : ℝ) ≤
        (x ^ (tol + 1))⁻¹ * B ^ r := by
  rw [Finset.expect_comm]
  have h1 : ∀ keys : Fin r → Bytes 32, 𝔼 H : X → Y,
      (if RingCheck prims βmin tol (O.gOrc H) (honestRing prims keys hr) then 0 else 1 : ℝ) =
        𝔼 G : CheckOrc p prims N reps,
          (if RingCheck prims βmin tol G (honestRing prims keys hr) then 0 else 1 : ℝ) :=
    fun keys => (O.expect_gameOrc hO fun HG =>
        if RingCheck prims βmin tol HG.2 (honestRing prims keys hr) then 0 else 1).trans
      (Finset.expect_comp_snd fun G =>
        if RingCheck prims βmin tol G (honestRing prims keys hr) then 0 else 1)
  rw [Finset.expect_congr rfl fun keys _ => h1 keys]
  refine (expect_not_ringCheck_honestRing_le prims βmin tol hr hx).trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (checkDefectMgf_nonneg prims βmin hx reps)
    hB r) (inv_nonneg.2 (pow_nonneg (by linarith) _))

omit [NeZero (bucketCount p)] [Fintype prims.Hint] [DecidableEq prims.Hint] [Inhabited prims.Hint]
  [Nonempty (MaskBox p)] [DecidableEq Y] in
open Classical in
/-- **Two members of an honest ring share a message representative at a uniform oracle with
probability at most `ε + r² / 2^512`** under the `tr`-collision assumption at `ε`: the
message-representative oracle read off a uniform oracle is uniform, and
`expect_not_muDistinct_le` for a ring of distinct `tr`. -/
theorem expect_not_muDistinct_muOrc_le (hO : O.UniformSplit) {r : ℕ} (hr : r ≤ N) {ε : ℝ}
    (hε : HonestTrDistinct prims r ε) (f : RingOf (PubKey p prims) N → Msg) :
    𝔼 H : X → Y, 𝔼 keys : Fin r → Bytes 32,
      (if MuDistinct prims (O.muOrc H) (honestRing prims keys hr) (f (honestRing prims keys hr))
        then 0 else 1 : ℝ) ≤
        ε + r ^ 2 / Fintype.card (Bytes 64) := by
  rw [Finset.expect_comm]
  have hc0 : (0 : ℝ) ≤ r ^ 2 / Fintype.card (Bytes 64) := by positivity
  have h1 : ∀ keys : Fin r → Bytes 32, 𝔼 H : X → Y,
      (if MuDistinct prims (O.muOrc H) (honestRing prims keys hr) (f (honestRing prims keys hr))
        then 0 else 1 : ℝ) ≤
        (if (List.ofFn fun j => pubTr prims (keyGen prims (keys j)).1).Nodup then 0 else 1) +
          r ^ 2 / Fintype.card (Bytes 64) := fun keys => by
    have he : 𝔼 H : X → Y, (if MuDistinct prims (O.muOrc H) (honestRing prims keys hr)
          (f (honestRing prims keys hr)) then 0 else 1 : ℝ) =
        𝔼 Hmu : MuOrc Msg, (if MuDistinct prims Hmu (honestRing prims keys hr)
          (f (honestRing prims keys hr)) then 0 else 1 : ℝ) :=
      (O.expect_gameOrc hO fun HG => if MuDistinct prims HG.1.1 (honestRing prims keys hr)
          (f (honestRing prims keys hr)) then 0 else 1).trans
        ((Finset.expect_comp_fst fun SH : SchOrc p Msg => if MuDistinct prims SH.1
            (honestRing prims keys hr) (f (honestRing prims keys hr)) then (0 : ℝ) else 1).trans
          (Finset.expect_comp_fst fun Hmu : MuOrc Msg => if MuDistinct prims Hmu
            (honestRing prims keys hr) (f (honestRing prims keys hr)) then (0 : ℝ) else 1))
    rw [he]
    by_cases hnd : (List.ofFn fun j => pubTr prims (keyGen prims (keys j)).1).Nodup
    · have htr : ((honestRing prims keys hr).1.map (pubTr prims)).Nodup := by
        change (List.map (pubTr prims) (List.ofFn fun j => (keyGen prims (keys j)).1)).Nodup
        rw [List.map_ofFn]
        exact hnd
      have hlen : (honestRing prims keys hr).1.length = r := List.length_ofFn
      simp only [hnd, ↓reduceIte, zero_add]
      exact (expect_not_muDistinct_le prims (honestRing prims keys hr)
        (f (honestRing prims keys hr)) htr).trans_eq
        (congrArg (fun t : ℕ => (t : ℝ) ^ 2 / (Fintype.card (Bytes 64) : ℝ)) hlen)
    · simp only [hnd, ↓reduceIte]
      refine le_add_of_le_of_nonneg ?_ hc0
      exact (Finset.expect_le_expect fun _ _ => by split_ifs <;> norm_num).trans_eq
        (Finset.expect_const Finset.univ_nonempty _)
  refine (Finset.expect_le_expect fun keys _ => h1 keys).trans ?_
  rw [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty]
  have h := hε
  unfold HonestTrDistinct at h
  linarith

omit [Fintype X] [DecidableEq X] [NeZero (bucketCount p)] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] [Nonempty (MaskBox p)] in
open Classical in
/-- **An honest ring has defect above `s` with probability at most
`r · (B - 1) / (reps (x - 1) s)`** under the check-defect conjecture at `B`: Markov's inequality
for the defect `∑_j δ_j`, and `1 + reps (x - 1) δ ≤ (1 + (x - 1) δ)^reps` (Bernoulli's
inequality) bounds the mean defect of one honest key by `(B - 1) / (reps (x - 1))`. -/
theorem expect_ringDefect_gt_le {r : ℕ} (hr : r ≤ N) {s x B : ℝ} (hs0 : 0 < s) (hx : 1 < x)
    (hreps : 0 < reps) (hB : W1CheckDefectMgf prims βmin x reps B) :
    𝔼 keys : Fin r → Bytes 32,
      (if s < ringDefect prims βmin (honestRing prims keys hr).1 then 1 else 0 : ℝ) ≤
        r * ((B - 1) / (reps * (x - 1))) / s := by
  have hpos : (0 : ℝ) < reps * (x - 1) := mul_pos (by exact_mod_cast hreps) (by linarith)
  have hδ : 𝔼 seed : Bytes 32, checkDefect prims (Cutoff.const βmin) (keyGen prims seed).1.2.2 ≤
      (B - 1) / (reps * (x - 1)) := by
    rw [le_div_iff₀ hpos]
    have hb : ∀ seed : Bytes 32, 1 + reps * ((x - 1) *
        checkDefect prims (Cutoff.const βmin) (keyGen prims seed).1.2.2) ≤
        (1 + (x - 1) * checkDefect prims (Cutoff.const βmin) (keyGen prims seed).1.2.2) ^ reps :=
            fun seed =>
      one_add_mul_le_pow (by
        have := checkDefect_nonneg prims (Cutoff.const βmin) (keyGen prims seed).1.2.2
        nlinarith) reps
    have h2 := (Finset.expect_le_expect fun seed _ => hb seed).trans hB
    rw [Finset.expect_add_distrib, Finset.expect_const Finset.univ_nonempty, ← Finset.mul_expect,
      ← Finset.mul_expect] at h2
    linarith
  have hsum : ∀ keys : Fin r → Bytes 32, ringDefect prims βmin (honestRing prims keys hr).1 =
      ∑ j : Fin r, checkDefect prims (Cutoff.const βmin) (keyGen prims (keys j)).1.2.2 := fun keys
          => by
    refine Fintype.sum_equiv (finCongr (List.length_ofFn)) _ _ fun j => ?_
    simp only [ringT0s, honestRing, List.get_eq_getElem, List.getElem_ofFn]
    rfl
  have hpt : ∀ keys : Fin r → Bytes 32,
      (if s < ringDefect prims βmin (honestRing prims keys hr).1 then 1 else 0 : ℝ) ≤
        ringDefect prims βmin (honestRing prims keys hr).1 / s := fun keys => by
    have h0 : 0 ≤ ringDefect prims βmin (honestRing prims keys hr).1 :=
      Finset.sum_nonneg fun j _ => checkDefect_nonneg prims (Cutoff.const βmin) _
    split_ifs with h
    · rw [le_div_iff₀ hs0]
      linarith
    · positivity
  refine (Finset.expect_le_expect fun keys _ => hpt keys).trans ?_
  rw [← Finset.expect_div]
  refine div_le_div_of_nonneg_right ?_ hs0.le
  simp only [hsum]
  rw [Finset.expect_sum_comm, Finset.sum_congr rfl fun j _ => PMF.expect_apply_eval j
    (fun x => checkDefect prims (Cutoff.const βmin) (keyGen prims x).1.2.2)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg _)

end Terms

/-! #### The loop term and the bound -/

variable (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg) (βmin : ℚ≥0)
  (tol : ℕ) (enc : Vector prims.High p.k → BucketVec p) (k D : ℕ) [NeZero D] {RMsg : Type}
  [Fintype RMsg] [DecidableEq RMsg] (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg)
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] (PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS)
  (adm : KeyRing (PubKey p prims) N → Prop) [DecidablePred adm]
  (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)

local notation "Bh" => hedgedBase prims O M βmin tol enc k D bmsg
local notation "Bf" => freshBase prims O M βmin tol enc k D bmsg
local notation "Sh" => hedgedScheme prims O M βmin tol enc k D bmsg PS adm

include hp hβ0 hβt in
open Classical in
omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] in
/-- **The loop term**: averaged over a uniform oracle and the members' key coins, the probability
that the ring passes the check, has distinct message representatives, and the hedged loop of the
signer `sI` rejects all `k` calls is at most the nonce-collision term `C(k, 2) / 2^256`, twice the
average family bound (`expect_lowError_le`, averaged over the keys), `k / D + (1 - Lk)^k`, and the
defect term (`expect_mul_refusalPubLaw_hedged_le`, `refusalPubLaw_freshBase_none_le`,
`expect_ringDefect_gt_le`). -/
theorem expect_loopRefusal_le [Fintype X] [DecidableEq X] (hT : 0 < T) (hO : O.UniformSplit)
    (hMask : (uniformOfFintype Y).map M.ans = uniformOfFintype (MaskBox p))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta) {s θ x Lk B : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs0 : 0 < s) (hs1 : s < 1) (hx : 1 < x)
    (hLk : Lk ≤ keepLevel p βmin s θ) (hLk1 : Lk ≤ 1) (hreps : 0 < reps) {r : ℕ} (hr : r ≤ N)
    {C : ℕ} (hC : ∀ keys : Fin r → Bytes 32,
      (Finset.univ.filter fun c : AnonRequest (Sh) r => c.Valid keys).card ≤ C)
    (hB : W1CheckDefectMgf prims βmin x reps B) (sI : Fin r) (m : RMsg) :
    𝔼 H : X → Y, 𝔼 keys : Fin r → Bytes 32,
      (if RingCheck prims βmin tol (O.gOrc H) (honestRing prims keys hr) ∧
          MuDistinct prims (O.muOrc H) (honestRing prims keys hr)
            (bmsg (honestRing prims keys hr) m) then 1 else 0) *
        ((Bh).refusalPubLaw H (keys sI) (honestRing prims keys hr) m none).toReal ≤
      (k.choose 2 : ℝ) / 2 ^ 256 +
        (2 * (2 * (1 - s)⁻¹ / θ * (r * regGapAt prims βmin) +
            √(4 * N / (θ * (1 - s)) ^ 2 *
                (2 * (r * collAt prims) /
                    ((standinScale p * βmin).toReal * Fintype.card (BucketVec p)) ^ 2 +
                  2 / Fintype.card (BucketVec p)) * Real.log C / 2) +
            √(N / ((1 - θ) ^ 2 * (1 - s) ^ 2 * Fintype.card (BucketVec p)) *
              Real.log (C + 1) / 2)) +
          k * (D : ℝ)⁻¹ + (1 - Lk) ^ k) +
        r * ((B - 1) / (reps * (x - 1))) / s := by
  set β := (standinScale p * βmin).toReal
  set W : ℝ := (Fintype.card (BucketVec p) : ℝ)
  set A : ℝ := 4 * N / (θ * (1 - s)) ^ 2
  set L : ℝ := Real.log C
  set sc : ℝ := N / ((1 - θ) ^ 2 * (1 - s) ^ 2 * W)
  set gap : (Fin r → Bytes 32) → ℝ := fun keys => ∑ u, signerRegGap prims (keyGen prims (keys u)).2
    (prims.expandA (keyGen prims (keys u)).2.rho) (Cutoff.const βmin)
  set cp : (Fin r → Bytes 32) → ℝ := fun keys =>
    ∑ u, commitCollision (prims.expandA (keyGen prims (keys u)).2.rho)
  have hcp0 : ∀ keys, 0 ≤ cp keys := fun keys =>
    Finset.sum_nonneg fun u _ => commitCollision_nonneg _
  have hLk0 : (0 : ℝ) ≤ (1 - Lk) ^ k := pow_nonneg (sub_nonneg.2 hLk1) _
  have hkD : (0 : ℝ) ≤ k * (D : ℝ)⁻¹ := by positivity
  -- the family bound averaged over a uniform oracle
  have hfam : ∀ keys : Fin r → Bytes 32, 𝔼 H : X → Y,
      lowError prims O M βmin tol enc k D bmsg PS adm r hp hβ0 hβt keys (O.muOrc H) s θ (O.chOrc H)
        ≤ 2 * (1 - s)⁻¹ / θ * gap keys + √(A * (2 * cp keys / (β * W) ^ 2 + 2 / W) * L / 2) +
          √(sc * Real.log (C + 1) / 2) := fun keys => by
    have he : 𝔼 H : X → Y, lowError prims O M βmin tol enc k D bmsg PS adm r hp hβ0 hβt keys
          (O.muOrc H) s θ (O.chOrc H) =
        𝔼 Hmu : MuOrc Msg, 𝔼 Hch : ChOrc p, lowError prims O M βmin tol enc k D bmsg PS adm r hp
          hβ0 hβt keys Hmu s θ Hch := by
      refine (O.expect_gameOrc hO fun HG => lowError prims O M βmin tol enc k D bmsg PS adm r hp
        hβ0 hβt keys HG.1.1 s θ HG.1.2).trans ?_
      rw [Finset.expect_comp_fst (fun SH : SchOrc p Msg => lowError prims O M βmin tol enc k D bmsg
        PS adm r hp hβ0 hβt keys SH.1 s θ SH.2), ← Finset.univ_product_univ, Finset.expect_product]
    rw [he]
    exact (Finset.expect_le_expect fun Hmu _ => expect_lowError_le hp hβ0 hβt h_laws hs2 hθ0 hθ1
      hs1 hC keys Hmu).trans_eq (Finset.expect_const Finset.univ_nonempty _)
  -- per key vector: hedged to fresh, then the fresh loop
  have hk : ∀ keys : Fin r → Bytes 32, 𝔼 H : X → Y,
      (if RingCheck prims βmin tol (O.gOrc H) (honestRing prims keys hr) ∧
          MuDistinct prims (O.muOrc H) (honestRing prims keys hr)
            (bmsg (honestRing prims keys hr) m) then 1 else 0) *
        ((Bh).refusalPubLaw H (keys sI) (honestRing prims keys hr) m none).toReal ≤
      (k.choose 2 : ℝ) / 2 ^ 256 +
        (2 * (2 * (1 - s)⁻¹ / θ * gap keys + √(A * (2 * cp keys / (β * W) ^ 2 + 2 / W) * L / 2) +
          √(sc * Real.log (C + 1) / 2)) + k * (D : ℝ)⁻¹ + (1 - Lk) ^ k) +
        (if s < ringDefect prims βmin (honestRing prims keys hr).1 then 1 else 0) := fun keys => by
    have h2 := expect_mul_refusalPubLaw_hedged_le prims O M βmin tol enc k D bmsg hM hdisj
      (keys sI) (honestRing prims keys hr) m
      (fun H => if RingCheck prims βmin tol (O.gOrc H) (honestRing prims keys hr) ∧
          MuDistinct prims (O.muOrc H) (honestRing prims keys hr)
            (bmsg (honestRing prims keys hr) m) then 1 else 0)
      (fun H => by split_ifs <;> norm_num) (fun H => by split_ifs <;> norm_num)
      (fun H H' h => by simp only [O.gOrc_eq_of_split h, O.muOrc_eq_of_split h])
    have hI0 : (0 : ℝ) ≤ if s < ringDefect prims βmin (honestRing prims keys hr).1 then 1 else 0 :=
      by split_ifs <;> norm_num
    have hfresh : ∀ H : X → Y,
        (if RingCheck prims βmin tol (O.gOrc H) (honestRing prims keys hr) ∧
          MuDistinct prims (O.muOrc H) (honestRing prims keys hr)
            (bmsg (honestRing prims keys hr) m) then 1 else 0) *
          ((Bf).refusalPubLaw H (keys sI) (honestRing prims keys hr) m none).toReal ≤
        2 * lowError prims O M βmin tol enc k D bmsg PS adm r hp hβ0 hβt keys (O.muOrc H) s θ
            (O.chOrc H) + k * (D : ℝ)⁻¹ + (1 - Lk) ^ k +
          (if s < ringDefect prims βmin (honestRing prims keys hr).1 then 1 else 0) := fun H => by
      have hF0 := lowError_nonneg (O := O) (M := M) (βmin := βmin) (tol := tol) (enc := enc)
        (k := k) (D := D) (bmsg := bmsg) (PS := PS) (adm := adm) hp hβ0 hβt hs1 hθ0 keys
        (O.muOrc H) (O.chOrc H)
      by_cases hok : RingCheck prims βmin tol (O.gOrc H) (honestRing prims keys hr) ∧
          MuDistinct prims (O.muOrc H) (honestRing prims keys hr)
            (bmsg (honestRing prims keys hr) m)
      · simp only [hok, and_self, ↓reduceIte, one_mul]
        exact refusalPubLaw_freshBase_none_le prims O M βmin tol enc k D bmsg PS adm r hp hβ0 hβt
          hT hMask h_laws hv henc hs2 hθ0 hθ1 hs1 hLk hLk1 H keys
          ⟨honestRing prims keys hr, m, sI, sI⟩
          ⟨List.mem_ofFn.2 ⟨sI, rfl⟩, List.mem_ofFn.2 ⟨sI, rfl⟩⟩ hok
      · simp only [hok, ↓reduceIte, zero_mul]
        linarith
    have h3 := Finset.expect_le_expect (s := Finset.univ) fun H (_ : H ∈ Finset.univ) => hfresh H
    rw [Finset.expect_add_distrib, Finset.expect_add_distrib, Finset.expect_add_distrib,
      ← Finset.mul_expect, Finset.expect_const Finset.univ_nonempty,
      Finset.expect_const Finset.univ_nonempty, Finset.expect_const Finset.univ_nonempty] at h3
    have h4 := hfam keys
    linarith
  -- the average over the members' key coins
  have hgap : 𝔼 keys : Fin r → Bytes 32, gap keys = r * regGapAt prims βmin := by
    simp only [gap]
    rw [Finset.expect_sum_comm, Finset.sum_congr rfl fun u _ => PMF.expect_apply_eval u
      (fun x => signerRegGap prims (keyGen prims x).2 (prims.expandA (keyGen prims x).2.rho)
          (Cutoff.const βmin))]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, regGapAt]
  have hcp : 𝔼 keys : Fin r → Bytes 32, cp keys = r * collAt prims := by
    simp only [cp]
    rw [Finset.expect_sum_comm, Finset.sum_congr rfl fun u _ => PMF.expect_apply_eval u
      (fun x => commitCollision (prims.expandA (keyGen prims x).2.rho))]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, collAt]
  have hsd : 𝔼 keys : Fin r → Bytes 32, √(A * (2 * cp keys / (β * W) ^ 2 + 2 / W) * L / 2) ≤
      √(A * (2 * (r * collAt prims) / (β * W) ^ 2 + 2 / W) * L / 2) := by
    have hL0 : 0 ≤ L := Real.log_natCast_nonneg C
    have hA0 : 0 ≤ A := by positivity
    refine (Real.expect_sqrt_le_sqrt_expect _ fun keys => by
      have := hcp0 keys
      positivity).trans (Real.sqrt_le_sqrt (le_of_eq ?_))
    have hlin : ∀ keys : Fin r → Bytes 32, A * (2 * cp keys / (β * W) ^ 2 + 2 / W) * L / 2 =
        (A * L / (β * W) ^ 2) * cp keys + A * (2 / W) * L / 2 := fun keys => by ring
    simp only [hlin]
    rw [Finset.expect_add_distrib, ← Finset.mul_expect, hcp,
      Finset.expect_const Finset.univ_nonempty]
    ring
  have hdef := expect_ringDefect_gt_le prims βmin hr hs0 hx hreps hB
  rw [Finset.expect_comm]
  refine (Finset.expect_le_expect fun keys _ => hk keys).trans ?_
  rw [Finset.expect_add_distrib, Finset.expect_add_distrib, Finset.expect_const
      Finset.univ_nonempty, Finset.expect_add_distrib, Finset.expect_add_distrib,
    Finset.expect_const Finset.univ_nonempty, Finset.expect_const Finset.univ_nonempty,
    ← Finset.mul_expect, Finset.expect_add_distrib, Finset.expect_add_distrib, ← Finset.mul_expect,
    Finset.expect_const Finset.univ_nonempty, hgap]
  linarith [hsd, hdef]

include hp hβ0 hβt in
open Classical in
omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] in
/-- **The refusal probability of the ring publishing `w₁`**: for `r ≤ N` honest members, every
signer position and message, the hedged base signer refuses an honest supported ring with
probability at most `w1RefusalError`, under the check-defect conjecture at `B` (`hB`) and the
`tr`-collision assumption at `ε` (`hε`), for at least one mask per call, a domain separation with
uniform decodings, a uniform mask decoding, disjoint and injective mask points, the signing and
verification laws, a coherent encoding, `‖s₂‖∞ ≤ η` for every honest key, the defect budget
`s ∈ (0, 1)`, `θ ∈ (0, 1)`, `x > 1`, `reps ≥ 1`, a keep level `Lk ≤ 1` at most `keepLevel`, and
`C` a bound on the valid challenges for every key vector of the `r` members. The refusal splits
into a failed check (`expect_not_ringCheck_gOrc_le`), a collision of message representatives
(`expect_not_muDistinct_muOrc_le`) and a rejecting loop on an admitted ring
(`expect_loopRefusal_le`). -/
theorem refuseProb_hedgedBase_le [Fintype X] [DecidableEq X] (hT : 0 < T) (hO : O.UniformSplit)
    (hMask : (uniformOfFintype Y).map M.ans = uniformOfFintype (MaskBox p))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta) {s θ x Lk B ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs0 : 0 < s) (hs1 : s < 1) (hx : 1 < x)
    (hLk : Lk ≤ keepLevel p βmin s θ) (hLk1 : Lk ≤ 1) (hreps : 0 < reps) {r : ℕ} (hr : r ≤ N)
    {C : ℕ} (hC : ∀ keys : Fin r → Bytes 32,
      (Finset.univ.filter fun c : AnonRequest (Sh) r => c.Valid keys).card ≤ C)
    (hB : W1CheckDefectMgf prims βmin x reps B) (hε : HonestTrDistinct prims r ε) (sI : Fin r)
    (m : RMsg) :
    ((Bh).refuseProb adm hr sI m).toReal ≤
      w1RefusalError prims βmin N r s θ C k D Lk reps tol x B ε := by
  refine (BaseSigner.toReal_refuseProb_eq (Bh) adm hr sI m).trans_le ?_
  change 𝔼 H : X → Y, 𝔼 keys : Fin r → Bytes 32, (if adm ((Bh).honestRing hr keys) then
      ((Bh).refusalPubLaw H (keys sI) ((Bh).honestRing hr keys) m none).toReal else 0) ≤ _
  have hpt : ∀ (H : X → Y) (keys : Fin r → Bytes 32),
      (if adm ((Bh).honestRing hr keys) then
          ((Bh).refusalPubLaw H (keys sI) ((Bh).honestRing hr keys) m none).toReal else 0) ≤
        (if RingCheck prims βmin tol (O.gOrc H) (honestRing prims keys hr) then 0 else 1) +
          (if MuDistinct prims (O.muOrc H) (honestRing prims keys hr)
            (bmsg (honestRing prims keys hr) m) then 0 else 1) +
          (if RingCheck prims βmin tol (O.gOrc H) (honestRing prims keys hr) ∧
              MuDistinct prims (O.muOrc H) (honestRing prims keys hr)
                (bmsg (honestRing prims keys hr) m) then 1 else 0) *
            ((Bh).refusalPubLaw H (keys sI) (honestRing prims keys hr) m none).toReal :=
    fun H keys => by
    have h0 : 0 ≤ ((Bh).refusalPubLaw H (keys sI) (honestRing prims keys hr) m none).toReal :=
      ENNReal.toReal_nonneg
    have h1 : ((Bh).refusalPubLaw H (keys sI) (honestRing prims keys hr) m none).toReal ≤ 1 :=
      ((ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _) ENNReal.one_ne_top).2
        (PMF.coe_le_one _ _)).trans_eq ENNReal.toReal_one
    have hI : ∀ q : Prop, [Decidable q] → (0 : ℝ) ≤ if q then 0 else 1 := fun q _ => by
      split_ifs <;> norm_num
    by_cases ha : adm ((Bh).honestRing hr keys)
    · simp only [ha, ↓reduceIte]
      change ((Bh).refusalPubLaw H (keys sI) (honestRing prims keys hr) m none).toReal ≤ _
      by_cases hc : RingCheck prims βmin tol (O.gOrc H) (honestRing prims keys hr) <;>
        by_cases hm : MuDistinct prims (O.muOrc H) (honestRing prims keys hr)
          (bmsg (honestRing prims keys hr) m) <;>
        simp only [hc, hm, and_self, and_false, false_and, ↓reduceIte, one_mul, zero_mul,
          add_zero, zero_add] <;> linarith
    · simp only [ha, ↓reduceIte]
      have := hI (RingCheck prims βmin tol (O.gOrc H) (honestRing prims keys hr))
      have := hI (MuDistinct prims (O.muOrc H) (honestRing prims keys hr)
        (bmsg (honestRing prims keys hr) m))
      have : (0 : ℝ) ≤ (if RingCheck prims βmin tol (O.gOrc H) (honestRing prims keys hr) ∧
          MuDistinct prims (O.muOrc H) (honestRing prims keys hr)
            (bmsg (honestRing prims keys hr) m) then 1 else 0) *
          ((Bh).refusalPubLaw H (keys sI) (honestRing prims keys hr) m none).toReal :=
        mul_nonneg (by split_ifs <;> norm_num) h0
      linarith
  refine (Finset.expect_le_expect fun H _ => Finset.expect_le_expect fun keys _ =>
    hpt H keys).trans ?_
  rw [Finset.expect_congr rfl fun H _ => (Finset.expect_add_distrib _ _ _).trans
    (congrArg (· + _) (Finset.expect_add_distrib _ _ _)), Finset.expect_add_distrib,
    Finset.expect_add_distrib]
  have hA := expect_not_ringCheck_gOrc_le prims O βmin tol hO hr hx.le hB
  have hBm := expect_not_muDistinct_muOrc_le prims O hO hr hε fun l => bmsg l m
  have hC' := expect_loopRefusal_le prims O M βmin tol enc k D bmsg PS adm hp hβ0 hβt hT hO hMask
    hM hdisj h_laws hv henc hs2 hθ0 hθ1 hs0 hs1 hx hLk hLk1 hreps hr hC hB sI m
  unfold w1RefusalError
  linarith

end Bound


/-! ### Every ring size, and the completeness headlines -/

section Concrete

open _root_.MLDSA.Concrete GordieHowe.MLDSA.Spec

attribute [local instance] concreteNTTRingOps

variable [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
  {O : W1Oracles X Y p (concretePrimitivesKeyGen p) Msg N reps} {M : MaskOracle X Y p T Msg}
  {βmin : ℚ≥0} {tol k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
  {bmsg : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → RMsg → Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase p O M βmin tol k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))) TPS}
  {adm : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → Prop} [DecidablePred adm]

omit [NeZero D] in
/-- **The refusal error grows with the ring size**: for `r ≤ N`, `B ≥ 1`, `x > 1`, `reps ≥ 1`,
`s ∈ (0, 1)` and `θ ∈ (0, 1)`, the refusal error at `r` members is at most the one at `N`. -/
theorem w1RefusalError_le_of_le (prims : Primitives p) [Fintype prims.Power2High]
    [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
    [Inhabited prims.Hint] {s θ x Lk B ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs0 : 0 < s)
    (hs1 : s < 1) (hx : 1 < x) (hreps : 0 < reps) (hB1 : 1 ≤ B) {C r : ℕ} (hr : r ≤ N) :
    w1RefusalError prims βmin N r s θ C k D Lk reps tol x B ε ≤
      w1RefusalError prims βmin N N s θ C k D Lk reps tol x B ε := by
  have hreg : 0 ≤ regGapAt prims βmin :=
    Finset.expect_nonneg fun _ _ => signerRegGap_nonneg _ _ _ (Cutoff.const _)
  have hcoll : 0 ≤ collAt prims := Finset.expect_nonneg fun _ _ => commitCollision_nonneg _
  have hrN : (r : ℝ) ≤ N := by exact_mod_cast hr
  have hpos : (0 : ℝ) < reps * (x - 1) := mul_pos (by exact_mod_cast hreps) (by linarith)
  have hq : 0 ≤ (B - 1) / (reps * (x - 1)) := div_nonneg (by linarith) hpos.le
  have hL0 : 0 ≤ Real.log C := Real.log_natCast_nonneg C
  have h1s : 0 < 1 - s := by linarith
  have hA0 : 0 ≤ 4 * (N : ℝ) / (θ * (1 - s)) ^ 2 := by positivity
  have hT1 : (x ^ (tol + 1))⁻¹ * B ^ r ≤ (x ^ (tol + 1))⁻¹ * B ^ N :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB1 hr) (inv_nonneg.2 (pow_nonneg (by linarith) _))
  have hT2 : (r : ℝ) ^ 2 / Fintype.card (Bytes 64) ≤ (N : ℝ) ^ 2 / Fintype.card (Bytes 64) :=
    div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hrN 2) (Nat.cast_nonneg _)
  have hT3 : (r : ℝ) * regGapAt prims βmin ≤ N * regGapAt prims βmin :=
    mul_le_mul_of_nonneg_right hrN hreg
  have hT4 : √(4 * N / (θ * (1 - s)) ^ 2 * (2 * (r * collAt prims) /
        ((standinScale p * βmin).toReal * Fintype.card (BucketVec p)) ^ 2 +
        2 / Fintype.card (BucketVec p)) * Real.log C / 2) ≤
      √(4 * N / (θ * (1 - s)) ^ 2 * (2 * (N * collAt prims) /
        ((standinScale p * βmin).toReal * Fintype.card (BucketVec p)) ^ 2 +
        2 / Fintype.card (BucketVec p)) * Real.log C / 2) := by
    refine Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add_left (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrN hcoll) (by norm_num))
        (sq_nonneg _)) _) hA0) hL0) (by norm_num))
  have hT5 : (r : ℝ) * ((B - 1) / (reps * (x - 1))) / s ≤ N * ((B - 1) / (reps * (x - 1))) / s :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hrN hq) hs0.le
  unfold w1RefusalError
  have hθs : 0 ≤ 2 * (1 - s)⁻¹ / θ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hT3 hθs]


open Classical in
omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] in
/-- **The refusal rate of the ML-DSA ring publishing `w₁` at the concrete primitives**
(`BaseSigner.RefuseWithin`) of an approved parameter set: at most `w1RefusalError` at `N` members,
under the check-defect conjecture at `B` (`hB`), the `tr`-collision assumption at `ε` for every
ring size `r ≤ N` (`hε`), and `C` a bound on the valid challenges of the `r` members for every
`r ≤ N` (`hC`) (`refuseProb_hedgedBase_le`, `w1RefusalError_le_of_le`). -/
theorem w1ConcreteBase_refuseWithin (hp : p.isApproved) (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) (hO : O.UniformSplit)
    (hMask : (uniformOfFintype Y).map M.ans = uniformOfFintype (MaskBox p))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    {s θ x Lk B ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs0 : 0 < s) (hs1 : s < 1) (hx : 1 < x)
    (hLk : Lk ≤ keepLevel p βmin s θ) (hLk1 : Lk ≤ 1) (hreps : 0 < reps) {C : ℕ}
    (hC : ∀ r ≤ N, ∀ keys : Fin r → Bytes 32, (Finset.univ.filter fun c :
      AnonRequest (w1Concrete p O M βmin tol k D bmsg PS adm) r => c.Valid keys).card ≤ C)
    (hB : W1CheckDefectMgf (concretePrimitivesKeyGen p) βmin x reps B)
    (hε : ∀ r ≤ N, HonestTrDistinct (concretePrimitivesKeyGen p) r ε) :
    (w1ConcreteBase p O M βmin tol k D bmsg).RefuseWithin adm (ENNReal.ofReal
      (w1RefusalError (concretePrimitivesKeyGen p) βmin N N s θ C k D Lk reps tol x B ε)) := by
  intro r hr sI m
  have hsp := SigningParams.of_isApproved hp
  have hB1 : 1 ≤ B := by
    refine le_trans ?_ hB
    refine le_trans (Finset.expect_const Finset.univ_nonempty (1 : ℝ)).ge
      (Finset.expect_le_expect fun seed _ => one_le_pow₀ ?_)
    have := checkDefect_nonneg (concretePrimitivesKeyGen p) (Cutoff.const βmin)
      (keyGen (concretePrimitivesKeyGen p) seed).1.2.2
    nlinarith
  have h := refuseProb_hedgedBase_le (concretePrimitivesKeyGen p) O M βmin tol (concreteEnc p) k D
    bmsg PS adm hsp hβ0 hβt hT hO hMask hM hdisj (signingLaws_concreteKeyGen p hp)
    (verifyLaws_concreteKeyGen hp) (concreteEnc_highBitsVec_keyGen hp)
    (fun seed => keyGenFromSeed_s2_bounded hp seed) hθ0 hθ1 hs0 hs1 hx hLk hLk1 hreps hr
    (hC r hr) hB (hε r hr) sI m
  have hne : (w1ConcreteBase p O M βmin tol k D bmsg).refuseProb adm hr sI m ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one _ _)
  calc (w1ConcreteBase p O M βmin tol k D bmsg).refuseProb adm hr sI m
      = ENNReal.ofReal ((w1ConcreteBase p O M βmin tol k D bmsg).refuseProb adm hr sI m).toReal :=
        (ENNReal.ofReal_toReal hne).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (h.trans (w1RefusalError_le_of_le _ hθ0 hθ1 hs0 hs1 hx hreps
        hB1 hr))

open Classical in
omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [DecidableEq TPS.Coins] in
/-- **Completeness of the ML-DSA ring publishing `w₁` at the concrete primitives with its refusal
rate bounded** (`w1Concrete.completeWithin` at `w1ConcreteBase_refuseWithin`): the ring signature
refuses with probability at most `w1RefusalError` at `N` members and is rejected with probability
at most `0 + εp (q + qPub)`, under the check-defect conjecture `W1CheckDefectMgf` and the
`tr`-collision assumption `HonestTrDistinct`. -/
@[headline]
theorem w1Concrete.completeWithin_refusal (hp : p.isApproved) (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) (hO : O.UniformSplit)
    (hMask : (uniformOfFintype Y).map M.ans = uniformOfFintype (MaskBox p))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    {s θ x Lk B ε : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs0 : 0 < s) (hs1 : s < 1) (hx : 1 < x)
    (hLk : Lk ≤ keepLevel p βmin s θ) (hLk1 : Lk ≤ 1) (hreps : 0 < reps) {C : ℕ}
    (hC : ∀ r ≤ N, ∀ keys : Fin r → Bytes 32, (Finset.univ.filter fun c :
      AnonRequest (w1Concrete p O M βmin tol k D bmsg PS adm) r => c.Valid keys).card ≤ C)
    (hB : W1CheckDefectMgf (concretePrimitivesKeyGen p) βmin x reps B)
    (hε : ∀ r ≤ N, HonestTrDistinct (concretePrimitivesKeyGen p) r ε) {εp : ℕ → ℝ≥0∞}
    (hPS : PS.CompleteWithin (RingSignature.ringRel (w1ConcreteBase p O M βmin tol k D bmsg) adm)
      εp) :
    (w1Concrete p O M βmin tol k D bmsg PS adm).CompleteWithin (ENNReal.ofReal
      (w1RefusalError (concretePrimitivesKeyGen p) βmin N N s θ C k D Lk reps tol x B ε))
      (0 + εp ((w1ConcreteBase p O M βmin tol k D bmsg).q +
        (w1ConcreteBase p O M βmin tol k D bmsg).qPub)) :=
  w1Concrete.completeWithin hp (w1ConcreteBase_refuseWithin hp hT hβ0 hβt hO hMask hM hdisj hθ0
    hθ1 hs0 hs1 hx hLk hLk1 hreps hC hB hε) hPS

end Concrete


/-! ### ML-DSA-44, ML-DSA-65 and ML-DSA-87 -/

section Instances

open _root_.MLDSA.Concrete GordieHowe.MLDSA.Spec

attribute [local instance] concreteNTTRingOps

variable [Fintype Msg] [DecidableEq Msg] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] {βmin : ℚ≥0} {tol k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg]

section P44

local notation "Pm" => _root_.MLDSA.mldsa44
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa44

/-- **The `tr`-collision assumption at ML-DSA-44** for rings of at most `N` members: for every
`r ≤ N`, `HonestTrDistinct` at the concrete primitives with `ε = C(r, 2) · 2^-255` (seed
collisions and SHAKE256 collisions, see the module docstring). -/
abbrev HonestTrDistinct44 (N : ℕ) : Prop :=
  ∀ r ≤ N, HonestTrDistinct Kg r ((r.choose 2 : ℝ) / 2 ^ 255)

variable {O : W1Oracles X Y Pm Kg Msg N reps} {M : MaskOracle X Y Pm T Msg}
  {bmsg : KeyRing (PubKey Pm Kg) N → RMsg → Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase Pm O M βmin tol k D bmsg)) (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm))) TPS}
  {adm : KeyRing (PubKey Pm (concretePrimitivesKeyGen Pm)) N → Prop} [DecidablePred adm]

open Classical in
omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [DecidableEq TPS.Coins] in
/-- **Completeness of the ML-DSA-44 ring signature publishing `w₁` with its refusal rate
bounded** (`w1Scheme44`; `w1Concrete.completeWithin_refusal` at ML-DSA-44, with
`ε = C(N, 2) · 2^-255` from `HonestTrDistinct44`), under the check-defect conjecture
`W1CheckDefectMgf`. -/
@[headline]
theorem w1Scheme44.completeWithin_refusal (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hO : O.UniformSplit) (hMask : (uniformOfFintype Y).map M.ans = uniformOfFintype (MaskBox Pm))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    {s θ x Lk B : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs0 : 0 < s) (hs1 : s < 1) (hx : 1 < x)
    (hLk : Lk ≤ keepLevel Pm βmin s θ) (hLk1 : Lk ≤ 1) (hreps : 0 < reps) {C : ℕ}
    (hC : ∀ r ≤ N, ∀ keys : Fin r → Bytes 32, (Finset.univ.filter fun c :
      AnonRequest (w1Scheme44 O M βmin tol k D bmsg PS adm) r => c.Valid keys).card ≤ C)
    (hB : W1CheckDefectMgf Kg βmin x reps B) (hε : HonestTrDistinct44 N) {εp : ℕ → ℝ≥0∞}
    (hPS : PS.CompleteWithin (RingSignature.ringRel (w1ConcreteBase Pm O M βmin tol k D bmsg) adm)
      εp) :
    (w1Scheme44 O M βmin tol k D bmsg PS adm).CompleteWithin (ENNReal.ofReal
      (w1RefusalError Kg βmin N N s θ C k D Lk reps tol x B ((N.choose 2 : ℝ) / 2 ^ 255)))
      (0 + εp ((w1ConcreteBase Pm O M βmin tol k D bmsg).q +
        (w1ConcreteBase Pm O M βmin tol k D bmsg).qPub)) :=
  w1Concrete.completeWithin_refusal (Or.inl rfl) hT hβ0 hβt hO hMask hM hdisj hθ0 hθ1 hs0 hs1 hx
    hLk hLk1 hreps hC hB (fun r hr => HonestTrDistinct.mono _ (hε r hr)
      (div_le_div_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose 2 hr) (by positivity)))
    hPS

end P44

section P65

local notation "Pm" => _root_.MLDSA.mldsa65
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa65

/-- **The `tr`-collision assumption at ML-DSA-65** for rings of at most `N` members: for every
`r ≤ N`, `HonestTrDistinct` at the concrete primitives with `ε = C(r, 2) · 2^-255` (seed
collisions and SHAKE256 collisions, see the module docstring). -/
abbrev HonestTrDistinct65 (N : ℕ) : Prop :=
  ∀ r ≤ N, HonestTrDistinct Kg r ((r.choose 2 : ℝ) / 2 ^ 255)

variable {O : W1Oracles X Y Pm Kg Msg N reps} {M : MaskOracle X Y Pm T Msg}
  {bmsg : KeyRing (PubKey Pm Kg) N → RMsg → Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase Pm O M βmin tol k D bmsg)) (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm))) TPS}
  {adm : KeyRing (PubKey Pm (concretePrimitivesKeyGen Pm)) N → Prop} [DecidablePred adm]

open Classical in
omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [DecidableEq TPS.Coins] in
/-- **Completeness of the ML-DSA-65 ring signature publishing `w₁` with its refusal rate
bounded** (`w1Scheme65`; `w1Concrete.completeWithin_refusal` at ML-DSA-65, with
`ε = C(N, 2) · 2^-255` from `HonestTrDistinct65`), under the check-defect conjecture
`W1CheckDefectMgf`. -/
@[headline]
theorem w1Scheme65.completeWithin_refusal (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hO : O.UniformSplit) (hMask : (uniformOfFintype Y).map M.ans = uniformOfFintype (MaskBox Pm))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    {s θ x Lk B : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs0 : 0 < s) (hs1 : s < 1) (hx : 1 < x)
    (hLk : Lk ≤ keepLevel Pm βmin s θ) (hLk1 : Lk ≤ 1) (hreps : 0 < reps) {C : ℕ}
    (hC : ∀ r ≤ N, ∀ keys : Fin r → Bytes 32, (Finset.univ.filter fun c :
      AnonRequest (w1Scheme65 O M βmin tol k D bmsg PS adm) r => c.Valid keys).card ≤ C)
    (hB : W1CheckDefectMgf Kg βmin x reps B) (hε : HonestTrDistinct65 N) {εp : ℕ → ℝ≥0∞}
    (hPS : PS.CompleteWithin (RingSignature.ringRel (w1ConcreteBase Pm O M βmin tol k D bmsg) adm)
      εp) :
    (w1Scheme65 O M βmin tol k D bmsg PS adm).CompleteWithin (ENNReal.ofReal
      (w1RefusalError Kg βmin N N s θ C k D Lk reps tol x B ((N.choose 2 : ℝ) / 2 ^ 255)))
      (0 + εp ((w1ConcreteBase Pm O M βmin tol k D bmsg).q +
        (w1ConcreteBase Pm O M βmin tol k D bmsg).qPub)) :=
  w1Concrete.completeWithin_refusal (Or.inr (Or.inl rfl)) hT hβ0 hβt hO hMask hM hdisj hθ0 hθ1 hs0
    hs1 hx hLk hLk1 hreps hC hB (fun r hr => HonestTrDistinct.mono _ (hε r hr)
      (div_le_div_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose 2 hr) (by positivity)))
    hPS

end P65

section P87

local notation "Pm" => _root_.MLDSA.mldsa87
local notation "Kg" => concretePrimitivesKeyGen _root_.MLDSA.mldsa87

/-- **The `tr`-collision assumption at ML-DSA-87** for rings of at most `N` members: for every
`r ≤ N`, `HonestTrDistinct` at the concrete primitives with `ε = C(r, 2) · 2^-255` (seed
collisions and SHAKE256 collisions, see the module docstring). -/
abbrev HonestTrDistinct87 (N : ℕ) : Prop :=
  ∀ r ≤ N, HonestTrDistinct Kg r ((r.choose 2 : ℝ) / 2 ^ 255)

variable {O : W1Oracles X Y Pm Kg Msg N reps} {M : MaskOracle X Y Pm T Msg}
  {bmsg : KeyRing (PubKey Pm Kg) N → RMsg → Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase Pm O M βmin tol k D bmsg)) (RingSignature.RingWitOf (FIPSSignature Pm (concretePrimitivesKeyGen Pm))) TPS}
  {adm : KeyRing (PubKey Pm (concretePrimitivesKeyGen Pm)) N → Prop} [DecidablePred adm]

open Classical in
omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [DecidableEq TPS.Coins] in
/-- **Completeness of the ML-DSA-87 ring signature publishing `w₁` with its refusal rate
bounded** (`w1Scheme87`; `w1Concrete.completeWithin_refusal` at ML-DSA-87, with
`ε = C(N, 2) · 2^-255` from `HonestTrDistinct87`), under the check-defect conjecture
`W1CheckDefectMgf`. -/
@[headline]
theorem w1Scheme87.completeWithin_refusal (hT : 0 < T) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hO : O.UniformSplit) (hMask : (uniformOfFintype Y).map M.ans = uniformOfFintype (MaskBox Pm))
    (hM : Function.Injective M.pt) (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    {s θ x Lk B : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs0 : 0 < s) (hs1 : s < 1) (hx : 1 < x)
    (hLk : Lk ≤ keepLevel Pm βmin s θ) (hLk1 : Lk ≤ 1) (hreps : 0 < reps) {C : ℕ}
    (hC : ∀ r ≤ N, ∀ keys : Fin r → Bytes 32, (Finset.univ.filter fun c :
      AnonRequest (w1Scheme87 O M βmin tol k D bmsg PS adm) r => c.Valid keys).card ≤ C)
    (hB : W1CheckDefectMgf Kg βmin x reps B) (hε : HonestTrDistinct87 N) {εp : ℕ → ℝ≥0∞}
    (hPS : PS.CompleteWithin (RingSignature.ringRel (w1ConcreteBase Pm O M βmin tol k D bmsg) adm)
      εp) :
    (w1Scheme87 O M βmin tol k D bmsg PS adm).CompleteWithin (ENNReal.ofReal
      (w1RefusalError Kg βmin N N s θ C k D Lk reps tol x B ((N.choose 2 : ℝ) / 2 ^ 255)))
      (0 + εp ((w1ConcreteBase Pm O M βmin tol k D bmsg).q +
        (w1ConcreteBase Pm O M βmin tol k D bmsg).qPub)) :=
  w1Concrete.completeWithin_refusal (Or.inr (Or.inr rfl)) hT hβ0 hβt hO hMask hM hdisj hθ0 hθ1 hs0
    hs1 hx hLk hLk1 hreps hC hB (fun r hr => HonestTrDistinct.mono _ (hε r hr)
      (div_le_div_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose 2 hr) (by positivity)))
    hPS

end P87

end Instances

end GordieHowe.Ring.MLDSAW1
