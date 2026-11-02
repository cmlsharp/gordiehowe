-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1Regularity
public import GordieHowe.Applications.Ring.PublicW1.MaskOracle

@[expose] public section

/-!
# The ML-DSA ring signer publishing `w₁` with FIPS 204 hedged signing

FIPS 204 Algorithm 7 (ML-DSA.Sign_internal) derives the masks of a signature from a fresh
32-byte nonce `rnd`: `ρ'' = H(K ‖ rnd ‖ µ, 64)` (line 7) and `y = ExpandMask(ρ'', κ)` for the
attempt counter `κ` (line 11), with at most `T` attempts per call. Here the composition of `H` and
`ExpandMask` is a random oracle onto the mask box (`MaskBox p`), the mask oracle `Y` of the game,
on the points `(rnd, (κ, (K, (tr, m))))`: the message enters the mask oracle as `(tr, m)`, the
input of `µ = H_µ(tr ‖ m)` (`MLDSAPublicW1.lean`). The ring signer calls ML-DSA.Sign with a fresh `rnd` every time the
flattening coin rejects (step 2 of the construction).

- `hedgeAttempt`, `hedgedSigner`: one call of the hedged base signer with `T` masks from a slice,
  then the flattening coin (`PMF.weightedAttemptMasks`); the hedged ring signer as a
  `MaskedSigner` of `pubSigner`: with fresh uniform masks its loop is the ideal-mask signer's
  (`signLaw_eq`, from `PMF.untilSome_uniform_bind_weightedAttemptMasks`).
- `KeepBound`: a lower bound `s̄` on the keep probability of one ring attempt of the ideal-mask
  signer, on the valid admitted challenges, a property of the honest signer.
  `keepBound_of_keepGood` proves it with `s̄ = keepLevel` (half the level `K β_min` times `θ`
  times the ring mass `(1 - s) |V|`) on the good event `KeepGood` (no high-defect ring passes the
  check, the anonymity error is below `1/2`), and `expect_ite_keepGood_le` bounds the failure of
  the good event by twice the anonymity error plus the check term.
- `advantage_le_hedged`: anonymity against the hedged signer is anonymity against the ideal-mask
  signer at every fixed mask oracle, plus twice the hedged error
  `(Q k)² / 2^256 + (Q + 1) q Q k / 2^256 + 2 Q (1 - s̄)^k` (`MaskedSigner.hedgeError`), for every
  query-bounded adversary (`MaskedSigner.QueryBounded`: `q` mask-oracle queries per choice and for
  the distinguisher) and every number `k` of attempts.
- `advantage_le_bkm06_mldsa{44,65,87}_hedged`: the ML-DSA headlines at the check parameters for
  the hedged signer, with `KeepBound` a hypothesis.
- `advantage_le_bkm06_mldsa{44,65,87}_hedged_keep`: the same with the keep bound discharged: the
  ideal-mask bound plus
  `2 · ((k² + 2 q k) / 2^256 + 2 · ((1 - β_min θ / 64)^k + 2 · (regularity + McDiarmid) + C / 2^240))`,
  with the regularity and McDiarmid terms of `advantage_le_bkm06_mldsa{44,65,87}_checkParams`.
  No hypothesis on the signer remains.

The check term `C / 2^240` counts the adversary's candidate rings per key vector (`C`); the check
oracle `G` is given whole, so the query bound `q` does not enter it. `MLDSAPublicW1HedgedQuery.lean`
states the headlines with `2 (q + 1) / 2^240` for adversaries with `q` check-oracle queries.

The adversary class is query-bounded on the mask oracle and has full key exposure (it receives
every honest user's key-generation coins, so it knows `K`); the nonce `rnd` is the only secret per
attempt. Deterministic signing (`rnd = 0`, FIPS 204 Algorithm 2 with the deterministic variant)
is not covered: with a fixed nonce the adversary computes every mask.
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA PMF Finset
open scoped ENNReal BigOperators

section Signer

variable {p : Params} (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)] {Msg : Type} [Fintype Msg] [DecidableEq Msg]
  [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High]

/-- **The points of the mask oracle at one nonce**: the attempt counter, the secret seed `K` and
the message point `(tr, m)`, the input of `µ`. -/
abbrev MaskPt (T : ℕ) (Msg : Type) : Type := Fin T × (Bytes 32 × (Bytes 64 × Msg))

open Classical in
/-- **One hedged call of the base signer, then the flattening coin**: on a ring admissible at the
game's oracles with the position in range, the first of the `T` masks `Z (κ, (K, (tr, m)))` of the
slice that passes the checks of FIPS 204 Algorithm 7, kept with the flattening weight; on other
rings the refusal's default. -/
noncomputable def hedgeAttempt (βmin : ℚ≥0) (tol : ℕ) {N reps : ℕ} (T : ℕ)
    (HG : GameOrc prims Msg N reps) (sk : SecretKey p) (R : RingOf (PubKey p prims) N) (i : ℕ)
    (m : Msg) (Z : MaskPt T Msg → MaskBox p) :
    PMF (Option (BucketVec p × FIPSSignature p prims)) :=
  if h : i < R.1.length ∧ RingAdmissible prims βmin tol HG R m then
    PMF.weightedAttemptMasks (ringWeights prims βmin (ringT0s prims R.1)) ⟨i, h.1⟩
      (realBuckets (prims.expandA sk.rho)) (attemptAccept prims sk (prims.expandA sk.rho))
      (fun a => (flattenCoin prims sk βmin a : ℝ≥0∞)) (coe_flattenCoin_le_one prims sk βmin)
      (fun y c => attemptOutput prims sk (prims.expandA sk.rho) (y, c))
      (ringOf (ringPts prims R.1 m) (schemeOrc HG.1)) fun t => Z (t, (sk.key, (sk.tr, m)))
  else PMF.pure (some default)

/-- **The masks of the hedged calls, at a uniform slice, are uniform.** -/
theorem uniform_bind_hedgeAttempt {βmin : ℚ≥0} {tol N reps T : ℕ}
    (HG : GameOrc prims Msg N reps) (sk : SecretKey p) {R : RingOf (PubKey p prims) N} {i : ℕ}
    (m : Msg) (h : i < R.1.length ∧ RingAdmissible prims βmin tol HG R m) :
    (PMF.uniformOfFintype (MaskPt T Msg → MaskBox p)).bind
        (hedgeAttempt prims βmin tol T HG sk R i m) =
      (PMF.uniformOfFintype (Fin T → MaskBox p)).bind
        (PMF.weightedAttemptMasks (ringWeights prims βmin (ringT0s prims R.1)) ⟨i, h.1⟩
          (realBuckets (prims.expandA sk.rho)) (attemptAccept prims sk (prims.expandA sk.rho))
          (fun a => (flattenCoin prims sk βmin a : ℝ≥0∞)) (coe_flattenCoin_le_one prims sk βmin)
          (fun y c => attemptOutput prims sk (prims.expandA sk.rho) (y, c))
          (ringOf (ringPts prims R.1 m) (schemeOrc HG.1))) := by
  unfold hedgeAttempt
  simp only [dif_pos h]
  rw [← PMF.uniform_map_slice (ι' := Fin T) (M := MaskBox p) (sk.key, (sk.tr, m)), PMF.bind_map]
  rfl

/-- **The hedged ring signer** (the README construction with FIPS 204 hedged signing): at most
`T` masks per call of ML-DSA.Sign, a fresh nonce for every call, the mask oracle on
`MaskPt T Msg` at every nonce. With fresh uniform masks its signing loop is the ideal-mask
signer's. -/
noncomputable def hedgedSigner (N : ℕ) (βmin : ℚ≥0) (reps tol : ℕ)
    (enc : Vector prims.High p.k → BucketVec p) (T : ℕ) (hT : 0 < T) :
    MaskedSigner (pubSigner prims (Msg := Msg) N βmin reps tol enc) where
  Rnd := Bytes 32
  Pt := MaskPt T Msg
  Mask := MaskBox p
  attempt HG sk R i m Z := hedgeAttempt prims βmin tol T HG sk R i m Z
  dflt := (default : BucketVec p × FIPSSignature p prims)
  signLaw_eq := fun (HG : GameOrc prims Msg N reps) (sk : SecretKey p)
      (R : RingOf (PubKey p prims) N) (i : ℕ) (m : Msg) => by
    show signLaw prims βmin tol HG sk R i m = _
    unfold signLaw
    split_ifs with h
    · refine congrArg (PMF.map _) ?_
      exact (PMF.untilSome_uniform_bind_weightedAttemptMasks _ _ _ _ _ _ _ _ hT).symm.trans
        (congrArg untilSome (uniform_bind_hedgeAttempt prims HG sk m h).symm)
    · have h0 : (PMF.uniformOfFintype (MaskPt T Msg → MaskBox p)).bind
          (hedgeAttempt prims βmin tol T HG sk R i m) = PMF.pure (some default) := by
        unfold hedgeAttempt
        simp only [dif_neg h, PMF.bind_const]
      show _ = PMF.map _ (untilSome ((PMF.uniformOfFintype (MaskPt T Msg → MaskBox p)).bind
        (hedgeAttempt prims βmin tol T HG sk R i m)))
      rw [h0, PMF.untilSome_pure_some]
      exact (PMF.pure_map (fun o : Option (BucketVec p × FIPSSignature p prims) => o.getD default)
        (some default)).symm

/-! ### Anonymity against the hedged signer -/

section Hedged

open IOP GordieHowe.SPBCS GordieHowe.QROM

variable {N : ℕ} {βmin : ℚ≥0} {reps tol : ℕ} {enc : Vector prims.High p.k → BucketVec p} {T : ℕ}
  (hT : 0 < T) {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)]
  {M : SPBCS Mg P (pubSigner prims (Msg := Msg) N βmin reps tol enc).Stmt k kN kS L e} {n Q : ℕ}

/-- **A lower bound `s̄` on the keep probability of one ring attempt** of the ideal-mask signer
(`ringAttemptOut`: one mask, the checks of FIPS 204 Algorithm 7, the flattening coin), for every
valid challenge of the set `choices` whose ring is admissible at the game's oracles, at the users'
coins `keys` and the oracles `HG`: the attempt rejects with probability at most `1 - s̄ keys HG`.
A property of the honest ML-DSA ring signer; this step takes it as a hypothesis and does not prove
it in Lean. The hedged signer's calls reject at most as often (`meanAttempt_none_le`). -/
structure KeepBound (βmin : ℚ≥0) (tol : ℕ) (choices : Finset (RingChoice (PubKey p prims) Msg N n))
    (sbar : (Fin n → _root_.MLDSA.Bytes 32) → GameOrc prims Msg N reps → ℝ≥0∞) : Prop where
  /-- One attempt keeps with probability at least `s̄`. -/
  keep : ∀ keys HG, ∀ c ∈ choices, c.Valid (fun seed => (keyGen prims seed).1) keys →
    RingAdmissible prims βmin tol HG c.ring c.msg →
    ∀ (b : Bool) (hlt : c.idx b < c.ring.1.length),
      ringAttemptOut prims βmin (keyGen prims (keys (c.user b))).2 c.ring.1 ⟨c.idx b, hlt⟩ c.msg
        (schemeOrc HG.1) none ≤ 1 - sbar keys HG

/-- **A hedged call with fresh masks rejects at most as often as one ideal ring attempt.** -/
theorem meanAttempt_none_le (keys : Fin n → _root_.MLDSA.Bytes 32) (HG : GameOrc prims Msg N reps)
    (c : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Choice n) (b : Bool)
    (hlt : c.idx b < c.ring.1.length) (hA : RingAdmissible prims βmin tol HG c.ring c.msg) :
    (hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).meanAttempt HG keys c b none ≤
      ringAttemptOut prims βmin (keyGen prims (keys (c.user b))).2 c.ring.1 ⟨c.idx b, hlt⟩ c.msg
        (schemeOrc HG.1) none := by
  have h := uniform_bind_hedgeAttempt prims (T := T) HG (keyGen prims (keys (c.user b))).2 c.msg
    ⟨hlt, hA⟩
  unfold MaskedSigner.meanAttempt
  refine (le_of_eq (congrFun (congrArg DFunLike.coe h) none)).trans ?_
  exact PMF.uniform_bind_weightedAttemptMasks_none_le _ _ _ _ _ _ _ _ hT

variable {E : (j : ι) → (M.comp j).Encoder}
  {V : GameOrc prims Msg N reps → (pubSigner prims (Msg := Msg) N βmin reps tol enc).Stmt →
    FullTr P τ → Bool}
  {Qs : ∀ H x, M.IOPQueries (V H) x} {R : Type} [Fintype R] [Nonempty R]
  {honest : GameOrc prims Msg N reps → (pubSigner prims (Msg := Msg) N βmin reps tol enc).Wit →
    R → CausalProver P τ (pubSigner prims (Msg := Msg) N βmin reps tol enc).Stmt}

/-- **Anonymity against FIPS 204 hedged signing from anonymity against the ideal-mask signer**
(BKM06 Definition 4, ePrint 2005/304, p. 6, keys given at the start as in CCLM22 Experiment 2,
p. 21): for an adversary and a distinguisher that read the mask oracle (`H(K ‖ rnd ‖ µ)` composed
with ExpandMask, a random oracle) through at most `q` queries per choice and for the distinguisher
(`hq`), and a lower bound `s̄` on the keep probability of one ring attempt (`hkeep`), the advantage
is at most the average over the mask oracle of the advantage of the adversary at that mask oracle
against the ideal-mask signer, plus
`2 · 𝔼_{keys, HG} ((Q k)² / 2^256 + (Q + 1) q Q k / 2^256 + 2 Q (1 - s̄)^k)` for every number `k`
of attempts. Deterministic signing (`rnd = 0`) is not covered. -/
theorem advantage_le_hedged
    (A : PubAnonAdversary (hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).real M n Q)
    (D : (Fin n → _root_.MLDSA.Bytes 32) → (hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).real.Orc →
      (Query k kN kS L → Out k e) → PubHist (BucketVec p) M.NIProof Q → Prop) {q : ℕ}
    (hq : (hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).QueryBounded A D q) (ka : ℕ)
    (sbar : (Fin n → _root_.MLDSA.Bytes 32) → GameOrc prims Msg N reps → ℝ≥0∞)
    (hkeep : KeepBound prims βmin tol A.choices sbar) :
    A.advantage (V := fun HY => V HY.1) E (fun HY => Qs HY.1) (fun HY => honest HY.1) D ≤
      𝔼 Y : (hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).MaskOrc,
        ((hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).atMask A Y).advantage E Qs honest
          (fun keys H => D keys (H, Y)) +
      2 * 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32, 𝔼 HG : GameOrc prims Msg N reps,
        ((hedgedSigner prims (Msg := Msg) N βmin reps tol enc T hT).hedgeError Q q ka (1 - sbar keys HG)).toReal :=
  MaskedSigner.advantage_le_atMask A D hq ka (fun keys HG => 1 - sbar keys HG)
    (fun keys HG => (tsub_le_self : (1 : ℝ≥0∞) - sbar keys HG ≤ 1)) fun keys HG c hc hv ha b => by
      have hlt : c.idx b < c.ring.1.length := by
        cases b
        · exact hv.idx₀_lt
        · exact hv.idx₁_lt
      exact (meanAttempt_none_le prims hT keys HG c b hlt ha).trans
        (hkeep.keep keys HG c hc hv ha b hlt)

end Hedged

/-! ### The keep bound from the family bound -/

section KeepFromFamily

open IOP GordieHowe.SPBCS

variable {N : ℕ} {βmin : ℚ≥0} {reps tol : ℕ} {enc : Vector prims.High p.k → BucketVec p}
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)]
  {M : SPBCS Mg P (pubSigner prims (Msg := Msg) N βmin reps tol enc).Stmt k kN kS L e} {n Q : ℕ}
  (A : PubAnonAdversary (pubSigner prims (Msg := Msg) N βmin reps tol enc) M n Q)

/-- **The keep level** at the cut-off `β_min`, the defect budget `s` and the threshold fraction
`θ`: half the signer's level `K β_min` times `θ` times the least mass `(1 - s) |V|` of a ring of
defect at most `s`. -/
noncomputable def keepLevel (p : Params) (βmin : ℚ≥0) (s θ : ℝ) : ℝ :=
  (standinScale p * βmin).toReal * (θ * ((1 - s) * Fintype.card (BucketVec p))) / 2

open Classical in
/-- **The good event for keeping**: no ring of defect above `s` among the challenges valid for
`keys` passes the check, and the anonymity error at `H` is below `1/2`. -/
def KeepGood (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤) (s θ : ℝ)
    (keys : Fin n → _root_.MLDSA.Bytes 32) (HG : GameOrc prims Msg N reps) : Prop :=
  ¬ BadPass prims A s keys HG.2 ∧ oracleError prims A hp hβ0 hβt s θ keys HG.1 < 1 / 2

open Classical in
/-- **The keep bound from the family bound**: on the good event, one ring attempt of a valid
admitted challenge keeps with probability at least the keep level (`keep_ge_of_familyBound_lt`,
the ring mass at least `(1 - s) |V|` for defect at most `s`); outside it, the bound `0`. -/
theorem keepBound_of_keepGood (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) {s θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) {Lk : ℝ} (hLk : Lk ≤ keepLevel p βmin s θ) :
    KeepBound prims βmin tol A.choices fun keys HG =>
      if KeepGood prims A hp hβ0 hβt s θ keys HG then ENNReal.ofReal Lk else 0 := by
  refine ⟨fun keys HG c hcm hv ha b hlt => ?_⟩
  split_ifs with hG
  · obtain ⟨hB, hO⟩ := hG
    have hd := lowDefect_of_not_badPass hB hcm hv ha
    let m : ValidChoiceMu prims A s keys HG.1.1 := ⟨⟨c, hcm⟩, hv, ha.1, hd⟩
    haveI hne : Nonempty (ValidChoiceMu prims A s keys HG.1.1) := ⟨m⟩
    have hF : familyBound (familyMu prims A hp hβ0 hβt s keys HG.1.1) θ HG.1.2 < 1 / 2 := by
      unfold oracleError at hO
      rwa [dif_pos hne] at hO
    have hkeep := keep_ge_of_familyBound_lt (familyMu prims A hp hβ0 hβt s keys HG.1.1) hθ0 hθ1
      (familyMu_mass_pos hp hβ0 hβt hs1 keys HG.1.1) hF m b
    have hnone : (familyMu prims A hp hβ0 hβt s keys HG.1.1 m).attempt b HG.1.2 none =
        ringAttemptOut prims βmin (keyGen prims (keys (c.user b))).2 c.ring.1 ⟨c.idx b, hlt⟩ c.msg
          (schemeOrc HG.1) none :=
      (ringAttemptOut_apply_none prims N βmin reps tol enc hp hβ0 hβt keys HG.1.1 c hv ha.1 HG.1.2
        b).symm
    have hmass : (1 - s) * Fintype.card (BucketVec p) ≤
        (familyMu prims A hp hβ0 hβt s keys HG.1.1 m).wts.mass := by
      calc (1 - s) * Fintype.card (BucketVec p) = ∑ _v : BucketVec p, (1 - s) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
        _ ≤ _ := Finset.sum_le_sum fun v _ =>
            one_sub_le_colMass_of_ringDefect_le prims hp hβ0 hβt hd v
    have hlev : Lk ≤
        (1 - ringAttemptOut prims βmin (keyGen prims (keys (c.user b))).2 c.ring.1 ⟨c.idx b, hlt⟩
          c.msg (schemeOrc HG.1) none).toReal := by
      calc Lk ≤ keepLevel p βmin s θ := hLk
        _ ≤ (standinScale p * βmin).toReal *
            (θ * (familyMu prims A hp hβ0 hβt s keys HG.1.1 m).wts.mass) / 2 := by
            unfold keepLevel
            gcongr
        _ ≤ (1 - (familyMu prims A hp hβ0 hβt s keys HG.1.1 m).attempt b HG.1.2 none).toReal :=
            hkeep
        _ = _ := by rw [hnone]
    set r := ringAttemptOut prims βmin (keyGen prims (keys (c.user b))).2 c.ring.1 ⟨c.idx b, hlt⟩
      c.msg (schemeOrc HG.1) none
    have hr1 : r ≤ 1 := PMF.coe_le_one _ _
    have h1 : ENNReal.ofReal Lk ≤ 1 - r := by
      rw [← ENNReal.ofReal_toReal (a := 1 - r) (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)]
      exact ENNReal.ofReal_le_ofReal hlev
    have hx1 : ENNReal.ofReal Lk ≤ 1 := h1.trans tsub_le_self
    rw [ENNReal.le_sub_iff_add_le_right (ne_top_of_le_ne_top ENNReal.one_ne_top hx1) hx1]
    calc r + ENNReal.ofReal Lk ≤ r + (1 - r) := add_le_add le_rfl h1
      _ = 1 := add_tsub_cancel_of_le hr1
  · rw [tsub_zero]
    exact PMF.coe_le_one _ _

open Classical in
/-- **The good event for keeping fails rarely**: averaged over the game's oracles, at most twice
the average anonymity error plus `C · checkError reps tol s x` (the Markov inequality on the
anonymity error at `1/2`, and `expect_exists_ringCheck_le` for the check). -/
theorem expect_ite_keepGood_le (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤) {s θ : ℝ}
    (hs1 : s < 1) (hθ0 : 0 < θ) {x : ℝ} (hx : 1 ≤ x) {C : ℕ} (hC : A.ValidCountLe C)
    (keys : Fin n → _root_.MLDSA.Bytes 32) :
    𝔼 HG : GameOrc prims Msg N reps,
        (if KeepGood prims A hp hβ0 hβt s θ keys HG then 0 else 1 : ℝ) ≤
      2 * 𝔼 HG : GameOrc prims Msg N reps, oracleError prims A hp hβ0 hβt s θ keys HG.1 +
        C * checkError reps tol s x := by
  have hpt : ∀ HG : GameOrc prims Msg N reps,
      (if KeepGood prims A hp hβ0 hβt s θ keys HG then 0 else 1 : ℝ) ≤
        2 * oracleError prims A hp hβ0 hβt s θ keys HG.1 +
          (if BadPass prims A s keys HG.2 then 1 else 0) := fun HG => by
    have h0 := oracleError_nonneg (A := A) hp hβ0 hβt hs1 hθ0 keys HG.1
    unfold KeepGood
    by_cases hB : BadPass prims A s keys HG.2
    · simp only [hB, not_true_eq_false, false_and, if_false, if_true]
      linarith
    · by_cases hO : oracleError prims A hp hβ0 hβt s θ keys HG.1 < 1 / 2
      · simp only [hB, hO, not_false_eq_true, and_self, if_true, if_false]
        linarith
      · simp only [hB, hO, not_false_eq_true, true_and, and_false, if_false]
        push Not at hO
        linarith
  refine (Finset.expect_le_expect fun HG _ => hpt HG).trans ?_
  rw [Finset.expect_add_distrib, ← Finset.mul_expect]
  refine add_le_add le_rfl ?_
  have hB : ∀ G : CheckOrc p prims N reps, (if BadPass prims A s keys G then 1 else 0 : ℝ) =
      if ∃ c ∈ A.validChoices keys, s < ringDefect prims βmin c.ring.1 ∧
        RingCheck prims βmin tol G c.ring then 1 else 0 := fun G =>
    if_congr Iff.rfl rfl rfl
  refine (Finset.expect_comp_snd
    (hαβ := (pubSigner prims (Msg := Msg) N βmin reps tol enc).instFintypeOrc)
    (fun G => (if BadPass prims A s keys G then 1 else 0 : ℝ))).trans_le ?_
  rw [Finset.expect_congr rfl fun G _ => hB G]
  convert (expect_exists_ringCheck_le prims βmin tol (A.validChoices keys) RingChoice.ring s
    hx).trans
    (mul_le_mul_of_nonneg_right (Nat.cast_le.2 (hC keys)) (checkError_nonneg reps tol s
      (zero_le_one.trans hx))) using 3

/-- **The anonymity error averaged over the users' coins and the oracles** is at most `anonError`
(`expect_oracleError_le`). -/
theorem expect_expect_oracleError_le (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (h_laws : SigningLaws prims) (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta)
    {s θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) [NeZero n] {C : ℕ} (hC : A.ValidCountLe C) :
    𝔼 keys : Fin n → _root_.MLDSA.Bytes 32, 𝔼 HG : GameOrc prims Msg N reps,
        oracleError prims A hp hβ0 hβt s θ keys HG.1 ≤
      anonError (A := A) hp hβ0 hβt s θ C :=
  Finset.expect_le_expect fun keys _ =>
    (Finset.expect_comp_fst
      (hαβ := (pubSigner prims (Msg := Msg) N βmin reps tol enc).instFintypeOrc)
      (fun H => oracleError prims A hp hβ0 hβt s θ keys H)).trans_le
      (expect_schOrc_oracleError_le hp hβ0 hβt h_laws hs2 hθ0 hθ1 hs1 hC keys)

end KeepFromFamily

end Signer


/-- **Averaging a pointwise bound through a mixture**: if `x a b c ≤ 𝔼_d y a b c d + 2 ε a b c`
pointwise and `𝔼_{a, b, c} y a b c d ≤ B` for every `d`, then `𝔼 x ≤ B + 2 𝔼 ε`. -/
theorem expect3_le_of_mix {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [Nonempty δ] (x ε : α → β → γ → ℝ) (y : α → β → γ → δ → ℝ)
    {B : ℝ} (h : ∀ a b c, x a b c ≤ 𝔼 d, y a b c d + 2 * ε a b c)
    (hB : ∀ d, 𝔼 a, 𝔼 b, 𝔼 c, y a b c d ≤ B) :
    𝔼 a, 𝔼 b, 𝔼 c, x a b c ≤ B + 2 * 𝔼 a, 𝔼 b, 𝔼 c, ε a b c := by
  refine (Finset.expect_le_expect fun a _ => Finset.expect_le_expect fun b _ =>
    Finset.expect_le_expect fun c _ => h a b c).trans ?_
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect]
  refine add_le_add ?_ le_rfl
  have e : 𝔼 a, 𝔼 b, 𝔼 c, 𝔼 d, y a b c d = 𝔼 d, 𝔼 a, 𝔼 b, 𝔼 c, y a b c d := by
    simp_rw [Finset.expect_comm (s := Finset.univ (α := γ)) (t := Finset.univ (α := δ))]
    simp_rw [Finset.expect_comm (s := Finset.univ (α := β)) (t := Finset.univ (α := δ))]
    rw [Finset.expect_comm]
  rw [e]
  exact (Finset.expect_le_expect fun d _ => hB d).trans_eq (Fintype.expect_const _)

/-! ### The hedged headlines -/

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA GordieHowe.MLDSA.Spec
  GordieHowe.MLDSA.Regularity IOP GordieHowe.SPBCS GordieHowe.QROM
open LatticeCrypto TransformOps

attribute [local instance] concreteNTTRingOps

/-- `Bytes 32` has `2^256` values. -/
theorem card_bytes32 [inst : Fintype (_root_.MLDSA.Bytes 32)] :
    (@Fintype.card _ inst : ℝ) = 2 ^ 256 := by
  rw [Fintype.card_congr (Vector.equivFun UInt8 32), Fintype.card_fun, Fintype.card_fin,
    Fintype.card_congr UInt8.equivFin, Fintype.card_fin]
  norm_num


section Hedged_mldsa44

variable {Msg : Type} [Fintype Msg] [DecidableEq Msg] {N : ℕ} {βmin : ℚ≥0} {reps tol T : ℕ}
  (hT : 0 < T) {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {n : ℕ}
  {M : ∀ (GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau) (GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44)
    (GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l),
    SPBCS Mg P (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
      (concreteEnc _root_.MLDSA.mldsa44)).Stmt k kN kS L e}
  (A : ∀ GB GS GA, PubAnonAdversary (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
    (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa44) T hT).real (M GB GS GA) n 1)
  {E : ∀ GB GS GA, (j : ι) → ((M GB GS GA).comp j).Encoder}
  {V : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa44)).Stmt → FullTr P τ → Bool}
  {Qs : ∀ GB GS GA H x, (M GB GS GA).IOPQueries (V GB GS GA H) x} {R : Type} [Fintype R]
  [Nonempty R]
  {honest : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa44)).Wit → R → CausalProver P τ
          (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
            (concreteEnc _root_.MLDSA.mldsa44)).Stmt}
  (D : ∀ GB GS GA, (Fin n → _root_.MLDSA.Bytes 32) →
    GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps × (_root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox _root_.MLDSA.mldsa44) →
    (Query k kN kS L → Out k e) → PubHist (BucketVec _root_.MLDSA.mldsa44) (M GB GS GA).NIProof 1 → Prop)

open Classical in
/-- **Anonymity at ML-DSA-44 with FI_root_.MLDSA.mldsa44 204 hedged signing at the check parameters**
(BKM06 Definition 4, ePrint 2005/304, p. 6, `Q = 1`, keys given at the start as in CCLM22
Experiment 2, p. 21): `advantage_le_bkm06_mldsa44_checkParams` for the ideal-mask signer at every
fixed mask oracle (`advantage_le_hedged`), plus twice the hedged error
`(k² + 2 q k) / 2^256 + 2 (1 - s̄)^k` averaged over the oracles and the users' coins, for an
adversary and a distinguisher with at most `q` mask-oracle queries per phase (`hq`), at most `C`
challenges of its set valid for any key vector (`hC`), a lower bound `s̄` on the keep probability
of one ring attempt (`hkeep`, a hypothesis not proved in Lean in this step) and every number `k`
of attempts (`ka`). The masks are `ExpandMask(H(K ‖ rnd ‖ µ), κ)` with `H` and ExpandMask one
random oracle, at most `T` per call and a fresh `rnd` per call; deterministic signing
(`rnd = 0`) is not covered. The check term `C / 2^240` counts the candidate rings per key vector,
not the mask-oracle queries. -/
theorem advantage_le_bkm06_mldsa44_hedged (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hreps : reps = 355) (htol : tol = 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) [NeZero n]
    (Rv : ∀ GB GS GA H, (M GB GS GA).Reveal (E GB GS GA) (Qs GB GS GA H)) {PubZ : Type}
    {pubZ : ∀ GB GS GA, (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc _root_.MLDSA.mldsa44)).Stmt → PubZ}
    {sim : ∀ GB GS GA H, CausalJointSimulator (Rv GB GS GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GB GS GA H, CausalHVZK (Rv GB GS GA H).MV ((pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa44)).rel H)
      (honest GB GS GA H) (pubZ GB GS GA) (sim GB GS GA H) δ)
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C) {q : ℕ}
    (hq : ∀ GB GS GA, (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc _root_.MLDSA.mldsa44) T hT).QueryBounded (A GB GS GA) (D GB GS GA) q) (ka : ℕ)
    (sbar : ∀ (_GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau)
      (_GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44) (_GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l),
      (Fin n → _root_.MLDSA.Bytes 32) → GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps → ℝ≥0∞)
    (hkeep : ∀ GB GS GA, KeepBound (withExpandA (oraclePrimitives GB GS) GA) βmin tol
      (A GB GS GA).choices (sbar GB GS GA)) :
    𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
          (A GB GS GA).advantage (V := fun HY => V GB GS GA HY.1) (E GB GS GA)
            (fun HY => Qs GB GS GA HY.1) (fun HY => honest GB GS GA HY.1) (D GB GS GA) ≤
      2 * (2 * 2 / θ * (n * (11 / 2 ^ 101 * (24 / 5) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
                (M GB GS GA).wiError δ C +
          C / 2 ^ 240 +
        2 * 𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
              𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
                𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps,
                  ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
                    (concreteEnc _root_.MLDSA.mldsa44) T hT).hedgeError 1 q ka (1 - sbar GB GS GA keys HG)).toReal := by
  set B : ℝ := 2 * (2 * 2 / θ   * (n * (11 / 2 ^ 101 * (24 / 5) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
                (M GB GS GA).wiError δ C +
          C / 2 ^ 240
  -- at every fixed mask oracle, the ideal-mask bound
  have hY : ∀ Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox _root_.MLDSA.mldsa44,
      𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
          𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
            ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
              (concreteEnc _root_.MLDSA.mldsa44) T hT).atMask (A GB GS GA) Y).advantage (E GB GS GA) (Qs GB GS GA)
                (honest GB GS GA) (fun keys H => D GB GS GA keys (H, Y)) ≤ B := fun Y =>
    advantage_le_bkm06_mldsa44_checkParams
      (fun GB GS GA => (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
        reps tol (concreteEnc _root_.MLDSA.mldsa44) T hT).atMask (A GB GS GA) Y)
      (fun GB GS GA keys H => D GB GS GA keys (H, Y)) hβ0 hβ1 hβt hreps htol hθ0 hθ1 Rv hz hC
  -- at every oracle, the hedged step
  refine expect3_le_of_mix _ _ (fun GB GS GA (Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox _root_.MLDSA.mldsa44) =>
      ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa44) T hT).atMask (A GB GS GA) Y).advantage (E GB GS GA) (Qs GB GS GA)
          (honest GB GS GA) (fun keys H => D GB GS GA keys (H, Y))) (fun GB GS GA => ?_) hY
  exact advantage_le_hedged (withExpandA (oraclePrimitives GB GS) GA) hT
    (V := V GB GS GA) (E := E GB GS GA) (Qs := Qs GB GS GA) (honest := honest GB GS GA)
    (A GB GS GA) (D GB GS GA) (hq GB GS GA) ka (sbar GB GS GA) (hkeep GB GS GA)

open Classical in
/-- **Anonymity at ML-DSA-44 with FI_root_.MLDSA.mldsa44 204 hedged signing, the keep bound discharged**
(BKM06 Definition 4, ePrint 2005/304, p. 6, `Q = 1`): `advantage_le_bkm06_mldsa44_hedged` with the
keep bound `s̄ = β_min θ / 64` on the good event (`keepBound_of_keepGood`: the anonymity error
below `1/2` and no high-defect ring passing the check, `keep_ge_of_familyBound_lt`, with
`K |V| ≥ 1/16`), whose failure is at most twice the anonymity error plus the check term
(`expect_ite_keepGood_le`), evaluated as in `advantage_le_bkm06_mldsa44_checkParams`. For every
adversary and distinguisher with at most `q` mask-oracle queries per phase (`hq`) and every number
`k` of hedged calls (`ka`), the advantage is at most the ideal-mask bound plus
`2 · ((k² + 2 q k) / 2^256 + 2 · ((1 - β_min θ / 64)^k + 2 · (regularity + McDiarmid) + C / 2^240))`.
Deterministic signing (`rnd = 0`) is not covered. -/
theorem advantage_le_bkm06_mldsa44_hedged_keep (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hreps : reps = 355) (htol : tol = 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) [NeZero n]
    (Rv : ∀ GB GS GA H, (M GB GS GA).Reveal (E GB GS GA) (Qs GB GS GA H)) {PubZ : Type}
    {pubZ : ∀ GB GS GA, (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc _root_.MLDSA.mldsa44)).Stmt → PubZ}
    {sim : ∀ GB GS GA H, CausalJointSimulator (Rv GB GS GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GB GS GA H, CausalHVZK (Rv GB GS GA H).MV ((pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc _root_.MLDSA.mldsa44)).rel H)
      (honest GB GS GA H) (pubZ GB GS GA) (sim GB GS GA H) δ)
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C) {q : ℕ}
    (hq : ∀ GB GS GA, (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc _root_.MLDSA.mldsa44) T hT).QueryBounded (A GB GS GA) (D GB GS GA) q) (ka : ℕ) :
    𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
          (A GB GS GA).advantage (V := fun HY => V GB GS GA HY.1) (E GB GS GA)
            (fun HY => Qs GB GS GA HY.1) (fun HY => honest GB GS GA HY.1) (D GB GS GA) ≤
      2 * (2 * 2 / θ * (n * (11 / 2 ^ 101 * (24 / 5) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
                (M GB GS GA).wiError δ C +
          C / 2 ^ 240 +
        2 * ((ka ^ 2 + 2 * q * ka) / 2 ^ 256 + 2 * ((1 - (βmin : ℝ≥0∞).toReal * θ / 64) ^ ka +
          (2 * (2 * 2 / θ * (n * (11 / 2 ^ 101 * (24 / 5) / (βmin : ℝ≥0∞).toReal)) +
            √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
            C / 2 ^ 240))) := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty (τ := _root_.MLDSA.mldsa44.tau) (by
    rw [show _root_.MLDSA.mldsa44.tau = 39 from rfl]; norm_num [ringDegree])
  have hp' := SigningParams.of_isApproved isApproved_mldsa44
  have hb0 : 0 < (βmin : ℝ≥0∞).toReal := ENNReal.toReal_pos hβ0 hβt
  have hb1 : (βmin : ℝ≥0∞).toReal ≤ 1 := ENNReal.toReal_le_one_of_le_one hβ1
  set Y0 : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox _root_.MLDSA.mldsa44 := fun _ => Classical.arbitrary _
  set A' := fun GB GS GA => (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N
    βmin reps tol (concreteEnc _root_.MLDSA.mldsa44) T hT).atMask (A GB GS GA) Y0
  set Lk : ℝ := (βmin : ℝ≥0∞).toReal * θ / 64
  have hLk0 : 0 ≤ Lk := by positivity
  have hLk1 : Lk ≤ 1 := by
    have : (βmin : ℝ≥0∞).toReal * θ ≤ 1 := mul_le_one₀ hb1 hθ0.le hθ1.le
    show (βmin : ℝ≥0∞).toReal * θ / 64 ≤ 1
    linarith
  have hLk : Lk ≤ keepLevel _root_.MLDSA.mldsa44 βmin (1 / 2) θ := by
    have hK := one_div_sixteen_le_standinScale_mul_card_mldsa44
    unfold keepLevel
    rw [ENNReal.toReal_mul]
    have hx := mul_le_mul_of_nonneg_right hK (by positivity : (0 : ℝ) ≤ (βmin : ℝ≥0∞).toReal * θ)
    show (βmin : ℝ≥0∞).toReal * θ / 64 ≤ _
    nlinarith [hx]
  set good := fun GB GS GA => KeepGood (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp'
    hβ0 hβt (1 / 2) θ
  have hkeep : ∀ GB GS GA, KeepBound (withExpandA (oraclePrimitives GB GS) GA) βmin tol
      (A GB GS GA).choices fun keys HG => if good GB GS GA keys HG then ENNReal.ofReal Lk else 0 :=
    fun GB GS GA => keepBound_of_keepGood _ (A' GB GS GA) hp' hβ0 hβt hθ0 hθ1 (by norm_num) hLk
  have h1 := advantage_le_bkm06_mldsa44_hedged hT A D hβ0 hβ1 hβt hreps htol hθ0 hθ1 Rv hz hC hq ka
    (fun GB GS GA keys HG => if good GB GS GA keys HG then ENNReal.ofReal Lk else 0) hkeep
  refine h1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ zero_le_two))
  -- the anonymity error of the adversaries at `Y0`, averaged
  have hE3 : 𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
          anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C ≤
        2 * 2 / θ * (n * (11 / 2 ^ 101 * (24 / 5) / (βmin : ℝ≥0∞).toReal)) +
          √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal)) := by
    have hM : 𝔼 GB : CommitHashBytes _root_.MLDSA.mldsa44 → ChallengeBall _root_.MLDSA.mldsa44.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs _root_.MLDSA.mldsa44,
          𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
            𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
              (√(maxDevVar (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ
                  keys * Real.log C / 2) +
                √(maxCountVar (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt
                  (1 / 2) θ keys * Real.log (C + 1) / 2)) ≤
          √(N * n * Real.log (C + 1)) / (2 ^ 2000 * (θ * (1 - θ) * (1 - 1 / 2) *
            (βmin : ℝ≥0∞).toReal)) :=
      (Finset.expect_le_expect fun GB _ => (Finset.expect_le_expect fun GS _ =>
        expect_mcDiarmidTerms_le_of (oraclePrimitives GB GS) (A' GB GS) hp' hβ0 hβ1 hβt hθ0 hθ1
          (by norm_num) C
          commitCollisionBound_le_mldsa44 one_div_sixteen_le_standinScale_mul_card_mldsa44
          two_pow_le_card_bucketVec_mldsa44).trans_eq
        (Finset.expect_const univ_nonempty _)).trans_eq (Finset.expect_const univ_nonempty _)
    have hI := expect_idealAnonError_le (p := _root_.MLDSA.mldsa44) (A := A') isApproved_mldsa44 hβ0 hβt hθ0
      (s := 1 / 2) (by norm_num) C (expect_regGapAvg_le_mldsa44 hβ0 hβ1)
    have hL1 : ∀ GB GS, 𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l,
        anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C ≤
          idealAnonError (oraclePrimitives GB GS) (A' GB GS) hp' hβ0 hβt (1 / 2) θ C :=
      fun GB GS => expect_anonError_le_idealAnonError (oraclePrimitives GB GS) (A' GB GS) hp' hβ0
        hβt hθ0 (by norm_num) C
    refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
      hL1 GB GS).trans (hI.trans ?_)
    have h2 : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
    have hm : √(N * n * Real.log (C + 1)) / (2 ^ 2000 * (θ * (1 - θ) * (1 - 1 / 2) *
      (βmin : ℝ≥0∞).toReal)) =
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal)) := by
      rw [show (2 : ℝ) ^ 2000 = 2 ^ 1999 * 2 from pow_succ 2 1999]
      generalize (2 : ℝ) ^ 1999 = T
      ring
    rw [h2]
    refine add_le_add le_rfl (hM.trans_eq hm)
  -- the failure of the good event
  have hchk : checkError reps tol (1 / 2) 89 ≤ 1 / 2 ^ 240 := by
    rw [hreps, htol]; exact checkError_checkParams_le
  have hE2 : ∀ GB GS GA, 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
      𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps,
        (if good GB GS GA keys HG then 0 else 1 : ℝ) ≤
      2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C + C / 2 ^ 240 := fun GB GS GA => by
    have hlaws := SigningLaws.withExpandA (oraclePrimitives GB GS)
      (signingLaws_concreteWithSampleInBallExpandS isApproved_mldsa44 (sampleInBallShape_oraclePrims GB) _)
      GA
    have hO := expect_expect_oracleError_le (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA)
      hp' hβ0 hβt hlaws (fun _ => (secretOfCoeffs_bounded (GS _)).2) hθ0 hθ1 (s := 1 / 2)
      (by norm_num) (hC GB GS GA)
    have hK := fun keys => expect_ite_keepGood_le (withExpandA (oraclePrimitives GB GS) GA)
      (A' GB GS GA) hp' hβ0 hβt (s := 1 / 2) (θ := θ) (by norm_num) hθ0 (x := 89) (by norm_num)
      (hC GB GS GA) keys
    calc _ ≤ 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
          (2 * 𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps,
            oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ
              keys HG.1 +
            (C : ℝ) * checkError reps tol (1 / 2) 89) := Finset.expect_le_expect fun keys _ => hK keys
      _ ≤ 2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C + (C : ℝ) * (1 / 2 ^ 240) := by
          rw [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
          exact add_le_add (mul_le_mul_of_nonneg_left hO zero_le_two)
            (mul_le_mul_of_nonneg_left hchk (Nat.cast_nonneg _))
      _ = _ := by rw [mul_one_div]
  -- the hedged error
  have hE1 : ∀ GB GS GA, 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
      𝔼 HG : GameOrc (concretePrimitivesKeyGen _root_.MLDSA.mldsa44) Msg N reps,
        ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
          (concreteEnc _root_.MLDSA.mldsa44) T hT).hedgeError 1 q ka
            (1 - if good GB GS GA keys HG then ENNReal.ofReal Lk else 0)).toReal ≤
        (ka ^ 2 + 2 * q * ka) / 2 ^ 256 + 2 * ((1 - Lk) ^ ka +
          (2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C + C / 2 ^ 240)) :=
    fun GB GS GA => by
      have h := MaskedSigner.expect_toReal_hedgeError_le (hedgedSigner (withExpandA
        (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa44) T hT) 1 q ka
        (good GB GS GA) hLk0 hLk1
      have hcard : (Fintype.card (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
          (Msg := Msg) N βmin reps tol (concreteEnc _root_.MLDSA.mldsa44) T hT).Rnd : ℝ) = 2 ^ 256 := card_bytes32
      rw [hcard] at h
      refine h.trans ?_
      have h3 := hE2 GB GS GA
      have : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
      simp only [Nat.cast_one, one_mul] at h ⊢
      have hc : ((ka : ℝ) ^ 2 * (2 ^ 256)⁻¹ + (1 + 1) * q * ka * (2 ^ 256)⁻¹) =
          (ka ^ 2 + 2 * q * ka) / 2 ^ 256 := by ring
      rw [hc]
      nlinarith [h3]
  refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
    Finset.expect_le_expect fun GA _ => hE1 GB GS GA).trans ?_
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
  have hfin := hE3
  nlinarith [hfin]

end Hedged_mldsa44

section Hedged_mldsa65

variable {Msg : Type} [Fintype Msg] [DecidableEq Msg] {N : ℕ} {βmin : ℚ≥0} {reps tol T : ℕ}
  (hT : 0 < T) {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {n : ℕ}
  {M : ∀ (GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau) (GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65)
    (GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l),
    SPBCS Mg P (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
      (concreteEnc mldsa65)).Stmt k kN kS L e}
  (A : ∀ GB GS GA, PubAnonAdversary (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
    (Msg := Msg) N βmin reps tol (concreteEnc mldsa65) T hT).real (M GB GS GA) n 1)
  {E : ∀ GB GS GA, (j : ι) → ((M GB GS GA).comp j).Encoder}
  {V : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc mldsa65)).Stmt → FullTr P τ → Bool}
  {Qs : ∀ GB GS GA H x, (M GB GS GA).IOPQueries (V GB GS GA H) x} {R : Type} [Fintype R]
  [Nonempty R]
  {honest : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc mldsa65)).Wit → R → CausalProver P τ
          (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
            (concreteEnc mldsa65)).Stmt}
  (D : ∀ GB GS GA, (Fin n → _root_.MLDSA.Bytes 32) →
    GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps × (_root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa65) →
    (Query k kN kS L → Out k e) → PubHist (BucketVec mldsa65) (M GB GS GA).NIProof 1 → Prop)

open Classical in
/-- **Anonymity at ML-DSA-65 with FImldsa65 204 hedged signing at the check parameters**
(BKM06 Definition 4, ePrint 2005/304, p. 6, `Q = 1`, keys given at the start as in CCLM22
Experiment 2, p. 21): `advantage_le_bkm06_mldsa65_checkParams` for the ideal-mask signer at every
fixed mask oracle (`advantage_le_hedged`), plus twice the hedged error
`(k² + 2 q k) / 2^256 + 2 (1 - s̄)^k` averaged over the oracles and the users' coins, for an
adversary and a distinguisher with at most `q` mask-oracle queries per phase (`hq`), at most `C`
challenges of its set valid for any key vector (`hC`), a lower bound `s̄` on the keep probability
of one ring attempt (`hkeep`, a hypothesis not proved in Lean in this step) and every number `k`
of attempts (`ka`). The masks are `ExpandMask(H(K ‖ rnd ‖ µ), κ)` with `H` and ExpandMask one
random oracle, at most `T` per call and a fresh `rnd` per call; deterministic signing
(`rnd = 0`) is not covered. The check term `C / 2^240` counts the candidate rings per key vector,
not the mask-oracle queries. -/
theorem advantage_le_bkm06_mldsa65_hedged (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hreps : reps = 355) (htol : tol = 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) [NeZero n]
    (Rv : ∀ GB GS GA H, (M GB GS GA).Reveal (E GB GS GA) (Qs GB GS GA H)) {PubZ : Type}
    {pubZ : ∀ GB GS GA, (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc mldsa65)).Stmt → PubZ}
    {sim : ∀ GB GS GA H, CausalJointSimulator (Rv GB GS GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GB GS GA H, CausalHVZK (Rv GB GS GA H).MV ((pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa65)).rel H)
      (honest GB GS GA H) (pubZ GB GS GA) (sim GB GS GA H) δ)
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C) {q : ℕ}
    (hq : ∀ GB GS GA, (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc mldsa65) T hT).QueryBounded (A GB GS GA) (D GB GS GA) q) (ka : ℕ)
    (sbar : ∀ (_GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau)
      (_GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65) (_GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l),
      (Fin n → _root_.MLDSA.Bytes 32) → GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps → ℝ≥0∞)
    (hkeep : ∀ GB GS GA, KeepBound (withExpandA (oraclePrimitives GB GS) GA) βmin tol
      (A GB GS GA).choices (sbar GB GS GA)) :
    𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
          (A GB GS GA).advantage (V := fun HY => V GB GS GA HY.1) (E GB GS GA)
            (fun HY => Qs GB GS GA HY.1) (fun HY => honest GB GS GA HY.1) (D GB GS GA) ≤
      2 * (2 * 2 / θ * (n * (11 / 2 ^ 199 * (9 / 2) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
                (M GB GS GA).wiError δ C +
          C / 2 ^ 240 +
        2 * 𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
              𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
                𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps,
                  ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
                    (concreteEnc mldsa65) T hT).hedgeError 1 q ka (1 - sbar GB GS GA keys HG)).toReal := by
  set B : ℝ := 2 * (2 * 2 / θ* (n * (11 / 2 ^ 199 * (9 / 2) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
                (M GB GS GA).wiError δ C +
          C / 2 ^ 240
  -- at every fixed mask oracle, the ideal-mask bound
  have hY : ∀ Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa65,
      𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
          𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
            ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
              (concreteEnc mldsa65) T hT).atMask (A GB GS GA) Y).advantage (E GB GS GA) (Qs GB GS GA)
                (honest GB GS GA) (fun keys H => D GB GS GA keys (H, Y)) ≤ B := fun Y =>
    advantage_le_bkm06_mldsa65_checkParams
      (fun GB GS GA => (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
        reps tol (concreteEnc mldsa65) T hT).atMask (A GB GS GA) Y)
      (fun GB GS GA keys H => D GB GS GA keys (H, Y)) hβ0 hβ1 hβt hreps htol hθ0 hθ1 Rv hz hC
  -- at every oracle, the hedged step
  refine expect3_le_of_mix _ _ (fun GB GS GA (Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa65) =>
      ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa65) T hT).atMask (A GB GS GA) Y).advantage (E GB GS GA) (Qs GB GS GA)
          (honest GB GS GA) (fun keys H => D GB GS GA keys (H, Y))) (fun GB GS GA => ?_) hY
  exact advantage_le_hedged (withExpandA (oraclePrimitives GB GS) GA) hT
    (V := V GB GS GA) (E := E GB GS GA) (Qs := Qs GB GS GA) (honest := honest GB GS GA)
    (A GB GS GA) (D GB GS GA) (hq GB GS GA) ka (sbar GB GS GA) (hkeep GB GS GA)

open Classical in
/-- **Anonymity at ML-DSA-65 with FImldsa65 204 hedged signing, the keep bound discharged**
(BKM06 Definition 4, ePrint 2005/304, p. 6, `Q = 1`): `advantage_le_bkm06_mldsa65_hedged` with the
keep bound `s̄ = β_min θ / 64` on the good event (`keepBound_of_keepGood`: the anonymity error
below `1/2` and no high-defect ring passing the check, `keep_ge_of_familyBound_lt`, with
`K |V| ≥ 1/16`), whose failure is at most twice the anonymity error plus the check term
(`expect_ite_keepGood_le`), evaluated as in `advantage_le_bkm06_mldsa65_checkParams`. For every
adversary and distinguisher with at most `q` mask-oracle queries per phase (`hq`) and every number
`k` of hedged calls (`ka`), the advantage is at most the ideal-mask bound plus
`2 · ((k² + 2 q k) / 2^256 + 2 · ((1 - β_min θ / 64)^k + 2 · (regularity + McDiarmid) + C / 2^240))`.
Deterministic signing (`rnd = 0`) is not covered. -/
theorem advantage_le_bkm06_mldsa65_hedged_keep (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hreps : reps = 355) (htol : tol = 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) [NeZero n]
    (Rv : ∀ GB GS GA H, (M GB GS GA).Reveal (E GB GS GA) (Qs GB GS GA H)) {PubZ : Type}
    {pubZ : ∀ GB GS GA, (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc mldsa65)).Stmt → PubZ}
    {sim : ∀ GB GS GA H, CausalJointSimulator (Rv GB GS GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GB GS GA H, CausalHVZK (Rv GB GS GA H).MV ((pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa65)).rel H)
      (honest GB GS GA H) (pubZ GB GS GA) (sim GB GS GA H) δ)
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C) {q : ℕ}
    (hq : ∀ GB GS GA, (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc mldsa65) T hT).QueryBounded (A GB GS GA) (D GB GS GA) q) (ka : ℕ) :
    𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
          (A GB GS GA).advantage (V := fun HY => V GB GS GA HY.1) (E GB GS GA)
            (fun HY => Qs GB GS GA HY.1) (fun HY => honest GB GS GA HY.1) (D GB GS GA) ≤
      2 * (2 * 2 / θ * (n * (11 / 2 ^ 199 * (9 / 2) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
                (M GB GS GA).wiError δ C +
          C / 2 ^ 240 +
        2 * ((ka ^ 2 + 2 * q * ka) / 2 ^ 256 + 2 * ((1 - (βmin : ℝ≥0∞).toReal * θ / 64) ^ ka +
          (2 * (2 * 2 / θ * (n * (11 / 2 ^ 199 * (9 / 2) / (βmin : ℝ≥0∞).toReal)) +
            √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
            C / 2 ^ 240))) := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty floorParams_mldsa65.tau_le
  have hp' := SigningParams.of_isApproved isApproved_mldsa65
  have hb0 : 0 < (βmin : ℝ≥0∞).toReal := ENNReal.toReal_pos hβ0 hβt
  have hb1 : (βmin : ℝ≥0∞).toReal ≤ 1 := ENNReal.toReal_le_one_of_le_one hβ1
  set Y0 : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa65 := fun _ => Classical.arbitrary _
  set A' := fun GB GS GA => (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N
    βmin reps tol (concreteEnc mldsa65) T hT).atMask (A GB GS GA) Y0
  set Lk : ℝ := (βmin : ℝ≥0∞).toReal * θ / 64
  have hLk0 : 0 ≤ Lk := by positivity
  have hLk1 : Lk ≤ 1 := by
    have : (βmin : ℝ≥0∞).toReal * θ ≤ 1 := mul_le_one₀ hb1 hθ0.le hθ1.le
    show (βmin : ℝ≥0∞).toReal * θ / 64 ≤ 1
    linarith
  have hLk : Lk ≤ keepLevel mldsa65 βmin (1 / 2) θ := by
    have hK := one_div_sixteen_le_standinScale_mul_card_mldsa65
    unfold keepLevel
    rw [ENNReal.toReal_mul]
    have hx := mul_le_mul_of_nonneg_right hK (by positivity : (0 : ℝ) ≤ (βmin : ℝ≥0∞).toReal * θ)
    show (βmin : ℝ≥0∞).toReal * θ / 64 ≤ _
    nlinarith [hx]
  set good := fun GB GS GA => KeepGood (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp'
    hβ0 hβt (1 / 2) θ
  have hkeep : ∀ GB GS GA, KeepBound (withExpandA (oraclePrimitives GB GS) GA) βmin tol
      (A GB GS GA).choices fun keys HG => if good GB GS GA keys HG then ENNReal.ofReal Lk else 0 :=
    fun GB GS GA => keepBound_of_keepGood _ (A' GB GS GA) hp' hβ0 hβt hθ0 hθ1 (by norm_num) hLk
  have h1 := advantage_le_bkm06_mldsa65_hedged hT A D hβ0 hβ1 hβt hreps htol hθ0 hθ1 Rv hz hC hq ka
    (fun GB GS GA keys HG => if good GB GS GA keys HG then ENNReal.ofReal Lk else 0) hkeep
  refine h1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ zero_le_two))
  -- the anonymity error of the adversaries at `Y0`, averaged
  have hE3 : 𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
          anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C ≤
        2 * 2 / θ * (n * (11 / 2 ^ 199 * (9 / 2) / (βmin : ℝ≥0∞).toReal)) +
          √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal)) := by
    have hM : 𝔼 GB : CommitHashBytes mldsa65 → ChallengeBall mldsa65.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa65,
          𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
            𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
              (√(maxDevVar (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ
                  keys * Real.log C / 2) +
                √(maxCountVar (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt
                  (1 / 2) θ keys * Real.log (C + 1) / 2)) ≤
          √(N * n * Real.log (C + 1)) / (2 ^ 2000 * (θ * (1 - θ) * (1 - 1 / 2) *
            (βmin : ℝ≥0∞).toReal)) :=
      (Finset.expect_le_expect fun GB _ => (Finset.expect_le_expect fun GS _ =>
        expect_mcDiarmidTerms_le_of (oraclePrimitives GB GS) (A' GB GS) hp' hβ0 hβ1 hβt hθ0 hθ1
          (by norm_num) C
          commitCollisionBound_le_mldsa65 one_div_sixteen_le_standinScale_mul_card_mldsa65
          two_pow_le_card_bucketVec_mldsa65).trans_eq
        (Finset.expect_const univ_nonempty _)).trans_eq (Finset.expect_const univ_nonempty _)
    have hI := expect_idealAnonError_le (p := mldsa65) (A := A') isApproved_mldsa65 hβ0 hβt hθ0
      (s := 1 / 2) (by norm_num) C (expect_regGapAvg_le_mldsa65 hβ0 hβ1)
    have hL1 : ∀ GB GS, 𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa65.k mldsa65.l,
        anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C ≤
          idealAnonError (oraclePrimitives GB GS) (A' GB GS) hp' hβ0 hβt (1 / 2) θ C :=
      fun GB GS => expect_anonError_le_idealAnonError (oraclePrimitives GB GS) (A' GB GS) hp' hβ0
        hβt hθ0 (by norm_num) C
    refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
      hL1 GB GS).trans (hI.trans ?_)
    have h2 : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
    have hm : √(N * n * Real.log (C + 1)) / (2 ^ 2000 * (θ * (1 - θ) * (1 - 1 / 2) *
      (βmin : ℝ≥0∞).toReal)) =
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal)) := by
      rw [show (2 : ℝ) ^ 2000 = 2 ^ 1999 * 2 from pow_succ 2 1999]
      generalize (2 : ℝ) ^ 1999 = T
      ring
    rw [h2]
    refine add_le_add le_rfl (hM.trans_eq hm)
  -- the failure of the good event
  have hchk : checkError reps tol (1 / 2) 89 ≤ 1 / 2 ^ 240 := by
    rw [hreps, htol]; exact checkError_checkParams_le
  have hE2 : ∀ GB GS GA, 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
      𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps,
        (if good GB GS GA keys HG then 0 else 1 : ℝ) ≤
      2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C + C / 2 ^ 240 := fun GB GS GA => by
    have hlaws := SigningLaws.withExpandA (oraclePrimitives GB GS)
      (signingLaws_concreteWithSampleInBallExpandS isApproved_mldsa65 (sampleInBallShape_oraclePrims GB) _)
      GA
    have hO := expect_expect_oracleError_le (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA)
      hp' hβ0 hβt hlaws (fun _ => (secretOfCoeffs_bounded (GS _)).2) hθ0 hθ1 (s := 1 / 2)
      (by norm_num) (hC GB GS GA)
    have hK := fun keys => expect_ite_keepGood_le (withExpandA (oraclePrimitives GB GS) GA)
      (A' GB GS GA) hp' hβ0 hβt (s := 1 / 2) (θ := θ) (by norm_num) hθ0 (x := 89) (by norm_num)
      (hC GB GS GA) keys
    calc _ ≤ 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
          (2 * 𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps,
            oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ
              keys HG.1 +
            (C : ℝ) * checkError reps tol (1 / 2) 89) := Finset.expect_le_expect fun keys _ => hK keys
      _ ≤ 2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C + (C : ℝ) * (1 / 2 ^ 240) := by
          rw [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
          exact add_le_add (mul_le_mul_of_nonneg_left hO zero_le_two)
            (mul_le_mul_of_nonneg_left hchk (Nat.cast_nonneg _))
      _ = _ := by rw [mul_one_div]
  -- the hedged error
  have hE1 : ∀ GB GS GA, 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
      𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa65) Msg N reps,
        ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
          (concreteEnc mldsa65) T hT).hedgeError 1 q ka
            (1 - if good GB GS GA keys HG then ENNReal.ofReal Lk else 0)).toReal ≤
        (ka ^ 2 + 2 * q * ka) / 2 ^ 256 + 2 * ((1 - Lk) ^ ka +
          (2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C + C / 2 ^ 240)) :=
    fun GB GS GA => by
      have h := MaskedSigner.expect_toReal_hedgeError_le (hedgedSigner (withExpandA
        (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol (concreteEnc mldsa65) T hT) 1 q ka
        (good GB GS GA) hLk0 hLk1
      have hcard : (Fintype.card (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
          (Msg := Msg) N βmin reps tol (concreteEnc mldsa65) T hT).Rnd : ℝ) = 2 ^ 256 := card_bytes32
      rw [hcard] at h
      refine h.trans ?_
      have h3 := hE2 GB GS GA
      have : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
      simp only [Nat.cast_one, one_mul] at h ⊢
      have hc : ((ka : ℝ) ^ 2 * (2 ^ 256)⁻¹ + (1 + 1) * q * ka * (2 ^ 256)⁻¹) =
          (ka ^ 2 + 2 * q * ka) / 2 ^ 256 := by ring
      rw [hc]
      nlinarith [h3]
  refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
    Finset.expect_le_expect fun GA _ => hE1 GB GS GA).trans ?_
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
  have hfin := hE3
  nlinarith [hfin]

end Hedged_mldsa65

section Hedged_mldsa87

variable {Msg : Type} [Fintype Msg] [DecidableEq Msg] {N : ℕ} {βmin : ℚ≥0} {reps tol T : ℕ}
  (hT : 0 < T) {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {n : ℕ}
  {M : ∀ (GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau) (GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87)
    (GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l),
    SPBCS Mg P (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
      (concreteEnc mldsa87)).Stmt k kN kS L e}
  (A : ∀ GB GS GA, PubAnonAdversary (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
    (Msg := Msg) N βmin reps tol (concreteEnc mldsa87) T hT).real (M GB GS GA) n 1)
  {E : ∀ GB GS GA, (j : ι) → ((M GB GS GA).comp j).Encoder}
  {V : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc mldsa87)).Stmt → FullTr P τ → Bool}
  {Qs : ∀ GB GS GA H x, (M GB GS GA).IOPQueries (V GB GS GA H) x} {R : Type} [Fintype R]
  [Nonempty R]
  {honest : ∀ GB GS GA, GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps →
    (pubSigner (withExpandA (oraclePrimitives GB GS) GA)
      (Msg := Msg) N βmin reps tol (concreteEnc mldsa87)).Wit → R → CausalProver P τ
          (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
            (concreteEnc mldsa87)).Stmt}
  (D : ∀ GB GS GA, (Fin n → _root_.MLDSA.Bytes 32) →
    GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps × (_root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa87) →
    (Query k kN kS L → Out k e) → PubHist (BucketVec mldsa87) (M GB GS GA).NIProof 1 → Prop)

open Classical in
/-- **Anonymity at ML-DSA-87 with FImldsa87 204 hedged signing at the check parameters**
(BKM06 Definition 4, ePrint 2005/304, p. 6, `Q = 1`, keys given at the start as in CCLM22
Experiment 2, p. 21): `advantage_le_bkm06_mldsa87_checkParams` for the ideal-mask signer at every
fixed mask oracle (`advantage_le_hedged`), plus twice the hedged error
`(k² + 2 q k) / 2^256 + 2 (1 - s̄)^k` averaged over the oracles and the users' coins, for an
adversary and a distinguisher with at most `q` mask-oracle queries per phase (`hq`), at most `C`
challenges of its set valid for any key vector (`hC`), a lower bound `s̄` on the keep probability
of one ring attempt (`hkeep`, a hypothesis not proved in Lean in this step) and every number `k`
of attempts (`ka`). The masks are `ExpandMask(H(K ‖ rnd ‖ µ), κ)` with `H` and ExpandMask one
random oracle, at most `T` per call and a fresh `rnd` per call; deterministic signing
(`rnd = 0`) is not covered. The check term `C / 2^240` counts the candidate rings per key vector,
not the mask-oracle queries. -/
theorem advantage_le_bkm06_mldsa87_hedged (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hreps : reps = 355) (htol : tol = 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) [NeZero n]
    (Rv : ∀ GB GS GA H, (M GB GS GA).Reveal (E GB GS GA) (Qs GB GS GA H)) {PubZ : Type}
    {pubZ : ∀ GB GS GA, (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc mldsa87)).Stmt → PubZ}
    {sim : ∀ GB GS GA H, CausalJointSimulator (Rv GB GS GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GB GS GA H, CausalHVZK (Rv GB GS GA H).MV ((pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa87)).rel H)
      (honest GB GS GA H) (pubZ GB GS GA) (sim GB GS GA H) δ)
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C) {q : ℕ}
    (hq : ∀ GB GS GA, (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc mldsa87) T hT).QueryBounded (A GB GS GA) (D GB GS GA) q) (ka : ℕ)
    (sbar : ∀ (_GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau)
      (_GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87) (_GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l),
      (Fin n → _root_.MLDSA.Bytes 32) → GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps → ℝ≥0∞)
    (hkeep : ∀ GB GS GA, KeepBound (withExpandA (oraclePrimitives GB GS) GA) βmin tol
      (A GB GS GA).choices (sbar GB GS GA)) :
    𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
          (A GB GS GA).advantage (V := fun HY => V GB GS GA HY.1) (E GB GS GA)
            (fun HY => Qs GB GS GA HY.1) (fun HY => honest GB GS GA HY.1) (D GB GS GA) ≤
      2 * (2 * 2 / θ * (n * (12 / 2 ^ 294 * (33 / 5) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
                (M GB GS GA).wiError δ C +
          C / 2 ^ 240 +
        2 * 𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
              𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
                𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps,
                  ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
                    (concreteEnc mldsa87) T hT).hedgeError 1 q ka (1 - sbar GB GS GA keys HG)).toReal := by
  set B : ℝ := 2 * (2 * 2 / θ* (n * (12 / 2 ^ 294 * (33 / 5) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
                (M GB GS GA).wiError δ C +
          C / 2 ^ 240
  -- at every fixed mask oracle, the ideal-mask bound
  have hY : ∀ Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa87,
      𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
          𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
            ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
              (concreteEnc mldsa87) T hT).atMask (A GB GS GA) Y).advantage (E GB GS GA) (Qs GB GS GA)
                (honest GB GS GA) (fun keys H => D GB GS GA keys (H, Y)) ≤ B := fun Y =>
    advantage_le_bkm06_mldsa87_checkParams
      (fun GB GS GA => (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
        reps tol (concreteEnc mldsa87) T hT).atMask (A GB GS GA) Y)
      (fun GB GS GA keys H => D GB GS GA keys (H, Y)) hβ0 hβ1 hβt hreps htol hθ0 hθ1 Rv hz hC
  -- at every oracle, the hedged step
  refine expect3_le_of_mix _ _ (fun GB GS GA (Y : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa87) =>
      ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa87) T hT).atMask (A GB GS GA) Y).advantage (E GB GS GA) (Qs GB GS GA)
          (honest GB GS GA) (fun keys H => D GB GS GA keys (H, Y))) (fun GB GS GA => ?_) hY
  exact advantage_le_hedged (withExpandA (oraclePrimitives GB GS) GA) hT
    (V := V GB GS GA) (E := E GB GS GA) (Qs := Qs GB GS GA) (honest := honest GB GS GA)
    (A GB GS GA) (D GB GS GA) (hq GB GS GA) ka (sbar GB GS GA) (hkeep GB GS GA)

open Classical in
/-- **Anonymity at ML-DSA-87 with FImldsa87 204 hedged signing, the keep bound discharged**
(BKM06 Definition 4, ePrint 2005/304, p. 6, `Q = 1`): `advantage_le_bkm06_mldsa87_hedged` with the
keep bound `s̄ = β_min θ / 64` on the good event (`keepBound_of_keepGood`: the anonymity error
below `1/2` and no high-defect ring passing the check, `keep_ge_of_familyBound_lt`, with
`K |V| ≥ 1/16`), whose failure is at most twice the anonymity error plus the check term
(`expect_ite_keepGood_le`), evaluated as in `advantage_le_bkm06_mldsa87_checkParams`. For every
adversary and distinguisher with at most `q` mask-oracle queries per phase (`hq`) and every number
`k` of hedged calls (`ka`), the advantage is at most the ideal-mask bound plus
`2 · ((k² + 2 q k) / 2^256 + 2 · ((1 - β_min θ / 64)^k + 2 · (regularity + McDiarmid) + C / 2^240))`.
Deterministic signing (`rnd = 0`) is not covered. -/
theorem advantage_le_bkm06_mldsa87_hedged_keep (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβ1 : (βmin : ℝ≥0∞) ≤ 1)
    (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (hreps : reps = 355) (htol : tol = 2) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) [NeZero n]
    (Rv : ∀ GB GS GA H, (M GB GS GA).Reveal (E GB GS GA) (Qs GB GS GA H)) {PubZ : Type}
    {pubZ : ∀ GB GS GA, (pubSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc mldsa87)).Stmt → PubZ}
    {sim : ∀ GB GS GA H, CausalJointSimulator (Rv GB GS GA H).MV PubZ} {δ : NNReal}
    (hz : ∀ GB GS GA H, CausalHVZK (Rv GB GS GA H).MV ((pubSigner
      (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
        (concreteEnc mldsa87)).rel H)
      (honest GB GS GA H) (pubZ GB GS GA) (sim GB GS GA H) δ)
    {C : ℕ} (hC : ∀ GB GS GA, (A GB GS GA).ValidCountLe C) {q : ℕ}
    (hq : ∀ GB GS GA, (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin
      reps tol (concreteEnc mldsa87) T hT).QueryBounded (A GB GS GA) (D GB GS GA) q) (ka : ℕ) :
    𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
          (A GB GS GA).advantage (V := fun HY => V GB GS GA HY.1) (E GB GS GA)
            (fun HY => Qs GB GS GA HY.1) (fun HY => honest GB GS GA HY.1) (D GB GS GA) ≤
      2 * (2 * 2 / θ * (n * (12 / 2 ^ 294 * (33 / 5) / (βmin : ℝ≥0∞).toReal)) +
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
        𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
          𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
            𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
                (M GB GS GA).wiError δ C +
          C / 2 ^ 240 +
        2 * ((ka ^ 2 + 2 * q * ka) / 2 ^ 256 + 2 * ((1 - (βmin : ℝ≥0∞).toReal * θ / 64) ^ ka +
          (2 * (2 * 2 / θ * (n * (12 / 2 ^ 294 * (33 / 5) / (βmin : ℝ≥0∞).toReal)) +
            √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal))) +
            C / 2 ^ 240))) := by
  have := concreteNTTRingLaws
  have := challengeBall_nonempty floorParams_mldsa87.tau_le
  have hp' := SigningParams.of_isApproved isApproved_mldsa87
  have hb0 : 0 < (βmin : ℝ≥0∞).toReal := ENNReal.toReal_pos hβ0 hβt
  have hb1 : (βmin : ℝ≥0∞).toReal ≤ 1 := ENNReal.toReal_le_one_of_le_one hβ1
  set Y0 : _root_.MLDSA.Bytes 32 × MaskPt T Msg → MaskBox mldsa87 := fun _ => Classical.arbitrary _
  set A' := fun GB GS GA => (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N
    βmin reps tol (concreteEnc mldsa87) T hT).atMask (A GB GS GA) Y0
  set Lk : ℝ := (βmin : ℝ≥0∞).toReal * θ / 64
  have hLk0 : 0 ≤ Lk := by positivity
  have hLk1 : Lk ≤ 1 := by
    have : (βmin : ℝ≥0∞).toReal * θ ≤ 1 := mul_le_one₀ hb1 hθ0.le hθ1.le
    show (βmin : ℝ≥0∞).toReal * θ / 64 ≤ 1
    linarith
  have hLk : Lk ≤ keepLevel mldsa87 βmin (1 / 2) θ := by
    have hK := one_div_sixteen_le_standinScale_mul_card_mldsa87
    unfold keepLevel
    rw [ENNReal.toReal_mul]
    have hx := mul_le_mul_of_nonneg_right hK (by positivity : (0 : ℝ) ≤ (βmin : ℝ≥0∞).toReal * θ)
    show (βmin : ℝ≥0∞).toReal * θ / 64 ≤ _
    nlinarith [hx]
  set good := fun GB GS GA => KeepGood (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp'
    hβ0 hβt (1 / 2) θ
  have hkeep : ∀ GB GS GA, KeepBound (withExpandA (oraclePrimitives GB GS) GA) βmin tol
      (A GB GS GA).choices fun keys HG => if good GB GS GA keys HG then ENNReal.ofReal Lk else 0 :=
    fun GB GS GA => keepBound_of_keepGood _ (A' GB GS GA) hp' hβ0 hβt hθ0 hθ1 (by norm_num) hLk
  have h1 := advantage_le_bkm06_mldsa87_hedged hT A D hβ0 hβ1 hβt hreps htol hθ0 hθ1 Rv hz hC hq ka
    (fun GB GS GA keys HG => if good GB GS GA keys HG then ENNReal.ofReal Lk else 0) hkeep
  refine h1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ zero_le_two))
  -- the anonymity error of the adversaries at `Y0`, averaged
  have hE3 : 𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
      𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
        𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
          anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C ≤
        2 * 2 / θ * (n * (12 / 2 ^ 294 * (33 / 5) / (βmin : ℝ≥0∞).toReal)) +
          √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal)) := by
    have hM : 𝔼 GB : CommitHashBytes mldsa87 → ChallengeBall mldsa87.tau,
        𝔼 GS : _root_.MLDSA.Bytes 64 → SecretCoeffs mldsa87,
          𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
            𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
              (√(maxDevVar (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ
                  keys * Real.log C / 2) +
                √(maxCountVar (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt
                  (1 / 2) θ keys * Real.log (C + 1) / 2)) ≤
          √(N * n * Real.log (C + 1)) / (2 ^ 2000 * (θ * (1 - θ) * (1 - 1 / 2) *
            (βmin : ℝ≥0∞).toReal)) :=
      (Finset.expect_le_expect fun GB _ => (Finset.expect_le_expect fun GS _ =>
        expect_mcDiarmidTerms_le_of (oraclePrimitives GB GS) (A' GB GS) hp' hβ0 hβ1 hβt hθ0 hθ1
          (by norm_num) C
          commitCollisionBound_le_mldsa87 one_div_sixteen_le_standinScale_mul_card_mldsa87
          two_pow_le_card_bucketVec_mldsa87).trans_eq
        (Finset.expect_const univ_nonempty _)).trans_eq (Finset.expect_const univ_nonempty _)
    have hI := expect_idealAnonError_le (p := mldsa87) (A := A') isApproved_mldsa87 hβ0 hβt hθ0
      (s := 1 / 2) (by norm_num) C (expect_regGapAvg_le_mldsa87 hβ0 hβ1)
    have hL1 : ∀ GB GS, 𝔼 GA : _root_.MLDSA.Bytes 32 → TqMatrix mldsa87.k mldsa87.l,
        anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C ≤
          idealAnonError (oraclePrimitives GB GS) (A' GB GS) hp' hβ0 hβt (1 / 2) θ C :=
      fun GB GS => expect_anonError_le_idealAnonError (oraclePrimitives GB GS) (A' GB GS) hp' hβ0
        hβt hθ0 (by norm_num) C
    refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
      hL1 GB GS).trans (hI.trans ?_)
    have h2 : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
    have hm : √(N * n * Real.log (C + 1)) / (2 ^ 2000 * (θ * (1 - θ) * (1 - 1 / 2) *
      (βmin : ℝ≥0∞).toReal)) =
        √(N * n * Real.log (C + 1)) / (2 ^ 1999 * (θ * (1 - θ) * (βmin : ℝ≥0∞).toReal)) := by
      rw [show (2 : ℝ) ^ 2000 = 2 ^ 1999 * 2 from pow_succ 2 1999]
      generalize (2 : ℝ) ^ 1999 = T
      ring
    rw [h2]
    refine add_le_add le_rfl (hM.trans_eq hm)
  -- the failure of the good event
  have hchk : checkError reps tol (1 / 2) 89 ≤ 1 / 2 ^ 240 := by
    rw [hreps, htol]; exact checkError_checkParams_le
  have hE2 : ∀ GB GS GA, 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
      𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps,
        (if good GB GS GA keys HG then 0 else 1 : ℝ) ≤
      2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C + C / 2 ^ 240 := fun GB GS GA => by
    have hlaws := SigningLaws.withExpandA (oraclePrimitives GB GS)
      (signingLaws_concreteWithSampleInBallExpandS isApproved_mldsa87 (sampleInBallShape_oraclePrims GB) _)
      GA
    have hO := expect_expect_oracleError_le (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA)
      hp' hβ0 hβt hlaws (fun _ => (secretOfCoeffs_bounded (GS _)).2) hθ0 hθ1 (s := 1 / 2)
      (by norm_num) (hC GB GS GA)
    have hK := fun keys => expect_ite_keepGood_le (withExpandA (oraclePrimitives GB GS) GA)
      (A' GB GS GA) hp' hβ0 hβt (s := 1 / 2) (θ := θ) (by norm_num) hθ0 (x := 89) (by norm_num)
      (hC GB GS GA) keys
    calc _ ≤ 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
          (2 * 𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps,
            oracleError (withExpandA (oraclePrimitives GB GS) GA) (A' GB GS GA) hp' hβ0 hβt (1 / 2) θ
              keys HG.1 +
            (C : ℝ) * checkError reps tol (1 / 2) 89) := Finset.expect_le_expect fun keys _ => hK keys
      _ ≤ 2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C + (C : ℝ) * (1 / 2 ^ 240) := by
          rw [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
          exact add_le_add (mul_le_mul_of_nonneg_left hO zero_le_two)
            (mul_le_mul_of_nonneg_left hchk (Nat.cast_nonneg _))
      _ = _ := by rw [mul_one_div]
  -- the hedged error
  have hE1 : ∀ GB GS GA, 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
      𝔼 HG : GameOrc (concretePrimitivesKeyGen mldsa87) Msg N reps,
        ((hedgedSigner (withExpandA (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol
          (concreteEnc mldsa87) T hT).hedgeError 1 q ka
            (1 - if good GB GS GA keys HG then ENNReal.ofReal Lk else 0)).toReal ≤
        (ka ^ 2 + 2 * q * ka) / 2 ^ 256 + 2 * ((1 - Lk) ^ ka +
          (2 * anonError (A := A' GB GS GA) hp' hβ0 hβt (1 / 2) θ C + C / 2 ^ 240)) :=
    fun GB GS GA => by
      have h := MaskedSigner.expect_toReal_hedgeError_le (hedgedSigner (withExpandA
        (oraclePrimitives GB GS) GA) (Msg := Msg) N βmin reps tol (concreteEnc mldsa87) T hT) 1 q ka
        (good GB GS GA) hLk0 hLk1
      have hcard : (Fintype.card (hedgedSigner (withExpandA (oraclePrimitives GB GS) GA)
          (Msg := Msg) N βmin reps tol (concreteEnc mldsa87) T hT).Rnd : ℝ) = 2 ^ 256 := card_bytes32
      rw [hcard] at h
      refine h.trans ?_
      have h3 := hE2 GB GS GA
      have : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
      simp only [Nat.cast_one, one_mul] at h ⊢
      have hc : ((ka : ℝ) ^ 2 * (2 ^ 256)⁻¹ + (1 + 1) * q * ka * (2 ^ 256)⁻¹) =
          (ka ^ 2 + 2 * q * ka) / 2 ^ 256 := by ring
      rw [hc]
      nlinarith [h3]
  refine (Finset.expect_le_expect fun GB _ => Finset.expect_le_expect fun GS _ =>
    Finset.expect_le_expect fun GA _ => hE1 GB GS GA).trans ?_
  simp only [Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]
  have hfin := hE3
  nlinarith [hfin]

end Hedged_mldsa87

end GordieHowe.Ring.MLDSAW1
