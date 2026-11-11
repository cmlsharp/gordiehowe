-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1Ring
public import GordieHowe.Model.Signature.Rejection

@[expose] public section

/-!
# The base signer of the ML-DSA ring publishing `w₁` as a rejection signer

The ring-aware base signer `w1BaseSigner … (ringLoop src O βmin k D) bmsg`
(`GordieHowe/Applications/Ring/MLDSAW1Ring.lean`) is, on honest keys, a standard signer followed by
a public rejection (`Signature.IsRejectionOn`, `GordieHowe/Model/Signature/Rejection.lean`), so the
lifting lemma of `GordieHowe/Model/Signature/RejectionRelay.lean` bounds its multi-user game by the
multi-user game of the standard signer: one call of FIPS 204 hedged signing (`stdProg`, `T`
attempts at one nonce).

- `w1Keep`: the public keep decision of one call's signature `σ` at the position `i` of `R` with
  the keep coin `u ∈ Fin D`: the members' message representatives `µ_j = H_µ(tr_j, bmsg R m)` are
  pairwise distinct, and `u < D · min(1, β_min / aw_i) · ∏_{j ≠ i} min(1, aw_j / β_min)` with the
  weights of the members' published `t₀` at the recomputed commitment `w₁ = w1Of pk_i σ` and the
  members' commitment hashes `H(µ_j, w₁)` (the signer's own hash is `σ`'s `c̃`). At most `2N`
  queries (`w1Keep_queries`); `keepBit`, the decision on the values read, and `run_w1Keep`.
- `w1Rejection`: the rejection form: standard coins the nonce, keep coins `Fin D`, the standard
  signer `stdProg` at one nonce, the check `ringCheckProg`, the keep decision `w1Keep`.
- `w1CoinEquiv`: the base signer's coins as `k` pairs of a nonce and a keep coin.
- `run_stdProg_one`: one call of the standard signer computes the first accepted attempt against
  the commitment hashes at the masks of the nonce.
- `isStdOn_w1Base`: the ordinary signer is the standard signer at the first nonce
  (`Signature.IsStdOn`, the hypothesis of the key-reuse lifting), for `0 < k`.
- `callOut_eq_att`: on an honest key at its position, one call of the ring loop is one attempt of
  the rejection form: the standard signature, kept by `w1Keep`, given the signing and verification
  laws and an encoding coherent with `bucketsOf`.
- `att_eq_none_of_not_nodup`: without distinct message representatives no attempt is kept.
- `isRejectionOn_w1Base`: **the base signer is the rejection form `w1Rejection` with `k` attempts
  on honest keys**, under the same hypotheses as `correctWithin_w1BaseSigner`.
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.Signature
open scoped ENNReal

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type}

section Keep

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps] {N reps : ℕ}
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg]
  [DecidableEq Msg] (O : W1Oracles X Y p prims Msg N reps) (βmin : ℚ≥0) (D : ℕ)
  (enc : Vector prims.High p.k → BucketVec p) {RMsg : Type}
  (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg)

/-- **The keep decision of one call's signature as a number**: the members' message
representatives `mus` are pairwise distinct and the keep coin `u` is below `D` times the
flattening weight at the commitment `w₁`, with the signer's weight at its hash `c̃` and the
members' weights at the hashes `hs`. The weights are rational, compared in `ℚ≥0`. -/
def keepBit (R : KeyRing (PubKey p prims) N) (i : Fin R.1.length) (w1 : BucketVec p)
    (cTilde : CommitHashBytes p) (mus : List (Bytes 64)) (hs : List (CommitHashBytes p))
    (u : Fin D) : Bool :=
  decide mus.Nodup && decide (((u : ℕ) : ℚ≥0) < D * (NNRat.minOneDiv βmin
    (t0Weight prims (R.1[i]).2.2 (w1, cTilde)) *
    (ringWeights prims βmin (ringT0s prims R.1)).otherWeight i (fun x => hs.getD x.1 default) w1))

/-- **The public keep decision of one call's signature** `σ` at the position `i` of `R` on the
message `m` with the keep coin `u`: the members' message representatives (one query per member),
their commitment hashes at the recomputed commitment `w1Of pk_i σ` (one query per member), then
`keepBit`; `false` when `i` is not a position of `R`. -/
def w1Keep (R : KeyRing (PubKey p prims) N) (i : ℕ) (m : RMsg)
    (σ : FIPSSignature p prims) (u : Fin D) : OracleProg X Y Bool :=
  if hi : i < R.1.length then
    (OracleProg.queryAll (R.1.map fun x => O.muPt (pubTr prims x, bmsg R m))).bind fun ans =>
      (OracleProg.queryAll ((List.range R.1.length).map fun j =>
          O.chPt ((ans.map O.muAns).getD j default, w1Of prims enc (R.1[i]'hi) σ))).mapOutput
        fun hs => keepBit prims βmin D R ⟨i, hi⟩ (w1Of prims enc (R.1[i]'hi) σ) σ.cTilde
          (ans.map O.muAns) (hs.map O.chAns) u
  else .pure false

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Inhabited prims.Hint] [Fintype Msg] [DecidableEq Msg] in
/-- The keep decision makes at most `2N` queries. -/
theorem w1Keep_queries (R : KeyRing (PubKey p prims) N) (i : ℕ) (m : RMsg)
    (σ : FIPSSignature p prims) (u : Fin D) :
    (w1Keep prims O βmin D enc bmsg R i m σ u).QueriesLE (N + N) := by
  unfold w1Keep
  split_ifs with hi
  · have h₁ := (OracleProg.QueriesLE.queryAll (B := Y)
      (R.1.map fun x => O.muPt (pubTr prims x, bmsg R m))).mono
      (show (R.1.map fun x => O.muPt (pubTr prims x, bmsg R m)).length ≤ N by
        rw [List.length_map]; exact R.2)
    refine h₁.bind fun ans => ?_
    refine ((OracleProg.QueriesLE.queryAll (B := Y) ((List.range R.1.length).map fun j =>
      O.chPt ((ans.map O.muAns).getD j default, w1Of prims enc (R.1[i]'hi) σ))).mono ?_).mapOutput _
    simpa using R.2
  · exact (OracleProg.QueriesLE.pure _ _).mono (Nat.zero_le _)

omit [NeZero (bucketCount p)] [Nonempty (MaskBox p)] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Inhabited prims.Hint] [Fintype Msg] [DecidableEq Msg] in
/-- **The keep decision computes `keepBit`** at the members' message representatives and their
commitment hashes at the recomputed commitment, read from the oracle. -/
theorem run_w1Keep (R : KeyRing (PubKey p prims) N) (i : ℕ) (hi : i < R.1.length) (m : RMsg)
    (σ : FIPSSignature p prims) (u : Fin D) (H : X → Y) :
    (w1Keep prims O βmin D enc bmsg R i m σ u).run H =
      keepBit prims βmin D R ⟨i, hi⟩ (w1Of prims enc (R.1[i]'hi) σ) σ.cTilde
        ((R.1.map fun x => O.muPt (pubTr prims x, bmsg R m)).map (O.muAns ∘ H))
        ((List.range R.1.length).map fun j =>
          O.chOrc H ((((R.1.map fun x => O.muPt (pubTr prims x, bmsg R m)).map H).map O.muAns).getD
            j default, w1Of prims enc (R.1[i]'hi) σ)) u := by
  simp only [w1Keep, hi, ↓reduceDIte, OracleProg.run_bind, OracleProg.run_mapOutput,
    OracleProg.run_queryAll, List.map_map]
  rfl

end Keep


section Form

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps] {N reps : ℕ}
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg]
  [DecidableEq Msg] (src : MaskSource X Y p T Msg) (O : W1Oracles X Y p prims Msg N reps)
  (βmin : ℚ≥0) (tol k D : ℕ) [NeZero D] (enc : Vector prims.High p.k → BucketVec p)
  {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg] (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg)

/-- **The base signer of the ring publishing `w₁` with the ring loop as a rejection form**: one
attempt is one call of the standard signer (`stdProg` at one nonce), the check is the public ring
check, the keep decision `w1Keep` with a keep coin on `Fin D`. -/
@[reducible] noncomputable def w1Rejection :
    Rejection (w1BaseSigner prims O βmin tol enc (ringLoop prims src O βmin k D) bmsg) where
  StdCoins := src.Rnd
  KeepCoins := Fin D
  qStd := 1 + T * src.qr + T
  std sk bm r := stdProg prims src O.toMLDSAOracles 1 sk bm fun _ => r
  std_queries sk bm _ := stdProg_queries prims src O.toMLDSAOracles 1 sk bm _
  qCheck := N * reps
  check R := ringCheckProg prims O βmin tol R
  check_queries R := ringCheckProg_queries prims O βmin tol R
  qKeep := N + N
  keep R i m σ u := w1Keep prims O βmin D enc bmsg R i m σ u
  keep_queries R i m σ u := w1Keep_queries prims O βmin D enc bmsg R i m σ u

/-- **The coins of the ring loop as `k` attempts**: the nonce and the keep coin of each call. -/
def w1CoinEquiv : (Fin k → src.Rnd) × (Fin k → Fin D) ≃ (Fin k → src.Rnd × Fin D) :=
  (Equiv.arrowProdEquivProdArrow _ _ _).symm

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] [Fintype Msg] [DecidableEq Msg] in
/-- **One call of the standard signer**: the first of the `T` masks of the nonce `r` whose
attempt passes the checks at the commitment hash `H((tr, m), w₁)` of its commitment. -/
theorem run_stdProg_one (sk : SecretKey p) (m : Msg) (r : src.Rnd) (H : X → Y) :
    (stdProg prims src O.toMLDSAOracles 1 sk m fun _ => r).run H =
      match (List.finRange T).find? (fun t => attemptAccept prims sk (prims.expandA sk.rho)
          ((src.read r (t, (sk.key, (sk.tr, m)))).run H)
          (O.hOrc H ((sk.tr, m), realBuckets (prims.expandA sk.rho)
            ((src.read r (t, (sk.key, (sk.tr, m)))).run H)))) with
      | some t => some (attemptOutput prims sk (prims.expandA sk.rho)
          ((src.read r (t, (sk.key, (sk.tr, m)))).run H,
            O.hOrc H ((sk.tr, m), realBuckets (prims.expandA sk.rho)
              ((src.read r (t, (sk.key, (sk.tr, m)))).run H))))
      | none => none := by
  simp only [stdProg, Nat.zero_lt_one, ↓reduceDIte, OracleProg.run_query,
    OracleProg.run_bind, OracleProg.run_mapOutput, OracleProg.run_tabulate, OracleProg.run_pure,
    List.mem_finRange, ite_true]
  rfl

variable [Fintype src.Rnd] [DecidableEq src.Rnd] [Nonempty src.Rnd]

omit [Inhabited prims.Hint] in
/-- **The ordinary signer is the standard signer at the first nonce** (`Signature.IsStdOn`, the
hypothesis of the key-reuse lifting lemma), for `0 < k`. -/
theorem isStdOn_w1Base (hk : 0 < k) :
    IsStdOn (w1BaseSigner prims O βmin tol enc (ringLoop prims src O βmin k D) bmsg)
      (w1Rejection prims src O βmin tol k D enc bmsg) k (w1CoinEquiv src k D) hk := by
  intro H kc bm c
  simp only [w1BaseSigner, ringLoop]
  change (stdProg prims src O.toMLDSAOracles k _ bm c.1).run H =
    (stdProg prims src O.toMLDSAOracles 1 _ bm fun _ => c.1 ⟨0, hk⟩).run H
  unfold stdProg
  simp only [hk, Nat.zero_lt_one, ↓reduceDIte]

omit [Inhabited prims.Hint] in
/-- **One call of the ring loop is one attempt of the rejection form** on an honest key at a
position `i` of the ring whose members' message representatives are distinct: the call's output at
the masks of the nonce `r` with the keep coin `u` is the standard signature of the nonce, kept by
`w1Keep` with `u`, given the signing and verification laws, an encoding `enc` coherent with
`bucketsOf` and `‖s₂‖∞ ≤ η` for the key. -/
theorem callOut_eq_att (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    {seed : Bytes 32} (hs2 : polyVecBounded (keyGen prims seed).2.s2 p.eta)
    {R : KeyRing (PubKey p prims) N} {i : ℕ} (hi : i < R.1.length)
    (hRi : R.1[i]'hi = (keyGen prims seed).1) (m : RMsg) (H : X → Y)
    (hmu : ((R.1.map fun x => O.muPt (pubTr prims x, bmsg R m)).map (O.muAns ∘ H)).Nodup)
    (r : src.Rnd) (u : Fin D) :
    callOut prims βmin D (keyGen prims seed).2 R ⟨i, hi⟩
        (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc H))
        (fun t => (src.read r (t, ((keyGen prims seed).2.key,
          ((keyGen prims seed).2.tr, bmsg R m)))).run H) u =
      (w1Rejection prims src O βmin tol k D enc bmsg).att H (keyGen prims seed).2 R i m (r, u) := by
  set sk := (keyGen prims seed).2 with hsk
  set A := prims.expandA sk.rho
  set ys : Fin T → MaskBox p := fun t => (src.read r (t, (sk.key, (sk.tr, bmsg R m)))).run H
  have hhc : ∀ w, PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc H) (⟨i, hi⟩, w) =
      O.hOrc H ((sk.tr, bmsg R m), w) := fun w => by
    simp only [PMF.ringOf, ringPts, List.get_eq_getElem, hRi, pubTr, hsk, keyGen, keyGenFromSeed_tr]
  have hstd : ((w1Rejection prims src O βmin tol k D enc bmsg).std sk
      ((w1BaseSigner prims O βmin tol enc (ringLoop prims src O βmin k D) bmsg).bmsg R m) r).run H =
      (stdProg prims src O.toMLDSAOracles 1 sk (bmsg R m) fun _ => r).run H := rfl
  have hkeep : ∀ σ, ((w1Rejection prims src O βmin tol k D enc bmsg).keep R i m σ u).run H =
      (w1Keep prims O βmin D enc bmsg R i m σ u).run H := fun _ => rfl
  unfold Rejection.att
  dsimp only
  rw [hstd, run_stdProg_one]
  unfold callOut
  simp only [hhc]
  rcases hf : (List.finRange T).find? (fun t => attemptAccept prims sk A (ys t)
      (O.hOrc H ((sk.tr, bmsg R m), realBuckets A (ys t)))) with _ | t
  · rfl
  · have hacc : attemptAccept prims sk A (ys t)
        (O.hOrc H ((sk.tr, bmsg R m), realBuckets A (ys t))) = true := by
      simpa using List.find?_some hf
    dsimp only
    erw [hkeep, run_w1Keep prims O βmin D enc bmsg R i hi m _ u H]
    -- the recomputed commitment of the attempt's signature is the mask's commitment
    have hver := ringVerify_attemptOutput prims h_laws hv henc (seed := seed)
      (pk := (keyGenFromSeed p prims seed).1) (sk := (keyGenFromSeed p prims seed).2) rfl hs2
      (O.hOrc H) (bmsg R m) (ys t) (by simpa only [hsk, A, keyGen, keyGenFromSeed_rho,
        keyGenFromSeed_tr] using hacc)
    have hw : w1Of prims enc (R.1[i]'hi) (attemptOutput prims sk A
        (ys t, O.hOrc H ((sk.tr, bmsg R m), realBuckets A (ys t)))) = realBuckets A (ys t) := by
      simp only [ringVerify, Bool.and_eq_true, decide_eq_true_eq] at hver
      rw [hRi]
      simpa only [w1Of, hsk, A, keyGen, keyGenFromSeed_rho, keyGenFromSeed_tr, pubPk] using
        hver.1.1.2
    rw [hw]
    have hother : ∀ v, (ringWeights prims βmin (ringT0s prims R.1)).otherWeight ⟨i, hi⟩
        (fun x => (((List.range R.1.length).map fun j =>
          O.chOrc H ((((R.1.map fun x => O.muPt (pubTr prims x, bmsg R m)).map H).map
            O.muAns).getD j default, v))).getD x.1 default) v =
        (ringWeights prims βmin (ringT0s prims R.1)).otherWeight ⟨i, hi⟩
          (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc H)) v := fun v =>
      Finset.prod_congr rfl fun j _ => by
        dsimp only
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range j.2, Option.map_some,
          Option.getD_some, chOrc_getD_eq prims O R (bmsg R m) H (j, v)]
    simp only [keepBit, hother, hmu, decide_true, Bool.true_and, decide_eq_true_eq]
    have ht0 : (R.1[(⟨i, hi⟩ : Fin R.1.length)]).2.2 = sk.t0 := by
      simp only [Fin.getElem_fin]
      rw [hRi]
      rfl
    rw [ht0]
    rfl

omit [Inhabited prims.Hint] in
/-- **Without distinct message representatives no attempt is kept.** -/
theorem att_eq_none_of_not_nodup {sk : SecretKey p} {R : KeyRing (PubKey p prims) N} {i : ℕ}
    (hi : i < R.1.length) {m : RMsg} {H : X → Y}
    (hmu : ¬ ((R.1.map fun x => O.muPt (pubTr prims x, bmsg R m)).map (O.muAns ∘ H)).Nodup)
    (x : src.Rnd × Fin D) :
    (w1Rejection prims src O βmin tol k D enc bmsg).att H sk R i m x = none := by
  unfold Rejection.att
  rcases ((w1Rejection prims src O βmin tol k D enc bmsg).std sk
    ((w1BaseSigner prims O βmin tol enc (ringLoop prims src O βmin k D) bmsg).bmsg R m) x.1).run H
    with _ | σ
  · rfl
  · dsimp only
    have hk : ((w1Rejection prims src O βmin tol k D enc bmsg).keep R i m σ x.2).run H = false := by
      change (w1Keep prims O βmin D enc bmsg R i m σ x.2).run H = false
      rw [run_w1Keep prims O βmin D enc bmsg R i hi m σ x.2 H, keepBit, decide_eq_false hmu,
        Bool.false_and]
    rw [hk]
    rfl

omit [Inhabited prims.Hint] in
/-- **The base signer of the ring publishing `w₁` is the rejection form `w1Rejection` with `k`
attempts on honest keys** (`Signature.IsRejectionOn`, the hypothesis of the lifting lemma), the
coins read as `k` pairs of a nonce and a keep coin (`w1CoinEquiv`), given the signing and
verification laws, an encoding `enc` coherent with `bucketsOf` and `‖s₂‖∞ ≤ η` for every honest
key (the hypotheses of `correctWithin_w1BaseSigner`). -/
theorem isRejectionOn_w1Base (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta) :
    IsRejectionOn (w1BaseSigner prims O βmin tol enc (ringLoop prims src O βmin k D) bmsg)
      (w1Rejection prims src O βmin tol k D enc bmsg) k (w1CoinEquiv src k D) := by
  intro H kc R hmem m c
  have hi := List.idxOf_lt_length_of_mem hmem
  have hRi := List.getElem_idxOf hi
  rw [Rejection.run_rejectSign]
  have hmd : (muDistinctProg prims O R (bmsg R m)).run H =
      decide ((R.1.map fun x => O.muPt (pubTr prims x, bmsg R m)).map (O.muAns ∘ H)).Nodup := by
    simp only [muDistinctProg, OracleProg.run_mapOutput, OracleProg.run_queryAll, List.map_map]
    rfl
  simp only [w1BaseSigner, ringLoop, Signature.BaseScheme.pk, Signature.BaseScheme.sk,
    OracleProg.run_bind, hmd]
  change _ = if (ringCheckProg prims O βmin tol R).run H then _ else _
  rcases (ringCheckProg prims O βmin tol R).run H with _ | _
  · simp
  · by_cases hnd : ((R.1.map fun x => O.muPt (pubTr prims x, bmsg R m)).map (O.muAns ∘ H)).Nodup
    · simp only [hnd, decide_true, and_self, ite_true]
      erw [run_ringLoopProg prims src O βmin k D _ R _ (bmsg R m) c H, dif_pos hi]
      unfold loopOut
      rw [List.ofFn_eq_map, List.findSome?_map]
      congr 1
      funext c'
      exact callOut_eq_att prims src O βmin tol k D enc bmsg h_laws hv henc (hs2 kc) hi hRi m H hnd
        (c.1 c') (c.2 c')
    · simp only [hnd, decide_false, and_false, ite_true, Bool.false_eq_true, ite_false,
        OracleProg.run_pure]
      exact (List.findSome?_eq_none_iff.2 fun x _ =>
        att_eq_none_of_not_nodup prims src O βmin tol k D enc bmsg hi hnd x).symm

end Form

end GordieHowe.Ring.MLDSAW1
