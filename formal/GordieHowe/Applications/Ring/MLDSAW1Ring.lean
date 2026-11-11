-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.BaseSigners
public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1Hedged
public import GordieHowe.Model.Signature.Properties

@[expose] public section

/-!
# The ML-DSA ring signature publishing `w₁`: the scheme

The ring loop of the ML-DSA ring publishing `w₁` (`GordieHowe/Applications/Ring/PublicW1/README.md`,
steps 2–3 of the construction) as a bounded classical oracle program (`W1Loop`), and the ring
signature `ofBase (w1BaseSigner …) PS adm` at ML-DSA-44, ML-DSA-65 and ML-DSA-87.

The masks come from a `MaskSource` (`Applications/MLDSA/Signing/Hedged.lean`): the hedged source
`MaskSource.hedged M` reads the mask oracle `M`, and the fresh source `MaskSource.fresh M`, the
counterpart of the hedged source for reprogramming at hidden salts, reads a mask function drawn
with the signing coins. The ordinary signer is `stdProg` of the same file.

- `callOut`: **one call of the base signer, then the flattening coin**, as a function: the first
  of the `T` masks whose attempt passes the checks of FIPS 204 Algorithm 7 against the members'
  commitment hashes `hc`, kept when the coin `u ∈ Fin D` is below `D` times the flattening weight
  `min(1, β_min / aw_i) · ∏_{j ≠ i} min(1, aw_j / β_min)` (`flattenCoin`, `otherWeight`): a
  uniform coin on `Fin D` in place of the real-valued coin of `PMF.weightedAttemptMasks`, within
  `1 / D` of it (`PMF.tvDist_finCoin_le`, `MLDSAW1IdealDist.lean`). `callOut_congr`: it reads `hc`
  only at the members' points of the `T` masks' commitments.
- `loopOut`: **`k` calls**, the first kept signature, `none` when every call rejects.
- `hashesOf`, `callProg`, `ringLoopProg`, `run_callProg`, `chOrc_getD_eq`, `run_ringLoopProg`: the
  same as classical oracle programs: the members' message representatives `µ_j` (one query per
  member), then per call the `T` masks and the members' commitment hashes at their commitments
  (one query per mask and member). `callProg_queries`, `ringLoopProg_queries`: at most
  `T · qr + T · N` queries per call and `N + k · (T · qr + T · N)` in all.
- `exists_of_callOut_eq_some`, `ringVerify_of_run_ringLoopProg`, `correctWithin_w1BaseSigner`,
  `correctWithin_w1ConcreteBase`: **correctness**: every signature of the loop is an accepted
  attempt and verifies at its recomputed commitment, so the base signer has correctness error `0`
  for every mask source (`BaseSigner.CorrectWithin`), and at the concrete primitives with no
  hypothesis beyond an approved parameter set.
- `exists_index_of_callOut_eq_some`, `exists_index_of_loopOut_eq_some`: every signature of one
  call and of the loop is the attempt output of one of the masks read.
- `ringCoins Rnd k D`: the ring loop's coins; `ringCoins.mk`, `ringCoins.nonces`, `ringCoins.idx`:
  built from and read as the per-call randomness and keep coins.
- `ringLoop src O βmin k D`: the ring loop as a `W1Loop` (`T` attempts per call); `hedgedLoop`,
  `freshLoop`: at the hedged and the fresh source.
- `w1Base p prims enc O M βmin tol k D bmsg`: the base signer `w1BaseSigner` with the hedged loop;
  `w1Scheme p prims enc O M βmin tol k D bmsg PS adm`: **the ring signature**
  `ofBase (w1Base …) PS adm` with the proof system `PS` a parameter (no compiled ring program for
  this relation exists in the library).
- `w1ConcreteBase p`, `w1Concrete p`: the same at the vendored FIPS 204 primitives with the FIPS 204
  `ExpandS` (`concretePrimitivesKeyGen`), the concrete NTT and the concrete encoding of commitments
  (`concreteEnc`); `w1Scheme44`, `w1Scheme65`, `w1Scheme87`: **the scheme constants** at ML-DSA-44,
  ML-DSA-65 and ML-DSA-87.

## Deliberate differences from the README construction

1. **At most `k` calls.** The README's signer repeats step 2 until a call keeps; here it makes at
   most `k` calls of ML-DSA.Sign and refuses (`none`) when all of them reject, so that signing is a
   program with a bounded number of queries (`RingScheme.sign_queries`).
2. **A finite keep coin.** The flattening coin keeps with a real probability `w`; here a uniform
   `u ∈ Fin D` keeps when `u < D · w`, within `1 / D` of keeping with probability `w` for `w ≤ 1`
   (`PMF.tvDist_finCoin_le`), since the signing coins of a `RingScheme` are uniform on a finite
   type.
3. **The signer queries every member's commitment hash at every mask** of a call (the README reads
   the members' hashes only for the first accepted mask); `callOut` reads the hashes only at the
   masks' commitments (`callOut_congr`).
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature
open scoped ENNReal

variable {X Y : Type}

variable {p : Params} {T : ℕ} {Msg : Type}

/-! ### One call and the loop, as functions -/

section Loop

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps] {N reps : ℕ}

/-- **One call of the base signer, then the flattening coin**: the first of the masks `ys` whose
attempt passes the checks of FIPS 204 Algorithm 7 at the signer's commitment hash
`hc (i, w₁)` (`attemptAccept`), kept with the coin `u ∈ Fin D` when `u < D · w` for the flattening
weight `w = flattenCoin (w₁, c̃_i) · otherWeight` of the ring's member weights against `hc`;
`none` when no mask passes or the coin rejects. The weights are rational, compared in `ℚ≥0`. -/
def callOut (βmin : ℚ≥0) (D : ℕ) (sk : SecretKey p)
    (R : KeyRing (PubKey p prims) N) (i : Fin R.1.length)
    (hc : Fin R.1.length × BucketVec p → CommitHashBytes p) (ys : Fin T → MaskBox p) (u : Fin D) :
    Option (FIPSSignature p prims) :=
  match (List.finRange T).find? (fun t => attemptAccept prims sk (prims.expandA sk.rho) (ys t)
      (hc (i, realBuckets (prims.expandA sk.rho) (ys t)))) with
  | none => none
  | some t =>
    if ((u : ℕ) : ℚ≥0) < D * (flattenCoin prims sk (Cutoff.const βmin) (realBuckets (prims.expandA
        sk.rho) (ys t),
        hc (i, realBuckets (prims.expandA sk.rho) (ys t))) *
        (ringWeights prims βmin (ringT0s prims R.1)).otherWeight i hc
          (realBuckets (prims.expandA sk.rho) (ys t))) then
      some (attemptOutput prims sk (prims.expandA sk.rho)
        (ys t, hc (i, realBuckets (prims.expandA sk.rho) (ys t))))
    else none

/-- **One call reads the commitment hashes only at the masks' commitments**: two hash functions
agreeing at every member's point of every mask's commitment give the same output. -/
theorem callOut_congr (βmin : ℚ≥0) (D : ℕ) (sk : SecretKey p) (R : KeyRing (PubKey p prims) N)
    (i : Fin R.1.length) {hc hc' : Fin R.1.length × BucketVec p → CommitHashBytes p}
    (ys : Fin T → MaskBox p) (u : Fin D)
    (h : ∀ t j, hc (j, realBuckets (prims.expandA sk.rho) (ys t)) =
      hc' (j, realBuckets (prims.expandA sk.rho) (ys t))) :
    callOut prims βmin D sk R i hc ys u = callOut prims βmin D sk R i hc' ys u := by
  have hfind : (fun t => attemptAccept prims sk (prims.expandA sk.rho) (ys t)
      (hc (i, realBuckets (prims.expandA sk.rho) (ys t)))) =
      (fun t => attemptAccept prims sk (prims.expandA sk.rho) (ys t)
      (hc' (i, realBuckets (prims.expandA sk.rho) (ys t)))) := by
    funext t
    rw [h t i]
  have hw : ∀ t, (ringWeights prims βmin (ringT0s prims R.1)).otherWeight i hc
      (realBuckets (prims.expandA sk.rho) (ys t)) =
      (ringWeights prims βmin (ringT0s prims R.1)).otherWeight i hc'
      (realBuckets (prims.expandA sk.rho) (ys t)) := fun t =>
    Finset.prod_congr rfl fun j _ => by rw [h t j]
  unfold callOut
  rw [hfind]
  rcases (List.finRange T).find? _ with _ | t
  · rfl
  · simp only [h t i, hw t]

/-- **`k` calls of the base signer with the flattening coin**: the masks `Z c` and the coin
`uv c` of call `c`, the first kept signature; `none` when every call rejects. -/
def loopOut (βmin : ℚ≥0) {k D : ℕ} (sk : SecretKey p)
    (R : KeyRing (PubKey p prims) N) (i : Fin R.1.length)
    (hc : Fin R.1.length × BucketVec p → CommitHashBytes p) (Z : Fin k → Fin T → MaskBox p)
    (uv : Fin k → Fin D) : Option (FIPSSignature p prims) :=
  (List.finRange k).findSome? fun c => callOut prims βmin D sk R i hc (Z c) (uv c)

/-! ### The loop as a classical oracle program -/

variable [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] [Nonempty (MaskBox p)]

/-- **The members' commitment hashes from the queried values**: at a commitment of one of the
masks `ys`, the value `cs (t, j)` queried for the first such mask `t` and member `j`; a default
elsewhere. -/
def hashesOf (ys : Fin T → MaskBox p) (sk : SecretKey p) {n : ℕ}
    (cs : Fin T × Fin n → CommitHashBytes p) (x : Fin n × BucketVec p) : CommitHashBytes p :=
  match (List.finRange T).find? (fun t => decide (realBuckets (prims.expandA sk.rho) (ys t) = x.2))
  with
  | some t => cs (t, x.1)
  | none => default

/-- **One call as a classical oracle program** from the members' message representatives `mus`:
the `T` masks of the nonce (or other randomness) `r` at the points `(κ, (K, (tr, m)))`, then the
commitment hash `H(µ_j, w₁)` of every member `j` at every mask's commitment `w₁`, then `callOut`
on the hashes read (`hashesOf`). -/
def callProg (src : MaskSource X Y p T Msg) (O : W1Oracles X Y p prims Msg N reps)
    (βmin : ℚ≥0) (D : ℕ) (sk : SecretKey p) (R : KeyRing (PubKey p prims) N)
    (i : Fin R.1.length) (m : Msg) (mus : List (Bytes 64)) (r : src.Rnd) (u : Fin D) :
    OracleProg X Y (Option (FIPSSignature p prims)) :=
  (OracleProg.tabulate (fun _ => maskBoxPoint p) (List.finRange T) fun t =>
      src.read r (t, (sk.key, (sk.tr, m)))).bind fun ys =>
    (OracleProg.tabulate (fun _ => default) (List.finRange T ×ˢ List.finRange R.1.length)
        fun tj => .query (O.chPt (mus.getD tj.2 default,
          realBuckets (prims.expandA sk.rho) (ys tj.1))) fun y => .pure (O.chAns y)).mapOutput
      fun cs => callOut prims βmin D sk R i (hashesOf prims ys sk cs) ys u

/-- **The ring loop as a classical oracle program**: on a position `i` of the ring `R`, the
members' message representatives `µ_j = H_µ(tr_j, m)` (one query per member), then at most `k` calls
(`callProg`) with the randomness `c.1` and the coins `c.2`, stopping at the first kept signature;
`none` when `i` is not a position of `R` or every call rejects. -/
def ringLoopProg (src : MaskSource X Y p T Msg) (O : W1Oracles X Y p prims Msg N reps)
    (βmin : ℚ≥0) (k D : ℕ) (sk : SecretKey p) (R : KeyRing (PubKey p prims) N) (i : ℕ) (m : Msg)
    (c : (Fin k → src.Rnd) × (Fin k → Fin D)) : OracleProg X Y (Option (FIPSSignature p prims)) :=
  if hi : i < R.1.length then
    (OracleProg.queryAll (R.1.map fun x => O.muPt (pubTr prims x, m))).bind fun ans =>
      OracleProg.iterate (fun c' s => match s with
        | some σ => .pure (some σ)
        | none => if hc : c' < k then
            callProg prims src O βmin D sk R ⟨i, hi⟩ m (ans.map O.muAns) (c.1 ⟨c', hc⟩)
              (c.2 ⟨c', hc⟩)
          else .pure none) k none
  else .pure none

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] in
/-- One call makes at most `T · qr + T · N` queries. -/
theorem callProg_queries (src : MaskSource X Y p T Msg) (O : W1Oracles X Y p prims Msg N reps)
    (βmin : ℚ≥0) (D : ℕ) (sk : SecretKey p) (R : KeyRing (PubKey p prims) N)
    (i : Fin R.1.length) (m : Msg) (mus : List (Bytes 64)) (r : src.Rnd) (u : Fin D) :
    (callProg prims src O βmin D sk R i m mus r u).QueriesLE (T * src.qr + T * N) := by
  have h₁ : (OracleProg.tabulate (fun _ => maskBoxPoint p) (List.finRange T)
      fun t => src.read r (t, (sk.key, (sk.tr, m)))).QueriesLE (T * src.qr) := by
    simpa using OracleProg.QueriesLE.tabulate (fun _ => maskBoxPoint p)
      (List.finRange T) fun t => src.read_queries r (t, (sk.key, (sk.tr, m)))
  refine h₁.bind fun ys => ?_
  have h₂ := OracleProg.QueriesLE.tabulate (fun _ => (default : CommitHashBytes p))
    (List.finRange T ×ˢ List.finRange R.1.length) (q := 1)
    (P := fun tj => .query (O.chPt (mus.getD tj.2 default,
      realBuckets (prims.expandA sk.rho) (ys tj.1))) fun y => .pure (O.chAns y))
    fun tj h => by simp [OracleProg.trace_query, OracleProg.trace_pure]
  refine (h₂.mapOutput _).mono ?_
  simp only [List.length_product, List.length_finRange, mul_one]
  exact Nat.mul_le_mul_left _ R.2

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] in
/-- **The ring loop makes at most `N + k · (T · qr + T · N)` queries.** -/
theorem ringLoopProg_queries (src : MaskSource X Y p T Msg)
    (O : W1Oracles X Y p prims Msg N reps) (βmin : ℚ≥0) (k D : ℕ) (sk : SecretKey p)
    (R : KeyRing (PubKey p prims) N) (i : ℕ) (m : Msg) (c : (Fin k → src.Rnd) × (Fin k → Fin D)) :
    (ringLoopProg prims src O βmin k D sk R i m c).QueriesLE (N + k * (T * src.qr + T * N)) := by
  unfold ringLoopProg
  split_ifs with hi
  · refine ((OracleProg.QueriesLE.queryAll _).mono ?_).bind fun ans =>
      OracleProg.QueriesLE.iterate (fun c' s => ?_) k none
    · simpa using R.2
    · rcases s with _ | σ
      · dsimp only
        split_ifs
        · exact callProg_queries prims src O βmin D sk R _ m _ _ _
        · exact OracleProg.QueriesLE.pure _ _
      · exact OracleProg.QueriesLE.pure _ _
  · exact OracleProg.QueriesLE.pure _ _

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] in
/-- **One call computes `callOut`** at the members' commitment hashes `H(µ_j, w₁)` with the given
message representatives `mus` and at the masks read from the randomness. -/
theorem run_callProg (src : MaskSource X Y p T Msg) (O : W1Oracles X Y p prims Msg N reps)
    (βmin : ℚ≥0) (D : ℕ) (sk : SecretKey p) (R : KeyRing (PubKey p prims) N)
    (i : Fin R.1.length) (m : Msg) (mus : List (Bytes 64)) (r : src.Rnd) (u : Fin D)
    (H : X → Y) :
    (callProg prims src O βmin D sk R i m mus r u).run H =
      callOut prims βmin D sk R i (fun x => O.chOrc H (mus.getD x.1 default, x.2))
        (fun t => (src.read r (t, (sk.key, (sk.tr, m)))).run H) u := by
  simp only [callProg, OracleProg.run_bind, OracleProg.run_mapOutput, OracleProg.run_tabulate,
    OracleProg.run_query, OracleProg.run_pure, List.mem_finRange, List.mem_product, and_self,
    ite_true]
  refine callOut_congr prims βmin D sk R i _ u fun t j => ?_
  set v : Fin T → BucketVec p := fun t => realBuckets (prims.expandA sk.rho)
    ((src.read r (t, (sk.key, (sk.tr, m)))).run H)
  obtain ⟨t₀, ht₀, hv⟩ : ∃ t₀, (List.finRange T).find? (fun t' => decide (v t' = v t)) = some t₀ ∧
      v t₀ = v t := by
    cases hf : (List.finRange T).find? (fun t' => decide (v t' = v t)) with
    | none => exact absurd (List.find?_eq_none.1 hf t (List.mem_finRange t)) (by simp)
    | some t₀ => exact ⟨t₀, rfl, by simpa using List.find?_some hf⟩
  simp only [hashesOf, List.mem_product, List.mem_finRange, and_self, ite_true]
  change (match (List.finRange T).find? (fun t' => decide (v t' = v t)) with
    | some t' => O.chAns (H (O.chPt (mus.getD j default, v t')))
    | none => default) = O.chOrc H (mus.getD j default, v t)
  rw [ht₀]
  dsimp only
  rw [hv]
  rfl

omit [NeZero (bucketCount p)] nttOps [Fintype prims.Power2High] [DecidableEq prims.Power2High]
  [Fintype prims.Hint] [DecidableEq prims.Hint] [Inhabited prims.Hint] [Nonempty (MaskBox p)] in
/-- The message representatives read by the loop are `H_µ(tr_j, m)`, so the commitment hashes it
reads are the members' points of the commitment hash `H((tr_j, m), w₁)`. -/
theorem chOrc_getD_eq (O : W1Oracles X Y p prims Msg N reps) (R : KeyRing (PubKey p prims) N)
    (m : Msg) (H : X → Y) (x : Fin R.1.length × BucketVec p) :
    O.chOrc H ((((R.1.map fun y => O.muPt (pubTr prims y, m)).map H).map O.muAns).getD x.1 default,
      x.2) = PMF.ringOf (ringPts prims R.1 m) (O.hOrc H) x := by
  simp only [List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem x.1.2, Option.map_some, Option.getD_some, PMF.ringOf, ringPts,
    MLDSAOracles.hOrc, schemeOrc, MLDSAOracles.muOrc, Function.comp_apply, List.get_eq_getElem]

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] in
/-- **The ring loop computes `loopOut`** at the members' points of the commitment hash read from the
oracle (`ringOf (ringPts R m) (O.hOrc H)`) and at the masks read from the randomness of each
call. -/
theorem run_ringLoopProg (src : MaskSource X Y p T Msg) (O : W1Oracles X Y p prims Msg N reps)
    (βmin : ℚ≥0) (k D : ℕ) (sk : SecretKey p) (R : KeyRing (PubKey p prims) N) (i : ℕ) (m : Msg)
    (c : (Fin k → src.Rnd) × (Fin k → Fin D)) (H : X → Y) :
    (ringLoopProg prims src O βmin k D sk R i m c).run H =
      if hi : i < R.1.length then
        loopOut prims βmin sk R ⟨i, hi⟩ (PMF.ringOf (ringPts prims R.1 m) (O.hOrc H))
          (fun c' t => (src.read (c.1 c') (t, (sk.key, (sk.tr, m)))).run H) c.2
      else none := by
  unfold ringLoopProg
  split_ifs with hi
  · simp only [OracleProg.run_bind, OracleProg.run_queryAll]
    set f : Fin k → Option (FIPSSignature p prims) := fun c' =>
      callOut prims βmin D sk R ⟨i, hi⟩ (PMF.ringOf (ringPts prims R.1 m) (O.hOrc H))
        ((fun c' t => (src.read (c.1 c') (t, (sk.key, (sk.tr, m)))).run H) c') (c.2 c')
    have hstep : ∀ m' : ℕ, (OracleProg.iterate (fun c' s => match s with
        | some σ => .pure (some σ)
        | none => if hc : c' < k then
            callProg prims src O βmin D sk R ⟨i, hi⟩ m
              ((((R.1.map fun x => O.muPt (pubTr prims x, m)).map H).map O.muAns)) (c.1 ⟨c', hc⟩)
              (c.2 ⟨c', hc⟩)
          else .pure none) m' none).run H =
        (List.range m').findSome? fun c' => if hc : c' < k then f ⟨c', hc⟩ else none := by
      intro m'
      induction m' with
      | zero => rfl
      | succ m' ih =>
        rw [OracleProg.run_iterate_succ, ih, List.range_succ, List.findSome?_append]
        rcases (List.range m').findSome? fun c' => if hc : c' < k then f ⟨c', hc⟩ else none with
          _ | σ
        · simp only [Option.none_or, List.findSome?_singleton]
          split_ifs with hc
          · rw [run_callProg]
            simp only [f]
            congr 1
            funext x
            exact chOrc_getD_eq prims O R m H x
          · rfl
        · rfl
    have hmap : (List.finRange k).map Fin.val = List.range k :=
      List.ext_getElem (by simp) fun n h₁ h₂ => by simp
    rw [hstep k, loopOut, ← hmap, List.findSome?_map]
    congr 1
    funext c'
    simp only [Function.comp_apply, Fin.is_lt, dite_true, f]
  · rfl

/-! ### The ordinary signer, the loop and the scheme -/

variable [Fintype Msg] [DecidableEq Msg]

/-- **The coins of the ring loop** with per-call randomness `Rnd`, at most `k` calls and keep
coins on `Fin D`: the randomness and the keep coin of each call. The hedged and the fresh signer
differ only in `Rnd`. A named type, so its instances are found at the name. -/
def ringCoins (Rnd : Type) (k D : ℕ) : Type := (Fin k → Rnd) × (Fin k → Fin D)

/-- The ring loop's coins with the per-call randomness `r` and the keep coins `u`. -/
def ringCoins.mk {Rnd : Type} {k D : ℕ} (r : Fin k → Rnd) (u : Fin k → Fin D) : ringCoins Rnd k D :=
  (r, u)

/-- The per-call randomness of the ring loop's coins. -/
def ringCoins.nonces {Rnd : Type} {k D : ℕ} (c : ringCoins Rnd k D) : Fin k → Rnd :=
  Prod.fst (α := Fin k → Rnd) (β := Fin k → Fin D) c

/-- The keep coin of each call of the ring loop's coins. -/
def ringCoins.idx {Rnd : Type} {k D : ℕ} (c : ringCoins Rnd k D) : Fin k → Fin D :=
  Prod.snd (α := Fin k → Rnd) (β := Fin k → Fin D) c

omit nttOps in
@[simp]
theorem ringCoins.nonces_mk {Rnd : Type} {k D : ℕ} (r : Fin k → Rnd) (u : Fin k → Fin D) :
    (ringCoins.mk r u).nonces = r :=
  rfl

omit nttOps in
@[simp]
theorem ringCoins.idx_mk {Rnd : Type} {k D : ℕ} (r : Fin k → Rnd) (u : Fin k → Fin D) :
    (ringCoins.mk r u).idx = u :=
  rfl

omit nttOps in
@[simp]
theorem ringCoins.mk_nonces_idx {Rnd : Type} {k D : ℕ} (c : ringCoins Rnd k D) :
    ringCoins.mk c.nonces c.idx = c :=
  rfl

instance {Rnd : Type} [Fintype Rnd] [DecidableEq Rnd] {k D : ℕ} : Fintype (ringCoins Rnd k D) :=
  inferInstanceAs (Fintype ((Fin k → Rnd) × (Fin k → Fin D)))

instance {Rnd : Type} [DecidableEq Rnd] {k D : ℕ} : DecidableEq (ringCoins Rnd k D) :=
  inferInstanceAs (DecidableEq ((Fin k → Rnd) × (Fin k → Fin D)))

instance {Rnd : Type} [Nonempty Rnd] {k D : ℕ} [NeZero D] : Nonempty (ringCoins Rnd k D) :=
  inferInstanceAs (Nonempty ((Fin k → Rnd) × (Fin k → Fin D)))

/-- **The ring loop of the ML-DSA ring publishing `w₁`** with the mask source `src`, the oracles
`O`, the cut-off `β_min`, at most `k` calls of `T` attempts each and keep coins on `Fin D`: coins
the per-call randomness and keep coins, the loop `ringLoopProg`, the ordinary signer `stdProg`, and
the query bound `N + k · (T · qr + T · N) + (1 + T · qr + T)`. -/
def ringLoop (src : MaskSource X Y p T Msg) (O : W1Oracles X Y p prims Msg N reps)
    (βmin : ℚ≥0) (k D : ℕ) [NeZero D] : W1Loop X Y p prims Msg N (ringCoins src.Rnd k D) where
  q := N + k * (T * src.qr + T * N) + (1 + T * src.qr + T)
  sign sk R i m c := ringLoopProg prims src O βmin k D sk R i m c
  sign_queries sk R i m c :=
    (ringLoopProg_queries prims src O βmin k D sk R i m c).mono (Nat.le_add_right _ _)
  std sk m c := stdProg prims src O.toMLDSAOracles k sk m c.1
  std_queries sk m c :=
    (stdProg_queries prims src O.toMLDSAOracles k sk m c.1).mono (Nat.le_add_left _ _)

/-- The ring loop signs with `ringLoopProg`. -/
theorem ringLoop_sign (src : MaskSource X Y p T Msg) (O : W1Oracles X Y p prims Msg N reps)
    (βmin : ℚ≥0) (k D : ℕ) [NeZero D] (sk : SecretKey p) (R : KeyRing (PubKey p prims) N) (i : ℕ)
    (m : Msg) (c : ringCoins src.Rnd k D) :
    (ringLoop prims src O βmin k D).sign sk R i m c = ringLoopProg prims src O βmin k D sk R i m c := by
  unfold ringLoop; rfl

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] [Fintype Msg] [DecidableEq Msg] in
/-- The ordinary signer of the ring loop is `stdProg` at the nonces of the coins. -/
theorem ringLoop_std (src : MaskSource X Y p T Msg) (O : W1Oracles X Y p prims Msg N reps)
    (βmin : ℚ≥0) (k D : ℕ) [NeZero D] (sk : SecretKey p) (m : Msg) (c : ringCoins src.Rnd k D) :
    (ringLoop prims src O βmin k D).std sk m c =
      stdProg prims src O.toMLDSAOracles k sk m c.nonces := by
  unfold ringLoop; rfl

/-- The query bound of the ring loop. -/
theorem ringLoop_q (src : MaskSource X Y p T Msg) (O : W1Oracles X Y p prims Msg N reps)
    (βmin : ℚ≥0) (k D : ℕ) [NeZero D] :
    (ringLoop prims src O βmin k D).q = N + k * (T * src.qr + T * N) + (1 + T * src.qr + T) := by
  unfold ringLoop; rfl

/-- **The hedged ring loop**: the masks from FIPS 204 hedged derivation at a fresh 32-byte nonce per
call (`MaskSource.hedged`). -/
abbrev hedgedLoop (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg)
    (βmin : ℚ≥0) (k D : ℕ) [NeZero D] : W1Loop X Y p prims Msg N (ringCoins (Bytes 32) k D) :=
  ringLoop prims (MaskSource.hedged M) O βmin k D

/-- The coins of the hedged ring loop are nonempty, as a named instance: applied to variables only,
it is never abstracted into an auxiliary lemma inside a definition, so the same proof term appears
in definitions and statements. -/
instance instNonemptyHedgedCoins {k D : ℕ} [NeZero D] : Nonempty (ringCoins (Bytes 32) k D) :=
  inferInstance

/-- The coins of the fresh ring loop are nonempty, as a named instance (as
`instNonemptyHedgedCoins`). -/
instance instNonemptyFreshCoins [Nonempty Y] {k D : ℕ} [NeZero D] :
    Nonempty (ringCoins (MaskFn T Msg Y) k D) :=
  inferInstance

/-- **The ring loop with fresh masks**: the masks from a function drawn with the coins per call
(`MaskSource.fresh`), the fresh counterpart of `hedgedLoop`. -/
abbrev freshLoop (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg)
    (βmin : ℚ≥0) (k D : ℕ) [NeZero D] : W1Loop X Y p prims Msg N (ringCoins (MaskFn T Msg Y) k D) :=
  ringLoop prims (MaskSource.fresh M) O βmin k D

/-- The hedged loop signs with `ringLoopProg` at the hedged source (`ringLoop_sign`). -/
theorem hedgedLoop_sign (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg)
    (βmin : ℚ≥0) (k D : ℕ) [NeZero D] (sk : SecretKey p) (R : KeyRing (PubKey p prims) N) (i : ℕ)
    (m : Msg) (c : ringCoins (Bytes 32) k D) :
    (hedgedLoop prims O M βmin k D).sign sk R i m c =
      ringLoopProg prims (MaskSource.hedged M) O βmin k D sk R i m c :=
  by delta hedgedLoop ringLoop; rfl

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] [Fintype Msg] [DecidableEq Msg] in
/-- The hedged loop's ordinary signer is `stdProg` at the hedged source (`ringLoop_std`). -/
theorem hedgedLoop_std (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg)
    (βmin : ℚ≥0) (k D : ℕ) [NeZero D] (sk : SecretKey p) (m : Msg) (c : ringCoins (Bytes 32) k D) :
    (hedgedLoop prims O M βmin k D).std sk m c =
      stdProg prims (MaskSource.hedged M) O.toMLDSAOracles k sk m c.nonces :=
  ringLoop_std prims (MaskSource.hedged M) O βmin k D sk m c

omit [Fintype Msg] [DecidableEq Msg] in
/-- The fresh loop signs with `ringLoopProg` at the fresh source (`ringLoop_sign`). -/
theorem freshLoop_sign (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg)
    (βmin : ℚ≥0) (k D : ℕ) [NeZero D] (sk : SecretKey p) (R : KeyRing (PubKey p prims) N) (i : ℕ)
    (m : Msg) (c : ringCoins (MaskFn T Msg Y) k D) :
    (freshLoop prims O M βmin k D).sign sk R i m c =
      ringLoopProg prims (MaskSource.fresh M) O βmin k D sk R i m c :=
  by delta freshLoop ringLoop; rfl

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] [Fintype Msg] [DecidableEq Msg] in
/-- The fresh loop's ordinary signer is `stdProg` at the fresh source (`ringLoop_std`). -/
theorem freshLoop_std (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg)
    (βmin : ℚ≥0) (k D : ℕ) [NeZero D] (sk : SecretKey p) (m : Msg)
    (c : ringCoins (MaskFn T Msg Y) k D) :
    (freshLoop prims O M βmin k D).std sk m c =
      stdProg prims (MaskSource.fresh M) O.toMLDSAOracles k sk m c.nonces :=
  ringLoop_std prims (MaskSource.fresh M) O βmin k D sk m c

variable (p) in
/-- **The base signer of the ML-DSA ring publishing `w₁` with hedged signing** at the parameter set
`p`, the primitives `prims` and the encoding `enc` of commitments: `w1BaseSigner` with the hedged
ring loop (`hedgedLoop`), the check's cut-off `β_min` and tolerance `tol`, at most `k` calls of
`T` attempts, keep coins on `Fin D`, and the base message `bmsg`. -/
abbrev w1Base (enc : Vector prims.High p.k → BucketVec p)
    (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg) (βmin : ℚ≥0) (tol k D : ℕ)
    [NeZero D] {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
    (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg) :
    BaseSigner X Y N (w1BaseT prims Msg RMsg (ringCoins (Bytes 32) k D)) :=
  w1BaseSigner prims O βmin tol enc (hedgedLoop prims O M βmin k D) bmsg

variable (p) in
/-- **The ML-DSA ring signature publishing `w₁`**: `ofBase (w1Base …) PS adm`, the
public value `w₁` with a proof of the ring relation by the proof system `PS` (a parameter) on the
supported rings `adm`. -/
abbrev w1Scheme (enc : Vector prims.High p.k → BucketVec p)
    (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg) (βmin : ℚ≥0) (tol k D : ℕ)
    [NeZero D] {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
    (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg)
    {TPS : PSTypes} (PS : ProofSystem X Y (RingSignature.RingStmt (w1Base p prims enc O M βmin tol k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS)
    (adm : KeyRing (PubKey p prims) N → Prop) [DecidablePred adm] :
    RingScheme X Y N (ofBaseT (w1BaseT prims Msg RMsg (ringCoins (Bytes 32) k D)) TPS) :=
  RingSignature.ofBase (w1Base p prims enc O M βmin tol k D bmsg) PS adm

/-! ### Correctness -/

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] [Nonempty (MaskBox p)] in
/-- **Every signature of one call is an accepted attempt**: `callOut` outputs `σ` only for a mask
`y` whose attempt passes the checks at `c̃ = hc (i, HighBits(Â·y))`, with
`σ = (c̃, y + c·s₁, h)`. -/
theorem exists_of_callOut_eq_some {βmin : ℚ≥0} {D : ℕ} {sk : SecretKey p}
    {R : KeyRing (PubKey p prims) N} {i : Fin R.1.length}
    {hc : Fin R.1.length × BucketVec p → CommitHashBytes p} {ys : Fin T → MaskBox p} {u : Fin D}
    {σ : FIPSSignature p prims} (h : callOut prims βmin D sk R i hc ys u = some σ) :
    ∃ y : MaskBox p, attemptAccept prims sk (prims.expandA sk.rho) y
        (hc (i, realBuckets (prims.expandA sk.rho) y)) = true ∧
      σ = attemptOutput prims sk (prims.expandA sk.rho)
        (y, hc (i, realBuckets (prims.expandA sk.rho) y)) := by
  unfold callOut at h
  split at h
  · exact absurd h (by simp)
  · rename_i t ht
    split_ifs at h
    exact ⟨ys t, by simpa using List.find?_some ht, (Option.some.inj h).symm⟩

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] [Nonempty (MaskBox p)] in
/-- **Every signature of one call is the output of one of its masks**: `callOut` outputs `σ` only
as `attemptOutput (ys t, hc (i, HighBits(Â·ys t)))` for some `t`. -/
theorem exists_index_of_callOut_eq_some {βmin : ℚ≥0} {D : ℕ} {sk : SecretKey p}
    {R : KeyRing (PubKey p prims) N} {i : Fin R.1.length}
    {hc : Fin R.1.length × BucketVec p → CommitHashBytes p} {ys : Fin T → MaskBox p} {u : Fin D}
    {σ : FIPSSignature p prims} (h : callOut prims βmin D sk R i hc ys u = some σ) :
    ∃ t, σ = attemptOutput prims sk (prims.expandA sk.rho)
      (ys t, hc (i, realBuckets (prims.expandA sk.rho) (ys t))) := by
  unfold callOut at h
  split at h
  · exact absurd h (by simp)
  · rename_i t _
    split_ifs at h
    exact ⟨t, (Option.some.inj h).symm⟩

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] [Nonempty (MaskBox p)] in
/-- **Every signature of the loop is the output of one of its masks**: `loopOut` outputs `σ` only
as `attemptOutput (Z c t, hc (i, HighBits(Â·Z c t)))` for some call `c` and mask `t`. -/
theorem exists_index_of_loopOut_eq_some {βmin : ℚ≥0} {k D : ℕ} {sk : SecretKey p}
    {R : KeyRing (PubKey p prims) N} {i : Fin R.1.length}
    {hc : Fin R.1.length × BucketVec p → CommitHashBytes p} {Z : Fin k → Fin T → MaskBox p}
    {uv : Fin k → Fin D} {σ : FIPSSignature p prims}
    (h : loopOut prims βmin sk R i hc Z uv = some σ) :
    ∃ c t, σ = attemptOutput prims sk (prims.expandA sk.rho)
      (Z c t, hc (i, realBuckets (prims.expandA sk.rho) (Z c t))) := by
  obtain ⟨c, -, hc'⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨t, rfl⟩ := exists_index_of_callOut_eq_some prims hc'
  exact ⟨c, t, rfl⟩

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Inhabited prims.Hint] [Fintype Msg] [DecidableEq Msg] in
/-- **The ring loop's signatures verify** for an honest key: for the key of `seed` with
`‖s₂‖∞ ≤ η`, at its position `i` of the ring, every signature the loop outputs at the oracle `H`
is accepted by `ringVerify` against the commitment hash read from the oracle at the recomputed
commitment `w1Of enc pk σ`, given the signing and verification laws and an encoding `enc` coherent
with `bucketsOf`. -/
theorem ringVerify_of_run_ringLoopProg (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    {enc : Vector prims.High p.k → BucketVec p}
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    {seed : Bytes 32} (hs2 : polyVecBounded (keyGen prims seed).2.s2 p.eta)
    (src : MaskSource X Y p T Msg) (O : W1Oracles X Y p prims Msg N reps) (βmin : ℚ≥0)
    (k D : ℕ) {R : KeyRing (PubKey p prims) N} {i : ℕ} (hR : R.1[i]? = some (keyGen prims seed).1)
    (m : Msg) (c : (Fin k → src.Rnd) × (Fin k → Fin D)) (H : X → Y) {σ : FIPSSignature p prims}
    (hσ : (ringLoopProg prims src O βmin k D (keyGen prims seed).2 R i m c).run H = some σ) :
    ringVerify prims (O.hOrc H) enc (pubPk prims (keyGen prims seed).1) m
      (w1Of prims enc (keyGen prims seed).1 σ) σ = true := by
  obtain ⟨hi, hRi⟩ := List.getElem?_eq_some_iff.1 hR
  simp only [run_ringLoopProg, hi, ↓reduceDIte, loopOut] at hσ
  obtain ⟨c', -, hc'⟩ := List.exists_of_findSome?_eq_some hσ
  obtain ⟨y, hacc, rfl⟩ := exists_of_callOut_eq_some prims hc'
  have hpt : PMF.ringOf (ringPts prims R.1 m) (O.hOrc H)
      (⟨i, hi⟩, realBuckets (prims.expandA (keyGen prims seed).2.rho) y) =
      O.hOrc H ((prims.hashPublicKey (keyGenFromSeed p prims seed).1.rho
        (keyGenFromSeed p prims seed).1.t1, m),
        realBuckets (prims.expandA (keyGenFromSeed p prims seed).1.rho) y) := by
    simp only [PMF.ringOf, ringPts, List.get_eq_getElem, hRi, pubTr, keyGen, keyGenFromSeed_rho]
  have hver := ringVerify_attemptOutput prims h_laws hv henc (seed := seed)
    (pk := (keyGenFromSeed p prims seed).1) (sk := (keyGenFromSeed p prims seed).2) rfl hs2
    (O.hOrc H) m y (by
      rw [← hpt]
      simpa only [keyGen, keyGenFromSeed_rho] using hacc)
  rw [hpt]
  have hw : w1Of prims enc (keyGen prims seed).1 (attemptOutput prims (keyGen prims seed).2
      (prims.expandA (keyGen prims seed).2.rho) (y, O.hOrc H ((prims.hashPublicKey
        (keyGenFromSeed p prims seed).1.rho (keyGenFromSeed p prims seed).1.t1, m),
        realBuckets (prims.expandA (keyGenFromSeed p prims seed).1.rho) y))) =
      realBuckets (prims.expandA (keyGenFromSeed p prims seed).1.rho) y := by
    simp only [ringVerify, Bool.and_eq_true, decide_eq_true_eq] at hver
    simpa only [w1Of, keyGen, keyGenFromSeed_rho, pubPk] using hver.1.1.2
  simp only [keyGen, keyGenFromSeed_rho] at hw ⊢
  rw [hw]
  simpa only [pubPk] using hver

omit [Inhabited prims.Hint] in
/-- **The base signer with the ring loop has correctness error `0`** (`BaseSigner.CorrectWithin`):
at every oracle and every honest key at its position of a ring, every signature the signer outputs
verifies, for any mask source, given `‖s₂‖∞ ≤ η` for every honest key, the signing and
verification laws and an encoding `enc` coherent with `bucketsOf`. -/
theorem correctWithin_w1BaseSigner (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    {enc : Vector prims.High p.k → BucketVec p}
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta) (src : MaskSource X Y p T Msg)
    [Fintype src.Rnd] [DecidableEq src.Rnd] [Nonempty src.Rnd]
    (O : W1Oracles X Y p prims Msg N reps) (βmin : ℚ≥0) (tol k D : ℕ) [NeZero D]
    {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
    (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg) :
    (w1BaseSigner prims O βmin tol enc (ringLoop prims src O βmin k D) bmsg).CorrectWithin 0 := by
  intro H kc R i hR m
  refine le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 ?_)
  refine Set.disjoint_left.2 fun c _ hc => ?_
  obtain ⟨σ, hσ, hver⟩ := hc
  simp only [w1BaseSigner, mldsaT0BaseScheme, ringLoop, OracleProg.run_bind] at hσ hver
  split_ifs at hσ with hok
  · have := ringVerify_of_run_ringLoopProg prims h_laws hv henc (hs2 kc) src O βmin k D hR
      (bmsg R m) c H hσ
    simp only [Signature.BaseScheme.pk] at this hver
    rw [this] at hver
    exact Bool.noConfusion hver
  · exact absurd hσ (by simp [OracleProg.run_pure])

end Loop

/-! ### ML-DSA-44, ML-DSA-65 and ML-DSA-87 -/

section Concrete

open _root_.MLDSA.Concrete GordieHowe.MLDSA.Spec

attribute [local instance] concreteNTTRingOps

variable [NeZero (bucketCount p)] [Nonempty (MaskBox p)] {N reps : ℕ} [Fintype Msg]
  [DecidableEq Msg]

variable (p) in
/-- **The base signer at the concrete primitives** of the parameter set `p`: `w1Base` at the
vendored FIPS 204 primitives with the FIPS 204 `ExpandS` (`concretePrimitivesKeyGen`), the concrete
NTT and the concrete encoding of commitments (`concreteEnc`). -/
abbrev w1ConcreteBase (O : W1Oracles X Y p (concretePrimitivesKeyGen p) Msg N reps)
    (M : MaskOracle X Y p T Msg) (βmin : ℚ≥0) (tol k D : ℕ) [NeZero D] {RMsg : Type}
    [Fintype RMsg] [DecidableEq RMsg]
    (bmsg : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → RMsg → Msg) :
    BaseSigner X Y N (w1BaseT (concretePrimitivesKeyGen p) Msg RMsg (ringCoins (Bytes 32) k D)) :=
  w1Base p (concretePrimitivesKeyGen p) (concreteEnc p) O M βmin tol k D bmsg

variable (p) in
/-- **The ML-DSA ring signature publishing `w₁` at the concrete primitives** of the parameter set
`p`: `w1Scheme` at `concretePrimitivesKeyGen p` and `concreteEnc p`. -/
abbrev w1Concrete (O : W1Oracles X Y p (concretePrimitivesKeyGen p) Msg N reps)
    (M : MaskOracle X Y p T Msg) (βmin : ℚ≥0) (tol k D : ℕ) [NeZero D] {RMsg : Type}
    [Fintype RMsg] [DecidableEq RMsg]
    (bmsg : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → RMsg → Msg)
    {TPS : PSTypes} (PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase p O M βmin tol k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))) TPS)
    (adm : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → Prop) [DecidablePred adm] :
    RingScheme X Y N (ofBaseT (w1BaseT (concretePrimitivesKeyGen p) Msg RMsg (ringCoins (Bytes 32) k D)) TPS) :=
  w1Scheme p (concretePrimitivesKeyGen p) (concreteEnc p) O M βmin tol k D bmsg PS adm

/-- **The base signer at the concrete primitives has correctness error `0`** at every approved
parameter set (`correctWithin_w1BaseSigner` with the signing and verification laws of the concrete
primitives, the coherence of `concreteEnc` and `‖s₂‖∞ ≤ η` for every honest key). -/
theorem correctWithin_w1ConcreteBase (hp : p.isApproved)
    (O : W1Oracles X Y p (concretePrimitivesKeyGen p) Msg N reps) (M : MaskOracle X Y p T Msg)
    (βmin : ℚ≥0) (tol k D : ℕ) [NeZero D] {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
    (bmsg : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → RMsg → Msg) :
    (w1ConcreteBase p O M βmin tol k D bmsg).CorrectWithin 0 :=
  correctWithin_w1BaseSigner _ (signingLaws_concreteKeyGen p hp) (verifyLaws_concreteKeyGen hp)
    (concreteEnc_highBitsVec_keyGen hp) (fun seed => keyGenFromSeed_s2_bounded hp seed) _ O βmin
    tol k D bmsg

/-- **The ML-DSA-44 ring signature publishing `w₁`** with hedged signing (`w1Concrete`). -/
abbrev w1Scheme44 :=
  w1Concrete (X := X) (Y := Y) (T := T) (Msg := Msg) (N := N) (reps := reps) _root_.MLDSA.mldsa44

/-- **The ML-DSA-65 ring signature publishing `w₁`** with hedged signing (`w1Concrete`). -/
abbrev w1Scheme65 :=
  w1Concrete (X := X) (Y := Y) (T := T) (Msg := Msg) (N := N) (reps := reps) _root_.MLDSA.mldsa65

/-- **The ML-DSA-87 ring signature publishing `w₁`** with hedged signing (`w1Concrete`). -/
abbrev w1Scheme87 :=
  w1Concrete (X := X) (Y := Y) (T := T) (Msg := Msg) (N := N) (reps := reps) _root_.MLDSA.mldsa87

variable (p) in
/-- **The ML-DSA ring signature publishing `w₁` with ring-binding base messages** at the concrete
primitives of the parameter set `p`: `w1Concrete` at `bmsg := Prod.mk`, so the base message binds
the ring: `(R, m)`. -/
abbrev w1BindConcrete {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
    (O : W1Oracles X Y p (concretePrimitivesKeyGen p)
      (KeyRing (PubKey p (concretePrimitivesKeyGen p)) N × RMsg) N reps)
    (M : MaskOracle X Y p T (KeyRing (PubKey p (concretePrimitivesKeyGen p)) N × RMsg))
    (βmin : ℚ≥0) (tol k D : ℕ) [NeZero D]
    {TPS : PSTypes} (PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase p O M βmin tol k D (RMsg := RMsg) Prod.mk)) (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))) TPS)
    (adm : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → Prop)
    [DecidablePred adm] :
    RingScheme X Y N (ofBaseT (w1BaseT (concretePrimitivesKeyGen p) (KeyRing (PubKey p (concretePrimitivesKeyGen p)) N × RMsg) RMsg (ringCoins (Bytes 32) k D)) TPS) :=
  w1Concrete p O M βmin tol k D (RMsg := RMsg) Prod.mk PS adm

/-- **The ML-DSA-44 ring signature publishing `w₁` with ring-binding base messages**
(`w1BindConcrete`). -/
abbrev w1BindScheme44 {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg] :=
  w1BindConcrete (X := X) (Y := Y) (T := T) (N := N) (reps := reps) (RMsg := RMsg)
    _root_.MLDSA.mldsa44

/-- **The ML-DSA-65 ring signature publishing `w₁` with ring-binding base messages**
(`w1BindConcrete`). -/
abbrev w1BindScheme65 {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg] :=
  w1BindConcrete (X := X) (Y := Y) (T := T) (N := N) (reps := reps) (RMsg := RMsg)
    _root_.MLDSA.mldsa65

/-- **The ML-DSA-87 ring signature publishing `w₁` with ring-binding base messages**
(`w1BindConcrete`). -/
abbrev w1BindScheme87 {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg] :=
  w1BindConcrete (X := X) (Y := Y) (T := T) (N := N) (reps := reps) (RMsg := RMsg)
    _root_.MLDSA.mldsa87

variable (p) in
/-- **The converted ML-DSA ring signature publishing `w₁`** at the concrete primitives of the
parameter set `p`: `w1Concrete` at `bmsg := fun _ m => m`, so the base message is the ring
message `m`. -/
abbrev w1ConvConcrete (O : W1Oracles X Y p (concretePrimitivesKeyGen p) Msg N reps)
    (M : MaskOracle X Y p T Msg) (βmin : ℚ≥0) (tol k D : ℕ) [NeZero D]
    {TPS : PSTypes} (PS : ProofSystem X Y (RingSignature.RingStmt (w1ConcreteBase p O M βmin tol k D (RMsg := Msg) fun _ m => m)) (RingSignature.RingWitOf (FIPSSignature p (concretePrimitivesKeyGen p))) TPS)
    (adm : KeyRing (PubKey p (concretePrimitivesKeyGen p)) N → Prop)
    [DecidablePred adm] : RingScheme X Y N (ofBaseT (w1BaseT (concretePrimitivesKeyGen p) Msg Msg (ringCoins (Bytes 32) k D)) TPS) :=
  w1Concrete p O M βmin tol k D (RMsg := Msg) (fun _ m => m) PS adm

/-- **The converted ML-DSA-44 ring signature publishing `w₁`** (`w1ConvConcrete`). -/
abbrev w1ConvScheme44 :=
  w1ConvConcrete (X := X) (Y := Y) (T := T) (Msg := Msg) (N := N) (reps := reps)
    _root_.MLDSA.mldsa44

/-- **The converted ML-DSA-65 ring signature publishing `w₁`** (`w1ConvConcrete`). -/
abbrev w1ConvScheme65 :=
  w1ConvConcrete (X := X) (Y := Y) (T := T) (Msg := Msg) (N := N) (reps := reps)
    _root_.MLDSA.mldsa65

/-- **The converted ML-DSA-87 ring signature publishing `w₁`** (`w1ConvConcrete`). -/
abbrev w1ConvScheme87 :=
  w1ConvConcrete (X := X) (Y := Y) (T := T) (Msg := Msg) (N := N) (reps := reps)
    _root_.MLDSA.mldsa87

end Concrete

end GordieHowe.Ring.MLDSAW1
