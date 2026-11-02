-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1IdealDist
public import GordieHowe.Foundations.ToMathlib.PMFRejectedPoints
public import GordieHowe.Applications.Ring.MLDSAW1KeyFreeHop

@[expose] public section

/-!
# The commitment points of the ring loop's attempts not kept

The ring loop of the ML-DSA ring publishing `w₁` (`loopOut`,
`GordieHowe/Applications/Ring/MLDSAW1Ring.lean`) runs at most `k` calls of `T` attempts. Each
attempt has a mask, a commitment `w₁` and a commitment point `H(µ, w₁)`. A call outputs the first
attempt that passes the checks of FIPS 204 Algorithm 7, if the call's flattening coin keeps it.
The signature published for the kept attempt determines its commitment (`w1Of_attemptOutput`).
The commitment points of the other attempts stay hidden: varying the mask of an attempt that is
not kept, the loop's output takes at most two values (`PMF.exists_loopOut_mem_range_of_not_keptAt`).

- `loopOut_eq_pmf`: the ring loop is `PMF.loopOut` at the acceptance test, the flattening coin's
  test and the attempt output of each call.
- `w1Of_out_of_keptAt`: the public value of the kept attempt's signature is its commitment.
- `response_reprogBase_sign`: the challenger's reply to a signing request at the oracle
  reprogrammed on its points is `replyOf` of the loop's output against a commitment hash that
  does not depend on the masks, for a prover reading the first components only off the
  commitment-hash points and at the public value's commitment-hash points (`ProverReadsPub`;
  `proverReadsPub_acceptAll`: the accepting proof system satisfies it) and an honest signer's key.
- `w1KeptPts`, `toReal_guess_mem_hidden_sign_le`, `toReal_guess_mem_hidden_le`: a guess from the
  reply to a request lands on a point of the request outside its kept points with probability at
  most `2 k T commitPointMax(Â_s)` (at most `2 k T Σ_s commitPointMax(Â_s)` for any request) over
  that request's signing coins.
- `keptPt`, `w1Pts_inter_w1KeptPts_eq`: the kept points among a request's points are determined by
  its response.
-/

open Finset
open scoped ENNReal BigOperators

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.MLDSA.Regularity GordieHowe.RingSignature
open GordieHowe.Quantum

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}

section Loop

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]

/-- The acceptance test of an attempt with mask `y`, at the commitment hash `hc`. -/
def attAcc (sk : SecretKey p) {R : KeyRing (PubKey p prims) N} (i : Fin R.1.length)
    (hc : Fin R.1.length × BucketVec p → CommitHashBytes p) (y : MaskBox p) : Bool :=
  attemptAccept prims sk (prims.expandA sk.rho) y (hc (i, realBuckets (prims.expandA sk.rho) y))

/-- The flattening coin `u`'s test of an attempt with mask `y`, at the commitment hash `hc`. -/
def attOk (βmin : ℚ≥0) (D : ℕ) (sk : SecretKey p) (R : KeyRing (PubKey p prims) N)
    (i : Fin R.1.length) (hc : Fin R.1.length × BucketVec p → CommitHashBytes p) (u : Fin D)
    (y : MaskBox p) : Bool :=
  decide (((u : ℕ) : ℚ≥0) < D * (flattenCoin prims sk βmin (realBuckets (prims.expandA sk.rho) y,
    hc (i, realBuckets (prims.expandA sk.rho) y)) *
    (ringWeights prims βmin (ringT0s prims R.1)).otherWeight i hc
      (realBuckets (prims.expandA sk.rho) y)))

/-- The signature of an attempt with mask `y`, at the commitment hash `hc`. -/
def attOut (sk : SecretKey p) {R : KeyRing (PubKey p prims) N} (i : Fin R.1.length)
    (hc : Fin R.1.length × BucketVec p → CommitHashBytes p) (y : MaskBox p) :
    FIPSSignature p prims :=
  attemptOutput prims sk (prims.expandA sk.rho) (y, hc (i, realBuckets (prims.expandA sk.rho) y))

/-- **The ring loop is `PMF.loopOut`** at the acceptance test, the flattening coin's test of each
call and the attempt output. -/
theorem loopOut_eq_pmf (βmin : ℚ≥0) {k D : ℕ} (sk : SecretKey p)
    (R : KeyRing (PubKey p prims) N) (i : Fin R.1.length)
    (hc : Fin R.1.length × BucketVec p → CommitHashBytes p) (ys : Fin k → Fin T → MaskBox p)
    (uv : Fin k → Fin D) :
    loopOut prims βmin sk R i hc ys uv =
      PMF.loopOut (fun _ => attAcc prims sk i hc) (fun c => attOk prims βmin D sk R i hc (uv c))
        (fun _ => attOut prims sk i hc) ys := by
  unfold loopOut PMF.loopOut PMF.firstKept
  refine congrArg (fun f => List.findSome? f (List.finRange k)) (funext fun c => ?_)
  unfold callOut PMF.callOutcome
  simp only [attAcc, attOk, attOut]
  rcases (List.finRange T).find? _ with _ | t
  · rfl
  · dsimp only
    split_ifs <;> (try simp_all); exact absurd ‹_ < _› (not_lt.2 ‹_ ≤ _›)

end Loop

section Kept

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)] (enc : Vector prims.High p.k → BucketVec p)

/-- **The public value of the kept attempt's signature is its commitment**, for an honest key
with `‖s₂‖∞ ≤ η`, the signing and verification laws and a coherent encoding: the loop outputs
the kept attempt's signature (`PMF.loopOut_of_keptAt`), and its recomputed commitment is the
attempt's (`w1Of_attemptOutput`). -/
theorem w1Of_out_of_keptAt (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    {seed : Bytes 32} (hs2 : polyVecBounded (keyGen prims seed).2.s2 p.eta) (βmin : ℚ≥0)
    {k D : ℕ} (R : KeyRing (PubKey p prims) N) (i : Fin R.1.length)
    (hc : Fin R.1.length × BucketVec p → CommitHashBytes p) (ys : Fin k → Fin T → MaskBox p)
    (uv : Fin k → Fin D) {c₀ : Fin k} {t₀ : Fin T}
    (h : PMF.KeptAt (fun _ => attAcc prims (keyGen prims seed).2 i hc)
      (fun c => attOk prims βmin D (keyGen prims seed).2 R i hc (uv c))
      (fun _ => attOut prims (keyGen prims seed).2 i hc) ys c₀ t₀) :
    loopOut prims βmin (keyGen prims seed).2 R i hc ys uv =
        some (attOut prims (keyGen prims seed).2 i hc (ys c₀ t₀)) ∧
      w1Of prims enc (keyGen prims seed).1 (attOut prims (keyGen prims seed).2 i hc (ys c₀ t₀)) =
        realBuckets (prims.expandA (keyGen prims seed).2.rho) (ys c₀ t₀) := by
  refine ⟨?_, ?_⟩
  · rw [loopOut_eq_pmf]
    exact PMF.loopOut_of_keptAt _ _ _ h
  · exact w1Of_attemptOutput prims enc h_laws hv henc hs2 _ _ h.2.2.1

end Kept

section Congr

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]

/-- **The ring loop reads the commitment hash only at the members' points of the masks'
commitments** (`callOut_congr`). -/
theorem loopOut_congr (βmin : ℚ≥0) {k D : ℕ} (sk : SecretKey p) (R : KeyRing (PubKey p prims) N)
    (i : Fin R.1.length) {hc hc' : Fin R.1.length × BucketVec p → CommitHashBytes p}
    (ys : Fin k → Fin T → MaskBox p) (uv : Fin k → Fin D)
    (h : ∀ c t j, hc (j, realBuckets (prims.expandA sk.rho) (ys c t)) =
      hc' (j, realBuckets (prims.expandA sk.rho) (ys c t))) :
    loopOut prims βmin sk R i hc ys uv = loopOut prims βmin sk R i hc' ys uv := by
  unfold loopOut
  exact congrArg (fun f => List.findSome? f (List.finRange k)) (funext fun c =>
    callOut_congr prims βmin D sk R i (ys c) (uv c) (h c))

end Congr

section Reply

variable {prims : Primitives p} [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y] [DecidableEq X]
  {O : W1Oracles X Y p prims Msg N reps} {M : MaskOracle X Y p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {TPS : PSTypes} {PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS}
  {adm : KeyRing (PubKey p prims) N → Prop}
  [hadm : DecidablePred adm]
  {Of : SideOracle (freshScheme prims O M βmin tol enc k D bmsg PS adm)} {n : ℕ}
  {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]

local notation "Sf" => freshScheme prims O M βmin tol enc k D bmsg PS adm
local notation "Bf" => freshBase prims O M βmin tol enc k D bmsg


/-- The masks of a signing request's calls: mask `t` of call `c` decoded from the signing coins
`cs` at the point `(t, key, tr, bmsg R m)` of the secret key `sk`. -/
def reqMasks (sk : SecretKey p) (R : KeyRing (PubKey p prims) N) (m : RMsg)
    (cs : Fin k → MaskPt T Msg → Y) : Fin k → Fin T → MaskBox p :=
  fun c t => M.ans (cs c (t, (sk.key, (sk.tr, bmsg R m))))

variable (O) in
/-- The commitment-hash points of a message representative `µ`. -/
noncomputable def muChPts (mu : Bytes 64) : Finset X :=
  Finset.univ.image fun w : BucketVec p => O.chPt (mu, w)

omit [NeZero (bucketCount p)] nttOps [Fintype prims.Power2High] [DecidableEq prims.Power2High]
  [Fintype prims.Hint] [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg]
  [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **The members' commitment hashes at a commitment `w` agree at two oracles reprogrammed on
point sets of one message representative `mu`** that both hold `H(mu, w)`, when the message
representatives are read off the reprogrammed points and the commitment-hash point map is
injective. -/
theorem ringOf_hOrc_reprogBase_eq (sp : Y ≃+ Y₁ × Y₂)
    (hch : Function.Injective O.chPt) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b)
    (R : KeyRing (PubKey p prims) N) (bm : Msg) (mu : Bytes 64) {S A : Finset X} (Z : X → Y₁)
    (H : X → Y) (hS : ∀ x ∈ S, ∃ w, x = O.chPt (mu, w)) (hA : ∀ x ∈ A, ∃ w, x = O.chPt (mu, w))
    {w : BucketVec p} (hwS : O.chPt (mu, w) ∈ S) (hwA : O.chPt (mu, w) ∈ A)
    (j : Fin R.1.length) :
    PMF.ringOf (ringPts prims R.1 bm) (O.hOrc (reprogBase sp S Z H)) (j, w) =
      PMF.ringOf (ringPts prims R.1 bm) (O.hOrc (reprogBase sp A Z H)) (j, w) := by
  have hmuPt : ∀ (T' : Finset X), (∀ x ∈ T', ∃ w, x = O.chPt (mu, w)) → ∀ a,
      reprogBase sp T' Z H (O.muPt a) = H (O.muPt a) := fun T' hT' a => by
    simp only [reprogBase]
    refine ite_eq_right_of_eq_false _ _ (eq_false fun hx => ?_)
    obtain ⟨w', hw'⟩ := hT' _ hx
    exact hdisj _ _ hw'
  simp only [PMF.ringOf, ringPts, W1Oracles.hOrc, schemeOrc, W1Oracles.muOrc, W1Oracles.chOrc]
  rw [hmuPt S hS, hmuPt A hA]
  by_cases hj : O.muAns (H (O.muPt (pubTr prims (R.1.get j), bm))) = mu
  · rw [hj]
    simp only [reprogBase, hwS, hwA, ↓reduceIte]
  · have h1 : O.chPt (O.muAns (H (O.muPt (pubTr prims (R.1.get j), bm))), w) ∉ S := fun hx => by
      obtain ⟨w', hw'⟩ := hS _ hx
      exact hj (Prod.mk.inj (hch hw')).1
    have h2 : O.chPt (O.muAns (H (O.muPt (pubTr prims (R.1.get j), bm))), w) ∉ A := fun hx => by
      obtain ⟨w', hw'⟩ := hA _ hx
      exact hj (Prod.mk.inj (hch hw')).1
    simp only [reprogBase, h1, h2, ↓reduceIte]

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg] [Fintype Y]
  [DecidableEq Y] [Nonempty Y] [NeZero D] in
/-- **The loop at two oracles reprogrammed on point sets of one message representative `mu`**
that both hold the signer's points of the masks' commitments gives the same output. -/
theorem loopOut_reprogBase_eq (sp : Y ≃+ Y₁ × Y₂)
    (hch : Function.Injective O.chPt) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b)
    (sk : SecretKey p) (R : KeyRing (PubKey p prims) N) (i : Fin R.1.length) (bm : Msg)
    (mu : Bytes 64) (S A : Finset X) (Z : X → Y₁) (H : X → Y) (ys : Fin k → Fin T → MaskBox p)
    (uv : Fin k → Fin D) (hS : ∀ x ∈ S, ∃ w, x = O.chPt (mu, w))
    (hA : ∀ x ∈ A, ∃ w, x = O.chPt (mu, w))
    (hmS : ∀ c t, O.chPt (mu, realBuckets (prims.expandA sk.rho) (ys c t)) ∈ S)
    (hmA : ∀ c t, O.chPt (mu, realBuckets (prims.expandA sk.rho) (ys c t)) ∈ A) :
    loopOut prims βmin sk R i (PMF.ringOf (ringPts prims R.1 bm) (O.hOrc (reprogBase sp S Z H)))
        ys uv =
      loopOut prims βmin sk R i (PMF.ringOf (ringPts prims R.1 bm) (O.hOrc (reprogBase sp A Z H)))
        ys uv :=
  loopOut_congr prims βmin sk R i ys uv fun c t j =>
    ringOf_hOrc_reprogBase_eq sp hch hdisj R bm mu Z H hS hA (hmS c t) (hmA c t) j

omit [AddGroup Y] in
/-- **The points of a signing request**: the commitment-hash points at the signer's message
representative of the commitments of all the masks. -/
theorem mem_w1Pts_sign (keys : Fin n → (Sf).KeyCoins) {Q : ℕ} (c : Fin Q → (Sf).SignCoins)
    (hist : List (HistoryEntry (UnforgeRequest (S := Sf) n Of) (UnforgeResponse (S := Sf) Of)))
    (s : Fin n) (R : KeyRing (PubKey p prims) N) (m : RMsg) (hR : (Bf).pk (keys s) ∈ R.1)
    (h : hist.length < Q) (H : X → Y) (x : X) :
    x ∈ (w1Pts Of keys c hist (.sign s R m)).run H ↔ ∃ ct : Fin k × Fin T,
      O.chPt (O.muAns (H (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m))),
        realBuckets (prims.expandA ((Sf).sk (keys s)).rho)
          (reqMasks (M := M) (bmsg := bmsg) ((Sf).sk (keys s)) R m (c ⟨hist.length, h⟩).1.1
            ct.1 ct.2)) = x := by
  unfold w1Pts
  simp only [h, ↓reduceDIte]
  split_ifs with hR'
  · simp [OracleProg.run_query, OracleProg.run_pure, reqMasks]
  · exact absurd hR hR'

open Classical in
variable (enc) in
/-- **The reply to a signing request from the loop's output**: on a supported ring passing the
public check with distinct message representatives at the oracle `H`, the loop's output `L` with
its public value and proof (prover coins `cp`, at the oracle `Hp`); a refusal otherwise. -/
noncomputable def replyOf (H Hp : X → Y) (pk : PubKey p prims) (R : KeyRing (PubKey p prims) N)
    (m : RMsg) (cp : (PS).Coins)
    (L : Option (FIPSSignature p prims)) : Option (UnforgeResponse (S := Sf) Of) :=
  (if adm R then
    (if RingCheck prims βmin tol (O.gOrc H) R ∧ MuDistinct prims (O.muOrc H) R (bmsg R m) then L
      else none).map fun σ => (w1Of prims enc pk σ,
        ((PS).prove ⟨R, m, w1Of prims enc pk σ⟩
            ⟨R.1.idxOf pk, σ⟩ cp).run Hp)
    else none).map UnforgeResponse.signature

omit nttOps in
/-- `Option.map` of two functions that agree at the value. -/
theorem option_map_congr_of_eq_some {α β : Type*} {f g : α → β} {L : Option α}
    (h : ∀ a, L = some a → f a = g a) : L.map f = L.map g := by
  rcases L with _ | a
  · rfl
  · exact congrArg some (h a rfl)

variable (O PS) in
/-- **The prover reads first components only at the commitment-hash points of the public value**:
two oracles with the same second components everywhere, agreeing off the commitment-hash points
and at the points `chPt (u, x.pub)` of the statement's public value, give the same proof. -/
def ProverReadsPub (sp : Y ≃+ Y₁ × Y₂) : Prop :=
  ∀ x w cp (H₁ H₂ : X → Y), (∀ z, (sp (H₁ z)).2 = (sp (H₂ z)).2) →
    (∀ z, (z ∉ Set.range O.chPt ∨ ∃ u, z = O.chPt (u, x.pub)) → H₁ z = H₂ z) →
    ((PS).prove x w cp).run H₁ =
    ((PS).prove x w cp).run H₂

omit [DecidableEq X] in
/-- **The accepting proof system satisfies `ProverReadsPub`**: its prover reads no oracle. -/
theorem proverReadsPub_acceptAll (sp : Y ≃+ Y₁ × Y₂) :
    ProverReadsPub (prims := prims) (M := M) (βmin := βmin) (tol := tol) (enc := enc) (k := k)
      (D := D) (bmsg := bmsg) O (ProofSystem.acceptAll X Y _ _) sp :=
  fun _ _ _ _ _ _ _ => rfl

open Classical in
/-- **The reply of the challenger at the oracle reprogrammed on a signing request's points** is
`replyOf` of the loop's output against the commitment hash of the oracle `O*` reprogrammed on all
the commitment-hash points of the signer's message representative `µ` (`muChPts`), with the
public check at `H` and the proof at `O*`; `O*` does not depend on the masks. The loop reads the
commitment hash only at the members' points of the masks' commitments, which are the request's
points for the signer and are not reprogrammed for the other members; the public check and the
message representatives read no commitment-hash point. The prover (`ProverReadsPub`) reads the
first component of the oracle only off the commitment-hash points and at the points
`chPt (u, pub)` of the statement's public value; for an honest signer's key (`‖s₂‖∞ ≤ η`, the
signing and verification laws, a coherent encoding) the public value of the output is the kept
attempt's commitment, so `chPt (µ, pub)` is a point of the request (`w1Of_out_of_keptAt`). -/
theorem response_reprogBase_sign (sp : Y ≃+ Y₁ × Y₂)
    (hch : Function.Injective O.chPt) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b)
    (hdisjg : ∀ a b, O.gPt a ≠ O.chPt b)
    (hPS : ProverReadsPub O PS sp) (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (keys : Fin n → (Sf).KeyCoins) {Q : ℕ} (c : Fin Q → (Sf).SignCoins)
    (rs : List (UnforgeRequest (S := Sf) n Of)) (s : Fin n) (R : KeyRing (PubKey p prims) N)
    (m : RMsg) (hs2 : polyVecBounded (keyGen prims (keys s)).2.s2 p.eta)
    (hR : (Bf).pk (keys s) ∈ R.1) (h : rs.length < Q) (Z : X → Y₁) (H : X → Y) :
    (((unforgeChallenger Sf n Of keys Q).respond c (Challenger.histOf rs) (.sign s R m)).run
        (reprogBase sp ((w1Pts Of keys c (Challenger.histOf rs) (.sign s R m)).run H) Z
          H)).response =
      replyOf enc H (reprogBase sp (muChPts O (O.muAns (H (O.muPt
          (pubTr prims ((Bf).pk (keys s)), bmsg R m))))) Z H) ((Bf).pk (keys s)) R m
        (c ⟨rs.length, h⟩).2
        (if hi : R.1.idxOf ((Bf).pk (keys s)) < R.1.length then
          loopOut prims βmin ((Sf).sk (keys s)) R ⟨_, hi⟩
            (PMF.ringOf (ringPts prims R.1 (bmsg R m))
              (O.hOrc (reprogBase sp (muChPts O (O.muAns (H (O.muPt
                (pubTr prims ((Bf).pk (keys s)), bmsg R m))))) Z H)))
            (reqMasks (M := M) (bmsg := bmsg) ((Sf).sk (keys s)) R m (c ⟨rs.length, h⟩).1.1)
            (c ⟨rs.length, h⟩).1.2
        else none) := by
  classical
  have hlen : (Challenger.histOf (Resp := UnforgeResponse (S := Sf) Of) rs).length = rs.length := by
    simp [Challenger.histOf]
  set S := (w1Pts Of keys c (Challenger.histOf rs) (.sign s R m)).run H with hS
  have hSsub : ∀ x ∈ S, x ∈ Set.range O.chPt := fun x hx =>
    w1Pts_subset keys c rs _ H (Finset.mem_coe.2 hx)
  have hoff : ∀ x ∉ Set.range O.chPt, reprogBase sp S Z H x = H x := fun x hx => by
    simp only [reprogBase]
    exact ite_eq_right_of_eq_false _ _ (eq_false fun h => hx (hSsub x h))
  have hsnd : ∀ (T' : Finset X) x, (sp (reprogBase sp T' Z H x)).2 = (sp (H x)).2 := fun T' x => by
    simp only [reprogBase]
    split_ifs
    · rw [AddEquiv.apply_symm_apply]
    · rfl
  have hgO : O.gOrc (reprogBase sp S Z H) = O.gOrc H := funext fun pt => by
    simp only [W1Oracles.gOrc]
    rw [hoff _ fun ⟨b, hb⟩ => hdisjg _ b hb.symm]
  have hmO : O.muOrc (reprogBase sp S Z H) = O.muOrc H := funext fun pt => by
    simp only [W1Oracles.muOrc]
    rw [hoff _ fun ⟨b, hb⟩ => hdisj _ b hb.symm]
  rcases hcj : c ⟨rs.length, h⟩ with ⟨cb, cp⟩
  simp only [unforgeChallenger, hlen, h, ↓reduceDIte, hcj]
  have hi : R.1.idxOf ((Bf).pk (keys s)) < R.1.length := List.idxOf_lt_length_iff.2 hR
  simp only [hi, ↓reduceDIte]
  split_ifs with hR'
  swap
  · exact absurd hR hR'
  rw [OracleProg.run_bind]
  erw [@run_sign_ofBase _ _ _ _ (freshBase prims O M βmin tol enc k D bmsg) _
    (PS) adm hadm _ (keys s) R m cb cp hR]
  unfold replyOf
  simp only [OracleProg.run_pure]
  refine congrArg (Option.map UnforgeResponse.signature) ?_
  by_cases ha : adm R
  · simp only [ha, ↓reduceIte]
    have hb := run_bsign_w1BaseSigner prims O βmin tol enc (MaskSource.fresh M) k D bmsg
      ((Sf).sk (keys s)) R (R.1.idxOf ((Bf).pk (keys s))) m cb (reprogBase sp S Z H)
    rw [hgO, hmO] at hb
    erw [hb]
    by_cases hc : RingCheck prims βmin tol (O.gOrc H) R ∧ MuDistinct prims (O.muOrc H) R (bmsg R m)
    · simp only [hc, hi, ↓reduceDIte]
      set mu := O.muAns (H (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m))) with hmu
      have hmemS : ∀ c' t, O.chPt (mu, realBuckets (prims.expandA ((Sf).sk (keys s)).rho)
          (reqMasks (M := M) (bmsg := bmsg) ((Sf).sk (keys s)) R m cb.1 c' t)) ∈ S := by
        intro c' t
        refine (mem_w1Pts_sign keys c (Challenger.histOf rs) s R m hR (hlen ▸ h) H _).2
          ⟨(c', t), ?_⟩
        simp only [hlen, hcj]
        rfl
      have hmuS : ∀ x ∈ S, ∃ w, x = O.chPt (mu, w) := fun x hx => by
        obtain ⟨ct, rfl⟩ :=
          (mem_w1Pts_sign keys c (Challenger.histOf rs) s R m hR (hlen ▸ h) H x).1 hx
        exact ⟨_, rfl⟩
      have hmuM : ∀ x ∈ muChPts O mu, ∃ w, x = O.chPt (mu, w) := fun x hx => by
        obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hx
        exact ⟨w, rfl⟩
      have hL : loopOut prims βmin ((Sf).sk (keys s)) R ⟨_, hi⟩
          (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc (reprogBase sp S Z H)))
          (reqMasks (M := M) (bmsg := bmsg) ((Sf).sk (keys s)) R m cb.1) cb.2 =
          loopOut prims βmin ((Sf).sk (keys s)) R ⟨_, hi⟩
            (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc (reprogBase sp (muChPts O mu) Z H)))
            (reqMasks (M := M) (bmsg := bmsg) ((Sf).sk (keys s)) R m cb.1) cb.2 := by
        exact loopOut_reprogBase_eq sp hch hdisj _ R _ (bmsg R m) mu S (muChPts O mu) Z H _ cb.2
          hmuS hmuM hmemS fun c' t => Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩
      simp only [and_self, ↓reduceIte]
      refine (congrArg (Option.map _) hL).trans (option_map_congr_of_eq_some fun σ hσ => ?_)
      have hpubS : O.chPt (mu, w1Of prims enc ((Bf).pk (keys s)) σ) ∈ S := by
        obtain ⟨c₀, t₀, hk, rfl⟩ := PMF.exists_keptAt_of_loopOut_eq_some _ _ _
          ((loopOut_eq_pmf prims βmin _ R _ _ _ _).symm.trans hσ)
        have hw : w1Of prims enc ((Bf).pk (keys s)) (attOut prims ((Sf).sk (keys s)) ⟨_, hi⟩
            (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc (reprogBase sp (muChPts O mu) Z H)))
            (reqMasks (M := M) (bmsg := bmsg) ((Sf).sk (keys s)) R m cb.1 c₀ t₀)) =
            realBuckets (prims.expandA ((Sf).sk (keys s)).rho)
              (reqMasks (M := M) (bmsg := bmsg) ((Sf).sk (keys s)) R m cb.1 c₀ t₀) :=
          (w1Of_out_of_keptAt prims enc h_laws hv henc hs2 βmin R _ _ _ cb.2 hk).2
        rw [hw]
        exact hmemS c₀ t₀
      have hpub : OracleProg.run (reprogBase sp S Z H)
          ((freshBase prims O M βmin tol enc k D bmsg).pub
            ((freshBase prims O M βmin tol enc k D bmsg).pk (keys s)) σ) =
          w1Of prims enc ((Bf).pk (keys s)) σ := rfl
      have hidx : @List.idxOf (freshBase prims O M βmin tol enc k D bmsg).PK
          instBEqOfDecidableEq ((freshBase prims O M βmin tol enc k D bmsg).pk (keys s)) R.1 =
          List.idxOf (α := PubKey p prims) ((Bf).pk (keys s)) R.1 :=
        idxOf_decEq_eq _ _
      rw [hpub, hidx]
      refine Prod.ext rfl (hPS _ _ _ _ _ (fun z => (hsnd S z).trans (hsnd _ z).symm) fun z hz => ?_)
      have hreq : (z ∈ S ↔ z ∈ muChPts O mu) →
          reprogBase sp S Z H z = reprogBase sp (muChPts O mu) Z H z := fun hT => by
        unfold reprogBase
        by_cases hzS : z ∈ S
        · simp only [hzS, hT.1 hzS, ↓reduceIte]
        · simp only [hzS, (not_congr hT).1 hzS, ↓reduceIte]
      refine hreq ?_
      rcases hz with hz | ⟨u, rfl⟩
      · refine ⟨fun hzS => absurd (hSsub _ hzS) hz, fun hzM => ?_⟩
        obtain ⟨w, rfl⟩ := hmuM _ hzM
        exact absurd ⟨_, rfl⟩ hz
      · by_cases hu : u = mu
        · rw [hu]
          exact ⟨fun _ => Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, fun _ => hpubS⟩
        · refine ⟨fun hzS => ?_, fun hzM => ?_⟩
          · obtain ⟨w, hw⟩ := hmuS _ hzS
            exact absurd (Prod.mk.inj (hch hw)).1 hu
          · obtain ⟨w, hw⟩ := hmuM _ hzM
            exact absurd (Prod.mk.inj (hch hw)).1 hu
    · simp only [hc, ↓reduceIte]
      rfl
  · exact (ite_eq_right_of_eq_false _ _ (eq_false ha)).trans
      (ite_eq_right_of_eq_false _ _ (eq_false ha)).symm

/-! ### The hidden points of a signing request -/

variable (Of) in
/-- **The response of the challenger at the oracle reprogrammed on a request's points**
`reprogBase sp S Z H` (the response of `Challenger.preReprog` and `Challenger.preReprogKeep`). -/
noncomputable def w1Resp (sp : Y ≃+ Y₁ × Y₂) (keys : Fin n → (Sf).KeyCoins) {Q : ℕ}
    (c : Fin Q → (Sf).SignCoins)
    (hist : List (HistoryEntry (UnforgeRequest (S := Sf) n Of) (UnforgeResponse (S := Sf) Of)))
    (req : UnforgeRequest (S := Sf) n Of) (Z : X → Y₁) (H : X → Y) :
    Option (UnforgeResponse (S := Sf) Of) :=
  (((unforgeChallenger Sf n Of keys Q).respond c hist req).run
    (reprogBase sp ((w1Pts Of keys c hist req).run H) Z H)).response

variable (O) in
/-- **The kept points of a response**: for a signature with public value `w₁`, the
commitment-hash points `chPt (u, w₁)`; none otherwise. -/
noncomputable def keepOf : Option (UnforgeResponse (S := Sf) Of) → Finset X
  | some (.signature σ) => Finset.univ.image fun u : Bytes 64 => O.chPt (u, σ.1)
  | _ => ∅

variable (Of) in
/-- **The kept points of a request given its response** (`keepOf`), in the form of the `keep`
argument of `Challenger.preReprogKeep`: they read neither the coins, the history nor the
request. -/
noncomputable def w1KeptPts {Q : ℕ} (_c : Fin Q → (Sf).SignCoins)
    (_hist : List (HistoryEntry (UnforgeRequest (S := Sf) n Of) (UnforgeResponse (S := Sf) Of)))
    (_req : UnforgeRequest (S := Sf) n Of) (r : Option (UnforgeResponse (S := Sf) Of)) :
    Finset X :=
  keepOf O r

omit [AddGroup Y] in
theorem mem_keepOf_signature (σ : (Sf).Sig) (x : X) :
    x ∈ keepOf O (some (UnforgeResponse.signature (S := Sf) (O := Of) σ)) ↔
      ∃ u, O.chPt (u, σ.1) = x := by
  simp [keepOf]

omit [DecidableEq X] [AddGroup Y] in
open Classical in
/-- `replyOf` refuses when the ring is unsupported or fails the checks. -/
theorem replyOf_eq_none {H Hp : X → Y} {pk : PubKey p prims} {R : KeyRing (PubKey p prims) N}
    {m : RMsg} {cp} (L : Option (FIPSSignature p prims))
    (hf : ¬ (adm R ∧ RingCheck prims βmin tol (O.gOrc H) R ∧
      MuDistinct prims (O.muOrc H) R (bmsg R m))) :
    replyOf (Of := Of) enc H Hp pk R m cp L = none := by
  unfold replyOf
  by_cases ha : adm R
  · have hc : ¬ (RingCheck prims βmin tol (O.gOrc H) R ∧
        MuDistinct prims (O.muOrc H) R (bmsg R m)) := fun hc => hf ⟨ha, hc⟩
    simp only [ha, hc, ↓reduceIte]
    rfl
  · simp only [ha, ↓reduceIte]
    rfl

omit [DecidableEq X] [AddGroup Y] in
open Classical in
/-- `replyOf` refuses when the loop outputs nothing. -/
theorem replyOf_none {H Hp : X → Y} {pk : PubKey p prims} {R : KeyRing (PubKey p prims) N}
    {m : RMsg} {cp} : replyOf (Of := Of) enc H Hp pk R m cp none = none := by
  unfold replyOf
  split_ifs <;> rfl

omit [DecidableEq X] [AddGroup Y] in
open Classical in
/-- `replyOf` of an output on a supported ring passing the checks: its signature. -/
theorem replyOf_some {H Hp : X → Y} {pk : PubKey p prims} {R : KeyRing (PubKey p prims) N}
    {m : RMsg} {cp} (σ : FIPSSignature p prims)
    (hp : adm R ∧ RingCheck prims βmin tol (O.gOrc H) R ∧
      MuDistinct prims (O.muOrc H) R (bmsg R m)) :
    ∃ prf, replyOf (Of := Of) enc H Hp pk R m cp (some σ) =
      some (.signature (w1Of prims enc pk σ, prf)) := by
  unfold replyOf
  simp only [hp.1, hp.2, and_self, ↓reduceIte, Option.map_some]
  exact ⟨_, rfl⟩

omit [DecidableEq X] [AddGroup Y] in
open Classical in
/-- A signature from `replyOf` is the output's: its public value is the output's `w₁`. -/
theorem exists_of_replyOf_eq_some {H Hp : X → Y} {pk : PubKey p prims}
    {R : KeyRing (PubKey p prims) N} {m : RMsg} {cp} {L : Option (FIPSSignature p prims)}
    {σ : (Sf).Sig} (h : replyOf (Of := Of) enc H Hp pk R m cp L = some (.signature σ)) :
    ∃ σ₀, L = some σ₀ ∧ σ.1 = w1Of prims enc pk σ₀ := by
  rcases L with _ | σ₀
  · rw [replyOf_none] at h
    exact absurd h (by simp)
  · refine ⟨σ₀, rfl, ?_⟩
    by_cases hp : adm R ∧ RingCheck prims βmin tol (O.gOrc H) R ∧
        MuDistinct prims (O.muOrc H) R (bmsg R m)
    · obtain ⟨prf, hprf⟩ := replyOf_some (Of := Of) (enc := enc) (Hp := Hp) (pk := pk) (cp := cp)
        σ₀ hp
      rw [hprf] at h
      injection h with h
      injection h with h
      subst h
      rfl
    · rw [replyOf_eq_none _ hp] at h
      exact absurd h (by simp)

omit [AddGroup Y] in
open Classical in
/-- The commitment-hash points of an output's public value are kept points of its reply, on a
supported ring passing the checks. -/
theorem mem_keepOf_replyOf {H Hp : X → Y} {pk : PubKey p prims} {R : KeyRing (PubKey p prims) N}
    {m : RMsg} {cp} (σ₀ : FIPSSignature p prims)
    (hp : adm R ∧ RingCheck prims βmin tol (O.gOrc H) R ∧
      MuDistinct prims (O.muOrc H) R (bmsg R m)) (mu : Bytes 64) :
    O.chPt (mu, w1Of prims enc pk σ₀) ∈
      keepOf O (replyOf (Of := Of) enc H Hp pk R m cp (some σ₀)) := by
  obtain ⟨prf, hprf⟩ := replyOf_some (Of := Of) (enc := enc) (Hp := Hp) (pk := pk) (cp := cp)
    σ₀ hp
  rw [hprf]
  simp only [keepOf, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨mu, rfl⟩

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Fintype Msg] [DecidableEq Msg] [DecidableEq Y] [AddGroup Y] in
/-- **A commitment-hash point of a decoded uniform mask is a given point** with probability at
most `commitPointMax`, for a uniform mask decoding and an injective point map. -/
theorem toReal_chPt_mask_le
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox p))
    (hch : Function.Injective O.chPt) (aHat : TqMatrix p.k p.l) (mu : Bytes 64) (x : X) :
    ((PMF.uniformOfFintype Y).toOuterMeasure
      {y | O.chPt (mu, realBuckets aHat (M.ans y)) = x}).toReal ≤ commitPointMax aHat := by
  classical
  by_cases hx : ∃ w, O.chPt (mu, w) = x
  · obtain ⟨w, rfl⟩ := hx
    have hiff : {y : Y | O.chPt (mu, realBuckets aHat (M.ans y)) = O.chPt (mu, w)} =
        M.ans ⁻¹' {b | realBuckets aHat b = w} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_preimage]
      exact ⟨fun he => (Prod.mk.inj (hch he)).2, fun he => by rw [he]⟩
    rw [hiff, ← PMF.toOuterMeasure_map_apply, hMask]
    have : (PMF.uniformOfFintype (MaskBox p)).toOuterMeasure {b | realBuckets aHat b = w} =
        ((maskUniform p).map (realBuckets aHat)) w := by
      rw [PMF.map_apply, PMF.toOuterMeasure_apply, maskUniform]
      refine tsum_congr fun b => ?_
      by_cases hb : realBuckets aHat b = w
      · simp [Set.indicator, hb]
      · have hb' : ¬ w = realBuckets aHat b := fun h => hb h.symm
        simp [Set.indicator, hb, hb']
    rw [this]
    exact toReal_map_realBuckets_le_commitPointMax aHat w
  · push Not at hx
    have hemp : {y : Y | O.chPt (mu, realBuckets aHat (M.ans y)) = x} = ∅ :=
      Set.eq_empty_of_forall_notMem fun y hy => hx _ hy
    rw [hemp, MeasureTheory.measure_empty, ENNReal.toReal_zero]
    exact (ENNReal.toReal_nonneg).trans
      (toReal_map_realBuckets_le_commitPointMax aHat (Classical.arbitrary _))

omit [DecidableEq X] [AddGroup Y] in
/-- The position of a member of a ring is below its length. -/
theorem idxOf_lt_of_mem (keys : Fin n → (Bf).KeyCoins) {s : Fin n} {R : KeyRing (PubKey p prims) N}
    (hR : (Bf).pk (keys s) ∈ R.1) : R.1.idxOf ((Bf).pk (keys s)) < R.1.length :=
  List.idxOf_lt_length_iff.2 hR

omit [AddGroup Y] in
/-- **The points of a signing request**, as the image of the attempts' masks. -/
theorem w1Pts_sign_eq (keys : Fin n → (Sf).KeyCoins) {Q : ℕ} (c : Fin Q → (Sf).SignCoins)
    (rs : List (UnforgeRequest (S := Sf) n Of)) (s : Fin n) (R : KeyRing (PubKey p prims) N)
    (m : RMsg) (hR : (Bf).pk (keys s) ∈ R.1) (h : rs.length < Q) (H : X → Y) :
    (w1Pts Of keys c (Challenger.histOf rs) (.sign s R m)).run H =
      Finset.univ.image fun ct : Fin k × Fin T =>
        O.chPt (O.muAns (H (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m))),
          realBuckets (prims.expandA ((Sf).sk (keys s)).rho)
            (reqMasks (M := M) (bmsg := bmsg) ((Sf).sk (keys s)) R m (c ⟨rs.length, h⟩).1.1
              ct.1 ct.2)) := by
  have hlen : (Challenger.histOf (Resp := UnforgeResponse (S := Sf) Of) rs).length = rs.length := by
    simp [Challenger.histOf]
  ext x
  rw [mem_w1Pts_sign keys c (Challenger.histOf rs) s R m hR (hlen ▸ h) H x, Finset.mem_image]
  have hj : (⟨(Challenger.histOf (Resp := UnforgeResponse (S := Sf) Of) rs).length, hlen ▸ h⟩ :
      Fin Q) = ⟨rs.length, h⟩ := Fin.ext hlen
  rw [hj]
  simp only [Finset.mem_univ, true_and]

open Classical in
/-- **The response to a signing request at the oracle reprogrammed on its points** is `replyOf`
of the loop's output at the commitment hash of `O*` (`response_reprogBase_sign`). -/
theorem w1Resp_sign_eq (sp : Y ≃+ Y₁ × Y₂)
    (hch : Function.Injective O.chPt) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b)
    (hdisjg : ∀ a b, O.gPt a ≠ O.chPt b) (hPS : ProverReadsPub O PS sp)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (keys : Fin n → (Sf).KeyCoins) {Q : ℕ} (c : Fin Q → (Sf).SignCoins)
    (rs : List (UnforgeRequest (S := Sf) n Of)) (s : Fin n) (R : KeyRing (PubKey p prims) N)
    (m : RMsg) (hs2 : polyVecBounded (keyGen prims (keys s)).2.s2 p.eta)
    (hR : (Bf).pk (keys s) ∈ R.1) (h : rs.length < Q) (Z : X → Y₁) (H : X → Y) :
    w1Resp Of sp keys c (Challenger.histOf rs) (.sign s R m) Z H =
      replyOf enc H (reprogBase sp (muChPts O (O.muAns (H (O.muPt
          (pubTr prims ((Bf).pk (keys s)), bmsg R m))))) Z H) ((Bf).pk (keys s)) R m
        (c ⟨rs.length, h⟩).2
        (loopOut prims βmin ((Sf).sk (keys s)) R ⟨_, idxOf_lt_of_mem keys hR⟩
          (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc (reprogBase sp (muChPts O
            (O.muAns (H (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m))))) Z H)))
          (reqMasks (M := M) (bmsg := bmsg) ((Sf).sk (keys s)) R m (c ⟨rs.length, h⟩).1.1)
          (c ⟨rs.length, h⟩).1.2) := by
  have hi : R.1.idxOf ((Bf).pk (keys s)) < R.1.length := List.idxOf_lt_length_iff.2 hR
  unfold w1Resp
  rw [response_reprogBase_sign sp hch hdisj hdisjg hPS h_laws hv henc keys c rs s R m hs2 hR h Z H]
  simp only [hi, ↓reduceDIte]

/-- **The commitment point of a signature's public value is a point of the request**, at the
signer's message representative, for an honest signer's key. -/
theorem chPt_mem_w1Pts_of_w1Resp (sp : Y ≃+ Y₁ × Y₂)
    (hch : Function.Injective O.chPt) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b)
    (hdisjg : ∀ a b, O.gPt a ≠ O.chPt b) (hPS : ProverReadsPub O PS sp)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (keys : Fin n → (Sf).KeyCoins) {Q : ℕ} (c : Fin Q → (Sf).SignCoins)
    (rs : List (UnforgeRequest (S := Sf) n Of)) (s : Fin n) (R : KeyRing (PubKey p prims) N)
    (m : RMsg) (hs2 : polyVecBounded (keyGen prims (keys s)).2.s2 p.eta)
    (hR : (Bf).pk (keys s) ∈ R.1) (h : rs.length < Q) (Z : X → Y₁) (H : X → Y) {σ : (Sf).Sig}
    (hr : w1Resp Of sp keys c (Challenger.histOf rs) (.sign s R m) Z H = some (.signature σ)) :
    O.chPt (O.muAns (H (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m))), σ.1) ∈
      (w1Pts Of keys c (Challenger.histOf rs) (.sign s R m)).run H := by
  rw [w1Resp_sign_eq sp hch hdisj hdisjg hPS h_laws hv henc keys c rs s R m hs2 hR h Z H] at hr
  obtain ⟨σ₀, hL, hσ⟩ := exists_of_replyOf_eq_some hr
  obtain ⟨c₀, t₀, hk, rfl⟩ := PMF.exists_keptAt_of_loopOut_eq_some _ _ _
    ((loopOut_eq_pmf prims βmin _ R _ _ _ _).symm.trans hL)
  have hw := (w1Of_out_of_keptAt prims enc h_laws hv henc hs2 βmin R _ _ _ _ hk).2
  rw [w1Pts_sign_eq keys c rs s R m hR h H, Finset.mem_image]
  exact ⟨(c₀, t₀), Finset.mem_univ _, by rw [hσ]; exact congrArg (fun w => O.chPt (_, w)) hw.symm⟩

/-- The signing coins `ω` with the coins of the masks at the points `(t, b₀)` overwritten by `v`.
-/
def ovrCoins (b₀ : Bytes 32 × (Bytes 64 × Msg)) (v : Fin k × Fin T → Y) (ω : (Sf).SignCoins) :
    (Sf).SignCoins :=
  (((fun cc (q : MaskPt T Msg) => if q.2 = b₀ then v (cc, q.1) else ω.1.1 cc q :
    Fin k → MaskPt T Msg → Y), ω.1.2), ω.2)

/-- The coins of the masks at the points `(t, b₀)`. -/
def rdCoins (b₀ : Bytes 32 × (Bytes 64 × Msg)) (ω : (Sf).SignCoins) : Fin k × Fin T → Y :=
  fun ct => ω.1.1 ct.1 (ct.2, b₀)

omit [DecidableEq X] [AddGroup Y] in
theorem rdCoins_ovrCoins (b₀ : Bytes 32 × (Bytes 64 × Msg)) (v : Fin k × Fin T → Y)
    (ω : (Sf).SignCoins) : rdCoins b₀ (ovrCoins b₀ v ω) = v := by
  funext ct
  simp [rdCoins, ovrCoins]

omit [DecidableEq X] [AddGroup Y] in
theorem ovrCoins_rdCoins (b₀ : Bytes 32 × (Bytes 64 × Msg)) (v : Fin k × Fin T → Y)
    (ω : (Sf).SignCoins) : ovrCoins b₀ (rdCoins b₀ ω) (ovrCoins b₀ v ω) = ω := by
  refine Prod.ext (Prod.ext (funext fun cc => funext fun q => ?_) rfl) rfl
  rcases q with ⟨t, b⟩
  by_cases hb : b = b₀
  · subst hb
    simp [rdCoins, ovrCoins]
  · simp [rdCoins, ovrCoins, hb]

omit [DecidableEq X] [AddGroup Y] in
theorem reqMasks_ovrCoins (keys : Fin n → (Sf).KeyCoins) (s : Fin n)
    (R : KeyRing (PubKey p prims) N) (m : RMsg) (v : Fin k × Fin T → Y) (ω : (Sf).SignCoins) :
    reqMasks (M := M) (bmsg := bmsg) ((Sf).sk (keys s)) R m
      (ovrCoins (((Sf).sk (keys s)).key, (((Sf).sk (keys s)).tr, bmsg R m)) v ω).1.1 =
      fun cc t => M.ans (v (cc, t)) := by
  funext cc t
  simp [reqMasks, ovrCoins]

omit [AddGroup Y] in
/-- **The points of a signing request at overwritten coins**: the commitment-hash points of the
decoded overwriting coins. -/
theorem w1Pts_update_ovrCoins (keys : Fin n → (Sf).KeyCoins) {Q : ℕ} (c : Fin Q → (Sf).SignCoins)
    (rs : List (UnforgeRequest (S := Sf) n Of)) (s : Fin n) (R : KeyRing (PubKey p prims) N)
    (m : RMsg) (hR : (Bf).pk (keys s) ∈ R.1) (h : rs.length < Q) (H : X → Y)
    (v : Fin k × Fin T → Y) (ω : (Sf).SignCoins) :
    (w1Pts Of keys (Function.update c ⟨rs.length, h⟩
        (ovrCoins (((Sf).sk (keys s)).key, (((Sf).sk (keys s)).tr, bmsg R m)) v ω))
        (Challenger.histOf rs) (.sign s R m)).run H =
      Finset.univ.image fun a : Fin k × Fin T =>
        O.chPt (O.muAns (H (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m))),
          realBuckets (prims.expandA ((Sf).sk (keys s)).rho) (M.ans (v a))) := by
  refine (w1Pts_sign_eq keys _ rs s R m hR h H).trans ?_
  rw [Function.update_self, reqMasks_ovrCoins keys s]

open Classical in
/-- **The response to a signing request at overwritten coins** is `replyOf` of `PMF.loopOut` on
the decoded overwriting coins. -/
theorem w1Resp_update_ovrCoins (sp : Y ≃+ Y₁ × Y₂)
    (hch : Function.Injective O.chPt) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b)
    (hdisjg : ∀ a b, O.gPt a ≠ O.chPt b) (hPS : ProverReadsPub O PS sp)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (keys : Fin n → (Sf).KeyCoins) {Q : ℕ} (c : Fin Q → (Sf).SignCoins)
    (rs : List (UnforgeRequest (S := Sf) n Of)) (s : Fin n) (R : KeyRing (PubKey p prims) N)
    (m : RMsg) (hs2 : polyVecBounded (keyGen prims (keys s)).2.s2 p.eta)
    (hR : (Bf).pk (keys s) ∈ R.1) (h : rs.length < Q) (Z : X → Y₁) (H : X → Y)
    (v : Fin k × Fin T → Y) (ω : (Sf).SignCoins) :
    w1Resp Of sp keys (Function.update c ⟨rs.length, h⟩
        (ovrCoins (((Sf).sk (keys s)).key, (((Sf).sk (keys s)).tr, bmsg R m)) v ω))
        (Challenger.histOf rs) (.sign s R m) Z H =
      replyOf enc H (reprogBase sp (muChPts O (O.muAns (H (O.muPt
          (pubTr prims ((Bf).pk (keys s)), bmsg R m))))) Z H) ((Bf).pk (keys s)) R m ω.2
        (PMF.loopOut
          (fun _ => attAcc prims ((Sf).sk (keys s)) ⟨_, idxOf_lt_of_mem keys hR⟩
            (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc (reprogBase sp (muChPts O
              (O.muAns (H (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m))))) Z H))))
          (fun cc => attOk prims βmin D ((Sf).sk (keys s)) R
            ⟨_, idxOf_lt_of_mem keys hR⟩
            (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc (reprogBase sp (muChPts O
              (O.muAns (H (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m))))) Z H)))
            (ω.1.2 cc))
          (fun _ => attOut prims ((Sf).sk (keys s)) ⟨_, idxOf_lt_of_mem keys hR⟩
            (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc (reprogBase sp (muChPts O
              (O.muAns (H (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m))))) Z H))))
          (fun cc t => M.ans (v (cc, t)))) := by
  refine (w1Resp_sign_eq sp hch hdisj hdisjg hPS h_laws hv henc keys _ rs s R m hs2 hR h Z H).trans
    ?_
  rw [Function.update_self, reqMasks_ovrCoins keys s]
  exact congrArg (fun L => replyOf (Of := Of) enc H (reprogBase sp (muChPts O (O.muAns (H (O.muPt
    (pubTr prims ((Bf).pk (keys s)), bmsg R m))))) Z H) ((Bf).pk (keys s)) R m ω.2 L)
    (loopOut_eq_pmf prims βmin _ R _ _ _ _)

open Classical in
/-- **A guess from the response to a signing request lands on a hidden point** (a point of the
request not kept, `w1KeptPts`) with probability at most `2 k T commitPointMax(Â_s)` over the
request's signing coins, for a fixed `Z`, a uniform mask decoding, an injective commitment-hash
point map, message-representative and public-check points that are not commitment-hash points, a
prover reading the first components only off the commitment-hash points and at the public value's
points (`ProverReadsPub`), and an honest signer's key. Each hidden point is the point of an attempt
not kept; varying that attempt's mask, the response takes at most two values
(`PMF.toReal_guess_mem_loopPoints_le`). -/
theorem toReal_guess_mem_hidden_sign_le (sp : Y ≃+ Y₁ × Y₂)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox p))
    (hch : Function.Injective O.chPt) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b)
    (hdisjg : ∀ a b, O.gPt a ≠ O.chPt b) (hPS : ProverReadsPub O PS sp)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (keys : Fin n → (Sf).KeyCoins) {Q : ℕ} (c : Fin Q → (Sf).SignCoins)
    (rs : List (UnforgeRequest (S := Sf) n Of)) (s : Fin n) (R : KeyRing (PubKey p prims) N)
    (m : RMsg) (hs2 : polyVecBounded (keyGen prims (keys s)).2.s2 p.eta)
    (hR : (Bf).pk (keys s) ∈ R.1) (h : rs.length < Q) (Z : X → Y₁) (H : X → Y)
    (g : Option (UnforgeResponse (S := Sf) Of) → X) :
    ((PMF.uniformOfFintype (Sf).SignCoins).toOuterMeasure {c' |
      g (w1Resp Of sp keys (Function.update c ⟨rs.length, h⟩ c') (Challenger.histOf rs)
          (.sign s R m) Z H) ∈
        (w1Pts Of keys (Function.update c ⟨rs.length, h⟩ c') (Challenger.histOf rs)
            (.sign s R m)).run H \
          w1KeptPts Of (Function.update c ⟨rs.length, h⟩ c') (Challenger.histOf rs) (.sign s R m)
            (w1Resp Of sp keys (Function.update c ⟨rs.length, h⟩ c') (Challenger.histOf rs)
              (.sign s R m) Z H)}).toReal ≤
      2 * k * T * commitPointMax (prims.expandA ((Sf).sk (keys s)).rho) := by
  have hi : R.1.idxOf ((Bf).pk (keys s)) < R.1.length := List.idxOf_lt_length_iff.2 hR
  refine PMF.toReal_uniform_le_of_overwrite
    (ovrCoins (((Sf).sk (keys s)).key, (((Sf).sk (keys s)).tr, bmsg R m)))
    (rdCoins (((Sf).sk (keys s)).key, (((Sf).sk (keys s)).tr, bmsg R m)))
    (rdCoins_ovrCoins _) (ovrCoins_rdCoins _) _ fun ω => ?_
  rw [← PMF.pi_uniformOfFintype]
  have hk : (∀ L L', replyOf (Of := Of) enc H (reprogBase sp (muChPts O (O.muAns (H (O.muPt
        (pubTr prims ((Bf).pk (keys s)), bmsg R m))))) Z H) ((Bf).pk (keys s)) R m ω.2 L =
      replyOf (Of := Of) enc H (reprogBase sp (muChPts O (O.muAns (H (O.muPt
        (pubTr prims ((Bf).pk (keys s)), bmsg R m))))) Z H) ((Bf).pk (keys s)) R m ω.2 L') ∨
      ∀ (ys : Fin k → Fin T → MaskBox p) cc t, PMF.KeptAt
        (fun _ => attAcc prims ((Sf).sk (keys s)) ⟨_, hi⟩
          (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc (reprogBase sp (muChPts O
            (O.muAns (H (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m))))) Z H))))
        (fun cc => attOk prims βmin D ((Sf).sk (keys s)) R ⟨_, hi⟩
          (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc (reprogBase sp (muChPts O
            (O.muAns (H (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m))))) Z H)))
          (ω.1.2 cc))
        (fun _ => attOut prims ((Sf).sk (keys s)) ⟨_, hi⟩
          (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc (reprogBase sp (muChPts O
            (O.muAns (H (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m))))) Z H)))) ys cc t →
        O.chPt (O.muAns (H (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m))),
          realBuckets (prims.expandA ((Sf).sk (keys s)).rho) (ys cc t)) ∈
          keepOf O (replyOf (Of := Of) enc H (reprogBase sp (muChPts O (O.muAns (H (O.muPt
            (pubTr prims ((Bf).pk (keys s)), bmsg R m))))) Z H) ((Bf).pk (keys s)) R m ω.2
            (PMF.loopOut
              (fun _ => attAcc prims ((Sf).sk (keys s)) ⟨_, hi⟩
                (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc (reprogBase sp (muChPts O
                  (O.muAns (H (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m))))) Z H))))
              (fun cc => attOk prims βmin D ((Sf).sk (keys s)) R ⟨_, hi⟩
                (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc (reprogBase sp (muChPts O
                  (O.muAns (H (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m))))) Z H)))
                (ω.1.2 cc))
              (fun _ => attOut prims ((Sf).sk (keys s)) ⟨_, hi⟩
                (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc (reprogBase sp (muChPts O
                  (O.muAns (H (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m))))) Z H))))
              ys)) := by
    by_cases hp : adm R ∧ RingCheck prims βmin tol (O.gOrc H) R ∧
        MuDistinct prims (O.muOrc H) R (bmsg R m)
    · refine Or.inr fun ys cc t hK => ?_
      rw [PMF.loopOut_of_keptAt _ _ _ hK]
      have hw : w1Of prims enc ((Bf).pk (keys s)) (attOut prims ((Sf).sk (keys s)) ⟨_, hi⟩
          (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc (reprogBase sp (muChPts O
            (O.muAns (H (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m))))) Z H)))
          (ys cc t)) = realBuckets (prims.expandA ((Sf).sk (keys s)).rho) (ys cc t) :=
        (w1Of_out_of_keptAt prims enc h_laws hv henc hs2 βmin R _ _ _ _ hK).2
      rw [← hw]
      exact mem_keepOf_replyOf _ hp _
    · exact Or.inl fun L L' => (replyOf_eq_none L hp).trans (replyOf_eq_none L' hp).symm
  have hbound := PMF.toReal_guess_mem_loopPoints_le _ _ _ (PMF.uniformOfFintype Y) M.ans
    (fun b => O.chPt (O.muAns (H (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m))),
      realBuckets (prims.expandA ((Sf).sk (keys s)).rho) b)) _ (keepOf O)
    (toReal_chPt_mask_le hMask hch _ _) hk g
  refine (ENNReal.toReal_mono (((PMF.pi fun _ => PMF.uniformOfFintype Y).toOuterMeasure_apply_le_one
    _).trans_lt ENNReal.one_lt_top).ne (MeasureTheory.measure_mono ?_)).trans
    (hbound.trans_eq (by ring))
  intro v hvE
  simp only [Set.mem_ofPred_eq] at hvE ⊢
  rw [w1Resp_update_ovrCoins sp hch hdisj hdisjg hPS h_laws hv henc keys c rs s R m hs2 hR h Z H,
    w1Pts_update_ovrCoins keys c rs s R m hR h H] at hvE
  exact hvE

/-- **A guess from the response to a request lands on a hidden point** with probability at most
`2 k T Σ_s commitPointMax(Â_s)` over the request's signing coins (`toReal_guess_mem_hidden_sign_le`
for a signing request whose signer is in the ring; other requests have no points). -/
theorem toReal_guess_mem_hidden_le (sp : Y ≃+ Y₁ × Y₂)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox p))
    (hch : Function.Injective O.chPt) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b)
    (hdisjg : ∀ a b, O.gPt a ≠ O.chPt b) (hPS : ProverReadsPub O PS sp)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (keys : Fin n → (Sf).KeyCoins) (hs2 : ∀ s, polyVecBounded (keyGen prims (keys s)).2.s2 p.eta)
    {Q : ℕ} (c : Fin Q → (Sf).SignCoins) (rs : List (UnforgeRequest (S := Sf) n Of))
    (req : UnforgeRequest (S := Sf) n Of) (h : rs.length < Q) (Z : X → Y₁) (H : X → Y)
    (g : Option (UnforgeResponse (S := Sf) Of) → X) :
    ((PMF.uniformOfFintype (Sf).SignCoins).toOuterMeasure {c' |
      g (w1Resp Of sp keys (Function.update c ⟨rs.length, h⟩ c') (Challenger.histOf rs) req Z H) ∈
        (w1Pts Of keys (Function.update c ⟨rs.length, h⟩ c') (Challenger.histOf rs) req).run H \
          w1KeptPts Of (Function.update c ⟨rs.length, h⟩ c') (Challenger.histOf rs) req
            (w1Resp Of sp keys (Function.update c ⟨rs.length, h⟩ c') (Challenger.histOf rs) req
              Z H)}).toReal ≤
      2 * k * T * ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho) := by
  have hcp : ∀ s, 0 ≤ commitPointMax (prims.expandA ((Sf).sk (keys s)).rho) := fun s =>
    (ENNReal.toReal_nonneg).trans
      (toReal_map_realBuckets_le_commitPointMax _ (Classical.arbitrary _))
  have hnn : 0 ≤ 2 * k * T * ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun s _ => hcp s)
  have hzero : (∀ c', (w1Pts Of keys (Function.update c ⟨rs.length, h⟩ c')
      (Challenger.histOf rs) req).run H = ∅) →
      ((PMF.uniformOfFintype (Sf).SignCoins).toOuterMeasure {c' |
        g (w1Resp Of sp keys (Function.update c ⟨rs.length, h⟩ c') (Challenger.histOf rs) req
          Z H) ∈
          (w1Pts Of keys (Function.update c ⟨rs.length, h⟩ c') (Challenger.histOf rs) req).run H \
            w1KeptPts Of (Function.update c ⟨rs.length, h⟩ c') (Challenger.histOf rs) req
              (w1Resp Of sp keys (Function.update c ⟨rs.length, h⟩ c') (Challenger.histOf rs) req
                Z H)}).toReal ≤
        2 * k * T * ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho) := fun hemp => by
    refine le_of_eq_of_le ?_ hnn
    have hset : {c' : (Sf).SignCoins |
        g (w1Resp Of sp keys (Function.update c ⟨rs.length, h⟩ c') (Challenger.histOf rs) req
          Z H) ∈
          (w1Pts Of keys (Function.update c ⟨rs.length, h⟩ c') (Challenger.histOf rs) req).run H \
            w1KeptPts Of (Function.update c ⟨rs.length, h⟩ c') (Challenger.histOf rs) req
              (w1Resp Of sp keys (Function.update c ⟨rs.length, h⟩ c') (Challenger.histOf rs) req
                Z H)} = ∅ :=
      Set.eq_empty_of_forall_notMem fun c' hc' => by
        simp only [Set.mem_ofPred_eq, hemp c', Finset.empty_sdiff] at hc'
        exact Finset.notMem_empty _ hc'
    rw [hset, MeasureTheory.measure_empty, ENNReal.toReal_zero]
  have hlen : (Challenger.histOf (Resp := UnforgeResponse (S := Sf) Of) rs).length = rs.length := by
    simp [Challenger.histOf]
  rcases req with i | ⟨s, R, m⟩ | ⟨i, bm⟩
  · exact hzero fun c' => by simp [w1Pts]
  · by_cases hR : (Bf).pk (keys s) ∈ R.1
    · refine (toReal_guess_mem_hidden_sign_le sp hMask hch hdisj hdisjg hPS h_laws hv henc keys c rs
        s R m (hs2 s) hR h Z H g).trans ?_
      exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun s =>
        commitPointMax (prims.expandA ((Sf).sk (keys s)).rho)) (fun s _ => hcp s)
        (Finset.mem_univ s)) (by positivity)
    · exact hzero fun c' => by simp [w1Pts, hlen, h, hR]
  · exact hzero fun c' => by simp [w1Pts]

/-- **The kept points among a request's points, given the response**: for a signature with public
value `w₁` to a signing request of `s` on `(R, m)` with `pk_s ∈ R`, the commitment-hash point
`chPt (µ_s, w₁)` at the signer's message representative read from `H`; none otherwise. -/
noncomputable def keptPt (keys : Fin n → (Sf).KeyCoins) (H : X → Y)
    (req : UnforgeRequest (S := Sf) n Of) (r : Option (UnforgeResponse (S := Sf) Of)) :
    Finset X :=
  match req, r with
  | .sign s R m, some (.signature σ) =>
    if (Bf).pk (keys s) ∈ R.1 then
      {O.chPt (O.muAns (H (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m))), σ.1)}
    else ∅
  | _, _ => ∅

/-- **The points of a request that its response keeps** are `keptPt` of the response, for an
honest signer's key: the kept point of a signature is a point of the request
(`chPt_mem_w1Pts_of_w1Resp`), and the request's points all have the signer's message
representative. -/
theorem w1Pts_inter_keepOf_eq (sp : Y ≃+ Y₁ × Y₂)
    (hch : Function.Injective O.chPt) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b)
    (hdisjg : ∀ a b, O.gPt a ≠ O.chPt b) (hPS : ProverReadsPub O PS sp)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (keys : Fin n → (Sf).KeyCoins) (hs2 : ∀ s, polyVecBounded (keyGen prims (keys s)).2.s2 p.eta)
    {Q : ℕ} (c : Fin Q → (Sf).SignCoins) (rs : List (UnforgeRequest (S := Sf) n Of))
    (req : UnforgeRequest (S := Sf) n Of) (h : rs.length < Q) (Z : X → Y₁) (H : X → Y)
    {r : Option (UnforgeResponse (S := Sf) Of)}
    (hr : w1Resp Of sp keys c (Challenger.histOf rs) req Z H = r) :
    (w1Pts Of keys c (Challenger.histOf rs) req).run H ∩ keepOf O r = keptPt keys H req r := by
  have hlen : (Challenger.histOf (Resp := UnforgeResponse (S := Sf) Of) rs).length = rs.length := by
    simp [Challenger.histOf]
  rcases req with i | ⟨s, R, m⟩ | ⟨i, bm⟩
  · simp [w1Pts, keptPt]
  · by_cases hR : (Bf).pk (keys s) ∈ R.1
    · rcases r with _ | (kc | σ | τ)
      · simp [keepOf, keptPt]
      · simp [keepOf, keptPt]
      · simp only [keptPt, hR, ↓reduceIte]
        ext x
        rw [Finset.mem_inter, mem_keepOf_signature, Finset.mem_singleton]
        constructor
        · rintro ⟨hxS, u, rfl⟩
          rw [w1Pts_sign_eq keys c rs s R m hR h H, Finset.mem_image] at hxS
          obtain ⟨ct, -, hct⟩ := hxS
          have he := Prod.mk.inj (hch hct)
          rw [← he.1]
        · rintro rfl
          exact ⟨chPt_mem_w1Pts_of_w1Resp sp hch hdisj hdisjg hPS h_laws hv henc keys c rs s R m
            (hs2 s) hR h Z H hr, _, rfl⟩
      · simp [keepOf, keptPt]
    · have hemp : (w1Pts Of keys c (Challenger.histOf rs) (.sign s R m)).run H = ∅ := by
        simp [w1Pts, hlen, h, hR]
      rw [hemp, Finset.empty_inter]
      rcases r with _ | (kc | σ | τ) <;> simp [keptPt, hR]
  · simp [w1Pts, keptPt]

/-- **A request's kept points, given its response, do not depend on the request's coins** (the
`hkept` hypothesis of `Challenger.HiddenReadsPair.ofPreReprogKeep` for the unforgeability
challenger, shared coins `Unit`, the coins of each request its signing coins, the points `w1Pts`
and the kept points `w1KeptPts`), for honest keys: both sides are `keptPt` of the common
response (`w1Pts_inter_keepOf_eq`). -/
theorem w1Pts_inter_w1KeptPts_eq (sp : Y ≃+ Y₁ × Y₂)
    (hch : Function.Injective O.chPt) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b)
    (hdisjg : ∀ a b, O.gPt a ≠ O.chPt b) (hPS : ProverReadsPub O PS sp)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (keys : Fin n → (Sf).KeyCoins) (hs2 : ∀ s, polyVecBounded (keyGen prims (keys s)).2.s2 p.eta)
    {Q : ℕ} :
    ∀ (_ω₀ : Unit) (c c' : Fin Q → (Sf).SignCoins) (rs : List (UnforgeRequest (S := Sf) n Of))
      (req : UnforgeRequest (S := Sf) n Of) (z : X → Y₁) (H : X → Y) (h : rs.length < Q),
      (∀ i, i ≠ ⟨rs.length, h⟩ → c i = c' i) →
      w1Resp Of sp keys c (Challenger.histOf rs) req z H =
        w1Resp Of sp keys c' (Challenger.histOf rs) req z H →
      (w1Pts Of keys c (Challenger.histOf rs) req).run H ∩
          w1KeptPts Of c (Challenger.histOf rs) req
            (w1Resp Of sp keys c (Challenger.histOf rs) req z H) =
        (w1Pts Of keys c' (Challenger.histOf rs) req).run H ∩
          w1KeptPts Of c' (Challenger.histOf rs) req
            (w1Resp Of sp keys c' (Challenger.histOf rs) req z H) := by
  intro _ c c' rs req z H h _ hresp
  unfold w1KeptPts
  rw [w1Pts_inter_keepOf_eq sp hch hdisj hdisjg hPS h_laws hv henc keys hs2 c rs req h z H rfl,
    w1Pts_inter_keepOf_eq sp hch hdisj hdisjg hPS h_laws hv henc keys hs2 c' rs req h z H rfl,
    hresp]

end Reply

end GordieHowe.Ring.MLDSAW1
