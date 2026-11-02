-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1Anonymity
public import GordieHowe.Applications.Ring.MLDSAW1Rejection
public import GordieHowe.Applications.Ring.MLDSAW1OracleFacts
public import GordieHowe.Model.RingSignature.Unforgeability
public import GordieHowe.Model.RingSignature.KeyReuse
public import GordieHowe.Model.RingSignature.SaltReprogramHist
public import GordieHowe.Model.Quantum.Interactive.RelabelAdversary

@[expose] public section

/-!
# Hedged to fresh masks in the unforgeability games of the ML-DSA ring publishing `w₁`

In the unforgeability game of BKM06 Definition 7 (`insiderForgeProb`,
`GordieHowe/Model/RingSignature/Unforgeability.lean`) and in the key-reuse game
(`keyReuseForgeProb`, `GordieHowe/Model/RingSignature/KeyReuse.lean`) of the hedged scheme
(`hedgedScheme`, `GordieHowe/Applications/Ring/MLDSAW1Anonymity.lean`), the hedged masks
`H(K ‖ rnd ‖ µ)` read by the signer at the per-call nonces `rnd` are replaced by fresh uniform
masks, at the cost of the hidden-salt reprogramming at the `Q · k` nonces
(`RingSignature.gameAdvantage_runLaw_salt_fresh_le_hist_of_pi`,
`GordieHowe/Model/RingSignature/SaltReprogramHist.lean`), as the anonymity proof does for its game
(`saltFreshPair`).

- `run_stdProg_hedged`, `run_stdProg_fresh_congr`: the ordinary signer with hedged masks is the one
  with fresh masks read off the oracle at the nonces; with fresh masks it reads the oracle only at
  the base signer's points.
- `SideHop Oh Of`: a side oracle `Oh` of the hedged scheme and one `Of` of the fresh scheme whose
  hedged signer is the fresh one at the masks read off the oracle at the nonces, the fresh one
  reading the oracle off the mask points, with the same covered rings and messages.
  `sideHopNone`: no side oracle on either side.
  `sideHopBase`: the base signers' ordinary signers (`baseSide`), under the domain separation
  `hdisj`.
- `unfReqEquiv`, `unfRespEquiv`: the requests and replies of the two games;
  `unfReqEquiv_sign`, `unfReqEquiv_sideSign`, `unfReqEquiv_symm_corrupt`, `unfReqEquiv_symm_sign`,
  `unfReqEquiv_symm_sideSign`: their values. `freshUnfChallenger`: the unforgeability challenger
  of the fresh scheme with the side oracle `Of`, on the hedged game's requests and replies
  (`Challenger.relabel`).
- `unfHopAns`, `unfSaltFreshPair`: **the hedged unforgeability challenger and its fresh counterpart
  form a `Challenger.SaltFreshPair`** at the mask oracle's points, the `Q · k` nonces as the hidden
  salts, when the base signer's oracles (`hdisj`) and the honest prover (`hPS`) read no mask point.
- `forges_congr`: the forgeries read the oracle only through the proof system's verifier, hence
  only off the mask points when the verifier does (`hPSv`).
- `freshForgeProb`: the probability of a forgery (`Forges`, on the hedged game's history) in the run
  of the adversary against `freshUnfChallenger`.
- `hedgedScheme.forgeProb_le`: **the hop** for every adversary of the game with a view read off the
  mask points: `forgeProb A Q ≤ freshForgeProb A Q + C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256)`
  (`RingSignature.gameAdvantage_runLaw_salt_fresh_le_hist_of_pi`).
- `relabel_request_eq_iff`, `forges_relabel_iff`: a forgery for a history is a forgery of the fresh
  scheme for the relabelled history. `freshForgeProb_eq`: `freshForgeProb` is the fresh scheme's forgery probability of
  the relabelled adversary (`GameAdversary.relabel`,
  `GordieHowe/Model/Quantum/Interactive/RelabelAdversary.lean`), for `n ≥ 1` users.
- `hedgedScheme.insiderForgeProb_le`, `hedgedScheme.keyReuseForgeProb_le`: **the hop in BKM06
  Definition 7 and in the key-reuse game**: the hedged scheme's forgery probability is at most the
  fresh scheme's for the relabelled adversary plus `C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256)`.
- `acceptAll_verify_eq`: the accepting proof system satisfies `hPSv`. The other hypotheses hold at
  `sumOracles`, `sumMask` (`sumMask_pt_injective`, `sumOracles_isPt_not_mem`), the accepting proof
  system (`acceptAll_prove_run_eq`) and the view of queries only (`queriesOnly_view_eq`).
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature
open scoped ENNReal NNReal BigOperators

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}

/-! ### The ordinary signer with hedged and with fresh masks -/

section Std

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y]
  (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg) (k : ℕ)

/-- **The ordinary signer with hedged masks is the one with fresh masks read off the oracle**: at
the oracle `H` and the nonces `r`, the masks of call `c` are `u ↦ H (M.pt (r c, u))`. -/
theorem run_stdProg_hedged (sk : SecretKey p) (m : Msg) (r : Fin k → (MaskSource.hedged M).Rnd)
    (H : X → Y) :
    (stdProg prims (MaskSource.hedged M) O k sk m r).run H =
      (stdProg prims (MaskSource.fresh M) O k sk m
        (fun c u => H (M.pt (r c, u)) : Fin k → (MaskSource.fresh M).Rnd)).run H := by
  unfold stdProg
  split_ifs with hk
  · simp only [OracleProg.run_query, OracleProg.run_bind, OracleProg.run_mapOutput,
      OracleProg.run_tabulate, OracleProg.run_pure]
    rfl
  · rfl

/-- **The ordinary signer with fresh masks reads the oracle only at the base signer's points**: its
runs agree at two oracles with the same first part of the split. -/
theorem run_stdProg_fresh_congr {H H' : X → Y} (hs : (O.split H).1 = (O.split H').1)
    (sk : SecretKey p) (m : Msg) (g : Fin k → (MaskSource.fresh M).Rnd) :
    (stdProg prims (MaskSource.fresh M) O k sk m g).run H =
      (stdProg prims (MaskSource.fresh M) O k sk m g).run H' := by
  by_cases hk : 0 < k
  · have h1 : ∀ G : X → Y, (stdProg prims (MaskSource.fresh M) O k sk m g).run G =
        (stdProg prims (MaskSource.fresh M) O 1 sk m fun _ => g ⟨0, hk⟩).run G := fun G => by
      unfold stdProg
      simp only [hk, Nat.zero_lt_one, ↓reduceDIte]
    rw [h1, h1, run_stdProg_one, run_stdProg_one, O.hOrc_eq_of_split hs]
    rfl
  · unfold stdProg
    simp only [hk, ↓reduceDIte, OracleProg.run_pure]

end Std

/-! ### The unforgeability challengers -/

section Hop

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y]
  (O : W1Oracles X Y p prims Msg N reps) (M : MaskOracle X Y p T Msg) (βmin : ℚ≥0) (tol : ℕ)
  (enc : Vector prims.High p.k → BucketVec p) (k D : ℕ) [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg)
  {TPS : PSTypes} (PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS)
  (adm : KeyRing (PubKey p prims) N → Prop) [DecidablePred adm]

local notation "Bh" => hedgedBase prims O M βmin tol enc k D bmsg
local notation "Bf" => freshBase prims O M βmin tol enc k D bmsg
local notation "Sh" => hedgedScheme prims O M βmin tol enc k D bmsg PS adm
local notation "Sf" => freshScheme prims O M βmin tol enc k D bmsg PS adm

/-- **A side oracle of the hedged scheme and one of the fresh scheme** with their messages and
signatures related by `eB` and `eS`: at the oracle `H`, the hedged side signer with the nonces `rv`
is the fresh one whose mask function of call `c` is `u ↦ H (M.pt (rv c, u))`, the fresh side
signer reads the oracle only outside the mask oracle's points, and related side messages cover the
same rings and messages. -/
structure SideHop (Oh : SideOracle (Sh)) (Of : SideOracle (Sf)) where
  /-- The side messages. -/
  eB : Oh.BMsg ≃ Of.BMsg
  /-- The side signatures. -/
  eS : Oh.BSig ≃ Of.BSig
  /-- Hedged side signing is fresh side signing with the masks read off the oracle. -/
  run_sign : ∀ (kp : (Sh).PK × (Sh).SK) (bm : Oh.BMsg) (rv : Fin k → Bytes 32) (uv : Fin k → Fin D)
    (cp : PS.Coins) (H : X → Y), (Oh.sign kp bm ((rv, uv), cp)).run H =
      ((Of.sign kp (eB bm) (((fun c u => H (M.pt (rv c, u))), uv), cp)).run H).map eS.symm
  /-- Fresh side signing reads the oracle off the mask oracle's points. -/
  run_sign_congr : ∀ H H', Quantum.AgreeOffRange M.pt H H' → ∀ kp bm c,
    (Of.sign kp bm c).run H = (Of.sign kp bm c).run H'
  /-- A side message covers the same rings and messages on both sides. -/
  covers_iff : ∀ bm R m, Of.Covers (eB bm) R m ↔ Oh.Covers bm R m

/-- **No side oracle on either side.** -/
def sideHopNone : SideHop prims O M βmin tol enc k D bmsg PS adm (SideOracle.none (Sh))
    (SideOracle.none (Sf)) where
  eB := Equiv.refl _
  eS := Equiv.refl _
  run_sign _ bm := bm.elim
  run_sign_congr _ _ _ _ bm := bm.elim
  covers_iff bm := bm.elim

/-- **The base signers' ordinary signers as the side oracles** (`baseSide`): with the hedged
ordinary signer reading the mask oracle at the first nonce, and the fresh one reading the oracle
only at the base signer's points, which are not mask points (`hdisj`). -/
def sideHopBase (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt) :
    SideHop prims O M βmin tol enc k D bmsg PS adm (baseSide (Bh) PS adm)
      (@baseSide X Y N _ (Bf) _ (PS) adm ‹DecidablePred adm›) where
  eB := Equiv.refl _
  eS := Equiv.refl _
  run_sign kp bm rv uv cp H := by
    with_unfolding_all
      change (stdProg prims (MaskSource.hedged M) O k kp.2 bm rv).run H =
        ((stdProg prims (MaskSource.fresh M) O k kp.2 bm fun c u => H (M.pt (rv c, u))).run H).map
          (Equiv.refl _).symm
    refine (run_stdProg_hedged prims O M k kp.2 bm rv H).trans ?_
    erw [Equiv.refl_symm, Equiv.coe_refl, Option.map_id]
    rfl
  run_sign_congr H H' h kp bm c := by
    with_unfolding_all exact
      run_stdProg_fresh_congr prims O M k (funext fun x => h x.1 (hdisj x.1 x.2)) kp.2 bm c.1.1
  covers_iff _ _ _ := Iff.rfl

end Hop

section Challenger

variable {prims : Primitives p} [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y]
  {O : W1Oracles X Y p prims Msg N reps} {M : MaskOracle X Y p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {TPS : PSTypes} {PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS}
  {adm : KeyRing (PubKey p prims) N → Prop} [DecidablePred adm]

local notation "Bh" => hedgedBase prims O M βmin tol enc k D bmsg
local notation "Bf" => freshBase prims O M βmin tol enc k D bmsg
local notation "Sh" => hedgedScheme prims O M βmin tol enc k D bmsg PS adm
local notation "Sf" => freshScheme prims O M βmin tol enc k D bmsg PS adm

variable {Oh : SideOracle (hedgedScheme prims O M βmin tol enc k D bmsg PS adm)}
  {Of : SideOracle (freshScheme prims O M βmin tol enc k D bmsg PS adm)}
  (P : SideHop prims O M βmin tol enc k D bmsg PS adm Oh Of) (n : ℕ)

/-- The requests of the two unforgeability games. -/
def unfReqEquiv : UnforgeRequest (S := Sh) n Oh ≃ UnforgeRequest (S := Sf) n Of where
  toFun := fun (r : UnforgeRequest (S := Sh) n Oh) => match r with
    | .corrupt i => .corrupt i
    | .sign s R m => .sign s R m
    | .sideSign i bm => .sideSign i (P.eB bm)
  invFun := fun (r : UnforgeRequest (S := Sf) n Of) => match r with
    | .corrupt i => .corrupt i
    | .sign s R m => .sign s R m
    | .sideSign i bm => .sideSign i (P.eB.symm bm)
  left_inv := fun (r : UnforgeRequest (S := Sh) n Oh) => by cases r <;> simp
  right_inv := fun (r : UnforgeRequest (S := Sf) n Of) => by cases r <;> simp

/-- A ring-signing request is relabelled to itself. -/
@[simp] theorem unfReqEquiv_sign (s : Fin n) (R : KeyRing (Sh).PK N) (m : (Sh).Msg) :
    unfReqEquiv P n (.sign s R m) = .sign s R m :=
  rfl

/-- A side request is relabelled at its message. -/
@[simp] theorem unfReqEquiv_sideSign (i : Fin n) (bm : Oh.BMsg) :
    unfReqEquiv P n (.sideSign i bm) = .sideSign i (P.eB bm) :=
  rfl

/-- A corruption is relabelled back to itself. -/
@[simp] theorem unfReqEquiv_symm_corrupt (i : Fin n) :
    (unfReqEquiv P n).symm (.corrupt i) = .corrupt i :=
  rfl

/-- A ring-signing request is relabelled back to itself. -/
@[simp] theorem unfReqEquiv_symm_sign (s : Fin n) (R : KeyRing (Sf).PK N) (m : (Sf).Msg) :
    (unfReqEquiv P n).symm (.sign s R m) = .sign s R m :=
  rfl

/-- A side request is relabelled back at its message. -/
@[simp] theorem unfReqEquiv_symm_sideSign (i : Fin n) (bm : Of.BMsg) :
    (unfReqEquiv P n).symm (.sideSign i bm) = .sideSign i (P.eB.symm bm) :=
  rfl

/-- The replies of the two unforgeability games. -/
def unfRespEquiv : UnforgeResponse (S := Sh) Oh ≃ UnforgeResponse (S := Sf) Of where
  toFun := fun (r : UnforgeResponse (S := Sh) Oh) => match r with
    | .keyCoins kc => .keyCoins kc
    | .signature σ => .signature σ
    | .sideSignature τ => .sideSignature (P.eS τ)
  invFun := fun (r : UnforgeResponse (S := Sf) Of) => match r with
    | .keyCoins kc => .keyCoins kc
    | .signature σ => .signature σ
    | .sideSignature τ => .sideSignature (P.eS.symm τ)
  left_inv := fun (r : UnforgeResponse (S := Sh) Oh) => by cases r <;> simp
  right_inv := fun (r : UnforgeResponse (S := Sf) Of) => by cases r <;> simp

/-- **The fresh counterpart of the hedged unforgeability challenger**: the unforgeability
challenger of the fresh scheme with the side oracle `Of`, on the hedged game's requests and replies
(`Challenger.relabel`). -/
noncomputable def freshUnfChallenger (keys : Fin n → Bytes 32) (Q : ℕ) :
    Quantum.Challenger X Y (UnforgeRequest (S := Sh) n Oh) (UnforgeResponse (S := Sh) Oh) :=
  (unforgeChallenger (Sf) n Of keys Q).relabel (unfReqEquiv P n) (unfRespEquiv P)

/-- **The answer to request number `j`** from the other coins `c'` and the mask functions `g` of
the `Q · k` calls: for `j < Q`, a corruption by the key coins, a ring-signing request of a member
by the fresh scheme's signature whose call `c` reads the mask function `g (j, c)` (`none` for a
non-member), a side request by the fresh side signer at the same coins; `none` for `j ≥ Q`. -/
noncomputable def unfHopAns (keys : Fin n → Bytes 32) (Q : ℕ)
    (c' : Fin Q → (Fin k → Fin D) × PS.Coins) (j : ℕ) (req : UnforgeRequest (S := Sh) n Oh)
    (g : Fin (Q * k) → MaskPt T Msg → Y) (H : X → Y) : Option (UnforgeResponse (S := Sh) Oh) :=
  if hj : j < Q then
    match req with
    | .corrupt i => some (.keyCoins (keys i))
    | .sign s R m =>
      if (Sh).pk (keys s) ∈ R.1 then
        (((Sf).sign ((Sf).keyGen (keys s)) R m
          (((fun c => g (finProdFinEquiv (⟨j, hj⟩, c))), (c' ⟨j, hj⟩).1), (c' ⟨j, hj⟩).2)).run
            H).map .signature
      else none
    | .sideSign i bm =>
      ((Of.sign ((Sf).keyGen (keys i)) (P.eB bm)
        (((fun c => g (finProdFinEquiv (⟨j, hj⟩, c))), (c' ⟨j, hj⟩).1), (c' ⟨j, hj⟩).2)).run
          H).map fun τ => .sideSignature (P.eS.symm τ)
  else none

/-- **The hedged unforgeability challenger reads the mask oracle at hidden fresh salts**
(`Challenger.SaltFreshPair`): the salts are the `Q · k` nonces of its coins, uniform and
independent (`PMF.pi`); its answer to request `j` is `unfHopAns` at the mask oracle's values on the
slices of the nonces of request `j`, and it reads the oracle off the mask oracle's points when the
base signer's oracles (`hdisj`) and the honest prover (`hPS`) do; its fresh counterpart is
`freshUnfChallenger`, which answers with uniform mask functions. -/
noncomputable def unfSaltFreshPair (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hPS : ∀ x w c H H', Quantum.AgreeOffRange M.pt H H' →
      (PS.prove x w c).run H = (PS.prove x w c).run H')
    (keys : Fin n → Bytes 32) (Q : ℕ) :
    (unforgeChallenger (Sh) n Oh keys Q).SaltFreshPair M.pt
      (PMF.pi fun _ : Fin (Q * k) => PMF.uniformOfFintype (Bytes 32))
      (freshUnfChallenger P n keys Q) where
  Coins' := Fin Q → (Fin k → Fin D) × PS.Coins
  ζ := PMF.uniformOfFintype _
  ans := unfHopAns P n keys Q
  readsOffRange c' j req g H H' h := by
    unfold unfHopAns
    split_ifs with hj
    · rcases req with i | ⟨s, R, m⟩ | ⟨i, bm⟩
      · rfl
      · dsimp only
        split_ifs
        · exact congrArg _ (freshScheme.run_sign_congr prims O M βmin tol enc k D bmsg PS adm
            (funext fun x => h x.1 (hdisj x.1 x.2)) (fun x w c => hPS x w c H H' h) _ _ _ _)
        · rfl
      · dsimp only
        exact congrArg _ (P.run_sign_congr H H' h _ _ _)
    · rfl
  dec₀ c := saltsEquiv Q k (Bytes 32) (Fin k → Fin D) PS.Coins c
  map_dec₀ := by
    change (PMF.uniformOfFintype _).map (saltsEquiv Q k (Bytes 32) (Fin k → Fin D) PS.Coins) = _
    rw [PMF.map_uniformOfFintype_equiv, PMF.pi_uniformOfFintype]
    exact PMF.uniformOfFintype_prod_eq_bind
  salted c hist req H hlt := by
    have hlt' : hist.length < Q := hlt
    have hg : (fun c₁ => Quantum.slices M.pt H
        ((saltsEquiv Q k (Bytes 32) (Fin k → Fin D) PS.Coins) c).2
          (finProdFinEquiv (⟨hist.length, hlt'⟩, c₁))) =
        fun c₁ u => H (M.pt ((c ⟨hist.length, hlt'⟩).1.1 c₁, u)) := by
      funext c₁ u
      exact congrArg (fun r => H (M.pt (r, u))) (saltsEquiv_snd_apply c _ c₁)
    unfold unforgeChallenger unfHopAns
    dsimp only
    rw [dite_eq_left_of_eq_true (eq_true hlt'), dite_eq_left_of_eq_true (eq_true hlt')]
    rcases req with i | ⟨s, R, m⟩ | ⟨i, bm⟩
    · rfl
    · dsimp only
      split_ifs with hm
      · rw [OracleProg.run_bind]
        change Quantum.Reply.mk _ _ = Quantum.Reply.mk _ _
        congr 1
        refine (congrArg (Option.map _) (hedgedScheme.run_sign prims O M βmin tol enc k D bmsg PS
          adm _ R m (c ⟨hist.length, hlt'⟩).1.1 (c ⟨hist.length, hlt'⟩).1.2
            (c ⟨hist.length, hlt'⟩).2 H)).trans ?_
        rw [hg]
        rfl
      · rfl
    · dsimp only
      rw [OracleProg.run_bind]
      change Quantum.Reply.mk _ _ = Quantum.Reply.mk _ _
      congr 1
      refine (congrArg (Option.map _) (P.run_sign _ bm (c ⟨hist.length, hlt'⟩).1.1
        (c ⟨hist.length, hlt'⟩).1.2 (c ⟨hist.length, hlt'⟩).2 H)).trans ?_
      rw [hg, Option.map_map]
      rfl
  dec₁ c := ((saltsEquiv Q k (MaskPt T Msg → Y) (Fin k → Fin D) PS.Coins c).2,
    (saltsEquiv Q k (MaskPt T Msg → Y) (Fin k → Fin D) PS.Coins c).1)
  map_dec₁ := by
    let _ : Fintype (MaskPt T Msg → Y) := inferInstance
    let _ : Fintype (Fin (Q * k) → MaskPt T Msg → Y) := inferInstance
    let _ : Fintype (Fin Q → (Fin k → Fin D) × PS.Coins) := inferInstance
    let e : (freshUnfChallenger P n keys Q).Coins ≃
        (Fin (Q * k) → MaskPt T Msg → Y) × (Fin Q → (Fin k → Fin D) × PS.Coins) :=
      (saltsEquiv Q k (MaskPt T Msg → Y) (Fin k → Fin D) PS.Coins).trans (Equiv.prodComm _ _)
    have : Nonempty (freshUnfChallenger P n keys Q).Coins :=
      ⟨e.symm (Classical.arbitrary _)⟩
    exact (PMF.map_uniformOfFintype_equiv e).trans PMF.uniformOfFintype_prod_eq_bind
  fresh c hist req H hlt := by
    have hlt' : hist.length < Q := hlt
    have hc : c ⟨(List.map (Quantum.HistoryEntry.relabel (unfReqEquiv P n) (unfRespEquiv P))
        hist).length, by rw [List.length_map]; exact hlt'⟩ =
        (((fun c₁ => (saltsEquiv Q k (MaskPt T Msg → Y) (Fin k → Fin D) PS.Coins c).2
          (finProdFinEquiv (⟨hist.length, hlt'⟩, c₁))),
          ((saltsEquiv Q k (MaskPt T Msg → Y) (Fin k → Fin D) PS.Coins c).1
            ⟨hist.length, hlt'⟩).1),
          ((saltsEquiv Q k (MaskPt T Msg → Y) (Fin k → Fin D) PS.Coins c).1
            ⟨hist.length, hlt'⟩).2) :=
      (congrArg c (Fin.ext (List.length_map _))).trans
        (Prod.ext (Prod.ext (funext fun c₁ => (saltsEquiv_snd_apply c _ c₁).symm) rfl) rfl)
    unfold freshUnfChallenger Quantum.Challenger.relabel unforgeChallenger unfHopAns
    dsimp only
    have hl : (List.map (Quantum.HistoryEntry.relabel (unfReqEquiv P n) (unfRespEquiv P))
        hist).length < Q := by
      rw [List.length_map]
      exact hlt'
    rw [dite_eq_left_of_eq_true (eq_true hl), dite_eq_left_of_eq_true (eq_true hlt'),
      OracleProg.run_mapOutput]
    simp only [hc]
    rcases req with i | ⟨s, R, m⟩ | ⟨i, bm⟩
    · rfl
    · rw [unfReqEquiv_sign]
      change Quantum.Reply.mk _ _ = Quantum.Reply.mk _ _
      dsimp only
      by_cases hm : (Sh).pk (keys s) ∈ R.1
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hm)]
        split_ifs with h2
        · rw [OracleProg.run_bind]
          simp only [OracleProg.run_pure, Option.map_map]
          rfl
        · exact absurd hm h2
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hm)]
        split_ifs with h2
        · exact absurd h2 hm
        · rfl
    · rw [unfReqEquiv_sideSign]
      change Quantum.Reply.mk _ _ = Quantum.Reply.mk _ _
      dsimp only
      rw [OracleProg.run_bind]
      simp only [OracleProg.run_pure, Option.map_map]
      rfl
  Q_eq := rfl

/-! ### The hop in the games -/

variable [Fintype X] [DecidableEq X] [Nonempty X] [AddGroup Y]

omit [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype X] [DecidableEq X] [Nonempty X]
  [AddGroup Y] in
/-- **The forgeries read the oracle only off the mask points** when the proof system's verifier
does (`hPSv`): the verification of `ofBase` is the verifier, and freshness reads only the
history. -/
theorem forges_congr (hPSv : ∀ x π H H', Quantum.AgreeOffRange M.pt H H' →
      PS.verify H x π = PS.verify H' x π)
    (keys : Fin n → Bytes 32) {H H' : X → Y} (h : Quantum.AgreeOffRange M.pt H H') :
    {p : (KeyRing (Sh).PK N × (Sh).Msg × (Sh).Sig) × UnforgeHist (S := Sh) n Oh |
        Forges keys H p.1 p.2} = {p | Forges keys H' p.1 p.2} := by
  ext p
  have hv : (Sh).verify H p.1.1 p.1.2.1 p.1.2.2 = (Sh).verify H' p.1.1 p.1.2.1 p.1.2.2 :=
    hPSv _ _ H H' h
  constructor
  · intro hf
    exact ⟨by rw [← hv]; exact hf.verify_eq, hf.fresh⟩
  · intro hf
    exact ⟨by rw [hv]; exact hf.verify_eq, hf.fresh⟩

/-- **The probability of a forgery against the fresh counterpart**: the run of the adversary
against `freshUnfChallenger` (fresh masks), with a forgery (`Forges`) for the users' key coins,
the oracle and the history of the hedged game's requests and replies. -/
noncomputable def freshForgeProb {V : OracleView X Y} {t : ℕ} (A : UnforgeAdversary (Sh) n Oh V t)
    (Q : ℕ) : ℝ≥0∞ :=
  (runLaw (fun keys H => A (fun i => (Sh).pk (keys i), V.view H)) fun keys =>
    freshUnfChallenger P n keys Q).toOuterMeasure {x | ∃ p ∈ x.2.2, Forges x.1 x.2.1 p.1 p.2}

/-- **Hedged to fresh masks in the unforgeability game** with the side oracles of `P`: for every
adversary with `t` superposition queries and an oracle view read off the mask oracle's points
(`hV`), and every number `Q` of requests, the probability of a forgery is at most that against the
fresh counterpart plus `C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256)`: the reprogramming of the mask
oracle at the `Q · k` uniform hidden nonces
(`gameAdvantage_runLaw_salt_fresh_le_hist_of_pi` with `unfSaltFreshPair`). The hypotheses `hM`,
`hdisj`, `hPS` and `hPSv` are the domain separation of the mask oracle from the base signer's
oracles, the honest prover and the verifier. -/
theorem hedgedScheme.forgeProb_le (hM : Function.Injective M.pt)
    (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hPS : ∀ x w c H H', Quantum.AgreeOffRange M.pt H H' →
      (PS.prove x w c).run H = (PS.prove x w c).run H')
    (hPSv : ∀ x π H H', Quantum.AgreeOffRange M.pt H H' → PS.verify H x π = PS.verify H' x π)
    {V : OracleView X Y} (hV : ∀ H H', Quantum.AgreeOffRange M.pt H H' → V.view H = V.view H')
    {t : ℕ} (A : UnforgeAdversary (Sh) n Oh V t) (Q : ℕ) :
    (forgeProb A Q).toReal ≤ (freshForgeProb P n A Q).toReal +
      ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) := by
  have hδ : ∀ (_ : Fin (Q * k)) (s : Bytes 32),
      ((PMF.uniformOfFintype (Bytes 32)) s).toReal ≤ (2 ^ 256 : ℝ)⁻¹ := fun _ s => by
    rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, card_bytes32]
  have h := gameAdvantage_runLaw_salt_fresh_le_hist_of_pi
    (fun keys H => A (fun i => (Sh).pk (keys i), V.view H))
    (fun keys H H' hH => by rw [hV H H' hH]) (fun keys => unfSaltFreshPair P n hdisj hPS keys Q) hM
    hδ (fun keys H => {p | Forges keys H p.1 p.2}) (fun keys H H' hH => forges_congr n hPSv keys hH)
  rw [gameAdvantage_eq] at h
  have key : ∀ a b c : ℝ, |a - b| ≤ c → a ≤ b + c := fun a b c hab => by
    linarith [(abs_sub_le_iff.1 hab).1]
  exact key _ _ _ h

omit [Fintype X] [DecidableEq X] [Nonempty X] [AddGroup Y] in
/-- **A relabelled request is `r'` exactly when the request is `r'` relabelled back.** -/
theorem relabel_request_eq_iff
    (e : Quantum.HistoryEntry (UnforgeRequest (S := Sh) n Oh) (UnforgeResponse (S := Sh) Oh))
    (r' : UnforgeRequest (S := Sf) n Of) :
    (e.relabel (unfReqEquiv P n) (unfRespEquiv P)).request = r' ↔
      e.request = (unfReqEquiv P n).symm r' :=
  (Equiv.eq_symm_apply _).symm

omit [Fintype X] [DecidableEq X] [Nonempty X] [AddGroup Y] in
/-- **A forgery is a forgery of the fresh scheme for the relabelled history**: the two schemes
verify alike, and the relabelling keeps the corruptions, the ring-signing requests and the side
requests with what they cover (`SideHop.covers_iff`). -/
theorem forges_relabel_iff (keys : Fin n → Bytes 32) (H : X → Y)
    (out : KeyRing (Sh).PK N × (Sh).Msg × (Sh).Sig) (hist : UnforgeHist (S := Sh) n Oh) :
    Forges (S := Sf) (O := Of) keys H out
        (hist.map (Quantum.HistoryEntry.relabel (unfReqEquiv P n) (unfRespEquiv P))) ↔
      Forges keys H out hist := by
  have hc : ∀ i, Corrupted (S := Sf)
      (hist.map (Quantum.HistoryEntry.relabel (unfReqEquiv P n) (unfRespEquiv P))) i ↔
      Corrupted hist i := fun i => by
    constructor
    · rintro ⟨e', he', hr⟩
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
      exact ⟨e, he, (relabel_request_eq_iff P n e _).1 hr⟩
    · rintro ⟨e, he, hr⟩
      exact ⟨_, List.mem_map.2 ⟨e, he, rfl⟩, (relabel_request_eq_iff P n e _).2 hr⟩
  have hs : ∀ R m, SignQueried (S := Sf)
      (hist.map (Quantum.HistoryEntry.relabel (unfReqEquiv P n) (unfRespEquiv P))) R m ↔
      SignQueried hist R m := fun R m => by
    constructor
    · rintro ⟨e', he', s', hr⟩
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
      exact ⟨e, he, s', (relabel_request_eq_iff P n e _).1 hr⟩
    · rintro ⟨e, he, s', hr⟩
      exact ⟨_, List.mem_map.2 ⟨e, he, rfl⟩, s', (relabel_request_eq_iff P n e _).2 hr⟩
  have hd : ∀ R m, SideCovered (S := Sf) keys
      (hist.map (Quantum.HistoryEntry.relabel (unfReqEquiv P n) (unfRespEquiv P))) R m ↔
      SideCovered keys hist R m := fun R m => by
    constructor
    · rintro ⟨e', he', i, bm', hr, hmem, hcov⟩
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
      refine ⟨e, he, i, P.eB.symm bm', (relabel_request_eq_iff P n e _).1 hr, hmem, ?_⟩
      rw [← P.covers_iff, Equiv.apply_symm_apply]
      exact hcov
    · rintro ⟨e, he, i, bm, hr, hmem, hcov⟩
      refine ⟨_, List.mem_map.2 ⟨e, he, rfl⟩, i, P.eB bm, (relabel_request_eq_iff P n e _).2 ?_,
        hmem, (P.covers_iff _ _ _).2 hcov⟩
      rw [hr, unfReqEquiv_symm_sideSign, Equiv.symm_apply_apply]
  constructor
  · rintro ⟨hv, hf⟩
    refine ⟨hv, fun pk hpk => ?_, fun h => hf.not_signQueried ((hs _ _).2 h),
      fun h => hf.not_sideCovered ((hd _ _).2 h)⟩
    obtain ⟨i, hi, hn⟩ := hf.honest_ring pk hpk
    exact ⟨i, hi, fun h => hn ((hc i).2 h)⟩
  · rintro ⟨hv, hf⟩
    refine ⟨hv, fun pk hpk => ?_, fun h => hf.not_signQueried ((hs _ _).1 h),
      fun h => hf.not_sideCovered ((hd _ _).1 h)⟩
    obtain ⟨i, hi, hn⟩ := hf.honest_ring pk hpk
    exact ⟨i, hi, fun h => hn ((hc i).1 h)⟩

/-- **The fresh counterpart's forgery probability is the fresh scheme's**: against
`freshUnfChallenger`, the probability of a forgery is the forgery probability, in the fresh
scheme's game with the side oracle `Of`, of the adversary relabelled to that game's requests and
replies (`GameAdversary.relabel`, `runLaw_relabel`, `forges_relabel_iff`). -/
theorem freshForgeProb_eq [NeZero n] {V : OracleView X Y} {t : ℕ}
    (A : UnforgeAdversary (Sh) n Oh V t) (Q : ℕ) :
    freshForgeProb P n A Q =
      forgeProb (S := Sf) (O := Of) (GameAdversary.relabel (unfReqEquiv P n) (unfRespEquiv P) A)
        Q := by
  unfold freshForgeProb forgeProb unforgeLaw
  change _ = (runLaw (fun keys H => (A (fun i => (Sh).pk (keys i), V.view H)).relabel
    (unfReqEquiv P n) (unfRespEquiv P)) fun keys =>
      unforgeChallenger (Sf) n Of keys Q).toOuterMeasure
      _
  rw [runLaw_relabel]
  refine Eq.trans ?_ (PMF.toOuterMeasure_map_apply _ _ _).symm
  congr 1
  ext ⟨keys, H, x⟩
  change (∃ p ∈ x, Forges keys H p.1 p.2) ↔ ∃ p ∈ x.map (fun p => (p.1,
    p.2.map (Quantum.HistoryEntry.relabel (unfReqEquiv P n) (unfRespEquiv P)))),
      Forges (S := Sf) (O := Of) keys H p.1 p.2
  rcases x with _ | ⟨out, hist⟩
  · simp only [Option.map_none, Option.mem_def, reduceCtorEq, false_and, exists_false]
  · simp only [Option.map_some, Option.mem_def, Option.some.injEq, exists_eq_left']
    exact (forges_relabel_iff P n keys H out hist).symm

end Challenger

/-! ### BKM06 Definition 7 and the key-reuse game -/

section Headlines

variable {prims : Primitives p} [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype X] [DecidableEq X] [Nonempty X] [AddGroup Y]
  {O : W1Oracles X Y p prims Msg N reps} {M : MaskOracle X Y p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {TPS : PSTypes} {PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS}
  {adm : KeyRing (PubKey p prims) N → Prop} [DecidablePred adm]
  {n : ℕ} [NeZero n]

local notation "Bh" => hedgedBase prims O M βmin tol enc k D bmsg
local notation "Bf" => freshBase prims O M βmin tol enc k D bmsg
local notation "Sh" => hedgedScheme prims O M βmin tol enc k D bmsg PS adm
local notation "Sf" => freshScheme prims O M βmin tol enc k D bmsg PS adm

/-- **Hedged to fresh masks in BKM06 Definition 7** (`insiderForgeProb`) for the ML-DSA ring
publishing `w₁` with `n ≥ 1` users and oracles with the mask-point facts `W1MaskPoints`: for every
adversary
with `t` superposition queries and an oracle view read off the mask oracle's points (`hV`), and
every number `Q` of requests, the probability of a forgery against the hedged scheme is at most
that of the relabelled adversary (`GameAdversary.relabel`) against the fresh scheme
(`freshScheme`) plus
`C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256)` (`hedgedScheme.forgeProb_le`, `freshForgeProb_eq`). -/
theorem hedgedScheme.insiderForgeProb_le (h : W1MaskPoints O M)
    (hPS : ∀ x w c H H', Quantum.AgreeOffRange M.pt H H' →
      (PS.prove x w c).run H = (PS.prove x w c).run H')
    (hPSv : ∀ x π H H', Quantum.AgreeOffRange M.pt H H' → PS.verify H x π = PS.verify H' x π)
    {V : OracleView X Y} (hV : ∀ H H', Quantum.AgreeOffRange M.pt H H' → V.view H = V.view H')
    {t : ℕ} (A : InsiderAdversary (Sh) n V t) (Q : ℕ) :
    (insiderForgeProb A Q).toReal ≤
      (insiderForgeProb (GameAdversary.relabel
        (unfReqEquiv (sideHopNone prims O M βmin tol enc k D bmsg PS adm) n)
        (unfRespEquiv (sideHopNone prims O M βmin tol enc k D bmsg PS adm)) A) Q).toReal +
      ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) := by
  rw [insiderForgeProb, insiderForgeProb, ← freshForgeProb_eq]
  exact hedgedScheme.forgeProb_le _ n h.hMinj h.hdisjM hPS hPSv hV A Q

/-- **Hedged to fresh masks in the key-reuse game** (`keyReuseForgeProb`, the base signers'
ordinary signers as side oracles, `sideHopBase`) for the ML-DSA ring publishing `w₁` with `n ≥ 1`
users: for every adversary with `t` superposition queries and an oracle view read off the mask
oracle's points (`hV`), and every number `Q` of requests, the probability of a forgery against the
hedged scheme is at most that of the relabelled adversary against the fresh scheme plus
`C(Q k, 2) / 2^256 + 2 t √(Q k / 2^256)`. -/
theorem hedgedScheme.keyReuseForgeProb_le (hM : Function.Injective M.pt)
    (hdisj : ∀ x, O.IsPt x → x ∉ Set.range M.pt)
    (hPS : ∀ x w c H H', Quantum.AgreeOffRange M.pt H H' →
      (PS.prove x w c).run H = (PS.prove x w c).run H')
    (hPSv : ∀ x π H H', Quantum.AgreeOffRange M.pt H H' → PS.verify H x π = PS.verify H' x π)
    {V : OracleView X Y} (hV : ∀ H H', Quantum.AgreeOffRange M.pt H H' → V.view H = V.view H')
    {t : ℕ} (A : KeyReuseAdversary (Bh) PS adm n V t) (Q : ℕ) :
    (keyReuseForgeProb A Q).toReal ≤
      (@keyReuseForgeProb X Y N _ (Bf) _ (PS) adm ‹DecidablePred adm› _ _ _ _ _ _ _ n V t
        (GameAdversary.relabel (Req := UnforgeRequest (S := Sh) n (baseSide (Bh) PS adm))
          (Resp := UnforgeResponse (S := Sh) (baseSide (Bh) PS adm))
          (unfReqEquiv (sideHopBase prims O M βmin tol enc k D bmsg PS adm hdisj) n)
          (unfRespEquiv (sideHopBase prims O M βmin tol enc k D bmsg PS adm hdisj)) A) Q).toReal +
      ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) := by
  unfold keyReuseForgeProb
  rw [← freshForgeProb_eq]
  exact hedgedScheme.forgeProb_le _ n hM hdisj hPS hPSv hV A Q

end Headlines

/-! ### Satisfiability of the verifier's domain separation -/

/-- **A proof system whose verifier reads no oracle satisfies `hPSv`**: the accepting proof
system's verifier agrees at any two oracles. -/
theorem acceptAll_verify_eq {S U Stmt Wit : Type} (emb : S × U → X) :
    ∀ x π (H H' : X → Y), Quantum.AgreeOffRange emb H H' →
      (ProofSystem.acceptAll X Y Stmt Wit).verify H x π =
        (ProofSystem.acceptAll X Y Stmt Wit).verify H' x π :=
  fun _ _ _ _ _ => rfl

end GordieHowe.Ring.MLDSAW1
