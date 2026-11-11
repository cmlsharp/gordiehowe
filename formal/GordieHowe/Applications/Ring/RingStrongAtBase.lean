-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingStrongMain
public import GordieHowe.Applications.Ring.RingForgerSplitChain
public import GordieHowe.Applications.Ring.RingAnonymity
public import GordieHowe.Applications.Ring.RingInsider
public import GordieHowe.Model.Quantum.Interactive.AbsorbTranscript

@[expose] public section

/-!
# The unforgeability game as an average over the base component

For an oracle split additively as `sp : Y ≃+ Y₁ × Y₂`
(`GordieHowe/Applications/Ring/MLDSAW1Split.lean`) and a base signer `B` reading only the base
component (`BaseSigner.ReadsOnly B (base sp)`), the forgery probability of BKM06 Definition 7 for
`ofBase B PS adm` is at most the average, over a uniform base component `ω`, of the forgery
probability for `ofBase (B.atBase sp ω) (PS' ω) adm` on the oracle `X → Y₂`, whose base signer
makes no queries, against the adversary read at `ω`. The proof reads the adversary and the game's
challenger at `ω` (`QueryBoundedAdversary.restrictAt`, `Challenger.restrictAt`,
`GordieHowe/Model/Quantum/Interactive/SplitRestrict.lean`), relays the restricted challenger to
the challenger of the game at `ω` (`QueryBoundedAdversary.transcriptLaw_le_absorbSide`), and splits
the uniform oracle into its two components (`tsum_uniform_split`).

- `BaseSigner.atBase B sp ω`: `B` with every program run at the oracle `join sp ω 0` and no
  queries. `BaseSigner.atBase_oracleFree`; `run_bsign_atBase`, `run_ssign_atBase`,
  `run_pub_atBase`, `bverify_atBase`: its programs. `BaseSigner.ReadsOnly.run_bsign_join`,
  `BaseSigner.ReadsOnly.run_pub_join`, `BaseSigner.ReadsOnly.bverify_join`,
  `BaseSigner.run_ssign_join`: under `ReadsOnly (base sp)` (`ReadsStdOnly` for `ssign`), `B`'s
  programs at `join sp ω h` are those of `B.atBase sp ω` at any oracle.
  `BaseSigner.CorrectWithin.atBase`: correctness transfers.
- `BaseSigner.atBaseStmt`, `BaseSigner.atBaseWit`: statements and witnesses of `B.atBase sp ω`
  as those of `B`.
- `ProofSystem.AtBase PS sp ω PS'`: the proof system `PS` read at the base component `ω` is `PS'`,
  along equivalences of the coins and the proofs: honest proofs at `join sp ω h` are `PS'`'s at
  `h`, and so is verification.
- `Quantum.QueryBoundedAdversary.transcriptLaw_mapOut`: the transcript law of an adversary with
  its output mapped (`QueryBoundedAdversary.mapOut`,
  `GordieHowe/Model/RingSignature/Transcript.lean`).
- `forgeProb_eq_tsum`: the forgery probability as an average over the key coins and the oracle.
- `unforgeReqAt`, `unforgeRespAt`, `unforgeRelayAt`, `relayList_unforgeRelayAt`, `outAt`: the
  requests, replies and signatures of the two games, and the relay between them.
  `InsiderAdversary.restrictAt hPS adm A`: the adversary read at `ω`, its requests and replies
  relabelled (`QueryBoundedAdversary.absorbSide`) and its output mapped by `outAt`.
- `Fresh.atBase`: freshness passes to the relabelled history. `coinsAt`,
  `run_sign_ofBase_atBase`, `relaysChallenger_unforgeRelayAt`: the game's challenger read at `ω`
  relays the challenger of the game at `ω`.
- `toOuterMeasure_forges_join_le`: at the oracle `join sp ω h`, the game is at most the game at
  `ω` at `h`. `insiderForgeProb_le_tsum_restrictAt`: the step.
- `Ring.spbcsSplitAt`, `Ring.atBase_spbcsSplitProofSystem`: the split spBCS proof system
  (`GordieHowe/Applications/Ring/SPBCSSplit.lean`) read at `ω` is the spBCS proof system at the
  program statements `(stmtProg x).run ω` (`GordieHowe/Applications/Ring/SPBCSComap.lean`), with the
  same coins and proofs. `Ring.insiderForgeProb_le_tsum_restrictAt_spbcsSplit`: the step for it.

The step is an inequality: the relay of the restricted challenger to the game at `ω` gives an
upper bound (`transcriptLaw_le_absorbSide`). It assumes at least one user (`NeZero n`), so that the
requests of the game at `ω` are inhabited.
-/

namespace GordieHowe

open Quantum Signature RingSignature RingSignature.OracleSplit
open scoped ENNReal

namespace RingSignature

/-! ### The base signer at a fixed base component -/

section AtBase

variable {X Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] {N : ℕ}
  {TB : BaseTypes}
  (B : BaseSigner X Y N TB)
  (sp : OracleSplit Y Y₁ Y₂) (ω : X → Y₁)

/-- **The base signer at the base component `ω`**, on the oracle `X → Y₂`: `B`'s types, keys and
base messages, and each of its programs (the ring-aware signer, the ordinary signer, the public
value) run at the oracle `join sp ω 0` with no queries; verification is `B`'s at that oracle. -/
abbrev BaseSigner.atBase : BaseSigner X Y₂ N TB :=
  { B with
    bsign := fun sk R i m c => .pure ((B.bsign sk R i m c).run (join sp ω 0))
    bsign_queries := fun _ _ _ _ _ => OracleProg.QueriesLE.pure _ _
    ssign := fun sk bm c => .pure ((B.ssign sk bm c).run (join sp ω 0))
    ssign_queries := fun _ _ _ => OracleProg.QueriesLE.pure _ _
    bverify := fun _ => B.bverify (join sp ω 0)
    pub := fun pk σ => .pure ((B.pub pk σ).run (join sp ω 0))
    pub_queries := fun _ _ => OracleProg.QueriesLE.pure _ _ }

/-- **The base signer at a fixed base component makes no queries.** -/
theorem BaseSigner.atBase_oracleFree : (B.atBase sp ω).OracleFree where
  bsign_noQuery _ _ _ _ _ := OracleProg.QueriesLE.pure _ _
  ssign_noQuery _ _ _ := OracleProg.QueriesLE.pure _ _
  pub_noQuery _ _ := OracleProg.QueriesLE.pure _ _
  bverify_eq _ _ := rfl

/-- The ring-aware signer at `ω` is `B`'s at `join sp ω 0`. -/
theorem run_bsign_atBase (sk : B.SK) (R : KeyRing B.PK N) (i : ℕ) (m : B.Msg) (c : B.Coins)
    (h : X → Y₂) :
    ((B.atBase sp ω).bsign sk R i m c).run h = (B.bsign sk R i m c).run (join sp ω 0) :=
  rfl

/-- The ordinary signer at `ω` is `B`'s at `join sp ω 0`. -/
theorem run_ssign_atBase (sk : B.SK) (bm : B.BMsg) (c : B.Coins) (h : X → Y₂) :
    ((B.atBase sp ω).ssign sk bm c).run h = (B.ssign sk bm c).run (join sp ω 0) :=
  rfl

/-- The public value at `ω` is `B`'s at `join sp ω 0`. -/
theorem run_pub_atBase (pk : B.PK) (σ : B.BSig) (h : X → Y₂) :
    ((B.atBase sp ω).pub pk σ).run h = (B.pub pk σ).run (join sp ω 0) :=
  rfl

/-- Verification at `ω` is `B`'s at `join sp ω 0`. -/
theorem bverify_atBase (h : X → Y₂) : (B.atBase sp ω).bverify h = B.bverify (join sp ω 0) :=
  rfl

variable [Fintype TB.Coins] [Nonempty TB.Coins]

variable {B}

omit [Fintype TB.Coins] [Nonempty TB.Coins] in
/-- **The ring-aware signer at a joined oracle** is the signer at `ω`, for a base signer reading
only the base component. -/
theorem BaseSigner.ReadsOnly.run_bsign_join (hB : B.ReadsOnly (base sp)) (sk : B.SK)
    (R : KeyRing B.PK N) (i : ℕ) (m : B.Msg) (c : B.Coins) (h h' : X → Y₂) :
    (B.bsign sk R i m c).run (join sp ω h) = ((B.atBase sp ω).bsign sk R i m c).run h' :=
  hB.run_bsign _ _ (by rw [base_join, base_join]) _ _ _ _ _

omit [Fintype TB.Coins] [Nonempty TB.Coins] in
/-- **The public value at a joined oracle** is the public value at `ω`, for a base signer reading
only the base component. -/
theorem BaseSigner.ReadsOnly.run_pub_join (hB : B.ReadsOnly (base sp)) (pk : B.PK) (σ : B.BSig)
    (h h' : X → Y₂) : (B.pub pk σ).run (join sp ω h) = ((B.atBase sp ω).pub pk σ).run h' :=
  hB.run_pub _ _ (by rw [base_join, base_join]) _ _

omit [Fintype TB.Coins] [Nonempty TB.Coins] in
/-- **Verification at a joined oracle** is verification at `ω`, for a base signer reading only
the base component. -/
theorem BaseSigner.ReadsOnly.bverify_join (hB : B.ReadsOnly (base sp)) (h h' : X → Y₂) :
    B.bverify (join sp ω h) = (B.atBase sp ω).bverify h' :=
  hB.bverify_eq _ _ (by rw [base_join, base_join])

omit [Fintype TB.Coins] [Nonempty TB.Coins] in
/-- **The ordinary signer at a joined oracle** is the ordinary signer at `ω`, for an ordinary
signer reading only the base component. -/
theorem BaseSigner.run_ssign_join (hS : B.ReadsStdOnly (base sp)) (sk : B.SK) (bm : B.BMsg)
    (c : B.Coins) (h h' : X → Y₂) :
    (B.ssign sk bm c).run (join sp ω h) = ((B.atBase sp ω).ssign sk bm c).run h' :=
  hS _ _ (by rw [base_join, base_join]) _ _ _

/-- **Correctness transfers to the base signer at `ω`**: its error at every oracle is `B`'s at
`join sp ω 0`. -/
theorem BaseSigner.CorrectWithin.atBase {ε : ℝ≥0∞} (hc : B.CorrectWithin ε) :
    (B.atBase sp ω).CorrectWithin ε :=
  fun _ kc R i hi m => hc (join sp ω 0) kc R i hi m

variable (B)

/-- **Statements of the base signer at `ω` as statements of `B`**: the same ring, message and
public value. -/
def BaseSigner.atBaseStmt : RingStmt (B.atBase sp ω) ≃ RingStmt B where
  toFun x := ⟨x.ring, x.msg, x.pub⟩
  invFun x := ⟨x.ring, x.msg, x.pub⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Witnesses of the base signer at `ω` as witnesses of `B`**: the same position and base
signature. -/
def BaseSigner.atBaseWit : RingWit (B.atBase sp ω) ≃ RingWit B where
  toFun w := ⟨w.idx, w.sig⟩
  invFun w := ⟨w.idx, w.sig⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### Proof systems at a fixed base component -/

/-- **The proof system `PS` read at the base component `ω` is `PS'`**, a proof system for the
base signer at `ω` on the oracle `X → Y₂`, along equivalences of the coins and of the proofs: the
honest proof at `join sp ω h` is `PS'`'s at `h` (`run_prove`), and so is verification
(`verify_eq`). -/
structure ProofSystem.AtBase {TB : BaseTypes}
    {B : BaseSigner X Y N TB} {TPS : PSTypes}
    (PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS)
    {TPS' : PSTypes} (PS' : ProofSystem X Y₂ (RingStmt (B.atBase sp ω)) (RingWit (B.atBase sp ω)) TPS') where
  /-- The coins. -/
  coinsEquiv : PS.Coins ≃ PS'.Coins
  /-- The proofs. -/
  proofEquiv : PS.Proof ≃ PS'.Proof
  /-- Honest proofs at a joined oracle are `PS'`'s. -/
  run_prove : ∀ x w c (h : X → Y₂), proofEquiv ((PS.prove x w c).run (join sp ω h)) =
    (PS'.prove ((B.atBaseStmt sp ω).symm x) ((B.atBaseWit sp ω).symm w) (coinsEquiv c)).run h
  /-- Verification at a joined oracle is `PS'`'s. -/
  verify_eq : ∀ (h : X → Y₂) x π,
    PS.verify (join sp ω h) x π = PS'.verify h ((B.atBaseStmt sp ω).symm x) (proofEquiv π)

end AtBase

end RingSignature

/-! ### Adversaries with a mapped output -/

namespace Quantum

variable {X Y Req Resp O O' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]

variable [Nonempty X] [AddGroup Y] [Nonempty Y] {t : ℕ}

/-- **The transcript law of an adversary with its output mapped** is the adversary's, with the
output mapped. -/
theorem QueryBoundedAdversary.transcriptLaw_mapOut (A : QueryBoundedAdversary X Y Req Resp O t)
    (g : O → O') (C : Challenger X Y Req Resp) (H : X → Y) :
    (A.mapOut g).transcriptLaw C H =
      (A.transcriptLaw C H).map (Option.map fun p => (g p.1, p.2)) := by
  simp only [transcriptLaw, PMF.map_bind]
  refine congrArg _ (funext fun a => ?_)
  simp only [Alg.outLaw]
  rw [PMF.map_comp, Option.map_comp_map]
  rfl

end Quantum

namespace RingSignature

/-! ### The forgery probability as an average over the key coins and the oracle -/

/-- **The forgery probability as an average** over the users' key coins and the oracle. -/
theorem forgeProb_eq_tsum {X Y : Type} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y]
    [DecidableEq Y] [AddGroup Y] [Nonempty Y] {N n t : ℕ} {TS : RingTypes} [Fintype TS.PK]
    [DecidableEq TS.PK] [Fintype TS.Msg] [DecidableEq TS.Msg] [Fintype TS.KeyCoins]
    [DecidableEq TS.KeyCoins] [Nonempty TS.KeyCoins] [Fintype TS.Sig] [DecidableEq TS.Sig]
    [Fintype TS.SignCoins] [DecidableEq TS.SignCoins] [Nonempty TS.SignCoins]
    {S : RingScheme X Y N TS}
    {O : SideOracle S} [Fintype O.BMsg] [DecidableEq O.BMsg] [Fintype O.BSig] [DecidableEq O.BSig]
    {V : OracleView X Y}
    (A : UnforgeAdversary S n O V t) (Q : ℕ) :
    forgeProb A Q = ∑' keys, PMF.uniformOfFintype (Fin n → S.KeyCoins) keys *
      ∑' H, PMF.uniformOfFintype (X → Y) H *
        ((A (fun i => S.pk (keys i), V.view H)).transcriptLaw (unforgeChallenger S n O keys Q)
          H).toOuterMeasure {x | ∃ p ∈ x, Forges keys H p.1 p.2} := by
  rw [forgeProb, unforgeLaw, runLaw, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun keys => congrArg _ ?_
  rw [PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun H => congrArg _ ?_
  rw [PMF.toOuterMeasure_map_apply]
  rfl


/-! ### The game at a fixed base component -/

section Game

variable {X Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] {N n : ℕ}
  {TB : BaseTypes}
  {B : BaseSigner X Y N TB}
  {sp : OracleSplit Y Y₁ Y₂} {ω : X → Y₁}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS}
  {TPS' : PSTypes} [Fintype TPS'.Proof] [DecidableEq TPS'.Proof] [Fintype TPS'.Coins]
  [DecidableEq TPS'.Coins] [Nonempty TPS'.Coins]
  {PS' : ProofSystem X Y₂ (RingStmt (B.atBase sp ω)) (RingWit (B.atBase sp ω)) TPS'}
  (hPS : PS.AtBase sp ω PS') (adm : KeyRing B.PK N → Prop) [DecidablePred adm]

variable [DecidableEq TB.PK]

/-- **The game's requests of the two schemes**: the same corruptions and signing requests. -/
def unforgeReqAt : UnforgeRequest (S := ofBase B PS adm) n (SideOracle.none _) ≃
    UnforgeRequest (S := ofBase (B.atBase sp ω) PS' adm) n (SideOracle.none _) where
  toFun
    | .corrupt i => .corrupt i
    | .sign s R m => .sign s R m
    | .sideSign _ bm => bm.elim
  invFun
    | .corrupt i => .corrupt i
    | .sign s R m => .sign s R m
    | .sideSign _ bm => bm.elim
  left_inv r := by rcases r with _ | _ | ⟨_, ⟨⟩⟩ <;> rfl
  right_inv r := by rcases r with _ | _ | ⟨_, ⟨⟩⟩ <;> rfl

/-- **The game's replies of the two schemes**: the same key coins, and signatures `(y, π)` with
the proof carried by `hPS.proofEquiv`. -/
def unforgeRespAt : UnforgeResponse (SideOracle.none (ofBase B PS adm)) ≃
    UnforgeResponse (SideOracle.none (ofBase (B.atBase sp ω) PS' adm)) where
  toFun
    | .keyCoins kc => .keyCoins kc
    | .signature s => .signature (s.1, hPS.proofEquiv s.2)
    | .sideSignature τ => τ.elim
  invFun
    | .keyCoins kc => .keyCoins kc
    | .signature s => .signature (s.1, hPS.proofEquiv.symm s.2)
    | .sideSignature τ => τ.elim
  left_inv r := by rcases r with _ | ⟨y, π⟩ | ⟨⟨⟩⟩ <;> simp
  right_inv r := by rcases r with _ | ⟨y, π⟩ | ⟨⟨⟩⟩ <;> simp

/-- **The relay from the game of `ofBase B PS adm` to the game at `ω`**: each request relabelled
(`unforgeReqAt`), each reply relabelled back (`unforgeRespAt`). -/
def unforgeRelayAt :
    SideRelay (UnforgeRequest (S := ofBase B PS adm) n (SideOracle.none _))
      (UnforgeResponse (SideOracle.none (ofBase B PS adm)))
      (UnforgeRequest (S := ofBase (B.atBase sp ω) PS' adm) n (SideOracle.none _))
      (UnforgeResponse (SideOracle.none (ofBase (B.atBase sp ω) PS' adm))) where
  route _ r := unforgeReqAt adm r
  answer _ _ a := a.map (unforgeRespAt hPS adm).symm

omit [DecidableEq TB.PK] in
/-- **The signature of the game at `ω`** of a signature of `ofBase B PS adm`: the proof carried by
`hPS.proofEquiv`. -/
def outAt (o : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof)) :
    KeyRing (B.atBase sp ω).PK N × (B.atBase sp ω).Msg × ((B.atBase sp ω).Pub × PS'.Proof) :=
  (o.1, o.2.1, (o.2.2.1, hPS.proofEquiv o.2.2.2))

variable [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [Nonempty Y]
  [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂] [Nonempty Y₂] [NeZero n] {t : ℕ}

variable [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]

/-- **The adversary at the base component `ω`**: on the users' public keys, the adversary read at
`ω` (`QueryBoundedAdversary.restrictAt`), with its requests and replies relabelled by
`unforgeRelayAt` (`QueryBoundedAdversary.absorbSide` with no side coins) and its output mapped by
`outAt`; an adversary of the game for `ofBase (B.atBase sp ω) PS' adm`. -/
noncomputable def InsiderAdversary.restrictAt
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly X Y) t) :
    InsiderAdversary (ofBase (B.atBase sp ω) PS' adm) n (OracleView.queriesOnly X Y₂) t :=
  fun inp => (((A inp).restrictAt sp ω).absorbSide (PMF.pure ())
    (fun _ => unforgeRelayAt (n := n) hPS adm) fun _ _ => (unforgeReqAt adm).injective).mapOut
    (outAt hPS)

/-! ### The game's challenger read at `ω` relays the challenger of the game at `ω` -/

omit [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype Y₁]
  [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂] [Nonempty Y₂] [NeZero n] [Fintype TPS.Proof]
  [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins]
  [Fintype TPS'.Proof] [DecidableEq TPS'.Proof] [Fintype TPS'.Coins] [DecidableEq TPS'.Coins]
  [Nonempty TPS'.Coins] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] in
/-- **The relay of a request list** is the list of the relabelled requests. -/
theorem relayList_unforgeRelayAt
    (rs : List (UnforgeRequest (S := ofBase B PS adm) n (SideOracle.none _))) :
    (unforgeRelayAt (n := n) hPS adm).relayList rs = rs.map (unforgeReqAt adm) := by
  refine List.ext_getElem (by simp [SideRelay.length_relayList]) fun i h₁ h₂ => ?_
  simp [SideRelay.relayList, unforgeRelayAt]

omit [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype Y₁]
  [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂] [Nonempty Y₂] [NeZero n] [Fintype TPS.Proof]
  [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins]
  [Fintype TPS'.Proof] [DecidableEq TPS'.Proof] [Fintype TPS'.Coins] [DecidableEq TPS'.Coins]
  [Nonempty TPS'.Coins] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] in
/-- **Freshness passes to the relabelled history**: a ring and message fresh after `hist` are
fresh, in the game at `ω`, after every history whose requests are the relabelled requests of
`hist`. -/
theorem Fresh.atBase {keys : Fin n → (ofBase B PS adm).KeyCoins}
    {hist : UnforgeHist n (SideOracle.none (ofBase B PS adm))}
    {hist' : UnforgeHist n (SideOracle.none (ofBase (B.atBase sp ω) PS' adm))}
    (hh : hist'.map HistoryEntry.request = (hist.map HistoryEntry.request).map (unforgeReqAt adm))
    {R : KeyRing B.PK N} {m : B.Msg} (hf : Fresh keys hist R m) :
    Fresh (S := ofBase (B.atBase sp ω) PS' adm) keys hist' R m := by
  have hmem : ∀ e' ∈ hist', ∃ e ∈ hist, unforgeReqAt adm e.request = e'.request := by
    intro e' he'
    have : e'.request ∈ (hist.map HistoryEntry.request).map (unforgeReqAt adm) := by
      rw [← hh]
      exact List.mem_map_of_mem he'
    simpa using this
  refine ⟨fun pk hpk => ?_, fun ⟨e', he', s, hr⟩ => ?_, not_sideCovered_none⟩
  · obtain ⟨i, hi, hc⟩ := hf.honest_ring pk hpk
    refine ⟨i, hi, fun ⟨e', he', hr⟩ => hc ?_⟩
    obtain ⟨e, he, hre⟩ := hmem e' he'
    refine ⟨e, he, ?_⟩
    rw [hr] at hre
    rcases h : e.request with j | ⟨s, R', m'⟩ | ⟨_, ⟨⟩⟩ <;> rw [h] at hre <;> cases hre
    rfl
  · obtain ⟨e, he, hre⟩ := hmem e' he'
    refine hf.not_signQueried ⟨e, he, s, ?_⟩
    rw [hr] at hre
    rcases h : e.request with j | ⟨s', R', m'⟩ | ⟨_, ⟨⟩⟩ <;> rw [h] at hre <;> cases hre
    rfl

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] in
/-- **The coins of the game's challenger at `ω`**: the base signer's coins kept and the prover's
carried by `hPS.coinsEquiv`, with no side coins. -/
def coinsAt (Q : ℕ) : (Fin Q → B.Coins × PS.Coins) ≃ Unit × (Fin Q → B.Coins × PS'.Coins) :=
  ((Equiv.refl (Fin Q)).arrowCongr ((Equiv.refl B.Coins).prodCongr hPS.coinsEquiv)).trans
    (Equiv.punitProd _).symm

omit [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype Y₁]
  [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂] [Nonempty Y₂] [NeZero n] [Fintype TPS.Proof]
  [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins]
  [Fintype TPS'.Proof] [DecidableEq TPS'.Proof] [Fintype TPS'.Coins] [DecidableEq TPS'.Coins]
  [Nonempty TPS'.Coins] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] in
/-- **Signing at `ω`**: for a base signer reading only the base component, the signer of
`ofBase (B.atBase sp ω) PS' adm` at the oracle `h` with the prover's coins carried by
`hPS.coinsEquiv` outputs the signature of `ofBase B PS adm` at `join sp ω h`, its proof carried by
`hPS.proofEquiv`. -/
theorem run_sign_ofBase_atBase (hB : B.ReadsOnly (base sp)) (kp : B.PK × B.SK)
    (R : KeyRing B.PK N) (m : B.Msg) (cb : B.Coins) (cp : PS.Coins) (h : X → Y₂) :
    ((ofBase (B.atBase sp ω) PS' adm).sign kp R m (cb, hPS.coinsEquiv cp)).run h =
      (((ofBase B PS adm).sign kp R m (cb, cp)).run (join sp ω h)).map
        fun s => (s.1, hPS.proofEquiv s.2) := by
  simp only [ofBase_sign]
  split_ifs
  · rw [run_signAt_eq, run_signAt_eq, ← hB.run_bsign_join sp ω _ _ _ _ _ h h]
    rcases (B.bsign kp.2 R (R.1.idxOf kp.1) m cb).run (join sp ω h) with _ | σ
    · rfl
    · simp only [Option.map_some]
      rw [← hB.run_pub_join sp ω _ _ h h]
      exact congrArg some (Prod.ext rfl (hPS.run_prove ⟨R, m, _⟩ ⟨_, σ⟩ cp h).symm)
  · rfl

variable [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins]

omit [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype Y₁]
  [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂] [Nonempty Y₂] [NeZero n] [Fintype TPS.Proof]
  [DecidableEq TPS.Proof] [Fintype TPS'.Proof] [DecidableEq TPS'.Proof] [Fintype TB.PK]
  [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins]
  [DecidableEq TB.KeyCoins] in
/-- **The game's challenger read at `ω` relays the game's challenger at `ω`** through
`unforgeRelayAt`, at the coins `c'` and their image under `coinsAt`, for a base signer reading
only the base component. -/
theorem relaysChallenger_unforgeRelayAt (hB : B.ReadsOnly (base sp))
    (keys : Fin n → (ofBase B PS adm).KeyCoins)
    (Q : ℕ) (c' : Fin Q → B.Coins × PS'.Coins) :
    (unforgeRelayAt (n := n) hPS adm).RelaysChallenger
      ((unforgeChallenger (ofBase B PS adm) n (SideOracle.none _) keys Q).restrictAt sp ω)
      ((coinsAt hPS Q).symm ((), c'))
      (unforgeChallenger (ofBase (B.atBase sp ω) PS' adm) n (SideOracle.none _) keys Q) c' where
  Q_eq := rfl
  run_eq hist hist' r G hh hlt := by
    refine (Challenger.run_respond_restrictAt sp ω _ _ hist r G).trans ?_
    have hl : hist'.length = hist.length := by
      have := congrArg List.length hh
      simpa [SideRelay.length_relayList] using this
    have ha := unforgeChallenger_noAssign (B := B.atBase sp ω) (PS := PS') (adm := adm) keys Q c'
      hist' (unforgeReqAt adm r) G
    refine congrArg₂ Reply.mk ?_ ha.symm
    have hlt₀ : hist.length < Q := hlt
    have hlt' : hist'.length < Q := hl ▸ hlt₀
    change (((unforgeChallenger (ofBase B PS adm) n (SideOracle.none _) keys Q).respond
        ((coinsAt hPS Q).symm ((), c')) hist r).run (join sp ω G)).response = _
    simp only [unforgeChallenger, hlt₀, hlt', ↓reduceDIte, unforgeRelayAt]
    have hf : (⟨hist'.length, hlt'⟩ : Fin Q) = ⟨hist.length, hlt₀⟩ := Fin.ext hl
    rw [hf]
    have hcj : (coinsAt hPS Q).symm ((), c') ⟨hist.length, hlt₀⟩ = ((c' ⟨hist.length, hlt₀⟩).1,
        hPS.coinsEquiv.symm (c' ⟨hist.length, hlt₀⟩).2) := rfl
    rcases r with i | ⟨s, R, m⟩ | ⟨_, ⟨⟩⟩
    · rfl
    · simp only [unforgeReqAt, Equiv.coe_fn_mk]
      by_cases hm : (ofBase B PS adm).pk (keys s) ∈ R.1
      · have hm' : (ofBase (B.atBase sp ω) PS' adm).pk (keys s) ∈ R.1 := hm
        simp only [hm, ↓reduceIte]
        split_ifs with h₁
        swap
        · exact absurd hm' h₁
        simp only [OracleProg.run_bind, OracleProg.run_pure]
        have hs := run_sign_ofBase_atBase hPS adm hB ((ofBase B PS adm).keyGen (keys s)) R m
          (c' ⟨hist.length, hlt₀⟩).1 (hPS.coinsEquiv.symm (c' ⟨hist.length, hlt₀⟩).2) G
        rw [Equiv.apply_symm_apply] at hs
        rw [hcj]
        erw [hs]
        generalize ((ofBase B PS adm).sign ((ofBase B PS adm).keyGen (keys s)) R m
          ((c' ⟨hist.length, hlt₀⟩).1, hPS.coinsEquiv.symm (c' ⟨hist.length, hlt₀⟩).2)).run
          (join sp ω G) = o
        rcases o with _ | ⟨y, π⟩
        · rfl
        · show some (UnforgeResponse.signature (O := SideOracle.none (ofBase B PS adm)) (y, π)) =
            some (UnforgeResponse.signature (O := SideOracle.none (ofBase B PS adm))
              (y, hPS.proofEquiv.symm (hPS.proofEquiv π)))
          rw [Equiv.symm_apply_apply]
      · have hm' : (ofBase (B.atBase sp ω) PS' adm).pk (keys s) ∉ R.1 := hm
        simp only [hm, ↓reduceIte]
        split_ifs with h₁
        · exact absurd h₁ hm'
        · rfl
  answer_none _ _ _ := rfl

/-! ### The step to the average over the base component -/

/-- **The game at a joined oracle is at most the game at `ω`**: at the users' key coins `keys` and
the oracle `join sp ω h`, the forgery probability of the adversary against the game's challenger
is at most that of the adversary at `ω` against the challenger of the game at `ω`, at `h`. -/
theorem toOuterMeasure_forges_join_le (hB : B.ReadsOnly (base sp))
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly X Y) t)
    (keys : Fin n → (ofBase B PS adm).KeyCoins) (Q : ℕ) (h : X → Y₂) :
    ((A (fun i => (ofBase B PS adm).pk (keys i), ())).transcriptLaw
        (unforgeChallenger (ofBase B PS adm) n (SideOracle.none _) keys Q)
        (join sp ω h)).toOuterMeasure {x | ∃ p ∈ x, Forges keys (join sp ω h) p.1 p.2} ≤
      ((InsiderAdversary.restrictAt hPS adm A
          (fun i => (ofBase B PS adm).pk (keys i), ())).transcriptLaw
        (unforgeChallenger (ofBase (B.atBase sp ω) PS' adm) n (SideOracle.none _) keys Q)
        h).toOuterMeasure
        {x | ∃ p ∈ x, Forges (S := ofBase (B.atBase sp ω) PS' adm) keys h p.1 p.2} := by
  refine (le_of_eq (congrArg (fun μ => PMF.toOuterMeasure μ _)
    (QueryBoundedAdversary.transcriptLaw_restrictAt_join sp ω _ _
      (unforgeChallenger_noAssign keys Q) h).symm)).trans ?_
  refine (QueryBoundedAdversary.transcriptLaw_le_absorbSide _
    (C' := unforgeChallenger (ofBase (B.atBase sp ω) PS' adm) n (SideOracle.none _) keys Q)
    (PMF.pure ())
    (fun _ => unforgeRelayAt (n := n) hPS adm) (coinsAt hPS Q) (fun s c' => ?_)
    (fun s c' => ?_) rfl (fun _ _ => (unforgeReqAt adm).injective) h _
    (fun p => Forges (S := ofBase (B.atBase sp ω) PS' adm) keys h
      (outAt (sp := sp) (ω := ω) hPS p.1) p.2)
    (fun s o hist hist' hE hh => ?_)).trans_eq ?_
  · cases s
    show PMF.uniformOfFintype (Fin Q → B.Coins × PS.Coins) _ =
      PMF.pure () () * PMF.uniformOfFintype (Fin Q → B.Coins × PS'.Coins) c'
    have hcard : Fintype.card (Fin Q → B.Coins × PS.Coins) =
        Fintype.card (Fin Q → B.Coins × PS'.Coins) :=
      Fintype.card_congr ((coinsAt hPS Q).trans (Equiv.punitProd _))
    rw [PMF.pure_apply_self, one_mul]
    exact (PMF.uniformOfFintype_apply _).trans ((congrArg (fun k : ℕ => (k : ℝ≥0∞)⁻¹) hcard).trans
      (PMF.uniformOfFintype_apply (α := Fin Q → B.Coins × PS'.Coins) c').symm)
  · cases s
    exact relaysChallenger_unforgeRelayAt hPS adm hB keys Q c'
  · refine ⟨?_, hE.fresh.atBase adm (by rw [hh, relayList_unforgeRelayAt])⟩
    have hv := hE.verify_eq
    change PS.verify (join sp ω h) _ _ = true at hv
    rw [hPS.verify_eq] at hv
    exact hv
  · refine Eq.trans ?_ (congrArg (fun μ => PMF.toOuterMeasure μ _)
      (QueryBoundedAdversary.transcriptLaw_mapOut _ (outAt hPS) _ h).symm)
    refine Eq.trans ?_ (PMF.toOuterMeasure_map_apply _ _ _).symm
    congr 1
    ext x
    rcases x with _ | ⟨o, hist⟩
    · exact ⟨fun ⟨p, hp, _⟩ => (by cases hp), fun ⟨p, hp, _⟩ => (by cases hp)⟩
    · exact ⟨fun ⟨p, hp, hf⟩ => (by cases hp; exact ⟨_, rfl, hf⟩),
        fun ⟨p, hp, hf⟩ => (by cases hp; exact ⟨_, rfl, hf⟩)⟩

variable [Nonempty TB.KeyCoins]

/-- **The unforgeability game as an average over the base component** (module docstring): for a
base signer reading only the base component (`hB`) and a proof system that is `PS' ω` at each
base component `ω` (`hPS`), the forgery probability of an adversary of BKM06 Definition 7 with `Q`
requests is at most the average over a uniform base component `ω` of the forgery probability of
the adversary at `ω` in the game for `ofBase (B.atBase sp ω) (PS' ω) adm`. -/
theorem insiderForgeProb_le_tsum_restrictAt [Nonempty Y₁] (hB : B.ReadsOnly (base sp))
    {TPS' : (X → Y₁) → PSTypes} [∀ ω, Fintype (TPS' ω).Proof] [∀ ω, DecidableEq (TPS' ω).Proof]
    [∀ ω, Fintype (TPS' ω).Coins] [∀ ω, DecidableEq (TPS' ω).Coins] [∀ ω, Nonempty (TPS' ω).Coins]
    {PS' : (ω : X → Y₁) → ProofSystem X Y₂ (RingStmt (B.atBase sp ω)) (RingWit (B.atBase sp ω)) (TPS' ω)}
    (hPS : ∀ ω, PS.AtBase sp ω (PS' ω))
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly X Y) t) (Q : ℕ) :
    insiderForgeProb A Q ≤ ∑' ω, PMF.uniformOfFintype (X → Y₁) ω *
      insiderForgeProb (InsiderAdversary.restrictAt (hPS ω) adm A) Q := by
  simp only [insiderForgeProb, forgeProb_eq_tsum]
  calc _ ≤ ∑' keys, PMF.uniformOfFintype (Fin n → (ofBase B PS adm).KeyCoins) keys *
        ∑' ω, PMF.uniformOfFintype (X → Y₁) ω * ∑' h, PMF.uniformOfFintype (X → Y₂) h *
          ((InsiderAdversary.restrictAt (hPS ω) adm A
            (fun i => (ofBase B PS adm).pk (keys i), ())).transcriptLaw
            (unforgeChallenger (ofBase (B.atBase sp ω) (PS' ω) adm) n (SideOracle.none _) keys Q)
            h).toOuterMeasure
            {x | ∃ p ∈ x, Forges (S := ofBase (B.atBase sp ω) (PS' ω) adm) keys h p.1 p.2} := by
        refine ENNReal.tsum_le_tsum fun keys => mul_le_mul_of_nonneg_left ?_ zero_le
        rw [tsum_uniform_split sp]
        exact ENNReal.tsum_le_tsum fun ω => mul_le_mul_of_nonneg_left (ENNReal.tsum_le_tsum fun h =>
          mul_le_mul_of_nonneg_left (toOuterMeasure_forges_join_le (hPS ω) adm hB A keys Q h)
            zero_le) zero_le
    _ = _ := by
        simp only [← ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun ω => tsum_congr fun keys => tsum_congr fun h => ?_
        exact mul_left_comm _ _ _

end Game

end RingSignature


/-! ### The split spBCS proof system -/

namespace Ring

open GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.IOP

section SPBCS

variable {k kN kS L e N : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁]
  (sp : OracleSplit Y Y₁ (XOut k e)) {TB : BaseTypes}
  {B : BaseSigner (Bits (queryBits k kN kS L)) Y N TB}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {X₀ Wit₀ : Type}
  (M : SPBCS Mg P X₀ k kN kS L e) (Λ : SiteLayout Mg) {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] (E : (j : ι) → (M.comp j).Encoder)
  {Vr : X₀ → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  (hb : M.FormatBounds Qs b b) {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
  (honest : Wit₀ → R → CausalProver P τ X₀)
  (stmtProg : RingSignature.RingStmt B → OracleProg (Bits (queryBits k kN kS L)) Y₁ X₀) (qS : ℕ)
  (hS : ∀ x, (stmtProg x).QueriesLE qS) (check : RingSignature.RingStmt B → Bool)
  (input : RingSignature.RingStmt B → RingSignature.RingWit B → Option Wit₀)

/-- **The split spBCS proof system at the base component `ω`**: the spBCS proof system read at
ring statements of the base signer at `ω`, at the program statements `(stmtProg x).run ω`, with
`check` and `input` read through `atBaseStmt` and `atBaseWit`. -/
noncomputable abbrev spbcsSplitAt (ω : Bits (queryBits k kN kS L) → Y₁) :
    ProofSystem (Bits (queryBits k kN kS L)) (XOut k e) (RingSignature.RingStmt (B.atBase sp ω)) (RingSignature.RingWit (B.atBase sp ω))
      (spbcsPST M b R) :=
  spbcsComapProofSystem M Λ E hb honest (fun x => (stmtProg (B.atBaseStmt sp ω x)).run ω)
    (fun x => check (B.atBaseStmt sp ω x))
    (fun x w => input (B.atBaseStmt sp ω x) (B.atBaseWit sp ω w))

/-- **The split spBCS proof system read at the base component `ω` is `spbcsSplitAt`**, with the
same coins and proofs: at `join sp ω h` its prover runs the statement program at `ω` and the
compiled prover at `h`, and its verifier checks the claim at the program statement
`(stmtProg x).run ω` against `h`. -/
noncomputable def atBase_spbcsSplitProofSystem (ω : Bits (queryBits k kN kS L) → Y₁) :
    (spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input).AtBase sp ω
      (spbcsSplitAt sp M Λ E hb honest stmtProg check input ω) where
  coinsEquiv := Equiv.refl _
  proofEquiv := Equiv.refl _
  run_prove x w c h := by
    have hin : input (B.atBaseStmt sp ω ((B.atBaseStmt sp ω).symm x))
        (B.atBaseWit sp ω ((B.atBaseWit sp ω).symm w)) = input x w := by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rcases hy : input x w with _ | y
    · change (((stmtProg x).mapQuery id fun y => (sp y).1).bind fun x₀ =>
        (input x w).elim (.pure none) fun y =>
          ((splitNIProver M Λ E hb honest).prog x₀ y c).mapQuery id fun y => (sp y).2).run
          (join sp ω h) = ((input (B.atBaseStmt sp ω ((B.atBaseStmt sp ω).symm x))
            (B.atBaseWit sp ω ((B.atBaseWit sp ω).symm w))).elim (.pure none) fun y =>
              (splitNIProver M Λ E hb honest).prog
                ((stmtProg (B.atBaseStmt sp ω ((B.atBaseStmt sp ω).symm x))).run ω) y c).run h
      rw [hin, hy, OracleProg.run_bind]
      rfl
    · refine (run_prove_spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input
        (join sp ω h) x w hy c).trans ?_
      change _ = ((input (B.atBaseStmt sp ω ((B.atBaseStmt sp ω).symm x))
            (B.atBaseWit sp ω ((B.atBaseWit sp ω).symm w))).elim (.pure none) fun y =>
              (splitNIProver M Λ E hb honest).prog
                ((stmtProg (B.atBaseStmt sp ω ((B.atBaseStmt sp ω).symm x))).run ω) y c).run h
      rw [hin, hy, base_join, prf_join, Equiv.apply_symm_apply]
      rfl
  verify_eq h x π := by
    refine Bool.eq_iff_iff.2 ((verify_spbcsSplitProofSystem_eq_true_iff sp M Λ E hb honest
      stmtProg qS hS check input (join sp ω h) x π).trans (Iff.trans ?_
        (verify_spbcsComapProofSystem_eq_true_iff M Λ E hb honest _ _ _ h _ π).symm))
    rw [base_join, prf_join]
    rfl

variable [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins]
  [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins]

variable [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  {n t : ℕ} [NeZero n] (adm : KeyRing B.PK N → Prop) [DecidablePred adm]

/-- **The unforgeability game with the split spBCS proof system as an average over the base
component**: for a base signer reading only the base component (`hB`), the forgery probability
of an adversary of BKM06 Definition 7 for `ofBase B (spbcsSplitProofSystem …) adm` with `Q`
requests is at most the average over a uniform base component `ω` of the forgery probability of
the adversary at `ω` in the game for `ofBase (B.atBase sp ω) (spbcsSplitAt … ω) adm`, a ring
signature with an oracle-free base signer and the spBCS proof system at the program statements
`(stmtProg x).run ω`. -/
theorem insiderForgeProb_le_tsum_restrictAt_spbcsSplit (hB : B.ReadsOnly (base sp))
    (A : InsiderAdversary (ofBase B (spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check
      input) adm) n (OracleView.queriesOnly _ _) t) (Q : ℕ) :
    insiderForgeProb A Q ≤ ∑' ω, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → Y₁) ω *
      insiderForgeProb (InsiderAdversary.restrictAt
        (atBase_spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input ω) adm A) Q :=
  insiderForgeProb_le_tsum_restrictAt adm hB
    (atBase_spbcsSplitProofSystem sp M Λ E hb honest stmtProg qS hS check input) A Q

end SPBCS

end Ring

end GordieHowe
