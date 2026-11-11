-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingUnforgeability
public import GordieHowe.Model.Quantum.Interactive.AbsorbRelay
public import GordieHowe.Model.RingSignature.TranscriptAbsorb

@[expose] public section

/-!
# The prover's coins carried by the requests

The first step of the reduction from the unforgeability game of `ofBase B PS adm` with a side
oracle `SO` (BKM06 Definition 7 for `SideOracle.none`, the key-reuse game for `baseSide`) to
MU-EUF-CMA^corr by an explicit forger: the prover's coins of each ring-signing request leave the
challenger. The challenger of the game draws, for request number `j`, the base
signer's coins and the prover's coins; the adversary is absorbed (`Quantum.AdaptiveIAlg.absorb`)
through a relay that attaches to request number `j` the prover's coins `ρ j`, drawn outside, and
the numbered challenger (`numChallenger`) answers each request as the game's challenger answers it
with those prover's coins and its own base signer's coins. A relay of the requests to the
multi-user challenger then needs no request numbers: each request carries its prover's coins.

- `respond_unforgeChallenger_congr`: the game's challenger reads its coins only at the request's
  number and its history only through its length.
- `NumReq`, `numChallenger keys Q`: requests with the prover's coins, answered as the game's
  challenger answers them with the base signer's coins `b`.
- `numRelay Q ρ`: request number `j` sent with `ρ j`, the reply passed on.
- `relaysChallenger_numRelay`: the game's challenger at the coins `fun j => (b j, ρ j)` relays the
  numbered challenger at `b` through `numRelay Q ρ` (`Quantum.SideRelay.RelaysChallenger`).
- `coinZip`, `uniform_coinZip`: the game's coins as the prover's coins and the base signer's, with
  the uniform law the product of the uniform laws.
- `toOuterMeasure_outLaw_numRelay`: the game's run is the average, over the prover's coins, of the
  absorbed adversary's run against the numbered challenger.
- `map_snd_relayList`, `transcriptLaw_numRelay`: the same for transcripts, on every event of the
  output and the requests, the numbered requests read without their prover's coins.
-/

namespace GordieHowe.RingSignature

open Quantum
open scoped ENNReal

variable {X Y : Type} {N : ℕ}

/-- **The game's challenger reads its coins only at the request's number**, and its history only
through its length: two coin functions agreeing at the number of the request, and two histories of
the same length, give the same reply program. -/
theorem respond_unforgeChallenger_congr {TS : RingTypes} [DecidableEq TS.PK] [Fintype TS.SignCoins]
    [DecidableEq TS.SignCoins] [Nonempty TS.SignCoins] {S : RingScheme X Y N TS} {n : ℕ}
    {O : SideOracle S}
    (keys : Fin n → S.KeyCoins) (Q : ℕ) {ω ω' : Fin Q → S.SignCoins}
    {hist hist' : UnforgeHist n O} (hl : hist.length = hist'.length)
    (hω : ∀ h : hist.length < Q, ω ⟨hist.length, h⟩ = ω' ⟨hist.length, h⟩)
    (r : UnforgeRequest n O) :
    (unforgeChallenger S n O keys Q).respond ω hist r =
      (unforgeChallenger S n O keys Q).respond ω' hist' r := by
  simp only [unforgeChallenger]
  by_cases h : hist.length < Q
  · have h' : hist'.length < Q := hl ▸ h
    rw [dif_pos h, dif_pos h']
    have hc : ω' ⟨hist'.length, h'⟩ = ω ⟨hist.length, h⟩ := by
      rw [hω h]
      exact congrArg ω' (Fin.ext hl.symm)
    rcases r with i | ⟨s, R, m⟩ | ⟨i, bm⟩ <;> simp only [hc]
  · rw [dif_neg h, dif_neg (hl ▸ h)]

variable {TB : BaseTypes} [DecidableEq TB.PK]
  {B : BaseSigner X Y N TB}
  {TPS : PSTypes} {PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {n : ℕ} {SO : SideOracle (ofBase B PS adm)}

variable [Fintype SO.BMsg] [DecidableEq SO.BMsg] [Fintype SO.BSig] [DecidableEq SO.BSig]

variable [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins]

variable (B PS adm n SO) in
/-- The requests of the unforgeability game of `ofBase B PS adm` with the side oracle `SO`. -/
abbrev RReq : Type := UnforgeRequest (S := ofBase B PS adm) n SO

variable (B PS adm SO) in
/-- The replies of the unforgeability game of `ofBase B PS adm` with the side oracle `SO`. -/
abbrev RResp : Type := UnforgeResponse SO

variable (B PS adm n SO) in
/-- **A request with the prover's coins.** -/
abbrev NumReq : Type := PS.Coins × RReq B PS adm n SO

section Coins

variable [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins]

variable (B PS adm n SO) in
/-- **The numbered challenger** at the users' key coins `keys`, answering `Q` requests: a request
`(ρ', r)` after the history `hist` is answered as the game's challenger answers `r` with the base
signer's coins `b` of the request's number and the prover's coins `ρ'`. -/
noncomputable def numChallenger (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    Challenger X Y (NumReq B PS adm n SO) (RResp B PS adm SO) where
  Coins := Fin Q → B.Coins
  coins := PMF.uniformOfFintype _
  Q := Q
  q := max (ofBase B PS adm).q SO.q
  respond b hist r :=
    (unforgeChallenger (ofBase B PS adm) n SO keys Q).respond
      (fun j => (b j, r.1)) (hist.map fun e => ⟨e.request.2, e.response⟩) r.2
  respond_queries _ _ r H :=
    (unforgeChallenger (ofBase B PS adm) n SO keys Q).respond_queries _ _ r.2 H

omit [Fintype TPS.Coins] [DecidableEq TPS.Coins] in
variable (B PS adm n SO) in
/-- **The relay attaching the prover's coins**: request number `j` with request `r` is sent as
`(ρ j, r)` (an arbitrary coin from the number `Q` on), and the numbered challenger's reply is passed
on. -/
noncomputable def numRelay (Q : ℕ) (ρ : Fin Q → PS.Coins) :
    SideRelay (RReq B PS adm n SO) (RResp B PS adm SO) (NumReq B PS adm n SO)
      (RResp B PS adm SO) where
  route c r := (if h : c < Q then ρ ⟨c, h⟩ else Classical.arbitrary _, r)
  answer _ _ a := a

omit [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Fintype SO.BMsg]
  [DecidableEq SO.BMsg] [Fintype SO.BSig] [DecidableEq SO.BSig] in
/-- The relay of a request number is injective. -/
theorem numRelay_route_injective (Q : ℕ) (ρ : Fin Q → PS.Coins) (c : ℕ) :
    Function.Injective ((numRelay B PS adm n SO Q ρ).route c) :=
  fun _ _ h => congrArg Prod.snd h

omit [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Fintype SO.BMsg] [DecidableEq SO.BMsg]
  [Fintype SO.BSig] [DecidableEq SO.BSig] in
/-- **The game's challenger at the coins `(b j, ρ j)` relays the numbered challenger at `b`**
through the relay attaching `ρ`: each request is answered as the numbered challenger answers it
with the prover's coins of its number. -/
theorem relaysChallenger_numRelay (keys : Fin n → B.KeyCoins) (Q : ℕ) (b : Fin Q → B.Coins)
    (ρ : Fin Q → PS.Coins) :
    (numRelay B PS adm n SO Q ρ).RelaysChallenger
      (unforgeChallenger (ofBase B PS adm) n SO keys Q) (fun j => (b j, ρ j))
      (numChallenger B PS adm n SO keys Q) b where
  Q_eq := rfl
  run_eq hist hist' r G hrel hlt := by
    have hl : hist.length = (hist'.map fun e :
        HistoryEntry (NumReq B PS adm n SO) (RResp B PS adm SO) =>
        (⟨e.request.2, e.response⟩ :
          HistoryEntry (RReq B PS adm n SO) (RResp B PS adm SO))).length := by
      have := congrArg List.length hrel
      simpa using this.symm
    have h := respond_unforgeChallenger_congr (S := ofBase B PS adm) (O := SO) keys Q
      (ω := fun j => (b j, ρ j)) hl (ω' := fun j => (b j,
        ((numRelay B PS adm n SO Q ρ).route hist.length r).1))
        (fun h => by simp only [numRelay, dif_pos h]) r
    exact (congrArg (fun p => p.run G) h).trans rfl
  answer_none _ _ _ := rfl

end Coins

variable (B PS) in
/-- **The game's coins as the prover's coins and the base signer's coins.** -/
def coinZip (Q : ℕ) : (Fin Q → B.Coins × PS.Coins) ≃ (Fin Q → PS.Coins) × (Fin Q → B.Coins) where
  toFun c := (fun j => (c j).2, fun j => (c j).1)
  invFun p := fun j => (p.2 j, p.1 j)
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidablePred adm] [DecidableEq TB.PK] [DecidableEq TB.Coins] [Fintype TB.PK] [Fintype TB.Msg]
  [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins]
  [DecidableEq TB.KeyCoins] in
/-- **The uniform game's coins are the product of the uniform prover's coins and the uniform base
signer's coins.** -/
theorem uniform_coinZip [Fintype TPS.Coins] [Nonempty TPS.Coins] (Q : ℕ) (ρ : Fin Q → PS.Coins) (b : Fin Q → B.Coins) :
    PMF.uniformOfFintype (Fin Q → B.Coins × PS.Coins) ((coinZip B PS Q).symm (ρ, b)) =
      PMF.uniformOfFintype (Fin Q → PS.Coins) ρ * PMF.uniformOfFintype (Fin Q → B.Coins) b := by
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
    mul_pow, Nat.cast_mul, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
      (Or.inl (ENNReal.natCast_ne_top _))]
  ring

/-! ### The game as an average over the prover's coins -/

variable [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y] [NeZero n] [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins]
  [DecidableEq TPS.Coins] [Nonempty TPS.Coins]

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] in
/-- A request with the prover's coins, as the default request of the numbered challenger. -/
noncomputable instance : Inhabited (NumReq B PS adm n SO) := ⟨(Classical.arbitrary _, .corrupt 0)⟩

/-- **The game's run is the average, over the prover's coins, of the absorbed adversary's run
against the numbered challenger** (`Quantum.AdaptiveIAlg.outLaw_absorb`): for every event `P` of the
adversary's registers and its logs, the probability under the game's challenger at the users' key
coins is the average over uniform prover's coins `ρ` of the probability that the adversary
absorbed through `numRelay Q ρ` runs against the numbered challenger with registers and logs (read
off the absorbed adversary) in `P`. -/
theorem toOuterMeasure_outLaw_numRelay {O : Type}
    {shA : AlgShape X Y (RReq B PS adm n SO) (RResp B PS adm SO)} (A : AdaptiveIAlg shA O) (keys : Fin n → B.KeyCoins)
    (Q : ℕ) (H : X → Y)
    (P : DReg A.toKindAlg.W A.width X Y (RReq B PS adm n SO) (RResp B PS adm SO) →
      LogReg (RReq B PS adm n SO) A.slots → Prop) :
    ((A.toKindAlg.composeBothOut (unforgeChallenger (ofBase B PS adm) n SO keys Q)
        id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P v.adv v.chal.logs} =
      ∑ ρ, PMF.uniformOfFintype (Fin Q → PS.Coins) ρ *
        (((A.absorb (numRelay B PS adm n SO Q ρ)).toKindAlg.composeBothOut
          (numChallenger B PS adm n SO keys Q) id).outLaw H).toOuterMeasure
          {o | ∃ v ∈ o, P (A.absorbedAdv (numRelay B PS adm n SO Q ρ) v.adv) v.adv.1.1.1.logs} :=
  A.outLaw_absorb (C := unforgeChallenger (ofBase B PS adm) n SO keys Q)
    (C' := numChallenger B PS adm n SO keys Q) (PMF.uniformOfFintype _)
    (fun ρ => numRelay B PS adm n SO Q ρ) (coinZip B PS Q)
    (fun ρ b => uniform_coinZip Q ρ b)
    (fun H ρ b => (relaysChallenger_numRelay keys Q b ρ).relays H A.slots)
    (fun ρ c => numRelay_route_injective Q ρ c) H (fun v lg _ _ _ => P v lg)

/-! ### The transcripts -/

omit [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y] [Nonempty Y]
  [NeZero n] [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Pub] [DecidableEq TB.Pub]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] [Fintype SO.BMsg] [DecidableEq SO.BMsg] [Fintype SO.BSig]
  [DecidableEq SO.BSig] in
/-- **The relayed requests read without the prover's coins** are the requests. -/
theorem map_snd_relayList (Q : ℕ) (ρ : Fin Q → PS.Coins) (rs : List (RReq B PS adm n SO)) :
    ((numRelay B PS adm n SO Q ρ).relayList rs).map Prod.snd = rs := by
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs r ih =>
    rw [SideRelay.relayList_append_singleton, List.map_append, ih]
    rfl

/-- **The transcripts of the game are the average, over the prover's coins, of the transcripts of
the absorbed adversary against the numbered challenger**, on every event `E` of the output and the
requests of the history; the numbered requests read without their prover's coins. -/
theorem transcriptLaw_numRelay {O : Type} {t : ℕ}
    (𝒜 : QueryBoundedAdversary X Y (RReq B PS adm n SO) (RResp B PS adm SO) O t)
    (keys : Fin n → B.KeyCoins) (Q : ℕ) (H : X → Y) (E : O → List (RReq B PS adm n SO) → Prop) :
    (𝒜.transcriptLaw (unforgeChallenger (ofBase B PS adm) n SO keys Q)
        H).toOuterMeasure {x | ∃ p ∈ x, E p.1 (p.2.map HistoryEntry.request)} =
      ∑ ρ, PMF.uniformOfFintype (Fin Q → PS.Coins) ρ *
        ((𝒜.absorbQB (numRelay B PS adm n SO Q ρ) (numRelay_route_injective Q ρ)).transcriptLaw
          (numChallenger B PS adm n SO keys Q) H).toOuterMeasure
          {x | ∃ p ∈ x, E p.1 ((p.2.map HistoryEntry.request).map Prod.snd)} := by
  simp only [QueryBoundedAdversary.transcriptLaw, PMF.toOuterMeasure_bind_apply]
  have key : ∀ a, 𝒜.aux a * ((((𝒜.alg a).toKindAlg.composeBothOut
      (unforgeChallenger (ofBase B PS adm) n SO keys Q) fun v =>
        ((𝒜.alg a).output (unforgeChallenger (ofBase B PS adm) n SO keys Q) v,
          (𝒜.alg a).history (unforgeChallenger (ofBase B PS adm) n SO keys Q)
            v)).outLaw
        H).toOuterMeasure {x | ∃ p ∈ x, E p.1 (p.2.map HistoryEntry.request)}) =
      ∑ ρ, PMF.uniformOfFintype (Fin Q → PS.Coins) ρ * (𝒜.aux a *
        (((((𝒜.alg a).absorb (numRelay B PS adm n SO Q ρ)).toKindAlg.composeBothOut
          (numChallenger B PS adm n SO keys Q) fun v =>
            (((𝒜.alg a).absorb (numRelay B PS adm n SO Q ρ)).output
              (numChallenger B PS adm n SO keys Q) v,
              ((𝒜.alg a).absorb (numRelay B PS adm n SO Q ρ)).history
                (numChallenger B PS adm n SO keys Q)
                v)).outLaw H).toOuterMeasure
          {x | ∃ p ∈ x, E p.1 ((p.2.map HistoryEntry.request).map Prod.snd)})) := by
    intro a
    simp only [mul_left_comm _ (𝒜.aux a), ← Finset.mul_sum]
    congr 1
    rw [KindAlg.toOuterMeasure_outLaw_composeBothOut]
    refine (Eq.trans ?_ ((𝒜.alg a).outLaw_absorb
      (C := unforgeChallenger (ofBase B PS adm) n SO keys Q)
      (C' := numChallenger B PS adm n SO keys Q) (PMF.uniformOfFintype _)
      (fun ρ => numRelay B PS adm n SO Q ρ) (coinZip B PS Q)
      (fun ρ b => uniform_coinZip Q ρ b)
      (fun H ρ b => (relaysChallenger_numRelay keys Q b ρ).relays H (𝒜.alg a).slots)
      (fun ρ c => numRelay_route_injective Q ρ c) H
      (fun d _ rlg _ _ => E ((𝒜.alg a).out d.1.1.1) (((requests rlg).take Q).map Prod.snd)))).trans
      ?_
    · congr 1
      ext o
      refine exists_congr fun v => and_congr_right fun _ => ?_
      rw [AdaptiveIAlg.map_request_history, SideRelay.requests_logs, List.map_take,
        map_snd_relayList]
      rfl
    · refine Finset.sum_congr rfl fun ρ _ => congrArg _ ?_
      refine Eq.trans ?_ (KindAlg.toOuterMeasure_outLaw_composeBothOut _ _ _ H _).symm
      refine congrArg _ (Set.ext fun o => exists_congr fun v => and_congr_right fun _ => ?_)
      dsimp only
      rw [AdaptiveIAlg.map_request_history ((𝒜.alg a).absorb (numRelay B PS adm n SO Q ρ))
        (numChallenger B PS adm n SO keys Q) v]
      rfl
  calc _ = ∑' a, ∑ ρ, PMF.uniformOfFintype (Fin Q → PS.Coins) ρ * (𝒜.aux a *
        (((((𝒜.alg a).absorb (numRelay B PS adm n SO Q ρ)).toKindAlg.composeBothOut
          (numChallenger B PS adm n SO keys Q) fun v =>
            (((𝒜.alg a).absorb (numRelay B PS adm n SO Q ρ)).output
              (numChallenger B PS adm n SO keys Q) v,
              ((𝒜.alg a).absorb (numRelay B PS adm n SO Q ρ)).history
                (numChallenger B PS adm n SO keys Q)
                v)).outLaw H).toOuterMeasure
          {x | ∃ p ∈ x, E p.1 ((p.2.map HistoryEntry.request).map Prod.snd)})) := tsum_congr key
    _ = _ := by
      rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [ENNReal.tsum_mul_left]
      rfl

end GordieHowe.RingSignature
