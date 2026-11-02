-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingForgerMU
public import GordieHowe.Model.RingSignature.KeyReuse

@[expose] public section

/-!
# The numbered requests of the key-reuse game relayed to the multi-user challenger

The key-reuse game of `ofBase B PS adm` (`GordieHowe/Model/RingSignature/KeyReuse.lean`, the
unforgeability game with the base scheme's ordinary signer `baseSide` as its side oracle) relayed
to the multi-user challenger with the ring-aware and the ordinary signing oracle
(`Signature.SignOracle.ringStd B`), as `GordieHowe/Applications/Ring/RingForgerMU.lean` relays BKM06
Definition 7 to the ring-aware one. A corruption is asked as a corruption; a ring-signing request
`(ρ, (s, R, m))` by a member of a supported ring is asked as the signing request of user `s` on
`inl (R, m)`, the ring signature computed by the relay from the base signature; an ordinary
signing request `sideSign i bm` is asked as the signing request of user `i` on `inr bm`, its reply
passed on. One main request and `qPub + PS.q` queries per request.

- `ringReplyStd`: the game's reply to a request at given coins and oracle.
  `numChallenger_noAssign_std`, `answerAfter_numChallenger_std`.
- `relayRingSignStd`, `forgerProgStd`, `forgerRelayStd pks i₁`: the relay programs.
- `ForgerAskStd`, `asksIn_forgerProgStd`, `runsWith_forgerProgStd`,
  `relaysChallenger_forgerRelayStd`: the main requests, the runs and the relay of the numbered
  challenger by the multi-user challenger.
- `RingFreshReqStd`, `Fresh.ringFreshReqStd`, `muFreshReq_of_relayStd`: freshness read from the
  requests, and through the relay for a ring-binding base message.
- `relayedForgerStd`, `keyReuseForgeProb_le_relayedForgerStd`: the game's forgery probability is
  at most the average, over the users' key coins, the oracle and the prover's coins, of the
  probability that the relayed forger outputs a verifying ring signature fresh for its multi-user
  requests.
-/

namespace GordieHowe.RingSignature

open Quantum Signature
open scoped ENNReal

variable {X Y : Type} {N : ℕ} {TB : BaseTypes} {B : BaseSigner X Y N TB} {TPS : PSTypes} {PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {n : ℕ}

/-! ### The game's replies -/

variable (B PS adm) in
/-- **The key-reuse game's reply to a request** at the users' key coins `keys`, the oracle `H` and
the request's coins `c`: as `ringReply`, and the base signer's ordinary signature for an ordinary
signing request. -/
noncomputable def ringReplyStd (keys : Fin n → B.KeyCoins) (H : X → Y) (c : B.Coins × PS.Coins) :
    RReq B PS adm n (baseSide B PS adm) → Option (RResp B PS adm (baseSide B PS adm))
  | .corrupt i => some (.keyCoins (keys i))
  | .sign s R m => if (ofBase B PS adm).pk (keys s) ∈ R.1 then
      (((ofBase B PS adm).sign ((ofBase B PS adm).keyGen (keys s)) R m c).run H).map .signature
    else none
  | .sideSign i bm =>
      (((baseSide B PS adm).sign ((ofBase B PS adm).keyGen (keys i)) bm c).run H).map
        .sideSignature

/-- **The game's reply to a member's request on a supported ring** is `signAt` at the member's
first position. -/
theorem ringReplyStd_sign_of_mem (keys : Fin n → B.KeyCoins) (H : X → Y) (c : B.Coins × PS.Coins)
    {s : Fin n} {R : KeyRing (ofBase B PS adm).PK N} {m : (ofBase B PS adm).Msg}
    (hm : B.pk (keys s) ∈ R.1) (ha : adm R) :
    ringReplyStd B PS adm keys H c (.sign s R m) =
      ((signAt B PS (B.pk (keys s)) (B.keyGen (keys s)).2 R (R.1.idxOf (B.pk (keys s))) m c).run
        H).map fun x => (.signature x : RResp B PS adm (baseSide B PS adm)) := by
  have hm' : ((ofBase B PS adm).keyGen (keys s)).1 ∈ R.1 := hm
  simp only [ringReplyStd]
  split_ifs with h
  · exact congrArg _ (congrArg (fun p => OracleProg.run H p)
      (sign_ofBase_of_mem B PS adm (kp := (ofBase B PS adm).keyGen (keys s)) hm' ha m c))
  · exact absurd hm h

/-- **The game refuses a request off a supported ring holding the member's key.** -/
theorem ringReplyStd_sign_of_not (keys : Fin n → B.KeyCoins) (H : X → Y) (c : B.Coins × PS.Coins)
    {s : Fin n} {R : KeyRing (ofBase B PS adm).PK N} {m : (ofBase B PS adm).Msg}
    (hc : ¬ (B.pk (keys s) ∈ R.1 ∧ adm R)) :
    ringReplyStd B PS adm keys H c (.sign s R m) = none := by
  simp only [ringReplyStd]
  split_ifs with hm
  · have ha : ¬ adm R := fun h => hc ⟨hm, h⟩
    have hs : (ofBase B PS adm).sign ((ofBase B PS adm).keyGen (keys s)) R m c = .pure none := by
      simp only [ofBase_sign]
      split_ifs with h'
      · exact absurd h'.2 ha
      · rfl
    rw [hs]
    rfl
  · rfl

/-- **The numbered challenger of the key-reuse game never reprograms.** -/
theorem numChallenger_noAssign_std [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [AddGroup Y] (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    (numChallenger B PS adm n (baseSide B PS adm) keys Q).NoAssign := by
  intro c hist r G
  obtain ⟨ρ, r⟩ := r
  change (((unforgeChallenger (ofBase B PS adm) n (baseSide B PS adm) keys Q).respond
    (fun j => (c j, ρ)) _ r).run G).assignments = []
  simp only [unforgeChallenger]
  split_ifs
  · rcases r with i | ⟨s, R, m⟩ | ⟨i, bm⟩
    · rfl
    · dsimp only
      split_ifs
      · simp [OracleProg.run_bind]
      · rfl
    · simp [OracleProg.run_bind]
  · rfl

/-- **The numbered challenger's reply** to a request numbered below `Q` is the game's reply with
the base signer's coins of that number and the request's prover's coins. -/
theorem answerAfter_numChallenger_std [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [AddGroup Y] [Nonempty Y] (keys : Fin n → B.KeyCoins) (Q : ℕ) (H : X → Y)
    (b : Fin Q → B.Coins) (rs : List (NumReq B PS adm n (baseSide B PS adm)))
    (r : NumReq B PS adm n (baseSide B PS adm)) (hi : rs.length < Q) :
    (numChallenger B PS adm n (baseSide B PS adm) keys Q).toPureEnv.answerAfter (H, b) rs r =
      ringReplyStd B PS adm keys H (b ⟨rs.length, hi⟩, r.1) r.2 := by
  have hn := numChallenger_noAssign_std (PS := PS) (adm := adm) keys Q
  obtain ⟨-, -, h3⟩ := hn.oracleIn H b rs
  rw [hn.answerAfter_eq H b rs r hi]
  have hl : ((numChallenger B PS adm n (baseSide B PS adm) keys Q).toPureEnv.oracleIn (H, b)
      rs).hist.length = rs.length := by
    rw [h3]
    exact min_eq_left (le_of_lt hi)
  generalize ((numChallenger B PS adm n (baseSide B PS adm) keys Q).toPureEnv.oracleIn (H, b)
    rs).hist = hist at hl ⊢
  obtain ⟨ρ, r⟩ := r
  have hl' : (hist.map fun e :
      HistoryEntry (NumReq B PS adm n (baseSide B PS adm)) (RResp B PS adm (baseSide B PS adm)) =>
      (⟨e.request.2, e.response⟩ :
        HistoryEntry (RReq B PS adm n (baseSide B PS adm))
          (RResp B PS adm (baseSide B PS adm)))).length < Q := by simpa [hl] using hi
  change (((unforgeChallenger (ofBase B PS adm) n (baseSide B PS adm) keys Q).respond
    (fun j => (b j, ρ)) _ r).run H).response = _
  have hf : (⟨(hist.map fun e :
      HistoryEntry (NumReq B PS adm n (baseSide B PS adm)) (RResp B PS adm (baseSide B PS adm)) =>
      (⟨e.request.2, e.response⟩ :
        HistoryEntry (RReq B PS adm n (baseSide B PS adm))
          (RResp B PS adm (baseSide B PS adm)))).length, hl'⟩ :
      Fin Q) = ⟨rs.length, hi⟩ := Fin.ext (by simpa using hl)
  simp only [unforgeChallenger, dif_pos hl', hf]
  rcases r with i | ⟨s, R, m⟩ | ⟨i, bm⟩
  · rfl
  · simp only [ringReplyStd]
    split_ifs
    · simp [OracleProg.run_bind]
    · rfl
  · simp [ringReplyStd, OracleProg.run_bind]

/-! ### The relay programs -/

section Programs

variable [Zero Y]

/-- **The relayed ring signing** by user `s` on `(R, m)` with the prover's coins `ρ`, with the
users' public keys `pks`: the signing request of user `s` on `inl (R, m)` asked of the multi-user
challenger, then, for a base signature `σ`, its public value `y` and the honest proof of
`(R, m, y)` with the witness at the first position of `pks s`, as relay queries. -/
def relayRingSignStd (pks : Fin n → B.PK) (ρ : PS.Coins) (s : Fin n) (R : KeyRing B.PK N)
    (m : B.Msg) :
    OracleProg (X ⊕ MURequest (SignOracle.ringStd B) n) (Y ⊕ Option (MUResponse B))
      (Option (RResp B PS adm (baseSide B PS adm))) :=
  (askResp (.sign s (.inl (R, m)))).bind fun
    | some (.signature σ) => (MultiRelay.liftQ (B.pub (pks s) σ)).bind fun y =>
        (MultiRelay.liftQ (PS.prove ⟨R, m, y⟩ ⟨R.1.idxOf (pks s), σ⟩ ρ)).mapOutput fun π =>
          some (.signature ((y, π) : B.Pub × PS.Proof))
    | _ => .pure none

open Classical in
variable (B PS adm) in
/-- **The relay program of a request of the key-reuse game with its prover's coins**: a
corruption asked as it is; a ring-signing request by a member of a supported ring relayed by
`relayRingSignStd`; the other ring-signing requests refused without a request; an ordinary
signing request asked as the signing request on `inr bm`, its signature passed on. -/
noncomputable def forgerProgStd (pks : Fin n → B.PK) :
    NumReq B PS adm n (baseSide B PS adm) → OracleProg (X ⊕ MURequest (SignOracle.ringStd B) n)
      (Y ⊕ Option (MUResponse B)) (Option (RResp B PS adm (baseSide B PS adm)))
  | (_, .corrupt i) => (askResp (.corrupt i)).mapOutput fun
      | some (.keyCoins kc) => some (.keyCoins kc)
      | _ => none
  | (ρ, .sign s R m) => if pks s ∈ R.1 ∧ adm R then relayRingSignStd pks ρ s R m else .pure none
  | (_, .sideSign i bm) => (askResp (.sign i (.inr bm))).mapOutput fun
      | some (.signature σ) => some (.sideSignature σ)
      | _ => none

variable (B PS adm) in
/-- **The relay of the key-reuse game's numbered requests to the multi-user challenger**: the
programs `forgerProgStd pks`, one main request and `qPub + PS.q` queries per request, the idle
request the public key of user `i₁`. -/
noncomputable def forgerRelayStd (pks : Fin n → B.PK) (i₁ : Fin n) :
    MultiRelay X Y (NumReq B PS adm n (baseSide B PS adm)) (RResp B PS adm (baseSide B PS adm))
      (MURequest (SignOracle.ringStd B) n) (MUResponse B) where
  prog := MultiRelay.plainProg (forgerProgStd B PS adm pks)
  K := 1
  K_pos := Nat.one_pos
  qR := B.qPub + PS.q
  idle := .publicKey i₁

end Programs

/-! ### The main requests of the relay -/

variable (B PS adm) in
/-- **The main request a numbered request of the key-reuse game relays to**: the same corruption,
the signing request of the same user on `inl (R, m)`, or on `inr bm`. -/
def ForgerAskStd :
    NumReq B PS adm n (baseSide B PS adm) → MURequest (SignOracle.ringStd B) n → Prop
  | (_, .corrupt i), r' => r' = .corrupt i
  | (_, .sign s R m), r' => r' = .sign s (.inl (R, m))
  | (_, .sideSign i bm), r' => r' = .sign i (.inr bm)

/-- **Every main request of a relay program is one its request relays to.** -/
theorem asksIn_forgerProgStd [Zero Y] (pks : Fin n → B.PK)
    (r : NumReq B PS adm n (baseSide B PS adm)) :
    MultiRelay.AsksIn (MUResponse B) (forgerProgStd B PS adm pks r) (ForgerAskStd B PS adm r) := by
  obtain ⟨ρ, r⟩ := r
  rcases r with i | ⟨s, R, m⟩ | ⟨i, bm⟩
  · exact (asksIn_askResp _).mapOutput _
  · simp only [forgerProgStd]
    split_ifs
    · refine MultiRelay.AsksIn.bind (asksIn_askResp _) fun o => ?_
      rcases o with _ | ⟨_⟩ | ⟨σ⟩ | ⟨_⟩
      · exact MultiRelay.AsksIn.pure _ _
      · exact MultiRelay.AsksIn.pure _ _
      · exact MultiRelay.AsksIn.bind (MultiRelay.AsksIn.liftQ _ _) fun y =>
          (MultiRelay.AsksIn.liftQ _ _).mapOutput _
      · exact MultiRelay.AsksIn.pure _ _
    · exact MultiRelay.AsksIn.pure _ _
  · exact (asksIn_askResp _).mapOutput _

/-! ### The relayed requests against the multi-user challenger -/

section Runs

variable [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y] (keys : Fin n → B.KeyCoins) (Q' : ℕ) (H : X → Y) (c' : Fin Q' → B.Coins)

/-- The multi-user challenger's replies, with the ring-aware and the ordinary signing oracle. -/
noncomputable abbrev ringStdMUAns : List (MURequest (SignOracle.ringStd B) n) →
    MURequest (SignOracle.ringStd B) n → Option (MUResponse B) :=
  (muChallenger (SignOracle.ringStd B) n keys Q').toPureEnv.answerAfter (H, c')

/-- **A relayed request runs with the game's reply**: the request `(ρ, r)`, after the main requests
`L` (fewer than `Q'`), runs with the game's reply at the coins `(c' |L|, ρ)`, at most one main
request and `qPub + PS.q` queries. -/
theorem runsWith_forgerProgStd (L : List (MURequest (SignOracle.ringStd B) n))
    (hL : L.length < Q') (r : NumReq B PS adm n (baseSide B PS adm)) :
    ∃ asks q, MultiRelay.RunsWith (ringStdMUAns keys Q' H c') H L
      (forgerProgStd B PS adm (fun i => B.pk (keys i)) r)
      (ringReplyStd B PS adm keys H (c' ⟨L.length, hL⟩, r.1) r.2) asks q ∧
      asks.length ≤ 1 ∧ q ≤ B.qPub + PS.q := by
  have hans := answerAfter_muChallenger (SignOracle.ringStd B) keys Q' H c' L
  obtain ⟨ρ, r⟩ := r
  rcases r with i | ⟨s, R, m⟩ | ⟨i, bm⟩
  · have h := (MultiRelay.RunsWith.query_inr (ansM := ringStdMUAns keys Q' H c') (H := H) (rs := L)
      (k := fun b => OracleProg.pure (b.elim (fun _ => none) id)) (.corrupt i)
      (MultiRelay.RunsWith.pure _ _)).mapOutput (fun
        | some (.keyCoins kc) => some (.keyCoins kc)
        | _ => none : Option (MUResponse B) → Option (RResp B PS adm (baseSide B PS adm)))
    refine ⟨_, _, h.congr_res ?_, by simp, Nat.zero_le _⟩
    simp only [Sum.elim_inr, id, ringStdMUAns, hans _ hL, muReply]
    rfl
  · simp only [forgerProgStd]
    by_cases hc : B.pk (keys s) ∈ R.1 ∧ adm R
    · rw [if_pos hc]
      have hq : MultiRelay.RunsWith (ringStdMUAns keys Q' H c') H L
          (askResp (Resp' := MUResponse B) (.sign s (.inl (R, m))))
          (ringStdMUAns keys Q' H c' L (.sign s (.inl (R, m)))) [.sign s (.inl (R, m))] 0 :=
        MultiRelay.RunsWith.query_inr (ansM := ringStdMUAns keys Q' H c') (H := H) (rs := L)
          (k := fun b => OracleProg.pure (b.elim (fun _ => none) id)) (.sign s (.inl (R, m)))
          (MultiRelay.RunsWith.pure _ _)
      have ha : (ringStdMUAns keys Q' H c' L (.sign s (.inl (R, m))) : Option (MUResponse B)) =
          ((B.bsign (B.keyGen (keys s)).2 R (R.1.idxOf (B.pk (keys s))) m
            (c' ⟨L.length, hL⟩)).run H).map .signature := by
        rw [ringStdMUAns, hans _ hL]
        have hm : (B.keyGen (keys s)).1 ∈ R.1 := hc.1
        simp only [muReply, SignOracle.ringStd, SignOracle.ring]
        split_ifs with h
        · rfl
        · exact absurd hm h
      rcases hb : (B.bsign (B.keyGen (keys s)).2 R (R.1.idxOf (B.pk (keys s))) m
          (c' ⟨L.length, hL⟩)).run H with _ | σ
      · refine ⟨[.sign s (.inl (R, m))] ++ [], 0 + 0, MultiRelay.RunsWith.bind hq ?_, by simp,
          by omega⟩
        simp only [ha, hb, Option.map_none]
        refine (MultiRelay.RunsWith.pure _ _).congr_res ?_
        rw [ringReplyStd_sign_of_mem keys H _ hc.1 hc.2]
        simp only [signAt_eq, OracleProg.run_bind]
        rw [show (B.bsign (B.keyGen (keys s)).2 R (R.1.idxOf (B.pk (keys s))) m
          (c' ⟨L.length, hL⟩, ρ).1).run H = none from hb]
        rfl
      · have hp := MultiRelay.RunsWith.liftQ (ansM := ringStdMUAns keys Q' H c') (H := H)
          (Resp' := MUResponse B) (L ++ [.sign s (.inl (R, m))]) (B.pub (B.pk (keys s)) σ)
        have hpr := MultiRelay.RunsWith.liftQ (ansM := ringStdMUAns keys Q' H c') (H := H)
          (Resp' := MUResponse B) (L ++ [.sign s (.inl (R, m))] ++ [])
          (PS.prove ⟨R, m, (B.pub (B.pk (keys s)) σ).run H⟩ ⟨R.1.idxOf (B.pk (keys s)), σ⟩ ρ)
        refine ⟨[.sign s (.inl (R, m))] ++ ([] ++ []),
          0 + (((B.pub (B.pk (keys s)) σ).trace H).length +
            ((PS.prove ⟨R, m, (B.pub (B.pk (keys s)) σ).run H⟩ ⟨R.1.idxOf (B.pk (keys s)), σ⟩
              ρ).trace H).length), MultiRelay.RunsWith.bind hq ?_, by simp, ?_⟩
        · simp only [ha, hb, Option.map_some]
          refine (MultiRelay.RunsWith.bind hp (hpr.mapOutput _)).congr_res ?_
          rw [ringReplyStd_sign_of_mem keys H _ hc.1 hc.2,
            run_signAt_of_bsign B PS (c := (c' ⟨L.length, hL⟩, ρ)) hb]
          rfl
        · have h1 := B.pub_queries (B.pk (keys s)) σ H
          have h2 := PS.prove_queries ⟨R, m, (B.pub (B.pk (keys s)) σ).run H⟩
            ⟨R.1.idxOf (B.pk (keys s)), σ⟩ ρ H
          omega
    · rw [if_neg hc]
      exact ⟨[], 0,
        (MultiRelay.RunsWith.pure _ _).congr_res (ringReplyStd_sign_of_not keys H _ hc).symm,
        Nat.zero_le _, Nat.zero_le _⟩
  · have h := (MultiRelay.RunsWith.query_inr (ansM := ringStdMUAns keys Q' H c') (H := H) (rs := L)
      (k := fun b => OracleProg.pure (b.elim (fun _ => none) id)) (.sign i (.inr bm))
      (MultiRelay.RunsWith.pure _ _)).mapOutput (fun
        | some (.signature σ) => some (.sideSignature σ)
        | _ => none : Option (MUResponse B) → Option (RResp B PS adm (baseSide B PS adm)))
    refine ⟨_, _, h.congr_res ?_, by simp, Nat.zero_le _⟩
    simp only [Sum.elim_inr, id, ringStdMUAns]
    rw [hans _ hL]
    change (match ((B.ssign (B.keyGen (keys i)).2 bm (c' ⟨L.length, hL⟩)).run H).map
        (MUResponse.signature (B := B)) with
      | some (.signature σ) => some (.sideSignature σ)
      | _ => none) = ((B.ssign (B.keyGen (keys i)).2 bm (c' ⟨L.length, hL⟩)).run H).map
        (UnforgeResponse.sideSignature (O := baseSide B PS adm))
    rcases (B.ssign (B.keyGen (keys i)).2 bm (c' ⟨L.length, hL⟩)).run H with _ | σ <;> rfl

end Runs

/-! ### The numbered challenger relays the multi-user challenger -/

section Relays

variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] [NeZero n]

/-- **The numbered challenger of the key-reuse game with `Q` requests is the relay
`forgerRelayStd` of the multi-user challenger with `Q' ≥ Q` requests**
(`MultiRelay.RelaysChallenger`), along the restriction of the coins to the first `Q`. -/
theorem relaysChallenger_forgerRelayStd (keys : Fin n → B.KeyCoins) (i₁ : Fin n) {Q Q' : ℕ}
    (hQ : Q ≤ Q') :
    (forgerRelayStd B PS adm (fun i => B.pk (keys i)) i₁).RelaysChallenger
      (numChallenger B PS adm n (baseSide B PS adm) keys Q)
      (muChallenger (SignOracle.ringStd B) n keys Q')
      (fun c' j => c' (Fin.castLE hQ j)) where
  coins_eq := (map_uniform_comp_embedding (Fin.castLEEmb hQ)).symm
  oracle_eq H c _ lg := (numChallenger_noAssign_std keys Q).oracle_eq H c lg
  oracle_eq' H c' _ lg := (muChallenger_noAssign _ keys Q').oracle_eq H c' lg
  answer_eq H c' rs r hi := by
    have hi' : rs.length < Q := hi
    refine (answerAfter_numChallenger_std keys Q H _ rs r hi').trans ?_
    have hlen := (forgerRelayStd B PS adm (fun i => B.pk (keys i)) i₁).length_mainReqs
      (numChallenger B PS adm n (baseSide B PS adm) keys Q).Q
      ((muChallenger (SignOracle.ringStd B) n keys Q').toPureEnv.answerAfter (H, c')) H rs hi.le
    change _ = 1 * rs.length at hlen
    rw [Nat.one_mul] at hlen
    have hL : ((forgerRelayStd B PS adm (fun i => B.pk (keys i)) i₁).mainReqs
        (numChallenger B PS adm n (baseSide B PS adm) keys Q).Q
        ((muChallenger (SignOracle.ringStd B) n keys Q').toPureEnv.answerAfter (H, c')) H
        rs).length < Q' := by omega
    obtain ⟨asks, q, h, ha, hq⟩ := runsWith_forgerProgStd keys Q' H c' _ hL r
    refine (((forgerRelayStd B PS adm (fun i => B.pk (keys i)) i₁).runReply_eq_of_runsWith rfl h ha
      hq).trans ?_).symm
    congr 3
    exact Fin.ext hlen

end Relays

/-! ### Freshness through the relays -/

section Fresh

variable (B PS adm) in
/-- **A ring forgery is fresh for the requests `rs` of the key-reuse game**: every key of its ring
is the key of a user that no request of `rs` corrupts, no request of `rs` asks for a ring
signature on its ring and message, and no request of `rs` asks a member of its ring for an
ordinary signature on its base message `bmsg R m`. -/
def RingFreshReqStd (keys : Fin n → B.KeyCoins) (o : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof))
    (rs : List (RReq B PS adm n (baseSide B PS adm))) : Prop :=
  (∀ pk ∈ o.1.1, ∃ i, B.pk (keys i) = pk ∧ UnforgeRequest.corrupt i ∉ rs) ∧
    (∀ s, UnforgeRequest.sign s o.1 o.2.1 ∉ rs) ∧
    ∀ i bm, UnforgeRequest.sideSign i bm ∈ rs → B.pk (keys i) ∈ o.1.1 → bm ≠ B.bmsg o.1 o.2.1

/-- **A fresh ring and message are fresh for the requests of the key-reuse game's history.** -/
theorem Fresh.ringFreshReqStd {keys : Fin n → B.KeyCoins}
    {hist : UnforgeHist (S := ofBase B PS adm) n (baseSide B PS adm)}
    {o : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof)} (h : Fresh keys hist o.1 o.2.1) :
    RingFreshReqStd B PS adm keys o (hist.map HistoryEntry.request) := by
  refine ⟨fun pk hpk => ?_, fun s hs => ?_, fun i bm hs hm hb => ?_⟩
  · obtain ⟨i, hi, hc⟩ := h.honest_ring pk hpk
    refine ⟨i, hi, fun hm => hc ?_⟩
    obtain ⟨e, he, hr⟩ := List.mem_map.1 hm
    exact ⟨e, he, hr⟩
  · obtain ⟨e, he, hr⟩ := List.mem_map.1 hs
    exact h.not_signQueried ⟨e, he, s, hr⟩
  · obtain ⟨e, he, hr⟩ := List.mem_map.1 hs
    exact h.not_sideCovered ⟨e, he, i, bm, hr, hm, hb⟩

/-- **Freshness passes through the relay of the key-reuse game** for a ring-binding base message:
if every multi-user request is the idle public-key request or one that a numbered request of `nrs`
relays to (`ForgerAskStd`), a ring forgery fresh for the requests of `nrs` (read without their
prover's coins) is fresh for the multi-user requests. -/
theorem muFreshReq_of_relayStd (hbind : B.BindsRing) {keys : Fin n → B.KeyCoins} {i₁ : Fin n}
    {o : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof)}
    {nrs : List (NumReq B PS adm n (baseSide B PS adm))}
    {mrs : List (MURequest (SignOracle.ringStd B) n)}
    (hf : RingFreshReqStd B PS adm keys o (nrs.map Prod.snd))
    (hrel : ∀ r' ∈ mrs, r' = .publicKey i₁ ∨ ∃ r ∈ nrs, ForgerAskStd B PS adm r r') :
    MUFreshReq B (PS := PS) keys o mrs := by
  refine ⟨fun pk hpk => ?_, fun j sm hs hj hb => ?_⟩
  · obtain ⟨i, hi, hc⟩ := hf.1 pk hpk
    refine ⟨i, hi, fun hm => ?_⟩
    rcases hrel _ hm with h | ⟨⟨ρ, r⟩, hr, ha⟩
    · cases h
    · rcases r with i' | ⟨s, R, m⟩ | ⟨i', bm⟩ <;> simp only [ForgerAskStd] at ha
      · cases ha
        exact hc (List.mem_map.2 ⟨_, hr, rfl⟩)
      · cases ha
      · cases ha
  · rcases hrel _ hs with h | ⟨⟨ρ, r⟩, hr, ha⟩
    · cases h
    · rcases r with i' | ⟨s, R, m⟩ | ⟨i', bm⟩ <;> simp only [ForgerAskStd] at ha
      · cases ha
      · cases ha
        obtain ⟨hR, hm⟩ := hbind _ _ _ _ hb
        subst hR
        subst hm
        exact hf.2.1 j (List.mem_map.2 ⟨_, hr, rfl⟩)
      · cases ha
        exact hf.2.2 j bm (List.mem_map.2 ⟨_, hr, rfl⟩) hj hb

end Fresh

/-! ### The game to the multi-user challenger -/

section Game

variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] [NeZero n] {t : ℕ}

variable (B PS adm) in
/-- **The relayed forger of the key-reuse game** at the users' public keys `pks` and the prover's
coins `ρ`: the adversary absorbed through `numRelay Q ρ`, relayed to the multi-user challenger by
`forgerRelayStd pks i₁` (`relayedForgerVia`). At most `t + Q · (qPub + PS.q)` queries. -/
noncomputable def relayedForgerStd (A : KeyReuseAdversary B PS adm n
    (OracleView.queriesOnly X Y) t) (pks : Fin n → B.PK) (i₁ : Fin n) (Q : ℕ)
    (ρ : Fin Q → PS.Coins) :
    QueryBoundedAdversary X Y (MURequest (SignOracle.ringStd B) n) (MUResponse B)
      (KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof)) (t + Q * (B.qPub + PS.q)) :=
  relayedForgerVia A (forgerRelayStd B PS adm pks i₁) pks Q ρ

/-- **The key-reuse game's forgery probability through the relayed forger** (a ring-binding base
message `hbind`): at most the average, over the users' key coins, the oracle and the prover's
coins, of the probability that the relayed forger against the multi-user challenger with the
ring-aware and the ordinary signing oracle and `Q' ≥ Q` requests outputs a ring signature that
verifies and is fresh for the multi-user requests of its history (`MUFreshReq`). -/
theorem keyReuseForgeProb_le_relayedForgerStd (hbind : B.BindsRing)
    (A : KeyReuseAdversary B PS adm n (OracleView.queriesOnly X Y) t) (i₁ : Fin n)
    (Q Q' : ℕ) (hQ : Q ≤ Q') :
    keyReuseForgeProb A Q ≤ ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' H, PMF.uniformOfFintype (X → Y) H * ∑ ρ, PMF.uniformOfFintype (Fin Q → PS.Coins) ρ *
        ((relayedForgerStd B PS adm A (fun i => B.pk (keys i)) i₁ Q ρ).transcriptLaw
          (muChallenger (SignOracle.ringStd B) n keys Q') H).toOuterMeasure
          {x | ∃ p ∈ x, (ofBase B PS adm).verify H p.1.1 p.1.2.1 p.1.2.2 = true ∧
            MUFreshReq B (PS := PS) keys p.1 (p.2.map HistoryEntry.request)} := by
  simp only [keyReuseForgeProb, forgeProb, unforgeLaw, runLaw, PMF.toOuterMeasure_bind_apply,
    PMF.toOuterMeasure_map_apply]
  refine ENNReal.tsum_le_tsum fun keys => mul_le_mul' le_rfl
    (ENNReal.tsum_le_tsum fun H => mul_le_mul' le_rfl ?_)
  have hsub : (fun o => (keys, H, o)) ⁻¹' {x : (Fin n → B.KeyCoins) × (X → Y) ×
      Option ((KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof)) ×
        UnforgeHist (S := ofBase B PS adm) n (baseSide B PS adm)) |
      ∃ p ∈ x.2.2, Forges x.1 x.2.1 p.1 p.2} ⊆
      {x | ∃ p ∈ x, (fun o rs => (ofBase B PS adm).verify H o.1 o.2.1 o.2.2 = true ∧
        RingFreshReqStd B PS adm keys o rs) p.1 (p.2.map HistoryEntry.request)} := by
    rintro x ⟨p, hp, hf⟩
    exact ⟨p, hp, hf.verify_eq, hf.fresh.ringFreshReqStd⟩
  refine (MeasureTheory.measure_mono hsub).trans ?_
  refine le_of_eq_of_le (transcriptLaw_numRelay (A (fun i => B.pk (keys i), ())) keys Q H
    (fun o rs => (ofBase B PS adm).verify H o.1 o.2.1 o.2.2 = true ∧
      RingFreshReqStd B PS adm keys o rs)) ?_
  refine Finset.sum_le_sum fun ρ _ => mul_le_mul' le_rfl ?_
  refine ((A (fun i => B.pk (keys i), ())).absorbQB (numRelay B PS adm n (baseSide B PS adm) Q ρ)
    (numRelay_route_injective Q ρ)).transcriptLaw_le_relay
    (forgerRelayStd B PS adm (fun i => B.pk (keys i)) i₁)
    (numChallenger B PS adm n (baseSide B PS adm) keys Q)
    (muChallenger (SignOracle.ringStd B) n keys Q') _ (relaysChallenger_forgerRelayStd keys i₁ hQ)
    H _ _ ?_
  intro o hist hist' ⟨hv, hf⟩ hrel
  refine ⟨hv, muFreshReq_of_relayStd hbind (i₁ := i₁) (nrs := hist.map HistoryEntry.request) ?_
    ?_⟩
  · exact hf
  · intro r' hr'
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 hr'
    rcases hrel e' he' with h | ⟨e, he, hc⟩
    · exact Or.inl h
    · exact Or.inr ⟨e.request, List.mem_map_of_mem he,
        (forgerRelayStd B PS adm (fun i => B.pk (keys i)) i₁).canAsk_of_asksIn
          (asksIn_forgerProgStd _ e.request).plainProg hc⟩

end Game

end GordieHowe.RingSignature
