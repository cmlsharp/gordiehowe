-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingForgerRelay
public import GordieHowe.Model.Signature.RejectionRelay
public import GordieHowe.Model.RingSignature.UserEmbed
public import GordieHowe.Model.Signature.MultiUserSim

@[expose] public section

/-!
# The numbered requests relayed to the multi-user challenger

The second step of the reduction from BKM06 Definition 7 for `ofBase B PS adm` to MU-EUF-CMA^corr
(after `GordieHowe/Applications/Ring/RingForgerRelay.lean`): the requests carrying their prover's
coins are relayed (`GordieHowe/Model/Quantum/Interactive/MultiRelay.lean`) to the multi-user
challenger with the ring-aware signing oracle (`Signature.SignOracle.ring B`). A corruption is asked
as a corruption; a ring-signing request `(ρ, (s, R, m))` by a member of a supported ring is asked as
the signing request of user `s` on `(R, m)`, and the ring signature is the public value of the base
signature and the honest proof with the prover's coins `ρ`, computed by the relay with oracle
queries; the other ring-signing requests are refused without a request. One main request and
`qPub + PS.q` queries per request.

- `ringReply`: the game's reply to a request at given coins and oracle.
  `numChallenger_noAssign`, `answerAfter_numChallenger`.
- `relayRingSign`, `forgerProg`, `forgerRelay pks i₁`: the relay programs, with the users' public
  keys `pks` and the idle request the public key of user `i₁`.
- `runsWith_forgerProg`: a relayed request runs with the game's reply.
- `relaysChallenger_forgerRelay`: the numbered challenger with `Q` requests is the relay of the
  multi-user challenger with `Q' ≥ Q` requests, along the restriction of its coins.
- `ForgerAsk`, `asksIn_forgerProg`: the main request of a relayed request is the same corruption,
  or the signing request of the same user for the same ring and message.
- `RingFreshReq`, `Fresh.ringFreshReq`, `MUFreshReq`, `muFreshReq_of_relay`: freshness read from
  the requests, and through the relay for a ring-binding base message.
- `RelayFam`, `relayedForgerVia`: relay families and the relayed forger through a relay, for any
  side oracle and signing oracle.
- `relayedForger`, `insiderForgeProb_le_relayedForger`: the game's forgery probability is at most
  the average, over the users' key coins, the oracle and the prover's coins, of the probability that
  the relayed forger against the multi-user challenger outputs a verifying ring signature fresh for
  its multi-user requests.
-/

namespace GordieHowe.RingSignature

open Quantum Signature
open scoped ENNReal

variable {X Y : Type} {N : ℕ} {T : Signature.SchemeTypes} {RMsg : Type}
  {B : BaseSigner X Y N T RMsg} {TPS : PSTypes}
  {PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {n : ℕ}

/-! ### The game's replies -/

variable [Fintype T.PK] [DecidableEq T.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype T.BSig]
  [DecidableEq T.BSig] [Fintype T.Pub] [DecidableEq T.Pub] [Fintype T.KeyCoins]
  [DecidableEq T.KeyCoins] [Nonempty T.KeyCoins] [Fintype T.Coins] [DecidableEq T.Coins]
  [Nonempty T.Coins]

variable (B PS adm) in
/-- **The game's reply to a request** at the users' key coins `keys`, the oracle `H` and the
request's coins `c` (the base signer's and the prover's): the key coins of a corrupted user, the
ring signature of a member's request (`ofBase`'s signer; a refusal passed on), and `none` for a
non-member. -/
noncomputable def ringReply (keys : Fin n → B.KeyCoins) (H : X → Y) (c : B.Coins × PS.Coins) :
    RReq B PS adm n (SideOracle.none _) → Option (RResp B PS adm (SideOracle.none _))
  | .corrupt i => some (.keyCoins (keys i))
  | .sign s R m => if (ofBase B PS adm).pk (keys s) ∈ R.1 then
      (((ofBase B PS adm).sign ((ofBase B PS adm).keyGen (keys s)) R m c).run H).map .signature
    else none
  | .sideSign _ bm => bm.elim

omit [Fintype T.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype T.BSig] [DecidableEq T.BSig]
  [Fintype T.Pub] [DecidableEq T.Pub] [Fintype T.KeyCoins] [DecidableEq T.KeyCoins]
  [Nonempty T.KeyCoins] [Fintype T.Coins] [DecidableEq T.Coins] [Nonempty T.Coins] in
/-- **The game's reply to a member's request on a supported ring** is `signAt` at the member's
first position. -/
theorem ringReply_sign_of_mem (keys : Fin n → B.KeyCoins) (H : X → Y) (c : B.Coins × PS.Coins)
    {s : Fin n} {R : KeyRing (ofBase B PS adm).PK N} {m : (ofBase B PS adm).Msg}
    (hm : B.pk (keys s) ∈ R.1)
    (ha : adm R) :
    ringReply B PS adm keys H c (.sign s R m) =
      ((signAt B PS (B.pk (keys s)) (B.keyGen (keys s)).2 R (R.1.idxOf (B.pk (keys s))) m c).run
        H).map fun x => (.signature x : RResp B PS adm (SideOracle.none _)) := by
  have hm' : ((ofBase B PS adm).keyGen (keys s)).1 ∈ R.1 := hm
  simp only [ringReply]
  split_ifs with h
  · exact congrArg _ (congrArg (fun p => OracleProg.run H p)
      (sign_ofBase_of_mem B PS adm (kp := (ofBase B PS adm).keyGen (keys s)) hm' ha m c))
  · exact absurd hm h

omit [Fintype T.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype T.BSig] [DecidableEq T.BSig]
  [Fintype T.Pub] [DecidableEq T.Pub] [Fintype T.KeyCoins] [DecidableEq T.KeyCoins]
  [Nonempty T.KeyCoins] [Fintype T.Coins] [DecidableEq T.Coins] [Nonempty T.Coins] in
/-- **The game refuses a request off a supported ring holding the member's key.** -/
theorem ringReply_sign_of_not (keys : Fin n → B.KeyCoins) (H : X → Y) (c : B.Coins × PS.Coins)
    {s : Fin n} {R : KeyRing (ofBase B PS adm).PK N} {m : (ofBase B PS adm).Msg}
    (hc : ¬ (B.pk (keys s) ∈ R.1 ∧ adm R)) :
    ringReply B PS adm keys H c (.sign s R m) = none := by
  simp only [ringReply]
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

omit [Fintype T.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype T.BSig] [DecidableEq T.BSig]
  [Fintype T.Pub] [DecidableEq T.Pub] [Fintype T.KeyCoins] [DecidableEq T.KeyCoins]
  [Nonempty T.KeyCoins] in
/-- **The numbered challenger never reprograms.** -/
theorem numChallenger_noAssign [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
    [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins]
    (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    (numChallenger B PS adm n (SideOracle.none _) keys Q).NoAssign := by
  intro c hist r G
  obtain ⟨ρ, r⟩ := r
  change (((unforgeChallenger (ofBase B PS adm) n (SideOracle.none _) keys Q).respond
    (fun j => (c j, ρ)) _ r).run G).assignments = []
  simp only [unforgeChallenger]
  split_ifs
  · rcases r with i | ⟨s, R, m⟩ | ⟨i, bm⟩
    · rfl
    · dsimp only
      split_ifs
      · simp [OracleProg.run_bind]
      · rfl
    · exact bm.elim
  · rfl

omit [Fintype T.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype T.BSig] [DecidableEq T.BSig]
  [Fintype T.Pub] [DecidableEq T.Pub] [Fintype T.KeyCoins] [DecidableEq T.KeyCoins]
  [Nonempty T.KeyCoins] in
/-- **The numbered challenger's reply** to a request numbered below `Q` is the game's reply with
the base signer's coins of that number and the request's prover's coins. -/
theorem answerAfter_numChallenger [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [AddGroup Y] [Nonempty Y] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins]
    (keys : Fin n → B.KeyCoins) (Q : ℕ) (H : X → Y)
    (b : Fin Q → B.Coins) (rs : List (NumReq B PS adm n (SideOracle.none _)))
    (r : NumReq B PS adm n (SideOracle.none _))
    (hi : rs.length < Q) :
    (numChallenger B PS adm n (SideOracle.none _) keys Q).toPureEnv.answerAfter (H, b) rs r =
      ringReply B PS adm keys H (b ⟨rs.length, hi⟩, r.1) r.2 := by
  have hn := numChallenger_noAssign (PS := PS) (adm := adm) keys Q
  obtain ⟨-, -, h3⟩ := hn.oracleIn H b rs
  rw [hn.answerAfter_eq H b rs r hi]
  have hl :
      ((numChallenger B PS adm n (SideOracle.none _) keys Q).toPureEnv.oracleIn (H, b)
        rs).hist.length =
      rs.length := by
    rw [h3]
    exact min_eq_left (le_of_lt hi)
  generalize ((numChallenger B PS adm n (SideOracle.none _) keys Q).toPureEnv.oracleIn (H, b)
    rs).hist = hist at hl ⊢
  obtain ⟨ρ, r⟩ := r
  have hl' : (hist.map fun e :
      HistoryEntry (NumReq B PS adm n (SideOracle.none _)) (RResp B PS adm (SideOracle.none _)) =>
      (⟨e.request.2, e.response⟩ :
        HistoryEntry (RReq B PS adm n (SideOracle.none _))
          (RResp B PS adm (SideOracle.none _)))).length <
      Q := by simpa [hl] using hi
  change (((unforgeChallenger (ofBase B PS adm) n (SideOracle.none _) keys Q).respond
    (fun j => (b j, ρ)) _ r).run H).response = _
  have hf : (⟨(hist.map fun e :
      HistoryEntry (NumReq B PS adm n (SideOracle.none _)) (RResp B PS adm (SideOracle.none _)) =>
      (⟨e.request.2, e.response⟩ :
        HistoryEntry (RReq B PS adm n (SideOracle.none _))
          (RResp B PS adm (SideOracle.none _)))).length,
      hl'⟩ :
      Fin Q) = ⟨rs.length, hi⟩ := Fin.ext (by simpa using hl)
  simp only [unforgeChallenger, dif_pos hl', hf]
  rcases r with i | ⟨s, R, m⟩ | ⟨i, bm⟩
  · rfl
  · simp only [ringReply]
    split_ifs
    · simp [OracleProg.run_bind]
    · rfl
  · exact bm.elim

/-! ### The relay programs -/

section Programs

variable [Zero Y]

/-- **The relayed ring signing** by user `s` on `(R, m)` with the prover's coins `ρ`, with the
users' public keys `pks`: the signing request of user `s` on `(R, m)` asked of the multi-user
challenger, then, for a base signature `σ`, its public value `y` and the honest proof of
`(R, m, y)` with the witness at the first position of `pks s`, as relay queries. -/
def relayRingSign (pks : Fin n → B.PK) (ρ : PS.Coins) (s : Fin n) (R : KeyRing B.PK N)
    (m : B.Msg) :
    OracleProg (X ⊕ MURequest (SignOracle.ring B) n) (Y ⊕ Option (MUResponse B.core))
      (Option (RResp B PS adm (SideOracle.none _))) :=
  (askResp (.sign s (R, m))).bind fun
    | some (.signature σ) => (MultiRelay.liftQ (B.pub (pks s) σ)).bind fun y =>
        (MultiRelay.liftQ (PS.prove ⟨R, m, y⟩ ⟨R.1.idxOf (pks s), σ⟩ ρ)).mapOutput fun π =>
          some (.signature ((y, π) : B.Pub × PS.Proof))
    | _ => .pure none

variable (B PS adm) in
/-- **The relay program of a request with its prover's coins**, with the users' public keys `pks`:
a corruption asked as it is; a ring-signing request by a member of a supported ring relayed by
`relayRingSign`; the other ring-signing requests refused without a request. -/
noncomputable def forgerProg (pks : Fin n → B.PK) :
    NumReq B PS adm n (SideOracle.none _) → OracleProg (X ⊕ MURequest (SignOracle.ring B) n)
      (Y ⊕ Option (MUResponse B.core)) (Option (RResp B PS adm (SideOracle.none _)))
  | (_, .corrupt i) => (askResp (.corrupt i)).mapOutput fun
      | some (.keyCoins kc) => some (.keyCoins kc)
      | _ => none
  | (ρ, .sign s R m) => if pks s ∈ R.1 ∧ adm R then relayRingSign pks ρ s R m else .pure none
  | (_, .sideSign _ bm) => bm.elim

variable (B PS adm) in
/-- **The relay of the numbered requests to the multi-user challenger**: the programs
`forgerProg pks`, one main request and `qPub + PS.q` queries per request, the idle request the
public key of user `i₁`. -/
noncomputable def forgerRelay (pks : Fin n → B.PK) (i₁ : Fin n) :
    MultiRelay X Y (NumReq B PS adm n (SideOracle.none _)) (RResp B PS adm (SideOracle.none _))
      (MURequest (SignOracle.ring B) n)
      (MUResponse B.core) where
  prog := MultiRelay.plainProg (forgerProg B PS adm pks)
  K := 1
  K_pos := Nat.one_pos
  qR := B.qPub + PS.q
  idle := .publicKey i₁

end Programs

/-! ### The main requests of the relay -/

variable (B PS adm) in
/-- **The main request a numbered request relays to**: the same corruption, or the signing request
of the same user for the same ring and message. -/
def ForgerAsk : NumReq B PS adm n (SideOracle.none _) → MURequest (SignOracle.ring B) n → Prop
  | (_, .corrupt i), r' => r' = .corrupt i
  | (_, .sign s R m), r' => r' = .sign s (R, m)
  | (_, .sideSign _ _), _ => False

omit [Fintype T.BSig] [DecidableEq T.BSig] [Fintype T.Pub] [DecidableEq T.Pub]
  [Fintype T.KeyCoins] [DecidableEq T.KeyCoins] [Nonempty T.KeyCoins] [Fintype T.Coins]
  [DecidableEq T.Coins] [Nonempty T.Coins] [Fintype T.PK] [Fintype RMsg] [DecidableEq RMsg]
  in
/-- **Every main request of a relay program is one its request relays to.** -/
theorem asksIn_forgerProg [Zero Y] (pks : Fin n → B.PK)
    (r : NumReq B PS adm n (SideOracle.none _)) :
    MultiRelay.AsksIn (MUResponse B.core) (forgerProg B PS adm pks r) (ForgerAsk B PS adm r) := by
  obtain ⟨ρ, r⟩ := r
  rcases r with i | ⟨s, R, m⟩ | ⟨i, bm⟩
  · exact (asksIn_askResp _).mapOutput _
  · simp only [forgerProg]
    split_ifs
    · refine MultiRelay.AsksIn.bind (asksIn_askResp _) fun o => ?_
      rcases o with _ | ⟨_⟩ | ⟨σ⟩ | ⟨_⟩
      · exact MultiRelay.AsksIn.pure _ _
      · exact MultiRelay.AsksIn.pure _ _
      · exact MultiRelay.AsksIn.bind (MultiRelay.AsksIn.liftQ _ _) fun y =>
          (MultiRelay.AsksIn.liftQ _ _).mapOutput _
      · exact MultiRelay.AsksIn.pure _ _
    · exact MultiRelay.AsksIn.pure _ _
  · exact bm.elim

/-! ### The relayed requests against the multi-user challenger -/

section Runs

variable [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y] (keys : Fin n → B.KeyCoins) (Q' : ℕ) (H : X → Y) (c' : Fin Q' → B.Coins)

/-- The multi-user challenger's replies. -/
noncomputable abbrev ringMUAns : List (MURequest (SignOracle.ring B) n) →
    MURequest (SignOracle.ring B) n → Option (MUResponse B.core) :=
  (muChallenger (SignOracle.ring B) n keys Q').toPureEnv.answerAfter (H, c')

omit [Fintype T.BSig] [DecidableEq T.BSig] [Fintype T.Pub] [DecidableEq T.Pub]
  [Fintype T.KeyCoins] [DecidableEq T.KeyCoins] [Nonempty T.KeyCoins] [Fintype T.PK]
  [Fintype RMsg] [DecidableEq RMsg] in
/-- **A relayed request runs with the game's reply**: the request `(ρ, r)`, after the main requests
`L` (fewer than `Q'`), runs with the game's reply at the coins `(c' |L|, ρ)`, at most one main
request and `qPub + PS.q` queries. -/
theorem runsWith_forgerProg (L : List (MURequest (SignOracle.ring B) n)) (hL : L.length < Q')
    (r : NumReq B PS adm n (SideOracle.none _)) :
    ∃ asks q, MultiRelay.RunsWith (ringMUAns keys Q' H c') H L
      (forgerProg B PS adm (fun i => B.pk (keys i)) r)
      (ringReply B PS adm keys H (c' ⟨L.length, hL⟩, r.1) r.2) asks q ∧
      asks.length ≤ 1 ∧ q ≤ B.qPub + PS.q := by
  have hans := answerAfter_muChallenger (SignOracle.ring B) keys Q' H c' L
  obtain ⟨ρ, r⟩ := r
  rcases r with i | ⟨s, R, m⟩ | ⟨i, bm⟩
  · have h := (MultiRelay.RunsWith.query_inr (ansM := ringMUAns keys Q' H c') (H := H) (rs := L)
      (k := fun b => OracleProg.pure (b.elim (fun _ => none) id)) (.corrupt i)
      (MultiRelay.RunsWith.pure _ _)).mapOutput (fun
        | some (.keyCoins kc) => some (.keyCoins kc)
        | _ => none : Option (MUResponse B.core) → Option (RResp B PS adm (SideOracle.none _)))
    refine ⟨_, _, h.congr_res ?_, by simp, Nat.zero_le _⟩
    simp only [Sum.elim_inr, id, ringMUAns, hans _ hL, muReply]
    rfl
  · simp only [forgerProg]
    by_cases hc : B.pk (keys s) ∈ R.1 ∧ adm R
    · rw [if_pos hc]
      have hq : MultiRelay.RunsWith (ringMUAns keys Q' H c') H L
          (askResp (Resp' := MUResponse B.core) (.sign s (R, m)))
          (ringMUAns keys Q' H c' L (.sign s (R, m))) [.sign s (R, m)] 0 :=
        MultiRelay.RunsWith.query_inr (ansM := ringMUAns keys Q' H c') (H := H) (rs := L)
          (k := fun b => OracleProg.pure (b.elim (fun _ => none) id)) (.sign s (R, m))
          (MultiRelay.RunsWith.pure _ _)
      have ha : (ringMUAns keys Q' H c' L (.sign s (R, m)) : Option (MUResponse B.core)) =
          ((B.bsign (B.keyGen (keys s)).2 R (R.1.idxOf (B.pk (keys s))) m
            (c' ⟨L.length, hL⟩)).run H).map .signature := by
        rw [ringMUAns, hans _ hL]
        have hm : (B.keyGen (keys s)).1 ∈ R.1 := hc.1
        simp only [muReply, SignOracle.ring]
        split_ifs with h
        · rfl
        · exact absurd hm h
      rcases hb : (B.bsign (B.keyGen (keys s)).2 R (R.1.idxOf (B.pk (keys s))) m
          (c' ⟨L.length, hL⟩)).run H with _ | σ
      · refine ⟨[.sign s (R, m)] ++ [], 0 + 0, MultiRelay.RunsWith.bind hq ?_, by simp, by omega⟩
        simp only [ha, hb, Option.map_none]
        refine (MultiRelay.RunsWith.pure _ _).congr_res ?_
        rw [ringReply_sign_of_mem keys H _ hc.1 hc.2]
        simp only [signAt_eq, OracleProg.run_bind]
        rw [show (B.bsign (B.keyGen (keys s)).2 R (R.1.idxOf (B.pk (keys s))) m
          (c' ⟨L.length, hL⟩, ρ).1).run H = none from hb]
        rfl
      · have hp := MultiRelay.RunsWith.liftQ (ansM := ringMUAns keys Q' H c') (H := H)
          (Resp' := MUResponse B.core) (L ++ [.sign s (R, m)]) (B.pub (B.pk (keys s)) σ)
        have hpr := MultiRelay.RunsWith.liftQ (ansM := ringMUAns keys Q' H c') (H := H)
          (Resp' := MUResponse B.core) (L ++ [.sign s (R, m)] ++ [])
          (PS.prove ⟨R, m, (B.pub (B.pk (keys s)) σ).run H⟩ ⟨R.1.idxOf (B.pk (keys s)), σ⟩ ρ)
        refine ⟨[.sign s (R, m)] ++ ([] ++ []),
          0 + (((B.pub (B.pk (keys s)) σ).trace H).length +
            ((PS.prove ⟨R, m, (B.pub (B.pk (keys s)) σ).run H⟩ ⟨R.1.idxOf (B.pk (keys s)), σ⟩
              ρ).trace H).length), MultiRelay.RunsWith.bind hq ?_, by simp, ?_⟩
        · simp only [ha, hb, Option.map_some]
          refine (MultiRelay.RunsWith.bind hp (hpr.mapOutput _)).congr_res ?_
          rw [ringReply_sign_of_mem keys H _ hc.1 hc.2,
            run_signAt_of_bsign B PS (c := (c' ⟨L.length, hL⟩, ρ)) hb]
          rfl
        · have h1 := B.pub_queries (B.pk (keys s)) σ H
          have h2 := PS.prove_queries ⟨R, m, (B.pub (B.pk (keys s)) σ).run H⟩
            ⟨R.1.idxOf (B.pk (keys s)), σ⟩ ρ H
          omega
    · rw [if_neg hc]
      exact ⟨[], 0,
        (MultiRelay.RunsWith.pure _ _).congr_res (ringReply_sign_of_not keys H _ hc).symm,
        Nat.zero_le _, Nat.zero_le _⟩
  · exact bm.elim

end Runs

/-! ### The numbered challenger relays the multi-user challenger -/

section Relays

variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] [NeZero n] [Fintype TPS.Proof] [DecidableEq TPS.Proof]
  [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins]

omit [Nonempty T.KeyCoins] in
/-- **The numbered challenger with `Q` requests is the relay `forgerRelay` of the multi-user
challenger with `Q' ≥ Q` requests** (`MultiRelay.RelaysChallenger`), along the restriction of the
coins to the first `Q`: each numbered request is answered as its relay program answers it against
the multi-user replies. -/
theorem relaysChallenger_forgerRelay (keys : Fin n → B.KeyCoins) (i₁ : Fin n) {Q Q' : ℕ}
    (hQ : Q ≤ Q') :
    (forgerRelay B PS adm (fun i => B.pk (keys i)) i₁).RelaysChallenger
      (numChallenger B PS adm n (SideOracle.none _) keys Q)
      (muChallenger (SignOracle.ring B) n keys Q')
      (fun c' j => c' (Fin.castLE hQ j)) where
  coins_eq := (map_uniform_comp_embedding (Fin.castLEEmb hQ)).symm
  oracle_eq H c _ lg := (numChallenger_noAssign keys Q).oracle_eq H c lg
  oracle_eq' H c' _ lg := (muChallenger_noAssign _ keys Q').oracle_eq H c' lg
  answer_eq H c' rs r hi := by
    have hi' : rs.length < Q := hi
    refine (answerAfter_numChallenger keys Q H _ rs r hi').trans ?_
    have hlen := (forgerRelay B PS adm (fun i => B.pk (keys i)) i₁).length_mainReqs
      (numChallenger B PS adm n (SideOracle.none _) keys Q).Q
      ((muChallenger (SignOracle.ring B) n keys Q').toPureEnv.answerAfter (H, c')) H rs hi.le
    change _ = 1 * rs.length at hlen
    rw [Nat.one_mul] at hlen
    have hL : ((forgerRelay B PS adm (fun i => B.pk (keys i)) i₁).mainReqs
        (numChallenger B PS adm n (SideOracle.none _) keys Q).Q
        ((muChallenger (SignOracle.ring B) n keys Q').toPureEnv.answerAfter (H, c')) H rs).length <
        Q' := by omega
    obtain ⟨asks, q, h, ha, hq⟩ := runsWith_forgerProg keys Q' H c' _ hL r
    refine (((forgerRelay B PS adm (fun i => B.pk (keys i)) i₁).runReply_eq_of_runsWith rfl h ha
      hq).trans ?_).symm
    congr 3
    exact Fin.ext hlen

end Relays

/-! ### Freshness through the relays -/

section Fresh

variable (B PS adm) in
/-- **A ring forgery is fresh for the requests `rs`**: every key of its ring is the key of a user
that no request of `rs` corrupts, and no request of `rs` asks for a ring signature on its ring and
message. -/
def RingFreshReq (keys : Fin n → B.KeyCoins) (o : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof))
    (rs : List (RReq B PS adm n (SideOracle.none _))) : Prop :=
  (∀ pk ∈ o.1.1, ∃ i, B.pk (keys i) = pk ∧ UnforgeRequest.corrupt i ∉ rs) ∧
    ∀ s, UnforgeRequest.sign s o.1 o.2.1 ∉ rs

omit [Fintype T.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype T.BSig] [DecidableEq T.BSig]
  [Fintype T.Pub] [DecidableEq T.Pub] [Fintype T.KeyCoins] [DecidableEq T.KeyCoins]
  [Fintype T.Coins] [DecidableEq T.Coins] [Nonempty T.Coins] [Nonempty T.KeyCoins] in
/-- **A fresh ring and message are fresh for the requests of the history.** -/
theorem Fresh.ringFreshReq {keys : Fin n → B.KeyCoins}
    {hist : UnforgeHist (S := ofBase B PS adm) n (SideOracle.none _)}
    {o : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof)} (h : Fresh keys hist o.1 o.2.1) :
    RingFreshReq B PS adm keys o (hist.map HistoryEntry.request) := by
  refine ⟨fun pk hpk => ?_, fun s hs => ?_⟩
  · obtain ⟨i, hi, hc⟩ := h.honest_ring pk hpk
    refine ⟨i, hi, fun hm => hc ?_⟩
    obtain ⟨e, he, hr⟩ := List.mem_map.1 hm
    exact ⟨e, he, hr⟩
  · obtain ⟨e, he, hr⟩ := List.mem_map.1 hs
    exact h.not_signQueried ⟨e, he, s, hr⟩

variable (B) in
/-- **A ring forgery is fresh for the multi-user requests `mrs`** (of any signing oracle `O`):
every key of its ring is the key of a user that no request of `mrs` corrupts, and no request of
`mrs` asks a member of the ring to sign for its base message `bmsg R m`. -/
def MUFreshReq {O : SignOracle B.core} (keys : Fin n → B.KeyCoins)
    (o : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof)) (mrs : List (MURequest O n)) : Prop :=
  (∀ pk ∈ o.1.1, ∃ i, B.pk (keys i) = pk ∧ MURequest.corrupt i ∉ mrs) ∧
    ∀ j sm, MURequest.sign j sm ∈ mrs → B.pk (keys j) ∈ o.1.1 → O.base sm ≠ B.bmsg o.1 o.2.1

omit [Fintype T.BSig] [DecidableEq T.BSig] [Fintype T.Pub] [DecidableEq T.Pub]
  [Fintype T.KeyCoins] [DecidableEq T.KeyCoins] [Nonempty T.KeyCoins] [Fintype T.PK]
  [Fintype RMsg] [DecidableEq RMsg] [Fintype T.Coins] [DecidableEq T.Coins]
  [Nonempty T.Coins] in
/-- **Freshness passes through the relay** for a ring-binding base message: if every multi-user
request is the idle public-key request or one that a numbered request of `hist` relays to
(`ForgerAsk`), a ring forgery fresh for the requests of `hist` (read without their prover's coins)
is fresh for the multi-user requests. -/
theorem muFreshReq_of_relay (hbind : B.BindsRing) {keys : Fin n → B.KeyCoins} {i₁ : Fin n}
    {o : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof)}
    {nrs : List (NumReq B PS adm n (SideOracle.none _))}
    {mrs : List (MURequest (SignOracle.ring B) n)}
    (hf : RingFreshReq B PS adm keys o (nrs.map Prod.snd))
    (hrel : ∀ r' ∈ mrs, r' = .publicKey i₁ ∨ ∃ r ∈ nrs, ForgerAsk B PS adm r r') :
    MUFreshReq B (PS := PS) keys o mrs := by
  refine ⟨fun pk hpk => ?_, fun j sm hs _ hb => ?_⟩
  · obtain ⟨i, hi, hc⟩ := hf.1 pk hpk
    refine ⟨i, hi, fun hm => ?_⟩
    rcases hrel _ hm with h | ⟨⟨ρ, r⟩, hr, ha⟩
    · cases h
    · rcases r with i' | ⟨s, R, m⟩ | ⟨i', bm⟩ <;> simp only [ForgerAsk] at ha
      · cases ha
        exact hc (List.mem_map.2 ⟨_, hr, rfl⟩)
      · cases ha
  · rcases hrel _ hs with h | ⟨⟨ρ, r⟩, hr, ha⟩
    · cases h
    · rcases r with i' | ⟨s, R, m⟩ | ⟨i', bm⟩ <;> simp only [ForgerAsk] at ha
      · cases ha
      · cases ha
        obtain ⟨hR, hm⟩ := hbind _ _ _ _ hb
        subst hR
        subst hm
        exact hf.2 j (List.mem_map.2 ⟨_, hr, rfl⟩)

end Fresh

/-! ### The game to the multi-user challenger -/

section Game

variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] [NeZero n] {t : ℕ} [Fintype TPS.Proof] [DecidableEq TPS.Proof]
  [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins]

variable (X Y B PS adm n) in
/-- **A relay family**: for each list of the users' public keys, a relay (`MultiRelay`) of the
numbered requests of the game with the side oracle `SO` to the multi-user challenger with the
signing oracle `O`. -/
abbrev RelayFam (SO : SideOracle (ofBase B PS adm)) (O : SignOracle B.core) : Type :=
  (Fin n → B.PK) → MultiRelay X Y (NumReq B PS adm n SO) (RResp B PS adm SO) (MURequest O n)
    (MUResponse B.core)

omit [Fintype T.BSig] [DecidableEq T.BSig] [Fintype T.Coins] [DecidableEq T.Coins]
  [Nonempty T.Coins] in
/-- **The relayed forger through a relay** `F` of an adversary of the unforgeability game with the
side oracle `SO`, at the users' public keys `pks` and the prover's coins `ρ`: the adversary
absorbed through `numRelay Q ρ`, relayed by `F` answering `Q` requests. At most
`t + Q · F.qR` queries (`F` has no side reads, so no pad sub-slots). -/
noncomputable def relayedForgerVia {SO : SideOracle (ofBase B PS adm)} [Fintype SO.BMsg]
    [DecidableEq SO.BMsg] [Fintype SO.BSig] [DecidableEq SO.BSig] {Req' Resp' : Type}
    [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req']
    (A : UnforgeAdversary (ofBase B PS adm) n SO (OracleView.queriesOnly X Y) t)
    (F : MultiRelay X Y (NumReq B PS adm n SO) (RResp B PS adm SO) Req' Resp')
    (pks : Fin n → B.PK) (Q : ℕ) (ρ : Fin Q → PS.Coins) :
    QueryBoundedAdversary X Y Req' Resp' (KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof))
      (t + Q * F.qR) :=
  (((A (pks, ())).absorbQB (numRelay B PS adm n SO Q ρ) (numRelay_route_injective Q ρ)).relay F
    Q).mono (le_of_eq (by rw [F.qP_eq_zero, Nat.mul_zero, Nat.add_zero]))

variable (B PS adm) in
/-- **The relayed forger** of an adversary of BKM06 Definition 7 at the users' public keys `pks`
and the prover's coins `ρ`: the adversary absorbed through `numRelay Q ρ`, relayed to the
multi-user challenger by `forgerRelay pks i₁` (`relayedForgerVia`). At most
`t + Q · (qPub + PS.q)` queries. -/
noncomputable def relayedForger (A : InsiderAdversary (ofBase B PS adm) n
    (OracleView.queriesOnly X Y) t) (pks : Fin n → B.PK) (i₁ : Fin n) (Q : ℕ)
    (ρ : Fin Q → PS.Coins) :
    QueryBoundedAdversary X Y (MURequest (SignOracle.ring B) n) (MUResponse B.core)
      (KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof)) (t + Q * (B.qPub + PS.q)) :=
  relayedForgerVia A (forgerRelay B PS adm pks i₁) pks Q ρ

/-- **The game's forgery probability through the relayed forger** (BKM06 Definition 7, a
ring-binding base message `hbind`): at most the average, over the users' key coins, the oracle and
the prover's coins, of the probability that the relayed forger against the multi-user challenger
with `Q' ≥ Q` requests outputs a ring signature that verifies and is fresh for the multi-user
requests of its history (`MUFreshReq`). -/
theorem insiderForgeProb_le_relayedForger (hbind : B.BindsRing)
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly X Y) t) (i₁ : Fin n)
    (Q Q' : ℕ) (hQ : Q ≤ Q') :
    insiderForgeProb A Q ≤ ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' H, PMF.uniformOfFintype (X → Y) H * ∑ ρ, PMF.uniformOfFintype (Fin Q → PS.Coins) ρ *
        ((relayedForger B PS adm A (fun i => B.pk (keys i)) i₁ Q ρ).transcriptLaw
          (muChallenger (SignOracle.ring B) n keys Q') H).toOuterMeasure
          {x | ∃ p ∈ x, (ofBase B PS adm).verify H p.1.1 p.1.2.1 p.1.2.2 = true ∧
            MUFreshReq B (PS := PS) keys p.1 (p.2.map HistoryEntry.request)} := by
  simp only [insiderForgeProb, forgeProb, unforgeLaw, runLaw, PMF.toOuterMeasure_bind_apply,
    PMF.toOuterMeasure_map_apply]
  refine ENNReal.tsum_le_tsum fun keys => mul_le_mul' le_rfl
    (ENNReal.tsum_le_tsum fun H => mul_le_mul' le_rfl ?_)
  have hsub : (fun o => (keys, H, o)) ⁻¹' {x : (Fin n → B.KeyCoins) × (X → Y) ×
      Option ((KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof)) ×
        UnforgeHist (S := ofBase B PS adm) n (SideOracle.none _)) |
      ∃ p ∈ x.2.2, Forges x.1 x.2.1 p.1 p.2} ⊆
      {x | ∃ p ∈ x, (fun o rs => (ofBase B PS adm).verify H o.1 o.2.1 o.2.2 = true ∧
        RingFreshReq B PS adm keys o rs) p.1 (p.2.map HistoryEntry.request)} := by
    rintro x ⟨p, hp, hf⟩
    exact ⟨p, hp, hf.verify_eq, hf.fresh.ringFreshReq⟩
  refine (MeasureTheory.measure_mono hsub).trans ?_
  refine le_of_eq_of_le (transcriptLaw_numRelay (A (fun i => B.pk (keys i), ())) keys Q H
    (fun o rs => (ofBase B PS adm).verify H o.1 o.2.1 o.2.2 = true ∧
      RingFreshReq B PS adm keys o rs)) ?_
  refine Finset.sum_le_sum fun ρ _ => mul_le_mul' le_rfl ?_
  refine ((A (fun i => B.pk (keys i), ())).absorbQB (numRelay B PS adm n (SideOracle.none _) Q ρ)
    (numRelay_route_injective Q ρ)).transcriptLaw_le_relay
    (forgerRelay B PS adm (fun i => B.pk (keys i)) i₁)
    (numChallenger B PS adm n (SideOracle.none _) keys Q)
    (muChallenger (SignOracle.ring B) n keys Q') _ (relaysChallenger_forgerRelay keys i₁ hQ) H _ _
    ?_
  intro o hist hist' ⟨hv, hf⟩ hrel
  refine ⟨hv, muFreshReq_of_relay hbind (i₁ := i₁) (nrs := hist.map HistoryEntry.request) ?_ ?_⟩
  · exact hf
  · intro r' hr'
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 hr'
    rcases hrel e' he' with h | ⟨e, he, hc⟩
    · exact Or.inl h
    · exact Or.inr ⟨e.request, List.mem_map_of_mem he,
        (forgerRelay B PS adm (fun i => B.pk (keys i)) i₁).canAsk_of_asksIn
          (asksIn_forgerProg _ e.request).plainProg hc⟩

end Game

end GordieHowe.RingSignature
