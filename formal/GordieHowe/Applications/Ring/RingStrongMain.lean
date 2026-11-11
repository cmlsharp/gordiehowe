-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.RingStrongRelay
public import GordieHowe.Model.Quantum.Interactive.MultiRelayPos

@[expose] public section

/-!
# The game relayed to the sum of the multi-user challenger and the real-proof challenger

The first step of the route from the insider unforgeability of `ofBase B PS adm` (BKM06
Definition 7, ordinary unforgeability) to the MU-SUF target, the only strong notion here: the
game's challenger is the relay `strongRelay` (`GordieHowe/Applications/Ring/RingStrongRelay.lean`)
of the main challenger `strongMain`, the sum (`Quantum.Challenger.sum`) of the multi-user challenger
with the ring-aware signing oracle and the real challenger of proof queries (`QROM.realChallenger`,
the trivial relation, the prover `ringProver` made from `PS`). Every request makes a multi-user
request and then a proof query, so that request number `j` reads the coins number `j` of both
parts: the game's coins `c j` are `(c₁ j, c₂ j)`.

- `QROM.realChallenger_noAssign`, `QROM.answerAfter_realChallenger`: the real challenger never
  reprograms, and answers proof query number `c` by the program on the coins number `c`.
- `MultiRelay.runsWith_askResp`, `MultiRelay.asksIn_askResp_of`: a main request runs with its
  main reply, and its request satisfies every predicate that holds of it.
- `unforgeChallenger_noAssign`, `answerAfter_unforgeChallenger`: the game's challenger never
  reprograms, and answers request number `c` by the game's reply (`ringReply`) at the coins `c`.
- `ringProver B PS adm n`, `strongMain B PS adm n keys Q`, `strongMain_noAssign`, `strongAns`,
  `strongAns_inl`, `strongAns_inr`: the main challenger and its replies.
- `runsWith_askDummy`, `runsWith_strongProg`: the dummy proof query runs with its reply; a relayed
  request runs with the game's reply, a multi-user request and
  then a proof query, and at most `qPub` queries. `length_mainReqs_strong`: after `rs`, the main
  requests have `|rs|` multi-user requests and `|rs|` proof queries.
- `relaysChallenger_strongRelay`: the game's challenger with `Q` requests is the relay of
  `strongMain keys Q`.
- `StrongAsk`, `asksIn_strongProg`: the multi-user request of a relayed request is the same
  corruption, or the signing request or public key request of the same user.
- `StrongFreshReq`, `strongFreshReq_of_relay`: freshness for the multi-user requests, and through
  the relay. `insiderForgeProb_le_strongMain`: the game's forgery probability is at most
  the average, over the users' key coins and the oracle, of the probability that the strongly
  relayed forger against `strongMain` outputs a verifying ring signature fresh for its multi-user
  requests.
-/

namespace GordieHowe

open Quantum Signature QROM
open scoped ENNReal

/-! ### The real challenger's replies -/

namespace QROM

variable {X Y Stmt Wit Proof Coins : Type} (rel : Stmt → Wit → Prop) [DecidableRel rel]
  [Fintype Coins] [DecidableEq Coins] (P : NARG.Prover X Y Stmt Wit Proof Coins) (μ : PMF Coins)
  (Q : ℕ)

/-- **The real challenger never reprograms.** -/
theorem realChallenger_noAssign : (realChallenger rel P μ Q).NoAssign := by
  intro c hist r G
  simp only [realChallenger]
  split_ifs <;> simp [OracleProg.run_bind]

/-- **The real challenger's reply** to proof query number `|rs|` below `Q`: the program's proof on
the coins of that number if the relation holds, else `none`. -/
theorem answerAfter_realChallenger [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (H : X → Y) (c : Fin Q → Coins) (rs : List (ProofQuery Stmt Wit)) (x : ProofQuery Stmt Wit)
    (hi : rs.length < Q) :
    (realChallenger rel P μ Q).toPureEnv.answerAfter (H, c) rs x =
      if rel x.stmt x.wit then some ((P.prog x.stmt x.wit (c ⟨rs.length, hi⟩)).run H)
      else none := by
  have hn := realChallenger_noAssign rel P μ Q
  obtain ⟨-, -, h3⟩ := hn.oracleIn H c rs
  rw [hn.answerAfter_eq H c rs x hi]
  have hl : ((realChallenger rel P μ Q).toPureEnv.oracleIn (H, c) rs).hist.length = rs.length := by
    rw [h3]
    exact min_eq_left hi.le
  generalize ((realChallenger rel P μ Q).toPureEnv.oracleIn (H, c) rs).hist = hist at hl ⊢
  have hi' : hist.length < Q := hl ▸ hi
  have hf : (⟨hist.length, hi'⟩ : Fin Q) = ⟨rs.length, hi⟩ := Fin.ext hl
  simp only [realChallenger, hi', ↓reduceDIte, hf]
  split_ifs <;> simp [OracleProg.run_bind]

end QROM

namespace Quantum.MultiRelay

variable {X Y Req Resp Req' Resp' : Type} (F : MultiRelay X Y Req Resp Req' Resp') [Inhabited X]
  [Zero Y] [Inhabited Req'] (ansM : List Req' → Req' → Option Resp') (H : X → Y)

omit [Inhabited X] [Inhabited Req'] in
/-- **A main request runs with its main reply.** -/
theorem runsWith_askResp (rs : List Req') (r' : Req') :
    RunsWith ansM H rs (askResp (X := X) (Y := Y) (Resp' := Resp') r') (ansM rs r') [r'] 0 :=
  RunsWith.query_inr (k := fun b => OracleProg.pure (b.elim (fun _ => none) id)) r'
    (RunsWith.pure _ _)

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
/-- **The main request of `askResp r'`** satisfies every `P` that holds of `r'`. -/
theorem asksIn_askResp_of {P : Req' → Prop} (r' : Req') (h : P r') :
    AsksIn Resp' (askResp (X := X) (Y := Y) (Resp' := Resp') r') P :=
  AsksIn.query (fun _ he => (Sum.inr.inj he) ▸ h) fun _ => AsksIn.pure _ _

end Quantum.MultiRelay

namespace RingSignature

variable {X Y : Type} {N : ℕ} {TB : BaseTypes}
  {B : BaseSigner X Y N TB} {TPS : PSTypes} [Fintype TPS.Proof]
  [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins]
  {PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {n : ℕ}

/-! ### The game's challenger -/

variable [DecidableEq TB.PK] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins]

section Game

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddGroup Y] [Nonempty Y]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddGroup Y] [Nonempty Y]
  [Fintype TPS.Proof] [DecidableEq TPS.Proof] in
/-- **The game's challenger never reprograms.** -/
theorem unforgeChallenger_noAssign (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    (unforgeChallenger (ofBase B PS adm) n (SideOracle.none _) keys Q).NoAssign := by
  intro c hist r G
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

omit [DecidableEq Y] [AddGroup Y] [Fintype TPS.Proof] [DecidableEq TPS.Proof] in
/-- **The game's reply** to request number `|rs|` below `Q`: `ringReply` at the coins of that
number. -/
theorem answerAfter_unforgeChallenger (keys : Fin n → B.KeyCoins) (Q : ℕ) (H : X → Y)
    (c : Fin Q → B.Coins × PS.Coins) (rs : List (RReq B PS adm n (SideOracle.none _)))
    (r : RReq B PS adm n (SideOracle.none _)) (hi : rs.length < Q) :
    (unforgeChallenger (ofBase B PS adm) n (SideOracle.none _) keys Q).toPureEnv.answerAfter
      (H, c) rs r = ringReply B PS adm keys H (c ⟨rs.length, hi⟩) r := by
  have hn := unforgeChallenger_noAssign (PS := PS) (adm := adm) keys Q
  obtain ⟨-, -, h3⟩ := hn.oracleIn H c rs
  rw [hn.answerAfter_eq H c rs r hi]
  have hl : ((unforgeChallenger (ofBase B PS adm) n (SideOracle.none _) keys Q).toPureEnv.oracleIn
      (H, c) rs).hist.length = rs.length := by
    rw [h3]
    exact min_eq_left hi.le
  generalize ((unforgeChallenger (ofBase B PS adm) n (SideOracle.none _) keys Q).toPureEnv.oracleIn
    (H, c) rs).hist = hist at hl ⊢
  have hi' : hist.length < Q := hl ▸ hi
  have hf : (⟨hist.length, hi'⟩ : Fin Q) = ⟨rs.length, hi⟩ := Fin.ext hl
  simp only [unforgeChallenger, hi', ↓reduceDIte, hf]
  rcases r with i | ⟨s, R, m⟩ | ⟨i, bm⟩
  · rfl
  · simp only [ringReply]
    split_ifs
    · simp [OracleProg.run_bind]
    · rfl
  · exact bm.elim

end Game

/-! ### The main challenger -/

variable [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.BSig]
  [DecidableEq TB.BSig] [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins]
  [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins]

variable (B PS adm n) in
/-- **The prover of the relayed proof queries**: on a relayed statement `x` (a ring statement and a
request) and a witness register `w`, `PS`'s prover on the ring statement `x.1` and the ring witness
of `w`. Its coins are uniform: the challengers draw them from `PMF.uniformOfFintype PS.Coins`. -/
def ringProver :
    NARG.Prover X Y (Insider.RelayStmt B PS adm n) (Insider.RelayWit B) PS.Proof PS.Coins where
  prog x w c := PS.prove x.1 w.toWit c
  q := PS.q
  prog_queries _ _ _ := PS.prove_queries _ _ _

section Main

variable [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y]

variable (B PS adm n) in
/-- **The main challenger of the strong relay** at the users' key coins `keys`, with `Q` requests
for each part: the sum of the multi-user challenger with the ring-aware signing oracle and the real
challenger of the relayed proof queries (the trivial relation, the prover `ringProver`). -/
noncomputable def strongMain (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    Challenger X Y (StrongReq B PS adm n) (StrongResp B PS) :=
  Challenger.sum (muChallenger (SignOracle.ring B) n keys Q)
    (realChallenger (fun _ _ => True) (ringProver B PS adm n) (PMF.uniformOfFintype _) Q)

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]
  [Nonempty TB.KeyCoins] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] in
/-- **The main challenger never reprograms.** -/
theorem strongMain_noAssign (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    (strongMain B PS adm n keys Q).NoAssign :=
  (muChallenger_noAssign _ keys Q).sum (realChallenger_noAssign _ _ _ Q)

variable (keys : Fin n → B.KeyCoins) (Q : ℕ) (H : X → Y)
  (c' : (Fin Q → B.Coins) × (Fin Q → PS.Coins))

/-- The main challenger's replies. -/
noncomputable abbrev strongAns : List (StrongReq B PS adm n) → StrongReq B PS adm n →
    Option (StrongResp B PS) :=
  (strongMain B PS adm n keys Q).toPureEnv.answerAfter (H, c')

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]
  [Nonempty TB.KeyCoins] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] in
/-- **The main reply to a multi-user request** after main requests `L` with `k < Q` multi-user
requests and at most `Q` proof queries: the multi-user reply with the coins number `k`. -/
theorem strongAns_inl (L : List (StrongReq B PS adm n)) (x : MURequest (SignOracle.ring B) n)
    {k : ℕ} (hk : k < Q) (hl : (L.filterMap Sum.getLeft?).length = k)
    (hr : (L.filterMap Sum.getRight?).length ≤ Q) :
    strongAns keys Q H c' L (.inl x) =
      (muReply (SignOracle.ring B) keys H (c'.1 ⟨k, hk⟩) x).map Sum.inl := by
  subst hl
  change (Challenger.sum (muChallenger (SignOracle.ring B) n keys Q)
    (realChallenger (fun _ _ => True) (ringProver B PS adm n) (PMF.uniformOfFintype _) Q)).toPureEnv.answerAfter (H, c') L
      (.inl x) = _
  rw [(muChallenger_noAssign (SignOracle.ring B) keys Q).answerAfter_sum_inl
    (realChallenger_noAssign (fun _ _ => True) (ringProver B PS adm n) (PMF.uniformOfFintype _) Q) H c' L x hk hr,
    answerAfter_muChallenger _ keys Q H c'.1 _ x hk]

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]
  [Nonempty TB.KeyCoins] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] in
/-- **The main reply to a proof query** after main requests `L` with at most `Q` multi-user
requests and `k < Q` proof queries: the proof of `PS` with the coins number `k`. -/
theorem strongAns_inr (L : List (StrongReq B PS adm n))
    (x : ProofQuery (Insider.RelayStmt B PS adm n) (Insider.RelayWit B)) {k : ℕ} (hk : k < Q)
    (hl : (L.filterMap Sum.getLeft?).length ≤ Q) (hr : (L.filterMap Sum.getRight?).length = k) :
    strongAns keys Q H c' L (.inr x) =
      some (.inr ((PS.prove x.stmt.1 x.wit.toWit (c'.2 ⟨k, hk⟩)).run H)) := by
  subst hr
  change (Challenger.sum (muChallenger (SignOracle.ring B) n keys Q)
    (realChallenger (fun _ _ => True) (ringProver B PS adm n) (PMF.uniformOfFintype _) Q)).toPureEnv.answerAfter (H, c') L
      (.inr x) = _
  rw [(muChallenger_noAssign (SignOracle.ring B) keys Q).answerAfter_sum_inr
    (realChallenger_noAssign (fun _ _ => True) (ringProver B PS adm n) (PMF.uniformOfFintype _) Q) H c' L x hl hk,
    answerAfter_realChallenger _ _ _ Q H c'.2 _ x hk]
  simp only [↓reduceIte]
  rfl

/-! ### The relayed requests against the main challenger -/

variable [Zero Y] [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig]

omit [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y] [Nonempty Y]
  [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] [Fintype TB.BSig] [DecidableEq TB.BSig] [Fintype TB.Pub] [DecidableEq TB.Pub]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] [Fintype TB.Coins]
  [DecidableEq TB.Coins] [Nonempty TB.Coins] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg]
  in
/-- The dummy proof query runs with its reply. -/
theorem runsWith_askDummy (ansM : List (StrongReq B PS adm n) → StrongReq B PS adm n →
      Option (StrongResp B PS)) (rs : List (StrongReq B PS adm n))
    (r : RReq B PS adm n (SideOracle.none _)) (o : Option (RResp B PS adm (SideOracle.none _))) :
    MultiRelay.RunsWith ansM H rs (askDummy B PS adm r o) o [.inr (dummyQuery B PS adm r)] 0 :=
  (MultiRelay.runsWith_askResp ansM H rs _).mapOutput (fun _ => o)

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]
  [Nonempty TB.KeyCoins] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] in
/-- **A relayed request runs with the game's reply**: the request `r`, after main requests `L` with
`k < Q` multi-user requests and `k` proof queries, runs with the game's reply at the coins
`(c'.1 k, c'.2 k)`, a multi-user request and then a proof query, and at most `qPub` queries. -/
theorem runsWith_strongProg (L : List (StrongReq B PS adm n)) {k : ℕ} (hk : k < Q)
    (hl : (L.filterMap Sum.getLeft?).length = k) (hr : (L.filterMap Sum.getRight?).length = k)
    (r : RReq B PS adm n (SideOracle.none _)) :
    ∃ a b q, MultiRelay.RunsWith (strongAns keys Q H c') H L
      (strongProg B PS adm (fun i => B.pk (keys i)) r)
      (ringReply B PS adm keys H (c'.1 ⟨k, hk⟩, c'.2 ⟨k, hk⟩) r) [.inl a, .inr b] q ∧
      q ≤ B.qPub := by
  rcases r with i | ⟨s, R, m⟩ | ⟨i, bm⟩
  · have h1 := MultiRelay.runsWith_askResp (strongAns keys Q H c') H L
      (.inl (.corrupt i) : StrongReq B PS adm n)
    rw [strongAns_inl keys Q H c' L _ hk hl (hr ▸ hk.le)] at h1
    have h2 := runsWith_askDummy H (strongAns keys Q H c') (L ++ [.inl (.corrupt i)]) (.corrupt i)
      (some (.keyCoins (keys i)))
    exact ⟨_, _, _, h1.bind h2, Nat.zero_le _⟩
  · simp only [strongProg]
    by_cases hc : B.pk (keys s) ∈ R.1 ∧ adm R
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
      have h1 := MultiRelay.runsWith_askResp (strongAns keys Q H c') H L
        (.inl (.sign s (R, m)) : StrongReq B PS adm n)
      have ha : strongAns keys Q H c' L (.inl (.sign s (R, m))) =
          ((B.bsign (B.keyGen (keys s)).2 R (R.1.idxOf (B.pk (keys s))) m
            (c'.1 ⟨k, hk⟩)).run H).map fun σ => .inl (.signature σ) := by
        rw [strongAns_inl keys Q H c' L _ hk hl (hr ▸ hk.le)]
        have hm : (B.keyGen (keys s)).1 ∈ R.1 := hc.1
        simp only [muReply, SignOracle.ring]
        split_ifs with h
        · simp only [Option.map_map, Function.comp_def]
          rfl
        · exact absurd hm h
      rw [ha] at h1
      rcases hb : (B.bsign (B.keyGen (keys s)).2 R (R.1.idxOf (B.pk (keys s))) m
          (c'.1 ⟨k, hk⟩)).run H with _ | σ
      · rw [hb, Option.map_none] at h1
        have h2 := runsWith_askDummy H (strongAns keys Q H c') (L ++ [.inl (.sign s (R, m))])
          (.sign s R m) none
        refine ⟨_, _, _, (h1.bind h2).congr_res ?_, Nat.zero_le _⟩
        rw [ringReply_sign_of_mem keys H _ hc.1 hc.2]
        simp only [signAt_eq, OracleProg.run_bind]
        rw [show (B.bsign (B.keyGen (keys s)).2 R (R.1.idxOf (B.pk (keys s))) m
          (c'.1 ⟨k, hk⟩, c'.2 ⟨k, hk⟩).1).run H = none from hb]
        rfl
      · rw [hb, Option.map_some] at h1
        have hp := MultiRelay.RunsWith.liftQ (ansM := strongAns keys Q H c') (H := H)
          (Resp' := StrongResp B PS) (L ++ [.inl (.sign s (R, m))]) (B.pub (B.pk (keys s)) σ)
        have hlen : R.1.idxOf (B.pk (keys s)) < N + 1 :=
          Nat.lt_succ_of_le ((List.idxOf_lt_length_of_mem hc.1).le.trans R.2)
        have hq := MultiRelay.runsWith_askResp (strongAns keys Q H c') H
          (L ++ [.inl (.sign s (R, m))] ++ [])
          (.inr ⟨(⟨R, m, (B.pub (B.pk (keys s)) σ).run H⟩, .sign s R m),
            (⟨min (R.1.idxOf (B.pk (keys s))) N, by omega⟩, σ)⟩ : StrongReq B PS adm n)
        rw [strongAns_inr keys Q H c' _ _ hk (by simp [List.filterMap_append, hl]; omega)
          (by simp [List.filterMap_append, hr])] at hq
        refine ⟨_, _, _, (h1.bind (hp.bind (hq.mapOutput _))).congr_res ?_, ?_⟩
        · rw [ringReply_sign_of_mem keys H _ hc.1 hc.2,
            run_signAt_of_bsign B PS (c := (c'.1 ⟨k, hk⟩, c'.2 ⟨k, hk⟩)) hb]
          simp [Insider.RelayWit.toWit, min_eq_left (Nat.le_of_lt_succ hlen)]
        · simp only [Nat.zero_add, Nat.add_zero]
          exact B.pub_queries _ _ H
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
      have h1 := MultiRelay.runsWith_askResp (strongAns keys Q H c') H L
        (.inl (.publicKey s) : StrongReq B PS adm n)
      have h2 := runsWith_askDummy H (strongAns keys Q H c') (L ++ [.inl (.publicKey s)])
        (.sign s R m) none
      exact ⟨_, _, _, (h1.bind h2).congr_res (ringReply_sign_of_not keys H _ hc).symm,
        Nat.zero_le _⟩
  · exact bm.elim

/-! ### The game's challenger relays the main challenger -/

variable [Inhabited X] [NeZero n]

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]
  [Nonempty TB.KeyCoins] in
/-- **The main requests after the requests `rs`** (at most `Q`) have `|rs|` multi-user requests and
`|rs|` proof queries: each request makes a multi-user request and then a proof query. -/
theorem length_mainReqs_strong (i₁ : Fin n) (rs : List (RReq B PS adm n (SideOracle.none _)))
    (hrs : rs.length ≤ Q) :
    (((strongRelay B PS adm (fun i => B.pk (keys i)) i₁).mainReqs Q (strongAns keys Q H c') H
        rs).filterMap Sum.getLeft?).length = rs.length ∧
      (((strongRelay B PS adm (fun i => B.pk (keys i)) i₁).mainReqs Q (strongAns keys Q H c') H
        rs).filterMap Sum.getRight?).length = rs.length := by
  induction rs using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl⟩
  | append_singleton rs r ih =>
    simp only [List.length_append, List.length_singleton] at hrs ⊢
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    obtain ⟨a, b, q, h, hq⟩ :=
      runsWith_strongProg keys Q H c' _ (by omega : rs.length < Q) ih1 ih2 r
    have he := MultiRelay.filterMap_runEntries_of_runsWith
      (strongRelay B PS adm (fun i => B.pk (keys i)) i₁) (strongAns keys Q H c') H rfl h le_rfl hq
    rw [MultiRelay.mainReqs_append, ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
      List.filterMap_append, List.filterMap_append, he, List.length_append, List.length_append,
      ih1, ih2]
    constructor <;> simp [strongRelay, List.filterMap_cons]

omit [Nonempty TB.KeyCoins] in
/-- **The game's challenger with `Q` requests is the relay `strongRelay` of the main challenger**
`strongMain keys Q` (`MultiRelay.RelaysChallenger`), along the pairing of the two parts' coins:
request number `j` reads the multi-user coins and the prover's coins number `j`. -/
theorem relaysChallenger_strongRelay (i₁ : Fin n) :
    (strongRelay B PS adm (fun i => B.pk (keys i)) i₁).RelaysChallenger
      (unforgeChallenger (ofBase B PS adm) n (SideOracle.none _) keys Q)
      (strongMain B PS adm n keys Q) (fun c' j => (c'.1 j, c'.2 j)) where
  coins_eq := by
    change PMF.uniformOfFintype _ = ((PMF.uniformOfFintype (Fin Q → B.Coins)).bind fun c₁ =>
      (PMF.pi fun _ => PMF.uniformOfFintype PS.Coins).map fun c₂ => (c₁, c₂)).map _
    rw [PMF.pi_uniformOfFintype, ← PMF.uniformOfFintype_prod_eq_bind]
    exact (PMF.map_uniformOfFintype_equiv (Equiv.arrowProdEquivProdArrow _ _ _).symm).symm
  oracle_eq H c _ lg := (unforgeChallenger_noAssign keys Q).oracle_eq H c lg
  oracle_eq' H c' _ lg := (strongMain_noAssign keys Q).oracle_eq H c' lg
  answer_eq H c' rs r hi := by
    have hi' : rs.length < Q := hi
    rw [answerAfter_unforgeChallenger keys Q H _ rs r hi']
    obtain ⟨hl, hr⟩ := length_mainReqs_strong keys Q H c' i₁ rs hi'.le
    obtain ⟨a, b, q, h, hq⟩ := runsWith_strongProg keys Q H c' _ hi' hl hr r
    exact ((strongRelay B PS adm (fun i => B.pk (keys i)) i₁).runReply_eq_of_runsWith rfl h le_rfl
      hq).symm

end Main

/-! ### The main requests of the relay and freshness -/

section Fresh

variable (B PS adm) in
/-- **The main request a request relays to**: a proof query, or the multi-user request of the same
corruption, or of the signing request or the public key of the same user for a ring-signing
request. -/
def StrongAsk (r : RReq B PS adm n (SideOracle.none _)) : StrongReq B PS adm n → Prop
  | .inl r' => match r with
    | .corrupt i => r' = .corrupt i
    | .sign s R m => r' = .sign s (R, m) ∨ r' = .publicKey s
    | .sideSign _ _ => False
  | .inr _ => True

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] [Fintype TB.BSig] [DecidableEq TB.BSig] [Fintype TB.Pub] [DecidableEq TB.Pub]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] [Fintype TB.PK]
  [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] in
/-- **Every main request of a relay program is one its request relays to.** -/
theorem asksIn_strongProg [Zero Y] [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig]
    (pks : Fin n → B.PK) (r : RReq B PS adm n (SideOracle.none _)) :
    MultiRelay.AsksIn (StrongResp B PS) (strongProg B PS adm pks r) (StrongAsk B PS adm r) := by
  have hd : ∀ o, MultiRelay.AsksIn (StrongResp B PS) (askDummy B PS adm r o)
      (StrongAsk B PS adm r) := fun o =>
    (MultiRelay.asksIn_askResp_of _ trivial).mapOutput _
  rcases r with i | ⟨s, R, m⟩ | ⟨i, bm⟩
  · refine MultiRelay.AsksIn.bind (MultiRelay.asksIn_askResp_of _ (by simp [StrongAsk])) fun o => ?_
    rcases o with _ | (_ | _ | _) | _ <;> exact hd _
  · simp only [strongProg]
    split_ifs
    · refine MultiRelay.AsksIn.bind (MultiRelay.asksIn_askResp_of _ (by simp [StrongAsk]))
        fun o => ?_
      rcases o with _ | (_ | σ | _) | _
      · exact hd _
      · exact hd _
      · exact MultiRelay.AsksIn.bind (MultiRelay.AsksIn.liftQ _ _) fun y =>
          (MultiRelay.asksIn_askResp_of _ trivial).mapOutput _
      · exact hd _
      · exact hd _
    · exact MultiRelay.AsksIn.bind (MultiRelay.asksIn_askResp_of _ (by simp [StrongAsk]))
        fun _ => hd _
  · exact bm.elim

variable (B PS) in
/-- **A ring forgery is fresh for the multi-user requests `mrs`**: every key of its ring is the key
of a user that no request of `mrs` corrupts, and no request of `mrs` asks a user to sign its ring
and message. -/
def StrongFreshReq (keys : Fin n → B.KeyCoins) (o : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof))
    (mrs : List (MURequest (SignOracle.ring B) n)) : Prop :=
  (∀ pk ∈ o.1.1, ∃ i, B.pk (keys i) = pk ∧ MURequest.corrupt i ∉ mrs) ∧
    ∀ s, MURequest.sign s (o.1, o.2.1) ∉ mrs

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] [Fintype TB.BSig] [DecidableEq TB.BSig] [Fintype TB.Pub] [DecidableEq TB.Pub]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] [Fintype TB.PK]
  [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] in
/-- **Freshness passes through the strong relay**: if every main request is the idle public-key
request or one that a request of `grs` relays to (`StrongAsk`), a ring forgery fresh for `grs` is
fresh for the multi-user main requests. -/
theorem strongFreshReq_of_relay {keys : Fin n → B.KeyCoins} {i₁ : Fin n}
    {o : KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof)}
    {grs : List (RReq B PS adm n (SideOracle.none _))} {mrs : List (StrongReq B PS adm n)}
    (hf : RingFreshReq B PS adm keys o grs)
    (hrel : ∀ r' ∈ mrs, r' = .inl (.publicKey i₁) ∨ ∃ r ∈ grs, StrongAsk B PS adm r r') :
    StrongFreshReq B PS keys o (mrs.filterMap Sum.getLeft?) := by
  obtain ⟨R₀, m₀, σ₀⟩ := o
  have hmem : ∀ x, x ∈ mrs.filterMap Sum.getLeft? → Sum.inl x ∈ mrs := fun x hx => by
    obtain ⟨a, ha, he⟩ := List.mem_filterMap.1 hx
    rwa [Sum.getLeft?_eq_some_iff.1 he] at ha
  refine ⟨fun pk hpk => ?_, fun s hs => ?_⟩
  · obtain ⟨i, hi, hc⟩ := hf.1 pk hpk
    refine ⟨i, hi, fun hm => ?_⟩
    rcases hrel _ (hmem _ hm) with h | ⟨r, hr, ha⟩
    · cases h
    · rcases r with i' | ⟨s, R, m⟩ | ⟨i', bm⟩
      · have ha' : MURequest.corrupt i = MURequest.corrupt i' := ha
        cases ha'
        exact hc hr
      · have ha' : (MURequest.corrupt i : MURequest (SignOracle.ring B) n) = .sign s (R, m) ∨
            (MURequest.corrupt i : MURequest (SignOracle.ring B) n) = .publicKey s := ha
        rcases ha' with ha' | ha' <;> cases ha'
      · exact bm.elim
  · rcases hrel _ (hmem _ hs) with h | ⟨r, hr, ha⟩
    · cases h
    · rcases r with i' | ⟨s', R, m⟩ | ⟨i', bm⟩
      · have ha' : (MURequest.sign s (R₀, m₀) : MURequest (SignOracle.ring B) n) =
            .corrupt i' := ha
        cases ha'
      · have ha' : (MURequest.sign s (R₀, m₀) : MURequest (SignOracle.ring B) n) =
            .sign s' (R, m) ∨
            (MURequest.sign s (R₀, m₀) : MURequest (SignOracle.ring B) n) = .publicKey s' := ha
        rcases ha' with ha' | ha'
        · cases ha'
          exact hf.2 s hr
        · cases ha'
      · exact bm.elim

end Fresh

/-! ### The game to the main challenger -/

section GameMain

variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] [Nonempty B.Msg] [Nonempty B.Pub] [Nonempty B.BSig] [NeZero n]
  {t : ℕ}

/-- **The game's forgery probability through the strong relay** (BKM06 Definition 7): at most the
average, over the users' key coins and the oracle, of the probability that the strongly relayed
forger against the main challenger `strongMain keys Q` (the multi-user challenger and the real
challenger of proof queries, `Q` requests each) outputs a ring signature that verifies and is fresh
for the multi-user requests of its history (`StrongFreshReq`). -/
theorem insiderForgeProb_le_strongMain
    (A : InsiderAdversary (ofBase B PS adm) n (OracleView.queriesOnly X Y) t) (i₁ : Fin n)
    (Q : ℕ) :
    insiderForgeProb A Q ≤ ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑' H, PMF.uniformOfFintype (X → Y) H *
        ((strongForger B PS adm A (fun i => B.pk (keys i)) i₁ Q).transcriptLaw
          (strongMain B PS adm n keys Q) H).toOuterMeasure
          {x | ∃ p ∈ x, (ofBase B PS adm).verify H p.1.1 p.1.2.1 p.1.2.2 = true ∧
            StrongFreshReq B PS keys p.1
              ((p.2.map HistoryEntry.request).filterMap Sum.getLeft?)} := by
  simp only [insiderForgeProb, forgeProb, unforgeLaw, runLaw, PMF.toOuterMeasure_bind_apply,
    PMF.toOuterMeasure_map_apply]
  refine ENNReal.tsum_le_tsum fun keys => mul_le_mul' le_rfl
    (ENNReal.tsum_le_tsum fun H => mul_le_mul' le_rfl ?_)
  have hsub : (fun o => (keys, H, o)) ⁻¹' {x : (Fin n → B.KeyCoins) × (X → Y) ×
      Option ((KeyRing B.PK N × B.Msg × (B.Pub × PS.Proof)) ×
        UnforgeHist (S := ofBase B PS adm) n (SideOracle.none _)) |
      ∃ p ∈ x.2.2, Forges x.1 x.2.1 p.1 p.2} ⊆
      {x | ∃ p ∈ x, (ofBase B PS adm).verify H p.1.1 p.1.2.1 p.1.2.2 = true ∧
        RingFreshReq B PS adm keys p.1 (p.2.map HistoryEntry.request)} := by
    rintro x ⟨p, hp, hf⟩
    exact ⟨p, hp, hf.verify_eq, hf.fresh.ringFreshReq⟩
  refine (MeasureTheory.measure_mono hsub).trans ?_
  refine (A (fun i => B.pk (keys i), ())).transcriptLaw_le_relay
    (strongRelay B PS adm (fun i => B.pk (keys i)) i₁)
    (unforgeChallenger (ofBase B PS adm) n (SideOracle.none _) keys Q)
    (strongMain B PS adm n keys Q) _ (relaysChallenger_strongRelay keys Q i₁) H
    (fun p => (ofBase B PS adm).verify H p.1.1 p.1.2.1 p.1.2.2 = true ∧
      RingFreshReq B PS adm keys p.1 (p.2.map HistoryEntry.request)) _ ?_
  intro o hist hist' ⟨hv, hf⟩ hrel
  refine ⟨hv, strongFreshReq_of_relay (i₁ := i₁) hf ?_⟩
  intro r' hr'
  obtain ⟨e', he', rfl⟩ := List.mem_map.1 hr'
  rcases hrel e' he' with h | ⟨e, he, hc⟩
  · exact Or.inl h
  · exact Or.inr ⟨e.request, List.mem_map_of_mem he,
      (strongRelay B PS adm (fun i => B.pk (keys i)) i₁).canAsk_of_asksIn
        (asksIn_strongProg _ e.request).plainProg hc⟩

end GameMain

end RingSignature

end GordieHowe
