-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Signature.SingleUser
public import GordieHowe.Model.Signature.MultiUserSim
public import GordieHowe.Model.Signature.RejectionRelay
public import GordieHowe.Model.RingSignature.TranscriptAbsorb
public import GordieHowe.Model.Quantum.Interactive.FreshCoins
public import GordieHowe.Model.Quantum.Interactive.MultiRelayPos
public import GordieHowe.Model.Signature.MultiUserCount
public import GordieHowe.Model.Quantum.Interactive.AbsorbHist

@[expose] public section

/-!
# The single-user adversary guessing the target user

The reduction from the multi-user games (`GordieHowe/Model/Signature/MultiUser.lean`) to the
single-user games (`GordieHowe/Model/Signature/SingleUser.lean`) by guessing the target user
(Bader, Hofheinz, Jager, Kiltz, Li, "Tightly-Secure Authenticated Key Exchange", TCC 2015, ePrint
2014/797, the loss `n` of the generic reduction from the multi-user to the single-user game): the
single-user adversary draws a user `i` uniformly, the key coins of all users and signing coins `ρ`
for the requests, runs the multi-user adversary on the public keys with user `i`'s replaced by
its own, and answers each request about user `i` by the same request about user `0` of its
challenger (a corruption included) and each other request itself, from the drawn key coins and the
signing coins `ρ c` of its request number `c`. Every request is relayed to one request of the
single-user challenger, a request about another user to the public key of user `0`, so that the
two challengers count the same requests.

- `aboutUser i`, `suReq`: a request about user `i`, and the same request about user `0` of the
  single-user game.
- `coinRelay Q ρ`: the relay attaching to request number `c` the signing coins `ρ c`.
- `localProg keys c`, `run_localProg`, `localProg_queries`: the multi-user challenger's reply with
  the signing coins `c` as an oracle program, the signer's queries made by the relay.
- `guessProg i keys`, `guessRelay i keys`: the relay programs and the relay of the requests with
  their coins to the single-user challenger.
- `guessKeys i keys pk`: the public keys with user `i`'s replaced by `pk`.
- `QueryBoundedAdversary.mix μ 𝒜`: the adversary drawing `z` from `μ`, then running `𝒜 z`;
  `transcriptLaw_mix`.
- `suGuess A Q`: the single-user adversary.
-/

namespace GordieHowe.Quantum.QueryBoundedAdversary

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {t : ℕ}

/-- **The mixture of adversaries**: draw `z` from `μ`, then run `𝒜 z` with its auxiliary input. -/
noncomputable def mix {Z : Type} (μ : PMF Z) (𝒜 : Z → QueryBoundedAdversary X Y Req Resp O t) :
    QueryBoundedAdversary X Y Req Resp O t where
  Aux := Σ z, (𝒜 z).Aux
  aux := μ.bind fun z => (𝒜 z).aux.map fun a => ⟨z, a⟩
  sh p := ((𝒜 p.1).alg p.2).toShape
  alg p := (𝒜 p.1).alg p.2
  tracePreserving p := (𝒜 p.1).tracePreserving p.2
  withinBudget p := (𝒜 p.1).withinBudget p.2
  queries_le p := (𝒜 p.1).queries_le p.2

/-- **The transcript of a mixture is the mixture of the transcripts.** -/
theorem transcriptLaw_mix {Z : Type} (μ : PMF Z) (𝒜 : Z → QueryBoundedAdversary X Y Req Resp O t)
    (C : Challenger X Y Req Resp) (H : X → Y) :
    (mix μ 𝒜).transcriptLaw C H = μ.bind fun z => (𝒜 z).transcriptLaw C H := by
  unfold QueryBoundedAdversary.transcriptLaw mix
  simp only [PMF.bind_bind, PMF.bind_map]
  rfl

end GordieHowe.Quantum.QueryBoundedAdversary

namespace GordieHowe.Signature

open GordieHowe.Quantum GordieHowe.RingSignature
open scoped ENNReal

variable {X Y : Type} {TB : SchemeTypes}
  {B : BaseScheme X Y TB} (O : SignOracle B) {n : ℕ}

/-! ### The requests -/

variable [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]
  [Nonempty O.Coins]

variable {O} in
/-- **A request about user `i`**: its public key, a signature of user `i`, or its corruption. -/
def aboutUser (i : Fin n) : MURequest O n → Bool
  | .publicKey j => decide (j = i)
  | .sign j _ => decide (j = i)
  | .corrupt j => decide (j = i)

variable {O} in
/-- **The same request about user `0` of the single-user game.** -/
def suReq : MURequest O n → MURequest O 1
  | .publicKey _ => .publicKey 0
  | .sign _ sm => .sign 0 sm
  | .corrupt _ => .corrupt 0

/-- **The relay attaching the signing coins** `ρ c` to request number `c` (an arbitrary value from
request `Q` on), the reply passed on. -/
noncomputable def coinRelay (Q : ℕ) (ρ : Fin Q → O.Coins) :
    SideRelay (MURequest O n) (MUResponse B) (O.Coins × MURequest O n) (MUResponse B) where
  route c r := (if h : c < Q then ρ ⟨c, h⟩ else Classical.arbitrary _, r)
  answer _ _ a := a

omit [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] in
/-- The relay of a request number is injective. -/
theorem coinRelay_route_injective (Q : ℕ) (ρ : Fin Q → O.Coins) (c : ℕ) :
    Function.Injective ((coinRelay O (n := n) Q ρ).route c) :=
  fun _ _ h => congrArg Prod.snd h

section Relay

variable [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y]

/-- **The multi-user challenger's reply with the signing coins `c`, as an oracle program**: the
public key, the signer's program on the request's message with the coins `c` (at most `O.q`
queries), or the key coins. -/
noncomputable def localProg (keys : Fin n → B.KeyCoins) (c : O.Coins) :
    MURequest O n → OracleProg X Y (Option (MUResponse B))
  | .publicKey j => .pure (some (.publicKey (B.pk (keys j))))
  | .sign j sm => (O.sign (B.keyGen (keys j)) sm c).mapOutput fun o => o.map .signature
  | .corrupt j => .pure (some (.keyCoins (keys j)))

omit [Nonempty O.Coins] [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins]
  [DecidableEq O.Coins] in
/-- **The program's result is the multi-user challenger's reply.** -/
theorem run_localProg (keys : Fin n → B.KeyCoins) (c : O.Coins) (H : X → Y) (r : MURequest O n) :
    (localProg O keys c r).run H = muReply O keys H c r := by
  rcases r with j | ⟨j, sm⟩ | j
  · rfl
  · simp only [localProg, OracleProg.run_mapOutput, muReply]
  · rfl

omit [Nonempty O.Coins] [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins]
  [DecidableEq O.Coins] in
/-- The program makes at most `O.q` queries. -/
theorem localProg_queries (keys : Fin n → B.KeyCoins) (c : O.Coins) (H : X → Y)
    (r : MURequest O n) : ((localProg O keys c r).trace H).length ≤ O.q := by
  rcases r with j | ⟨j, sm⟩ | j
  · simp [localProg]
  · simp only [localProg, OracleProg.trace_mapOutput]
    exact O.sign_queries _ _ _ H
  · simp [localProg]

/-- **The relay program of a request with its signing coins**: a request about user `i` asked of
the single-user challenger as the same request about user `0`; any other request answered by
`localProg keys c` with relay queries, with no main request. -/
noncomputable def guessProg (i : Fin n) (keys : Fin n → B.KeyCoins) :
    O.Coins × MURequest O n →
      OracleProg (X ⊕ MURequest O 1) (Y ⊕ Option (MUResponse B)) (Option (MUResponse B))
  | (c, r) => if aboutUser i r then askResp (suReq r) else MultiRelay.liftQ (localProg O keys c r)

/-- **The relay to the single-user challenger**: the programs `guessProg i keys`, one main request
per request (a request answered locally is padded with the idle request, the public key of user
`0`), at most `O.q` queries (the signer's). -/
noncomputable def guessRelay (i : Fin n) (keys : Fin n → B.KeyCoins) :
    MultiRelay X Y (O.Coins × MURequest O n) (MUResponse B) (MURequest O 1) (MUResponse B) where
  prog := MultiRelay.plainProg (guessProg O i keys)
  K := 1
  K_pos := Nat.one_pos
  qR := O.q
  idle := .publicKey 0

end Relay


/-! ### The challenger of requests with their coins -/

variable [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]

section Challenger

variable [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y]

/-- **The multi-user challenger answering requests with their signing coins** at the users' key
coins `keys`: request number `j` about user `i` is answered with the challenger's coins `a j`, any
other request with the coins it carries. -/
noncomputable def guessChallenger (i : Fin n) (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    Challenger X Y (O.Coins × MURequest O n) (MUResponse B) where
  Coins := Fin Q → O.Coins
  coins := PMF.uniformOfFintype _
  Q := Q
  q := O.q
  respond a hist r :=
    if h : hist.length < Q then
      match r.2 with
      | .publicKey j => .pure ⟨some (.publicKey (B.pk (keys j))), []⟩
      | .sign j sm =>
        (O.sign (B.keyGen (keys j)) sm (if aboutUser i r.2 then a ⟨hist.length, h⟩ else r.1)).bind
          fun o => .pure ⟨o.map .signature, []⟩
      | .corrupt j => .pure ⟨some (.keyCoins (keys j)), []⟩
    else .pure ⟨none, []⟩
  respond_queries a hist r H := by
    by_cases h : hist.length < Q
    · rw [dif_pos h]
      rcases r with ⟨c, j | ⟨j, sm⟩ | j⟩
      · simp
      · dsimp only
        rw [OracleProg.trace_bind, OracleProg.trace_pure, List.append_nil]
        exact O.sign_queries _ _ _ H
      · simp
    · rw [dif_neg h]
      simp

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Fintype O.SMsg] [DecidableEq O.SMsg] in
/-- The challenger assigns nothing. -/
theorem guessChallenger_noAssign (i : Fin n) (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    (guessChallenger O i keys Q).NoAssign := by
  intro c hist r G
  simp only [guessChallenger]
  by_cases h : hist.length < Q
  · rw [dif_pos h]
    rcases r with ⟨c', j | ⟨j, sm⟩ | j⟩ <;> simp [OracleProg.run_bind]
  · rw [dif_neg h]
    rfl

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Fintype O.SMsg] [DecidableEq O.SMsg] in
/-- **The challenger's reply** to a request numbered below `Q` is `muReply` with the challenger's
coins of that request for a request about user `i`, with the request's coins otherwise. -/
theorem answerAfter_guessChallenger (i : Fin n) (keys : Fin n → B.KeyCoins) (Q : ℕ) (H : X → Y)
    (a : Fin Q → O.Coins) (rs : List (O.Coins × MURequest O n)) (r : O.Coins × MURequest O n)
    (hi : rs.length < Q) :
    (guessChallenger O i keys Q).toPureEnv.answerAfter (H, a) rs r =
      muReply O keys H (if aboutUser i r.2 then a ⟨rs.length, hi⟩ else r.1) r.2 := by
  have hn := guessChallenger_noAssign O i keys Q
  obtain ⟨-, -, h3⟩ := hn.oracleIn H a rs
  rw [hn.answerAfter_eq H a rs r hi]
  have hl : ((guessChallenger O i keys Q).toPureEnv.oracleIn (H, a) rs).hist.length =
      rs.length := by
    rw [h3]
    exact min_eq_left (le_of_lt hi)
  generalize ((guessChallenger O i keys Q).toPureEnv.oracleIn (H, a) rs).hist = hist at hl ⊢
  have hi' : hist.length < Q := hl ▸ hi
  have hf : (⟨hist.length, hi'⟩ : Fin Q) = ⟨rs.length, hi⟩ := Fin.ext hl
  simp only [guessChallenger]
  rw [dif_pos hi']
  rcases r with ⟨c, j | ⟨j, sm⟩ | j⟩
  · rfl
  · simp only [OracleProg.run_bind, muReply, hf]
    rfl
  · rfl


omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Fintype O.Coins] [DecidableEq O.Coins]
  [Nonempty O.Coins] [Fintype O.SMsg] [DecidableEq O.SMsg] in
/-- **A request about user `i` is answered as the same request about user `0` at user `i`'s key
coins.** -/
theorem muReply_suReq (keys : Fin n → B.KeyCoins) (H : X → Y) (c : O.Coins) {i : Fin n}
    {r : MURequest O n} (hr : aboutUser i r = true) :
    muReply O keys H c r = muReply O (fun _ : Fin 1 => keys i) H c (suReq r) := by
  rcases r with j | ⟨j, sm⟩ | j <;> simp only [aboutUser, decide_eq_true_eq] at hr <;> subst hr <;>
    rfl

variable [Inhabited X]

/-- **The challenger of requests with their coins is the relay `guessRelay` of the single-user
challenger** at user `i`'s key coins (`MultiRelay.RelaysChallenger`), both answering `Q` requests
at the same coins: a request about user `i` is answered as the single-user challenger answers it
about user `0`, any other request as the relay answers it itself, with the signer's queries. -/
theorem relaysChallenger_guessRelay (i : Fin n) (keys : Fin n → B.KeyCoins)
    (Q : ℕ) :
    (guessRelay O i keys).RelaysChallenger (guessChallenger O i keys Q)
      (muChallenger O 1 (fun _ => keys i) Q) id := by
  exact {
    coins_eq := (PMF.map_id _).symm
    oracle_eq := fun H c _ lg => (guessChallenger_noAssign O i keys Q).oracle_eq H c lg
    oracle_eq' := fun H c' _ lg => (muChallenger_noAssign O _ Q).oracle_eq H c' lg
    answer_eq := fun H c' rs r hi => by
      have hi' : rs.length < Q := hi
      have hlen := (guessRelay O i keys).length_mainReqs Q
        ((muChallenger O 1 (fun _ => keys i) Q).toPureEnv.answerAfter (H, c')) H rs hi'.le
      have hlt : ((guessRelay (X := X) (Y := Y) O i keys).mainReqs Q
          ((muChallenger O 1 (fun _ => keys i) Q).toPureEnv.answerAfter (H, c')) H rs).length
            < Q := by
        rw [hlen]
        change 1 * rs.length < Q
        omega
      refine (answerAfter_guessChallenger O i keys Q H c' rs r hi).trans ?_
      by_cases hr : aboutUser i r.2 = true
      · rw [if_pos hr]
        have h := MultiRelay.RunsWith.query_inr
          (ansM := (muChallenger O 1 (fun _ => keys i) Q).toPureEnv.answerAfter (H, c')) (H := H)
          (rs := (guessRelay (X := X) (Y := Y) O i keys).mainReqs Q
            ((muChallenger O 1 (fun _ => keys i) Q).toPureEnv.answerAfter (H, c')) H rs)
          (k := fun b => OracleProg.pure (b.elim (fun _ => none) id)) (suReq r.2)
          (MultiRelay.RunsWith.pure _ _)
        refine Eq.trans ?_ ((guessRelay O i keys).runReply_eq_of_runsWith (r := r) rfl
          (by simp only [guessRelay, guessProg, if_pos hr]; exact h) (by simp [guessRelay])
          (Nat.zero_le _)).symm
        rw [answerAfter_muChallenger O _ Q H c' _ _ hlt]
        have hf : (⟨_, hlt⟩ : Fin Q) = ⟨rs.length, hi'⟩ := Fin.ext (hlen.trans (one_mul _))
        rw [hf]
        exact muReply_suReq O keys H _ hr
      · rw [if_neg hr]
        have h := MultiRelay.RunsWith.liftQ
          (ansM := (muChallenger O 1 (fun _ => keys i) Q).toPureEnv.answerAfter (H, c')) (H := H)
          ((guessRelay (X := X) (Y := Y) O i keys).mainReqs Q
            ((muChallenger O 1 (fun _ => keys i) Q).toPureEnv.answerAfter (H, c')) H rs)
          (localProg O keys r.1 r.2)
        refine Eq.trans ?_ ((guessRelay O i keys).runReply_eq_of_runsWith (r := r) rfl
          (by simp only [guessRelay, guessProg, if_neg hr]; exact h) (by simp [guessRelay])
          (localProg_queries O keys _ H _)).symm
        exact (run_localProg O keys _ H _).symm }


omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Fintype O.SMsg] [DecidableEq O.SMsg] in
/-- **The multi-user challenger signing user `i`'s requests with its coins and the others with `ρ`
relays the challenger of requests with their coins** through `coinRelay Q ρ`, at the same coins. -/
theorem relaysChallenger_coinRelay (i : Fin n) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (ρ : Fin Q → O.Coins) (a : Fin Q → O.Coins) :
    (coinRelay O Q ρ).RelaysChallenger (muChallengerAt O n keys Q (aboutUser i) ρ) a
      (guessChallenger O i keys Q) a where
  Q_eq := rfl
  run_eq hist hist' r G hrel hlt := by
    have hl : hist'.length = hist.length := by
      have := congrArg List.length hrel
      simpa [SideRelay.length_relayList] using this
    have hlt' : hist.length < Q := hlt
    have hl' : hist'.length < Q := hl ▸ hlt'
    have hc : a ⟨hist'.length, hl'⟩ = a ⟨hist.length, hlt'⟩ := congrArg a (Fin.ext hl)
    simp only [muChallengerAt, guessChallenger, dif_pos hlt', dif_pos hl', coinRelay]
    rcases r with j | ⟨j, sm⟩ | j
    · rfl
    · simp only [hc]
    · rfl
  answer_none _ _ _ := rfl

end Challenger


/-! ### The forgery events -/

section Events

variable {O}

/-- **User `i` qualifies** for the forgery `f` at the requests `rs`: the signature verifies, the key
is user `i`'s, and no request corrupts user `i` or asks it to sign for the base message. -/
def Qual (keys : Fin n → B.KeyCoins) (H : X → Y) (i : Fin n) (f : B.PK × B.BMsg × B.BSig)
    (rs : List (MURequest O n)) : Prop :=
  B.bverify H f.1 f.2.1 f.2.2 = true ∧ B.pk (keys i) = f.1 ∧ MURequest.corrupt i ∉ rs ∧
    ∀ sm, MURequest.sign i sm ∈ rs → O.base sm ≠ f.2.1

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Fintype O.SMsg] [DecidableEq O.SMsg]
  [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins] in
/-- **A forgery of MU-EUF-CMA^corr is one for which some user qualifies** at the history's
requests. -/
theorem Forges.exists_qual {keys : Fin n → B.KeyCoins} {H : X → Y} {f : B.PK × B.BMsg × B.BSig}
    {hist : MUHist O n} (h : Forges keys H f hist) :
    ∃ i, Qual keys H i f (hist.map HistoryEntry.request) := by
  obtain ⟨i, hi, hc, hs⟩ := h.exists_user
  refine ⟨i, h.verify_eq, hi, fun hm => hc ?_, fun sm hm hb => hs ?_⟩
  · obtain ⟨e, he, hr⟩ := List.mem_map.1 hm
    exact ⟨e, he, hr⟩
  · obtain ⟨e, he, hr⟩ := List.mem_map.1 hm
    exact ⟨e, he, sm, hr, hb⟩

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Fintype O.SMsg] [DecidableEq O.SMsg]
  [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins] in
/-- **A request with its coins is about user `i` exactly when its request is.** The main request of
`guessProg i keys` at a request about user `i` is its `suReq`; it asks nothing at another. -/
theorem asksIn_guessProg [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y]
    [AddGroup Y] [Nonempty Y] (i : Fin n) (keys : Fin n → B.KeyCoins)
    (r : O.Coins × MURequest O n) :
    MultiRelay.AsksIn (MUResponse B) (guessProg O i keys r)
      (fun r' => aboutUser i r.2 = true ∧ r' = suReq r.2) := by
  obtain ⟨c, r⟩ := r
  simp only [guessProg]
  split_ifs with h
  · exact fun ans r' hr => ⟨h, asksIn_askResp (X := X) (Y := Y) (Resp' := MUResponse B) (suReq r)
      ans r' hr⟩
  · exact MultiRelay.AsksIn.liftQ _ _

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Fintype O.SMsg] [DecidableEq O.SMsg]
  [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins] in
/-- **A qualifying user `i` gives a forgery of the single-user game** at user `i`'s key coins for
every history of main requests that are the idle request or the `suReq` of requests about user `i`
of a history at which user `i` qualifies. -/
theorem Qual.forges_su {keys : Fin n → B.KeyCoins} {H : X → Y} {i : Fin n}
    {f : B.PK × B.BMsg × B.BSig} {rs : List (MURequest O n)} (hq : Qual keys H i f rs)
    {hist' : MUHist O 1}
    (h : ∀ e' ∈ hist', e'.request = .publicKey 0 ∨
      ∃ r ∈ rs, aboutUser i r = true ∧ e'.request = suReq r) :
    Forges (fun _ => keys i) H f hist' := by
  obtain ⟨hv, hk, hc, hs⟩ := hq
  refine ⟨hv, 0, hk, ?_, ?_⟩
  · rintro ⟨e', he', hr⟩
    rcases h e' he' with h1 | ⟨r, hr', ha, hreq⟩
    · rw [hr] at h1
      cases h1
    · rw [hr] at hreq
      rcases r with j | ⟨j, sm⟩ | j <;> simp only [suReq, reduceCtorEq] at hreq
      simp only [aboutUser, decide_eq_true_eq] at ha
      exact hc (ha ▸ hr')
  · rintro ⟨e', he', sm, hr, hb⟩
    rcases h e' he' with h1 | ⟨r, hr', ha, hreq⟩
    · rw [hr] at h1
      cases h1
    · rw [hr] at hreq
      rcases r with j | ⟨j, sm'⟩ | j <;>
        simp only [suReq, reduceCtorEq, MURequest.sign.injEq] at hreq
      simp only [aboutUser, decide_eq_true_eq] at ha
      obtain ⟨-, rfl⟩ := hreq
      exact hs sm (ha ▸ hr') hb

end Events


/-- The default request with coins: the public key of user `0` at arbitrary coins. -/
noncomputable instance [NeZero n] : Inhabited (O.Coins × MURequest O n) :=
  ⟨(Classical.arbitrary _, .publicKey 0)⟩

section Guess

variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y]

omit [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y] [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Fintype O.SMsg] [DecidableEq O.SMsg]
  [Fintype O.Coins] [DecidableEq O.Coins] in
/-- **The requests of the relay attaching coins are the requests.** -/
theorem map_snd_relayList_coinRelay (Q : ℕ) (ρ : Fin Q → O.Coins) (rs : List (MURequest O n)) :
    ((coinRelay O Q ρ).relayList rs).map Prod.snd = rs := by
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs r ih =>
    rw [SideRelay.relayList_append_singleton, List.map_append, ih]
    rfl

variable [NeZero n] in
/-- **The guess at a fixed user, keys and oracle**: the
probability that user `i` qualifies in the multi-user game is at most the average over the signing
coins `ρ` of the probability that the adversary absorbed through `coinRelay Q ρ` and relayed by
`guessRelay i keys` forges in the single-user game at user `i`'s key coins. -/
theorem qual_le_guess (i : Fin n) (keys : Fin n → B.KeyCoins) (Q : ℕ) {t : ℕ}
    (𝒜 : QueryBoundedAdversary X Y (MURequest O n) (MUResponse B) (B.PK × B.BMsg × B.BSig) t)
    (H : X → Y) :
    (𝒜.transcriptLaw (muChallenger O n keys Q) H).toOuterMeasure
        {x | ∃ p ∈ x, Qual keys H i p.1 (p.2.map HistoryEntry.request)} ≤
      ∑' ρ, PMF.uniformOfFintype (Fin Q → O.Coins) ρ *
        (((𝒜.absorbQB (coinRelay O Q ρ) (coinRelay_route_injective O Q ρ)).relay
            (guessRelay O i keys) Q).transcriptLaw (muChallenger O 1 (fun _ => keys i) Q)
          H).toOuterMeasure {x | ∃ p ∈ x, Forges (fun _ => keys i) H p.1 p.2} := by
  rw [toOuterMeasure_transcriptLaw_muChallenger (keys := keys) (Q := Q) (tgt := aboutUser i)]
  refine ENNReal.tsum_le_tsum fun ρ => mul_le_mul_right ?_ _
  refine (𝒜.transcriptLaw_le_absorbQB (coinRelay O Q ρ) (coinRelay_route_injective O Q ρ)
    (muChallengerAt O n keys Q (aboutUser i) ρ) (guessChallenger O i keys Q) (Equiv.refl _)
    (fun _ => rfl) (fun c' => relaysChallenger_coinRelay O i keys Q ρ c') H
    (fun o rs => Qual keys H i o rs) (fun o rs => Qual keys H i o (rs.map Prod.snd))
    fun o rs h => ?_).trans ?_
  · rw [List.map_take, map_snd_relayList_coinRelay]
    exact h
  · exact (𝒜.absorbQB (coinRelay O Q ρ) (coinRelay_route_injective O Q ρ)).transcriptLaw_le_relay
      (guessRelay O i keys) (guessChallenger O i keys Q) (muChallenger O 1 (fun _ => keys i) Q) id
      (relaysChallenger_guessRelay O i keys Q) H
      (fun p => Qual keys H i p.1 ((p.2.map HistoryEntry.request).map Prod.snd))
      (fun p => Forges (fun _ => keys i) H p.1 p.2)
      fun o hist hist' hq hrel => hq.forges_su fun e' he' => by
        rcases hrel e' he' with h1 | ⟨e, he, hc⟩
        · exact Or.inl h1
        · obtain ⟨ha, hr⟩ := (guessRelay O i keys).canAsk_of_asksIn
            (asksIn_guessProg i keys e.request).plainProg hc
          exact Or.inr ⟨e.request.2, List.mem_map.2 ⟨e.request, List.mem_map_of_mem he, rfl⟩,
            ha, hr⟩

end Guess


/-! ### The adversary -/

/-- **The public keys with user `i`'s replaced by `pk`**, the others those of the key coins. -/
def guessKeys (i : Fin n) (keys : Fin n → B.KeyCoins) (pk : B.PK) : Fin n → B.PK :=
  fun j => if j = i then pk else B.pk (keys j)

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] in
/-- **The guessed public keys** at the key coins updated at user `i` are the public keys of the
updated key coins. -/
theorem guessKeys_update (i : Fin n) (keys : Fin n → B.KeyCoins) (k : B.KeyCoins) :
    guessKeys i keys (B.pk k) = fun j => B.pk (Function.update keys i k j) := by
  funext j
  by_cases h : j = i
  · subst h
    simp [guessKeys]
  · simp [guessKeys, h]

section Update

variable [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y]

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Fintype O.SMsg] [DecidableEq O.SMsg]
  [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins] in
/-- **The relay reads the key coins only off user `i`.** -/
theorem guessRelay_update (i : Fin n) (keys : Fin n → B.KeyCoins) (k : B.KeyCoins) :
    guessRelay O i (Function.update keys i k) = guessRelay O i keys := by
  have h : guessProg O i (Function.update keys i k) = guessProg O i keys := by
    funext r
    obtain ⟨c, r⟩ := r
    simp only [guessProg]
    split_ifs with ha
    · rfl
    · congr 1
      rcases r with j | ⟨j, sm⟩ | j <;> simp only [aboutUser, decide_eq_true_eq] at ha <;>
        simp [localProg, Function.update_of_ne ha]
  simp only [guessRelay, h]

end Update



variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] {V : OracleView X Y} {t : ℕ}

variable [NeZero n]

variable [Nonempty TB.KeyCoins]

/-- **The single-user adversary guessing the target user** (module docstring): it draws a user `i`,
the key coins `keys` of all users and the signing coins `ρ` uniformly, and runs the adversary on the
public keys `guessKeys i keys pk` (its own key `pk` at user `i`) absorbed through `coinRelay Q ρ`
and relayed by `guessRelay i keys` to its challenger, answering `Q` requests. The relay makes the
signer's queries for the other users: at most `t + Q · O.q` queries. -/
noncomputable def suGuess (A : MUAdversary O n V t) (Q : ℕ) : SUAdversary O V (t + Q * O.q) :=
  fun inp =>
  QueryBoundedAdversary.mix
    (PMF.uniformOfFintype (Fin n × (Fin n → B.KeyCoins) × (Fin Q → O.Coins))) fun z =>
      (((A (guessKeys z.1 z.2.1 (inp.1 0), inp.2)).absorbQB (coinRelay O Q z.2.2)
        (coinRelay_route_injective O Q z.2.2)).relay (guessRelay O z.1 z.2.1) Q).mono
        (by simp [guessRelay])

/-! ### The bound -/

omit [Nonempty TB.KeyCoins] in
/-- **The relayed adversary at one draw** of the target user `i`, the key coins `keys` and the
signing coins `ρ`, with the single-user key `pk`, at the oracle `H`. -/
noncomputable abbrev guessAdv (A : MUAdversary O n V t) (Q : ℕ) (i : Fin n)
    (keys : Fin n → B.KeyCoins) (ρ : Fin Q → O.Coins) (pk : B.PK) (H : X → Y) :=
  ((A (guessKeys i keys pk, V.view H)).absorbQB (coinRelay O Q ρ)
    (coinRelay_route_injective O Q ρ)).relay (guessRelay O i keys) Q

omit [Nonempty TB.KeyCoins] in
/-- **The single-user forgery probability at one draw**, with the single-user key coins `k`. -/
noncomputable def guessWin (A : MUAdversary O n V t) (Q : ℕ) (i : Fin n)
    (keys : Fin n → B.KeyCoins) (ρ : Fin Q → O.Coins) (k : B.KeyCoins) (H : X → Y) : ℝ≥0∞ :=
  ((guessAdv O A Q i keys ρ (B.pk k) H).transcriptLaw (muChallenger O 1 (fun _ => k) Q)
    H).toOuterMeasure {x | ∃ p ∈ x, Forges (fun _ => k) H p.1 p.2}

omit [Nonempty TB.KeyCoins] in
/-- **The draw reads the key coins only off the target user.** -/
theorem guessWin_update (A : MUAdversary O n V t) (Q : ℕ) (i : Fin n) (keys : Fin n → B.KeyCoins)
    (x : B.KeyCoins) (ρ : Fin Q → O.Coins) (k : B.KeyCoins) (H : X → Y) :
    guessWin O A Q i (Function.update keys i x) ρ k H = guessWin O A Q i keys ρ k H := by
  have hk : guessKeys i (Function.update keys i x) (B.pk k) = guessKeys i keys (B.pk k) := by
    funext j
    by_cases h : j = i
    · simp [guessKeys, h]
    · simp [guessKeys, h, Function.update_of_ne h]
  simp only [guessWin, guessAdv, hk]
  rw [guessRelay_update]

/-- **The multi-user forgery probability is at most the sum over the users of their guessed
forgery probabilities**: `qual_le_guess` at every key coins
and oracle, after the union over the qualifying user. -/
theorem muEufProb_le_sum_guessWin (A : MUAdversary O n V t) (Q : ℕ) :
    muEufProb A Q ≤ ∑ keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑ H, PMF.uniformOfFintype (X → Y) H * ∑ i, ∑ ρ, PMF.uniformOfFintype (Fin Q → O.Coins) ρ *
        guessWin O A Q i keys ρ (keys i) H := by
  classical
  unfold muEufProb muLaw runLaw
  simp only [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply,
    tsum_fintype (L := .unconditional _)]
  refine Finset.sum_le_sum fun keys _ => mul_le_mul_right (Finset.sum_le_sum fun H _ =>
    mul_le_mul_right ?_ _) _
  have hsub : (fun o => (keys, H, o)) ⁻¹'
      {x : (Fin n → B.KeyCoins) × (X → Y) × Option ((B.PK × B.BMsg × B.BSig) × MUHist O n) |
        ∃ p ∈ x.2.2, Forges x.1 x.2.1 p.1 p.2} ⊆
      ⋃ i, {x | ∃ p ∈ x, Qual keys H i p.1 (p.2.map HistoryEntry.request)} := by
    rintro x ⟨p, hp, hf⟩
    obtain ⟨i, hi⟩ := hf.exists_qual
    exact Set.mem_iUnion.2 ⟨i, p, hp, hi⟩
  refine (MeasureTheory.measure_mono hsub).trans
    ((MeasureTheory.measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun i _ => ?_))
  have hA : A (fun j => B.pk (keys j), V.view H) =
      A (guessKeys i keys (B.pk (keys i)), V.view H) := by
    rw [guessKeys_update i keys (keys i), Function.update_eq_self]
  rw [← tsum_fintype (L := .unconditional _)]
  refine (qual_le_guess O i keys Q _ H).trans_eq ?_
  simp only [guessWin, guessAdv, hA]

/-- **The single-user adversary's success**: the average over its key coins, the oracle and the
draw of the guessed forgery probabilities. -/
theorem suEufProb_suGuess (A : MUAdversary O n V t) (Q : ℕ) :
    suEufProb (suGuess O A Q) Q = ∑ k, PMF.uniformOfFintype B.KeyCoins k *
      ∑ H, PMF.uniformOfFintype (X → Y) H *
        ∑ z, PMF.uniformOfFintype (Fin n × (Fin n → B.KeyCoins) × (Fin Q → O.Coins)) z *
          guessWin O A Q z.1 z.2.1 z.2.2 k H := by
  classical
  unfold suEufProb muEufProb muLaw runLaw
  simp only [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply,
    tsum_fintype (L := .unconditional _)]
  let e : B.KeyCoins ≃ (Fin 1 → B.KeyCoins) :=
    { toFun := fun k _ => k
      invFun := fun f => f 0
      left_inv := fun _ => rfl
      right_inv := fun f => funext fun j => by rw [Fin.fin_one_eq_zero j] }
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hU : PMF.uniformOfFintype (Fin 1 → B.KeyCoins) (e k) =
      PMF.uniformOfFintype B.KeyCoins k := by
    simp [PMF.uniformOfFintype_apply, Fintype.card_fun]
  rw [hU]
  refine congrArg _ (Finset.sum_congr rfl fun H _ => congrArg _ ?_)
  simp only [suGuess, QueryBoundedAdversary.transcriptLaw_mix, PMF.toOuterMeasure_bind_apply,
    tsum_fintype (L := .unconditional _), QueryBoundedAdversary.transcriptLaw_mono]
  rfl

variable [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins]

omit [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **The key coins re-split at the target user**: the average over the key coins of the draw at
the target user's own key coins is the average over the key coins and independent single-user key
coins. -/
theorem sum_guessWin_resplit (A : MUAdversary O n V t) (Q : ℕ) (i : Fin n) (ρ : Fin Q → O.Coins)
    (H : X → Y) :
    ∑ keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys * guessWin O A Q i keys ρ (keys i) H =
      ∑ keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
        ∑ k, PMF.uniformOfFintype B.KeyCoins k * guessWin O A Q i keys ρ k H := by
  rw [Interaction.sum_uniform_update i (fun keys => guessWin O A Q i keys ρ (keys i) H)]
  simp only [Function.update_self, guessWin_update]

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BMsg]
  [DecidableEq TB.BMsg] [Fintype TB.BSig] [DecidableEq TB.BSig] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [DecidableEq TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] [Fintype O.SMsg] [DecidableEq O.SMsg] [DecidableEq O.Coins] in
/-- **The uniform law on the draws** is the product of the uniform laws. -/
theorem uniform_draw_apply (Q : ℕ) (z : Fin n × (Fin n → B.KeyCoins) × (Fin Q → O.Coins)) :
    PMF.uniformOfFintype (Fin n × (Fin n → B.KeyCoins) × (Fin Q → O.Coins)) z =
      (n : ℝ≥0∞)⁻¹ * (PMF.uniformOfFintype (Fin n → B.KeyCoins) z.2.1 *
        PMF.uniformOfFintype (Fin Q → O.Coins) z.2.2) := by
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  rw [ENNReal.mul_inv (Or.inl (by simp [NeZero.ne n])) (by simp),
    ENNReal.mul_inv (by simp) (by simp)]

/-! ### The main requests of the guess relay -/

section MainReqs

variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y]

/-- **The main request of a request with its coins**: the same request about user `0` for a request
about user `i`, the idle request (the public key of user `0`) otherwise. -/
def guessMain (i : Fin n) (r : O.Coins × MURequest O n) : MURequest O 1 :=
  if aboutUser i r.2 then suReq r.2 else .publicKey 0

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BMsg]
  [DecidableEq TB.BMsg] [Fintype TB.BSig] [DecidableEq TB.BSig] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins]
  [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] [Nonempty O.Coins] [Fintype O.SMsg]
  [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] in
/-- **The relay of one request makes its one main request.** -/
theorem filterMap_runEntries_guessRelay (i : Fin n) (keys : Fin n → B.KeyCoins)
    (ans : List (MURequest O 1) → MURequest O 1 → Option (MUResponse B)) (H : X → Y)
    (r : O.Coins × MURequest O n) (prev : List (MURequest O 1)) :
    ((guessRelay O i keys).runEntries ans H r prev).filterMap Prod.fst = [guessMain O i r] := by
  obtain ⟨c, r⟩ := r
  by_cases ha : aboutUser i r = true
  · have h := MultiRelay.RunsWith.query_inr (ansM := ans) (H := H) (rs := prev)
      (k := fun b => OracleProg.pure (b.elim (fun _ => none) id)) (suReq r)
      (MultiRelay.RunsWith.pure _ _)
    rw [(guessRelay O i keys).filterMap_runEntries_of_runsWith ans H rfl
      (by simp only [guessRelay, guessProg, if_pos ha]; exact h) (by simp [guessRelay])
      (Nat.zero_le _)]
    simp [guessRelay, guessMain, ha]
  · have h := MultiRelay.RunsWith.liftQ (ansM := ans) (H := H) (Resp' := MUResponse B) prev
      (localProg O keys c r)
    rw [(guessRelay O i keys).filterMap_runEntries_of_runsWith ans H rfl
      (by simp only [guessRelay, guessProg, if_neg ha]; exact h) (by simp [guessRelay])
      (localProg_queries O keys c H r)]
    simp [guessRelay, guessMain, ha]

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BMsg]
  [DecidableEq TB.BMsg] [Fintype TB.BSig] [DecidableEq TB.BSig] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins]
  [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] [Nonempty O.Coins] in
/-- **The main requests of the guess relay**, position by position: the first `Q` requests' main
requests `guessMain`, the idle request for each later one. -/
theorem mainReqs_guessRelay (i : Fin n) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (ans : List (MURequest O 1) → MURequest O 1 → Option (MUResponse B)) (H : X → Y)
    (rs : List (O.Coins × MURequest O n)) :
    (guessRelay O i keys).mainReqs Q ans H rs =
      (rs.take Q).map (guessMain O i) ++ List.replicate (rs.length - Q) (.publicKey 0) := by
  induction rs using List.reverseRecOn with
  | nil => simp [MultiRelay.mainReqs]
  | append_singleton rs r ih =>
    rw [MultiRelay.mainReqs_append, ih]
    split_ifs with h
    · rw [filterMap_runEntries_guessRelay, List.take_of_length_le (by omega : rs.length ≤ Q),
        List.take_of_length_le (by simp; omega : (rs ++ [r]).length ≤ Q)]
      have h1 : rs.length - Q = 0 := by omega
      have h2 : (rs ++ [r]).length - Q = 0 := by simp; omega
      rw [h1, h2]
      simp
    · have h1 : (rs ++ [r]).take Q = rs.take Q := by
        rw [List.take_append_of_le_length (by omega)]
      have h2 : (rs ++ [r]).length - Q = (rs.length - Q) + 1 := by simp; omega
      rw [h1, h2, List.replicate_succ', List.append_assoc]
      rfl

end MainReqs

/-! ### The bound with few signing and corruption requests -/

section Within

variable {O}

/-- **User `i` qualifies with at most `Qs` signing and corruption requests.** -/
def QualW (keys : Fin n → B.KeyCoins) (H : X → Y) (i : Fin n) (Qs : ℕ)
    (f : B.PK × B.BMsg × B.BSig) (rs : List (MURequest O n)) : Prop :=
  Qual keys H i f rs ∧ rs.countP MURequest.isSignOrCorrupt ≤ Qs

omit [NeZero n] [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BMsg]
  [DecidableEq TB.BMsg] [Fintype TB.BSig] [DecidableEq TB.BSig] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins]
  [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] [Fintype O.SMsg]
  [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins] in
/-- **The main request of a request is a signing or corruption request only if the request is.** -/
theorem countP_map_guessMain_le (i : Fin n) (rs : List (O.Coins × MURequest O n)) :
    (rs.map (guessMain O i)).countP MURequest.isSignOrCorrupt ≤
      (rs.map Prod.snd).countP MURequest.isSignOrCorrupt := by
  rw [List.countP_map, List.countP_map]
  refine List.countP_mono_left fun x _ hx => ?_
  obtain ⟨c, r⟩ := x
  simp only [Function.comp_apply, guessMain] at hx ⊢
  split_ifs at hx with ha
  · rcases r with j | ⟨j, sm⟩ | j <;> simp_all [suReq, MURequest.isSignOrCorrupt]
  · simp [MURequest.isSignOrCorrupt] at hx

variable (O)

omit [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] in
/-- **The guess at a fixed user, keys and oracle, with few signing and corruption requests**: as
`qual_le_guess`, the single-user history with at most as many signing and corruption requests as
the multi-user one (`mainReqs_guessRelay`). -/
theorem qualW_le_guess (i : Fin n)
    (keys : Fin n → B.KeyCoins) (Q Qs : ℕ) {t : ℕ}
    (𝒜 : QueryBoundedAdversary X Y (MURequest O n) (MUResponse B) (B.PK × B.BMsg × B.BSig) t)
    (H : X → Y) :
    (𝒜.transcriptLaw (muChallenger O n keys Q) H).toOuterMeasure
        {x | ∃ p ∈ x, QualW keys H i Qs p.1 (p.2.map HistoryEntry.request)} ≤
      ∑' ρ, PMF.uniformOfFintype (Fin Q → O.Coins) ρ *
        (((𝒜.absorbQB (coinRelay O Q ρ) (coinRelay_route_injective O Q ρ)).relay
            (guessRelay O i keys) Q).transcriptLaw (muChallenger O 1 (fun _ => keys i) Q)
          H).toOuterMeasure
          {x | ∃ p ∈ x, Forges (fun _ => keys i) H p.1 p.2 ∧ signCorruptCount p.2 ≤ Qs} := by
  rw [toOuterMeasure_transcriptLaw_muChallenger (keys := keys) (Q := Q) (tgt := aboutUser i)]
  refine ENNReal.tsum_le_tsum fun ρ => mul_le_mul_right ?_ _
  refine (𝒜.transcriptLaw_le_absorbQB (coinRelay O Q ρ) (coinRelay_route_injective O Q ρ)
    (muChallengerAt O n keys Q (aboutUser i) ρ) (guessChallenger O i keys Q) (Equiv.refl _)
    (fun _ => rfl) (fun c' => relaysChallenger_coinRelay O i keys Q ρ c') H
    (fun o rs => QualW keys H i Qs o rs) (fun o rs => QualW keys H i Qs o (rs.map Prod.snd))
    fun o rs h => ?_).trans ?_
  · rw [List.map_take, map_snd_relayList_coinRelay]
    exact h
  · refine (𝒜.absorbQB (coinRelay O Q ρ)
      (coinRelay_route_injective O Q ρ)).transcriptLaw_le_relay_pos
      (guessRelay O i keys) (guessChallenger O i keys Q) (muChallenger O 1 (fun _ => keys i) Q) id
      (relaysChallenger_guessRelay O i keys Q) H
      (fun p => QualW keys H i Qs p.1 ((p.2.map HistoryEntry.request).map Prod.snd))
      (fun p => Forges (fun _ => keys i) H p.1 p.2 ∧ signCorruptCount p.2 ≤ Qs)
      fun c' o rs k _ hq => ?_
    rw [map_request_histAlong] at hq
    obtain ⟨hq, hc⟩ := hq
    rw [mainReqs_guessRelay] at *
    set l := ((List.take Q rs).map (guessMain O i) ++
      List.replicate (rs.length - Q) (MURequest.publicKey 0 : MURequest O 1) ++
      List.replicate k (MURequest.publicKey 0 : MURequest O 1)).take Q with hl
    have hmem : ∀ r' ∈ l, r' = .publicKey 0 ∨
        ∃ r ∈ rs.map Prod.snd, aboutUser i r = true ∧ r' = suReq r := by
      intro r' hr'
      have hr'' := List.mem_of_mem_take hr'
      simp only [List.mem_append, List.mem_replicate, List.mem_map] at hr''
      rcases hr'' with (⟨x, hx, rfl⟩ | ⟨-, rfl⟩) | ⟨-, rfl⟩
      · simp only [guessMain]
        split_ifs with ha
        · exact Or.inr ⟨x.2, List.mem_map.2 ⟨x, List.mem_of_mem_take hx, rfl⟩, ha, rfl⟩
        · exact Or.inl rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
    refine ⟨hq.forges_su fun e' he' => ?_, ?_⟩
    · have : e'.request ∈ l := by
        rw [← map_request_histAlong
          (ans := (muChallenger O 1 (fun _ => keys i) Q).toPureEnv.answerAfter
          (H, c')) l]
        exact List.mem_map_of_mem he'
      exact hmem _ this
    · rw [signCorruptCount_eq, map_request_histAlong]
      refine le_trans ?_ hc
      calc l.countP MURequest.isSignOrCorrupt
          ≤ ((List.take Q rs).map (guessMain O i) ++
              List.replicate (rs.length - Q) (MURequest.publicKey 0 : MURequest O 1) ++
              List.replicate k (MURequest.publicKey 0 : MURequest O 1)).countP
                MURequest.isSignOrCorrupt :=
            (List.take_sublist _ _).countP_le
        _ = ((List.take Q rs).map (guessMain O i)).countP MURequest.isSignOrCorrupt := by
            simp [List.countP_append, List.countP_replicate, MURequest.isSignOrCorrupt]
        _ ≤ ((List.take Q rs).map Prod.snd).countP MURequest.isSignOrCorrupt :=
            countP_map_guessMain_le i _
        _ ≤ (rs.map Prod.snd).countP MURequest.isSignOrCorrupt :=
            ((List.take_sublist Q rs).map Prod.snd).countP_le

omit [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] in
/-- **The single-user forgery probability at one draw, with at most `Qs` signing and corruption
requests**, with the single-user key coins `k`. -/
noncomputable def guessWinW (A : MUAdversary O n V t) (Q Qs : ℕ) (i : Fin n)
    (keys : Fin n → B.KeyCoins) (ρ : Fin Q → O.Coins) (k : B.KeyCoins) (H : X → Y) : ℝ≥0∞ :=
  ((guessAdv O A Q i keys ρ (B.pk k) H).transcriptLaw (muChallenger O 1 (fun _ => k) Q)
    H).toOuterMeasure {x | ∃ p ∈ x, Forges (fun _ => k) H p.1 p.2 ∧ signCorruptCount p.2 ≤ Qs}

omit [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] in
/-- **The draw reads the key coins only off the target user.** -/
theorem guessWinW_update (A : MUAdversary O n V t) (Q Qs : ℕ) (i : Fin n)
    (keys : Fin n → B.KeyCoins)
    (x : B.KeyCoins) (ρ : Fin Q → O.Coins) (k : B.KeyCoins) (H : X → Y) :
    guessWinW O A Q Qs i (Function.update keys i x) ρ k H = guessWinW O A Q Qs i keys ρ k H := by
  have hk : guessKeys i (Function.update keys i x) (B.pk k) = guessKeys i keys (B.pk k) := by
    funext j
    by_cases h : j = i
    · simp [guessKeys, h]
    · simp [guessKeys, h, Function.update_of_ne h]
  simp only [guessWinW, guessAdv, hk]
  rw [guessRelay_update]

omit [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **The multi-user forgery probability with at most `Qs` signing and corruption requests is at
most the sum over the users of their guessed ones**: `qualW_le_guess` at every key coins
and oracle, after the union over the qualifying user. -/
theorem muEufProbWithin_le_sum_guessWinW (A : MUAdversary O n V t) (Q Qs : ℕ) :
    muEufProbWithin A Q Qs ≤ ∑ keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑ H, PMF.uniformOfFintype (X → Y) H * ∑ i, ∑ ρ, PMF.uniformOfFintype (Fin Q → O.Coins) ρ *
        guessWinW O A Q Qs i keys ρ (keys i) H := by
  classical
  unfold muEufProbWithin muLaw runLaw
  simp only [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply,
    tsum_fintype (L := .unconditional _)]
  refine Finset.sum_le_sum fun keys _ => mul_le_mul_right (Finset.sum_le_sum fun H _ =>
    mul_le_mul_right ?_ _) _
  have hsub : (fun o => (keys, H, o)) ⁻¹'
      {x : (Fin n → B.KeyCoins) × (X → Y) × Option ((B.PK × B.BMsg × B.BSig) × MUHist O n) |
        ∃ p ∈ x.2.2, Forges x.1 x.2.1 p.1 p.2 ∧ signCorruptCount p.2 ≤ Qs} ⊆
      ⋃ i, {x | ∃ p ∈ x, QualW keys H i Qs p.1 (p.2.map HistoryEntry.request)} := by
    rintro x ⟨p, hp, hf, hc⟩
    obtain ⟨i, hi⟩ := hf.exists_qual
    exact Set.mem_iUnion.2 ⟨i, p, hp, hi, (signCorruptCount_eq p.2) ▸ hc⟩
  refine (MeasureTheory.measure_mono hsub).trans
    ((MeasureTheory.measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun i _ => ?_))
  have hA : A (fun j => B.pk (keys j), V.view H) =
      A (guessKeys i keys (B.pk (keys i)), V.view H) := by
    rw [guessKeys_update i keys (keys i), Function.update_eq_self]
  rw [← tsum_fintype (L := .unconditional _)]
  refine (qualW_le_guess O i keys Q Qs _ H).trans_eq ?_
  simp only [guessWinW, guessAdv, hA]

omit [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **The single-user adversary's success with at most `Qs` signing and corruption requests**: the
average over its key coins, the oracle and the draw of the guessed forgery probabilities. -/
theorem muEufProbWithin_suGuess (A : MUAdversary O n V t) (Q Qs : ℕ) :
    muEufProbWithin (suGuess O A Q) Q Qs = ∑ k, PMF.uniformOfFintype B.KeyCoins k *
      ∑ H, PMF.uniformOfFintype (X → Y) H *
        ∑ z, PMF.uniformOfFintype (Fin n × (Fin n → B.KeyCoins) × (Fin Q → O.Coins)) z *
          guessWinW O A Q Qs z.1 z.2.1 z.2.2 k H := by
  classical
  unfold muEufProbWithin muLaw runLaw
  simp only [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply,
    tsum_fintype (L := .unconditional _)]
  let e : B.KeyCoins ≃ (Fin 1 → B.KeyCoins) :=
    { toFun := fun k _ => k
      invFun := fun f => f 0
      left_inv := fun _ => rfl
      right_inv := fun f => funext fun j => by rw [Fin.fin_one_eq_zero j] }
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hU : PMF.uniformOfFintype (Fin 1 → B.KeyCoins) (e k) =
      PMF.uniformOfFintype B.KeyCoins k := by
    simp [PMF.uniformOfFintype_apply, Fintype.card_fun]
  rw [hU]
  refine congrArg _ (Finset.sum_congr rfl fun H _ => congrArg _ ?_)
  simp only [suGuess, QueryBoundedAdversary.transcriptLaw_mix, PMF.toOuterMeasure_bind_apply,
    tsum_fintype (L := .unconditional _), QueryBoundedAdversary.transcriptLaw_mono]
  rfl

omit [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **The key coins re-split at the target user**: the average over the key coins of the draw at
the target user's own key coins is the average over the key coins and independent single-user key
coins. -/
theorem sum_guessWinW_resplit (A : MUAdversary O n V t) (Q Qs : ℕ) (i : Fin n) (ρ : Fin Q → O.Coins)
    (H : X → Y) :
    ∑ keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
        guessWinW O A Q Qs i keys ρ (keys i) H =
      ∑ keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
        ∑ k, PMF.uniformOfFintype B.KeyCoins k * guessWinW O A Q Qs i keys ρ k H := by
  rw [Interaction.sum_uniform_update i (fun keys => guessWinW O A Q Qs i keys ρ (keys i) H)]
  simp only [Function.update_self, guessWinW_update]


end Within

/-! ### The strong forgery events -/

section Strong

variable {O}

/-- **User `i` qualifies for a strong forgery** at the history `hist`: the signature verifies, the
key is user `i`'s, user `i` was not corrupted and was not returned the signature for the base
message. -/
def QualS (keys : Fin n → B.KeyCoins) (H : X → Y) (i : Fin n) (f : B.PK × B.BMsg × B.BSig)
    (hist : MUHist O n) : Prop :=
  B.bverify H f.1 f.2.1 f.2.2 = true ∧ B.pk (keys i) = f.1 ∧ ¬ Corrupted hist i ∧
    ¬ Returned hist i f.2.1 f.2.2

omit [NeZero n] [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BMsg]
  [DecidableEq TB.BMsg] [Fintype TB.BSig] [DecidableEq TB.BSig] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins]
  [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] [Fintype O.SMsg]
  [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins] in
/-- **A strong forgery is one for which some user qualifies.** -/
theorem StrongForges.exists_qualS {keys : Fin n → B.KeyCoins} {H : X → Y}
    {f : B.PK × B.BMsg × B.BSig} {hist : MUHist O n} (h : StrongForges keys H f hist) :
    ∃ i, QualS keys H i f hist := by
  obtain ⟨i, hi, hc, hs⟩ := h.exists_user
  exact ⟨i, h.verify_eq, hi, hc, hs⟩

/-- **The requests of a history with their coins read as a multi-user history.** -/
def dropCoins (hist : List (HistoryEntry (O.Coins × MURequest O n) (MUResponse B))) : MUHist O n :=
  hist.map fun e => ⟨e.request.2, e.response⟩

variable (O)

omit [NeZero n] [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BMsg]
  [DecidableEq TB.BMsg] [Fintype TB.BSig] [DecidableEq TB.BSig] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins]
  [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] [Fintype O.SMsg]
  [DecidableEq O.SMsg] in
/-- **The reply of the multi-user challenger signing user `i`'s requests with its coins and the
others with `ρ`**, to a request numbered below `Q`. -/
theorem answerAfter_muChallengerAt (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (tgt : MURequest O n → Bool) (ρ : Fin Q → O.Coins) (H : X → Y) (a : Fin Q → O.Coins)
    (rs : List (MURequest O n)) (r : MURequest O n) (hi : rs.length < Q) :
    (muChallengerAt O n keys Q tgt ρ).toPureEnv.answerAfter (H, a) rs r =
      muReply O keys H (if tgt r then a ⟨rs.length, hi⟩ else ρ ⟨rs.length, hi⟩) r := by
  have hn := muChallengerAt_noAssign (keys := keys) (Q := Q) (tgt := tgt) (ρ := ρ)
  obtain ⟨-, -, h3⟩ := hn.oracleIn H a rs
  rw [hn.answerAfter_eq H a rs r hi]
  have hl : ((muChallengerAt O n keys Q tgt ρ).toPureEnv.oracleIn (H, a) rs).hist.length =
      rs.length := by
    rw [h3]
    exact min_eq_left (le_of_lt hi)
  generalize ((muChallengerAt O n keys Q tgt ρ).toPureEnv.oracleIn (H, a) rs).hist = hist at hl ⊢
  have hi' : hist.length < Q := hl ▸ hi
  have hf : (⟨hist.length, hi'⟩ : Fin Q) = ⟨rs.length, hi⟩ := Fin.ext hl
  simp only [muChallengerAt]
  rw [dif_pos hi']
  rcases r with j | ⟨j, sm⟩ | j
  · rfl
  · simp only [OracleProg.run_bind, muReply, hf]
    rfl
  · rfl

omit [NeZero n] [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] in
/-- **The coin relay keeps the history**: the history of the requests with their coins against the
challenger of requests with their coins, read without the coins, is the multi-user history against
the challenger signing user `i`'s requests with its coins and the others with `ρ`, at the same
coins. -/
theorem dropCoins_histAlong_coinRelay (i : Fin n) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (ρ : Fin Q → O.Coins) (H : X → Y) (a : Fin Q → O.Coins) (rs : List (MURequest O n))
    (hrs : rs.length ≤ Q) :
    dropCoins (histAlong ((guessChallenger O i keys Q).toPureEnv.answerAfter (H, a))
        ((coinRelay O Q ρ).relayList rs)) =
      histAlong ((muChallengerAt O n keys Q (aboutUser i) ρ).toPureEnv.answerAfter (H, a)) rs := by
  refine List.ext_getElem (by simp [dropCoins]) fun j h1 h2 => ?_
  have hj : j < rs.length := by simpa using h2
  have hjQ : j < Q := lt_of_lt_of_le hj hrs
  simp only [dropCoins, List.getElem_map, getElem_histAlong]
  have hrel : ((coinRelay O Q ρ).relayList rs)[j]'(by simpa using hj) = (ρ ⟨j, hjQ⟩, rs[j]) := by
    simp [SideRelay.relayList, coinRelay, hjQ]
  have htake : (((coinRelay O Q ρ).relayList rs).take j).length = j := by simp; omega
  rw [hrel, answerAfter_guessChallenger O i keys Q H a _ _ (by rw [htake]; exact hjQ),
    answerAfter_muChallengerAt O keys Q (aboutUser i) ρ H a _ _ (by simp; omega)]
  have htake' : (rs.take j).length = j := by simp; omega
  congr 2
  split_ifs
  · congr 1
    exact Fin.ext (htake.trans htake'.symm)
  · exact congrArg ρ (Fin.ext htake'.symm)


omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BMsg]
  [DecidableEq TB.BMsg] [Fintype TB.BSig] [DecidableEq TB.BSig] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins]
  [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] in
omit [NeZero n] [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]
  [Nonempty O.Coins] in
/-- **A main request of the guess relay other than the idle request** is the `suReq` of a request
about user `i` at the same position. -/
theorem guessList_getElem (i : Fin n) (Q k : ℕ) (rs : List (O.Coins × MURequest O n))
    (hrs : rs.length ≤ Q) (j : ℕ)
    (hj : j < (((rs.take Q).map (guessMain O i) ++ List.replicate (rs.length - Q)
      (MURequest.publicKey 0 : MURequest O 1) ++
        List.replicate k (MURequest.publicKey 0)).take Q).length)
    (hne : (((rs.take Q).map (guessMain O i) ++ List.replicate (rs.length - Q)
      (MURequest.publicKey 0 : MURequest O 1) ++
        List.replicate k (MURequest.publicKey 0)).take Q)[j]
        ≠ .publicKey 0) :
    ∃ hjr : j < rs.length, aboutUser i (rs[j]).2 = true ∧
      (((rs.take Q).map (guessMain O i) ++ List.replicate (rs.length - Q)
        (MURequest.publicKey 0 : MURequest O 1) ++
          List.replicate k (MURequest.publicKey 0)).take Q)[j]
          = suReq (rs[j]).2 := by
  have hq : rs.take Q = rs := List.take_of_length_le hrs
  have hz : rs.length - Q = 0 := by omega
  simp only [hq, hz, List.replicate_zero, List.append_nil, List.getElem_take] at hj hne ⊢
  by_cases hjr : j < rs.length
  · refine ⟨hjr, ?_⟩
    rw [List.getElem_append_left (by simpa using hjr), List.getElem_map] at hne ⊢
    simp only [guessMain] at hne ⊢
    split_ifs at hne ⊢ with ha
    · exact ⟨ha, rfl⟩
    · exact absurd rfl hne
  · rw [List.getElem_append_right (by simp; omega), List.getElem_replicate] at hne
    exact absurd rfl hne

omit [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] in variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y]
  [DecidableEq Y] [AddGroup Y] [Nonempty Y] [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig]
  [DecidableEq TB.BSig] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] in
/-- **A user qualifying for a strong forgery gives a strong forgery of the single-user game** at its
key coins, at the history of the guess relay's main requests (`mainReqs_guessRelay`, with an idle
tail) against the single-user challenger, at the coins `c'` of both challengers. -/
theorem QualS.strongForges_su {keys : Fin n → B.KeyCoins} {H : X → Y} {i : Fin n}
    {f : B.PK × B.BMsg × B.BSig} {Q k : ℕ} {rs : List (O.Coins × MURequest O n)}
    (hrs : rs.length ≤ Q) (c' : Fin Q → O.Coins)
    (hq : QualS keys H i f
      (dropCoins (histAlong ((guessChallenger O i keys Q).toPureEnv.answerAfter (H, c')) rs))) :
    StrongForges (fun _ => keys i) H f
      (histAlong ((muChallenger O 1 (fun _ => keys i) Q).toPureEnv.answerAfter (H, c'))
        (((guessRelay O i keys).mainReqs Q
          ((muChallenger O 1 (fun _ => keys i) Q).toPureEnv.answerAfter (H, c')) H rs ++
            List.replicate k (guessRelay O i keys).idle).take Q)) := by
  obtain ⟨hv, hk, hc, hs⟩ := hq
  rw [mainReqs_guessRelay, show (guessRelay O i keys).idle = (MURequest.publicKey 0 : MURequest O 1)
    from rfl]
  set l := ((rs.take Q).map (guessMain O i) ++ List.replicate (rs.length - Q)
    (MURequest.publicKey 0 : MURequest O 1) ++ List.replicate k (MURequest.publicKey 0)).take Q
    with hl
  have hlQ : l.length ≤ Q := by simp [hl]
  -- the entry `j` of the multi-user history
  have hmu : ∀ (j : ℕ) (hjr : j < rs.length),
      (dropCoins (histAlong ((guessChallenger O i keys Q).toPureEnv.answerAfter (H, c')) rs))[j]'(by
        simpa [dropCoins] using hjr) =
        ⟨(rs[j]).2, muReply O keys H (if aboutUser i (rs[j]).2 then c' ⟨j, by omega⟩ else (rs[j]).1)
          (rs[j]).2⟩ := by
    intro j hjr
    simp only [dropCoins, List.getElem_map, getElem_histAlong]
    rw [answerAfter_guessChallenger O i keys Q H c' _ _ (by simp; omega)]
    have ht : (rs.take j).length = j := by simp; omega
    congr 2
    split_ifs
    · exact congrArg c' (Fin.ext ht)
    · rfl
  refine ⟨hv, 0, hk, ?_, ?_⟩
  · rintro ⟨e, he, hr⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
    have hjl : j < l.length := by rw [length_histAlong] at hj; exact hj
    rw [getElem_histAlong] at hr
    have hr' : l[j] = .corrupt 0 := hr
    have hne : l[j] ≠ .publicKey 0 := fun h => by rw [h] at hr'; cases hr'
    obtain ⟨hjr, ha, hsu⟩ := guessList_getElem O i Q k rs hrs j hjl hne
    rw [hr'] at hsu
    apply hc
    refine ⟨_, List.getElem_mem (by simpa [dropCoins] using hjr), ?_⟩
    rw [hmu j hjr]
    rcases hreq : (rs[j]).2 with x | ⟨x, sm⟩ | x <;>
      simp only [hreq, aboutUser, decide_eq_true_eq, suReq, reduceCtorEq] at ha hsu
    simp [ha]
  · rintro ⟨e, he, sm, hr, hb, hresp⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he
    have hjl : j < l.length := by rw [length_histAlong] at hj; exact hj
    rw [getElem_histAlong] at hr hresp
    have hr' : l[j] = .sign 0 sm := hr
    have hne : l[j] ≠ .publicKey 0 := fun h => by rw [h] at hr'; cases hr'
    obtain ⟨hjr, ha, hsu⟩ := guessList_getElem O i Q k rs hrs j hjl hne
    change (muChallenger O 1 (fun _ => keys i) Q).toPureEnv.answerAfter (H, c') (l.take j) l[j] =
      some (.signature f.2.2) at hresp
    rw [hr'] at hsu hresp
    have hjQ : j < Q := by omega
    rw [answerAfter_muChallenger O _ Q H c' _ _ (by simp; omega)] at hresp
    apply hs
    refine ⟨_, List.getElem_mem (by simpa [dropCoins] using hjr), sm, ?_, hb, ?_⟩
    · rw [hmu j hjr]
      rcases hreq : (rs[j]).2 with x | ⟨x, sm'⟩ | x <;>
        simp only [hreq, aboutUser, decide_eq_true_eq, suReq, reduceCtorEq,
          MURequest.sign.injEq] at ha hsu
      obtain ⟨-, rfl⟩ := hsu
      simp [ha]
    · rw [hmu j hjr, if_pos ha]
      have hidx : (⟨(l.take j).length, by simp; omega⟩ : Fin Q) = ⟨j, hjQ⟩ :=
        Fin.ext (by simp; omega)
      rw [hidx] at hresp
      rw [← hresp, muReply_suReq O keys H _ ha, hsu]


omit [NeZero n] [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BMsg]
  [DecidableEq TB.BMsg] [Fintype TB.BSig] [DecidableEq TB.BSig] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins]
  [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] [Fintype O.SMsg]
  [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] in
/-- The relay of a prefix is the prefix of the relay. -/
theorem relayList_take_coinRelay (Q : ℕ) (ρ : Fin Q → O.Coins) (rs : List (MURequest O n))
    (m : ℕ) :
    (coinRelay O Q ρ).relayList (rs.take m) = ((coinRelay O Q ρ).relayList rs).take m := by
  refine List.ext_getElem (by simp) fun j h1 h2 => ?_
  simp [SideRelay.relayList]

omit [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] in
variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] in
/-- **The guess at a fixed user, keys and oracle, for strong forgeries**: as `qual_le_guess`, the
histories compared with their responses through the coin relay (`transcriptLaw_le_absorbQB_hist`,
`dropCoins_histAlong_coinRelay`) and position by position through the guess relay
(`transcriptLaw_le_relay_pos`, `QualS.strongForges_su`). -/
theorem qualS_le_guess (i : Fin n) (keys : Fin n → B.KeyCoins) (Q : ℕ) {t : ℕ}
    (𝒜 : QueryBoundedAdversary X Y (MURequest O n) (MUResponse B) (B.PK × B.BMsg × B.BSig) t)
    (H : X → Y) :
    (𝒜.transcriptLaw (muChallenger O n keys Q) H).toOuterMeasure
        {x | ∃ p ∈ x, QualS keys H i p.1 p.2} ≤
      ∑' ρ, PMF.uniformOfFintype (Fin Q → O.Coins) ρ *
        (((𝒜.absorbQB (coinRelay O Q ρ) (coinRelay_route_injective O Q ρ)).relay
            (guessRelay O i keys) Q).transcriptLaw (muChallenger O 1 (fun _ => keys i) Q)
          H).toOuterMeasure {x | ∃ p ∈ x, StrongForges (fun _ => keys i) H p.1 p.2} := by
  rw [toOuterMeasure_transcriptLaw_muChallenger (keys := keys) (Q := Q) (tgt := aboutUser i)]
  refine ENNReal.tsum_le_tsum fun ρ => mul_le_mul_right ?_ _
  refine (𝒜.transcriptLaw_le_absorbQB_hist (coinRelay O Q ρ) (coinRelay_route_injective O Q ρ)
    (muChallengerAt O n keys Q (aboutUser i) ρ) (guessChallenger O i keys Q) (Equiv.refl _)
    (fun _ => rfl) (fun c' => relaysChallenger_coinRelay O i keys Q ρ c') H
    (fun p => QualS keys H i p.1 p.2) (fun p => QualS keys H i p.1 (dropCoins p.2))
    fun c o rs h => ?_).trans ?_
  · change QualS keys H i o (dropCoins (histAlong
      ((guessChallenger O i keys Q).toPureEnv.answerAfter (H, c))
      (((coinRelay O Q ρ).relayList rs).take Q)))
    rw [← relayList_take_coinRelay, dropCoins_histAlong_coinRelay O i keys Q ρ H c _
      (by simp)]
    exact h
  · exact (𝒜.absorbQB (coinRelay O Q ρ)
      (coinRelay_route_injective O Q ρ)).transcriptLaw_le_relay_pos
      (guessRelay O i keys) (guessChallenger O i keys Q) (muChallenger O 1 (fun _ => keys i) Q) id
      (relaysChallenger_guessRelay O i keys Q) H
      (fun p => QualS keys H i p.1 (dropCoins p.2))
      (fun p => StrongForges (fun _ => keys i) H p.1 p.2)
      fun c' o rs k hlen hq => QualS.strongForges_su O hlen c' hq

omit [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] in
/-- **The single-user strong forgery probability at one draw**, with the single-user key coins `k`.
-/
noncomputable def guessWinS (A : MUAdversary O n V t) (Q : ℕ) (i : Fin n)
    (keys : Fin n → B.KeyCoins) (ρ : Fin Q → O.Coins) (k : B.KeyCoins) (H : X → Y) : ℝ≥0∞ :=
  ((guessAdv O A Q i keys ρ (B.pk k) H).transcriptLaw (muChallenger O 1 (fun _ => k) Q)
    H).toOuterMeasure {x | ∃ p ∈ x, StrongForges (fun _ => k) H p.1 p.2}

omit [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] in
/-- **The draw reads the key coins only off the target user.** -/
theorem guessWinS_update (A : MUAdversary O n V t) (Q : ℕ) (i : Fin n) (keys : Fin n → B.KeyCoins)
    (x : B.KeyCoins) (ρ : Fin Q → O.Coins) (k : B.KeyCoins) (H : X → Y) :
    guessWinS O A Q i (Function.update keys i x) ρ k H = guessWinS O A Q i keys ρ k H := by
  have hk : guessKeys i (Function.update keys i x) (B.pk k) = guessKeys i keys (B.pk k) := by
    funext j
    by_cases h : j = i
    · simp [guessKeys, h]
    · simp [guessKeys, h, Function.update_of_ne h]
  simp only [guessWinS, guessAdv, hk]
  rw [guessRelay_update]

omit [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **The multi-user strong forgery probability is at most the sum over the users of their guessed
strong forgery probabilities**: `qualS_le_guess` at every key coins
and oracle, after the union over the qualifying user. -/
theorem muSufProb_le_sum_guessWinS (A : MUAdversary O n V t) (Q : ℕ) :
    muSufProb A Q ≤ ∑ keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
      ∑ H, PMF.uniformOfFintype (X → Y) H * ∑ i, ∑ ρ, PMF.uniformOfFintype (Fin Q → O.Coins) ρ *
        guessWinS O A Q i keys ρ (keys i) H := by
  classical
  unfold muSufProb muLaw runLaw
  simp only [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply,
    tsum_fintype (L := .unconditional _)]
  refine Finset.sum_le_sum fun keys _ => mul_le_mul_right (Finset.sum_le_sum fun H _ =>
    mul_le_mul_right ?_ _) _
  have hsub : (fun o => (keys, H, o)) ⁻¹'
      {x : (Fin n → B.KeyCoins) × (X → Y) × Option ((B.PK × B.BMsg × B.BSig) × MUHist O n) |
        ∃ p ∈ x.2.2, StrongForges x.1 x.2.1 p.1 p.2} ⊆
      ⋃ i, {x | ∃ p ∈ x, QualS keys H i p.1 p.2} := by
    rintro x ⟨p, hp, hf⟩
    obtain ⟨i, hi⟩ := hf.exists_qualS
    exact Set.mem_iUnion.2 ⟨i, p, hp, hi⟩
  refine (MeasureTheory.measure_mono hsub).trans
    ((MeasureTheory.measure_iUnion_fintype_le _ _).trans (Finset.sum_le_sum fun i _ => ?_))
  have hA : A (fun j => B.pk (keys j), V.view H) =
      A (guessKeys i keys (B.pk (keys i)), V.view H) := by
    rw [guessKeys_update i keys (keys i), Function.update_eq_self]
  rw [← tsum_fintype (L := .unconditional _)]
  refine (qualS_le_guess O i keys Q _ H).trans_eq ?_
  simp only [guessWinS, guessAdv, hA]

omit [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **The single-user adversary's success in SUF-CMA**: the average over its key coins, the oracle
and the draw of the guessed forgery probabilities. -/
theorem suSufProb_suGuess (A : MUAdversary O n V t) (Q : ℕ) :
    suSufProb (suGuess O A Q) Q = ∑ k, PMF.uniformOfFintype B.KeyCoins k *
      ∑ H, PMF.uniformOfFintype (X → Y) H *
        ∑ z, PMF.uniformOfFintype (Fin n × (Fin n → B.KeyCoins) × (Fin Q → O.Coins)) z *
          guessWinS O A Q z.1 z.2.1 z.2.2 k H := by
  classical
  unfold suSufProb muSufProb muLaw runLaw
  simp only [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply,
    tsum_fintype (L := .unconditional _)]
  let e : B.KeyCoins ≃ (Fin 1 → B.KeyCoins) :=
    { toFun := fun k _ => k
      invFun := fun f => f 0
      left_inv := fun _ => rfl
      right_inv := fun f => funext fun j => by rw [Fin.fin_one_eq_zero j] }
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hU : PMF.uniformOfFintype (Fin 1 → B.KeyCoins) (e k) =
      PMF.uniformOfFintype B.KeyCoins k := by
    simp [PMF.uniformOfFintype_apply, Fintype.card_fun]
  rw [hU]
  refine congrArg _ (Finset.sum_congr rfl fun H _ => congrArg _ ?_)
  simp only [suGuess, QueryBoundedAdversary.transcriptLaw_mix, PMF.toOuterMeasure_bind_apply,
    tsum_fintype (L := .unconditional _), QueryBoundedAdversary.transcriptLaw_mono]
  rfl

omit [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **The key coins re-split at the target user**: the average over the key coins of the draw at
the target user's own key coins is the average over the key coins and independent single-user key
coins. -/
theorem sum_guessWinS_resplit (A : MUAdversary O n V t) (Q : ℕ) (i : Fin n) (ρ : Fin Q → O.Coins)
    (H : X → Y) :
    ∑ keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys * guessWinS O A Q i keys ρ (keys i) H =
      ∑ keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
        ∑ k, PMF.uniformOfFintype B.KeyCoins k * guessWinS O A Q i keys ρ k H := by
  rw [Interaction.sum_uniform_update i (fun keys => guessWinS O A Q i keys ρ (keys i) H)]
  simp only [Function.update_self, guessWinS_update]


end Strong

end GordieHowe.Signature
