-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Signature.RejectionRelay

@[expose] public section

/-!
# The lifting lemma for rejection signers with a public context

A signing oracle whose signer is a standard signer followed by a public rejection step: on a
request with payload `p` by the key pair `(pk, sk)`, the signer refuses unless the public admission
`adm pk p` holds, and otherwise runs a public check on the context `ctx pk p`, then up to `K`
attempts of the standard signer on the base message `bmsg p`, each kept by a public keep decision
on the context and the signature, with its own public coin (`CtxRejection`). The context is the
public data the rejection reads: for a ring-aware signer, the key ring, the signer's position and
the ring message (`GordieHowe/Model/Signature/RejectionRelay.lean`); for a single signer, its public
key and the message.

For an oracle `O` that signs this way (`CtxRejection.SignsOn`, along a classifier `π` of its
messages into payloads and base messages), every adversary of the multi-user game with `O` is
turned into an explicit adversary of the standard multi-user game with `K` times the requests, in
two steps.

1. **The keep coins become side coins** (`GordieHowe/Model/Quantum/Interactive/Absorb.lean`). The
   intermediate oracle `C.keepOracle K hK` takes the keep coins in the request: a payload request
   `(p, ks)` is answered by `rejectSign` with the keep coins `ks` and `K` standard coins of the
   oracle (refused when not admitted); a base message `bm` is answered by the standard signer with
   the standard coins of attempt `0`. At the side coins `s`, the challenger of `O` relays the
   challenger of `keepOracle` by `msgRelay (C.keepMsg K hK π s)` (`relaysChallenger_keep`, along
   the split `keepSplit e Q` of the signing coins).
2. **The index-blind relay** (`GordieHowe/Model/Quantum/Interactive/MultiRelay.lean`) from
   `keepOracle` to the standard game: `C.relay K n hK pks i₀` (the relay programs `C.prog`, with
   the users' public keys `pks`): a public-key request or a corruption is asked as it is; a payload
   request of user `i` for `(p, ks)` is refused unless `adm (pks i) p`, and otherwise relayed by
   `relaySign`: the public check of `ctx (pks i) p`, then the first of `K` standard signatures of
   user `i` on `bmsg p`, each asked of the standard challenger, that the public keep decision with
   the keep coin `ks j` keeps; a base message is asked as one standard request.
   `relaysChallenger_relay`: the challenger of `keepOracle` with `Q` requests is the relay of the
   standard challenger with `K · Q` requests, along the attempts' coins (`attemptCoins`).

The relayed adversary `C.liftAdversary K n hK i₀ Q f hf A` of an adversary `A` with `Q` requests
absorbs uniform side coins along the message maps `f s`, then relays; at most
`t + Q · (qCheck + K · qKeep)` queries. `C.relayAdversary` is the one along `C.keepMsg K hK π`.
With `0 < K`, under `C.SignsOn K hK O π e`:

- `CtxRejection.muEufProb_le_relay`: `muEufProb A Q ≤ muEufProb (C.relayAdversary …) (K · Q)`;
- `CtxRejection.muSufProb_le_muVerifyProb_relay`: `muSufProb A Q ≤ muVerifyProb A' (K · Q)` for the
  same `A'` (not a reduction to MU-SUF-CMA^corr: `muVerifyProb` counts the signatures passed on).
-/

namespace GordieHowe.Signature

open GordieHowe.Quantum GordieHowe.RingSignature
open scoped ENNReal

variable {X Y : Type}

section Ctx

variable {TB : SchemeTypes} (B : BaseScheme X Y TB) (P Ctx : Type)

/-- **A standard signer followed by a public rejection with a context**, for the base signer `B`,
payloads `P` and contexts `Ctx`: the standard signer `std` on base messages with its own coins; the
public admission `adm pk p` of a payload by a public key, the context `ctx pk p` and the base
message `bmsg p` of the payload; the public check `check` of the context and the public keep
decision `keep c σ u` on a signature with its own public coin `u` (`KeepCoins`), with their query
bounds.
Neither `check` nor `keep` takes a secret key. -/
structure CtxRejection where
  /-- The coins of one standard signature. -/
  StdCoins : Type
  /-- The coins of one keep decision. -/
  KeepCoins : Type
  /-- The bound on the standard signer's queries. -/
  qStd : ℕ
  /-- The standard signer. -/
  std : B.SK → B.BMsg → StdCoins → OracleProg X Y (Option B.BSig)
  /-- It makes at most `qStd` queries. -/
  std_queries : ∀ sk bm c, (std sk bm c).QueriesLE qStd
  /-- The bound on the check's queries. -/
  qCheck : ℕ
  /-- The public check of a context. -/
  check : Ctx → OracleProg X Y Bool
  /-- It makes at most `qCheck` queries. -/
  check_queries : ∀ c, (check c).QueriesLE qCheck
  /-- The bound on the keep decision's queries. -/
  qKeep : ℕ
  /-- The public keep decision on a context and a signature, with its coin. -/
  keep : Ctx → B.BSig → KeepCoins → OracleProg X Y Bool
  /-- It makes at most `qKeep` queries. -/
  keep_queries : ∀ c σ u, (keep c σ u).QueriesLE qKeep
  /-- The admission of a payload by a public key; a payload not admitted is refused. -/
  adm : B.PK → P → Prop
  /-- The admission is decidable. -/
  admDec : ∀ pk p, Decidable (adm pk p)
  /-- The context of a payload signed under a public key. -/
  ctx : B.PK → P → Ctx
  /-- The base message of a payload. -/
  bmsg : P → B.BMsg

namespace CtxRejection

variable {B P Ctx} (C : CtxRejection B P Ctx)

instance (pk : B.PK) (p : P) : Decidable (C.adm pk p) := C.admDec pk p

/-- **The standard signer as a signing oracle** on base messages. -/
@[reducible] def stdOracle : SignOracle B where
  SMsg := B.BMsg
  Coins := C.StdCoins
  q := C.qStd
  sign kp bm c := C.std kp.2 bm c
  sign_queries kp bm c := C.std_queries kp.2 bm c
  base bm := bm

/-- **The rejection step on given attempts**: the check of the context `c`, then the first of the
attempts `sgn` whose signature the keep decision with the keep coin `ks j` of attempt `j` keeps;
`none` if the check fails or no attempt is kept. -/
def rejectWith (c : Ctx) {K : ℕ} (ks : Fin K → C.KeepCoins)
    (sgn : Fin K → OracleProg X Y (Option B.BSig)) : OracleProg X Y (Option B.BSig) :=
  (C.check c).bind fun ok =>
    if ok then firstKept (List.ofFn fun j => (sgn j, fun σ => C.keep c σ (ks j)))
    else .pure none

/-- **The rejection signer** with `K` attempts at the context `c` on the base message `bm`: attempt
`j` the standard signature of `sk` on `bm` with the standard coins `(cs j).1`, kept with the keep
coin `(cs j).2`. -/
def rejectSign (K : ℕ) (sk : B.SK) (c : Ctx) (bm : B.BMsg) (cs : Fin K → C.StdCoins × C.KeepCoins) :
    OracleProg X Y (Option B.BSig) :=
  C.rejectWith c (fun j => (cs j).2) fun j => C.std sk bm (cs j).1

/-- The rejection signer makes at most `qCheck + K · (qStd + qKeep)` queries. -/
theorem rejectSign_queries (K : ℕ) (sk : B.SK) (c : Ctx) (bm : B.BMsg)
    (cs : Fin K → C.StdCoins × C.KeepCoins) :
    (C.rejectSign K sk c bm cs).QueriesLE (C.qCheck + K * (C.qStd + C.qKeep)) := by
  refine (C.check_queries c).bind fun ok => ?_
  split_ifs
  · have h := firstKept_queries (q₁ := C.qStd) (q₂ := C.qKeep)
      (List.ofFn fun j => (C.std sk bm (cs j).1, fun σ => C.keep c σ (cs j).2))
      (fun q hq => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hq
        exact ⟨C.std_queries _ _ _, fun σ => C.keep_queries _ _ _⟩)
    rwa [List.length_ofFn] at h
  · exact (OracleProg.QueriesLE.pure _ _).mono (Nat.zero_le _)

/-- **The kept outcome of one standard attempt** at the oracle `H` with the standard coins `c.1`
and the keep coin `c.2`. -/
def att (H : X → Y) (sk : B.SK) (c : Ctx) (bm : B.BMsg) (cs : C.StdCoins × C.KeepCoins) :
    Option B.BSig :=
  match (C.std sk bm cs.1).run H with
  | none => none
  | some σ => if (C.keep c σ cs.2).run H then some σ else none

/-- **The run of the rejection signer**: after a passed check, the first kept attempt. -/
theorem run_rejectSign (H : X → Y) (K : ℕ) (sk : B.SK) (c : Ctx) (bm : B.BMsg)
    (cs : Fin K → C.StdCoins × C.KeepCoins) :
    (C.rejectSign K sk c bm cs).run H =
      if (C.check c).run H then (List.ofFn cs).findSome? (C.att H sk c bm) else none := by
  rw [rejectSign, rejectWith, OracleProg.run_bind]
  split_ifs
  · rw [run_firstKept, show (List.ofFn fun j =>
        (C.std sk bm (cs j).1, fun σ => C.keep c σ (cs j).2)) =
        (List.ofFn cs).map (fun d => (C.std sk bm d.1, fun σ => C.keep c σ d.2)) by
        rw [List.map_ofFn]; rfl,
      List.findSome?_map]
    congr 1
    funext d
    simp only [Function.comp, att]
    rcases (C.std sk bm d.1).run H with _ | σ <;> rfl
  · rfl

/-! ### The signing oracle with keep coins in the request -/

variable (K n : ℕ)

/-- **The signing oracle with the keep coins in the request**, for `0 < K`: a payload request
`(p, ks)` with `ks : Fin K → KeepCoins` by the key pair `kp` is answered by `rejectSign` at the
context `ctx kp.1 p` on `bmsg p`, with attempt `j` on the oracle's standard coins `cs j` and the
keep coin `ks j` (refused unless `adm kp.1 p`); a base message `bm` is answered by the standard
signer with the standard coins `cs 0`, for itself. -/
noncomputable def keepOracle (hK : 0 < K) : SignOracle B where
  SMsg := (P × (Fin K → C.KeepCoins)) ⊕ B.BMsg
  Coins := Fin K → C.StdCoins
  q := C.qCheck + K * (C.qStd + C.qKeep)
  sign kp
    | .inl p, cs => if C.adm kp.1 p.1 then
        C.rejectSign K kp.2 (C.ctx kp.1 p.1) (C.bmsg p.1) (fun j => (cs j, p.2 j))
      else .pure none
    | .inr bm, cs => C.std kp.2 bm (cs ⟨0, hK⟩)
  sign_queries kp sm cs := by
    rcases sm with p | bm
    · dsimp only
      split_ifs
      · exact C.rejectSign_queries _ _ _ _ _
      · exact (OracleProg.QueriesLE.pure _ _).mono (Nat.zero_le _)
    · have : C.qStd ≤ K * (C.qStd + C.qKeep) :=
        (Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_left _ hK)
      exact (C.std_queries _ _ _).mono (by omega)
  base
    | .inl p => C.bmsg p.1
    | .inr bm => bm

section KeepInstances

variable (hK : 0 < K)

instance keepOracle.instFintypeSMsg [Fintype P] [Fintype TB.BMsg] [Fintype C.KeepCoins] :
    Fintype (C.keepOracle K hK).SMsg :=
  inferInstanceAs (Fintype ((P × (Fin K → C.KeepCoins)) ⊕ B.BMsg))

instance keepOracle.instDecEqSMsg [DecidableEq P] [DecidableEq TB.BMsg]
    [DecidableEq C.KeepCoins] : DecidableEq (C.keepOracle K hK).SMsg :=
  inferInstanceAs (DecidableEq ((P × (Fin K → C.KeepCoins)) ⊕ B.BMsg))

instance keepOracle.instFintypeCoins [Fintype C.StdCoins] : Fintype (C.keepOracle K hK).Coins :=
  inferInstanceAs (Fintype (Fin K → C.StdCoins))

instance keepOracle.instDecEqCoins [DecidableEq C.StdCoins] :
    DecidableEq (C.keepOracle K hK).Coins :=
  inferInstanceAs (DecidableEq (Fin K → C.StdCoins))

instance keepOracle.instNonemptyCoins [Nonempty C.StdCoins] : Nonempty (C.keepOracle K hK).Coins :=
  inferInstanceAs (Nonempty (Fin K → C.StdCoins))

end KeepInstances

/-! ### The signing oracle of the rejection form -/

/-- **The signing oracle of the rejection form with `K` attempts**: a payload `p` under the key
pair `kp` is answered by `rejectSign` at the context `ctx kp.1 p` on the base message `bmsg p`
(refused unless `adm kp.1 p`), with one pair of standard and keep coins per attempt. -/
def oracle : SignOracle B where
  SMsg := P
  Coins := Fin K → C.StdCoins × C.KeepCoins
  q := C.qCheck + K * (C.qStd + C.qKeep)
  sign kp p cs := if C.adm kp.1 p then C.rejectSign K kp.2 (C.ctx kp.1 p) (C.bmsg p) cs
    else .pure none
  sign_queries kp p cs := by
    split_ifs
    · exact C.rejectSign_queries _ _ _ _ _
    · exact (OracleProg.QueriesLE.pure _ _).mono (Nat.zero_le _)
  base p := C.bmsg p

section OracleInstances

instance oracle.instFintypeSMsg [Fintype P] : Fintype (C.oracle K).SMsg :=
  inferInstanceAs (Fintype P)

instance oracle.instDecEqSMsg [DecidableEq P] : DecidableEq (C.oracle K).SMsg :=
  inferInstanceAs (DecidableEq P)

instance oracle.instFintypeCoins [Fintype C.StdCoins] [Fintype C.KeepCoins] :
    Fintype (C.oracle K).Coins :=
  inferInstanceAs (Fintype (Fin K → C.StdCoins × C.KeepCoins))

instance oracle.instDecEqCoins [DecidableEq C.StdCoins] [DecidableEq C.KeepCoins] :
    DecidableEq (C.oracle K).Coins :=
  inferInstanceAs (DecidableEq (Fin K → C.StdCoins × C.KeepCoins))

instance oracle.instNonemptyCoins [Nonempty C.StdCoins] [Nonempty C.KeepCoins] :
    Nonempty (C.oracle K).Coins :=
  inferInstanceAs (Nonempty (Fin K → C.StdCoins × C.KeepCoins))

end OracleInstances

/-! ### The keep coins as side coins -/

section Side

variable {K n}

/-- **The side coins of request number `c`**: those of `s` for `c < Q`, arbitrary after. -/
noncomputable def sideAt {KC : Type} [Nonempty KC] {Q : ℕ} (s : Fin Q → Fin K → KC) (c : ℕ) :
    Fin K → KC :=
  if h : c < Q then s ⟨c, h⟩ else Classical.arbitrary _

/-- The side coins of request number `j < Q` are `s j`. -/
theorem sideAt_fin {KC : Type} [Nonempty KC] {Q : ℕ} (s : Fin Q → Fin K → KC) (j : Fin Q) :
    sideAt s j = s j := by
  simp [sideAt, j.2]

variable [Nonempty C.KeepCoins]

/-- **The message map along the classifier `π`** at the side coins `s`: a message classified as the
payload `p`, numbered `c`, becomes the request `(p, sideAt s c)`; one classified as a base message
stays. -/
noncomputable def keepMsg (hK : 0 < K) {O : SignOracle B} (π : O.SMsg → P ⊕ B.BMsg) {Q : ℕ}
    (s : Fin Q → Fin K → C.KeepCoins) (c : ℕ) (sm : O.SMsg) : (C.keepOracle K hK).SMsg :=
  match π sm with
  | .inl p => .inl (p, sideAt s c)
  | .inr bm => .inr bm

/-- `keepMsg` is injective at every request number when `π` is. -/
theorem keepMsg_injective (hK : 0 < K) {O : SignOracle B} {π : O.SMsg → P ⊕ B.BMsg}
    (hπ : Function.Injective π) {Q : ℕ} (s : Fin Q → Fin K → C.KeepCoins) (c : ℕ) :
    Function.Injective (C.keepMsg hK π s c) := by
  intro a b h
  apply hπ
  unfold keepMsg at h
  rcases ha : π a with p | bm <;> rcases hb : π b with p' | bm' <;> rw [ha, hb] at h
  · exact congrArg Sum.inl (Prod.mk.inj (Sum.inl_injective h)).1
  · exact (Sum.inl_ne_inr h).elim
  · exact (Sum.inr_ne_inl h).elim
  · exact congrArg Sum.inr (Sum.inr_injective h)

end Side

/-- **The oracle `O` signs as the rejection form `C`**, its messages classified by `π` into payloads
and base messages and its coins read as `K` pairs of standard and keep coins through `e`: at every
oracle, key coins, message and coins, a payload request runs as `rejectSign` at its context
(refused unless admitted) and a base message as the standard signer with the standard coins of
attempt `0`; and the base message of a message is that of its class. -/
structure SignsOn (hK : 0 < K) (O : SignOracle B) (π : O.SMsg → P ⊕ B.BMsg)
    (e : O.Coins ≃ (Fin K → C.StdCoins × C.KeepCoins)) : Prop where
  /-- The signer on payloads and base messages. -/
  sign_eq : ∀ (H : X → Y) (kc : B.KeyCoins) (sm : O.SMsg) (c : O.Coins),
    (O.sign (B.keyGen kc) sm c).run H =
      match π sm with
      | .inl p => (if C.adm (B.keyGen kc).1 p then
          C.rejectSign K (B.keyGen kc).2 (C.ctx (B.keyGen kc).1 p) (C.bmsg p) (e c)
        else .pure none).run H
      | .inr bm => (C.std (B.keyGen kc).2 bm (e c ⟨0, hK⟩).1).run H
  /-- The base messages. -/
  base_eq : ∀ sm : O.SMsg, (match π sm with
      | .inl p => C.bmsg p
      | .inr bm => bm) = O.base sm

/-- The rejection form's oracle signs as the rejection form, every message a payload. -/
theorem signsOn_oracle (hK : 0 < K) :
    C.SignsOn K hK (C.oracle K) Sum.inl (Equiv.refl _) where
  sign_eq _ _ _ _ := rfl
  base_eq _ := rfl

/-! ### The relay programs -/

section Programs

variable [Zero Y]

/-- **The relayed rejection signing** at the context `c` on the base message `bm`, with the keep
coins `ks`, for user `i`: the public check, then the first of `K` standard signatures of user `i` on
`bm`, each asked of the main challenger, that the public keep decision with the keep coin `ks j` of
attempt `j` keeps (`rejectWith` with main requests as the attempts). -/
def relaySign (c : Ctx) (bm : B.BMsg) (ks : Fin K → C.KeepCoins) (i : Fin n) :
    OracleProg (X ⊕ MURequest C.stdOracle n) (Y ⊕ Option (MUResponse B)) (Option B.BSig) :=
  (MultiRelay.liftQ (C.check c)).bind fun ok =>
    if ok then firstKept (List.ofFn fun j : Fin K =>
      ((askResp (.sign i bm)).mapOutput toSig,
        fun σ => MultiRelay.liftQ (C.keep c σ (ks j))))
    else .pure none

/-- **The relay program of a request of the game with keep coins in the request**, with the users'
public keys `pks`: a public-key request or a corruption is asked of the main challenger as it is;
a payload request of user `i` for `(p, ks)` is refused unless `adm (pks i) p`, and otherwise relayed
by `relaySign` at the context `ctx (pks i) p` on `bmsg p`; a base message is asked as it is. -/
def prog (hK : 0 < K) (pks : Fin n → B.PK) :
    MURequest (C.keepOracle K hK) n →
      OracleProg (X ⊕ MURequest C.stdOracle n) (Y ⊕ Option (MUResponse B)) (Option (MUResponse B))
  | .publicKey i => askResp (.publicKey i)
  | .corrupt i => askResp (.corrupt i)
  | .sign i (.inl p) => if C.adm (pks i) p.1 then
      (C.relaySign K n (C.ctx (pks i) p.1) (C.bmsg p.1) p.2 i).mapOutput (Option.map .signature)
    else .pure none
  | .sign i (.inr bm) => askResp (.sign i bm)

/-- **The relay of the game with keep coins in the request to the standard game**: the programs
`prog`, `K` main requests and `qCheck + K · qKeep` queries per request, the idle request the public
key of user `i₀`. -/
def relay (hK : 0 < K) (pks : Fin n → B.PK) (i₀ : Fin n) :
    MultiRelay X Y (MURequest (C.keepOracle K hK) n) (MUResponse B)
      (MURequest C.stdOracle n) (MUResponse B) where
  prog := MultiRelay.plainProg (C.prog K n hK pks)
  K := K
  K_pos := hK
  qR := C.qCheck + K * C.qKeep
  idle := .publicKey i₀

end Programs

/-! ### The main requests of the relay -/

section Asks

variable {C K n}

/-- **The main request a request relays to**: the same public-key request or corruption, or a
signing request of the same user for its base message. -/
def Ask {hK : 0 < K} : MURequest (C.keepOracle K hK) n → MURequest C.stdOracle n → Prop
  | .publicKey i, r' => r' = .publicKey i
  | .corrupt i, r' => r' = .corrupt i
  | .sign i sm, r' => r' = .sign i ((C.keepOracle K hK).base sm)

variable [Zero Y]

/-- **Every main request of the relayed rejection signing** is the signing request of user `i` for
`bm`. -/
theorem asksIn_relaySign (c : Ctx) (bm : B.BMsg) (ks : Fin K → C.KeepCoins) (i : Fin n) :
    MultiRelay.AsksIn (MUResponse B) (C.relaySign K n c bm ks i) (· = .sign i bm) := by
  refine MultiRelay.AsksIn.bind (MultiRelay.AsksIn.liftQ _ _) fun ok => ?_
  split_ifs
  · refine asksIn_firstKept _ fun q hq => ?_
    obtain ⟨_, rfl⟩ := List.mem_ofFn.1 hq
    exact ⟨(asksIn_askResp _).mapOutput _, fun σ => MultiRelay.AsksIn.liftQ _ _⟩
  · exact MultiRelay.AsksIn.pure _ _

/-- **Every main request of the relay program of `r` is one `r` relays to.** -/
theorem asksIn_prog (hK : 0 < K) (pks : Fin n → B.PK) (r : MURequest (C.keepOracle K hK) n) :
    MultiRelay.AsksIn (MUResponse B) (C.prog K n hK pks r) (Ask r) := by
  rcases r with i | ⟨i, p | bm⟩ | i
  · exact asksIn_askResp _
  · simp only [prog]
    split_ifs
    · exact (asksIn_relaySign _ _ _ _).mapOutput _
    · exact MultiRelay.AsksIn.pure _ _
  · exact asksIn_askResp _
  · exact asksIn_askResp _

/-- **The relay's histories relay the game's** (`HistRelay`): if every request of the standard
history `hist'` is the idle request (a public key) or one that a request of the history `hist`
relays to, every signing request of `hist'` is for the base message of a signing request of the
same user in `hist`, and every corruption of `hist'` is one of `hist`. -/
theorem histRelay_of_relays (hK : 0 < K) (pks : Fin n → B.PK) (i₀ : Fin n)
    {hist : MUHist (C.keepOracle K hK) n} {hist' : MUHist C.stdOracle n}
    (h : ∀ e' ∈ hist', e'.request = (C.relay K n hK pks i₀).idle ∨
      ∃ e ∈ hist, (C.relay K n hK pks i₀).CanAsk e.request e'.request) :
    HistRelay hist hist' where
  sign_mem e' he' i sm' hr := by
    rcases h e' he' with h1 | ⟨e, he, hc⟩
    · rw [hr] at h1
      cases h1
    · have := (C.relay K n hK pks i₀).canAsk_of_asksIn (asksIn_prog hK pks e.request).plainProg hc
      rw [hr] at this
      rcases hreq : e.request with j | ⟨j, sm⟩ | j <;> rw [hreq] at this <;>
        simp only [Ask] at this
      · cases this
      · obtain ⟨rfl, rfl⟩ := MURequest.sign.inj this
        exact ⟨e, he, sm, hreq, rfl⟩
      · cases this
  corrupt_mem i := by
    rintro ⟨e', he', hr⟩
    rcases h e' he' with h1 | ⟨e, he, hc⟩
    · rw [hr] at h1
      cases h1
    · have := (C.relay K n hK pks i₀).canAsk_of_asksIn (asksIn_prog hK pks e.request).plainProg hc
      rw [hr] at this
      rcases hreq : e.request with j | ⟨j, sm⟩ | j <;> rw [hreq] at this <;>
        simp only [Ask] at this
      · cases this
      · cases this
      · cases this
        exact ⟨e, he, hreq⟩

end Asks

/-! ### The relayed requests against the standard challenger -/

section Runs

variable [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y] {C K n} [Fintype C.StdCoins] [DecidableEq C.StdCoins] [Nonempty C.StdCoins]
  (keys : Fin n → B.KeyCoins) (Q : ℕ) (H : X → Y) (c' : Fin (K * Q) → C.StdCoins)

variable (C) in
/-- The standard challenger's replies. -/
noncomputable abbrev stdAns : List (MURequest C.stdOracle n) → MURequest C.stdOracle n →
    Option (MUResponse B) :=
  (muChallenger C.stdOracle n keys (K * Q)).toPureEnv.answerAfter (H, c')

/-- **One attempt**: a standard signature of user `i` on `bm`, asked of the standard challenger
as main request number `|L|`. -/
theorem runsWith_attempt (L : List (MURequest C.stdOracle n)) (hL : L.length < K * Q) (i : Fin n)
    (bm : B.BMsg) :
    MultiRelay.RunsWith (C.stdAns keys Q H c') H L
      ((askResp (Resp' := MUResponse B) (.sign i bm)).mapOutput toSig)
      ((C.std (B.keyGen (keys i)).2 bm (c' ⟨L.length, hL⟩)).run H) [.sign i bm] 0 := by
  have h := (MultiRelay.RunsWith.query_inr (ansM := C.stdAns keys Q H c') (H := H) (rs := L)
    (k := fun b => OracleProg.pure (b.elim (fun _ => none) id)) (.sign i bm)
    (MultiRelay.RunsWith.pure _ _)).mapOutput toSig
  refine h.congr_res ?_
  simp only [Sum.elim_inr, id]
  have ha := answerAfter_muChallenger C.stdOracle keys (K * Q) H c' L (.sign i bm) hL
  refine (congrArg toSig ha).trans ?_
  change toSig (Option.map MUResponse.signature ((C.std (B.keyGen (keys i)).2 bm _).run H)) = _
  rcases (C.std (B.keyGen (keys i)).2 bm (c' ⟨L.length, hL⟩)).run H with _ | σ <;> rfl

/-- **The attempts**: the first kept of `m` standard signatures of user `i` on `bm`, asked as main
requests number `|L|, …, |L| + m - 1` and kept by the keep decisions at the context `c` with the
keep coins `ks`, runs with the first kept attempt of their coins, at most `m` main requests and at
most `m · qKeep` queries. -/
theorem runsWith_firstKept (i : Fin n) (c : Ctx) (bm : B.BMsg) :
    ∀ (m : ℕ) (ks : Fin m → C.KeepCoins) (L : List (MURequest C.stdOracle n))
      (hL : L.length + m ≤ K * Q),
      ∃ asks q, MultiRelay.RunsWith (C.stdAns keys Q H c') H L
        (firstKept (List.ofFn fun t : Fin m =>
          ((askResp (Resp' := MUResponse B) (.sign i bm)).mapOutput toSig,
            fun σ => MultiRelay.liftQ (Req' := MURequest C.stdOracle n) (Resp' := MUResponse B)
              (C.keep c σ (ks t)))))
        ((List.ofFn fun t : Fin m => (c' ⟨L.length + t, by omega⟩, ks t)).findSome?
          (C.att H (B.keyGen (keys i)).2 c bm)) asks q ∧ asks.length ≤ m ∧ q ≤ m * C.qKeep
  | 0, _, L, _ => ⟨[], 0, MultiRelay.RunsWith.pure _ _, le_rfl, Nat.zero_le _⟩
  | m + 1, ks, L, hL => by
    have hA := runsWith_attempt keys Q H c' L (by omega) i bm
    obtain ⟨asks₂, q₂, h₂, ha₂, hq₂⟩ := runsWith_firstKept i c bm m (fun t => ks t.succ)
      (L ++ [.sign i bm]) (by simp; omega)
    have hrest : (List.ofFn fun t : Fin m =>
        (c' ⟨(L ++ [MURequest.sign i bm]).length + t, by simp; omega⟩, ks t.succ)) =
        List.ofFn fun t : Fin m => (c' ⟨L.length + (t.succ : ℕ), by simp; omega⟩, ks t.succ) := by
      congr 1
      funext t
      congr 2
      ext
      simp
      omega
    rw [hrest] at h₂
    rw [List.ofFn_succ, List.ofFn_succ, firstKept, List.findSome?_cons]
    simp only [Fin.val_zero, Nat.add_zero]
    rcases hx : (C.std (B.keyGen (keys i)).2 bm (c' ⟨L.length, by omega⟩)).run H with _ | σ
    · have hatt : C.att H (B.keyGen (keys i)).2 c bm (c' ⟨L.length, by omega⟩, ks 0) = none := by
        simp only [att, hx]
      rw [hatt]
      dsimp only
      refine ⟨[.sign i bm] ++ asks₂, 0 + q₂, MultiRelay.RunsWith.bind hA ?_, ?_, ?_⟩
      · rw [hx]
        exact h₂
      · simp only [List.singleton_append, List.length_cons]
        omega
      · rw [Nat.zero_add, Nat.succ_mul]
        omega
    · have hk := MultiRelay.RunsWith.liftQ (ansM := C.stdAns keys Q H c') (H := H)
        (Resp' := MUResponse B) (L ++ [.sign i bm]) (C.keep c σ (ks 0))
      have hkq := C.keep_queries c σ (ks 0) H
      rcases hb : (C.keep c σ (ks 0)).run H
      · have hatt : C.att H (B.keyGen (keys i)).2 c bm (c' ⟨L.length, by omega⟩, ks 0) =
            none := by
          simp only [att, hx, hb, Bool.false_eq_true, ite_false]
        rw [hatt]
        dsimp only
        refine ⟨[.sign i bm] ++ ([] ++ asks₂),
          0 + ((C.keep c σ (ks 0)).trace H).length + q₂, ?_, ?_, ?_⟩
        · rw [Nat.add_assoc]
          refine MultiRelay.RunsWith.bind hA ?_
          rw [hx]
          refine MultiRelay.RunsWith.bind hk ?_
          rw [hb, List.append_nil]
          exact h₂
        · simp only [List.singleton_append, List.nil_append, List.length_cons]
          omega
        · rw [Nat.zero_add, Nat.succ_mul]
          omega
      · have hatt : C.att H (B.keyGen (keys i)).2 c bm (c' ⟨L.length, by omega⟩, ks 0) =
            some σ := by
          simp only [att, hx, hb, ite_true]
        rw [hatt]
        dsimp only
        refine ⟨[.sign i bm] ++ ([] ++ []),
          0 + (((C.keep c σ (ks 0)).trace H).length + 0), ?_, ?_, ?_⟩
        · refine MultiRelay.RunsWith.bind hA ?_
          rw [hx]
          refine MultiRelay.RunsWith.bind hk ?_
          rw [hb]
          exact MultiRelay.RunsWith.pure _ _
        · simp
        · rw [Nat.zero_add, Nat.add_zero, Nat.succ_mul]
          omega

/-- **The relayed rejection signing** runs with the rejection step on the attempts' coins: the
check, then the first kept of the `K` attempts asked as main requests number
`|L|, …, |L| + K - 1`, with the keep coins `ks`. -/
theorem runsWith_relaySign (i : Fin n) (c : Ctx) (bm : B.BMsg) (ks : Fin K → C.KeepCoins)
    (L : List (MURequest C.stdOracle n)) (hL : L.length + K ≤ K * Q) :
    ∃ asks q, MultiRelay.RunsWith (C.stdAns keys Q H c') H L (C.relaySign K n c bm ks i)
      (if (C.check c).run H then
        (List.ofFn fun t : Fin K => (c' ⟨L.length + t, by omega⟩, ks t)).findSome?
          (C.att H (B.keyGen (keys i)).2 c bm) else none) asks q ∧
      asks.length ≤ K ∧ q ≤ C.qCheck + K * C.qKeep := by
  have hc := MultiRelay.RunsWith.liftQ (ansM := C.stdAns keys Q H c') (H := H)
    (Resp' := MUResponse B) L (C.check c)
  have hcq := C.check_queries c H
  rcases hok : (C.check c).run H
  · refine ⟨[] ++ [], ((C.check c).trace H).length + 0, MultiRelay.RunsWith.bind hc ?_, ?_, ?_⟩
    · rw [hok]
      exact MultiRelay.RunsWith.pure _ _
    · simp
    · omega
  · obtain ⟨asks₂, q₂, h₂, ha₂, hq₂⟩ := runsWith_firstKept keys Q H c' i c bm K ks (L ++ [])
      (by simpa using hL)
    refine ⟨[] ++ asks₂, ((C.check c).trace H).length + q₂, MultiRelay.RunsWith.bind hc ?_, ?_, ?_⟩
    · rw [hok]
      simp only [ite_true]
      refine h₂.congr_res ?_
      simp only [List.append_nil]
    · simpa using ha₂
    · omega

/-- **A relayed request runs with the reply of the challenger with keep coins in the request**:
the request numbered `j < Q`, after the main requests `L` of the `j` before it, runs with `muReply`
at the attempts' coins of request `j`, at most `K` main requests and `qCheck + K · qKeep`
queries. -/
theorem runsWith_prog (hK : 0 < K) (j : ℕ) (hj : j < Q) (L : List (MURequest C.stdOracle n))
    (hL : L.length = K * j) (r : MURequest (C.keepOracle K hK) n) :
    ∃ asks q, MultiRelay.RunsWith (C.stdAns keys Q H c') H L
      (C.prog K n hK (fun i => B.pk (keys i)) r)
      (muReply (C.keepOracle K hK) keys H (attemptCoins Q c' ⟨j, hj⟩) r) asks q ∧
      asks.length ≤ K ∧ q ≤ C.qCheck + K * C.qKeep := by
  have hLK : L.length + K ≤ K * Q := by
    rw [hL]
    have := Nat.mul_le_mul_left K (Nat.succ_le_of_lt hj)
    rw [Nat.mul_succ] at this
    exact this
  have hLt : L.length < K * Q := by omega
  rcases r with i | ⟨i, ⟨p, ks⟩ | bm⟩ | i
  · have h := MultiRelay.RunsWith.query_inr (ansM := C.stdAns keys Q H c') (H := H) (rs := L)
      (k := fun b => OracleProg.pure (b.elim (fun _ => none) id)) (.publicKey i)
      (MultiRelay.RunsWith.pure _ _)
    refine ⟨_, _, h.congr_res ?_, by simp; omega, Nat.zero_le _⟩
    exact answerAfter_muChallenger C.stdOracle keys (K * Q) H c' L _ hLt
  · simp only [prog]
    by_cases hm : C.adm (B.pk (keys i)) p
    · rw [ite_eq_left hm]
      obtain ⟨asks, q, h, ha, hq⟩ := runsWith_relaySign keys Q H c' i
        (C.ctx (B.pk (keys i)) p) (C.bmsg p) ks L hLK
      refine ⟨asks, q, (h.mapOutput (Option.map MUResponse.signature)).congr_res ?_, ha, hq⟩
      simp only [muReply, keepOracle]
      have hm' : C.adm (B.keyGen (keys i)).1 p := hm
      rw [ite_eq_left hm', C.run_rejectSign]
      congr 2
      simp only [attemptCoins]
      congr 1
      refine congrArg List.ofFn (funext fun t => ?_)
      congr 2
      exact Fin.ext (by simp [hL])
    · rw [ite_eq_right hm]
      refine ⟨[], 0, (MultiRelay.RunsWith.pure _ _).congr_res ?_, Nat.zero_le _, Nat.zero_le _⟩
      simp only [muReply, keepOracle]
      have hm' : ¬ C.adm (B.keyGen (keys i)).1 p := hm
      rw [ite_eq_right hm']
      rfl
  · have h := MultiRelay.RunsWith.query_inr (ansM := C.stdAns keys Q H c') (H := H) (rs := L)
      (k := fun b => OracleProg.pure (b.elim (fun _ => none) id)) (.sign i bm)
      (MultiRelay.RunsWith.pure _ _)
    refine ⟨_, _, h.congr_res ?_, by simp; omega, Nat.zero_le _⟩
    refine (answerAfter_muChallenger C.stdOracle keys (K * Q) H c' L _ hLt).trans ?_
    have hc : c' ⟨L.length, hLt⟩ = attemptCoins Q c' ⟨j, hj⟩ ⟨0, hK⟩ :=
      congrArg c' (Fin.ext (by simp [hL]))
    change Option.map MUResponse.signature
        ((C.std (B.keyGen (keys i)).2 bm (c' ⟨L.length, hLt⟩)).run H) =
      Option.map MUResponse.signature
        ((C.std (B.keyGen (keys i)).2 bm (attemptCoins Q c' ⟨j, hj⟩ ⟨0, hK⟩)).run H)
    rw [hc]
  · have h := MultiRelay.RunsWith.query_inr (ansM := C.stdAns keys Q H c') (H := H) (rs := L)
      (k := fun b => OracleProg.pure (b.elim (fun _ => none) id)) (.corrupt i)
      (MultiRelay.RunsWith.pure _ _)
    refine ⟨_, _, h.congr_res ?_, by simp; omega, Nat.zero_le _⟩
    exact answerAfter_muChallenger C.stdOracle keys (K * Q) H c' L _ hLt

end Runs

/-! ### The challenger with keep coins in the request relays the standard challenger -/

section Relays

variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] {C K n} [Fintype C.StdCoins] [DecidableEq C.StdCoins]
  [Nonempty C.StdCoins] [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Fintype TB.BMsg] [DecidableEq TB.BMsg]
  [Fintype P] [DecidableEq P] [Fintype C.KeepCoins] [DecidableEq C.KeepCoins]

/-- **The challenger with keep coins in the request, with `Q` requests, is the relay `relay` of the
standard challenger with `K · Q` requests** (`MultiRelay.RelaysChallenger`), along the attempts'
coins: each request is answered as its relay program answers it against the standard replies. -/
theorem relaysChallenger_relay (hK : 0 < K) (keys : Fin n → B.KeyCoins) (i₀ : Fin n) (Q : ℕ) :
    letI : Inhabited (MURequest C.stdOracle n) := ⟨.publicKey i₀⟩
    (C.relay K n hK (fun i => B.pk (keys i)) i₀).RelaysChallenger
      (muChallenger (C.keepOracle K hK) n keys Q)
      (muChallenger C.stdOracle n keys (K * Q)) (attemptCoins Q) := by
  let _ : Inhabited (MURequest C.stdOracle n) := ⟨.publicKey i₀⟩
  exact {
    coins_eq := (map_uniformOfFintype_equiv (attemptCoinsEquiv hK Q)).symm
    oracle_eq := fun H c _ lg => (muChallenger_noAssign _ keys Q).oracle_eq H c lg
    oracle_eq' := fun H c' _ lg => (muChallenger_noAssign _ keys (K * Q)).oracle_eq H c' lg
    answer_eq := fun H c' rs r hi => by
      rw [answerAfter_muChallenger (C.keepOracle K hK) keys Q H (attemptCoins Q c') rs r hi]
      obtain ⟨asks, q, h, ha, hq⟩ := runsWith_prog keys Q H c' hK rs.length hi
        ((C.relay K n hK (fun i => B.pk (keys i)) i₀).mainReqs Q
          ((muChallenger C.stdOracle n keys (K * Q)).toPureEnv.answerAfter (H, c')) H rs)
        ((C.relay K n hK (fun i => B.pk (keys i)) i₀).length_mainReqs Q _ H rs hi.le) r
      exact ((C.relay K n hK (fun i => B.pk (keys i)) i₀).runReply_eq_of_runsWith rfl h ha
        hq).symm }

end Relays

/-! ### The lifting lemma -/

section Lifting

variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] {V : OracleView X Y} {t : ℕ} [Fintype C.StdCoins]
  [DecidableEq C.StdCoins] [Nonempty C.StdCoins] [Fintype C.KeepCoins] [DecidableEq C.KeepCoins]
  [Nonempty C.KeepCoins] [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] [Fintype TB.BMsg]
  [DecidableEq TB.BMsg] [Fintype P] [DecidableEq P]

/-- **The relayed multi-user adversary** of an adversary `A` of the game with the signing oracle
`O` and `Q` requests, along the message maps `f s` at the side coins `s`: on the public keys
`pks`, the auxiliary input of `A` with uniform side coins `s : Fin Q → Fin K → KeepCoins`, the
algorithm of `A` with its requests absorbed through `msgRelay (f s)`
(`QueryBoundedAdversary.absorbSide`, an adversary of the game with keep coins in the request), then
relayed by the programs `relay` at `pks` (`QueryBoundedAdversary.relay`), answering `Q` requests,
with `K` standard requests and `qCheck + K · qKeep` queries per request, the idle request the
public key of user `i₀`. It makes at most `t + Q · (qCheck + K · qKeep)` queries on every
branch. -/
noncomputable def liftAdversary (hK : 0 < K) (i₀ : Fin n) {O : SignOracle B} [Fintype O.SMsg]
    [DecidableEq O.SMsg] (Q : ℕ)
    (f : (Fin Q → Fin K → C.KeepCoins) → ℕ → O.SMsg → (C.keepOracle K hK).SMsg)
    (hf : ∀ s c, Function.Injective (f s c)) (A : MUAdversary O n V t) :
    MUAdversary C.stdOracle n V (t + Q * (C.qCheck + K * C.qKeep)) := fun inp =>
  letI : Inhabited (MURequest (C.keepOracle K hK) n) := ⟨.publicKey i₀⟩
  letI : Inhabited (MURequest C.stdOracle n) := ⟨.publicKey i₀⟩
  ((A inp).absorbSide (PMF.uniformOfFintype (Fin Q → Fin K → C.KeepCoins))
    (fun s => msgRelay n (f s)) fun s c => MURequest.mapMsg_injective (hf s c)).relay
      (C.relay K n hK inp.1 i₀) Q

/-- **The relayed multi-user adversary along the classifier `π`** (`liftAdversary` along
`keepMsg π`). -/
noncomputable def relayAdversary (hK : 0 < K) (i₀ : Fin n) {O : SignOracle B} [Fintype O.SMsg]
    [DecidableEq O.SMsg] {π : O.SMsg → P ⊕ B.BMsg} (hπ : Function.Injective π)
    (A : MUAdversary O n V t) (Q : ℕ) :
    MUAdversary C.stdOracle n V (t + Q * (C.qCheck + K * C.qKeep)) :=
  C.liftAdversary K n hK i₀ Q (C.keepMsg hK π) (C.keepMsg_injective hK hπ) A

variable {C K n}

omit [Nonempty TB.KeyCoins] in
/-- **The two steps of the relay for an event of the transcript**, at the users' key coins `keys`
and the oracle `H`: the transcript of `A` against the challenger of `O` lies in `E` with at most the
probability that the transcript of `liftAdversary` against the standard challenger with `K · Q`
requests lies in `E''`, when `E` passes to `E'` along every relay of messages (`himp₁`) and `E'` to
`E''` along every relay history of `relay` (`himp₂`). Hypotheses: the signing coins split along
`e` into uniform side coins and uniform standard coins (`hcoins`), and at the side coins `s` the
challenger of `O` relays the challenger of `keepOracle` by `msgRelay (f s)` (`hrel`). -/
theorem transcriptLaw_le_lift (hK : 0 < K) (i₀ : Fin n) {O : SignOracle B} [Fintype O.SMsg]
    [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins] (Q : ℕ)
    (f : (Fin Q → Fin K → C.KeepCoins) → ℕ → O.SMsg → (C.keepOracle K hK).SMsg)
    (hf : ∀ s c, Function.Injective (f s c))
    (e : (Fin Q → O.Coins) ≃ (Fin Q → Fin K → C.KeepCoins) × (Fin Q → Fin K → C.StdCoins))
    (hcoins : ∀ s c', PMF.uniformOfFintype _ (e.symm (s, c')) =
      PMF.uniformOfFintype _ s * PMF.uniformOfFintype _ c')
    (keys : Fin n → B.KeyCoins)
    (hrel : ∀ s c', (msgRelay n (f s)).RelaysChallenger (muChallenger O n keys Q) (e.symm (s, c'))
      (muChallenger (C.keepOracle K hK) n keys Q) c')
    (A : MUAdversary O n V t) (H : X → Y)
    (E : (B.PK × B.BMsg × B.BSig) × MUHist O n → Prop)
    (E' : (B.PK × B.BMsg × B.BSig) × MUHist (C.keepOracle K hK) n → Prop)
    (E'' : (B.PK × B.BMsg × B.BSig) × MUHist C.stdOracle n → Prop)
    (himp₁ : ∀ s o hist hist', E (o, hist) →
      hist'.map HistoryEntry.request = (msgRelay n (f s)).relayList
        (hist.map HistoryEntry.request) → E' (o, hist'))
    (himp₂ : ∀ o hist hist', E' (o, hist) → HistRelay hist hist' → E'' (o, hist')) :
    ((A (fun i => B.pk (keys i), V.view H)).transcriptLaw (muChallenger O n keys Q)
      H).toOuterMeasure {x | ∃ p ∈ x, E p} ≤
      ((C.liftAdversary K n hK i₀ Q f hf A (fun i => B.pk (keys i), V.view H)).transcriptLaw
        (muChallenger C.stdOracle n keys (K * Q)) H).toOuterMeasure {x | ∃ p ∈ x, E'' p} := by
  let _ : Inhabited (MURequest (C.keepOracle K hK) n) := ⟨.publicKey i₀⟩
  let _ : Inhabited (MURequest C.stdOracle n) := ⟨.publicKey i₀⟩
  refine le_trans ((A (fun i => B.pk (keys i), V.view H)).transcriptLaw_le_absorbSide
    (C := muChallenger O n keys Q) (C' := muChallenger (C.keepOracle K hK) n keys Q)
    (PMF.uniformOfFintype (Fin Q → Fin K → C.KeepCoins)) (fun s => msgRelay n (f s)) e hcoins hrel
    rfl (fun s c => MURequest.mapMsg_injective (hf s c)) H E E' himp₁) ?_
  refine le_of_le_of_eq
    (((A (fun i => B.pk (keys i), V.view H)).absorbSide _ _ _).transcriptLaw_le_relay
    (C.relay K n hK (fun i => B.pk (keys i)) i₀)
    (muChallenger (C.keepOracle K hK) n keys Q) (muChallenger C.stdOracle n keys (K * Q))
    (attemptCoins Q) (relaysChallenger_relay hK keys i₀ Q) H E' E''
    (fun o hist hist' hE hr => himp₂ o hist hist' hE (histRelay_of_relays hK _ i₀ hr))) ?_
  congr 3

/-- **The lifting lemma for MU-EUF-CMA^corr along a relay of messages**: under the hypotheses of
`transcriptLaw_le_lift` at every key coins, with base messages kept by `f` (`hb`), every adversary
`A` of the game with the signing oracle `O` and `Q` requests has at most the success probability
of `liftAdversary` in the standard game with `K · Q` requests. -/
theorem muEufProb_le_lift (hK : 0 < K) (i₀ : Fin n) {O : SignOracle B} [Fintype O.SMsg]
    [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins] (Q : ℕ)
    (f : (Fin Q → Fin K → C.KeepCoins) → ℕ → O.SMsg → (C.keepOracle K hK).SMsg)
    (hf : ∀ s c, Function.Injective (f s c))
    (hb : ∀ s c sm, (C.keepOracle K hK).base (f s c sm) = O.base sm)
    (e : (Fin Q → O.Coins) ≃ (Fin Q → Fin K → C.KeepCoins) × (Fin Q → Fin K → C.StdCoins))
    (hcoins : ∀ s c', PMF.uniformOfFintype _ (e.symm (s, c')) =
      PMF.uniformOfFintype _ s * PMF.uniformOfFintype _ c')
    (hrel : ∀ keys s c', (msgRelay n (f s)).RelaysChallenger (muChallenger O n keys Q)
      (e.symm (s, c')) (muChallenger (C.keepOracle K hK) n keys Q) c')
    (A : MUAdversary O n V t) :
    muEufProb A Q ≤ muEufProb (C.liftAdversary K n hK i₀ Q f hf A) (K * Q) := by
  unfold muEufProb muLaw runLaw
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  refine ENNReal.tsum_le_tsum fun keys => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  refine ENNReal.tsum_le_tsum fun H => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  exact transcriptLaw_le_lift hK i₀ Q f hf e hcoins keys (hrel keys) A H
    (fun p => Forges keys H p.1 p.2) (fun p => Forges keys H p.1 p.2)
    (fun p => Forges keys H p.1 p.2)
    (fun s _ _ _ hE hmap => hE.of_histRelay (histRelay_of_msgRelay (hb s) hmap))
    (fun _ _ _ hE hr => hE.of_histRelay hr)

/-- **The strong-forgery probability is at most the relayed adversary's probability of a verifying
signature under an uncorrupted user's key**, along a relay of messages: under the hypotheses of
`muEufProb_le_lift`, the success probability of `A` in MU-SUF-CMA^corr is at most `muVerifyProb`
of `liftAdversary` with `K · Q` requests. The right-hand side counts the signatures passed on to
`A` as well, so this is not a reduction to MU-SUF-CMA^corr. -/
theorem muSufProb_le_muVerifyProb_lift (hK : 0 < K) (i₀ : Fin n) {O : SignOracle B}
    [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]
    [Nonempty O.Coins] (Q : ℕ)
    (f : (Fin Q → Fin K → C.KeepCoins) → ℕ → O.SMsg → (C.keepOracle K hK).SMsg)
    (hf : ∀ s c, Function.Injective (f s c))
    (hb : ∀ s c sm, (C.keepOracle K hK).base (f s c sm) = O.base sm)
    (e : (Fin Q → O.Coins) ≃ (Fin Q → Fin K → C.KeepCoins) × (Fin Q → Fin K → C.StdCoins))
    (hcoins : ∀ s c', PMF.uniformOfFintype _ (e.symm (s, c')) =
      PMF.uniformOfFintype _ s * PMF.uniformOfFintype _ c')
    (hrel : ∀ keys s c', (msgRelay n (f s)).RelaysChallenger (muChallenger O n keys Q)
      (e.symm (s, c')) (muChallenger (C.keepOracle K hK) n keys Q) c')
    (A : MUAdversary O n V t) :
    muSufProb A Q ≤ muVerifyProb (C.liftAdversary K n hK i₀ Q f hf A) (K * Q) := by
  unfold muSufProb muVerifyProb muLaw runLaw
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  refine ENNReal.tsum_le_tsum fun keys => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  refine ENNReal.tsum_le_tsum fun H => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  exact transcriptLaw_le_lift hK i₀ Q f hf e hcoins keys (hrel keys) A H
    (fun p => StrongForges keys H p.1 p.2) (fun p => HonestVerifies keys H p.1 p.2)
    (fun p => HonestVerifies keys H p.1 p.2)
    (fun s _ _ _ hE hmap => hE.honestVerifies.of_histRelay (histRelay_of_msgRelay (hb s) hmap))
    (fun _ _ _ hE hr => hE.of_histRelay hr)

/-! ### Oracles that sign as the rejection form -/

variable {O : SignOracle B} {π : O.SMsg → P ⊕ B.BMsg}
  {e : O.Coins ≃ (Fin K → C.StdCoins × C.KeepCoins)}

omit [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y] [Fintype C.StdCoins] [DecidableEq C.StdCoins] [Nonempty C.StdCoins]
  [Fintype C.KeepCoins] [DecidableEq C.KeepCoins] [Fintype TB.PK] [DecidableEq TB.PK]
  [Fintype TB.BSig] [DecidableEq TB.BSig] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]
  [Nonempty TB.KeyCoins] [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype P] [DecidableEq P] in
/-- **`keepMsg` keeps the base messages** of an oracle that signs as the rejection form. -/
theorem SignsOn.keepMsg_base {hK : 0 < K} (h : C.SignsOn K hK O π e) {Q : ℕ}
    (s : Fin Q → Fin K → C.KeepCoins) (c : ℕ) (sm : O.SMsg) :
    (C.keepOracle K hK).base (C.keepMsg hK π s c sm) = O.base sm := by
  rw [← h.base_eq sm]
  unfold keepMsg
  rcases π sm with p | bm <;> rfl

omit [Nonempty X] [Inhabited X] [DecidableEq Y] [AddGroup Y] [Fintype C.KeepCoins]
  [DecidableEq C.KeepCoins] [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig]
  [DecidableEq TB.BSig] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins]
  [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype P] [DecidableEq P] in
/-- **The challenger of an oracle that signs as the rejection form relays the challenger with keep
coins in the request**, at the side coins `s` and the standard coins `c'`: signing request number
`c` for a payload `p` is answered as the request for `(p, sideAt s c)`, a base message as it is. -/
theorem SignsOn.relaysChallenger_keep {hK : 0 < K} (h : C.SignsOn K hK O π e) [Fintype O.Coins]
    [DecidableEq O.Coins] [Nonempty O.Coins] (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (s : Fin Q → Fin K → C.KeepCoins) (c' : Fin Q → Fin K → C.StdCoins) :
    (msgRelay n (C.keepMsg hK π s)).RelaysChallenger (muChallenger O n keys Q)
      ((keepSplit e Q).symm (s, c')) (muChallenger (C.keepOracle K hK) n keys Q) c' := by
  refine relaysChallenger_msgRelay (O := O) (O' := C.keepOracle K hK) _ keys Q _ c'
    fun j i sm G => ?_
  have he : e ((keepSplit e Q).symm (s, c') j) = fun k => (c' j k, s j k) := by
    simp [keepSplit]
  rw [h.sign_eq, he]
  unfold keepMsg
  rcases π sm with p | bm
  · change _ = (if C.adm (B.keyGen (keys i)).1 p then
        C.rejectSign K (B.keyGen (keys i)).2 (C.ctx (B.keyGen (keys i)).1 p) (C.bmsg p)
          (fun k => (c' j k, sideAt s j k)) else .pure none).run G
    rw [sideAt_fin]
  · rfl

/-- **The lifting lemma for MU-EUF-CMA^corr**: for an oracle `O` that signs as the rejection form
(`SignsOn`) along an injective classifier `π`, every adversary `A` of the game with `O` and `Q`
requests has at most the success probability of its relayed adversary (at most
`t + Q · (qCheck + K · qKeep)` queries) in the standard game with `K · Q` requests. -/
theorem SignsOn.muEufProb_le_relay {hK : 0 < K} (h : C.SignsOn K hK O π e) [Fintype O.SMsg]
    [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins]
    (hπ : Function.Injective π) (i₀ : Fin n) (A : MUAdversary O n V t) (Q : ℕ) :
    muEufProb A Q ≤ muEufProb (C.relayAdversary K n hK i₀ hπ A Q) (K * Q) :=
  C.muEufProb_le_lift hK i₀ Q (C.keepMsg hK π) (C.keepMsg_injective hK hπ) h.keepMsg_base
    (keepSplit e Q) (uniform_keepSplit_symm e Q)
    (fun keys s c' => h.relaysChallenger_keep keys Q s c') A

/-- **The strong-forgery probability of an oracle that signs as the rejection form is at most the
relayed adversary's probability of a verifying signature under an uncorrupted user's key**. Not a
reduction to MU-SUF-CMA^corr: the right-hand side counts the signatures passed on to `A`. -/
theorem SignsOn.muSufProb_le_muVerifyProb_relay {hK : 0 < K} (h : C.SignsOn K hK O π e)
    [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]
    [Nonempty O.Coins] (hπ : Function.Injective π) (i₀ : Fin n) (A : MUAdversary O n V t)
    (Q : ℕ) :
    muSufProb A Q ≤ muVerifyProb (C.relayAdversary K n hK i₀ hπ A Q) (K * Q) :=
  C.muSufProb_le_muVerifyProb_lift hK i₀ Q (C.keepMsg hK π) (C.keepMsg_injective hK hπ)
    h.keepMsg_base (keepSplit e Q) (uniform_keepSplit_symm e Q)
    (fun keys s c' => h.relaysChallenger_keep keys Q s c') A

end Lifting

end CtxRejection

end Ctx

section Ring

variable {N : ℕ} {TB : BaseTypes} (B : BaseSigner X Y N TB)

/-! ### The ring-aware rejection signer as a case -/

namespace Rejection

variable {B} (J : Rejection B) [DecidableEq TB.PK]

/-- **The ring-aware rejection form as a rejection form with a context**: payloads the ring requests
`(R, m)`, admitted when the key is in `R`; the context of `(R, m)` under `pk` is `R`, the first
position of `pk` in `R` and `m`; the base message is `bmsg R m`. The check reads the ring, the keep
decision the ring, the position and the message. -/
@[reducible] def toCtx :
    CtxRejection B.core (KeyRing B.PK N × B.Msg) (KeyRing B.PK N × ℕ × B.Msg) where
  StdCoins := J.StdCoins
  KeepCoins := J.KeepCoins
  qStd := J.qStd
  std := J.std
  std_queries := J.std_queries
  qCheck := J.qCheck
  check c := J.check c.1
  check_queries c := J.check_queries c.1
  qKeep := J.qKeep
  keep c σ u := J.keep c.1 c.2.1 c.2.2 σ u
  keep_queries c σ u := J.keep_queries c.1 c.2.1 c.2.2 σ u
  adm pk p := pk ∈ p.1.1
  admDec _ _ := inferInstance
  ctx pk p := (p.1, p.1.1.idxOf pk, p.2)
  bmsg p := B.bmsg p.1 p.2

variable (K n : ℕ)

set_option smartUnfolding false in
/-- **The ring-aware oracle with keep coins in the request is the context form's.** The two
oracles' fields are separately compiled matches that agree constructor by constructor, and the
elaborator compares them only with smart unfolding off. -/
theorem ringKeep_eq (hK : 0 < K) : SignOracle.ringKeep J K hK = J.toCtx.keepOracle K hK :=
  rfl

variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] {V : OracleView X Y} {t : ℕ} [Fintype J.StdCoins]
  [DecidableEq J.StdCoins] [Nonempty J.StdCoins] [Fintype J.KeepCoins] [DecidableEq J.KeepCoins]
  [Nonempty J.KeepCoins] [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.BMsg]
  [DecidableEq TB.BMsg] [Fintype TB.BSig] [DecidableEq TB.BSig] [Fintype TB.KeyCoins]
  [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins]

omit [Fintype J.StdCoins] [DecidableEq J.StdCoins] [Nonempty J.StdCoins] [Nonempty TB.KeyCoins] in
set_option smartUnfolding false in
/-- **The relayed adversary of the ring-aware game is the context form's** along the payload
classifier `Sum.inl`. The two oracles' fields are separately compiled matches that agree
constructor by constructor, and the elaborator compares them only with smart unfolding off. -/
theorem relayMUAdversary_eq (hK : 0 < K) (i₀ : Fin n) (A : MUAdversary (SignOracle.ring B) n V t)
    (Q : ℕ) :
    relayMUAdversary J K n hK i₀ A Q =
      J.toCtx.relayAdversary K n hK i₀ (π := Sum.inl) Sum.inl_injective A Q :=
  rfl

omit [Fintype J.StdCoins] [DecidableEq J.StdCoins] [Nonempty J.StdCoins] [Nonempty TB.KeyCoins] in
set_option smartUnfolding false in
/-- **The relayed adversary of the key-reuse game is the context form's** along the classifier
`id`. The two oracles' fields are separately compiled matches that agree constructor by
constructor, and the elaborator compares them only with smart unfolding off. -/
theorem relayMUAdversaryStd_eq (hK : 0 < K) (i₀ : Fin n)
    (A : MUAdversary (SignOracle.ringStd B) n V t) (Q : ℕ) :
    relayMUAdversaryStd J K n hK i₀ A Q =
      J.toCtx.relayAdversary K n hK i₀ (π := id) Function.injective_id A Q :=
  rfl

end Rejection

section SignsOn

variable {B : BaseSigner X Y N TB} {J : Rejection B} {K : ℕ} [DecidableEq TB.PK]
  {e : B.Coins ≃ (Fin K → J.StdCoins × J.KeepCoins)}

/-- **The ring-aware oracle signs as the context form** of a rejection form on honest keys. -/
theorem IsRejectionOn.signsOn (h : IsRejectionOn B J K e) (hK : 0 < K) :
    J.toCtx.SignsOn K hK (SignOracle.ring B) Sum.inl e where
  sign_eq H kc p c := by
    change (if (B.keyGen kc).1 ∈ p.1.1 then
        B.bsign (B.keyGen kc).2 p.1 (p.1.1.idxOf (B.keyGen kc).1) p.2 c else .pure none).run H =
      (if (B.keyGen kc).1 ∈ p.1.1 then
        J.rejectSign K (B.keyGen kc).2 p.1 (p.1.1.idxOf (B.keyGen kc).1) p.2 (e c)
      else .pure none).run H
    split_ifs with hm
    · exact h H kc p.1 hm p.2 c
    · rfl
  base_eq _ := rfl

/-- **The key-reuse oracle signs as the context form** of a rejection form on honest keys whose
ordinary signer is the standard signer. -/
theorem IsRejectionOn.signsOn_ringStd (h : IsRejectionOn B J K e) {hK : 0 < K}
    (hstd : IsStdOn B J K e hK) : J.toCtx.SignsOn K hK (SignOracle.ringStd B) id e where
  sign_eq H kc sm c := by
    rcases sm with p | bm
    · exact (h.signsOn hK).sign_eq H kc p c
    · exact hstd H kc bm c
  base_eq sm := by
    rcases sm with p | bm <;> rfl

end SignsOn

section RingLifting

variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] {V : OracleView X Y} {t : ℕ} {B : BaseSigner X Y N TB}
  {J : Rejection B} {K n : ℕ} [Fintype J.StdCoins] [DecidableEq J.StdCoins] [Nonempty J.StdCoins]
  [Fintype J.KeepCoins] [DecidableEq J.KeepCoins] [Nonempty J.KeepCoins] [Fintype TB.PK]
  [DecidableEq TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.BMsg] [DecidableEq TB.BMsg]
  [Fintype TB.BSig] [DecidableEq TB.BSig] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]
  [Nonempty TB.KeyCoins] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins]
  {e : B.Coins ≃ (Fin K → J.StdCoins × J.KeepCoins)}

/-- **The lifting lemma for MU-EUF-CMA^corr** (`GordieHowe/Model/Signature/RejectionRelay.lean`):
under `IsRejectionOn B J K e`, every adversary `A` of the ring-aware game with `Q` requests has at
most the success probability of its relayed adversary (at most `t + Q · (qCheck + K · qKeep)`
queries) in the standard game with `K · Q` requests (`CtxRejection.SignsOn.muEufProb_le_relay` at
`Rejection.toCtx`). -/
theorem muEufProb_le_relay (hK : 0 < K) (hrej : IsRejectionOn B J K e) (i₀ : Fin n)
    (A : MUAdversary (SignOracle.ring B) n V t) (Q : ℕ) :
    muEufProb A Q ≤ muEufProb (relayMUAdversary J K n hK i₀ A Q) (K * Q) := by
  rw [Rejection.relayMUAdversary_eq]
  exact (hrej.signsOn hK).muEufProb_le_relay Sum.inl_injective i₀ A Q

/-- **The strong-forgery probability of the ring-aware game is at most the relayed adversary's
probability of a verifying signature under an uncorrupted user's key**: under
`IsRejectionOn B J K e`, every adversary `A` of the ring-aware game with `Q` requests has
MU-SUF-CMA^corr success probability at most `muVerifyProb` of its relayed adversary in the standard
game with `K · Q` requests. Not a reduction to MU-SUF-CMA^corr: the right-hand side counts the
signatures passed on to `A`. -/
theorem muSufProb_le_muVerifyProb_relay (hK : 0 < K) (hrej : IsRejectionOn B J K e) (i₀ : Fin n)
    (A : MUAdversary (SignOracle.ring B) n V t) (Q : ℕ) :
    muSufProb A Q ≤ muVerifyProb (relayMUAdversary J K n hK i₀ A Q) (K * Q) := by
  rw [Rejection.relayMUAdversary_eq]
  exact (hrej.signsOn hK).muSufProb_le_muVerifyProb_relay Sum.inl_injective i₀ A Q

/-- **The lifting lemma for MU-EUF-CMA^corr with key reuse**: under `IsRejectionOn B J K e` and
`IsStdOn B J K e hK`, every adversary `A` of the key-reuse game (`SignOracle.ringStd`, ring requests
and base messages) with `Q` requests has at most the success probability of its relayed adversary
`relayMUAdversaryStd` (at most `t + Q · (qCheck + K · qKeep)` queries) in the standard game with
`K · Q` requests. -/
theorem muEufProb_le_relay_ringStd (hK : 0 < K) (hrej : IsRejectionOn B J K e)
    (hstd : IsStdOn B J K e hK) (i₀ : Fin n) (A : MUAdversary (SignOracle.ringStd B) n V t)
    (Q : ℕ) : muEufProb A Q ≤ muEufProb (relayMUAdversaryStd J K n hK i₀ A Q) (K * Q) := by
  rw [Rejection.relayMUAdversaryStd_eq]
  exact (hrej.signsOn_ringStd hstd).muEufProb_le_relay Function.injective_id i₀ A Q

/-- **The strong-forgery probability of the key-reuse game is at most the relayed adversary's
probability of a verifying signature under an uncorrupted user's key**: under the hypotheses of
`muEufProb_le_relay_ringStd`, the bound of `muSufProb_le_muVerifyProb_relay` for the key-reuse game
and `relayMUAdversaryStd`. -/
theorem muSufProb_le_muVerifyProb_relay_ringStd (hK : 0 < K) (hrej : IsRejectionOn B J K e)
    (hstd : IsStdOn B J K e hK) (i₀ : Fin n) (A : MUAdversary (SignOracle.ringStd B) n V t)
    (Q : ℕ) :
    muSufProb A Q ≤ muVerifyProb (relayMUAdversaryStd J K n hK i₀ A Q) (K * Q) := by
  rw [Rejection.relayMUAdversaryStd_eq]
  exact (hrej.signsOn_ringStd hstd).muSufProb_le_muVerifyProb_relay Function.injective_id i₀ A Q

end RingLifting

end Ring

end GordieHowe.Signature
