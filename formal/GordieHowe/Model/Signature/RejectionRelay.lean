-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Signature.Rejection
public import GordieHowe.Model.Quantum.Interactive.AbsorbTranscript

@[expose] public section

/-!
# The relay of a ring-aware rejection signer

For a base signer `B` whose ring-aware signer is a rejection signer on honest keys
(`IsRejectionOn B J K e`, `GordieHowe/Model/Signature/Rejection.lean`), every adversary of the
ring-aware multi-user game is turned into an explicit adversary of the standard multi-user game
with `K` times the requests, in two steps. This file defines the objects of the two steps; the
lifting lemmas are proved for rejection forms with a public context
(`GordieHowe/Model/Signature/RejectionCtx.lean`), of which the ring-aware rejection form is the case
`Rejection.toCtx`, with these objects as the context form's at that case.

1. **The keep coins become side coins** (`GordieHowe/Model/Quantum/Interactive/Absorb.lean`). The
   intermediate signing oracle `SignOracle.ringKeep J K hK` takes the keep coins in the request:
   a ring request `((R, m), ks)` with `ks : Fin K → J.KeepCoins` is answered by `rejectSign` with
   the keep coins `ks` and `K` standard coins of the oracle (refused when the key is not in `R`);
   a base message `bm` is answered by the standard signer with the standard coins of attempt `0`.
   At the side coins `s : Fin Q → Fin K → J.KeepCoins`, signing request number `c` for `p` becomes
   the request for `(p, keepAt s c)` (`ringKeepMsg`; `ringStdKeepMsg` for the key-reuse oracle
   `SignOracle.ringStd B`), along the split `keepSplit e Q` of the signing coins into keep coins and
   standard coins (`uniform_keepSplit_symm`). `MURequest.mapMsg`, `msgRelay`,
   `relaysChallenger_msgRelay`, `histRelay_of_msgRelay`: the general relay of messages and its
   history transfer.
2. **The index-blind relay** (`GordieHowe/Model/Quantum/Interactive/MultiRelay.lean`) from
   `ringKeep` to the standard game: `ringRelay J K n hK pks i₀` (the relay programs `ringProg`,
   with the users' public keys `pks`): a public-key request or a corruption is asked as it is; a
   ring request of user `i` for `((R, m), ks)` is refused when `pks i ∉ R`, and otherwise relayed by
   `relaySign`: the public ring check, then the first of `K` standard signatures of user `i` on
   `bmsg R m`, each asked of the standard challenger, that the public keep decision with the keep
   coin `ks j` keeps; a base message is asked as one standard request. `K` main requests (padded
   with the public-key request of user `i₀`) and `qCheck + K · qKeep` queries per request.
   `askResp`, `toSig`, `asksIn_askResp`, `asksIn_firstKept`, `muReply`, `muChallenger_noAssign`,
   `answerAfter_muChallenger`, `attemptCoins`, `attemptCoinsEquiv`, `map_uniformOfFintype_equiv`:
   pieces the context form's relay uses.

The relayed adversary `liftAdversary J K n hK i₀ f A Q` of an adversary `A` with `Q` requests:
its auxiliary input is `A`'s with uniform side coins `s`, its algorithm `A`'s with its requests
absorbed through `msgRelay (f s)` (`QueryBoundedAdversary.absorbSide`), then relayed by
`ringRelay` (`QueryBoundedAdversary.relay`); at most `t + Q · (qCheck + K · qKeep)` queries.
`relayMUAdversary` (`f = ringKeepMsg`) and `relayMUAdversaryStd` (`f = ringStdKeepMsg`).
`muVerifyProb` is the probability that the output is a signature verifying under the key of an
uncorrupted user (`HonestVerifies`; `StrongForges.honestVerifies`, `HonestVerifies.of_histRelay`).

The lifting lemmas, in `GordieHowe/Model/Signature/RejectionCtx.lean`, with `0 < K`:

- `muEufProb_le_relay` (**the lifting lemma for MU-EUF-CMA^corr**), under `IsRejectionOn`:
  `muEufProb (SignOracle.ring B) A Q ≤ muEufProb (relayMUAdversary J K n hK i₀ A Q) (K · Q)`;
- `muSufProb_le_muVerifyProb_relay`: `muSufProb A Q ≤ muVerifyProb A' (K · Q)` for the same `A'`.
  This is not a reduction to MU-SUF-CMA^corr: the event of `muVerifyProb` contains the outputs
  repeating a signature that `A'` passed on to `A`. A reduction would charge only the outputs
  repeating a rejected attempt that `A'` obtained and did not pass on; that form is not proved
  (`GordieHowe/Model/Signature/Rejection.lean`).
- `muEufProb_le_relay_ringStd`, `muSufProb_le_muVerifyProb_relay_ringStd` (**the key-reuse
  form**), under `IsRejectionOn` and `IsStdOn` (the ordinary signer is the standard signer at the
  standard coins of attempt `0`): the same bounds for `SignOracle.ringStd B` and
  `relayMUAdversaryStd`, each ordinary request relayed as one standard request.
-/

namespace GordieHowe.Signature

open GordieHowe.Quantum GordieHowe.RingSignature
open scoped ENNReal

variable {X Y : Type}

section RingKeep

variable {N : ℕ} {TB : BaseTypes}
  {B : BaseSigner X Y N TB} (J : Rejection B) (K n : ℕ)

/-! ### The signing oracle with keep coins in the request -/

/-- **The signing oracle with the keep coins in the request**, for `0 < K`: a ring request
`((R, m), ks)` by the key pair `kp` is answered by `rejectSign J K` at the first position of `kp.1`
in `R`, with attempt `j` on the oracle's standard coins `cs j` and the keep coin `ks j` (refused when
`kp.1 ∉ R`), for the base message `bmsg R m`; a base message `bm` is answered by the standard
signer with the standard coins `cs 0`, for itself. -/
noncomputable def SignOracle.ringKeep [DecidableEq TB.PK] (hK : 0 < K) : SignOracle B.core where
  SMsg := ((KeyRing B.PK N × B.Msg) × (Fin K → J.KeepCoins)) ⊕ B.BMsg
  Coins := Fin K → J.StdCoins
  q := J.qCheck + K * (J.qStd + J.qKeep)
  sign kp
    | .inl p, cs => if kp.1 ∈ p.1.1.1 then
        J.rejectSign K kp.2 p.1.1 (p.1.1.1.idxOf kp.1) p.1.2 (fun j => (cs j, p.2 j))
      else .pure none
    | .inr bm, cs => J.std kp.2 bm (cs ⟨0, hK⟩)
  sign_queries kp sm cs := by
    rcases sm with p | bm
    · dsimp only
      split_ifs
      · exact J.rejectSign_queries _ _ _ _ _ _
      · exact (OracleProg.QueriesLE.pure _ _).mono (Nat.zero_le _)
    · have : J.qStd ≤ K * (J.qStd + J.qKeep) :=
        (Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_left _ hK)
      exact (J.std_queries _ _ _).mono (by omega)
  base
    | .inl p => B.bmsg p.1.1 p.1.2
    | .inr bm => bm

/-! The instances of the oracle's messages and coins: those of
`((KeyRing B.PK N × B.Msg) × (Fin K → J.KeepCoins)) ⊕ B.BMsg` and of `Fin K → J.StdCoins`. -/

section RingKeepInstances

variable (hK : 0 < K)

variable [DecidableEq TB.PK]

instance SignOracle.ringKeep.instFintypeSMsg [Fintype TB.PK] [Fintype TB.Msg] [Fintype TB.BMsg]
    [Fintype J.KeepCoins] : Fintype (SignOracle.ringKeep J K hK).SMsg :=
  inferInstanceAs (Fintype (((KeyRing B.PK N × B.Msg) × (Fin K → J.KeepCoins)) ⊕ B.BMsg))

instance SignOracle.ringKeep.instDecEqSMsg [DecidableEq TB.Msg] [DecidableEq TB.BMsg]
    [DecidableEq J.KeepCoins] :
    DecidableEq (SignOracle.ringKeep J K hK).SMsg :=
  inferInstanceAs (DecidableEq (((KeyRing B.PK N × B.Msg) × (Fin K → J.KeepCoins)) ⊕ B.BMsg))

instance SignOracle.ringKeep.instFintypeCoins [Fintype J.StdCoins] :
    Fintype (SignOracle.ringKeep J K hK).Coins :=
  inferInstanceAs (Fintype (Fin K → J.StdCoins))

instance SignOracle.ringKeep.instDecEqCoins [DecidableEq J.StdCoins] :
    DecidableEq (SignOracle.ringKeep J K hK).Coins :=
  inferInstanceAs (DecidableEq (Fin K → J.StdCoins))

instance SignOracle.ringKeep.instNonemptyCoins [Nonempty J.StdCoins] :
    Nonempty (SignOracle.ringKeep J K hK).Coins :=
  inferInstanceAs (Nonempty (Fin K → J.StdCoins))

end RingKeepInstances

end RingKeep

/-! ### Relaying the messages of a request -/

section MsgRelay

variable {TB : SchemeTypes} {B : BaseScheme X Y TB}

variable {n : ℕ} {O O' : SignOracle B}

/-- **A request with its message mapped by `g`.** -/
def MURequest.mapMsg (g : O.SMsg → O'.SMsg) : MURequest O n → MURequest O' n
  | .publicKey i => .publicKey i
  | .sign i sm => .sign i (g sm)
  | .corrupt i => .corrupt i

/-- Mapping the messages by an injective map is injective. -/
theorem MURequest.mapMsg_injective {g : O.SMsg → O'.SMsg} (hg : Function.Injective g) :
    Function.Injective (MURequest.mapMsg (n := n) g) := by
  rintro (i | ⟨i, sm⟩ | i) (j | ⟨j, sm'⟩ | j) h <;>
    simp only [MURequest.mapMsg, MURequest.publicKey.injEq, MURequest.sign.injEq,
      MURequest.corrupt.injEq, reduceCtorEq] at h ⊢
  · exact h
  · exact ⟨h.1, hg h.2⟩
  · exact h

variable (n) in
/-- **The relay of messages**: request number `c` is sent with its message mapped by `f c`, and the
main reply is passed on. -/
def msgRelay (f : ℕ → O.SMsg → O'.SMsg) :
    SideRelay (MURequest O n) (MUResponse B) (MURequest O' n) (MUResponse B) where
  route c := MURequest.mapMsg (f c)
  answer _ _ a := a

variable [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins] [Fintype O'.Coins]
  [DecidableEq O'.Coins] [Nonempty O'.Coins]

/-- **The challenger of `O` relays the challenger of `O'` by `msgRelay f`** at coins `c` and `c'`
when, for every request number `j < Q`, user and message, the signature of `O` on `sm` with the
coins `c j` runs as the signature of `O'` on `f j sm` with the coins `c' j`. -/
theorem relaysChallenger_msgRelay [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (f : ℕ → O.SMsg → O'.SMsg) (keys : Fin n → B.KeyCoins) (Q : ℕ) (c : Fin Q → O.Coins)
    (c' : Fin Q → O'.Coins)
    (h : ∀ (j : Fin Q) (i : Fin n) (sm : O.SMsg) (G : X → Y),
      (O.sign (B.keyGen (keys i)) sm (c j)).run G =
        (O'.sign (B.keyGen (keys i)) (f j sm) (c' j)).run G) :
    (msgRelay n f).RelaysChallenger (muChallenger O n keys Q) c (muChallenger O' n keys Q) c' where
  Q_eq := rfl
  run_eq hist hist' r G hmap hlt := by
    have hl : hist'.length = hist.length := by
      have := congrArg List.length hmap
      simpa using this
    have hlt' : hist'.length < Q := hl ▸ hlt
    have hj : (⟨hist'.length, hlt'⟩ : Fin Q) = ⟨hist.length, hlt⟩ := Fin.ext hl
    have hlt0 : hist.length < Q := hlt
    simp only [muChallenger]
    rw [dif_pos hlt0, dif_pos hlt']
    rcases r with i | ⟨i, sm⟩ | i
    · rfl
    · simp only [msgRelay, MURequest.mapMsg, OracleProg.run_bind, hj]
      rw [h ⟨hist.length, hlt⟩ i sm G]
    · rfl
  answer_none _ _ _ := rfl

omit [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins] [Fintype O'.Coins]
  [DecidableEq O'.Coins] [Nonempty O'.Coins] in
/-- **The history transfer of a relay of messages**: if `f` keeps the base messages and the
requests of `hist'` are the relayed requests of `hist`, then `hist'` relays `hist`
(`HistRelay`). -/
theorem histRelay_of_msgRelay {f : ℕ → O.SMsg → O'.SMsg}
    (hb : ∀ c sm, O'.base (f c sm) = O.base sm) {hist : MUHist O n} {hist' : MUHist O' n}
    (h : hist'.map HistoryEntry.request =
      (msgRelay n f).relayList (hist.map HistoryEntry.request)) :
    HistRelay hist hist' := by
  have hmem : ∀ e' ∈ hist', ∃ k, ∃ hk : k < hist.length,
      MURequest.mapMsg (f k) hist[k].request = e'.request := by
    intro e' he'
    have hm : e'.request ∈ hist'.map HistoryEntry.request := List.mem_map_of_mem he'
    rw [h, SideRelay.relayList, List.mem_mapIdx] at hm
    obtain ⟨k, hk, hk'⟩ := hm
    refine ⟨k, by simpa using hk, ?_⟩
    rw [← hk']
    simp [msgRelay]
  refine ⟨fun e' he' i sm' hr => ?_, fun i ⟨e', he', hr⟩ => ?_⟩
  · obtain ⟨k, hk, hk'⟩ := hmem e' he'
    rw [hr] at hk'
    rcases hreq : hist[k].request with j | ⟨j, sm⟩ | j <;> rw [hreq] at hk' <;>
      simp only [MURequest.mapMsg] at hk'
    · cases hk'
    · obtain ⟨rfl, rfl⟩ := MURequest.sign.inj hk'
      exact ⟨hist[k], List.getElem_mem hk, sm, hreq, (hb k sm).symm⟩
    · cases hk'
  · obtain ⟨k, hk, hk'⟩ := hmem e' he'
    rw [hr] at hk'
    rcases hreq : hist[k].request with j | ⟨j, sm⟩ | j <;> rw [hreq] at hk' <;>
      simp only [MURequest.mapMsg] at hk'
    · cases hk'
    · cases hk'
    · cases hk'
      exact ⟨hist[k], List.getElem_mem hk, hreq⟩

end MsgRelay

section RingSide

variable {N : ℕ} {TB : BaseTypes}
  {B : BaseSigner X Y N TB} (J : Rejection B) (K n : ℕ)

variable [Fintype J.StdCoins] [DecidableEq J.StdCoins] [Fintype J.KeepCoins]
  [DecidableEq J.KeepCoins]

/-! ### The keep coins as side coins -/

variable [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.BMsg]
  [DecidableEq TB.BMsg] [Nonempty J.StdCoins] [Nonempty J.KeepCoins]

variable [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins]

section Side

variable {J K n}

/-- **The keep coins of request number `c`**: those of `s` for `c < Q`, arbitrary after. -/
noncomputable def keepAt {Q : ℕ} (s : Fin Q → Fin K → J.KeepCoins) (c : ℕ) : Fin K → J.KeepCoins :=
  if h : c < Q then s ⟨c, h⟩ else Classical.arbitrary _

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.BMsg]
  [DecidableEq TB.BMsg] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins]
  [Fintype J.StdCoins] [DecidableEq J.StdCoins] [Fintype J.KeepCoins] [DecidableEq J.KeepCoins]
  [Nonempty J.StdCoins] in
/-- The keep coins of request number `j < Q` are `s j`. -/
theorem keepAt_fin {Q : ℕ} (s : Fin Q → Fin K → J.KeepCoins) (j : Fin Q) : keepAt s j = s j := by
  simp [keepAt, j.2]

/-- **The message map of the ring-aware game at the side coins `s`**: the ring request `p` numbered
`c` becomes `(p, keepAt s c)`. -/
noncomputable def ringKeepMsg (hK : 0 < K) {Q : ℕ} (s : Fin Q → Fin K → J.KeepCoins) (c : ℕ)
    (p : (SignOracle.ring B).SMsg) : (SignOracle.ringKeep J K hK).SMsg :=
  .inl (p, keepAt s c)

/-- **The message map of the key-reuse game at the side coins `s`**: the ring request `p` numbered
`c` becomes `(p, keepAt s c)`, a base message stays. -/
noncomputable def ringStdKeepMsg (hK : 0 < K) {Q : ℕ} (s : Fin Q → Fin K → J.KeepCoins) (c : ℕ) :
    (SignOracle.ringStd B).SMsg → (SignOracle.ringKeep J K hK).SMsg
  | .inl p => .inl (p, keepAt s c)
  | .inr bm => .inr bm

omit [Fintype J.StdCoins] [DecidableEq J.StdCoins] [Fintype J.KeepCoins] [DecidableEq J.KeepCoins]
  [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.BMsg] [DecidableEq TB.BMsg]
  [Nonempty J.StdCoins] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- `ringKeepMsg` is injective at every request number. -/
theorem ringKeepMsg_injective (hK : 0 < K) {Q : ℕ} (s : Fin Q → Fin K → J.KeepCoins) (c : ℕ) :
    Function.Injective (ringKeepMsg hK s c) := fun _ _ h =>
  (Prod.mk.inj (Sum.inl_injective h)).1

omit [Fintype J.StdCoins] [DecidableEq J.StdCoins] [Fintype J.KeepCoins] [DecidableEq J.KeepCoins]
  [Fintype TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.BMsg] [DecidableEq TB.BMsg]
  [Nonempty J.StdCoins] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- `ringStdKeepMsg` is injective at every request number. -/
theorem ringStdKeepMsg_injective (hK : 0 < K) {Q : ℕ} (s : Fin Q → Fin K → J.KeepCoins) (c : ℕ) :
    Function.Injective (ringStdKeepMsg hK s c) := by
  rintro (p | bm) (p' | bm') h
  · exact congrArg Sum.inl (Prod.mk.inj (Sum.inl_injective h)).1
  · exact (Sum.inl_ne_inr h).elim
  · exact (Sum.inr_ne_inl h).elim
  · exact congrArg Sum.inr (Sum.inr_injective h)

/-- **The signing coins split into keep coins and standard coins**: request `j`'s coins `c j` read
through `e` as `K` pairs, the keep coins first. -/
def keepSplit {Co SC KC : Type} (e : Co ≃ (Fin K → SC × KC)) (Q : ℕ) :
    (Fin Q → Co) ≃ (Fin Q → Fin K → KC) × (Fin Q → Fin K → SC) where
  toFun c := (fun j k => (e (c j) k).2, fun j k => (e (c j) k).1)
  invFun p j := e.symm fun k => (p.2 j k, p.1 j k)
  left_inv c := by
    funext j
    simp
  right_inv p := by
    simp

/-- **Uniform signing coins are uniform keep coins and uniform standard coins.** -/
theorem uniform_keepSplit_symm {Co SC KC : Type} [Fintype Co] [Nonempty Co] [Fintype SC]
    [Nonempty SC] [Fintype KC] [Nonempty KC] (e : Co ≃ (Fin K → SC × KC)) (Q : ℕ)
    (s : Fin Q → Fin K → KC) (c' : Fin Q → Fin K → SC) :
    PMF.uniformOfFintype (Fin Q → Co) ((keepSplit e Q).symm (s, c')) =
      PMF.uniformOfFintype _ s * PMF.uniformOfFintype _ c' := by
  simp only [PMF.uniformOfFintype_apply]
  rw [Fintype.card_congr (keepSplit e Q), Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

end Side

/-! ### The relay programs -/

section Programs

variable {Req' Resp' : Type}

/-- **A main request and its reply**: ask `r'`, return the main reply. -/
def askResp (r' : Req') : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') (Option Resp') :=
  .query (.inr r') fun b => .pure (b.elim (fun _ => none) id)

end Programs

end RingSide

section ToSig

variable {TB : SchemeTypes} {B : BaseScheme X Y TB}

/-- The signature of a reply. -/
def toSig : Option (MUResponse B) → Option B.BSig
  | some (.signature σ) => some σ
  | _ => none

end ToSig

section RingRelay

variable {N : ℕ} {TB : BaseTypes}
  {B : BaseSigner X Y N TB} (J : Rejection B) (K n : ℕ)

variable [Fintype J.StdCoins] [DecidableEq J.StdCoins] [Fintype J.KeepCoins]
  [DecidableEq J.KeepCoins]

variable [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.BMsg]
  [DecidableEq TB.BMsg] [Nonempty J.StdCoins] [Nonempty J.KeepCoins]

variable [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins]

section Programs

variable [Zero Y]

/-- **The relayed ring signing**, for the ring `R`, the signer's position `idx`, the message `m`,
the keep coins `ks` and user `i`: the public ring check, then the first of `K` standard signatures
of user `i` on `bmsg R m`, each asked of the main challenger, that the public keep decision with
the keep coin `ks j` of attempt `j` keeps (`Rejection.rejectWith` with main requests as the
attempts). -/
def relaySign (R : KeyRing B.PK N) (idx : ℕ) (m : B.Msg) (ks : Fin K → J.KeepCoins) (i : Fin n) :
    OracleProg (X ⊕ MURequest J.stdOracle n) (Y ⊕ Option (MUResponse B.core)) (Option B.BSig) :=
  (MultiRelay.liftQ (J.check R)).bind fun ok =>
    if ok then firstKept (List.ofFn fun j : Fin K =>
      ((askResp (.sign i (B.bmsg R m))).mapOutput toSig,
        fun σ => MultiRelay.liftQ (J.keep R idx m σ (ks j))))
    else .pure none

omit [Fintype J.StdCoins] [DecidableEq J.StdCoins] [Nonempty J.StdCoins] [Fintype J.KeepCoins]
  [DecidableEq J.KeepCoins] [Nonempty J.KeepCoins] in
/-- **The relay program of a request of the game with keep coins in the request**, with the users'
public keys `pks`: a public-key request or a corruption is asked of the main challenger as it is;
a ring request of user `i` for `((R, m), ks)` is refused when `pks i` is not in `R`, and otherwise
relayed by `relaySign` at the first position of `pks i` in `R`; a base message is asked as it
is. -/
def ringProg (hK : 0 < K) (pks : Fin n → B.PK) :
    MURequest (SignOracle.ringKeep J K hK) n →
      OracleProg (X ⊕ MURequest J.stdOracle n) (Y ⊕ Option (MUResponse B.core))
        (Option (MUResponse B.core))
  | .publicKey i => askResp (.publicKey i)
  | .corrupt i => askResp (.corrupt i)
  | .sign i (.inl p) => if pks i ∈ p.1.1.1 then
      (relaySign J K n p.1.1 (p.1.1.1.idxOf (pks i)) p.1.2 p.2 i).mapOutput (Option.map .signature)
    else .pure none
  | .sign i (.inr bm) => askResp (.sign i bm)

omit [Fintype J.StdCoins] [DecidableEq J.StdCoins] [Nonempty J.StdCoins] [Fintype J.KeepCoins]
  [DecidableEq J.KeepCoins] [Nonempty J.KeepCoins] in
/-- **The relay of the game with keep coins in the request to the standard game**: the programs
`ringProg`, `K` main requests and `qCheck + K · qKeep` queries per request, the idle request the
public key of user `i₀`. -/
def ringRelay (hK : 0 < K) (pks : Fin n → B.PK) (i₀ : Fin n) :
    MultiRelay X Y (MURequest (SignOracle.ringKeep J K hK) n) (MUResponse B.core)
      (MURequest J.stdOracle n) (MUResponse B.core) where
  prog := MultiRelay.plainProg (ringProg J K n hK pks)
  K := K
  K_pos := hK
  qR := J.qCheck + K * J.qKeep
  idle := .publicKey i₀

end Programs

/-! ### The main requests of the relay -/

section Asks

variable {J K n}

/-- **The main request of `askResp r'` is `r'`.** -/
theorem asksIn_askResp {Req' Resp' : Type} (r' : Req') :
    MultiRelay.AsksIn (X := X) (Y := Y) Resp' (askResp r') (· = r') :=
  MultiRelay.AsksIn.query (fun _ h => (Sum.inr.inj h).symm) fun _ => MultiRelay.AsksIn.pure _ _

/-- **The main requests of `firstKept`** satisfy `P` when those of every program and every keep
decision do. -/
theorem asksIn_firstKept {Req' Resp' α : Type} {P : Req' → Prop} :
    ∀ ps : List (OracleProg (X ⊕ Req') (Y ⊕ Option Resp') (Option α) ×
        (α → OracleProg (X ⊕ Req') (Y ⊕ Option Resp') Bool)),
      (∀ pk ∈ ps, MultiRelay.AsksIn Resp' pk.1 P ∧ ∀ σ, MultiRelay.AsksIn Resp' (pk.2 σ) P) →
        MultiRelay.AsksIn Resp' (firstKept ps) P
  | [], _ => MultiRelay.AsksIn.pure _ _
  | pk :: ps, hps => by
    have ih := asksIn_firstKept ps fun q hq => hps q (List.mem_cons_of_mem _ hq)
    obtain ⟨hp, hk⟩ := hps pk List.mem_cons_self
    refine MultiRelay.AsksIn.bind hp fun o => ?_
    rcases o with _ | σ
    · exact ih
    · refine MultiRelay.AsksIn.bind (hk σ) fun b => ?_
      split_ifs
      · exact MultiRelay.AsksIn.pure _ _
      · exact ih

variable [Zero Y]

end Asks

end RingRelay

/-! ### The multi-user challenger -/

section Challenger

variable {TB : SchemeTypes} {B : BaseScheme X Y TB} {n : ℕ}

variable [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y] (O : SignOracle B) (keys : Fin n → B.KeyCoins)

/-- **The reply of the multi-user challenger** with the signing coins `cc` at the oracle `H`: the
user's public key, its signature by the oracle's signer (a refusal passed on), or its key coins. -/
noncomputable def muReply (H : X → Y) (cc : O.Coins) : MURequest O n → Option (MUResponse B)
  | .publicKey i => some (.publicKey (B.pk (keys i)))
  | .sign i sm => ((O.sign (B.keyGen (keys i)) sm cc).run H).map .signature
  | .corrupt i => some (.keyCoins (keys i))

variable [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins]

/-- **The multi-user challenger never reprograms.** -/
theorem muChallenger_noAssign (Q : ℕ) : (muChallenger O n keys Q).NoAssign := by
  intro c hist r G
  simp only [muChallenger]
  split_ifs
  · rcases r with i | ⟨i, sm⟩ | i <;> simp [OracleProg.run_bind]
  · rfl

/-- **The multi-user challenger's reply** to a request numbered below `Q` is `muReply` with the
coins of that request. -/
theorem answerAfter_muChallenger (Q : ℕ) (H : X → Y) (c : Fin Q → O.Coins)
    (rs : List (MURequest O n)) (r : MURequest O n) (hi : rs.length < Q) :
    (muChallenger O n keys Q).toPureEnv.answerAfter (H, c) rs r =
      muReply O keys H (c ⟨rs.length, hi⟩) r := by
  have hn := muChallenger_noAssign O keys Q
  obtain ⟨-, -, h3⟩ := hn.oracleIn H c rs
  rw [hn.answerAfter_eq H c rs r hi]
  have hl : ((muChallenger O n keys Q).toPureEnv.oracleIn (H, c) rs).hist.length = rs.length := by
    rw [h3]
    exact min_eq_left (le_of_lt hi)
  generalize ((muChallenger O n keys Q).toPureEnv.oracleIn (H, c) rs).hist = hist at hl ⊢
  have hi' : hist.length < Q := hl ▸ hi
  have hf : (⟨hist.length, hi'⟩ : Fin Q) = ⟨rs.length, hi⟩ := Fin.ext hl
  simp only [muChallenger]
  rw [dif_pos hi']
  rcases r with i | ⟨i, sm⟩ | i
  · rfl
  · simp only [OracleProg.run_bind, muReply, hf]
    rfl
  · rfl

end Challenger

section RingLift

variable {N : ℕ} {TB : BaseTypes}
  {B : BaseSigner X Y N TB} (J : Rejection B) (K n : ℕ)

variable [Fintype J.StdCoins] [DecidableEq J.StdCoins] [Fintype J.KeepCoins]
  [DecidableEq J.KeepCoins]

variable [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.Msg] [DecidableEq TB.Msg] [Fintype TB.BMsg]
  [DecidableEq TB.BMsg] [Nonempty J.StdCoins] [Nonempty J.KeepCoins]

variable [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins]

/-! ### The coins of the attempts -/

section Coins

variable {J K}

/-- The index `K j + k` of attempt `k < K` of request `j < Q` is below `K · Q`. -/
theorem lt_mul_of_lt {j k Q : ℕ} (hj : j < Q) (hk : k < K) : K * j + k < K * Q := by
  have h1 : K * (j + 1) ≤ K * Q := Nat.mul_le_mul_left K hj
  rw [Nat.mul_succ] at h1
  omega

/-- **The standard coins of the requests from the standard coins of the main requests**: attempt
`k` of request `j` has the coins of main request `K j + k`. -/
def attemptCoins {SC : Type} (Q : ℕ) (c' : Fin (K * Q) → SC) : Fin Q → Fin K → SC :=
  fun j k => c' ⟨K * j + k, lt_mul_of_lt j.2 k.2⟩

/-- `attemptCoins` is a bijection. -/
def attemptCoinsEquiv {SC : Type} (hK : 0 < K) (Q : ℕ) :
    (Fin (K * Q) → SC) ≃ (Fin Q → Fin K → SC) where
  toFun := attemptCoins Q
  invFun c ℓ := c ⟨ℓ / K, Nat.div_lt_of_lt_mul ℓ.2⟩ ⟨ℓ % K, Nat.mod_lt _ hK⟩
  left_inv c' := by
    funext ℓ
    simp only [attemptCoins]
    congr 1
    ext
    exact Nat.div_add_mod ℓ K
  right_inv c := by
    funext j k
    simp only [attemptCoins]
    have h1 : (K * j + k) / K = j := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hK, Nat.div_eq_of_lt k.2, Nat.zero_add]
    have h2 : (K * j + k) % K = k := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt k.2]
    simp only [h1, h2]

/-- **The image of a uniform draw along a bijection is uniform.** -/
theorem map_uniformOfFintype_equiv {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (f : α ≃ β) : (PMF.uniformOfFintype α).map f = PMF.uniformOfFintype β := by
  classical
  ext b
  rw [PMF.map_apply, tsum_fintype, Finset.sum_eq_single (f.symm b) (fun a _ ha => by
    rw [if_neg (fun h => ha (by rw [h, Equiv.symm_apply_apply]))]) (by simp)]
  simp [PMF.uniformOfFintype_apply, Fintype.card_congr f]

end Coins

/-! ### Runs of relay programs -/

section Runs

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddGroup Y] [Nonempty Y]

/-- `RunsWith` along an equality of results. -/
theorem _root_.GordieHowe.Quantum.MultiRelay.RunsWith.congr_res {Req' Resp' R : Type}
    {ansM : List Req' → Req' → Option Resp'} {H : X → Y} {rs : List Req'}
    {p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R} {res res' : R} {asks : List Req'} {q : ℕ}
    (h : MultiRelay.RunsWith ansM H rs p res asks q) (e : res = res') :
    MultiRelay.RunsWith ansM H rs p res' asks q :=
  e ▸ h

end Runs

variable [Fintype TB.BSig] [DecidableEq TB.BSig] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]

/-! ### The lifting lemma -/

variable [Nonempty TB.KeyCoins]

section Lifting

variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] {V : OracleView X Y} {t : ℕ}

omit [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] [Fintype J.StdCoins]
  [DecidableEq J.StdCoins] [Nonempty J.StdCoins] in
/-- **The relayed multi-user adversary** of an adversary `A` of the game with the signing oracle
`O` and `Q` requests, along the message maps `f s` at the side coins `s`: on the public keys
`pks`, the auxiliary input of `A` with uniform side coins `s : Fin Q → Fin K → J.KeepCoins`, the
algorithm of `A` with its requests absorbed through `msgRelay (f s)`
(`QueryBoundedAdversary.absorbSide`, an adversary of the game with keep coins in the request),
then relayed by the programs `ringRelay` at `pks` (`QueryBoundedAdversary.relay`), answering `Q`
requests, with `K` standard requests and `qCheck + K · qKeep` queries per request, the idle request
the public key of user `i₀`. It makes at most `t + Q · (qCheck + K · qKeep)` queries on every
branch. -/
noncomputable def liftAdversary (hK : 0 < K) (i₀ : Fin n) {O : SignOracle B.core} [Fintype O.SMsg]
    [DecidableEq O.SMsg] (Q : ℕ)
    (f : (Fin Q → Fin K → J.KeepCoins) → ℕ → O.SMsg → (SignOracle.ringKeep J K hK).SMsg)
    (hf : ∀ s c, Function.Injective (f s c)) (A : MUAdversary O n V t) :
    MUAdversary J.stdOracle n V (t + Q * (J.qCheck + K * J.qKeep)) := fun inp =>
  letI : Inhabited (MURequest (SignOracle.ringKeep J K hK) n) := ⟨.publicKey i₀⟩
  letI : Inhabited (MURequest J.stdOracle n) := ⟨.publicKey i₀⟩
  ((A inp).absorbSide (PMF.uniformOfFintype (Fin Q → Fin K → J.KeepCoins))
    (fun s => msgRelay n (f s)) fun s c => MURequest.mapMsg_injective (hf s c)).relay
      (ringRelay J K n hK inp.1 i₀) Q

omit [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] [Fintype J.StdCoins]
  [DecidableEq J.StdCoins] [Nonempty J.StdCoins] in
/-- **The relayed multi-user adversary of the ring-aware game** (`liftAdversary` along
`ringKeepMsg`). -/
noncomputable def relayMUAdversary (hK : 0 < K) (i₀ : Fin n)
    (A : MUAdversary (SignOracle.ring B) n V t) (Q : ℕ) :
    MUAdversary J.stdOracle n V (t + Q * (J.qCheck + K * J.qKeep)) :=
  liftAdversary J K n hK i₀ Q (ringKeepMsg hK) (ringKeepMsg_injective hK) A

omit [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] [Fintype J.StdCoins]
  [DecidableEq J.StdCoins] [Nonempty J.StdCoins] in
/-- **The relayed multi-user adversary of the key-reuse game** (`liftAdversary` along
`ringStdKeepMsg`). -/
noncomputable def relayMUAdversaryStd (hK : 0 < K) (i₀ : Fin n)
    (A : MUAdversary (SignOracle.ringStd B) n V t) (Q : ℕ) :
    MUAdversary J.stdOracle n V (t + Q * (J.qCheck + K * J.qKeep)) :=
  liftAdversary J K n hK i₀ Q (ringStdKeepMsg hK) (ringStdKeepMsg_injective hK) A

end Lifting

end RingLift

section Honest

variable {TB : SchemeTypes} {B : BaseScheme X Y TB} {n : ℕ}

variable [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BMsg] [DecidableEq TB.BMsg]

variable [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins]

variable [Fintype TB.BSig] [DecidableEq TB.BSig] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]

variable [Nonempty TB.KeyCoins]

variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] {V : OracleView X Y} {t : ℕ}

/-- **A verifying signature under the key of an uncorrupted user**: `σ` verifies on `bm` under
`pk`, the key of a user not corrupted in `hist`. -/
structure HonestVerifies {O : SignOracle B} (keys : Fin n → B.KeyCoins) (H : X → Y)
    (f : B.PK × B.BMsg × B.BSig) (hist : MUHist O n) : Prop where
  /-- The signature verifies. -/
  verify_eq : B.bverify H f.1 f.2.1 f.2.2 = true
  /-- The key is that of a user not corrupted. -/
  exists_user : ∃ i, B.pk (keys i) = f.1 ∧ ¬ Corrupted hist i

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.BSig]
  [DecidableEq TB.BSig] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Fintype TB.Coins]
  [DecidableEq TB.Coins] [Nonempty TB.Coins] [Nonempty TB.KeyCoins] in
/-- A strong forgery is a verifying signature under the key of an uncorrupted user. -/
theorem StrongForges.honestVerifies {O : SignOracle B} {keys : Fin n → B.KeyCoins} {H : X → Y}
    {f : B.PK × B.BMsg × B.BSig} {hist : MUHist O n} (h : StrongForges keys H f hist) :
    HonestVerifies keys H f hist :=
  let ⟨i, hi, hc, _⟩ := h.exists_user
  ⟨h.verify_eq, i, hi, hc⟩

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.BSig]
  [DecidableEq TB.BSig] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Fintype TB.Coins]
  [DecidableEq TB.Coins] [Nonempty TB.Coins] [Nonempty TB.KeyCoins] in
/-- `HonestVerifies` for a history holds for every relay of it. -/
theorem HonestVerifies.of_histRelay {O O' : SignOracle B} {keys : Fin n → B.KeyCoins} {H : X → Y}
    {f : B.PK × B.BMsg × B.BSig} {hist : MUHist O n} {hist' : MUHist O' n}
    (h : HonestVerifies keys H f hist) (hr : HistRelay hist hist') :
    HonestVerifies keys H f hist' :=
  let ⟨i, hi, hc⟩ := h.exists_user
  ⟨h.verify_eq, i, hi, fun h' => hc (hr.corrupt_mem i h')⟩

/-- **The probability that the adversary's output is a verifying signature under the key of an
uncorrupted user**, with `Q` requests (`HonestVerifies`). Every strong forgery and every forgery is
such an output, and so is every signature the oracle returned to an uncorrupted user. -/
noncomputable def muVerifyProb {O : SignOracle B} [Fintype O.SMsg] [DecidableEq O.SMsg]
    [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins] (A : MUAdversary O n V t) (Q : ℕ) :
    ℝ≥0∞ :=
  (muLaw A Q).toOuterMeasure {x | ∃ p ∈ x.2.2, HonestVerifies x.1 x.2.1 p.1 p.2}

end Honest

end GordieHowe.Signature
