-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Signature.Rejection
public import GordieHowe.Model.Quantum.Interactive.AbsorbTranscript

@[expose] public section

/-!
# The lifting lemma for rejection signers

For a base signer `B` whose ring-aware signer is a rejection signer on honest keys
(`IsRejectionOn B J K e`, `GordieHowe/Model/Signature/Rejection.lean`), every adversary of the
ring-aware multi-user game is turned into an explicit adversary of the standard multi-user game
with `K` times the requests, in two steps.

1. **The keep coins become side coins** (`GordieHowe/Model/Quantum/Interactive/Absorb.lean`). The
   intermediate signing oracle `SignOracle.ringKeep J K hK` takes the keep coins in the request:
   a ring request `((R, m), ks)` with `ks : Fin K → J.KeepCoins` is answered by `rejectSign` with
   the keep coins `ks` and `K` standard coins of the oracle (refused when the key is not in `R`);
   a base message `bm` is answered by the standard signer with the standard coins of attempt `0`.
   At the side coins `s : Fin Q → Fin K → J.KeepCoins`, the ring-aware challenger relays the
   challenger of `ringKeep` by `msgRelay (ringKeepMsg s)`: signing request number `c` for `p`
   becomes the request for `(p, s c)` (`relaysChallenger_ringKeep`, under `IsRejectionOn`, along the
   split `keepSplit e Q` of the signing coins into keep coins and standard coins,
   `uniform_keepSplit_symm`). The same for the key-reuse oracle `SignOracle.ringStd B`
   (`ringStdKeepMsg`, `relaysChallenger_ringStdKeep`, under `IsRejectionOn` and `IsStdOn`).
   `MURequest.mapMsg`, `msgRelay`, `keepAt`, `relaysChallenger_msgRelay`,
   `histRelay_of_msgRelay`: the general relay of messages and its history transfer.
2. **The index-blind relay** (`GordieHowe/Model/Quantum/Interactive/MultiRelay.lean`) from
   `ringKeep` to the standard game: `ringRelay J K n hK pks i₀` (the relay programs, with the users'
   public keys `pks`): a public-key request or a corruption is asked as it is; a ring request of
   user `i` for `((R, m), ks)` is refused when `pks i ∉ R`, and otherwise relayed by `relaySign`:
   the public ring check, then the first of `K` standard signatures of user `i` on `bmsg R m`, each
   asked of the standard challenger, that the public keep decision with the keep coin `ks j` keeps
   (`Rejection.rejectWith` with main requests as the attempts); a base message is asked as one
   standard request. `K` main requests (padded with the public-key request of user `i₀`) and
   `qCheck + K · qKeep` queries per request. `askResp`, `toSig`, `ringProg`: its pieces.
   `RingAsk`, `asksIn_askResp`, `asksIn_firstKept`, `asksIn_relaySign`, `asksIn_ringProg`,
   `histRelay_of_relays`: every main request of the relay program of a request is the same
   public-key request or corruption, or a signing request of the same user for its base message.
   `relaysChallenger_ringRelay`: the challenger of `ringKeep` with `Q` requests is the relay of the
   standard challenger with `K · Q` requests, along the attempts' coins (`attemptCoins`,
   `attemptCoinsEquiv`), through `muReply`, `muChallenger_noAssign`, `answerAfter_muChallenger`,
   `map_uniformOfFintype_equiv`, `runsWith_attempt`, `runsWith_firstKept`, `runsWith_relaySign`,
   `runsWith_ringProg`.

The relayed adversary `liftAdversary J K n hK i₀ f A Q` of an adversary `A` with `Q` requests:
its auxiliary input is `A`'s with uniform side coins `s`, its algorithm `A`'s with its requests
absorbed through `msgRelay (f s)` (`QueryBoundedAdversary.absorbSide`), then relayed by
`ringRelay` (`QueryBoundedAdversary.relay`); at most `t + Q · (qCheck + K · qKeep)` queries.
`relayMUAdversary` (`f = ringKeepMsg`) and `relayMUAdversaryStd` (`f = ringStdKeepMsg`).
`muEufProb_le_lift`, `muSufProb_le_muVerifyProb_lift`: the two steps for a general message relay.
With `0 < K`:

- `muEufProb_le_relay` (**the lifting lemma for MU-EUF-CMA^corr**), under `IsRejectionOn`:
  `muEufProb (SignOracle.ring B) A Q ≤ muEufProb (relayMUAdversary J K n hK i₀ A Q) (K · Q)`;
- `muSufProb_le_muVerifyProb_relay`: `muSufProb A Q ≤ muVerifyProb A' (K · Q)` for the same `A'`,
  with `muVerifyProb` the probability that the output is a signature verifying under the key of an
  uncorrupted user (`HonestVerifies`; `StrongForges.honestVerifies`,
  `HonestVerifies.of_histRelay`). This is not a reduction to MU-SUF-CMA^corr: the event of
  `muVerifyProb` contains the outputs repeating a signature that `A'` passed on to `A`. A reduction
  would charge only the outputs repeating a rejected attempt that `A'` obtained and did not pass on;
  that form is not proved (`GordieHowe/Model/Signature/Rejection.lean`).
- `muEufProb_le_relay_ringStd`, `muSufProb_le_muVerifyProb_relay_ringStd` (**the key-reuse
  form**), under
  `IsRejectionOn` and `IsStdOn` (the ordinary signer is the standard signer at the standard coins
  of attempt `0`): the same bounds for `SignOracle.ringStd B` and `relayMUAdversaryStd`, each
  ordinary request relayed as one standard request.
-/

namespace GordieHowe.Signature

open GordieHowe.Quantum GordieHowe.RingSignature
open scoped ENNReal

variable {X Y : Type} {N : ℕ} {TB : BaseTypes} {B : BaseSigner X Y N TB} (J : Rejection B) (K n : ℕ)

/-! ### The signing oracle with keep coins in the request -/

/-- **The signing oracle with the keep coins in the request**, for `0 < K`: a ring request
`((R, m), ks)` by the key pair `kp` is answered by `rejectSign J K` at the first position of `kp.1`
in `R`, with attempt `j` on the oracle's standard coins `cs j` and the keep coin `ks j` (refused when
`kp.1 ∉ R`), for the base message `bmsg R m`; a base message `bm` is answered by the standard
signer with the standard coins `cs 0`, for itself. -/
noncomputable def SignOracle.ringKeep (hK : 0 < K) : SignOracle B where
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

/-! ### Relaying the messages of a request -/

section MsgRelay

variable {n} {O O' : SignOracle B}

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

/-! ### The keep coins as side coins -/

section Side

variable {J K n}

/-- **The keep coins of request number `c`**: those of `s` for `c < Q`, arbitrary after. -/
noncomputable def keepAt {Q : ℕ} (s : Fin Q → Fin K → J.KeepCoins) (c : ℕ) : Fin K → J.KeepCoins :=
  if h : c < Q then s ⟨c, h⟩ else Classical.arbitrary _

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

/-- `ringKeepMsg` is injective at every request number. -/
theorem ringKeepMsg_injective (hK : 0 < K) {Q : ℕ} (s : Fin Q → Fin K → J.KeepCoins) (c : ℕ) :
    Function.Injective (ringKeepMsg hK s c) := fun _ _ h =>
  (Prod.mk.inj (Sum.inl_injective h)).1

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
def keepSplit (e : B.Coins ≃ (Fin K → J.StdCoins × J.KeepCoins)) (Q : ℕ) :
    (Fin Q → B.Coins) ≃ (Fin Q → Fin K → J.KeepCoins) × (Fin Q → Fin K → J.StdCoins) where
  toFun c := (fun j k => (e (c j) k).2, fun j k => (e (c j) k).1)
  invFun p j := e.symm fun k => (p.2 j k, p.1 j k)
  left_inv c := by
    funext j
    simp
  right_inv p := by
    simp

/-- **Uniform signing coins are uniform keep coins and uniform standard coins.** -/
theorem uniform_keepSplit_symm (e : B.Coins ≃ (Fin K → J.StdCoins × J.KeepCoins)) (Q : ℕ)
    (s : Fin Q → Fin K → J.KeepCoins) (c' : Fin Q → Fin K → J.StdCoins) :
    PMF.uniformOfFintype (Fin Q → B.Coins) ((keepSplit e Q).symm (s, c')) =
      PMF.uniformOfFintype _ s * PMF.uniformOfFintype _ c' := by
  simp only [PMF.uniformOfFintype_apply]
  rw [Fintype.card_congr (keepSplit e Q), Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

/-- **The ring-aware challenger relays the challenger with keep coins in the request**, at the side
coins `s` and the standard coins `c'`, under `IsRejectionOn`: signing request number `c` for `p`
is answered as the request for `(p, keepAt s c)`. -/
theorem relaysChallenger_ringKeep (hK : 0 < K) {e : B.Coins ≃ (Fin K → J.StdCoins × J.KeepCoins)}
    (hrej : IsRejectionOn B J K e) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (s : Fin Q → Fin K → J.KeepCoins) (c' : Fin Q → Fin K → J.StdCoins) :
    (msgRelay n (ringKeepMsg hK s)).RelaysChallenger (muChallenger (SignOracle.ring B) n keys Q)
      ((keepSplit e Q).symm (s, c')) (muChallenger (SignOracle.ringKeep J K hK) n keys Q) c' := by
  refine relaysChallenger_msgRelay (O := SignOracle.ring B) (O' := SignOracle.ringKeep J K hK) _
    keys Q _ c' fun j i p G => ?_
  change (if (B.keyGen (keys i)).1 ∈ p.1.1 then
      B.bsign (B.keyGen (keys i)).2 p.1 (p.1.1.idxOf (B.keyGen (keys i)).1) p.2
        (e.symm fun k => (c' j k, s j k)) else .pure none).run G =
    (if (B.keyGen (keys i)).1 ∈ p.1.1 then
      J.rejectSign K (B.keyGen (keys i)).2 p.1 (p.1.1.idxOf (B.keyGen (keys i)).1) p.2
        (fun k => (c' j k, keepAt s j k)) else .pure none).run G
  rw [keepAt_fin]
  split_ifs with hm
  · have h := hrej G (keys i) _ hm (show KeyRing B.PK N × B.Msg from p).2 (e.symm fun k => (c' j k, s j k))
    rw [Equiv.apply_symm_apply] at h
    exact h
  · rfl

/-- **The key-reuse challenger relays the challenger with keep coins in the request**, under
`IsRejectionOn` and `IsStdOn`: a ring request as in `relaysChallenger_ringKeep`, a base message as
it is. -/
theorem relaysChallenger_ringStdKeep (hK : 0 < K) {e : B.Coins ≃ (Fin K → J.StdCoins × J.KeepCoins)}
    (hrej : IsRejectionOn B J K e) (hstd : IsStdOn B J K e hK) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (s : Fin Q → Fin K → J.KeepCoins) (c' : Fin Q → Fin K → J.StdCoins) :
    (msgRelay n (ringStdKeepMsg hK s)).RelaysChallenger
      (muChallenger (SignOracle.ringStd B) n keys Q) ((keepSplit e Q).symm (s, c'))
      (muChallenger (SignOracle.ringKeep J K hK) n keys Q) c' := by
  refine relaysChallenger_msgRelay (O := SignOracle.ringStd B) (O' := SignOracle.ringKeep J K hK)
    _ keys Q _ c' fun j i sm G => ?_
  rcases sm with p | bm
  · change (if (B.keyGen (keys i)).1 ∈ p.1.1 then
        B.bsign (B.keyGen (keys i)).2 p.1 (p.1.1.idxOf (B.keyGen (keys i)).1) p.2
          (e.symm fun k => (c' j k, s j k)) else .pure none).run G =
      (if (B.keyGen (keys i)).1 ∈ p.1.1 then
        J.rejectSign K (B.keyGen (keys i)).2 p.1 (p.1.1.idxOf (B.keyGen (keys i)).1) p.2
          (fun k => (c' j k, keepAt s j k)) else .pure none).run G
    rw [keepAt_fin]
    split_ifs with hm
    · have h := hrej G (keys i) _ hm (show KeyRing B.PK N × B.Msg from p).2 (e.symm fun k => (c' j k, s j k))
      rw [Equiv.apply_symm_apply] at h
      exact h
    · rfl
  · change (B.ssign (B.keyGen (keys i)).2 bm (e.symm fun k => (c' j k, s j k))).run G =
      (J.std (B.keyGen (keys i)).2 bm (c' j ⟨0, hK⟩)).run G
    have h := hstd G (keys i) bm (e.symm fun k => (c' j k, s j k))
    rw [Equiv.apply_symm_apply] at h
    exact h

end Side

/-! ### The relay programs -/

section Programs

variable {Req' Resp' : Type}

/-- **A main request and its reply**: ask `r'`, return the main reply. -/
def askResp (r' : Req') : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') (Option Resp') :=
  .query (.inr r') fun b => .pure (b.elim (fun _ => none) id)

/-- The signature of a reply. -/
def toSig : Option (MUResponse B) → Option B.BSig
  | some (.signature σ) => some σ
  | _ => none

variable [Zero Y]

/-- **The relayed ring signing**, for the ring `R`, the signer's position `idx`, the message `m`,
the keep coins `ks` and user `i`: the public ring check, then the first of `K` standard signatures
of user `i` on `bmsg R m`, each asked of the main challenger, that the public keep decision with
the keep coin `ks j` of attempt `j` keeps (`Rejection.rejectWith` with main requests as the
attempts). -/
def relaySign (R : KeyRing B.PK N) (idx : ℕ) (m : B.Msg) (ks : Fin K → J.KeepCoins) (i : Fin n) :
    OracleProg (X ⊕ MURequest J.stdOracle n) (Y ⊕ Option (MUResponse B)) (Option B.BSig) :=
  (MultiRelay.liftQ (J.check R)).bind fun ok =>
    if ok then firstKept (List.ofFn fun j : Fin K =>
      ((askResp (.sign i (B.bmsg R m))).mapOutput toSig,
        fun σ => MultiRelay.liftQ (J.keep R idx m σ (ks j))))
    else .pure none

/-- **The relay program of a request of the game with keep coins in the request**, with the users'
public keys `pks`: a public-key request or a corruption is asked of the main challenger as it is;
a ring request of user `i` for `((R, m), ks)` is refused when `pks i` is not in `R`, and otherwise
relayed by `relaySign` at the first position of `pks i` in `R`; a base message is asked as it
is. -/
def ringProg (hK : 0 < K) (pks : Fin n → B.PK) :
    MURequest (SignOracle.ringKeep J K hK) n →
      OracleProg (X ⊕ MURequest J.stdOracle n) (Y ⊕ Option (MUResponse B)) (Option (MUResponse B))
  | .publicKey i => askResp (.publicKey i)
  | .corrupt i => askResp (.corrupt i)
  | .sign i (.inl p) => if pks i ∈ p.1.1.1 then
      (relaySign J K n p.1.1 (p.1.1.1.idxOf (pks i)) p.1.2 p.2 i).mapOutput (Option.map .signature)
    else .pure none
  | .sign i (.inr bm) => askResp (.sign i bm)

/-- **The relay of the game with keep coins in the request to the standard game**: the programs
`ringProg`, `K` main requests and `qCheck + K · qKeep` queries per request, the idle request the
public key of user `i₀`. -/
def ringRelay (hK : 0 < K) (pks : Fin n → B.PK) (i₀ : Fin n) :
    MultiRelay X Y (MURequest (SignOracle.ringKeep J K hK) n) (MUResponse B)
      (MURequest J.stdOracle n) (MUResponse B) where
  prog := MultiRelay.plainProg (ringProg J K n hK pks)
  K := K
  K_pos := hK
  qR := J.qCheck + K * J.qKeep
  idle := .publicKey i₀

end Programs

/-! ### The main requests of the relay -/

section Asks

variable {J K n}

/-- **The main request a request relays to**: the same public-key request or corruption, or a
signing request of the same user for its base message. -/
def RingAsk {hK : 0 < K} : MURequest (SignOracle.ringKeep J K hK) n → MURequest J.stdOracle n → Prop
  | .publicKey i, r' => r' = .publicKey i
  | .corrupt i, r' => r' = .corrupt i
  | .sign i sm, r' => r' = .sign i ((SignOracle.ringKeep J K hK).base sm)

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

/-- **Every main request of the relayed ring signing** is the signing request of user `i` for
`bmsg R m`. -/
theorem asksIn_relaySign (R : KeyRing B.PK N) (idx : ℕ) (m : B.Msg) (ks : Fin K → J.KeepCoins)
    (i : Fin n) :
    MultiRelay.AsksIn (MUResponse B) (relaySign J K n R idx m ks i)
      (· = .sign i (B.bmsg R m)) := by
  refine MultiRelay.AsksIn.bind (MultiRelay.AsksIn.liftQ _ _) fun ok => ?_
  split_ifs
  · refine asksIn_firstKept _ fun q hq => ?_
    obtain ⟨_, rfl⟩ := List.mem_ofFn.1 hq
    exact ⟨(asksIn_askResp _).mapOutput _, fun σ => MultiRelay.AsksIn.liftQ _ _⟩
  · exact MultiRelay.AsksIn.pure _ _

/-- **Every main request of the relay program of `r` is one `r` relays to.** -/
theorem asksIn_ringProg (hK : 0 < K) (pks : Fin n → B.PK)
    (r : MURequest (SignOracle.ringKeep J K hK) n) :
    MultiRelay.AsksIn (MUResponse B) (ringProg J K n hK pks r) (RingAsk r) := by
  rcases r with i | ⟨i, p | bm⟩ | i
  · exact asksIn_askResp _
  · simp only [ringProg]
    split_ifs
    · exact (asksIn_relaySign _ _ _ _ _).mapOutput _
    · exact MultiRelay.AsksIn.pure _ _
  · exact asksIn_askResp _
  · exact asksIn_askResp _

/-- **The relay's histories relay the game's** (`HistRelay`): if every request of the standard
history `hist'` is the idle request (a public key) or one that a request of the history `hist`
relays to, every signing request of `hist'` is for the base message of a signing request of the
same user in `hist`, and every corruption of `hist'` is one of `hist`. -/
theorem histRelay_of_relays (hK : 0 < K) (pks : Fin n → B.PK) (i₀ : Fin n)
    {hist : MUHist (SignOracle.ringKeep J K hK) n} {hist' : MUHist J.stdOracle n}
    (h : ∀ e' ∈ hist', e'.request = (ringRelay J K n hK pks i₀).idle ∨
      ∃ e ∈ hist, (ringRelay J K n hK pks i₀).CanAsk e.request e'.request) :
    HistRelay hist hist' where
  sign_mem e' he' i sm' hr := by
    rcases h e' he' with h1 | ⟨e, he, hc⟩
    · rw [hr] at h1
      cases h1
    · have := (ringRelay J K n hK pks i₀).canAsk_of_asksIn
        (asksIn_ringProg (J := J) (K := K) hK pks e.request).plainProg hc
      rw [hr] at this
      rcases hreq : e.request with j | ⟨j, sm⟩ | j <;> rw [hreq] at this <;>
        simp only [RingAsk] at this
      · cases this
      · obtain ⟨rfl, rfl⟩ := MURequest.sign.inj this
        exact ⟨e, he, sm, hreq, rfl⟩
      · cases this
  corrupt_mem i := by
    rintro ⟨e', he', hr⟩
    rcases h e' he' with h1 | ⟨e, he, hc⟩
    · rw [hr] at h1
      cases h1
    · have := (ringRelay J K n hK pks i₀).canAsk_of_asksIn
        (asksIn_ringProg (J := J) (K := K) hK pks e.request).plainProg hc
      rw [hr] at this
      rcases hreq : e.request with j | ⟨j, sm⟩ | j <;> rw [hreq] at this <;>
        simp only [RingAsk] at this
      · cases this
      · cases this
      · cases this
        exact ⟨e, he, hreq⟩

end Asks

/-! ### The multi-user challenger -/

section Challenger

variable [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y] {n} (O : SignOracle B) (keys : Fin n → B.KeyCoins)

/-- **The reply of the multi-user challenger** with the signing coins `cc` at the oracle `H`: the
user's public key, its signature by the oracle's signer (a refusal passed on), or its key coins. -/
noncomputable def muReply (H : X → Y) (cc : O.Coins) : MURequest O n → Option (MUResponse B)
  | .publicKey i => some (.publicKey (B.pk (keys i)))
  | .sign i sm => ((O.sign (B.keyGen (keys i)) sm cc).run H).map .signature
  | .corrupt i => some (.keyCoins (keys i))

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
def attemptCoins (Q : ℕ) (c' : Fin (K * Q) → J.StdCoins) : Fin Q → Fin K → J.StdCoins :=
  fun j k => c' ⟨K * j + k, lt_mul_of_lt j.2 k.2⟩

/-- `attemptCoins` is a bijection. -/
def attemptCoinsEquiv (hK : 0 < K) (Q : ℕ) :
    (Fin (K * Q) → J.StdCoins) ≃ (Fin Q → Fin K → J.StdCoins) where
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

/-! ### The relayed requests against the standard challenger -/

section Runs

variable [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y] {J K n} (keys : Fin n → B.KeyCoins) (Q : ℕ) (H : X → Y)
  (c' : Fin (K * Q) → J.StdCoins)

omit [Nonempty X] in
/-- `RunsWith` along an equality of results. -/
theorem _root_.GordieHowe.Quantum.MultiRelay.RunsWith.congr_res {Req' Resp' R : Type}
    {ansM : List Req' → Req' → Option Resp'} {H : X → Y} {rs : List Req'}
    {p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R} {res res' : R} {asks : List Req'} {q : ℕ}
    (h : MultiRelay.RunsWith ansM H rs p res asks q) (e : res = res') :
    MultiRelay.RunsWith ansM H rs p res' asks q :=
  e ▸ h

/-- The standard challenger's replies. -/
noncomputable abbrev stdAns : List (MURequest J.stdOracle n) → MURequest J.stdOracle n →
    Option (MUResponse B) :=
  (muChallenger J.stdOracle n keys (K * Q)).toPureEnv.answerAfter (H, c')

/-- **One attempt**: a standard signature of user `i` on `bm`, asked of the standard challenger
as main request number `|L|`. -/
theorem runsWith_attempt (L : List (MURequest J.stdOracle n)) (hL : L.length < K * Q) (i : Fin n)
    (bm : B.BMsg) :
    MultiRelay.RunsWith (stdAns keys Q H c') H L
      ((askResp (Resp' := MUResponse B) (.sign i bm)).mapOutput toSig)
      ((J.std (B.keyGen (keys i)).2 bm (c' ⟨L.length, hL⟩)).run H) [.sign i bm] 0 := by
  have h := (MultiRelay.RunsWith.query_inr (ansM := stdAns keys Q H c') (H := H) (rs := L)
    (k := fun b => OracleProg.pure (b.elim (fun _ => none) id)) (.sign i bm)
    (MultiRelay.RunsWith.pure _ _)).mapOutput toSig
  refine h.congr_res ?_
  simp only [Sum.elim_inr, id]
  have ha := answerAfter_muChallenger J.stdOracle keys (K * Q) H c' L (.sign i bm) hL
  refine (congrArg toSig ha).trans ?_
  change toSig (Option.map MUResponse.signature ((J.std (B.keyGen (keys i)).2 bm _).run H)) = _
  rcases (J.std (B.keyGen (keys i)).2 bm (c' ⟨L.length, hL⟩)).run H with _ | σ <;> rfl

/-- **The attempts**: the first kept of `m` standard signatures of user `i` on `bmsg R msg`, asked
as main requests number `|L|, …, |L| + m - 1` and kept by the keep decisions with the keep coins
`ks`, runs with the first kept attempt of their coins, at most `m` main requests and at most
`m · qKeep` queries. -/
theorem runsWith_firstKept (i : Fin n) (R : KeyRing B.PK N) (idx : ℕ) (msg : B.Msg) :
    ∀ (m : ℕ) (ks : Fin m → J.KeepCoins) (L : List (MURequest J.stdOracle n))
      (hL : L.length + m ≤ K * Q),
      ∃ asks q, MultiRelay.RunsWith (stdAns keys Q H c') H L
        (firstKept (List.ofFn fun t : Fin m =>
          ((askResp (Resp' := MUResponse B) (.sign i (B.bmsg R msg))).mapOutput toSig,
            fun σ => MultiRelay.liftQ (Req' := MURequest J.stdOracle n) (Resp' := MUResponse B)
              (J.keep R idx msg σ (ks t)))))
        ((List.ofFn fun t : Fin m => (c' ⟨L.length + t, by omega⟩, ks t)).findSome?
          (J.att H (B.keyGen (keys i)).2 R idx msg)) asks q ∧ asks.length ≤ m ∧ q ≤ m * J.qKeep
  | 0, _, L, _ => ⟨[], 0, MultiRelay.RunsWith.pure _ _, le_rfl, Nat.zero_le _⟩
  | m + 1, ks, L, hL => by
    have hA := runsWith_attempt keys Q H c' L (by omega) i (B.bmsg R msg)
    obtain ⟨asks₂, q₂, h₂, ha₂, hq₂⟩ := runsWith_firstKept i R idx msg m (fun t => ks t.succ)
      (L ++ [.sign i (B.bmsg R msg)]) (by simp; omega)
    have hrest : (List.ofFn fun t : Fin m =>
        (c' ⟨(L ++ [MURequest.sign i (B.bmsg R msg)]).length + t, by simp; omega⟩, ks t.succ)) =
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
    rcases hx : (J.std (B.keyGen (keys i)).2 (B.bmsg R msg) (c' ⟨L.length, by omega⟩)).run H
      with _ | σ
    · have hatt : J.att H (B.keyGen (keys i)).2 R idx msg (c' ⟨L.length, by omega⟩, ks 0) =
          none := by
        simp only [Rejection.att, hx]
      rw [hatt]
      dsimp only
      refine ⟨[.sign i (B.bmsg R msg)] ++ asks₂, 0 + q₂, MultiRelay.RunsWith.bind hA ?_, ?_, ?_⟩
      · rw [hx]
        exact h₂
      · simp only [List.singleton_append, List.length_cons]
        omega
      · rw [Nat.zero_add, Nat.succ_mul]
        omega
    · have hk := MultiRelay.RunsWith.liftQ (ansM := stdAns keys Q H c') (H := H)
        (Resp' := MUResponse B) (L ++ [.sign i (B.bmsg R msg)]) (J.keep R idx msg σ (ks 0))
      have hkq := J.keep_queries R idx msg σ (ks 0) H
      rcases hb : (J.keep R idx msg σ (ks 0)).run H
      · have hatt : J.att H (B.keyGen (keys i)).2 R idx msg (c' ⟨L.length, by omega⟩, ks 0) =
            none := by
          simp only [Rejection.att, hx, hb, Bool.false_eq_true, if_false]
        rw [hatt]
        dsimp only
        refine ⟨[.sign i (B.bmsg R msg)] ++ ([] ++ asks₂),
          0 + ((J.keep R idx msg σ (ks 0)).trace H).length + q₂, ?_, ?_, ?_⟩
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
      · have hatt : J.att H (B.keyGen (keys i)).2 R idx msg (c' ⟨L.length, by omega⟩, ks 0) =
            some σ := by
          simp only [Rejection.att, hx, hb, if_true]
        rw [hatt]
        dsimp only
        refine ⟨[.sign i (B.bmsg R msg)] ++ ([] ++ []),
          0 + (((J.keep R idx msg σ (ks 0)).trace H).length + 0), ?_, ?_, ?_⟩
        · refine MultiRelay.RunsWith.bind hA ?_
          rw [hx]
          refine MultiRelay.RunsWith.bind hk ?_
          rw [hb]
          exact MultiRelay.RunsWith.pure _ _
        · simp
        · rw [Nat.zero_add, Nat.add_zero, Nat.succ_mul]
          omega

/-- **The relayed ring signing** runs with the rejection step on the attempts' coins: the check,
then the first kept of the `K` attempts asked as main requests number `|L|, …, |L| + K - 1`, with
the keep coins `ks`. -/
theorem runsWith_relaySign (i : Fin n) (R : KeyRing B.PK N) (idx : ℕ) (msg : B.Msg)
    (ks : Fin K → J.KeepCoins) (L : List (MURequest J.stdOracle n)) (hL : L.length + K ≤ K * Q) :
    ∃ asks q, MultiRelay.RunsWith (stdAns keys Q H c') H L (relaySign J K n R idx msg ks i)
      (if (J.check R).run H then
        (List.ofFn fun t : Fin K => (c' ⟨L.length + t, by omega⟩, ks t)).findSome?
          (J.att H (B.keyGen (keys i)).2 R idx msg) else none) asks q ∧
      asks.length ≤ K ∧ q ≤ J.qCheck + K * J.qKeep := by
  have hc := MultiRelay.RunsWith.liftQ (ansM := stdAns keys Q H c') (H := H)
    (Resp' := MUResponse B) L (J.check R)
  have hcq := J.check_queries R H
  rcases hok : (J.check R).run H
  · refine ⟨[] ++ [], ((J.check R).trace H).length + 0, MultiRelay.RunsWith.bind hc ?_, ?_, ?_⟩
    · rw [hok]
      exact MultiRelay.RunsWith.pure _ _
    · simp
    · omega
  · obtain ⟨asks₂, q₂, h₂, ha₂, hq₂⟩ := runsWith_firstKept keys Q H c' i R idx msg K ks (L ++ [])
      (by simpa using hL)
    refine ⟨[] ++ asks₂, ((J.check R).trace H).length + q₂, MultiRelay.RunsWith.bind hc ?_, ?_, ?_⟩
    · rw [hok]
      simp only [if_true]
      refine h₂.congr_res ?_
      simp only [List.append_nil]
    · simpa using ha₂
    · omega

/-- **A relayed request runs with the reply of the challenger with keep coins in the request**:
the request numbered `j < Q`, after the main requests `L` of the `j` before it, runs with `muReply`
at the attempts' coins of request `j`, at most `K` main requests and `qCheck + K · qKeep`
queries. -/
theorem runsWith_ringProg (hK : 0 < K) (j : ℕ) (hj : j < Q)
    (L : List (MURequest J.stdOracle n)) (hL : L.length = K * j)
    (r : MURequest (SignOracle.ringKeep J K hK) n) :
    ∃ asks q, MultiRelay.RunsWith (stdAns keys Q H c') H L
      (ringProg J K n hK (fun i => B.pk (keys i)) r)
      (muReply (SignOracle.ringKeep J K hK) keys H (attemptCoins Q c' ⟨j, hj⟩) r) asks q ∧
      asks.length ≤ K ∧ q ≤ J.qCheck + K * J.qKeep := by
  have hLK : L.length + K ≤ K * Q := by
    rw [hL]
    have := Nat.mul_le_mul_left K (Nat.succ_le_of_lt hj)
    rw [Nat.mul_succ] at this
    exact this
  have hLt : L.length < K * Q := by omega
  rcases r with i | ⟨i, ⟨⟨R, msg⟩, ks⟩ | bm⟩ | i
  · have h := MultiRelay.RunsWith.query_inr (ansM := stdAns keys Q H c') (H := H) (rs := L)
      (k := fun b => OracleProg.pure (b.elim (fun _ => none) id)) (.publicKey i)
      (MultiRelay.RunsWith.pure _ _)
    refine ⟨_, _, h.congr_res ?_, by simp; omega, Nat.zero_le _⟩
    exact answerAfter_muChallenger J.stdOracle keys (K * Q) H c' L _ hLt
  · simp only [ringProg]
    by_cases hm : B.pk (keys i) ∈ R.1
    · rw [if_pos hm]
      obtain ⟨asks, q, h, ha, hq⟩ := runsWith_relaySign keys Q H c' i R
        (R.1.idxOf (B.pk (keys i))) msg ks L hLK
      refine ⟨asks, q, (h.mapOutput (Option.map MUResponse.signature)).congr_res ?_, ha, hq⟩
      simp only [muReply, SignOracle.ringKeep]
      have hm' : (B.keyGen (keys i)).1 ∈ R.1 := hm
      rw [if_pos hm', J.run_rejectSign]
      congr 2
      simp only [attemptCoins]
      congr 1
      refine congrArg List.ofFn (funext fun t => ?_)
      congr 2
      exact Fin.ext (by simp [hL])
    · rw [if_neg hm]
      refine ⟨[], 0, (MultiRelay.RunsWith.pure _ _).congr_res ?_, Nat.zero_le _, Nat.zero_le _⟩
      simp only [muReply, SignOracle.ringKeep]
      have hm' : (B.keyGen (keys i)).1 ∉ R.1 := hm
      rw [if_neg hm']
      rfl
  · have h := MultiRelay.RunsWith.query_inr (ansM := stdAns keys Q H c') (H := H) (rs := L)
      (k := fun b => OracleProg.pure (b.elim (fun _ => none) id)) (.sign i bm)
      (MultiRelay.RunsWith.pure _ _)
    refine ⟨_, _, h.congr_res ?_, by simp; omega, Nat.zero_le _⟩
    refine (answerAfter_muChallenger J.stdOracle keys (K * Q) H c' L _ hLt).trans ?_
    have hc : c' ⟨L.length, hLt⟩ = attemptCoins Q c' ⟨j, hj⟩ ⟨0, hK⟩ :=
      congrArg c' (Fin.ext (by simp [hL]))
    change Option.map MUResponse.signature ((J.std (B.keyGen (keys i)).2 bm (c' ⟨L.length, hLt⟩)).run
        H) =
      Option.map MUResponse.signature
        ((J.std (B.keyGen (keys i)).2 bm (attemptCoins Q c' ⟨j, hj⟩ ⟨0, hK⟩)).run H)
    rw [hc]
  · have h := MultiRelay.RunsWith.query_inr (ansM := stdAns keys Q H c') (H := H) (rs := L)
      (k := fun b => OracleProg.pure (b.elim (fun _ => none) id)) (.corrupt i)
      (MultiRelay.RunsWith.pure _ _)
    refine ⟨_, _, h.congr_res ?_, by simp; omega, Nat.zero_le _⟩
    exact answerAfter_muChallenger J.stdOracle keys (K * Q) H c' L _ hLt

end Runs

/-! ### The challenger with keep coins in the request relays the standard challenger -/

section Relays

variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] {J K n}

/-- **The challenger with keep coins in the request, with `Q` requests, is the relay `ringRelay`
of the standard challenger with `K · Q` requests** (`MultiRelay.RelaysChallenger`), along the
attempts' coins: each request is answered as its relay program answers it against the standard
replies. -/
theorem relaysChallenger_ringRelay (hK : 0 < K) (keys : Fin n → B.KeyCoins) (i₀ : Fin n)
    (Q : ℕ) :
    letI : Inhabited (MURequest J.stdOracle n) := ⟨.publicKey i₀⟩
    (ringRelay J K n hK (fun i => B.pk (keys i)) i₀).RelaysChallenger
      (muChallenger (SignOracle.ringKeep J K hK) n keys Q)
      (muChallenger J.stdOracle n keys (K * Q)) (attemptCoins Q) := by
  letI : Inhabited (MURequest J.stdOracle n) := ⟨.publicKey i₀⟩
  exact {
    coins_eq := (map_uniformOfFintype_equiv (attemptCoinsEquiv hK Q)).symm
    oracle_eq := fun H c _ lg => (muChallenger_noAssign _ keys Q).oracle_eq H c lg
    oracle_eq' := fun H c' _ lg => (muChallenger_noAssign _ keys (K * Q)).oracle_eq H c' lg
    answer_eq := fun H c' rs r hi => by
      rw [answerAfter_muChallenger (SignOracle.ringKeep J K hK) keys Q H (attemptCoins Q c') rs r
        hi]
      obtain ⟨asks, q, h, ha, hq⟩ := runsWith_ringProg keys Q H c' hK rs.length hi
        ((ringRelay J K n hK (fun i => B.pk (keys i)) i₀).mainReqs Q
          ((muChallenger J.stdOracle n keys (K * Q)).toPureEnv.answerAfter (H, c')) H rs)
        ((ringRelay J K n hK (fun i => B.pk (keys i)) i₀).length_mainReqs Q _ H rs hi.le) r
      exact ((ringRelay J K n hK (fun i => B.pk (keys i)) i₀).runReply_eq_of_runsWith rfl h ha
        hq).symm }

end Relays

/-! ### The lifting lemma -/

section Lifting

variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] {V : OracleView X Y} {t : ℕ}

/-- **The relayed multi-user adversary** of an adversary `A` of the game with the signing oracle
`O` and `Q` requests, along the message maps `f s` at the side coins `s`: on the public keys
`pks`, the auxiliary input of `A` with uniform side coins `s : Fin Q → Fin K → J.KeepCoins`, the
algorithm of `A` with its requests absorbed through `msgRelay (f s)`
(`QueryBoundedAdversary.absorbSide`, an adversary of the game with keep coins in the request),
then relayed by the programs `ringRelay` at `pks` (`QueryBoundedAdversary.relay`), answering `Q`
requests, with `K` standard requests and `qCheck + K · qKeep` queries per request, the idle request
the public key of user `i₀`. It makes at most `t + Q · (qCheck + K · qKeep)` queries on every
branch. -/
noncomputable def liftAdversary (hK : 0 < K) (i₀ : Fin n) {O : SignOracle B} (Q : ℕ)
    (f : (Fin Q → Fin K → J.KeepCoins) → ℕ → O.SMsg → (SignOracle.ringKeep J K hK).SMsg)
    (hf : ∀ s c, Function.Injective (f s c)) (A : MUAdversary O n V t) :
    MUAdversary J.stdOracle n V (t + Q * (J.qCheck + K * J.qKeep)) := fun inp =>
  letI : Inhabited (MURequest (SignOracle.ringKeep J K hK) n) := ⟨.publicKey i₀⟩
  letI : Inhabited (MURequest J.stdOracle n) := ⟨.publicKey i₀⟩
  ((A inp).absorbSide (PMF.uniformOfFintype (Fin Q → Fin K → J.KeepCoins))
    (fun s => msgRelay n (f s)) fun s c => MURequest.mapMsg_injective (hf s c)).relay
      (ringRelay J K n hK inp.1 i₀) Q

/-- **The relayed multi-user adversary of the ring-aware game** (`liftAdversary` along
`ringKeepMsg`). -/
noncomputable def relayMUAdversary (hK : 0 < K) (i₀ : Fin n)
    (A : MUAdversary (SignOracle.ring B) n V t) (Q : ℕ) :
    MUAdversary J.stdOracle n V (t + Q * (J.qCheck + K * J.qKeep)) :=
  liftAdversary J K n hK i₀ Q (ringKeepMsg hK) (ringKeepMsg_injective hK) A

/-- **The relayed multi-user adversary of the key-reuse game** (`liftAdversary` along
`ringStdKeepMsg`). -/
noncomputable def relayMUAdversaryStd (hK : 0 < K) (i₀ : Fin n)
    (A : MUAdversary (SignOracle.ringStd B) n V t) (Q : ℕ) :
    MUAdversary J.stdOracle n V (t + Q * (J.qCheck + K * J.qKeep)) :=
  liftAdversary J K n hK i₀ Q (ringStdKeepMsg hK) (ringStdKeepMsg_injective hK) A

variable {J K n}

/-- **A verifying signature under the key of an uncorrupted user**: `σ` verifies on `bm` under
`pk`, the key of a user not corrupted in `hist`. -/
structure HonestVerifies {O : SignOracle B} (keys : Fin n → B.KeyCoins) (H : X → Y)
    (f : B.PK × B.BMsg × B.BSig) (hist : MUHist O n) : Prop where
  /-- The signature verifies. -/
  verify_eq : B.bverify H f.1 f.2.1 f.2.2 = true
  /-- The key is that of a user not corrupted. -/
  exists_user : ∃ i, B.pk (keys i) = f.1 ∧ ¬ Corrupted hist i

/-- A strong forgery is a verifying signature under the key of an uncorrupted user. -/
theorem StrongForges.honestVerifies {O : SignOracle B} {keys : Fin n → B.KeyCoins} {H : X → Y}
    {f : B.PK × B.BMsg × B.BSig} {hist : MUHist O n} (h : StrongForges keys H f hist) :
    HonestVerifies keys H f hist :=
  let ⟨i, hi, hc, _⟩ := h.exists_user
  ⟨h.verify_eq, i, hi, hc⟩

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
noncomputable def muVerifyProb {O : SignOracle B} (A : MUAdversary O n V t) (Q : ℕ) : ℝ≥0∞ :=
  (muLaw A Q).toOuterMeasure {x | ∃ p ∈ x.2.2, HonestVerifies x.1 x.2.1 p.1 p.2}

/-- **The two steps of the relay for an event of the transcript**, at the users' key coins `keys`
and the oracle `H`: the transcript of `A` against the challenger of `O` lies in `E` with at most
the probability that the transcript of `liftAdversary` against the standard challenger with
`K · Q` requests lies in `E''`, when `E` passes to `E'` along every relay of messages (`himp₁`)
and `E'` to `E''` along every relay history of `ringRelay` (`himp₂`). Hypotheses: the signing coins
split along `e` into uniform side coins and uniform standard coins (`hcoins`), and at the side
coins `s` the challenger of `O` relays the challenger of `ringKeep` by `msgRelay (f s)` (`hrel`). -/
theorem transcriptLaw_le_lift (hK : 0 < K) (i₀ : Fin n) {O : SignOracle B} (Q : ℕ)
    (f : (Fin Q → Fin K → J.KeepCoins) → ℕ → O.SMsg → (SignOracle.ringKeep J K hK).SMsg)
    (hf : ∀ s c, Function.Injective (f s c))
    (e : (Fin Q → O.Coins) ≃ (Fin Q → Fin K → J.KeepCoins) × (Fin Q → Fin K → J.StdCoins))
    (hcoins : ∀ s c', PMF.uniformOfFintype _ (e.symm (s, c')) =
      PMF.uniformOfFintype _ s * PMF.uniformOfFintype _ c')
    (keys : Fin n → B.KeyCoins)
    (hrel : ∀ s c', (msgRelay n (f s)).RelaysChallenger (muChallenger O n keys Q) (e.symm (s, c'))
      (muChallenger (SignOracle.ringKeep J K hK) n keys Q) c')
    (A : MUAdversary O n V t) (H : X → Y)
    (E : (B.PK × B.BMsg × B.BSig) × MUHist O n → Prop)
    (E' : (B.PK × B.BMsg × B.BSig) × MUHist (SignOracle.ringKeep J K hK) n → Prop)
    (E'' : (B.PK × B.BMsg × B.BSig) × MUHist J.stdOracle n → Prop)
    (himp₁ : ∀ s o hist hist', E (o, hist) →
      hist'.map HistoryEntry.request = (msgRelay n (f s)).relayList
        (hist.map HistoryEntry.request) → E' (o, hist'))
    (himp₂ : ∀ o hist hist', E' (o, hist) → HistRelay hist hist' → E'' (o, hist')) :
    ((A (fun i => B.pk (keys i), V.view H)).transcriptLaw (muChallenger O n keys Q) H).toOuterMeasure
        {x | ∃ p ∈ x, E p} ≤
      ((liftAdversary J K n hK i₀ Q f hf A (fun i => B.pk (keys i), V.view H)).transcriptLaw
        (muChallenger J.stdOracle n keys (K * Q)) H).toOuterMeasure {x | ∃ p ∈ x, E'' p} := by
  let _ : Inhabited (MURequest (SignOracle.ringKeep J K hK) n) := ⟨.publicKey i₀⟩
  let _ : Inhabited (MURequest J.stdOracle n) := ⟨.publicKey i₀⟩
  refine le_trans ((A (fun i => B.pk (keys i), V.view H)).transcriptLaw_le_absorbSide
    (C := muChallenger O n keys Q) (C' := muChallenger (SignOracle.ringKeep J K hK) n keys Q)
    (PMF.uniformOfFintype (Fin Q → Fin K → J.KeepCoins)) (fun s => msgRelay n (f s)) e hcoins hrel
    rfl (fun s c => MURequest.mapMsg_injective (hf s c)) H E E' himp₁) ?_
  -- TODO(unbundle-M4): `congr 3` splits the comparison of `liftAdversary` with the relay of the
  -- absorbed adversary, which `exact` unfolds through both shapes
  refine le_of_le_of_eq (((A (fun i => B.pk (keys i), V.view H)).absorbSide _ _ _).transcriptLaw_le_relay
    (ringRelay J K n hK (fun i => B.pk (keys i)) i₀)
    (muChallenger (SignOracle.ringKeep J K hK) n keys Q) (muChallenger J.stdOracle n keys (K * Q))
    (attemptCoins Q) (relaysChallenger_ringRelay hK keys i₀ Q) H E' E''
    (fun o hist hist' hE hr => himp₂ o hist hist' hE (histRelay_of_relays hK _ i₀ hr))) ?_
  congr 3

/-- **The lifting lemma for MU-EUF-CMA^corr along a relay of messages**: under the hypotheses of
`transcriptLaw_le_lift` at every key coins, with base messages kept by `f` (`hb`), every adversary
`A` of the game with the signing oracle `O` and `Q` requests has at most the success probability
of `liftAdversary` in the standard game with `K · Q` requests. -/
theorem muEufProb_le_lift (hK : 0 < K) (i₀ : Fin n) {O : SignOracle B} (Q : ℕ)
    (f : (Fin Q → Fin K → J.KeepCoins) → ℕ → O.SMsg → (SignOracle.ringKeep J K hK).SMsg)
    (hf : ∀ s c, Function.Injective (f s c))
    (hb : ∀ s c sm, (SignOracle.ringKeep J K hK).base (f s c sm) = O.base sm)
    (e : (Fin Q → O.Coins) ≃ (Fin Q → Fin K → J.KeepCoins) × (Fin Q → Fin K → J.StdCoins))
    (hcoins : ∀ s c', PMF.uniformOfFintype _ (e.symm (s, c')) =
      PMF.uniformOfFintype _ s * PMF.uniformOfFintype _ c')
    (hrel : ∀ keys s c', (msgRelay n (f s)).RelaysChallenger (muChallenger O n keys Q)
      (e.symm (s, c')) (muChallenger (SignOracle.ringKeep J K hK) n keys Q) c')
    (A : MUAdversary O n V t) :
    muEufProb A Q ≤ muEufProb (liftAdversary J K n hK i₀ Q f hf A) (K * Q) := by
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
`A` as well, so this is not a reduction to MU-SUF-CMA^corr (module docstring). -/
theorem muSufProb_le_muVerifyProb_lift (hK : 0 < K) (i₀ : Fin n) {O : SignOracle B} (Q : ℕ)
    (f : (Fin Q → Fin K → J.KeepCoins) → ℕ → O.SMsg → (SignOracle.ringKeep J K hK).SMsg)
    (hf : ∀ s c, Function.Injective (f s c))
    (hb : ∀ s c sm, (SignOracle.ringKeep J K hK).base (f s c sm) = O.base sm)
    (e : (Fin Q → O.Coins) ≃ (Fin Q → Fin K → J.KeepCoins) × (Fin Q → Fin K → J.StdCoins))
    (hcoins : ∀ s c', PMF.uniformOfFintype _ (e.symm (s, c')) =
      PMF.uniformOfFintype _ s * PMF.uniformOfFintype _ c')
    (hrel : ∀ keys s c', (msgRelay n (f s)).RelaysChallenger (muChallenger O n keys Q)
      (e.symm (s, c')) (muChallenger (SignOracle.ringKeep J K hK) n keys Q) c')
    (A : MUAdversary O n V t) :
    muSufProb A Q ≤ muVerifyProb (liftAdversary J K n hK i₀ Q f hf A) (K * Q) := by
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

variable {e : B.Coins ≃ (Fin K → J.StdCoins × J.KeepCoins)}

/-- **The lifting lemma for MU-EUF-CMA^corr** (module docstring): under `IsRejectionOn B J K e`,
every adversary `A` of the ring-aware game with `Q` requests has at most the success probability
of its relayed adversary (at most `t + Q · (qCheck + K · qKeep)` queries) in the standard game with
`K · Q` requests. -/
theorem muEufProb_le_relay (hK : 0 < K) (hrej : IsRejectionOn B J K e) (i₀ : Fin n)
    (A : MUAdversary (SignOracle.ring B) n V t) (Q : ℕ) :
    muEufProb A Q ≤ muEufProb (relayMUAdversary J K n hK i₀ A Q) (K * Q) :=
  muEufProb_le_lift hK i₀ Q (ringKeepMsg hK) (ringKeepMsg_injective hK) (fun _ _ _ => rfl)
    (keepSplit e Q) (uniform_keepSplit_symm e Q)
    (fun keys s c' => relaysChallenger_ringKeep hK hrej keys Q s c') A

/-- **The strong-forgery probability of the ring-aware game is at most the relayed adversary's
probability of a verifying signature under an uncorrupted user's key** (module docstring): under
`IsRejectionOn B J K e`, every adversary `A` of the ring-aware game with `Q` requests has
MU-SUF-CMA^corr success probability at most `muVerifyProb` of its relayed adversary in the standard
game with `K · Q` requests. Not a reduction to MU-SUF-CMA^corr: the right-hand side counts the
signatures passed on to `A`. -/
theorem muSufProb_le_muVerifyProb_relay (hK : 0 < K) (hrej : IsRejectionOn B J K e) (i₀ : Fin n)
    (A : MUAdversary (SignOracle.ring B) n V t) (Q : ℕ) :
    muSufProb A Q ≤ muVerifyProb (relayMUAdversary J K n hK i₀ A Q) (K * Q) :=
  muSufProb_le_muVerifyProb_lift hK i₀ Q (ringKeepMsg hK) (ringKeepMsg_injective hK)
    (fun _ _ _ => rfl) (keepSplit e Q) (uniform_keepSplit_symm e Q)
    (fun keys s c' => relaysChallenger_ringKeep hK hrej keys Q s c') A

/-- `ringStdKeepMsg` keeps the base messages. -/
theorem ringStdKeepMsg_base (hK : 0 < K) {Q : ℕ} (s : Fin Q → Fin K → J.KeepCoins) (c : ℕ)
    (sm : (SignOracle.ringStd B).SMsg) :
    (SignOracle.ringKeep J K hK).base (ringStdKeepMsg hK s c sm) = (SignOracle.ringStd B).base sm :=
  by rcases sm with p | bm <;> rfl

/-- **The lifting lemma for MU-EUF-CMA^corr with key reuse** (module docstring): under
`IsRejectionOn B J K e` and `IsStdOn B J K e hK`, every adversary `A` of the key-reuse game
(`SignOracle.ringStd`, ring requests and base messages) with `Q` requests has at most the success
probability of its relayed adversary `relayMUAdversaryStd` (at most
`t + Q · (qCheck + K · qKeep)` queries) in the standard game with `K · Q` requests. -/
theorem muEufProb_le_relay_ringStd (hK : 0 < K) (hrej : IsRejectionOn B J K e)
    (hstd : IsStdOn B J K e hK) (i₀ : Fin n) (A : MUAdversary (SignOracle.ringStd B) n V t)
    (Q : ℕ) : muEufProb A Q ≤ muEufProb (relayMUAdversaryStd J K n hK i₀ A Q) (K * Q) :=
  muEufProb_le_lift hK i₀ Q (ringStdKeepMsg hK) (ringStdKeepMsg_injective hK)
    (ringStdKeepMsg_base hK) (keepSplit e Q) (uniform_keepSplit_symm e Q)
    (fun keys s c' => relaysChallenger_ringStdKeep hK hrej hstd keys Q s c') A

/-- **The strong-forgery probability of the key-reuse game is at most the relayed adversary's
probability of a verifying signature under an uncorrupted user's key**: under the hypotheses of
`muEufProb_le_relay_ringStd`, the bound of `muSufProb_le_muVerifyProb_relay` for the key-reuse game
and `relayMUAdversaryStd`. -/
theorem muSufProb_le_muVerifyProb_relay_ringStd (hK : 0 < K) (hrej : IsRejectionOn B J K e)
    (hstd : IsStdOn B J K e hK) (i₀ : Fin n) (A : MUAdversary (SignOracle.ringStd B) n V t)
    (Q : ℕ) :
    muSufProb A Q ≤ muVerifyProb (relayMUAdversaryStd J K n hK i₀ A Q) (K * Q) :=
  muSufProb_le_muVerifyProb_lift hK i₀ Q (ringStdKeepMsg hK) (ringStdKeepMsg_injective hK)
    (ringStdKeepMsg_base hK) (keepSplit e Q) (uniform_keepSplit_symm e Q)
    (fun keys s c' => relaysChallenger_ringStdKeep hK hrej hstd keys Q s c') A

end Lifting

end GordieHowe.Signature
