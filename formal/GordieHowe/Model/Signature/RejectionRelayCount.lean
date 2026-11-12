-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Signature.RejectionCtx
public import GordieHowe.Model.Signature.MultiUserCount
public import GordieHowe.Model.Quantum.Interactive.MultiRelayHistCount

@[expose] public section

/-!
# The lifting lemma with at most `K · Qs` signing and corruption requests

The lifting lemmas of `GordieHowe/Model/Signature/RejectionRelay.lean` in the form
`Signature.muEufProbWithin` (`GordieHowe/Model/Signature/MultiUserCount.lean`): an adversary of the
ring-aware game that wins with at most `Qs` signing and corruption requests (against a challenger
answering `Q` requests) has at most the success probability of its relayed adversary winning with
at most `K · Qs` signing and corruption requests in the standard game (against `K · Q`). The relay
of messages maps signing and corruption requests to signing and corruption requests one to one;
the programs of the ring relay ask a signing or corruption request only for a signing or
corruption request, at most `K` of them, and their idle request is a public key
(`QueryBoundedAdversary.transcriptLaw_le_relay_count`,
`GordieHowe/Model/Quantum/Interactive/MultiRelayHistCount.lean`).

- `MURequest.isSignOrCorrupt_mapMsg`, `countP_relayList_msgRelay`: the relay of messages keeps the
  count.
- `isSignOrCorrupt_of_canAsk_ringRelay`: a program of the ring relay asks a signing or corruption
  request only for a signing or corruption request.
- `transcriptLaw_le_lift_count`: `transcriptLaw_le_lift` with the count in the second step.
- `muEufProbWithin_le_lift`, `muEufProbWithin_le_relay`, `muEufProbWithin_le_relay_ringStd`:
  **the lifting lemmas with the count.**
- `CtxRejection.isSignOrCorrupt_of_canAsk_relay`, `CtxRejection.transcriptLaw_le_lift_count`,
  `CtxRejection.muEufProbWithin_le_lift`, `CtxRejection.SignsOn.muEufProbWithin_le_relay`: the same
  for the rejection forms with a context of `GordieHowe/Model/Signature/RejectionCtx.lean`.
-/

namespace GordieHowe.Signature

open GordieHowe.Quantum GordieHowe.RingSignature
open scoped ENNReal

variable {X Y : Type}

section Count

variable {TB : SchemeTypes} {B : BaseScheme X Y TB}

variable {n : ℕ} {O O' : SignOracle B}

/-- Mapping the message keeps signing and corruption requests. -/
@[simp]
theorem MURequest.isSignOrCorrupt_mapMsg (g : O.SMsg → O'.SMsg) (r : MURequest O n) :
    (MURequest.mapMsg g r).isSignOrCorrupt = r.isSignOrCorrupt := by
  rcases r with i | ⟨i, sm⟩ | i <;> rfl

/-- A list mapped request by request keeping signing and corruption requests has their number. -/
theorem countP_mapIdx_isSignOrCorrupt (g : ℕ → MURequest O n → MURequest O' n)
    (hg : ∀ i r, (g i r).isSignOrCorrupt = r.isSignOrCorrupt) :
    ∀ rs : List (MURequest O n),
      (rs.mapIdx g).countP MURequest.isSignOrCorrupt = rs.countP MURequest.isSignOrCorrupt
  | [] => rfl
  | r :: rs => by
    rw [List.mapIdx_cons, List.countP_cons, List.countP_cons, hg,
      countP_mapIdx_isSignOrCorrupt (fun i => g (i + 1)) (fun i => hg (i + 1)) rs]

variable (n) in
/-- **The relay of messages keeps the number of signing and corruption requests.** -/
theorem countP_relayList_msgRelay (f : ℕ → O.SMsg → O'.SMsg) (rs : List (MURequest O n)) :
    ((msgRelay n f).relayList rs).countP MURequest.isSignOrCorrupt =
      rs.countP MURequest.isSignOrCorrupt :=
  countP_mapIdx_isSignOrCorrupt _ (fun i r => MURequest.isSignOrCorrupt_mapMsg (f i) r) rs

end Count

section Ctx

variable {TB : SchemeTypes} {B : BaseScheme X Y TB} {K n : ℕ}

variable [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BMsg] [DecidableEq TB.BMsg]

variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] {V : OracleView X Y} {t : ℕ}

variable [Fintype TB.BSig] [DecidableEq TB.BSig] [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]

variable [Nonempty TB.KeyCoins]

variable [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins]

/-! ### The count for rejection forms with a context -/

namespace CtxRejection

variable {P Ctx : Type} {C : CtxRejection B P Ctx}

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BMsg]
  [DecidableEq TB.BMsg] [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y]
  [DecidableEq Y] [AddGroup Y] [Nonempty Y] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins] [Fintype TB.Coins]
  [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **A program of the relay asks a signing or corruption request only for a signing or corruption
request.** -/
theorem isSignOrCorrupt_of_canAsk_relay [Zero Y] (hK : 0 < K) (pks : Fin n → B.PK) (i₀ : Fin n)
    (r : MURequest (C.keepOracle K hK) n) (r' : MURequest C.stdOracle n)
    (hc : (C.relay K n hK pks i₀).CanAsk r r') (hr' : r'.isSignOrCorrupt = true) :
    r.isSignOrCorrupt = true := by
  have h := (C.relay K n hK pks i₀).canAsk_of_asksIn (asksIn_prog hK pks r).plainProg hc
  rcases r with i | ⟨i, sm⟩ | i
  · change r' = .publicKey i at h
    rw [h] at hr'
    exact hr'
  · rfl
  · rfl

variable [Fintype C.StdCoins] [DecidableEq C.StdCoins] [Nonempty C.StdCoins]
  [Fintype C.KeepCoins] [DecidableEq C.KeepCoins] [Nonempty C.KeepCoins] [Fintype P]
  [DecidableEq P]

omit [Nonempty TB.KeyCoins] [Fintype TB.Coins]
  [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **`transcriptLaw_le_lift` with the count**: the second step's implication may also use that the
standard history holds at most `K` times as many signing and corruption requests as the history of
`keepOracle`. -/
theorem transcriptLaw_le_lift_count (hK : 0 < K) (i₀ : Fin n) {O : SignOracle B} [Fintype O.SMsg]
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
    (himp₂ : ∀ o hist hist', E' (o, hist) → HistRelay hist hist' →
      signCorruptCount hist' ≤ K * signCorruptCount hist → E'' (o, hist')) :
    ((A (fun i => B.pk (keys i), V.view H)).transcriptLaw (muChallenger O n keys Q)
      H).toOuterMeasure
        {x | ∃ p ∈ x, E p} ≤
      ((C.liftAdversary K n hK i₀ Q f hf A (fun i => B.pk (keys i), V.view H)).transcriptLaw
        (muChallenger C.stdOracle n keys (K * Q)) H).toOuterMeasure {x | ∃ p ∈ x, E'' p} := by
  let _ : Inhabited (MURequest (C.keepOracle K hK) n) := ⟨.publicKey i₀⟩
  let _ : Inhabited (MURequest C.stdOracle n) := ⟨.publicKey i₀⟩
  refine le_trans ((A (fun i => B.pk (keys i), V.view H)).transcriptLaw_le_absorbSide
    (C := muChallenger O n keys Q) (C' := muChallenger (C.keepOracle K hK) n keys Q)
    (PMF.uniformOfFintype (Fin Q → Fin K → C.KeepCoins)) (fun s => msgRelay n (f s)) e hcoins hrel
    rfl (fun s c => MURequest.mapMsg_injective (hf s c)) H E E' himp₁) ?_
  refine le_of_le_of_eq
    (((A (fun i => B.pk (keys i), V.view H)).absorbSide _ _ _).transcriptLaw_le_relay_count
    (C.relay K n hK (fun i => B.pk (keys i)) i₀)
    (muChallenger (C.keepOracle K hK) n keys Q) (muChallenger C.stdOracle n keys (K * Q))
    (attemptCoins Q) (relaysChallenger_relay hK keys i₀ Q) H (p := MURequest.isSignOrCorrupt)
    (q := MURequest.isSignOrCorrupt) rfl
    (isSignOrCorrupt_of_canAsk_relay hK _ i₀) E' E''
    (fun o hist hist' hE hr hc => himp₂ o hist hist' hE (histRelay_of_relays hK _ i₀ hr) hc)) ?_
  congr 3

omit [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] in
/-- **The lifting lemma for MU-EUF-CMA^corr with the count, along a relay of messages**: under the
hypotheses of `muEufProb_le_lift`, the probability that `A` wins with at most `Qs` signing and
corruption requests is at most the probability that `liftAdversary` wins with at most `K · Qs` in
the standard game with `K · Q` requests. -/
theorem muEufProbWithin_le_lift (hK : 0 < K) (i₀ : Fin n) {O : SignOracle B} [Fintype O.SMsg]
    [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins] [Nonempty O.Coins] (Q : ℕ)
    (f : (Fin Q → Fin K → C.KeepCoins) → ℕ → O.SMsg → (C.keepOracle K hK).SMsg)
    (hf : ∀ s c, Function.Injective (f s c))
    (hb : ∀ s c sm, (C.keepOracle K hK).base (f s c sm) = O.base sm)
    (e : (Fin Q → O.Coins) ≃ (Fin Q → Fin K → C.KeepCoins) × (Fin Q → Fin K → C.StdCoins))
    (hcoins : ∀ s c', PMF.uniformOfFintype _ (e.symm (s, c')) =
      PMF.uniformOfFintype _ s * PMF.uniformOfFintype _ c')
    (hrel : ∀ keys s c', (msgRelay n (f s)).RelaysChallenger (muChallenger O n keys Q)
      (e.symm (s, c')) (muChallenger (C.keepOracle K hK) n keys Q) c')
    (A : MUAdversary O n V t) (Qs : ℕ) :
    muEufProbWithin A Q Qs ≤
      muEufProbWithin (C.liftAdversary K n hK i₀ Q f hf A) (K * Q) (K * Qs) := by
  unfold muEufProbWithin muLaw runLaw
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  refine ENNReal.tsum_le_tsum fun keys => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  refine ENNReal.tsum_le_tsum fun H => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  exact transcriptLaw_le_lift_count hK i₀ Q f hf e hcoins keys (hrel keys) A H
    (fun p => Forges keys H p.1 p.2 ∧ signCorruptCount p.2 ≤ Qs)
    (fun p => Forges keys H p.1 p.2 ∧ signCorruptCount p.2 ≤ Qs)
    (fun p => Forges keys H p.1 p.2 ∧ signCorruptCount p.2 ≤ K * Qs)
    (fun s _ hist hist' hE hmap => ⟨hE.1.of_histRelay (histRelay_of_msgRelay (hb s) hmap), by
      rw [signCorruptCount_eq, hmap, countP_relayList_msgRelay, ← signCorruptCount_eq]
      exact hE.2⟩)
    (fun _ _ _ hE hr hc => ⟨hE.1.of_histRelay hr, hc.trans (Nat.mul_le_mul_left K hE.2)⟩)

omit [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] in
/-- **The lifting lemma for MU-EUF-CMA^corr with the count**: for an oracle `O` that signs as the
rejection form (`SignsOn`) along an injective classifier `π`, the probability that an adversary `A`
of the game with `O` and `Q` requests wins with at most `Qs` signing and corruption requests is at
most the probability that its relayed adversary wins with at most `K · Qs` in the standard game
with `K · Q` requests. -/
theorem SignsOn.muEufProbWithin_le_relay {O : SignOracle B} {π : O.SMsg → P ⊕ B.BMsg}
    {e : O.Coins ≃ (Fin K → C.StdCoins × C.KeepCoins)} {hK : 0 < K} (h : C.SignsOn K hK O π e)
    [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]
    [Nonempty O.Coins] (hπ : Function.Injective π) (i₀ : Fin n) (A : MUAdversary O n V t)
    (Q Qs : ℕ) :
    muEufProbWithin A Q Qs ≤
      muEufProbWithin (C.relayAdversary K n hK i₀ hπ A Q) (K * Q) (K * Qs) :=
  muEufProbWithin_le_lift hK i₀ Q (C.keepMsg hK π) (C.keepMsg_injective hK hπ) h.keepMsg_base
    (keepSplit e Q) (uniform_keepSplit_symm e Q)
    (fun keys s c' => h.relaysChallenger_keep keys Q s c') A Qs

omit [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins] in
/-- **The lifting lemma with the count at the rejection form's oracle**
(`SignsOn.muEufProbWithin_le_relay` at `signsOn_oracle`): the probability that an adversary `A`
of the game with `C.oracle K` and `Q` requests wins with at most `Qs` signing and corruption
requests is at most the probability that its relayed adversary wins with at most `K · Qs` in the
standard game with `K · Q` requests. -/
theorem muEufProbWithin_oracle_le_relay (hK : 0 < K) (i₀ : Fin n)
    (A : MUAdversary (C.oracle K) n V t) (Q Qs : ℕ) :
    muEufProbWithin A Q Qs ≤
      muEufProbWithin (C.relayAdversary K n hK i₀ Sum.inl_injective A Q) (K * Q) (K * Qs) :=
  (C.signsOn_oracle K hK).muEufProbWithin_le_relay Sum.inl_injective i₀ A Q Qs

end CtxRejection

end Ctx

section Ring

variable {N : ℕ} {T : Signature.SchemeTypes} {RMsg : Type}
  {B : BaseSigner X Y N T RMsg} (J : Rejection B) (K n : ℕ)

variable [Fintype J.StdCoins] [DecidableEq J.StdCoins] [Nonempty J.StdCoins] [Fintype J.KeepCoins]
  [DecidableEq J.KeepCoins] [Nonempty J.KeepCoins]

variable {J K n}

variable [Fintype T.PK] [DecidableEq T.PK] [Fintype RMsg] [DecidableEq RMsg] [Fintype T.BMsg]
  [DecidableEq T.BMsg]

variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] {V : OracleView X Y} {t : ℕ}

variable [Fintype T.BSig] [DecidableEq T.BSig] [Fintype T.KeyCoins] [DecidableEq T.KeyCoins]

variable [Nonempty T.KeyCoins]

variable [Fintype T.Coins] [DecidableEq T.Coins] [Nonempty T.Coins]

variable {e : B.Coins ≃ (Fin K → J.StdCoins × J.KeepCoins)}


/-- **The lifting lemma for MU-EUF-CMA^corr with the count**: under `IsRejectionOn B J K e`, the
probability that an adversary `A` of the ring-aware game with `Q` requests wins with at most `Qs`
signing and corruption requests is at most the probability that its relayed adversary wins with at
most `K · Qs` in the standard game with `K · Q` requests
(`CtxRejection.SignsOn.muEufProbWithin_le_relay` at `Rejection.toCtx`). -/
theorem muEufProbWithin_le_relay (hK : 0 < K) (hrej : IsRejectionOn B J K e) (i₀ : Fin n)
    (A : MUAdversary (SignOracle.ring B) n V t) (Q Qs : ℕ) :
    muEufProbWithin A Q Qs ≤
      muEufProbWithin (relayMUAdversary J K n hK i₀ A Q) (K * Q) (K * Qs) := by
  rw [Rejection.relayMUAdversary_eq]
  exact (hrej.signsOn hK).muEufProbWithin_le_relay Sum.inl_injective i₀ A Q Qs

/-- **The joint-security form**: under `IsRejectionOn B J K e` and `IsStdOn B J K e hK`, the bound of
`muEufProbWithin_le_relay` for the joint-security game and `relayMUAdversaryStd`. -/
theorem muEufProbWithin_le_relay_ringStd (hK : 0 < K) (hrej : IsRejectionOn B J K e)
    (hstd : IsStdOn B J K e hK) (i₀ : Fin n) (A : MUAdversary (SignOracle.ringStd B) n V t)
    (Q Qs : ℕ) :
    muEufProbWithin A Q Qs ≤
      muEufProbWithin (relayMUAdversaryStd J K n hK i₀ A Q) (K * Q) (K * Qs) := by
  rw [Rejection.relayMUAdversaryStd_eq]
  exact (hrej.signsOn_ringStd hstd).muEufProbWithin_le_relay Function.injective_id i₀ A Q Qs

end Ring

end GordieHowe.Signature
