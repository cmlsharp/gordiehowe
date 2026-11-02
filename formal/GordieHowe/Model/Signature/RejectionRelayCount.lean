-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Signature.RejectionRelay
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
-/

namespace GordieHowe.Signature

open GordieHowe.Quantum GordieHowe.RingSignature
open scoped ENNReal

variable {X Y : Type} {N : ℕ} {TB : BaseTypes} {B : BaseSigner X Y N TB} (J : Rejection B) (K n : ℕ)

section Count

variable {n} {O O' : SignOracle B}

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

variable {J K n}

/-- **A program of the ring relay asks a signing or corruption request only for a signing or
corruption request.** -/
theorem isSignOrCorrupt_of_canAsk_ringRelay [Zero Y] (hK : 0 < K) (pks : Fin n → B.PK) (i₀ : Fin n)
    (r : MURequest (SignOracle.ringKeep J K hK) n) (r' : MURequest J.stdOracle n)
    (hc : (ringRelay J K n hK pks i₀).CanAsk r r') (hr' : r'.isSignOrCorrupt = true) :
    r.isSignOrCorrupt = true := by
  have h := (ringRelay J K n hK pks i₀).canAsk_of_asksIn
    (asksIn_ringProg (J := J) (K := K) hK pks r).plainProg
    hc
  rcases r with i | ⟨i, sm⟩ | i
  · change r' = .publicKey i at h
    rw [h] at hr'
    exact hr'
  · rfl
  · rfl

variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y] {V : OracleView X Y} {t : ℕ}

/-- **`transcriptLaw_le_lift` with the count**: the second step's implication may also use that the
standard history holds at most `K` times as many signing and corruption requests as the
history of `ringKeep`. -/
theorem transcriptLaw_le_lift_count (hK : 0 < K) (i₀ : Fin n) {O : SignOracle B} (Q : ℕ)
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
    (himp₂ : ∀ o hist hist', E' (o, hist) → HistRelay hist hist' →
      signCorruptCount hist' ≤ K * signCorruptCount hist → E'' (o, hist')) :
    ((A (fun i => B.pk (keys i), V.view H)).transcriptLaw (muChallenger O n keys Q)
      H).toOuterMeasure
        {x | ∃ p ∈ x, E p} ≤
      ((liftAdversary J K n hK i₀ Q f hf A (fun i => B.pk (keys i), V.view H)).transcriptLaw
        (muChallenger J.stdOracle n keys (K * Q)) H).toOuterMeasure {x | ∃ p ∈ x, E'' p} := by
  let _ : Inhabited (MURequest (SignOracle.ringKeep J K hK) n) := ⟨.publicKey i₀⟩
  let _ : Inhabited (MURequest J.stdOracle n) := ⟨.publicKey i₀⟩
  refine le_trans ((A (fun i => B.pk (keys i), V.view H)).transcriptLaw_le_absorbSide
    (C := muChallenger O n keys Q) (C' := muChallenger (SignOracle.ringKeep J K hK) n keys Q)
    (PMF.uniformOfFintype (Fin Q → Fin K → J.KeepCoins)) (fun s => msgRelay n (f s)) e hcoins hrel
    rfl (fun s c => MURequest.mapMsg_injective (hf s c)) H E E' himp₁) ?_
  -- TODO(unbundle-M4): `exact` times out unifying `liftAdversary` with the relay; `congr 3` splits it.
  refine le_of_le_of_eq (((A (fun i => B.pk (keys i), V.view H)).absorbSide _ _ _).transcriptLaw_le_relay_count
    (ringRelay J K n hK (fun i => B.pk (keys i)) i₀)
    (muChallenger (SignOracle.ringKeep J K hK) n keys Q) (muChallenger J.stdOracle n keys (K * Q))
    (attemptCoins Q) (relaysChallenger_ringRelay hK keys i₀ Q) H (p := MURequest.isSignOrCorrupt)
    (q := MURequest.isSignOrCorrupt) rfl
    (isSignOrCorrupt_of_canAsk_ringRelay hK _ i₀) E' E''
    (fun o hist hist' hE hr hc => himp₂ o hist hist' hE (histRelay_of_relays hK _ i₀ hr) hc)) ?_
  congr 3

/-- **The lifting lemma for MU-EUF-CMA^corr with the count, along a relay of messages**: under the
hypotheses of `muEufProb_le_lift`, the probability that `A` wins with at most `Qs` signing and
corruption requests is at most the probability that `liftAdversary` wins with at most `K · Qs` in
the standard game with `K · Q` requests. -/
theorem muEufProbWithin_le_lift (hK : 0 < K) (i₀ : Fin n) {O : SignOracle B} (Q : ℕ)
    (f : (Fin Q → Fin K → J.KeepCoins) → ℕ → O.SMsg → (SignOracle.ringKeep J K hK).SMsg)
    (hf : ∀ s c, Function.Injective (f s c))
    (hb : ∀ s c sm, (SignOracle.ringKeep J K hK).base (f s c sm) = O.base sm)
    (e : (Fin Q → O.Coins) ≃ (Fin Q → Fin K → J.KeepCoins) × (Fin Q → Fin K → J.StdCoins))
    (hcoins : ∀ s c', PMF.uniformOfFintype _ (e.symm (s, c')) =
      PMF.uniformOfFintype _ s * PMF.uniformOfFintype _ c')
    (hrel : ∀ keys s c', (msgRelay n (f s)).RelaysChallenger (muChallenger O n keys Q)
      (e.symm (s, c')) (muChallenger (SignOracle.ringKeep J K hK) n keys Q) c')
    (A : MUAdversary O n V t) (Qs : ℕ) :
    muEufProbWithin A Q Qs ≤
      muEufProbWithin (liftAdversary J K n hK i₀ Q f hf A) (K * Q) (K * Qs) := by
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

variable {e : B.Coins ≃ (Fin K → J.StdCoins × J.KeepCoins)}

/-- **The lifting lemma for MU-EUF-CMA^corr with the count** (module docstring): under
`IsRejectionOn B J K e`, the probability that an adversary `A` of the ring-aware game with `Q`
requests wins with at most `Qs` signing and corruption requests is at most the probability that
its relayed adversary wins with at most `K · Qs` in the standard game with `K · Q` requests. -/
theorem muEufProbWithin_le_relay (hK : 0 < K) (hrej : IsRejectionOn B J K e) (i₀ : Fin n)
    (A : MUAdversary (SignOracle.ring B) n V t) (Q Qs : ℕ) :
    muEufProbWithin A Q Qs ≤
      muEufProbWithin (relayMUAdversary J K n hK i₀ A Q) (K * Q) (K * Qs) :=
  muEufProbWithin_le_lift hK i₀ Q (ringKeepMsg hK) (ringKeepMsg_injective hK) (fun _ _ _ => rfl)
    (keepSplit e Q) (uniform_keepSplit_symm e Q)
    (fun keys s c' => relaysChallenger_ringKeep hK hrej keys Q s c') A Qs

/-- **The key-reuse form**: under `IsRejectionOn B J K e` and `IsStdOn B J K e hK`, the bound of
`muEufProbWithin_le_relay` for the key-reuse game and `relayMUAdversaryStd`. -/
theorem muEufProbWithin_le_relay_ringStd (hK : 0 < K) (hrej : IsRejectionOn B J K e)
    (hstd : IsStdOn B J K e hK) (i₀ : Fin n) (A : MUAdversary (SignOracle.ringStd B) n V t)
    (Q Qs : ℕ) :
    muEufProbWithin A Q Qs ≤
      muEufProbWithin (relayMUAdversaryStd J K n hK i₀ A Q) (K * Q) (K * Qs) :=
  muEufProbWithin_le_lift hK i₀ Q (ringStdKeepMsg hK) (ringStdKeepMsg_injective hK)
    (ringStdKeepMsg_base hK) (keepSplit e Q) (uniform_keepSplit_symm e Q)
    (fun keys s c' => relaysChallenger_ringStdKeep hK hrej hstd keys Q s c') A Qs

end GordieHowe.Signature
