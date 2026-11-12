-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Signature.MultiUserSim
public import GordieHowe.Model.Signature.MultiUserBridge
public import GordieHowe.Model.Quantum.Interactive.ReqBridgeSlots

@[expose] public section

/-!
# Forgeries with few signing and corruption requests

The multi-user challenger of `GordieHowe/Model/Signature/MultiUser.lean` counts every request,
public-key requests included, against its bound. This file counts only the signing and corruption
requests of a history and restricts the forgery event of MU-EUF-CMA^corr to the histories with at
most `Qs` of them; a bound by this probability says that the forger wins only on branches where it
asked at most `Qs` signatures and corruptions.

- `MURequest.isSignOrCorrupt`, `signCorruptCount`: the signing and corruption requests of a
  history and their number.
- `muEufProbWithin A Q' Qs`: the probability that `A`, against the challenger answering `Q'`
  requests, terminates with a forgery for a history with at most `Qs` signing and corruption
  requests; `muEufProbWithin_le_muEufProb`, `muEufProbWithin_mono`.
- `muSufProbWithin A Q' Qs`: the same for a strong forgery (`StrongForges`, MU-SUF-CMA^corr);
  `muEufProbWithin_le_muSufProbWithin`, `muSufProbWithin_le_muSufProb`, `muSufProbWithin_mono`,
  `muEufProbWithin_le_one`, `muSufProbWithin_le_one`.
- `muEufProbWithin_coSimMU`: for a forger holding a compressed-oracle simulation (`coSimMU`), the
  Born-weight form of `muEufProb_coSimMU` with the count of the logged requests;
  `toOuterMeasure_muLaw_coSimMU`: the same for any event of the terminal requests;
  `toOuterMeasure_muLaw_coSimMU_count`: at the event of more than `Qs` signing and corruption
  requests.
- `countP_requestsBefore`, `countP_requests`: the requests of logs satisfying a test are counted by
  the filled entries satisfying it (`Option.any`).
- `answerSlot_inj`, `card_bridge_le`: on a basis state of the bridge
  algorithm's simulation where every request is the dummy or the outer request of the log of the
  slot it answers (`bridgeAlg_slotLogs`), the requests satisfying a test the dummy fails are at most
  the absorbed logs whose outer requests satisfy it.
-/

namespace GordieHowe

open Quantum QROM RingSignature
open scoped ENNReal

/-! ### Counting requests of logs -/

/-- **The requests before slot `k` satisfying `p`** are counted by the slots below `k` whose
entries satisfy it. -/
theorem countP_requestsBefore {Req : Type} {m : ℕ} (lg : LogReg Req m) (p : Req → Bool) :
    ∀ k, (requestsBefore lg k).countP p =
      ∑ j : Fin m, if (j : ℕ) < k then (lg j).toList.countP p else 0
  | 0 => by simp [requestsBefore]
  | k + 1 => by
    rw [requestsBefore, List.countP_append, countP_requestsBefore lg p k]
    have hsplit : ∀ j : Fin m, (if (j : ℕ) < k + 1 then (lg j).toList.countP p else 0) =
        (if (j : ℕ) < k then (lg j).toList.countP p else 0) +
          (if (j : ℕ) = k then (lg j).toList.countP p else 0) := fun j => by
      split_ifs <;> omega
    rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib]
    congr 1
    split_ifs with hk
    · rw [Finset.sum_eq_single ⟨k, hk⟩ (fun j _ hj => if_neg fun h => hj (Fin.ext h))
        (by simp), if_pos rfl]
    · rw [Finset.sum_eq_zero fun (j : Fin m) _ => if_neg fun (h : (j : ℕ) = k) => hk (h ▸ j.isLt)]
      simp

/-- **The requests of logs satisfying `p`** are counted by the filled entries satisfying it. -/
theorem countP_requests {Req : Type} {m : ℕ} (lg : LogReg Req m) (p : Req → Bool) :
    (requests lg).countP p = (Finset.univ.filter fun j => (lg j).any p = true).card := by
  rw [requests, countP_requestsBefore lg p m, Finset.card_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [if_pos j.isLt]
  rcases h : lg j with _ | r
  · simp
  · by_cases hp : p r <;> simp [hp]

/-! ### The answer steps are injective; the count on the bridge -/

section Bridge

variable {m : ℕ} {I J Bd : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)

omit [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁] in
/-- **Distinct answer steps answer distinct slots.** -/
theorem answerSlot_inj {k k' : ℕ} {j : Fin A.slots} (h : answerSlot A C₁ k = some j)
    (h' : answerSlot A C₁ k' = some j) : k = k' :=
  (answerSlot_eq_some A C₁ h).trans (answerSlot_eq_some A C₁ h').symm

omit [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁]
  [Fintype Req₂] [DecidableEq Req₂] in
/-- **The count on the bridge** (module docstring): if every request of the log register `lg` of
the request points is the dummy `d₂` or the outer request (along `outer` at the slot) of the log of
the slot its point answers (`hlg`), the requests satisfying `p`, which the dummy fails (`hp`), are at most the
logs `logs` whose outer request satisfies `p`. -/
theorem card_bridge_le {t : ℕ} (outer : Fin A.slots → Req → Option Req₂) (d₂ : Req₂) (lg : LogReg Req₂ t)
    (logs : LogReg Req A.slots) (p : Req₂ → Bool) (hp : p d₂ = false)
    (hlg : ∀ i q, lg i = some q → q = d₂ ∨ ∃ j r, answerSlot A C₁ i = some j ∧
      logs j = some r ∧ outer j r = some q) :
    (Finset.univ.filter fun i => (lg i).any p = true).card ≤
      (Finset.univ.filter fun j => (logs j).any (fun r => (outer j r).any p) = true).card := by
  set S := Finset.univ.filter fun i : Fin t => (lg i).any p = true
  set S' := Finset.univ.filter fun j : Fin A.slots =>
    (logs j).any (fun r => (outer j r).any p) = true
  have hmap : ∀ i ∈ S, ∃ j ∈ S', answerSlot A C₁ i = some j := by
    intro i hi
    have hPq := (Finset.mem_filter.1 hi).2
    rcases hq : lg i with _ | q
    · rw [hq] at hPq
      exact absurd hPq (by simp)
    rw [hq, Option.any_some] at hPq
    rcases hlg i q hq with h | ⟨j, r, hj, hr, ho⟩
    · rw [h, hp] at hPq
      exact absurd hPq Bool.false_ne_true
    · refine ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, hj⟩
      rw [hr, Option.any_some, ho, Option.any_some]
      exact hPq
  calc S.card ≤ (S'.map Function.Embedding.some).card := by
        refine Finset.card_le_card_of_injOn (fun i => answerSlot A C₁ i) (fun i hi => ?_)
          (fun i hi i' hi' he => ?_)
        · obtain ⟨j, hj, hs⟩ := hmap i hi
          exact Finset.mem_map.2 ⟨j, hj, hs.symm⟩
        · obtain ⟨j, -, hs⟩ := hmap i hi
          have hs' : answerSlot A C₁ i' = some j := (he.symm.trans hs : _)
          exact Fin.ext (answerSlot_inj A C₁ hs hs')
    _ = S'.card := Finset.card_map _

end Bridge

namespace Signature

section Core

variable {X Y : Type} {TB : SchemeTypes}
  {B : BaseScheme X Y TB} {O : SignOracle B} {n : ℕ}

/-! ### Signing and corruption requests -/

/-- **A signing or corruption request**, not a public-key request. -/
def MURequest.isSignOrCorrupt : MURequest O n → Bool
  | .publicKey _ => false
  | .sign _ _ => true
  | .corrupt _ => true

/-- **The number of signing and corruption requests** of a history. -/
def signCorruptCount (hist : MUHist O n) : ℕ :=
  hist.countP fun e => e.request.isSignOrCorrupt

/-- The number of signing and corruption requests read from the requests of the history. -/
theorem signCorruptCount_eq (hist : MUHist O n) :
    signCorruptCount hist = (hist.map HistoryEntry.request).countP MURequest.isSignOrCorrupt := by
  rw [signCorruptCount, List.countP_map]
  rfl

variable [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y] {V : OracleView X Y} {t : ℕ}

variable [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]
  [Nonempty O.Coins]

variable [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] [Nonempty TB.KeyCoins]

/-- **The success probability of the adversary in MU-EUF-CMA^corr with at most `Qs` signing and
corruption requests**, against the challenger answering `Q'` requests: it terminates with a forgery
(`Forges`) for a history with at most `Qs` signing and corruption requests. -/
noncomputable def muEufProbWithin (A : MUAdversary O n V t) (Q' Qs : ℕ) : ℝ≥0∞ :=
  (muLaw A Q').toOuterMeasure
    {r | r.Wins fun keys H f hist => Forges keys H f hist ∧ signCorruptCount hist ≤ Qs}

/-- **The restricted event is within MU-EUF-CMA^corr.** -/
theorem muEufProbWithin_le_muEufProb (A : MUAdversary O n V t) (Q' Qs : ℕ) :
    muEufProbWithin A Q' Qs ≤ muEufProb A Q' :=
  PMF.toOuterMeasure_mono _ fun _ ⟨⟨p, hp, hf, _⟩, _⟩ => ⟨p, hp, hf⟩

/-- **More signing and corruption requests allowed, a larger probability.** -/
theorem muEufProbWithin_mono (A : MUAdversary O n V t) (Q' : ℕ) {Qs Qs' : ℕ} (h : Qs ≤ Qs') :
    muEufProbWithin A Q' Qs ≤ muEufProbWithin A Q' Qs' :=
  PMF.toOuterMeasure_mono _ fun _ ⟨⟨p, hp, hf, hc⟩, _⟩ => ⟨p, hp, hf, hc.trans h⟩

/-- **The success probability of the adversary in MU-SUF-CMA^corr with at most `Qs` signing and
corruption requests**, against the challenger answering `Q'` requests: it terminates with a strong
forgery (`StrongForges`) for a history with at most `Qs` signing and corruption requests. -/
noncomputable def muSufProbWithin (A : MUAdversary O n V t) (Q' Qs : ℕ) : ℝ≥0∞ :=
  (muLaw A Q').toOuterMeasure
    {r | r.Wins fun keys H f hist => StrongForges keys H f hist ∧ signCorruptCount hist ≤ Qs}

/-- **The restricted MU-EUF-CMA^corr event is within the restricted MU-SUF-CMA^corr event**
(`Forges.strongForges`), with the same numbers of requests. -/
theorem muEufProbWithin_le_muSufProbWithin (A : MUAdversary O n V t) (Q' Qs : ℕ) :
    muEufProbWithin A Q' Qs ≤ muSufProbWithin A Q' Qs :=
  PMF.toOuterMeasure_mono _ fun _ ⟨⟨p, hp, hf, hc⟩, _⟩ => ⟨p, hp, hf.strongForges, hc⟩

/-- **The restricted event is within MU-SUF-CMA^corr.** -/
theorem muSufProbWithin_le_muSufProb (A : MUAdversary O n V t) (Q' Qs : ℕ) :
    muSufProbWithin A Q' Qs ≤ muSufProb A Q' :=
  PMF.toOuterMeasure_mono _ fun _ ⟨⟨p, hp, hf, _⟩, _⟩ => ⟨p, hp, hf⟩

/-- **More signing and corruption requests allowed, a larger probability** (MU-SUF-CMA^corr). -/
theorem muSufProbWithin_mono (A : MUAdversary O n V t) (Q' : ℕ) {Qs Qs' : ℕ} (h : Qs ≤ Qs') :
    muSufProbWithin A Q' Qs ≤ muSufProbWithin A Q' Qs' :=
  PMF.toOuterMeasure_mono _ fun _ ⟨⟨p, hp, hf, hc⟩, _⟩ => ⟨p, hp, hf, hc.trans h⟩

/-- The restricted success probability in MU-EUF-CMA^corr is at most `1`. -/
theorem muEufProbWithin_le_one (A : MUAdversary O n V t) (Q' Qs : ℕ) :
    muEufProbWithin A Q' Qs ≤ 1 :=
  (muEufProbWithin_le_muEufProb A Q' Qs).trans (muEufProb_le_one A Q')

/-- The restricted success probability in MU-SUF-CMA^corr is at most `1`. -/
theorem muSufProbWithin_le_one (A : MUAdversary O n V t) (Q' Qs : ℕ) :
    muSufProbWithin A Q' Qs ≤ 1 :=
  (muSufProbWithin_le_muSufProb A Q' Qs).trans (muSufProb_le_one A Q')

end Core

section Forger

variable {N n : ℕ} {m : ℕ} {I J Bd : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {T : Signature.SchemeTypes} {RMsg : Type}
  {B : BaseSigner (Bits m) (BitStr I J) N T RMsg} (O : SignOracle B.core) [NeZero n]
  (e : BitStr I J ≃ Bd)

variable [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]
  [Nonempty O.Coins]

variable [Fintype T.PK] [DecidableEq T.PK] [Fintype T.BSig] [DecidableEq T.BSig]
  [Fintype T.KeyCoins] [DecidableEq T.KeyCoins] [Nonempty T.KeyCoins]

/-- **The success probability with few signing and corruption requests of the forger holding a
compressed-oracle simulation** (`muEufProb_coSimMU` with the count): averaged over the users' key
coins, the oracle, the auxiliary input and the challenger's coins, the Born weight of `|Sim*⟩` on
the outcomes whose readout is a forgery for the logged requests, at most `Qs` of them signing or
corruption requests. -/
theorem muEufProbWithin_coSimMU (hO : O.NoQuery) (Aux : (Fin n → B.PK) → Type)
    (aux : ∀ pks, PMF (Aux pks)) (t : ∀ pks, Aux pks → ℕ) (Ot : ∀ pks, Aux pks → Type)
    (G : ∀ pks a, ReqQueryAlg (Bits m) (BitStr I J) (MURequest O n) (MUResponse B.core) (t pks a)
      (Ot pks a))
    (g : ∀ pks a, Ot pks a × DB (Bits m) Bd → B.PK × B.BMsg × B.BSig) (Q' Qs : ℕ)
    (hQ : ∀ pks a, t pks a + 1 ≤ Q') :
    muEufProbWithin (coSimMU O e Aux aux t Ot G g) Q' Qs =
      ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
        ∑' H, PMF.uniformOfFintype (Bits m → BitStr I J) H *
          ∑' a, aux (fun i => B.pk (keys i)) a *
            ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
              bornWeight
                (simState e ((G (fun i => B.pk (keys i)) a).inst (muReplyAfter O keys Q' c)))
                {b | ForgesReq keys H (g (fun i => B.pk (keys i)) a
                  ((G (fun i => B.pk (keys i)) a).out b.1.1.1, slotsDB e b.2))
                  (requests b.1.1.2) ∧
                  (requests b.1.1.2).countP MURequest.isSignOrCorrupt ≤ Qs} := by
  classical
  simp only [muEufProbWithin, muLaw, runLaw, PMF.toOuterMeasure_bind_apply,
    PMF.toOuterMeasure_map_apply, QueryBoundedAdversary.transcriptLaw]
  refine tsum_congr fun keys => congrArg _ (tsum_congr fun H => congrArg _ (tsum_congr fun a => ?_))
  congr 1
  set G' := G (fun i => B.pk (keys i)) a
  set g' := g (fun i => B.pk (keys i)) a
  have hset : (fun o => (keys, H, o)) ⁻¹' {x : (Fin n → B.KeyCoins) × (Bits m → BitStr I J) ×
      Option ((B.PK × B.BMsg × B.BSig) × MUHist O n) |
        ∃ p ∈ x.2.2, Forges x.1 x.2.1 p.1 p.2 ∧ signCorruptCount p.2 ≤ Qs} =
      {o | ∃ p ∈ o, Forges keys H p.1 p.2 ∧ signCorruptCount p.2 ≤ Qs} := rfl
  rw [hset]
  -- TODO(unbundle-M4): rewriting `alg` leaves the scheme's `sh a` in the shape argument; state
  -- `composeBothOut_mapOut` at the field shape and go back to `rw`
  change ((KindAlg.composeBothOut (muChallenger O n keys Q')
      (ReqQueryAlg.coSimAdv e G' (BitStr I J)).toKindAlg fun v =>
        (g' ((ReqQueryAlg.coSimAdv e G' (BitStr I J)).output (muChallenger O n keys Q') v),
          (ReqQueryAlg.coSimAdv e G' (BitStr I J)).history (muChallenger O n keys Q') v)).outLaw
        H).toOuterMeasure {o | ∃ p ∈ o, Forges keys H p.1 p.2 ∧ signCorruptCount p.2 ≤ Qs} = _
  rw [KindAlg.toOuterMeasure_outLaw_composeBothOut]
  simp only [forges_iff_forgesReq, signCorruptCount_eq]
  rw [← KindAlg.toOuterMeasure_outLaw_composeBothOut (ReqQueryAlg.coSimAdv e G'
    (BitStr I J)).toKindAlg (muChallenger O n keys Q') (fun v =>
      ((ReqQueryAlg.coSimAdv e G' (BitStr I J)).output (muChallenger O n keys Q') v,
        (ReqQueryAlg.coSimAdv e G' (BitStr I J)).history (muChallenger O n keys Q') v)) H
    (fun p => ForgesReq keys H (g' p.1) (p.2.map HistoryEntry.request) ∧
      (p.2.map HistoryEntry.request).countP MURequest.isSignOrCorrupt ≤ Qs)]
  exact ReqQueryAlg.toOuterMeasure_outLaw_coSimAdv_history e (G := G') H
    (muChallenger O n keys Q') (muReplyAfter O keys Q') (hQ _ a)
    (fun c k hist w hl => (run_respond_muChallenger hO keys Q' c hist _ H).trans (by rw [hl]))
    (fun c hist r H' => by rw [run_respond_muChallenger hO keys Q' c hist r H'])
    (fun o rs => ForgesReq keys H (g' o) rs ∧ rs.countP MURequest.isSignOrCorrupt ≤ Qs)

/-- **The law of the forger holding a compressed-oracle simulation on an event of its terminal
requests** (`muEufProb_coSimMU` for any event `P` of the users' key coins, the oracle, the forgery
and the requests of the history): averaged over the users' key coins, the oracle, the auxiliary
input and the challenger's coins, the Born weight of `|Sim*⟩` on the outcomes whose readout and
logged requests satisfy `P`. -/
theorem toOuterMeasure_muLaw_coSimMU (hO : O.NoQuery) (Aux : (Fin n → B.PK) → Type)
    (aux : ∀ pks, PMF (Aux pks)) (t : ∀ pks, Aux pks → ℕ) (Ot : ∀ pks, Aux pks → Type)
    (G : ∀ pks a, ReqQueryAlg (Bits m) (BitStr I J) (MURequest O n) (MUResponse B.core) (t pks a)
      (Ot pks a))
    (g : ∀ pks a, Ot pks a × DB (Bits m) Bd → B.PK × B.BMsg × B.BSig) (Q' : ℕ)
    (hQ : ∀ pks a, t pks a + 1 ≤ Q')
    (P : (Fin n → B.KeyCoins) → (Bits m → BitStr I J) → B.PK × B.BMsg × B.BSig →
      List (MURequest O n) → Prop) :
    (muLaw (coSimMU O e Aux aux t Ot G g) Q').toOuterMeasure
        {x | ∃ p ∈ x.2.2, P x.1 x.2.1 p.1 (p.2.map HistoryEntry.request)} =
      ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
        ∑' H, PMF.uniformOfFintype (Bits m → BitStr I J) H *
          ∑' a, aux (fun i => B.pk (keys i)) a *
            ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
              bornWeight
                (simState e ((G (fun i => B.pk (keys i)) a).inst (muReplyAfter O keys Q' c)))
                {b | P keys H (g (fun i => B.pk (keys i)) a
                  ((G (fun i => B.pk (keys i)) a).out b.1.1.1, slotsDB e b.2))
                  (requests b.1.1.2)} := by
  classical
  simp only [muLaw, runLaw, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply,
    QueryBoundedAdversary.transcriptLaw]
  refine tsum_congr fun keys => congrArg _ (tsum_congr fun H => congrArg _ (tsum_congr fun a => ?_))
  congr 1
  set G' := G (fun i => B.pk (keys i)) a
  set g' := g (fun i => B.pk (keys i)) a
  have hset : (fun o => (keys, H, o)) ⁻¹' {x : (Fin n → B.KeyCoins) × (Bits m → BitStr I J) ×
      Option ((B.PK × B.BMsg × B.BSig) × MUHist O n) |
        ∃ p ∈ x.2.2, P x.1 x.2.1 p.1 (p.2.map HistoryEntry.request)} =
      {o | ∃ p ∈ o, P keys H p.1 (p.2.map HistoryEntry.request)} := rfl
  rw [hset]
  -- TODO(unbundle-M4): rewriting `alg` leaves the scheme's `sh a` in the shape argument; state
  -- `composeBothOut_mapOut` at the field shape and go back to `rw`
  change ((KindAlg.composeBothOut (muChallenger O n keys Q')
      (ReqQueryAlg.coSimAdv e G' (BitStr I J)).toKindAlg fun v =>
        (g' ((ReqQueryAlg.coSimAdv e G' (BitStr I J)).output (muChallenger O n keys Q') v),
          (ReqQueryAlg.coSimAdv e G' (BitStr I J)).history (muChallenger O n keys Q') v)).outLaw
        H).toOuterMeasure {o | ∃ p ∈ o, P keys H p.1 (p.2.map HistoryEntry.request)} = _
  rw [KindAlg.toOuterMeasure_outLaw_composeBothOut]
  rw [← KindAlg.toOuterMeasure_outLaw_composeBothOut (ReqQueryAlg.coSimAdv e G'
    (BitStr I J)).toKindAlg (muChallenger O n keys Q') (fun v =>
      ((ReqQueryAlg.coSimAdv e G' (BitStr I J)).output (muChallenger O n keys Q') v,
        (ReqQueryAlg.coSimAdv e G' (BitStr I J)).history (muChallenger O n keys Q') v)) H
    (fun p => P keys H (g' p.1) (p.2.map HistoryEntry.request))]
  exact ReqQueryAlg.toOuterMeasure_outLaw_coSimAdv_history e (G := G') H
    (muChallenger O n keys Q') (muReplyAfter O keys Q') (hQ _ a)
    (fun c k hist w hl => (run_respond_muChallenger hO keys Q' c hist _ H).trans (by rw [hl]))
    (fun c hist r H' => by rw [run_respond_muChallenger hO keys Q' c hist r H'])
    (fun o rs => P keys H (g' o) rs)

/-- **The forger holding a compressed-oracle simulation asks more than `Qs` signatures and
corruptions** with the coin average of the Born weights of the outcomes with more than `Qs` logged
signing and corruption requests (`toOuterMeasure_muLaw_coSimMU` at that event). -/
theorem toOuterMeasure_muLaw_coSimMU_count (hO : O.NoQuery) (Aux : (Fin n → B.PK) → Type)
    (aux : ∀ pks, PMF (Aux pks)) (t : ∀ pks, Aux pks → ℕ) (Ot : ∀ pks, Aux pks → Type)
    (G : ∀ pks a, ReqQueryAlg (Bits m) (BitStr I J) (MURequest O n) (MUResponse B.core) (t pks a)
      (Ot pks a))
    (g : ∀ pks a, Ot pks a × DB (Bits m) Bd → B.PK × B.BMsg × B.BSig) (Q' Qs : ℕ)
    (hQ : ∀ pks a, t pks a + 1 ≤ Q') :
    (muLaw (coSimMU O e Aux aux t Ot G g) Q').toOuterMeasure
        {x | ∃ p ∈ x.2.2, Qs < signCorruptCount p.2} =
      ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
        ∑' H, PMF.uniformOfFintype (Bits m → BitStr I J) H *
          ∑' a, aux (fun i => B.pk (keys i)) a *
            ∑ c, PMF.uniformOfFintype (Fin Q' → O.Coins) c *
              bornWeight
                (simState e ((G (fun i => B.pk (keys i)) a).inst (muReplyAfter O keys Q' c)))
                {b | Qs < (requests b.1.1.2).countP MURequest.isSignOrCorrupt} := by
  simp only [signCorruptCount_eq]
  exact toOuterMeasure_muLaw_coSimMU O e hO Aux aux t Ot G g Q' hQ
    fun _ _ _ rs => Qs < rs.countP MURequest.isSignOrCorrupt

end Forger

end Signature

end GordieHowe
