-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.MultiRelay
public import GordieHowe.Model.Quantum.Pure.MultiRelayOriginCount

@[expose] public section

/-!
# The number of the relayed adversary's requests of a kind, for transcripts

The counting form of `AdaptiveIAlg.history_relayPlace` and
`QueryBoundedAdversary.transcriptLaw_le_relay`
(`GordieHowe/Model/Quantum/Interactive/MultiRelay.lean`): for a test `p` on main requests that the
idle request fails and a test `q` on relayed requests holding of every request whose program can
make
a main request satisfying `p`, the relayed adversary's history holds at most `K` times as many
requests satisfying `p` as the adversary's history holds requests satisfying `q`
(`Distinguisher.countP_place_le`, `GordieHowe/Model/Quantum/Pure/MultiRelayOriginCount.lean`).

- `AdaptiveIAlg.countP_history_relayPlace_le`: at a placed basis state.
- `QueryBoundedAdversary.transcriptLaw_le_relay_count`: the transcript bound with the count in the
  history implication.
- `RingSignature.GameAdversary.transcriptLaw_le_relay_count`: the same for game adversaries.
-/

namespace GordieHowe.Quantum

namespace AdaptiveIAlg

open Classical

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) [AddGroup Y] [Nonempty X] [Nonempty Y]
  {Req' Resp' O' : Type} [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Inhabited X] [Inhabited Req'] {Xs Ys : Type} [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
  (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)
  (out' : A.RelayWS F → O')

/-- **The count at a placed basis state** (module docstring): the relayed adversary's history at
the placement of `y` holds at most `K` times as many requests satisfying `p` as the adversary's
history at `y` holds requests satisfying `q`. -/
theorem countP_history_relayPlace_le {p : Req' → Bool} {q : Req → Bool} (hpi : p F.idle = false)
    (hq : ∀ r r', F.CanAsk r r' → p r' = true → q r = true)
    (Cout : Challenger X Y Req Resp) (c : Cout.Coins)
    (C : Challenger X Y Req' Resp') (H : X → Y) (c' : C.Coins)
    (y : GameReg (A.toTPKindAlg true).unitOut.DW (A.toTPKindAlg true).unitOut.width X Y Req Resp
      (A.toTPKindAlg true).unitOut.slots) :
    ((A.relayAdv F Cout.Q out').history C (A.relayPlace F Cout.Q out' C H c' y)).countP
        (fun e' => p e'.request) ≤
      F.K * (A.history Cout
        (A.toKindAlg.emb Cout H c A.slots
          (((A.toTPKindAlg true).unitOut.relG y).1.1 : A.toKindAlg.G)).1).countP
          (fun e => q e.request) := by
  have hm := Challenger.map_request_regStateOf C.Q C.respond
    (A.relayPlace F Cout.Q out' C H c' y).chal.coins
    (A.relayPlace F Cout.Q out' C H c' y).chal.logs
    ((A.relayAdv F Cout.Q out').toKindAlg.ansOf C (A.relayPlace F Cout.Q out' C H c' y).chal)
    (A.relayAdv F Cout.Q out').toKindAlg.slots
  have hA := Challenger.map_request_regStateOf Cout.Q Cout.respond c
    (splitLogs y).2 (A.toKindAlg.ansOf Cout
      (A.toKindAlg.emb Cout H c A.slots
        (((A.toTPKindAlg true).unitOut.relG y).1.1 : A.toKindAlg.G)).1.chal) A.slots
  have hlogs : (splitLogs (embR A.post true y)).2 = extLogs A.post (splitLogs y).2 := rfl
  have hplace := A.pureD.countP_place_le F (A.budget + A.post) Cout.Q
    (C.toPureEnv.answerAfter (H, c')) H hpi hq (embR A.post true y)
  rw [hlogs, requests_extLogs] at hplace
  rw [show (fun e' : HistoryEntry Req' Resp' => p e'.request) = p ∘ HistoryEntry.request from rfl,
    show (fun e : HistoryEntry Req Resp => q e.request) = q ∘ HistoryEntry.request from rfl,
    ← List.countP_map, ← List.countP_map]
  erw [hm, hA]
  exact ((List.take_sublist _ _).countP_le).trans hplace

end AdaptiveIAlg

namespace QueryBoundedAdversary

open Classical

variable {X Y Req Resp O Req' Resp' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Nonempty X] [AddGroup Y] [Nonempty Y]
  [Inhabited X] [Inhabited Req'] {Xs Ys : Type} [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] {t : ℕ}

/-- **The multi-request relay for transcripts, with the count** (module docstring): the bound of
`transcriptLaw_le_relay` when `E'` holds of every output with every history `hist'` each of whose
requests is the idle request or one that the program of a request of a history `hist` can make, and
holding at most `K` times as many requests satisfying `p` as `hist` holds requests satisfying `q`,
if `E` holds of the output with `hist`. -/
theorem transcriptLaw_le_relay_count (𝒜 : QueryBoundedAdversary X Y Req Resp O t)
    (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (Cout : Challenger X Y Req Resp)
    (C : Challenger X Y Req' Resp') (κ : C.Coins → Cout.Coins) (hF : F.RelaysChallenger Cout C κ)
    (H : X → Y) {p : Req' → Bool} {q : Req → Bool} (hpi : p F.idle = false)
    (hq : ∀ r r', F.CanAsk r r' → p r' = true → q r = true)
    (E : O × List (HistoryEntry Req Resp) → Prop)
    (E' : O × List (HistoryEntry Req' Resp') → Prop)
    (himp : ∀ (o : O) (hist : List (HistoryEntry Req Resp))
      (hist' : List (HistoryEntry Req' Resp')),
      E (o, hist) →
        (∀ e' ∈ hist', e'.request = F.idle ∨ ∃ e ∈ hist, F.CanAsk e.request e'.request) →
        hist'.countP (fun e' => p e'.request) ≤ F.K * hist.countP (fun e => q e.request) →
        E' (o, hist')) :
    (𝒜.transcriptLaw Cout H).toOuterMeasure {x | ∃ p ∈ x, E p} ≤
      ((𝒜.relay F Cout.Q).transcriptLaw C H).toOuterMeasure {x | ∃ p ∈ x, E' p} := by
  rw [transcriptLaw, transcriptLaw, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  refine ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [KindAlg.toOuterMeasure_outLaw_composeBothOut]
  conv_rhs => rw [KindAlg.toOuterMeasure_outLaw_composeBothOut]
  refine (𝒜.alg a).toOuterMeasure_le_relayAdv F ((𝒜.alg a).relayOut F) Cout C κ hF H _ _ ?_
  intro c' y hy
  have ho := (𝒜.alg a).output_relayPlace F Cout.Q C H c' y Cout (κ c')
  have hh := (𝒜.alg a).history_relayPlace F ((𝒜.alg a).relayOut F) Cout (κ c') C H c' y
  have hc := (𝒜.alg a).countP_history_relayPlace_le F ((𝒜.alg a).relayOut F) hpi hq Cout (κ c')
    C H c' y
  have h := himp _ _ _ hy.2 hh hc
  rw [← ho] at h
  exact h

end QueryBoundedAdversary

end GordieHowe.Quantum

namespace GordieHowe.RingSignature.GameAdversary

open GordieHowe.Quantum Classical

variable {X Y Req Resp O Req' Resp' In : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Nonempty X] [AddGroup Y] [Nonempty Y]
  [Inhabited X] [Inhabited Req'] {Xs Ys : Type} [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] {t : ℕ}

/-- **`QueryBoundedAdversary.transcriptLaw_le_relay_count` for game adversaries.** -/
theorem transcriptLaw_le_relay_count (A : GameAdversary X Y Req Resp In O t)
    (F : In → MultiRelay X Y Req Resp Req' Resp' Xs Ys) (qR : ℕ)
    (hF : ∀ inp, (F inp).qR ≤ qR) (qP : ℕ) (hP : ∀ inp, (F inp).qP ≤ qP)
    (inp : In) (Cout : Challenger X Y Req Resp) (C : Challenger X Y Req' Resp')
    (κ : C.Coins → Cout.Coins) (hFC : (F inp).RelaysChallenger Cout C κ) (H : X → Y)
    {p : Req' → Bool} {q : Req → Bool} (hpi : p (F inp).idle = false)
    (hq : ∀ r r', (F inp).CanAsk r r' → p r' = true → q r = true)
    (E : O × List (HistoryEntry Req Resp) → Prop) (E' : O × List (HistoryEntry Req' Resp') → Prop)
    (himp : ∀ (o : O) (hist : List (HistoryEntry Req Resp))
      (hist' : List (HistoryEntry Req' Resp')),
      E (o, hist) → (∀ e' ∈ hist', e'.request = (F inp).idle ∨
        ∃ e ∈ hist, (F inp).CanAsk e.request e'.request) →
        hist'.countP (fun e' => p e'.request) ≤ (F inp).K * hist.countP (fun e => q e.request) →
        E' (o, hist')) :
    ((A inp).transcriptLaw Cout H).toOuterMeasure {x | ∃ p ∈ x, E p} ≤
      ((A.relay F qR hF qP hP Cout.Q inp).transcriptLaw C H).toOuterMeasure {x | ∃ p ∈ x, E' p} :=
  (A inp).transcriptLaw_le_relay_count (F inp) Cout C κ hFC H hpi hq E E' himp

end GordieHowe.RingSignature.GameAdversary
