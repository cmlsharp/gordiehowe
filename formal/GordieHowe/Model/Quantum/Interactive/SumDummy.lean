-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.SumChallenger
public import GordieHowe.Model.Quantum.Interactive.AbsorbRelay
public import GordieHowe.Model.Quantum.Interactive.AbsorbTranscript
public import GordieHowe.Model.Quantum.Interactive.RevealedPair
public import GordieHowe.Model.Quantum.Interactive.ReqBridge

@[expose] public section

/-!
# The sum of two challengers, the second reading its coins by the global count

`Challenger.sumDummy C₁ C₂ enc`: a challenger answering requests of `Req₁ ⊕ R`, a left request by
`C₁` on the history's left entries (`leftHist`), a right request `q` by `C₂` at the main request
`enc (inr q)`, on the whole history with every request `x` read as `enc x` (`dummyHist`). Every
request, left or right, is one entry of `C₂`'s history, so `C₂` reads its coins by the global
request count. It answers `C₂.Q` requests. Our construction: a left request stands for a dummy
request `enc (inl r)` of `C₂` answered by `C₁`, the form in which a distinguisher absorbs the
left requests as dummy requests of `C₂` (`outLaw_sumDummy`).

With `enc = Sum.elim (fun _ => d₂) id` every left request reads as the one dummy `d₂`; the
absorption lemmas need `enc` injective (`DummyHyps.enc_injective`), so the dummy request of a left
request `r` depends on `r`.

- `dummyHist`, `Challenger.sumDummy`, `Challenger.coins_sumDummy`.
- `Challenger.NoAssign.sumDummy`: the sum of two challengers that never reprogram never
  reprograms. `Challenger.response_sumDummy_inl`, `Challenger.response_sumDummy_inr`.
- `Challenger.map_request_hist_oracleIn`: the requests of a challenger's history after `rs` are
  the first `Q` requests of `rs`.
- `Challenger.NoAssign.leftHist_oracleIn_sumDummy`,
  `Challenger.NoAssign.answerAfter_sumDummy_inl`, `Challenger.NoAssign.answerAfter_sumDummy_inr`:
  below the cap, the left entries of the history are `C₁`'s history after the left requests; the
  reply to a left (right) request is `C₁`'s after the left requests (`C₂`'s after the main
  requests `L.map enc`, for `C₂` reading its history through the requests), tagged.
- `SideRelay.dummyRelay f enc Q`: request `x` sent as `enc x`; a left request `r` numbered below
  `Q` answered by `f r`, a right one by the main reply. `SideRelay.relayList_dummyRelay`.
- `DummyHyps C₁ C₂ enc f`: `enc` injective, `C₁` answering `r` below the cap by `f r` with no
  assignment under every oracle, `C₂` reading its history through the requests and assigning
  nothing on dummy requests. `DummyHyps.relaysChallenger`: then `sumDummy C₁ C₂ enc` at the coins
  `(c₁, c₂)` relays `C₂` at `c₂` by `dummyRelay f enc C₂.Q`.
- `AdaptiveIAlg.outLaw_sumDummy`, `AdaptiveIAlg.outLaw_sumDummy_of_main` (**L1**): the output law
  against `sumDummy C₁ C₂ enc` is that of the adversary absorbed through `dummyRelay` against
  `C₂` (averaged over `C₁`'s coins, or directly on events that do not read them).
  `QueryBoundedAdversary.transcriptLaw_le_sumDummy`: the transcript form.
- `TwoRelay.dummyTwo enc Q`, `TwoRelay.dummyTwo_atC` (**L2**): the relay with the left requests as
  outer requests; at the outer replies `f`, it is `dummyRelay f enc Q`.
-/

namespace GordieHowe.Quantum

variable {X Y Req₁ Resp₁ R Req₂ Resp₂ : Type}

/-- **The history read by the second part**: every request `x` read as the main request `enc x`,
the replies read on the right (`none` for a left entry). -/
def dummyHist (enc : Req₁ ⊕ R → Req₂) :
    List (HistoryEntry (Req₁ ⊕ R) (Resp₁ ⊕ Resp₂)) → List (HistoryEntry Req₂ Resp₂) :=
  List.map fun e => ⟨enc e.request, e.response.bind Sum.getRight?⟩

/-- The requests of `dummyHist` are the encoded requests. -/
theorem map_request_dummyHist (enc : Req₁ ⊕ R → Req₂)
    (hist : List (HistoryEntry (Req₁ ⊕ R) (Resp₁ ⊕ Resp₂))) :
    (dummyHist enc hist).map HistoryEntry.request = (hist.map HistoryEntry.request).map enc := by
  simp [dummyHist, Function.comp_def]

/-- **The sum of two challengers, the second reading its coins by the global count**: a left
request `r` answered by `C₁` on its coins and the history's left entries, a right request `q` by
`C₂` on its coins at the main request `enc (inr q)` and the whole history read through `enc`
(`dummyHist`); the replies tagged by the side, the assignments those of the part answering. It
answers `C₂.Q` requests. -/
noncomputable def Challenger.sumDummy (C₁ : Challenger X Y Req₁ Resp₁)
    (C₂ : Challenger X Y Req₂ Resp₂) (enc : Req₁ ⊕ R → Req₂) :
    Challenger X Y (Req₁ ⊕ R) (Resp₁ ⊕ Resp₂) where
  Coins := C₁.Coins × C₂.Coins
  coins := C₁.coins.bind fun c₁ => C₂.coins.map fun c₂ => (c₁, c₂)
  Q := C₂.Q
  q := max C₁.q C₂.q
  respond ω hist
    | .inl r => (C₁.respond ω.1 (leftHist hist) r).mapOutput fun p =>
        ⟨p.response.map Sum.inl, p.assignments⟩
    | .inr q => (C₂.respond ω.2 (dummyHist enc hist) (enc (.inr q))).mapOutput fun p =>
        ⟨p.response.map Sum.inr, p.assignments⟩
  respond_queries ω hist r H := by
    rcases r with r | r
    · rw [OracleProg.trace_mapOutput]
      exact (C₁.respond_queries _ _ _ H).trans (le_max_left _ _)
    · rw [OracleProg.trace_mapOutput]
      exact (C₂.respond_queries _ _ _ H).trans (le_max_right _ _)

namespace Challenger

variable {C₁ : Challenger X Y Req₁ Resp₁} {C₂ : Challenger X Y Req₂ Resp₂}
  {enc : Req₁ ⊕ R → Req₂}

/-- **The coins of `sumDummy`** are independent coins of the two parts. -/
theorem coins_sumDummy (c₁ : C₁.Coins) (c₂ : C₂.Coins) :
    (Challenger.sumDummy C₁ C₂ enc).coins (c₁, c₂) = C₁.coins c₁ * C₂.coins c₂ := by
  classical
  change (C₁.coins.bind fun c₁ => C₂.coins.map fun c₂ => (c₁, c₂)) (c₁, c₂) = _
  rw [PMF.bind_apply, tsum_eq_single c₁ fun a ha => ?_]
  · rw [PMF.map_apply, tsum_eq_single c₂ fun b hb => by simp [Ne.symm hb]]
    simp
  · rw [PMF.map_apply, ENNReal.tsum_eq_zero.2 fun b => by simp [Ne.symm ha], mul_zero]

/-- **The sum of two challengers that never reprogram never reprograms.** -/
theorem NoAssign.sumDummy (h₁ : C₁.NoAssign) (h₂ : C₂.NoAssign) :
    (Challenger.sumDummy C₁ C₂ enc).NoAssign := by
  rintro c hist (r | r) G
  · simp only [Challenger.sumDummy, OracleProg.run_mapOutput]
    exact h₁ _ _ _ _
  · simp only [Challenger.sumDummy, OracleProg.run_mapOutput]
    exact h₂ _ _ _ _

/-- The reply of `sumDummy` to a left request is `C₁`'s on the left entries, tagged. -/
theorem response_sumDummy_inl (c : C₁.Coins × C₂.Coins)
    (hist : List (HistoryEntry (Req₁ ⊕ R) (Resp₁ ⊕ Resp₂))) (r : Req₁) (G : X → Y) :
    (((Challenger.sumDummy C₁ C₂ enc).respond c hist (.inl r)).run G).response =
      ((C₁.respond c.1 (leftHist hist) r).run G).response.map Sum.inl := by
  simp only [Challenger.sumDummy, OracleProg.run_mapOutput]

/-- The reply of `sumDummy` to a right request is `C₂`'s at its main request, tagged. -/
theorem response_sumDummy_inr (c : C₁.Coins × C₂.Coins)
    (hist : List (HistoryEntry (Req₁ ⊕ R) (Resp₁ ⊕ Resp₂))) (q : R) (G : X → Y) :
    (((Challenger.sumDummy C₁ C₂ enc).respond c hist (.inr q)).run G).response =
      ((C₂.respond c.2 (dummyHist enc hist) (enc (.inr q))).run G).response.map Sum.inr := by
  simp only [Challenger.sumDummy, OracleProg.run_mapOutput]

section Hist

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

/-- **The requests of a challenger's history** after `rs` are the first `Q` requests of `rs`. -/
theorem map_request_hist_oracleIn {Req Resp : Type} (C : Challenger X Y Req Resp)
    (ω : (X → Y) × C.Coins) (rs : List Req) :
    (C.toPureEnv.oracleIn ω rs).hist.map HistoryEntry.request = rs.take C.Q := by
  induction rs using List.reverseRecOn with
  | nil => simp [Env.oracleIn_nil, Challenger.toPureEnv]
  | append_singleton rs r ih =>
    rw [Env.oracleIn_append_singleton]
    by_cases hq : rs.length < C.Q
    · rw [C.update_toPureEnv_of_lt _ _ _ hq, List.map_append, ih,
        List.take_of_length_le hq.le, List.take_of_length_le (by simp; omega)]
      rfl
    · rw [C.update_toPureEnv_of_le _ _ _ (not_lt.1 hq), ih,
        List.take_append_of_le_length (not_lt.1 hq)]

/-- **The left entries of the history of `sumDummy`** of challengers that never reprogram: after
the requests `L` (at most `C₂.Q` of them, at most `C₁.Q` on the left), they are the history of
`C₁` after the left requests, on its coins. -/
theorem NoAssign.leftHist_oracleIn_sumDummy (h₁ : C₁.NoAssign) (h₂ : C₂.NoAssign) (H : X → Y)
    (c : C₁.Coins × C₂.Coins) (L : List (Req₁ ⊕ R)) (hL : L.length ≤ C₂.Q)
    (hl : (L.filterMap Sum.getLeft?).length ≤ C₁.Q) :
    leftHist ((Challenger.sumDummy C₁ C₂ enc).toPureEnv.oracleIn (H, c) L).hist =
      (C₁.toPureEnv.oracleIn (H, c.1) (L.filterMap Sum.getLeft?)).hist := by
  induction L using List.reverseRecOn with
  | nil => rfl
  | append_singleton L r ih =>
    simp only [List.length_append, List.length_singleton] at hL
    obtain ⟨hb, ha, -⟩ := (h₁.sumDummy (enc := enc) h₂).oracleIn H c L
    have hLQ : L.length < (Challenger.sumDummy C₁ C₂ enc).Q := by
      change _ < C₂.Q
      omega
    rcases r with r | r
    · simp only [List.filterMap_append, List.filterMap_cons, Sum.getLeft?_inl,
        List.filterMap_nil, List.length_append, List.length_singleton] at hl ⊢
      have ih1 := ih (by omega) (by omega)
      obtain ⟨hb₁, ha₁, -⟩ := h₁.oracleIn H c.1 (L.filterMap Sum.getLeft?)
      rw [Env.oracleIn_append_singleton, Env.oracleIn_append_singleton,
        Challenger.update_toPureEnv_of_lt _ _ _ _ hLQ,
        Challenger.update_toPureEnv_of_lt _ _ _ _
          (by omega : (L.filterMap Sum.getLeft?).length < C₁.Q)]
      dsimp only
      rw [leftHist_append_inl, response_sumDummy_inl, hb, ha, ih1, hb₁, ha₁,
        bind_getLeft?_map_inl]
    · simp only [List.filterMap_append, List.filterMap_cons, Sum.getLeft?_inr,
        List.filterMap_nil, List.append_nil] at hl ⊢
      rw [Env.oracleIn_append_singleton, Challenger.update_toPureEnv_of_lt _ _ _ _ hLQ]
      dsimp only
      rw [leftHist_append_inr, ih (by omega) hl]

/-- **The reply of `sumDummy` to a left request** after the requests `L`, fewer than `C₂.Q` of
them and fewer than `C₁.Q` on the left: `C₁`'s reply after the left requests, tagged. -/
theorem NoAssign.answerAfter_sumDummy_inl (h₁ : C₁.NoAssign) (h₂ : C₂.NoAssign) (H : X → Y)
    (c : C₁.Coins × C₂.Coins) (L : List (Req₁ ⊕ R)) (r : Req₁) (hL : L.length < C₂.Q)
    (hl : (L.filterMap Sum.getLeft?).length < C₁.Q) :
    (Challenger.sumDummy C₁ C₂ enc).toPureEnv.answerAfter (H, c) L (.inl r) =
      (C₁.toPureEnv.answerAfter (H, c.1) (L.filterMap Sum.getLeft?) r).map Sum.inl := by
  rw [(h₁.sumDummy (enc := enc) h₂).answerAfter_eq H c L _ hL, h₁.answerAfter_eq H c.1 _ r hl,
    ← h₁.leftHist_oracleIn_sumDummy (enc := enc) h₂ H c L hL.le hl.le]
  simp only [Challenger.sumDummy, OracleProg.run_mapOutput]

/-- **The reply of `sumDummy` to a right request** after the requests `L`, fewer than `C₂.Q` of
them, for `C₂` reading its history through the requests: `C₂`'s reply to the main request after
the main requests `L.map enc`, tagged. -/
theorem NoAssign.answerAfter_sumDummy_inr (h₁ : C₁.NoAssign) (h₂ : C₂.NoAssign)
    (hr : C₂.RespondsByRequests) (H : X → Y) (c : C₁.Coins × C₂.Coins) (L : List (Req₁ ⊕ R))
    (q : R) (hL : L.length < C₂.Q) :
    (Challenger.sumDummy C₁ C₂ enc).toPureEnv.answerAfter (H, c) L (.inr q) =
      (C₂.toPureEnv.answerAfter (H, c.2) (L.map enc) (enc (.inr q))).map Sum.inr := by
  rw [(h₁.sumDummy (enc := enc) h₂).answerAfter_eq H c L _ hL,
    h₂.answerAfter_eq H c.2 _ _ (by simpa using hL), response_sumDummy_inr,
    hr c.2 _ ((C₂.toPureEnv.oracleIn (H, c.2) (L.map enc)).hist)]
  rw [map_request_dummyHist, map_request_hist_oracleIn, map_request_hist_oracleIn,
    List.take_of_length_le (show L.length ≤ (Challenger.sumDummy C₁ C₂ enc).Q from hL.le),
    List.take_of_length_le (by simpa using hL.le)]

end Hist

end Challenger

/-! ### The relay of the left requests as dummy requests -/

namespace SideRelay

/-- **The relay of the left requests as dummy requests**: request `x` is sent as `enc x`; a left
request `r` numbered below `Q` is answered by `f r` (the main reply ignored), a right request by
the main reply, tagged. -/
def dummyRelay (f : Req₁ → Option Resp₁) (enc : Req₁ ⊕ R → Req₂) (Q : ℕ) :
    SideRelay (Req₁ ⊕ R) (Resp₁ ⊕ Resp₂) Req₂ Resp₂ where
  route _ x := enc x
  answer c x a := match x with
    | .inl r => if c < Q then (f r).map Sum.inl else none
    | .inr _ => a.map Sum.inr

/-- The relayed requests of `dummyRelay` are the encoded requests. -/
theorem relayList_dummyRelay (f : Req₁ → Option Resp₁) (enc : Req₁ ⊕ R → Req₂) (Q : ℕ)
    (rs : List (Req₁ ⊕ R)) : (dummyRelay (Resp₂ := Resp₂) f enc Q).relayList rs = rs.map enc := by
  exact List.ext_getElem (by simp) fun i _ _ => by simp [relayList, dummyRelay]

end SideRelay

/-- **The hypotheses of the absorption of the left part** (`AdaptiveIAlg.outLaw_sumDummy`): the
encoding of requests is injective (`enc_injective`); below the cap `C₂.Q`, `C₁` answers `r` by
`f r` with no assignments, at every coin, history and oracle, so it makes no assignment and its
reply reads no query (`respond₁`); `C₂` reads its history only through its requests
(`byRequests₂`) and assigns nothing on a dummy request `enc (inl r)` (`dummy_noAssign`). -/
structure DummyHyps (C₁ : Challenger X Y Req₁ Resp₁) (C₂ : Challenger X Y Req₂ Resp₂)
    (enc : Req₁ ⊕ R → Req₂) (f : Req₁ → Option Resp₁) : Prop where
  /-- The encoding of requests is injective. -/
  enc_injective : Function.Injective enc
  /-- Below the cap, `C₁` answers `r` by `f r`, with no assignments. -/
  respond₁ : ∀ c (hist : List (HistoryEntry Req₁ Resp₁)) r (G : X → Y), hist.length < C₂.Q →
    (C₁.respond c hist r).run G = ⟨f r, []⟩
  /-- `C₂` reads its history only through its requests. -/
  byRequests₂ : C₂.RespondsByRequests
  /-- `C₂` assigns nothing on a dummy request. -/
  dummy_noAssign : ∀ c (hist : List (HistoryEntry Req₂ Resp₂)) r (G : X → Y),
    ((C₂.respond c hist (enc (.inl r))).run G).assignments = []

namespace DummyHyps

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] {C₁ : Challenger X Y Req₁ Resp₁}
  {C₂ : Challenger X Y Req₂ Resp₂} {enc : Req₁ ⊕ R → Req₂} {f : Req₁ → Option Resp₁}

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] in
/-- **`sumDummy` relays its second part**: at the coins `(c₁, c₂)` it relays `C₂` at `c₂` by
`dummyRelay f enc C₂.Q`. -/
theorem relaysChallenger (h : DummyHyps C₁ C₂ enc f) (c₁ : C₁.Coins) (c₂ : C₂.Coins) :
    (SideRelay.dummyRelay (Resp₂ := Resp₂) f enc C₂.Q).RelaysChallenger
      (Challenger.sumDummy C₁ C₂ enc) (c₁, c₂)
      C₂ c₂ where
  Q_eq := rfl
  run_eq hist hist' x G hreq hlen := by
    change hist.length < C₂.Q at hlen
    rcases x with r | q
    · have hl : (leftHist hist).length < C₂.Q :=
        lt_of_le_of_lt (List.length_filterMap_le _ _) hlen
      simp only [Challenger.sumDummy, OracleProg.run_mapOutput, h.respond₁ _ _ _ _ hl,
        SideRelay.dummyRelay, hlen, ↓reduceIte, h.dummy_noAssign]
    · rw [SideRelay.relayList_dummyRelay, ← map_request_dummyHist] at hreq
      simp only [Challenger.sumDummy, OracleProg.run_mapOutput, SideRelay.dummyRelay,
        h.byRequests₂ c₂ _ _ _ hreq.symm]
  answer_none i x hi := by
    change C₂.Q ≤ i at hi
    rcases x with r | q
    · simp [SideRelay.dummyRelay, not_lt.2 hi]
    · rfl

end DummyHyps

/-! ### L1: absorbing the left part -/

namespace AdaptiveIAlg

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req₁] [DecidableEq Req₁]
  [Fintype Resp₁] [DecidableEq Resp₁] [Fintype R] [DecidableEq R] [Fintype Req₂]
  [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₂] [Nonempty X]
  [AddGroup Y] [Nonempty Y] {O : Type} {C₁ : Challenger X Y Req₁ Resp₁}
  {C₂ : Challenger X Y Req₂ Resp₂} {enc : Req₁ ⊕ R → Req₂} {f : Req₁ → Option Resp₁}

/-- **L1, absorbing the left part** (`outLaw_absorb` with `C₁`'s coins as side coins): the output
law of `A` against `sumDummy C₁ C₂ enc`, on every event of the adversary's registers, its logs,
the relayed logs, the coins and the final oracle, is the average over `C₁`'s coins of the law of
`A` absorbed through `dummyRelay f enc C₂.Q` against `C₂`. -/
theorem outLaw_sumDummy {shA : AlgShape X Y (Req₁ ⊕ R) (Resp₁ ⊕ Resp₂)} (A : AdaptiveIAlg shA O)
    (h : DummyHyps C₁ C₂ enc f) (H : X → Y)
    (P : DReg A.toKindAlg.W A.width X Y (Req₁ ⊕ R) (Resp₁ ⊕ Resp₂) →
      LogReg (Req₁ ⊕ R) A.slots → LogReg Req₂ A.slots → C₁.Coins × C₂.Coins → (X → Y) → Prop) :
    ((A.toKindAlg.composeBothOut (Challenger.sumDummy C₁ C₂ enc) id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v.adv v.chal.logs
          ((SideRelay.dummyRelay (Resp₂ := Resp₂) f enc C₂.Q).logs v.chal.logs)
          v.chal.coins (H.reprogram (A.toKindAlg.postAss _ v.chal))} =
      ∑ s, C₁.coins s *
        (((A.absorb (SideRelay.dummyRelay f enc C₂.Q)).toKindAlg.composeBothOut C₂ id).outLaw
          H).toOuterMeasure
          {o | ∃ v ∈ o, P (A.absorbedAdv (SideRelay.dummyRelay f enc C₂.Q) v.adv)
            v.adv.1.1.1.logs v.chal.logs (s, v.chal.coins)
            (H.reprogram ((A.absorb (SideRelay.dummyRelay f enc C₂.Q)).toKindAlg.postAss C₂
              v.chal))} :=
  A.outLaw_absorb (C := Challenger.sumDummy C₁ C₂ enc) C₁.coins
    (fun _ => SideRelay.dummyRelay (Resp₂ := Resp₂) f enc C₂.Q) (Equiv.refl _)
    (fun s c' => Challenger.coins_sumDummy s c')
    (fun H s c' => (h.relaysChallenger s c').relays H _) (fun _ _ => h.enc_injective) H P

/-- **L1 on events that do not read `C₁`'s coins**: the output law against
`sumDummy C₁ C₂ enc` is the law of `A` absorbed through `dummyRelay f enc C₂.Q` against `C₂`. -/
theorem outLaw_sumDummy_of_main {shA : AlgShape X Y (Req₁ ⊕ R) (Resp₁ ⊕ Resp₂)} (A : AdaptiveIAlg shA O)
    (h : DummyHyps C₁ C₂ enc f) (H : X → Y)
    (P : DReg A.toKindAlg.W A.width X Y (Req₁ ⊕ R) (Resp₁ ⊕ Resp₂) →
      LogReg (Req₁ ⊕ R) A.slots → LogReg Req₂ A.slots → C₂.Coins → (X → Y) → Prop) :
    ((A.toKindAlg.composeBothOut (Challenger.sumDummy C₁ C₂ enc) id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v.adv v.chal.logs
          ((SideRelay.dummyRelay (Resp₂ := Resp₂) f enc C₂.Q).logs v.chal.logs)
          v.chal.coins.2 (H.reprogram (A.toKindAlg.postAss _ v.chal))} =
      (((A.absorb (SideRelay.dummyRelay f enc C₂.Q)).toKindAlg.composeBothOut C₂ id).outLaw
          H).toOuterMeasure
        {o | ∃ v ∈ o, P (A.absorbedAdv (SideRelay.dummyRelay f enc C₂.Q) v.adv)
          v.adv.1.1.1.logs v.chal.logs v.chal.coins
          (H.reprogram ((A.absorb (SideRelay.dummyRelay f enc C₂.Q)).toKindAlg.postAss C₂
            v.chal))} := by
  rw [A.outLaw_sumDummy h H fun adv lg lg' c G => P adv lg lg' c.2 G]
  dsimp only
  rw [← Finset.sum_mul, PMF.sum_coe, one_mul]

end AdaptiveIAlg

namespace QueryBoundedAdversary

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req₁] [DecidableEq Req₁]
  [Fintype Resp₁] [DecidableEq Resp₁] [Fintype R] [DecidableEq R] [Fintype Req₂]
  [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₂] [Nonempty X]
  [AddGroup Y] [Nonempty Y] {O : Type} {t : ℕ} {C₁ : Challenger X Y Req₁ Resp₁}
  {C₂ : Challenger X Y Req₂ Resp₂} {enc : Req₁ ⊕ R → Req₂} {f : Req₁ → Option Resp₁}

/-- **L1 for transcripts** (`transcriptLaw_le_absorbSide` with `C₁`'s coins as side coins): the
transcript of `𝒜` against `sumDummy C₁ C₂ enc` lies in `E` with at most the probability that
the transcript of `𝒜` absorbed through `dummyRelay f enc C₂.Q` against `C₂` lies in `E'`, when
`E'` holds of the output with every history whose requests are the encoded requests of a history
satisfying `E` (`himp`). -/
theorem transcriptLaw_le_sumDummy (𝒜 : QueryBoundedAdversary X Y (Req₁ ⊕ R) (Resp₁ ⊕ Resp₂) O t)
    (h : DummyHyps C₁ C₂ enc f) (H : X → Y)
    (E : O × List (HistoryEntry (Req₁ ⊕ R) (Resp₁ ⊕ Resp₂)) → Prop)
    (E' : O × List (HistoryEntry Req₂ Resp₂) → Prop)
    (himp : ∀ o (hist : List (HistoryEntry (Req₁ ⊕ R) (Resp₁ ⊕ Resp₂)))
      (hist' : List (HistoryEntry Req₂ Resp₂)), E (o, hist) →
        hist'.map HistoryEntry.request = (hist.map HistoryEntry.request).map enc → E' (o, hist')) :
    (𝒜.transcriptLaw (Challenger.sumDummy C₁ C₂ enc) H).toOuterMeasure {x | ∃ p ∈ x, E p} ≤
      ((𝒜.absorbSide C₁.coins (fun _ => SideRelay.dummyRelay (Resp₂ := Resp₂) f enc C₂.Q)
        (fun _ _ => h.enc_injective)).transcriptLaw C₂ H).toOuterMeasure
        {x | ∃ p ∈ x, E' p} :=
  𝒜.transcriptLaw_le_absorbSide C₁.coins (fun _ => SideRelay.dummyRelay (Resp₂ := Resp₂) f enc C₂.Q)
    (Equiv.refl _) (fun s c' => Challenger.coins_sumDummy s c')
    (fun s c' => h.relaysChallenger s c') rfl (fun _ _ => h.enc_injective) H E E'
    fun _ o hist hist' hE hr => himp o hist hist' hE (by
      rw [hr, SideRelay.relayList_dummyRelay])

end QueryBoundedAdversary

/-! ### L2: the left requests as outer requests -/

namespace TwoRelay

/-- **The relay with the left requests as outer requests**: request `x` is sent to the inner
challenger as `enc x`; a left request `r` numbered below `Q` has the outer request `r`, its reply
the outer reply tagged; a right request is answered by the inner reply, tagged, and a left one
numbered `Q` or later by `none`. -/
def dummyTwo (enc : Req₁ ⊕ R → Req₂) (Q : ℕ) :
    TwoRelay (Req₁ ⊕ R) (Resp₁ ⊕ Resp₂) Req₂ Resp₂ Req₁ Resp₁ where
  route₁ _ x := enc x
  answer₁ _ x a := match x with
    | .inl _ => none
    | .inr _ => a.map Sum.inr
  outer c x := match x with
    | .inl r => if c < Q then some r else none
    | .inr _ => none
  answer₂ _ _ b := b.map Sum.inl

/-- **L2: at the outer replies `f`, the relay with outer left requests is `dummyRelay`.** -/
theorem dummyTwo_atC (f : Req₁ → Option Resp₁) (enc : Req₁ ⊕ R → Req₂) (Q : ℕ) :
    (dummyTwo (Resp₂ := Resp₂) enc Q).atC (fun _ q => f q) = SideRelay.dummyRelay f enc Q := by
  simp only [atC, dummyTwo, SideRelay.dummyRelay, SideRelay.mk.injEq, true_and]
  funext c x a
  rcases x with r | q
  · by_cases h : c < Q <;> simp [h]
  · rfl

end TwoRelay

end GordieHowe.Quantum
