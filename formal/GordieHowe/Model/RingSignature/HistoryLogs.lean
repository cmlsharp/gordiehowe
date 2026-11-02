-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.Transcript
public import GordieHowe.Model.Quantum.Interactive.SaltReprogram
public import GordieHowe.Model.Quantum.Interactive.SplitHybrid

@[expose] public section

/-!
# Events of the output and the history as pure games

For a challenger that answers request by request (`Challenger.AnswersBy resp`), the history of a
run is read off the logs: its entries are the first `min (|requests|, Q)` logged requests with the
responses `resp c H j req`. So an event of the run's output and history under the transcript law
(`QueryBoundedAdversary.transcriptLaw`) is the coin average of the probability, in the final state
of the pure game of the dilated adversary without a final unitary, of a register set
(running branch, output in `E`) intersected with a set of logs that depends on the coins and the
oracle.

- `Challenger.ansHist resp Q c H rs`: the history of the requests `rs` answered by `resp`: the
  first `Q` requests, request number `j` with the response `resp c H j req`.
  `Challenger.ansHist_append_singleton`: one request more.
  `Challenger.AnswersBy.hist`: the history of the pure game's challenger state.
- `Challenger.histLogs resp Q c H F`: the logs whose history satisfies `F`.
  `Challenger.histLogs_exists_request`: for the predicate "an entry's request satisfies `B`", the
  logs one of whose first `Q` requests satisfies `B`, independent of `resp`, `c` and `H`.
  `Challenger.extLogs_preimage_histLogs`: the log set is unchanged by blank slots appended.
- `AdaptiveIAlg.runDil`: the dilated adversary with its post phase as query slots and its output
  forgotten (`AdaptiveIAlg.pureDil` of `mapOut`), a distinguisher with no final unitary;
  `AdaptiveIAlg.runDilBudget`: its budget of `budget + post` query slots.
  `AdaptiveIAlg.outAcc E`: its basis states on a running branch with the adversary's output in
  `E`.
- `AdaptiveIAlg.toOuterMeasure_outLaw_compose_hist`: at the oracle `H`, the composition's output
  lies in `E` and its history satisfies `F` with the coin average of
  `prob (outAcc E ∩ logsIn (histLogs resp Q c H F)) (runDil.final C.toPureEnv noPost (H, c))`.
- `QueryBoundedAdversary.transcriptLaw_outHist`: the same for the transcript law, averaged over
  the auxiliary input. `QueryBoundedAdversary.transcriptLaw_histHas`: the special case "the history
  has an entry whose request satisfies `B`", with no output condition.

The proof composes `KindAlg.toOuterMeasure_outLaw_composeBothOut_id` (`Interactive/Absorb.lean`),
`KindAlg.prob_final_dilate` (`Interactive/SplitHybrid.lean`) and
`Distinguisher.final_withPostSlots` (`Pure/PostSlots.lean`).
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

/-! ### The history of a challenger answering request by request -/

namespace Challenger

section AnsHist

variable {Coins X Y Req Resp : Type} (resp : Coins → (X → Y) → ℕ → Req → Option Resp) (Q : ℕ)
  (c : Coins) (H : X → Y)

/-- **The history of the requests `rs` answered by `resp`**: the first `Q` requests, request number
`j` with request `req` paired with the response `resp c H j req`. -/
def ansHist (rs : List Req) : List (HistoryEntry Req Resp) :=
  (rs.take Q).mapIdx fun j req => ⟨req, resp c H j req⟩

/-- **The history of one request more**: the request, numbered `rs.length`, is appended when
`rs.length < Q`. -/
theorem ansHist_append_singleton (rs : List Req) (req : Req) :
    ansHist resp Q c H (rs ++ [req]) =
      if rs.length < Q then ansHist resp Q c H rs ++ [⟨req, resp c H rs.length req⟩]
      else ansHist resp Q c H rs := by
  unfold ansHist
  split_ifs with h
  · rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by omega),
      List.mapIdx_append]
    simp
  · rw [List.take_append_of_le_length (by omega)]

/-- The logs whose history, answered by `resp`, satisfies `F`. -/
def histLogs (F : List (HistoryEntry Req Resp) → Prop) {m : ℕ} : Set (LogReg Req m) :=
  {lg | F (ansHist resp Q c H (requests lg))}

/-- **The logs one of whose first `Q` requests satisfies `B`** are the logs whose history has an
entry whose request satisfies `B`. -/
theorem histLogs_exists_request (B : Req → Prop) {m : ℕ} :
    histLogs resp Q c H (fun h => ∃ e ∈ h, B e.request) =
      {lg : LogReg Req m | ∃ req ∈ (requests lg).take Q, B req} := by
  ext lg
  simp only [histLogs, ansHist, Set.mem_ofPred_eq, List.mem_mapIdx]
  constructor
  · rintro ⟨e, ⟨j, hj, rfl⟩, hB⟩
    exact ⟨_, List.getElem_mem hj, hB⟩
  · rintro ⟨req, hreq, hB⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hreq
    exact ⟨_, ⟨j, hj, rfl⟩, hB⟩

/-- **Blank slots appended to the logs** leave the log set of a history predicate unchanged. -/
theorem extLogs_preimage_histLogs (F : List (HistoryEntry Req Resp) → Prop) {m : ℕ} (b : ℕ) :
    extLogs b ⁻¹' histLogs resp Q c H F (m := m + b) = histLogs resp Q c H F (m := m) := by
  ext lg
  simp only [histLogs, Set.mem_preimage, Set.mem_ofPred_eq, requests_extLogs]

end AnsHist

variable {X Y Req Resp : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  {C : Challenger X Y Req Resp} {resp : C.Coins → (X → Y) → ℕ → Req → Option Resp}

/-- **The history of the pure game's challenger** answering request by request is the history of
the requests answered by `resp` (`ansHist`). -/
theorem AnswersBy.hist (h : C.AnswersBy resp) (ω : (X → Y) × C.Coins) (rs : List Req) :
    (C.toPureEnv.oracleIn ω rs).hist = ansHist resp C.Q ω.2 ω.1 rs := by
  induction rs using List.reverseRecOn with
  | nil => simp [Env.oracleIn_nil, toPureEnv, ansHist]
  | append_singleton rs req ih =>
    rw [ansHist_append_singleton, Env.oracleIn_append_singleton, Env.update]
    split_ifs with hq
    · obtain ⟨hb, ha, hl⟩ := h.oracleIn ω rs
      set s := C.toPureEnv.oracleIn ω rs
      have hl' : s.hist.length = rs.length := by
        rw [hl]
        exact min_eq_left hq.le
      have hrun : (C.respond ω.2 s.hist req).run (s.base.reprogram s.ass) =
          ⟨resp ω.2 ω.1 rs.length req, []⟩ := by
        rw [hb, ha, ← hl']
        exact h _ _ _ _ (hl'.trans_lt hq)
      change s.hist ++ [⟨req, ((C.respond ω.2 s.hist req).run (s.base.reprogram s.ass)).response⟩] = _
      rw [hrun, ih]
    · exact ih

end Challenger

/-! ### The dilated adversary with its output forgotten -/

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O)

/-- **The dilated adversary as a distinguisher without a final unitary, its output forgotten**:
`pureDil` of the adversary with its output mapped to `()`. -/
noncomputable def runDil :=
  (A.mapOut fun _ => ()).pureDil ()

/-- **The dilated adversary has a budget of `budget + post` query slots.** -/
noncomputable def runDilBudget : A.runDil.Budget (A.budget + A.post) :=
  (A.mapOut fun _ => ()).pureDilBudget ()

/-- **The running branches with the adversary's output in `E`**: the basis states of `runDil`
with the flag of the post slots set, the halting flag clear and the output read from the
workspace in `E`. -/
def outAcc (E : Set O) :=
  embR (W := (A.mapOut fun _ => ()).toKindAlg.DW) (n := (A.mapOut fun _ => ()).toKindAlg.width)
    (X := X) (Y := Y) (Req := Req) (A := Resp) (m := (A.mapOut fun _ => ()).toKindAlg.slots)
    (A.mapOut fun _ => ()).toKindAlg.post true ''
      (A.mapOut fun _ => ()).toKindAlg.dilSet {r | A.out r.1.1.1 ∈ E}

/-- **An event of the composition's output and history as a pure game**: for a challenger
answering request by request (`Challenger.AnswersBy resp`), at the oracle `H` the composition
terminates with an output in `E` and a history satisfying `F` with the coin average of the
probability of the running branches with output in `E` (`outAcc E`) and logs whose history
satisfies `F` (`Challenger.histLogs`) in the final state of `runDil` against the challenger's pure
game at the tape `(H, c)`. -/
theorem toOuterMeasure_outLaw_compose_hist (C : Challenger X Y Req Resp)
    {resp : C.Coins → (X → Y) → ℕ → Req → Option Resp} (h : C.AnswersBy resp) (H : X → Y)
    (E : Set O) (F : List (HistoryEntry Req Resp) → Prop) :
    ((A.toKindAlg.composeBothOut C fun v => (A.output C v, A.history C v)).outLaw H).toOuterMeasure
        {x | ∃ p ∈ x, p.1 ∈ E ∧ F p.2} =
      ENNReal.ofReal (∑ c, (C.coins c).toReal *
        prob (A.outAcc E ∩ logsIn (Challenger.histLogs resp C.Q c H F))
          (A.runDil.final C.toPureEnv noPost (H, c))) := by
  classical
  have hmap : (A.toKindAlg.composeBothOut C fun v => (A.output C v, A.history C v)).outLaw H =
      ((A.toKindAlg.composeBothOut C id).outLaw H).map
        (Option.map fun v => (A.output C v, A.history C v)) := by
    simp only [Alg.outLaw]
    rw [PMF.map_comp, Option.map_comp_map]
    rfl
  have hset : (Option.map fun v => (A.output C v, A.history C v)) ⁻¹'
      {x : Option (O × List (HistoryEntry Req Resp)) | ∃ p ∈ x, p.1 ∈ E ∧ F p.2} =
      {o | ∃ v ∈ o, A.output C v ∈ E ∧ F (A.history C v)} := by
    ext x
    rcases x with _ | v <;> simp
  rw [hmap, PMF.toOuterMeasure_map_apply, hset,
    KindAlg.toOuterMeasure_outLaw_composeBothOut_id A.toKindAlg C H
      (fun v => A.output C v ∈ E ∧ F (A.history C v))]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  set B := (A.mapOut fun _ => ()).toKindAlg
  set T : Set B.G := {r | A.out r.1.1.1 ∈ E ∧
    (splitLogs r).2 ∈ Challenger.histLogs resp C.Q c H F (m := A.slots)}
  have hpost : B.postOp = fun H => Distinguisher.postN
      (fun j => B.uStepD (B.slots + 1 + j)) H B.post :=
    funext fun H => B.postOpN_eq_postN H _
  have hpre : embR (W := B.DW) (n := B.width) (X := X) (Y := Y) (Req := Req) (A := Resp)
      (m := B.slots) B.post true ⁻¹'
      (A.outAcc E ∩ logsIn (Challenger.histLogs resp C.Q c H F)) = B.dilSet T := by
    rw [Set.preimage_inter, outAcc, Set.preimage_image_eq _ (embR_injective _ true)]
    ext x
    change _ ∧ extLogs A.post (splitLogs x).2 ∈ Challenger.histLogs resp C.Q c H F ↔ _
    rw [← Set.mem_preimage, Challenger.extLogs_preimage_histLogs]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
  rw [runDil, pureDil, Distinguisher.final_withPostSlots, prob_embV (embR_injective _ true), hpre,
    ← hpost]
  refine Eq.trans ?_ (B.prob_final_dilate C.toPureEnv () T (H, c)).symm
  refine Finset.sum_congr rfl fun r _ => ?_
  have hd : (A.toKindAlg.mgRun C.toPureEnv (H, c) true r r) =
      (A.toKindAlg.mgRun C.toPureEnv (H, c) false r r) := by
    rw [A.toKindAlg.mgRun_deph, dephase_apply_self]
  rw [hd]
  have hhist : A.history C (A.toKindAlg.emb C H c A.toKindAlg.slots r).1 =
      Challenger.ansHist resp C.Q c H (requests (splitLogs r).2) := by
    change (C.regState c (splitLogs r).2 (A.toKindAlg.ansOf C ⟨(splitLogs r).2,
      A.toKindAlg.garFill C H c (splitLogs r).2 A.toKindAlg.slots, c⟩) A.toKindAlg.slots).history = _
    rw [A.toKindAlg.regState_eq C H c (splitLogs r).2 A.toKindAlg.slots le_rfl]
    exact h.hist (H, c) _
  have hiff : (A.output C (A.toKindAlg.emb C H c A.toKindAlg.slots r).1 ∈ E ∧
      F (A.history C (A.toKindAlg.emb C H c A.toKindAlg.slots r).1)) ↔ r ∈ T := by
    rw [hhist]
    exact Iff.rfl
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (hiff.1 h1) h2
  · exact absurd (hiff.2 h2) h1
  · rfl

end AdaptiveIAlg

/-! ### Events of the transcript law -/

namespace QueryBoundedAdversary

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {t : ℕ}

/-- **An event of the output and the history under the transcript law as a pure game**: for a
challenger answering request by request, at the oracle `H` the adversary terminates with an output
in `E` and a history satisfying `F` with the average over the auxiliary input `a` and the coins
`c` of the probability of `outAcc E ∩ logsIn (histLogs resp Q c H F)` in the final state of the
dilated adversary `runDil` (budget `budget + post`, no final unitary) against the challenger's
pure game at the tape `(H, c)`. -/
theorem transcriptLaw_outHist (𝒜 : QueryBoundedAdversary X Y Req Resp O t)
    (C : Challenger X Y Req Resp) {resp : C.Coins → (X → Y) → ℕ → Req → Option Resp}
    (h : C.AnswersBy resp) (H : X → Y) (E : Set O) (F : List (HistoryEntry Req Resp) → Prop) :
    (𝒜.transcriptLaw C H).toOuterMeasure {x | ∃ p ∈ x, p.1 ∈ E ∧ F p.2} =
      ∑' a, 𝒜.aux a * ENNReal.ofReal (∑ c, (C.coins c).toReal *
        prob ((𝒜.alg a).outAcc E ∩ logsIn (Challenger.histLogs resp C.Q c H F))
          ((𝒜.alg a).runDil.final C.toPureEnv noPost (H, c))) := by
  rw [transcriptLaw, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun a => ?_
  rw [(𝒜.alg a).toOuterMeasure_outLaw_compose_hist C h H E F]

/-- **The history has an entry whose request satisfies `B`**, with no output condition, as a pure
game: the average over the auxiliary input and the coins of the probability of the running
branches (`outAcc univ`) whose logs have one of their first `Q` requests satisfying `B`. -/
theorem transcriptLaw_histHas (𝒜 : QueryBoundedAdversary X Y Req Resp O t)
    (C : Challenger X Y Req Resp) {resp : C.Coins → (X → Y) → ℕ → Req → Option Resp}
    (h : C.AnswersBy resp) (H : X → Y) (B : Req → Prop) :
    (𝒜.transcriptLaw C H).toOuterMeasure {x | ∃ p ∈ x, ∃ e ∈ p.2, B e.request} =
      ∑' a, 𝒜.aux a * ENNReal.ofReal (∑ c, (C.coins c).toReal *
        prob ((𝒜.alg a).outAcc Set.univ ∩
            logsIn {lg | ∃ req ∈ (requests lg).take C.Q, B req})
          ((𝒜.alg a).runDil.final C.toPureEnv noPost (H, c))) := by
  have hs : {x : Option (O × List (HistoryEntry Req Resp)) | ∃ p ∈ x, ∃ e ∈ p.2, B e.request} =
      {x | ∃ p ∈ x, p.1 ∈ Set.univ ∧ (fun h => ∃ e ∈ h, B e.request) p.2} := by
    ext x
    simp
  rw [hs, 𝒜.transcriptLaw_outHist C h H Set.univ (fun h => ∃ e ∈ h, B e.request)]
  simp only [Challenger.histLogs_exists_request]

end QueryBoundedAdversary

end GordieHowe.Quantum
