-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.Adversary
public import GordieHowe.Model.Quantum.Interactive.ClassicalSim
public import GordieHowe.Model.Quantum.Interactive.AbsorbBudget
public import GordieHowe.Model.Quantum.Interactive.AbsorbTranscript
public import GordieHowe.Model.Quantum.Interactive.ThenProgOut

@[expose] public section

/-!
# Events of the transcript law

Events of the adversary's output under `Quantum.QueryBoundedAdversary.transcriptLaw`
(`GordieHowe/Model/RingSignature/Adversary.lean`), as output laws of the composed algorithm and
as events of the classical simulation (`GordieHowe/Model/Quantum/Interactive/ClassicalSim.lean`).

- `AdaptiveIAlg.mapOut`, `AdaptiveIAlg.outLaw_compose_mapOut`: the adversary with its output read
  through a function; its output law is that of the composition's transcript, mapped. Its shape
  is the adversary's (`mapOut_toShape`).
- `QueryBoundedAdversary.OutIn E`: the adversary terminates with an output in `E`.
  `QueryBoundedAdversary.transcriptLaw_out_mem`: its probability is the output `true` of the
  adversary whose output is the event, averaged over the auxiliary input.
- `QueryBoundedAdversary.map_transcriptLaw_fst`: the output part of the transcript law is the
  output law of the composition, averaged over the auxiliary input.
  `QueryBoundedAdversary.toOuterMeasure_transcriptLaw_fst`: hence the probability that the
  transcript's output is `o`.
- `QueryBoundedAdversary.toOuterMeasure_transcriptLaw_outIn`,
  `QueryBoundedAdversary.transcriptLaw_none`: at every oracle `H`, the output events and the
  non-termination of the transcript law have the probabilities of the corresponding events of the
  adversary's classical strategy (`KindAlg.classicalSim`) against the challenger at `H`, averaged
  over the auxiliary input.
- `AdaptiveIAlg.mapOut_tracePreserving`, `AdaptiveIAlg.mapOut_withinBudget`,
  `QueryBoundedAdversary.mapOut`: a `t`-query adversary with its output read through a map.
- `Challenger.oracleIn_toPureEnv_map`, `answer_toPureEnv_map`, `oracle_toPureEnv_map`,
  `KindAlg.toOuterMeasure_outLaw_map`: challengers whose replies run alike along a map of their
  coins give the composition the same law on events of the adversary's registers and the logs;
  `QueryBoundedAdversary.transcriptLaw_requests_congr`: the same events of the output and the
  answered requests under the transcript law.
- `QueryBoundedAdversary.transcriptLaw_eq_tsum_test`: against a challenger that reprograms
  nothing, a transcript event of the output's first part and the answered requests is the
  acceptance of a classical test at the final oracle, for the adversary with the rest of its
  output dropped.
-/

namespace GordieHowe

open GordieHowe.Quantum
open scoped ENNReal

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]

namespace Quantum.AdaptiveIAlg

/-- **The adversary with its output read through `g`**: the same steps, workspace and budget;
the output `g (out w)`. -/
def mapOut {O' : Type} {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (g : O → O') :
    AdaptiveIAlg shA O' :=
  { A with out := g ∘ A.out }

/-- **The adversary with its output read through `g` has its shape.** -/
theorem mapOut_toShape {O' : Type} {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (g : O → O') :
    (A.mapOut g).toShape = A.toShape :=
  rfl

variable [Nonempty X] [AddGroup Y] [Nonempty Y]

/-- **The output law of the adversary with its output read through `g`** is the law of the
composition's transcript (output and history), mapped by `g` of the output. -/
theorem outLaw_compose_mapOut {O' : Type} {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (g : O → O')
    (C : Challenger X Y Req Resp) (H : X → Y) :
    ((A.mapOut g).compose C).outLaw H =
      ((A.toKindAlg.composeBothOut C fun v => (A.output C v, A.history C v)).outLaw H).map
        (Option.map fun p => g p.1) := by
  simp only [Alg.outLaw]
  rw [PMF.map_comp, Option.map_comp_map]
  rfl

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
/-- Reading the output through a map keeps trace preservation. -/
theorem mapOut_tracePreserving {O' : Type} {shA : AlgShape X Y Req Resp} {A : AdaptiveIAlg shA O} (h : A.TracePreserving)
    (f : O → O') : (A.mapOut f).TracePreserving :=
  h

/-- Reading the output through a map keeps the budget. -/
theorem mapOut_withinBudget {O' : Type} {shA : AlgShape X Y Req Resp} {A : AdaptiveIAlg shA O} (h : A.WithinBudget)
    (f : O → O') : (A.mapOut f).WithinBudget := by
  rw [withinBudget_iff] at h ⊢
  intro C H
  have h' := h C H
  rw [outLaw_compose_none_eq] at h' ⊢
  exact h'

end Quantum.AdaptiveIAlg

namespace Quantum.Challenger

variable [Nonempty Y]

omit [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] in
/-- **Challengers whose replies run alike along a map of their coins have the same states**: after
every request list, at the coins `c` and `π c`. -/
theorem oracleIn_toPureEnv_map {C C' : Challenger X Y Req Resp} (π : C.Coins → C'.Coins)
    (hQ : C.Q = C'.Q)
    (hrun : ∀ c hist r G, (C.respond c hist r).run G = (C'.respond (π c) hist r).run G)
    (H : X → Y) (c : C.Coins) :
    ∀ rs : List Req, C.toPureEnv.oracleIn (H, c) rs = C'.toPureEnv.oracleIn (H, π c) rs := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs r ih =>
    rw [Env.oracleIn_append_singleton, Env.oracleIn_append_singleton, ih]
    simp only [Env.update, hQ]
    split_ifs
    · simp only [toPureEnv, hrun]
    · rfl

omit [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] in
/-- Challengers whose replies run alike along a map of their coins give the same answers. -/
theorem answer_toPureEnv_map {C C' : Challenger X Y Req Resp} (π : C.Coins → C'.Coins)
    (hQ : C.Q = C'.Q)
    (hrun : ∀ c hist r G, (C.respond c hist r).run G = (C'.respond (π c) hist r).run G)
    (H : X → Y) (c : C.Coins) {m : ℕ} (lg : LogReg Req m) (k : Fin m) :
    C.toPureEnv.answer (H, c) lg k = C'.toPureEnv.answer (H, π c) lg k := by
  unfold Env.answer Env.answerAfter
  cases lg k with
  | none => rfl
  | some r =>
    simp only [Option.elim, oracleIn_toPureEnv_map π hQ hrun H c, hQ]
    split_ifs
    · simp only [toPureEnv, hrun]
    · rfl

omit [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] in
/-- Challengers whose replies run alike along a map of their coins have the same oracles in
force. -/
theorem oracle_toPureEnv_map {C C' : Challenger X Y Req Resp} (π : C.Coins → C'.Coins)
    (hQ : C.Q = C'.Q)
    (hrun : ∀ c hist r G, (C.respond c hist r).run G = (C'.respond (π c) hist r).run G)
    (H : X → Y) (c : C.Coins) {m : ℕ} (lg : LogReg Req m) :
    C.toPureEnv.oracle (H, c) lg = C'.toPureEnv.oracle (H, π c) lg := by
  unfold Env.oracle
  rw [oracleIn_toPureEnv_map π hQ hrun H c]

omit [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] in
/-- **Challengers that never reprogram and whose replies run alike at the oracle `H`** along a map
of their coins have the same states after every request list, at the coins `c` and `π c`. -/
theorem oracleIn_toPureEnv_map_at {C C' : Challenger X Y Req Resp} (π : C.Coins → C'.Coins)
    (hQ : C.Q = C'.Q) (hNA' : C'.NoAssign) (H : X → Y)
    (hrun : ∀ c hist r, (C.respond c hist r).run H = (C'.respond (π c) hist r).run H)
    (c : C.Coins) :
    ∀ rs : List Req, C.toPureEnv.oracleIn (H, c) rs = C'.toPureEnv.oracleIn (H, π c) rs := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs r ih =>
    obtain ⟨hb, ha, -⟩ := hNA'.oracleIn H (π c) rs
    rw [Env.oracleIn_append_singleton, Env.oracleIn_append_singleton, ih]
    by_cases hq : rs.length < C.Q
    · rw [C.update_toPureEnv_of_lt _ _ _ hq, C'.update_toPureEnv_of_lt _ _ _ (hQ ▸ hq), hb, ha,
        show H.reprogram ([] : List (Assignment X Y)) = H from rfl, hrun]
    · rw [C.update_toPureEnv_of_le _ _ _ (not_lt.1 hq),
        C'.update_toPureEnv_of_le _ _ _ (hQ ▸ not_lt.1 hq)]

omit [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] in
/-- Challengers that never reprogram and whose replies run alike at `H` give the same replies after
every request list. -/
theorem answerAfter_toPureEnv_map_at {C C' : Challenger X Y Req Resp} (π : C.Coins → C'.Coins)
    (hQ : C.Q = C'.Q) (hNA' : C'.NoAssign) (H : X → Y)
    (hrun : ∀ c hist r, (C.respond c hist r).run H = (C'.respond (π c) hist r).run H)
    (c : C.Coins) (rs : List Req) (r : Req) :
    C.toPureEnv.answerAfter (H, c) rs r = C'.toPureEnv.answerAfter (H, π c) rs r := by
  by_cases hq : rs.length < C.Q
  · obtain ⟨hb, ha, -⟩ := hNA'.oracleIn H (π c) rs
    rw [C.answerAfter_toPureEnv_of_lt _ _ _ hq, C'.answerAfter_toPureEnv_of_lt _ _ _ (hQ ▸ hq),
      oracleIn_toPureEnv_map_at π hQ hNA' H hrun c, hb, ha,
      show H.reprogram ([] : List (Assignment X Y)) = H from rfl, hrun]
  · rw [C.answerAfter_toPureEnv_of_le _ _ _ (not_lt.1 hq),
      C'.answerAfter_toPureEnv_of_le _ _ _ (hQ ▸ not_lt.1 hq)]

omit [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] in
/-- Challengers that never reprogram and whose replies run alike at `H` give the same answers. -/
theorem answer_toPureEnv_map_at {C C' : Challenger X Y Req Resp} (π : C.Coins → C'.Coins)
    (hQ : C.Q = C'.Q) (hNA' : C'.NoAssign) (H : X → Y)
    (hrun : ∀ c hist r, (C.respond c hist r).run H = (C'.respond (π c) hist r).run H)
    (c : C.Coins) {m : ℕ} (lg : LogReg Req m) (k : Fin m) :
    C.toPureEnv.answer (H, c) lg k = C'.toPureEnv.answer (H, π c) lg k := by
  unfold Env.answer
  cases lg k with
  | none => rfl
  | some r =>
    simp only [Option.elim]
    by_cases hq : (requestsBefore lg k).length < C.Q
    · obtain ⟨hb, ha, -⟩ := hNA'.oracleIn H (π c) (requestsBefore lg k)
      rw [C.answerAfter_toPureEnv_of_lt _ _ _ hq, C'.answerAfter_toPureEnv_of_lt _ _ _ (hQ ▸ hq),
        oracleIn_toPureEnv_map_at π hQ hNA' H hrun c, hb, ha,
        show H.reprogram ([] : List (Assignment X Y)) = H from rfl, hrun]
    · rw [C.answerAfter_toPureEnv_of_le _ _ _ (not_lt.1 hq),
        C'.answerAfter_toPureEnv_of_le _ _ _ (hQ ▸ not_lt.1 hq)]

omit [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] in
/-- Challengers that never reprogram and whose replies run alike at `H` have the same oracles in
force. -/
theorem oracle_toPureEnv_map_at {C C' : Challenger X Y Req Resp} (π : C.Coins → C'.Coins)
    (hQ : C.Q = C'.Q) (hNA' : C'.NoAssign) (H : X → Y)
    (hrun : ∀ c hist r, (C.respond c hist r).run H = (C'.respond (π c) hist r).run H)
    (c : C.Coins) {m : ℕ} (lg : LogReg Req m) :
    C.toPureEnv.oracle (H, c) lg = C'.toPureEnv.oracle (H, π c) lg := by
  unfold Env.oracle
  rw [oracleIn_toPureEnv_map_at π hQ hNA' H hrun c]

end Quantum.Challenger

namespace Quantum.KindAlg

variable [Nonempty X] [AddGroup Y] [Nonempty Y] {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O)

/-- **Challengers with the same answers and oracles along a map of their coins** at the oracle `H`
(`hans`, `hor`), whose coin laws are related by `π` (`hcoins`), give the composition the same law
on events `P` and `P'` of the composed registers that agree at the placed registers of each basis
state (`hP`). -/
theorem toOuterMeasure_outLaw_congr_emb {C C' : Challenger X Y Req Resp} (π : C.Coins → C'.Coins)
    (hcoins : C.coins.map π = C'.coins) (H : X → Y)
    (hans : ∀ c {m : ℕ} (lg : LogReg Req m) (k : Fin m),
      C.toPureEnv.answer (H, c) lg k = C'.toPureEnv.answer (H, π c) lg k)
    (hor : ∀ c {m : ℕ} (lg : LogReg Req m),
      C.toPureEnv.oracle (H, c) lg = C'.toPureEnv.oracle (H, π c) lg)
    (P : B.CW C → Prop) (P' : B.CW C' → Prop)
    (hP : ∀ c r, P (B.emb C H c B.slots r).1 ↔ P' (B.emb C' H (π c) B.slots r).1) :
    ((B.composeBothOut C id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P v} =
      ((B.composeBothOut C' id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P' v} := by
  classical
  rw [B.toOuterMeasure_outLaw_composeBothOut_id C H, B.toOuterMeasure_outLaw_composeBothOut_id C' H]
  congr 1
  set g : C'.Coins → ℝ := fun c' => ∑ r : B.G,
    if P' (B.emb C' H c' B.slots r).1
    then (B.mgRun C'.toPureEnv (H, c') true r r).re else 0 with hg
  have hterm : ∀ c, (∑ r : B.G,
      if P (B.emb C H c B.slots r).1
      then (B.mgRun C.toPureEnv (H, c) true r r).re else 0) = g (π c) := by
    intro c
    have hm : B.mgRun C.toPureEnv (H, c) true = B.mgRun C'.toPureEnv (H, π c) true :=
      B.mgRun_congr _ _ (fun lg k => hans c lg k) (fun lg => hor c lg) true
    simp only [hg, hm]
    exact Finset.sum_congr rfl fun r _ => if_congr (hP c r) rfl rfl
  simp only [hterm]
  rw [← hcoins]
  have hfib : ∀ c', (C.coins.map π c').toReal =
      ∑ c, if π c = c' then (C.coins c).toReal else 0 := by
    intro c'
    rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum fun c _ => by
      split_ifs <;> simp [PMF.apply_ne_top]]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases h : c' = π c
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg fun h' => h h'.symm, ENNReal.toReal_zero]
  simp only [hfib, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_eq_single (π c) (fun c' _ hc' => by rw [if_neg fun h => hc' h.symm, zero_mul])
    (fun h => absurd (Finset.mem_univ _) h), if_pos rfl]

/-- **Challengers with the same answers and oracles along a map of their coins** at the oracle `H`
(`hans`, `hor`), whose coin laws are related by `π` (`hcoins`), give the composition the same law
on every event of the adversary's registers and the logs. -/
theorem toOuterMeasure_outLaw_map_of {C C' : Challenger X Y Req Resp} (π : C.Coins → C'.Coins)
    (hcoins : C.coins.map π = C'.coins) (H : X → Y)
    (hans : ∀ c {m : ℕ} (lg : LogReg Req m) (k : Fin m),
      C.toPureEnv.answer (H, c) lg k = C'.toPureEnv.answer (H, π c) lg k)
    (hor : ∀ c {m : ℕ} (lg : LogReg Req m),
      C.toPureEnv.oracle (H, c) lg = C'.toPureEnv.oracle (H, π c) lg)
    (P : DReg B.W B.width X Y Req Resp → LogReg Req B.slots → Prop) :
    ((B.composeBothOut C id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P v.adv v.chal.logs} =
      ((B.composeBothOut C' id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P v.adv v.chal.logs} :=
  B.toOuterMeasure_outLaw_congr_emb π hcoins H hans hor _ _ fun _ _ => Iff.rfl

/-- **A challenger read through a map of its coins**: two challengers that answer the same number of
requests, whose reply programs run alike along a map `π` of the coins and whose coin laws are
related by `π` (`hcoins`), give the composition the same law on every event of the adversary's
registers and the logs. -/
theorem toOuterMeasure_outLaw_map {C C' : Challenger X Y Req Resp} (π : C.Coins → C'.Coins)
    (hcoins : C.coins.map π = C'.coins) (hQ : C.Q = C'.Q)
    (hrun : ∀ c hist r G, (C.respond c hist r).run G = (C'.respond (π c) hist r).run G)
    (H : X → Y) (P : DReg B.W B.width X Y Req Resp → LogReg Req B.slots → Prop) :
    ((B.composeBothOut C id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P v.adv v.chal.logs} =
      ((B.composeBothOut C' id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P v.adv v.chal.logs} :=
  B.toOuterMeasure_outLaw_map_of π hcoins H
    (fun c _ lg k => Challenger.answer_toPureEnv_map π hQ hrun H c lg k)
    (fun c _ lg => Challenger.oracle_toPureEnv_map π hQ hrun H c lg) P

end Quantum.KindAlg

variable [Nonempty X] [AddGroup Y] [Nonempty Y] {t : ℕ}

namespace Quantum.QueryBoundedAdversary

/-- The event that the adversary terminates with an output in `E`. -/
def OutIn (E : Set O) : Set (Option (O × List (HistoryEntry Req Resp))) :=
  {x | ∃ p ∈ x, p.1 ∈ E}

open Classical in
/-- **An event of the output under the transcript law** is the output `true` of the adversary
whose output is the event, averaged over the auxiliary input. -/
theorem transcriptLaw_out_mem (𝒜 : QueryBoundedAdversary X Y Req Resp O t)
    (C : Challenger X Y Req Resp) (H : X → Y) (E : Set O) :
    (𝒜.transcriptLaw C H).toOuterMeasure (OutIn E) =
      ∑' a, 𝒜.aux a *
        (((𝒜.alg a).mapOut fun o => decide (o ∈ E)).compose C).outLaw H (some true) := by
  rw [transcriptLaw, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun a => ?_
  congr 1
  rw [AdaptiveIAlg.outLaw_compose_mapOut, ← PMF.toOuterMeasure_apply_singleton,
    PMF.toOuterMeasure_map_apply]
  congr 1
  ext x
  rcases x with _ | ⟨o, h⟩ <;> simp [OutIn]


/-- **The output part of the transcript law** is the output law of the composition, averaged
over the auxiliary input. -/
theorem map_transcriptLaw_fst (𝒜 : QueryBoundedAdversary X Y Req Resp O t)
    (C : Challenger X Y Req Resp) (H : X → Y) :
    (𝒜.transcriptLaw C H).map (Option.map Prod.fst) =
      𝒜.aux.bind fun a => ((𝒜.alg a).compose C).outLaw H := by
  rw [transcriptLaw, PMF.map_bind]
  congr 1
  funext a
  simp only [Alg.outLaw]
  rw [PMF.map_comp, Option.map_comp_map]
  rfl

/-- **The transcript's output is `o`** with the average, over the auxiliary input, of the
probability that the composition outputs `o` (`map_transcriptLaw_fst` at the event `{some o}`). -/
theorem toOuterMeasure_transcriptLaw_fst (𝒜 : QueryBoundedAdversary X Y Req Resp O t)
    (C : Challenger X Y Req Resp) (H : X → Y) (o : O) :
    (𝒜.transcriptLaw C H).toOuterMeasure {x | ∃ p ∈ x, p.1 = o} =
      ∑' a, 𝒜.aux a * ((𝒜.alg a).compose C).outLaw H (some o) := by
  have hs : {x : Option (O × List (HistoryEntry Req Resp)) | ∃ p ∈ x, p.1 = o} =
      Option.map Prod.fst ⁻¹' {some o} := by
    ext x
    rcases x with _ | ⟨o', l⟩ <;> simp
  rw [hs, ← PMF.toOuterMeasure_map_apply, map_transcriptLaw_fst, PMF.toOuterMeasure_bind_apply]
  simp only [PMF.toOuterMeasure_apply_singleton]

/-- **Output events of the transcript law in the classical simulation**: at every oracle `H`,
the adversary terminates with an output in `E` with the probability that its classical strategy
outputs an element of `E` against the challenger at `H`, averaged over the auxiliary input. -/
theorem toOuterMeasure_transcriptLaw_outIn [DecidableEq O]
    (𝒜 : QueryBoundedAdversary X Y Req Resp O t) (C : Challenger X Y Req Resp) (H : X → Y)
    (E : Set O) :
    (𝒜.transcriptLaw C H).toOuterMeasure (OutIn E) =
      ∑' a, 𝒜.aux a * (Interaction.exper (𝒜.alg a).toKindAlg.classicalSim (C.classicalAt H)
        (𝒜.alg a).slots).toOuterMeasure {p | ∃ o ∈ p.2, o ∈ E} := by
  have hset : (OutIn E : Set (Option (O × List (HistoryEntry Req Resp)))) =
      Option.map Prod.fst ⁻¹' {x | ∃ o ∈ x, o ∈ E} := by
    ext x
    rcases x with _ | ⟨o, h⟩ <;> simp [OutIn]
  rw [hset, ← PMF.toOuterMeasure_map_apply, map_transcriptLaw_fst,
    PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun a => ?_
  rw [AdaptiveIAlg.toOuterMeasure_outLaw_compose]
  rfl

/-- **Non-termination under the transcript law in the classical simulation**: at every oracle
`H`, the adversary fails to terminate with the probability that its classical strategy outputs
`none` against the challenger at `H`, averaged over the auxiliary input. -/
theorem transcriptLaw_none [DecidableEq O] (𝒜 : QueryBoundedAdversary X Y Req Resp O t)
    (C : Challenger X Y Req Resp) (H : X → Y) :
    𝒜.transcriptLaw C H none =
      ∑' a, 𝒜.aux a * (Interaction.exper (𝒜.alg a).toKindAlg.classicalSim (C.classicalAt H)
        (𝒜.alg a).slots).toOuterMeasure {p | p.2 = none} := by
  have hset : ({none} : Set (Option (O × List (HistoryEntry Req Resp)))) =
      Option.map Prod.fst ⁻¹' {none} := by
    ext x
    rcases x with _ | ⟨o, h⟩ <;> simp
  rw [← PMF.toOuterMeasure_apply_singleton, hset, ← PMF.toOuterMeasure_map_apply,
    map_transcriptLaw_fst, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun a => ?_
  rw [PMF.toOuterMeasure_apply_singleton, AdaptiveIAlg.outLaw_compose_none_eq_exper]

/-- **The `t`-query adversary with its output read through `g`** (`AdaptiveIAlg.mapOut` at every
auxiliary value). -/
def mapOut {O' : Type} (𝒜 : QueryBoundedAdversary X Y Req Resp O t) (g : O → O') :
    QueryBoundedAdversary X Y Req Resp O' t where
  Aux := 𝒜.Aux
  aux := 𝒜.aux
  sh a := 𝒜.sh a
  alg a := (𝒜.alg a).mapOut g
  tracePreserving a := 𝒜.tracePreserving a
  withinBudget a := AdaptiveIAlg.mapOut_withinBudget (𝒜.withinBudget a) g
  queries_le a := 𝒜.queries_le a

/-- The shape of the adversary with its output read through `g` is `𝒜`'s. -/
@[simp] theorem mapOut_sh {O' : Type} (𝒜 : QueryBoundedAdversary X Y Req Resp O t) (g : O → O')
    (a : 𝒜.Aux) : (𝒜.mapOut g).sh a = 𝒜.sh a :=
  rfl

/-- **A transcript event of the output's first part and the answered requests as a test at the
final oracle**: against a challenger that reprograms nothing, the probability that the output
`(o, _)` and the answered requests satisfy `W` is the average over the auxiliary input of the
probability that the adversary with output `o` passes a test `test` of `o` and its logged
requests at the final oracle in force, when the test at `H` accepts exactly on `W` at the first
`C.Q` logged requests (`htest`). -/
theorem transcriptLaw_eq_tsum_test {T : Type} (𝒜 : QueryBoundedAdversary X Y Req Resp (O × T) t)
    {C : Challenger X Y Req Resp} (hC : C.NoAssign) (H : X → Y) (W : O → List Req → Prop)
    (test : O → List Req → OracleProg X Y Bool)
    (htest : ∀ o rs, (test o rs).run H = true ↔ W o (rs.take C.Q)) :
    (𝒜.transcriptLaw C H).toOuterMeasure {x | ∃ p ∈ x, W p.1.1 (p.2.map HistoryEntry.request)} =
      ∑' a, (𝒜.mapOut Prod.fst).aux a *
        ((((𝒜.mapOut Prod.fst).alg a).toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
          {o | ∃ v ∈ o, (test (((𝒜.mapOut Prod.fst).alg a).out v.adv.workspace.1)
            (Quantum.requests v.chal.logs)).run
              (H.reprogram (((𝒜.mapOut Prod.fst).alg a).toKindAlg.postAss C v.chal)) = true} := by
  classical
  simp only [transcriptLaw, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun a => congrArg _ ?_
  refine (AdaptiveIAlg.toOuterMeasure_outLaw_comp (𝒜.alg a) C id
      (fun v => ((𝒜.alg a).output C v, (𝒜.alg a).history C v)) H
      fun p => W p.1.1 (p.2.map HistoryEntry.request)).symm.trans ?_
  change _ = (((𝒜.alg a).toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
    {o | ∃ v ∈ o, (test ((𝒜.alg a).out v.adv.workspace.1).1 (Quantum.requests v.chal.logs)).run
      (H.reprogram ((𝒜.alg a).toKindAlg.postAss C v.chal)) = true}
  set P₁ : (𝒜.alg a).toKindAlg.CW C → Prop := fun v =>
    W ((𝒜.alg a).output C v).1 (((𝒜.alg a).history C v).map HistoryEntry.request)
  set P₂ : (𝒜.alg a).toKindAlg.CW C → Prop := fun v =>
    (test ((𝒜.alg a).out v.adv.workspace.1).1 (Quantum.requests v.chal.logs)).run
      (H.reprogram ((𝒜.alg a).toKindAlg.postAss C v.chal)) = true
  have hcomp : ∀ P : (𝒜.alg a).toKindAlg.CW C → Prop,
      (((𝒜.alg a).toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P v} =
      (((𝒜.alg a).toKindAlg.composeBothOut C fun v => P v).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, v} := fun P =>
    AdaptiveIAlg.toOuterMeasure_outLaw_comp (𝒜.alg a) C id (fun v => P v) H id
  change (((𝒜.alg a).toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
      {o | ∃ v ∈ o, P₁ v} = (((𝒜.alg a).toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
      {o | ∃ v ∈ o, P₂ v}
  rw [hcomp P₁, hcomp P₂]
  refine congrArg (fun μ : PMF (Option Prop) => μ.toOuterMeasure {o | ∃ v ∈ o, v})
    (KindAlg.outLaw_composeBothOut_congr_emb _ C H fun c r => ?_)
  simp only [P₁, P₂, KindAlg.reprogram_postAss_emb_of_noAssign _ hC, htest,
    AdaptiveIAlg.map_request_history]
  rfl

/-- **Challengers whose replies run alike give the same transcript events of requests**: two
challengers answering the same number of requests, whose reply programs run alike along a map
`π` of the coins and whose coin laws are related by `π`, give every event of the output and the
answered requests the same probability. -/
theorem transcriptLaw_requests_congr {C C' : Challenger X Y Req Resp} (π : C.Coins → C'.Coins)
    (hcoins : C.coins.map π = C'.coins) (hQ : C.Q = C'.Q)
    (hrun : ∀ c hist r G, (C.respond c hist r).run G = (C'.respond (π c) hist r).run G)
    (𝒜 : QueryBoundedAdversary X Y Req Resp O t) (H : X → Y) (E : O × List Req → Prop) :
    (𝒜.transcriptLaw C H).toOuterMeasure {x | ∃ p ∈ x, E (p.1, p.2.map HistoryEntry.request)} =
      (𝒜.transcriptLaw C' H).toOuterMeasure
        {x | ∃ p ∈ x, E (p.1, p.2.map HistoryEntry.request)} := by
  simp only [transcriptLaw, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun a => congrArg _ ?_
  have key : ∀ C₀ : Challenger X Y Req Resp,
      (((𝒜.alg a).toKindAlg.composeBothOut C₀ fun v =>
        ((𝒜.alg a).output C₀ v, (𝒜.alg a).history C₀ v)).outLaw H).toOuterMeasure
        {x | ∃ p ∈ x, E (p.1, p.2.map HistoryEntry.request)} =
      (((𝒜.alg a).toKindAlg.composeBothOut C₀ id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, E ((𝒜.alg a).toKindAlg.out v.adv.workspace,
          (requests v.chal.logs).take C₀.Q)} := by
    intro C₀
    refine (AdaptiveIAlg.toOuterMeasure_outLaw_comp (𝒜.alg a) C₀ id
      (fun v => ((𝒜.alg a).output C₀ v, (𝒜.alg a).history C₀ v)) H
      fun p => E (p.1, p.2.map HistoryEntry.request)).symm.trans ?_
    refine congrArg _ (Set.ext fun x => ?_)
    simp only [Set.mem_ofPred_eq, AdaptiveIAlg.map_request_history]
    rfl
  rw [key C, key C', ← hQ]
  exact KindAlg.toOuterMeasure_outLaw_map _ π hcoins hQ hrun H
    fun adv lg => E ((𝒜.alg a).toKindAlg.out adv.workspace, (requests lg).take C.Q)

end Quantum.QueryBoundedAdversary

end GordieHowe
