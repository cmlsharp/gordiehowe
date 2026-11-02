-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.HistoryLogs
public import GordieHowe.Model.Quantum.Interactive.UntilBad
public import GordieHowe.Model.Quantum.Interactive.TPRun

@[expose] public section

/-!
# Identical until a bad request, in the ring-signature games

Two families of challengers answering request by request (`Challenger.AnswersBy`), with the
same number of requests and coin laws matched by an equivalence of the coins, whose responses
agree on every request that is not bad, give the same law to every event "output in `E` and no bad
request in the history", and the same probability to "a bad request in the history". So the
advantage of every output event between the two runs is at most the probability of a bad request
in the history (`RingSignature.gameAdvantage_runLaw_le_untilBad`). This is the identical-until-bad
lemma (Shoup 2004, Lemma 1; Bellare–Rogaway 2006, the fundamental lemma of game playing) with the
bad event a request of a quantum adversary; the step on the pure game is
`GordieHowe/Model/Quantum/Pure/UntilBad.lean`.

- `PMF.toOuterMeasure_inter_add_diff`: an event splits along another.
  `PMF.toOuterMeasure_some_add_some_add_none`: the events "some value satisfies `P`", "some value
  fails `P`" and `none` of a law on `Option α` have total probability `1`.
- `Challenger.histLogs_not_exists_request`: the logs whose history has no bad entry are
  `goodLogs Q Bad`.
- `QueryBoundedAdversary.transcriptLaw_none_eq_zero`: a `t`-query adversary terminates with probability
  `1`.
- `QueryBoundedAdversary.transcriptLaw_outGood_eq`, `QueryBoundedAdversary.transcriptLaw_bad_eq`:
  at a fixed oracle, the events "output in `E`, no bad request in the history" and "a bad request in
  the history" have the same probabilities against the two challengers.
- `RingSignature.RunBad Bad` (with `RingSignature.RunOutIn E` of
  `GordieHowe/Model/RingSignature/Adversary.lean`): the run's events "terminates with an
  output in `E`" and "terminates with a bad request in its history", the badness of a request
  depending on the start draw and the oracle. `RingSignature.toOuterMeasure_runLaw`: an event of the
  run's law as the average of its sections.
- `RingSignature.runLaw_outGood_eq`, `RingSignature.runLaw_bad_eq`,
  `RingSignature.gameAdvantage_runLaw_le_untilBad`: the game forms.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe

/-! ### Splitting the probability of an event -/

/-- **An event splits along another**: the probabilities of `s ∩ t` and `s \ t` add up to that of
`s`. -/
theorem PMF.toOuterMeasure_inter_add_diff {α : Type*} (p : PMF α) (s t : Set α) :
    p.toOuterMeasure (s ∩ t) + p.toOuterMeasure (s \ t) = p.toOuterMeasure s := by
  classical
  simp only [PMF.toOuterMeasure_apply]
  rw [← ENNReal.tsum_add]
  refine tsum_congr fun x => ?_
  by_cases hs : x ∈ s <;> by_cases ht : x ∈ t <;> simp [Set.indicator, hs, ht]

/-- **A law on `Option α` splits along a predicate**: the probabilities that the value is some `a`
with `P a`, some `a` with `¬ P a`, and `none` add up to `1`. -/
theorem PMF.toOuterMeasure_some_add_some_add_none {α : Type*} (p : PMF (Option α)) (P : α → Prop) :
    p.toOuterMeasure {x | ∃ a ∈ x, P a} + p.toOuterMeasure {x | ∃ a ∈ x, ¬ P a} + p none = 1 := by
  classical
  rw [← PMF.toOuterMeasure_apply_singleton, ← p.tsum_coe]
  simp only [PMF.toOuterMeasure_apply]
  rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine tsum_congr fun x => ?_
  rcases x with _ | a
  · simp [Set.indicator]
  · by_cases hP : P a <;> simp [Set.indicator, hP]

namespace Quantum

/-! ### The good logs as a log set of a history predicate -/

/-- **The logs whose history has no bad entry** are the logs whose first `Q` requests are all
good. -/
theorem Challenger.histLogs_not_exists_request {Coins X Y Req Resp : Type}
    (resp : Coins → (X → Y) → ℕ → Req → Option Resp) (Q : ℕ) (c : Coins) (H : X → Y)
    (Bad : Req → Prop) {m : ℕ} :
    Challenger.histLogs resp Q c H (fun h => ¬ ∃ e ∈ h, Bad e.request) =
      goodLogs (m := m) Q Bad := by
  ext lg
  have h := Set.ext_iff.1 (Challenger.histLogs_exists_request resp Q c H Bad (m := m)) lg
  simp only [Challenger.histLogs, Set.mem_ofPred_eq] at h ⊢
  rw [h]
  simp [goodLogs]

/-! ### At a fixed oracle -/

namespace QueryBoundedAdversary

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {t : ℕ} (𝒜 : QueryBoundedAdversary X Y Req Resp O t)

/-- **A `t`-query adversary terminates with probability `1`**: its transcript law gives `none`
probability `0` (`AdaptiveIAlg.WithinBudget.outLaw_compose_none`). -/
theorem transcriptLaw_none_eq_zero (C : Challenger X Y Req Resp) (H : X → Y) :
    𝒜.transcriptLaw C H none = 0 := by
  have hs : ({none} : Set (Option (O × List (HistoryEntry Req Resp)))) =
      Option.map Prod.fst ⁻¹' {none} := by
    ext x
    rcases x with _ | ⟨o, l⟩ <;> simp
  rw [← PMF.toOuterMeasure_apply_singleton, hs, ← PMF.toOuterMeasure_map_apply,
    map_transcriptLaw_fst, PMF.toOuterMeasure_bind_apply]
  refine ENNReal.tsum_eq_zero.2 fun a => ?_
  rw [PMF.toOuterMeasure_apply_singleton, (𝒜.withinBudget a).outLaw_compose_none C H, mul_zero]

variable {C C' : Challenger X Y Req Resp} {resp : C.Coins → (X → Y) → ℕ → Req → Option Resp}
  {resp' : C'.Coins → (X → Y) → ℕ → Req → Option Resp}

/-- **Identical until a bad request, at a fixed oracle: the good outputs.** For two challengers
answering request by request (`resp`, `resp'`), answering the same number of requests, with an
equivalence `e` of their coins carrying the coin law of `C` to that of `C'`, whose responses at the
oracle `H` to request number `j < Q` agree whenever the request is not bad, the adversary
terminates with an output in `E` and no bad request in its history with the same probability
against both. -/
theorem transcriptLaw_outGood_eq (h : C.AnswersBy resp) (h' : C'.AnswersBy resp')
    (hQ : C'.Q = C.Q) (e : C.Coins ≃ C'.Coins) (he : ∀ c, C'.coins (e c) = C.coins c) (H : X → Y)
    (Bad : Req → Prop)
    (hagree : ∀ c j req, j < C.Q → ¬ Bad req → resp' (e c) H j req = resp c H j req)
    (E : Set O) :
    (𝒜.transcriptLaw C H).toOuterMeasure {x | ∃ p ∈ x, p.1 ∈ E ∧ ¬ ∃ e ∈ p.2, Bad e.request} =
      (𝒜.transcriptLaw C' H).toOuterMeasure
        {x | ∃ p ∈ x, p.1 ∈ E ∧ ¬ ∃ e ∈ p.2, Bad e.request} := by
  rw [𝒜.transcriptLaw_outHist C h H E (fun l => ¬ ∃ e ∈ l, Bad e.request),
    𝒜.transcriptLaw_outHist C' h' H E (fun l => ¬ ∃ e ∈ l, Bad e.request)]
  refine tsum_congr fun a => ?_
  congr 2
  rw [← e.sum_comp]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hg : ∀ {m : ℕ}, goodLogs (Req := Req) (m := m) C'.Q Bad = goodLogs C.Q Bad := by
    intro m
    rw [hQ]
  rw [he, Challenger.histLogs_not_exists_request, Challenger.histLogs_not_exists_request, hg]
  exact congrArg _ (Challenger.AnswersBy.prob_inter_goodLogs_eq (𝒜.alg a).runDil noPost h h' hQ
    (hagree c) ((𝒜.alg a).outAcc E))

/-- **Identical until a bad request, at a fixed oracle: the bad histories.** Under the hypotheses
of `transcriptLaw_outGood_eq`, the adversary terminates with a bad request in its history with the
same probability against both challengers. -/
theorem transcriptLaw_bad_eq (h : C.AnswersBy resp) (h' : C'.AnswersBy resp')
    (hQ : C'.Q = C.Q) (e : C.Coins ≃ C'.Coins) (he : ∀ c, C'.coins (e c) = C.coins c) (H : X → Y)
    (Bad : Req → Prop)
    (hagree : ∀ c j req, j < C.Q → ¬ Bad req → resp' (e c) H j req = resp c H j req) :
    (𝒜.transcriptLaw C H).toOuterMeasure {x | ∃ p ∈ x, ∃ e ∈ p.2, Bad e.request} =
      (𝒜.transcriptLaw C' H).toOuterMeasure {x | ∃ p ∈ x, ∃ e ∈ p.2, Bad e.request} := by
  have hs : {x : Option (O × List (HistoryEntry Req Resp)) |
      ∃ p ∈ x, p.1 ∈ (Set.univ : Set O) ∧ ¬ ∃ e ∈ p.2, Bad e.request} =
      {x | ∃ p ∈ x, ¬ ∃ e ∈ p.2, Bad e.request} := by
    ext x
    simp
  have hg := 𝒜.transcriptLaw_outGood_eq h h' hQ e he H Bad hagree Set.univ
  rw [hs] at hg
  have p1 := PMF.toOuterMeasure_some_add_some_add_none (𝒜.transcriptLaw C H)
    (fun p => ∃ e ∈ p.2, Bad e.request)
  have p2 := PMF.toOuterMeasure_some_add_some_add_none (𝒜.transcriptLaw C' H)
    (fun p => ∃ e ∈ p.2, Bad e.request)
  rw [𝒜.transcriptLaw_none_eq_zero, add_zero] at p1 p2
  rw [hg, ← p2] at p1
  have hne : (𝒜.transcriptLaw C' H).toOuterMeasure {x | ∃ p ∈ x, ¬ ∃ e ∈ p.2, Bad e.request} ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one _ _)
  exact (ENNReal.add_left_inj hne).1 p1

end QueryBoundedAdversary

end Quantum

/-! ### The game forms -/

namespace RingSignature

open Quantum

variable {X Y Req Resp O K : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {t : ℕ} [Fintype K] [Nonempty K]

/-- **The run terminates with a bad request in its history**, the badness of a request depending
on the start draw and the oracle. -/
def RunBad (Bad : K → (X → Y) → Req → Prop) :
    Set (K × (X → Y) × Option (O × List (HistoryEntry Req Resp))) :=
  {x | ∃ p ∈ x.2.2, ∃ h ∈ p.2, Bad x.1 x.2.1 h.request}

/-- **An event of the run's law** is the average, over the start draw and the oracle, of the
transcript law's probability of its section. -/
theorem toOuterMeasure_runLaw (A : K → (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (C : K → Challenger X Y Req Resp)
    (S : Set (K × (X → Y) × Option (O × List (HistoryEntry Req Resp)))) :
    (runLaw A C).toOuterMeasure S =
      ∑' k, PMF.uniformOfFintype K k * ∑' H, PMF.uniformOfFintype (X → Y) H *
        ((A k H).transcriptLaw (C k) H).toOuterMeasure {x | (k, H, x) ∈ S} := by
  rw [runLaw, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun k => ?_
  rw [PMF.toOuterMeasure_bind_apply]
  congr 1
  refine tsum_congr fun H => ?_
  rw [PMF.toOuterMeasure_map_apply]
  rfl

variable {A : K → (X → Y) → QueryBoundedAdversary X Y Req Resp O t}
  {C C' : K → Challenger X Y Req Resp}
  {resp : ∀ k, (C k).Coins → (X → Y) → ℕ → Req → Option Resp}
  {resp' : ∀ k, (C' k).Coins → (X → Y) → ℕ → Req → Option Resp}

/-- **Identical until a bad request: the good outputs.** For two families of challengers
answering request by request (`resp k`, `resp' k`), answering the same number of requests, with
equivalences `e k` of their coins carrying the coin laws of `C k` to those of `C' k`, whose
responses to request number `j < Q` agree whenever the request is not bad (`Bad k H`), the run
terminates with an output in `E` and no bad request in its history with the same probability
against both. -/
theorem runLaw_outGood_eq (hC : ∀ k, (C k).AnswersBy (resp k)) (hC' : ∀ k, (C' k).AnswersBy (resp' k))
    (hQ : ∀ k, (C' k).Q = (C k).Q) (e : ∀ k, (C k).Coins ≃ (C' k).Coins)
    (he : ∀ k c, (C' k).coins (e k c) = (C k).coins c) (Bad : K → (X → Y) → Req → Prop)
    (hagree : ∀ k c H j req, j < (C k).Q → ¬ Bad k H req →
      resp' k (e k c) H j req = resp k c H j req)
    (E : Set O) :
    (runLaw A C).toOuterMeasure (RunOutIn E \ RunBad Bad) =
      (runLaw A C').toOuterMeasure (RunOutIn E \ RunBad Bad) := by
  rw [toOuterMeasure_runLaw, toOuterMeasure_runLaw]
  refine tsum_congr fun k => ?_
  congr 1
  refine tsum_congr fun H => ?_
  congr 1
  have hs : {x : Option (O × List (HistoryEntry Req Resp)) | (k, H, x) ∈ RunOutIn E \ RunBad Bad} =
      {x | ∃ p ∈ x, p.1 ∈ E ∧ ¬ ∃ e ∈ p.2, Bad k H e.request} := by
    ext x
    rcases x with _ | ⟨o, l⟩ <;> simp [RunOutIn, RunBad]
  rw [hs]
  exact (A k H).transcriptLaw_outGood_eq (hC k) (hC' k) (hQ k) (e k) (he k) H (Bad k H)
    (fun c => hagree k c H) E

/-- **Identical until a bad request: the bad histories** have the same probability, under the
hypotheses of `runLaw_outGood_eq`. -/
theorem runLaw_bad_eq (hC : ∀ k, (C k).AnswersBy (resp k)) (hC' : ∀ k, (C' k).AnswersBy (resp' k))
    (hQ : ∀ k, (C' k).Q = (C k).Q) (e : ∀ k, (C k).Coins ≃ (C' k).Coins)
    (he : ∀ k c, (C' k).coins (e k c) = (C k).coins c) (Bad : K → (X → Y) → Req → Prop)
    (hagree : ∀ k c H j req, j < (C k).Q → ¬ Bad k H req →
      resp' k (e k c) H j req = resp k c H j req) :
    (runLaw A C).toOuterMeasure (RunBad (O := O) Bad) =
      (runLaw A C').toOuterMeasure (RunBad Bad) := by
  rw [toOuterMeasure_runLaw, toOuterMeasure_runLaw]
  refine tsum_congr fun k => ?_
  congr 1
  refine tsum_congr fun H => ?_
  congr 1
  exact (A k H).transcriptLaw_bad_eq (hC k) (hC' k) (hQ k) (e k) (he k) H (Bad k H)
    (fun c => hagree k c H)

/-- **Identical until a bad request, the game bound**: under the hypotheses of
`runLaw_outGood_eq`, the advantage between the two runs of the event "terminates with an output
in `E`" is at most the probability, under `C'`, that the run terminates with a bad request in its
history (equal to that under `C`, `runLaw_bad_eq`). -/
theorem gameAdvantage_runLaw_le_untilBad (hC : ∀ k, (C k).AnswersBy (resp k))
    (hC' : ∀ k, (C' k).AnswersBy (resp' k)) (hQ : ∀ k, (C' k).Q = (C k).Q)
    (e : ∀ k, (C k).Coins ≃ (C' k).Coins) (he : ∀ k c, (C' k).coins (e k c) = (C k).coins c)
    (Bad : K → (X → Y) → Req → Prop)
    (hagree : ∀ k c H j req, j < (C k).Q → ¬ Bad k H req →
      resp' k (e k c) H j req = resp k c H j req)
    (E : Set O) :
    gameAdvantage (runLaw A C) (runLaw A C') (RunOutIn E) ≤
      ((runLaw A C').toOuterMeasure (RunBad Bad)).toReal := by
  have hg := runLaw_outGood_eq (A := A) hC hC' hQ e he Bad hagree E
  have hb := runLaw_bad_eq (A := A) hC hC' hQ e he Bad hagree
  have s1 := PMF.toOuterMeasure_inter_add_diff (runLaw A C) (RunOutIn E) (RunBad Bad)
  have s2 := PMF.toOuterMeasure_inter_add_diff (runLaw A C') (RunOutIn E) (RunBad Bad)
  have m1 : (runLaw A C).toOuterMeasure (RunOutIn E ∩ RunBad Bad) ≤
      (runLaw A C).toOuterMeasure (RunBad Bad) :=
    (runLaw A C).toOuterMeasure.mono Set.inter_subset_right
  have m2 : (runLaw A C').toOuterMeasure (RunOutIn E ∩ RunBad Bad) ≤
      (runLaw A C').toOuterMeasure (RunBad Bad) :=
    (runLaw A C').toOuterMeasure.mono Set.inter_subset_right
  have fin : ∀ (μ : PMF (K × (X → Y) × Option (O × List (HistoryEntry Req Resp)))) S,
      μ.toOuterMeasure S ≠ ∞ := fun μ S =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one _ _)
  rw [← hb] at m2
  rw [← hb]
  simp only [gameAdvantage, advantage, Set.ofPred]
  change |((runLaw A C).toOuterMeasure (RunOutIn E)).toReal -
      ((runLaw A C').toOuterMeasure (RunOutIn E)).toReal| ≤ _
  rw [← s1, ← s2, hg, ENNReal.toReal_add (fin _ _) (fin _ _),
    ENNReal.toReal_add (fin _ _) (fin _ _)]
  have r1 := (ENNReal.toReal_le_toReal (fin _ _) (fin _ _)).2 m1
  have r2 := (ENNReal.toReal_le_toReal (fin _ _) (fin _ _)).2 m2
  have n1 := ENNReal.toReal_nonneg (a := (runLaw A C).toOuterMeasure (RunOutIn E ∩ RunBad Bad))
  have n2 := ENNReal.toReal_nonneg (a := (runLaw A C').toOuterMeasure (RunOutIn E ∩ RunBad Bad))
  rw [abs_le]
  constructor <;> linarith

end RingSignature

end GordieHowe
