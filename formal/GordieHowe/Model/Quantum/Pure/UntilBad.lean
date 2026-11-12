-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.GameTape

@[expose] public section

/-!
# Identical until a bad request, in the pure game

Two environments of the pure game, at tapes `ω` and `ω'`, with the same oracle in force after
every list of requests, whose answers to request number `j < Q` agree whenever the request is not
bad, give final states with the same part on the logs whose first `Q` requests are all good
(`goodLogs Q Bad`). That set of logs is closed for the game: once a bad request is among the first
`Q` requests of a branch it stays there (`Distinguisher.eventPerm_notMem_goodLogs`). This is the
identical-until-bad lemma (Shoup 2004, Lemma 1; Bellare–Rogaway 2006, the fundamental lemma of
game playing) with the bad event a request, chosen in superposition.

- `prob_inter_add_prob_inter_compl`: the probability of `S` is the sum of the probabilities of
  `S ∩ T` and `S ∩ Tᶜ`.
- `goodLogs Q Bad`: the logs whose first `Q` requests all fail `Bad`.
- `Distinguisher.final_congr`: two environments, with any states, giving the same answers and
  oracles in force on every log at their tapes give the same final state.
- `Distinguisher.mask_final_eq_untilBad`: the final states agree on `goodLogs Q Bad`.
- `Distinguisher.prob_inter_goodLogs_eq`: every set of game registers has the same probability
  on those logs; `Distinguisher.prob_badLogs_eq`: the logs with a bad request among the first `Q`
  have the same probability; `Distinguisher.abs_prob_sub_le_untilBad`: every set of game registers
  has probabilities that differ by at most the probability of those bad logs.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

/-- **The probability of `S` splits along `T`**: the probabilities of `S ∩ T` and `S ∩ Tᶜ`. -/
theorem prob_inter_add_prob_inter_compl {ι : Type*} [Fintype ι] (S T : Set ι) (v : QState ι) :
    prob (S ∩ T) v + prob (S ∩ Tᶜ) v = prob S v := by
  classical
  rw [prob, prob, prob, norm_mask_sq, norm_mask_sq, norm_mask_sq, Finset.sum_filter,
    Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT]

/-- **The logs whose first `Q` requests are all good**: no request among the first `Q` logged
requests satisfies `Bad`. -/
def goodLogs {Req : Type*} {m : ℕ} (Q : ℕ) (Bad : Req → Prop) : Set (LogReg Req m) :=
  {lg | ∀ req ∈ (requests lg).take Q, ¬ Bad req}

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} (D : Distinguisher W X Y Req A n m) [DecidableEq Req] [DecidableEq A] [AddGroup Y]
  {Ω Ω' : Type*} {Q : ℕ}

/-- **The final state reads an environment only through its answers and its oracles in force**:
two environments, with any states, giving the same answers and oracles in force on every log at
the tapes `ω` and `ω'` give the same final state. -/
theorem final_congr {St St' : Type _} {Q' : ℕ} [OracleState St X Y] [OracleState St' X Y]
    (E : Env Ω Req A X Y Q St) (E' : Env Ω' Req A X Y Q' St') {ω : Ω} {ω' : Ω'}
    (hA : ∀ (lg : LogReg Req m) k, E.answer ω lg k = E'.answer ω' lg k)
    (hO : ∀ lg : LogReg Req m, E.oracle ω lg = E'.oracle ω' lg)
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)) :
    D.final E post ω = D.final E' post ω' := by
  have hev : ∀ k, D.eventPerm E ω k = D.eventPerm E' ω' k := fun k => by
    unfold eventPerm
    split_ifs with hk
    · have h1 : E.requestPerm (n := n) D.kind ω ⟨k, hk⟩ = E'.requestPerm D.kind ω' ⟨k, hk⟩ := by
        simp only [Env.requestPerm, hA]
      have h2 : E.oraclePerm (n := n) (m := m) D.kind ω = E'.oraclePerm D.kind ω' := by
        simp only [Env.oraclePerm, hO]
      rw [h1, h2]
    · rfl
  have hst : D.run E ω = D.run E' ω' := by
    simp only [run, stage]
    have h := congrArg (fun π => hybrid D.liftedStep (fun k => permOp (π k)) D.gameInit m)
      (funext hev)
    exact h
  simp only [final, hst]
  exact congrArg (fun U => logControlled U (D.run E' ω')) (funext fun lg => by rw [hO lg])

/-- **A bad request among the first `Q` stays there**: on a reachable state whose logs have a bad
request among their first `Q` requests, a slot keeps the logs outside `goodLogs Q Bad`. -/
theorem eventPerm_notMem_goodLogs (E : Env Ω Req A X Y Q) (ω : Ω) (Bad : Req → Prop) {k : ℕ}
    {r : GameReg W n X Y Req A m} (hr : r ∈ logsIn (reachableLogs k))
    (hN : r ∉ logsIn (goodLogs Q Bad)) : D.eventPerm E ω k r ∉ logsIn (goodLogs Q Bad) := by
  simp only [mem_logsIn, goodLogs, Set.mem_ofPred_eq, not_forall, not_not] at hN ⊢
  obtain ⟨req, hreq, hB⟩ := hN
  refine ⟨req, ?_, hB⟩
  rw [D.requests_eventPerm E ω hr]
  split_ifs
  · exact ((List.prefix_append _ _).take Q).subset hreq
  · exact hreq

/-- **Identical until a bad request**: two environments at the tapes `ω` and `ω'` with the same
oracle in force after every list of requests, whose answers to request number `rs.length < Q`
agree whenever the request is not bad, give final states with the same part on the logs whose
first `Q` requests are all good. -/
theorem mask_final_eq_untilBad (E : Env Ω Req A X Y Q) (E' : Env Ω' Req A X Y Q) {ω : Ω}
    {ω' : Ω'} (Bad : Req → Prop) (horacle : ∀ rs, E.oracleIn ω rs = E'.oracleIn ω' rs)
    (hans : ∀ rs req, rs.length < Q → ¬ Bad req →
      E.answerAfter ω rs req = E'.answerAfter ω' rs req)
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)) :
    mask (logsIn (goodLogs Q Bad)) (D.final E post ω) =
      mask (logsIn (goodLogs Q Bad)) (D.final E' post ω') := by
  refine D.mask_final_eq E E' post ?_ fun lg _ => by simp only [Env.oracle, horacle]
  refine D.mask_stage_eq_of_eventPerm E E' _ (fun k r hr hN => ?_)
    (fun k r hr hN himg => ?_) m
  · exact ⟨D.eventPerm_notMem_goodLogs E ω Bad hr hN, D.eventPerm_notMem_goodLogs E' ω' Bad hr hN⟩
  · by_cases hk : k < m
    · refine D.eventPerm_eq_of_agree E E' hr (fun _ => by simp only [Env.oracle, horacle])
        fun hkind => ?_
      by_cases hQ : (requests (splitLogs r).2).length < Q
      · by_cases hB : Bad r.request
        · exfalso
          have hout : ∀ (E₀ : Env Ω Req A X Y Q) (ω₀ : Ω),
              D.eventPerm E₀ ω₀ k r ∉ logsIn (goodLogs Q Bad) := fun E₀ ω₀ => by
            simp only [mem_logsIn, goodLogs, Set.mem_ofPred_eq, not_forall, not_not]
            refine ⟨r.request, ?_, hB⟩
            rw [D.requests_eventPerm E₀ ω₀ hr, if_pos ⟨hkind, hk⟩,
              List.take_of_length_le (by simp; omega)]
            simp
          have hout' : D.eventPerm E' ω' k r ∉ logsIn (goodLogs Q Bad) := by
            simp only [mem_logsIn, goodLogs, Set.mem_ofPred_eq, not_forall, not_not]
            refine ⟨r.request, ?_, hB⟩
            rw [D.requests_eventPerm E' ω' hr, if_pos ⟨hkind, hk⟩,
              List.take_of_length_le (by simp; omega)]
            simp
          rcases himg with h | h
          · exact hout E ω h
          · exact hout' h
        · exact hans _ _ hQ hB
      · simp only [Env.answerAfter, dif_neg hQ]
    · rw [D.eventPerm_of_le E ω (not_lt.1 hk), D.eventPerm_of_le E' ω' (not_lt.1 hk)]

variable (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
  {E : Env Ω Req A X Y Q} {E' : Env Ω' Req A X Y Q} {ω : Ω} {ω' : Ω'} {Bad : Req → Prop}

/-- **Every set of game registers has the same probability on the good logs** under the
hypotheses of `mask_final_eq_untilBad`. -/
theorem prob_inter_goodLogs_eq (horacle : ∀ rs, E.oracleIn ω rs = E'.oracleIn ω' rs)
    (hans : ∀ rs req, rs.length < Q → ¬ Bad req →
      E.answerAfter ω rs req = E'.answerAfter ω' rs req)
    (S : Set (GameReg W n X Y Req A m)) :
    prob (S ∩ logsIn (goodLogs Q Bad)) (D.final E post ω) =
      prob (S ∩ logsIn (goodLogs Q Bad)) (D.final E' post ω') := by
  rw [prob_inter_eq_prob_mask, prob_inter_eq_prob_mask,
    D.mask_final_eq_untilBad E E' Bad horacle hans post]

/-- **The bad logs have the same probability**: the logs with a bad request among their first `Q`
requests, under the hypotheses of `mask_final_eq_untilBad`. -/
theorem prob_badLogs_eq (horacle : ∀ rs, E.oracleIn ω rs = E'.oracleIn ω' rs)
    (hans : ∀ rs req, rs.length < Q → ¬ Bad req →
      E.answerAfter ω rs req = E'.answerAfter ω' rs req) :
    prob (logsIn (goodLogs Q Bad))ᶜ (D.final E post ω) =
      prob (logsIn (goodLogs Q Bad))ᶜ (D.final E' post ω') := by
  have h := D.prob_inter_goodLogs_eq post horacle hans Set.univ
  have h1 := prob_inter_add_prob_inter_compl Set.univ (logsIn (goodLogs Q Bad))
    (D.final E post ω)
  have h2 := prob_inter_add_prob_inter_compl Set.univ (logsIn (goodLogs Q Bad))
    (D.final E' post ω')
  rw [prob_univ, D.norm_final] at h1
  rw [prob_univ, D.norm_final] at h2
  simp only [Set.univ_inter] at h h1 h2
  linarith

/-- **Identical until bad, as a bound**: under the hypotheses of `mask_final_eq_untilBad`, the
probabilities of every set of game registers differ by at most the probability of the bad logs. -/
theorem abs_prob_sub_le_untilBad (horacle : ∀ rs, E.oracleIn ω rs = E'.oracleIn ω' rs)
    (hans : ∀ rs req, rs.length < Q → ¬ Bad req →
      E.answerAfter ω rs req = E'.answerAfter ω' rs req)
    (S : Set (GameReg W n X Y Req A m)) :
    |prob S (D.final E post ω) - prob S (D.final E' post ω')| ≤
      prob (logsIn (goodLogs Q Bad))ᶜ (D.final E post ω) := by
  have hg := D.prob_inter_goodLogs_eq post horacle hans S
  have hb := D.prob_badLogs_eq post horacle hans
  have h1 := prob_inter_add_prob_inter_compl S (logsIn (goodLogs Q Bad)) (D.final E post ω)
  have h2 := prob_inter_add_prob_inter_compl S (logsIn (goodLogs Q Bad)) (D.final E' post ω')
  have m1 := prob_inter_add_prob_inter_compl (logsIn (goodLogs Q Bad))ᶜ S (D.final E post ω)
  have m2 := prob_inter_add_prob_inter_compl (logsIn (goodLogs Q Bad))ᶜ S (D.final E' post ω')
  have e1 : (logsIn (goodLogs Q Bad))ᶜ ∩ S = S ∩ (logsIn (W := W) (n := n) (X := X) (Y := Y)
      (A := A) (goodLogs Q Bad))ᶜ := Set.inter_comm _ _
  rw [e1] at m1 m2
  have n1 := prob_nonneg ((logsIn (W := W) (n := n) (X := X) (Y := Y) (A := A)
    (goodLogs Q Bad))ᶜ ∩ Sᶜ) (D.final E post ω)
  have n2 := prob_nonneg ((logsIn (W := W) (n := n) (X := X) (Y := Y) (A := A)
    (goodLogs Q Bad))ᶜ ∩ Sᶜ) (D.final E' post ω')
  have p1 := prob_nonneg (S ∩ (logsIn (W := W) (n := n) (X := X) (Y := Y) (A := A)
    (goodLogs Q Bad))ᶜ) (D.final E post ω)
  have p2 := prob_nonneg (S ∩ (logsIn (W := W) (n := n) (X := X) (Y := Y) (A := A)
    (goodLogs Q Bad))ᶜ) (D.final E' post ω')
  rw [abs_le]
  constructor <;> linarith

end Distinguisher

end GordieHowe.Quantum
