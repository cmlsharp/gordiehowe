-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.O2H.Game
public import GordieHowe.Foundations.ToMathlib.PMFTV
public import GordieHowe.Foundations.ToMathlib.PMFUniform

@[expose] public section

/-!
# Changing the tape of a game

Three ways to compare two environments of the game of `GordieHowe/Model/Quantum/Pure/Game.lean`, used by the hybrids
of zero-knowledge proofs. Each is stated for the acceptance probability on the logs in a set `L`
(`Distinguisher.acceptProbOn`), and the whole acceptance probability is the case `L = univ`.

- `Distinguisher.acceptProbOnAt_eq_of_agree`: on two tapes where the environments have the same
  initial oracle and the same responses, the game accepts with the same probability.
  `Distinguisher.acceptProbOn_comap` is the relabelling form: if the tape law of `E'` is the image
  of the tape law of `E` under `f` (a measure-preserving map of tapes), and `E'` at `f ω` agrees
  with `E` at `ω`, the acceptance probabilities are equal.
- `Distinguisher.abs_acceptProbOn_sub_le_of_eq_off`: two environments with the same tape law that
  agree outside an event `B` of tapes are distinguished with advantage at most the probability of
  `B` (the "identical until bad" lemma for a bad event of the tape). It uses
  `0 ≤ acceptProbOnAt ≤ 1`.
- `Distinguisher.abs_acceptProbOn_sub_le_of_kernel`: **kernel replacement at one request.** The
  tape is `(v, τ)` with `τ` drawn independently of `v`, and only request number `j` reads `τ`. If,
  for each `v`, each logged request and each oracle in force before request `j`, the laws of the
  response and the new oracle under `τ ← ν` and `τ' ← ν'` are within `ε v` in total variation,
  the games are distinguished with advantage at most the average of `ε v`. The request is chosen
  by the distinguisher after its queries, in superposition, and so is the slot at which it is
  made; the bound holds because the log of a request never changes afterwards, so the final
  acceptance probability is a sum over the logged values of terms that each depend on `τ` only
  through that request's response kernel.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

namespace Env

variable {Ω Ω' Req A X Y : Type*} {Q : ℕ} {E : Env Ω Req A X Y Q} {E' : Env Ω' Req A X Y Q}
  {ω : Ω} {ω' : Ω'}

/-- Two environments with the same initial oracle and responses on two tapes compute the same
oracles. -/
theorem oracleIn_eq_of_agree (h0 : E.oracle₀ ω = E'.oracle₀ ω')
    (hr : E.respond ω = E'.respond ω') (rs : List Req) : E.oracleIn ω rs = E'.oracleIn ω' rs := by
  have hu : E.update ω = E'.update ω' := by
    funext H p
    simp only [update, hr]
  simp only [oracleIn, hu, h0]

theorem answerAfter_eq_of_agree (h0 : E.oracle₀ ω = E'.oracle₀ ω')
    (hr : E.respond ω = E'.respond ω') (rs : List Req) (req : Req) :
    E.answerAfter ω rs req = E'.answerAfter ω' rs req := by
  simp only [answerAfter, oracleIn_eq_of_agree h0 hr, hr]

theorem oracle_eq_of_agree {m : ℕ} (h0 : E.oracle₀ ω = E'.oracle₀ ω')
    (hr : E.respond ω = E'.respond ω') (lg : LogReg Req m) : E.oracle ω lg = E'.oracle ω' lg :=
  oracleIn_eq_of_agree h0 hr _

theorem answer_eq_of_agree {m : ℕ} (h0 : E.oracle₀ ω = E'.oracle₀ ω')
    (hr : E.respond ω = E'.respond ω') (lg : LogReg Req m) (k : Fin m) :
    E.answer ω lg k = E'.answer ω' lg k := by
  unfold answer
  rw [show E.answerAfter ω (requestsBefore lg k) = E'.answerAfter ω' (requestsBefore lg k) from
    funext (answerAfter_eq_of_agree h0 hr _)]

end Env

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} (D : Distinguisher W X Y Req A n m) [DecidableEq Req] [DecidableEq A] [AddGroup Y]
  {Q : ℕ} (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))

section Agree

variable {Ω Ω' : Type*} {E : Env Ω Req A X Y Q} {E' : Env Ω' Req A X Y Q}

/-- **Agreeing environments.** On two tapes where the environments have the same initial oracle
and the same responses, the game has the same final state. -/
theorem final_eq_of_agree {ω : Ω} {ω' : Ω'} (h0 : E.oracle₀ ω = E'.oracle₀ ω')
    (hr : E.respond ω = E'.respond ω') : D.final E post ω = D.final E' post ω' := by
  have hev : ∀ k, D.eventPerm E ω k = D.eventPerm E' ω' k := fun k => by
    unfold eventPerm Env.oraclePerm Env.requestPerm
    simp only [Env.oracle_eq_of_agree h0 hr, Env.answer_eq_of_agree h0 hr]
  simp only [final, run, stage, hev, Env.oracle_eq_of_agree h0 hr]

theorem acceptProbOnAt_eq_of_agree {ω : Ω} {ω' : Ω'} (h0 : E.oracle₀ ω = E'.oracle₀ ω')
    (hr : E.respond ω = E'.respond ω') (L : Set (LogReg Req m)) :
    D.acceptProbOnAt E post L ω = D.acceptProbOnAt E' post L ω' := by
  rw [acceptProbOnAt, acceptProbOnAt, D.final_eq_of_agree post h0 hr]

theorem acceptProbOnAt_nonneg (E : Env Ω Req A X Y Q) (L : Set (LogReg Req m)) (ω : Ω) :
    0 ≤ D.acceptProbOnAt E post L ω :=
  prob_nonneg _ _

/-- The final state of the game is a unit vector. -/
theorem norm_final (E : Env Ω Req A X Y Q) (ω : Ω) : ‖D.final E post ω‖ = 1 := by
  rw [final, LinearIsometryEquiv.norm_map, run, stage, norm_hybrid, D.norm_gameInit]

theorem acceptProbOnAt_le_one (E : Env Ω Req A X Y Q) (L : Set (LogReg Req m)) (ω : Ω) :
    D.acceptProbOnAt E post L ω ≤ 1 := by
  rw [acceptProbOnAt, prob, show (1 : ℝ) = ‖D.final E post ω‖ ^ 2 by
    rw [D.norm_final post E ω, one_pow]]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_mask_le _ _) 2

variable [Fintype Ω] [Fintype Ω']

/-- **Relabelling the tape.** If the tape law of `E'` is the image of the tape law of `E` under
`f`, and `E'` at `f ω` has the initial oracle and the responses of `E` at `ω`, the two games
accept with the same probability on every set of logs. -/
theorem acceptProbOn_comap (f : Ω → Ω') (hμ : E'.μ = E.μ.map f)
    (h0 : ∀ ω, E.oracle₀ ω = E'.oracle₀ (f ω)) (hr : ∀ ω, E.respond ω = E'.respond (f ω))
    (L : Set (LogReg Req m)) : D.acceptProbOn E post L = D.acceptProbOn E' post L := by
  rw [acceptProbOn, acceptProbOn, hμ, PMF.sum_toReal_map_mul]
  exact sum_congr rfl fun ω _ => by rw [D.acceptProbOnAt_eq_of_agree post (h0 ω) (hr ω)]

/-- **Relabelling the tape**, whole acceptance probability. -/
theorem acceptProb_comap (f : Ω → Ω') (hμ : E'.μ = E.μ.map f)
    (h0 : ∀ ω, E.oracle₀ ω = E'.oracle₀ (f ω)) (hr : ∀ ω, E.respond ω = E'.respond (f ω)) :
    D.acceptProb E post = D.acceptProb E' post := by
  rw [← acceptProbOn_univ, ← acceptProbOn_univ, D.acceptProbOn_comap post f hμ h0 hr]

/-- **Identical until a bad tape.** Two environments with the same tape law that have the same
initial oracle and responses on every tape outside `B` are distinguished with advantage at most
the probability of `B`, on every set of logs. -/
theorem abs_acceptProbOn_sub_le_of_eq_off (E E' : Env Ω Req A X Y Q) (hμ : E'.μ = E.μ)
    (B : Set Ω) (h0 : ∀ ω ∉ B, E.oracle₀ ω = E'.oracle₀ ω)
    (hr : ∀ ω ∉ B, E.respond ω = E'.respond ω) (L : Set (LogReg Req m)) :
    |D.acceptProbOn E post L - D.acceptProbOn E' post L| ≤ (E.μ.toOuterMeasure B).toReal := by
  classical
  rw [acceptProbOn, acceptProbOn, hμ, ← sum_sub_distrib, PMF.toReal_toOuterMeasure_apply]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun ω _ => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  split_ifs with hω
  · have h1 := D.acceptProbOnAt_nonneg post E L ω
    have h2 := D.acceptProbOnAt_le_one post E L ω
    have h3 := D.acceptProbOnAt_nonneg post E' L ω
    have h4 := D.acceptProbOnAt_le_one post E' L ω
    exact mul_le_of_le_one_right ENNReal.toReal_nonneg (abs_sub_le_iff.2 ⟨by linarith, by linarith⟩)
  · rw [D.acceptProbOnAt_eq_of_agree post (h0 ω hω) (hr ω hω), sub_self, abs_zero, mul_zero]

/-- **Identical until a bad tape**, whole acceptance probability. -/
theorem abs_acceptProb_sub_le_of_eq_off (E E' : Env Ω Req A X Y Q) (hμ : E'.μ = E.μ)
    (B : Set Ω) (h0 : ∀ ω ∉ B, E.oracle₀ ω = E'.oracle₀ ω)
    (hr : ∀ ω ∉ B, E.respond ω = E'.respond ω) :
    |D.acceptProb E post - D.acceptProb E' post| ≤ (E.μ.toOuterMeasure B).toReal := by
  rw [← acceptProbOn_univ, ← acceptProbOn_univ]
  exact D.abs_acceptProbOn_sub_le_of_eq_off post E E' hμ B h0 hr _

end Agree

section Split

variable {Ω : Type*}

/-- The acceptance probability on `L` splits into the parts on `L ∩ N` and `L ∩ Nᶜ`. -/
theorem acceptProbOnAt_eq_add (E : Env Ω Req A X Y Q) (L N : Set (LogReg Req m)) (ω : Ω) :
    D.acceptProbOnAt E post L ω =
      D.acceptProbOnAt E post (L ∩ N) ω + D.acceptProbOnAt E post (L ∩ Nᶜ) ω := by
  classical
  rw [acceptProbOnAt, prob_eq_sum_fiber _ fun r => decide ((splitLogs r).2 ∈ N),
    Fintype.sum_bool, acceptProbOnAt, acceptProbOnAt]
  congr 2 <;> ext r <;> simp [and_assoc]

theorem acceptProbOn_eq_add [Fintype Ω] (E : Env Ω Req A X Y Q) (L N : Set (LogReg Req m)) :
    D.acceptProbOn E post L = D.acceptProbOn E post (L ∩ N) + D.acceptProbOn E post (L ∩ Nᶜ) := by
  simp only [acceptProbOn, D.acceptProbOnAt_eq_add post E L N, mul_add, Finset.sum_add_distrib]

end Split

section Kernel

/-! The proof of `abs_acceptProbOn_sub_le_of_kernel`. For a tape `ω₀` and a response function
`s`, `Env.withResponse E ω₀ j s` is `E` at `ω₀` with request `j` answered by `s`. Its acceptance
probability on `L` splits by the key of request `j` (`keyOf`): the logged request and the oracle
in force before it. The part on the branches that never make request `j` does not depend on `s`
(`acceptProbOnAt_notMade_eq`), and the part on the key `κ` depends on `s` only through `s` at
`κ` (`acceptProbOnAt_withResponse_key`). -/

variable {Ω : Type*} [DecidableEq X]

/-- `E` at the tape `ω₀`, with request number `j` answered by `s`. -/
noncomputable def _root_.GordieHowe.Quantum.Env.withResponse (E : Env Ω Req A X Y Q) (ω₀ : Ω) (j : Fin Q)
    (s : Req → (X → Y) → EnvReply A (X → Y)) : Env Unit Req A X Y Q where
  μ := PMF.pure ()
  oracle₀ _ := E.oracle₀ ω₀
  respond _ c := if c = j then s else E.respond ω₀ c

omit [DecidableEq X] in
@[simp] theorem _root_.GordieHowe.Quantum.Env.withResponse_respond (E : Env Ω Req A X Y Q) (ω₀ : Ω)
    (j : Fin Q) (s : Req → (X → Y) → EnvReply A (X → Y)) (u : Unit) (c : Fin Q) :
    (E.withResponse ω₀ j s).respond u c = if c = j then s else E.respond ω₀ c :=
  rfl

/-- The key of request number `j` on a branch: the logged request and the oracle in force before
it, at the tape `ω₀`; `none` if the branch did not make request `j`. -/
def _root_.GordieHowe.Quantum.Env.keyOf (E : Env Ω Req A X Y Q) (ω₀ : Ω) (j : ℕ) (lg : LogReg Req m) :
    Option (Req × (X → Y)) :=
  if h : j < (requests lg).length then some ((requests lg)[j], E.oracleIn ω₀ ((requests lg).take j))
  else none

variable (E : Env Ω Req A X Y Q) (ω₀ : Ω) (j : Fin Q)

/-- Before request `j`, the environment with a replaced response computes the oracles of `E`. -/
theorem oracleIn_withResponse_of_le (s : Req → (X → Y) → EnvReply A (X → Y)) {rs : List Req}
    (hrs : rs.length ≤ j) : (E.withResponse ω₀ j s).oracleIn () rs = E.oracleIn ω₀ rs := by
  refine Env.oracleIn_eq_of_update_eq (E.withResponse ω₀ j s) E rfl rs fun i hi => ?_
  simp only [Env.update]
  split_ifs with hQ
  · have hne : (⟨i, hQ⟩ : Fin Q) ≠ j := fun e => by
      have := congrArg Fin.val e
      simp at this
      omega
    simp [Env.withResponse, hne]
  · rfl

/-- Before request `j`, the environment with a replaced response gives the answers of `E`. -/
theorem answerAfter_withResponse_of_lt (s : Req → (X → Y) → EnvReply A (X → Y)) {rs : List Req}
    (hrs : rs.length < j) (req : Req) :
    (E.withResponse ω₀ j s).answerAfter () rs req = E.answerAfter ω₀ rs req := by
  simp only [Env.answerAfter, oracleIn_withResponse_of_le E ω₀ j s hrs.le]
  split_ifs with hQ
  · have hne : (⟨rs.length, hQ⟩ : Fin Q) ≠ j := fun e => by
      have := congrArg Fin.val e
      simp at this
      omega
    simp [Env.withResponse, hne]
  · rfl

/-- Request `j` is answered by `s` at the key: the request and the oracle of `E` before it. -/
theorem answerAfter_withResponse_of_eq (s : Req → (X → Y) → EnvReply A (X → Y)) {rs : List Req}
    (hrs : rs.length = j) (req : Req) :
    (E.withResponse ω₀ j s).answerAfter () rs req = (s req (E.oracleIn ω₀ rs)).response := by
  have hQ : rs.length < Q := hrs ▸ j.2
  have he : (⟨rs.length, hQ⟩ : Fin Q) = j := Fin.ext hrs
  rw [Env.answerAfter, dif_pos hQ, oracleIn_withResponse_of_le E ω₀ j s hrs.le]
  simp [Env.withResponse, he]

/-- After request `j`, two response functions that agree at the key of request `j` give the same
oracles and answers. -/
theorem oracleIn_withResponse_congr {s s' : Req → (X → Y) → EnvReply A (X → Y)} {rs : List Req}
    (hrs : j < rs.length)
    (hs : s rs[j] (E.oracleIn ω₀ (rs.take j)) = s' rs[j] (E.oracleIn ω₀ (rs.take j))) :
    (E.withResponse ω₀ j s).oracleIn () rs = (E.withResponse ω₀ j s').oracleIn () rs := by
  refine Env.oracleIn_eq_of_update_eq (E.withResponse ω₀ j s) (E.withResponse ω₀ j s') rfl rs
    fun i hi => ?_
  simp only [Env.update]
  split_ifs with hQ
  · by_cases he : (⟨i, hQ⟩ : Fin Q) = j
    · have hij : i = j := congrArg Fin.val he
      subst hij
      rw [Env.withResponse_respond, Env.withResponse_respond, if_pos he, if_pos he,
        oracleIn_withResponse_of_le E ω₀ _ s (by simp)]
      exact congrArg EnvReply.state hs
    · rw [Env.withResponse_respond, Env.withResponse_respond, if_neg he, if_neg he]
  · rfl

theorem answerAfter_withResponse_congr {s s' : Req → (X → Y) → EnvReply A (X → Y)}
    {rs : List Req} (hrs : j < rs.length)
    (hs : s rs[j] (E.oracleIn ω₀ (rs.take j)) = s' rs[j] (E.oracleIn ω₀ (rs.take j)))
    (req : Req) :
    (E.withResponse ω₀ j s).answerAfter () rs req =
      (E.withResponse ω₀ j s').answerAfter () rs req := by
  simp only [Env.answerAfter, oracleIn_withResponse_congr E ω₀ j hrs hs]
  split_ifs with hQ
  · have hne : (⟨rs.length, hQ⟩ : Fin Q) ≠ j := fun e => by
      have := congrArg Fin.val e
      simp at this
      omega
    simp [Env.withResponse, hne]
  · rfl

omit [DecidableEq Req] [DecidableEq A] [AddGroup Y] [DecidableEq X] in
theorem keyOf_eq_none_iff {lg : LogReg Req m} {j' : ℕ} :
    E.keyOf ω₀ j' lg = none ↔ (requests lg).length ≤ j' := by
  unfold Env.keyOf
  split_ifs with h <;> simp <;> omega

omit [DecidableEq Req] [DecidableEq A] [AddGroup Y] [DecidableEq X] in
theorem keyOf_eq_some {lg : LogReg Req m} {j' : ℕ} {κ : Req × (X → Y)}
    (h : E.keyOf ω₀ j' lg = some κ) : ∃ hlt : j' < (requests lg).length,
      κ = ((requests lg)[j'], E.oracleIn ω₀ ((requests lg).take j')) := by
  unfold Env.keyOf at h
  split_ifs at h with hlt
  exact ⟨hlt, (Option.some_inj.1 h).symm⟩

omit [DecidableEq Req] [DecidableEq A] [AddGroup Y] [DecidableEq X] in
/-- Appending a request after request `j` keeps the key. -/
theorem keyOf_append_of_lt {lg lg' : LogReg Req m} {j' : ℕ} {a : Req}
    (h : requests lg' = requests lg ++ [a]) (hj : j' < (requests lg).length) :
    E.keyOf ω₀ j' lg' = E.keyOf ω₀ j' lg := by
  unfold Env.keyOf
  rw [dif_pos hj, dif_pos (by rw [h, List.length_append]; omega)]
  simp only [h, List.getElem_append_left hj, List.take_append_of_le_length hj.le]

omit [DecidableEq Req] [DecidableEq A] [AddGroup Y] [DecidableEq X] in
/-- Appending request number `j` gives the key of the request and the oracle before it. -/
theorem keyOf_append_of_eq {lg lg' : LogReg Req m} {j' : ℕ} {a : Req}
    (h : requests lg' = requests lg ++ [a]) (hj : (requests lg).length = j') :
    E.keyOf ω₀ j' lg' = some (a, E.oracleIn ω₀ (requests lg)) := by
  unfold Env.keyOf
  rw [dif_pos (by rw [h, List.length_append]; simp; omega)]
  subst hj
  simp [h]

/-- **The part of the game on one key.** The acceptance probability on the branches whose
request `j` has the key `κ` depends on the response function only at `κ`. -/
theorem acceptProbOnAt_withResponse_key (L : Set (LogReg Req m)) (κ : Req × (X → Y))
    {s s' : Req → (X → Y) → EnvReply A (X → Y)} (hs : s κ.1 κ.2 = s' κ.1 κ.2) :
    D.acceptProbOnAt (E.withResponse ω₀ j s) post (L ∩ {lg | E.keyOf ω₀ j lg = some κ}) () =
      D.acceptProbOnAt (E.withResponse ω₀ j s') post (L ∩ {lg | E.keyOf ω₀ j lg = some κ}) () := by
  set N : Set (LogReg Req m) := {lg | E.keyOf ω₀ j lg = none ∨ E.keyOf ω₀ j lg = some κ}
  -- the oracles agree on the logs in `N`
  have horacle : ∀ lg ∈ N, (E.withResponse ω₀ j s).oracle () lg =
      (E.withResponse ω₀ j s').oracle () lg := by
    intro lg hlg
    rcases hlg with h | h
    · have hle := (keyOf_eq_none_iff E ω₀).1 h
      rw [Env.oracle, Env.oracle, oracleIn_withResponse_of_le E ω₀ j s hle,
        oracleIn_withResponse_of_le E ω₀ j s' hle]
    · obtain ⟨hlt, rfl⟩ := keyOf_eq_some E ω₀ h
      exact oracleIn_withResponse_congr E ω₀ j hlt hs
  have hrun : mask (logsIn N) (D.run (E.withResponse ω₀ j s) ()) =
      mask (logsIn N) (D.run (E.withResponse ω₀ j s') ()) := by
    refine D.mask_stage_eq_of_eventPerm _ _ N (fun k r hr hN => ?_) (fun k r hr hN himg => ?_) m
    · -- a branch with another key keeps it
      have hkey : ∀ (E'' : Env Unit Req A X Y Q), D.eventPerm E'' () k r ∉ logsIn N := by
        intro E'' himg
        simp only [N, mem_logsIn, Set.mem_ofPred_eq, not_or] at hN himg
        have hmade : (j : ℕ) < (requests (splitLogs r).2).length := by
          by_contra h
          exact hN.1 ((keyOf_eq_none_iff E ω₀).2 (not_lt.1 h))
        have hsame : E.keyOf ω₀ j (splitLogs (D.eventPerm E'' () k r)).2 =
            E.keyOf ω₀ j (splitLogs r).2 := by
          have := D.requests_eventPerm E'' () hr
          split_ifs at this
          · exact keyOf_append_of_lt E ω₀ this hmade
          · simp only [Env.keyOf, this]
        rw [hsame] at himg
        tauto
      exact ⟨hkey _, hkey _⟩
    · by_cases hk : k < m
      · refine D.eventPerm_eq_of_agree _ _ hr (fun _ => horacle _ hN) fun hkind => ?_
        set rs := requests (splitLogs r).2
        rcases lt_trichotomy rs.length j with hlt | heq | hgt
        · rw [answerAfter_withResponse_of_lt E ω₀ j s hlt, answerAfter_withResponse_of_lt E ω₀ j s' hlt]
        · rw [answerAfter_withResponse_of_eq E ω₀ j s heq, answerAfter_withResponse_of_eq E ω₀ j s' heq]
          -- the image has the key of this request, which is `κ`
          have hreq : ∀ (E'' : Env Unit Req A X Y Q),
              requests (splitLogs (D.eventPerm E'' () k r)).2 = rs ++ [r.request] := fun E'' => by
            rw [D.requests_eventPerm E'' () hr, if_pos ⟨hkind, hk⟩]
          have hkimg : ∀ (E'' : Env Unit Req A X Y Q), D.eventPerm E'' () k r ∈ logsIn N →
              κ = (r.request, E.oracleIn ω₀ rs) := fun E'' h => by
            simp only [N, mem_logsIn, Set.mem_ofPred_eq] at h
            rw [keyOf_append_of_eq E ω₀ (hreq E'') heq] at h
            rcases h with h | h
            · exact absurd h (by simp)
            · exact (Option.some_inj.1 h).symm
          have := himg.elim (hkimg _) (hkimg _)
          rw [this] at hs
          rw [hs]
        · have hκ : E.keyOf ω₀ j (splitLogs r).2 = some κ := by
            rcases hN with h | h
            · exact absurd ((keyOf_eq_none_iff E ω₀).1 h) (not_le.2 hgt)
            · exact h
          obtain ⟨hlt, hκ'⟩ := keyOf_eq_some E ω₀ hκ
          rw [hκ'] at hs
          exact answerAfter_withResponse_congr E ω₀ j hlt hs _
      · rw [D.eventPerm_of_le _ () (not_lt.1 hk), D.eventPerm_of_le _ () (not_lt.1 hk)]
  have h := D.acceptProbOnAt_inter_eq _ _ post (D.mask_final_eq _ _ post hrun horacle)
    (L ∩ {lg | E.keyOf ω₀ j lg = some κ})
  have hset : L ∩ {lg | E.keyOf ω₀ j lg = some κ} ∩ N = L ∩ {lg | E.keyOf ω₀ j lg = some κ} :=
    Set.inter_eq_left.2 fun lg hlg => Or.inr hlg.2
  rwa [hset] at h

/-- **The split by keys.** The acceptance probability on `L` is the part on the branches that
never make request `j` plus the parts on the keys of request `j`. -/
theorem acceptProbOnAt_eq_add_sum_key (E' : Env Unit Req A X Y Q) (L : Set (LogReg Req m)) :
    D.acceptProbOnAt E' post L () = D.acceptProbOnAt E' post (L ∩ (madeLogs j)ᶜ) () +
      ∑ κ : Req × (X → Y), D.acceptProbOnAt E' post (L ∩ {lg | E.keyOf ω₀ j lg = some κ}) () := by
  classical
  rw [acceptProbOnAt, prob_eq_sum_fiber _ (fun r => E.keyOf ω₀ j (splitLogs r).2),
    Fintype.sum_option]
  congr 1
  · rw [acceptProbOnAt]
    congr 1
    ext r
    simp [madeLogs, keyOf_eq_none_iff, and_assoc]
  · refine sum_congr rfl fun κ _ => ?_
    rw [acceptProbOnAt]
    congr 1
    ext r
    simp [and_assoc]

/-- **The part of the game on one key** with request `j` answered by the constant reply `y`:
the acceptance probability on the logs in `L` whose request `j` has the key `κ`. By
`acceptProbOnAt_withResponse_key` it is the part on `κ` of every response function with value `y`
at `κ`. -/
noncomputable def keyPart (L : Set (LogReg Req m)) (κ : Req × (X → Y)) (y : EnvReply A (X → Y)) :
    ℝ :=
  D.acceptProbOnAt (E.withResponse ω₀ j fun _ _ => y) post (L ∩ {lg | E.keyOf ω₀ j lg = some κ}) ()

omit [DecidableEq X] in
theorem keyPart_nonneg (L : Set (LogReg Req m)) (κ : Req × (X → Y)) (y : EnvReply A (X → Y)) :
    0 ≤ D.keyPart post E ω₀ j L κ y :=
  D.acceptProbOnAt_nonneg post _ _ ()

/-- **The game with request `j` answered by `s`, split by the key of request `j`**: the part on
the branches that never make request `j`, which does not depend on `s`, plus the key parts at the
values of `s`. -/
theorem acceptProbOnAt_withResponse_eq_add_sum (L : Set (LogReg Req m))
    (s s₀ : Req → (X → Y) → EnvReply A (X → Y)) :
    D.acceptProbOnAt (E.withResponse ω₀ j s) post L () =
      D.acceptProbOnAt (E.withResponse ω₀ j s₀) post (L ∩ (madeLogs j)ᶜ) () +
        ∑ κ : Req × (X → Y), D.keyPart post E ω₀ j L κ (s κ.1 κ.2) := by
  rw [D.acceptProbOnAt_eq_add_sum_key post E ω₀ j]
  congr 1
  · exact D.acceptProbOnAt_notMade_eq _ _ post
      (fun rs req h => by rw [answerAfter_withResponse_of_lt _ _ _ _ h,
        answerAfter_withResponse_of_lt _ _ _ _ h])
      (fun rs h => by rw [oracleIn_withResponse_of_le _ _ _ _ h,
        oracleIn_withResponse_of_le _ _ _ _ h]) L
  · exact Finset.sum_congr rfl fun κ _ => D.acceptProbOnAt_withResponse_key post E ω₀ j L κ rfl

/-- **The largest key parts sum to at most one**: for any choice `y κ` of a reply per key, the
key parts at `y` are the key parts of the response function `fun req H => y (req, H)`, whose
acceptance probability is at most one. -/
theorem sum_keyPart_le_one (L : Set (LogReg Req m)) (y : Req × (X → Y) → EnvReply A (X → Y)) :
    ∑ κ : Req × (X → Y), D.keyPart post E ω₀ j L κ (y κ) ≤ 1 := by
  have h1 := D.acceptProbOnAt_le_one post (E.withResponse ω₀ j fun req H => y (req, H)) L ()
  have h2 := D.acceptProbOnAt_nonneg post (E.withResponse ω₀ j fun req H => y (req, H))
    (L ∩ (madeLogs j)ᶜ) ()
  have h3 := D.acceptProbOnAt_withResponse_eq_add_sum post E ω₀ j L (fun req H => y (req, H))
    (fun req H => y (req, H))
  linarith

/-- **A key that no branch carries has an empty part**: if the oracle of the key is the oracle in
force after no list of `j` requests, no logs have that key. -/
theorem keyPart_eq_zero (L : Set (LogReg Req m)) {κ : Req × (X → Y)}
    (hκ : ∀ rs : List Req, rs.length = j → κ.2 ≠ E.oracleIn ω₀ rs) (y : EnvReply A (X → Y)) :
    D.keyPart post E ω₀ j L κ y = 0 := by
  have hempty : L ∩ {lg : LogReg Req m | E.keyOf ω₀ j lg = some κ} = ∅ := by
    ext lg
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro _ hk
    obtain ⟨hlt, hκ'⟩ := keyOf_eq_some E ω₀ hk
    exact hκ ((requests lg).take j) (List.length_take_of_le hlt.le) (by rw [hκ'])
  rw [keyPart, acceptProbOnAt, hempty]
  have h0' : D.gameAccept ∩ logsIn (∅ : Set (LogReg Req m)) = ∅ := by
    ext r
    simp [logsIn]
  rw [h0']
  have hm : ∀ v : QState (GameReg W n X Y Req A m), mask ∅ v = 0 := fun v => by
    ext i
    simp
  simp [prob, hm]

variable {V R R' : Type*} [Fintype V] [Fintype R] [Fintype R']

omit [DecidableEq X] in
/-- **The game at a tape is the game with request `j` answered by the tape's kernel**: an
environment `E'` that agrees with `E` at `ω₀` on the initial oracle and on every request other
than number `j` is `E` at `ω₀` with request `j` answered by `E'`. -/
theorem acceptProbOnAt_eq_withResponse {Ω' : Type*} (E' : Env Ω' Req A X Y Q) {ω : Ω'}
    (h0 : E'.oracle₀ ω = E.oracle₀ ω₀) (hi : ∀ c : Fin Q, c ≠ j → E'.respond ω c = E.respond ω₀ c)
    (L : Set (LogReg Req m)) :
    D.acceptProbOnAt E' post L ω = D.acceptProbOnAt (E.withResponse ω₀ j (E'.respond ω j)) post L () :=
  D.acceptProbOnAt_eq_of_agree post (E := E') (E' := E.withResponse ω₀ j (E'.respond ω j))
    (ω' := ()) h0 (funext fun c => by
      rw [Env.withResponse_respond]
      by_cases hc : c = j
      · rw [if_pos hc, hc]
      · rw [if_neg hc, hi c hc]) L

/-- **The average over one kernel, split by the key**: the average over `τ ← ν` of the game with
request `j` answered by the kernel at `τ` is the part on the branches that never make request `j`
plus, per key, the average key part. -/
theorem sum_acceptProbOnAt_withResponse (ν : PMF R) (L : Set (LogReg Req m))
    (s : R → Req → (X → Y) → EnvReply A (X → Y)) (s₀ : Req → (X → Y) → EnvReply A (X → Y)) :
    ∑ τ, (ν τ).toReal * D.acceptProbOnAt (E.withResponse ω₀ j (s τ)) post L () =
      D.acceptProbOnAt (E.withResponse ω₀ j s₀) post (L ∩ (madeLogs j)ᶜ) () +
        ∑ κ : Req × (X → Y), ∑ τ, (ν τ).toReal * D.keyPart post E ω₀ j L κ (s τ κ.1 κ.2) := by
  simp only [D.acceptProbOnAt_withResponse_eq_add_sum post E ω₀ j L _ s₀, mul_add,
    Finset.sum_add_distrib, ← Finset.sum_mul, PMF.sum_toReal, one_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- **Kernel replacement at one tape `v`**: if the laws of request `j`'s reply under the two
kernels are within `ε` at every key that a branch can carry, the two averaged games differ by at
most `ε`. -/
theorem abs_sum_withResponse_sub_le {ν : PMF R} {ν' : PMF R'} (L : Set (LogReg Req m))
    (s : R → Req → (X → Y) → EnvReply A (X → Y)) (s' : R' → Req → (X → Y) → EnvReply A (X → Y))
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hj : ∀ req (rs : List Req), rs.length = j →
      PMF.tvDist (ν.map fun τ => s τ req (E.oracleIn ω₀ rs))
        (ν'.map fun τ => s' τ req (E.oracleIn ω₀ rs)) ≤ ε) :
    |∑ τ, (ν τ).toReal * D.acceptProbOnAt (E.withResponse ω₀ j (s τ)) post L () -
      ∑ τ, (ν' τ).toReal * D.acceptProbOnAt (E.withResponse ω₀ j (s' τ)) post L ()| ≤ ε := by
  classical
  obtain ⟨y₀⟩ : Nonempty (EnvReply A (X → Y)) := ⟨⟨none, 0⟩⟩
  have hmax : ∀ κ, ∃ y, ∀ y', D.keyPart post E ω₀ j L κ y' ≤ D.keyPart post E ω₀ j L κ y :=
    fun κ => by
      obtain ⟨y, -, hy⟩ := Finset.exists_max_image Finset.univ (D.keyPart post E ω₀ j L κ)
        Finset.univ_nonempty
      exact ⟨y, fun y' => hy y' (Finset.mem_univ _)⟩
  choose ymax hymax using hmax
  rw [D.sum_acceptProbOnAt_withResponse post E ω₀ j ν L s fun _ _ => y₀,
    D.sum_acceptProbOnAt_withResponse post E ω₀ j ν' L s' fun _ _ => y₀, add_sub_add_left_eq_sub,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ κ : Req × (X → Y), |∑ τ, (ν τ).toReal * D.keyPart post E ω₀ j L κ (s τ κ.1 κ.2) -
        ∑ τ, (ν' τ).toReal * D.keyPart post E ω₀ j L κ (s' τ κ.1 κ.2)|
      ≤ ∑ κ : Req × (X → Y), D.keyPart post E ω₀ j L κ (ymax κ) * ε := Finset.sum_le_sum fun κ _ => by
        rw [← PMF.sum_toReal_map_mul ν (fun τ => s τ κ.1 κ.2) (D.keyPart post E ω₀ j L κ),
          ← PMF.sum_toReal_map_mul ν' (fun τ => s' τ κ.1 κ.2) (D.keyPart post E ω₀ j L κ)]
        refine (PMF.abs_sum_toReal_mul_sub_le _ _ (fun y => D.keyPart_nonneg post E ω₀ j L κ y)
          (hymax κ)).trans ?_
        by_cases hreach : ∃ rs : List Req, rs.length = j ∧ κ.2 = E.oracleIn ω₀ rs
        · obtain ⟨rs, hrs, hκ⟩ := hreach
          refine mul_le_mul_of_nonneg_left ?_ (D.keyPart_nonneg post E ω₀ j L κ _)
          have := hj κ.1 rs hrs
          rwa [← hκ] at this
        · push Not at hreach
          rw [D.keyPart_eq_zero post E ω₀ j L hreach, zero_mul, zero_mul]
    _ = (∑ κ : Req × (X → Y), D.keyPart post E ω₀ j L κ (ymax κ)) * ε := by rw [Finset.sum_mul]
    _ ≤ 1 * ε := mul_le_mul_of_nonneg_right (D.sum_keyPart_le_one post E ω₀ j L ymax) hε0
    _ = ε := one_mul _

end Kernel

section KernelReplacement

variable {V R R' : Type*} [Fintype V] [Fintype R] [Fintype R'] [DecidableEq X]

/-- **Kernel replacement at request `j`.** Let the tapes be `(v, τ)` with
`E.μ (v, τ) = μV v * ν τ` and `E'.μ (v, τ') = μV v * ν' τ'`, and suppose:

- (`h0`, `hi`) the initial oracles and the responses to every request other than number `j` are
  the same in both environments and do not depend on `τ`;
- (`hj`) for each `v`, each logged request `req` and each list `rs` of `j` earlier requests, the
  response to request `j` and the new oracle, as functions of `τ ← ν` and of `τ' ← ν'` with the
  oracle in force after `rs`, have laws within `ε v` in total variation.

Then the games against `E` and `E'` are distinguished with advantage at most the average of
`ε v` over `v ← μV`, on every set of logs. The request and its slot may depend on the
distinguisher's queries before it (it is prepared in superposition and measured by the log
copy), and `ε v` may depend on everything in `v`, including the initial oracle. The proof: at each
`v` both games are the game at `(v, τ₀)` with request `j` answered by a kernel
(`acceptProbOnAt_eq_withResponse`), and the averaged games differ by at most `ε v`
(`abs_sum_withResponse_sub_le`).

Hypotheses: `hμ`, `hμ'`, `h0`, `hi` describe the two environments; `hj` is the
classical closeness of the two response kernels, and `hε0` says the bound is nonnegative. -/
theorem abs_acceptProbOn_sub_le_of_kernel (E : Env (V × R) Req A X Y Q)
    (E' : Env (V × R') Req A X Y Q) {μV : PMF V} {ν : PMF R} {ν' : PMF R'}
    (hμ : ∀ v τ, E.μ (v, τ) = μV v * ν τ) (hμ' : ∀ v τ, E'.μ (v, τ) = μV v * ν' τ) (j : Fin Q)
    (h0 : ∀ v τ τ', E.oracle₀ (v, τ) = E'.oracle₀ (v, τ'))
    (hi : ∀ v τ τ' (i : Fin Q), i ≠ j → E.respond (v, τ) i = E'.respond (v, τ') i)
    (ε : V → ℝ) (hε0 : ∀ v, 0 ≤ ε v)
    (hj : ∀ v τ₀ req (rs : List Req), rs.length = j →
      PMF.tvDist (ν.map fun τ => E.respond (v, τ) j req (E.oracleIn (v, τ₀) rs))
        (ν'.map fun τ => E'.respond (v, τ) j req (E.oracleIn (v, τ₀) rs)) ≤ ε v)
    (L : Set (LogReg Req m)) :
    |D.acceptProbOn E post L - D.acceptProbOn E' post L| ≤ ∑ v, (μV v).toReal * ε v := by
  classical
  obtain ⟨τ₀, -⟩ := ν.support_nonempty
  obtain ⟨τ₀', -⟩ := ν'.support_nonempty
  have hE : ∀ v τ, D.acceptProbOnAt E post L (v, τ) =
      D.acceptProbOnAt (E.withResponse (v, τ₀) j (E.respond (v, τ) j)) post L () := fun v τ =>
    D.acceptProbOnAt_eq_withResponse post E (v, τ₀) j E ((h0 v τ τ₀').trans (h0 v τ₀ τ₀').symm)
      (fun c hc => (hi v τ τ₀' c hc).trans (hi v τ₀ τ₀' c hc).symm) L
  have hE' : ∀ v τ, D.acceptProbOnAt E' post L (v, τ) =
      D.acceptProbOnAt (E.withResponse (v, τ₀) j (E'.respond (v, τ) j)) post L () := fun v τ =>
    D.acceptProbOnAt_eq_withResponse post E (v, τ₀) j E' (h0 v τ₀ τ).symm
      (fun c hc => (hi v τ₀ τ c hc).symm) L
  rw [acceptProbOn, acceptProbOn, Fintype.sum_prod_type, Fintype.sum_prod_type, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun v _ => ?_)
  simp only [hμ, hμ', ENNReal.toReal_mul, mul_assoc, ← mul_sum, ← mul_sub, abs_mul,
    abs_of_nonneg ENNReal.toReal_nonneg, hE, hE']
  exact mul_le_mul_of_nonneg_left (D.abs_sum_withResponse_sub_le post E (v, τ₀) j L
    (fun τ => E.respond (v, τ) j) (fun τ => E'.respond (v, τ) j) (hε0 v)
    fun req rs hrs => hj v τ₀ req rs hrs) ENNReal.toReal_nonneg

end KernelReplacement


end Distinguisher

end GordieHowe.Quantum
