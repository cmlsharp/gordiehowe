-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.SaltReprogram
public import GordieHowe.Model.Quantum.Pure.UntilBad

@[expose] public section

/-!
# Identical until a bad request, for challengers answering request by request

`GordieHowe/Model/Quantum/Pure/UntilBad.lean` compares two environments of the pure game that
agree on the answers to the good requests. This file carries it to challengers that answer
request by request and reprogram nothing (`Challenger.AnswersBy`).

- `Challenger.answersEnv Q resp coins`: the environment with the oracle of the tape as its state,
  answering request number `j < Q` by `resp c H j req` and keeping the oracle.
  `Challenger.AnswersBy.final_eq`: a challenger answering request by request by `resp` gives the
  final state of that environment, for every distinguisher.
- `Challenger.AnswersBy.prob_inter_goodLogs_eq`, `Challenger.AnswersBy.prob_badLogs_eq`,
  `Challenger.AnswersBy.abs_prob_sub_le_untilBad`: two such challengers, at the tapes `(H, c)` and
  `(H, c')`, answering the same number of requests, whose responses to request number `j < Q`
  agree whenever the request is not bad, give every set of game registers the same probability on
  the logs whose first `Q` requests are all good (`goodLogs`), give the bad logs the same
  probability, and give every set of game registers probabilities that differ by at most it.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

namespace Challenger

variable {X Y Req Resp : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

/-- **The environment of a challenger answering request by request**, with the oracle of the
tape as its state: the tape is the oracle, uniform, and the coins `c ← coins`; request number
`j < Q` with request `req` gets `resp c H j req`, and the oracle is kept. -/
noncomputable def answersEnv {Coins : Type} (Q : ℕ)
    (resp : Coins → (X → Y) → ℕ → Req → Option Resp) (coins : PMF Coins) :
    Env ((X → Y) × Coins) Req Resp X Y Q where
  μ := (PMF.uniformOfFintype (X → Y)).bind fun H => coins.map fun c => (H, c)
  oracle₀ ω := ω.1
  respond ω j req H := ⟨resp ω.2 ω.1 j req, H⟩

theorem keepsState_answersEnv {Coins : Type} (Q : ℕ)
    (resp : Coins → (X → Y) → ℕ → Req → Option Resp) (coins : PMF Coins) :
    (answersEnv Q resp coins).KeepsState :=
  fun _ _ _ _ => rfl

theorem oracleIn_answersEnv {Coins : Type} (Q : ℕ)
    (resp : Coins → (X → Y) → ℕ → Req → Option Resp) (coins : PMF Coins) (ω : (X → Y) × Coins)
    (rs : List Req) : (answersEnv Q resp coins).oracleIn ω rs = ω.1 :=
  Env.oracleIn_of_keepsState (keepsState_answersEnv Q resp coins) ω rs

variable {C : Challenger X Y Req Resp} {resp : C.Coins → (X → Y) → ℕ → Req → Option Resp}
  [Fintype Req] [Fintype Resp] [DecidableEq Req] [DecidableEq Resp] [AddGroup Y]
  {W : Type} [Fintype W] {n m : ℕ} (D : Distinguisher W X Y Req Resp n m)
  (post : (X → Y) → QState (DReg W n X Y Req Resp) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req Resp))

/-- **A challenger answering request by request is its environment `answersEnv`** in the pure
game: every distinguisher has the same final state against both, at every tape and for any
number `Q = C.Q` of answered requests. -/
theorem AnswersBy.final_eq (h : C.AnswersBy resp) {Q : ℕ} (hQ : C.Q = Q)
    (ω : (X → Y) × C.Coins) :
    D.final C.toPureEnv post ω = D.final (answersEnv Q resp C.coins) post ω := by
  subst hQ
  refine D.final_congr _ _ (fun lg k => ?_) (fun lg => ?_) post
  · unfold Env.answer
    refine congrArg ((lg k).elim none) (funext fun req => ?_)
    rw [h.answerAfter]
    simp only [Env.answerAfter, answersEnv]
    split_ifs <;> rfl
  · rw [h.oracle]
    simp only [Env.oracle, oracleIn_answersEnv]
    rfl

variable {C' : Challenger X Y Req Resp} {resp' : C'.Coins → (X → Y) → ℕ → Req → Option Resp}
  {H : X → Y} {c : C.Coins} {c' : C'.Coins} {Bad : Req → Prop}

/-- **Identical until a bad request, on the good logs**: two challengers answering request by
request (`resp` at the tape `(H, c)`, `resp'` at `(H, c')`), answering the same number `Q` of
requests, whose responses to request number `j < Q` agree whenever the request is not bad, give
every set `S` of game registers the same probability on the logs whose first `Q` requests are all
good. -/
theorem AnswersBy.prob_inter_goodLogs_eq (h : C.AnswersBy resp) (h' : C'.AnswersBy resp')
    (hQ : C'.Q = C.Q)
    (hagree : ∀ j req, j < C.Q → ¬ Bad req → resp' c' H j req = resp c H j req)
    (S : Set (GameReg W n X Y Req Resp m)) :
    prob (S ∩ logsIn (goodLogs C.Q Bad)) (D.final C.toPureEnv post (H, c)) =
      prob (S ∩ logsIn (goodLogs C.Q Bad)) (D.final C'.toPureEnv post (H, c')) := by
  rw [h.final_eq D post rfl, h'.final_eq D post hQ]
  refine D.prob_inter_goodLogs_eq post (fun rs => ?_) (fun rs req hrs hB => ?_) S
  · simp only [oracleIn_answersEnv]
  · simp only [Env.answerAfter, dif_pos hrs, answersEnv]
    exact (hagree _ _ hrs hB).symm

/-- **Identical until a bad request: the bad logs** (the logs with a bad request among their
first `Q` requests) have the same probability, under the hypotheses of
`AnswersBy.prob_inter_goodLogs_eq`. -/
theorem AnswersBy.prob_badLogs_eq (h : C.AnswersBy resp) (h' : C'.AnswersBy resp')
    (hQ : C'.Q = C.Q)
    (hagree : ∀ j req, j < C.Q → ¬ Bad req → resp' c' H j req = resp c H j req) :
    prob (logsIn (goodLogs C.Q Bad))ᶜ (D.final C.toPureEnv post (H, c)) =
      prob (logsIn (goodLogs C.Q Bad))ᶜ (D.final C'.toPureEnv post (H, c')) := by
  rw [h.final_eq D post rfl, h'.final_eq D post hQ]
  refine D.prob_badLogs_eq post (fun rs => ?_) (fun rs req hrs hB => ?_)
  · simp only [oracleIn_answersEnv]
  · simp only [Env.answerAfter, dif_pos hrs, answersEnv]
    exact (hagree _ _ hrs hB).symm

/-- **Identical until a bad request, as a bound**: under the hypotheses of
`AnswersBy.prob_inter_goodLogs_eq`, the probabilities of every set of game registers differ by at
most the probability of the bad logs. -/
theorem AnswersBy.abs_prob_sub_le_untilBad (h : C.AnswersBy resp) (h' : C'.AnswersBy resp')
    (hQ : C'.Q = C.Q)
    (hagree : ∀ j req, j < C.Q → ¬ Bad req → resp' c' H j req = resp c H j req)
    (S : Set (GameReg W n X Y Req Resp m)) :
    |prob S (D.final C.toPureEnv post (H, c)) - prob S (D.final C'.toPureEnv post (H, c'))| ≤
      prob (logsIn (goodLogs C.Q Bad))ᶜ (D.final C.toPureEnv post (H, c)) := by
  rw [h.final_eq D post rfl, h'.final_eq D post hQ]
  refine D.abs_prob_sub_le_untilBad post (fun rs => ?_) (fun rs req hrs hB => ?_) S
  · simp only [oracleIn_answersEnv]
  · simp only [Env.answerAfter, dif_pos hrs, answersEnv]
    exact (hagree _ _ hrs hB).symm

end Challenger

end GordieHowe.Quantum
