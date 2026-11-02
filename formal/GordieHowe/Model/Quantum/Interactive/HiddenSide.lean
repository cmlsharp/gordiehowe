-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.SaltReprogram
public import GordieHowe.Model.Quantum.O2H.HiddenSide

@[expose] public section

/-!
# Hidden points correlated with the replies, against interactive adversaries

`GordieHowe/Model/Quantum/O2H/HiddenSide.lean` bounds, for distinguishers of the pure game with a
query budget, the change between two environments whose oracles differ at hidden points of each
request (`HiddenSide`). This file carries the bound to the interactive adversaries of
`GordieHowe/Model/Quantum/Interactive` (`AdaptiveIAlg`) through their dilation
(`AdaptiveIAlg.pureDil`, `AdaptiveIAlg.toReal_outLaw_compose_eq`), as
`AdaptiveIAlg.advantage_salt_fresh_le` does for hidden fresh salts.

- `AdaptiveIAlg.advantage_outLaw_le_of_hidden`: for challengers `C` and `C'` whose pure games,
  averaged over an oracle law `μH` and their coins, are the games against `E` and `E'` for the
  dilated adversary (`hC`, `hC'`), the probabilities that the adversary outputs `o` differ by at
  most `2 (budget + post) √(width ∑ c, ε c)`.

The event is the adversary's output. The hypotheses `hC` and `hC'` identify the challengers
with the two environments in the pure game; `Challenger.SaltFreshPair.sum_salt` is an example
of such an identification.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] [DecidableEq O] {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O)

/-- **Hidden points correlated with the replies, against an interactive adversary**
(`Distinguisher.advantage_acceptProb_le_of_hidden_budget` through the dilation): if the
challengers `C` and `C'`, averaged over the oracle law `μH` and their coins, are the games against
environments `E` and `E'` whose oracles differ at hidden points of each request (`HiddenSide`),
and every guess from the response to a request is a hidden point of it with probability at most
`ε c` over the coins of request number `c`, the probabilities that the adversary outputs `o`
against `C` and against `C'` differ by at most `2 (budget + post) √(width ∑ c, ε c)`. -/
theorem advantage_outLaw_le_of_hidden [Nonempty Req] {C C' : Challenger X Y Req Resp}
    {μH : PMF (X → Y)} {Ω U : Type} [Fintype Ω] [Fintype U] {Q : ℕ}
    {E E' : Env Ω Req Resp X Y Q} {ν : PMF U} {res : Fin Q → Ω → U → Ω}
    {hidden : Ω → List Req → Req → Set X} (hE : HiddenSide E E' ν res hidden) (ε : Fin Q → ℝ)
    (hfind : ∀ (c : Fin Q) ω rs₀ req, rs₀.length = (c : ℕ) → ∀ g : Option Resp → X,
      (ν.toOuterMeasure {a | g (E.answerAfter (res c ω a) rs₀ req) ∈
        hidden (res c ω a) rs₀ req}).toReal ≤ ε c)
    (o : O)
    (hC : ∑ H, (μH H).toReal * ∑ c, (C.coins c).toReal *
      (A.pureDil o).acceptProbAt C.toPureEnv noPost (H, c) = (A.pureDil o).acceptProb E noPost)
    (hC' : ∑ H, (μH H).toReal * ∑ c, (C'.coins c).toReal *
      (A.pureDil o).acceptProbAt C'.toPureEnv noPost (H, c) =
        (A.pureDil o).acceptProb E' noPost) :
    GordieHowe.advantage (∑ H, (μH H).toReal * ((A.compose C).outLaw H (some o)).toReal)
      (∑ H, (μH H).toReal * ((A.compose C').outLaw H (some o)).toReal) ≤
        2 * (A.budget + A.post : ℕ) * √(A.width * ∑ c, ε c) := by
  simp only [toReal_outLaw_compose_eq]
  rw [hC, hC']
  exact Distinguisher.advantage_acceptProb_le_of_hidden_budget (A.pureDilBudget o) hE ε hfind

end AdaptiveIAlg

end GordieHowe.Quantum
