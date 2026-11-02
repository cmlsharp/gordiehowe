-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.HiddenSide
public import GordieHowe.Model.Quantum.O2H.HiddenReads

@[expose] public section

/-!
# Hidden points correlated with the replies, with the challenger's reads as queries, against
interactive adversaries

`GordieHowe/Model/Quantum/O2H/HiddenReads.lean` bounds, for distinguishers of the pure game with a
query budget, the change between two environments whose oracles differ at hidden points of each
request and whose answers differ only through the challenger's reads at those points
(`HiddenSideReads`). This file carries the bound to the interactive adversaries
(`AdaptiveIAlg`) through their dilation, as `AdaptiveIAlg.advantage_outLaw_le_of_hidden`
(`GordieHowe/Model/Quantum/Interactive/HiddenSide.lean`) does without reads.

- `AdaptiveIAlg.advantage_outLaw_le_of_hiddenReads`: for challengers `C` and `C'` whose pure
  games, averaged over an oracle law `μH` and their coins, are the games against `E` and `E'` for
  the dilated adversary (`hC`, `hC'`), the probabilities that the adversary outputs `o` differ by at
  most `2 √(q + Q') √((width q + qC Q) ∑ c, ε c)` with `q = budget + post` and `Q' = 0` if
  `qC = 0`, `Q` otherwise.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] [DecidableEq O] {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O)

/-- **Hidden points correlated with the replies, with the challenger's reads as queries, against
an interactive adversary** (`Distinguisher.advantage_acceptProb_le_of_hiddenReads_budget` through
the dilation). -/
theorem advantage_outLaw_le_of_hiddenReads [Nonempty Req] {C C' : Challenger X Y Req Resp}
    {μH : PMF (X → Y)} {Ω U : Type} [Fintype Ω] [Fintype U] {Q : ℕ}
    {St St' : Type} [OracleState St X Y] [OracleState St' X Y]
    {E : Env Ω Req Resp X Y Q St} {E' : Env Ω Req Resp X Y Q St'} {ν : PMF U} {res : Fin Q → Ω → U → Ω}
    {hidden : Ω → List Req → Req → Set X} {reads : Ω → List Req → Req → Finset X} {qC : ℕ}
    (hE : HiddenSideReads E E' ν res hidden reads qC) (ε : Fin Q → ℝ)
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
        2 * √((A.budget + A.post : ℕ) + if qC = 0 then 0 else Q) *
          √((A.width * (A.budget + A.post : ℕ) + qC * Q) * ∑ c, ε c) := by
  simp only [toReal_outLaw_compose_eq]
  rw [hC, hC']
  exact Distinguisher.advantage_acceptProb_le_of_hiddenReads_budget (A.pureDilBudget o) hE ε hfind

end AdaptiveIAlg

end GordieHowe.Quantum
