-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.Adaptive
public import GordieHowe.Model.Quantum.Pure.ClassicalSim
public import GordieHowe.Foundations.ToMathlib.PMFOption

@[expose] public section

/-!
# Interactive quantum adversaries with classical messages are classical randomized strategies

An interactive adversary of the model (`KindAlg`, and `AdaptiveIAlg` through `toKindAlg`: Unruh
2017, ePrint 2017/398, p. 10, oracle algorithms that choose at run time between queries and
requests) keeps a quantum workspace across all its slots, queries the random oracle `H` in
superposition, and sends classical requests to a classical challenger (`Challenger`), whose
classical replies may depend on its coins, the history and `H`. Its semantics is the composed
core algorithm (`KindAlg.composeBoth`, `AdaptiveIAlg.compose`).

**The conditional-sampling simulation** (`outLaw_composeBoth_some_eq`): for every oracle `H`,
the output law of the composed algorithm equals the output law of one classical randomized
strategy (`KindAlg.classicalSim`, a behavioral strategy of
`GordieHowe/Foundations/Probability/Interaction.lean`) against the challenger as a classical
challenger with input `H` (`Challenger.classicalAt`): in each slot the strategy draws its move
(a request, or a query slot) from the adversary's conditional law given the classical
transcript so far, and its output from the conditional law given the whole transcript; on a
branch whose halting flag is set (`KindAlg.dilOut`) the strategy outputs `none`. Since both laws
are laws on `Option O`, the whole output law is the strategy's output law
(`outLaw_composeBoth_eq_map`): the probability of the output `none` is that of the strategy's
output `none` (`outLaw_composeBoth_none_eq`), and every event of the output has the probability
of the strategy's output lying in it (`toOuterMeasure_outLaw_composeBoth`). The strategy is
defined from the adversary alone; it receives the oracle `H` whole as its input and the oracle in
force with each reply.

The proof is the pure-game simulation (`Distinguisher.acceptProbOnAt_eq_cont`,
`GordieHowe/Model/Quantum/Pure/ClassicalSim.lean`) for the dilated adversary
(`KindAlg.dilate`), whose acceptance on each output is the composed algorithm's output law
(`KindAlg.outLaw_composeBoth_some`, `mgAccept_deph`, `acceptProbAt_dilate`). The dilations for
the different outputs differ only in their accepting sets, so one strategy serves every output
(`classicalSim_eq_dilate`).

`advantage_outLaw_composeBoth_le_of_det`: with the derandomization of behavioral strategies
(`Interaction.abs_winDiff_le_of_det`), a bound `ε` on the advantage of every deterministic
classical strategy between two challengers at `H` for the event of the output `some o` bounds by
`ε` the advantage of every interactive quantum adversary between them at `H` for the output `o`.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

namespace Challenger

variable {X Y Req Resp : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  (C : Challenger X Y Req Resp)

/-- **The challenger at the oracle `H` as a classical challenger**: its coins drawn from its law,
the oracle `H` as the adversary's input, and the visible replies of the pure game at the tape
`(H, c)` (`Env.toClassical`). -/
noncomputable def classicalAt (H : X → Y) :
    Interaction.Challenger C.Coins (X → Y) (Option Req) (Option Resp × (X → Y)) :=
  C.toPureEnv.toClassical C.coins fun c => (H, c)

end Challenger

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {ksA : KindShape X Y Req Resp} (A : KindAlg ksA O)

/-- The output of a basis state of the dilated adversary's registers: `none` on a halted branch
(the halting flag set), the adversary's output read from the workspace otherwise. -/
def dilOut (x : DReg A.DW A.width X Y Req Resp) : Option O :=
  if x.1.1.2.1 then none else some (A.out x.1.1.1)

/-- **The classical strategy of an interactive adversary**: the classical strategy
(`Distinguisher.classical`) of its dilation (the kind register, initial state and steps of
`KindAlg.dilate`, which do not depend on the output; the accepting set is not read), with the
output read as the adversary's output or `none` on a halted branch. -/
noncomputable def classicalSim :
    Interaction.Strategy (X → Y) (Option Req) (Option Resp × (X → Y)) (Option O) :=
  (Distinguisher.classical (m := A.slots)
    { kind := fun w => A.kind w.1 || w.2.1
      init := Quantum.relabel A.relD A.dInitVec
      norm_init := by rw [LinearIsometryEquiv.norm_map, A.norm_dInitVec]
      step := fun k : Fin (A.slots + 1) => A.uStepD k
      accept := ∅ } A.postOp).mapOut A.dilOut

omit [Nonempty X] [Nonempty Y] in
/-- The classical strategy is that of the dilation for any output `o`. -/
theorem classicalSim_eq_dilate [DecidableEq O] (o : O) :
    A.classicalSim = ((A.dilate o).classical A.postOp).mapOut A.dilOut := by
  rw [classicalSim, Distinguisher.classical_congr _ (A.dilate_kind o).symm (A.dilate_init o).symm
    (funext fun k => (A.dilate_step o k).symm)]

omit [Nonempty X] [Nonempty Y] in
/-- The accepting event of the dilation for the output `o` is the event that the output read by
`dilOut` is `some o`. -/
theorem acceptEvent_dilate [DecidableEq O] (o : O) :
    (A.dilate o).acceptEvent Set.univ =
      Prod.map id A.dilOut ⁻¹' {p : Interaction.Hist (Option Req) (Option Resp × (X → Y)) ×
        Option O | p.2 = some o} := by
  ext p
  simp only [Distinguisher.acceptEvent, dilate_accept, Set.mem_univ, true_and, Set.mem_ofPred_eq,
    Set.mem_preimage, Prod.map, dilOut]
  split_ifs with h <;> simp [h]

/-- **The conditional-sampling simulation** (module docstring): at every oracle `H`, the
probability that the composed algorithm of the adversary and the challenger outputs `o` is the
probability that the adversary's classical strategy outputs `some o` against the challenger at
`H` as a classical challenger. -/
theorem outLaw_composeBoth_some_eq [DecidableEq O] (C : Challenger X Y Req Resp) (H : X → Y)
    (o : O) :
    (A.composeBoth C).outLaw H (some o) =
      (Interaction.exper A.classicalSim (C.classicalAt H) A.slots).toOuterMeasure
        {p | p.2 = some o} := by
  have hacc : ∀ c : C.Coins, A.mgAccept C.toPureEnv o (H, c) true =
      (A.dilate o).acceptProbOnAt C.toPureEnv A.postOp Set.univ (H, c) := fun c => by
    rw [Distinguisher.acceptProbOnAt_univ, mgAccept_deph, acceptProbAt_dilate]
  have hwin := (A.dilate o).tsum_acceptProbOnAt_eq_winProb C.toPureEnv A.postOp C.coins
    (fun c => (H, c)) Set.univ
  rw [acceptEvent_dilate, ← Interaction.winProb_mapOut, ← classicalSim_eq_dilate] at hwin
  rw [outLaw_composeBoth_some]
  simp only [hacc]
  rw [← tsum_fintype (L := SummationFilter.unconditional _) (fun c : C.Coins =>
      (C.coins c).toReal * (A.dilate o).acceptProbOnAt C.toPureEnv A.postOp Set.univ (H, c)),
    hwin, Interaction.winProb,
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
      (PMF.toOuterMeasure_apply_le_one _ _))]
  rfl

/-- **The output law of the composition is the classical strategy's output law** at every oracle
`H`: `outLaw_composeBoth_some_eq` for the outputs `some o`, and hence also for `none`
(`PMF.ext_of_some`). -/
theorem outLaw_composeBoth_eq_map [DecidableEq O] (C : Challenger X Y Req Resp) (H : X → Y) :
    (A.composeBoth C).outLaw H =
      (Interaction.exper A.classicalSim (C.classicalAt H) A.slots).map Prod.snd :=
  PMF.ext_of_some fun o => by
    rw [outLaw_composeBoth_some_eq, ← PMF.toOuterMeasure_apply_singleton,
      PMF.toOuterMeasure_map_apply]
    rfl

/-- **Non-termination in the classical simulation**: at every oracle `H`, the probability that the
composed algorithm outputs `none` is the probability that the adversary's classical strategy
outputs `none` against the challenger at `H`. -/
theorem outLaw_composeBoth_none_eq [DecidableEq O] (C : Challenger X Y Req Resp) (H : X → Y) :
    (A.composeBoth C).outLaw H none =
      (Interaction.exper A.classicalSim (C.classicalAt H) A.slots).toOuterMeasure
        {p | p.2 = none} := by
  rw [outLaw_composeBoth_eq_map, ← PMF.toOuterMeasure_apply_singleton,
    PMF.toOuterMeasure_map_apply]
  rfl

/-- **Events of the output in the classical simulation**: at every oracle `H`, an event `E` of the
composed algorithm's output (`none` included) has the probability that the classical strategy's
output lies in `E`. -/
theorem toOuterMeasure_outLaw_composeBoth [DecidableEq O] (C : Challenger X Y Req Resp)
    (H : X → Y) (E : Set (Option O)) :
    ((A.composeBoth C).outLaw H).toOuterMeasure E =
      (Interaction.exper A.classicalSim (C.classicalAt H) A.slots).toOuterMeasure
        {p | p.2 ∈ E} := by
  rw [outLaw_composeBoth_eq_map, PMF.toOuterMeasure_map_apply]
  rfl

/-- **Interactive quantum adversaries are no better than deterministic classical strategies**: if
every deterministic classical strategy (moves and output as functions of the oracle `H` and the
visible history) has advantage at most `ε` between the challengers `C₀` and `C₁` at `H` as
classical challengers, every interactive adversary has advantage at most `ε` between them at
`H`, for the event that it outputs `o`. -/
theorem advantage_outLaw_composeBoth_le_of_det [Fintype O] [DecidableEq O]
    (C₀ C₁ : Challenger X Y Req Resp) (H : X → Y) (o : O) {ε : ℝ}
    (hdet : ∀ s : Interaction.DetStrategy (X → Y) (Option Req) (Option Resp × (X → Y)) (Option O),
      |Interaction.winProb s.toStrategy (C₀.classicalAt H) A.slots {p | p.2 = some o} -
        Interaction.winProb s.toStrategy (C₁.classicalAt H) A.slots {p | p.2 = some o}| ≤ ε) :
    GordieHowe.advantage ((A.composeBoth C₀).outLaw H (some o)).toReal
      ((A.composeBoth C₁).outLaw H (some o)).toReal ≤ ε := by
  rw [GordieHowe.advantage, outLaw_composeBoth_some_eq, outLaw_composeBoth_some_eq]
  exact Interaction.abs_winDiff_le_of_det _ _ _ _ A.slots hdet

end KindAlg

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O)

/-- **The conditional-sampling simulation for adversaries with run-time kinds and a query
budget** (`KindAlg.outLaw_composeBoth_some_eq` for `toKindAlg`): at every oracle `H`, the
composition with a challenger outputs `o` with the probability that the adversary's classical
strategy outputs `some o` against the challenger at `H`. -/
theorem outLaw_compose_some_eq [DecidableEq O] (C : Challenger X Y Req Resp) (H : X → Y) (o : O) :
    (A.compose C).outLaw H (some o) =
      (Interaction.exper A.toKindAlg.classicalSim (C.classicalAt H) A.slots).toOuterMeasure
        {p | p.2 = some o} :=
  A.toKindAlg.outLaw_composeBoth_some_eq C H o

/-- **`KindAlg.outLaw_composeBoth_eq_map` for adversaries with run-time kinds and a query
budget.** -/
theorem outLaw_compose_eq_map [DecidableEq O] (C : Challenger X Y Req Resp) (H : X → Y) :
    (A.compose C).outLaw H =
      (Interaction.exper A.toKindAlg.classicalSim (C.classicalAt H) A.slots).map Prod.snd :=
  A.toKindAlg.outLaw_composeBoth_eq_map C H

/-- **`KindAlg.outLaw_composeBoth_none_eq` for adversaries with run-time kinds and a query
budget**: non-termination has the probability of the classical strategy's output `none`. -/
theorem outLaw_compose_none_eq_exper [DecidableEq O] (C : Challenger X Y Req Resp) (H : X → Y) :
    (A.compose C).outLaw H none =
      (Interaction.exper A.toKindAlg.classicalSim (C.classicalAt H) A.slots).toOuterMeasure
        {p | p.2 = none} :=
  A.toKindAlg.outLaw_composeBoth_none_eq C H

/-- **`KindAlg.toOuterMeasure_outLaw_composeBoth` for adversaries with run-time kinds and a query
budget.** -/
theorem toOuterMeasure_outLaw_compose [DecidableEq O] (C : Challenger X Y Req Resp) (H : X → Y)
    (E : Set (Option O)) :
    ((A.compose C).outLaw H).toOuterMeasure E =
      (Interaction.exper A.toKindAlg.classicalSim (C.classicalAt H) A.slots).toOuterMeasure
        {p | p.2 ∈ E} :=
  A.toKindAlg.toOuterMeasure_outLaw_composeBoth C H E

/-- **`KindAlg.advantage_outLaw_composeBoth_le_of_det` for adversaries with run-time kinds and a
query budget.** -/
theorem advantage_outLaw_compose_le_of_det [Fintype O] [DecidableEq O]
    (C₀ C₁ : Challenger X Y Req Resp) (H : X → Y) (o : O) {ε : ℝ}
    (hdet : ∀ s : Interaction.DetStrategy (X → Y) (Option Req) (Option Resp × (X → Y)) (Option O),
      |Interaction.winProb s.toStrategy (C₀.classicalAt H) A.slots {p | p.2 = some o} -
        Interaction.winProb s.toStrategy (C₁.classicalAt H) A.slots {p | p.2 = some o}| ≤ ε) :
    GordieHowe.advantage ((A.compose C₀).outLaw H (some o)).toReal
      ((A.compose C₁).outLaw H (some o)).toReal ≤ ε :=
  A.toKindAlg.advantage_outLaw_composeBoth_le_of_det C₀ C₁ H o hdet

end AdaptiveIAlg

end GordieHowe.Quantum
