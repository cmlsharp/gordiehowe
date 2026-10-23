-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.AdaptiveTP

@[expose] public section

/-!
# Query-bounded adversaries

The one adversary class of the headline theorems: the `(t, Q)`-adversaries of the paper's
`def:adversary` (Definition 6.1), after Unruh 2017 (ePrint 2017/398, section 3, p. 10) and CMS19
(section 3.2, p. 14). A member

- chooses at run time, from a measured kind register, whether each call is a query to the random
  oracle or a proof query to the second oracle (`AdaptiveIAlg`);
- applies quantum channels between calls: trace-preserving Kraus maps, which include measurements
  with a classical outcome register (`AdaptiveIAlg.TracePreserving`);
- starts from auxiliary input drawn independently of the oracle and an arbitrary mixed initial
  state on each value;
- makes at most `t` queries on every branch, over its query slots and its post phase
  (`QueryBoundedAdversary.queries_le`);
- outputs the computational-basis measurement of its workspace read by `out`.

Proof queries are not bounded by the class: every challenger answers the first `Q` proof queries and gives
`none` after that, so the class contains every adversary with at most `Q` proof queries, and a theorem
over the class holds for those.

The other adversary forms (`SimExtractionAdversary`, the fixed-order
`Adversary` of knowledge soundness) are proof devices; their theorems are restated over this class
through the maps of this file.
-/

open Finset Matrix
open scoped BigOperators ENNReal

namespace GordieHowe

namespace Quantum.AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]

/-- **Every step of the adversary is a channel**: each of its Kraus maps is trace-preserving,
`∑ r, (op r)ᴴ * op r = 1` (Unruh 2017 p. 10: every primitive of an oracle algorithm, a unitary
gate, a computational-basis measurement, a partial trace or a fresh qubit, preserves the trace). -/
def TracePreserving (A : AdaptiveIAlg X Y Req Resp O) : Prop :=
  ∀ k, ∑ r, ((A.step k).op r)ᴴ * (A.step k).op r = 1

theorem tracePreserving_iff (A : AdaptiveIAlg X Y Req Resp O) :
    A.TracePreserving ↔ ∀ k, ∑ r, ((A.step k).op r)ᴴ * (A.step k).op r = 1 :=
  Iff.rfl

/-- Whether the branch of a composed register has ended (its query counter is `ended`). -/
def endedFlag (A : AdaptiveIAlg X Y Req Resp O) (C : Challenger X Y Req Resp)
    (v : A.toKindAlg.CW C) : Bool :=
  decide (v.adv.workspace.2 = A.ended)

variable [Nonempty X] [AddGroup Y] [Nonempty Y]

/-- **The adversary stays within its budget on every branch** (the every-branch query bound of
the paper's `def:adversary`): against every challenger and every oracle, its trace-preserving form
(`toTPKindAlg`, in which a branch that asks for a query slot over `budget` aborts to the ended
value of its counter) ends with probability `0`. So the branches of positive weight never ask for
an over-budget query slot. The ended value also receives the weight the adversary's own Kraus maps
lose; for a trace-preserving adversary there is none (`TracePreserving.haltOp_eq_zero`).
Equivalently, the model's run (`compose`) never fails to terminate (`withinBudget_iff`). -/
def WithinBudget (A : AdaptiveIAlg X Y Req Resp O) : Prop :=
  ∀ (C : Challenger X Y Req Resp) (H : X → Y),
    (A.toTPKindAlg.composeBothOut C (A.endedFlag C)).outLaw H (some true) = 0

end Quantum.AdaptiveIAlg

/-- **A `t`-query adversary** (the paper's `(t, Q)`-adversary, `def:adversary`; Unruh 2017
section 3, p. 10; CMS19 section 3.2, p. 14): auxiliary input drawn independently of the oracle,
then on each value an interactive adversary that chooses the kind of each slot at run time
(`AdaptiveIAlg`), whose steps are channels (`tracePreserving`), which never asks for a query slot
over its budget on a branch of positive weight (`withinBudget`), and which makes at most `t`
queries on every branch, `width` per query slot over at most `budget` query slots and `width` per
post batch (`queries_le`). -/
structure Quantum.QueryBoundedAdversary (X Y Req Resp O : Type) [Fintype X] [Fintype Y] [Fintype Req]
    [Fintype Resp] [DecidableEq X] [DecidableEq Y] [DecidableEq Req] [DecidableEq Resp]
    [Nonempty X] [AddGroup Y] [Nonempty Y] (t : ℕ) where
  /-- The values of the auxiliary input. -/
  Aux : Type
  /-- The distribution of the auxiliary input, independent of the oracle. -/
  aux : PMF Aux
  /-- The adversary run on each value of the auxiliary input. -/
  alg : Aux → AdaptiveIAlg X Y Req Resp O
  /-- Every step is a channel. -/
  tracePreserving : ∀ a, (alg a).TracePreserving
  /-- No branch of positive weight asks for a query slot over the budget. -/
  withinBudget : ∀ a, (alg a).WithinBudget
  /-- At most `t` queries on every branch: the query slots and the post phase. -/
  queries_le : ∀ a, (alg a).width * ((alg a).budget + (alg a).post) ≤ t

namespace Quantum.QueryBoundedAdversary

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {T : ℕ} (𝒜 : QueryBoundedAdversary X Y Req Resp O T)

/-- **The probability that a bit-valued adversary outputs `true` against the challenger `C`**:
the oracle uniform, the auxiliary input drawn, and the composed core algorithm run. -/
noncomputable def acceptProb (𝒟 : QueryBoundedAdversary X Y Req Resp Bool T)
    (C : Challenger X Y Req Resp) : ℝ≥0∞ :=
  ∑' a, 𝒟.aux a * (((𝒟.alg a).compose C).realLaw (Equiv.refl Y)).toOuterMeasure
    {p | p.out = some true}

end Quantum.QueryBoundedAdversary

namespace QROM

variable {X Y Stmt Wit Proof Coins SimCoins : Type} (rel : Stmt → Wit → Prop) [DecidableRel rel]
  [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [AddGroup Y]
  [Fintype Stmt] [Fintype Wit] [DecidableEq Stmt] [DecidableEq Wit] [Fintype Proof]
  [DecidableEq Proof] [Nonempty X] [DecidableEq Y] [Fintype Coins] [DecidableEq Coins]
  [Fintype SimCoins] [DecidableEq SimCoins]

variable {rel}

end QROM

end GordieHowe
