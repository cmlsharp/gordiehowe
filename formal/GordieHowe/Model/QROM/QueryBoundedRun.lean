-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.AdaptiveCount
public import GordieHowe.Model.Quantum.Interactive.QueryBounded
public import GordieHowe.Model.Quantum.Interactive.TPRun

@[expose] public section

/-!
# The run of a request-free query-bounded adversary

The semantics of a query-bounded adversary of `def:adversary` (`Quantum.QueryBoundedAdversary`)
that makes no requests, as used by the knowledge-soundness games of the compiled arguments
(`GordieHowe/Model/NARG/QROM.lean`, `GordieHowe/SPBCS/Extraction/OnlineExtract.lean`):

- `nullChallenger`: the challenger that answers nothing;
- `AdaptiveIAlg.tpRun`, `QueryBoundedAdversary.run`: the real run, the trace-preserving form
  composed with `nullChallenger`; `QueryBoundedAdversary.modelRun`: the model's run
  (`AdaptiveIAlg.compose`);
- `QueryBoundedAdversary.cohQueryCount`, `queryCount_le`: the coherent pure form of the real run
  makes at most `width * (budget + post) ≤ t` unpadded queries on every branch
  (`AdaptiveIAlg.tpQueryCount`).
-/

namespace GordieHowe.Quantum

/-- **The challenger that answers nothing**: no coins, no request answered (`Q = 0`), no queries.
Composed with an adversary, its request slots are idle slots. -/
noncomputable def nullChallenger (X Y Req Resp : Type) : Challenger X Y Req Resp where
  Coins := Unit
  coins := PMF.pure ()
  Q := 0
  q := 0
  respond _ _ _ := .pure ⟨none, []⟩
  respond_queries := by
    intros
    simp [OracleProg.trace]

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] (A : AdaptiveIAlg X Y Req Resp O)

/-- **The run of a request-free adversary** (proof-internal semantics of the knowledge-soundness
game): the composition of the trace-preserving form of `A` with the challenger that answers
nothing, with `A`'s output read from its workspace. -/
noncomputable abbrev tpRun : Alg X Y O :=
  A.toTPKindAlg.composeBothOut (nullChallenger X Y Req Resp) fun v => A.out v.adv.workspace.1

end AdaptiveIAlg

namespace QueryBoundedAdversary

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {t : ℕ} (𝒢 : QueryBoundedAdversary X Y Req Resp O t)

/-- **The real run of `𝒢` without requests at the auxiliary input `a`** (`AdaptiveIAlg.tpRun`):
its trace-preserving form composed with the challenger that answers nothing. -/
noncomputable abbrev run (a : 𝒢.Aux) : Alg X Y O :=
  (𝒢.alg a).tpRun

/-- **The model's run of `𝒢` without requests at `a`** (`AdaptiveIAlg.compose` with the
challenger that answers nothing): over-budget branches are projected away. -/
noncomputable abbrev modelRun (a : 𝒢.Aux) : Alg X Y O :=
  (𝒢.alg a).compose (nullChallenger X Y Req Resp)

end QueryBoundedAdversary

end GordieHowe.Quantum

namespace GordieHowe.Quantum.QueryBoundedAdversary

open GordieHowe.QROM

variable {m : ℕ} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {B : Type} (e : BitStr I J ≃ B) {O : Type} {t : ℕ}
  (𝒢 : QueryBoundedAdversary (Bits m) (BitStr I J) Unit Empty O t)

/-- **The coherent pure form of the real run makes at most `width * (budget + post)` unpadded
queries on every branch** (`AdaptiveIAlg.tpQueryCount` with the challenger that answers
nothing). -/
noncomputable def cohQueryCount (a : 𝒢.Aux) :
    QueryCount e (𝒢.run a).toQueryAlgCoh
      ((𝒢.alg a).width * (𝒢.alg a).budget + 0 * 0 + (𝒢.alg a).width * (𝒢.alg a).post) :=
  AdaptiveIAlg.tpQueryCount e (𝒢.alg a) (nullChallenger _ _ Unit Empty)
    (fun v => (𝒢.alg a).out v.adv.workspace.1) id

theorem queryCount_le (a : 𝒢.Aux) :
    (𝒢.alg a).width * (𝒢.alg a).budget + 0 * 0 + (𝒢.alg a).width * (𝒢.alg a).post ≤ t := by
  have := 𝒢.queries_le a
  rw [Nat.mul_add] at this
  omega

end GordieHowe.Quantum.QueryBoundedAdversary
