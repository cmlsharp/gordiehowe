-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.QueryBounded
public import GordieHowe.Foundations.Probability.Advantage

@[expose] public section

/-!
# The adversaries of the ring-signature games

One adversary class for every ring-signature game: interactive quantum algorithms in the quantum
random-oracle model (`Quantum.QueryBoundedAdversary`, the paper's `(t, Q)`-adversaries: run-time
kinds, quantum memory across rounds, classical requests and replies, auxiliary input independent
of the oracle, at most `t` superposition queries on every branch), given a classical start input.

- `OracleView X Y`: the part of the oracle `X → Y` a game hands to the adversary whole, as a
  classical table (`Tab`, read off the oracle by `view`). The adversary also has at most `t`
  superposition queries to the whole oracle. `OracleView.queriesOnly` hands out nothing (the
  unforgeability games: query access only); `OracleView.whole` hands out the whole oracle (the
  statistical anonymity results); `OracleView.tableOn P` hands out the oracle on the points
  satisfying `P` and leaves the other points to queries (the anonymity of the ML-DSA ring publishing
  `w₁`, whose mask derivation is queried, not tabulated).
- `GameAdversary X Y Req Resp In O t`: on each start input `In` (the honest users' key coins, or
  their public keys, with the table), a `t`-query adversary with requests `Req`, replies `Resp`
  and output `O`.
- `Quantum.AdaptiveIAlg.history`: the requests answered in a run, with their replies, read from
  the composed registers. `Quantum.AdaptiveIAlg.length_history_le`: at most `Q` of them.
- `Quantum.QueryBoundedAdversary.transcriptLaw`: at the oracle `H` against the challenger `C`, the
  law of the adversary's output with the history (`none`: no termination).
- `runLaw`: the law of a game's run: start draws (the users' key coins) uniform, the oracle
  uniform, the adversary of the start input and the oracle's table against the challenger of the
  start draws. Every game probability is an event of this one law, so it is at most `1`
  (`prob_runLaw_le_one`).
- `RunOutIn E`: the event of a run's law that the adversary terminates with an output in `E`.

## Sources and deliberate differences

The class is the paper's `def:adversary` (Unruh 2017, ePrint 2017/398, section 3, p. 10; CMS19,
section 3.2, p. 14), with requests to a classical challenger (GHS16 p. 10, "challenger model").
BKM06 (ePrint 2005/304) states its games for ppt adversaries and plain-model algorithms. Here:

1. The adversaries are quantum, in the QROM, and need not be efficient: the bounds are in the query
   count `t` and the request count `Q` (every challenger answers the first `Q` requests). A
   classical or randomized adversary is a member of the class.
2. The adversary's start input is classical and given before its first step (BKM06 Definition 4
   hands out the key coins at the challenge; Definition 7 hands out the public keys at the start).
3. Per game, a part of the oracle may be handed out whole (`OracleView`): such results are
   statistical in that part. BKM06 has no random oracle.
-/

namespace GordieHowe

open GordieHowe.Quantum
open scoped ENNReal

namespace RingSignature

/-- **The part of the oracle a game hands out whole**: a classical table `Tab`, read off the
oracle by `view`. The adversary has superposition queries to the whole oracle besides. -/
structure OracleView (X Y : Type) where
  /-- The table. -/
  Tab : Type
  /-- The table of an oracle. -/
  view : (X → Y) → Tab

namespace OracleView

variable (X Y : Type)

/-- **No table**: the adversary reaches the oracle by queries only. -/
def queriesOnly : OracleView X Y := ⟨Unit, fun _ => ()⟩

/-- **The whole oracle as a table.** -/
def whole : OracleView X Y := ⟨X → Y, id⟩

variable {X} in
/-- **The oracle on the points satisfying `P` as a table**; the other points by queries only. -/
def tableOn (P : X → Prop) : OracleView X Y := ⟨{x // P x} → Y, fun H x => H x.1⟩

end OracleView

/-- **An adversary of a ring-signature game** with start input `In`: on each start input, a
`t`-query adversary (`Quantum.QueryBoundedAdversary`) with requests `Req`, replies `Resp` and output
`O`. -/
abbrev GameAdversary (X Y Req Resp In O : Type) [Fintype X] [Fintype Y] [Fintype Req]
    [Fintype Resp] [DecidableEq X] [DecidableEq Y] [DecidableEq Req] [DecidableEq Resp]
    [Nonempty X] [AddGroup Y] [Nonempty Y] (t : ℕ) : Type 1 :=
  In → QueryBoundedAdversary X Y Req Resp O t

end RingSignature

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]

namespace Quantum.AdaptiveIAlg

variable {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (C : Challenger X Y Req Resp)

/-- **The answered requests with their replies**, read from the composed registers `v`: the
challenger's history after the last slot. -/
def history (v : A.toKindAlg.CW C) : List (HistoryEntry Req Resp) :=
  (A.toKindAlg.stateAt C v.chal A.toKindAlg.slots).history

/-- **The adversary's output**, read from the composed registers `v`. -/
def output (v : A.toKindAlg.CW C) : O :=
  A.out v.adv.workspace.1

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] in
/-- **A challenger's record holds at most `Q` requests**: the history read from the logs and the
answers after any number of slots. -/
theorem length_regStateOf_le {Coins : Type} (Q : ℕ)
    (respond : Coins → List (HistoryEntry Req Resp) → Req → OracleProg X Y (Reply X Y Resp))
    {m : ℕ} (ω : Coins) (lg : LogReg Req m) (ans : Fin m → List Y) :
    ∀ j, (Challenger.regStateOf Q respond ω lg ans j).history.length ≤ Q
  | 0 => by simp [Challenger.regStateOf]
  | j + 1 => by
    have ih := length_regStateOf_le Q respond ω lg ans j
    rw [Challenger.regStateOf]
    dsimp only
    split
    · split
      · exact ih
      · split
        · simp only [List.length_append, List.length_singleton]
          omega
        · exact ih
    · exact ih

/-- **At most `Q` requests are answered in a run.** -/
theorem length_history_le (v : A.toKindAlg.CW C) : (A.history C v).length ≤ C.Q :=
  length_regStateOf_le C.Q C.respond _ _ _ _

end Quantum.AdaptiveIAlg

variable [Nonempty X] [AddGroup Y] [Nonempty Y] {t : ℕ}

namespace Quantum.QueryBoundedAdversary

/-- **The law of the adversary's output and the history** at the oracle `H` against the challenger
`C`: the auxiliary input drawn, then the composed algorithm run, its output and the answered
requests read from the measured registers; `none` when the run does not terminate. -/
noncomputable def transcriptLaw (A : QueryBoundedAdversary X Y Req Resp O t)
    (C : Challenger X Y Req Resp) (H : X → Y) : PMF (Option (O × List (HistoryEntry Req Resp))) :=
  A.aux.bind fun a =>
    ((A.alg a).toKindAlg.composeBothOut C fun v =>
      ((A.alg a).output C v, (A.alg a).history C v)).outLaw H

end Quantum.QueryBoundedAdversary

namespace RingSignature

/-- **The law of a game's run**: the start draws `k` uniform on `K` and the oracle `H` uniform, then
the transcript of the adversary `A k H` against the challenger `C k` at `H`. A game's start input
is a function of `k` and of the table of `H`, so `A k H` is a `GameAdversary` read at it. -/
noncomputable def runLaw {K : Type} [Fintype K] [Nonempty K]
    (A : K → (X → Y) → QueryBoundedAdversary X Y Req Resp O t)
    (C : K → Challenger X Y Req Resp) :
    PMF (K × (X → Y) × Option (O × List (HistoryEntry Req Resp))) :=
  (PMF.uniformOfFintype K).bind fun k =>
    (PMF.uniformOfFintype (X → Y)).bind fun H =>
      ((A k H).transcriptLaw (C k) H).map fun o => (k, H, o)

/-- **A game probability is at most `1`**: every event of the run's law. -/
theorem prob_runLaw_le_one {K : Type} [Fintype K] [Nonempty K]
    (A : K → (X → Y) → QueryBoundedAdversary X Y Req Resp O t) (C : K → Challenger X Y Req Resp)
    (E : Set (K × (X → Y) × Option (O × List (HistoryEntry Req Resp)))) :
    (runLaw A C).toOuterMeasure E ≤ 1 :=
  PMF.toOuterMeasure_apply_le_one _ _

/-- **The output events of a game's run**: the adversary terminates with an output in `E`. -/
def RunOutIn {Start : Type} (E : Set O) :
    Set (Start × (X → Y) × Option (O × List (HistoryEntry Req Resp))) :=
  {x | ∃ p ∈ x.2.2, p.1 ∈ E}

end RingSignature

end GordieHowe
