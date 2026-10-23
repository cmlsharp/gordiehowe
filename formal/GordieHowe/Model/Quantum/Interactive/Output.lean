-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.PureGame

@[expose] public section

/-!
# The composition with an output read from all classical registers

Games whose outcome depends on the challenger's state, such as simulation-sound extractability
(the verifier runs under the final reprogrammed oracle, and the statement must not have been
sent to the simulator), read their outcome from the classical registers of the composed
algorithm (`IAlg.compose`), not only from the adversary's workspace.

- `IAlg.composeOut A C f`: the composed circuit of `IAlg.compose` with the output `f` of the
  composed registers (adversary registers, logs, the challenger's query registers, coins). It
  has the same final state as `IAlg.compose` (`composeOut_final`).
- `KindAlg.Consistent H v`: the challenger's query registers of `v` hold the query pairs of the
  challenger's programs with the answers of the oracle in force (`Quantum.KindAlg.garFill`), read from the
  logs and coins of `v`.
-/

open Finset Matrix
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  (A : KindAlg X Y Req Resp O) (C : Challenger X Y Req Resp)

/-- **Consistent registers** of a composition with a challenger: the challenger's query registers
hold the query pairs of its programs on the logged requests, with the answers of the oracle `H`
reprogrammed by the assignments in force (`KindAlg.garFill`), at the logs and coins of the
registers. -/
def Consistent (H : X → Y) (v : A.CW C) : Prop :=
  v.chal.queries = A.garFill C H v.chal.coins v.chal.logs A.slots

end KindAlg

namespace IAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] (A : IAlg X Y Req Resp O) (C : Challenger X Y Req Resp)

/-- **The composition with the output `f` of the composed registers**: the circuit of
`IAlg.compose`, its output read by `f` from the adversary's registers, the logs, the challenger's
query registers and its coins. -/
noncomputable abbrev composeOut {O' : Type} (f : A.toKindAlg.CW C → O') : Alg X Y O' :=
  (A.fullCirc C).toCircuit.toAlg (MState.withAnc KindAlg.x₀ (A.toKindAlg.initSys C)) fun v => f v.1

theorem composeOut_final {O' : Type} (f : A.toKindAlg.CW C → O') (H : X → Y) :
    (A.composeOut C f).final H = (A.compose C).final H :=
  rfl

end IAlg

end GordieHowe.Quantum
