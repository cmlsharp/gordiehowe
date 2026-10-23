-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.CircuitClasses
public import GordieHowe.Model.Quantum.Interactive.Output

@[expose] public section

/-!
# A trace-preserving Kraus map keeps every constant function

`KrausMap.keeps_const`. For an adversary followed by a test, the statement that every Kraus map of
the composed circuit after the junction keeps the copy register and the challenger's registers is
in `GordieHowe/Model/QROM/AdaptiveTestClasses.lean` (`AdaptiveIAlg.copyChal`,
`AdaptiveIAlg.stepsKeep_composeBothOut_withTest`); it gives the hypothesis of
`Alg.keepsClasses_toQueryAlgCoh`.
-/

open Finset Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

namespace KrausMap

variable {R Γ : Type*} {ι : Type} [Fintype R] [Fintype ι] [DecidableEq ι]

/-- A trace-preserving Kraus map keeps every constant function. -/
theorem keeps_const {K : KrausMap R ι ι} (htp : ∑ r, (K.op r)ᴴ * K.op r = 1) (c : Γ) :
    K.Keeps fun _ => c where
  tp := htp
  keeps _ _ _ _ := rfl

end KrausMap

namespace IAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {A : IAlg X Y Req Resp O} (T : A.QTest) (C : Challenger X Y Req Resp)

end IAlg

end GordieHowe.Quantum
