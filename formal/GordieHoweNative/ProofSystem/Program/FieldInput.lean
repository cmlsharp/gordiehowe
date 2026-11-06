-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.ProofSystem.Program.FieldTree
public import GordieHoweNative.Language.RealizedProgram.Valid

/-!
# GordieHowe: the compiled definitions of `GordieHowe.ProofSystem.Program.FieldInput`

The definitions of `GordieHowe.ProofSystem.Program.FieldInput` that the field checks run (the bit edges, the viewed words and the entries' predicates), in the
Mathlib-free library `GordieHoweNative`, which Lake compiles to a shared library
(`precompileModules`): native mode runs the checkers as compiled code. The declarations keep their
names. Their lemmas are in `GordieHowe/ProofSystem/Program/FieldInput.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- **A bit edge**: `F_2 <16` with squaring-chain masks (`isView` without its parent). -/
def isBitEdge (e : PackingEdge) : Bool :=
  e.childDegree == 1 && e.degree == 16 && e.mode == .squaringChain

section

variable (ir : RealizedProgram)

/-- **The words of value `w` are viewed**: its type is named after its node, some edge's child is
its node, and some bit edge's parent is its node (a sweep of the edges; `viewableB_iff` is the
lookup form, `nodeIdx` then `viewChild`). -/
def viewableB (es : List PackingEdge) (w : ℕ) : Bool :=
  match (ir.value w).node with
  | some nr => ((ir.value w).type.nodeName.getD "") == nr.name &&
      es.any (fun e => e.child == nr.name) &&
      es.any (fun e => isBitEdge e && e.parent == nr.name)
  | none => false

/-- **Entry `e` names a predicate of the program**, when it names one. -/
def entryPredOkB : CircuitEntry → Bool
  | .pred p => decide (p < ir.predicates.length)
  | .typeCheck p => decide (p < ir.predicates.length)
  | _ => true

end

end GordieHowe.RealizedProgram
