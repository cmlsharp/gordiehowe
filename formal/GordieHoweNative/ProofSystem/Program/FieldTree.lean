-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Export
public import GordieHoweNative.Language.RealizedProgram.StructureCheck

/-!
# GordieHowe: the compiled definitions of `GordieHowe.ProofSystem.Program.FieldTree`

The definitions of `GordieHowe.ProofSystem.Program.FieldTree` that the field checks run (the edges of a packing tree and the tree condition), in the
Mathlib-free library `GordieHoweNative`, which Lake compiles to a shared library
(`precompileModules`): native mode runs the checkers as compiled code. The declarations keep their
names. Their lemmas are in `GordieHowe/ProofSystem/Program/FieldTree.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- The edge read outside a list of edges: no child, no parent, degree `0`. -/
def noEdge : PackingEdge := ⟨"", "", .subfieldMasks, 0, 0, 0, 0, 0, 0, true, 0⟩

/-- **The parent edge of edge `a`**: the edge whose child is `a`'s parent (`none`: the root). -/
def parentIdx (es : List PackingEdge) (a : ℕ) : Option ℕ :=
  es.findIdx? fun e => e.child == (es.getD a noEdge).parent

/-- **The edge whose child is node `name`**. -/
def nodeIdx (es : List PackingEdge) (name : String) : Option ℕ :=
  es.findIdx? fun e => e.child == name

/-- **The tree condition at edge `b` (`e`)**, a sweep of the edges with no search: its relative
degree is positive; every edge whose child is `e`'s parent comes later and spans `e`'s edge; and
when no edge's child is `e`'s parent, `e` spans the field. -/
def treeEdgeB (es : List PackingEdge) (n b : ℕ) (e : PackingEdge) : Bool :=
  decide (0 < e.degree) &&
    Twin.okB (Twin.allE (fun j f => Twin.guardE (f.child != e.parent ||
      (decide (b < j) && f.childDegree == e.childDegree * e.degree)) ()) 0 es) &&
    (es.any (·.child == e.parent) || e.childDegree * e.degree == n)

/-- **The tree condition as a check** whose failure names the edge (`treeEdge`). -/
def treeOkE (es : List PackingEdge) (n : ℕ) : Except StructFailure Unit :=
  Twin.allE (fun b e => Twin.guardE (treeEdgeB es n b e) ⟨b, 0, .treeEdge⟩) 0 es

/-- **The tree condition as a test** (`okB` of `treeOkE`). -/
def treeOkB (es : List PackingEdge) (n : ℕ) : Bool := Twin.okB (treeOkE es n)

end GordieHowe.RealizedProgram
