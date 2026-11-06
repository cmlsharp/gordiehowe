-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Circuit.OpRows
public import GordieHowe.Language.Realizations.Circuit.NttPure
public import GordieHowe.ProofSystem.GKR.Twin
public import GordieHowe.ProofSystem.GKR.CertificateBridge
public import GordieHoweNative.Data
public import GordieHoweNative.Language.Realizations.Circuit.RelTable

@[expose] public section

/-!
# GordieHowe: the cuts of a circuit's node table

The certificate of a GKR circuit (`GordieHowe.RealizedProgram.CircuitData`) holds the scheduling
DAG, the node table of the trees the emitter walked, and per node-table coordinate the wire the
emitter produced (`ENodeInfo.wires`) at the nodes the compiler marked cut (`ENodeInfo.cut`). This
file states, per cut node, the *cuts* the relational check (`GKR.Rel.relOk`) compares: per
coordinate, the node's wire against its one-level expression (`GKR.Rel.TE`) over its kids' tree
expressions, by the node's kind. An uncut node has no wires: its parents expand it.

* **Kids** (`GordieHowe.RealizedProgram.kidTEF`): a node reads a kid below it, at
  coordinates below the kid's length: a cut kid's wires, an uncut kid's expansion
  (`GordieHowe.RealizedProgram.nodeEF`) with the cuts the expansion needs.
* **Operators** (`GordieHowe.RealizedProgram.opTE`): a view reads its operand's coordinates by its
  index map, run by run (`pickL`: a run of step `1` a slice, of step `0` one coordinate repeated,
  any other through a trie); a named operator and a sparse matrix are rows of codes over them
  (`emitRows`, `coefCode`).
* **The kinds** (`GordieHowe.RealizedProgram.nodeStep`): `lin` (the terms' operators, scaled and
  summed), `const`, `scale`, `sum`, `broadcast`, `lnot`, both `mux` forms (the field form with its
  difference `t − e` as aux), `materialize`, `gather`, `apply`, and chains.
* **Chains** (`GordieHowe.RealizedProgram.chainE`): the leaves of a chain root through its uncut
  same-combine kids (`leavesOf`); `add` (and `xor` in characteristic two) the sum of the leaves,
  every other combine a balanced tree whose internal results are the node's aux wires, in
  post-order.
* **Leaves** (`GordieHowe.RealizedProgram.placeCuts`): a value read from the input block its
  placement names (checked to be the value's block of its kind, and the first such), a late value
  as its message input minus its pad input, a value read through its definition as the wires of
  the (cut) node computing it.
* **Nodes** (`GordieHowe.RealizedProgram.nodeCutsE`): a cut node's wires against its expansion; a
  value leaf's placement.

The compiler's choice of cut nodes is not validated: an uncut operand where a product needs a wire
or a constant fails the relational check by itself.

Every checker is written as its failure-reporting twin (`Except CertFailure`); the `Bool` checker is
`Twin.okB` of it.

The definitions are in `GordieHoweNative/Language/Realizations/Circuit/RelTable.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open GordieHowe.GKR.Certificate GordieHowe.GKR.Fold GordieHowe.Twin
open GordieHowe.GKR.Rel (Wire TE Place EntryCert Assert)

/-! ## Tree expressions over wires -/

theorem length_padTo (n : ℕ) (es : List ℕ) : (padTo n es).length = n := by
  simp [padTo]; omega

theorem getD_padTo {n i : ℕ} (es : List ℕ) (h : i < n) : (padTo n es).getD i 0 = es.getD i 0 := by
  unfold padTo
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt h]
  by_cases hi : i < es.length
  · rw [List.getElem?_append_left hi]
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hi), List.getElem?_eq_none (Nat.le_of_not_lt hi),
      List.getElem?_replicate]
    have : i - es.length < n - es.length := by omega
    simp [this]

section Cuts

variable (ir : RealizedProgram) (c : ℕ) (env : TEnv) (E : ETable)

/-! ## Leaves -/

/-- **The cuts of value leaf `k`** (frozen interface): `placeCutsE` as an option. -/
def placeCuts (k : ℕ) : Option (List (Wire × TE)) := (ir.placeCutsE c env E k).toOption

end Cuts

end GordieHowe.RealizedProgram
