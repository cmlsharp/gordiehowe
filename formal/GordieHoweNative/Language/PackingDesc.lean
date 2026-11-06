-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Export

/-!
# GordieHowe: the packing descriptor of a field

A field's packing facts (`GordieHowe.RealizedProgram.FieldInterp.Packing`, Mathlib-side) at the
queries a program's checks make, as naturals, Booleans and strings (`PackingDesc`), with its
lookups. The program data's field table (`FieldTable.packing`) holds one per field; a field's
packing facts are checked equal to it at its keys (`FieldInterp.Packing.desc`), and the domains'
checks read it (`fieldOkBD`, `fieldOkB_of_desc`).
-/

@[expose] public section

namespace GordieHowe

open RealizedProgram

/-- **The packing descriptor of a field**: the packing facts a program's checks read, at the
points the program queries, as naturals, Booleans and strings, checked once against the
interpretation's packing facts (`FieldInterp.Packing.desc`). -/
structure PackingDesc where
  /-- The degree of the field over its prime field (`FieldInterp.Packing.n`). -/
  n : Nat := 0
  /-- The size of the evaluation domain (`FieldInterp.Packing.q`). -/
  q : Nat := 0
  /-- At each queried child degree, relative degree and masking mode, whether the field realizes
  the edge (`FieldInterp.Packing.edge`). -/
  edges : List (Nat × Nat × Export.PackingMode × Bool) := []
  /-- At each queried node name, its degree (`FieldInterp.Packing.nodeDeg`). -/
  nodeDegs : List (String × Option Nat) := []
  /-- At each queried width and degree, whether the field has the skip domain
  (`FieldInterp.Packing.skip`). -/
  skips : List (Nat × Nat × Bool) := []
  /-- Whether the field has the bit sumcheck's interpolation nodes (`FieldInterp.Packing.nodes`). -/
  hasNodes : Bool := false
  /-- At each queried child degree, relative degree and masking mode, the mask cells of the
  field's kit for the edge, before the tableau's rows and in them (`masks.nPre`, `masks.nOwn`;
  `(0, 0)` where the field does not realize the edge). -/
  masks : List (Nat × Nat × Export.PackingMode × Nat × Nat) := []
  deriving Repr, DecidableEq, Inhabited

namespace PackingDesc

/-- **Whether the descriptor's field realizes the edge** of child degree `m`, relative degree `k`
and masking mode `mode`: the queried entry's answer, `false` when the descriptor has no entry. -/
def edgeOk (D : PackingDesc) (m k : Nat) (mode : Export.PackingMode) : Bool :=
  match D.edges.find? (fun x => x.1 == m && x.2.1 == k && x.2.2.1 == mode) with
  | some x => x.2.2.2
  | none => false

/-- **The degree of node `s`** in the descriptor's field, `none` when the descriptor has no
entry for `s`. -/
def nodeDeg? (D : PackingDesc) (s : String) : Option (Option Nat) :=
  (D.nodeDegs.find? (·.1 == s)).map (·.2)

/-- **Whether the descriptor's field has the skip domain** of width `w` at degree `k`: the
queried entry's answer, `false` when the descriptor has no entry. -/
def skipOk (D : PackingDesc) (w k : Nat) : Bool :=
  match D.skips.find? (fun x => x.1 == w && x.2.1 == k) with
  | some x => x.2.2
  | none => false

/-- **The mask cells of the kit for the edge** of child degree `m`, relative degree `k` and
masking mode `mode`, before the tableau's rows and in them: the queried entry's answer, `(0, 0)`
when the descriptor has no entry. -/
def maskNums (D : PackingDesc) (m k : Nat) (mode : Export.PackingMode) : Nat × Nat :=
  match D.masks.find? (fun x => x.1 == m && x.2.1 == k && x.2.2.1 == mode) with
  | some x => x.2.2.2
  | none => (0, 0)

/-- **Every plan edge has a mask query** in the descriptor. The numbers at those keys are
validated separately by `FieldInterp.Packing.desc`. -/
def masksCoverB (D : PackingDesc) (es : List Export.PackingEdge) : Bool :=
  es.all fun e => (D.masks.find? fun x =>
    x.1 == e.childDegree && x.2.1 == e.degree && x.2.2.1 == e.mode).isSome

end PackingDesc

end GordieHowe
