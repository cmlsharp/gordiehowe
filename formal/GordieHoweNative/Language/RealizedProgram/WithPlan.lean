-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram
public import GordieHoweNative.Language.Export.Valid

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.WithPlan`

The plan's domain of each program domain and the nodes of its fields, in the Mathlib-free library
`GordieHoweNative`. The declarations keep their names; their lemmas are in
`GordieHowe/Language/RealizedProgram/WithPlan.lean`, which imports this module.
-/

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- **The plan's domain of program domain `d`**, by position: the compiler lists the plan's domains
and the program's in the compiled system's domain order (`DomainsMatch` checks the two agree). -/
def Export.Plan.domainAt (P : Plan) (d : Nat) : Option Domain := P.domains[d]?

/-- **The prime-subfield nodes of the plan's domain** of each program domain: the field's own node
when the field has degree `1` (a prime field is its own prime subfield), and its declared subfields
of degree `1` (none when the plan has no domain at that position). -/
def primeNodesOf (P : Plan) (_ : RealizedProgram) (d : Nat) : List String :=
  ((P.domainAt d).map fun pd =>
    (if pd.field.degree = 1 then [pd.field.name] else []) ++
      (pd.subfields.filter (·.degree = 1)).map (·.name)).getD []

/-- **The packing-tree nodes of the plan's domain** of each program domain (none when the plan has
no domain at that position). -/
def treeNodesOf (P : Plan) (_ : RealizedProgram) (d : Nat) : List String :=
  ((P.domainAt d).map Domain.treeNodes).getD []

end GordieHowe.RealizedProgram
