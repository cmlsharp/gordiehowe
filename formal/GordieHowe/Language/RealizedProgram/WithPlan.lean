-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Check
public import GordieHowe.Language.RealizedProgram.CheckValues
public import GordieHowe.Language.Export.Valid

@[expose] public section

/-!
# GordieHowe: the plan's program with the plan

The conditions that tie a program (`GordieHowe.RealizedProgram`) to its plan (`GordieHowe.RealizedProgram.Export.Plan`):

* `Interp.Registered`: the interpretation of the program's fields follows the field registry
  (`GordieHowe.RealizedProgram.Export.fieldRegistry`);
* `primeNodesOf`: the prime-subfield nodes of each domain, the plan's field and subfields of degree `1`
  (`Interp.Lawful` ties them to the interpretation);
* `DomainsMatch`: the program's domains are the plan's, with the same fields;
* `RealizedProgram.Valid P ir`: the plan is valid (`Plan.Valid`), the domains match, and the program is
  valid for the plan's packing trees (`GordieHowe.RealizedProgram.ValidAtNodes` at `treeNodesOf P ir`).

`GordieHowe.RealizedProgram.Valid` is decidable through the checker of `GordieHowe/Language/RealizedProgram/Check.lean`;
the exported plans are checked against their programs in `GordieHowe/Generated/**/Valid.lean`.
-/

namespace GordieHowe.RealizedProgram

open Export

/-- **The interpretation follows the registry**: every field of the program is read as a field
whose specification is a registry entry's (`Export.fieldRegistry`) with the program's name and
characteristic, of characteristic and cardinality that specification's. -/
structure Interp.Registered (I : Interp) (ir : RealizedProgram) : Prop where
  /-- The specification is a registry entry's. -/
  registry : ∀ f < ir.fields.length, ∃ e ∈ fieldRegistry, e.spec = (I f).spec
  /-- The name is the program's. -/
  name : ∀ f < ir.fields.length, (I f).spec.name = (ir.field f).name
  /-- The characteristic is the program's. -/
  characteristic : ∀ f < ir.fields.length, (I f).spec.characteristic = (ir.field f).characteristic
  /-- The Lean field has the specification's characteristic. -/
  ringChar : ∀ f < ir.fields.length, _root_.ringChar (I f).K = (I f).spec.characteristic
  /-- The Lean field has the specification's cardinality. -/
  card : ∀ f < ir.fields.length,
    Fintype.card (I f).K = (I f).spec.characteristic ^ (I f).spec.degree

/-! ## With the plan -/

/-- **The program's domains are the plan's**: every domain of the program is a domain of the plan
of the same name, whose field has the program's field's name and characteristic. -/
def DomainsMatch (P : Plan) (ir : RealizedProgram) : Prop :=
  ∀ d ∈ ir.domains, ∃ pd ∈ P.domains, pd.name = d.name ∧
    pd.field.name = (ir.field d.field).name ∧
    pd.field.characteristic = (ir.field d.field).characteristic

instance (P : Plan) (ir : RealizedProgram) : Decidable (DomainsMatch P ir) := by
  unfold DomainsMatch; infer_instance

/-- **The prime-subfield nodes of the plan's domain** of each program domain: the field's own node
when the field has degree `1` (a prime field is its own prime subfield), and its declared subfields
of degree `1` (none when the plan has no domain of that name). -/
def primeNodesOf (P : Plan) (ir : RealizedProgram) (d : ℕ) : List String :=
  ((P.domain (ir.domain d).name).map fun pd =>
    (if pd.field.degree = 1 then [pd.field.name] else []) ++
      (pd.subfields.filter (·.degree = 1)).map (·.name)).getD []

/-- **The packing-tree nodes of the plan's domain** of each program domain (none when the plan has
no domain of that name). -/
def treeNodesOf (P : Plan) (ir : RealizedProgram) (d : ℕ) : List String :=
  ((P.domain (ir.domain d).name).map Domain.treeNodes).getD []

/-- **A plan with its program is valid**: the plan is valid (`Plan.Valid`), the program's domains
are the plan's, and the program is valid for the plan's packing trees (`RealizedProgram.ValidAtNodes`, with
`RealizedProgram.ChallengeOrder`, `RealizedProgram.PadOrderValid`, `RealizedProgram.TypeSources` and
`RealizedProgram.TargetsAdmit`). -/
structure Valid (P : Plan) (ir : RealizedProgram) : Prop where
  /-- The plan is valid. -/
  plan : P.Valid
  /-- The domains match. -/
  domains : DomainsMatch P ir
  /-- The program is valid. -/
  program : ir.ValidAtNodes (treeNodesOf P ir)

end GordieHowe.RealizedProgram
