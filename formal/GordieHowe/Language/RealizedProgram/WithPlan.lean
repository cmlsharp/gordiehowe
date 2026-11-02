-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Check
public import GordieHowe.Language.RealizedProgram.CheckValues
public import GordieHowe.Language.Export.Valid
public import GordieHowe.Language.RealizedProgram.MemberValues

@[expose] public section

/-!
# GordieHowe: the plan's program with the plan

The conditions that tie a program (`GordieHowe.RealizedProgram`) to its plan (`GordieHowe.RealizedProgram.Export.Plan`):

* `Interp.Registered`: the interpretation of the program's fields follows the field registry
  (`GordieHowe.RealizedProgram.Export.fieldRegistry`);
* `Export.Plan.domainAt`: the plan's domain of each program domain, by position (the compiler emits
  both lists in its domain order);
* `primeNodesOf`: the prime-subfield nodes of each domain, the plan's field and subfields of degree `1`
  (`Interp.Lawful` ties them to the interpretation);
* `DomainsMatch`: the program's domains are the plan's, position by position, with the same fields
  (decided by `domainsAlignedB`, the twin `domainsAlignedE`);
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

/-- **The plan's domain of program domain `d`**, by position: the compiler lists the plan's domains
and the program's in the compiled system's domain order (`DomainsMatch` checks the two agree). -/
def Export.Plan.domainAt (P : Plan) (d : ℕ) : Option Domain := P.domains[d]?

/-- **The plan's domain `pd` is the program's domain `x`**: the same name, and a field of the
program's field's name and characteristic. -/
def DomainAgrees (ir : RealizedProgram) (pd : Domain) (x : DomainDecl) : Prop :=
  pd.name = x.name ∧ pd.field.name = (ir.field x.field).name ∧
    pd.field.characteristic = (ir.field x.field).characteristic

instance (ir : RealizedProgram) (pd : Domain) (x : DomainDecl) :
    Decidable (ir.DomainAgrees pd x) := by
  unfold DomainAgrees; infer_instance

/-- **The program's domains are the plan's**, position by position: as many, and the plan's domain
at each position (`Export.Plan.domainAt`) agrees with the program's there (`DomainAgrees`). -/
def DomainsMatch (P : Plan) (ir : RealizedProgram) : Prop :=
  P.domains.length = ir.domains.length ∧
    ∀ d < ir.domains.length, ∃ pd, P.domainAt d = some pd ∧ ir.DomainAgrees pd (ir.domain d)

/-- **The domains' alignment check**: as many domains (`domainCount`, naming both counts), and at
each position the plan's domain agrees with the program's (`domainMismatch`, naming the
position). -/
def domainsAlignedE (P : Plan) (ir : RealizedProgram) : Except StructFailure Unit :=
  Twin.seqE
    (Twin.guardE (P.domains.length == ir.domains.length)
      ⟨P.domains.length, ir.domains.length, .domainCount⟩)
    (Twin.allE (fun d x =>
      match P.domainAt d with
      | some pd => Twin.guardE (decide (ir.DomainAgrees pd x)) ⟨d, 0, .domainMismatch⟩
      | none => .error ⟨d, 0, .domainCount⟩) 0 ir.domains)

/-- **`domainsAlignedE` as a `Bool`.** -/
def domainsAlignedB (P : Plan) (ir : RealizedProgram) : Bool := Twin.okB (domainsAlignedE P ir)

theorem domainsAlignedB_iff (P : Plan) (ir : RealizedProgram) :
    domainsAlignedB P ir = true ↔ DomainsMatch P ir := by
  unfold domainsAlignedB domainsAlignedE DomainsMatch
  rw [Twin.okB_seqE, Twin.okB_guardE, Bool.and_eq_true, beq_iff_eq]
  refine and_congr_right fun _ => ?_
  rw [Twin.okB_allE_iff]
  refine forall_congr' fun d => ?_
  constructor
  · intro h hd
    have hx : ir.domains[d] = ir.domain d := by
      rw [domain, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hd, Option.getD_some]
    have h := h hd
    rw [Nat.zero_add, hx] at h
    split at h
    · rename_i pd hpd
      exact ⟨pd, hpd, of_decide_eq_true (by simpa [Twin.okB_guardE] using h)⟩
    · cases h
  · intro h hd
    obtain ⟨pd, hpd, hag⟩ := h hd
    have hx : ir.domains[d] = ir.domain d := by
      rw [domain, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hd, Option.getD_some]
    rw [Nat.zero_add, hx, hpd, Twin.okB_guardE]
    exact decide_eq_true hag

instance (P : Plan) (ir : RealizedProgram) : Decidable (DomainsMatch P ir) :=
  decidable_of_iff _ (domainsAlignedB_iff P ir)

/-- **The prime-subfield nodes of the plan's domain** of each program domain: the field's own node
when the field has degree `1` (a prime field is its own prime subfield), and its declared subfields
of degree `1` (none when the plan has no domain at that position). -/
def primeNodesOf (P : Plan) (_ : RealizedProgram) (d : ℕ) : List String :=
  ((P.domainAt d).map fun pd =>
    (if pd.field.degree = 1 then [pd.field.name] else []) ++
      (pd.subfields.filter (·.degree = 1)).map (·.name)).getD []

/-- **The packing-tree nodes of the plan's domain** of each program domain (none when the plan has
no domain at that position). -/
def treeNodesOf (P : Plan) (_ : RealizedProgram) (d : ℕ) : List String :=
  ((P.domainAt d).map Domain.treeNodes).getD []

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
