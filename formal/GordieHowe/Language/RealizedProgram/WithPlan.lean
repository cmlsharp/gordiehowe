-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Check
public import GordieHowe.Language.RealizedProgram.CheckValues
public import GordieHowe.Language.Export.Valid
public import GordieHowe.Language.RealizedProgram.MemberValues
public import GordieHoweNative.Language.RealizedProgram.WithPlan

@[expose] public section

/-!
# GordieHowe: the plan's program with the plan

The conditions that tie a program (`GordieHowe.RealizedProgram`) to its plan (`GordieHowe.RealizedProgram.Export.Plan`):

* `Interp.Registered`: the interpretation of the program's fields follows the field registry
  (`GordieHowe.RealizedProgram.Export.fieldRegistry`);
* `Export.Plan.domainAt`: the plan's domain of each program domain, by position (the compiler emits
  both lists in its domain order; defined in `GordieHoweNative/Language/RealizedProgram/WithPlan.lean`
  with `primeNodesOf` and `treeNodesOf`);
* `primeNodesOf`: the prime-subfield nodes of each domain, the plan's field and subfields of degree `1`
  (`Interp.Lawful` ties them to the interpretation);
* `DomainsMatch`: the program's domains are the plan's, position by position, with the same fields
  (decided by `domainsAlignedB`, the twin `domainsAlignedE`); no theorem reads it;
* `RealizedProgram.Valid ir`: the program is well formed and has the challenge and pad orders, the
  validity conditions the proof system reads.
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

/-- **The program is valid**: the validity conditions some theorem reads, well-formedness
(`RealizedProgram.WellFormed`), the challenge order (`RealizedProgram.ChallengeOrder`) and the pad
order (`RealizedProgram.PadOrderValid`). The other conditions that `Valid.lean` and
`Export/Valid.lean` define (the messages, reads, degrees, type sources, targets, pad realizations,
the domains' match with the plan and the seven plan conditions of `Plan.Valid`) are read by no
theorem and are no longer certified. -/
structure Valid (ir : RealizedProgram) : Prop where
  /-- Well-formedness. -/
  wellFormed : ir.WellFormed
  /-- The challenge order. -/
  order : ir.ChallengeOrder
  /-- The pad order. -/
  pads : ir.PadOrderValid

end GordieHowe.RealizedProgram
