-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.ProgramData
public import GordieHoweNative.Language.CircuitCheck
public import GordieHowe.Language.RealizedProgram.WithPlan
public import GordieHowe.Language.RealizedProgram.WellFormedReader
public import GordieHowe.Language.RealizedProgram.CellsReader
public import GordieHowe.Language.RealizedProgram.LocalityReader
public import GordieHowe.Language.RealizedProgram.AssignmentReads
public import GordieHowe.Language.RealizedProgram.SourceCheck
public import GordieHowe.Language.Realizations.Derivation
public import GordieHowe.Language.Completeness.Check
public import GordieHowe.Language.FiguresCheck
public import GordieHowe.Language.RealizedProgram.Shapes
public import GordieHowe.Language.RealizedProgram.SourceRoles
public import GordieHowe.ProofSystem.Program.FieldReader
public import GordieHoweNative.Language.TableauCheck

public section

/-!
# GordieHowe: a program's check

`ProgramData.programOkB d`: the conjunction of a program's parts, each a checker at the data's
projections, in a fixed order: validity, realization, program facts, completeness, shapes,
figures, optional source roles, and GKR circuits. Most parts use their kernel form here;
compiled code runs their context-built form in `GordieHoweNative` through a `@[csimp]`
equality. The GKR part directly uses the compiled `circuitCertBC`, whose equality to the
canonical circuit checker is proved in the semantic layer. Its kernel leaf transports the
existing sliced circuit proofs through `gkrPartB_iff`. Thus `gh_native_check` executes every
part in one compiled run, while kernel composition retains the sliced proofs.

`programOkB` holds these parts: well-formedness
(`wellFormedA`, `memberValuesB`), challenge and pad order (`orderB`, `padsB`), the expression annotations (`exprAnnOkB`), the derivations
(`derivsB`), the cells (`placementB`), the source part (`sourceChecksB`), locality
(`chalValuesB`, `localWithB`), every domain's checks at its field's packing descriptor
(`fieldOkBD`), every domain's tableau at its descriptor's numbers (`tableauFitB`), the table
selections (`selectionsB`), the completion certificate
(`completionB`), honest roles (`honestRolesB`), the absence of field-form predicates, the shapes
the frontends read (`shapesB`), figures when present (`figuresPartB`), optional source-role
placement and coverage (`sourceRolesB`), every circuit certificate (`gkrPartB`), and the plan's
opaque-function set and the opaque values' arguments against the field table's interpretation
(`opaqueSetB`). The other conditions of `GordieHowe.ProgramConditions` (the tableaus, the field
table, the packing descriptors and the interpretation's model) are proved per program in a module of
their own. A checker that `programOkB` does not run certifies nothing.

**The kernel composition.** A program's check module proves `programOk : data.programOkB = true`.
In kernel mode the proof is a term over leaf theorems, each stating one part (or a slice of one) at
`data` with the part's own arguments, joined by `and_intro`: the kernel unfolds `programOkB`, its
groups and `data` only, compares each leaf's statement with its part syntactically, and evaluates
no part.
-/

namespace GordieHowe

open RealizedProgram

/-- **Domain `i`'s packing descriptor**: its field's, by the field table. -/
@[expose] def RuntimeInputs.packingDesc (r : RuntimeInputs) (i : ℕ) : PackingDesc :=
  r.fieldTable.packing.getD (r.fieldTable.domainField i) default

namespace ProgramData

variable (d : ProgramData)

/-! ## The parts -/

/-- **Well-formedness**, through the annotations, with the statement's member checks. -/
@[expose] def wellFormedB : Bool :=
  d.program.wellFormedA d.hints.exprAnn && d.program.memberValuesB d.records

/-- **The challenge order.** -/
@[expose] def orderB : Bool := d.program.orderB

/-- **The pad order.** -/
@[expose] def padsB : Bool := d.program.padsB

/-- **The expression annotations** pass their local rules. -/
@[expose] def exprAnnB : Bool := d.program.exprAnnOkB d.hints.exprAnn

/-- **The derivations of the realization** check, at the plan's prime-subfield nodes and the
declared statement bounds. -/
@[expose] def derivsB : Bool :=
  d.program.derivsB (primeNodesOf d.plan d.program) (d.program.declaredRanges ++ []) d.records
    d.hints.derivs

/-- **The cells checks** at the structure records. -/
@[expose] def cellsB : Bool := d.program.placementB d.records

/-- **The source part's checks.** -/
@[expose] def sourceB : Bool := d.program.sourceChecksB

/-- **Locality**: the challenge holders of the structure records, then every domain's reads. -/
@[expose] def localityB : Bool :=
  d.program.chalValuesB d.records &&
    d.program.localWithB d.records.chalOf (treeNodesOf d.plan d.program)

/-- **Every domain's checks** at its field's packing descriptor (`RealizedProgram.fieldOkBD`), one
per domain of the field table. -/
@[expose] def fieldsB : Bool :=
  allIdx (fun i _ => d.program.fieldOkBD i d.plan (d.packingDesc i)) d.fieldTable.domainFields 0

/-- **Every domain's tableau fits** its field's packing descriptor and the plan, at its tableau
descriptor's numbers (`tableauFitB`), one per domain of the field table. -/
@[expose] def tableausB : Bool :=
  allIdx (fun i _ => tableauFitB (d.tableauDesc i).nums (d.packingDesc i).q d.plan i)
    d.fieldTable.domainFields 0

/-- **The table selections** (`RealizedProgram.selectionsB`): every certificate's gadget facts, and a
linked certificate for every selection a product form's kernel reads. -/
@[expose] def selectionsPartB : Bool := d.program.selectionsB d.selections

/-- **No opaque value takes an argument.** -/
@[expose] def opaqueFreeB : Bool :=
  d.program.values.all fun v => !v.kind.takesOpaqueArgsB

/-- **The field table's opaque-function set is the program's**: the plan names it, and it is `none`
exactly when no opaque value takes an argument. `OpaqueKey.none` reads an opaque value as the
constant `0`, so a value with arguments under it would change the program's meaning. -/
@[expose] def opaqueSetB : Bool :=
  d.plan.opaqueSet == d.fieldTable.interp.opaque.name &&
    (d.fieldTable.interp.opaque == .none) == d.opaqueFreeB

/-- **The opaque-function check, as statements.** -/
theorem opaqueSetB_iff : d.opaqueSetB = true ↔
    d.plan.opaqueSet = d.fieldTable.interp.opaque.name ∧
      (d.fieldTable.interp.opaque = .none ↔ d.opaqueFreeB = true) := by
  simp only [opaqueSetB, Bool.and_eq_true, Bool.beq_eq_decide_eq, decide_eq_true_eq]
  cases d.opaqueFreeB <;> simp

/-- **The completion certificate** checks. -/
@[expose] def completionPartB : Bool :=
  d.program.completionB (primeNodesOf d.plan d.program) d.nodes d.records d.gens
    d.cderivs

/-- **The honest roles.** -/
@[expose] def rolesB : Bool := d.program.honestRolesB d.nodes d.records

/-- **No field-form predicate**, when the field table says so. -/
@[expose] def noFieldFormB : Bool :=
  !d.fieldTable.noFieldForm || d.program.predicates.all (fun p => !p.body.isFieldForm)

/-! ## The groups and the check -/

/-- **The validity parts.** -/
@[expose] def validB : Bool := d.wellFormedB && d.orderB && d.padsB

/-- **The realization parts.** -/
@[expose] def realizationB : Bool := d.exprAnnB && d.derivsB

/-- Exact assignment-read rows are required certificate data. An omitted empty
list rejects every program with a nonempty values list. -/
@[expose] def assignmentReadsB : Bool :=
  d.program.assignmentReadsB d.hints.assignmentReads

/-- Kernel field checks consume the supplied rows after the separate row check. -/
@[expose] def fieldsWithAssignmentReadsB : Bool :=
  allIdx (fun i _ => fieldWithAssignmentReadsB d.program d.hints.assignmentReads
    i d.plan (d.packingDesc i)) d.fieldTable.domainFields 0

/-- Kernel locality checks consume the supplied rows after the separate row check. -/
@[expose] def localityWithAssignmentReadsB : Bool :=
  d.program.chalValuesB d.records &&
    localWithAssignmentReadsB d.program d.hints.assignmentReads
      d.records.chalOf (treeNodesOf d.plan d.program)

/-- Checked rows preserve the public field-check endpoint exactly. -/
theorem fieldsWithAssignmentReadsB_eq (h : d.assignmentReadsB = true) :
    d.fieldsWithAssignmentReadsB = d.fieldsB := by
  have hf : (fun i (_ : Nat) => fieldWithAssignmentReadsB d.program d.hints.assignmentReads
      i d.plan (d.packingDesc i)) =
      (fun i (_ : Nat) => d.program.fieldOkBD i d.plan (d.packingDesc i)) := by
    funext i _
    exact fieldWithAssignmentReadsB_eq_canonical _ _ _ _ _ h
  simp only [fieldsWithAssignmentReadsB, fieldsB, hf]

/-- Checked rows preserve the public locality-check endpoint exactly. -/
theorem localityWithAssignmentReadsB_eq (h : d.assignmentReadsB = true) :
    d.localityWithAssignmentReadsB = d.localityB := by
  simp only [localityWithAssignmentReadsB, localityB,
    localWithAssignmentReadsB_eq_canonical _ _ _ _ h]

/-- **The program-fact parts**, guarded by the exact supplied-row check. The
canonical Fields and Locality endpoints keep their existing meanings. -/
@[expose] def factsB : Bool :=
  d.assignmentReadsB &&
    (d.cellsB && d.sourceB && d.localityB && d.fieldsB && d.tableausB && d.selectionsPartB)

/-- Compiled facts validate the assignment rows once and share their context
between all field checks and locality. Runtime constructors do not use it. -/
@[expose] def factsBC : Bool :=
  d.cellsB && d.sourceB &&
    assignmentFactsBC d.program d.plan d.records d.fieldTable.domainFields d.packingDesc
      (treeNodesOf d.plan d.program) d.hints.assignmentReads &&
    d.tableausB && d.selectionsPartB

/-- The compiled shared context is exactly the guarded canonical facts for every
program and supplied row list, including malformed or omitted rows. -/
@[csimp] theorem factsB_csimp : @factsB = @factsBC := by
  funext d
  simp only [factsB, factsBC, assignmentReadsB, localityB, fieldsB,
    assignmentFactsBC_eq, fieldOkBD_csimp, chalValuesB_csimp, localWithB_csimp,
    Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

/-- **The completeness parts.** -/
@[expose] def completeB : Bool := d.completionPartB && d.rolesB && d.noFieldFormB

/-- **The check of the proof system's conditions** (`GordieHowe.CoreConditions`). -/
@[expose] def coreOkB : Bool := d.validB && d.realizationB && d.factsB

/-- **The check of a program** (module docstring). -/
@[expose] def programOkB : Bool :=
  d.coreOkB && d.completeB && d.shapesB && d.figuresPartB && d.sourceRolesB && d.gkrPartB &&
    d.opaqueSetB

end ProgramData

/-! ## The composition's lemmas -/

/-- **A conjunction from its conjuncts**, the step of a check's kernel composition. -/
theorem and_intro {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]; rfl

/-- **The left conjunct.** -/
theorem and_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a <;> simp_all

/-- **The right conjunct.** -/
theorem and_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a <;> cases b <;> simp_all

/-- **The proof system's check from the program's.** -/
theorem ProgramData.coreOkB_of {d : ProgramData} (h : d.programOkB = true) : d.coreOkB = true :=
  and_left (and_left (and_left (and_left (and_left (and_left h)))))

/-- The member-value pointers are checked by the program's well-formedness part. -/
theorem ProgramData.memberValuesB_of_programOk {d : ProgramData} (h : d.programOkB = true) :
    d.program.memberValuesB d.records = true := by
  have hv : d.validB = true := and_left (and_left (coreOkB_of h))
  have hw : d.wellFormedB = true := and_left (and_left hv)
  exact and_right hw

end GordieHowe
