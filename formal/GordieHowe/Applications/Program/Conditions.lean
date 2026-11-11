-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.ProgramCheck
public import GordieHoweNative.Language.CircuitCheck
public import GordieHowe.Applications.FieldInterps.Registry
public import GordieHowe.ProofSystem.Program.FieldTable
public import GordieHowe.ProofSystem.Program.ProgramFigures
public import GordieHowe.Language.RealizedProgram.MemberValues
public import GordieHowe.Foundations.ReedSolomon.JohnsonAgreement

@[expose] public section

/-!
# The conditions of a program

`CoreConditions d`: every fact about a program's data `d` that its proof system needs, one named
predicate per field; `ProgramConditions d` adds the facts of its honest strategy, figures,
frontend shapes, and optional source-role placement and coverage. Hand-written proofs learn about a program only from these conditions
and the small data (`d.fieldTable`, `d.figures`).

Every predicate and accessor that reads only the computational inputs (`RuntimeInputs`: the
program, the plan, the field table, the tableaus and the figures) is defined once, on those inputs;
at a program's data `d` it applies as `d.inputs` (`d.TableausOk` is `d.inputs.TableausOk`). Only
the circuits' condition (`CircuitsOk`) reads a certificate.

`programOk_sound` gives the conditions that `ProgramData.programOkB` checks; the others are
proved per program in a module of their own (`GordieHowe/Language/ProgramCheck.lean`).

**Not certified.** The conditions that no theorem reads are not fields here and no check
certifies them: the messages' order (`MessagesMatch`), the exported reads (`ReadsSound`) and
degrees (`DegreesSound`), the type sources (`TypeSources`), the targets (`TargetsAdmit`), the pad
realizations (`PadRealized`), the domains' match with the plan (`DomainsMatch`), the seven plan
conditions of `Plan.Valid`, the structure records' key order (`Structure.keysOkB`), and the
degree-zero and closure annotations those checks read.

**Facts about earlier conditions.** The domains' checks (`FieldOkAt`) are stated at the tableaus
that `TableausOk` certifies, and the figures (`FiguresOk`) at the ready data the core conditions
give. Each is stated for every proof of the earlier condition: the proofs are proof-irrelevant, so
one proof at the program's conditions gives the statement at any.
-/

namespace GordieHowe

open RealizedProgram ReedSolomon.HiddenDerivative SPBCS SPBCS.Configurations QROM

/-! ## Tableaus -/

/-- **The Ligero numbers of a Johnson tableau.** -/
def JohnsonDesc.shape (j : JohnsonDesc) : Ligero.Relative.Shape where
  rate := j.rate
  nreq := j.nreq
  blockEnc := j.blockEnc
  nrep := j.nrep
  r := j.r

/-- **A Johnson tableau's line certificate holds**: the weighted Johnson certificate at degree
`D = block − 1` on `N` points (`IsJohnsonWeightedCertificate`), `2 ≤ block ≤ agree ≤ N`,
`B ≤ 2 D + 1`, and the refined exceptional count within `exceptions`
(`RSCode.lineCertificate_of_weightedJohnson`). -/
structure JohnsonDesc.Ok (j : JohnsonDesc) : Prop where
  cert : IsJohnsonWeightedCertificate j.shape.N (j.shape.block - 1) j.agree j.m j.B j.H
  block_ge : 2 ≤ j.shape.block
  block_le : j.shape.block ≤ j.agree
  agree_le : j.agree ≤ j.shape.N
  B_le : j.B ≤ 2 * (j.shape.block - 1) + 1
  count_le : johnsonWeightedRefinedExceptionCount j.shape.N (j.shape.block - 1) j.agree j.B j.H ≤
    (j.exceptions : ℚ)

instance (n D A m B H : ℕ) : Decidable (IsJohnsonWeightedCertificate n D A m B H) := by
  unfold IsJohnsonWeightedCertificate; infer_instance

theorem JohnsonDesc.ok_iff (j : JohnsonDesc) : j.Ok ↔
    IsJohnsonWeightedCertificate j.shape.N (j.shape.block - 1) j.agree j.m j.B j.H ∧
      2 ≤ j.shape.block ∧ j.shape.block ≤ j.agree ∧ j.agree ≤ j.shape.N ∧
      j.B ≤ 2 * (j.shape.block - 1) + 1 ∧
      johnsonWeightedRefinedExceptionCount j.shape.N (j.shape.block - 1) j.agree j.B j.H ≤
        (j.exceptions : ℚ) :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    h.2.2.2.2.1, h.2.2.2.2.2⟩⟩

instance (j : JohnsonDesc) : Decidable j.Ok := decidable_of_iff _ j.ok_iff.symm

/-- **The tableau of a Johnson descriptor**: its numbers, the mask test, and the line certificate
of the weighted Johnson certificate. -/
def JohnsonDesc.cert (j : JohnsonDesc) (h : j.Ok) : LigeroCert where
  Sh := j.shape
  agree := j.agree
  exceptions := j.exceptions
  line C hk := ⟨by rw [hk]; exact h.block_le,
    RSCode.lineCertificate_of_weightedJohnson C h.cert (by rw [hk]; have := h.block_ge; omega)
      (by have := h.block_ge; omega) (by have := h.block_ge; have := h.block_le; omega) h.agree_le
      h.B_le h.count_le⟩
  masking := .split

/-- **A tableau descriptor checks**: a library tableau always, a Johnson tableau by its line
certificate. -/
def TableauDesc.Ok : TableauDesc → Prop
  | .library _ => True
  | .johnson j => j.Ok

instance (t : TableauDesc) : Decidable t.Ok := by cases t <;> unfold TableauDesc.Ok <;> infer_instance

/-- **The tableau of a checked descriptor.** -/
def TableauDesc.cert : (t : TableauDesc) → t.Ok → LigeroCert
  | .library k, _ => k.cert
  | .johnson j, h => j.cert h

/-- **A Johnson tableau has its descriptor's numbers.** -/
theorem JohnsonDesc.cert_nums (j : JohnsonDesc) (h : j.Ok) : (j.cert h).nums = j.nums := rfl

/-- **The tableau of a checked descriptor has the descriptor's numbers.** -/
theorem TableauDesc.cert_nums : ∀ (t : TableauDesc) (h : t.Ok), (t.cert h).nums = t.nums
  | .library k, _ => k.cert_nums
  | .johnson j, h => j.cert_nums h

namespace RuntimeInputs

variable (r : RuntimeInputs)

/-! ## The named conditions on the computational inputs -/

/-- **The tableaus check** (each tableau descriptor). -/
def TableausOk : Prop := ∀ t ∈ r.tableaus, t.Ok

instance : Decidable r.TableausOk := by unfold TableausOk; infer_instance

/-- Domain `i`'s descriptor checks, including the default past the list. -/
theorem TableausOk.at {r : RuntimeInputs} (h : r.TableausOk) (i : ℕ) : (r.tableauDesc i).Ok := by
  unfold tableauDesc
  by_cases hi : i < r.tableaus.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
    trivial

/-- **Domain `i`'s tableau.** -/
def tableau (h : r.TableausOk) (i : ℕ) : LigeroCert := (r.tableauDesc i).cert (h.at i)

/-- **The program's interpretation**: the registry's, at its field table. -/
@[reducible] def interp : Interp := r.fieldTable.interp.interp

/-- **Domain `i`'s checks** (`RealizedProgram.fieldOkB`): its packing facts, the registry's, and
its tableau, at every proof that the tableaus check. -/
def FieldOkAt (i : ℕ) : Prop :=
  ∀ h : r.TableausOk, r.program.fieldOkB (I := r.interp) i r.plan
    (r.fieldTable.interp.packing (r.program.domainField i)) (r.tableau h i) = true

/-- **Every domain's checks.** -/
def FieldsOk : Prop := ∀ i : Fin r.program.domains.length, r.FieldOkAt i

/-- **The field table is the program's** (`RealizedProgram.FieldTable`): its domain fields and
circuit domains. -/
def FieldTableOk : Prop :=
  r.program.FieldTable r.fieldTable.domainFields.length r.fieldTable.domainField
    r.fieldTable.circuitDomains.length r.fieldTable.circuitDomain

/-- **No field-form `mod_q`**, when the field table says so. -/
def NoFieldForm : Prop :=
  r.fieldTable.noFieldForm = true →
    ∀ p < r.program.predicates.length, r.program.isFieldForm p = false

/-- **Every domain's checks at its field's packing descriptor** (`RealizedProgram.fieldOkBD`), the
part `ProgramData.fieldsB`. -/
def FieldDescsOk : Prop :=
  ∀ i < r.fieldTable.domainFields.length, r.program.fieldOkBD i r.plan (r.packingDesc i) = true

/-- **The packing descriptors are the registry's packing facts** at their queries
(`FieldInterp.Packing.desc`), at every domain of the field table. -/
def PackingsOk : Prop :=
  ∀ i < r.fieldTable.domainFields.length,
    (r.fieldTable.interp.packing (r.fieldTable.domainField i)).desc (r.packingDesc i) =
      r.packingDesc i

instance : Decidable r.PackingsOk := by unfold PackingsOk; infer_instance

/-- **Every domain's tableau fits its field and the plan** (`LigeroCert.validB`,
`RealizedProgram.planLigeroB`), at every proof that the tableaus check. Like `FieldOkAt`, it is
stated for every proof of `TableausOk` (module docstring), so any one proof, such as the
conditions' own `tableaus`, gives it. -/
def TableausFit : Prop :=
  ∀ h : r.TableausOk, ∀ i < r.fieldTable.domainFields.length,
    (r.tableau h i).validB (r.fieldTable.interp.packing (r.fieldTable.domainField i)).q = true ∧
      r.program.planLigeroB r.plan i (r.tableau h i) = true

/-- **Every domain's tableau fits its field's packing descriptor and the plan**, at its tableau
descriptor's numbers (`tableauFitB`), the part `ProgramData.tableausB`. -/
def TableauDescsFit : Prop :=
  ∀ i < r.fieldTable.domainFields.length,
    tableauFitB (r.tableauDesc i).nums (r.packingDesc i).q r.plan i = true

/-- **Every domain's tableau fits its field and the plan**, from the fit at the packing descriptors
(`TableauDescsFit`) and the descriptors' match with the registry's packing facts (`PackingsOk`):
the tableau's tests read only its numbers (`LigeroCert.validB_eq_nums`,
`LigeroCert.matchesB_eq_nums`), the descriptor's (`TableauDesc.cert_nums`), and the descriptor's
domain size is the field's. -/
theorem TableausFit.of_descs {r : RuntimeInputs} (hp : r.PackingsOk) (ht : r.TableauDescsFit) :
    r.TableausFit := by
  intro h i hi
  have hq : (r.fieldTable.interp.packing (r.fieldTable.domainField i)).q = (r.packingDesc i).q :=
    congrArg PackingDesc.q (hp i hi)
  have hn : (r.tableau h i).nums = (r.tableauDesc i).nums := TableauDesc.cert_nums _ _
  have hfit := ht i hi
  simp only [tableauFitB, Bool.and_eq_true] at hfit
  refine ⟨?_, ?_⟩
  · rw [LigeroCert.validB_eq_nums, hn, hq]
    exact hfit.1
  · simp only [planLigeroB, LigeroCert.matchesB_eq_nums, hn]
    exact hfit.2

/-- **Every domain's checks**, from the part at the packing descriptors (`FieldDescsOk`), the
descriptors' match with the registry's packing facts (`PackingsOk`) and the tableaus' fit
(`TableausFit`), at the field table (`RealizedProgram.fieldOkB_of_desc`). -/
theorem FieldsOk.of_descs {r : RuntimeInputs} (hft : r.FieldTableOk) (hd : r.FieldDescsOk)
    (hp : r.PackingsOk) (hf : r.TableausFit) : r.FieldsOk := by
  intro i h
  have hi : (i : ℕ) < r.fieldTable.domainFields.length := hft.domains_length ▸ i.2
  have heq : r.program.domainField i = r.fieldTable.domainField i := hft.domainField_eq i hi
  apply fieldOkB_of_desc (D := r.packingDesc i)
  · rw [heq]
    exact hp i hi
  · exact hd i hi
  · rw [heq]
    exact (hf h i hi).1
  · exact (hf h i hi).2

/-- **The completion certificate checks** (`RealizedProgram.completionB`) at the completion
inputs `c`. -/
def CompletionOk (c : CompletionInputs) : Prop :=
  r.program.completionB (primeNodesOf r.plan r.program) c.nodes c.records c.gens c.cderivs = true

/-- **The honest roles check** (`RealizedProgram.honestRolesB`) at the completion inputs `c`. -/
def RolesOk (c : CompletionInputs) : Prop := r.program.honestRolesB c.nodes c.records = true

instance (c : CompletionInputs) : Decidable (r.RolesOk c) := by unfold RolesOk; infer_instance

instance (c : CompletionInputs) : Decidable (r.CompletionOk c) := by
  unfold CompletionOk; infer_instance

/-! ## The ready data and the figures -/

/-- **The facts the ready data reads**: well-formedness, the tableaus and every domain's checks. -/
structure ReadyFacts : Prop where
  /-- Well-formedness. -/
  wellFormed : r.program.WellFormed
  /-- The tableaus. -/
  tableaus : r.TableausOk
  /-- Every domain's checks. -/
  fields : r.FieldsOk

/-- **The ready data of every domain**: the registry's packing facts, the tableau, the domain's
checks and well-formedness. -/
def ready (h : r.ReadyFacts) (i : Fin r.program.domains.length) :
    r.program.FieldReady r.interp i r.plan :=
  ⟨r.fieldTable.interp.packing (r.program.domainField i), r.tableau h.tableaus i,
    h.fields i h.tableaus, h.wellFormed⟩

/-- **The codec of domain `i`'s field.** -/
def cod (i : Fin r.program.domains.length) :
    FieldCodec (r.interp (r.program.domainField i)) :=
  r.fieldTable.interp.codec _

/-- **The bytes of the fields' elements.** -/
def fieldBytes : FieldBytesOf r.interp := r.fieldTable.interp.bytes

/-- **The readers of the fields' elements.** -/
def fieldReader (f : ℕ) : SPBCS.CReader (r.interp f).K :=
  r.fieldTable.interp.reader f

/-- **The largest load of a challenge** (`RealizedProgram.stdChalLoad`). -/
def chalLoadMax : Load :=
  r.program.stdChalLoad fun f => (r.fieldReader f).load

/-- **The readers' check** (`RealizedProgram.ReadersOk` at the fields' sizes). -/
def ReadersOk : Prop :=
  r.program.ReadersOk (fun f => (r.fieldReader f).load) r.interp.specCard

instance : Decidable r.ReadersOk := by unfold ReadersOk; infer_instance

/-- **The readers of the challenges' values** (`RealizedProgram.stdReaders`). -/
def samplerReaders (hr : r.ReadersOk) : SamplerReaders r.interp r.program :=
  stdReaders r.fieldReader r.fieldTable.interp.card hr

/-- Domain `i`'s largest array. -/
def maxArray (i : Fin r.program.domains.length) : ℕ := nthOr r.figures.maxArray i

/-- Domain `i`'s largest challenge read. -/
def maxRead (i : Fin r.program.domains.length) : ℕ := nthOr r.figures.maxRead i

/-- Domain `i`'s reads besides its first combination. -/
def restRead (i : Fin r.program.domains.length) : ℕ := nthOr r.figures.restRead i

/-- **The branch names**: each domain's field name, by the field table. -/
def branchName (i : Fin r.program.domains.length) : List Byte :=
  SPBCS.Configurations.asciiBytes (r.fieldTable.interp.key (r.fieldTable.domainField i)).name

/-- **The domains' size bounds** (`RealizedProgram.FitsOk`). -/
def FitsOk (h : r.ReadyFacts) : Prop :=
  ∀ i, RealizedProgram.FitsOk (r.ready h i) (r.cod i).fb (r.maxArray i) (r.maxRead i)

instance (h : r.ReadyFacts) : Decidable (r.FitsOk h) := by
  unfold FitsOk; infer_instance

/-- **The numbers of the domains** (`RealizedProgram.ForkNumbers`). -/
def numbers (h : r.ReadyFacts) (hf : r.FitsOk h) :
    ForkNumbers (r.ready h) where
  cod := r.cod
  Mx := r.maxArray
  Lmax := r.maxRead
  ok := hf
  grants i := r.figures.grants.getD i {}

/-- **The figures' facts at the ready data**: the readers, the size bounds, the messages' bound,
the figures' check (`ProgramFigures.Check`) and the loads on the default stream. -/
structure FiguresFacts (h : r.ReadyFacts) : Prop where
  /-- The readers' check. -/
  readers : r.ReadersOk
  /-- The size bounds. -/
  fits : r.FitsOk h
  /-- The messages' bound. -/
  msg : ∀ k, r.program.msgB r.fieldBytes k ≤ 2 ^ 20
  /-- The figures' check. -/
  check : r.figures.figures.Check (r.numbers h fits) r.figures.sourceErrors
    (r.samplerReaders readers) r.chalLoadMax
    (chalLoad_stdReaders_le_std r.fieldReader r.fieldTable.interp.card readers)
    r.restRead r.figures.grantMax
  /-- The loads on the default stream. -/
  loads : r.figures.defaultLoads = true → r.figures.figures.DefaultLoadsOk (r.numbers h fits)

end RuntimeInputs

namespace ProgramData

variable (d : ProgramData)

/-- **Every circuit's certificate checks** (`RealizedProgram.circuitCertB`), at its field's code
arithmetic, and its data's characteristic is its field's. -/
def CircuitsOk : Prop :=
  ∀ c < d.program.circuits.length,
    d.program.circuitCertB c (d.circuitCode c) (d.circuitData c) = true ∧
      (d.circuitData c).chr = (d.interp (d.fieldTable.circuitField c)).spec.characteristic

/-- The GKR part is exactly the existing circuit condition, at the selected field interpretation. -/
theorem gkrPartB_iff : d.gkrPartB = true ↔ d.CircuitsOk := by
  simp only [gkrPartB_eq, CircuitsOk, List.all_eq_true, List.mem_range,
    Bool.and_eq_true, beq_iff_eq, RuntimeInputs.interp, InterpDesc.spec_eq,
    ← circuitCertB_eq_compiled]

end ProgramData

/-! ## The conditions -/

/-- **Everything the proof system needs about a program** (module docstring). The checks the
module docstring lists as not certified are not here. -/
structure CoreConditions (d : ProgramData) : Prop where
  /-- Well-formedness. -/
  wellFormed : d.program.WellFormed
  /-- The challenge order. -/
  order : d.program.ChallengeOrder
  /-- The pad order. -/
  pads : d.program.PadOrderValid
  /-- The realization's derivations. -/
  derivable : d.program.Derivable (primeNodesOf d.plan d.program) (d.program.declaredRanges ++ [])
  /-- The cells checks. -/
  cells : d.program.CellsValid
  /-- The source part. -/
  source : d.program.SourceValid
  /-- Every domain's constraints read only its domain. -/
  locality : d.program.Local (treeNodesOf d.plan d.program)
  /-- The interpretation's model. -/
  model : d.interp.Model d.plan d.program []
  /-- The tableaus. -/
  tableaus : d.TableausOk
  /-- Every domain's checks. -/
  fields : d.FieldsOk
  /-- The table selections (`RealizedProgram.selectionsB`): every certificate's gadget facts, which
  the frontends' table selections read (`RealizedProgram.TableSelect.ofSelections`). -/
  selections : d.program.selectionsB d.selections = true
  /-- Every circuit's certificate. -/
  circuits : d.CircuitsOk
  /-- The field table. -/
  fieldTable : d.FieldTableOk

/-- **The facts the ready data reads**, from the core conditions. -/
theorem CoreConditions.readyFacts {d : ProgramData} (h : CoreConditions d) : d.ReadyFacts :=
  ⟨h.wellFormed, h.tableaus, h.fields⟩

/-- **The figures' facts** (`RuntimeInputs.FiguresFacts`), at every proof of the core
conditions. -/
def ProgramData.FiguresOk (d : ProgramData) : Prop :=
  ∀ h : CoreConditions d, d.FiguresFacts h.readyFacts

/-- **Everything a configuration needs about a program** (module docstring). -/
structure ProgramConditions (d : ProgramData) : Prop extends CoreConditions d where
  /-- The completion certificate. -/
  completion : d.CompletionOk d.completion
  /-- The honest roles. -/
  roles : d.RolesOk d.completion
  /-- No field-form `mod_q`, when the field table says so. -/
  noFieldForm : d.NoFieldForm
  /-- The figures. -/
  figures : d.FiguresOk
  /-- The shapes the frontends read. -/
  shapes : ShapesHold d.program d.shapes
  /-- Checked placement and coverage of the optional source-role table. -/
  sourceRoles : SourceRolesPartOk d.program d.sourceRoles

/-! ## Soundness of the check -/

/-- **The conditions `programOkB` checks**: well-formedness, the challenge and pad orders, the
derivations, the cells, the source part, locality, every domain's checks at its packing descriptor,
every domain's tableau at its descriptor's numbers, the table selections, the absence of
field-form `mod_q` where the field table states it, the completion certificate, the honest roles, the shapes,
the figures (present and checked at `withFigures`, absent otherwise), the optional source roles,
the GKR part and the opaque-function set. Applications transport the checked figures to
`FiguresOk` with the packing descriptors. -/
structure CheckedConditions (d : ProgramData) (withFigures : Bool) : Prop where
  wellFormed : d.program.WellFormed
  order : d.program.ChallengeOrder
  pads : d.program.PadOrderValid
  derivable : d.program.Derivable (primeNodesOf d.plan d.program) (d.program.declaredRanges ++ [])
  cells : d.program.CellsValid
  source : d.program.SourceValid
  locality : d.program.Local (treeNodesOf d.plan d.program)
  fieldDescs : d.FieldDescsOk
  tableaus : d.TableauDescsFit
  selections : d.program.selectionsB d.selections = true
  completion : d.CompletionOk d.completion
  roles : d.RolesOk d.completion
  noFieldForm : d.NoFieldForm
  shapes : ShapesHold d.program d.shapes
  figures : d.figuresPartB withFigures = true
  /-- Checked placement and coverage of the optional source-role table. -/
  sourceRoles : SourceRolesPartOk d.program d.sourceRoles
  circuits : d.CircuitsOk
  /-- The plan names the field table's opaque-function set. -/
  opaqueSet : d.plan.opaqueSet = d.fieldTable.interp.opaque.name
  /-- The field table's opaque-function set is `none` exactly when no opaque value takes an
  argument: `none` reads such a value as the constant `0`. -/
  opaqueFree : d.fieldTable.interp.opaque = .none ↔ d.opaqueFreeB = true

/-- **The check of a program is sound** (`ProgramData.programOkB`), each part by its checker's
soundness lemma. -/
theorem programOk_sound (d : ProgramData) {withFigures : Bool}
    (hall : d.programOkB withFigures = true) : CheckedConditions d withFigures :=
  have h : (d.coreOkB && d.completeB && d.shapesB && d.figuresPartB withFigures &&
      d.sourceRolesB && d.gkrPartB) = true := and_left hall
  have hparts : (d.coreOkB && d.completeB && d.shapesB && d.figuresPartB withFigures) = true :=
    and_left (and_left h)
  have hcc : (d.coreOkB && d.completeB) = true := and_left (and_left hparts)
  have hcore : d.coreOkB = true := and_left hcc
  have hv : d.validB = true := and_left (and_left hcore)
  have hr : d.realizationB = true := and_right (and_left hcore)
  have hf : (d.cellsB && d.sourceB && d.localityB && d.fieldsB && d.tableausB &&
      d.selectionsPartB) = true := and_right (and_right hcore)
  have hann : d.exprAnnB = true := and_left hr
  have hder : d.derivsB = true := and_right hr
  have hw : d.wellFormedB = true := and_left (and_left hv)
  have hcomp : d.completeB = true := and_right hcc
  have hwf : d.program.WellFormed :=
    wellFormed_of_ann_members hann d.records (and_left hw) (and_right hw)
  have hcslft : (d.cellsB && d.sourceB && d.localityB && d.fieldsB && d.tableausB) = true :=
    and_left hf
  have hcslf : (d.cellsB && d.sourceB && d.localityB && d.fieldsB) = true := and_left hcslft
  have hcsl : (d.cellsB && d.sourceB && d.localityB) = true := and_left hcslf
  have hcs : d.cellsB = true := and_left (and_left hcsl)
  have hsrc : d.sourceB = true := and_right (and_left hcsl)
  have hloc : d.localityB = true := and_right hcsl
  { wellFormed := hwf
    order := (orderB_iff _).1 (and_right (and_left hv))
    pads := (padsB_iff _).1 (and_right hv)
    derivable := ⟨d.hints.derivs, derivationsValid_of_derivsB hwf hder⟩
    cells := cellsValid_of_placementB hcs
    source := .of_sourceChecksB hwf hsrc
    locality := Local.of_localWithB hwf (chalNode_eq_chalOf (and_left hloc)) (and_right hloc)
    fieldDescs := fun i hi => by
      have h := (allIdx_iff _ _ 0).1 (and_right hcslf) i hi
      rwa [Nat.zero_add] at h
    tableaus := fun i hi => by
      have h := (allIdx_iff _ _ 0).1 (and_right hcslft) i hi
      rwa [Nat.zero_add] at h
    selections := and_right hf
    completion := and_left (and_left hcomp)
    roles := and_right (and_left hcomp)
    noFieldForm := fun hnf => by
      have h := and_right hcomp
      rw [ProgramData.noFieldFormB, hnf] at h
      exact isFieldForm_eq_false_of_all h
    shapes := shapes_sound (and_right (and_left hparts))
    figures := and_right hparts
    sourceRoles := sourceRolesPart_sound (and_right (and_left h))
    circuits := (d.gkrPartB_iff).1 (and_right h)
    opaqueSet := (d.opaqueSetB_iff.1 (and_right hall)).1
    opaqueFree := (d.opaqueSetB_iff.1 (and_right hall)).2 }

end GordieHowe
