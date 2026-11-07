-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Program.Conditions
public import GordieHowe.Language.Realizations.SelectionCheck
public import GordieHowe.ProofSystem.Program.Certified
public import GordieHowe.ProofSystem.Program.CertifiedProgram

public section

/-!
# The proof system and certified data of a program

`RuntimeInputs.proofSystemOf` and `RuntimeInputs.certified` build a program's proof system and
its certified data (`RealizedProgram.CertifiedProgram`, `Configuration.ofCertified`) from its
computational inputs (`RuntimeInputs`, `CompletionInputs`) and erased facts about them. Both are
generic: the field interpretation, the packing facts, the codecs, the readers and the figures are
library functions of the inputs and the field registry. No construction cases on a domain or a
circuit.

The GKR certificates are not arguments: the executable source parts (`SourceParts.ofTriples`) are,
with the certificates confined to an erased `Nonempty` witness (`CoreConditions.certs`). The facts
come from a program's checked conditions (`CoreConditions.coreFacts`,
`ProgramConditions.fullFacts`).
-/

namespace GordieHowe

open RealizedProgram SPBCS QROM

/-- Executable source parts from the compiled sections of the circuit certificates. -/
@[expose] def RealizedProgram.SourceParts.ofTriples
    (xs : List (GKR.Certificate.Layered × Nat × GKR.Fold.Consts)) : SourceParts where
  layered i := (xs.getD i (default : CircuitData).sourceParts).1
  width i := (xs.getD i (default : CircuitData).sourceParts).2.1
  consts i := (xs.getD i (default : CircuitData).sourceParts).2.2

namespace RuntimeInputs

variable (r : RuntimeInputs)

/-- The facts used by the proof system. GKR certificates remain a separate witness. -/
structure CoreFacts : Prop where
  ready : r.ReadyFacts
  checks : r.program.Checks r.plan []
  model : r.interp.Model r.plan r.program []
  hdom : ∀ c < r.program.circuits.length,
    (r.program.circuit c).domain < r.program.domains.length
  /-- The selections' soundness (`RealizedProgram.SelSound`). -/
  selSound : r.program.SelSound r.interp

/-- Additional facts used by the certified program and its honest strategy. -/
structure FullFacts (c : CompletionInputs) : Prop extends r.CoreFacts where
  figures : r.FiguresFacts ready
  completion : r.CompletionOk c
  roles : r.RolesOk c

/-- **The proof system** (`ProgramCerts.proofSystem`), from the executable source parts and the
ready data. -/
@[expose] def proofSystemOf (parts : SourceParts)
    (hc : Nonempty (r.program.ProgramCerts r.interp parts)) (h : r.CoreFacts) :
    r.program.ProofSystem r.plan r.interp :=
  ProgramCerts.proofSystem parts hc h.checks h.model (r.ready h.ready) h.hdom
    (fun _ => r.fieldTable.interp.packing_nodes _) h.selSound

/-- **The certified data of a program** (`RealizedProgram.CertifiedProgram`). -/
@[expose] def certified (c : CompletionInputs) (h : r.FullFacts c) :
    CertifiedProgram r.plan r.program r.interp where
  ready := r.ready h.ready
  figures := r.figures.figures
  numbers := r.numbers h.ready h.figures.fits
  sourceErrors := r.figures.sourceErrors
  samplerReaders := r.samplerReaders h.figures.readers
  chalLoadMax := r.chalLoadMax
  chalLoad_le := chalLoad_stdReaders_le_std r.fieldReader r.fieldTable.interp.card
    h.figures.readers
  restRead := r.restRead
  grantMax := r.figures.grantMax
  figuresOk := h.figures.check
  fieldCard := r.fieldTable.interp.card
  fieldBytes := r.fieldBytes
  msgB_le := h.figures.msg
  branchName := r.branchName
  branchName_le _ := FieldKey.name_le _
  opaqueRanges := []
  model := h.model
  wellFormed := h.ready.wellFormed
  ranges := r.program.declaredRanges ++ []
  derivable := h.checks.realization
  sourceValid := h.checks.source
  records := c.records
  gens := c.gens
  cderivs := c.cderivs
  nodes := c.nodes
  completionOk := h.completion
  rolesOk := h.roles

end RuntimeInputs

namespace ProgramData

variable (d : ProgramData)

/-- **The source parts of the certificates**: each circuit's layered circuit, term width and
constants. -/
@[expose] def parts : SourceParts where
  layered c := (d.circuitData c).layered
  width c := (d.circuitData c).w
  consts c := (d.circuitData c).consts

/-- The source parts are the named fields of each circuit, including the default past the list. -/
theorem parts_eq : d.parts =
    { layered := fun c => (d.circuits.getD c default).layered
      width := fun c => (d.circuits.getD c default).w
      consts := fun c => (d.circuits.getD c default).consts } := rfl

/-- The emitted source triples are exactly the checked certificates' executable parts. -/
theorem sourceParts_eq :
    SourceParts.ofTriples (d.circuits.map CircuitData.sourceParts) = d.parts := by
  have hget (i : Nat) :
      (d.circuits.map CircuitData.sourceParts).getD i (default : CircuitData).sourceParts =
        (d.circuits.getD i default).sourceParts := by
    generalize d.circuits = xs
    induction xs generalizing i with
    | nil => rfl
    | cons x xs ih => cases i with
      | zero => rfl
      | succ i => exact ih i
  rw [d.parts_eq]
  unfold SourceParts.ofTriples
  congr 1
  all_goals funext i; rw [hget]; rfl

end ProgramData

namespace CoreConditions

variable {d : ProgramData}

/-- **Every circuit's domain is a domain of the program**, from the field table. -/
theorem hdom (h : CoreConditions d) :
    ∀ c < d.program.circuits.length, (d.program.circuit c).domain < d.program.domains.length := by
  intro c hc
  have T := h.fieldTable
  rw [T.circuits_length] at hc
  rw [T.circuitDomain_eq c hc, T.domains_length]
  exact T.circuitDomain_lt c hc

/-- **The checks of the proof system** (`RealizedProgram.Checks`). -/
theorem checks (h : CoreConditions d) : d.program.Checks d.plan [] :=
  ⟨⟨h.wellFormed, h.order, h.pads⟩, h.derivable, h.source, h.cells, h.locality⟩

/-- **The facts the proof system reads**, from the core conditions. -/
theorem coreFacts (h : CoreConditions d) : d.CoreFacts :=
  ⟨h.readyFacts, h.checks, h.model, h.hdom,
    selSound_of_selectionsB h.wellFormed h.model.registered h.model.lawful h.selections⟩

/-- **The certificates of the program exist** at the executable source parts
(`ProgramCerts.ofParts`): every circuit's at its field's code arithmetic, its field's model and
code homomorphism from the registry. The certificates appear only inside `Nonempty`. -/
theorem certs (h : CoreConditions d) {parts : SourceParts} (hp : parts = d.parts) :
    Nonempty (d.program.ProgramCerts d.interp parts) := by
  subst hp
  exact ⟨ProgramCerts.ofParts d.circuitData d.circuitCode (fun c hc => (h.circuits c hc).1)
    (fun c hc => by
      have T := h.fieldTable
      have hc' : c < d.fieldTable.circuitDomains.length := T.circuits_length ▸ hc
      exact CircuitFieldOk.of_model_at (T.circField_eq hc') (d.fieldTable.interp.models _)
        (d.fieldTable.interp.codeHom _) (h.circuits c hc).2)
    (fun _ _ => rfl)⟩

end CoreConditions

/-- **The facts the certified data reads**, from the application conditions. -/
theorem ProgramConditions.fullFacts {d : ProgramData} (h : ProgramConditions d) :
    d.FullFacts d.completion :=
  { h.coreFacts with
    figures := h.figures h.toCoreConditions
    completion := h.completion
    roles := h.roles }

end GordieHowe
