-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Completeness.Check
public import GordieHowe.ProofSystem.Program.FieldModel

public section

/-!
# GordieHowe: the ready data of a generated program's honest strategy

`CompletionReady.ofGenerated` assembles the ready data of the honest strategy
(`RealizedProgram.CompletionReady`) from the facts every generated program has, each a generated
constant: its well-formedness (`Valid.wellFormed`), its interpretation's model (`Interp.Model`), its
derivable realizations (`Realize.derivable`), its source part (`CompletionReady.sourceValid`), and
the checks of its completeness certificate and honest roles (`Completion.completionOk`,
`Completion.rolesOk`), at the honest nodes (`Honest.nodes`) and a proof that they contain `1`.
-/

namespace GordieHowe.RealizedProgram

open Export

variable {ir : RealizedProgram} {I : Interp} {P : Plan} {orng : List (ℕ × ℕ)}
  {L : List (ℕ × String)} {S : Structure} {G : Gens} {D : CDerivations} {sr : List (ℕ × ℕ)}

/-- **The ready data of a generated program's honest strategy**, from its generated facts by name
(module docstring): the nodes `L` and that they contain `1`, the program well formed, the
interpretation's model (registry, integer readings at the plan's prime-subfield nodes, MAC model),
the derivable realizations (valid tables, covered MAC realizations), the source part well formed,
the completeness certificate's check and the honest roles' check. -/
@[expose] def CompletionReady.ofGenerated (oneNodes : OneNodes I L) (wf : ir.WellFormed)
    (model : I.Model P ir orng) (derivable : ir.Derivable (primeNodesOf P ir) sr)
    (sourceValid : ir.SourceValid) (ok : ir.completionB (primeNodesOf P ir) L S G D = true)
    (rolesOk : ir.honestRolesB L S = true) : ir.CompletionReady I (primeNodesOf P ir) S G D where
  nodes := L
  oneNodes := oneNodes
  wf := wf
  registered := model.registered
  lawful := model.lawful
  macModel := model.macModel
  tables := derivable.tables
  macsRealizable := derivable.eventsOk
  sourceValid := sourceValid
  ok := ok
  rolesOk := rolesOk

/-- **The nodes of `CompletionReady.ofGenerated` are the given nodes.** -/
@[simp] theorem CompletionReady.ofGenerated_nodes (oneNodes : OneNodes I L) (wf : ir.WellFormed)
    (model : I.Model P ir orng) (derivable : ir.Derivable (primeNodesOf P ir) sr)
    (sourceValid : ir.SourceValid) (ok : ir.completionB (primeNodesOf P ir) L S G D = true)
    (rolesOk : ir.honestRolesB L S = true) :
    (CompletionReady.ofGenerated oneNodes wf model derivable sourceValid ok rolesOk).nodes = L :=
  rfl

end GordieHowe.RealizedProgram
