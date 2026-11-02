-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe.Language.Completeness.Check
import GordieHowe.ProofSystem.Program.FieldDomain
import GordieHowe.ProofSystem.Program.FieldTree
import GordieHowe.Generated.Falcon512.Native.ROMParams.Plan
import GordieHowe.Generated.Falcon512.Native.ROMParams.Interp
import GordieHowe.Generated.Falcon512.Native.ROMParams.Structure

/-!
# Tests of the name checks at the structure records' pointers

On Falcon512 Native, ROM parameters (late value 609 `mac.value` with its message 610; member check 0
of `hhat`, value 593; domains `H`, `A`):

* the messages' check (`messageRecsE`) accepts the exported `messages` and refuses a message value
  with no entry (`uncovered`) and an entry naming no message of its key (`notMessage`);
* the member checks' check (`memberValuesE`) accepts the exported `memberValues` and refuses a
  pointer to another value (`notMember`), a missing entry (`noRecord`) and, on a two-value program,
  a pointer past the first member value (`earlierMember`);
* the domains' alignment (`domainsAlignedE`) accepts the plan and refuses swapped domains
  (`domainMismatch`) and a missing one (`domainCount`);
* a predicate's name at its identifier (`predNameE`) accepts `270` as `h2p.select.start` and refuses
  `271` (`nameMismatch`);
* the packing tree's checks (`treeOkE`, `placeOkE`) accept domain `H`'s plan edges and refuse an
  edge of degree `0` (`treeEdge`) and edges whose children name no cell's node (`nodeDegree`).
-/

namespace GordieHoweTest.StructureNames

open GordieHowe GordieHowe.RealizedProgram GordieHowe.Twin
open GordieHowe.Generated.Falcon512.Native.ROMParams

/-- The failure a twin reports, if any. -/
def failOf : Except StructFailure Unit → Option StructFailure
  | .ok _ => none
  | .error f => some f

/-- The program. -/
abbrev ir : RealizedProgram := Program.program

/-- The structure records with other `messages`. -/
def withMessages (l : List (ℕ × ℕ)) : Structure := { Structure.records with messages := l }

/-- The structure records with other `memberValues`. -/
def withMembers (l : List (ℕ × ℕ)) : Structure := { Structure.records with memberValues := l }

/-! ## Messages (H8) -/

/-- The exported entries, as printed. -/
example : Structure.records.messages = [(609, 610)] := by decide +kernel

/-- The exported entries are accepted. -/
example : failOf (ir.messageRecsE Structure.records) = none := by decide +kernel

/-- The verdict is the twin's. -/
example (S : Structure) : ir.messageRecsB S = okB (ir.messageRecsE S) := rfl

/-- No entry: the message value 610 is refused, naming it and its late value. -/
example : failOf (ir.messageRecsE (withMessages [])) = some ⟨610, 609, .uncovered⟩ := by
  decide +kernel

/-- An entry naming `hhat` (593) as `mac.value`'s message: refused, naming the entry. -/
example : failOf (ir.messageRecsE (withMessages [(609, 593)])) = some ⟨609, 593, .notMessage⟩ := by
  decide +kernel

/-! ## Member checks (N2) -/

/-- The exported entries, as printed. -/
example : Structure.records.memberValues = [(0, 593)] := by decide +kernel

/-- The exported entries are accepted. -/
example : failOf (ir.memberValuesE Structure.records) = none := by decide +kernel

/-- The verdict is the twin's. -/
example (S : Structure) : ir.memberValuesB S = okB (ir.memberValuesE S) := rfl

/-- Check 0 pointed at value 594 (`crossing.c_A`): refused, naming the check and the value. -/
example : failOf (ir.memberValuesE (withMembers [(0, 594)])) = some ⟨0, 594, .notMember⟩ := by
  decide +kernel

/-- Check 0's entry removed: refused, naming the check. -/
example : failOf (ir.memberValuesE (withMembers [])) = some ⟨0, 0, .noRecord⟩ := by
  decide +kernel

/-- A statement value of member `k`, an opaque value of no argument. -/
def kValue : Value :=
  { name := "statement.k", shape := [1], kind := .pub (.«opaque» "statement.k" []), type := .field }

/-- A check of member `k`. -/
def kCheck : MemberCheck := ⟨"k", 0, 2, "falcon_key_canonical", [12289]⟩

/-- A program of two values that are both member `k`, and one check of `k`. -/
def twoMembers : RealizedProgram :=
  { phases := 1, fields := [], domains := [], values := [kValue, kValue], predicates := [],
    statement := { checks := [kCheck] } }

/-- The first member value is accepted. -/
example : failOf (twoMembers.memberValuesE { Structure.records with memberValues := [(0, 0)] }) =
    none := by
  decide +kernel

/-- The second is refused: value 0 is the member too. -/
example : failOf (twoMembers.memberValuesE { Structure.records with memberValues := [(0, 1)] }) =
    some ⟨0, 0, .earlierMember⟩ := by
  decide +kernel

/-! ## Domains by position (S6) -/

/-- The plan's domains are the program's, position by position. -/
example : failOf (domainsAlignedE Plan.plan ir) = none := by decide +kernel

/-- The verdict is the twin's. -/
example : domainsAlignedB Plan.plan ir = okB (domainsAlignedE Plan.plan ir) := rfl

/-- The plan's domains swapped: refused at position 0. -/
example : failOf (domainsAlignedE { Plan.plan with domains := Plan.plan.domains.reverse } ir) =
    some ⟨0, 0, .domainMismatch⟩ := by
  decide +kernel

/-- The plan's last domain dropped: refused, naming both counts. -/
example : failOf (domainsAlignedE { Plan.plan with domains := Plan.plan.domains.take 1 } ir) =
    some ⟨1, 2, .domainCount⟩ := by
  decide +kernel

/-! ## Predicate names (N1) -/

example : failOf (ir.predNameE 270 "h2p.select.start") = none := by decide +kernel

example : failOf (ir.predNameE 271 "h2p.select.start") = some ⟨271, 0, .nameMismatch⟩ := by
  decide +kernel

/-! ## The packing tree (FT) -/

/-- Domain `H`'s plan edges. -/
abbrev edgesH : List Export.PackingEdge := ir.planPacking Plan.plan 0

/-- The tree check accepts them. -/
example : failOf (treeOkE edgesH fieldPkH.n) = none := by decide +kernel

/-- The verdict is the twin's. -/
example (es : List Export.PackingEdge) (n : ℕ) : treeOkB es n = okB (treeOkE es n) := rfl

/-- Edge 0 of degree `0`: refused, naming the edge. -/
example : failOf (treeOkE (edgesH.modifyHead fun e => { e with degree := 0 })
    fieldPkH.n) = some ⟨0, 0, .treeEdge⟩ := by
  decide +kernel

/-- The placement check accepts domain `H`'s cells on its edges. -/
example : failOf (ir.placeOkE (I := interp) 0
    fieldPkH edgesH) = none := by
  decide +kernel

/-- Edges whose children name no node: a named cell is refused for its node's degree. -/
example : (failOf (ir.placeOkE (I := interp) 0
    fieldPkH
      (edgesH.map fun e => { e with child := e.child ++ "'" }))).map
      (·.reason) = some .nodeDegree := by
  decide +kernel

end GordieHoweTest.StructureNames
