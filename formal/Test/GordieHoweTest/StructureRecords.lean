-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe.Language.RealizedProgram.StructureCheck
import GordieHowe.Generated.Falcon512.Native.ROMParams.Valid.PlanNoWrap

/-!
# Tests of the structure records' common pieces

The keys' order check and its twin, the gadget index, and the plan's range requests read at the
structure records' pointers (Falcon512 Native, ROM parameters): accepted at the exported pointers,
refused at none and at shifted ones.
-/

namespace GordieHoweTest.StructureRecords

open GordieHowe GordieHowe.RealizedProgram GordieHowe.Twin

/-- A structure with two gadgets and sorted keys. -/
def ok : Structure :=
  { (default : Structure) with
    gadgets := [{ kind := .macSite, preds := [7, 5], values := [3], params := [] },
      { kind := .modField, preds := [9, 2], values := [], params := [] }]
    origins := [(3, ⟨0, 0⟩), (4, ⟨1, 0⟩)]
    logupHosts := [((0, 1), (2, 3)), ((1, 0), (2, 4))] }

example : ok.keysOkB = true := by decide

/-- The failure a twin reports, if any. -/
def failOf : Except StructFailure Unit → Option StructFailure
  | .ok _ => none
  | .error f => some f

/-- Origins out of order: refused, the twin naming the list (1) and the key (3). -/
example : failOf ({ ok with origins := [(4, ⟨1, 0⟩), (3, ⟨0, 0⟩)] } : Structure).keysOkE =
    some ⟨1, 3, .badKey⟩ := by decide

/-- A repeated key: refused. -/
example : ({ ok with origins := [(3, ⟨0, 0⟩), (3, ⟨1, 0⟩)] } : Structure).keysOkB = false := by
  decide

/-- Table groups out of lexicographic order: refused, the twin naming the list (6). -/
example : failOf ({ ok with logupHosts := [((1, 0), (2, 4)), ((0, 1), (2, 3))] } :
    Structure).keysOkE = some ⟨6, 0, .badKey⟩ := by decide

/-- The gadget index reads a gadget by its first predicate, and nothing else. -/
example : ok.gadgetAt.get? 7 = some 0 := by decide
example : ok.gadgetAt.get? 9 = some 1 := by decide
example : ok.gadgetAt.get? 5 = none := by decide

example : ∃ g, ok.gadgets[1]? = some g ∧ g.preds.head? = some 9 :=
  Structure.gadgetAt_spec (p := 9) (by decide)

open GordieHowe.Generated.Falcon512.Native.ROMParams in
/-- The exported pointers are accepted (as `Valid.planNoWrap` decides). -/
example : Plan.plan.NoWrapHoldsAt Structure.records.macRequests
    Structure.records.modRequests := by decide +kernel

open GordieHowe.Generated.Falcon512.Native.ROMParams in
/-- No pointers: the MAC record's requests are not read, so it is refused. -/
example : ¬ Plan.plan.NoWrapHoldsAt [] Structure.records.modRequests := by decide +kernel

open GordieHowe.Generated.Falcon512.Native.ROMParams in
/-- Every pointer shifted by one: refused. -/
example : ¬ Plan.plan.NoWrapHoldsAt
    (Structure.records.macRequests.map fun e => (e.1, e.2.map (· + 1)))
    Structure.records.modRequests := by decide +kernel

end GordieHoweTest.StructureRecords
