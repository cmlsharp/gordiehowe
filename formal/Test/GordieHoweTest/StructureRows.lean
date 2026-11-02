-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe.Language.Honest.Exec
import GordieHowe.Language.Realizations.Derivation
import GordieHowe.Generated.Falcon512.Native.ROMParams.Realize

/-!
# Tests of the companion rows, the interval sources and the type roles

The structure records' field rows (`modField`, `fieldRowsE`, `fieldRowOkE`), the values' intervals
at the exported interval sources (`srcLeafIvl`) and the type predicates' roles (`typeRoleVE`), on
the program of Falcon512 Native, ROM parameters: accepted at the exported pointers, refused, with
the reason, at missing, misdirected and out-of-range ones.
-/

namespace GordieHoweTest.StructureRows

open GordieHowe GordieHowe.RealizedProgram GordieHowe.Twin
open GordieHowe.Generated.Falcon512.Native.ROMParams

/-- The failure a twin reports, if any. -/
def failOf : Except StructFailure Unit → Option StructFailure
  | .ok _ => none
  | .error f => some f

/-- The program. -/
abbrev Pg : RealizedProgram := Program.program

/-- The plan's prime-subfield nodes. -/
abbrev PN : ℕ → List String := primeNodesOf Plan.plan Program.program

/-- The exported records with the gadget records `gs`. -/
def withGadgets (gs : List Gadget) : Structure := { Structure.records with gadgets := gs }

/-! ## Field rows: the `mod_q` `signature.equation` (predicate `308`) and its row (`289`) -/

/-- The exported records name the field row of every source field-form `mod_q`. -/
example : failOf (Pg.fieldRowsE Structure.records) = none := by decide +kernel

/-- The record names the row `289`. -/
example : Structure.records.gadgets.any (fun g => g.kind == .modField && g.preds == [308, 289]) =
    true := by decide +kernel

/-- No record: refused, naming the `mod_q`. -/
example : failOf (Pg.fieldRowsE (withGadgets [])) = some ⟨308, 0, .noRecord⟩ := by decide +kernel

/-- A record of another kind at the `mod_q`: refused. -/
example : failOf (Pg.fieldRowsE (withGadgets
    [{ kind := .modCommitted, preds := [308, 289], values := [], params := [] }])) =
    some ⟨308, 0, .wrongKind⟩ := by decide +kernel

/-- A record without its row slot: refused. -/
example : failOf (Pg.fieldRowsE (withGadgets
    [{ kind := .modField, preds := [308], values := [], params := [] }])) =
    some ⟨308, 0, .slotMismatch⟩ := by decide +kernel

/-- A row past the predicates: refused. -/
example : failOf (Pg.fieldRowsE (withGadgets
    [{ kind := .modField, preds := [308, 100000], values := [], params := [] }])) =
    some ⟨308, 1, .badPointer⟩ := by decide +kernel

/-- Another predicate as the row (`288`, not of role `realization 308`): refused. -/
example : failOf (Pg.fieldRowsE (withGadgets
    [{ kind := .modField, preds := [308, 288], values := [], params := [] }])) =
    some ⟨308, 1, .roleMismatch⟩ := by decide +kernel

/-- The derivation checker's clause at the `mod_q`: accepted at the exported records, refused
without its record. -/
example : failOf (Pg.fieldRowOkE Structure.records 308 (Pg.predicate 308).body) = none := by
  decide +kernel
example : failOf (Pg.fieldRowOkE (withGadgets []) 308 (Pg.predicate 308).body) =
    some ⟨308, 0, .noRecord⟩ := by decide +kernel

/-- The row's role names its `mod_q` (`fieldRowRealB`); its neighbour is no field row. -/
example : Pg.fieldRowRealB 289 = true := by decide +kernel
example : Pg.fieldRowRealB 290 = false := by decide +kernel

/-! ## Type roles: the Boolean check `crossing.c_A.boolean` (predicate `292`) of value `594` -/

/-- The exported role names the value. -/
example : failOf (Pg.typeRoleVE 594 (Pg.value 594)) = none := by decide +kernel

/-- A type predicate whose role names another value: refused. -/
example : failOf (Pg.typeRoleVE 594 { Pg.value 594 with typeSource := .pred 291 }) =
    some ⟨594, 0, .roleMismatch⟩ := by decide +kernel

/-- A type predicate past the predicates: refused. -/
example : failOf (Pg.typeRoleVE 594 { Pg.value 594 with typeSource := .pred 100000 }) =
    some ⟨594, 0, .badPointer⟩ := by decide +kernel

/-! ## Interval sources: the statement value `hhat` (value `593`), declared below `q` -/

/-- The exported source gives the declared interval. -/
example : Pg.srcLeafIvl PN Structure.records (Pg.valueField 593) 593 = some ⟨0, 12288⟩ := by
  decide +kernel

/-- No source: no interval. -/
example : Pg.srcLeafIvl PN { Structure.records with ivlSources := [] } (Pg.valueField 593) 593 =
    none := by decide +kernel

/-- A source the value's kind does not take (a constant's): no interval. -/
example : Pg.srcLeafIvl PN { Structure.records with ivlSources := [(593, .const)] }
    (Pg.valueField 593) 593 = none := by decide +kernel

end GordieHoweTest.StructureRows
