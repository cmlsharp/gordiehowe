-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.FieldCodes
public import GordieHoweNative.Language.FieldNums
public import GordieHoweNative.Language.Realizations.Circuit.RelEntry

/-! # The compiled GKR part

Circuit lookup preserves the empty default past the supplied data. The check ranges over the
program's circuits and uses the field table's selected interpretation key at every circuit.
-/

public section

namespace GordieHowe

open RealizedProgram
local notation "ℕ" => Nat

/-- **The empty certificate data**, read past a program's circuits: no constants, nodes, layers,
schedule or entries. -/
@[expose] instance instInhabitedCircuitData_gordieHowe : Inhabited CircuitData :=
  ⟨{ c := 0, w := 0, chr := 0, prime := 0, char2 := false, neg1 := 0, half := 0,
     consts := ⟨0, .ident⟩, dag := ⟨.nil, 0, 0, [], []⟩, layered := ⟨0, []⟩,
     sched := ⟨0, [], [], []⟩, table := ⟨0, .nil⟩, entries := [] }⟩

namespace ProgramData

variable (d : ProgramData)

/-- Circuit `c`'s certificate data. -/
@[expose] def circuitData (c : ℕ) : CircuitData := d.circuits.getD c default

/-- Circuit `c`'s code arithmetic: its field's, by the field table. -/
@[expose] def circuitCode (c : ℕ) : GKR.Fold.CodeArith :=
  (d.fieldTable.interp.key (d.fieldTable.circuitField c)).code

/-- Every program circuit passes its certificate and has its selected field's characteristic.
The supplied data list need not have a prescribed length: lookups retain their empty default. -/
@[expose] def gkrPartB : Bool :=
  (List.range d.program.circuits.length).all fun c =>
    d.program.circuitCertBC c (d.circuitCode c) (d.circuitData c) &&
      (d.circuitData c).chr ==
        (d.fieldTable.interp.key (d.fieldTable.circuitField c)).specN.characteristic

/-- Defining equation for the GKR part, used by the semantic transport. -/
theorem gkrPartB_eq : d.gkrPartB =
    (List.range d.program.circuits.length).all (fun c =>
      d.program.circuitCertBC c (d.circuitCode c) (d.circuitData c) &&
        (d.circuitData c).chr ==
          (d.fieldTable.interp.key (d.fieldTable.circuitField c)).specN.characteristic) := rfl

end ProgramData
end GordieHowe
