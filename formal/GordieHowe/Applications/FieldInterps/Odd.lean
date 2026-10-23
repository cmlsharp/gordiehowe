-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldModel
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative6Coords
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative11Coords
public import GordieHowe.Foundations.Fields.GoldilocksCoords

@[expose] public section

/-!
# GordieHowe: the odd fields of the ML-DSA and emulated programs, read in Lean

The field interpretations (`FieldInterp`, `GordieHowe/Language/RealizedProgram/Semantics.lean`) of domain `A`'s
fields that `F_q^9` and `F_q^20` (`GordieHowe/Applications/FieldInterps/Basic.lean`,
`GordieHowe/Applications/FieldInterps/Fq20.lean`) do not cover, each with its model at the prime subfield
`GF(p^1)` (`FieldInterp.model_of_primeCoord`):

* **`F_q^6`** (`GordieHowe.RealizedProgram.fq6`, `q = 8380417`, `MLDSA44.Native.ROMParams`) and **`F_q^11`**
  (`GordieHowe.RealizedProgram.fq11`, `MLDSA44.Native.QROMParams`);
* **Goldilocks²** (`GordieHowe.RealizedProgram.gold2`, `Falcon512.Ring.Carrier.ROMParams`,
  `MLDSA44.Emulated.ROMParams`) and **Goldilocks⁴** (`GordieHowe.RealizedProgram.gold4`,
  `Falcon512.Ring.Carrier.QROMParams`, `MLDSA44.Emulated.QROMParams`).

Each is the registry entry's field, constants cast from naturals, the integer reading the constant
coordinate, the node `GF(p^1)` the prime subfield, no bit coordinates (an odd field). The fields
keep the namespaces of the configurations that introduced them.
-/

namespace GordieHowe.MLDSA44.Native.ROMParams.HashField

open RealizedProgram.Export RelativePacking

/-- **The nodes of `F_q^6`**: `GF(p^1)` is the prime subfield `F_q`, any other name the field. -/
def _root_.GordieHowe.RealizedProgram.fq6Node (s : String) : AddSubgroup MLDSANativeField6 :=
  if s = "GF(p^1)" then (fixedField MLDSANativeField6 8380417 1).toSubring.toAddSubgroup else ⊤

/-- Membership in a node of `F_q^6` is decidable (one exponentiation for `F_q`). -/
instance _root_.GordieHowe.RealizedProgram.fq6NodeDec (s : String) : DecidablePred (· ∈ RealizedProgram.fq6Node s) := fun x => by
  unfold RealizedProgram.fq6Node
  split
  · exact decidableMemFixedField (p := 8380417) (m := 1) x
  · exact isTrue (AddSubgroup.mem_top x)

/-- **`F_q^6` as a field of the program**: the registry entry, `MLDSANativeField6`, constants as
casts of naturals, the integer reading the constant coefficient, the nodes `fq6Node`, no bit
coordinates (an odd field). -/
def _root_.GordieHowe.RealizedProgram.fq6 : RealizedProgram.FieldInterp where
  spec := mldsaNative6Entry.spec
  K := MLDSANativeField6
  decode n := (n : MLDSANativeField6)
  toNat x := (mldsaNative6Coords x 0).val
  node := RealizedProgram.fq6Node
  memDec := RealizedProgram.fq6NodeDec
  coord _ _ _ := false

/-- **The model of `F_q^6`** at its prime subfield `GF(p^1)` (`FieldInterp.model_of_primeCoord`):
the registry entry `mldsaNative6Entry` (cardinality `q^6`, `mldsaNativeField_card`), the integer
reading the constant coordinate (`mldsaNative6Coords_natCast`, `mldsaNative6Coords_algebraMap`). -/
theorem _root_.GordieHowe.RealizedProgram.fq6_model : RealizedProgram.fq6.Model ["GF(p^1)"] [] :=
  RealizedProgram.FieldInterp.model_of_primeCoord (spec := mldsaNative6Entry.spec) (p := 8380417)
    (c := fun x => mldsaNative6Coords x 0) ⟨mldsaNative6Entry, by simp [fieldRegistry], rfl⟩ rfl
    mldsaNativeField_card mldsaNative6Coords_natCast mldsaNative6Coords_algebraMap
    (fun _ hx => by rwa [RealizedProgram.fq6Node, if_pos rfl] at hx)
    (by rw [RealizedProgram.fq6Node, if_neg (by decide)])

end GordieHowe.MLDSA44.Native.ROMParams.HashField

namespace GordieHowe.MLDSA44.Native.QROMParams.HashField

open RealizedProgram.Export RelativePacking

/-- **The nodes of `F_q^11`**: `GF(p^1)` is the prime subfield `F_q`, any other name the field. -/
def _root_.GordieHowe.RealizedProgram.fq11Node (s : String) : AddSubgroup MLDSANativeField11 :=
  if s = "GF(p^1)" then (fixedField MLDSANativeField11 8380417 1).toSubring.toAddSubgroup else ⊤

/-- Membership in a node of `F_q^11` is decidable (one exponentiation for `F_q`). -/
instance _root_.GordieHowe.RealizedProgram.fq11NodeDec (s : String) : DecidablePred (· ∈ RealizedProgram.fq11Node s) := fun x => by
  unfold RealizedProgram.fq11Node
  split
  · exact decidableMemFixedField (p := 8380417) (m := 1) x
  · exact isTrue (AddSubgroup.mem_top x)

/-- **`F_q^11` as a field of the program**: the registry entry, `MLDSANativeField11`, constants as
casts of naturals, the integer reading the constant coefficient, the nodes `fq11Node`, no bit
coordinates (an odd field). -/
def _root_.GordieHowe.RealizedProgram.fq11 : RealizedProgram.FieldInterp where
  spec := mldsaNative11Entry.spec
  K := MLDSANativeField11
  decode n := (n : MLDSANativeField11)
  toNat x := (mldsaNative11Coords x 0).val
  node := RealizedProgram.fq11Node
  memDec := RealizedProgram.fq11NodeDec
  coord _ _ _ := false

/-- **The model of `F_q^11`** at its prime subfield `GF(p^1)` (`FieldInterp.model_of_primeCoord`):
the registry entry `mldsaNative11Entry` (cardinality `q^11`, `mldsaNativeField11_card`), the integer
reading the constant coordinate (`mldsaNative11Coords_natCast`,
`mldsaNative11Coords_algebraMap`). -/
theorem _root_.GordieHowe.RealizedProgram.fq11_model : RealizedProgram.fq11.Model ["GF(p^1)"] [] :=
  RealizedProgram.FieldInterp.model_of_primeCoord (spec := mldsaNative11Entry.spec) (p := 8380417)
    (c := fun x => mldsaNative11Coords x 0) ⟨mldsaNative11Entry, by simp [fieldRegistry], rfl⟩ rfl
    mldsaNativeField11_card mldsaNative11Coords_natCast mldsaNative11Coords_algebraMap
    (fun _ hx => by rwa [RealizedProgram.fq11Node, if_pos rfl] at hx)
    (by rw [RealizedProgram.fq11Node, if_neg (by decide)])

end GordieHowe.MLDSA44.Native.QROMParams.HashField

namespace GordieHowe.Falcon512.Ring.Carrier.ROMParams

open RealizedProgram.Export RelativePacking

/-- **The nodes of Goldilocks²**: `GF(p^1)` is the prime subfield `F_p`, any other name the
field. -/
def _root_.GordieHowe.RealizedProgram.gold2Node (s : String) : AddSubgroup GoldilocksExt2 :=
  if s = "GF(p^1)" then (fixedField GoldilocksExt2 pGold 1).toSubring.toAddSubgroup else ⊤

/-- Membership in a node of Goldilocks² is decidable (one exponentiation for `F_p`). -/
instance _root_.GordieHowe.RealizedProgram.gold2NodeDec (s : String) : DecidablePred (· ∈ RealizedProgram.gold2Node s) := fun x => by
  unfold RealizedProgram.gold2Node
  split
  · exact decidableMemFixedField (p := pGold) (m := 1) x
  · exact isTrue (AddSubgroup.mem_top x)

/-- **Goldilocks² as a field of the program**: the registry entry, `GoldilocksExt2`, constants as
casts of naturals, the integer reading the constant coordinate, the nodes `gold2Node`, no bit
coordinates (an odd field). -/
def _root_.GordieHowe.RealizedProgram.gold2 : RealizedProgram.FieldInterp where
  spec := goldilocksExt2Entry.spec
  K := GoldilocksExt2
  decode n := (n : GoldilocksExt2)
  toNat x := (goldilocksExt2Coords x 0).val
  node := RealizedProgram.gold2Node
  memDec := RealizedProgram.gold2NodeDec
  coord _ _ _ := false

/-- **The model of Goldilocks²** at its prime subfield `GF(p^1)`
(`FieldInterp.model_of_primeCoord`): the registry entry `goldilocksExt2Entry` (cardinality `p^2`,
`goldilocksExt2_card`), the integer reading the constant coordinate (`goldilocksExt2Coords_natCast`,
`goldilocksExt2Coords_algebraMap`). -/
theorem _root_.GordieHowe.RealizedProgram.gold2_model : RealizedProgram.gold2.Model ["GF(p^1)"] [] :=
  RealizedProgram.FieldInterp.model_of_primeCoord (spec := goldilocksExt2Entry.spec) (p := pGold)
    (c := fun x => goldilocksExt2Coords x 0) ⟨goldilocksExt2Entry, by simp [fieldRegistry], rfl⟩ rfl
    goldilocksExt2_card goldilocksExt2Coords_natCast goldilocksExt2Coords_algebraMap
    (fun _ hx => by rwa [RealizedProgram.gold2Node, if_pos rfl] at hx)
    (by rw [RealizedProgram.gold2Node, if_neg (by decide)])

end GordieHowe.Falcon512.Ring.Carrier.ROMParams

namespace GordieHowe.Falcon512.Ring.Carrier.QROMParams

open RealizedProgram.Export RelativePacking

/-- **The nodes of Goldilocks⁴**: `GF(p^1)` is the prime subfield `F_p`, any other name the
field. -/
def _root_.GordieHowe.RealizedProgram.gold4Node (s : String) : AddSubgroup GoldilocksExt4 :=
  if s = "GF(p^1)" then (fixedField GoldilocksExt4 pGold 1).toSubring.toAddSubgroup else ⊤

/-- Membership in a node of Goldilocks⁴ is decidable (one exponentiation for `F_p`). -/
instance _root_.GordieHowe.RealizedProgram.gold4NodeDec (s : String) : DecidablePred (· ∈ RealizedProgram.gold4Node s) := fun x => by
  unfold RealizedProgram.gold4Node
  split
  · exact decidableMemFixedField (p := pGold) (m := 1) x
  · exact isTrue (AddSubgroup.mem_top x)

/-- **Goldilocks⁴ as a field of the program**: the registry entry, `GoldilocksExt4`, constants as
casts of naturals, the integer reading the constant coordinate, the nodes `gold4Node`, no bit
coordinates (an odd field). -/
def _root_.GordieHowe.RealizedProgram.gold4 : RealizedProgram.FieldInterp where
  spec := goldilocksExt4Entry.spec
  K := GoldilocksExt4
  decode n := (n : GoldilocksExt4)
  toNat x := (goldilocksExt4Coords x 0).val
  node := RealizedProgram.gold4Node
  memDec := RealizedProgram.gold4NodeDec
  coord _ _ _ := false

/-- **The model of Goldilocks⁴** at its prime subfield `GF(p^1)`
(`FieldInterp.model_of_primeCoord`): the registry entry `goldilocksExt4Entry` (cardinality `p^4`,
`goldilocksExt4_card`), the integer reading the constant coordinate (`goldilocksExt4Coords_natCast`,
`goldilocksExt4Coords_algebraMap`). -/
theorem _root_.GordieHowe.RealizedProgram.gold4_model : RealizedProgram.gold4.Model ["GF(p^1)"] [] :=
  RealizedProgram.FieldInterp.model_of_primeCoord (spec := goldilocksExt4Entry.spec) (p := pGold)
    (c := fun x => goldilocksExt4Coords x 0) ⟨goldilocksExt4Entry, by simp [fieldRegistry], rfl⟩ rfl
    goldilocksExt4_card goldilocksExt4Coords_natCast goldilocksExt4Coords_algebraMap
    (fun _ hx => by rwa [RealizedProgram.gold4Node, if_pos rfl] at hx)
    (by rw [RealizedProgram.gold4Node, if_neg (by decide)])

end GordieHowe.Falcon512.Ring.Carrier.QROMParams
