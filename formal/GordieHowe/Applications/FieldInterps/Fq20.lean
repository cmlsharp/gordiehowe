-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldModel
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative20Relative
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNativeCoords

@[expose] public section

/-!
# GordieHowe: `F_q^20` read in Lean

The field interpretation of `F_q^20` (`q = 12289`), shared by the native Falcon programs at the
QROM parameters (`Falcon512.Native.QROMParams`, `Falcon512.Ring.Native.QROMParams`):

* **`F_q^20`** (`fq20`): the registry entry `falconNative20Entry`, `FalconNativeField20`; constants
  are casts of naturals, the integer reading is the constant coefficient (`falconQuarticCoords` of
  the first `falconNative20Coords` coordinate); the node `GF(p^1)` is the prime subfield `F_q`
  (`fq20Node`), every other node the whole field; no bit coordinates (an odd field).
* **Its model** at `GF(p^1)` (`fq20_model`): the integer reading is below `q`, inverts the cast of
  a natural below `q`, and an element of `F_q` is the cast of its integer reading; the integer
  reading is linear (`fq20_readLinear`).
-/

namespace GordieHowe.RealizedProgram

open Export RelativePacking

/-- **The nodes of `F_q^20`**: `GF(p^1)` is the prime subfield `F_q`, any other name the field. -/
def fq20Node (s : String) : AddSubgroup FalconNativeField20 :=
  if s = "GF(p^1)" then (fixedField FalconNativeField20 12289 1).toSubring.toAddSubgroup else ⊤

/-- Membership in a node of `F_q^20` is decidable (one exponentiation for `F_q`). -/
instance fq20NodeDec (s : String) : DecidablePred (· ∈ fq20Node s) := fun x => by
  unfold fq20Node
  split
  · exact decidableMemFixedField (p := 12289) (m := 1) x
  · exact isTrue (AddSubgroup.mem_top x)

/-- **`F_q^20` as a field of the program**: the registry entry, `FalconNativeField20`, constants as
casts of naturals, the integer reading the constant coefficient, the nodes `fq20Node`, no bit
coordinates (an odd field). -/
def fq20 : FieldInterp where
  spec := falconNative20Entry.spec
  K := FalconNativeField20
  decode n := (n : FalconNativeField20)
  toNat x := (falconQuarticCoords (falconNative20Coords x 0) 0).val
  node := fq20Node
  memDec := fq20NodeDec
  coord _ _ _ := false

/-- **The model of `F_q^20`** at its prime subfield `GF(p^1)` (`FieldInterp.model_of_primeCoord`):
the registry entry `falconNative20Entry` (cardinality `q^20`, `falconNativeField20_card`), the
integer reading the constant coordinate (`falconNative20Coords_natCast`,
`falconNative20Coords_algebraMap`). -/
theorem fq20_model : fq20.Model ["GF(p^1)"] [] :=
  FieldInterp.model_of_primeCoord (spec := falconNative20Entry.spec) (p := 12289)
    (c := fun x => falconQuarticCoords (falconNative20Coords x 0) 0)
    ⟨falconNative20Entry, by simp [fieldRegistry], rfl⟩ rfl falconNativeField20_card
    falconNative20Coords_natCast falconNative20Coords_algebraMap
    (fun _ hx => by rwa [fq20Node, if_pos rfl] at hx)
    (by rw [fq20Node, if_neg (by decide)])

/-- **The integer reading of `F_q^20` reads `0` as `0`.** -/
theorem fq20_toNat_zero : fq20.toNat 0 = 0 := by
  have h := fq20_model.toNat_natCast 0 (by decide)
  rwa [Nat.cast_zero] at h

/-- **`F_q^20` reads linearly** (`FieldInterp.ReadLinear`): its integer reading is the constant
coordinate, additive (`falconNative20Coords_val_cast_add`). -/
theorem fq20_readLinear : fq20.ReadLinear :=
  .of_add falconNative20Coords_val_cast_add (by rw [fq20_toNat_zero, Nat.cast_zero])

end GordieHowe.RealizedProgram
