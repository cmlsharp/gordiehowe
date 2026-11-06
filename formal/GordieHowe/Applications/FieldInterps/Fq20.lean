-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Applications.FieldInterps.Codes
public import GordieHowe.ProofSystem.Program.FieldModel
public import GordieHowe.Applications.Falcon512.Fields.FalconNative20Relative
public import GordieHowe.Applications.Falcon512.Fields.FalconNativeCoords

@[expose] public section

/-!
# GordieHowe: `F_q^20` read in Lean

The field interpretation of `F_q^20` (`q = 12289`), shared by the native Falcon programs at the
QROM parameters (`Falcon512.Native.QROMParams`, `Falcon512.Ring.Native.QROMParams`):

* **`F_q^20`** (`fq20`): the registry entry `falconNative20Entry`, `FalconNativeField20`; constants
  are coefficient vectors in the C++ encoding, over the quartic step's (`fq20Code`,
  `fq20QuarticCode`), the integer reading is the constant coefficient (`falconQuarticCoords` of
  the first `falconNative20Coords` coordinate); the node `GF(p^1)` is the prime subfield `F_q`
  (`fq20Node`), every other node the whole field; no bit coordinates (an odd field).
* **Its model** at `GF(p^1)` (`fq20_model`): the integer reading is below `q`, inverts the cast of
  a natural below `q`, and an element of `F_q` is the cast of its integer reading; the integer
  reading is linear (`fq20_readLinear`).
-/

namespace GordieHowe.RealizedProgram

open Export RelativePacking

/-- **The decoding of the quartic step**: coefficient `i` of `u^i` is digit `i` of `14` bits. -/
def fq20QuarticDecode (c : ℕ) : FalconQuartic :=
  GKR.Fold.extDecode (fun c : ℕ => (c : ZMod 12289)) 14 4 c

/-- The quartic step decodes `0` to `0`. -/
theorem fq20QuarticDecode_zero : fq20QuarticDecode 0 = 0 := by
  rw [fq20QuarticDecode, GKR.Fold.ExtCode.extDecode_natCast_of_lt (by norm_num) (by norm_num),
    Nat.cast_zero, PolyRep.const_zero]
  rfl

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
coefficient vectors (`GKR.Fold.extDecode` over `fq20QuarticDecode`), the integer reading the
constant coefficient, the nodes `fq20Node`, no bit
coordinates (an odd field). -/
def fq20 : FieldInterp where
  spec := falconNative20Entry.spec
  K := FalconNativeField20
  decode := GKR.Fold.extDecode fq20QuarticDecode 56 5
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
    (fun c hc => by
      rw [GKR.Fold.extDecode_of_lt _ fq20QuarticDecode_zero (hc.trans (by norm_num)),
        fq20QuarticDecode, GKR.Fold.ExtCode.extDecode_natCast_of_lt (by norm_num) hc]
      rfl)
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

/-- `v^5 = u + 2`: the code `2 + 2^14` decodes to `u + 2`. -/
theorem fq20QuarticDecode_beta : fq20QuarticDecode 16386 = falconU + 2 := by
  change GKR.Fold.extDecode _ 14 4 16386 =
    PolyRep.add PolyRep.gen (PolyRep.const ((2 : ℕ) : ZMod 12289))
  refine Vector.ext fun i hi => ?_
  interval_cases i <;> simp [GKR.Fold.digit, PolyRep.add, PolyRep.gen, PolyRep.const]

/-- **The code arithmetic of `F_q^20` is the field's** (`GKR.Fold.ExtCode.hom`, over the quartic
step's, `GKR.Fold.ExtCode.overPrime_hom`). -/
theorem fq20_codeHom : fq20.CodeHom fq20Code.arith :=
  GKR.Fold.ExtCode.hom falconNative20_polySpec
    (GKR.Fold.ExtCode.overPrime_hom falconQuartic_polySpec Nat.cast_ofNat (by norm_num))
    fq20QuarticDecode_beta
    (fq20QuarticCode.arith_bounded (GKR.Fold.primeArith_bounded (by norm_num) (by decide)))

/-- **`F_q^20`'s arithmetic is arithmetic modulo `q` on `F_q`** (A15: the tower over `F_q^4` over
`F_q`), so its checks take the fast path `.withPrime 12289`. -/
theorem fq20Code_primeOn : fq20Code.arith.PrimeOn 12289 :=
  GKR.Fold.ExtCode.primeOn (E := fq20Code)
    (GKR.Fold.ExtCode.overPrime_primeOn (p := 12289) (s := 14) (n := 4) (beta := 11)
      (by norm_num) (by norm_num))
    (GKR.Fold.ExtCode.absorbs (E := fq20QuarticCode) (GKR.Fold.primeArith_absorbs 12289))
    (by norm_num) (by decide) (by decide)

end GordieHowe.RealizedProgram
