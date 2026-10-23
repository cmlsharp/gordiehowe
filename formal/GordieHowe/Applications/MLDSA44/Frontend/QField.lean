-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.ROMParams.HashField
public import GordieHowe.Applications.MLDSA44.Native.QROMParams.HashField
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative11Coords
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative6Coords
public import LatticeCrypto.MLDSA.Arithmetic

@[expose] public section

/-!
# GordieHowe frontend: the field facts of a native ML-DSA program's domain `A`

The native ML-DSA programs carry domain `A` over an extension of `F_q`, `q = 8380417`: `F_q^6`
at the ROM parameters (`GordieHowe.RealizedProgram.fq6`), `F_q^11` at the QROM parameters
(`GordieHowe.RealizedProgram.fq11`). The native frontend
reads domain `A` only through the data and facts below (`GordieHowe.MLDSA44.QField`), discharged once per field:
characteristic `q`, constants decode as casts, the integer reading is the value of the constant
coordinate (an additive map to `F_q` taking a natural's cast to its cast), and the node `GF(p^1)`
is the prime subfield, on which the cast of the integer reading is the element.
-/

namespace GordieHowe.RealizedProgram

open RelativePacking

/-- **The field data and facts of a native program's domain `A`.** -/
class _root_.GordieHowe.MLDSA44.QField (F0 : FieldInterp) where
  /-- The field has characteristic `q`. -/
  charP : CharP F0.K 8380417
  /-- The registry entry's characteristic is `q`. -/
  char_spec : F0.spec.characteristic = 8380417
  /-- Constants decode as casts. -/
  decode_eq : ∀ c, F0.decode c = (c : F0.K)
  /-- The constant coordinate. -/
  coord0 : F0.K →+ _root_.MLDSA.Coeff
  /-- The constant coordinate of a natural's cast is its cast. -/
  coord0_natCast : ∀ n : ℕ, coord0 (n : F0.K) = (n : _root_.MLDSA.Coeff)
  /-- The integer reading is the value of the constant coordinate. -/
  toNat_eq : ∀ x, F0.toNat x = (coord0 x).val
  /-- The node `GF(p^1)` is the prime subfield. -/
  node_prime : ∀ x, x ∈ F0.node "GF(p^1)" ↔ x ∈ fixedField F0.K 8380417 1
  /-- On the prime subfield, the cast of the integer reading is the element. -/
  natCast_toNat : ∀ x, x ∈ F0.node "GF(p^1)" → ((F0.toNat x : ℕ) : F0.K) = x

instance _root_.GordieHowe.MLDSA44.QField.instCharP (F0 : FieldInterp) [h : MLDSA44.QField F0] : CharP F0.K 8380417 :=
  h.charP

/-- **The integer reading of a natural below `q`** is the natural. -/
theorem _root_.GordieHowe.MLDSA44.QField.toNat_natCast {F0 : FieldInterp} [MLDSA44.QField F0] {k : ℕ} (hk : k < 8380417) :
    F0.toNat (k : F0.K) = k := by
  rw [MLDSA44.QField.toNat_eq, MLDSA44.QField.coord0_natCast, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt hk

/-- **The coordinates of a sum** in `MLDSANativeField6` are the sums of the coordinates. -/
theorem mldsaNative6Coords_add (x y : MLDSANativeField6) (i : Fin 6) :
    mldsaNative6Coords (x + y) i = mldsaNative6Coords x i + mldsaNative6Coords y i := by
  show PolyRep.coordsEquiv (PolyRep.add (n := 6) x y) i = _
  simp [PolyRep.add, mldsaNative6Coords]
  rfl

/-- **The coordinates of `0`** in `MLDSANativeField6` are `0`. -/
theorem mldsaNative6Coords_zero (i : Fin 6) : mldsaNative6Coords (0 : MLDSANativeField6) i = 0 := by
  show PolyRep.coordsEquiv (PolyRep.zero : Vector (ZMod 8380417) 6) i = 0
  simp [PolyRep.zero]

/-- **The coordinates of a sum** in `MLDSANativeField11` are the sums of the coordinates. -/
theorem mldsaNative11Coords_add (x y : MLDSANativeField11) (i : Fin 11) :
    mldsaNative11Coords (x + y) i = mldsaNative11Coords x i + mldsaNative11Coords y i := by
  show PolyRep.coordsEquiv (PolyRep.add (n := 11) x y) i = _
  simp [PolyRep.add, mldsaNative11Coords]
  rfl

/-- **The coordinates of `0`** in `MLDSANativeField11` are `0`. -/
theorem mldsaNative11Coords_zero (i : Fin 11) :
    mldsaNative11Coords (0 : MLDSANativeField11) i = 0 := by
  show PolyRep.coordsEquiv (PolyRep.zero : Vector (ZMod 8380417) 11) i = 0
  simp [PolyRep.zero]

open RealizedProgram (fq6 fq6Node) in
/-- `F_q^6` has domain `A`'s field data. -/
instance : MLDSA44.QField fq6 where
  charP := inferInstanceAs (CharP MLDSANativeField6 8380417)
  char_spec := rfl
  decode_eq _ := rfl
  coord0 :=
    { toFun := fun x => mldsaNative6Coords x 0
      map_zero' := mldsaNative6Coords_zero 0
      map_add' := fun x y => mldsaNative6Coords_add x y 0 }
  coord0_natCast := mldsaNative6Coords_natCast
  toNat_eq _ := rfl
  node_prime x := by
    change x ∈ fq6Node "GF(p^1)" ↔ _
    simp only [fq6Node, ite_true]
    exact Iff.rfl
  natCast_toNat x hx := by
    change x ∈ fq6Node "GF(p^1)" at hx
    simp only [fq6Node, ite_true] at hx
    obtain ⟨z, rfl⟩ : x ∈ Set.range (algebraMap (ZMod 8380417) MLDSANativeField6) := by
      rw [GordieHowe.range_algebraMap_eq_fixedField]
      exact hx
    change (((mldsaNative6Coords (algebraMap (ZMod 8380417) MLDSANativeField6 z) 0).val : ℕ) :
      MLDSANativeField6) = _
    rw [mldsaNative6Coords_algebraMap, ← map_natCast (algebraMap (ZMod 8380417) MLDSANativeField6),
      ZMod.natCast_zmod_val]

open RealizedProgram (fq11 fq11Node) in
/-- `F_q^11` has domain `A`'s field data. -/
instance : MLDSA44.QField fq11 where
  charP := inferInstanceAs (CharP MLDSANativeField11 8380417)
  char_spec := rfl
  decode_eq _ := rfl
  coord0 :=
    { toFun := fun x => mldsaNative11Coords x 0
      map_zero' := mldsaNative11Coords_zero 0
      map_add' := fun x y => mldsaNative11Coords_add x y 0 }
  coord0_natCast := mldsaNative11Coords_natCast
  toNat_eq _ := rfl
  node_prime x := by
    change x ∈ fq11Node "GF(p^1)" ↔ _
    simp only [fq11Node, ite_true]
    exact Iff.rfl
  natCast_toNat x hx := by
    change x ∈ fq11Node "GF(p^1)" at hx
    simp only [fq11Node, ite_true] at hx
    obtain ⟨z, rfl⟩ : x ∈ Set.range (algebraMap (ZMod 8380417) MLDSANativeField11) := by
      rw [GordieHowe.range_algebraMap_eq_fixedField]
      exact hx
    change (((mldsaNative11Coords (algebraMap (ZMod 8380417) MLDSANativeField11 z) 0).val : ℕ) :
      MLDSANativeField11) = _
    rw [mldsaNative11Coords_algebraMap,
      ← map_natCast (algebraMap (ZMod 8380417) MLDSANativeField11), ZMod.natCast_zmod_val]

end GordieHowe.RealizedProgram
