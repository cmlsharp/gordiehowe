-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Frontend.Fields
public import GordieHowe.Applications.Falcon512.Ring.Carrier.ROMParams.Interp
public import GordieHowe.Applications.Falcon512.Ring.Carrier.QROMParams.Interp
public import GordieHowe.Language.Realizations.Realize

@[expose] public section

/-!
# GordieHowe: the fields of the emulated Falcon programs

The ring carrier programs at the ROM and QROM parameters (`Falcon512.Ring.Carrier.ROMParams`,
`Falcon512.Ring.Carrier.QROMParams`, export `b65a4929`) emulate Falcon's arithmetic modulo `q` in
one domain `A` over a Goldilocks extension (Goldilocks² at the ROM parameters, Goldilocks⁴ at the
QROM parameters: `GordieHowe.RealizedProgram.gold2`, `GordieHowe.RealizedProgram.gold4`, which
decode a natural as its cast; every constant of these programs is below `p`). This file states the
field facts of such a domain (`Falcon512.EField`) and proves them for both fields.
-/

namespace GordieHowe

open RealizedProgram.Export

/-! ## The field facts of an emulated program's domain `A` -/

/-- **The field data and facts of an emulated Falcon program's domain `A`** (a Goldilocks
extension): characteristic `p = pGold`, the constant coordinate (additive, the integer reading its
value, a natural's cast's coordinate its cast), constants below `p` decode to their casts, and an
element of the node `GF(p^1)` is the cast of its integer reading. -/
class Falcon512.EField (FA : RealizedProgram.FieldInterp) where
  /-- The field has characteristic `p`. -/
  charP : CharP FA.K pGold
  /-- The registry's characteristic is `p`. -/
  spec_char : FA.spec.characteristic = pGold
  /-- The constant coordinate. -/
  coord0 : FA.K →+ ZMod pGold
  /-- The constant coordinate of a natural's cast is its cast. -/
  coord0_natCast : ∀ n : ℕ, coord0 (n : FA.K) = n
  /-- The integer reading is the constant coordinate's value. -/
  toNat_eq : ∀ x, FA.toNat x = (coord0 x).val
  /-- Constants below `p` decode to their casts. -/
  decode_lt : ∀ c < pGold, FA.decode c = (c : FA.K)
  /-- An element of the node `GF(p^1)` is the cast of its integer reading. -/
  natCast_toNat : ∀ x ∈ FA.node "GF(p^1)", ((FA.toNat x : ℕ) : FA.K) = x

attribute [instance] Falcon512.EField.charP

namespace Falcon512.EField

variable {FA : RealizedProgram.FieldInterp} [EField FA]

/-- **The integer reading inverts the casts below `p`.** -/
theorem toNat_natCast {k : ℕ} (hk : k < pGold) : FA.toNat (k : FA.K) = k := by
  rw [toNat_eq, coord0_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hk]

/-- **The prime field `F_p` in `FA`.** -/
noncomputable abbrev φp : ZMod pGold →+* FA.K := ZMod.castHom (dvd_refl pGold) _

theorem φp_apply (z : ZMod pGold) : (φp z : FA.K) = ((z.val : ℕ) : FA.K) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  exact map_natCast _ _

/-- **The constant coordinate is `F_p`-linear**: `coord0 (z · y) = z · coord0 y`. -/
theorem coord0_φp_mul (z : ZMod pGold) (y : FA.K) : coord0 (φp z * y) = z * coord0 y := by
  rw [φp_apply, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

end Falcon512.EField

instance (priority := 100) Falcon512.EField.toFalconAReading (FA : RealizedProgram.FieldInterp) [Falcon512.EField FA] :
    Falcon512.AReading FA :=
  ⟨fun hk => Falcon512.EField.toNat_natCast (lt_trans hk (by norm_num [pGold]))⟩

/-- **Goldilocks² as an emulated program's field**: the constant coordinate
`goldilocksExt2Coords x 0`. -/
instance : Falcon512.EField RealizedProgram.gold2 where
  charP := inferInstanceAs (CharP GoldilocksExt2 pGold)
  spec_char := rfl
  coord0 :=
    { toFun x := goldilocksExt2Coords x 0
      map_zero' := by
        have h := goldilocksExt2Coords_natCast 0
        rwa [Nat.cast_zero, Nat.cast_zero] at h
      map_add' x y := goldilocksExt2Coords_add x y 0 }
  coord0_natCast := goldilocksExt2Coords_natCast
  toNat_eq _ := rfl
  decode_lt _ _ := rfl
  natCast_toNat x hx :=
    RealizedProgram.gold2_model.natCast_toNat "GF(p^1)" (List.mem_singleton_self _) x hx

/-- **Goldilocks⁴ as an emulated program's field**: the constant coordinate
`goldilocksExt4Coords x 0`. -/
instance : Falcon512.EField RealizedProgram.gold4 where
  charP := inferInstanceAs (CharP GoldilocksExt4 pGold)
  spec_char := rfl
  coord0 :=
    { toFun x := goldilocksExt4Coords x 0
      map_zero' := by
        have h := goldilocksExt4Coords_natCast 0
        rwa [Nat.cast_zero, Nat.cast_zero] at h
      map_add' x y := goldilocksExt4Coords_add x y 0 }
  coord0_natCast := goldilocksExt4Coords_natCast
  toNat_eq _ := rfl
  decode_lt _ _ := rfl
  natCast_toNat x hx :=
    RealizedProgram.gold4_model.natCast_toNat "GF(p^1)" (List.mem_singleton_self _) x hx

end GordieHowe
