-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.KummerTrace
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative20
public import GordieHowe.Foundations.ToMathlib.RootsOfUnity

@[expose] public section

/-!
# The relative packing basis of `FalconNativeField20` over `F_12289`

The extension packing of domain A of the native Falcon arm packs `D = 20` coordinates of the prime
subfield `E = F_q`, `q = 12289`, into one element of the tower
`K = F_q[u]/(u^4 − 11)[v]/(v^5 − (u + 2))`: `ExtensionTraits<NativeWide<…, 20, …>>` has
`degree = 20`, `q = B::m_` (`lib/zk/zk_extension_packed.h:66-71`), so `φ(x) = x^q`, relative to the
prime field and not to the quartic step: the instance
`RelFrobeniusOrder FalconNativeField20 12289 1 20`. The basis is the coordinate basis
`beta[4j + i] = e[4j + i] = u^i v^j` (`:134-141`; `falconCoord`).

The trace dual is structural (`RelativeBasis.ofTower`), through the quartic subfield
`M = F_{q^4}`, the fixed field of `x ↦ x^(q^4)`:
* inner layer `K/M`: `v^(q^4) = η v` with `η = (u + 2)^((q^4 − 1)/5) ∈ M`, a primitive 5th root
  of unity (`falconU_add_two_pow_ne_one`);
* outer layer `M/E`: `u^q = ζ u` with `ζ = 11^((q − 1)/4) ∈ E`, a primitive 4th root of unity
  (`ζ^2 = 11^((q − 1)/2) = −1`);
so `Tr_{K/E}(e_k / e_l) = 20 δ_kl` and `dual_l = (20 e_l)⁻¹`.
-/

namespace GordieHowe

open Polynomial RelativePacking

instance : RelFrobeniusOrder FalconNativeField20 12289 1 20 :=
  .of_card (by rw [falconNativeField20_card, one_mul]) (by norm_num)

/-- The quartic field lies in the fixed field of `x ↦ x^(q^4)`. -/
theorem algebraMap_falconQuartic_mem_fixedField (a : FalconQuartic) :
    algebraMap FalconQuartic FalconNativeField20 a ∈ fixedField FalconNativeField20 12289 4 := by
  rw [mem_fixedField, phi_def, mul_one, ← map_pow, ← falconQuartic_card, FiniteField.pow_card]

theorem isPrimitiveRoot_eleven_pow_falconQ_sub_one_div_four :
    IsPrimitiveRoot ((11 : ZMod 12289) ^ ((12289 - 1) / 4)) 4 := by
  have : Fact (2 < 12289) := ⟨by norm_num⟩
  exact IsPrimitiveRoot.of_pow_two_pow_eq_neg_one (n := 1) ZMod.neg_one_ne_one
    (by rw [pow_one, ← pow_mul]; exact pow_eleven_falconQ_sub_one_div_two_eq_neg_one)

theorem isPrimitiveRoot_falconU_add_two_pow :
    IsPrimitiveRoot ((falconU + 2) ^ ((12289 ^ 4 - 1) / 5)) 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [IsPrimitiveRoot.iff_orderOf]
  refine orderOf_eq_prime ?_ falconU_add_two_pow_ne_one
  rw [← pow_mul, show (12289 ^ 4 - 1) / 5 * 5 = 12289 ^ 4 - 1 by norm_num, ← falconQuartic_card,
    FiniteField.pow_card_sub_one_eq_one _ falconU_add_two_ne_zero]

theorem falconUTower_ne_zero : falconUTower ≠ 0 := by
  intro h
  have h4 := falconUTower_pow_four
  rw [h, zero_pow (by norm_num)] at h4
  exact falconNativeField20_natCast_ne_zero (a := 11) (by norm_num) (by norm_num)
    (by rw [Nat.cast_ofNat]; exact h4.symm)

theorem falconV_ne_zero : falconV ≠ 0 := by
  intro h
  have h5 := falconV_pow_five
  rw [h, zero_pow (by norm_num)] at h5
  exact falconU_add_two_ne_zero ((_root_.map_eq_zero _).mp h5.symm)

/-- `u^q = 11^((q − 1)/4) · u`. -/
theorem phi_falconUTower :
    phi 12289 1 1 falconUTower = (11 : FalconNativeField20) ^ ((12289 - 1) / 4) * falconUTower :=
  phi_one_of_pow_eq falconUTower_pow_four (by norm_num)

/-- `v^(q^4) = (u + 2)^((q^4 − 1)/5) · v`. -/
theorem phi_falconV :
    phi 12289 4 1 falconV =
      algebraMap FalconQuartic FalconNativeField20 ((falconU + 2) ^ ((12289 ^ 4 - 1) / 5)) *
        falconV := by
  rw [map_pow]
  exact phi_one_of_pow_eq falconV_pow_five (by norm_num)

/-- The relative basis `beta[4j + i] = u^i v^j` of `FalconNativeField20` over `F_12289`, with
trace dual `(20 e_l)⁻¹`. -/
def falcon20RelativeBasis : RelativeBasis FalconNativeField20 12289 1 20 :=
  RelativeBasis.ofTower (D₁ := 4) (D₂ := 5) (by norm_num)
    (algebraMap_falconQuartic_mem_fixedField falconU)
    (by
      rw [← map_ofNat (algebraMap (ZMod 12289) FalconNativeField20)]
      exact pow_mem (algebraMap_mem_fixedField_one _) _)
    phi_falconUTower
    (by
      rw [← map_ofNat (algebraMap (ZMod 12289) FalconNativeField20), ← map_pow]
      exact isPrimitiveRoot_eleven_pow_falconQ_sub_one_div_four.map_of_injective
        injective_algebraMap_falconNativeField20)
    falconUTower_ne_zero
    (algebraMap_falconQuartic_mem_fixedField _)
    phi_falconV
    (isPrimitiveRoot_falconU_add_two_pow.map_of_injective
      (algebraMap FalconQuartic FalconNativeField20).injective)
    falconV_ne_zero
    (falconNativeField20_natCast_ne_zero (by norm_num) (by norm_num))

theorem falcon20RelativeBasis_β (k : Fin 20) : falcon20RelativeBasis.β k = falconCoord k := rfl

theorem falcon20RelativeBasis_dual (l : Fin 20) :
    falcon20RelativeBasis.dual l = (((20 : ℕ) : FalconNativeField20) * falconCoord l)⁻¹ := rfl

end GordieHowe
