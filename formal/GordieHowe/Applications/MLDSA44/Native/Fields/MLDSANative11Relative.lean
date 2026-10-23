-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.KummerTrace
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative11

@[expose] public section

/-!
# The relative packing basis of `MLDSANativeField11` over `F_8380417`

The extension packing of domain A of the native ML-DSA arm packs `D = 11` coordinates of the prime
subfield `E = F_q`, `q = 8380417`, into one element of `K = F_q[X]/(X^11 − 2)`:
`ExtensionTraits<NativeWide<…, 11, …>>` has `degree = 11`, `q = B::m_`
(`lib/zk/zk_extension_packed.h:66-71`), so `φ(x) = x^q`: the instance
`RelFrobeniusOrder MLDSANativeField11 8380417 1 11`. The basis is the coordinate basis
`beta[i] = e_i = X^i` (`:134-141`).

The trace dual is structural (`RelativeBasis.ofBinomialRoot`): `X^q = ζ X` with
`ζ = 2^((q − 1)/11) = 4690951`, a primitive 11th root of unity in `F_q`, so
`Tr(X^i / X^j) = 11 δ_ij` and `dual_j = (11 X^j)⁻¹`.
-/

namespace GordieHowe

open Polynomial RelativePacking

instance : RelFrobeniusOrder MLDSANativeField11 8380417 1 11 :=
  .of_card (by rw [mldsaNativeField11_card, one_mul]) (by norm_num)

/-- The generator `X`, `X^11 = 2`. -/
theorem root_mldsaNative11Poly_pow_eleven :
    mldsaNative11Gen ^ 11 = algebraMap (ZMod 8380417) MLDSANativeField11 2 :=
  mldsaNative11ToSpec.injective (by
    rw [map_pow, mldsaNative11ToSpec_gen, AlgEquiv.commutes, AdjoinRoot.algebraMap_eq]
    exact root_X_pow_sub_C_pow 11 (2 : ZMod 8380417))

theorem isPrimitiveRoot_two_pow_mlDsaQ_sub_one_div_eleven :
    IsPrimitiveRoot ((2 : ZMod 8380417) ^ ((8380417 - 1) / 11)) 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  rw [IsPrimitiveRoot.iff_orderOf]
  refine orderOf_eq_prime ?_ pow_two_mlDsaQ_sub_one_div_eleven_ne_one
  rw [← pow_mul, show (8380417 - 1) / 11 * 11 = 8380417 - 1 by norm_num,
    ZMod.pow_card_sub_one_eq_one (by decide)]

/-- The relative basis `beta[i] = X^i` of `MLDSANativeField11` over `F_8380417`, with trace
dual `(11 X^j)⁻¹`. -/
def mldsa11RelativeBasis : RelativeBasis MLDSANativeField11 8380417 1 11 :=
  .ofBinomialRoot (t := (8380417 - 1) / 11) root_mldsaNative11Poly_pow_eleven
    (algebraMap_mem_fixedField_one _)
    ((_root_.map_ne_zero _).mpr (by decide))
    (by norm_num)
    (by
      rw [← map_pow]
      exact isPrimitiveRoot_two_pow_mlDsaQ_sub_one_div_eleven.map_of_injective
        injective_algebraMap_mldsaNativeField11)
    (mldsaNativeField11_natCast_ne_zero (by norm_num) (by norm_num))

theorem mldsa11RelativeBasis_β (i : Fin 11) :
    mldsa11RelativeBasis.β i = mldsaNative11Gen ^ (i : ℕ) := rfl

theorem mldsa11RelativeBasis_dual (j : Fin 11) :
    mldsa11RelativeBasis.dual j =
      (((11 : ℕ) : MLDSANativeField11) * mldsaNative11Gen ^ (j : ℕ))⁻¹ := rfl

end GordieHowe
