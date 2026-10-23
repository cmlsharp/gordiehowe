-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.KummerTrace
public import GordieHowe.Applications.MLDSA44.Native.Fields.MLDSANative6
public import GordieHowe.Foundations.ToMathlib.OrderOf

@[expose] public section

/-!
# The relative packing basis of `MLDSANativeField6` over `F_8380417`

At the ROM parameters, the native ML-DSA field is `Fp24_6` (`lib/params/param_sets.h`,
`MLDSANativeField6 = Fp24_6`), `K = F_q[X]/(X^6 − 7)`, `q = 8380417` (`lib/algebra/fp24_6.h:57-63`):
`MLDSANativeField6`. The extension packing of domain A packs `D = 6` coordinates of the prime
subfield `E = F_q` into one element of `K`: `ExtensionTraits<Fp24_6>` has `degree = 6`,
`q = 8380417` (`lib/zk/zk_extension_packed.h:30-34`), so `φ(x) = x^q`: the instance
`RelFrobeniusOrder MLDSANativeField6 8380417 1 6`. `Fp24_6` is a `Native` field (`:87-89`), whose
generator is the coordinate `e[1] = X` (`:131-134`), so `beta[i] = X^i` (`:139-146`), the
coordinate basis.

The trace dual is structural (`RelativeBasis.ofBinomialRoot`): `X^q = ζ X` with
`ζ = 7^((q − 1)/6)`, a primitive 6th root of unity in `F_q` (`7` is neither a square nor a cube),
so `Tr(X^i / X^j) = 6 δ_ij` and `dual_j = (6 X^j)⁻¹`.
-/

namespace GordieHowe

open Polynomial RelativePacking

instance : RelFrobeniusOrder MLDSANativeField6 8380417 1 6 :=
  .of_card (by rw [mldsaNativeField_card, one_mul]) (by norm_num)

/-- The generator `X`, `X^6 = 7`. -/
theorem root_mldsaNativePoly_pow_six :
    mldsaNative6Gen ^ 6 = algebraMap (ZMod 8380417) MLDSANativeField6 7 :=
  mldsaNative6ToSpec.injective (by
    rw [map_pow, mldsaNative6ToSpec_gen, AlgEquiv.commutes, AdjoinRoot.algebraMap_eq]
    exact root_X_pow_sub_C_pow 6 (7 : ZMod 8380417))

/-- `7^((q − 1)/6)` is a primitive 6th root of unity mod `q`: its cube is `7^((q − 1)/2) ≠ 1`
and its square is `7^((q − 1)/3) ≠ 1`. -/
theorem isPrimitiveRoot_seven_pow_mlDsaQ_sub_one_div_six :
    IsPrimitiveRoot ((7 : ZMod 8380417) ^ ((8380417 - 1) / 6)) 6 := by
  rw [IsPrimitiveRoot.iff_orderOf]
  refine orderOf_eq_prod_of_pow_ne_one (l := [2, 3]) (by norm_num) ?_ ?_
  · rw [← pow_mul, show (8380417 - 1) / 6 * [2, 3].prod = 8380417 - 1 by norm_num,
      ZMod.pow_card_sub_one_eq_one (by decide)]
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [← pow_mul, show (8380417 - 1) / 6 * ([2, 3].prod / 2) = (8380417 - 1) / 2 by norm_num]
      exact pow_seven_mlDsaQ_sub_one_div_two_ne_one
    · rw [← pow_mul, show (8380417 - 1) / 6 * ([2, 3].prod / 3) = (8380417 - 1) / 3 by norm_num]
      exact pow_seven_mlDsaQ_sub_one_div_three_ne_one

/-- The relative basis `beta[i] = X^i` of `MLDSANativeField6` over `F_8380417`, with trace
dual `(6 X^j)⁻¹`. -/
def mldsaNativeRelativeBasis : RelativeBasis MLDSANativeField6 8380417 1 6 :=
  .ofBinomialRoot (t := (8380417 - 1) / 6) root_mldsaNativePoly_pow_six
    (algebraMap_mem_fixedField_one _)
    ((_root_.map_ne_zero _).mpr (by decide))
    (by norm_num)
    (by
      rw [← map_pow]
      exact isPrimitiveRoot_seven_pow_mlDsaQ_sub_one_div_six.map_of_injective
        injective_algebraMap_mldsaNativeField)
    (mldsaNativeField_natCast_ne_zero (by norm_num) (by norm_num))

theorem mldsaNativeRelativeBasis_β (i : Fin 6) :
    mldsaNativeRelativeBasis.β i = mldsaNative6Gen ^ (i : ℕ) := rfl

theorem mldsaNativeRelativeBasis_dual (j : Fin 6) :
    mldsaNativeRelativeBasis.dual j =
      (((6 : ℕ) : MLDSANativeField6) * mldsaNative6Gen ^ (j : ℕ))⁻¹ := rfl

end GordieHowe
