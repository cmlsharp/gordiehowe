-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.KummerTrace
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative9

@[expose] public section

/-!
# The relative packing basis of `FalconNativeField9` over `F_12289`

The native Falcon field at the ROM parameters is `Fp14_9 = Fp14_N<9, 2>`
(`lib/params/param_sets.h`, `FalconNativeField9 = Fp14_9`; `lib/algebra/fp14_n.h:384`),
`K = F_q[X]/(X^9 − 2)`, `q = 12289`: `FalconNativeField9`. The extension packing of domain A packs
`D = 9` coordinates of the prime subfield `E = F_q` into one element of `K`:
`ExtensionTraits<Fp14_9>` has `degree = 9`, `q = 12289` (`lib/zk/zk_extension_packed.h:35-39`),
so `φ(x) = x^q`: the instance `RelFrobeniusOrder FalconNativeField9 12289 1 9`. `Fp14_9` is a
`Native` field (`:87-89`), whose generator is the coordinate `e[1] = X` (`:131-134`), so
`beta[i] = X^i` (`:139-146`), the coordinate basis.

`9 ∤ q − 1` (`q − 1 = 2^12 · 3`), so `X` is not an eigenvector of `φ`: `φ(X) = 2^1365 X^4`.
The trace dual is structural through the cubic subfield `M = F_{q^3}`, the fixed field of
`x ↦ x^(q^3)` (`RelativeBasis.ofTowerPow`):
* inner layer `K/M`: `X^(q^3) = η X` with `η = 2^((q^3 − 1)/9) ∈ E ⊆ M`, a primitive cube root
  of unity (`q^3 ≡ 1 mod 9`);
* outer layer `M/E`: `(X^3)^q = ζ X^3` with `ζ = 2^((q − 1)/3) ∈ E`, a primitive cube root of
  unity (`2` is a cubic non-residue, `pow_two_falconQ_sub_one_div_three_ne_one`);
so `Tr_{K/E}(X^i / X^j) = 9 δ_ij` and `dual_j = (9 X^j)⁻¹`.
-/

namespace GordieHowe

open Polynomial RelativePacking

instance : RelFrobeniusOrder FalconNativeField9 12289 1 9 :=
  .of_card (by rw [falconNativeField_card, one_mul]) (by norm_num)

/-- The generator `X`, `X^9 = 2`. -/
theorem root_falconNativePoly_pow_nine :
    falconNative9Gen ^ 9 = algebraMap (ZMod 12289) FalconNativeField9 2 :=
  falconNative9ToSpec.injective (by
    rw [map_pow, falconNative9ToSpec_gen, AlgEquiv.commutes, AdjoinRoot.algebraMap_eq]
    exact root_X_pow_sub_C_pow 9 (2 : ZMod 12289))

theorem powMod_two_falconQ_cube_sub_one_div_three :
    powMod 2 ((12289 ^ 3 - 1) / 3) 12289 = 1 := by
  decide +kernel

theorem powMod_two_falconQ_cube_sub_one_div_nine :
    powMod 2 ((12289 ^ 3 - 1) / 9) 12289 ≠ 1 := by
  decide +kernel

/-- `2^((q − 1)/3)` is a primitive cube root of unity mod `q`. -/
theorem isPrimitiveRoot_two_pow_falconQ_sub_one_div_three :
    IsPrimitiveRoot ((2 : ZMod 12289) ^ ((12289 - 1) / 3)) 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [IsPrimitiveRoot.iff_orderOf]
  refine orderOf_eq_prime ?_ pow_two_falconQ_sub_one_div_three_ne_one
  rw [← pow_mul, show (12289 - 1) / 3 * 3 = 12289 - 1 by norm_num,
    ZMod.pow_card_sub_one_eq_one (by decide)]

/-- `2^((q^3 − 1)/9)` is a primitive cube root of unity mod `q`. -/
theorem isPrimitiveRoot_two_pow_falconQ_cube_sub_one_div_nine :
    IsPrimitiveRoot ((2 : ZMod 12289) ^ ((12289 ^ 3 - 1) / 9)) 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [IsPrimitiveRoot.iff_orderOf]
  refine orderOf_eq_prime ?_ (powMod_ne_one_of_ne (by norm_num)
    powMod_two_falconQ_cube_sub_one_div_nine)
  rw [← pow_mul, show (12289 ^ 3 - 1) / 9 * 3 = (12289 ^ 3 - 1) / 3 by norm_num]
  exact powMod_eq_one_of_eq powMod_two_falconQ_cube_sub_one_div_three

/-- The relative basis `beta[i] = X^i` of `FalconNativeField9` over `F_12289`, with trace dual
`(9 X^j)⁻¹`. -/
def falconNativeRelativeBasis : RelativeBasis FalconNativeField9 12289 1 9 :=
  RelativeBasis.ofTowerPow (m₁ := 1) (D₁ := 3) (D₂ := 3) (m₂ := 3) (y := falconNative9Gen) (by norm_num)
    (ζ := algebraMap (ZMod 12289) FalconNativeField9 (2 ^ ((12289 - 1) / 3)))
    (η := algebraMap (ZMod 12289) FalconNativeField9 (2 ^ ((12289 ^ 3 - 1) / 9)))
    (algebraMap_mem_fixedField_one _)
    (by
      rw [map_pow]
      exact phi_one_of_pow_eq (n := 3) (t := (12289 - 1) / 3)
        ((pow_mul _ 3 3).symm.trans root_falconNativePoly_pow_nine) (by norm_num))
    (isPrimitiveRoot_two_pow_falconQ_sub_one_div_three.map_of_injective
        injective_algebraMap_falconNativeField)
    (mem_fixedField_mul (algebraMap_mem_fixedField_one _) 3)
    (by
      rw [map_pow]
      exact phi_one_of_pow_eq (n := 9) (t := (12289 ^ 3 - 1) / 9) root_falconNativePoly_pow_nine
        (by norm_num))
    (isPrimitiveRoot_two_pow_falconQ_cube_sub_one_div_nine.map_of_injective
        injective_algebraMap_falconNativeField)
    (fun h => by
      have h9 := root_falconNativePoly_pow_nine
      rw [h, zero_pow (by norm_num), eq_comm, _root_.map_eq_zero] at h9
      exact absurd h9 (by decide))
    (falconNativeField_natCast_ne_zero (by norm_num) (by norm_num))

theorem falconNativeRelativeBasis_β (i : Fin 9) :
    falconNativeRelativeBasis.β i = falconNative9Gen ^ (i : ℕ) := rfl

theorem falconNativeRelativeBasis_dual (j : Fin 9) :
    falconNativeRelativeBasis.dual j =
      (((9 : ℕ) : FalconNativeField9) * falconNative9Gen ^ (j : ℕ))⁻¹ := rfl

end GordieHowe
