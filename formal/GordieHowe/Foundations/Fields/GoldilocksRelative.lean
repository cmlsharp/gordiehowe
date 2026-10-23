-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.KummerTrace
public import GordieHowe.Foundations.Fields.GoldilocksRoots
public import GordieHowe.Foundations.ToMathlib.RootsOfUnity

@[expose] public section

/-!
# The relative packing basis of `GoldilocksExt2` over `F_p`, `p = pGold`

The emulated field at the ROM parameters is `Fp64G2` (`lib/params/param_sets.h`,
`EmulatedField = Fp64G2`), `K = F_p[X]/(X^2 − 7)` with elements `re + im · X`
(`lib/algebra/fp_goldilocks.h`: class `Fp64G2` line 218, `kProtocolFieldId` lines
224-225, `Elt` lines 235-238): `GoldilocksExt2`. The extension packing of domain A packs
`D = 2` coordinates of the prime subfield `E = F_p` into one element of `K`:
`ExtensionTraits<Fp64G2>` has `degree = 2`, `q = 0xffffffff00000001` (`lib/zk/zk_extension_packed.h:40-44`),
so `φ(x) = x^p`: the instance `RelFrobeniusOrder GoldilocksExt2 pGold 1 2`. The generator is
`generator.im = 1`, that is `X` (`:135-138`), and `beta = (1, X)` (`:139-146`).

The trace dual is structural (`RelativeBasis.ofBinomialRoot`): `X^p = ζ X` with
`ζ = 7^((p − 1)/2) = −1`, a primitive square root of unity, so `Tr(X^i / X^j) = 2 δ_ij` and
`dual_j = (2 X^j)⁻¹`.
-/

namespace GordieHowe

open Polynomial RelativePacking

instance : RelFrobeniusOrder GoldilocksExt2 pGold 1 2 :=
  .of_card (by rw [goldilocksExt2_card, one_mul]) (by norm_num)

/-- The generator `X`, `X^2 = 7`. -/
theorem root_goldQuadPoly_pow_two :
    goldilocksExt2Gen ^ 2 = algebraMap (ZMod pGold) GoldilocksExt2 7 :=
  goldilocksExt2ToSpec.injective (by
    rw [map_pow, goldilocksExt2ToSpec_gen, AlgEquiv.commutes, AdjoinRoot.algebraMap_eq]
    exact root_X_pow_sub_C_pow 2 (7 : ZMod pGold))

theorem isPrimitiveRoot_seven_pow_pGold_sub_one_div_two :
    IsPrimitiveRoot ((7 : ZMod pGold) ^ ((pGold - 1) / 2)) 2 := by
  have : Fact (2 < pGold) := ⟨by rw [pGold_eq]; norm_num⟩
  exact IsPrimitiveRoot.of_pow_two_pow_eq_neg_one (n := 0) ZMod.neg_one_ne_one
    (by rw [pow_zero, pow_one, pow_7_pGold_sub_one_div_two_eq_neg_one])

/-- The relative basis `beta = (1, X)` of `GoldilocksExt2` over `F_p`, with trace dual `(2 X^j)⁻¹`. -/
def goldilocksExt2RelativeBasis : RelativeBasis GoldilocksExt2 pGold 1 2 :=
  .ofBinomialRoot (t := (pGold - 1) / 2) root_goldQuadPoly_pow_two
    (algebraMap_mem_fixedField_one _)
    ((_root_.map_ne_zero _).mpr seven_ne_zero_pGold)
    (by rw [pow_one, pGold_eq])
    (by
      rw [← map_pow]
      exact isPrimitiveRoot_seven_pow_pGold_sub_one_div_two.map_of_injective
        injective_algebraMap_goldilocksExt2)
    (goldilocksExt2_natCast_ne_zero (by norm_num) (by rw [pGold_eq]; norm_num))

theorem goldilocksExt2RelativeBasis_β (i : Fin 2) :
    goldilocksExt2RelativeBasis.β i = goldilocksExt2Gen ^ (i : ℕ) := rfl

theorem goldilocksExt2RelativeBasis_dual (j : Fin 2) :
    goldilocksExt2RelativeBasis.dual j =
      (((2 : ℕ) : GoldilocksExt2) * goldilocksExt2Gen ^ (j : ℕ))⁻¹ := rfl

end GordieHowe
