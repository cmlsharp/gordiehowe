-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.KummerTrace
public import GordieHowe.Foundations.Fields.GoldilocksQuartic
public import GordieHowe.Foundations.ToMathlib.RootsOfUnity

@[expose] public section

/-!
# The relative packing basis of `GoldilocksExt4` over `F_p`, `p = pGold`

The extension packing of domain A of the emulated arms packs `D = 4` coordinates of the prime
subfield `E = F_p` into one element of `K = F_p[X]/(X^4 − 7)`: `ExtensionTraits<Fp64G4>` has
`degree = 4`, `q = Fp64G::kP` (`lib/zk/zk_extension_packed.h:51-55`), so `φ(x) = x^p`: the
instance `RelFrobeniusOrder GoldilocksExt4 pGold 1 4`. The basis is `beta[i] = g^i`, `g = e[1] = X`
(`:126-141`), the coordinate basis `X^i`.

The trace dual is structural (`RelativeBasis.ofBinomialRoot`): `X^p = ζ X` with
`ζ = 7^((p − 1)/4)`, a primitive 4th root of unity (`ζ^2 = 7^((p − 1)/2) = −1`), so
`Tr(X^i / X^j) = 4 δ_ij` and `dual_j = (4 X^j)⁻¹`.
-/

namespace GordieHowe

open Polynomial RelativePacking

instance : RelFrobeniusOrder GoldilocksExt4 pGold 1 4 :=
  .of_card (by rw [goldilocksExt4_card, one_mul]) (by norm_num)

/-- The generator `X`, `X^4 = 7`. -/
theorem root_goldQuarticPoly_pow_four :
    goldilocksExt4Gen ^ 4 = algebraMap (ZMod pGold) GoldilocksExt4 7 :=
  goldilocksExt4ToSpec.injective (by
    rw [map_pow, goldilocksExt4ToSpec_gen, AlgEquiv.commutes, AdjoinRoot.algebraMap_eq]
    exact root_X_pow_sub_C_pow 4 (7 : ZMod pGold))

theorem pGold_sub_one_div_four_mul_two : (pGold - 1) / 4 * 2 = (pGold - 1) / 2 := by
  rw [pGold_eq]

theorem isPrimitiveRoot_seven_pow_pGold_sub_one_div_four :
    IsPrimitiveRoot ((7 : ZMod pGold) ^ ((pGold - 1) / 4)) 4 := by
  have : Fact (2 < pGold) := ⟨by rw [pGold_eq]; norm_num⟩
  exact IsPrimitiveRoot.of_pow_two_pow_eq_neg_one (n := 1) ZMod.neg_one_ne_one
    (by rw [pow_one, ← pow_mul, pGold_sub_one_div_four_mul_two,
      pow_7_pGold_sub_one_div_two_eq_neg_one])

/-- The relative basis `beta[i] = X^i` of `GoldilocksExt4` over `F_p`, with trace dual
`(4 X^j)⁻¹`. -/
def goldilocksExt4RelativeBasis : RelativeBasis GoldilocksExt4 pGold 1 4 :=
  .ofBinomialRoot (t := (pGold - 1) / 4) root_goldQuarticPoly_pow_four
    (algebraMap_mem_fixedField_one _)
    ((_root_.map_ne_zero _).mpr seven_ne_zero_pGold)
    (by rw [pow_one, pGold_eq])
    (by
      rw [← map_pow]
      exact isPrimitiveRoot_seven_pow_pGold_sub_one_div_four.map_of_injective
        injective_algebraMap_goldilocksExt4)
    (goldilocksExt4_natCast_ne_zero (by norm_num) (by rw [pGold_eq]; norm_num))

theorem goldilocksExt4RelativeBasis_β (i : Fin 4) :
    goldilocksExt4RelativeBasis.β i = goldilocksExt4Gen ^ (i : ℕ) := rfl

theorem goldilocksExt4RelativeBasis_dual (j : Fin 4) :
    goldilocksExt4RelativeBasis.dual j =
      (((4 : ℕ) : GoldilocksExt4) * goldilocksExt4Gen ^ (j : ℕ))⁻¹ := rfl

end GordieHowe
