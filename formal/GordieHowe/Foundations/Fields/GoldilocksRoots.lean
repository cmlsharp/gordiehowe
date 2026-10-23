-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Fields.Goldilocks
public import GordieHowe.Foundations.Algebra.PowMod
public import GordieHowe.Foundations.Algebra.PowModOrder
public import GordieHowe.Foundations.ToMathlib.RootsOfUnity

@[expose] public section

/-!
# The order of the Goldilocks `2^32`-th root of unity

`GoldilocksExt2 = ZMod pGold [X] / (X² − 7)` (`GordieHowe.pGold_prime`, `GordieHowe.goldQuadPoly_irreducible`,
instance `GordieHowe.instFactPrimePGold`). The flagship C++ builds every Goldilocks NTT from the
base field's `2^32`-th root of unity, squared down to the transform's own length.

The base root, `goldilocks_root_2_32()` at `lib/algebra/fp_goldilocks.h:486-489`:
```
inline Fp64G::Elt goldilocks_root_2_32() {
  const Fp64G& f = goldilocks_base();
  return f.powf(f.of_scalar(Fp64G2::kW), (Fp64G::kP - 1) >> 32);
}
```
`Fp64G2::kW = 7` (`lib/algebra/fp_goldilocks.h:265`, "generates `F_p^*`, so a non-residue"),
the same witness `GordieHowe.pGold_prime`'s Lucas certificate uses. `(kP − 1) >> 32 = (p − 1) / 2^32
= 2^32 − 1`: `p − 1 = 2^32 · 3 · 5 · 17 · 257 · 65537` (`GordieHowe.pGold_sub_one`), and `3 · 5 · 17 ·
257 · 65537` (the five Fermat primes `F₀, …, F₄`) is exactly `2^32 − 1`. So the stored
constant is `7 ^ (2^32 − 1)` (`goldRootStored` below). Claimed value
`1753635133440165772` (verified independently by direct modular exponentiation), order
`2^32`.

The order certificate reuses `GordieHowe.pow_7_pGold_sub_one_div_two_eq_neg_one`
(`(7 : ZMod pGold) ^ ((p − 1) / 2) = −1`, established while proving `GordieHowe.pGold_prime`):
`goldRootStored ^ (2^31)` is that same `(p − 1) / 2`-th power of `7`, since
`(2^32 − 1) · 2^31 = (p − 1) / 2` (`goldRootStored_pow_two_pow_31`), so no fresh `powMod`
certificate is needed. `goldilocksExt2_natCast_ne_zero`: a natural strictly between `0` and `p`
is nonzero in `GoldilocksExt2`.
-/

namespace GordieHowe

/-- `goldilocks_root_2_32()` (`lib/algebra/fp_goldilocks.h:486-489`): `7 ^ ((p − 1) / 2^32) =
7 ^ (2^32 − 1)`, since `(p − 1) / 2^32 = 2^32 − 1` (`GordieHowe.pGold_sub_one`). -/
def goldRootStored : ZMod pGold := (7 : ZMod pGold) ^ (2 ^ 32 - 1)

/-- `goldRootStored ^ (2^31) = -1`: `(2^32 − 1) * 2^31 = (p − 1) / 2` (`GordieHowe.pGold_sub_one`),
so this is `GordieHowe.pow_7_pGold_sub_one_div_two_eq_neg_one` after `pow_mul`, with no fresh
`powMod` certificate. -/
theorem goldRootStored_pow_two_pow_31 : goldRootStored ^ (2 ^ 31) = -1 := by
  unfold goldRootStored
  rw [← pow_mul, show (2 ^ 32 - 1) * 2 ^ 31 = (pGold - 1) / 2 by rw [pGold_sub_one]; norm_num]
  exact pow_7_pGold_sub_one_div_two_eq_neg_one

/-- `goldilocks_root_2_32` is a primitive `2^32`-th root of unity of `ZMod pGold` (claimed
order, `lib/algebra/fp_goldilocks.h:486-489`). -/
theorem isPrimitiveRoot_goldRootStored : IsPrimitiveRoot goldRootStored (2 ^ 32) := by
  have h32 : (2 : ℕ) ^ 32 = 2 ^ (31 + 1) := by norm_num
  rw [h32]
  exact IsPrimitiveRoot.of_pow_two_pow_eq_neg_one (by rw [pGold_eq]; decide)
    goldRootStored_pow_two_pow_31

/-- A natural strictly between `0` and `p` casts to a nonzero element of `GoldilocksExt2`
(`CharP GoldilocksExt2 pGold`, `GordieHowe.Foundations.Fields.Goldilocks`): needed at `256` and `512`, the flagship's
two transform lengths, wherever a row evaluator divides by a transform length. -/
theorem goldilocksExt2_natCast_ne_zero {a : ℕ} (ha : 0 < a) (hlt : a < pGold) : (a : GoldilocksExt2) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff GoldilocksExt2 pGold a]
  intro hdvd
  exact absurd (Nat.le_of_dvd ha hdvd) (not_le.mpr hlt)

end GordieHowe
