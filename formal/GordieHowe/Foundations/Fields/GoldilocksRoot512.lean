-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Fields.Goldilocks
public import GordieHowe.Foundations.Algebra.PowMod
public import GordieHowe.Foundations.Algebra.PowModOrder
public import GordieHowe.Foundations.ToMathlib.RootsOfUnity

@[expose] public section

/-!
# The Goldilocks primitive `512`-th root of unity of the length-`256` negacyclic transform

The ML-DSA ring carriers (`lib/gordiehowe/examples/rings/mldsa_ring_carrier.h`, `carrier_ntt`)
transform polynomials of `ℤ_q[X]/(X^256 + 1)` lifted to the integers by the negacyclic transform
of length `256` over a Goldilocks extension, at the root `ψ = 1803076106186727246`
(`ops::FieldNtt<AF>::root(f, 512)`; the programs print it in `ConvForm.ntt`). This file proves
the root's order in every field of characteristic `p = 2^64 − 2^32 + 1`:

* `psi512_pow_zmod`, `psi512_pow`: `ψ^256 = −1` (one `powMod` value);
* `psi512_isPrimitiveRoot`: `ψ` is a primitive `512`-th root of unity;
* `natCast_256_ne_zero`: the transform length `256` is invertible.
-/

namespace GordieHowe

/-- **The Goldilocks root of the length-`256` negacyclic transform** (`1803076106186727246`). -/
abbrev psi512 : ℕ := 1803076106186727246

/-- `ψ ^ 256 = −1` modulo `p` (one `powMod` value). -/
theorem psi512_pow_zmod : (psi512 : ZMod pGold) ^ 2 ^ 8 = -1 :=
  powMod_eq_neg_one_of_eq (by norm_num [pGold]) (by decide)

section Root

variable {K : Type*} [Field K] [CharP K pGold]

/-- `ψ ^ 256 = −1` in every field of characteristic `p`. -/
theorem psi512_pow : (psi512 : K) ^ 256 = -1 := by
  have h := congrArg (ZMod.castHom (dvd_refl pGold) K) psi512_pow_zmod
  rw [map_pow, map_natCast, map_neg, map_one] at h
  simpa using h

/-- `ψ` is a primitive `512`-th root of unity in every field of characteristic `p`. -/
theorem psi512_isPrimitiveRoot : IsPrimitiveRoot (psi512 : K) (2 * 256) := by
  have h1 : (-1 : K) ≠ 1 := by
    intro h
    have h2 : ((2 : ℕ) : K) = 0 := by
      push_cast
      linear_combination -h
    rw [CharP.cast_eq_zero_iff K pGold] at h2
    norm_num [pGold] at h2
  have := IsPrimitiveRoot.of_pow_two_pow_eq_neg_one (n := 8) h1 (by simpa using psi512_pow (K := K))
  simpa using this

/-- `256` is nonzero in every field of characteristic `p`. -/
theorem natCast_256_ne_zero : ((256 : ℕ) : K) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff K pGold]
  norm_num [pGold]

end Root

end GordieHowe
