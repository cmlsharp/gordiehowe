-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.DFTExtra

@[expose] public section

/-!
# The negacyclic transform in natural order

The negacyclic transform of length `n` at a root `ψ` with `ψ ^ n = -1`, in natural order: entry `k`
is the evaluation of the polynomial `a` at `ψ ^ (2k + 1)` (`lib/gordiehowe/ops/operators.h`,
`NttOrder::kNatural`; `lib/gordiehowe/lib/table.h`, `RowMap::negacyclic`: "cell k is
a(psi^(2k + 1))"). It is the transform with root `ψ ^ 2` of the input twisted by the powers of `ψ`
(`negSpectrum_eq_dft`), so:

* it turns the negacyclic product into the pointwise product (`negSpectrum_negacyclicConvCoeff`);
* it is injective when `ψ` is a primitive `2n`-th root and `n` is invertible
  (`negSpectrum_injective`).

The frequency order plays no role in either fact; the C++ circuits compute the transform by staged
butterflies (`StagedNtt`), whose output is this specification.
-/

namespace GordieHowe.DFT

variable {F : Type*} [Field F] {n : ℕ}

/-- **The negacyclic transform in natural order**: `Σ_j a_j ψ^(j (2k + 1))`, the evaluation of
`a` at `ψ ^ (2k + 1)`. -/
def negSpectrum (ψ : F) (a : Fin n → F) (k : Fin n) : F :=
  ∑ j : Fin n, a j * ψ ^ ((j : ℕ) * (2 * k + 1))

/-- The transform is the transform with root `ψ ^ 2` of the twisted input. -/
theorem negSpectrum_eq_dft (ψ : F) (a : Fin n → F) : negSpectrum ψ a = dft (ψ ^ 2) (twist ψ a) := by
  funext k
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [twist, ← pow_mul, show (j : ℕ) * (2 * k + 1) = j + 2 * (j * k) by ring, pow_add]
  ring

/-- The transform is additive. -/
theorem negSpectrum_sub (ψ : F) (a b : Fin n → F) :
    negSpectrum ψ (a - b) = negSpectrum ψ a - negSpectrum ψ b := by
  funext k
  simp only [negSpectrum, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- Twisting by `ψ` undoes the untwisting by `ψ⁻¹`. -/
theorem twist_untwist {ψ : F} (hψ : ψ ≠ 0) (c : Fin n → F) :
    twist ψ (fun k : Fin n => ψ⁻¹ ^ (k : ℕ) * c k) = c := by
  funext k
  rw [twist, ← mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hψ), one_mul]

/-- **The transform of a negacyclic product is the pointwise product of the transforms**, for
`ψ ^ n = -1`. -/
theorem negSpectrum_negacyclicConvCoeff {ψ : F} (hψ : ψ ^ n = -1) (u v : Fin n → F) :
    negSpectrum ψ (LatticeCrypto.negacyclicConvCoeff u v) =
      negSpectrum ψ u * negSpectrum ψ v := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · funext k
    exact k.elim0
  have hψ0 : ψ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hψ
    exact absurd hψ.symm (neg_ne_zero.mpr one_ne_zero)
  have hω : (ψ ^ 2) ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hψ]; norm_num
  rw [negSpectrum_eq_dft, negSpectrum_eq_dft, negSpectrum_eq_dft,
    negacyclicConvCoeff_eq_untwist hψ, twist_untwist hψ0, dft_cyclicConv hω]

/-- **The transform is injective** at a primitive `2n`-th root `ψ` when `n` is invertible. -/
theorem negSpectrum_injective {ψ : F} (hψ : IsPrimitiveRoot ψ (2 * n)) (hn : (n : F) ≠ 0) :
    Function.Injective (negSpectrum (n := n) ψ) := by
  intro a b hab
  have hn0 : n ≠ 0 := fun h => hn (by rw [h, Nat.cast_zero])
  have hψ0 : ψ ≠ 0 := hψ.ne_zero (by omega)
  rw [negSpectrum_eq_dft, negSpectrum_eq_dft] at hab
  have htw := congrArg (idft (ψ ^ 2)) hab
  rw [idft_dft (IsPrimitiveRoot.sq_of_two_mul hψ hn0) hn,
    idft_dft (IsPrimitiveRoot.sq_of_two_mul hψ hn0) hn] at htw
  funext j
  have hj := congrFun htw j
  simp only [twist] at hj
  exact mul_left_cancel₀ (pow_ne_zero _ hψ0) hj

end GordieHowe.DFT
