-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

/-!
# The Frobenius order of a field

`FrobeniusOrder K M` states that every element of `K` satisfies `y ^ (2 ^ M) = y`, with `M > 0`: the
`M`-fold iterate of `y ↦ y ^ 2` is the identity. For the finite field of `2 ^ M` elements, `M` is
its degree over `F₂` (`FrobeniusOrder.of_card`). It is a `field` fact about the type alone,
delivered as an instance, with `M` an output of the search. The relative Frobenius order derives
from it (`RelativePacking.RelFrobeniusOrder.of_frobeniusOrder`).
-/

namespace GordieHowe

/-- Every element of `K` is fixed by `y ↦ y ^ (2 ^ M)`, for a positive `M`. -/
class FrobeniusOrder (K : Type*) [Field K] (M : outParam ℕ) : Prop where
  pos : 0 < M
  pow_eq : ∀ y : K, y ^ (2 ^ M) = y

/-- A finite field of `2 ^ M` elements, `M > 0`, has Frobenius order `M`. -/
theorem FrobeniusOrder.of_card {K : Type*} [Field K] [Fintype K] {M : ℕ}
    (hcard : Fintype.card K = 2 ^ M) (hM : 0 < M) : FrobeniusOrder K M where
  pos := hM
  pow_eq y := by
    rw [← hcard]
    exact FiniteField.pow_card y

end GordieHowe
