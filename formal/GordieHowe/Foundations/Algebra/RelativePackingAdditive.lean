-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.RelativePacking

@[expose] public section

/-!
# Relative packing: additivity of the trace and the coordinates

The relative trace `Tr_{K/E}` and the coordinates in a relative basis (`GordieHowe/Foundations/Algebra/RelativePacking.lean`)
are additive (`relTrace_add`, `coord_add`: the iterated Frobenius is additive, `phi_add`), and the
first coordinate of an element of `E` in a basis whose first element is `1` is the element itself
(`coord_zero_of_mem`). A word's bits, read through its first relative coordinate, are then an
additive function of the field (`GordieHowe/Applications/MLDSA44/Native/ROMParams/HashField.lean`).
-/

namespace GordieHowe.RelativePacking

variable {K : Type*} [Field K] {p m D : ℕ} [ExpChar K p]

/-- **The relative trace is additive.** -/
theorem relTrace_add (x y : K) : relTrace p m D (x + y) = relTrace p m D x + relTrace p m D y := by
  simp only [relTrace, phi_add, Finset.sum_add_distrib]

/-- **The relative coordinates are additive.** -/
theorem coord_add (B : RelativeBasis K p m D) (x y : K) (i : Fin D) :
    coord B (x + y) i = coord B x i + coord B y i := by
  simp only [coord, mul_add, relTrace_add]

/-- **The first coordinate of an element of `E` is the element**, when the basis's first element is
`1`: the element packed alone in the first coordinate (`coord_pack`). -/
theorem coord_zero_of_mem [NeZero D] (B : RelativeBasis K p m D) (hβ : B.β 0 = 1) {x : K}
    (hx : x ∈ fixedField K p m) : coord B x 0 = x := by
  have hpack : pack B (fun i => if i = 0 then x else 0) = x := by
    simp only [pack, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hβ, one_mul]
  have h := coord_pack B (c := fun i => if i = 0 then x else 0)
    (fun i => by split_ifs; exacts [hx, zero_mem _]) 0
  rwa [hpack, ite_eq_left_iff.mpr (fun h0 => absurd rfl h0)] at h

end GordieHowe.RelativePacking
