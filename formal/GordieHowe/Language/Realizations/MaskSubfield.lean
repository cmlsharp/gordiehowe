-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Algebra.Field.Basic
public import GordieHowe.Foundations.Algebra.KummerTrace
public import GordieHowe.Foundations.Fields.PolyRep

@[expose] public section

/-!
# The masking subfield of a domain

The masking subfield `S` of a domain's field `F` (`subfield.h`, `domain_subfield`): an embedding
with a left inverse, through which the honest prover writes the naturals of its late messages.
Shared by the configurations whose late values are vectors over a subfield (Falcon emulated, both
ML-DSA configurations). Relative packing needs the masking subfield to be the packing subfield, the
fixed field of `x ↦ x^p`; for the prime field's `algebraMap` this is
`range_algebraMap_eq_fixedField`. A concrete masking subfield's left inverse reads the constant
coefficient of a `PolyRep` vector (`PolyRep.coordsEquiv_const_zero`).
-/

namespace GordieHowe

/-- **The constant coefficient of a constant vector** (`PolyRep.const c`, the representation of a
base-field element in a field built by `PolyRep.ops`) is `c`.

TODO(move): a fact about `PolyRep.const`; belongs in `GordieHowe/Foundations/Fields/PolyRep.lean`. -/
theorem PolyRep.coordsEquiv_const_zero {K : Type} [CommRing K] {n : ℕ} (hn : 0 < n) (c : K) :
    PolyRep.coordsEquiv (PolyRep.const c : Vector K n) ⟨0, hn⟩ = c := by
  simp [PolyRep.coordsEquiv, PolyRep.const]

end GordieHowe

namespace GordieHowe

variable {S F : Type} [Field S] [Field F]

/-- **The masking subfield of a domain's field `F`** (`subfield.h`, `domain_subfield`; for example
Goldilocks in Goldilocks⁴): an embedding of `S` into `F` with a left inverse, through which the
honest prover writes the naturals it sends. -/
structure MaskSubfield (S F : Type) [Field S] [Field F] where
  /-- The embedding. -/
  embed : S →+* F
  /-- A left inverse of the embedding. -/
  coord : F → S
  coord_embed : ∀ s, coord (embed s) = s

/-- The image of the prime field's `algebraMap` is the fixed field of `x ↦ x^p`
(`RelativePacking.fixedField_one_eq_range`). -/
theorem range_algebraMap_eq_fixedField (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    [Algebra (ZMod p) K] [ExpChar K p] :
    Set.range (algebraMap (ZMod p) K) = (RelativePacking.fixedField K p 1 : Set K) := by
  rw [RelativePacking.fixedField_one_eq_range]
  rfl

/-- **An element of the prime subfield is the cast of its coordinate** `c` onto `F_p`, for a
coordinate `c` that inverts the prime field's `algebraMap` (`range_algebraMap_eq_fixedField`). -/
theorem natCast_val_eq_of_mem_fixedField {p : ℕ} [Fact p.Prime] {K : Type} [Field K]
    [Algebra (ZMod p) K] [ExpChar K p] {c : K → ZMod p}
    (hc : ∀ z, c (algebraMap (ZMod p) K z) = z) {x : K}
    (hx : x ∈ RelativePacking.fixedField K p 1) : (((c x).val : ℕ) : K) = x := by
  obtain ⟨z, rfl⟩ : x ∈ Set.range (algebraMap (ZMod p) K) := by
    rw [range_algebraMap_eq_fixedField]
    exact hx
  rw [hc, ← map_natCast (algebraMap (ZMod p) K), ZMod.natCast_zmod_val]

end GordieHowe
