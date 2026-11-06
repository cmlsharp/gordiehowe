-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Semantics
public import GordieHowe.Foundations.Algebra.RelativePacking

@[expose] public section

/-!
# Field interpretations read through their prime field

A frontend reads a field of characteristic `p` through two lists of facts, stated once here for
every family and every `p`:

* **the casts** (`PrimeCastField F p`): the field has characteristic `p`, also as its registry entry
  states it; a constant below `p` decodes to its cast; the integer reading takes the cast of a
  natural below `p` back to the natural;
* **the constant coordinate** (`PrimeCoordField F p`, for a field of prime characteristic): an
  additive map `coord0` onto `ZMod p` that takes a natural's cast to its cast and whose value is the
  integer reading; the node `GF(p^1)` is the prime subfield, on which the cast of the integer
  reading is the element.

Both are discharged once per field, next to the field's definition or its configuration.
-/

namespace GordieHowe.RealizedProgram

open RelativePacking

/-- **The cast facts of a field of characteristic `p`** (module docstring). -/
class PrimeCastField (F : FieldInterp) (p : ℕ) : Prop where
  /-- The field has characteristic `p`. -/
  charP : CharP F.K p
  /-- The registry entry's characteristic is `p`. -/
  char_spec : F.spec.characteristic = p
  /-- Constants below `p` decode to their casts. -/
  decode_lt : ∀ c < p, F.decode c = (c : F.K)
  /-- The integer reading takes the cast of a natural below `p` back to the natural. -/
  toNat_natCast : ∀ k < p, F.toNat (k : F.K) = k

attribute [instance] PrimeCastField.charP

/-- **The integer reading of a natural below `p`** is the natural. -/
theorem PrimeCastField.toNat_natCast_lt {F : FieldInterp} {p : ℕ} [PrimeCastField F p] {k : ℕ}
    (hk : k < p) : F.toNat (k : F.K) = k :=
  PrimeCastField.toNat_natCast k hk

/-- **The constant coordinate of a field of prime characteristic `p`** (module docstring). -/
class PrimeCoordField (F : FieldInterp) (p : ℕ) [Fact p.Prime] extends PrimeCastField F p where
  /-- The constant coordinate. -/
  coord0 : F.K →+ ZMod p
  /-- The constant coordinate of a natural's cast is its cast. -/
  coord0_natCast : ∀ n : ℕ, coord0 (n : F.K) = n
  /-- The integer reading is the value of the constant coordinate. -/
  toNat_eq : ∀ x, F.toNat x = (coord0 x).val
  /-- The node `GF(p^1)` is the prime subfield. -/
  node_prime : ∀ x, x ∈ F.node "GF(p^1)" ↔ x ∈ fixedField F.K p 1
  /-- On the prime subfield, the cast of the integer reading is the element. -/
  natCast_toNat : ∀ x ∈ F.node "GF(p^1)", ((F.toNat x : ℕ) : F.K) = x

/-- **The integer reading of a natural below `p`** from the constant coordinate, the cast fact a
`PrimeCoordField` instance supplies for its parent. -/
theorem PrimeCoordField.toNat_natCast_of {F : FieldInterp} {p : ℕ} [NeZero p] (c : F.K →+ ZMod p)
    (hc : ∀ n : ℕ, c (n : F.K) = n) (ht : ∀ x, F.toNat x = (c x).val) {k : ℕ} (hk : k < p) :
    F.toNat (k : F.K) = k := by
  rw [ht, hc, ZMod.val_natCast, Nat.mod_eq_of_lt hk]

end GordieHowe.RealizedProgram
