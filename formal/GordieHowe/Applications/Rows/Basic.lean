-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Linear rows

A linear constraint on the committed witness is a pair of an `F`-linear
functional on the witness type and a constant.  Ligero checks every row of a
list against the commitment; the soundness statement of that check is the
proof-system layer's business, and this file only fixes the type.

The witness type is any `F`-module.  Structured witnesses are products of
function types, so the module instances come from Mathlib and projections are
`LinearMap.fst`, `LinearMap.snd` and `LinearMap.proj`.
-/

namespace GordieHowe

/-- A linear row: functional and constant. -/
abbrev Row (F Wit : Type*) [Field F] [AddCommGroup Wit] [Module F Wit] := (Wit →ₗ[F] F) × F

variable {F Wit : Type*} [Field F] [AddCommGroup Wit] [Module F Wit]

/-- The row `f W = c`. -/
def Row.holds (r : Row F Wit) (W : Wit) : Prop := r.1 W = r.2

/-- Every row of the family holds on `W`. -/
def rowsHold {m : ℕ} (L : Fin m → Row F Wit) (W : Wit) : Prop := ∀ r, (L r).holds W

end GordieHowe
