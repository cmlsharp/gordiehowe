-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Lowering
public import GordieHowe.Foundations.Algebra.IntLift
public import GordieHowe.Applications.Rows.MAC

@[expose] public section

/-!
# The MAC equality's agreement predicate

The cross-domain equality of a bit vector held in a binary domain `H` (`X_H`, in the field `KH`) and
in an odd-characteristic domain `A` (`X_A`, in the field `F`) is lowered to the MAC equality
(`lib/gordiehowe/compiler/mac.h`, `EqualityLoweringImpl::mac`, with domain A's part in `tail`). The
bits are read as `nch` chunks of `w` bits (the C++ reshapes `X_H` to `[nch][w]`, zero-extending the
last chunk).

This file states the conclusion of that equality (`BitsAgree`): the two chunk vectors are bits and
agree entry by entry. The MAC realization of a cross-field `equal` and its soundness are in
`GordieHowe/Language/Realizations/RealizeMac.lean`.
-/

namespace GordieHowe
open IOP RealizedProgram.ProofSystem.PhaseLayout Range
open scoped NNReal ENNReal

/-! ### The MAC equality -/

/-- **Two bit vectors agree across fields**: `x` (in `KH`) and `y` (in `F`), `nch` chunks of `w`
entries, are bits, and each entry of `x` is `1` exactly when the corresponding entry of `y` is. -/
structure BitsAgree {KH F : Type} [Field KH] [Field F] {nch w : ℕ} (x : Fin nch → Fin w → KH)
    (y : Fin nch → Fin w → F) : Prop where
  left : ∀ c j, x c j = 0 ∨ x c j = 1
  right : ∀ c j, y c j = 0 ∨ y c j = 1
  agree : ∀ c j, x c j = 1 ↔ y c j = 1

end GordieHowe
