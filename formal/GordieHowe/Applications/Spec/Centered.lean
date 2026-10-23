-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import LatticeCrypto.Ring.Norms

@[expose] public section

/-!
# Elementary bounds for centered representatives

Facts here connect natural representatives to the vendored `LatticeCrypto.centeredRepr` used by the
scheme specifications.
-/

namespace GordieHowe.Centered

/-- Reducing a natural modulo `q` and choosing its centered representative cannot
increase its absolute value. This includes `q = 0`, where `ZMod 0 = ℤ`. -/
theorem natAbs_centeredRepr_natCast_le (q a : ℕ) :
    (LatticeCrypto.centeredRepr (a : ZMod q)).natAbs ≤ a := by
  rcases eq_zero_or_neZero q with rfl | hq
  · change Int.natAbs (Int.ofNat a) ≤ a
    exact le_rfl
  · rw [LatticeCrypto.centeredRepr_eq_valMinAbs, ZMod.valMinAbs_natAbs_eq_min,
      ZMod.val_natCast]
    exact (min_le_left _ _).trans (Nat.mod_le _ _)

end GordieHowe.Centered
