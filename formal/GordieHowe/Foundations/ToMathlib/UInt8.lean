-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# Converting byte lists between `UInt8` and `ℕ`

The vendored verifiers take messages as `List UInt8`; the circuit specifications
read bytes as naturals below `256`. These lemmas say the two conversions are
inverse on that range. Candidates for upstreaming to core's `UInt8` API.
-/

/-- Reading bytes as naturals and back is the identity. -/
@[simp] theorem List.map_toUInt8_map_toNat (l : List UInt8) :
    (l.map UInt8.toNat).map Nat.toUInt8 = l := by
  simp [Function.comp_def, Nat.toUInt8_eq, UInt8.ofNat_toNat]

/-- Naturals below `256` survive the round trip through `UInt8`. -/
theorem List.map_toNat_map_toUInt8 {l : List ℕ} (h : ∀ b ∈ l, b < 256) :
    (l.map Nat.toUInt8).map UInt8.toNat = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  refine List.map_congr_left fun b hb => ?_
  simp [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (h b hb)]
