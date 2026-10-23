-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.ConvMatrix

@[expose] public section

/-!
# The MAC profiles

The MAC's field `GF(2^w)` with its reduction taps (`../params/param_sets.h`,
`MACShape<w>`), shared by every configuration's MAC equality. The two concrete profiles (`w = 256`
and `w = 128`) are instances, in `GordieHowe/Applications/Shared/MACProfiles.lean`. A configuration's profile
extends it with the facts its own MAC needs (`FalconEmulated.Params.Profile`,
`GordieHowe.MLDSA44.Native.Params.Profile`).
-/

namespace GordieHowe

/-- **A MAC profile**: the MAC's width `w` (H's field is `GF(2^w)`), the taps of its reduction
polynomial `X^w + Σ_{d ∈ taps} X^d`, and the largest chunk row sum `convMax` of those taps
(`../params/param_sets.h`, `MACShape<w>`), with `convMax` the row sum
(`convMax_eq`). -/
structure MACProfile where
  /-- The MAC's width `w`. -/
  macWidth : ℕ
  /-- The taps of `GF(2^w)`'s reduction polynomial. -/
  macTaps : Finset ℕ
  /-- The MAC's largest chunk row sum (`operators.h:1054`, `mac_conv_max`). -/
  convMax : ℕ
  /-- `convMax` is the row sum of the taps. -/
  convMax_eq : Conv.convMax macWidth macTaps = convMax

end GordieHowe
