-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHoweTest.GKRRelUnitLogupData

/-!
# The range LogUp record's leaf family cuts

The record's first 1024 family cuts (leaf denominators `α − needle`) are accepted.
-/

namespace GordieHoweTest.GKRRelUnit

open GordieHowe GordieHowe.Twin GordieHowe.RealizedProgram GordieHowe.GKR.Rel GordieHowe.GKR.Fold
open GordieHowe.Generated.Falcon512.Native.ROMParams.Program

/-- Accepted: its first 1024 family cuts (leaf denominators `α − needle`). -/
example : okB (famSliceE program 1 ar synthLogup 3 0 1024) = true := by decide +kernel

end GordieHoweTest.GKRRelUnit
