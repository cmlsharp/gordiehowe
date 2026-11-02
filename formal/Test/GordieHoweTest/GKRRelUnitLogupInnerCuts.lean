-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHoweTest.GKRRelUnitLogupData

/-!
# The range LogUp record's inner family cuts

1024 family cuts among the record's inner nodes are accepted.
-/

namespace GordieHoweTest.GKRRelUnit

open GordieHowe GordieHowe.Twin GordieHowe.RealizedProgram GordieHowe.GKR.Rel GordieHowe.GKR.Fold
open GordieHowe.Generated.Falcon512.Native.ROMParams.Program

/-- Accepted: 1024 family cuts among the inner nodes. -/
example : okB (famSliceE program 1 ar synthLogup 3 6000 1024) = true := by decide +kernel

end GordieHoweTest.GKRRelUnit
