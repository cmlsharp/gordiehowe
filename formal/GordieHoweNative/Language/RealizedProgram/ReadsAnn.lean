-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Annotations

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.ReadsAnn`

The reads annotation (`ReadsAnn`), in the Mathlib-free library `GordieHoweNative`. The declarations keep their names; their
checks and lemmas are in `GordieHowe/Language/RealizedProgram/ReadsAnn.lean`, which imports this
module.
-/

@[expose] public section

namespace GordieHowe.RealizedProgram

/-- **The reads annotation**: per value, the codes of its reads. -/
structure ReadsAnn where
  /-- The values' reads, packed. -/
  reads : PackedLists

end GordieHowe.RealizedProgram
