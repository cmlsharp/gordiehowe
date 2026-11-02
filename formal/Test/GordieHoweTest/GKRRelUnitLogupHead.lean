-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHoweTest.GKRRelUnitLogupData

/-!
# The range LogUp record's head

The record's head and its value leaves are accepted; the head is rejected with its `α` pointer
naming the needles' node, with one inner node's kids swapped (a span), and with a needle pointer
past the circuit's table.
-/

namespace GordieHoweTest.GKRRelUnit

open GordieHowe GordieHowe.Twin GordieHowe.RealizedProgram GordieHowe.GKR.Rel GordieHowe.GKR.Fold
open GordieHowe.Generated.Falcon512.Native.ROMParams.Program

/-- Accepted: the LogUp entry's head (its guards, the tree's spans, its item `N − D·S`). -/
example : okB (entryHeadE program 1 ar synthLogup 3) = true := by decide +kernel

/-- Accepted: its three value leaves (the needles, `α`, the histogram). -/
example : okB (entryNodesE program 1 ar synthLogup 3 11 3) = true := by decide +kernel

/-- Rejected: the `α` pointer naming the needles' node. -/
example : okB (entryHeadE program 1 ar
    (mutFam synthLogup 3 (mutLogup fun lc => { lc with alpha := 11 })) 3) = false := by
  decide +kernel

/-- Rejected: one inner node's kids swapped, so its kids' spans are not adjacent. -/
example : okB (entryHeadE program 1 ar
    (mutFam synthLogup 3 (mutLogup fun lc => { lc with tree := swapKids 5 lc.tree })) 3)
      = false := by
  decide +kernel

/-- Rejected: a needle node read past the circuit's table (a mutated pointer). -/
example : okB (entryHeadE program 1 ar
    (mutFam synthLogup 3 (mutLogup fun lc => { lc with needles := [14] })) 3) = false := by
  decide +kernel

end GordieHoweTest.GKRRelUnit
