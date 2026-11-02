-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe.ProofSystem.Program.FieldInput

/-!
# The view-word coverage of a circuit's input layout

The input-layout check `GordieHowe.RealizedProgram.InputsT` requires the words every view block
reads to have a committed block in the circuit (`InputsT.coverView`,
`GordieHowe.RealizedProgram.viewWordsCommittedB`), which the proof system's premise on the bit views
(`InputPremises.views`) rests on. On a one-domain program with a committed word `w` and a bit view
`u` of it, the layout holding both is accepted, and layouts whose view block reads a word without a
committed block are rejected, by the coverage and by the whole check.
-/

namespace GordieHoweTest.CircuitInput

open GordieHowe GordieHowe.RealizedProgram

/-- A program with a committed `GF(2^16)` word `w` (value `0`), a bit view `u` of it (value `1`)
and a second committed word `y` (value `2`), whose one circuit has the input blocks `bs`. -/
def prog (bs : List InputBlock) : RealizedProgram where
  phases := 0
  fields := [{ name := "GF(2^16)", characteristic := 2, degree := 16 }]
  domains := [{ name := "A", field := 0 }]
  values := [{ name := "w", shape := [1], kind := .priv, type := .field },
    { name := "u", shape := [16], kind := .bits 0 [(0, 0, 1)], type := .bit },
    { name := "y", shape := [1], kind := .priv, type := .field }]
  predicates := []
  circuits := [{ name := "A", domain := 0, predicates := [], inputs := bs, inputCount := 18 }]

/-- The honest layout: `w` committed at input `1`, `u` viewed at inputs `2` to `17`. -/
def honest : List InputBlock := [.committed 0 1 1, .view 1 2 16]

/-- Accepted: the view block's word has a committed block. -/
example : ∀ b ∈ honest, (prog honest).viewWordsCommittedB 0 b = true := by decide

/-- Rejected: the word's committed block is missing (filler in its place). -/
example : (prog [.filler 1 1, .view 1 2 16]).viewWordsCommittedB 0 (.view 1 2 16) = false := by
  decide

/-- Rejected: the committed block holds another value. -/
example : (prog [.committed 2 1 1, .view 1 2 16]).viewWordsCommittedB 0 (.view 1 2 16) = false := by
  decide

/-- The honest layout passes the whole input-layout check (its conditions, `inputsT_iff`). -/
example : (prog honest).InputsT 0 0 := ((prog honest).inputsT_iff 0 0).2 (by decide +kernel)

/-- The layout without the word's committed block fails the input-layout check: every other
condition holds (the filler is plain and the circuit reads no value), so the view-word coverage
rejects it. -/
example : ¬ (prog [.filler 1 1, .view 1 2 16]).InputsT 0 0 := fun h =>
  absurd (h.coverView (.view 1 2 16) (by decide +kernel)) (by decide)

end GordieHoweTest.CircuitInput
