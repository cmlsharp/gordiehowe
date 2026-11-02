-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHoweTest.GKRRelUnitData

/-!
# The relational check's difference check on a deep chain

A cut of node `4000` of a ladder DAG unfolds 3999 nodes in a row; it is accepted against the right
constant and rejected against a wrong one.
-/

namespace GordieHoweTest.GKRRelUnit

open GordieHowe GordieHowe.Twin GordieHowe.RealizedProgram GordieHowe.GKR.Rel GordieHowe.GKR.Fold
open GordieHowe.Generated.Falcon512.Native.ROMParams.Program

/-- A trie of the chunks `f k`, keys below `2 ^ d`. -/
def treeOf : ℕ → (ℕ → ℕ) → GKR.Certificate.NTree
  | 0, f => .leaf (f 0)
  | d + 1, f => .node (treeOf d fun k => f (2 * k)) (treeOf d fun k => f (2 * k + 1))

/-- A DAG of width `16` with inputs `0, 1` and nodes `i = 1 · [i − 1] + 1 · [0] · [0]` up to `4095`. -/
def ladderDag : GKR.Certificate.Dag :=
  ⟨treeOf 12 fun i => 4 + 2 ^ 16 * (1 + (i - 1) * 2 ^ 32 + 2 ^ 48), 2, 4096, [], []⟩

/-- A cut of node `4000` against `[1] + 3999`: the difference check unfolds 3999 nodes in a row, its
accumulators evaluated at every step, so the kernel nests no chain of pending merges. -/
example : cutOk 16 ladderDag synth.consts ar (Wire.node 4000) (.add (.wire 0 1 1) (.const 3999)) =
    true := by decide +kernel

/-- Rejected: the same cut against `[1] + 3998`. -/
example : cutOk 16 ladderDag synth.consts ar (Wire.node 4000) (.add (.wire 0 1 1) (.const 3998)) =
    false := by decide +kernel

end GordieHoweTest.GKRRelUnit
