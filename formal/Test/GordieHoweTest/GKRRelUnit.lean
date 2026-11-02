-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHoweTest.GKRRelUnitData
import GordieHoweTest.GKRRelUnitLadder
import GordieHoweTest.GKRRelUnitLogupHead
import GordieHoweTest.GKRRelUnitLogupLeafCuts
import GordieHoweTest.GKRRelUnitLogupInnerCuts
import GordieHoweTest.GKRRelUnitH

/-!
# The relational check of a node table on synthetic tables

Synthetic node tables over the inputs of Falcon-512 native's circuit `1` (domain `A`, `F_q^9`), written
by a scratch generator as `.ghc` files (`GKRRelData/Synth*.ghc`) and loaded by `load_ghc`: each
core kind's cuts (`nodeCutsE`), each placement, a chain with aux, the field `mux`'s aux, and the
assertion pairs of a root are accepted by the relational check; a mutated wire, code, aux entry,
block index, pad block and assertion pair are rejected. Uncut nodes: an uncut chain interior
and an uncut `scale` under a `lin` are expanded by their parents, a cut node is read by two
parents, and an uncut product operand that is not a wire is rejected. A cut whose DAG node clones
its kid's terms is accepted, and rejected with a wrong coefficient in the clone.

Family records (`RelFamily.lean`): a range LogUp record for circuit `1`'s entry `3`
(`.logup 1 0`, 5120 needles), reconstructed by a scratch generator from the committed DAG with its
three value leaves appended (`GKRRelData/SynthLogup.ghc`), has its head, its nodes and its first
family slice accepted, and is rejected with its `α` pointer naming the needles' node or one inner
node's kids swapped (a span); RSA H's alignment entry is accepted with its filler block and
rejected with another block. MLDSA44 H's MAC H record (the C++ export) is accepted, and rejected
with its powers pointer naming the tag's node or one chunk's wire changed. Small fraction trees are
checked for their spans.

The tests are split over modules that build in parallel: the synthetic tables and shared
mutations (`GKRRelUnitData`, `GKRRelUnitLogupData`), the deep chain (`GKRRelUnitLadder`), the
LogUp record's head and its leaf and inner family cuts (`GKRRelUnitLogupHead`,
`GKRRelUnitLogupLeafCuts`, `GKRRelUnitLogupInnerCuts`), the exported H records (`GKRRelUnitH`), and
this module's node, root, trie, index-map and fraction-tree tests.
-/

namespace GordieHoweTest.GKRRelUnit

open GordieHowe GordieHowe.Twin GordieHowe.RealizedProgram GordieHowe.GKR.Rel GordieHowe.GKR.Fold
open GordieHowe.Generated.Falcon512.Native.ROMParams.Program

/-- Accepted: the committed leaf (node 0). -/
example : okB (entryNodesE program 1 ar synth 0 0 1) = true := by decide +kernel

/-- Accepted: the public leaf (node 1). -/
example : okB (entryNodesE program 1 ar synth 0 1 1) = true := by decide +kernel

/-- Accepted: the late leaf (node 2). -/
example : okB (entryNodesE program 1 ar synth 0 2 1) = true := by decide +kernel

/-- Accepted: the uncut chain interior (node 3): it has no cuts of its own. -/
example : okB (entryNodesE program 1 ar synth 0 3 1) = true := by decide +kernel

/-- Accepted: the product chain with one aux (node 4). -/
example : okB (entryNodesE program 1 ar synth 0 4 1) = true := by decide +kernel

/-- Accepted: the sum chain (node 5). -/
example : okB (entryNodesE program 1 ar synth 0 5 1) = true := by decide +kernel

/-- Accepted: the odd `xor` (node 6). -/
example : okB (entryNodesE program 1 ar synth 0 6 1) = true := by decide +kernel

/-- Accepted: the `or` (node 7). -/
example : okB (entryNodesE program 1 ar synth 0 7 1) = true := by decide +kernel

/-- Accepted: the Bit `mux` (node 8). -/
example : okB (entryNodesE program 1 ar synth 0 8 1) = true := by decide +kernel

/-- Accepted: the scale (node 9). -/
example : okB (entryNodesE program 1 ar synth 0 9 1) = true := by decide +kernel

/-- Accepted: the `sum` (node 10). -/
example : okB (entryNodesE program 1 ar synth 0 10 1) = true := by decide +kernel

/-- Accepted: `materialize` (node 11). -/
example : okB (entryNodesE program 1 ar synth 0 11 1) = true := by decide +kernel

/-- Accepted: `lnot` (node 12). -/
example : okB (entryNodesE program 1 ar synth 0 12 1) = true := by decide +kernel

/-- Accepted: the field `mux` (node 13). -/
example : okB (entryNodesE program 1 ar synth 0 13 1) = true := by decide +kernel

/-- Accepted: a constant (node 14). -/
example : okB (entryNodesE program 1 ar synth 0 14 1) = true := by decide +kernel

/-- Accepted: `lin` of two terms (node 15). -/
example : okB (entryNodesE program 1 ar synth 0 15 1) = true := by decide +kernel

/-- Accepted: `lin` with a named `sum` (node 16). -/
example : okB (entryNodesE program 1 ar synth 0 16 1) = true := by decide +kernel

/-- Accepted: `apply` of `fromDigits` (node 17). -/
example : okB (entryNodesE program 1 ar synth 0 17 1) = true := by decide +kernel

/-- Accepted: an uncut `scale` (node 18): it has no cuts of its own. -/
example : okB (entryNodesE program 1 ar synth 0 18 1) = true := by decide +kernel

/-- Accepted: a `lin` over the uncut `scale` (node 19), which it expands. -/
example : okB (entryNodesE program 1 ar synth 0 19 1) = true := by decide +kernel

/-- Accepted: a cut `scale` (node 20) and its two parents (nodes 21 and 22). -/
example : okB (entryNodesE program 1 ar synth 0 20 3) = true := by decide +kernel

/-- Rejected: a product over an uncut `lin` of two wires (node 29). -/
example : okB (entryNodesE program 1 ar synthUncutOp 0 29 1) = false := by decide +kernel

/-- Accepted: a cut `scale` (node 24) whose wire's DAG node reads the inputs, not the chain's wire
node: the difference check unfolds the chain's node. -/
example : okB (entryNodesE program 1 ar synth 0 24 1) = true := by decide +kernel

/-- Accepted: a cut `scale 2` (node 27) of a cut `lin` whose wire's DAG node clones the kid's terms,
scaled, with no wire node of the kid on the DAG side. -/
example : okB (entryNodesE program 1 ar synth 0 27 1) = true := by decide +kernel

/-- Rejected: the same cut with a wrong coefficient inside the clone. -/
example : okB (entryNodesE program 1 ar synthClone 0 27 1) = false := by decide +kernel

/-- Accepted in stop mode: a cut `materialize` (node 25) whose wires are copies of the chain's
wire nodes, and a cut `scale` (node 26) of it whose wire's DAG node reads the copied node: the
copy reads as the node it copies. -/
example : okB (entryNodesE program 1 ar synth 0 25 2) = true := by decide +kernel

/-- Accepted: a cut `scale` (node 23) of the cut add chain (node 5): its wire's DAG node reads the
chain's wire node, where the expansion stops. -/
example : okB (entryNodesE program 1 ar synth 0 23 1) = true := by decide +kernel

/-- Accepted: the root's assertion pairs. -/
example : okB (relOkE synth.w synth.dag synth.consts ar []
    (rootItems synth 4 [⟨28314, 28298⟩, ⟨28315, 28299⟩])) = true := by decide +kernel

/-- Rejected: a `lin` node with a mutated wire coefficient. -/
example : okB (entryNodesE program 1 ar synthWire 0 15 1) = false := by decide +kernel

/-- Rejected: a scale with a mutated code. -/
example : okB (entryNodesE program 1 ar synthCode 0 9 1) = false := by decide +kernel

/-- Rejected: a product chain with a mutated aux wire. -/
example : okB (entryNodesE program 1 ar synthAux 0 4 1) = false := by decide +kernel

/-- Rejected: a field `mux` with a mutated difference wire. -/
example : okB (entryNodesE program 1 ar synthMuxAux 0 13 1) = false := by decide +kernel

/-- Rejected: a leaf naming another value's block. -/
example : okB (entryNodesE program 1 ar synthBlock 0 0 1) = false := by decide +kernel

/-- Rejected: a late leaf naming another pad block. -/
example : okB (entryNodesE program 1 ar synthLate 0 2 1) = false := by decide +kernel

/-- Rejected: an assertion pair naming the root's node as its asserted node. -/
example : okB (relOkE synthAssert.w synthAssert.dag synthAssert.consts ar []
    (rootItems synthAssert 4 [⟨28298, 28298⟩, ⟨28315, 28299⟩])) = false := by decide +kernel

/-- The trie of linear atoms: 2000 atoms added out of order, the largest comes out first. -/
example : (match KTrie.insertAll ar .nil
    ((List.range 2000).map fun i => ⟨0, (i * 7919) % 2000 + 1, 1⟩) with
    | some t => (KTrie.popMax t).map (·.1)
    | none => none) = some 2000 := by decide +kernel

/-- An index map read along a path in one pass: increasing entries through two runs, and an entry
before the current run (the path turning back) read directly. -/
example : IndexMap.entriesAt [(5, 1, 3), (20, 2, 2)] [0, 1, 2, 3, 4, 1, 9] =
    [0, 1, 2, 3, 4, 1, 9].map (IndexMap.entry [(5, 1, 3), (20, 2, 2)]) := by decide +kernel

example : IndexMap.entriesAt [(5, 1, 3), (20, 2, 2)] [0, 1, 2, 3, 4, 1] = [5, 6, 7, 20, 22, 6] := by
  decide +kernel

/-- A tree of three leaves, `((0, 1), 2)`: well formed. -/
example : FracTree.okB ⟨[default, default, default], [⟨0, 1, default, default⟩,
    ⟨3, 2, default, default⟩]⟩ = true := by decide +kernel

/-- Rejected: `((0, 2), 1)`, the first inner node's kids not adjacent. -/
example : FracTree.okB ⟨[default, default, default], [⟨0, 2, default, default⟩,
    ⟨3, 1, default, default⟩]⟩ = false := by decide +kernel

/-- Rejected: a root that spans only two of the three leaves. -/
example : FracTree.okB ⟨[default, default, default], [⟨0, 1, default, default⟩]⟩ = false := by
  decide +kernel

/-- Rejected: an inner node reading itself. -/
example : FracTree.okB ⟨[default, default], [⟨2, 1, default, default⟩]⟩ = false := by
  decide +kernel

end GordieHoweTest.GKRRelUnit
