-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Merkle.Tree
public import GordieHowe.Model.NARG.OracleProg

@[expose] public section

/-!
# Merkle trees as counted oracle programs

The node digests of a Merkle tree (`MerkleTree.nodeDigest`) and its leaf digests computed by
classical oracle programs over the domain-separated oracle, with their results and query counts:
`heapProg n ld` computes the heap of node digests from the leaf digests `ld` (one `node` query per
inner node), `leafProg a` the digest of one leaf (one `leaf` query), `treeHeapProg` both. The
compiled honest provers (`GordieHowe.SPBCS.niProver`) and the simulators run them, whatever the
opening format (`GordieHowe/SPBCS/Merkle/Opening.lean`).
-/

namespace GordieHowe.SPBCS
open GordieHowe.QROM

variable {k kN kS L e : ℕ}

namespace MerkleTree

variable {n : ℕ}

variable (h : Query k kN kS L → Out k e)

/-- **The tree over leaf digests depends on the leaf digests below `n` only**, at the heap
positions below `2n`. -/
theorem nodeDigest_congr_leaves {ld ld' : ℕ → Digest k} (hld : ∀ j < n, ld j = ld' j) :
    ∀ i, i < 2 * n → nodeDigest h n ld i = nodeDigest h n ld' i
  | i, hi => by
    by_cases hn : n ≤ i
    · rw [nodeDigest_leaf h ld hn, nodeDigest_leaf h ld' hn, hld _ (by omega)]
    · by_cases h0 : i = 0
      · subst h0
        rw [nodeDigest, dif_neg hn, dif_pos rfl, nodeDigest, dif_neg hn, dif_pos rfl]
      · rw [nodeDigest_node h ld (by omega) (by omega), nodeDigest_node h ld' (by omega) (by omega),
          nodeDigest_congr_leaves hld (2 * i) (by omega),
          nodeDigest_congr_leaves hld (2 * i + 1) (by omega)]
termination_by i => n - i
decreasing_by all_goals omega

/-- **The heap position `i` of an `n`-leaf tree is in the window** read by the verifier: a position
in `[1, 2n)`, or the root position `1`. -/
def InWindow (n i : ℕ) : Prop := 1 ≤ i ∧ i < 2 * n ∨ i = 1

theorem inWindow_iff {n i : ℕ} : InWindow n i ↔ 1 ≤ i ∧ i < 2 * n ∨ i = 1 := Iff.rfl

/-- The tree over leaf digests at the root position and the positions in `[1, 2n)`: it depends on
the leaf digests below `n`, and for `n = 0` on the digest at `1`. -/
theorem nodeDigest_congr_window {ld ld' : ℕ → Digest k} (hld : ∀ j < n, ld j = ld' j)
    (h1 : n = 0 → ld 1 = ld' 1) {i : ℕ} (hi : InWindow n i) :
    nodeDigest h n ld i = nodeDigest h n ld' i := by
  rw [inWindow_iff] at hi
  by_cases hin : i < 2 * n
  · exact nodeDigest_congr_leaves h hld i hin
  · obtain rfl : i = 1 := by omega
    obtain rfl : n = 0 := by omega
    rw [nodeDigest_leaf h ld (Nat.zero_le _), nodeDigest_leaf h ld' (Nat.zero_le _)]
    exact h1 rfl

/-- The heap loop: the positions `m, m - 1, …, 1` of the current heap `cur`, each set to the
digest of the `node` query on its children's current digests. -/
def heapLoop : ℕ → (ℕ → Digest k) → OracleProg (Query k kN kS L) (Out k e) (ℕ → Digest k)
  | 0, cur => .pure cur
  | m + 1, cur => .query (.node (cur (2 * (m + 1))) (cur (2 * (m + 1) + 1))) fun w =>
      heapLoop m (Function.update cur (m + 1) w.digest)

/-- **The heap program** of an `n`-leaf tree over the leaf digests `ld`: the heap with the leaf
digest `ld j` at the leaf position `n + j` and the all-zero digest at position `0`, then one
`node` query per inner position `n - 1, …, 1` in that order (the bottom-up loop of
`BasicMerkleTree`, `lib/merkle/merkle_tree.h` lines 111–126: `set_leaf`, `build_tree`). -/
def heapProg (n : ℕ) (ld : ℕ → Digest k) :
    OracleProg (Query k kN kS L) (Out k e) (ℕ → Digest k) :=
  heapLoop (n - 1) fun i => if n ≤ i then ld (i - n) else fun _ => 0

theorem length_trace_heapLoop : ∀ (m : ℕ) (cur : ℕ → Digest k),
    ((heapLoop m cur : OracleProg (Query k kN kS L) (Out k e) _).trace h).length = m
  | 0, _ => rfl
  | m + 1, cur => by
    simp [heapLoop, length_trace_heapLoop m]

/-- The heap program makes `n - 1` queries. -/
theorem length_trace_heapProg (n : ℕ) (ld : ℕ → Digest k) :
    ((heapProg n ld : OracleProg (Query k kN kS L) (Out k e) _).trace h).length = n - 1 :=
  length_trace_heapLoop h _ _

/-- The heap loop at positions `m, …, 1` completes a heap that is correct elsewhere. -/
theorem run_heapLoop (ld : ℕ → Digest k) : ∀ (m : ℕ) (cur : ℕ → Digest k), m < n ∨ m = 0 →
    (∀ i, (i = 0 ∨ m < i) → cur i = nodeDigest h n ld i) →
      (heapLoop m cur).run h = nodeDigest h n ld
  | 0, cur, _, hcur => funext fun i => hcur i (by omega)
  | m + 1, cur, hm, hcur => by
    have hm' : m + 1 < n := by omega
    rw [heapLoop, OracleProg.run_query]
    refine run_heapLoop ld m _ (by omega) fun i hi => ?_
    by_cases him : i = m + 1
    · subst him
      rw [Function.update_self, nodeDigest_node h ld hm' (by omega), hcur _ (by omega),
        hcur _ (by omega)]
    · rw [Function.update_of_ne him]
      exact hcur i (by omega)

/-- **The heap program computes the tree over the leaf digests** at every position. -/
theorem run_heapProg (n : ℕ) (ld : ℕ → Digest k) : (heapProg n ld).run h = nodeDigest h n ld := by
  refine run_heapLoop h ld _ _ (by omega) fun i hi => ?_
  by_cases hn : n ≤ i
  · rw [if_pos hn, nodeDigest_leaf h ld hn]
  · rw [if_neg hn, nodeDigest, dif_neg hn, dif_pos (by omega)]

/-- The leaf program: the `leaf` query of `(salt, column)`, returning its digest. -/
def leafProg (a : MerkleLeaf kN L) : OracleProg (Query k kN kS L) (Out k e) (Digest k) :=
  .query (.leaf a.salt a.column) fun w => .pure w.digest

theorem run_leafProg (a : MerkleLeaf kN L) : (leafProg a).run h = leafDigest h a := rfl

theorem length_trace_leafProg (a : MerkleLeaf kN L) :
    ((leafProg a : OracleProg (Query k kN kS L) (Out k e) _).trace h).length = 1 := rfl

/-- **The program of an honest tree**: the `leaf` queries of the leaves `lf j`, `j < n`, in order,
then the heap over their digests, with `dflt` read past the last leaf. -/
def treeHeapProg (n : ℕ) (lf : ℕ → MerkleLeaf kN L) (dflt : Digest k) :
    OracleProg (Query k kN kS L) (Out k e) (ℕ → Digest k) :=
  (OracleProg.tabulate (fun _ => dflt) (List.range n) fun j => leafProg (lf j)).bind (heapProg n)

theorem run_treeHeapProg (n : ℕ) (lf : ℕ → MerkleLeaf kN L) (dflt : Digest k) :
    (treeHeapProg n lf dflt).run h =
      nodeDigest h n fun j => if j < n then leafDigest h (lf j) else dflt := by
  simp only [treeHeapProg, OracleProg.run_bind, OracleProg.run_tabulate, run_heapProg,
    List.mem_range, run_leafProg]

/-- The program of an honest tree makes `n + (n - 1)` queries. -/
theorem length_trace_treeHeapProg (n : ℕ) (lf : ℕ → MerkleLeaf kN L) (dflt : Digest k) :
    ((treeHeapProg n lf dflt : OracleProg (Query k kN kS L) (Out k e) _).trace h).length =
      n + (n - 1) := by
  simp only [treeHeapProg, OracleProg.trace_bind, List.length_append,
    OracleProg.length_trace_tabulate, length_trace_leafProg, length_trace_heapProg]
  simp

end MerkleTree

end GordieHowe.SPBCS
