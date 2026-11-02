-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.NatTrie

@[expose] public section

/-!
# GordieHowe: a finite map on the naturals for kernel reduction

`NatTrie α` is a binary trie keyed by naturals: key `0` at the root, key `2m + 1` at key `m` of the
first subtrie and key `2m + 2` at key `m` of the second. A lookup or an update reads `O(log k)`
nodes, with `Nat` division and remainder, which the kernel evaluates on literals by GMP; a list
lookup `List.getD l k` reads `k` cells. The validity checkers of the plan's program
(`GordieHowe/Language/RealizedProgram/Check.lean`) keep their tables in it.

`NatTrie.set` recurses on a fuel argument (`k + 1`), not by well-founded recursion, so the kernel
reduces it.

The definitions are in `GordieHoweNative/Language/RealizedProgram/NatTrie.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

namespace NatTrie

variable {α : Type}

theorem getD_set (t : NatTrie α) (k j : Nat) (x d : α) :
    (t.set k x).getD j d = if j = k then x else t.getD j d := by
  simp only [getD, get?_set]
  split <;> rfl

end NatTrie

end GordieHowe.RealizedProgram
