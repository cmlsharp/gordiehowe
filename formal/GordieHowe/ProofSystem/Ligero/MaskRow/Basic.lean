-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.FieldProof.CommitProve

@[expose] public section

/-!
# The prefix cells of a packing tree's commitment

A GordieHowe domain commits its cells as `[prefix | root children's words | root own]`
(`lib/gordiehowe/compiler/tree_zk.h`, `TreeLayout`). The prefix holds every subfield-mask stage's masks, at
every depth of the tree ("Prefix: the root children's subfield masks first, then the others"), and
Ligero tests that every queried entry of the prefix rows lies in the designated subfield `S0`
(`lp_->commit(..., l.prefix_padded, ...)`). This file holds the data shared by the two maskings of
Ligero with the prefix-row test (`GordieHowe.Ligero.UntestedMask`, `GordieHowe.Ligero.MaskTest`):

* `PrefixCells`: the prefix cells and their subfield `E` (`S0`), with decidable membership (the
  verifier's test);
* `PrefixCells.In`: every prefix cell of a vector lies in `E`, the condition the test proves on the
  extracted cells (`CommitProve.SoundOn`);
* `PrefixCells.confineMap`: the extracted cells with every prefix cell outside `E` replaced by
  `0`, which confines the extraction to `In` (`confines`), so that a circuit proof reads its
  witness from cells whose prefix lies in `E` (`CommitProve.SoundOn.confine`).
-/

namespace GordieHowe.Ligero.MaskRow

/-- **The prefix cells of a commitment** (`tree_zk.h`, the prefix of `TreeLayout`): `np` cells and
the subfield `E` the prefix-row test checks, with decidable membership. -/
structure PrefixCells (K ι : Type) [Field K] (np : ℕ) where
  /-- The prefix cells. -/
  cell : Fin np → ι
  /-- The subfield of the test (`S0`). -/
  E : Subfield K
  /-- Membership in `E` is decidable (for a fixed field, the Frobenius test). -/
  [decE : DecidablePred (· ∈ E)]

attribute [instance] PrefixCells.decE

variable {K ι : Type} [Field K] {np : ℕ}

namespace PrefixCells

variable (P : PrefixCells K ι np)

/-- **Every prefix cell lies in `E`.** -/
def In (x : ι → K) : Prop := ∀ j, x (P.cell j) ∈ P.E

/-- **The confined cells**: every prefix cell outside `E` replaced by `0`, the others unchanged.

Running time: for each cell, a search over the `np` prefix cells and one membership test.
This running time is argued here, not proved in Lean. -/
def confineMap [DecidableEq ι] (x : ι → K) (i : ι) : K :=
  if (∃ j, P.cell j = i) ∧ x i ∉ P.E then 0 else x i

/-- **The confined cells satisfy `In`, and `confineMap` fixes the vectors satisfying `In`.** -/
theorem confines [DecidableEq ι] : FieldProof.CommitProve.Confines P.In P.confineMap where
  good x j := by
    unfold confineMap
    split_ifs with h
    · exact P.E.zero_mem
    · exact not_not.mp fun hx => h ⟨⟨j, rfl⟩, hx⟩
  fixes x hx := by
    funext i
    unfold confineMap
    split_ifs with h
    · obtain ⟨⟨j, rfl⟩, h'⟩ := h
      exact absurd (hx j) h'
    · rfl

end PrefixCells

end GordieHowe.Ligero.MaskRow
