-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Embed
public import GordieHowe.Applications.MLDSA44.HPreds

@[expose] public section

/-!
# GordieHowe frontend: what the ML-DSA embedding data give in general

Facts about a checked embedding's data (`GordieHowe.RealizedProgram.EmbedData`) that the ML-DSA
frontends read, stated over the data's lists: a program decides of its data only that the lists
have the stated shape, never where a particular identifier lands.

* **Challenges as a range**: when the data's challenge images are the consecutive identifiers from
  `c`, the renaming (`EmbedData.renamingAfter`) adds `c` to every challenge
  (`renamingAfter_chal_of_range`).
-/

namespace GordieHowe.MLDSA44

open RealizedProgram

/-- The largest entry of a nonempty range is its last. -/
theorem foldr_max_range' : ∀ (c n : ℕ), (List.range' c (n + 1)).foldr max 0 = c + n
  | c, 0 => by simp [List.range']
  | c, n + 1 => by
    rw [List.range'_succ, List.foldr_cons, foldr_max_range' (c + 1) n]
    omega

/-- **Challenges as a range**: when the data's challenge images are `c, c + 1, …, c + n`, the
renaming adds `c` to every challenge, past the list too. -/
theorem renamingAfter_chal_of_range {d : EmbedData} {c n : ℕ}
    (h : d.chals = List.range' c (n + 1)) (j : ℕ) : d.renamingAfter.chal j = j + c := by
  change (if j < d.chals.length then d.chals.getD j j
    else j - d.chals.length + (d.chals.foldr max 0 + 1)) = j + c
  rw [h, List.length_range', foldr_max_range']
  split
  · rename_i hj
    rw [List.getD_eq_getElem _ _ (by rw [List.length_range']; exact hj), List.getElem_range']
    omega
  · omega

end GordieHowe.MLDSA44
