-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Completeness.Bound

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Completeness.Committed`

The definitions of `GordieHowe.Language.Completeness.Committed` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Completeness/Committed.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable {ir : RealizedProgram} {primeNodes : ℕ → List String} {S : Structure}

variable (ir) in
/-- **The facts of group `g` of table `t` with the static histogram `h`** at the
certificate's generators `G`: a committed cell of the table's size in the field of the table's challenge,
no source value, generated as the group's static histogram; the needles and the rows read no
challenge and no late value, and no value they read is a static histogram or a pad copy; a table
packed at a value has its members packed alike. -/
structure StaticGroupFactsC (G : Gens) (t g h : ℕ) : Prop where
  /-- A committed cell. -/
  cell : ir.privCellB h = true
  /-- The table's size. -/
  size : (ir.value h).size = ir.tableSize t
  /-- The field of the table's challenge. -/
  field : ir.valueField h = ir.chalField (ir.alphaOf t)
  /-- No source value. -/
  notSource : ¬ ir.IsSourceValue h
  /-- Generated as the group's static histogram. -/
  own : G.at h = .staticHist t g
  /-- The needles read no challenge, no late value, no static histogram and no pad copy. -/
  needles : ∀ m ∈ ir.staticMembers t g, ∀ w ∈ ir.histNodes t m,
    (ir.readsT.getD w []).isEmpty = true ∧
      ∀ u ∈ ir.valReads ir.fuel w, (∀ t' g', G.at u ≠ .staticHist t' g') ∧
        (ir.value u).kind.isPadCopy = false
  /-- The rows read no challenge, no late value, no static histogram and no pad copy. -/
  rows : ∀ w ∈ ir.histRowNodes t, (ir.readsT.getD w []).isEmpty = true ∧
    ∀ u ∈ ir.valReads ir.fuel w, (∀ t' g', G.at u ≠ .staticHist t' g') ∧
      (ir.value u).kind.isPadCopy = false
  /-- A table packed at a value has its members packed alike. -/
  packed : ir.packGroupB t g = true

end

end GordieHowe.RealizedProgram
