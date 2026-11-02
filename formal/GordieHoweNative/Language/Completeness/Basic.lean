-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Honest.Exec

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Completeness.Basic`

The definitions of `GordieHowe.Language.Completeness.Basic` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Completeness/Basic.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- **The generator of a value**, naming the program items it reads by id. -/
inductive Gen where
  /-- A value the semantics fixes, or that no generator computes: `0` where honest. -/
  | none
  /-- A value of the source program: the execution's. -/
  | source
  /-- Digit `j` of the record of the two-sided or digit lookup `p` (of `N − 1` minus it for the
  second set). -/
  | lookupDigit (p : ℕ) (second : Bool) (j : ℕ)
  /-- Digit `k` of the lookup `lk` of radix-`R` digit `j` of the honest quotient of `mod_q` `m`. -/
  | commDigit (m j lk k : ℕ)
  /-- The transformed value of convolution `c` of `RealizedProgram.convs`. -/
  | spec (c : ℕ)
  /-- The static histogram of group `g` of table `t`. -/
  | staticHist (t g : ℕ)
  /-- The tag of the MAC of cross-field `equal` `p`. -/
  | tag (p : ℕ)
  /-- The accumulators of the grouped `mod_q` `p`. -/
  | acc (p : ℕ)
  /-- The quotient digits of the grouped `mod_q` `p`. -/
  | quotDigit (p : ℕ)
  /-- The accumulator of the ungrouped digit-form `mod_q` `p`. -/
  | digitsAcc (p : ℕ)
  /-- Lower digit `j` of the ungrouped digit-form `mod_q` `p`. -/
  | lowDigit (p j : ℕ)
  /-- The late histogram of group `g` of table `t`. -/
  | lateHist (t g : ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- **The generators of a program's values**, aligned with the values. -/
abbrev Gens : Type := List Gen

/-- **The generator of value `v`** (`none` past the list): entry `v` of `G` (`Gens.at_eq_getD`),
read through its trie (`NatTrie.ofSeq`). -/
def Gens.at (G : Gens) (v : ℕ) : Gen := (NatTrie.ofSeq G).getD v .none

end GordieHowe.RealizedProgram
