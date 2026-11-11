-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Completeness.Deriv
public import GordieHoweNative.Language.Completeness.Late

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Completeness.Honest`

The definitions of `GordieHowe.Language.Completeness.Honest` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Completeness/Honest.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export
section

variable {ir : RealizedProgram} {primeNodes : ℕ → List String} {S : Structure}

variable (ir primeNodes) in
/-- **A late member `m` of a mixed group at the late histogram `v` of table `t` reads a digit of the
tail of the MAC of site `st`** (`MixedGroupFactsC.members` at a site, with the generators read off
`G`), as a check: the site's MAC and interval facts check, and the needle is the lower or the top
digit of an ungrouped digit tail (`lateMemberAtB`, the top digit's bound `macTopMax` below the late
histogram's size) or the quotient of a one-digit tail (`lateMemberOneAtB`, its bound `macQuotMax`
below that size). -/
def mixedMemberCB (S : Structure) (G : Gens) (t v : ℕ) (st : MacSite) (m : Member) : Bool :=
  ir.macBaseCB primeNodes S G st && ir.macIvlB primeNodes S st &&
    ((ir.digitsMacCB G st && ir.lateMemberAtB st t v m &&
        decide (ir.macTopMax st < (ir.value v).size)) ||
      (ir.oneDigitMacCB G st && ir.lateMemberOneAtB st t m &&
        decide (ir.macQuotMax st < (ir.value v).size)))

end

end GordieHowe.RealizedProgram
