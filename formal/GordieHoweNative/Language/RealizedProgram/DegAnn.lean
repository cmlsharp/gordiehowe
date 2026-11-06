-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Std

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.DegAnn`

The degree annotation (`DegAnn`) and its packed tables, in the Mathlib-free library `GordieHoweNative`. The declarations keep their names; their
checks and lemmas are in `GordieHowe/Language/RealizedProgram/DegAnn.lean`, which imports this
module.
-/

@[expose] public section

namespace GordieHowe.RealizedProgram

/-! ## The annotation -/

/-- **A degree annotation in one challenge**: packed tables of `w`-bit bounds on the degrees of the
values' (`vals`) and the shared expressions' (`refs`) coordinates. -/
structure DegAnn where
  /-- The values' bounds. -/
  vals : Nat
  /-- The shared expressions' bounds. -/
  refs : Nat
  /-- The width of a bound. -/
  w : Nat
  deriving Repr, Inhabited

namespace DegAnn

/-- **Entry `i` of a packed table** of `w`-bit entries: bits `[w i, w (i + 1))` of `T`. -/
def entry (T w i : Nat) : Nat := (T >>> (w * i)) % 2 ^ w

/-- The bound of value `v`. -/
def val (a : DegAnn) (v : Nat) : Nat := entry a.vals a.w v

/-- The bound of shared expression `k` among `n` (past them, value `0`'s: what the default
expression `leaf 0` reads). -/
def ref (a : DegAnn) (n k : Nat) : Nat := if k < n then entry a.refs a.w k else a.val 0

end DegAnn

end GordieHowe.RealizedProgram
