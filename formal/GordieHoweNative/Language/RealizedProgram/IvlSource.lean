-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.IvlSource`

The definitions of `GordieHowe.Language.RealizedProgram.IvlSource` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/RealizedProgram/IvlSource.lean`, which imports this module.
-/

@[expose] public section

namespace GordieHowe.RealizedProgram

/-- **The source of a value's interval**: the rule, with the predicates or the entry it reads, that
justifies the interval (`RealizedProgram.ivlAt`). -/
inductive IvlSource where
  /-- A constant: its centred entries. -/
  | const
  /-- An opaque value of type `Bit` computed from arguments: `[0, 1]`. -/
  | opaqueBit
  /-- Entry `k` of the value ranges: the value with its bound `N`, `[0, N − 1]`. -/
  | declared (k : Nat)
  /-- A bound value: the `in` on it or on it plus a constant of predicate `q`, read centred. -/
  | shiftRange (q : Nat)
  /-- The direct or digit `in` `v ∈ [0, N)` of predicate `q`: `[0, N − 1]`. -/
  | range (q : Nat)
  /-- The quadratic root equation of predicate `q`, its `m` with the interval of the `in` of
  predicate `r` (`shiftRange r`): `[0, c]`. -/
  | quadRoot (q r : Nat)
  /-- The root-set equations of the predicates `qs`, covering every coordinate: the hull of their
  intervals. -/
  | rootSet (qs : List Nat)
  /-- A prime-subfield read: `[0, 1]` for `Bit`, else `[0, p − 1]`. -/
  | prime
  deriving Repr, DecidableEq, Inhabited

/-- **The sources a value of kind `k` takes**: a constant only its entries; an opaque value
computed from arguments its `Bit` type or a value range; an opaque statement value with no arguments
a value range, a range or a prime-subfield read; a bound value an `in` read centred; any other
value a root equation, a range or a prime-subfield read. -/
def IvlSource.allows : Kind → IvlSource → Bool
  | .constant _, .const => true
  | .constant _, _ => false
  | .pub (.opaque _ (_ :: _)), .opaqueBit => true
  | .pub (.opaque _ (_ :: _)), .declared _ => true
  | .pub (.opaque _ (_ :: _)), _ => false
  | .pub (.opaque _ []), .declared _ => true
  | .pub (.opaque _ []), .range _ => true
  | .pub (.opaque _ []), .prime => true
  | .pub (.opaque _ []), _ => false
  | .bound _, .shiftRange _ => true
  | .bound _, _ => false
  | _, .quadRoot _ _ => true
  | _, .rootSet _ => true
  | _, .range _ => true
  | _, .prime => true
  | _, _ => false

end GordieHowe.RealizedProgram
