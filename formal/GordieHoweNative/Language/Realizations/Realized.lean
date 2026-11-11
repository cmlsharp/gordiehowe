-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Protocol

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.Realized`

The definitions of `GordieHowe.Language.Realizations.Realized` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/Realized.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export
/-- **A member of a table group's LogUp sum**: `(pred, needle, first, count)`, the coordinates
`[first, first + count)` of needle `needle` (an index into the `in` predicate's needles) of the `in`
predicate `pred` (`TableGroup.members`). -/
abbrev Member : Type := ℕ × ℕ × ℕ × ℕ

namespace Member

/-- The `in` predicate of a member. -/
def pred (m : Member) : ℕ := m.1

/-- The needle of a member, an index into its predicate's needles. -/
def needle (m : Member) : ℕ := m.2.1

/-- The first coordinate of a member. -/
def first (m : Member) : ℕ := m.2.2.1

/-- The number of coordinates of a member. -/
def count (m : Member) : ℕ := m.2.2.2

end Member

section

variable (ir : RealizedProgram)

/-- **The lookup realization of a predicate body**: an `in` realized by lookups. -/
def lookupOf? : PredBody → Option LookupRealization
  | .mem _ _ _ (.lookup r) => some r
  | _ => none

/-- **Needle `n` of predicate `p`**, an expression of its lookup realization (a default expression
when `p` has none). -/
def needleExpr (p n : ℕ) : Expr :=
  ((lookupOf? (ir.predicate p).body).map fun r => r.needles.getD n default).getD default

/-- **The size `T` of table `t`**: the range `[0, T)`, the size of a committed table's first
column (the one a single-record `in` reads, `RealizedProgram.InRows`), or the length of the expression whose
coordinates are the rows. -/
def tableSize (t : ℕ) : ℕ :=
  match (ir.table t).rows with
  | .range T => T
  | .columns cols => (ir.value (cols.headD 0)).size
  | .expr e' => ir.exprLen e'

/-- **The challenge `α` of table `t`.** -/
def alphaOf (t : ℕ) : ℕ := (ir.table t).alpha

/-- **Group `g` of table `t`.** -/
def groupOf (t g : ℕ) : TableGroup := (ir.table t).groups.getD g default

/-- **The members of group `g` of table `t`**, in the order its LogUp sum reads them. -/
def members (t g : ℕ) : List Member := (ir.groupOf t g).members

/-- **The number of needles of group `g` of table `t`**: the coordinates of its members. -/
def groupCount (t g : ℕ) : ℕ := ((ir.members t g).map Member.count).sum

/-- **The number of groups of table `t`.** -/
def groupCountOf (t : ℕ) : ℕ := (ir.table t).groups.length

/-- **The largest table challenge `j` avoids**: `tmax` for the sampler `fieldMinusTables (range
tmax)`, `0` otherwise. -/
def tmaxOf (j : ℕ) : ℕ :=
  match (ir.challenge j).sampler with
  | .fieldMinusTables (.range T) => T
  | _ => 0

/-- Whether a predicate body is a field `equal`. -/
def _root_.GordieHowe.RealizedProgram.PredBody.isEqual : PredBody → Bool
  | .equal _ _ _ _ => true
  | _ => false


end

/-- Whether a predicate body is a `mod_0` (an integer equality). -/
def _root_.GordieHowe.RealizedProgram.PredBody.isIntEq : PredBody → Bool
  | .mod _ 0 _ _ _ => true
  | _ => false

/-- **Whether a predicate body is a `mod_q` in the field form**: `isFieldForm` at a predicate read
from a walk of the predicates (`isFieldForm_eq`). -/
def PredBody.isFieldForm : PredBody → Bool
  | .mod _ _ _ _ real => real.form == .field
  | _ => false

end GordieHowe.RealizedProgram
