-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Library.Eval
public import GordieHoweNative.Language.RealizedProgram.MemberValues
public import GordieHoweNative.Language.RealizedProgram.RealizationValid

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.RealizeLookup`

The definitions of `GordieHowe.Language.Realizations.RealizeLookup` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/RealizeLookup.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export
section

variable {ir : RealizedProgram}

variable {primeNodes : ℕ → List String} {L : ℕ → ℕ → Option Ivl}

variable (ir) in
/-- **A complement lookup's shape without the record's interval** (the record's interval left
out). -/
structure ComplementCore (pid d : ℕ) (recs : List Expr) (set : InSet) (r : LookupRealization) :
    Prop where
  table : r.table < ir.tables.length
  domain : d = (ir.table r.table).domain
  rangeTable : ir.IsRange r.table
  single : recs.length = 1
  range : set = .range set.bound
  pos : 0 < set.bound
  le : set.bound ≤ ir.tableSize r.table
  needle : r.needles.length = 1
  complement : ir.complementMatch d set.bound (recs.headD default) (r.needles.headD default) = true
  char : 2 < ir.charOf (ir.domainField d)
  refs : ∀ e ∈ r.needles, ∀ k ∈ e.refs, k < ir.exprs.length
  covered : ∀ n < r.needles.length,
    tiles (ir.coverRuns r.table pid n) 0 (ir.exprLen (r.needles.getD n default)) = true

theorem complementCore_iff (pid d : ℕ) (recs : List Expr) (set : InSet) (r : LookupRealization) :
    ir.ComplementCore pid d recs set r ↔
      r.table < ir.tables.length ∧ d = (ir.table r.table).domain ∧ ir.IsRange r.table ∧
        recs.length = 1 ∧ set = .range set.bound ∧ 0 < set.bound ∧
        set.bound ≤ ir.tableSize r.table ∧ r.needles.length = 1 ∧
        ir.complementMatch d set.bound (recs.headD default) (r.needles.headD default) = true ∧
        2 < ir.charOf (ir.domainField d) ∧ (∀ e ∈ r.needles, ∀ k ∈ e.refs, k < ir.exprs.length) ∧
        ∀ n < r.needles.length,
          tiles (ir.coverRuns r.table pid n) 0 (ir.exprLen (r.needles.getD n default)) = true :=
  ⟨fun h => ⟨h.table, h.domain, h.rangeTable, h.single, h.range, h.pos, h.le, h.needle,
      h.complement, h.char, h.refs, h.covered⟩,
    fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩⟩

instance (pid d : ℕ) (recs : List Expr) (set : InSet) (r : LookupRealization) :
    Decidable (ir.ComplementCore pid d recs set r) :=
  decidable_of_iff _ (complementCore_iff pid d recs set r).symm

end

end GordieHowe.RealizedProgram
