-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Honest.Check
public import GordieHowe.Language.Completeness.Bound
public import GordieHowe.Language.RealizedProgram.StructureCheck
public import GordieHoweNative.Language.Honest.CheckValues

@[expose] public section

/-!
# GordieHowe: the honest strategy's value checks in one pass

The checks that range over the values (`RealizedProgram.allValuesB`, `boundNoCopyB`) look value
`v` up in the list, `v` steps, and so cost the square of the number of values. Each has a check here
that visits the values once (`allIdx`), reads the value it visits from the list, any other value
through the table `valueT` and any predicate through `predT`, with an `_iff` lemma to the check
that looks values up; the generated proof modules decide the one-pass check and transport it
through the lemma.

The value checks on value `v` (`cellV`, `realTypeV`, …) are those of
`GordieHowe/Language/Honest/Check.lean` with `ir.value v` the visited value `x`, each with its
equation.

A value bound to its digits names the lookup whose record it is in the structure records
(`Structure.boundRecs`, read through the table `Structure.boundRecTab`); `boundRecsVE` checks the
lookup at that pointer (`boundRecAtT`) and reports the value it refuses, and `boundRecsV` is its
verdict (`boundRecsV_sound`).

The definitions are in `GordieHoweNative/Language/Honest/CheckValues.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

section

variable (ir : RealizedProgram)

/-! ## Value and predicate readings -/

theorem isLateV_eq (v : ℕ) : ir.isLateV (ir.value v) = decide (ir.IsLate v) := by
  rw [Bool.eq_iff_iff, isLateV_iff, decide_eq_true_iff]

/-- **A check of every value in one pass is the check of every value.** -/
theorem allIdx_iff_all_range {P : ℕ → Value → Bool} {Q : ℕ → Bool}
    (h : ∀ v, P v (ir.value v) = Q v) :
    allIdx P ir.values 0 = true ↔ (List.range ir.values.length).all Q = true := by
  rw [allIdx_values_iff]
  simp [List.all_eq_true, h]

theorem isLateOf_eq (d v : ℕ) : ir.isLateOf d v = ir.lateOfV d (ir.value v) := by
  rw [lateOfV, isLateV_eq]
  rfl

/-- `noLateReadB v`, through the tables. -/
def noLateReadT (v : ℕ) : Bool :=
  (ir.readsT.getD v []).all fun r =>
    match r with
    | .late u => !(decide (u < ir.values.length) && ir.isLateV (ir.valueT u))
    | _ => true

theorem noLateReadT_eq (v : ℕ) : ir.noLateReadT v = ir.noLateReadB v := by
  rw [noLateReadT, noLateReadB_eq]
  congr 1
  funext r
  cases r <;> simp [valueT_eq, isLateV_eq]

/-! ## The values bound to their digits -/

theorem commOfT_eq (G : Gens) (r : LookupRealization) : commOfT (toTrie G) r = G.commOf? r := by
  unfold commOfT Gens.commOf?
  congr 1

theorem boundRecAtT_eq (G : Gens) (v pid : ℕ) :
    ir.boundRecAtT (toTrie G) v pid = ir.boundRecAtB G v pid := by
  simp only [boundRecAtT, boundRecAtB, predicateT_eq, valueT_eq, valueFieldT_eq, commOfT_eq]
  rfl

/-- **A bound value that passes `boundRecsV` is a source value and the record of a two-sided or
digit lookup** (`BoundRecs`): the entry's pointer witnesses it. -/
theorem boundRecsV_sound {G : Gens} {T : NatTrie ℕ} {v : ℕ}
    (h : ir.boundRecsV (toTrie G) T v (ir.value v) = true)
    (hb : (ir.value v).kind.isBound = true) :
    ir.IsSourceValue v ∧ ∃ pid < ir.predicates.length, ir.boundRecAtB G v pid = true := by
  unfold boundRecsV boundRecsVE at h
  rw [hb] at h
  simp only [Twin.okB_seqE, Twin.okB_guardE, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hs, h⟩ := h
  refine ⟨hs, ?_⟩
  split at h
  · rename_i pid _
    rw [Twin.okB_guardE, boundRecAtT_eq] at h
    exact ⟨pid, lt_of_boundRecAtB h, h⟩
  · cases h

/-! ## The value checks on a value -/

variable (L : List (ℕ × String))

/-- `typedNoLateB v`, on value `v`. -/
def typedNoLateV (v : ℕ) (x : Value) : Bool :=
  !(x.typeSource == .node) || ir.isLateV x || ir.noLateReadT v

theorem typedNoLateV_eq (v : ℕ) : ir.typedNoLateV v (ir.value v) = ir.typedNoLateB v := by
  simp only [typedNoLateV, typedNoLateB, isLateV_eq, noLateReadT_eq]

theorem srcNoPadCopyV_eq (v : ℕ) : srcNoPadCopyV v (ir.value v) = ir.srcNoPadCopyB v := rfl

theorem srcNoMessageV_eq (v : ℕ) : srcNoMessageV v (ir.value v) = ir.srcNoMessageB v := rfl

theorem srcLatePadV_eq (v : ℕ) : ir.srcLatePadV v (ir.value v) = ir.srcLatePadB v := by
  simp only [srcLatePadV, srcLatePadB, isLateV_eq]
  rfl

theorem cellV_eq (v : ℕ) : ir.cellV L v (ir.value v) = ir.cellB L v := rfl

theorem realTypeV_eq (v : ℕ) : ir.realTypeV L v (ir.value v) = ir.realTypeB L v := by
  simp only [realTypeV, realTypeB, isLateV_eq]
  rfl

/-! ## The value checks in one pass -/

variable {L}

theorem typedNoLateV_iff :
    allIdx ir.typedNoLateV ir.values 0 = true ↔ ir.allValuesB ir.typedNoLateB = true :=
  ir.allIdx_iff_all_range ir.typedNoLateV_eq

theorem boundNoCopyV_iff : allIdx ir.boundNoCopyV ir.values 0 = true ↔ ir.boundNoCopyB = true :=
  ir.allIdx_iff_all_range fun u => by
    simp only [boundNoCopyV, valueT_eq]
    rfl

end

end GordieHowe.RealizedProgram
