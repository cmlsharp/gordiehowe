-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Honest.Check

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

/-- `isCellValue d v`, on value `v`. -/
def cellValueV (d : ℕ) (x : Value) : Bool :=
  x.domain == d &&
    match x.kind with
    | .priv => true
    | .padCopy _ _ => true
    | _ => false

/-- `isLateOf d v`, on value `v`. -/
def lateOfV (d : ℕ) (x : Value) : Bool := x.field.isNone && x.domain == d && ir.isLateV x

theorem isLateOf_eq (d v : ℕ) : ir.isLateOf d v = ir.lateOfV d (ir.value v) := by
  rw [lateOfV, isLateV_eq]
  rfl

/-- `padNatB L v`, on value `v`. -/
def padNatV (L : List (ℕ × String)) (x : Value) : Bool :=
  match x.padSpace with
  | .full => true
  | .node S => L.contains (ir.fieldOfV x, S)

/-- `natTypedInB L v`, on value `v`. -/
def natTypedV (L : List (ℕ × String)) (x : Value) : Bool :=
  match x.type with
  | .field => true
  | .sub E => L.contains (ir.fieldOfV x, E)
  | .bit => false

/-- `latePadTypeB v`, on value `v`. -/
def latePadTypeV (x : Value) : Bool :=
  match x.padSpace, x.type with
  | .full, _ => true
  | .node E', .sub E => E == E'
  | .node _, _ => false

/-- `cellNodeB v`, on value `v`. -/
def cellNodeV (x : Value) : Bool :=
  match x.node with
  | some nr => !decide (x.role = .source) || (x.type == .sub nr.name || x.type == .bit ||
      (x.type == .field && nr.name == (ir.field (ir.domainField x.domain)).name))
  | none => false

/-- `cellNodeInB L v`, on value `v`. -/
def cellNodeInV (L : List (ℕ × String)) (x : Value) : Bool :=
  match x.node with
  | some nr => L.contains (ir.domainField x.domain, nr.name)
  | none => false

/-- `privCellB v`, on value `v`. -/
def privCellV (v : ℕ) (x : Value) : Bool :=
  (match x.kind with
    | .priv => true
    | _ => false) &&
    decide (v < ir.values.length) && decide (x.domain < ir.domains.length) &&
    cellValueV x.domain x

/-- `noLateReadB v`, through the tables. -/
def noLateReadT (v : ℕ) : Bool :=
  (ir.readsT.getD v []).all fun r =>
    match r with
    | .late u => !(decide (u < ir.values.length) && ir.isLateV (ir.valueT u))
    | _ => true

theorem noLateReadT_eq (v : ℕ) : ir.noLateReadT v = ir.noLateReadB v := by
  unfold noLateReadT noLateReadB
  congr 1
  funext r
  cases r <;> simp [valueT_eq, isLateV_eq]

/-! ## The values bound to their digits -/

/-- `boundRecAtB v pid`, through the tables. -/
def boundRecAtT (v pid : ℕ) : Bool :=
  match (ir.predicateT pid).body with
  | .mem d [rec] (.range _) (.lookup r) =>
    (r.kind == .twoSided || r.kind == .digits) && (ir.commRecOf? pid).isNone &&
      ir.boundDigitsOk d rec r &&
      match rec with
      | .leaf u => u == v
      | .add (.leaf u) (.leaf c) =>
        u == v && match (ir.valueT c).kind with
          | .constant es => decide (es.length ≤ (ir.valueT v).size) &&
              es.all (· < ir.charOf (ir.valueFieldT c))
          | _ => false
      | _ => false
  | _ => false

/-- **The two-sided and digit `in`s with one record and a range**, by index. -/
def recLookups : List ℕ :=
  (List.range ir.predicates.length).filter fun pid =>
    match (ir.predicateT pid).body with
    | .mem _ [_] (.range _) (.lookup r) => r.kind == .twoSided || r.kind == .digits
    | _ => false

/-- `boundRecB v`, through the tables, searched among `recLookups`. -/
def boundRecT (v : ℕ) : Bool := ir.recLookups.any (ir.boundRecAtT v)

theorem boundRecT_eq (v : ℕ) : ir.boundRecT v = ir.boundRecB v := by
  unfold boundRecT recLookups
  rw [any_filter_eq]
  · unfold boundRecB
    congr 1
    funext pid
    simp only [boundRecAtT, boundRecAtB, predicateT_eq, valueT_eq, valueFieldT_eq]
    rfl
  intro pid _ hp
  unfold boundRecAtT
  split
  · rename_i d rec N r hb
    rw [hb] at hp
    simp [hp]
  · rfl

/-! ## The value checks on a value -/

variable (L : List (ℕ × String))

/-- `typedNoLateB v`, on value `v`. -/
def typedNoLateV (v : ℕ) (x : Value) : Bool :=
  !(x.typeSource == .node) || ir.isLateV x || ir.noLateReadT v

theorem typedNoLateV_eq (v : ℕ) : ir.typedNoLateV v (ir.value v) = ir.typedNoLateB v := by
  simp only [typedNoLateV, typedNoLateB, isLateV_eq, noLateReadT_eq]

/-- `srcNoPadCopyB v`, on value `v`. -/
def srcNoPadCopyV (_ : ℕ) (x : Value) : Bool := !decide (x.role = .source) || !x.kind.isPadCopy

theorem srcNoPadCopyV_eq (v : ℕ) : srcNoPadCopyV v (ir.value v) = ir.srcNoPadCopyB v := rfl

/-- `srcNoMessageB v`, on value `v`. -/
def srcNoMessageV (_ : ℕ) (x : Value) : Bool := !decide (x.role = .source) || !x.kind.isMessage

theorem srcNoMessageV_eq (v : ℕ) : srcNoMessageV v (ir.value v) = ir.srcNoMessageB v := rfl

/-- `srcLatePadB v`, on value `v`. -/
def srcLatePadV (_ : ℕ) (x : Value) : Bool :=
  !decide (x.role = .source) || !ir.isLateV x || latePadTypeV x

theorem srcLatePadV_eq (v : ℕ) : ir.srcLatePadV v (ir.value v) = ir.srcLatePadB v := by
  simp only [srcLatePadV, srcLatePadB, isLateV_eq]
  rfl

/-- `boundRecsB v`, on value `v`. -/
def boundRecsV (v : ℕ) (x : Value) : Bool :=
  !x.kind.isBound || (decide (x.role = .source) && ir.boundRecT v)

theorem boundRecsV_eq (v : ℕ) : ir.boundRecsV v (ir.value v) = ir.boundRecsB v := by
  simp only [boundRecsV, boundRecsB, boundRecT_eq]
  rfl

/-- `cellB L v`, on value `v`. -/
def cellV (_ : ℕ) (x : Value) : Bool :=
  !cellValueV x.domain x || (ir.cellNodeV x && ir.cellNodeInV L x)

theorem cellV_eq (v : ℕ) : ir.cellV L v (ir.value v) = ir.cellB L v := rfl

/-- `realTypeB L v`, on value `v`. -/
def realTypeV (v : ℕ) (x : Value) : Bool :=
  !(x.typeSource == .node) || ir.isLateV x || decide (x.role = .source) ||
    (ir.privCellV v x && ir.natTypedV L x)

theorem realTypeV_eq (v : ℕ) : ir.realTypeV L v (ir.value v) = ir.realTypeB L v := by
  simp only [realTypeV, realTypeB, isLateV_eq]
  rfl

/-- `boundNoCopyB`'s check at value `u`, on value `u`. -/
def boundNoCopyV (_ : ℕ) (x : Value) : Bool :=
  match x.kind with
  | .bound e => (ir.exprNodes e).all fun w =>
      match (ir.valueT w).kind with
      | .padCopy _ _ => false
      | _ => true
  | _ => true

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
