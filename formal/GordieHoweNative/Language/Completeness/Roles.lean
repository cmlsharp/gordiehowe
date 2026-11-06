-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Honest.Exec
public import GordieHoweNative.Language.Honest.Packed
public import GordieHoweNative.Language.Honest.Source
public import GordieHoweNative.Language.RealizedProgram.Reader

/-!
# GordieHowe: the compiled honest roles' check

The honest roles' check (`GordieHowe.RealizedProgram.honestRolesB`,
`GordieHowe/Language/Completeness/Roles.lean`) reads the program's values and predicates by index,
which compiled code reads by a walk of their lists. Here it is written against a program reader
(`PReader`), each check in generic form; at the kernel's reader (`PReader.ofProgram`) it is the
kernel checker by definition, and compiled code runs it at the program's context built once
(`honestRolesBC`, the code of `honestRolesB` by `honestRolesB_csimp`, in
`GordieHowe/Language/Completeness/Roles.lean`), whose arrays it reads.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

namespace PReader

variable (ir : RealizedProgram) [r : PReader]

/-- `isCellValue`, at the reader. -/
def isCellValue (d v : ℕ) : Bool :=
  (r.value v).domain == d &&
    match (r.value v).kind with
    | .priv => true
    | .padCopy _ _ => true
    | _ => false

/-- `privCellB`, at the reader. -/
def privCellB (v : ℕ) : Bool :=
  (match (r.value v).kind with
    | .priv => true
    | _ => false) &&
    decide (v < r.nValues) && decide ((r.value v).domain < ir.domains.length) &&
    isCellValue (r.value v).domain v

/-- `privBitsB`, at the reader. -/
def privBitsB (v : ℕ) : Bool :=
  (match (r.value v).kind with
    | .bits w _ =>
      match (r.value w).kind with
      | .priv => true
      | _ => false
    | _ => false) && (r.value v).type == .bit

/-- `cellTypeB`, at the reader. -/
def cellTypeB (v : ℕ) : Bool :=
  match (r.value v).type with
  | .sub E => (r.value v).node.map (·.name) == some E
  | .bit => (r.value v).node.isSome
  | .field => true

/-- `typedClassB`, at the reader. -/
def typedClassB (v : ℕ) : Bool :=
  !((r.value v).typeSource == .node) || decide (PReader.IsLate ir v) || privBitsB v ||
    (privCellB ir v && cellTypeB v)

/-- `valueField`, at the reader. -/
def valueField (v : ℕ) : ℕ :=
  match (r.value v).kind.allowsField, (r.value v).field with
  | true, some f => f
  | _, _ => ir.domainField (r.value v).domain

/-- `natTypedInB`, at the reader. -/
def natTypedInB (L : List (ℕ × String)) (v : ℕ) : Bool :=
  match (r.value v).type with
  | .field => true
  | .sub E => L.contains (valueField ir v, E)
  | .bit => false

/-- `valueRolesB`, at the reader. -/
def valueRolesB (L : List (ℕ × String)) (v : ℕ) : Bool :=
  typedClassB ir v && (!decide (PReader.IsLate ir v) || !decide (PReader.IsSourceValue v)) &&
    (!(r.value v).kind.isBound || natTypedInB ir L v)

/-- `inSource`, at the reader. -/
def inSource (p : Predicate) : Bool :=
  match p.role with
  | .source => true
  | .type v => decide (PReader.IsSourceValue v)
  | .realization _ => false

/-- `boolCheckB`, at the reader. -/
def boolCheckB (v : ℕ) : Bool :=
  match (r.value v).typeSource with
  | .pred q =>
    decide (q < r.nPreds) && (r.value v).type == .bit &&
      inSource (r.predicate q) &&
      match (r.predicate q).body with
      | .equal d (.mul (.leaf a) (.leaf b)) (.leaf c) _ =>
        a == v && b == v && c == v && decide (ir.domainField d = valueField ir v)
      | _ => false
  | _ => false

/-- `KprivTyped`, at the reader. -/
def KprivTyped : Prop :=
  ∀ v < ir.values.length, PReader.IsSourceValue v → (r.value v).kind.isKpriv = true →
    (r.value v).typeSource ≠ .node →
      (r.value v).type = .field ∨ boolCheckB ir v = true ∨
        ((r.value v).kind.isBound = true ∧ (r.value v).type ≠ .bit)

instance : Decidable (KprivTyped ir) := by
  unfold KprivTyped
  exact Nat.decidableBallLT _ _

/-- `honestRolesB`, at the reader. -/
def honestRolesB (L : List (ℕ × String)) (S : Structure) : Bool :=
  (List.range ir.values.length).all (valueRolesB ir L) && decide (KprivTyped ir) &&
    ir.fieldRowsB S && decide ir.NoGammaTables

end PReader

/-- **The honest roles' check at the program's context built once**: the code compiled for
`honestRolesB` (`honestRolesB_csimp`). -/
def honestRolesBC (ir : RealizedProgram) (L : List (ℕ × String)) (S : Structure) : Bool :=
  let c := PCtx.build ir
  @PReader.honestRolesB ir (PReader.ofCtx c) L S

end GordieHowe.RealizedProgram
