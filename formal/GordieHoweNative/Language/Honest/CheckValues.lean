-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Completeness.Bound
public import GordieHoweNative.Language.Honest.Check

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Honest.CheckValues`

The definitions of `GordieHowe.Language.Honest.CheckValues` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Honest/CheckValues.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

section

variable (ir : RealizedProgram)

/-- `isCellValue d v`, on value `v`. -/
def cellValueV (d : ℕ) (x : Value) : Bool :=
  x.domain == d &&
    match x.kind with
    | .priv => true
    | .padCopy _ _ => true
    | _ => false

/-- `isLateOf d v`, on value `v`. -/
def lateOfV (d : ℕ) (x : Value) : Bool := x.field.isNone && x.domain == d && ir.isLateV x

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

/-- `Gens.commOf? G r`, the generators read through the table `GT`. -/
def commOfT (GT : NatTrie Gen) (r : LookupRealization) : Option (ℕ × ℕ) :=
  r.digitValues.head?.bind fun u => (GT.getD u default).commPos?

/-- `boundRecAtB G v pid`, through the tables (the generators through `GT`). -/
def boundRecAtT (GT : NatTrie Gen) (v pid : ℕ) : Bool :=
  match (ir.predicateT pid).body with
  | .mem d [rec] (.range _) (.lookup r) =>
    (r.kind == .twoSided || r.kind == .digits) && (commOfT GT r).isNone &&
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

/-- **The bound values' record lookups**, keyed by value (`Structure.boundRecs`), as a table built
once. -/
def _root_.GordieHowe.RealizedProgram.Structure.boundRecTab (S : Structure) : NatTrie ℕ :=
  NatTrie.ofList S.boundRecs

/-- **A value bound to its digits is a source value and the record of the lookup its entry names**
(value `v`, visited as `x`; the entries through the table `T`, the generators through `GT`), as a
check whose failure names the value: not a source value (`roleMismatch`), no entry (`noRecord`), or
an entry whose lookup does not bind it (`notBoundRec`, the slot the lookup). -/
def boundRecsVE (GT : NatTrie Gen) (T : NatTrie ℕ) (v : ℕ) (x : Value) :
    Except StructFailure Unit :=
  match x.kind.isBound with
  | false => .ok ()
  | true =>
    Twin.seqE (Twin.guardE (decide (x.role = .source)) ⟨v, 0, .roleMismatch⟩)
      (match T.get? v with
        | some pid => Twin.guardE (ir.boundRecAtT GT v pid) ⟨v, pid, .notBoundRec⟩
        | none => .error ⟨v, 0, .noRecord⟩)

/-- `boundRecsVE`'s verdict. -/
def boundRecsV (GT : NatTrie Gen) (T : NatTrie ℕ) (v : ℕ) (x : Value) : Bool :=
  Twin.okB (ir.boundRecsVE GT T v x)

variable (L : List (ℕ × String))

/-- `srcNoPadCopyB v`, on value `v`. -/
def srcNoPadCopyV (_ : ℕ) (x : Value) : Bool := !decide (x.role = .source) || !x.kind.isPadCopy

/-- `srcNoMessageB v`, on value `v`. -/
def srcNoMessageV (_ : ℕ) (x : Value) : Bool := !decide (x.role = .source) || !x.kind.isMessage

/-- `srcLatePadB v`, on value `v`. -/
def srcLatePadV (_ : ℕ) (x : Value) : Bool :=
  !decide (x.role = .source) || !ir.isLateV x || latePadTypeV x

/-- `cellB L v`, on value `v`. -/
def cellV (_ : ℕ) (x : Value) : Bool :=
  !cellValueV x.domain x || (ir.cellNodeV x && ir.cellNodeInV L x)

/-- `realTypeB L v`, on value `v`. -/
def realTypeV (v : ℕ) (x : Value) : Bool :=
  !(x.typeSource == .node) || ir.isLateV x || decide (x.role = .source) ||
    (ir.privCellV v x && ir.natTypedV L x)

/-- `boundNoCopyB`'s check at value `u`, on value `u`. -/
def boundNoCopyV (_ : ℕ) (x : Value) : Bool :=
  match x.kind with
  | .bound e => (ir.exprNodes e).all fun w =>
      match (ir.valueT w).kind with
      | .padCopy _ _ => false
      | _ => true
  | _ => true

end

end GordieHowe.RealizedProgram
