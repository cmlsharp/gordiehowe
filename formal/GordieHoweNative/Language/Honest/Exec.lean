-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Honest.Packed

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Honest.Exec`

The definitions of `GordieHowe.Language.Honest.Exec` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Honest/Exec.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export
/-- Whether a kind is a message. -/
def Kind.isMessage : Kind → Bool
  | .message _ => true
  | _ => false

section

variable (ir : RealizedProgram)

variable {ir I}

variable (ir) in
/-- **An expression through a top shared expression**: `.ref k` the shared expression `k`, any other
expression itself. -/
def unref : Expr → Expr
  | .ref k => if k < ir.exprs.length then ir.expr k else .ref k
  | e => e

variable (ir) in
/-- **The members a static histogram counts** in group `g` of table `t`: with a late histogram
beside it, the members reading no late value (the late histogram counts the others); otherwise all
the group's members. -/
def staticMembers (t g : ℕ) : List Member :=
  if (ir.groupOf t g).lateMult.isSome then (ir.members t g).filter fun m => !ir.memberReadsLate m
  else ir.members t g

variable {primeNodes : ℕ → List String} {L : ℕ → ℕ → Option Ivl}

/-- Whether a kind is a pad copy. -/
def _root_.GordieHowe.RealizedProgram.Kind.isPadCopy : Kind → Bool
  | .padCopy _ _ => true
  | _ => false

variable (ir) in
/-- **The values the honest static histogram reads of member `m`'s needle** in table `t`: for a
table packed at a value, its records' expression (`memberBase?`); otherwise the needle's values. -/
def histNodes (t : ℕ) (m : Member) : List ℕ :=
  match ir.gammaPack? t with
  | some (P, A, _) =>
    match ir.memberBase? P A m with
    | some b => ir.exprNodes b
    | none => ir.exprNodes (ir.needleExpr m.pred m.needle)
  | none => ir.exprNodes (ir.needleExpr m.pred m.needle)

variable (ir) in
/-- **The values the honest static histogram reads of table `t`'s rows**: for a table packed at a
value, its records' expression's values; otherwise the rows' (`tableRowReads`). -/
def histRowNodes (t : ℕ) : List ℕ :=
  match ir.gammaPack? t with
  | some (_, _, b) => ir.exprNodes b
  | none => ir.tableRowReads t

variable (ir) in
/-- **Member `m`'s needle is packed at the value `P` with `A` columns**, as a check
(`memberBase?`): its coordinates within the needle's length, its records' expression reading only
source values. -/
def packMemberB (P A : ℕ) (m : Member) : Bool :=
  match ir.memberBase? P A m with
  | some b => decide (m.first + m.count ≤ ir.exprLen (ir.needleExpr m.pred m.needle)) &&
      (ir.exprNodes b).all fun w => decide (ir.IsSourceValue w)
  | none => false

variable (ir) in
/-- **The static members of group `g` of a table packed at a value are packed alike**, as a check:
the powers' value and the rows' records read only source values, and every member it counts is
packed at the table's value and arity (`packMemberB`); a table packed at no value passes. -/
def packGroupB (t g : ℕ) : Bool :=
  match ir.gammaPack? t with
  | some (P, A, b) => decide (ir.IsSourceValue P) &&
      (ir.exprNodes b).all (fun w => decide (ir.IsSourceValue w)) &&
      (ir.staticMembers t g).all (ir.packMemberB P A)
  | none => true

variable (ir L) in
/-- **The interval of an expression in field `f` from the source values' intervals** (`ivlOf` at the
values' intervals `L` restricted to the source values of the program). -/
def srcIvl (f : ℕ) (e : Expr) : Option Ivl :=
  ir.ivlOf (ir.charOf f) (fun v => if v < ir.values.length ∧ ir.IsSourceValue v then
    L f v else none) e

variable (L) in
/-- **The interval of an expression in field `f` from the source values' intervals**, at a program
reader (`srcIvl`). -/
def PReader.srcIvl (ir : RealizedProgram) [r : PReader] (f : ℕ) (e : Expr) : Option Ivl :=
  ir.ivlOf (ir.charOf f) (fun v => if v < r.nValues ∧ PReader.IsSourceValue v then
    L f v else none) e

variable (ir L) in
/-- **Predicate `rid` is the quotient's `in` of the one-digit `mod_q` `m`, whose honest quotient
lies in its range**, as a check: `m` is a source `mod_q` in the one-digit form with `q > 0` and
`p > 2`, its quotient derived from the sides (`quotDerivedB`), `rid` its quotient's direct `in`
`Q ∈ [0, N)` (`quotRangeB`), and by the sides' intervals from the source values (`srcIvl`,
`[l, h]` and `[l', h']`) the honest quotient `(e − e')/q − qlo` lies in `[0, N)`:
`h' − l + q · qlo < q` and `(h − l')/q − qlo < N`. -/
def oneDigitQuotAtB (m rid : ℕ) : Bool :=
  match (ir.predicate m).body with
  | .mod d q e e' real =>
    ir.inSource (ir.predicate m) && real.form == .oneDigit && decide (0 < q) &&
      decide (2 < ir.charOf (ir.domainField d)) && ir.quotDerivedB d q e e' real &&
      ir.quotRangeB d q e real rid &&
      match ir.srcIvl L (ir.domainField d) e, ir.srcIvl L (ir.domainField d) e',
        (ir.predicate rid).body with
      | some J, some J', .mem _ [_] (.range N) _ =>
        decide (J'.hi - J.lo + q * real.quotientLo < q) &&
          decide ((J.hi - J'.lo) / q - real.quotientLo < N)
      | _, _, _ => false
  | _ => false

variable (ir) in
/-- **Predicate `q` is the Boolean check of a pad copy**, as a check: `v · v = v` in a domain of
`v`'s field, `v` a pad copy that is a committed cell of its domain. -/
def padCopyBoolB (q : ℕ) : Bool :=
  match (ir.predicate q).body with
  | .equal d (.mul (.leaf a) (.leaf b)) (.leaf v) _ =>
    a == v && b == v && (ir.value v).kind.isPadCopy && decide (v < ir.values.length) &&
      decide ((ir.value v).domain < ir.domains.length) &&
      ir.isCellValue (ir.value v).domain v && decide (ir.domainField d = ir.valueField v)
  | _ => false

variable (ir) in
/-- **Predicate `q` is the field equation of a source `mod_q` in the field form**, as a check: `q`'s
role names its owner `m` (`realization m`), a source `mod_q` of sides `e`, `e'` whose realization
has the field form, and `q` is its row `e + (p − 1) e' = 0` (`fieldRowB`). -/
def fieldRowRealB (q : ℕ) : Bool :=
  match (ir.predicateT q).role with
  | .realization m =>
    decide (m < ir.predicates.length) && ir.inSource (ir.predicateT m) &&
      match (ir.predicateT m).body with
      | .mod d _ a b real => real.form == .field && ir.fieldRowB d a b (ir.predicateT q).body
      | _ => false
  | _ => false

variable (ir) in
/-- **Every source `mod_q` in the field form has its field row at the structure records' pointer**
(`fieldRowPtrE`), as a check whose failure names the `mod_q`. -/
def fieldRowsE (S : Structure) : Except StructFailure Unit :=
  Twin.allE (fun m p =>
    if ir.inSource p && (match p.body with
        | .mod _ _ _ _ real => real.form == .field
        | _ => false) then ir.fieldRowPtrE S m
    else .ok ()) 0 ir.predicates

/-- **The value a quadratic root equation is on** (`quadRootView`'s `v₁`), read off the equation. -/
def quadVar? (pr : Predicate) : Option ℕ :=
  match pr.body with
  | .equal _ (.mul (.add (.leaf _) (.scale (.const _) (.leaf v₁))) _) (.leaf _) _ => some v₁
  | _ => none

variable (ir) in
/-- **The value a root-set equation is on** (`rootSetView`'s first reading of the root product),
read off the equation. -/
def rootSetVar? (pr : Predicate) : Option ℕ :=
  match pr.body with
  | .equal d lhs (.leaf _) _ => (ir.rootsAt (ir.domainField d) rootFuel ir.exprs.length 0 lhs).map (·.1)
  | _ => none

/-- **The value whose type check predicate `pr` is**, read off its role (`.type v`). -/
def typeVar? (pr : Predicate) : Option ℕ :=
  match pr.role with
  | .type v => some v
  | _ => none

variable (ir) in
/-- **The type predicate of value `v` (`x`, its value) names `v` in its role**, as a check whose
failure names `v`: a value whose type is enforced by predicate `q` (`typeSource = .pred q`) has `q`
a predicate of the program of role `type v`. -/
def typeRoleVE (v : ℕ) (x : Value) : Except StructFailure Unit :=
  match x.typeSource with
  | .pred q =>
    Twin.seqE (Twin.guardE (decide (q < ir.predicates.length)) ⟨v, 0, .badPointer⟩)
      (Twin.guardE ((ir.predicateT q).role == .type v) ⟨v, 0, .roleMismatch⟩)
  | _ => .ok ()

variable (ir) in
/-- **`typeRoleVE` as a `Bool`.** -/
def typeRoleV (v : ℕ) (x : Value) : Bool := Twin.okB (ir.typeRoleVE v x)

variable (ir) in
/-- **The predicates the source values' intervals read are source predicates**, at predicate `q`,
as a check: a source predicate; or a direct, digit or two-sided `in` on no source value or on no
source value plus a value; or a field `equal` that is the type predicate or a root equation
(`rootEqB`) of no source value (the type check's value read off its role, `typeVar?`). -/
def ivlSourceB (q : ℕ) : Bool :=
  ir.inSource (ir.predicateT q) ||
    match (ir.predicateT q).body with
    | .mem _ [rec] _ (.lookup r) =>
      !(r.kind == .direct || r.kind == .digits || r.kind == .twoSided) ||
        match rec with
        | .leaf v => !decide (ir.IsSourceValue v)
        | .add (.leaf v) (.leaf _) => !decide (ir.IsSourceValue v)
        | _ => true
    | .equal .. =>
      ((quadVar? (ir.predicateT q)).toList ++ (ir.rootSetVar? (ir.predicateT q)).toList ++
          (typeVar? (ir.predicateT q)).toList).all fun v =>
        !(decide (v < ir.values.length) && decide (ir.IsSourceValue v) &&
          (ir.rootEqB v (ir.predicateT q) || (ir.value v).typeSource == .pred q))
    | _ => true

end

/-- **A value of a `kpriv` variable** (paper, `def:o-semantics`): committed, bound to its digits
(a committed source value), or late. -/
def Kind.isKpriv : Kind → Bool
  | .priv => true
  | .late => true
  | .bound _ => true
  | _ => false

section

variable (ir : RealizedProgram)

/-- **`fieldRowsE` as a `Bool`.** -/
def fieldRowsB (S : Structure) : Bool := Twin.okB (ir.fieldRowsE S)

end

end GordieHowe.RealizedProgram
