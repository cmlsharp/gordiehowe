-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Honest.Exec

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Honest.Check`

The definitions of `GordieHowe.Language.Honest.Check` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Honest/Check.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export
/-- **The operands and the realization of a cross-field `equal`.** -/
structure CrossParts where
  /-- The `x` domain. -/
  dx : ℕ
  /-- The `x` operand. -/
  x : Expr
  /-- The `y` domain. -/
  dy : ℕ
  /-- The `y` operand. -/
  y : Expr
  /-- The kind. -/
  k : CrossKind
  /-- The MAC realization. -/
  real : MacRealization
  deriving Inhabited

/-- **The parts of a cross-field `equal`**, none for any other predicate. -/
def PredBody.crossParts? : PredBody → Option CrossParts
  | .cross dx x dy y k real => some ⟨dx, x, dy, y, k, real⟩
  | _ => none

/-- **The domain, modulus, sides and realization of a `mod_q`.** -/
structure ModParts where
  /-- The domain. -/
  d : ℕ
  /-- The modulus. -/
  q : ℕ
  /-- The left side. -/
  lhs : Expr
  /-- The right side. -/
  rhs : Expr
  /-- The realization. -/
  real : ModRealization
  deriving Inhabited

/-- **The parts of a `mod_q`**, none for any other predicate. -/
def PredBody.modParts? : PredBody → Option ModParts
  | .mod d q lhs rhs real => some ⟨d, q, lhs, rhs, real⟩
  | _ => none

/-- **Whether an expression is a leaf.** -/
def Expr.isLeaf : Expr → Bool
  | .leaf _ => true
  | _ => false

/-- **A MAC site**: the cross-field `equal` `pid`, one of its MAC checks over a field, over `x`'s
field (`xSide`) or over `y`'s field, and the check's tail `tail`. A MAC its `x` domain hosts has
one site, the check over `y`'s field; a MAC no domain hosts has two (compiler/mac.h, `mac_odd`).
The sites are read at the compiler's `macSite` structure records (`macSiteAt`). -/
structure MacSite where
  /-- The cross-field `equal`. -/
  pid : ℕ
  /-- Whether the site is the check over `x`'s field. -/
  xSide : Bool
  /-- The tail of the site's check. -/
  tail : ℕ

/-- **The role of a predicate in a MAC** (the completeness step `CStep.macRow` names it): its
tail, its H predicate, the accumulator row (digit and one-digit tails), group `g`'s accumulator
row, the residues' Boolean check, the quotient-digit lookup (grouped tails), the quotient lookup
(the final quotient of a grouped tail, the quotient of a one-digit tail), the lower-digit and the
top-digit lookups and the no-wrap range (digit tails). -/
inductive MacRole where
  /-- The tail. -/
  | tail
  /-- The H predicate. -/
  | h
  /-- The accumulator row of a digit or one-digit tail. -/
  | accRow
  /-- The accumulator row of group `g` of a grouped tail. -/
  | groupRow (g : ℕ)
  /-- The residues' Boolean check of a grouped tail. -/
  | residues
  /-- The quotient-digit lookup of a grouped tail. -/
  | gqLookup
  /-- The quotient lookup of a grouped or a one-digit tail. -/
  | quotLookup
  /-- The lower-digit lookup of a digit tail. -/
  | lowLookup
  /-- The top-digit lookup of a digit tail. -/
  | topLookup
  /-- The no-wrap range of a digit tail. -/
  | wrap
  deriving Repr, DecidableEq, Inhabited

section

variable {ir : RealizedProgram} {primeNodes : ℕ → List String}
  {L : ℕ → ℕ → Option Ivl}

section Parts

variable (ir)

/-- **Whether predicate `pid` is a cross-field `equal`.** -/
def isCrossB (pid : ℕ) : Bool := (ir.predicateT pid).body.crossParts?.isSome

/-- **The parts of cross-field `equal` `pid`.** -/
def macCross (pid : ℕ) : CrossParts := (ir.predicateT pid).body.crossParts?.getD default

/-- **The slot of the `y`-side site** in a `macSite` record of cross-field `equal` `p`: `2` where
no domain hosts the MAC (`blindX`; the record's tails are `x`'s, then `y`'s), else `1`. -/
def ySlot (p : ℕ) : ℕ := if (ir.macCross p).real.blindX.isSome then 2 else 1

/-- **Site `i` of `macSite` record `g`**, as a check whose failure names the record and the slot:
the cross-field `equal` `preds[0]`, the tail `preds[i]` (`i ≥ 1`), the check over `x`'s field
where `i = 1` and no domain hosts the MAC. -/
def macSiteAtE (S : Structure) (g i : ℕ) : Except StructFailure MacSite :=
  match S.gadgets[g]? with
  | none => .error ⟨g, 0, .noRecord⟩
  | some G =>
    match G.kind with
    | .macSite =>
      match G.preds[0]?, G.preds[i]? with
      | some p, some t =>
        if i = 0 then .error ⟨g, i, .noSlot⟩
        else .ok ⟨p, i == 1 && (ir.macCross p).real.blindX.isSome, t⟩
      | _, _ => .error ⟨g, i, .noSlot⟩
    | _ => .error ⟨g, 0, .notMacSite⟩

/-- **Site `i` of `macSite` record `g`** (`macSiteAtE`, forgetting the failure). -/
def macSiteAt (S : Structure) (g i : ℕ) : Option MacSite := (ir.macSiteAtE S g i).toOption

/-- **The domain of MAC site `st`**: the `x` domain for the check over `x`'s field, the `y` domain
otherwise. -/
def siteDom (st : MacSite) : ℕ := if st.xSide then (ir.macCross st.pid).dx else (ir.macCross st.pid).dy

/-- **The operand of MAC site `st`**: the `x` operand for the check over `x`'s field, the `y`
operand otherwise. -/
def siteOp (st : MacSite) : Expr := if st.xSide then (ir.macCross st.pid).x else (ir.macCross st.pid).y

/-- **The blind of MAC site `st`**: `blindX` for the check over `x`'s field, `blind` otherwise. -/
def macBlind (st : MacSite) : ℕ :=
  if st.xSide then (ir.macCross st.pid).real.blindX.getD 0 else (ir.macCross st.pid).real.blind.getD 0

/-- **The operand a MAC tail `pr` checks**: the operand of its left side's MAC convolution. -/
def tailOperandOf (pr : Predicate) : Expr :=
  match pr.body with
  | .mod _ _ (.add _ (.apply _ z')) _ _ => z'
  | _ => default

/-- **The operand `z'` of a check of MAC site `st` reads the site's operand**: padded by zeros to
`chunks · width` coordinates (`zeroPadB`) where `x`'s domain hosts the MAC; the operand itself where
no domain does. -/
def macOpOkB (st : MacSite) (z' : Expr) : Bool :=
  match (ir.macCross st.pid).real.blindX with
  | none => ir.zeroPadB (ir.domainField (ir.siteDom st))
      ((ir.macCross st.pid).real.chunks * (ir.macCross st.pid).real.width) z' (ir.siteOp st)
  | some _ => z'.beq (ir.siteOp st)

/-- **The tail of MAC site `st`**: the predicate its record names. The checks verify it at the
pointer (`MacBaseFactsC.tail`, `macTailAtB`). -/
def macTail (_ : RealizedProgram) (st : MacSite) : ℕ := st.tail

/-- **The operand the tail of MAC site `st` checks** (`tailOperandOf`). -/
def macCheckOp (st : MacSite) : Expr := tailOperandOf (ir.predicateT (ir.macTail st))

/-- **The parts of the tail of the MAC of `st`.** -/
def macTailParts (st : MacSite) : ModParts :=
  (ir.predicateT (ir.macTail st)).body.modParts?.getD default

/-- **The units of the tail of the MAC of `st`.** -/
def macUnitsAt (st : MacSite) : MacUnits :=
  (macUnits? (ir.macTailParts st).lhs).getD ⟨0, 0, 0, 0, [], default⟩

/-- **The largest entry of the MAC convolution's matrices** of the tail of `st`
(`macConvMax?`, `0` when none). -/
def macConvMaxAt (st : MacSite) : ℕ :=
  (macConvMax? (ir.macUnitsAt st).width (ir.macUnitsAt st).taps).getD 0

variable (primeNodes) in
/-- **The MAC check over the field of site `st`** (`MacFieldCheck`): the check over `y`'s field
with its blind (`macBlindCoreB`) where the `x` domain hosts the MAC; where no domain hosts it, the
check over either field, of odd characteristic (`MacOddFieldOk` with the site's tail,
`macOddFieldAtB`, at the values' intervals of the structure records `S`, `srcLeafIvl`), both
operands' domains of characteristic above `1`. -/
def macFieldCheckB (S : Structure) (st : MacSite) : Bool :=
  match (ir.macCross st.pid).real.blindX with
  | none => !st.xSide &&
      ir.macBlindCoreB (ir.siteDom st) (ir.macBlind st) (ir.macCross st.pid).real
  | some _ => ir.macOddFieldAtB (ir.srcLeafIvl primeNodes S) st.pid (ir.siteDom st)
      (ir.siteOp st) (ir.macBlind st) (ir.macCross st.pid).real (ir.macTail st) &&
      decide (MacChars ir (ir.macCross st.pid).dx (ir.macCross st.pid).dy)

end Parts

section Grouped

variable (ir)

/-- **The grouping of the tail of the MAC of `st`.** -/
def macGrouping (st : MacSite) : GroupedMod := (ir.macTailParts st).real.grouped.getD default

/-- **The accumulators of the grouped tail of `st`.** -/
def macGroupAcc (st : MacSite) : ℕ :=
  match (ir.macGrouping st).accumulators with
  | some (.leaf a) => a
  | _ => 0

/-- **The quotient digits of the grouped tail of `st`.** -/
def macGroupGq (st : MacSite) : ℕ :=
  match (ir.macGrouping st).groupDigits with
  | .leaf g => g
  | _ => 0

end Grouped

section Digits

variable (ir)

/-- **The lower digit of the digit tail of `st`**: the first of its two digits. -/
def macLow (st : MacSite) : ℕ :=
  match (ir.macTailParts st).real.digits with
  | [.leaf l, _] => l
  | _ => 0

/-- **The derived top digit of the digit tail of `st`**: the second of its two digits. -/
def macTop (st : MacSite) : Expr :=
  match (ir.macTailParts st).real.digits with
  | [_, t] => t
  | _ => default

/-- **The accumulator of the digit tail of `st`** (`digitsAcc`). -/
def macDigitsAcc (st : MacSite) : ℕ := ir.digitsAcc (ir.macTailParts st).real

/-- **The no-wrap range's expression of the digit tail of `st`**: `2 low + 2 B top`. -/
def macWrapExpr (st : MacSite) : Expr :=
  .add (.scale (.const 2) (.leaf (ir.macLow st)))
    (.scale (.const (2 * (ir.macTailParts st).real.radix)) (ir.macTop st))

end Digits

section OneDigit

variable (ir)

/-- **The accumulator of the one-digit tail of `st`** (`oneDigitAcc`). -/
def macOneAcc (st : MacSite) : ℕ := ir.oneDigitAcc (ir.macTailParts st).real

end OneDigit

section TwoSides

variable (ir)

/-- **The tail of a MAC check over a field of characteristic `2`**: the predicate the site's record
names. The check verifies it at the pointer (`TwoMacFactsC.tail`, `macTailTwoB`). -/
def twoTail (_ : RealizedProgram) (st : MacSite) : ℕ := st.tail

end TwoSides

section Groups

variable (ir)

/-- **A group without a late histogram reads no late value, nor do its table's rows**
(`RealizeFacts.staticGroups`), as a check at a program reader. -/
def PReader.staticGroupNoLateB (ir : RealizedProgram) [r : PReader] (t g : ℕ) : Bool :=
  match (ir.groupOf t g).lateMult with
  | none => (ir.members t g).all (fun m =>
        (ir.exprNodes (ir.needleExpr m.pred m.needle)).all (PReader.noLateReadB ir)) &&
      (ir.groupOf t g).staticMult.toList.all (PReader.noLateReadB ir) &&
      (ir.tableRowReads t).all (PReader.noLateReadB ir)
  | some _ => true

/-- **A group without a late histogram reads no late value, nor do its table's rows**
(`RealizeFacts.staticGroups`), as a check (`PReader.staticGroupNoLateB` at the program). -/
def staticGroupNoLateB (t g : ℕ) : Bool := @PReader.staticGroupNoLateB ir (PReader.ofProgram ir) t g

/-- **A property of every group of every table**, as a check. -/
def allGroupsB (P : ℕ → ℕ → Bool) : Bool :=
  (List.range ir.tables.length).all fun t => (List.range (ir.groupCountOf t)).all (P t)

end Groups

section Values

variable (ir)

/-- **A property of every predicate of the program**, as a check. -/
def allPredsB (P : ℕ → Bool) : Bool := (List.range ir.predicates.length).all P

/-- **Every blind of a cross-field `equal`'s MAC is the pad copy `polynomialBits` of its tag's pad**
(`BlindsArePadCopies`), as a check at predicate `q`: a committed cell of a domain of the program at
each of its `width` coordinates, the tag's pad a cell of its domain at coordinate `0`. -/
def blindsB (q : ℕ) : Bool :=
  match (ir.predicateT q).body with
  | .cross _ _ _ _ _ real =>
    (real.blind.toList ++ real.blindX.toList).all fun b =>
      ir.isPadCopyB b real.tag "polynomialBits" &&
        decide ((ir.value b).domain < ir.domains.length) &&
        decide (b < ir.values.length) && ir.isCellValue (ir.value b).domain b &&
        decide (real.width ≤ (ir.value b).size) &&
        decide ((ir.value real.tag).domain < ir.domains.length) &&
        decide (real.tag < ir.values.length) &&
        !ir.isCellValue (ir.value real.tag).domain real.tag &&
        ir.isLateOf (ir.value real.tag).domain real.tag &&
        decide (0 < (ir.value real.tag).size)
  | _ => true

/-- **`NoGenRead`, through the reads table**, at a program reader. -/
def PReader.noGenReadB (ir : RealizedProgram) [r : PReader] (w : ℕ) : Bool :=
  (r.reads w).all fun rd =>
    match rd with
    | .late u => !decide (u < r.nValues ∧ PReader.IsLate ir u) || decide (PReader.IsSourceValue u)
    | _ => true

/-- **`NoGenPred`, as a check**, through the closure table (`predNodesM`), at a program reader. -/
def PReader.noGenPredB (ir : RealizedProgram) [PReader] (b : PredBody) : Bool :=
  (PReader.predNodesM ir b).all (PReader.noGenReadB ir)

/-- **`NoGenRead`, as a check**, through the reads table (`PReader.noGenReadB` at the
program). -/
def noGenReadB (w : ℕ) : Bool := @PReader.noGenReadB ir (PReader.ofProgram ir) w

/-- **`NoGenPred`, as a check**, through the closure table (`PReader.noGenPredB` at the
program). -/
def noGenPredB (b : PredBody) : Bool := @PReader.noGenPredB ir (PReader.ofProgram ir) b

end Values

section Honest

variable (ir)

variable (L) in
/-- **The cross-field `equal` of MAC site `st` is a source predicate and the site's operand reads
within `[0, 1]` by the source values' intervals** (`HonestFacts.macIvls`), as a check at the values'
intervals `L`. -/
def macIvlAtB (st : MacSite) : Bool :=
  ir.inSource (ir.predicateT st.pid) &&
    decide (IvlWithin (ir.srcIvl L (ir.domainField (ir.siteDom st)) (ir.macCheckOp st)) 0 1)

variable (L) in
/-- **The cross-field `equal` of MAC site `st` is a source predicate and the site's operand reads
within `[0, 1]` by the source values' intervals** (`macIvlAtB`), at a program reader. -/
def PReader.macIvlAtB (ir : RealizedProgram) [r : PReader] (st : MacSite) : Bool :=
  ir.inSource (r.predicate st.pid) &&
    decide (IvlWithin (PReader.srcIvl L ir (ir.domainField (ir.siteDom st))
      (ir.macCheckOp st)) 0 1)

variable (primeNodes) in
/-- **`macIvlAtB` at the values' intervals `srcLeafIvl` of the structure records `S`.** -/
def macIvlB (S : Structure) (st : MacSite) : Bool := ir.macIvlAtB (ir.srcLeafIvl primeNodes S) st

/-- **A late member of a mixed group at the late histogram `v` of table `t` reads a digit of the
digit tail of `st`**, as a check. -/
def lateMemberAtB (st : MacSite) (t v : ℕ) (m : Member) : Bool :=
  decide (ir.chalField (ir.alphaOf t) = ir.domainField (ir.siteDom st)) &&
    decide (m.first + m.count ≤ (ir.macUnitsAt st).width) &&
    (((ir.needleExpr m.pred m.needle).beq (.leaf (ir.macLow st)) &&
        decide ((ir.macTailParts st).real.radix ≤ (ir.value v).size)) ||
      (ir.needleExpr m.pred m.needle).beq (ir.macTop st))

/-- **A late member of a mixed group reads the quotient of the one-digit tail of `st`**, as a check at table `t`. -/
def lateMemberOneAtB (st : MacSite) (t : ℕ) (m : Member) : Bool :=
  decide (ir.chalField (ir.alphaOf t) = ir.domainField (ir.siteDom st)) &&
    decide (m.first + m.count ≤ (ir.macUnitsAt st).width) &&
    (ir.needleExpr m.pred m.needle).beq (ir.macTailParts st).real.quotExpr

/-- **The bound on the honest quotient of the one-digit tail of `st`**. -/
def macQuotMax (st : MacSite) : ℕ := (1 + (ir.macUnitsAt st).chunks * ir.macConvMaxAt st) / 2

/-- **The bound on the honest top digit of the digit tail of `st`**. -/
def macTopMax (st : MacSite) : ℕ :=
  (1 + (ir.macUnitsAt st).chunks * ir.macConvMaxAt st) / 2 / (ir.macTailParts st).real.radix

end Honest

end

end GordieHowe.RealizedProgram
