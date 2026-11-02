-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Completeness.Committed
public import GordieHoweNative.Language.Honest.Check

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Completeness.MacCheck`

The definitions of `GordieHowe.Language.Completeness.MacCheck` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Completeness/MacCheck.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export
section

variable {ir : RealizedProgram} {primeNodes : ℕ → List String} {S : Structure}

/-- **The facts of the MAC of site `st` with its tail, at the certificate's generators `G`**
(`MacBaseC`): the site's check (`macFieldCheckB`), a blind, a tail (`macTailAtB`) that is a
`mod_2` of the `y` domain in the MAC unit form with a leaf on the right; the tag late, of one
coordinate; the operands, the unit's operand and the powers reading no late value; the blind the
tag's pad copy; the MAC field of characteristic `2` holding the powers, of the units' width. -/
structure MacBaseFactsC (S : Structure) (G : Gens) (st : MacSite) : Prop where
  lt : st.pid < ir.predicates.length
  cross : ir.isCrossB st.pid = true
  side : ir.macFieldCheckB primeNodes S st = true
  blind : (ir.macCross st.pid).real.blind.isSome = true
  tail : ir.macTailAtB st.pid (ir.siteDom st) (ir.macCheckOp st) (ir.macBlind st)
    (ir.macCross st.pid).real (ir.macTail st) = true
  opOk : ir.macOpOkB st (ir.macCheckOp st) = true
  dyLt : ir.siteDom st < ir.domains.length
  opExpr : ir.ExprOk (ir.domainField (ir.siteDom st)) (ir.macCheckOp st)
  tailMod : (ir.predicateT (ir.macTail st)).body.modParts?.isSome = true
  tailD : (ir.macTailParts st).d = (ir.siteDom st)
  tailQ : (ir.macTailParts st).q = 2
  tailR : (ir.macTailParts st).rhs.isLeaf = true
  units : (macUnits? (ir.macTailParts st).lhs).isSome = true
  tagGen : G.at (ir.macCross st.pid).real.tag = .tag st.pid
  tagNotSource : ¬ ir.IsSourceValue (ir.macCross st.pid).real.tag
  tagLate : ir.IsLate (ir.macCross st.pid).real.tag
  tag1 : (ir.value (ir.macCross st.pid).real.tag).size = 1
  xNoLate : ∀ v ∈ ir.exprNodes (ir.macCross st.pid).x, ir.noLateReadB v = true
  yNoLate : ∀ v ∈ ir.exprNodes (ir.macCross st.pid).y, ir.noLateReadB v = true
  opNoLate : ∀ v ∈ ir.exprNodes (ir.macUnitsAt st).operand, ir.noLateReadB v = true
  powNoLate : ir.noLateReadB (ir.macUnitsAt st).powers = true
  blindCopy : ir.isPadCopyB (ir.macBlind st) (ir.macCross st.pid).real.tag "polynomialBits" = true
  macChar : ir.charOf (ir.macCross st.pid).real.macField = 2
  powField : ir.valueField (ir.macUnitsAt st).powers = (ir.macCross st.pid).real.macField
  width : (ir.macUnitsAt st).width = (ir.macCross st.pid).real.width

/-- **`MacBaseFactsC` is decidable**, as the conjunction of its fields. -/
instance (S : Structure) (G : Gens) (st : MacSite) :
    Decidable (ir.MacBaseFactsC (primeNodes := primeNodes) S G st) :=
  decidable_of_iff (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧
    _ ∧ _ ∧ _ ∧ _ ∧ _)
    ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
      h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩,
     fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
      h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩⟩

variable (ir primeNodes) in
/-- **The MAC of site `st` with its tail at the generators `G`, as a check** (`MacBaseFactsC`). -/
def macBaseCB (S : Structure) (G : Gens) (st : MacSite) : Bool :=
  decide (ir.MacBaseFactsC (primeNodes := primeNodes) S G st)

/-- **`MacBaseFactsC`, decided at a program reader**: its fields' decisions in their order, the
values, the predicates and the reads through the reader (`macBaseB_ofProgram`). -/
def PReader.macBaseB (ir : RealizedProgram) [r : PReader] (primeNodes : ℕ → List String) (S : Structure) (G : Gens)
    (st : MacSite) : Bool :=
  decide (st.pid < r.nPreds) && ir.isCrossB st.pid && ir.macFieldCheckB primeNodes S st &&
    (ir.macCross st.pid).real.blind.isSome &&
    ir.macTailAtB st.pid (ir.siteDom st) (ir.macCheckOp st) (ir.macBlind st)
      (ir.macCross st.pid).real (ir.macTail st) &&
    ir.macOpOkB st (ir.macCheckOp st) && decide (ir.siteDom st < ir.domains.length) &&
    decide (ir.ExprOk (ir.domainField (ir.siteDom st)) (ir.macCheckOp st)) &&
    (r.predicate (ir.macTail st)).body.modParts?.isSome &&
    decide ((ir.macTailParts st).d = (ir.siteDom st)) && decide ((ir.macTailParts st).q = 2) &&
    (ir.macTailParts st).rhs.isLeaf && (macUnits? (ir.macTailParts st).lhs).isSome &&
    decide (G.at (ir.macCross st.pid).real.tag = .tag st.pid) &&
    !decide (PReader.IsSourceValue (ir.macCross st.pid).real.tag) &&
    decide (PReader.IsLate ir (ir.macCross st.pid).real.tag) &&
    decide ((r.value (ir.macCross st.pid).real.tag).size = 1) &&
    (ir.exprNodes (ir.macCross st.pid).x).all (PReader.noLateReadB ir) &&
    (ir.exprNodes (ir.macCross st.pid).y).all (PReader.noLateReadB ir) &&
    (ir.exprNodes (ir.macUnitsAt st).operand).all (PReader.noLateReadB ir) &&
    PReader.noLateReadB ir (ir.macUnitsAt st).powers &&
    ir.isPadCopyB (ir.macBlind st) (ir.macCross st.pid).real.tag "polynomialBits" &&
    decide (ir.charOf (ir.macCross st.pid).real.macField = 2) &&
    decide (ir.valueField (ir.macUnitsAt st).powers = (ir.macCross st.pid).real.macField) &&
    decide ((ir.macUnitsAt st).width = (ir.macCross st.pid).real.width)

/-- **The facts of the ungrouped digit tail of the MAC of `st`, at the certificate's generators
`G`** (`DigitsMacC`): the digit form with the digits
`[low, top]`, the accumulator committing the left side and the top digit derived; the accumulator
and the lower digit late values of the `y` domain's field of the units' width; the left side reading
no late value; the convolutions, the accumulator and the radix fitting the characteristic; the
lookups on the digits and the no-wrap range having room. -/
structure DigitsMacFactsC (G : Gens) (st : MacSite) : Prop where
  tailForm : (ir.macTailParts st).real.isDigitsTail = true
  two : (match (ir.macTailParts st).real.digits with
      | [.leaf _, _] => true
      | _ => false) = true
  derived : ir.topDerivedB (ir.siteDom st) 2 (ir.macTailParts st).rhs
    (ir.macTailParts st).real (ir.macDigitsAcc st) = true
  accGen : G.at (ir.macDigitsAcc st) = .digitsAcc (ir.macTail st)
  accNotSource : ¬ ir.IsSourceValue (ir.macDigitsAcc st)
  accLt : ir.macDigitsAcc st < ir.values.length
  accLate : ir.IsLate (ir.macDigitsAcc st)
  accField : ir.valueField (ir.macDigitsAcc st) = ir.domainField (ir.siteDom st)
  lowGen : G.at (ir.macLow st) = .lowDigit (ir.macTail st) 0
  lowNotSource : ¬ ir.IsSourceValue (ir.macLow st)
  lowLt : ir.macLow st < ir.values.length
  lowLate : ir.IsLate (ir.macLow st)
  lowField : ir.valueField (ir.macLow st) = ir.domainField (ir.siteDom st)
  lowSize : (ir.value (ir.macLow st)).size = (ir.macUnitsAt st).width
  accSize : (ir.value (ir.macDigitsAcc st)).size = (ir.macUnitsAt st).width
  topLen : ir.exprLen (ir.macTop st) = (ir.macUnitsAt st).width
  lNoLate : ∀ v ∈ ir.exprNodes (ir.macTailParts st).lhs, ir.noLateReadB v = true
  hw : 0 < (ir.macUnitsAt st).width
  conv : (macConvMax? (ir.macUnitsAt st).width (ir.macUnitsAt st).taps).isSome = true
  convFit : 2 * (ir.macUnitsAt st).width < ir.charOf (ir.domainField (ir.siteDom st))
  accMax : 1 + (ir.macUnitsAt st).chunks * ir.macConvMaxAt st <
      ir.charOf (ir.domainField (ir.siteDom st))
  radixPos : 0 < (ir.macTailParts st).real.radix
  radixChar : 2 * (ir.macTailParts st).real.radix < ir.charOf (ir.domainField (ir.siteDom st))
  lowRoom : ir.digitsRoomB (ir.macLow st) (ir.siteDom st) (ir.macTailParts st).real.radix = true
  topRoom : ir.topRoomB (ir.macTop st) (ir.siteDom st)
      ((1 + (ir.macUnitsAt st).chunks * ir.macConvMaxAt st) /
        (2 * (ir.macTailParts st).real.radix)) = true
  wrapRoom : ir.wrapRoomB (ir.macWrapExpr st) (ir.siteDom st)
      (1 + (ir.macUnitsAt st).chunks * ir.macConvMaxAt st) = true

/-- **`DigitsMacFactsC` is decidable**, as the conjunction of its fields. -/
instance (G : Gens) (st : MacSite) : Decidable (ir.DigitsMacFactsC G st) :=
  decidable_of_iff (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧
    _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25, h26⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26⟩,
     fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25, h26⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26⟩⟩

/-- **`DigitsMacFactsC`, decided at a program reader**: its fields' decisions in their order, the
values and the reads through the reader (`digitsMacB_ofProgram`). -/
def PReader.digitsMacB (ir : RealizedProgram) [r : PReader] (G : Gens) (st : MacSite) : Bool :=
  (ir.macTailParts st).real.isDigitsTail &&
    (match (ir.macTailParts st).real.digits with
      | [.leaf _, _] => true
      | _ => false) &&
    ir.topDerivedB (ir.siteDom st) 2 (ir.macTailParts st).rhs (ir.macTailParts st).real
      (ir.macDigitsAcc st) &&
    decide (G.at (ir.macDigitsAcc st) = .digitsAcc (ir.macTail st)) &&
    !decide (PReader.IsSourceValue (ir.macDigitsAcc st)) &&
    decide (ir.macDigitsAcc st < r.nValues) && decide (PReader.IsLate ir (ir.macDigitsAcc st)) &&
    decide (ir.valueField (ir.macDigitsAcc st) = ir.domainField (ir.siteDom st)) &&
    decide (G.at (ir.macLow st) = .lowDigit (ir.macTail st) 0) &&
    !decide (PReader.IsSourceValue (ir.macLow st)) && decide (ir.macLow st < r.nValues) &&
    decide (PReader.IsLate ir (ir.macLow st)) &&
    decide (ir.valueField (ir.macLow st) = ir.domainField (ir.siteDom st)) &&
    decide ((r.value (ir.macLow st)).size = (ir.macUnitsAt st).width) &&
    decide ((r.value (ir.macDigitsAcc st)).size = (ir.macUnitsAt st).width) &&
    decide (ir.exprLen (ir.macTop st) = (ir.macUnitsAt st).width) &&
    (ir.exprNodes (ir.macTailParts st).lhs).all (PReader.noLateReadB ir) &&
    decide (0 < (ir.macUnitsAt st).width) &&
    (macConvMax? (ir.macUnitsAt st).width (ir.macUnitsAt st).taps).isSome &&
    decide (2 * (ir.macUnitsAt st).width < ir.charOf (ir.domainField (ir.siteDom st))) &&
    decide (1 + (ir.macUnitsAt st).chunks * ir.macConvMaxAt st <
      ir.charOf (ir.domainField (ir.siteDom st))) &&
    decide (0 < (ir.macTailParts st).real.radix) &&
    decide (2 * (ir.macTailParts st).real.radix < ir.charOf (ir.domainField (ir.siteDom st))) &&
    ir.digitsRoomB (ir.macLow st) (ir.siteDom st) (ir.macTailParts st).real.radix &&
    ir.topRoomB (ir.macTop st) (ir.siteDom st)
      ((1 + (ir.macUnitsAt st).chunks * ir.macConvMaxAt st) /
        (2 * (ir.macTailParts st).real.radix)) &&
    ir.wrapRoomB (ir.macWrapExpr st) (ir.siteDom st)
      (1 + (ir.macUnitsAt st).chunks * ir.macConvMaxAt st)

variable (ir) in
/-- **The ungrouped digit tail of the MAC of `st` at the generators `G`, as a check**
(`DigitsMacFactsC`). -/
def digitsMacCB (G : Gens) (st : MacSite) : Bool := decide (ir.DigitsMacFactsC G st)

/-- **The facts of the one-digit tail of the MAC of `st`, at the certificate's generators `G`**
(`OneDigitMacC`): the one-digit form, its quotient derived from the accumulator,
which commits the left side; the accumulator a late value of the `y` domain's field of the units'
width; the left side reading no late value; the convolutions and the accumulator fitting the
characteristic; the lookups on the quotient having room. -/
structure OneDigitMacFactsC (G : Gens) (st : MacSite) : Prop where
  tailForm : (ir.macTailParts st).real.isOneDigitTail = true
  derived : ir.quotAccShapeB (ir.siteDom st) 2 (ir.macTailParts st).rhs
    (ir.macTailParts st).real = true
  accGen : G.at (ir.macOneAcc st) = .digitsAcc (ir.macTail st)
  accNotSource : ¬ ir.IsSourceValue (ir.macOneAcc st)
  accLt : ir.macOneAcc st < ir.values.length
  accLate : ir.IsLate (ir.macOneAcc st)
  accField : ir.valueField (ir.macOneAcc st) = ir.domainField (ir.siteDom st)
  accSize : (ir.value (ir.macOneAcc st)).size = (ir.macUnitsAt st).width
  quotLen : ir.exprLen (ir.macTailParts st).real.quotExpr = (ir.macUnitsAt st).width
  lNoLate : ∀ v ∈ ir.exprNodes (ir.macTailParts st).lhs, ir.noLateReadB v = true
  hw : 0 < (ir.macUnitsAt st).width
  conv : (macConvMax? (ir.macUnitsAt st).width (ir.macUnitsAt st).taps).isSome = true
  convFit : 2 * (ir.macUnitsAt st).width < ir.charOf (ir.domainField (ir.siteDom st))
  accMax : 1 + (ir.macUnitsAt st).chunks * ir.macConvMaxAt st <
      ir.charOf (ir.domainField (ir.siteDom st))
  quotRoom : ir.topRoomB (ir.macTailParts st).real.quotExpr (ir.siteDom st)
      ((1 + (ir.macUnitsAt st).chunks * ir.macConvMaxAt st) / 2) = true

/-- **`OneDigitMacFactsC` is decidable**, as the conjunction of its fields. -/
instance (G : Gens) (st : MacSite) : Decidable (ir.OneDigitMacFactsC G st) :=
  decidable_of_iff (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩,
     fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩⟩

variable (ir) in
/-- **The one-digit tail of the MAC of `st` at the generators `G`, as a check**
(`OneDigitMacFactsC`). -/
def oneDigitMacCB (G : Gens) (st : MacSite) : Bool := decide (ir.OneDigitMacFactsC G st)

/-- **The facts of the grouped tail of the MAC of `st`, at the certificate's generators `G`**
(`GroupedMacC`): the grouped form, the accumulators
and the quotient digits leaves, late values of the `y` domain's field; the groups' sums fit the
digits; the lookups on the digits and the final quotient have room. -/
structure GroupedMacFactsC (G : Gens) (st : MacSite) : Prop where
  grouped : (ir.macTailParts st).real.grouped.isSome = true
  core : ir.groupedCoreB (ir.siteDom st) 2 (ir.macTailParts st).lhs (ir.macTailParts st).rhs
    (ir.macTailParts st).real = true
  quotRange : ir.groupedQuotRangeB (ir.siteDom st) (ir.macTailParts st).lhs
    (ir.macTailParts st).real = true
  accLeaf : (match (ir.macGrouping st).accumulators with
      | some (.leaf _) => true
      | _ => false) = true
  gqLeaf : (match (ir.macGrouping st).groupDigits with
      | .leaf _ => true
      | _ => false) = true
  accGen : G.at (ir.macGroupAcc st) = .acc (ir.macTail st)
  accNotSource : ¬ ir.IsSourceValue (ir.macGroupAcc st)
  accLt : ir.macGroupAcc st < ir.values.length
  accLate : ir.IsLate (ir.macGroupAcc st)
  accField : ir.valueField (ir.macGroupAcc st) = ir.domainField (ir.siteDom st)
  gqGen : G.at (ir.macGroupGq st) = .quotDigit (ir.macTail st)
  gqNotSource : ¬ ir.IsSourceValue (ir.macGroupGq st)
  gqLt : ir.macGroupGq st < ir.values.length
  gqLate : ir.IsLate (ir.macGroupGq st)
  gqField : ir.valueField (ir.macGroupGq st) = ir.domainField (ir.siteDom st)
  conv : (macConvMax? (ir.macUnitsAt st).width (ir.macUnitsAt st).taps).isSome = true
  fit : ∀ fc ∈ (ir.macGrouping st).groups, fc.2 * ir.macConvMaxAt st / 2 <
      (ir.macGrouping st).base ^ (ir.macGrouping st).digitCount
  digitsRoom : ir.digitsRoomB (ir.macGroupGq st) (ir.siteDom st) (ir.macGrouping st).base = true
  finalRoom : ir.finalRoomB (ir.macTailParts st).real.quotExpr (ir.siteDom st)
      (ir.macGrouping st).groups.length = true

/-- **`GroupedMacFactsC` is decidable**, as the conjunction of its fields. -/
instance (G : Gens) (st : MacSite) :
    Decidable (ir.GroupedMacFactsC G st) :=
  decidable_of_iff (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    ⟨fun ⟨h1, h2, h2', h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ =>
      ⟨h1, h2, h2', h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩,
     fun ⟨h1, h2, h2', h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ =>
      ⟨h1, h2, h2', h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩⟩

variable (ir) in
/-- **The grouped tail of the MAC of `st` at the generators `G`, as a check**
(`GroupedMacFactsC`). -/
def groupedMacCB (G : Gens) (st : MacSite) : Bool :=
  decide (ir.GroupedMacFactsC G st)

variable (ir) in
/-- **The tail of the MAC of `st` at the generators `G`, as a check**: a grouped tail
(`groupedMacCB`), a one-digit tail (`oneDigitMacCB`) or an ungrouped digit tail (`digitsMacCB`), by
the tail's form. -/
def macTailCB (G : Gens) (st : MacSite) : Bool :=
  if (ir.macTailParts st).real.grouped.isSome then ir.groupedMacCB G st
  else if (ir.macTailParts st).real.isOneDigitTail then ir.oneDigitMacCB G st
  else ir.digitsMacCB G st

variable (ir primeNodes) in
/-- **Predicate `q` plays role `role` in the MAC of site `st`** (`MacFormC.Role`), as a check: the
role fits the form of the site's tail (grouped, one-digit or digit, read off the tail's
realization), and `q` is the site's tail, its H predicate, or a predicate of the role's shape at
the site's parts. -/
def macRoleAtB (S : Structure) (st : MacSite) (role : MacRole) (q : ℕ) : Bool :=
  let R := (ir.macTailParts st).real
  let b := (ir.predicateT q).body
  match role with
  | .tail => q == ir.macTail st
  | .h => (ir.macCross st.pid).real.hPredicate == some q
  | .groupRow g => R.grouped.isSome && decide (g < (ir.macGrouping st).groups.length) &&
      ir.groupRowB (ir.srcLeafIvl primeNodes S) (ir.siteDom st) (ir.macUnitsAt st)
        (ir.macGrouping st) (ir.macGroupAcc st) g ((ir.macGrouping st).groups.getD g default) b
  | .residues => R.grouped.isSome &&
      match b with
      | .equal d (.mul R₁ R₂) R₃ _ => d == ir.siteDom st &&
          R₁.beq (ir.macGrouping st).residues && R₂.beq (ir.macGrouping st).residues &&
          R₃.beq (ir.macGrouping st).residues
      | _ => false
  | .gqLookup => R.grouped.isSome &&
      match b with
      | .mem _ [.leaf g] (.range _) (.lookup _) => g == ir.macGroupGq st
      | _ => false
  | .quotLookup => (R.grouped.isSome || R.isOneDigitTail) &&
      match b with
      | .mem _ [D] (.range _) (.lookup _) => D.beq R.quotExpr
      | _ => false
  | .accRow => !R.grouped.isSome &&
      match b with
      | .equal d Lr (.leaf z) _ => d == ir.siteDom st &&
          ir.constAll z 0 (ir.exprLen (ir.macTailParts st).lhs) (ir.domainField (ir.siteDom st)) &&
          accTerms (ir.charOf (ir.domainField (ir.siteDom st)))
            (if R.isOneDigitTail then ir.macOneAcc st else ir.macDigitsAcc st) Lr
            (ir.macTailParts st).lhs
      | _ => false
  | .lowLookup => !R.grouped.isSome && !R.isOneDigitTail &&
      match b with
      | .mem _ [.leaf l] (.range _) (.lookup _) => l == ir.macLow st
      | _ => false
  | .topLookup => !R.grouped.isSome && !R.isOneDigitTail &&
      match b with
      | .mem _ [D] (.range _) (.lookup _) => D.beq (ir.macTop st)
      | _ => false
  | .wrap => !R.grouped.isSome && !R.isOneDigitTail &&
      match b with
      | .mem _ [D] (.range _) _ => D.beq (ir.macWrapExpr st)
      | _ => false

/-- **The facts of a MAC check over a field of characteristic `2` with its tail, at the
certificate's generators `G`** (`TwoMacC`): a cross-field `equal` with both blinds, the check's
facts at the site's tail (`macTwoFieldAtB`), the tail (`macTailTwoB`); the tag late; the operands
reading no late value; the blind the tag's pad copy; the cross-field `equal` a source predicate. -/
structure TwoMacFactsC (G : Gens) (st : MacSite) : Prop where
  lt : st.pid < ir.predicates.length
  cross : ir.isCrossB st.pid = true
  blind : (ir.macCross st.pid).real.blind.isSome = true
  blindX : (ir.macCross st.pid).real.blindX.isSome = true
  sideOk : ir.macTwoFieldAtB primeNodes st.pid (ir.siteDom st) (ir.siteOp st) (ir.macBlind st)
    (ir.macCross st.pid).real (ir.twoTail st) = true
  tail : ir.macTailTwoB st.pid (ir.siteDom st) (ir.siteOp st) (ir.macBlind st)
    (ir.macCross st.pid).real (ir.twoTail st) = true
  tagGen : G.at (ir.macCross st.pid).real.tag = .tag st.pid
  tagNotSource : ¬ ir.IsSourceValue (ir.macCross st.pid).real.tag
  tagLate : ir.IsLate (ir.macCross st.pid).real.tag
  xNoLate : ∀ v ∈ ir.exprNodes (ir.macCross st.pid).x, ir.noLateReadB v = true
  yNoLate : ∀ v ∈ ir.exprNodes (ir.macCross st.pid).y, ir.noLateReadB v = true
  blindCopy : ir.isPadCopyB (ir.macBlind st) (ir.macCross st.pid).real.tag "polynomialBits" = true
  source : ir.inSource (ir.predicate st.pid) = true
  chars : MacChars ir (ir.macCross st.pid).dx (ir.macCross st.pid).dy

/-- **`TwoMacFactsC` is decidable**, as the conjunction of its fields. -/
instance (G : Gens) (st : MacSite) : Decidable (ir.TwoMacFactsC (primeNodes := primeNodes) G st) :=
  decidable_of_iff (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ => ⟨h1, h2, h3, h4, h5, h6,
      h7, h8, h9, h10, h11, h12, h13, h14⟩,
     fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ => ⟨h1, h2, h3, h4, h5, h6,
      h7, h8, h9, h10, h11, h12, h13, h14⟩⟩

variable (ir primeNodes) in
/-- **A MAC check over a field of characteristic `2` with its tail at the generators `G`, as a
check** (`TwoMacFactsC`). -/
def twoMacCB (G : Gens) (st : MacSite) : Bool :=
  decide (ir.TwoMacFactsC (primeNodes := primeNodes) G st)

end

end GordieHowe.RealizedProgram
