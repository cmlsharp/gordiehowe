-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Completeness.Honest
public import GordieHoweNative.Language.Honest.CheckP

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Completeness.Check`

The definitions of `GordieHowe.Language.Completeness.Check` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Completeness/Check.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- **Whether a generator is a static histogram's**, decidably. -/
instance (x : Gen) : Decidable (∀ t g, x ≠ .staticHist t g) := by
  cases x
  case staticHist t g => exact isFalse fun h => h t g rfl
  all_goals exact isTrue fun _ _ h => Gen.noConfusion h

/-- **Whether a generator is a late histogram's**, decidably. -/
instance (x : Gen) : Decidable (∀ t g, x ≠ .lateHist t g) := by
  cases x
  case lateHist t g => exact isFalse fun h => h t g rfl
  all_goals exact isTrue fun _ _ h => Gen.noConfusion h

section

variable (ir : RealizedProgram)

instance (G : Gens) (t g h : ℕ) : Decidable (ir.StaticGroupFactsC G t g h) :=
  decidable_of_iff (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _)
    ⟨fun ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩,
     fun h => ⟨h.cell, h.size, h.field, h.notSource, h.own, h.needles, h.rows, h.packed⟩⟩

/-- **A two-sided or digit lookup `q` has one record, a range and its facts at the generators `G`**:
when the generator of its first digit names a quotient digit (`Gens.commOf?`), the committed digits
of that quotient digit (`commLookupCB`), else its digits generated as its digits
(`DigitLookupFactsC`), as a check whose failure names the lookup (`lookupShape`, `commLookup`,
`lookupFacts`). -/
def digitLookupCE (G : Gens) (q : ℕ) : Except StructFailure Unit :=
  match lookupOf? (ir.predicateT q).body with
  | some r =>
    match r.kind == .twoSided || r.kind == .digits with
    | false => .ok ()
    | true =>
      match (ir.predicateT q).body with
      | .mem d [rec] (.range N) (.lookup r') =>
        match G.commOf? r' with
        | some (m, j) => Twin.guardE (ir.commLookupCB G q m j) ⟨q, 0, .commLookup⟩
        | none => Twin.guardE (decide (ir.DigitLookupFactsC G q d rec N r')) ⟨q, 0, .lookupFacts⟩
      | _ => .error ⟨q, 0, .lookupShape⟩
  | none => .ok ()

/-- `digitLookupCE`'s verdict. -/
def digitLookupCB (G : Gens) (q : ℕ) : Bool := Twin.okB (ir.digitLookupCE G q)

variable (primeNodes : ℕ → List String) in
/-- **A MAC site's facts**: the MAC check over a field of characteristic `2` where the site's
domain has it, else the MAC, tail and interval facts. -/
def siteCB (S : Structure) (G : Gens) (st : MacSite) : Bool :=
  if ir.charOf (ir.domainField (ir.siteDom st)) = 2 then ir.twoMacCB primeNodes G st
  else ir.macBaseCB primeNodes S G st && ir.macTailCB G st && ir.macIvlB primeNodes S st

/-- **The facts of site `i` of `macSite` record `g`** (`siteCB` at the site `st`), as the shared
verdicts of a certificate reader. -/
def CReader.siteCB (ir : RealizedProgram) [r : CReader] (g i : ℕ) (st : MacSite) : Bool :=
  if ir.charOf (ir.domainField (ir.siteDom st)) = 2 then r.site .two g i
  else r.site .base g i && r.site .tail g i && r.site .ivl g i

/-- **A cross-field `equal` `q` has a checked site** (`CompletionFacts.macs`), at a certificate
reader: its `macSite` record (the record whose first predicate is `q`, `Structure.gadgetAt`) has a
`y`-side site (`ySlot`) of `q` whose facts check (`CReader.siteCB`). -/
def CReader.macCB (ir : RealizedProgram) [r : CReader] (S : Structure) (q : ℕ) : Bool :=
  !ir.isCrossB q ||
    match S.gadgetAt.get? q with
    | some g =>
      match ir.macSiteAt S g (ir.ySlot q) with
      | some st => st.pid == q && CReader.siteCB ir g (ir.ySlot q) st
      | none => false
    | none => false

variable (primeNodes : ℕ → List String) in
/-- **A cross-field `equal` `q` has a checked site** (`CompletionFacts.macs`; `CReader.macCB` at
the program): its `macSite` record has a `y`-side site (`ySlot`) of `q` whose facts check
(`siteCB`). -/
def macCB (S : Structure) (G : Gens) (q : ℕ) : Bool :=
  @CReader.macCB ir (CReader.ofProgram ir primeNodes S G) S q

/-- **The completeness checks at predicate `q`**, at a certificate reader: the source values'
intervals read source predicates, a two-sided or digit lookup with its facts, a cross-field `equal`
with its MAC. -/
def CReader.predCB (ir : RealizedProgram) [r : CReader] (S : Structure) (G : Gens) (q : ℕ) : Bool :=
  ir.ivlSourceB q && ir.digitLookupCB G q && CReader.macCB ir S q

variable (primeNodes : ℕ → List String) in
/-- **The completeness checks at predicate `q`** (`CReader.predCB` at the program): the source
values' intervals read source predicates, a two-sided or digit lookup with its facts, a
cross-field `equal` with its MAC. -/
def predCB (S : Structure) (G : Gens) (q : ℕ) : Bool :=
  @CReader.predCB ir (CReader.ofProgram ir primeNodes S G) S G q

/-- **The needles of group `g` of table `t` read only late values of the program that are generated
as no late histogram** (`LateGroupFactsC.needles`), as a check through the reads table at a program
reader. -/
def PReader.needlesLateCB (ir : RealizedProgram) [r : PReader] (G : Gens) (t g : ℕ) : Bool :=
  (ir.members t g).all fun m =>
    (ir.exprNodes (ir.needleExpr m.pred m.needle)).all fun w =>
      (r.reads w).all fun rd =>
        match rd with
        | .late u => decide (u < r.nValues ∧ PReader.IsLate ir u) &&
          decide (∀ t' g', G.at u ≠ .lateHist t' g')
        | _ => true

/-- **The needles of group `g` of table `t` read only late values of the program that are generated
as no late histogram** (`LateGroupFactsC.needles`), as a check through the reads table
(`PReader.needlesLateCB` at the program). -/
def needlesLateCB (G : Gens) (t g : ℕ) : Bool := @PReader.needlesLateCB ir (PReader.ofProgram ir) G t g

/-- **A group with the late histogram `v` and the static histogram `s` has its facts**
(`MixedGroupFactsC`), as a check at a certificate reader: the late members' MAC digits at the MAC
site their predicate's completeness step names (`CReader.mixedMemberCB`; `D`'s step
`macRow g i _`, the site `macSiteAt S g i`). -/
def CReader.mixedGroupCB (ir : RealizedProgram) [r : CReader] (S : Structure) (G : Gens) (D : CDerivations)
    (t g v s : ℕ) : Bool :=
  decide (G.at v = .lateHist t g) && !decide (PReader.IsSourceValue v) &&
    decide (v < r.nValues) && decide (PReader.IsLate ir v) &&
    decide ((r.value v).size ≤ ir.tableSize t) &&
    decide (ir.valueField v = ir.chalField (ir.alphaOf t)) &&
    decide (ir.IsRange t) &&
    decide (ir.StaticGroupFactsC G t g s) && PReader.noLateReadB ir s &&
    (ir.members t g).all (fun m => ir.memberReadsLate m ||
      (ir.exprNodes (ir.needleExpr m.pred m.needle)).all (PReader.noLateReadB ir)) &&
    PReader.needlesLateCB ir G t g &&
    decide (ir.chalField (ir.alphaOf t) < ir.fields.length) &&
    decide (ir.tableSize t ≤ ir.charOf (ir.chalField (ir.alphaOf t))) &&
    (ir.members t g).all (fun m => !ir.memberReadsLate m ||
      match D.derivs[m.pred]? with
      | some [.macRow g' i _] =>
        match ir.macSiteAt S g' i with
        | some st => CReader.mixedMemberCB ir g' i t v st m
        | none => false
      | _ => false)

variable (primeNodes : ℕ → List String) in
/-- **A group with the late histogram `v` and the static histogram `s` has its facts**
(`MixedGroupFactsC`; `CReader.mixedGroupCB` at the program): the late members' MAC digits at the
MAC site their predicate's completeness step names (`mixedMemberCB`). -/
def mixedGroupCB (S : Structure) (G : Gens) (D : CDerivations) (t g v s : ℕ) : Bool :=
  @CReader.mixedGroupCB ir (CReader.ofProgram ir primeNodes S G) S G D t g v s

/-- **The completeness checks at group `g` of table `t`**, at a certificate reader: a late
histogram with its facts, alone (`LateGroupFactsC`) or beside a static one
(`CReader.mixedGroupCB`); without one, a static histogram with its facts (`StaticGroupFactsC`), or
no members. -/
def CReader.groupCB (ir : RealizedProgram) [r : CReader] (S : Structure) (G : Gens) (D : CDerivations) (t g : ℕ) : Bool :=
  match (ir.groupOf t g).lateMult with
  | some v =>
    ((ir.groupOf t g).staticMult.isNone && decide (G.at v = .lateHist t g) &&
      !decide (PReader.IsSourceValue v) && decide (v < r.nValues) && decide (PReader.IsLate ir v) &&
      decide ((r.value v).size = ir.tableSize t) &&
      decide (ir.valueField v = ir.chalField (ir.alphaOf t)) &&
      decide (ir.IsRange t) && PReader.needlesLateCB ir G t g) ||
    match (ir.groupOf t g).staticMult with
    | some s => CReader.mixedGroupCB ir S G D t g v s
    | none => false
  | none =>
    match (ir.groupOf t g).staticMult with
    | none => (ir.members t g).isEmpty
    | some h => decide (ir.StaticGroupFactsC G t g h)

variable (primeNodes : ℕ → List String) in
/-- **The completeness checks at group `g` of table `t`** (`CReader.groupCB` at the program): a late
histogram with its facts, alone (`LateGroupFactsC`) or beside a static one (`mixedGroupCB`);
without one, a static histogram with its facts (`StaticGroupFactsC`), or no members. -/
def groupCB (S : Structure) (G : Gens) (D : CDerivations) (t g : ℕ) : Bool :=
  @CReader.groupCB ir (CReader.ofProgram ir primeNodes S G) S G D t g

/-- **Generator `g` is no MAC tag's** (`Gens.notTagAt`, on the generator). -/
def _root_.GordieHowe.RealizedProgram.Gen.notTag (g : Gen) : Bool :=
  match g with
  | .tag _ => false
  | _ => true

/-- `tagFullCB G v`, on value `x` and generator `g`. -/
def tagFullCV (x : Value) (g : Gen) : Bool :=
  match g with
  | .tag _ =>
    match x.padSpace with
    | .full => true
    | _ => false
  | _ => true

/-- `lateGenCB L v`, on value `x`. -/
def lateGenCV (L : List (ℕ × String)) (x : Value) : Bool :=
  !ir.isLateV x ||
    (ir.padNatV L x && decide (x.domain < ir.domains.length) && !cellValueV x.domain x &&
      ir.lateOfV x.domain x)

/-- `genLateTypeCB L G v`, on value `x` and generator `g`. -/
def genLateTypeCV (L : List (ℕ × String)) (x : Value) (g : Gen) : Bool :=
  !ir.isLateV x || decide (x.role = .source) || !(x.typeSource == .node) ||
    (g.notTag && ir.natTypedV L x)

/-- `valueCB L G S v`, on value `x` and generator `g`, the generators read through `GT` and the
bound values' records through `T`. -/
def valueCV (L : List (ℕ × String)) (GT : NatTrie Gen) (T : NatTrie ℕ) (v : ℕ) (x : Value)
    (g : Gen) : Bool :=
  srcNoPadCopyV v x && srcNoMessageV v x && ir.srcLatePadV v x && ir.boundRecsV GT T v x &&
    tagFullCV x g && ir.lateGenCV L x && ir.cellV L v x && ir.realTypeV L v x &&
    ir.genLateTypeCV L x g

/-- `histCoveredCB G MT rs v`, on generator `g`, the other generators read through `GT`, at a
program reader. -/
def PReader.histCoveredCV (ir : RealizedProgram) [r : PReader] (GT : NatTrie Gen) (MT : NatTrie ℕ) (rs : List Read)
    (g : Gen) : Bool :=
  match g with
  | .lateHist t g => (ir.members t g).all fun m =>
      (ir.exprNodes (ir.needleExpr m.pred m.needle)).all fun w =>
        PReader.srcCoveredB ir MT rs w && (r.reads w).all fun rd =>
          match rd with
          | .late u => PReader.genCoveredCB ir [GT.getD u default] MT rs 0
          | _ => true
  | _ => true

/-- `histCoveredCB G MT rs v`, on generator `g`, the other generators read through `GT`
(`PReader.histCoveredCV` at the program). -/
def histCoveredCV (GT : NatTrie Gen) (MT : NatTrie ℕ) (rs : List Read) (g : Gen) : Bool :=
  @PReader.histCoveredCV ir (PReader.ofProgram ir) GT MT rs g

/-- `genReadsCoveredCB G`'s check at value `v`, on value `x` and generator `g`, the other
generators read through `GT`, at a program reader. -/
def PReader.coveredCV (ir : RealizedProgram) [r : PReader] (GT : NatTrie Gen) (MT : NatTrie ℕ) (_ : ℕ) (x : Value)
    (g : Gen) : Bool :=
  !ir.isLateV x ||
    (PReader.genCoveredCB ir [g] MT x.reads 0 && PReader.histCoveredCV ir GT MT x.reads g)

/-- `genReadsCoveredCB G`'s check at value `v`, on value `x` and generator `g`, the other
generators read through `GT` (`PReader.coveredCV` at the program). -/
def coveredCV (GT : NatTrie Gen) (MT : NatTrie ℕ) (v : ℕ) (x : Value) (g : Gen) : Bool :=
  @PReader.coveredCV ir (PReader.ofProgram ir) GT MT v x g

/-- `typedNoLateV v x`, on the reads `rs` of value `v` (`readsL`'s entry, zipped with the values),
not read through the table, at a program reader. -/
def PReader.typedNoLateL (ir : RealizedProgram) [r : PReader] (_ : ℕ) (x : Value) (rs : List Read) : Bool :=
  !(x.typeSource == .node) || ir.isLateV x ||
    rs.all fun rd =>
      match rd with
      | .late u => !(decide (u < r.nValues) && ir.isLateV (r.value u))
      | _ => true

/-- `typedNoLateV v x`, on the reads `rs` of value `v` (`readsL`'s entry, zipped with the values),
not read through the table (`PReader.typedNoLateL` at the program). -/
def typedNoLateL (v : ℕ) (x : Value) (rs : List Read) : Bool :=
  @PReader.typedNoLateL ir (PReader.ofProgram ir) v x rs

/-- **The checker of a completeness certificate** at the nodes `L` and the structure records `S`,
at a certificate reader. -/
def CReader.completionB (ir : RealizedProgram) [r : CReader] (primeNodes : ℕ → List String)
    (L : List (ℕ × String)) (S : Structure) (G : Gens) (D : CDerivations) : Bool :=
  allIdx2 (ir.valueCV L (toTrie G) S.boundRecTab) .none ir.values G 0 &&
    ir.allPredsB (CReader.predCB ir S G) &&
    ir.allGroupsB (CReader.groupCB ir S G D) && allIdx ir.boundNoCopyV ir.values 0 &&
    allIdx2 (PReader.coveredCV ir (toTrie G) S.messageTab) .none ir.values G 0 &&
    allIdx2 (PReader.typedNoLateL ir) [] ir.values r.readsL 0 && ir.allPredsB ir.blindsB &&
    ir.allGroupsB (PReader.staticGroupNoLateB ir) && CReader.cderivsB ir primeNodes S G D &&
    allIdx ir.typeRoleV ir.values 0 && ir.messageRecsB S

/-- **The checker of a completeness certificate** at the nodes `L` and the structure records `S`
(`CReader.completionB` at the program). -/
def completionB (primeNodes : ℕ → List String) (L : List (ℕ × String)) (S : Structure)
    (G : Gens) (D : CDerivations) : Bool :=
  @CReader.completionB ir (CReader.ofProgram ir primeNodes S G) primeNodes L S G D

/-- **The checker of a completeness certificate, as compiled code runs it**
(`completionB_csimp`): `CReader.completionB` at the context built once (`CCtx.build`). -/
def completionBA (primeNodes : ℕ → List String) (L : List (ℕ × String)) (S : Structure)
    (G : Gens) (D : CDerivations) : Bool :=
  let c := CCtx.build ir primeNodes S G
  @CReader.completionB ir (CReader.ofCtx c) primeNodes L S G D

end

end GordieHowe.RealizedProgram
