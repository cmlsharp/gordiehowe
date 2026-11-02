-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Check
public import GordieHoweNative.Language.RealizedProgram.StructureCheck

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.Annotations`

The definitions of `GordieHowe.Language.RealizedProgram.Annotations` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/RealizedProgram/Annotations.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

/-- **Entry `i` of a packed table** of `w`-bit entries: bits `[w i, w (i + 1))` of `T`. -/
def packedGet (T w i : ℕ) : ℕ := (T >>> (w * i)) % 2 ^ w

/-- **The bit set of a list**: bit `w` set for each entry `w`, one `Nat` operation per entry
(`testBit_bitsOf`). -/
def bitsOf (l : List ℕ) : ℕ := l.foldr (fun w acc => 2 ^ w ||| acc) 0

/-- **Two lists have the same elements**, as a check: their bit sets are equal, so the check
reads each entry once. -/
def sameMemB (a b : List ℕ) : Bool := bitsOf a == bitsOf b

/-- **Lists packed in two tables**: the entries of all lists in `ids` (`idW` bits each), and in
`offs` (`offW` bits each) the position of each list's first entry, list `k` ending where list
`k + 1` starts. -/
structure PackedLists where
  /-- The lists' entries, one after another. -/
  ids : ℕ
  /-- The position of each list's first entry, and the end of the last. -/
  offs : ℕ
  /-- The width of an entry. -/
  idW : ℕ
  /-- The width of a position. -/
  offW : ℕ

/-- **List `k`** of the packed lists. -/
def PackedLists.get (c : PackedLists) (k : ℕ) : List ℕ :=
  let a := packedGet c.offs c.offW k
  (List.range (packedGet c.offs c.offW (k + 1) - a)).map fun t => packedGet c.ids c.idW (a + t)

section Packed

variable (ir : RealizedProgram)

/-- **The packed lists are the shared expressions' values**, as a check: list `k` has the values
shared expression `k` reads directly and those of the earlier lists its references name. -/
def closuresOkB (c : PackedLists) : Bool :=
  allIdx (fun k e => e.refs.all (· < k) &&
    sameMemB (c.get k) (e.directNodes ++ e.refs.flatMap c.get)) ir.exprs 0

end Packed

/-- **The structural annotations of the shared expressions**: packed tables of `maxW`-bit bounds
(entry `k` one past every value the closure of entry `k` reads), `fieldW`-bit field sets (bit `f`
of entry `k`: a value it reads in its own field has field `f`) and `lenW`-bit lengths, and a mask
(bit `k`: every coefficient value the closure of entry `k` reads is public). -/
structure ExprAnn where
  /-- The bounds on the values read. -/
  maxId : ℕ
  /-- The field sets. -/
  fields : ℕ
  /-- The public-coefficient mask. -/
  pub : ℕ
  /-- The lengths. -/
  len : ℕ
  /-- The degrees in the committed cells (`degT cellNdT`). -/
  deg : ℕ
  /-- The vanishing-at-zero mask (`zeroT`). -/
  zero : ℕ
  /-- The width of a bound. -/
  maxW : ℕ
  /-- The width of a field set. -/
  fieldW : ℕ
  /-- The width of a length. -/
  lenW : ℕ
  /-- The width of a degree. -/
  degW : ℕ

namespace ExprAnn

variable (a : ExprAnn)

/-- The bound of entry `k`. -/
def maxAt (k : ℕ) : ℕ := packedGet a.maxId a.maxW k

/-- The field set of entry `k`. -/
def fieldsAt (k : ℕ) : ℕ := packedGet a.fields a.fieldW k

/-- The length of entry `k`. -/
def lenAt (k : ℕ) : ℕ := packedGet a.len a.lenW k

/-- The cell degree of entry `k`. -/
def degAt (k : ℕ) : ℕ := packedGet a.deg a.degW k

/-- Whether entry `k` vanishes at zero. -/
def zeroAt (k : ℕ) : Bool := a.zero.testBit k

end ExprAnn

section Ann

variable (ir : RealizedProgram)

/-- **The annotations' local rules**, at shared expression `k` with expression `e`: its references
are earlier entries; its bound lies above the values it reads directly and the bounds of the
entries it references; its field set holds its own values' fields and those of the entries it
references; it is public only when its coefficient values are and the entries it references
are; its length is `e`'s at the entries' lengths. -/
def annAtB (a : ExprAnn) (k : ℕ) (e : Expr) : Bool :=
  e.refs.all (· < k) &&
    e.directNodes.all (· < a.maxAt k) && e.refs.all (fun j => a.maxAt j ≤ a.maxAt k) &&
    (e.fieldNodes.all fun v => (a.fieldsAt k).testBit (ir.valueFieldT v)) &&
    e.refs.all (fun j => a.fieldsAt j &&& a.fieldsAt k == a.fieldsAt j) &&
    (!a.pub.testBit k ||
      (e.pubNodes.all ir.isPublicT && e.refs.all fun j => a.pub.testBit j)) &&
    a.lenAt k == ir.lenV a.lenAt e

/-- **The annotations' check**: every shared expression passes its local rules. -/
def exprAnnOkB (a : ExprAnn) : Bool := allIdx (ir.annAtB a) ir.exprs 0

end Ann

section DegZero

variable (ir : RealizedProgram)

/-- **The degree and vanishing annotations' local rules**: at shared expression `k`, its cell
degree and its vanishing at zero are `e`'s at the entries' annotations. -/
def degZeroOkB (a : ExprAnn) : Bool :=
  allIdx (fun k e => e.refs.all (· < k) && a.degAt k == e.deg ir.cellNdT a.degAt &&
    a.zeroAt k == e.zeroAtZero a.zeroAt) ir.exprs 0

end DegZero

section WellFormed

variable (ir : RealizedProgram) (a : ExprAnn)

/-- **`closAll Expr.directNodes (· < b)`, through the bounds.** -/
def belowA (b : ℕ) (e : Expr) : Bool :=
  e.directNodes.all (· < b) && e.refs.all fun j => a.maxAt j ≤ b

mutual

/-- **The three node tests in one walk**: `p` on the values `e` reads directly, `q` on those it
reads in its own field, `r` on its coefficient values (`directNodes`, `fieldNodes`, `pubNodes`). -/
def Expr.walk3 (p q r : ℕ → Bool) : Expr → Bool
  | .leaf v => p v && q v
  | .add e e' => Expr.walk3 p q r e && Expr.walk3 p q r e'
  | .sub e e' => Expr.walk3 p q r e && Expr.walk3 p q r e'
  | .scale c e => c.nodes.all (fun v => p v && q v && r v) && Expr.walk3 p q r e
  | .mul e e' => Expr.walk3 p q r e && Expr.walk3 p q r e'
  | .reindex _ e => Expr.walk3 p q r e
  | .concat e e' => Expr.walk3 p q r e && Expr.walk3 p q r e'
  | .linear rows e =>
    (rows.flatMap (·.flatMap fun t => t.2.nodes)).all (fun v => p v && q v && r v) &&
      Expr.walk3 p q r e
  | .prod _ e => Expr.walk3 p q r e
  | .mux b t e => Expr.walk3 p q r b && Expr.walk3 p q r t && Expr.walk3 p q r e
  | .apply op e =>
    op.operands.all (fun v => p v && q v) && op.pubOperands.all r &&
      op.foreignOperands.all (fun v => p v && r v) && Expr.walk3 p q r e
  | .ref _ => true
  | .logic _ _ args => Expr.walk3List p q r args

/-- `Expr.walk3` on a list. -/
def Expr.walk3List (p q r : ℕ → Bool) : List Expr → Bool
  | [] => true
  | e :: es => Expr.walk3 p q r e && Expr.walk3List p q r es

end

/-- **`exprOkA` in one walk** of the expression and one pass over its references. -/
def exprOkF (f : ℕ) (e : Expr) : Bool :=
  e.refs.all (· < ir.exprs.length) &&
    Expr.walk3 (· < ir.values.length) (fun v => ir.valueFieldT v == f) ir.isPublicT e &&
    e.refs.all (fun j => a.maxAt j ≤ ir.values.length &&
      (a.fieldsAt j == 0 || a.fieldsAt j == 1 <<< f) && a.pub.testBit j) &&
    ir.shapeOkV a.lenAt e

/-- **`kindOkB`, through the annotations.** -/
def kindOkA (v : ℕ) : Kind → Bool
  | .pub (.expr e) => ir.exprOkF a (ir.valueFieldT v) e && belowA a v e
  | .bound e => ir.exprOkF a (ir.valueFieldT v) e && belowA a ir.values.length e
  | k => ir.kindOkB v k

/-- **`lensOkB`, through the annotations' lengths.** -/
def lensOkA : PredBody → Bool
  | .equal _ e e' _ => ir.lenV a.lenAt e == ir.lenV a.lenAt e'
  | .mem _ _ _ _ => true
  | .mod _ _ e e' _ => ir.lenV a.lenAt e == ir.lenV a.lenAt e'
  | .cross _ x _ y _ _ => ir.lenV a.lenAt x == ir.lenV a.lenAt y

/-- **`predOkB`, through the annotations.** -/
def predOkA (b : PredBody) : Bool :=
  b.exprs.all (fun de => de.1 < ir.domains.length && ir.exprOkF a (ir.domainField de.1) de.2) &&
    ir.lensOkA a b

/-- **`wellFormedB`, through the annotations** (checked by `exprAnnOkB`). -/
def wellFormedA : Bool :=
  decide (∀ d ∈ ir.domains, d.field < ir.fields.length) &&
    allIdx (fun v x => x.domain < ir.domains.length && ir.kindOkA a v x.kind) ir.values 0 &&
    allIdx (fun _ e => ir.shapeOkV a.lenAt e) ir.exprs 0 &&
    ir.predicates.all (fun p => ir.predOkA a p.body) &&
    decide (∀ c ∈ ir.challenges, ir.ChallengeOk c) &&
    allIdx (fun _ x => ir.fieldOkV x) ir.values 0

end WellFormed

section Targets

variable (ir : RealizedProgram) (a : ExprAnn) (c : PackedLists) (S : Structure)

/-- `closAll Expr.directNodes`, through the packed closures. -/
def closP (p : ℕ → Bool) (e : Expr) : Bool :=
  e.directNodes.all p && e.refs.all fun k => (c.get k).all p

/-- **`batchAdmitsB`, through the annotations.** -/
def batchAdmitsA (pid d b : ℕ) (e e' : Expr) : Bool :=
  let B := ir.batch b
  let p := (ir.field (ir.domainField d)).characteristic
  decide (b < ir.batches.length ∧ B.domain = d) && ir.inPartsB b pid &&
    closP c ir.isBatchNodeT e && closP c ir.isBatchNodeT e' &&
    decide (1 ≤ B.degree) && decide (e.deg ir.cellNdT a.degAt ≤ B.degree) &&
    decide (e'.deg ir.cellNdT a.degAt ≤ B.degree) && e.zeroAtZero a.zeroAt &&
    e'.zeroAtZero a.zeroAt &&
    decide (B.skipDomain = skipDomainName p ∧ SkipFits B.degree B.width p) &&
    decide (ir.lenV a.lenAt e ≤ B.operands.lane * B.instances) &&
    decide (B.operands.lane * B.instances ≤ 2 ^ B.rounds * B.width)

/-- **`gkrAdmitsB`, through the packed closures.** -/
def gkrAdmitsA (pid d cc : ℕ) (e e' : Expr) : Bool :=
  decide (cc < ir.circuits.length ∧ (ir.circuit cc).domain = d) &&
    natMem (ir.circuitT.getD cc default).preds pid &&
    closP c (fun v => isCircuitInputT (ir.circuitT.getD cc default) v (ir.valueT v).kind) e &&
    closP c (fun v => isCircuitInputT (ir.circuitT.getD cc default) v (ir.valueT v).kind) e'

/-- **`gkrAdmitsA` reading the circuit's lists**: the code compiled for `gkrAdmitsA`
(`gkrAdmitsA_csimp`). Compiled code would build the circuits' sets (`circuitT`) again at every
value the closures read; it reads the circuit's predicates and input blocks instead. -/
def gkrAdmitsAC (pid d cc : ℕ) (e e' : Expr) : Bool :=
  let C := ir.circuit cc
  decide (cc < ir.circuits.length ∧ C.domain = d) && C.predicates.contains pid &&
    closP c (fun v => isCircuitInputL C v (ir.valueT v).kind) e &&
    closP c (fun v => isCircuitInputL C v (ir.valueT v).kind) e'

@[csimp] theorem gkrAdmitsA_csimp : @gkrAdmitsA = @gkrAdmitsAC := by
  funext ir c pid d cc e e'
  simp only [gkrAdmitsA, gkrAdmitsAC]
  by_cases h : cc < ir.circuits.length
  · simp only [ir.circuitT_getD h, circuitSets_preds, natMem_natSet, isCircuitInputT_circuitSets]
  · simp [h]

/-- **The realized target `q` of predicate `pid` admits the field equation `e = e'` of domain
`d`, at the structure records' route of `pid`** (`Route.realized q js`: the conversions in
mismatch order, `realizedAdmitsAtB`). -/
def realizedAtS (pid d : ℕ) (e e' : Expr) (q : ℕ) : Bool :=
  match (NatTrie.ofList S.routes).get? pid with
  | some (.realized q' js) => q' == q && ir.realizedAdmitsAtB d e e' q js
  | _ => false

/-- **`targetAdmitsB`, through the annotations**; a realized target at the structure records'
route of `pid` (`realizedAtS`). -/
def targetAdmitsA (pid d : ℕ) (e e' : Expr) : Target → Bool
  | .affine => decide (e.deg ir.cellNdT a.degAt ≤ 1) && decide (e'.deg ir.cellNdT a.degAt ≤ 1)
  | .quadratic => ir.isQuadraticT e e'
  | .batch b => ir.batchAdmitsA a c pid d b e e'
  | .gkr cc => ir.gkrAdmitsA c pid d cc e e'
  | .realized q => ir.realizedAtS S pid d e e' q

/-- **`bodyAdmittedB`, through the annotations.** -/
def bodyAdmittedA (pid : ℕ) : PredBody → Bool
  | .equal d e e' t => ir.targetAdmitsA a c S pid d e e' t
  | .mem _ _ _ _ => true
  | .mod d q e e' real =>
    (q != 0 || real.target.isSome) &&
      match real.target with
      | some t => ir.targetAdmitsA a c S pid d e e' t
      | none => true
  | .cross _ _ _ _ _ _ => true

/-- **`targetsB`, through the annotations.** -/
def targetsA : Bool :=
  allIdx (fun pid p => ir.bodyAdmittedA a c S pid p.body) ir.predicates 0 &&
    allIdx (fun cc C => C.predicates.all fun pid =>
      decide (pid < ir.predicates.length ∧
        PredBody.target (ir.predT.getD pid default).body = some (.gkr cc))) ir.circuits 0 &&
    decide (∀ cc ∈ ir.circuits, CircuitLaidOut cc)

end Targets

end GordieHowe.RealizedProgram
