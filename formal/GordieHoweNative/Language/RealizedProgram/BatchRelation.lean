-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Check

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.BatchRelation`

The definitions of `GordieHowe.Language.RealizedProgram.BatchRelation` that the certificate
checkers run (the batch forms, their summaries and shapes, and the parts' checks), in the
Mathlib-free library `GordieHoweNative`, which Lake compiles to a shared library
(`precompileModules`): native mode runs the checkers as compiled code. The declarations keep their
names. Their lemmas are in `GordieHowe/Language/RealizedProgram/BatchRelation.lean`, which imports
this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-! ## Batch forms -/

/-- **A coefficient of a batch form**: a sign and a product of constants (naturals of the C++
encoding). -/
structure BCoef where
  /-- The sign is negative. -/
  neg : Bool := false
  /-- The constant factors. -/
  consts : List ℕ := []
  deriving DecidableEq, Repr, Inhabited

namespace BCoef

/-- The product of two coefficients. -/
def mul (a b : BCoef) : BCoef := ⟨xor a.neg b.neg, a.consts ++ b.consts⟩

/-- The negated coefficient. -/
def negate (a : BCoef) : BCoef := ⟨!a.neg, a.consts⟩

/-- The coefficient times the constant `c`. -/
def scale (c : ℕ) (a : BCoef) : BCoef := ⟨a.neg, c :: a.consts⟩

/-- The coefficient `1`. -/
def one : BCoef := ⟨false, []⟩

end BCoef

/-- **A monomial of a batch form**: a coefficient and its factors, atoms. -/
structure BMono where
  /-- The coefficient. -/
  coef : BCoef := BCoef.one
  /-- The factors. -/
  factors : List Expr := []
  deriving Inhabited

namespace BMono

/-- The negated monomial. -/
def negate (m : BMono) : BMono := ⟨m.coef.negate, m.factors⟩

/-- The monomial times the constant `c`. -/
def scale (c : ℕ) (m : BMono) : BMono := ⟨m.coef.scale c, m.factors⟩

/-- The product of two monomials. -/
def mul (m m' : BMono) : BMono := ⟨m.coef.mul m'.coef, m.factors ++ m'.factors⟩

/-- **The monomial with each factor `x` replaced by `h x`** (a view of the monomial, when `h` is a
view). -/
def mapFactors (h : Expr → Expr) (m : BMono) : BMono := ⟨m.coef, m.factors.map h⟩

end BMono

/-- **The index map of the first `n` coordinates**: one run `0, 1, …, n − 1`. -/
def IndexMap.first (n : ℕ) : IndexMap := [(0, 1, n)]

/-- **A factor of the left piece of a concatenation, `n` coordinates, extended by zeros**: `x` on
the first `n` coordinates, `x − x` after them. -/
def Expr.padRight (n : ℕ) (x : Expr) : Expr := .concat (.reindex (IndexMap.first n) x) (.sub x x)

/-- **A factor of the right piece of a concatenation, after `n` zeros**: `x − x` on the first `n`
coordinates (read at the first `n` of `x`), `x` after them. -/
def Expr.padLeft (n : ℕ) (x : Expr) : Expr :=
  .concat (.sub (.reindex (IndexMap.first n) x) (.reindex (IndexMap.first n) x)) x

/-- **Two atoms are one node**: the same shared expression or the same value (the export writes a
node read more than once as a shared expression, so the C++'s shared atoms are these). -/
def Expr.sameAtom : Expr → Expr → Bool
  | .ref a, .ref b => a == b
  | .leaf a, .leaf b => a == b
  | _, _ => false

/-- **What an atom test reads of an expression** (`RealizedProgram.atomSum`): whether every value
it reads passes the test's leaf test and every coefficient value is a constant, and its degree
capped at `2` (the atom test compares it with `1`). -/
structure AtomSum where
  /-- The values pass the leaf test and the coefficients' values have degree `0`. -/
  ok : Bool
  /-- The degree, capped at `2`. -/
  deg : ℕ

namespace AtomSum

/-- **An atom**: its values and coefficients pass, and its degree is at most one. -/
def atom (s : AtomSum) : Bool := s.ok && decide (s.deg ≤ 1)

/-- The summary of a sum, a difference or a concatenation of expressions with summaries `s`, `t`. -/
def join (s t : AtomSum) : AtomSum := ⟨s.ok && t.ok, max s.deg t.deg⟩

/-- The summary of a product of expressions with summaries `s`, `t`. -/
def mul (s t : AtomSum) : AtomSum := ⟨s.ok && t.ok, min (s.deg + t.deg) 2⟩

end AtomSum

section

variable (ir : RealizedProgram)

/-- A node of a batch form at the atom test `atom`: one monomial of degree one when the node is an
atom, `rest` otherwise. -/
def bnode (atom : Expr → Bool) (e : Expr) (rest : Option (List BMono)) : Option (List BMono) :=
  if atom e then some [⟨BCoef.one, [e]⟩] else rest

/-- **The monomials `ms` of a view**, when each has a factor and every factor is an atom (`none`
otherwise). -/
def viewed (atom : Expr → Bool) (ms : List BMono) : Option (List BMono) :=
  if ms.all fun m => !m.factors.isEmpty && m.factors.all atom then some ms else none

/-- **The summary of an expression for an atom test** with leaf test `lf` and value degrees `nd`:
whether every value it reads (`exprNodes`) passes `lf` and every coefficient value (`closure
Expr.coefNodes`) has degree `0`, and its degree (`degOf nd`) capped at `2`. `atomB` and `bitsAtomB`
are the atom tests of such summaries (`atomSum_atom`). -/
def atomSum (lf : ℕ → Bool) (nd : ℕ → ℕ) (e : Expr) : AtomSum :=
  ⟨(ir.exprNodes e).all lf && (ir.closure Expr.coefNodes e).all (nd · == 0),
    min (ir.degOf nd e) 2⟩

/-- **The batch form with its summary, in one walk** (`bpolySum_eq`): `bpoly` at the atom test of
`atomSum lf nd`, each node's summary combined from its children's (`AtomSum.join`,
`AtomSum.mul`) where `bpoly` distributes, so the atom test at a node does not walk the node's
subtree again, and a shared expression's summary read from `rs` (`refSum`). A view's factors are
views of atoms, themselves atoms (`atomSum_padRight`), so a view is checked only for monomials
without factors. -/
def bpolySum (lf : ℕ → Bool) (nd : ℕ → ℕ) (rs : ℕ → AtomSum) :
    Expr → AtomSum × Option (List BMono)
  | .add a b =>
      let ra := bpolySum lf nd rs a
      let rb := bpolySum lf nd rs b
      let s := ra.1.join rb.1
      (s, bnode (fun _ => s.atom) (.add a b) do
        let p ← ra.2
        let q ← rb.2
        pure (p ++ q))
  | .sub a b =>
      let ra := bpolySum lf nd rs a
      let rb := bpolySum lf nd rs b
      let s := ra.1.join rb.1
      (s, bnode (fun _ => s.atom) (.sub a b) do
        let p ← ra.2
        let q ← rb.2
        pure (p ++ q.map BMono.negate))
  | .scale (.const c) a =>
      let ra := bpolySum lf nd rs a
      (ra.1, bnode (fun _ => ra.1.atom) (.scale (.const c) a) do
        let p ← ra.2
        pure (p.map (BMono.scale c)))
  | .mul a b =>
      let ra := bpolySum lf nd rs a
      let rb := bpolySum lf nd rs b
      let s := ra.1.mul rb.1
      (s, bnode (fun _ => s.atom) (.mul a b) do
        let p ← ra.2
        let q ← rb.2
        pure (p.flatMap fun m => q.map m.mul))
  | .reindex idx a =>
      let ra := bpolySum lf nd rs a
      (ra.1, bnode (fun _ => ra.1.atom) (.reindex idx a) do
        let p ← ra.2
        viewed (fun _ => true) (p.map (BMono.mapFactors (.reindex idx))))
  | .concat a b =>
      let ra := bpolySum lf nd rs a
      let rb := bpolySum lf nd rs b
      let s := ra.1.join rb.1
      (s, bnode (fun _ => s.atom) (.concat a b) do
        let p ← ra.2
        let q ← rb.2
        viewed (fun _ => true) (p.map (BMono.mapFactors (Expr.padRight (ir.exprLen a))) ++
          q.map (BMono.mapFactors (Expr.padLeft (ir.exprLen a)))))
  | .ref k =>
      let s := rs k
      (s, bnode (fun _ => s.atom) (.ref k) none)
  | e =>
      let s := ir.atomSum lf nd e
      (s, bnode (fun _ => s.atom) e none)

/-- **The summary of an expression from its shared expressions' summaries `rs`**: its own values
and coefficients tested, and each shared expression's summary read (`sumWith_expr`). -/
def Expr.sumWith (lf : ℕ → Bool) (nd : ℕ → ℕ) (rs : ℕ → AtomSum) (e : Expr) : AtomSum :=
  ⟨e.directNodes.all lf && e.coefNodes.all (nd · == 0) && e.refs.all fun k => (rs k).ok,
    min (e.deg nd fun k => (rs k).deg) 2⟩

/-- **The shared expressions' summaries as bit sets** (`refBits`): bit `k` of `fail` set when entry
`k`'s values or coefficients fail, of `one` when its capped degree is at least one, of `two` when
it is two. A summary is then read by three `Nat.testBit`s. -/
structure RefBits where
  /-- The entries whose values or coefficients fail. -/
  fail : ℕ
  /-- The entries of degree at least one. -/
  one : ℕ
  /-- The entries of degree at least two. -/
  two : ℕ

end

namespace RefBits

/-- **The summary of entry `k`.** -/
def get (t : RefBits) (k : ℕ) : AtomSum :=
  ⟨!t.fail.testBit k, if t.two.testBit k then 2 else if t.one.testBit k then 1 else 0⟩

/-- **The bit sets with entry `k`'s summary `s` added.** -/
def push (t : RefBits) (k : ℕ) (s : AtomSum) : RefBits :=
  ⟨t.fail ||| cond s.ok 0 (2 ^ k), t.one ||| cond (decide (1 ≤ s.deg)) (2 ^ k) 0,
    t.two ||| cond (decide (2 ≤ s.deg)) (2 ^ k) 0⟩

/-- **The bit sets of the summaries of a list of entries**, from position `k` on, the summaries of
the entries before read from the bit sets built so far. -/
def ofExprs (lf : ℕ → Bool) (nd : ℕ → ℕ) : List Expr → ℕ → RefBits → RefBits
  | [], _, t => t
  | e :: es, k, t => ofExprs lf nd es (k + 1) (t.push k (e.sumWith lf nd t.get))

end RefBits

section

variable (ir : RealizedProgram)

/-- **The shared expressions' summaries as bit sets**, in one walk of the entries
(`refBits_get`). -/
def refBits (lf : ℕ → Bool) (nd : ℕ → ℕ) : RefBits := RefBits.ofExprs lf nd ir.exprs 0 ⟨0, 0, 0⟩

/-- **The summary of shared expression `k`** (`refSum_eq`): read from `refBits` when the shared
expressions read only earlier entries and `k` is one, computed from its closure otherwise. -/
def refSum (lf : ℕ → Bool) (nd : ℕ → ℕ) (k : ℕ) : AtomSum :=
  if ir.refsOrderedB && decide (k < ir.exprs.length) then (ir.refBits lf nd).get k
  else ir.atomSum lf nd (.ref k)

/-- **A value a batch operand on columns may read**, at its record (`batchLeafOk_eq`). -/
def batchLeafV (x : Value) : Bool :=
  match x.kind with
  | .priv => x.phase == 0
  | .padCopy _ _ => true
  | .constant _ => true
  | _ => false

/-- **A value of degree one in the committed cells**, at its record (`cellNd_eq`): a committed value
or a late value. -/
def cellNdV (x : Value) : Bool := x.isCommittedB || x.kind.isLate

/-- **The values a batch operand on columns may not read**, as a bit set (`failBits`), for
`batchLeafB`. -/
def batchLeafFail : ℕ := failBits (fun _ x => batchLeafV x) ir.values 0

/-- **`batchLeafOk`, as a test** (`batchLeafB_eq`): one `Nat.testBit` of `batchLeafFail`, where
`batchLeafOk` looks the value up in the values' trie. -/
def batchLeafB (v : ℕ) : Bool := bitTest ir.batchLeafFail ir.values.length (batchLeafV default) v

/-- **The values of degree zero in the committed cells**, as a bit set (`failBits`), for
`cellNdB`. -/
def cellFail : ℕ := failBits (fun _ x => !cellNdV x) ir.values 0

/-- **`cellNd`, as a test** (`cellNdB_eq`): one `Nat.testBit` of `cellFail`. -/
def cellNdB (v : ℕ) : ℕ := cond (bitTest ir.cellFail ir.values.length (!cellNdV default) v) 0 1

/-- **Place a factor among the atoms**: its position, appending it when no atom is the same node
(`Expr.sameAtom`). -/
def placeAtom (atoms : List Expr) (f : Expr) : List Expr × ℕ :=
  match atoms.findIdx? (Expr.sameAtom · f) with
  | some j => (atoms, j)
  | none => (atoms ++ [f], atoms.length)

/-- **Place a monomial's factors among the atoms**: each factor's position, in order. -/
def placeFactors : List Expr → List Expr → List Expr × List ℕ
  | atoms, [] => (atoms, [])
  | atoms, f :: fs => ((placeFactors (placeAtom atoms f).1 fs).1,
      (placeAtom atoms f).2 :: (placeFactors (placeAtom atoms f).1 fs).2)

/-- **Place the monomials**: each monomial's factors among the atoms, the monomial recorded as its
coefficient and the factors' positions. -/
def placeMonos : List Expr → List BMono → List Expr × List (BCoef × List ℕ)
  | atoms, [] => (atoms, [])
  | atoms, m :: ms => ((placeMonos (placeFactors atoms m.factors).1 ms).1,
      (m.coef, (placeFactors atoms m.factors).2) ::
        (placeMonos (placeFactors atoms m.factors).1 ms).2)

/-- **An operand of a batch** (`batch_form`): one atom (a factor of a quadratic monomial), or the
linear part, signed constant multiples of atoms. -/
inductive BOperand where
  /-- An atom. -/
  | atom (e : Expr)
  /-- The linear part. -/
  | lin (terms : List (BCoef × Expr))
  /-- A constant-zero operand, added by the padding (`Pad`). -/
  | zero
  deriving Inhabited

/-- **The padding of a batch form** (`batch_form` with `pad_affine`, which `place_predicates`
passes): an affine form is written `a b + c` with `a`, `b` two constant-zero operands and `c` its
linear part, and a lone product `a b` of two distinct operands without a linear part is written
`a b + c` with `c` a constant-zero operand, so that either joins a batch of the degree-two shape
`a b + c`. -/
inductive Pad where
  /-- No padding. -/
  | none
  /-- The quadratic monomial `0 · 0` on two constant-zero operands, placed after the atoms. -/
  | zeroQuad
  /-- The linear monomial on a constant-zero operand, the last. -/
  | zeroLin
  deriving DecidableEq, Inhabited

/-- **The linear monomial of a shape** (`FieldRelation`'s monomial of degree one): the position of
its operand and its sign. The operand is the linear part itself (its own operand, the last, sign
positive), or an atom of the quadratic monomials that the linear part, one term with coefficient
`±1`, reuses. -/
structure LinOperand where
  /-- The operand's position. -/
  pos : ℕ
  /-- The sign is negative. -/
  neg : Bool
  deriving DecidableEq, Inhabited

/-- **The shape of a batch form** (`BatchForm::shape_key`): the operand count and the monomials,
each a coefficient and its factors' operand positions (with repetition): the monomials of degree at
least two on the atoms, the padding's, and the linear monomial (its operand's position, the
coefficient `±1`). -/
structure Shape where
  /-- The operand count. -/
  k : ℕ
  /-- The monomials. -/
  monos : List (BCoef × List ℕ)
  deriving DecidableEq, Inhabited

/-- **The form of a part** of a batch: the distinct atoms of its monomials of degree at least two,
those monomials on them, and its linear part. -/
structure PartForm where
  /-- The atoms of the monomials of degree at least two. -/
  atoms : List Expr
  /-- The monomials of degree at least two: coefficient and the factors' atom positions. -/
  monos : List (BCoef × List ℕ)
  /-- The linear part. -/
  lin : List (BCoef × Expr)
  /-- The padding. -/
  pad : Pad := .none
  deriving Inhabited

end

namespace PartForm

variable (pf : PartForm)

/-- The part has a linear part. -/
def hasLin : Bool := !pf.lin.isEmpty

/-- **The atom the linear part reuses**: when the linear part is one term with coefficient `±1` (no
constant factor) on an atom of the quadratic monomials (`Expr.sameAtom`), that atom's position and
the sign. The C++ writes the Boolean checks `v · v = v` as the relation `x·x − x` on one operand
(`compiler/compiled_domain.h`, the field batch of the Boolean checks), and `batch_form` reuses
the operand of an atom when the linear part is that atom with coefficient one (`op(*lin)`). -/
def reused : Option LinOperand :=
  match pf.lin with
  | [t] => if t.1.consts = [] then
      (pf.atoms.findIdx? (Expr.sameAtom · t.2)).map fun j => ⟨j, t.1.neg⟩
    else none
  | _ => none

/-- **The linear part is its own operand**: it has one and reuses no atom. -/
def linOwn : Bool := pf.hasLin && pf.reused.isNone

/-- **The constant-zero operands of the quadratic padding**: two with `Pad.zeroQuad`, none
otherwise. -/
def zeroOps : List BOperand := if pf.pad = .zeroQuad then [.zero, .zero] else []

/-- **The last operand**: the linear part when it is its own operand, a constant zero with
`Pad.zeroLin`, none otherwise. -/
def tailOps : List BOperand :=
  if pf.linOwn then [.lin pf.lin] else if pf.pad = .zeroLin then [.zero] else []

/-- **The operands of a part**: its atoms, the padding's constant zeros (`zeroOps`), then its
linear part when it is its own operand or the padding's constant zero (`tailOps`). -/
def operands : List BOperand := pf.atoms.map .atom ++ pf.zeroOps ++ pf.tailOps

/-- **The padding's quadratic monomial**: with `Pad.zeroQuad`, coefficient one on the two
constant-zero operands after the atoms. -/
def padMonos : List (BCoef × List ℕ) :=
  if pf.pad = .zeroQuad then [(BCoef.one, [pf.atoms.length, pf.atoms.length + 1])] else []

/-- **The linear monomial of a part**: the reused atom's position and sign (`reused`), or else the
last operand with sign positive, when the part has a linear part; the last operand, a constant zero,
with `Pad.zeroLin`; none otherwise. -/
def linOperand : Option LinOperand :=
  if pf.hasLin then some (pf.reused.getD ⟨pf.atoms.length + pf.zeroOps.length, false⟩)
  else if pf.pad = .zeroLin then some ⟨pf.atoms.length + pf.zeroOps.length, false⟩ else none

/-- **The linear monomial of a part as a monomial**: its operand's position, the coefficient `±1`. -/
def linMono : List (BCoef × List ℕ) :=
  match pf.linOperand with
  | some l => [(⟨l.neg, []⟩, [l.pos])]
  | none => []

/-- **The shape of a part**: the operands; the monomials of degree at least two, the padding's and
the linear monomial. -/
def shape : Shape := ⟨pf.operands.length, pf.monos ++ pf.padMonos ++ pf.linMono⟩

end PartForm

section

variable (ir : RealizedProgram)

/-- **The padding of a form** (`batch_form`'s `pad_affine`): `Pad.zeroQuad` when there are no
monomials of degree at least two and a linear part; `Pad.zeroLin` when there is no linear part and
one monomial, a product of two distinct atoms; `Pad.none` otherwise. -/
def padOf (monos : List (BCoef × List ℕ)) (low : List BMono) : Pad :=
  if monos.isEmpty && !low.isEmpty then .zeroQuad
  else if low.isEmpty && (match monos with | [(_, [a, b])] => a != b | _ => false) then .zeroLin
  else .none

/-- **A leaf of a zero constant**: a leaf of a constant value of a field of the program whose
entries are all `0` (the export writes `assert_zero(e)` as `e = c` with such a constant `c`;
`batch_form` reads a constant node as the constant monomial and drops a monomial whose coefficient
is zero, `zero_coef`). -/
def zeroLeafB : Expr → Bool
  | .leaf v => decide (ir.valueField v < ir.fields.length) &&
      match (ir.value v).kind with
      | .constant es => es.all (· == 0)
      | _ => false
  | _ => false

/-- **A monomial the batch form drops**: one whose factors are leaves of zero constants
(`zeroLeafB`; on a monomial of degree one, `batch_form`'s `zero_coef`). -/
def zeroMonoB (m : BMono) : Bool := m.factors.all ir.zeroLeafB

/-- **The form of a part** with sides `e`, `e'`: the batch forms of `e` and of `−e'`; the monomials
of degree other than one placed on their atoms (`placeMonos`), the monomials of degree one as the
linear part, without those on a zero constant (`zeroMonoB`, `batch_form`'s `zero_coef`), padded by
`padOf`; the batch forms of the sides are `bp`'s (`bpoly` at an atom test). -/
def partForm (bp : Expr → Option (List BMono)) (e e' : Expr) : Option PartForm := do
  let p ← bp e
  let q ← bp e'
  let ms := p ++ q.map BMono.negate
  let high := ms.filter (·.factors.length != 1)
  let low := (ms.filter (·.factors.length == 1)).filter fun m => !ir.zeroMonoB m
  pure ⟨(placeMonos [] high).1, (placeMonos [] high).2,
    low.map fun m => (m.coef, m.factors.getD 0 default), padOf (placeMonos [] high).2 low⟩

end

namespace Shape

/-- **The monomials of a shape on operands shifted by `o`.** -/
def shift (sh : Shape) (o : ℕ) : List (BCoef × List ℕ) :=
  sh.monos.map fun c => (c.1, c.2.map (· + o))

/-- **`Ok`, decided.** -/
def okB (sh : Shape) (D : ℕ) : Bool :=
  sh.monos.all fun c => decide (c.2 ≠ []) && decide (c.2.length ≤ D) && c.2.all (· < sh.k)

/-- **The first operand of part `j`** when parts of shapes `sh` lie side by side: the operand counts
of the parts before it. -/
def offset (sh : ℕ → Shape) (j : ℕ) : ℕ := ((List.range j).map fun j' => (sh j').k).sum

/-- **The shape of a batch's relation from its `n` parts' shapes `sh`**: the first part's, or, when
the batch merges its parts, the parts' monomials on their operands side by side (`Σ_p γ^p Q_p` at
`γ = 1`). -/
def batched (merged : Bool) (n : ℕ) (sh : ℕ → Shape) : Shape :=
  if merged then ⟨offset sh n, (List.range n).flatMap fun j => (sh j).shift (offset sh j)⟩
  else sh 0

end Shape

section

variable (ir : RealizedProgram)

/-- **The sides of a predicate of domain `d` placed in batch `b`**: a field `equal`'s with target
`batch(b)`, or a `mod_0`'s field equation's with that target. -/
def PredBody.batchSides (body : PredBody) (d b : ℕ) : Option (Expr × Expr) :=
  match body with
  | .equal d' e e' (.batch b') => if d' = d ∧ b' = b then some (e, e') else none
  | .mod d' 0 e e' real => if d' = d ∧ real.target = some (.batch b) then some (e, e') else none
  | _ => none

/-- The predicate of part `j` of batch `b`. -/
def partPred (b j : ℕ) : ℕ := (ir.batch b).parts.getD j 0

/-- **The form of predicate `pr` as a part of batch `b`** in domain `d` at the batch forms `bp`. -/
def predForm (bp : Expr → Option (List BMono)) (d b : ℕ) (pr : Predicate) : Option PartForm :=
  (pr.body.batchSides d b).bind fun s => ir.partForm bp s.1 s.2

/-- **The shape of predicate `pr` as a part of batch `b`.** -/
def predShape (bp : Expr → Option (List BMono)) (d b : ℕ) (pr : Predicate) : Shape :=
  ((ir.predForm bp d b pr).map PartForm.shape).getD default

/-- **The coordinates of predicate `pr` as a part of batch `b`**: those of its left side. -/
def predLen (d b : ℕ) (pr : Predicate) : ℕ :=
  ((pr.body.batchSides d b).map fun s => ir.exprLen s.1).getD 0

/-- **The sides of part `j` of batch `b`** in domain `d`. -/
def partSides (d b j : ℕ) : Option (Expr × Expr) :=
  (ir.predicate (ir.partPred b j)).body.batchSides d b

/-- **The instances of part `j`**: the coordinates of its left side. -/
def partLen (d b j : ℕ) : ℕ := ((ir.partSides d b j).map fun s => ir.exprLen s.1).getD 0

/-- **Batch `b` merges its parts** (`batch.h`, `FieldOperands::relation(gamma)`): its `merged`
flag is set. -/
def merged (b : ℕ) : Bool := (ir.batch b).merged

/-- **The shape of batch `b`'s relation at the batch forms `bp`**: `relShape` from the parts'
predicates' shapes (`relShape_eq_batchShape`). -/
def batchShape (bp : Expr → Option (List BMono)) (d b : ℕ) : Shape :=
  Shape.batched (ir.merged b) (ir.batch b).parts.length fun j =>
    ir.predShape bp d b (ir.predicate (ir.partPred b j))

/-- **A part's check at its predicate `pr`** (`PartsOk` at one part): a form, a relation of
degree at most the batch's, and, without a merging challenge, the shape `sh0`, with one, the
coordinates `l0`. -/
def partPredOkB (bp : Expr → Option (List BMono)) (d b : ℕ) (sh0 : Shape) (l0 : ℕ)
    (pr : Predicate) : Bool :=
  match ir.predForm bp d b pr with
  | some pf => pf.shape.okB (ir.batch b).degree && (ir.merged b || pf.shape == sh0) &&
      (!ir.merged b || ir.predLen d b pr == l0)
  | none => false

/-- **`PartsOk`, decided** in one walk of the batch's parts, in order, each part's predicate
checked against the first part's shape and coordinates (`partPredOkB`). -/
def partsOkB (bp : Expr → Option (List BMono)) (d b : ℕ) : Bool :=
  match (ir.batch b).parts with
  | [] => false
  | p0 :: ps => (p0 :: ps).all fun p => decide (p < ir.predicates.length) &&
      ir.partPredOkB bp d b (ir.predShape bp d b (ir.predicate p0))
        (ir.predLen d b (ir.predicate p0)) (ir.predicate p)

end

end GordieHowe.RealizedProgram
