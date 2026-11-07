-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.ValueShape
public import GordieHoweNative.Language.RealizedProgram.Source
public import GordieHoweNative.Language.Honest.Source
public import GordieHoweNative.Language.RealizedProgram.SourceCheck

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.Embed`

The renaming of a program's identifiers, the correspondence checks between a program and a larger
one through a renaming, and the check that a program holds a part of another (`embeddingB`). Lake
compiles this module with the rest of `GordieHoweNative`, so native mode runs the check as compiled
code. Its lemmas are in `GordieHowe/Language/RealizedProgram/Embed.lean`, which imports this module.
-/

local notation "ℕ" => Nat
local notation "ℤ" => Int

@[expose] public section

namespace GordieHowe.RealizedProgram

/-- **A named operator reads no value**: the transforms, sums of groups and digit
recompositions, possibly batched. Its block, rows and columns are the same in every program. -/
def NamedOp.valueFree : NamedOp → Bool
  | .ntt _ _ _ | .inverseNtt _ _ | .nttTranspose _ _ | .sum _ | .fromDigits _ _ => true
  | .batched _ op => op.valueFree
  | _ => false

mutual

/-- **Every named operator of an expression reads no value** (`NamedOp.valueFree`). -/
def Expr.opsFree : Expr → Bool
  | .leaf _ | .ref _ => true
  | .add e e' | .sub e e' | .mul e e' | .concat e e' => e.opsFree && e'.opsFree
  | .scale _ e | .reindex _ e | .linear _ e | .prod _ e => e.opsFree
  | .mux b t e => b.opsFree && t.opsFree && e.opsFree
  | .apply op e => op.valueFree && e.opsFree
  | .logic _ _ args => Expr.opsFreeList args

/-- Every named operator of a list of expressions reads no value. -/
def Expr.opsFreeList : List Expr → Bool
  | [] => true
  | e :: es => e.opsFree && Expr.opsFreeList es

end

/-! ## The renaming -/

/-- **A renaming of identifiers**: of values (`val`), of shared expressions (`ref`) and of
challenges (`chal`). -/
structure Renaming where
  /-- The new identifier of a value. -/
  val : ℕ → ℕ
  /-- The new identifier of a shared expression. -/
  ref : ℕ → ℕ
  /-- The new identifier of a challenge. -/
  chal : ℕ → ℕ

namespace Renaming

variable (σ : Renaming)

/-- A coefficient, its value renamed. -/
def coef : Coef → Coef
  | .const c => .const c
  | .node v i => .node (σ.val v) i

mutual

/-- **An expression renamed**: its leaves, coefficients' values and references. Named operators
are kept (renamed expressions are read for operators that read no value, `Expr.opsFree`). -/
def expr : Expr → Expr
  | .leaf v => .leaf (σ.val v)
  | .add e e' => .add (expr e) (expr e')
  | .sub e e' => .sub (expr e) (expr e')
  | .scale c e => .scale (σ.coef c) (expr e)
  | .mul e e' => .mul (expr e) (expr e')
  | .reindex idx e => .reindex idx (expr e)
  | .concat e e' => .concat (expr e) (expr e')
  | .linear rows e => .linear (rows.map (·.map fun t => (t.1, σ.coef t.2))) (expr e)
  | .prod n e => .prod n (expr e)
  | .mux b t e => .mux (expr b) (expr t) (expr e)
  | .apply op e => .apply op (expr e)
  | .ref k => .ref (σ.ref k)
  | .logic op w args => .logic op w (exprs args)

/-- A list of expressions renamed. -/
def exprs : List Expr → List Expr
  | [] => []
  | e :: es => expr e :: exprs es

end

/-- **A value's kind renamed**, for the kinds an embedding holds: a challenge's identifier, a bit
view's words, a pad copy's late value and a bound value's expression renamed, the others kept;
`none` for a public expression, an opaque function of arguments and a message. -/
def kind? : Kind → Option Kind
  | .priv => some .priv
  | .pub .input => some (.pub .input)
  | .pub (.opaque n []) => some (.pub (.opaque n []))
  | .constant es => some (.constant es)
  | .challenge c => some (.challenge (σ.chal c))
  | .late => some .late
  | .bits w sel => some (.bits (σ.val w) sel)
  | .padCopy v m => some (.padCopy (σ.val v) m)
  | .bound e => some (.bound (σ.expr e))
  | _ => none

/-- **A value's kind corresponds**: the larger program's kind is the renamed kind (`kind?`). -/
def kindCorr (k k' : Kind) : Bool :=
  match σ.kind? k, k' with
  | some .priv, .priv => true
  | some (.pub .input), .pub .input => true
  | some (.pub (.opaque n [])), .pub (.opaque n' []) => n == n'
  | some (.constant es), .constant es' => es == es'
  | some (.challenge c), .challenge c' => c == c'
  | some .late, .late => true
  | some (.bits w sel), .bits w' sel' => w == w' && decide (sel = sel')
  | some (.padCopy v m), .padCopy v' m' => v == v' && m == m'
  | some (.bound e), .bound e' => e.beq e'
  | _, _ => false


end Renaming


section

variable {ir ir' : RealizedProgram}

variable (ir ir') in
/-- **A predicate `equal` of `ir'` is a renamed one of `ir`**: one domain of one field in both,
the renamed sides of `V` and `R`, whose named operators read no value. -/
def equalCorrB (σ : Renaming) (V R : List ℕ) : PredBody → PredBody → Bool
  | .equal d x y _, .equal d' x' y' _ =>
    d == d' && ir'.domainField d == ir.domainField d && (σ.expr x).beq x' && (σ.expr y).beq y' &&
      x.opsFree && y.opsFree && (x.directNodes ++ y.directNodes).all (· ∈ V) &&
      (x.refs ++ y.refs).all (· ∈ R)
  | _, _ => false

/-- **An expression of the part**: its named operators read no value, it reads values of `V` and
shared expressions of `R`. -/
def partExprB (V R : List ℕ) (x : Expr) : Bool :=
  x.opsFree && x.directNodes.all (· ∈ V) && x.refs.all (· ∈ R)

/-- **An expression of `ir'` is a renamed expression of the part.** -/
def exprCorrB (σ : Renaming) (V R : List ℕ) (x x' : Expr) : Bool :=
  (σ.expr x).beq x' && partExprB V R x

/-- **A quotient of `ir'` is the renamed quotient of the part**, or neither program has one. -/
def quotCorrB (σ : Renaming) (V R : List ℕ) : Option Expr → Option Expr → Bool
  | none, none => true
  | some Q, some Q' => exprCorrB σ V R Q Q'
  | _, _ => false

variable (ir ir') in
/-- **A predicate of `ir'` is a renamed one of `ir`**, a body of the part: an `equal`
(`equalCorrB`); a range `in` of one range, one domain of one field in both, the renamed
nonempty records of the part; a `mod_q` of one modulus, one domain of one field in both, the
renamed sides of the part, with one product flag, quotient bounds and renamed quotient. -/
def bodyCorrB (σ : Renaming) (V R : List ℕ) : PredBody → PredBody → Bool
  | .equal d x y t, .equal d' x' y' t' =>
    ir.equalCorrB ir' σ V R (.equal d x y t) (.equal d' x' y' t')
  | .mem d rs (.range n) _, .mem d' rs' (.range n') _ =>
    d == d' && ir'.domainField d == ir.domainField d && n == n' && !rs.isEmpty &&
      Expr.beqList (σ.exprs rs) rs' && rs.all (partExprB V R)
  | .mod d q x y real, .mod d' q' x' y' real' =>
    d == d' && ir'.domainField d == ir.domainField d && q == q' && exprCorrB σ V R x x' &&
      exprCorrB σ V R y y' && real.form.isProduct == real'.form.isProduct &&
      real.quotientLo == real'.quotientLo && real.qmax == real'.qmax &&
      quotCorrB σ V R real.quotient real'.quotient
  | _, _ => false


end

/-- **The data of a part held by a larger program**: the smaller program, the images of its value,
shared-expression and challenge identifiers, the part's values and shared expressions, and the
pairs of corresponding predicates, of field equalities (`equals`) and of other bodies (`bodies`). -/
structure EmbedData where
  /-- The smaller program. -/
  source : RealizedProgram
  /-- The image of value `v`, at position `v`. -/
  vals : List ℕ
  /-- The image of shared expression `k`, at position `k`. -/
  refs : List ℕ
  /-- The image of challenge `j`, at position `j`. -/
  chals : List ℕ
  /-- The part's values. -/
  V : List ℕ
  /-- The part's shared expressions. -/
  R : List ℕ
  /-- Corresponding field equalities. -/
  equals : List (ℕ × ℕ) := []
  /-- Corresponding predicates of any body the part reads. -/
  bodies : List (ℕ × ℕ) := []
  /-- Predicates of the larger program that must be source predicates. -/
  sources : List ℕ := []
  deriving Repr

/-- The renaming the data lists: each identifier's image at its position, the identifier itself
past the end of its list. -/
def EmbedData.renaming (d : EmbedData) : Renaming :=
  let tv := NatTrie.ofSeq d.vals
  let tr := NatTrie.ofSeq d.refs
  ⟨fun v => tv.getD v v, fun k => tr.getD k k, fun j => d.chals.getD j j⟩

/-- Whether a kind's identifiers lie in the lists of the data, so that the data alone fixes the
kind's image. -/
def EmbedData.kindCoveredB (d : EmbedData) : Kind → Bool
  | .challenge c => decide (c < d.chals.length)
  | .bits w _ => decide (w < d.vals.length)
  | .padCopy v _ => decide (v < d.vals.length)
  | .bound e => e.directNodes.all (· < d.vals.length) && e.refs.all (· < d.refs.length)
  | _ => true

/-- The check of one value of the part. -/
def EmbedData.valueB (d : EmbedData) (ir' : RealizedProgram) (v : ℕ) : Bool :=
  let ir := d.source
  let σ := d.renaming
  let x := ir.value v
  let x' := ir'.value (σ.val v)
  decide (v < ir.values.length) && decide (v < d.vals.length) &&
    decide (σ.val v < ir'.values.length) && ir'.valueField (σ.val v) == ir.valueField v &&
    x'.size == x.size && decide (x'.type = x.type) && x'.phase == x.phase &&
    σ.kindCorr x.kind x'.kind && d.kindCoveredB x.kind &&
    (valueDeps ir v).all (· ∈ d.V) &&
    (match x.kind with
      | .challenge c => ir'.chalField (σ.chal c) == ir.chalField c
      | _ => true)

/-- The check of one shared expression of the part. -/
def EmbedData.refB (d : EmbedData) (ir' : RealizedProgram) (k : ℕ) : Bool :=
  let ir := d.source
  let σ := d.renaming
  decide (k < ir.exprs.length) && decide (k < d.refs.length) &&
    decide (σ.ref k < ir'.exprs.length) && (σ.expr (ir.expr k)).beq (ir'.expr (σ.ref k)) &&
    (ir.expr k).opsFree && (ir.expr k).directNodes.all (· ∈ d.V) &&
    (ir.expr k).refs.all (· ∈ d.R)

/-- Whether a value's public expression reads only shared expressions of the program. -/
def refsInB (ir : RealizedProgram) (x : Value) : Bool :=
  match x.kind with
  | .pub (.expr e) => e.refs.all (· < ir.exprs.length)
  | _ => true

/-- Whether a program's values read values of smaller identifiers, each value's reads taken through
the closure table (`valueDepsOf`) and its shared expressions checked to exist. The kernel builds
the table once; a walk of each value's shared expressions repeats the walk of every entry they
share. -/
def valuesOrderedB (ir : RealizedProgram) : Bool :=
  allIdx (fun v x => ir.refsInB x && (ir.valueDepsOf x).all (· < v)) ir.values 0

/-- **The larger program holds the part**: both programs read in identifier order, the part's
values and shared expressions correspond, and so do the listed predicates, each a predicate of the
smaller program and a source predicate of the larger one. The check reads both programs, element
by element. -/
def embeddingB (ir' : RealizedProgram) (d : EmbedData) : Bool :=
  let ir := d.source
  let σ := d.renaming
  valuesOrderedB ir && valuesOrderedB ir' && ir.refsOrderedB && ir'.refsOrderedB &&
    d.V.all (d.valueB ir') && d.R.all (d.refB ir') &&
    d.equals.all (fun p => ir.equalCorrB ir' σ d.V d.R (ir.predicate p.1).body
        (ir'.predicate p.2).body && decide (p.1 < ir.predicates.length) &&
      decide (p.2 < ir'.predicates.length) && ir'.inSource (ir'.predicate p.2)) &&
    d.bodies.all (fun p => ir.bodyCorrB ir' σ d.V d.R (ir.predicate p.1).body
        (ir'.predicate p.2).body && decide (p.1 < ir.predicates.length) &&
      decide (p.2 < ir'.predicates.length)) &&
    d.sources.all (fun p => ir'.inSource (ir'.predicate p)) &&
    ir.challenges.length == d.chals.length &&
    (List.range d.chals.length).all fun j =>
      (ir'.challenge (σ.chal j)).phase == (ir.challenge j).phase

end GordieHowe.RealizedProgram
