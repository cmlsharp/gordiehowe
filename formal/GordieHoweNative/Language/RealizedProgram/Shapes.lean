-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.ValueShape
public import GordieHoweNative.Language.RealizedProgram.Source
public import GordieHoweNative.Language.Honest.Source
public import GordieHoweNative.Language.RealizedProgram.Embed
public import GordieHoweNative.Language.Realizations.Realized
public import GordieHoweNative.Language.Realizations.Derivation.Events
public import GordieHoweNative.Language.Realizations.Derivation.Rules

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.Shapes`

The shape claims about a realized program that its applications' frontends read (a value's kind, a
predicate's body), as data (`ShapeClaim`), and their check (`ShapeClaim.check`, over a list
`shapesB`), in the Mathlib-free library `GordieHoweNative`, which Lake compiles to a shared library
(`precompileModules`): native mode runs the check as compiled code. A claim names only small shape
data (value and predicate indices, names, argument lists, expressions, a `mod_q`'s form, integers),
and compares parts of a kind or a body, never a whole `Kind` or `PredBody`, which have no decidable
equality. Their lemmas are in `GordieHowe/Language/RealizedProgram/Shapes.lean`, which imports this
module.
-/

local notation "ℕ" => Nat
local notation "ℤ" => Int

@[expose] public section

namespace GordieHowe.RealizedProgram

/-- **The small header of an equality predicate**, excluding its expressions. -/
abbrev Predicate.EqualHeader :=
  String × List Read × List (Nat × Nat) × PredRole × Option Target

/-- **Read an equality predicate's metadata and realization target.** -/
def Predicate.equalHeader (p : Predicate) : Predicate.EqualHeader :=
  (p.name, p.reads, p.degree, p.role,
    match p.body with | .equal _ _ _ t => some t | _ => none)

/-- **A shape claim about a realized program**:

* `embedding d`: the program holds the part of `d.source` that `d` lists (`embeddingB`);
* `exprTable es`: the program's first shared expressions are `es`;
* `phaseCount n`: the program has `n` challenge phases;
* `sourcePredicates lo hi`: the predicates from `lo` through `hi` are valid source predicates;
* `privateFieldSources field`: every private cell in field `field` is a source value;
* `kindPadCopy v w map`: value `v` is a pad copy of the late value `w`, with map `map`;
* `sourceChallenges ids`: the complete list of source-role challenges;
* `fullChallenge c field size`: the scalar parts of the full-field challenge `c`;
* `valueType v type`: the type of value `v`;
* `kindExprEq v e`: value `v` is the public expression `e`;
* `crossPredicates ids`: the complete list of cross-field predicates;
* `statementChecks checks` and `statementRanges ranges`: the complete statement checks and bounds;
* `valueHeader v header`: finite metadata of valid value `v`, excluding its expression and kind;
* `valueCount n`, `predicateCount n`, `exprCount n`, `domainCount n` and `challengeCount n`: the
  program's exact counts;
* `predicateRole p role`: the role of valid predicate `p`;
* `kindConstant v entries`: value `v` is the constant vector `entries`;
* `kindPriv v`: value `v` is committed in phase `0` (`Kind.priv`);
* `kindOpaque v name args`: value `v` is the opaque public value `name` of the values `args`;
* `kindChallenge v c`: value `v` is the challenge `c`;
* `kindExpr v`: value `v` is a public expression;
* `kindBits v w sel`: value `v` is the bit view of the words `sel` of value `w`;
* `kindBound v e`: value `v` is a source value bound to its digits, read as `e`;
* `exprEq k e`: shared expression `k` is `e`;
* `equalHeader p h`: the equality predicate has metadata header `h`;
* `equalParts p d lhs rhs`: predicate `p` is the field equality `lhs = rhs` in domain `d`;
* `memParts p d records set`: predicate `p` is the lookup of `records` in `set` in domain `d`;
* `crossParts p dx x dy y kind`: predicate `p` is the cross-field equality of `x` in domain `dx`
  and `y` in domain `dy`, of kind `kind`;
* `modParts p d q lhs rhs form quotient quotientLo qmax`: predicate `p` is the congruence
  `lhs ≡ rhs (mod q)` in domain `d`, its realization of form `form`, derived quotient `quotient`,
  quotient's lower end `quotientLo` and range `qmax`;
* `family rows template`: the claims `template`, read at each row of `rows`. -/
inductive ShapeClaim where
  /-- The program holds a part of another program, as the data lists. -/
  | embedding (d : EmbedData)
  /-- The program's first shared expressions are `es`. -/
  | exprTable (es : List Expr)
  /-- The number of challenge phases. -/
  | phaseCount (n : ℕ)
  /-- The predicates from `lo` through `hi` are valid source predicates. -/
  | sourcePredicates (lo hi : ℕ)
  /-- Every private cell in this field is a source value. -/
  | privateFieldSources (field : ℕ)
  /-- A pad copy names a late value and its map, without other value data. -/
  | kindPadCopy (v w : ℕ) (map : String)
  /-- The complete list of source-role challenge indices. -/
  | sourceChallenges (ids : List ℕ)
  /-- The scalar parts of a full-field challenge at a valid index. -/
  | fullChallenge (c field size : ℕ)
  /-- The finite declared type of a valid value, independent of its packing node. -/
  | valueType (v : ℕ) (type : VType)
  /-- The exact expression of a public value, without other kind data. -/
  | kindExprEq (v : ℕ) (e : Expr)
  /-- The complete list of cross-field predicate indices. -/
  | crossPredicates (ids : List ℕ)
  /-- The complete list of statement member checks. -/
  | statementChecks (checks : List MemberCheck)
  /-- The complete list of declared statement-value bounds. -/
  | statementRanges (ranges : List (ℕ × ℕ))
  /-- The finite metadata of a valid value. -/
  | valueHeader (v : ℕ) (header : ValueShape)
  /-- The number of realized values. -/
  | valueCount (n : ℕ)
  /-- The number of realized predicates. -/
  | predicateCount (n : ℕ)
  /-- The number of shared expressions. -/
  | exprCount (n : ℕ)
  /-- The number of domains. -/
  | domainCount (n : ℕ)
  /-- The number of challenges. -/
  | challengeCount (n : ℕ)
  /-- Source or generated realization ownership of a valid predicate. -/
  | predicateRole (p : ℕ) (role : PredRole)
  /-- Value `v` is the constant vector `entries`. -/
  | kindConstant (v : ℕ) (entries : List ℕ)
  /-- Value `v` is committed in phase `0`. -/
  | kindPriv (v : ℕ)
  /-- Value `v` is the opaque public value `name` of the values `args`. -/
  | kindOpaque (v : ℕ) (name : String) (args : List ℕ)
  /-- Value `v` is the challenge `c`. -/
  | kindChallenge (v c : ℕ)
  /-- Value `v` is a public expression. -/
  | kindExpr (v : ℕ)
  /-- Value `v` is the bit view of the words `sel` of value `w`. -/
  | kindBits (v w : ℕ) (sel : IndexMap)
  /-- Value `v` is a source value bound to its digits, read as `e`. -/
  | kindBound (v : ℕ) (e : Expr)
  /-- Shared expression `k` is `e`. -/
  | exprEq (k : ℕ) (e : Expr)
  /-- Equality predicate metadata, without body expressions. -/
  | equalHeader (p : ℕ) (header : Predicate.EqualHeader)
  /-- Predicate `p` is the field equality `lhs = rhs` in domain `d`. -/
  | equalParts (p d : ℕ) (lhs rhs : Expr)
  /-- Predicate `p` is the lookup of `records` in `set` in domain `d`. -/
  | memParts (p d : ℕ) (records : List Expr) (set : InSet)
  /-- Predicate `p` is the cross-field equality of `x` in domain `dx` and `y` in domain `dy`. -/
  | crossParts (p dx : ℕ) (x : Expr) (dy : ℕ) (y : Expr) (kind : CrossKind)
  /-- Predicate `p` is the congruence `lhs ≡ rhs (mod q)` in domain `d`, with the given parts of
  its realization. -/
  | modParts (p d q : ℕ) (lhs rhs : Expr) (form : ModForm) (quotient : Option Expr)
      (quotientLo : ℤ) (qmax : ℕ)
  /-- The claims `template` hold at every row of `rows` (`ShapeClaim.atRow`): a repeated gadget's
  one shape, with the value, predicate and shared-expression ids of each repetition in its row. -/
  | family (rows : List (List ℕ)) (template : List ShapeClaim)
  deriving Repr, Inhabited

/-- **An expression's value and shared-expression ids read as positions of a row.** Operators,
coefficients, index maps and Logic arguments stay literal. -/
def Expr.atRow (r : List ℕ) : Expr → Expr
  | .leaf v => .leaf (r.getD v 0)
  | .ref k => .ref (r.getD k 0)
  | .add a b => .add (a.atRow r) (b.atRow r)
  | .sub a b => .sub (a.atRow r) (b.atRow r)
  | .mul a b => .mul (a.atRow r) (b.atRow r)
  | .concat a b => .concat (a.atRow r) (b.atRow r)
  | .mux b t e => .mux (b.atRow r) (t.atRow r) (e.atRow r)
  | .scale c e => .scale c (e.atRow r)
  | .reindex i e => .reindex i (e.atRow r)
  | .linear m e => .linear m (e.atRow r)
  | .prod n e => .prod n (e.atRow r)
  | .apply op e => .apply op (e.atRow r)
  | e => e

/-- **A template claim at a row**: its leading ids and its expressions' ids read as positions of
the row. A constructor outside this list has no row positions and stays literal. -/
def ShapeClaim.atRow (r : List ℕ) : ShapeClaim → ShapeClaim
  | .kindPriv v => .kindPriv (r.getD v 0)
  | .kindBits v w sel => .kindBits (r.getD v 0) (r.getD w 0) sel
  | .valueHeader v header => .valueHeader (r.getD v 0) header
  | .valueType v type => .valueType (r.getD v 0) type
  | .predicateRole p role => .predicateRole (r.getD p 0) role
  | .equalParts p d lhs rhs => .equalParts (r.getD p 0) d (lhs.atRow r) (rhs.atRow r)
  | .exprEq k e => .exprEq (r.getD k 0) (e.atRow r)
  | c => c

/-- **Structural equality of optional expressions** (`Expr.beq` under `some`). -/
def Expr.beqOpt : Option Expr → Option Expr → Bool
  | none, none => true
  | some e, some e' => e.beq e'
  | _, _ => false

section

variable (ir : RealizedProgram)

/-- **Whether a kind is the constant vector `entries`.** -/
def Kind.isConstantB (entries : List ℕ) : Kind → Bool
  | .constant es => es == entries
  | _ => false

/-- Whether a kind is the specified pad copy. -/
def Kind.isPadCopyB (w : ℕ) (map : String) : Kind → Bool
  | .padCopy w' map' => w' == w && map' == map
  | _ => false

/-- **Whether a kind is `priv`.** -/
def Kind.isPrivB : Kind → Bool
  | .priv => true
  | _ => false

/-- **Whether a kind is the opaque public value `name` of `args`.** -/
def Kind.isOpaqueB (name : String) (args : List ℕ) : Kind → Bool
  | .pub (.opaque n a) => n == name && a == args
  | _ => false

/-- **Whether a kind is an opaque public value taking an argument.** -/
def Kind.takesOpaqueArgsB : Kind → Bool
  | .pub (.opaque _ (_ :: _)) => true
  | _ => false

/-- **Whether a kind is the challenge `c`.** -/
def Kind.isChallengeB (c : ℕ) : Kind → Bool
  | .challenge c' => c' == c
  | _ => false

/-- **Whether a kind is a public expression.** -/
def Kind.isExprB : Kind → Bool
  | .pub (.expr _) => true
  | _ => false

/-- Whether a public-expression kind has the specified expression. -/
def Kind.isExprEqB (e : Expr) : Kind → Bool
  | .pub (.expr e') => e'.beq e
  | _ => false

/-- **Whether a kind is the bit view of the words `sel` of value `w`.** -/
def Kind.isBitsB (w : ℕ) (sel : IndexMap) : Kind → Bool
  | .bits w' sel' => w' == w && sel' == sel
  | _ => false

/-- **Whether a kind is the bound value read as `e`.** -/
def Kind.isBoundB (e : Expr) : Kind → Bool
  | .bound e' => e'.beq e
  | _ => false

/-- **Whether a body is the field equality `lhs = rhs` in domain `d`.** -/
def PredBody.isEqualB (d : ℕ) (lhs rhs : Expr) : PredBody → Bool
  | .equal d' l r _ => d' == d && l.beq lhs && r.beq rhs
  | _ => false

/-- **Whether a body is the lookup of `records` in `set` in domain `d`.** -/
def PredBody.isMemB (d : ℕ) (records : List Expr) (set : InSet) : PredBody → Bool
  | .mem d' rs s _ => d' == d && Expr.beqList rs records && decide (s = set)
  | _ => false

/-- **Whether a body is the cross-field equality of `x` in domain `dx` and `y` in domain `dy`, of
kind `kind`.** -/
def PredBody.isCrossB (dx : ℕ) (x : Expr) (dy : ℕ) (y : Expr) (kind : CrossKind) : PredBody → Bool
  | .cross dx' x' dy' y' k _ => dx' == dx && x'.beq x && dy' == dy && y'.beq y && decide (k = kind)
  | _ => false

/-- **Whether a body is the congruence `lhs ≡ rhs (mod q)` in domain `d`** with the given parts of
its realization. -/
def PredBody.isModB (d q : ℕ) (lhs rhs : Expr) (form : ModForm) (quotient : Option Expr)
    (quotientLo : ℤ) (qmax : ℕ) : PredBody → Bool
  | .mod d' q' l r real =>
    d' == d && q' == q && l.beq lhs && r.beq rhs && real.form == form &&
      Expr.beqOpt real.quotient quotient && real.quotientLo == quotientLo && real.qmax == qmax
  | _ => false

/-- Whether a challenge uses the full-field sampler. -/
def Challenge.isFullB (c : Challenge) : Bool :=
  match c.sampler with
  | .full => true
  | _ => false

/-- All cross-field predicate indices, in program order. -/
def crossPredicateIds : List ℕ :=
  (List.range ir.predicates.length).filter fun p => (ir.predicateT p).body.isCross

/-- **A shape claim holds** of the program, read through the tables (`valueT`, `predicateT`, and `expr`, whose
compiled code is a walk). -/
def ShapeClaim.check : ShapeClaim → Bool
  | .embedding d => embeddingB ir d
  | .exprTable es => decide (es.length ≤ ir.exprs.length) &&
      (List.range es.length).all fun k => (ir.expr k).beq (es.getD k default)
  | .phaseCount n => ir.phases == n
  | .sourcePredicates lo hi => decide (hi < ir.predicates.length) &&
      (List.range' lo (hi + 1 - lo)).all fun p => ir.inSource (ir.predicate p)
  | .privateFieldSources field => (List.range ir.values.length).all fun v =>
      !ir.privCellB v || !(ir.valueField v == field) || decide (ir.IsSourceValue v)
  | .kindPadCopy v w map => (ir.valueT v).kind.isPadCopyB w map
  | .sourceChallenges ids => decide (ir.sourceChallengeIds = ids)
  | .fullChallenge c field size => decide (c < ir.challenges.length) &&
      (ir.challenge c).isFullB && decide (ir.chalField c = field) &&
      decide ((ir.challenge c).size = size)
  | .valueType v type => decide (v < ir.values.length) && decide ((ir.valueT v).type = type)
  | .kindExprEq v e => (ir.valueT v).kind.isExprEqB e
  | .crossPredicates ids => decide (ir.crossPredicateIds = ids)
  | .statementChecks checks => decide (ir.statement.checks = checks)
  | .statementRanges ranges => decide (ir.declaredRanges = ranges)
  | .valueHeader v header => decide (v < ir.values.length) && decide (ir.valueShapeT v = header)
  | .valueCount n => ir.values.length == n
  | .predicateCount n => ir.predicates.length == n
  | .exprCount n => ir.exprs.length == n
  | .domainCount n => ir.domains.length == n
  | .challengeCount n => ir.challenges.length == n
  | .predicateRole p role => decide (p < ir.predicates.length) && decide ((ir.predicateT p).role = role)
  | .kindConstant v entries => (ir.valueT v).kind.isConstantB entries
  | .kindPriv v => (ir.valueT v).kind.isPrivB
  | .kindOpaque v name args => (ir.valueT v).kind.isOpaqueB name args
  | .kindChallenge v c => (ir.valueT v).kind.isChallengeB c
  | .kindExpr v => (ir.valueT v).kind.isExprB
  | .kindBits v w sel => (ir.valueT v).kind.isBitsB w sel
  | .kindBound v e => (ir.valueT v).kind.isBoundB e
  | .exprEq k e => (ir.expr k).beq e
  | .equalHeader p header => decide ((ir.predicateT p).equalHeader = header)
  | .equalParts p d lhs rhs => (ir.predicateT p).body.isEqualB d lhs rhs
  | .memParts p d records set => (ir.predicateT p).body.isMemB d records set
  | .crossParts p dx x dy y kind => (ir.predicateT p).body.isCrossB dx x dy y kind
  | .modParts p d q lhs rhs form quotient quotientLo qmax =>
    (ir.predicateT p).body.isModB d q lhs rhs form quotient quotientLo qmax
  | .family _ _ => false

/-- **A claim holds, a family at each of its rows.** A family in a template fails. -/
def ShapeClaim.checkFamily : ShapeClaim → Bool
  | .family rows template =>
    allK (fun r => allK (fun c => ShapeClaim.check ir (c.atRow r)) template) rows
  | c => ShapeClaim.check ir c

/-- **Every shape claim of a list holds** of the program. -/
def shapesB (cs : List ShapeClaim) : Bool := allK (ShapeClaim.checkFamily ir) cs

end

end GordieHowe.RealizedProgram
