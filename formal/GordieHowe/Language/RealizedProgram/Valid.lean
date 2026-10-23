-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Semantics
public import GordieHowe.Language.RealizedProgram.RunVec
public import GordieHowe.Language.RealizedProgram.Encoding

@[expose] public section

/-!
# GordieHowe: the validity conditions that read the plan's program

The conditions of `Plan.Valid` that read the value table and the predicates of the realized program (`GordieHowe.RealizedProgram`), as
decidable predicates:

* `GordieHowe.RealizedProgram.WellFormed`: identifiers in range, every expression of a predicate in its domain's field
  (the MAC's powers read by `macConv` excepted: they are read in their own field) and of consistent
  lengths, coefficients and named operators' operands public, values acyclic (each reads values of
  smaller identifier only), shared expressions acyclic (each reads entries of smaller index only),
  challenges of positive size in phases among the program's;
* `GordieHowe.RealizedProgram.MessagesMatch`: the messages are the late values, in `MsgBefore` order, with their
  phases, sizes and pad spaces;
* `GordieHowe.RealizedProgram.ReadsSound`: every predicate's exported reads contain the reads computed from its
  expressions (`GordieHowe.RealizedProgram.predReads`, through the shared expressions), so its meaning depends only
  on them (`GordieHowe/Language/RealizedProgram/Lemmas.lean`);
* `GordieHowe.RealizedProgram.DegreesSound`: every exported degree bounds the degree computed from the expressions, the
  largest over their coordinates of the per-coordinate degree (`Expr.degAt`, `GordieHowe.RealizedProgram.exprDeg`; the
  exported degrees are the C++'s `deg_c(p)`, computed coordinate by coordinate);
* `GordieHowe.RealizedProgram.ChallengeOrder`: (a) a late value of phase `k` reads only challenges of phases at most
  `k` (and pads); (b) for each source predicate `p` and challenge `c` with `deg_c(p) > 0`, every
  late value `p` reads that is not computed from `c` has phase below `c`'s; (c) the realizations' phase conditions (`in`: the late needles, the group's late histogram
  and the digits before `α`; cross-field `equal`: the key before the tag and the accumulators);
* `GordieHowe.RealizedProgram.PadOrderValid`: every late value reads only pads of pad-realized late values of strictly
  earlier messages in `MsgBefore` order (never its own);
* `GordieHowe.RealizedProgram.TypeSources`: every committed or late `Bit` and `Sub(E)` value has a type source, a
  packing-tree node of that subfield or its Boolean-check predicate `v · v = v`;
* `GordieHowe.RealizedProgram.TargetsAdmit`: every target admits its predicate, the GKR circuits list exactly the
  predicates placed in them, and their input layouts are contiguous with the public blocks first
  (`GordieHowe.RealizedProgram.CircuitLaidOut`);
* `GordieHowe.RealizedProgram.PadRealized`: every late value is pad-realized (`commitment` is rejected).

No condition bounds the challenges' degrees: the exported degrees are data that the frontend's
lowerings read.

`GordieHowe.RealizedProgram.ValidAtNodes` is their conjunction for given packing-tree nodes; `RealizedProgram.Valid P ir`
(`GordieHowe/Language/RealizedProgram/WithPlan.lean`) adds the plan's `Plan.Valid P` and the agreement of the
program's domains with the plan's, the nodes being the plan's.

**Shared expressions.** A property of an expression through its shared expressions is computed by
`GordieHowe.RealizedProgram.closure` (lists, such as the values read) or by a table of the entries' values with one
level per entry (`GordieHowe.RealizedProgram.refDeg`, degrees in the cells; `GordieHowe.RealizedProgram.refDegAt`, per-coordinate degrees
in a challenge). Both recompute an entry at each reference, so their cost is that of the expression
written as a tree. They are the definitions; the decision procedure is the checker of
`GordieHowe/Language/RealizedProgram/Check.lean`, which computes each entry once: `WellFormed` takes its `Decidable`
instance from `wellFormedB` (`wellFormedB_iff`), and `ReadsSound`, `DegreesSound` and `TargetsAdmit`
are decided through `readsB`, `degreesB` and `targetsB` (`readsB_iff`, `degreesB_iff`,
`targetsB_iff`). The conditions over the values (`MessagesMatch`, `ChallengeOrder`,
`PadOrderValid`, `PadRealized`, `TypeSources`) have `Decidable` instances here that look each
value up in the list, quadratic in the number of values; the proof modules decide them through the
one-pass checkers of `GordieHowe/Language/RealizedProgram/CheckValues.lean`.
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## Syntax: nodes, references, reads and degrees -/

/-- The values a coefficient reads. -/
def Coef.nodes : Coef → List ℕ
  | .const _ => []
  | .node v _ => [v]

/-- **The public operands of a named operator read in its operand's field** (`h`, `a`, `t`, `M`,
`d`, `c`; through `batched`). -/
def NamedOp.operands : NamedOp → List ℕ
  | .negacyclicConv h _ => [h]
  | .polyMatVec a _ _ _ => [a]
  | .polyBroadcast t _ _ => [t]
  | .ntt _ _ _ => []
  | .inverseNtt _ _ => []
  | .nttTranspose _ _ => []
  | .rowDot M _ _ => [M]
  | .macConv _ _ _ _ => []
  | .acyclicConv h _ => [h]
  | .diagonal d => [d]
  | .scale c => [c]
  | .constDiagonal d => [d]
  | .sum _ => []
  | .fromDigits _ _ => []
  | .batched _ op => operands op

/-- **The public operands of a named operator read in their own field**: the MAC's powers `r` of
`macConv` (their bits in the MAC field's polynomial basis). -/
def NamedOp.foreignOperands : NamedOp → List ℕ
  | .macConv r _ _ _ => [r]
  | .batched _ op => foreignOperands op
  | _ => []

/-- **A named operator's block widths are positive** (`cols` and `rows`). -/
def NamedOp.widthsOk (ir : RealizedProgram) (op : NamedOp) : Bool :=
  0 < NamedOp.cols ir op && 0 < NamedOp.rows ir op

mutual

/-- **The values an expression reads directly** (not through its shared expressions): its leaves,
the values of its coefficients and the operands of its named operators. -/
def Expr.directNodes : Expr → List ℕ
  | .leaf v => [v]
  | .add e e' => e.directNodes ++ e'.directNodes
  | .sub e e' => e.directNodes ++ e'.directNodes
  | .scale c e => c.nodes ++ e.directNodes
  | .mul e e' => e.directNodes ++ e'.directNodes
  | .reindex _ e => e.directNodes
  | .concat e e' => e.directNodes ++ e'.directNodes
  | .linear rows e => rows.flatMap (·.flatMap fun t => t.2.nodes) ++ e.directNodes
  | .prod _ e => e.directNodes
  | .mux b t e => b.directNodes ++ t.directNodes ++ e.directNodes
  | .apply op e => op.operands ++ op.foreignOperands ++ e.directNodes
  | .ref _ => []
  | .logic _ _ args => Expr.directNodesList args

/-- The values a list of expressions reads directly. -/
def Expr.directNodesList : List Expr → List ℕ
  | [] => []
  | e :: es => e.directNodes ++ Expr.directNodesList es

end

mutual

/-- **The values an expression reads directly in its own field**: `Expr.directNodes` without the
MAC's powers of `macConv`. -/
def Expr.fieldNodes : Expr → List ℕ
  | .leaf v => [v]
  | .add e e' => e.fieldNodes ++ e'.fieldNodes
  | .sub e e' => e.fieldNodes ++ e'.fieldNodes
  | .scale c e => c.nodes ++ e.fieldNodes
  | .mul e e' => e.fieldNodes ++ e'.fieldNodes
  | .reindex _ e => e.fieldNodes
  | .concat e e' => e.fieldNodes ++ e'.fieldNodes
  | .linear rows e => rows.flatMap (·.flatMap fun t => t.2.nodes) ++ e.fieldNodes
  | .prod _ e => e.fieldNodes
  | .mux b t e => b.fieldNodes ++ t.fieldNodes ++ e.fieldNodes
  | .apply op e => op.operands ++ e.fieldNodes
  | .ref _ => []
  | .logic _ _ args => Expr.fieldNodesList args

/-- The values a list of expressions reads directly in its own field. -/
def Expr.fieldNodesList : List Expr → List ℕ
  | [] => []
  | e :: es => e.fieldNodes ++ Expr.fieldNodesList es

end

mutual

/-- **The public values an expression reads directly as coefficients**: its coefficients' values
and its named operators' operands. -/
def Expr.coefNodes : Expr → List ℕ
  | .leaf _ => []
  | .add e e' => e.coefNodes ++ e'.coefNodes
  | .sub e e' => e.coefNodes ++ e'.coefNodes
  | .scale c e => c.nodes ++ e.coefNodes
  | .mul e e' => e.coefNodes ++ e'.coefNodes
  | .reindex _ e => e.coefNodes
  | .concat e e' => e.coefNodes ++ e'.coefNodes
  | .linear rows e => rows.flatMap (·.flatMap fun t => t.2.nodes) ++ e.coefNodes
  | .prod _ e => e.coefNodes
  | .mux b t e => b.coefNodes ++ t.coefNodes ++ e.coefNodes
  | .apply op e => op.operands ++ op.foreignOperands ++ e.coefNodes
  | .ref _ => []
  | .logic _ _ args => Expr.coefNodesList args

/-- The coefficient values a list of expressions reads directly. -/
def Expr.coefNodesList : List Expr → List ℕ
  | [] => []
  | e :: es => e.coefNodes ++ Expr.coefNodesList es

end

mutual

/-- **The shared expressions an expression reads directly** (`ref k`). -/
def Expr.refs : Expr → List ℕ
  | .leaf _ => []
  | .add e e' => e.refs ++ e'.refs
  | .sub e e' => e.refs ++ e'.refs
  | .scale _ e => e.refs
  | .mul e e' => e.refs ++ e'.refs
  | .reindex _ e => e.refs
  | .concat e e' => e.refs ++ e'.refs
  | .linear _ e => e.refs
  | .prod _ e => e.refs
  | .mux b t e => b.refs ++ t.refs ++ e.refs
  | .apply _ e => e.refs
  | .ref k => [k]
  | .logic _ _ args => Expr.refsList args

/-- The shared expressions a list of expressions reads directly. -/
def Expr.refsList : List Expr → List ℕ
  | [] => []
  | e :: es => e.refs ++ Expr.refsList es

end

/-- The coefficients of sparse rows. -/
def Expr.rowCoefs (rows : List (List (ℕ × Coef))) : List Coef := rows.flatMap (·.map (·.2))

mutual

/-- **An expression's degree**, the values having degrees `nd` and the shared expressions `rd`: `+`
takes the maximum, `·` adds, `prod` multiplies by the axis length, a coefficient adds its degree, a
named operator adds the largest degree of its operands, a Logic builder on words of `w` bits
multiplies the largest degree of its arguments by `2w` (`lt_reduce` has degree at most `2w` in its
bits). -/
def Expr.deg (nd : ℕ → ℕ) (rd : ℕ → ℕ) : Expr → ℕ
  | .leaf v => nd v
  | .add e e' => max (e.deg nd rd) (e'.deg nd rd)
  | .sub e e' => max (e.deg nd rd) (e'.deg nd rd)
  | .scale c e => (c.nodes.map nd).foldr max 0 + e.deg nd rd
  | .mul e e' => e.deg nd rd + e'.deg nd rd
  | .reindex _ e => e.deg nd rd
  | .concat e e' => max (e.deg nd rd) (e'.deg nd rd)
  | .linear rows e =>
      ((Expr.rowCoefs rows).flatMap (·.nodes) |>.map nd).foldr max 0 + e.deg nd rd
  | .prod n e => n * e.deg nd rd
  | .mux b t e => b.deg nd rd + max (t.deg nd rd) (e.deg nd rd)
  | .apply op e => ((op.operands ++ op.foreignOperands).map nd).foldr max 0 + e.deg nd rd
  | .ref k => rd k
  | .logic _ w args => 2 * w * (Expr.degList nd rd args).foldr max 0

/-- The degrees of a list of expressions. -/
def Expr.degList (nd : ℕ → ℕ) (rd : ℕ → ℕ) : List Expr → List ℕ
  | [] => []
  | e :: es => e.deg nd rd :: Expr.degList nd rd es

end

/-- **The coordinates of its operand a named operator reads**: the operand's size for the
convolutions, the transform-free products and the diagonals (`polyMatVec` and `polyBroadcast` read
their operand's first `K·L·n` and `K·n` coordinates, within its size), `R·W` for `rowDot`, one for
`scale`; none for an operator without an operand. -/
def NamedOp.readLen (ir : RealizedProgram) : NamedOp → ℕ
  | .negacyclicConv h _ => (ir.value h).size
  | .polyMatVec a _ _ _ => (ir.value a).size
  | .polyBroadcast t _ _ => (ir.value t).size
  | .rowDot _ R W => R * W
  | .macConv r _ _ _ => (ir.value r).size
  | .acyclicConv h _ => (ir.value h).size
  | .diagonal d => (ir.value d).size
  | .scale _ => 1
  | .constDiagonal d => (ir.value d).size
  | .batched _ op => readLen ir op
  | _ => 0

/-- **The degree a named operator's operands add**: the largest degree among the coordinates of
its operands it reads (`NamedOp.readLen`), the values having per-coordinate degrees `nd`. -/
def NamedOp.opDeg (ir : RealizedProgram) (nd : ℕ → ℕ → ℕ) (op : NamedOp) : ℕ :=
  ((op.operands ++ op.foreignOperands).map fun v => maxBelow (op.readLen ir) (nd v)).foldr max 0

/-- **A coefficient's degree**, the values having per-coordinate degrees `nd`: `0` for a constant,
the coordinate's for a value's coordinate. -/
def Coef.degAt (nd : ℕ → ℕ → ℕ) : Coef → ℕ
  | .const _ => 0
  | .node v i => nd v i

section DegAt

variable (ir : RealizedProgram)

mutual

/-- **The degree of coordinate `i` of an expression** in a challenge, the values having
per-coordinate degrees `nd`, the shared expressions `rd` and their lengths `rl`
(`lib/gordiehowe/expr.h`, `challenge_coord_degrees`): `+` and `-` take the coordinatewise maximum, a
product adds coordinatewise, a multiple adds its coefficient's degree, a multiplexer adds its
selector's degree to the larger branch's; a view (`reindex`, `concat`) gives each coordinate the
degree of the coordinate it reads; a sparse row takes the largest over its terms of the
coefficient's degree plus the coordinate's; `prod n` adds the degrees of its group; a named operator
gives output `i` the largest degree of the block it reads plus its operands' (`NamedOp.opDeg`),
which for `sum w` is the largest of its group and for the C++'s other operators is at most the
largest over their input; a Logic builder on words of `w` bits gives output `i` `2w` times the
largest degree of the bits it reads (the C++ gives a comparison of an operand of positive degree no
finite bound). Every coordinate has a degree, also past the expression's length: the degree of a
coordinate is that of what it reads, so the bound holds at every coordinate. -/
def Expr.degAt (nd rd : ℕ → ℕ → ℕ) (rl : ℕ → ℕ) : Expr → ℕ → ℕ
  | .leaf v, i => nd v i
  | .add e e', i => max (Expr.degAt nd rd rl e i) (Expr.degAt nd rd rl e' i)
  | .sub e e', i => max (Expr.degAt nd rd rl e i) (Expr.degAt nd rd rl e' i)
  | .scale c e, i => c.degAt nd + Expr.degAt nd rd rl e i
  | .mul e e', i => Expr.degAt nd rd rl e i + Expr.degAt nd rd rl e' i
  | .reindex idx e, i => Expr.degAt nd rd rl e (idx.entry i)
  | .concat e e', i =>
      if i < Expr.len ir rl e then Expr.degAt nd rd rl e i
      else Expr.degAt nd rd rl e' (i - Expr.len ir rl e)
  | .linear rows e, i =>
      ((rows.getD i []).map fun t => t.2.degAt nd + Expr.degAt nd rd rl e t.1).foldr max 0
  | .prod n e, i => ((List.range n).map fun t => Expr.degAt nd rd rl e (i * n + t)).sum
  | .mux b t e, i =>
      Expr.degAt nd rd rl b i + max (Expr.degAt nd rd rl t i) (Expr.degAt nd rd rl e i)
  | .apply op e, i =>
      op.opDeg ir nd + maxBelow (op.cols ir) fun t =>
        Expr.degAt nd rd rl e (i / op.rows ir * op.cols ir + t)
  | .ref k, i => rd k i
  | .logic _ w args, i =>
      2 * w * ((Expr.degAtList nd rd rl args).map fun g => maxBelow w fun t => g (i * w + t)).foldr
        max 0

/-- The per-coordinate degrees of a list of expressions. -/
def Expr.degAtList (nd rd : ℕ → ℕ → ℕ) (rl : ℕ → ℕ) : List Expr → List (ℕ → ℕ)
  | [] => []
  | e :: es => Expr.degAt nd rd rl e :: Expr.degAtList nd rd rl es

end

end DegAt

mutual

/-- **An expression vanishes where all its values vanish**, the shared expressions doing so where
`rz` holds (a batch relation's `Q(0) = 0`, with every value an operand). -/
def Expr.zeroAtZero (rz : ℕ → Bool) : Expr → Bool
  | .leaf _ => true
  | .add e e' => e.zeroAtZero rz && e'.zeroAtZero rz
  | .sub e e' => e.zeroAtZero rz && e'.zeroAtZero rz
  | .scale _ e => e.zeroAtZero rz
  | .mul e e' => e.zeroAtZero rz || e'.zeroAtZero rz
  | .reindex _ e => e.zeroAtZero rz
  | .concat e e' => e.zeroAtZero rz && e'.zeroAtZero rz
  | .linear _ e => e.zeroAtZero rz
  | .prod n e => 0 < n && e.zeroAtZero rz
  | .mux b t e => e.zeroAtZero rz && (b.zeroAtZero rz || t.zeroAtZero rz)
  | .apply _ e => e.zeroAtZero rz
  | .ref k => rz k
  | .logic _ _ _ => false

end

/-- The late values among reads. -/
def Read.lates (rds : List Read) : List ℕ :=
  rds.filterMap fun
    | .late u => some u
    | _ => none

/-- The pads among reads. -/
def Read.pads (rds : List Read) : List ℕ :=
  rds.filterMap fun
    | .pad u => some u
    | _ => none

/-- **The expressions of a set**: `e'` for the entries of `e'`, none for a range or a table. -/
def InSet.exprs : InSet → List Expr
  | .expr e' => [e']
  | _ => []

@[simp] theorem InSet.exprs_range (n : ℕ) : (InSet.range n).exprs = [] := rfl
@[simp] theorem InSet.exprs_table (t : ℕ) : (InSet.table t).exprs = [] := rfl
@[simp] theorem InSet.exprs_expr (e' : Expr) : (InSet.expr e').exprs = [e'] := rfl

/-- **The expressions of a predicate body**, each with its domain: an `in` reads its records and
the expression of its set. -/
def PredBody.exprs : PredBody → List (ℕ × Expr)
  | .equal d e e' _ => [(d, e), (d, e')]
  | .mem d records set _ => (records ++ set.exprs).map ((d, ·))
  | .mod d _ e e' _ => [(d, e), (d, e')]
  | .cross dx x dy y _ _ => [(dx, x), (dy, y)]

/-- **A predicate body is the Boolean check of value `v`**: `v · v = v`, either way round. -/
def PredBody.isBoolCheck (v : ℕ) : PredBody → Bool
  | .equal _ (.mul (.leaf u) (.leaf u')) (.leaf u'') _ => u == v && u' == v && u'' == v
  | .equal _ (.leaf u'') (.mul (.leaf u) (.leaf u')) _ => u == v && u' == v && u'' == v
  | _ => false

section

variable (ir : RealizedProgram)

/-! ## Through the shared expressions -/

/-- **A list property of shared expression `k`** with `n` levels: `g` of the entry, then of the
entries it reads. -/
def refClosure {α : Type} (g : Expr → List α) : ℕ → ℕ → List α
  | 0, _ => []
  | n + 1, k => g (ir.expr k) ++ (ir.expr k).refs.flatMap (refClosure g n)

/-- **A list property of an expression through its shared expressions**: `g` of the expression,
then of the entries it reads, at the program's depth (the number of entries). -/
def closure {α : Type} (g : Expr → List α) (e : Expr) : List α :=
  g e ++ e.refs.flatMap (ir.refClosure g ir.exprs.length)

/-- **The values an expression reads**, through its shared expressions. -/
def exprNodes (e : Expr) : List ℕ := ir.closure Expr.directNodes e

/-- **The degrees of the shared expressions**, the values having degrees `nd`, with `n` levels. -/
def refDeg (nd : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, k => (ir.expr k).deg nd (refDeg nd n)

/-- **An expression's degree** through its shared expressions, the values having degrees `nd`. -/
def degOf (nd : ℕ → ℕ) (e : Expr) : ℕ := e.deg nd (ir.refDeg nd ir.exprs.length)

/-- **Whether the shared expressions vanish at zero**, with `n` levels. -/
def refZero : ℕ → ℕ → Bool
  | 0, _ => false
  | n + 1, k => (ir.expr k).zeroAtZero (refZero n)

/-- **An expression vanishes where its values vanish**, through its shared expressions. -/
def zeroOf (e : Expr) : Bool := e.zeroAtZero (ir.refZero ir.exprs.length)

/-! ## Reads and degrees -/

/-- **What value `v` reads from the run**, with `n` levels of values read by values (as
`RealizedProgram.read`): a challenge value its challenge, a late value itself, a message its late value,
a public expression, an opaque value or a bit view what the values they read read. -/
def nodeReads : ℕ → ℕ → List Read
  | 0, _ => []
  | n + 1, v =>
    match (ir.value v).kind with
    | .pub (.expr e) => (ir.exprNodes e).flatMap (nodeReads n)
    | .pub (.opaque _ args) => args.flatMap (nodeReads n)
    | .challenge c => [.chal c]
    | .late => [.late v]
    | .bits w _ => nodeReads n w
    | .message u => [.late u]
    | _ => []

/-- **The values the table of a lookup reads**: its columns for a table of columns, the values its
expression reads for a table of an expression's coordinates. -/
def tableCols : PredBody → List ℕ
  | .mem _ _ (.table t) _ =>
    match (ir.table t).rows with
    | .columns cols => cols
    | .range _ => []
    | .expr e' => ir.exprNodes e'
  | _ => []

/-- **The values a predicate reads**: those of its expressions, and the columns of the table it
looks up into. -/
def predNodes (b : PredBody) : List ℕ := b.exprs.flatMap (ir.exprNodes ·.2) ++ ir.tableCols b

/-- **What a predicate reads from the run**, computed from its values (at the program's fuel). -/
def predReads (b : PredBody) : List Read := (ir.predNodes b).flatMap (ir.nodeReads ir.fuel)

/-- **The per-coordinate degrees of the shared expressions**, the values having per-coordinate
degrees `nd`, with `n` levels. -/
def refDegAt (nd : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, k, i => Expr.degAt ir nd (refDegAt nd n) (ir.refLen ir.exprs.length) (ir.expr k) i

/-- **The degree of coordinate `i` of an expression** through its shared expressions, the values
having per-coordinate degrees `nd`. -/
def degAtOf (nd : ℕ → ℕ → ℕ) (e : Expr) (i : ℕ) : ℕ :=
  Expr.degAt ir nd (ir.refDegAt nd ir.exprs.length) (ir.refLen ir.exprs.length) e i

/-- **The degree of coordinate `i` of value `v` in challenge `c`**, with `n` levels of public
expressions: `1` at a value of challenge `c`, its expression's at a public expression, `0`
otherwise. -/
def nodeDegAt (c : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | n + 1, v, i =>
    match (ir.value v).kind with
    | .pub (.expr e) => ir.degAtOf (nodeDegAt c n) e i
    | .challenge c' => if c' = c then 1 else 0
    | _ => 0

/-- **The degree of a predicate in challenge `c`**, computed from its expressions: the largest
degree among their coordinates below their lengths. -/
def exprDeg (c : ℕ) (b : PredBody) : ℕ :=
  (b.exprs.map fun de => maxBelow (ir.exprLen de.2) (ir.degAtOf (ir.nodeDegAt c ir.fuel) de.2)).foldr
    max 0

/-- Whether value `v` is committed in phase `0` (a committed value, a bit view of committed words, a
pad copy, or a value bound to its digits, which the source program commits). -/
def isCommitted (v : ℕ) : Bool :=
  match (ir.value v).kind with
  | .priv => true
  | .bits _ _ => true
  | .padCopy _ _ => true
  | .bound _ => true
  | _ => false

/-- Whether value `v` is a public expression. -/
def isPubExpr (v : ℕ) : Bool :=
  match (ir.value v).kind with
  | .pub (.expr _) => true
  | _ => false

/-- Whether value `v` is late. -/
def isLateNode (v : ℕ) : Bool := (ir.value v).kind.isLate

/-- Whether value `v` is public (a statement member, an opaque or expression public value, a
constant, a challenge value or a message). -/
def isPublic (v : ℕ) : Bool := !(ir.isCommitted v) && !(ir.isLateNode v)

/-- Whether value `v` is an operand a batch may read: a value committed in phase `0`, a constant,
or a statement member or opaque public value (no challenge, no late value and no message). -/
def isBatchNode (v : ℕ) : Bool :=
  match (ir.value v).kind with
  | .priv => (ir.value v).phase == 0
  | .bits _ _ => true
  | .padCopy _ _ => true
  | .constant _ => true
  | .pub .input => true
  | .pub (.opaque _ _) => true
  | _ => false

/-! ## Well-formedness -/

/-- **A Logic builder's arguments have consistent lengths** `lens`: two for `lt`, `leq`, `eq`, of
one length, one for `any` and `all`, the length a multiple of the width `w ≥ 1`. -/
def logicShapeOk (op : LogicOp) (w : ℕ) (lens : List ℕ) : Bool :=
  0 < w && lens.length == (match op with
    | .lt | .leq | .eq => 2
    | .any | .all => 1) &&
  lens.all (· == lens.headD 0) && lens.headD 0 % w == 0

mutual

/-- **An expression's lengths are consistent** (its shared expressions are checked once each,
`RealizedProgram.ExprsOk`): the operands of `+`, `-`, `·` and `mux` have one length, index maps and sparse
rows stay in range, a product's axis divides the length, a named operator's block divides its
operand, and a Logic builder's arguments are of one length, a multiple of the word width. -/
def exprShapeOk : Expr → Bool
  | .leaf _ => true
  | .add e e' => exprShapeOk e && exprShapeOk e' && ir.exprLen e == ir.exprLen e'
  | .sub e e' => exprShapeOk e && exprShapeOk e' && ir.exprLen e == ir.exprLen e'
  | .scale _ e => exprShapeOk e
  | .mul e e' => exprShapeOk e && exprShapeOk e' && ir.exprLen e == ir.exprLen e'
  | .reindex idx e => exprShapeOk e && idx.inRange (ir.exprLen e)
  | .concat e e' => exprShapeOk e && exprShapeOk e'
  | .linear rows e => exprShapeOk e && rows.all (·.all (·.1 < ir.exprLen e))
  | .prod n e => exprShapeOk e && 0 < n && ir.exprLen e % n == 0
  | .mux b t e =>
      exprShapeOk b && exprShapeOk t && exprShapeOk e && ir.exprLen b == ir.exprLen t &&
        ir.exprLen t == ir.exprLen e
  | .apply op e =>
      exprShapeOk e && op.widthsOk ir && ir.exprLen e % NamedOp.cols ir op == 0
  | .ref _ => true
  | .logic op w args => exprShapeOkList args && logicShapeOk op w (args.map ir.exprLen)

/-- The lengths of a list of expressions are consistent. -/
def exprShapeOkList : List Expr → Bool
  | [] => true
  | e :: es => exprShapeOk e && exprShapeOkList es

end

/-- **An expression is well formed in field `f`**: its values exist; those read in its field lie
in field `f`; its coefficients and operators' operands are public; its shared expressions exist;
its lengths are consistent. -/
structure ExprOk (f : ℕ) (e : Expr) : Prop where
  /-- The values exist. -/
  range : ∀ v ∈ ir.exprNodes e, v < ir.values.length
  /-- The values read in the expression's field lie in field `f`. -/
  field : ∀ v ∈ ir.closure Expr.fieldNodes e, ir.valueField v = f
  /-- The coefficients and operands are public. -/
  coefs : ∀ v ∈ ir.closure Expr.coefNodes e, ir.isPublic v = true
  /-- The shared expressions exist. -/
  refs : ∀ k ∈ e.refs, k < ir.exprs.length
  /-- The lengths are consistent. -/
  shape : ir.exprShapeOk e = true

theorem exprOk_iff (f : ℕ) (e : Expr) : ir.ExprOk f e ↔
    (∀ v ∈ ir.exprNodes e, v < ir.values.length) ∧
      (∀ v ∈ ir.closure Expr.fieldNodes e, ir.valueField v = f) ∧
      (∀ v ∈ ir.closure Expr.coefNodes e, ir.isPublic v = true) ∧
      (∀ k ∈ e.refs, k < ir.exprs.length) ∧ ir.exprShapeOk e = true :=
  ⟨fun h => ⟨h.range, h.field, h.coefs, h.refs, h.shape⟩,
    fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, h5⟩⟩

instance (f : ℕ) (e : Expr) : Decidable (ir.ExprOk f e) :=
  decidable_of_iff _ (ir.exprOk_iff f e).symm

/-- **The shared expressions are well formed**: entry `k` reads only entries of smaller index, and
its lengths are consistent. -/
def ExprsOk : Prop :=
  ∀ k < ir.exprs.length, (∀ k' ∈ (ir.expr k).refs, k' < k) ∧ ir.exprShapeOk (ir.expr k) = true

/-- **A public value's definition is well formed**: a public expression is well formed in the
value's field and reads only values of smaller identifier; an opaque function's arguments are
values of smaller identifier. -/
def PubDefOk (v : ℕ) : PubDef → Prop
  | .input => True
  | .opaque _ args => ∀ u ∈ args, u < v
  | .expr e => ir.ExprOk (ir.valueField v) e ∧ ∀ u ∈ ir.exprNodes e, u < v

instance (v : ℕ) (d : PubDef) : Decidable (ir.PubDefOk v d) := by
  cases d <;> unfold PubDefOk <;> infer_instance

/-- **A value's kind is well formed**: a public value's definition (`PubDefOk`); a challenge
value's challenge exists and lies in the value's field; a bit view's words are words of a value
of smaller identifier, in range, its size a multiple of their number; a pad copy's late value is a
late value (the copy is committed: it reads no value); a message's late value is a late value of
smaller identifier, in its field; a bound value's expression is well formed in the value's field
and reads only values of the program (its digits may come after it: the realized program reads a
bound value as its expression at the committed assignment, `RealizedProgram.bindAsg`, never through the
value order). -/
def KindOk (v : ℕ) : Kind → Prop
  | .priv => True
  | .pub d => ir.PubDefOk v d
  | .constant _ => True
  | .challenge c => c < ir.challenges.length ∧ ir.chalField c = ir.valueField v
  | .late => True
  | .bits w sel =>
      w < v ∧ 0 < sel.size ∧ sel.inRange (ir.value w).size = true ∧
        (ir.value v).size % sel.size = 0
  | .padCopy u _ => ir.isLateNode u = true
  | .message u => u < v ∧ ir.isLateNode u = true ∧ ir.valueField u = ir.valueField v
  | .bound e => ir.ExprOk (ir.valueField v) e ∧ ∀ u ∈ ir.exprNodes e, u < ir.values.length

instance (v : ℕ) (k : Kind) : Decidable (ir.KindOk v k) := by
  cases k <;> unfold KindOk <;> infer_instance

/-- **A value is well formed**: its domain exists and its kind is well formed. -/
def ValueOk (v : ℕ) : Prop :=
  (ir.value v).domain < ir.domains.length ∧ ir.KindOk v (ir.value v).kind

/-- **The sides of a predicate have one length**: those of a field `equal`, of a `mod_q` and of a
cross-field `equal`. -/
def LensOk : PredBody → Prop
  | .equal _ e e' _ => ir.exprLen e = ir.exprLen e'
  | .mem _ _ _ _ => True
  | .mod _ _ e e' _ => ir.exprLen e = ir.exprLen e'
  | .cross _ x _ y _ _ => ir.exprLen x = ir.exprLen y

instance (b : PredBody) : Decidable (ir.LensOk b) := by
  cases b <;> unfold LensOk <;> infer_instance

/-- **A predicate is well formed**: every expression is well formed in its domain's field, and
the sides have one length (`LensOk`). -/
def PredOk (b : PredBody) : Prop :=
  (∀ de ∈ b.exprs, de.1 < ir.domains.length ∧ ir.ExprOk (ir.domainField de.1) de.2) ∧ ir.LensOk b

/-- **A challenge's sampler is supported** for a challenge of `size` coordinates: the field or a
node; the field minus `[0, tmax)` for a challenge of one coordinate. The packed rows of public tables
and unions are rejected (their `U` depends on an earlier challenge under the `gamma` packing;
`FieldInterp.SamplerTy`). -/
def SamplerOk (size : ℕ) : Sampler → Prop
  | .full => True
  | .node _ => True
  | .fieldMinusTables (.range _) => size = 1
  | .fieldMinusTables (.packedRows _) => False
  | .fieldMinusTables (.union _ _) => False

instance (size : ℕ) (s : Sampler) : Decidable (SamplerOk size s) := by
  rcases s with _ | _ | ⟨_ | _⟩ <;> unfold SamplerOk <;> infer_instance

/-- **A challenge is well formed**: of positive size, in a phase of the program and in a field of
it, with a supported sampler. -/
def ChallengeOk (c : Challenge) : Prop :=
  1 ≤ c.size ∧ 1 ≤ c.phase ∧ c.phase ≤ ir.phases ∧ c.field < ir.fields.length ∧
    SamplerOk c.size c.sampler

instance (c : Challenge) : Decidable (ir.ChallengeOk c) := by unfold ChallengeOk; infer_instance

/-- **A value's field is well formed**: a value of a field no domain commits (`Value.field`, the
odd–odd MAC's key, chunk powers, tag and message) names a field of the program, is of a kind that
may lie there (`Kind.allowsField`) and of type `Field`; every other value lies in its domain. -/
def FieldOk (v : ℕ) : Prop :=
  match (ir.value v).field with
  | none => True
  | some f =>
    f < ir.fields.length ∧ (ir.value v).kind.allowsField = true ∧ (ir.value v).type = .field

instance (v : ℕ) : Decidable (ir.FieldOk v) := by
  unfold FieldOk
  split <;> infer_instance

/-- **A member check of the statement is well formed**, by its kind (`MemberCheck.kind?`): an
entry bound reads a value of the program (`RealizedProgram.memberValue?`) with the kind's bytes per
coordinate; `p256_affine_point` reads a value of two 32-byte coordinates in a field of
characteristic `p256Prime` and degree `1`; `limbBits b w L` reads a value of `L` limbs, `b` bits in
the member's bytes, `b ≤ w L`, and `2^w` at most the characteristic. Any other check, an unknown id
among them, is rejected. -/
def CheckOk (m : MemberCheck) : Prop :=
  match ir.memberValue? m.member, m.kind? with
  | some v, some (.below _ w) => m.bytes = w * (ir.value v).size
  | some v, some .p256Point => m.bytes = 64 ∧ (ir.value v).size = 2 ∧
      (ir.field (ir.valueField v)).characteristic = p256Prime ∧
      (ir.field (ir.valueField v)).degree = 1
  | some v, some (.limbBits b w L) => m.bytes * 8 = b ∧ (ir.value v).size = L ∧ b ≤ w * L ∧
      2 ^ w ≤ (ir.field (ir.valueField v)).characteristic
  | _, _ => False

/-- **`CheckOk` as a check** (`checkOkB_iff`). -/
def checkOkB (m : MemberCheck) : Bool :=
  match ir.memberValue? m.member, m.kind? with
  | some v, some (.below _ w) => decide (m.bytes = w * (ir.value v).size)
  | some v, some .p256Point => decide (m.bytes = 64 ∧ (ir.value v).size = 2 ∧
      (ir.field (ir.valueField v)).characteristic = p256Prime ∧
      (ir.field (ir.valueField v)).degree = 1)
  | some v, some (.limbBits b w L) => decide (m.bytes * 8 = b ∧ (ir.value v).size = L ∧
      b ≤ w * L ∧ 2 ^ w ≤ (ir.field (ir.valueField v)).characteristic)
  | _, _ => false

theorem checkOkB_iff (m : MemberCheck) : ir.checkOkB m = true ↔ ir.CheckOk m := by
  unfold checkOkB CheckOk
  split <;> simp

instance (m : MemberCheck) : Decidable (ir.CheckOk m) := decidable_of_iff _ (ir.checkOkB_iff m)

/-- **The program is well formed**: domains' fields exist; values, shared expressions,
predicates, challenges and the statement's member checks are well formed; every value lies in its
domain or in a field of the program of a kind that may lie there (`FieldOk`). -/
structure WellFormed : Prop where
  /-- Every domain's field exists. -/
  domains : ∀ d ∈ ir.domains, d.field < ir.fields.length
  /-- Every value is well formed. -/
  values : ∀ v < ir.values.length, ir.ValueOk v
  /-- The shared expressions are well formed. -/
  exprs : ir.ExprsOk
  /-- Every predicate is well formed. -/
  predicates : ∀ p ∈ ir.predicates, ir.PredOk p.body
  /-- Every challenge is well formed. -/
  challenges : ∀ c ∈ ir.challenges, ir.ChallengeOk c
  /-- Every member check is well formed. -/
  checks : ∀ m ∈ ir.statement.checks, ir.CheckOk m
  /-- Every value's field is well formed. -/
  fields : ∀ v < ir.values.length, ir.FieldOk v

theorem wellFormed_iff : ir.WellFormed ↔
    (∀ d ∈ ir.domains, d.field < ir.fields.length) ∧ (∀ v < ir.values.length, ir.ValueOk v) ∧
      ir.ExprsOk ∧ (∀ p ∈ ir.predicates, ir.PredOk p.body) ∧
      (∀ c ∈ ir.challenges, ir.ChallengeOk c) ∧ (∀ m ∈ ir.statement.checks, ir.CheckOk m) ∧
      (∀ v < ir.values.length, ir.FieldOk v) :=
  ⟨fun h => ⟨h.domains, h.values, h.exprs, h.predicates, h.challenges, h.checks, h.fields⟩,
    fun ⟨h1, h2, h3, h4, h5, h6, h7⟩ => ⟨h1, h2, h3, h4, h5, h6, h7⟩⟩

variable {ir} in
/-- **A value of type `Bit` or `Sub(E)` lies in its domain** (`FieldOk`). -/
theorem WellFormed.field_none_of_type (hwf : ir.WellFormed) {v : ℕ} (hv : v < ir.values.length)
    (ht : (ir.value v).type ≠ .field) : (ir.value v).field = none := by
  have h := hwf.fields v hv
  unfold FieldOk at h
  revert h
  cases (ir.value v).field with
  | none => exact fun _ => rfl
  | some f => exact fun h => absurd h.2.2 ht

/-! ## Messages -/

/-- **The message order on identifiers**: by phase, then by identifier (`PhaseLayout.MsgBefore` on
the program's layout). -/
def MsgBeforeId (u v : ℕ) : Prop :=
  (ir.value u).phase < (ir.value v).phase ∨ ((ir.value u).phase = (ir.value v).phase ∧ u < v)

instance (u v : ℕ) : Decidable (ir.MsgBeforeId u v) := inferInstanceAs (Decidable (_ ∨ _))

/-- **A message matches its value**: the value is a late value of the program's phases, with the
message's domain, field, phase, size, space and late realization. -/
def MessageOk (m : Message) : Prop :=
  m.value < ir.values.length ∧ ir.IsLate m.value ∧ (ir.value m.value).domain = m.domain ∧
    (ir.value m.value).field = m.field ∧
    (ir.value m.value).phase = m.phase ∧ (ir.value m.value).size = m.size ∧
    (ir.value m.value).padSpace = m.space ∧ (ir.value m.value).realization = m.realization

instance (m : Message) : Decidable (ir.MessageOk m) := by unfold MessageOk; infer_instance

/-- **The messages are the late values in `MsgBefore` order.** -/
structure MessagesMatch : Prop where
  /-- Every message matches its value. -/
  values : ∀ m ∈ ir.messages, ir.MessageOk m
  /-- The messages are in strictly increasing `MsgBefore` order. -/
  ordered : (ir.messages.map (·.value)).Pairwise ir.MsgBeforeId
  /-- Every late value has a message. -/
  complete : ∀ v < ir.values.length, ir.isLateNode v = true → v ∈ ir.messages.map (·.value)

theorem messagesMatch_iff : ir.MessagesMatch ↔
    (∀ m ∈ ir.messages, ir.MessageOk m) ∧ (ir.messages.map (·.value)).Pairwise ir.MsgBeforeId ∧
      (∀ v < ir.values.length, ir.isLateNode v = true → v ∈ ir.messages.map (·.value)) :=
  ⟨fun h => ⟨h.values, h.ordered, h.complete⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩

instance : Decidable ir.MessagesMatch := decidable_of_iff _ ir.messagesMatch_iff.symm

/-! ## Reads and degrees -/

/-- **The exported reads are sound**: every predicate's reads contain those computed from its
expressions. -/
def ReadsSound : Prop := ∀ p ∈ ir.predicates, ∀ rd ∈ ir.predReads p.body, rd ∈ p.reads

/-- **The exported degrees are sound**: every predicate's degree in every challenge bounds the
degree computed from its expressions (the largest over their coordinates, `exprDeg`), and every
public expression's degree bounds the largest over its coordinates. -/
structure DegreesSound : Prop where
  /-- The predicates' degrees. -/
  predicates : ∀ p ∈ ir.predicates, ∀ c < ir.challenges.length, ir.exprDeg c p.body ≤ p.deg c
  /-- The public expressions' degrees. -/
  values : ∀ v < ir.values.length, ir.isPubExpr v = true → ∀ c < ir.challenges.length,
    maxBelow (ir.value v).size (ir.nodeDegAt c ir.fuel v) ≤ ((ir.value v).degree.lookup c).getD 0

/-! ## The challenge order -/

/-- **The challenge order, part (a)**, for late value `v` and one of its reads: it reads only
challenges of phases at most its own, and pads (no late value: a late value's reads are its honest
computation's, closed under the late values it depends on). -/
def LateReadOrdered (v : ℕ) : Read → Prop
  | .chal c => (ir.challenge c).phase ≤ (ir.value v).phase
  | .late _ => False
  | .pad _ => True

instance (v : ℕ) (rd : Read) : Decidable (ir.LateReadOrdered v rd) := by
  cases rd <;> unfold LateReadOrdered <;> infer_instance

/-- **The challenge order, part (a)**, for late value `v`: every read is ordered
(`LateReadOrdered`). -/
def LateReadsOrdered (v : ℕ) : Prop := ∀ rd ∈ (ir.value v).reads, ir.LateReadOrdered v rd

instance (v : ℕ) : Decidable (ir.LateReadsOrdered v) := by
  unfold LateReadsOrdered; infer_instance

/-- **The challenge order, part (b)**, for a read of a predicate at challenge `c`: a late value that
`c` tests, one not computed from `c` (`c` is not among its reads, which are closed under the late
values it depends on), has phase below `c`'s. A late value computed from `c` is chosen after `c`, so
`c` is one of its coefficients, not a test of it; challenges are not chosen by the prover and are
not tested (the C++'s rule, compiler/lowering.h `infer_phases`: a challenge tests the prover-chosen
values a constraint reads with it that are not computed from it). -/
def PredReadOrdered (c : ℕ) : Read → Prop
  | .chal _ => True
  | .late u => Read.chal c ∈ (ir.value u).reads ∨ (ir.value u).phase < (ir.challenge c).phase
  | .pad _ => True

instance (c : ℕ) (rd : Read) : Decidable (ir.PredReadOrdered c rd) := by
  cases rd <;> unfold PredReadOrdered <;> infer_instance

/-- **The challenge order, part (b)**, for a source predicate `p` at challenge `c`: when
`deg_c(p) > 0`, every late value `p` reads that `c` tests is fixed before `c` (`PredReadOrdered`). -/
def PredReadsOrdered (p : Predicate) (c : ℕ) : Prop :=
  p.role.isSource = true → 0 < p.deg c → ∀ rd ∈ p.reads, ir.PredReadOrdered c rd

instance (p : Predicate) (c : ℕ) : Decidable (ir.PredReadsOrdered p c) := by
  unfold PredReadsOrdered; infer_instance

/-- **The challenge order, part (c), for an `in` realization** with reads `rds`: realized by lookups
into group `g` of a table with challenge `α`, every late value it reads, the group's late histogram
and the digits have phase below `α`'s. -/
def InRealOrdered (rds : List Read) : InRealization → Prop
  | .lookup r =>
      (∀ u ∈ Read.lates rds, (ir.value u).phase < (ir.challenge (ir.table r.table).alpha).phase) ∧
      (∀ m ∈ ((ir.table r.table).groups.getD r.group default).lateMult.toList,
        (ir.value m).phase < (ir.challenge (ir.table r.table).alpha).phase) ∧
      (∀ u ∈ r.digitValues ++ r.second,
        (ir.value u).phase < (ir.challenge (ir.table r.table).alpha).phase)
  | .implied _ _ => True

instance (rds : List Read) (real : InRealization) : Decidable (ir.InRealOrdered rds real) := by
  cases real <;> unfold InRealOrdered <;> infer_instance

/-- **The challenge order, part (c), for a predicate body** with reads `rds`: an `in`'s realization
(`InRealOrdered`); for a cross-field `equal`, the key's phase is at most the tag's and every
accumulator's. -/
def BodyOrdered (rds : List Read) : PredBody → Prop
  | .equal _ _ _ _ => True
  | .mem _ _ _ real => ir.InRealOrdered rds real
  | .mod _ _ _ _ _ => True
  | .cross _ _ _ _ _ real =>
      (ir.challenge real.key).phase ≤ (ir.value real.tag).phase ∧
        ∀ u ∈ real.accumulators, (ir.challenge real.key).phase ≤ (ir.value u).phase

instance (rds : List Read) (b : PredBody) : Decidable (ir.BodyOrdered rds b) := by
  cases b <;> unfold BodyOrdered <;> infer_instance

/-- **The challenge order, part (c)**, the phase conditions of a predicate's realization
(`BodyOrdered`). -/
def RealizationOrdered (p : Predicate) : Prop := ir.BodyOrdered p.reads p.body

instance (p : Predicate) : Decidable (ir.RealizationOrdered p) :=
  inferInstanceAs (Decidable (ir.BodyOrdered _ _))

/-- **The challenge order.** -/
structure ChallengeOrder : Prop where
  /-- (a) Late values read challenges of phases at most their own. -/
  late : ∀ v < ir.values.length, ir.isLateNode v = true → ir.LateReadsOrdered v
  /-- (b) Predicates read the late values each challenge of positive degree tests before it. -/
  preds : ∀ p ∈ ir.predicates, ∀ c < ir.challenges.length, ir.PredReadsOrdered p c
  /-- (c) The realizations' phase conditions. -/
  realizations : ∀ p ∈ ir.predicates, ir.RealizationOrdered p

theorem challengeOrder_iff : ir.ChallengeOrder ↔
    (∀ v < ir.values.length, ir.isLateNode v = true → ir.LateReadsOrdered v) ∧
      (∀ p ∈ ir.predicates, ∀ c < ir.challenges.length, ir.PredReadsOrdered p c) ∧
      (∀ p ∈ ir.predicates, ir.RealizationOrdered p) :=
  ⟨fun h => ⟨h.late, h.preds, h.realizations⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩

instance : Decidable ir.ChallengeOrder := decidable_of_iff _ ir.challengeOrder_iff.symm

/-! ## The pad order -/

/-- Whether value `v` is pad-realized. -/
def isPadRealized (v : ℕ) : Bool :=
  match (ir.value v).realization with
  | .pad _ => true
  | .commitment _ => false

/-- **The pad order** for late value `v`: every pad it reads is the pad of a pad-realized late value
of a strictly earlier message. -/
def PadsBefore (v : ℕ) : Prop :=
  ∀ u ∈ Read.pads (ir.value v).reads,
    u < ir.values.length ∧ ir.IsLate u ∧ ir.isPadRealized u = true ∧ ir.MsgBeforeId u v

instance (v : ℕ) : Decidable (ir.PadsBefore v) := by
  unfold PadsBefore; infer_instance

/-- **The pad order.** -/
def PadOrderValid : Prop := ∀ v < ir.values.length, ir.isLateNode v = true → ir.PadsBefore v

instance : Decidable ir.PadOrderValid := by unfold PadOrderValid; infer_instance

/-- **Every late value is pad-realized** (`commitment` realizations are rejected). -/
def PadRealized : Prop := ∀ v < ir.values.length, ir.isLateNode v = true → ir.isPadRealized v = true

instance : Decidable ir.PadRealized := by unfold PadRealized; infer_instance

/-! ## Type sources -/

/-- **A type source for value `v`**, the nodes of each domain's packing tree being `treeNodes`: a
committed or late value of type `Bit` or `Sub(E)` is stored at the node of that subfield (its
packing-tree node, or for a late value its pad space, the whole field when the node is the domain
field's own, the root of its tree), a node of its domain's tree; or, for `Bit`,
its type source is its Boolean check, a predicate of role `type v`. A value bound to its digits has
no cell; its digits' ranges bound it. -/
def TypeSourced (treeNodes : ℕ → List String) (v : ℕ) : Prop :=
  if (ir.value v).kind.isBound then True else
  match (ir.value v).type.nodeName with
  | none => True
  | some s =>
    match (ir.value v).typeSource with
    | .node =>
        s ∈ treeNodes (ir.value v).domain ∧
          (if ir.isLateNode v then
             (ir.value v).padSpace = Space.node s ∨
               ((ir.value v).padSpace = .full ∧
                 s = (ir.field (ir.domainField (ir.value v).domain)).name)
           else (ir.value v).node.map (·.name) = some s)
    | .pred p => (ir.value v).type = .bit ∧ p < ir.predicates.length ∧
        (ir.predicate p).body.isBoolCheck v = true ∧ (ir.predicate p).role = .type v
    | .none => False

instance (treeNodes : ℕ → List String) (v : ℕ) : Decidable (ir.TypeSourced treeNodes v) := by
  unfold TypeSourced
  split
  · infer_instance
  · split
    · infer_instance
    · split <;> infer_instance

/-- **Every committed or late `Bit` and `Sub(E)` value has a type source.** -/
def TypeSources (treeNodes : ℕ → List String) : Prop :=
  ∀ v < ir.values.length, (ir.isCommitted v || ir.isLateNode v) = true → ir.TypeSourced treeNodes v

instance (treeNodes : ℕ → List String) : Decidable (ir.TypeSources treeNodes) := by
  unfold TypeSources; infer_instance

/-! ## Targets -/

/-- **The degree of an expression in the committed cells** (committed values, bit views, pad
copies and late values, a late value being its message minus its pad; public values and
coefficients have degree `0`). -/
def cellDeg (e : Expr) : ℕ :=
  ir.degOf (fun v => if ir.isCommitted v || ir.isLateNode v then 1 else 0) e

/-- **A cell of the quadratic test** (compiler/compiled_domain.h, `place_predicates`): a committed
value of phase `0`, typed `Field` (so stored at the root, outside the relatively packed subfield
region), unbound (a value node, not a derived value). -/
def isQuadCell (v : ℕ) : Bool :=
  match (ir.value v).kind with
  | .priv => (ir.value v).phase == 0 && (ir.value v).type == .field
  | _ => false

/-- **The quadratic form** `a · b = c` on single cells of the quadratic test (`isQuadCell`). -/
def isQuadratic : Expr → Expr → Bool
  | .mul (.leaf a) (.leaf b), .leaf c => ir.isQuadCell a && ir.isQuadCell b && ir.isQuadCell c
  | _, _ => false

/-- **The skip domain's limit** at degree `D`, width `w` and characteristic `p`: `D(w − 1) < p` in
odd characteristic, `D(w − 1) + 1 ≤ 256` in characteristic two. -/
def SkipFits (D w p : ℕ) : Prop := if p = 2 then D * (w - 1) + 1 ≤ 256 else D * (w - 1) < p

instance (D w p : ℕ) : Decidable (SkipFits D w p) := by unfold SkipFits; infer_instance

/-- **The skip domain's name** in characteristic `p`: `gf256` in characteristic two, `integers`
otherwise (compiler/field_skip.h, `SkipDomain`). -/
def skipDomainName (p : ℕ) : String := if p = 2 then "gf256" else "integers"

/-- **Batch `b` admits predicate `pid`** with sides `e`, `e'` in domain `d`: the batch is of the
domain and lists the predicate among its parts; the sides read only batch operands (values
committed in phase `0`, constants, statement values), have degree at most `D ≥ 1` in the committed
cells (`cellDeg`: a constant, such as a constant mask column, has degree `0`, so a constant-masked
affine view is of degree one, one operand of the batch form, `RealizedProgram.atomB`), vanish at
zero and fit the instances, `N` lanes of `OperandMap.lane` coordinates each (`64` on bits); the skip
domain is the characteristic's and admits `D`; and the instances' coordinates fit the rows,
`lane · N ≤ 2^n · w` (as `RealizedProgram.BatchOk` states them). -/
def BatchAdmits (pid d b : ℕ) (e e' : Expr) : Prop :=
  let B := ir.batch b
  let p := (ir.field (ir.domainField d)).characteristic
  b < ir.batches.length ∧ B.domain = d ∧ pid ∈ B.parts ∧
    (∀ v ∈ ir.exprNodes e ++ ir.exprNodes e', ir.isBatchNode v = true) ∧
    1 ≤ B.degree ∧ ir.cellDeg e ≤ B.degree ∧ ir.cellDeg e' ≤ B.degree ∧
    ir.zeroOf e = true ∧ ir.zeroOf e' = true ∧ B.skipDomain = skipDomainName p ∧
    SkipFits B.degree B.width p ∧ ir.exprLen e ≤ B.operands.lane * B.instances ∧
    B.operands.lane * B.instances ≤ 2 ^ B.rounds * B.width

/-- **A value of kind `k` is an input of a GKR circuit with layout `ins`**
(compiler/compiled_domain.h, `need`): a committed value or a pad copy as committed coordinates, a
bit view as a view block, a late value as its message (public) and its pad, a public value, a
challenge value or a message as a public input; a constant needs no input (the export writes the
circuit's constant expressions as constant values), nor does a value bound to its digits (the
circuit reads its digits). -/
def IsCircuitInputOf (ins : List InputBlock) (v : ℕ) : Kind → Prop
  | .priv => ins.any (·.isCommittedOf v) = true
  | .pub _ => ins.any (·.isPubOf v) = true
  | .constant _ => True
  | .challenge _ => ins.any (·.isPubOf v) = true
  | .late => ins.any (·.isPubOf v) = true ∧ ins.any (·.isPadOf v) = true
  | .bits _ _ => ins.any (·.isViewOf v) = true
  | .padCopy _ _ => ins.any (·.isCommittedOf v) = true
  | .message _ => ins.any (·.isPubOf v) = true
  | .bound _ => True

instance (ins : List InputBlock) (v : ℕ) (k : Kind) : Decidable (IsCircuitInputOf ins v k) := by
  cases k <;> unfold IsCircuitInputOf <;> infer_instance

/-- **Circuit `c` admits predicate `pid`** with sides `e`, `e'` in domain `d`: the circuit is of
the domain, lists the predicate, and has every value the sides read among its inputs. -/
def GkrAdmits (pid d c : ℕ) (e e' : Expr) : Prop :=
  c < ir.circuits.length ∧ (ir.circuit c).domain = d ∧ pid ∈ (ir.circuit c).predicates ∧
    ∀ v ∈ ir.exprNodes e ++ ir.exprNodes e', IsCircuitInputOf (ir.circuit c).inputs v (ir.value v).kind

/-! ### Convolutions realized through a transform -/

/-- Whether a target is a realization predicate's (`Target.realized`). -/
def _root_.GordieHowe.RealizedProgram.Target.isRealized : Target → Bool
  | .realized _ => true
  | _ => false


/-- **A constant holding `0`**: a constant value whose every entry is `0`. -/
def zeroConst (z : ℕ) : Bool :=
  match (ir.value z).kind with
  | .constant es => es.all (· == 0)
  | _ => false

/-- **The parts of a source convolution** (`SpectralConv.source`): the sum width `la`, the two
operands' views `mA`, `mB`, the operands `a`, `b` and their zero constants `zA`, `zB`. -/
structure ConvSource where
  /-- The sum width. -/
  la : ℕ
  /-- The left operand's view. -/
  mA : IndexMap
  /-- The left operand. -/
  a : Expr
  /-- The left operand's zero constant. -/
  zA : ℕ
  /-- The right operand's view. -/
  mB : IndexMap
  /-- The right operand. -/
  b : Expr
  /-- The right operand's zero constant. -/
  zB : ℕ

/-- **The parts of an expression of the source convolution's form**
`.apply (.sum la) (.mul (.reindex mA (.concat a (.leaf zA))) (.reindex mB (.concat b (.leaf zB))))`,
none for any other. -/
def _root_.GordieHowe.RealizedProgram.Expr.convSource? : Expr → Option ConvSource
  | .apply (.sum la) (.mul (.reindex mA (.concat a (.leaf zA))) (.reindex mB (.concat b (.leaf zB)))) =>
    some ⟨la, mA, a, zA, mB, b, zB⟩
  | _ => none

/-- **The parts of a reading through the inverse transform** (`SpectralConv.read`): the gather
`g`, the blocks `B`, the length `M`, the root `ψ` and the transformed value `z`. -/
structure ConvRead where
  /-- The gather. -/
  g : IndexMap
  /-- The blocks. -/
  B : ℕ
  /-- The transform length. -/
  M : ℕ
  /-- The root. -/
  psi : ℕ
  /-- The transformed value. -/
  z : ℕ

/-- **The parts of an expression of the form**
`.reindex g (.apply (.batched B (.inverseNtt M ψ)) (.leaf z))`, none for any other. -/
def _root_.GordieHowe.RealizedProgram.Expr.convRead? : Expr → Option ConvRead
  | .reindex g (.apply (.batched B (.inverseNtt M psi)) (.leaf z)) => some ⟨g, B, M, psi, z⟩
  | _ => none

/-- **The parts of a spectral product** (the left side of `SpectralConv.products`): each operand's
blocks, length, root, zero extension, operand and zero constant. -/
structure ConvProducts where
  /-- The left transform's blocks. -/
  B : ℕ
  /-- The left transform's length. -/
  M : ℕ
  /-- The left transform's root. -/
  psi : ℕ
  /-- The left operand's zero extension. -/
  pA : IndexMap
  /-- The left operand. -/
  a : Expr
  /-- The left operand's zero constant. -/
  zA : ℕ
  /-- The right transform's blocks. -/
  B' : ℕ
  /-- The right transform's length. -/
  M' : ℕ
  /-- The right transform's root. -/
  psi' : ℕ
  /-- The right operand's zero extension. -/
  pB : IndexMap
  /-- The right operand. -/
  b : Expr
  /-- The right operand's zero constant. -/
  zB : ℕ

/-- **The parts of an expression of the form** `NTT(pA (a, 0)) · NTT(pB (b, 0))`,
`.mul (.apply (.batched B (.ntt M ψ .scheme)) (.reindex pA (.concat a (.leaf zA))))
(.apply (.batched B' (.ntt M' ψ' .scheme)) (.reindex pB (.concat b (.leaf zB))))`, none for any
other. -/
def _root_.GordieHowe.RealizedProgram.Expr.convProducts? : Expr → Option ConvProducts
  | .mul (.apply (.batched B (.ntt M psi .scheme)) (.reindex pA (.concat a (.leaf zA))))
      (.apply (.batched B' (.ntt M' psi' .scheme)) (.reindex pB (.concat b (.leaf zB)))) =>
    some ⟨B, M, psi, pA, a, zA, B', M', psi', pB, b, zB⟩
  | _ => none

/-- **The facts of a spectrally realized convolution** `c` in domain `d` (field `F` of
characteristic `p`), its source's parts `s`, its reading's `r` and its products' `q`, `z` the
transformed value: the identifiers exist; the source sums width `la` over the operands' views
`IndexMap.convLeft B la lb` and `IndexMap.convRight B la lb`; the reading gathers the first
`la + lb − 1` coordinates of each block of `INTT_M(z)` at the root `ψ`; the products are
`NTT_M` at `ψ` of the same operands zero-extended to `M` (`IndexMap.zeroExtend`); the zero
constants and `z` lie in `F`, the constants holding `0`; the operands have `B la` and `B lb`
coordinates; and the transform computes the product: `M = 2^k ≥ la + lb − 1` with `la, lb ≥ 1`,
`2 < p`, `ψ, M < p`, and `ψ^M ≡ −1 (mod p)`, so `ψ` is a primitive `2M`-th root of unity of `F` and
`M` is invertible. -/
structure ConvFacts (c : SpectralConv) (s : ConvSource) (r : ConvRead) (q : ConvProducts)
    (d z : ℕ) : Prop where
  source_lt : c.source < ir.exprs.length
  read_lt : c.read < ir.exprs.length
  products_lt : c.products < ir.predicates.length
  la : s.la = c.left
  mA : s.mA = IndexMap.convLeft c.blocks c.left c.right
  mB : s.mB = IndexMap.convRight c.blocks c.left c.right
  g : r.g = IndexMap.blockPrefix c.blocks c.length (c.left + c.right - 1)
  rB : r.B = c.blocks
  rM : r.M = c.length
  rpsi : r.psi = c.root
  rz : r.z = z
  qB : q.B = c.blocks ∧ q.B' = c.blocks
  qM : q.M = c.length ∧ q.M' = c.length
  qpsi : q.psi = c.root ∧ q.psi' = c.root
  pA : q.pA = IndexMap.zeroExtend c.blocks c.left c.length
  pB : q.pB = IndexMap.zeroExtend c.blocks c.right c.length
  qa : q.a = s.a
  qb : q.b = s.b
  zeros : ∀ v ∈ [s.zA, s.zB, q.zA, q.zB], ir.zeroConst v = true
  fields : ∀ v ∈ [s.zA, s.zB, q.zA, q.zB, z], ir.valueField v = ir.domainField d
  lenA : ir.exprLen s.a = c.blocks * c.left
  lenB : ir.exprLen s.b = c.blocks * c.right
  left_pos : 0 < c.left
  right_pos : 0 < c.right
  fits : c.left + c.right - 1 ≤ c.length
  pow2 : c.length = 2 ^ Nat.log2 c.length
  char : 2 < (ir.field (ir.domainField d)).characteristic
  root_lt : c.root < (ir.field (ir.domainField d)).characteristic
  length_lt : c.length < (ir.field (ir.domainField d)).characteristic
  root_pow : c.root ^ c.length % (ir.field (ir.domainField d)).characteristic =
    (ir.field (ir.domainField d)).characteristic - 1

theorem convFacts_iff (c : SpectralConv) (s : ConvSource) (r : ConvRead) (q : ConvProducts)
    (d z : ℕ) : ir.ConvFacts c s r q d z ↔
      c.source < ir.exprs.length ∧ c.read < ir.exprs.length ∧ c.products < ir.predicates.length ∧
      s.la = c.left ∧ s.mA = IndexMap.convLeft c.blocks c.left c.right ∧
      s.mB = IndexMap.convRight c.blocks c.left c.right ∧
      r.g = IndexMap.blockPrefix c.blocks c.length (c.left + c.right - 1) ∧ r.B = c.blocks ∧
      r.M = c.length ∧ r.psi = c.root ∧ r.z = z ∧ (q.B = c.blocks ∧ q.B' = c.blocks) ∧
      (q.M = c.length ∧ q.M' = c.length) ∧ (q.psi = c.root ∧ q.psi' = c.root) ∧
      q.pA = IndexMap.zeroExtend c.blocks c.left c.length ∧
      q.pB = IndexMap.zeroExtend c.blocks c.right c.length ∧ q.a = s.a ∧ q.b = s.b ∧
      (∀ v ∈ [s.zA, s.zB, q.zA, q.zB], ir.zeroConst v = true) ∧
      (∀ v ∈ [s.zA, s.zB, q.zA, q.zB, z], ir.valueField v = ir.domainField d) ∧
      ir.exprLen s.a = c.blocks * c.left ∧ ir.exprLen s.b = c.blocks * c.right ∧
      0 < c.left ∧ 0 < c.right ∧ c.left + c.right - 1 ≤ c.length ∧
      c.length = 2 ^ Nat.log2 c.length ∧ 2 < (ir.field (ir.domainField d)).characteristic ∧
      c.root < (ir.field (ir.domainField d)).characteristic ∧
      c.length < (ir.field (ir.domainField d)).characteristic ∧
      c.root ^ c.length % (ir.field (ir.domainField d)).characteristic =
        (ir.field (ir.domainField d)).characteristic - 1 :=
  ⟨fun h => ⟨h.source_lt, h.read_lt, h.products_lt, h.la, h.mA, h.mB, h.g, h.rB, h.rM, h.rpsi,
      h.rz, h.qB, h.qM, h.qpsi, h.pA, h.pB, h.qa, h.qb, h.zeros, h.fields, h.lenA, h.lenB,
      h.left_pos, h.right_pos, h.fits, h.pow2, h.char, h.root_lt, h.length_lt, h.root_pow⟩,
    fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
        h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
        h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩⟩

instance (c : SpectralConv) (s : ConvSource) (r : ConvRead) (q : ConvProducts) (d z : ℕ) :
    Decidable (ir.ConvFacts c s r q d z) :=
  decidable_of_iff _ (ir.convFacts_iff c s r q d z).symm

/-- **The products side `lhs` has the parts of a spectral product** (`Expr.convProducts?`) with
the facts `ConvFacts` of `c`, `s`, `r` at domain `d` and transformed value `z`. -/
def ConvProductsOk (c : SpectralConv) (s : ConvSource) (r : ConvRead) (d z : ℕ) (lhs : Expr) :
    Prop :=
  match lhs.convProducts? with
  | some q => ir.ConvFacts c s r q d z
  | none => False

/-- **`ConvProductsOk`, decided.** -/
def convProductsOkB (c : SpectralConv) (s : ConvSource) (r : ConvRead) (d z : ℕ) (lhs : Expr) :
    Bool :=
  match lhs.convProducts? with
  | some q => decide (ir.ConvFacts c s r q d z)
  | none => false

theorem convProductsOkB_iff (c : SpectralConv) (s : ConvSource) (r : ConvRead) (d z : ℕ)
    (lhs : Expr) : ir.convProductsOkB c s r d z lhs = true ↔ ir.ConvProductsOk c s r d z lhs := by
  unfold convProductsOkB ConvProductsOk
  cases lhs.convProducts? <;> simp

instance (c : SpectralConv) (s : ConvSource) (r : ConvRead) (d z : ℕ) (lhs : Expr) :
    Decidable (ir.ConvProductsOk c s r d z lhs) :=
  decidable_of_iff _ (ir.convProductsOkB_iff c s r d z lhs)

/-- **The convolution `c` is spectrally realized in domain `d`** (compiler/conv.h, the batch
form): its source and its reading have the forms of `Expr.convSource?` and `Expr.convRead?`, its
products predicate is a field `equal` of `d` between a spectral product (`Expr.convProducts?`) and
the transformed value `z` whose target is no realization's, and the facts `ConvFacts` hold
(`ConvProductsOk`). Then, wherever the
products predicate holds, the reading equals the source below their common length
(`RealizedProgram.convRead_eq_source`). -/
def ConvOkAt (d : ℕ) (c : SpectralConv) : Prop :=
  match (ir.expr c.source).convSource?, (ir.expr c.read).convRead?,
      (ir.predicate c.products).body with
  | some s, some r, .equal d' lhs (.leaf z) t =>
    d' = d ∧ t.isRealized = false ∧ ir.ConvProductsOk c s r d z lhs
  | _, _, _ => False

/-- **`ConvOkAt`, decided.** -/
def convOkAtB (d : ℕ) (c : SpectralConv) : Bool :=
  match (ir.expr c.source).convSource?, (ir.expr c.read).convRead?,
      (ir.predicate c.products).body with
  | some s, some r, .equal d' lhs (.leaf z) t =>
    decide (d' = d) && !t.isRealized && ir.convProductsOkB c s r d z lhs
  | _, _, _ => false

theorem convOkAtB_iff (d : ℕ) (c : SpectralConv) : ir.convOkAtB d c = true ↔ ir.ConvOkAt d c := by
  unfold convOkAtB ConvOkAt
  cases (ir.expr c.source).convSource? <;> cases (ir.expr c.read).convRead? <;>
    cases (ir.predicate c.products).body <;> try simp
  all_goals
    rename_i d' lhs rhs t
    cases rhs <;> simp [convProductsOkB_iff, and_assoc]

instance (d : ℕ) (c : SpectralConv) : Decidable (ir.ConvOkAt d c) :=
  decidable_of_iff _ (ir.convOkAtB_iff d c)

/-- **Shared expressions `k` and `k'` are a convolution and its reading** in domain `d`: some
spectrally realized convolution of the program (`ConvOkAt`) has the source `k` and the reading
`k'`. -/
def ConvPair (d k k' : ℕ) : Prop :=
  ∃ c ∈ ir.convs, c.source = k ∧ c.read = k' ∧ ir.ConvOkAt d c

instance (d k k' : ℕ) : Decidable (ir.ConvPair d k k') :=
  inferInstanceAs (Decidable (∃ c ∈ ir.convs, _))

/-- **`E` is `e` with some shared expressions replaced by others** (`P k k'`: `k` may be read as
`k'`): the two have the same form through sums, differences, constant or public multiples,
products, views, concatenations and named operators, the same parameters, and at their leaves
the same expression, or shared expressions `k`, `k'` with `k = k'` or `P k k'`. -/
def _root_.GordieHowe.RealizedProgram.Expr.matchB (P : ℕ → ℕ → Bool) : Expr → Expr → Bool
  | .ref k, .ref k' => k == k' || P k k'
  | .add a b, .add a' b' => Expr.matchB P a a' && Expr.matchB P b b'
  | .sub a b, .sub a' b' => Expr.matchB P a a' && Expr.matchB P b b'
  | .mul a b, .mul a' b' => Expr.matchB P a a' && Expr.matchB P b b'
  | .concat a b, .concat a' b' => Expr.matchB P a a' && Expr.matchB P b b'
  | .scale c a, .scale c' a' => decide (c = c') && Expr.matchB P a a'
  | .reindex m a, .reindex m' a' => decide (m = m') && Expr.matchB P a a'
  | .apply op a, .apply op' a' => decide (op = op') && Expr.matchB P a a'
  | e, e' => e.beq e'

/-- **Predicate `q` realizes the field equation `e = e'` of domain `d`** (`Target.realized`):
`q` is a field `equal` of `d` whose target is no realization's, and its sides are `e` and `e'` with
convolutions read through their spectral realizations (`Expr.matchB` at `ConvPair d`). Then the
field equation holds wherever `q` and the realizations' products predicates do
(`RealizedProgram.fieldEq_of_realized`). -/
def RealizedAdmits (d : ℕ) (e e' : Expr) (q : ℕ) : Prop :=
  q < ir.predicates.length ∧
    match (ir.predicate q).body with
    | .equal d' E E' t => d' = d ∧ t.isRealized = false ∧
        Expr.matchB (fun k k' => decide (ir.ConvPair d k k')) e E = true ∧
        Expr.matchB (fun k k' => decide (ir.ConvPair d k k')) e' E' = true
    | _ => False

/-- **`RealizedAdmits`, decided.** -/
def realizedAdmitsB (d : ℕ) (e e' : Expr) (q : ℕ) : Bool :=
  decide (q < ir.predicates.length) &&
    match (ir.predicate q).body with
    | .equal d' E E' t => decide (d' = d) && !t.isRealized &&
        Expr.matchB (fun k k' => decide (ir.ConvPair d k k')) e E &&
        Expr.matchB (fun k k' => decide (ir.ConvPair d k k')) e' E'
    | _ => false

theorem realizedAdmitsB_iff (d : ℕ) (e e' : Expr) (q : ℕ) :
    ir.realizedAdmitsB d e e' q = true ↔ ir.RealizedAdmits d e e' q := by
  unfold realizedAdmitsB RealizedAdmits
  cases (ir.predicate q).body <;> simp [and_assoc]

instance (d : ℕ) (e e' : Expr) (q : ℕ) : Decidable (ir.RealizedAdmits d e e' q) :=
  decidable_of_iff _ (ir.realizedAdmitsB_iff d e e' q)

/-- **Target `t` admits the field equation `e = e'`** of predicate `pid` in domain `d`
(`TargetsAdmit`): `affine`, degree at most one in the committed cells (coefficients and constants
may read public values and challenges); `quadratic`, `a · b = c` on single cells of the quadratic
test (`isQuadratic`); `batch`, `BatchAdmits`; `gkr`, `GkrAdmits`; `realized`, `RealizedAdmits`. -/
def TargetAdmits (pid d : ℕ) (e e' : Expr) : Target → Prop
  | .affine => ir.cellDeg e ≤ 1 ∧ ir.cellDeg e' ≤ 1
  | .quadratic => ir.isQuadratic e e' = true
  | .batch b => ir.BatchAdmits pid d b e e'
  | .gkr c => ir.GkrAdmits pid d c e e'
  | .realized q => ir.RealizedAdmits d e e' q

/-- **The target of a predicate body**: a field `equal`'s, or a `mod_q`'s field equation's (`q = 0`,
or `q` the characteristic of a prime-field `mod_q`). -/
def PredBody.target : PredBody → Option Target
  | .equal _ _ _ t => some t
  | .mem _ _ _ _ => none
  | .mod _ _ _ _ real => real.target
  | .cross _ _ _ _ _ _ => none

/-- **A side condition admitted by an optional target**: by the target, or true without one. -/
def OptTargetAdmits (pid d : ℕ) (e e' : Expr) : Option Target → Prop
  | some t => ir.TargetAdmits pid d e e' t
  | none => True

/-- **Predicate body `b` of predicate `pid` is admitted by its target**: a field `equal` by its
target; a `mod_q` that carries a field equation by its target, and a `mod_0` must carry one; the
other predicates have no target. -/
def BodyAdmitted (pid : ℕ) : PredBody → Prop
  | .equal d e e' t => ir.TargetAdmits pid d e e' t
  | .mem _ _ _ _ => True
  | .mod d q e e' real => (q = 0 → real.target.isSome) ∧ ir.OptTargetAdmits pid d e e' real.target
  | .cross _ _ _ _ _ _ => True

/-- **Predicate `pid` is admitted by its target** (`BodyAdmitted`). -/
def PredAdmitted (pid : ℕ) : Prop := ir.BodyAdmitted pid (ir.predicate pid).body

/-- **The end of an input layout** read from input `pos`: the input after the last block when every
block starts where the previous one ends, none otherwise. -/
def _root_.GordieHowe.RealizedProgram.InputBlock.layoutEnd : ℕ → List InputBlock → Option ℕ
  | pos, [] => some pos
  | pos, b :: bs => if b.first = pos then InputBlock.layoutEnd (pos + b.len) bs else none

/-- **The predicates of an emission order**: its Boolean checks and placed predicates, in order. -/
def _root_.GordieHowe.RealizedProgram.CircuitEntry.predicate? : CircuitEntry → Option ℕ
  | .typeCheck p => some p
  | .pred p => some p
  | _ => none

/-- **A GKR circuit's layout is well formed** (stage (c)): the blocks are contiguous from input `1`
to the input count, the public blocks come first and end at `publicInputs`, and the predicates are
those of the emission order, in order. -/
structure CircuitLaidOut (c : Circuit) : Prop where
  /-- The blocks are contiguous. -/
  contiguous : InputBlock.layoutEnd 1 c.inputs = some c.inputCount
  /-- The public blocks end at `publicInputs`. -/
  publicEnd : InputBlock.layoutEnd 1 (c.inputs.takeWhile (·.isPublic)) = some c.publicInputs
  /-- No public block follows a committed one. -/
  publicFirst : (c.inputs.dropWhile (·.isPublic)).all (!·.isPublic) = true
  /-- The predicates are the emission order's. -/
  entries : c.entries.filterMap (·.predicate?) = c.predicates

theorem circuitLaidOut_iff (c : Circuit) : CircuitLaidOut c ↔
    InputBlock.layoutEnd 1 c.inputs = some c.inputCount ∧
      InputBlock.layoutEnd 1 (c.inputs.takeWhile (·.isPublic)) = some c.publicInputs ∧
      (c.inputs.dropWhile (·.isPublic)).all (!·.isPublic) = true ∧
      c.entries.filterMap (·.predicate?) = c.predicates :=
  ⟨fun h => ⟨h.contiguous, h.publicEnd, h.publicFirst, h.entries⟩,
    fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

instance (c : Circuit) : Decidable (CircuitLaidOut c) := decidable_of_iff _ (circuitLaidOut_iff c).symm

/-- **Every target admits its predicate**, every GKR circuit lists only predicates placed in it, and
every circuit's layout is well formed. -/
structure TargetsAdmit : Prop where
  /-- Every predicate is admitted by its target. -/
  predicates : ∀ pid < ir.predicates.length, ir.PredAdmitted pid
  /-- Every circuit's predicates are placed in it. -/
  circuits : ∀ c < ir.circuits.length, ∀ pid ∈ (ir.circuit c).predicates,
    pid < ir.predicates.length ∧ PredBody.target (ir.predicate pid).body = some (.gkr c)
  /-- Every circuit's layout is well formed. -/
  layouts : ∀ c ∈ ir.circuits, CircuitLaidOut c

theorem targetsAdmit_iff : ir.TargetsAdmit ↔
    (∀ pid < ir.predicates.length, ir.PredAdmitted pid) ∧
      (∀ c < ir.circuits.length, ∀ pid ∈ (ir.circuit c).predicates,
        pid < ir.predicates.length ∧ PredBody.target (ir.predicate pid).body = some (.gkr c)) ∧
      (∀ c ∈ ir.circuits, CircuitLaidOut c) :=
  ⟨fun h => ⟨h.predicates, h.circuits, h.layouts⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩

/-! ## The program's validity -/

/-- **The program is valid** for the packing-tree nodes `treeNodes` of its domains. -/
structure ValidAtNodes (treeNodes : ℕ → List String) : Prop where
  /-- Well-formedness. -/
  wellFormed : ir.WellFormed
  /-- The messages are the late values in `MsgBefore` order. -/
  messages : ir.MessagesMatch
  /-- The exported reads are sound. -/
  reads : ir.ReadsSound
  /-- The exported degrees are sound. -/
  degrees : ir.DegreesSound
  /-- The challenge order. -/
  order : ir.ChallengeOrder
  /-- The pad order. -/
  pads : ir.PadOrderValid
  /-- Type sources. -/
  types : ir.TypeSources treeNodes
  /-- The targets admit their predicates. -/
  targets : ir.TargetsAdmit
  /-- Every late value is pad-realized. -/
  padRealized : ir.PadRealized

end

end GordieHowe.RealizedProgram
