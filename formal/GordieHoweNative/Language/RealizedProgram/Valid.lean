-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Encoding
public import GordieHoweNative.Language.RealizedProgram.Semantics

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.Valid`

The definitions of `GordieHowe.Language.RealizedProgram.Valid` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/RealizedProgram/Valid.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

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

/-- **The operands a named operator requires public** (`Expr.pubNodes`): its operands
(`NamedOp.operands`), but none for a negacyclic convolution or a polynomial broadcast in transform
form, whose spectra a committed value may hold (the circuit multiplies them by the operand's
transform). -/
def NamedOp.pubOperands : NamedOp → List ℕ
  | .negacyclicConv _ (.ntt _) => []
  | .negacyclicConv _ (.nttNatural _) => []
  | .polyBroadcast _ _ (.ntt _) => []
  | .polyBroadcast _ _ (.nttNatural _) => []
  | op => op.operands

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

/-- **The values an expression requires public**: its coefficients' values and its named
operators' operands required public (`NamedOp.pubOperands`; `Expr.coefNodes` with every operand). -/
def Expr.pubNodes : Expr → List ℕ
  | .leaf _ => []
  | .add e e' => e.pubNodes ++ e'.pubNodes
  | .sub e e' => e.pubNodes ++ e'.pubNodes
  | .scale c e => c.nodes ++ e.pubNodes
  | .mul e e' => e.pubNodes ++ e'.pubNodes
  | .reindex _ e => e.pubNodes
  | .concat e e' => e.pubNodes ++ e'.pubNodes
  | .linear rows e => rows.flatMap (·.flatMap fun t => t.2.nodes) ++ e.pubNodes
  | .prod _ e => e.pubNodes
  | .mux b t e => b.pubNodes ++ t.pubNodes ++ e.pubNodes
  | .apply op e => op.pubOperands ++ op.foreignOperands ++ e.pubNodes
  | .ref _ => []
  | .logic _ _ args => Expr.pubNodesList args

/-- The values a list of expressions requires public. -/
def Expr.pubNodesList : List Expr → List ℕ
  | [] => []
  | e :: es => e.pubNodes ++ Expr.pubNodesList es

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

/-- **The expressions of a set**: `e'` for the entries of `e'`, none for a range or a table. -/
def InSet.exprs : InSet → List Expr
  | .expr e' => [e']
  | _ => []

/-- **The expressions of a predicate body**, each with its domain: an `in` reads its records and
the expression of its set, a `mod_q` its sides. -/
def PredBody.exprs : PredBody → List (ℕ × Expr)
  | .equal d e e' _ => [(d, e), (d, e')]
  | .mem d records set _ => (records ++ set.exprs).map ((d, ·))
  | .mod d _ e e' _ => [(d, e), (d, e')]
  | .cross dx x dy y _ _ => [(dx, x), (dy, y)]

section

variable (ir : RealizedProgram)

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

/-- **What value `v` reads from the run**, with `n` levels of values read by values (as
`RealizedProgram.read`): a challenge value its challenge, a late value itself, a message its late
value, a public expression, an opaque value or a bit view what the values they read read. -/
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

/-- Whether value `v` is committed in phase `0` (a committed value, a bit view of committed words, a
pad copy, or a value bound to its digits, which the source program commits). -/
def isCommitted (v : ℕ) : Bool :=
  match (ir.value v).kind with
  | .priv => true
  | .bits _ _ => true
  | .padCopy _ _ => true
  | .bound _ => true
  | _ => false

/-- Whether value `v` is late. -/
def isLateNode (v : ℕ) : Bool := (ir.value v).kind.isLate

/-- Whether value `v` is public (a statement member, an opaque or expression public value, a
constant, a challenge value or a message). -/
def isPublic (v : ℕ) : Bool := !(ir.isCommitted v) && !(ir.isLateNode v)

/-- **A Logic builder's arguments have consistent lengths** `lens`: two for `lt`, `leq`, `eq`, of
one length, one for `any` and `all`, the length a multiple of the width `w ≥ 1`. -/
def logicShapeOk (op : LogicOp) (w : ℕ) (lens : List ℕ) : Bool :=
  0 < w && lens.length == (match op with
    | .lt | .leq | .eq => 2
    | .any | .all => 1) &&
  lens.all (· == lens.headD 0) && lens.headD 0 % w == 0

mutual

/-- **An expression's lengths are consistent** (its shared expressions are checked once each,
`RealizedProgram.ExprsOk`): the operands of `+`, `-`, `·` and `mux` have one length, index maps and
sparse rows stay in range, a product's axis divides the length, a named operator's block divides its
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
  /-- The coefficients and operands are public (`Expr.pubNodes`). -/
  coefs : ∀ v ∈ ir.closure Expr.pubNodes e, ir.isPublic v = true
  /-- The shared expressions exist. -/
  refs : ∀ k ∈ e.refs, k < ir.exprs.length
  /-- The lengths are consistent. -/
  shape : ir.exprShapeOk e = true

theorem exprOk_iff (f : ℕ) (e : Expr) : ir.ExprOk f e ↔
    (∀ v ∈ ir.exprNodes e, v < ir.values.length) ∧
      (∀ v ∈ ir.closure Expr.fieldNodes e, ir.valueField v = f) ∧
      (∀ v ∈ ir.closure Expr.pubNodes e, ir.isPublic v = true) ∧
      (∀ k ∈ e.refs, k < ir.exprs.length) ∧ ir.exprShapeOk e = true :=
  ⟨fun h => ⟨h.range, h.field, h.coefs, h.refs, h.shape⟩,
    fun ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, h5⟩⟩

instance (f : ℕ) (e : Expr) : Decidable (ir.ExprOk f e) :=
  decidable_of_iff _ (ir.exprOk_iff f e).symm

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
bound value as its expression at the committed assignment, `RealizedProgram.bindAsg`, never through
the value order). -/
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

/-- **A challenge's sampler is supported** for a challenge of `size` coordinates: the field or a
node; the field minus `[0, tmax)` for a challenge of one coordinate. The packed rows of public
tables and unions are rejected (their `U` depends on an earlier challenge under the `gamma` packing;
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

/-- **The skip domain's limit** at degree `D`, width `w` and characteristic `p`: `D(w − 1) < p` in
odd characteristic, `D(w − 1) + 1 ≤ 256` in characteristic two. -/
def SkipFits (D w p : ℕ) : Prop := if p = 2 then D * (w - 1) + 1 ≤ 256 else D * (w - 1) < p

instance (D w p : ℕ) : Decidable (SkipFits D w p) := by unfold SkipFits; infer_instance

/-- **The skip domain's name** in characteristic `p`: `gf256` in characteristic two, `integers`
otherwise (compiler/field_skip.h, `SkipDomain`). -/
def skipDomainName (p : ℕ) : String := if p = 2 then "gf256" else "integers"

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
  | .apply (.sum la)
      (.mul (.reindex mA (.concat a (.leaf zA))) (.reindex mB (.concat b (.leaf zB)))) =>
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

mutual

/-- **`Expr.beq` comparing index maps and rows by `List.beq`**: the same function
(`Expr.beqK_eq`), evaluated by the kernel in depth bounded by the expressions' depth. -/
def _root_.GordieHowe.RealizedProgram.Expr.beqK : Expr → Expr → Bool
  | .leaf v, .leaf v' => v == v'
  | .add a b, .add a' b' => a.beqK a' && b.beqK b'
  | .sub a b, .sub a' b' => a.beqK a' && b.beqK b'
  | .scale c a, .scale c' a' => decide (c = c') && a.beqK a'
  | .mul a b, .mul a' b' => a.beqK a' && b.beqK b'
  | .reindex idx a, .reindex idx' a' => idx == idx' && a.beqK a'
  | .concat a b, .concat a' b' => a.beqK a' && b.beqK b'
  | .linear rows a, .linear rows' a' => rows == rows' && a.beqK a'
  | .prod n a, .prod n' a' => n == n' && a.beqK a'
  | .mux b t a, .mux b' t' a' => b.beqK b' && t.beqK t' && a.beqK a'
  | .apply op a, .apply op' a' => decide (op = op') && a.beqK a'
  | .ref k, .ref k' => k == k'
  | .logic op w args, .logic op' w' args' =>
      decide (op = op') && w == w' && Expr.beqKList args args'
  | _, _ => false

/-- `Expr.beqK` on lists of expressions. -/
def _root_.GordieHowe.RealizedProgram.Expr.beqKList : List Expr → List Expr → Bool
  | [], [] => true
  | e :: es, e' :: es' => e.beqK e' && Expr.beqKList es es'
  | _, _ => false

end

mutual

/-- **`Expr.beqK` is `Expr.beq`.** -/
theorem _root_.GordieHowe.RealizedProgram.Expr.beqK_eq :
    ∀ e e' : Expr, e.beqK e' = e.beq e'
  | .leaf _, e' => by cases e' <;> rfl
  | .add a b, e' => by
    cases e' <;> try rfl
    simp only [Expr.beqK, Expr.beq, Expr.beqK_eq a, Expr.beqK_eq b]
  | .sub a b, e' => by
    cases e' <;> try rfl
    simp only [Expr.beqK, Expr.beq, Expr.beqK_eq a, Expr.beqK_eq b]
  | .scale _ a, e' => by
    cases e' <;> try rfl
    simp only [Expr.beqK, Expr.beq, Expr.beqK_eq a]
  | .mul a b, e' => by
    cases e' <;> try rfl
    simp only [Expr.beqK, Expr.beq, Expr.beqK_eq a, Expr.beqK_eq b]
  | .reindex _ a, e' => by
    cases e' <;> try rfl
    simp only [Expr.beqK, Expr.beq, Expr.beqK_eq a, Bool.beq_eq_decide_eq]
  | .concat a b, e' => by
    cases e' <;> try rfl
    simp only [Expr.beqK, Expr.beq, Expr.beqK_eq a, Expr.beqK_eq b]
  | .linear _ a, e' => by
    cases e' <;> try rfl
    simp only [Expr.beqK, Expr.beq, Expr.beqK_eq a, Bool.beq_eq_decide_eq]
  | .prod _ a, e' => by
    cases e' <;> try rfl
    simp only [Expr.beqK, Expr.beq, Expr.beqK_eq a]
  | .mux b t a, e' => by
    cases e' <;> try rfl
    simp only [Expr.beqK, Expr.beq, Expr.beqK_eq b, Expr.beqK_eq t, Expr.beqK_eq a]
  | .apply _ a, e' => by
    cases e' <;> try rfl
    simp only [Expr.beqK, Expr.beq, Expr.beqK_eq a]
  | .ref _, e' => by cases e' <;> rfl
  | .logic _ _ args, e' => by
    cases e' <;> try rfl
    simp only [Expr.beqK, Expr.beq, Expr.beqKList_eq args]

/-- **`Expr.beqKList` is `Expr.beqList`.** -/
theorem _root_.GordieHowe.RealizedProgram.Expr.beqKList_eq :
    ∀ es es' : List Expr, Expr.beqKList es es' = Expr.beqList es es'
  | [], [] => rfl
  | e :: es, e' :: es' => by
    simp only [Expr.beqKList, Expr.beqList, Expr.beqK_eq e, Expr.beqKList_eq es]
  | [], _ :: _ | _ :: _, [] => rfl

end

/-- **`Expr.beqK` decides equality.** -/
theorem _root_.GordieHowe.RealizedProgram.Expr.beqK_iff {e e' : Expr} :
    e.beqK e' = true ↔ e = e' := by
  rw [Expr.beqK_eq]
  exact ⟨Expr.eq_of_beq, fun h => h ▸ Expr.beq_self e⟩

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

/-- **`ConvFacts` with the index maps compared by `List.beq` and the operands by `Expr.beqK`**,
the form its decision evaluates. -/
theorem convFacts_iff_beq (c : SpectralConv) (s : ConvSource) (r : ConvRead)
    (q : ConvProducts) (d z : ℕ) : ir.ConvFacts c s r q d z ↔
      c.source < ir.exprs.length ∧ c.read < ir.exprs.length ∧ c.products < ir.predicates.length ∧
      s.la = c.left ∧ (s.mA == IndexMap.convLeft c.blocks c.left c.right) = true ∧
      (s.mB == IndexMap.convRight c.blocks c.left c.right) = true ∧
      (r.g == IndexMap.blockPrefix c.blocks c.length (c.left + c.right - 1)) = true ∧
      r.B = c.blocks ∧ r.M = c.length ∧ r.psi = c.root ∧ r.z = z ∧
      (q.B = c.blocks ∧ q.B' = c.blocks) ∧ (q.M = c.length ∧ q.M' = c.length) ∧
      (q.psi = c.root ∧ q.psi' = c.root) ∧
      (q.pA == IndexMap.zeroExtend c.blocks c.left c.length) = true ∧
      (q.pB == IndexMap.zeroExtend c.blocks c.right c.length) = true ∧
      q.a.beqK s.a = true ∧ q.b.beqK s.b = true ∧
      (∀ v ∈ [s.zA, s.zB, q.zA, q.zB], ir.zeroConst v = true) ∧
      (∀ v ∈ [s.zA, s.zB, q.zA, q.zB, z], ir.valueField v = ir.domainField d) ∧
      ir.exprLen s.a = c.blocks * c.left ∧ ir.exprLen s.b = c.blocks * c.right ∧
      0 < c.left ∧ 0 < c.right ∧ c.left + c.right - 1 ≤ c.length ∧
      c.length = 2 ^ Nat.log2 c.length ∧ 2 < (ir.field (ir.domainField d)).characteristic ∧
      c.root < (ir.field (ir.domainField d)).characteristic ∧
      c.length < (ir.field (ir.domainField d)).characteristic ∧
      c.root ^ c.length % (ir.field (ir.domainField d)).characteristic =
        (ir.field (ir.domainField d)).characteristic - 1 := by
  rw [convFacts_iff]
  simp only [beq_iff_eq, Expr.beqK_iff]

instance (c : SpectralConv) (s : ConvSource) (r : ConvRead) (q : ConvProducts) (d z : ℕ) :
    Decidable (ir.ConvFacts c s r q d z) :=
  decidable_of_iff _ (ir.convFacts_iff_beq c s r q d z).symm

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

/-- **The committed reading of `c`, if any, is linked to its reading in domain `d`**: with
`c.committed = some (kc, r)`, the shared expression `kc` has the reading's length and the predicate
`r` is the field `equal` `.ref kc = .ref c.read` of `d` whose target is no realization's (the
affine row `C = INTT_M(z)[0, lo)` of a convolution read in a predicate not affine in its
convolutions). Then, wherever `r` holds, `kc` reads as the reading. -/
def CommittedOk (d : ℕ) (c : SpectralConv) : Prop :=
  match c.committed with
  | none => True
  | some (kc, r) =>
    r < ir.predicates.length ∧ ir.exprLen (.ref kc) = ir.exprLen (.ref c.read) ∧
      ∃ t, (ir.predicate r).body = .equal d (.ref kc) (.ref c.read) t ∧ t.isRealized = false

/-- **`CommittedOk`, decided.** -/
def committedOkB (d : ℕ) (c : SpectralConv) : Bool :=
  match c.committed with
  | none => true
  | some (kc, r) =>
    decide (r < ir.predicates.length) && decide (ir.exprLen (.ref kc) = ir.exprLen (.ref c.read)) &&
      match (ir.predicate r).body with
      | .equal d' (.ref k) (.ref k') t =>
        decide (d' = d) && k == kc && k' == c.read && !t.isRealized
      | _ => false

theorem committedOkB_iff (d : ℕ) (c : SpectralConv) :
    ir.committedOkB d c = true ↔ ir.CommittedOk d c := by
  unfold committedOkB CommittedOk
  rcases c.committed with _ | ⟨kc, r⟩
  · simp
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨hr, hl⟩, hb⟩
      refine ⟨hr, hl, ?_⟩
      split at hb
      · rename_i d' k k' t hbody
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at hb
        obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, ht⟩ := hb
        exact ⟨t, hbody, ht⟩
      · cases hb
    · rintro ⟨hr, hl, t, hbody, ht⟩
      refine ⟨⟨hr, hl⟩, ?_⟩
      rw [hbody]
      simp [ht]

instance (d : ℕ) (c : SpectralConv) : Decidable (ir.CommittedOk d c) :=
  decidable_of_iff _ (ir.committedOkB_iff d c)

/-- **The convolution `c` is spectrally realized in domain `d`** (compiler/conv.h, the batch
form): its source and its reading have the forms of `Expr.convSource?` and `Expr.convRead?`, its
products predicate is a field `equal` of `d` between a spectral product (`Expr.convProducts?`) and
the transformed value `z` whose target is no realization's, the facts `ConvFacts` hold
(`ConvProductsOk`), and its committed reading, if any, is linked to its reading (`CommittedOk`).
Then, wherever the products predicate holds, the reading equals the source below their common
length (`RealizedProgram.convRead_eq_source`), and so does the committed reading where its row
holds. -/
def ConvOkAt (d : ℕ) (c : SpectralConv) : Prop :=
  match (ir.expr c.source).convSource?, (ir.expr c.read).convRead?,
      (ir.predicate c.products).body with
  | some s, some r, .equal d' lhs (.leaf z) t =>
    d' = d ∧ t.isRealized = false ∧ ir.ConvProductsOk c s r d z lhs ∧ ir.CommittedOk d c
  | _, _, _ => False

/-- **`ConvOkAt`, decided.** -/
def convOkAtB (d : ℕ) (c : SpectralConv) : Bool :=
  match (ir.expr c.source).convSource?, (ir.expr c.read).convRead?,
      (ir.predicate c.products).body with
  | some s, some r, .equal d' lhs (.leaf z) t =>
    decide (d' = d) && !t.isRealized && ir.convProductsOkB c s r d z lhs && ir.committedOkB d c
  | _, _, _ => false

theorem convOkAtB_iff (d : ℕ) (c : SpectralConv) : ir.convOkAtB d c = true ↔ ir.ConvOkAt d c := by
  unfold convOkAtB ConvOkAt
  cases (ir.expr c.source).convSource? <;> cases (ir.expr c.read).convRead? <;>
    cases (ir.predicate c.products).body <;> try simp
  all_goals
    rename_i d' lhs rhs t
    cases rhs <;> simp [convProductsOkB_iff, committedOkB_iff, and_assoc]

instance (d : ℕ) (c : SpectralConv) : Decidable (ir.ConvOkAt d c) :=
  decidable_of_iff _ (ir.convOkAtB_iff d c)

/-- **The parts of a direct convolution's products** (the left side of `SpectralConv.products`
of a `direct` convolution): `C`'s side `cv`, the constant `s` (`p − 1`) and the linear map's rows
over the products of the operands' views `ia`, `ib` of `a` and `b`. -/
structure DirectProducts where
  /-- The committed `C`'s side. -/
  cv : Expr
  /-- The constant multiplying the sums. -/
  s : ℕ
  /-- The sums' rows. -/
  rows : List (List (ℕ × Coef))
  /-- The left operand's view. -/
  ia : IndexMap
  /-- The left operand. -/
  a : Expr
  /-- The right operand's view. -/
  ib : IndexMap
  /-- The right operand. -/
  b : Expr

/-- **The parts of an expression of the form** `C − Σ_rows (ia a) · (ib b)`,
`.add cv (.scale (.const s) (.linear rows (.mul (.reindex ia a) (.reindex ib b))))`, none for any
other. -/
def _root_.GordieHowe.RealizedProgram.Expr.directProducts? : Expr → Option DirectProducts
  | .add cv (.scale (.const s) (.linear rows (.mul (.reindex ia a) (.reindex ib b)))) =>
    some ⟨cv, s, rows, ia, a, ib, b⟩
  | _ => none

/-- **The value an expression reads at a coordinate through its views**: `.reindex m e` at `i`
is `e` at entry `i` of `m`, any other expression at `i` itself. -/
def _root_.GordieHowe.RealizedProgram.Expr.site : Expr → ℕ → Expr × ℕ
  | .reindex m e, i => Expr.site e (m.entry i)
  | e, i => (e, i)

/-- **`e` reads `x` at its first `n` coordinates**: `e` is `x`, or a view of `x` whose first `n`
entries are `0, …, n − 1`. -/
def _root_.GordieHowe.RealizedProgram.Expr.IdView (e x : Expr) (n : ℕ) : Prop :=
  e = x ∨ ∃ m, e = .reindex m x ∧ ∀ j < n, m.entry j = j

/-- **`Expr.IdView`, decided** (expressions compared by `Expr.beqK`). -/
def _root_.GordieHowe.RealizedProgram.Expr.idViewB (e x : Expr) (n : ℕ) : Bool :=
  e.beqK x ||
    match e with
    | .reindex m x' => x'.beqK x && (List.range n).all fun j => m.entry j == j
    | _ => false

theorem _root_.GordieHowe.RealizedProgram.Expr.idViewB_iff (e x : Expr) (n : ℕ) :
    e.idViewB x n = true ↔ e.IdView x n := by
  unfold Expr.idViewB Expr.IdView
  rw [Bool.or_eq_true, Expr.beqK_iff]
  apply or_congr Iff.rfl
  constructor
  · intro h
    split at h
    · rename_i m x'
      simp only [Bool.and_eq_true, Expr.beqK_iff, List.all_eq_true, List.mem_range,
        beq_iff_eq] at h
      exact ⟨m, by rw [h.1], h.2⟩
    · cases h
  · rintro ⟨m, rfl, hm⟩
    simp only [Bool.and_eq_true, Expr.beqK_iff, List.all_eq_true, List.mem_range, beq_iff_eq]
    exact ⟨trivial, hm⟩

/-- **The terms of coordinate `k` of block `blk` of a direct convolution** of operand rows of
lengths `la` and `lb` (compiler/conv.h, `direct`): for each `u < la` with `k − u` below `lb`, the
operands' coordinates `blk la + u` and `blk lb + (k − u)` with the coefficient `1`; in a square
block (`sq`: the operands' rows are one row of one value) only those with `u ≤ k − u`, the
coefficient `2` for `u < k − u`. -/
def directTerms (la lb blk k : ℕ) (sq : Bool) : List (ℕ × ℕ × Coef) :=
  (List.range la).filterMap fun u =>
    if u ≤ k ∧ k - u < lb ∧ (sq = false ∨ u ≤ k - u) then
      some (blk * la + u, blk * lb + (k - u), .const (if sq = true ∧ u ≠ k - u then 2 else 1))
    else none

/-- **The facts of a directly realized convolution** `c` in domain `d` (field `F` of
characteristic `p`), its source's parts `s`, its products' `q`, `C` the committed value it reads as
and `z` the products' right side: the identifiers exist; the source sums width `la` over the
operands' views `IndexMap.convLeft B la lb` and `IndexMap.convRight B la lb`; the zero constants lie
in `F` and hold `0`; the operands have `B la` and `B lb` coordinates; `C` and the products' `C` side
have `B (la + lb − 1)`, the side reading `C` unchanged; the products' operands read the source's unchanged;
the constant is `p − 1` (`−1`) with `2 < p`; row `blk (la + lb − 1) + k` of the sums has the terms
`directTerms` (their operand coordinates through `ia` and `ib`), and a square block's operands read
one value's coordinates. Where the products predicate holds, `C` is then the convolution
(`RealizedProgram.directRead_eq_source`). -/
def DirectFacts (c : SpectralConv) (s : ConvSource) (q : DirectProducts) (d C z : ℕ) : Prop :=
  c.source < ir.exprs.length ∧ c.read < ir.exprs.length ∧ c.products < ir.predicates.length ∧
    s.la = c.left ∧ s.mA = IndexMap.convLeft c.blocks c.left c.right ∧
    s.mB = IndexMap.convRight c.blocks c.left c.right ∧
    (∀ v ∈ [s.zA, s.zB, z], ir.zeroConst v = true) ∧
    (∀ v ∈ [s.zA, s.zB, z], ir.valueField v = ir.domainField d) ∧
    ir.exprLen s.a = c.blocks * c.left ∧ ir.exprLen s.b = c.blocks * c.right ∧
    0 < c.left ∧ 0 < c.right ∧
    (ir.value C).size = c.blocks * (c.left + c.right - 1) ∧
    q.cv.IdView (.leaf C) (c.blocks * (c.left + c.right - 1)) ∧
    ir.exprLen q.cv = c.blocks * (c.left + c.right - 1) ∧
    q.a.IdView s.a (c.blocks * c.left) ∧ q.b.IdView s.b (c.blocks * c.right) ∧
    q.s + 1 = (ir.field (ir.domainField d)).characteristic ∧
    2 < (ir.field (ir.domainField d)).characteristic ∧
    (∀ i < c.blocks * (c.left + c.right - 1),
      (q.rows.getD i []).map (fun t => (q.ia.entry t.1, q.ib.entry t.1, t.2)) =
        directTerms c.left c.right (i / (c.left + c.right - 1)) (i % (c.left + c.right - 1))
          (c.squares.getD (i / (c.left + c.right - 1)) false)) ∧
    ∀ blk < c.blocks, c.squares.getD blk false = true →
      c.left = c.right ∧ ∀ u < c.left, s.a.site (blk * c.left + u) = s.b.site (blk * c.right + u)

/-- **`DirectFacts`, decided** (expressions compared by `Expr.beqK`, index maps by `List.beq`). -/
def directFactsB (c : SpectralConv) (s : ConvSource) (q : DirectProducts) (d C z : ℕ) : Bool :=
  decide (c.source < ir.exprs.length) && decide (c.read < ir.exprs.length) &&
    decide (c.products < ir.predicates.length) && s.la == c.left &&
    s.mA == IndexMap.convLeft c.blocks c.left c.right &&
    s.mB == IndexMap.convRight c.blocks c.left c.right &&
    [s.zA, s.zB, z].all (ir.zeroConst ·) &&
    [s.zA, s.zB, z].all (fun v => ir.valueField v == ir.domainField d) &&
    ir.exprLen s.a == c.blocks * c.left && ir.exprLen s.b == c.blocks * c.right &&
    decide (0 < c.left) && decide (0 < c.right) &&
    (ir.value C).size == c.blocks * (c.left + c.right - 1) &&
    q.cv.idViewB (.leaf C) (c.blocks * (c.left + c.right - 1)) &&
    ir.exprLen q.cv == c.blocks * (c.left + c.right - 1) &&
    q.a.idViewB s.a (c.blocks * c.left) && q.b.idViewB s.b (c.blocks * c.right) &&
    q.s + 1 == (ir.field (ir.domainField d)).characteristic &&
    decide (2 < (ir.field (ir.domainField d)).characteristic) &&
    (List.range (c.blocks * (c.left + c.right - 1))).all (fun i =>
      (q.rows.getD i []).map (fun t => (q.ia.entry t.1, q.ib.entry t.1, t.2)) ==
        directTerms c.left c.right (i / (c.left + c.right - 1)) (i % (c.left + c.right - 1))
          (c.squares.getD (i / (c.left + c.right - 1)) false)) &&
    (List.range c.blocks).all fun blk =>
      !c.squares.getD blk false ||
        (c.left == c.right && (List.range c.left).all fun u =>
          (s.a.site (blk * c.left + u)).1.beqK (s.b.site (blk * c.right + u)).1 &&
            (s.a.site (blk * c.left + u)).2 == (s.b.site (blk * c.right + u)).2)

theorem directFactsB_iff (c : SpectralConv) (s : ConvSource) (q : DirectProducts) (d C z : ℕ) :
    ir.directFactsB c s q d C z = true ↔ ir.DirectFacts c s q d C z := by
  unfold directFactsB DirectFacts
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range,
    Expr.idViewB_iff, Bool.or_eq_true, Bool.not_eq_true', Expr.beqK_iff, Prod.ext_iff,
    and_assoc]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21⟩
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, fun blk hb hsq => ?_⟩
    rcases h21 blk hb with h | h
    · rw [h] at hsq
      cases hsq
    · exact ⟨h.1, fun u hu => (h.2 u hu)⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21⟩
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, fun blk hb => ?_⟩
    cases hsq : c.squares.getD blk false
    · exact .inl rfl
    · exact .inr ⟨(h21 blk hb hsq).1, fun u hu => (h21 blk hb hsq).2 u hu⟩

instance (c : SpectralConv) (s : ConvSource) (q : DirectProducts) (d C z : ℕ) :
    Decidable (ir.DirectFacts c s q d C z) :=
  decidable_of_iff _ (ir.directFactsB_iff c s q d C z)

/-- **The convolution `c` is directly realized in domain `d`** (compiler/conv.h, the direct
form): its source has the form of `Expr.convSource?`, its reading is the committed `C`'s leaf, it
has no committed reading besides, and its products predicate is a field `equal` of `d` whose
target is no realization's, between `C − Σ_rows (ia a) · (ib b)` (`Expr.directProducts?`) and a
zero constant `z`, with the facts `DirectFacts`. Then, wherever the products predicate holds, the
reading equals the source below their common length (`RealizedProgram.directRead_eq_source`). -/
def DirectOkAt (d : ℕ) (c : SpectralConv) : Prop :=
  match (ir.expr c.source).convSource?, ir.expr c.read, (ir.predicate c.products).body with
  | some s, .leaf C, .equal d' lhs (.leaf z) t =>
    match lhs.directProducts? with
    | some q => d' = d ∧ t.isRealized = false ∧ c.committed = none ∧ ir.DirectFacts c s q d C z
    | none => False
  | _, _, _ => False

/-- **`DirectOkAt`, decided.** -/
def directOkAtB (d : ℕ) (c : SpectralConv) : Bool :=
  match (ir.expr c.source).convSource?, ir.expr c.read, (ir.predicate c.products).body with
  | some s, .leaf C, .equal d' lhs (.leaf z) t =>
    match lhs.directProducts? with
    | some q =>
      decide (d' = d) && !t.isRealized && c.committed.isNone && ir.directFactsB c s q d C z
    | none => false
  | _, _, _ => false

theorem directOkAtB_iff (d : ℕ) (c : SpectralConv) :
    ir.directOkAtB d c = true ↔ ir.DirectOkAt d c := by
  unfold directOkAtB DirectOkAt
  split
  · split
    · simp [directFactsB_iff, Option.isNone_iff_eq_none, and_assoc]
    · simp
  · simp

instance (d : ℕ) (c : SpectralConv) : Decidable (ir.DirectOkAt d c) :=
  decidable_of_iff _ (ir.directOkAtB_iff d c)

/-- **The convolution `c` is realized in domain `d`**: directly (`DirectOkAt`) for a `direct`
convolution, spectrally (`ConvOkAt`) otherwise. -/
def ConvRealizedAt (d : ℕ) (c : SpectralConv) : Prop :=
  if c.direct then ir.DirectOkAt d c else ir.ConvOkAt d c

/-- **`ConvRealizedAt`, decided.** -/
def convRealizedAtB (d : ℕ) (c : SpectralConv) : Bool :=
  if c.direct then ir.directOkAtB d c else ir.convOkAtB d c

theorem convRealizedAtB_iff (d : ℕ) (c : SpectralConv) :
    ir.convRealizedAtB d c = true ↔ ir.ConvRealizedAt d c := by
  unfold convRealizedAtB ConvRealizedAt
  split
  · exact ir.directOkAtB_iff d c
  · exact ir.convOkAtB_iff d c

instance (d : ℕ) (c : SpectralConv) : Decidable (ir.ConvRealizedAt d c) :=
  decidable_of_iff _ (ir.convRealizedAtB_iff d c)

/-- **`Expr.matchB` consuming the given conversions in mismatch order**: at a pair of different
shared expressions `k`, `k'` the next conversion `j` of `js` must pass `ok j k k'`; the rest of `js`
after the match, none when a pair fails. The order is the walk's: the sides' subterms `a` before
`b`, pre-order. Index maps are compared by `List.beq` and the other pairs by `Expr.beqK`, so the
kernel evaluates the walk in depth bounded by the expressions' depth. -/
def _root_.GordieHowe.RealizedProgram.Expr.matchL (ok : ℕ → ℕ → ℕ → Bool) :
    Expr → Expr → List ℕ → Option (List ℕ)
  | .ref k, .ref k', js =>
    if k == k' then some js
    else
      match js with
      | j :: js' => if ok j k k' then some js' else none
      | [] => none
  | .add a b, .add a' b', js => (Expr.matchL ok a a' js).bind (Expr.matchL ok b b')
  | .sub a b, .sub a' b', js => (Expr.matchL ok a a' js).bind (Expr.matchL ok b b')
  | .mul a b, .mul a' b', js => (Expr.matchL ok a a' js).bind (Expr.matchL ok b b')
  | .concat a b, .concat a' b', js => (Expr.matchL ok a a' js).bind (Expr.matchL ok b b')
  | .scale c a, .scale c' a', js => if c = c' then Expr.matchL ok a a' js else none
  | .reindex m a, .reindex m' a', js => if m == m' then Expr.matchL ok a a' js else none
  | .apply op a, .apply op' a', js => if op = op' then Expr.matchL ok a a' js else none
  | e, e', js => if e.beqK e' then some js else none

/-- **Conversion `j` is a realized convolution of domain `d` with source `k` and reading or
committed reading `k'`** (`ConvRealizedAt`), read at the pointer `j`. -/
def convAtB (d j k k' : ℕ) : Bool :=
  match ir.convs[j]? with
  | some c =>
    c.source == k && (c.read == k' || c.committed.map Prod.fst == some k') &&
      ir.convRealizedAtB d c
  | none => false

/-- **`RealizedAdmits`, at the given conversions** (`Route.realized q js`): `q` is a field `equal`
of `d` whose target is no realization's, and its sides match `e` and `e'` consuming exactly the
conversions `js`, each checked at its pointer (`convAtB`). -/
def realizedAdmitsAtB (d : ℕ) (e e' : Expr) (q : ℕ) (js : List ℕ) : Bool :=
  decide (q < ir.predicates.length) &&
    match (ir.predicate q).body with
    | .equal d' E E' t => decide (d' = d) && !t.isRealized &&
        match Expr.matchL (ir.convAtB d) e E js with
        | some js' => Expr.matchL (ir.convAtB d) e' E' js' == some []
        | none => false
    | _ => false

/-- **The target of a predicate body**: a field `equal`'s, or a `mod_q`'s field equation's (`q = 0`,
or `q` the characteristic of a prime-field `mod_q`). -/
def PredBody.target : PredBody → Option Target
  | .equal _ _ _ t => some t
  | .mem _ _ _ _ => none
  | .mod _ _ _ _ real => real.target
  | .cross _ _ _ _ _ _ => none

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

instance (c : Circuit) : Decidable (CircuitLaidOut c) :=
  decidable_of_iff _ (circuitLaidOut_iff c).symm

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

section

variable (ir : RealizedProgram)

/-- **The degrees of the shared expressions**, the values having degrees `nd`, with `n` levels. -/
def refDeg (nd : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, k => (ir.expr k).deg nd (refDeg nd n)

/-- **An expression's degree** through its shared expressions, the values having degrees `nd`. -/
def degOf (nd : ℕ → ℕ) (e : Expr) : ℕ := e.deg nd (ir.refDeg nd ir.exprs.length)

/-- **The degree of an expression in the committed cells** (committed values, bit views, pad
copies and late values, a late value being its message minus its pad; public values and
coefficients have degree `0`). -/
def cellDeg (e : Expr) : ℕ :=
  ir.degOf (fun v => if ir.isCommitted v || ir.isLateNode v then 1 else 0) e

end

end GordieHowe.RealizedProgram
