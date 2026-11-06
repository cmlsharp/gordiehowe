-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Semantics
public import GordieHowe.Language.RealizedProgram.RunVec
public import GordieHowe.Language.RealizedProgram.Encoding
public import GordieHoweNative.Language.RealizedProgram.Valid

@[expose] public section

/-!
# GordieHowe: the validity conditions that read the plan's program

The conditions of `Plan.Valid` that read the value table and the predicates of the realized program
(`GordieHowe.RealizedProgram`), as decidable predicates:

* `GordieHowe.RealizedProgram.WellFormed`: identifiers in range, every expression of a predicate in
  its domain's field (the MAC's powers read by `macConv` excepted: they are read in their own field)
  and of consistent lengths, coefficients and named operators' operands public (a transform-form
  convolution's spectrum excepted, `NamedOp.pubOperands`), values acyclic (each reads values of
  smaller identifier only), shared expressions acyclic (each reads entries of smaller index only),
  challenges of positive size in phases among the program's;
* `GordieHowe.RealizedProgram.MessagesMatch`: the messages are the late values, in `MsgBefore`
  order, with their phases, sizes and pad spaces;
* `GordieHowe.RealizedProgram.ReadsSound`: every predicate's exported reads contain the reads
  computed from its expressions (`GordieHowe.RealizedProgram.predReads`, through the shared
  expressions), so its meaning depends only on them
  (`GordieHowe/Language/RealizedProgram/Lemmas.lean`);
* `GordieHowe.RealizedProgram.DegreesSound`: every exported degree bounds the degree computed from
  the expressions, the largest over their coordinates of the per-coordinate degree (`Expr.degAt`,
  `GordieHowe.RealizedProgram.exprDeg`; the exported degrees are the C++'s `deg_c(p)`, computed
  coordinate by coordinate);
* `GordieHowe.RealizedProgram.ChallengeOrder`: (a) a late value of phase `k` reads only challenges
  of phases at most `k` (and pads); (b) for each source predicate `p` and challenge `c` with
  `deg_c(p) > 0`, every late value `p` reads that is not computed from `c` has phase below `c`'s;
  (c) the realizations' phase conditions (`in`: the late needles, the group's late histogram and the
  digits before `α`; cross-field `equal`: the key before the tag and the accumulators);
* `GordieHowe.RealizedProgram.PadOrderValid`: every late value reads only pads of pad-realized late
  values of strictly earlier messages in `MsgBefore` order (never its own);
* `GordieHowe.RealizedProgram.TypeSources`: every committed or late `Bit` and `Sub(E)` value has a
  type source, a packing-tree node of that subfield or its Boolean-check predicate `v · v = v`;
* `GordieHowe.RealizedProgram.TargetsAdmit`: every target admits its predicate, the GKR circuits
  list exactly the predicates placed in them, and their input layouts are contiguous with the public
  blocks first (`GordieHowe.RealizedProgram.CircuitLaidOut`);
* `GordieHowe.RealizedProgram.PadRealized`: every late value is pad-realized (`commitment` is
  rejected).

No condition bounds the challenges' degrees: the exported degrees are data that the frontend's
lowerings read.

Of these, the proof system reads `WellFormed`, `ChallengeOrder` and `PadOrderValid`
(`RealizedProgram.Valid ir`, `GordieHowe/Language/RealizedProgram/WithPlan.lean`). No theorem reads
the others, and the program checks (`GordieHowe.ProgramData.programOkB`) no longer certify them.

**Shared expressions.** A property of an expression through its shared expressions is computed by
`GordieHowe.RealizedProgram.closure` (lists, such as the values read) or by a table of the entries'
values with one level per entry (`GordieHowe.RealizedProgram.refDeg`, degrees in the cells;
`GordieHowe.RealizedProgram.refDegAt`, per-coordinate degrees in a challenge). Both recompute an
entry at each reference, so their cost is that of the expression written as a tree. They are the
definitions; the decision procedure is the checker of
`GordieHowe/Language/RealizedProgram/Check.lean`, which computes each entry once: `WellFormed` takes
its `Decidable` instance from `wellFormedB` (`wellFormedB_iff`), and `ReadsSound`, `DegreesSound`
and `TargetsAdmit` are decided through `readsB`, `degreesB` and `targetsB` (`readsB_iff`,
`degreesB_iff`, `targetsB_iff`). The conditions over the values (`MessagesMatch`, `ChallengeOrder`,
`PadOrderValid`, `PadRealized`, `TypeSources`) have `Decidable` instances here that look each value
up in the list, quadratic in the number of values; the proof modules decide them through the
one-pass checkers of `GordieHowe/Language/RealizedProgram/CheckValues.lean`.

The definitions are in `GordieHoweNative/Language/RealizedProgram/Valid.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## Syntax: nodes, references, reads and degrees -/

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

@[simp] theorem InSet.exprs_range (n : ℕ) : (InSet.range n).exprs = [] := rfl
@[simp] theorem InSet.exprs_table (t : ℕ) : (InSet.table t).exprs = [] := rfl
@[simp] theorem InSet.exprs_expr (e' : Expr) : (InSet.expr e').exprs = [e'] := rfl

/-- **A predicate body is the Boolean check of value `v`**: `v · v = v`, either way round. -/
def PredBody.isBoolCheck (v : ℕ) : PredBody → Bool
  | .equal _ (.mul (.leaf u) (.leaf u')) (.leaf u'') _ => u == v && u' == v && u'' == v
  | .equal _ (.leaf u'') (.mul (.leaf u) (.leaf u')) _ => u == v && u' == v && u'' == v
  | _ => false

section

variable (ir : RealizedProgram)

/-! ## Through the shared expressions -/

/-- **Whether the shared expressions vanish at zero**, with `n` levels. -/
def refZero : ℕ → ℕ → Bool
  | 0, _ => false
  | n + 1, k => (ir.expr k).zeroAtZero (refZero n)

/-- **An expression vanishes where its values vanish**, through its shared expressions. -/
def zeroOf (e : Expr) : Bool := e.zeroAtZero (ir.refZero ir.exprs.length)

/-! ## Reads and degrees -/

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
  (b.exprs.map fun de =>
    maxBelow (ir.exprLen de.2) (ir.degAtOf (ir.nodeDegAt c ir.fuel) de.2)).foldr max 0

/-- Whether value `v` is a public expression. -/
def isPubExpr (v : ℕ) : Bool :=
  match (ir.value v).kind with
  | .pub (.expr _) => true
  | _ => false

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

/-- **The shared expressions are well formed**: entry `k` reads only entries of smaller index, and
its lengths are consistent. -/
def ExprsOk : Prop :=
  ∀ k < ir.exprs.length, (∀ k' ∈ (ir.expr k).refs, k' < k) ∧ ir.exprShapeOk (ir.expr k) = true

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
`deg_c(p) > 0`, every late value `p` reads that `c` tests is fixed before `c`
(`PredReadOrdered`). -/
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
    ∀ v ∈ ir.exprNodes e ++ ir.exprNodes e',
      IsCircuitInputOf (ir.circuit c).inputs v (ir.value v).kind

/-! ### Equality checks the kernel evaluates in bounded depth

The derived decidable equality of lists nests one kernel reduction per entry, so `decide (m = m')`
on index maps of some thousands of entries exceeds the kernel's recursion limit (RSA2048's
convolution views hold 11577 entries). `List.beq` returns its recursive call in tail position,
which the kernel evaluates in constant depth. The checks below compare index maps and linear maps'
rows by `==` (`List.beq`) and expressions by `Expr.beqK`, which is `Expr.beq` with those
comparisons (`Expr.beqK_eq`). -/

instance (c : SpectralConv) (s : ConvSource) (r : ConvRead) (d z : ℕ) (lhs : Expr) :
    Decidable (ir.ConvProductsOk c s r d z lhs) :=
  decidable_of_iff _ (ir.convProductsOkB_iff c s r d z lhs)

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

/-! ### The realized route at the given conversions -/

/-- **A match at the given conversions is a match** (`Expr.matchB`) at every relation the
conversions' test implies. -/
theorem _root_.GordieHowe.RealizedProgram.Expr.matchB_of_matchL {P : ℕ → ℕ → Bool}
    {ok : ℕ → ℕ → ℕ → Bool} (hok : ∀ j k k', ok j k k' = true → P k k' = true) :
    ∀ (e E : Expr) (js : List ℕ) {js' : List ℕ}, Expr.matchL ok e E js = some js' →
      Expr.matchB P e E = true
  | e, E, js, js', h => by
    cases e <;> cases E <;> simp only [Expr.matchL, Expr.matchB] at h ⊢
    all_goals first
      | (split at h
         · assumption
         · cases h)
      | (rw [Option.bind_eq_some_iff] at h
         obtain ⟨j₁, h1, h2⟩ := h
         rw [Bool.and_eq_true]
         exact ⟨Expr.matchB_of_matchL hok _ _ _ h1, Expr.matchB_of_matchL hok _ _ _ h2⟩)
      | (split at h
         · rename_i hc
           rw [Expr.beqK_eq] at hc
           exact hc
         · cases h)
      | (split at h
         · rename_i hc
           rw [Bool.and_eq_true, decide_eq_true_eq]
           exact ⟨by first | exact hc | exact beq_iff_eq.1 hc,
             Expr.matchB_of_matchL hok _ _ _ h⟩
         · cases h)
      | (rw [Bool.or_eq_true, beq_iff_eq]
         rename_i k k'
         by_cases hk : k = k'
         · exact .inl hk
         · simp only [beq_iff_eq, hk, ↓reduceIte] at h
           split at h
           · split at h
             · exact .inr (hok _ _ _ (by assumption))
             · cases h
           · cases h)
  termination_by e => e

/-- **The conversion at the pointer pairs its source and reading** (`ConvPair`). -/
theorem convPair_of_convAtB {d j k k' : ℕ} (h : ir.convAtB d j k k' = true) :
    decide (ir.ConvPair d k k') = true := by
  unfold convAtB at h
  split at h
  · rename_i c hc
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hs, hr⟩, hok⟩ := h
    exact decide_eq_true ⟨c, List.mem_of_getElem? hc, hs, hr, (ir.convOkAtB_iff d c).1 hok⟩
  · cases h

/-- **The realized route at its conversions admits the field equation** (`RealizedAdmits`). -/
theorem realizedAdmits_of_atB {d q : ℕ} {e e' : Expr} {js : List ℕ}
    (h : ir.realizedAdmitsAtB d e e' q js = true) : ir.RealizedAdmits d e e' q := by
  unfold realizedAdmitsAtB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hq, h⟩ := h
  refine ⟨hq, ?_⟩
  split at h
  · rename_i d' E E' t hb
    simp only [hb]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨hd, ht⟩, h⟩ := h
    split at h
    · rename_i js' h1
      have h2 : Expr.matchL (ir.convAtB d) e' E' js' = some [] := by simpa using h
      exact ⟨hd, ht, Expr.matchB_of_matchL (fun _ _ _ h => ir.convPair_of_convAtB h) _ _ _ h1,
        Expr.matchB_of_matchL (fun _ _ _ h => ir.convPair_of_convAtB h) _ _ _ h2⟩
    · cases h
  · cases h

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

end

end GordieHowe.RealizedProgram
