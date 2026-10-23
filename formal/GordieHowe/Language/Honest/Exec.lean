-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Honest.Packed

@[expose] public section

/-!
# GordieHowe: the honest strategy from an execution of the source program

The completeness hypothesis of the paper's `thm:backend` (1) is an execution of the source program
`P₀` (`def:o-semantics`) that is accepting except with probability `errc` (`def:o-guarantees`).
`lem:core-red` (2) extends it by the values the realizations add and obtains the honest prover of
the realized program. This file states the execution as a plan-level input and builds the honest
strategy from it once for all programs.

* **The execution** (`GordieHowe.RealizedProgram.SourceExecutionCore`; with per-phase errors, `GordieHowe.RealizedProgram.SourceExecution`): on
  honest inputs `Inp` related to statements by `relH`, the statement of an input, the source
  program's phase-`0` values and its late values as functions of the challenges, completeness
  events charged to each phase, and one obligation in the source program's vocabulary: off the events, the source program accepts
  (`GordieHowe.RealizedProgram.SourceAcceptingAt`) in the environment of the execution (`GordieHowe.RealizedProgram.execEnv`). The
  statement facts (`checks`, `bounded`) are the paper's `Stmt_P₀`.
* **The accepting execution** (`GordieHowe.RealizedProgram.SourceAcceptingAt`): every source predicate holds and every
  `kpriv` source value lies in its type (`Kind.isKpriv`), the paper's accepting assignment.
* **The environment of an execution** (`GordieHowe.RealizedProgram.execEnv`): the statement, the phase-`0` values at
  the committed coordinates and at the coordinates of the values bound to their digits, the late
  values at the late values' coordinates, the challenges, and no pads; a value bound to its digits
  reads its own value, as in `P₀`.
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP Range
open scoped NNReal

/-- **A value of a `kpriv` variable** (paper, `def:o-semantics`): committed, bound to its digits
(a committed source value), or late. -/
def Kind.isKpriv : Kind → Bool
  | .priv => true
  | .late => true
  | .bound _ => true
  | _ => false

/-- Whether a kind is a message. -/
def Kind.isMessage : Kind → Bool
  | .message _ => true
  | _ => false

section

variable (ir : RealizedProgram) (I : Interp)

/-! ## The execution of the source program -/

/-- **A coordinate the execution of the source program assigns in the committed assignment**: a
committed cell coordinate (a value of a domain of the program with a cell there), or a coordinate,
below the value's size, of a value bound to its digits. -/
def ExecCoord (u i : ℕ) : Prop :=
  ((ir.value u).domain < ir.domains.length ∧ CellKey.val u i ∈ ir.cellKeys (ir.value u).domain) ∨
    ((ir.value u).kind.isBound = true ∧ i < (ir.value u).size)

instance (u i : ℕ) : Decidable (ir.ExecCoord u i) := by unfold ExecCoord; infer_instance

/-- **The environment of an execution of the source program** at the statement `x`, the phase-`0`
values `s`, the late values `l` and the challenges `c`: `s` at the coordinates the execution assigns
(`ExecCoord`), `l` at the late values' coordinates, `0` elsewhere and at every pad. A value bound to
its digits reads its own value (the committed assignment at it is `s`), as in the source program;
the realized program reads it through its digits. -/
def execEnv (x s l : ir.Valuation I) (c : ∀ k, (ir.layout I).Ch k) : ir.Env I where
  stmt := x
  asg := ⟨fun u i => if ir.ExecCoord u i then s u i else 0, 0⟩
  chal := ir.chalRead I c
  late v i := if v < ir.values.length ∧ ir.IsLate v ∧ i < (ir.value v).size then l v i else 0

/-- **Every source cross-field `equal` reads bits** in the environment `e`: both operands, at every
coordinate (the paper's `pshare` relates operands of type `Bit`; the Lean cross-field `equal`
leaves the H operand's Booleanity to its caller, `RealizedProgram.HoldsWith`). -/
def CrossBitsAt (e : ir.Env I) : Prop :=
  ∀ p ∈ ir.predicates, ir.inSource p = true → ∀ dx x dy y k real,
    p.body = .cross dx x dy y k real →
      (∀ i < ir.exprLen x, ir.evalWith (ir.reader e) dx x i = 0 ∨ ir.evalWith (ir.reader e) dx x i = 1) ∧
        ∀ i < ir.exprLen y, ir.evalWith (ir.reader e) dy y i = 0 ∨ ir.evalWith (ir.reader e) dy y i = 1

/-- **Every source `mod_q` in the field form holds as its field equation** in the environment `e`:
both sides are equal in the field of the domain, at every coordinate. Over the prime field the
congruence modulo `p` gives it; over an extension (Falcon native's `F_q^9`) it is stronger, and the
field form's realization (`RealizedProgram.FieldFormOk`, a field `equal` row) is complete exactly on
executions satisfying it. -/
def FieldEqsAt (e : ir.Env I) : Prop :=
  ∀ p ∈ ir.predicates, ir.inSource p = true → ∀ d q a b real,
    p.body = .mod d q a b real → real.form = .field →
      ∀ i < ir.exprLen a, ir.evalWith (ir.reader e) d a i = ir.evalWith (ir.reader e) d b i

/-- **The source program accepts in the environment `e`** (paper, `def:o-semantics`, an accepting
assignment): every source predicate holds and every node-typed source value lies in its type
(`SourceSatAt`), and every `kpriv` source value (`Kind.isKpriv`) lies in its type, whatever states
its type (a node, a check or nothing: an unchecked bit, `bit_from_unchecked`, included), and every
source cross-field `equal` reads bits (`CrossBitsAt`, the paper's `pshare` on `Bit` operands). This
is the completeness proof's obligation; `SourceSatAt` is what the source protocol's verifier checks.
-/
structure SourceAcceptingAt (e : ir.Env I) : Prop where
  /-- The source program holds. -/
  sat : ir.SourceSatAt e
  /-- Every `kpriv` source value lies in its type. -/
  types : ∀ v < ir.values.length, ir.IsSourceValue v → (ir.value v).kind.isKpriv = true →
    ∀ i < (ir.value v).size, (I (ir.valueField v)).InType (ir.value v).type (ir.reader e v i)
  /-- Every source cross-field `equal` reads bits. -/
  crossBits : ir.CrossBitsAt I e

/-- **The source program's late values read only their exported challenges**: at challenge vectors
agreeing on the challenges a source late value reads, it is the same. -/
def SourceRespectsReads (l : (∀ k, (ir.layout I).Ch k) → ir.Valuation I) : Prop :=
  ∀ v, ir.IsSourceValue v → ir.IsLate v → ∀ c c' : (∀ k, (ir.layout I).Ch k),
    (∀ j, Read.chal j ∈ (ir.value v).reads → ir.chalRead I c j = ir.chalRead I c' j) →
      l c v = l c' v

/-- **An execution of the source program** on honest inputs `Inp` related to statements by `relH`
(`Exec_{P₀}(stm, wit)`, `def:o-semantics`): the statement of an input, the source program's
phase-`0` values and its late values as functions of the challenges (reading only their exported
challenges), completeness events charged to each phase, which may read the challenges of every
phase; the statement facts of `Stmt_P₀` (`checks`, `bounded`); and, off the events, the source
program accepts in the environment of the execution (`accepting`). The values are read only at the
source values. The completeness hypothesis of the paper's `thm:backend` (1) is such an execution
whose events have together probability at most `errc` (`HonestCore.Complete` of
`HonestCore.ofCompletion`, or `HonestCore.CoinComplete` for an honest prover with coins). -/
structure SourceExecutionCore {Inp : Type} (relH : Set (ir.Valuation I × Inp)) where
  /-- The statement of an honest input (the honest prover runs on the statement and the input). -/
  stmtOf : Inp → ir.Valuation I
  /-- The statement of a related input is its statement. -/
  stmt : ∀ x y, (x, y) ∈ relH → x = stmtOf y
  /-- The source program's phase-`0` values. -/
  val : Inp → ir.Valuation I
  /-- The source program's late values, from the challenges. -/
  late : Inp → (∀ k, (ir.layout I).Ch k) → ir.Valuation I
  /-- The late values read only their exported challenges. -/
  respects : ∀ y, ir.SourceRespectsReads I (late y)
  /-- The completeness event charged to phase `k + 1`, at the challenges of every phase. -/
  bad : (k : Fin ir.phases) → ir.Valuation I → Inp → (∀ k, (ir.layout I).Ch k) → Prop
  /-- The honest statements pass the program's member checks. -/
  checks : ∀ x y, (x, y) ∈ relH → ir.StatementOk I x
  /-- The honest statements lie within the declared bounds (automatic for a program declaring
  none, `stmtBounded_of_nil`). -/
  bounded : ∀ x y, (x, y) ∈ relH → ir.StmtBounded I x := by
    exact fun x _ _ => Program.stmtBounded_of_nil (by decide +kernel) x
  /-- Off the events, the source program accepts in the environment of the execution. -/
  accepting : ∀ x y, (x, y) ∈ relH → ∀ c : ∀ k, (ir.layout I).Ch k, (∀ k, ¬ bad k x y c) →
    ir.SourceAcceptingAt I (ir.execEnv I x (val y) (late y c) c)
  /-- Off the events, the source `mod_q`s in the field form hold as their field equations in the
  environment of the execution (vacuous for a program without one, `fieldEqsAt_of_none`). -/
  fieldEqs : ∀ x y, (x, y) ∈ relH → ∀ c : ∀ k, (ir.layout I).Ch k, (∀ k, ¬ bad k x y c) →
    ir.FieldEqsAt I (ir.execEnv I x (val y) (late y c) c)
  /-- Off the events, the packing of every table packed at a challenge is injective on its records
  in the environment of the execution (`PackFreeAt`; automatic for a program with no such table,
  `packFreeAt_of_noGamma`; an application with one charges the collisions to its events,
  `GordieHowe.prob_packCollision_le`). -/
  packFree : ∀ x y, (x, y) ∈ relH → ∀ c : ∀ k, (ir.layout I).Ch k, (∀ k, ¬ bad k x y c) →
    ir.PackFreeAt I (ir.execEnv I x (val y) (late y c) c) := by
    exact fun _ _ _ _ _ => packFreeAt_of_noGamma (by decide +kernel) _

open Classical in
/-- **An execution of the source program with per-phase errors** (`SourceExecutionCore`): the
completeness event of each phase has probability at most `δ` over the phase's challenge whatever
the others (`badBound`), so the events have together probability at most `∑ k, δ k`
(`HonestStrategy.complete`). -/
structure SourceExecution {Inp : Type} (relH : Set (ir.Valuation I × Inp)) extends
    ir.SourceExecutionCore I relH where
  /-- The completeness error at every phase. -/
  δ : Fin ir.phases → ℝ≥0
  /-- On the relation, at the challenges `c` of every phase, the event of phase `k + 1` has
  probability at most `δ k` over that phase's challenge, the others those of `c`. -/
  badBound : ∀ k x y, (x, y) ∈ relH → ∀ c : ∀ k, (ir.layout I).Ch k,
    Pr[c' ← (ir.layout I).Ch k : bad k x y (Function.update c k c')] ≤ δ k

/-- **The pad space of value `v` contains its type**, as a check: the whole field, or the node of
its type `Sub(E)`. -/
def latePadTypeB (v : ℕ) : Bool :=
  match (ir.value v).padSpace, (ir.value v).type with
  | .full, _ => true
  | .node E', .sub E => E == E'
  | .node _, _ => false

/-- **Late values in their pad spaces**: `l` at each coordinate where it lies in its value's pad
space, `0` elsewhere. -/
def padSpaceLate (l : ir.Valuation I) : ir.Valuation I := fun v i =>
  if l v i ∈ (I (ir.valueField v)).space (ir.value v).padSpace then l v i else 0

variable {ir I}

/-- **An element of a value's type lies in its pad space** where the pad space contains the type
(`latePadTypeB`). -/
theorem mem_space_of_latePadTypeB {v : ℕ} (h : ir.latePadTypeB v = true)
    {z : (I (ir.valueField v)).K} (hz : (I (ir.valueField v)).InType (ir.value v).type z) :
    z ∈ (I (ir.valueField v)).space (ir.value v).padSpace := by
  unfold latePadTypeB at h
  revert h hz
  generalize (ir.value v).padSpace = ps
  generalize (ir.value v).type = t
  intro h hz
  cases ps with
  | full => exact AddSubgroup.mem_top z
  | node E' =>
    cases t with
    | sub E =>
      simp only [beq_iff_eq] at h
      subst h
      exact hz
    | bit => simp at h
    | field => simp at h

/-- **Late values in their pad spaces lie in them.** -/
theorem padSpaceLate_mem (l : ir.Valuation I) (v i : ℕ) :
    ir.padSpaceLate I l v i ∈ (I (ir.valueField v)).space (ir.value v).padSpace := by
  unfold padSpaceLate
  split_ifs with h
  · exact h
  · exact AddSubgroup.zero_mem _

/-! ## Reading the environment of an execution -/

/-- **The environment of an execution reads a committed value** at a cell coordinate as its
phase-`0` value. -/
theorem reader_execEnv_priv (x s l : ir.Valuation I) (c : ∀ k, (ir.layout I).Ch k) {v i : ℕ}
    (hk : (ir.value v).kind = .priv) (hd : (ir.value v).domain < ir.domains.length)
    (hc : CellKey.val v i ∈ ir.cellKeys (ir.value v).domain) :
    ir.reader (ir.execEnv I x s l c) v i = s v i := by
  rw [reader_of_priv _ hk]
  simp only [execEnv, ExecCoord, hd, hc, and_self, true_or, ite_true]

/-- **The environment of an execution reads a value bound to its digits** below its size as its
phase-`0` value. -/
theorem reader_execEnv_bound (x s l : ir.Valuation I) (c : ∀ k, (ir.layout I).Ch k) {v i : ℕ}
    {e : Expr} (hk : (ir.value v).kind = .bound e) (hi : i < (ir.value v).size) :
    ir.reader (ir.execEnv I x s l c) v i = s v i := by
  have hr : ir.reader (ir.execEnv I x s l c) v i = (ir.execEnv I x s l c).asg.val v i := by
    simp [reader, fuel, read, hk]
  rw [hr]
  have hb : (ir.value v).kind.isBound = true := by rw [hk]; rfl
  simp only [execEnv, ExecCoord, hb, hi, and_self, or_true, ite_true]

/-! ## Environments agreeing on the source values -/

/-- **Two environments agree on the source values**: one statement, the same source challenges and
source late values, and the same committed values at the source values a value reads whole
(committed, pad copies, bound to their digits). -/
structure Env.AgreeOnSourceVals (e e' : ir.Env I) : Prop where
  /-- The statements agree. -/
  stmt : e.stmt = e'.stmt
  /-- The source challenges agree. -/
  chal : ∀ c, ir.chalIsSource c = true → e.chal c = e'.chal c
  /-- The source late values agree. -/
  late : ∀ u, ir.IsSourceValue u → e.late u = e'.late u
  /-- The committed values at the source values agree. -/
  val : ∀ u, ir.IsSourceValue u → e.asg.val u = e'.asg.val u

/-- **The agreement on the source values is symmetric.** -/
theorem Env.AgreeOnSourceVals.symm {e e' : ir.Env I} (h : Env.AgreeOnSourceVals e e') :
    Env.AgreeOnSourceVals e' e where
  stmt := h.stmt.symm
  chal c hc := (h.chal c hc).symm
  late u hu := (h.late u hu).symm
  val u hu := (h.val u hu).symm

/-- **A source value reads only source challenges and source late values** (`SourceValid`). -/
theorem sourceRead_of_mem_nodeReads (hs : ir.SourceValid) {v : ℕ} (hv : ir.IsSourceValue v)
    {rd : Read} (hr : rd ∈ ir.nodeReads ir.fuel v) : ir.SourceRead rd := by
  by_cases hl : v < ir.values.length
  · exact hs.reads v hl hv rd hr
  · rw [nodeReads_of_le (Nat.le_of_not_lt hl)] at hr
    cases hr

variable (ir) in
/-- **No source value is a message.** -/
def SrcNoMessage : Prop :=
  ∀ v < ir.values.length, ir.IsSourceValue v → (ir.value v).kind.isMessage = false

/-- **Environments agreeing on the source values read every source value alike**, with `n` levels,
where no source value is a message: a source value reads only source values (`SourceValid`). -/
theorem Env.AgreeOnSourceVals.read_eq (hs : ir.SourceValid) (hnm : ir.SrcNoMessage)
    {e e' : ir.Env I} (h : Env.AgreeOnSourceVals e e') :
    ∀ n v, ir.IsSourceValue v → ir.read e n v = ir.read e' n v
  | 0, _, _ => rfl
  | n + 1, v, hv => by
    have hdeps : ∀ w ∈ ir.valueDeps v, ir.IsSourceValue w := by
      intro w hw
      by_cases hl : v < ir.values.length
      · exact hs.values v hl hv w hw
      · have h0 : ir.valueDeps v = [] := by
          unfold valueDeps
          rw [value_eq_default (Nat.le_of_not_lt hl)]
          rfl
        rw [h0] at hw
        cases hw
    funext i
    rcases hk : (ir.value v).kind with
      _ | ⟨_ | ⟨name, args⟩ | x⟩ | es | c | _ | ⟨w, sel⟩ | ⟨u, m⟩ | u | xb
    case priv => simp only [read, hk, h.val v hv]
    case padCopy => simp only [read, hk, h.val v hv]
    case bound => simp only [read, hk, h.val v hv]
    case late => simp only [read, hk, h.late v hv]
    case challenge =>
      have hc : Read.chal c ∈ ir.nodeReads ir.fuel v := by
        simp [fuel, nodeReads, hk]
      simp only [read, hk, h.chal c (sourceRead_of_mem_nodeReads hs hv hc)]
    case message =>
      have hl : v < ir.values.length := by
        by_contra hl
        rw [value_eq_default (Nat.le_of_not_lt hl)] at hk
        cases hk
      have hm := hnm v hl hv
      rw [hk] at hm
      simp [Kind.isMessage] at hm
    case pub.input => simp only [read, hk, h.stmt]
    case pub.opaque =>
      simp only [read, hk, h.stmt]
      split_ifs
      · rfl
      · have hargs : args.map (fun u j => (I (ir.valueField u)).toNat (ir.read e n u j)) =
            args.map (fun u j => (I (ir.valueField u)).toNat (ir.read e' n u j)) :=
          List.map_congr_left fun u hu => by
            rw [Env.AgreeOnSourceVals.read_eq hs hnm h n u
              (hdeps u (by simp only [valueDeps, hk]; exact hu))]
        rw [hargs]
    case pub.expr =>
      simp only [read, hk]
      exact congrFun (evalE_congr fun u hu => Env.AgreeOnSourceVals.read_eq hs hnm h n u
        (hdeps u (by simp only [valueDeps, hk]; exact hu))) i
    case bits =>
      simp only [read, hk, bitView,
        Env.AgreeOnSourceVals.read_eq hs hnm h n w (hdeps w (by simp [valueDeps, hk]))]
    all_goals simp only [read, hk]

/-- **Environments agreeing on the source values read every source value alike**, where no source
value is a message. -/
theorem Env.AgreeOnSourceVals.reader_eq (hs : ir.SourceValid) (hnm : ir.SrcNoMessage)
    {e e' : ir.Env I} (h : Env.AgreeOnSourceVals e e') {v : ℕ} (hv : ir.IsSourceValue v) :
    ir.reader e v = ir.reader e' v :=
  h.read_eq hs hnm ir.fuel v hv

/-- **Environments agreeing on the source values agree on the source program's truth**: its
predicates read source values only (`SourceValid`). -/
theorem Env.AgreeOnSourceVals.sourceSatAt_congr (hs : ir.SourceValid) (hnm : ir.SrcNoMessage)
    {e e' : ir.Env I}
    (h : Env.AgreeOnSourceVals e e') : ir.SourceSatAt e ↔ ir.SourceSatAt e' := by
  have hp : ∀ p ∈ ir.predicates, ir.inSource p = true →
      (ir.HoldsAt e p.body ↔ ir.HoldsAt e' p.body) := fun p hp hsrc =>
    holdsWith_congr fun v hv => h.reader_eq hs hnm (hs.preds p hp hsrc v hv)
  rw [sourceSatAt_iff, sourceSatAt_iff]
  refine and_congr (forall₂_congr fun p hp' => forall_congr' fun hsrc => hp p hp' hsrc) ?_
  refine forall₂_congr fun v _ => forall_congr' fun hv => ?_
  rw [h.reader_eq hs hnm hv]

/-- **Environments agreeing on the source values read a source predicate's expressions alike.** -/
theorem Env.AgreeOnSourceVals.evalWith_eq (hs : ir.SourceValid) (hnm : ir.SrcNoMessage)
    {e e' : ir.Env I} (h : Env.AgreeOnSourceVals e e') {p : Predicate} (hp : p ∈ ir.predicates)
    (hsrc : ir.inSource p = true) {d : ℕ} {z : Expr} (hdz : (d, z) ∈ p.body.exprs) :
    ir.evalWith (ir.reader e) d z = ir.evalWith (ir.reader e') d z :=
  funext fun i => congrFun (evalE_congr fun w hw => h.reader_eq hs hnm
    (hs.preds p hp hsrc w (List.mem_append_left _ (List.mem_flatMap.2 ⟨(d, z), hdz, hw⟩)))) i

/-- **Environments agreeing on the source values agree on the source cross-field `equal`s'
bits.** -/
theorem Env.AgreeOnSourceVals.crossBitsAt (hs : ir.SourceValid) (hnm : ir.SrcNoMessage)
    {e e' : ir.Env I}
    (h : Env.AgreeOnSourceVals e e') (hc : ir.CrossBitsAt I e) : ir.CrossBitsAt I e' := by
  intro p hp hsrc dx x dy y k real hb
  obtain ⟨hx, hy⟩ := hc p hp hsrc dx x dy y k real hb
  rw [← h.evalWith_eq hs hnm hp hsrc (by rw [hb]; simp [PredBody.exprs] : (dx, x) ∈ _),
    ← h.evalWith_eq hs hnm hp hsrc (by rw [hb]; simp [PredBody.exprs] : (dy, y) ∈ _)]
  exact ⟨hx, hy⟩

/-- **Environments agreeing on the source values agree on the source field-form `mod_q`s' field
equations.** -/
theorem Env.AgreeOnSourceVals.fieldEqsAt (hs : ir.SourceValid) (hnm : ir.SrcNoMessage)
    {e e' : ir.Env I}
    (h : Env.AgreeOnSourceVals e e') (hf : ir.FieldEqsAt I e) : ir.FieldEqsAt I e' := by
  intro p hp hsrc d q a b real hb hform
  rw [← h.evalWith_eq hs hnm hp hsrc (by rw [hb]; simp [PredBody.exprs] : (d, a) ∈ _),
    ← h.evalWith_eq hs hnm hp hsrc (by rw [hb]; simp [PredBody.exprs] : (d, b) ∈ _)]
  exact hf p hp hsrc d q a b real hb hform

/-- **A program without field-form `mod_q`s has its field equations in every environment.** -/
theorem fieldEqsAt_of_none (h : ∀ p < ir.predicates.length, ir.isFieldForm p = false)
    (e : ir.Env I) : ir.FieldEqsAt I e := by
  intro p hp _ d q a b real hb hform
  obtain ⟨k, hk, rfl⟩ := exists_index_of_mem hp
  have := h k hk
  simp [isFieldForm, hb, hform] at this

/-! ## The committed values the realizations add -/

/-- **A digit of a two-sided or digit lookup**: digit `idx` of the `in` predicate `pid`'s record, in
the first digit set (`second = false`: the record's digits) or, for a two-sided lookup, in the
second (`second = true`: the digits of `N − 1` minus the record). -/
structure LookupDigit where
  /-- The `in` predicate. -/
  pid : ℕ
  /-- The digit set. -/
  second : Bool
  /-- The digit's position. -/
  idx : ℕ
  deriving DecidableEq

/-- **The honest lookup digit `o` at coordinate `i`** at the reader `rd`: for the `in` predicate's
record `v` (its first record) and range `[0, N)`, digit `o.idx` in base `T` of the integer reading
of `v` (first set) or of `N − 1` minus it (second set). -/
def lookupDigitNat (rd : ir.Valuation I) (o : LookupDigit) (i : ℕ) : ℕ :=
  match (ir.predicate o.pid).body with
  | .mem d recs set (.lookup r) =>
    (if o.second then set.bound - 1 - (I (ir.domainField d)).toNat (ir.evalWith rd d (recs.headD default) i)
      else (I (ir.domainField d)).toNat (ir.evalWith rd d (recs.headD default) i)) /
        r.base ^ o.idx % r.base
  | _ => 0

variable (ir) in
/-- **An expression through a top shared expression**: `.ref k` the shared expression `k`, any other
expression itself. -/
def unref : Expr → Expr
  | .ref k => if k < ir.exprs.length then ir.expr k else .ref k
  | e => e

/-- **An expression through a top shared expression reads alike** (`unref`, `evalE_ref`). -/
theorem evalE_unref (hwf : ir.WellFormed) (rd : ir.Valuation I) (f : ℕ) (e : Expr) (i : ℕ) :
    ir.evalE rd f (ir.unref e) i = ir.evalE rd f e i := by
  cases e with
  | ref k =>
    by_cases hk : k < ir.exprs.length
    · simp only [unref, hk, ite_true]
      rw [evalE_ref hwf.refsOrdered _ _ hk]
    · simp only [unref, hk, ite_false]
  | _ => rfl

/-- **A digit of a committed-digits `mod_q`'s quotient, looked up by its digits**: the `mod_q`
`mod` (a source `mod_q` in the committed-digits form), the position `j` of the quotient digit, the
digit lookup `lk` whose record is that quotient digit, and the position `k` of the committed value
among the lookup's digits. -/
structure CommDigit where
  /-- The committed-digits `mod_q`. -/
  mod : ℕ
  /-- The position of the quotient digit. -/
  j : ℕ
  /-- The digit lookup whose record is the quotient digit. -/
  lk : ℕ
  /-- The position among the lookup's digits. -/
  k : ℕ
  deriving DecidableEq

variable (ir) in
/-- **The source `mod_q`s in the committed-digits form**, by index. -/
def srcCommMods : List ℕ :=
  (List.range ir.predicates.length).filter fun m =>
    ir.inSource (ir.predicateT m) &&
      match (ir.predicateT m).body with
      | .mod _ _ _ _ real => real.form == .committedDigits
      | _ => false

variable (ir) in
/-- **The source committed-digits `mod_q` `m` listing `rec` among its digits**, and the digit's
position (`commRecOf?`'s step, through the predicates' table `pr`). -/
def commRecStep (pr : ℕ → Predicate) (rec : Expr) (m : ℕ) : Option (ℕ × ℕ) :=
  if ir.inSource (pr m) = true then
    match (pr m).body with
    | .mod _ _ _ _ real =>
      if real.form = .committedDigits then
        (real.digits.findIdx? fun D => D.beq rec).map fun j => (m, j)
      else none
    | _ => none
  else none

variable (ir) in
/-- **The quotient digit the record of predicate `lk` is**, searched among the
source committed-digits `mod_q`s (`srcCommMods`) through the predicates' table. -/
def commRecOf? (lk : ℕ) : Option (ℕ × ℕ) :=
  match (ir.predicateT lk).body with
  | .mem _ [rec] (.range _) (.lookup r) =>
    if r.kind = .digits then ir.srcCommMods.findSome? (ir.commRecStep ir.predicateT rec) else none
  | _ => none

/-- **The honest quotient of the committed-digits `mod_q` `m`** at coordinate `i` at the reader
`rd`: `(e − e') / q − qlo` over the sides' integer readings, as a natural. -/
def commQuot (rd : ir.Valuation I) (m i : ℕ) : ℕ :=
  match (ir.predicate m).body with
  | .mod d q e e' real =>
    ((ir.evalIntWith rd d e i - ir.evalIntWith rd d e' i) / q - real.quotientLo).toNat
  | _ => 0

/-- **The honest committed digit `o` at coordinate `i`** at the reader `rd`: digit `o.k` in the
lookup's base `T` of digit `o.j` in the radix `R` of the honest quotient (`commQuot`). -/
def commDigitNat (rd : ir.Valuation I) (o : CommDigit) (i : ℕ) : ℕ :=
  match (ir.predicate o.mod).body, lookupOf? (ir.predicate o.lk).body with
  | .mod _ _ _ _ real, some r =>
    ir.commQuot rd o.mod i / real.radix ^ o.j % real.radix / r.base ^ o.k % r.base
  | _, _ => 0

/-- **The honest transformed value of the convolution `c` at coordinate `i`** at the reader `rd`:
the integer reading of its products predicate's left side `NTT_M(a) · NTT_M(b)`. -/
def specNat (rd : ir.Valuation I) (c : SpectralConv) (i : ℕ) : ℕ :=
  match (ir.predicate c.products).body with
  | .equal d lhs _ _ => (I (ir.domainField d)).toNat (ir.evalWith rd d lhs i)
  | _ => 0

/-- **The needles a static histogram counts** in group `g` of table `t`: with a late histogram
beside it, the needles of the members reading no late value (`staticNeedles`; the late histogram
counts the others); otherwise all the group's needles. -/
def staticHistNeedles (rd : ir.Valuation I) (f t g : ℕ) : List (I f).K :=
  if (ir.groupOf t g).lateMult.isSome then ir.staticNeedles rd f t g else ir.groupNeedles rd f t g

/-- **The honest count of row `j` of table `t`** over the needles `ns`, a natural, reading values
by `rd` in the field of the table's challenge (`honestCounts`): for a range, the number of needles
equal to `j`; for any other table, at a row's first occurrence the number of needles equal to it
(`tableRow`), at a repeated row `0` (`Range.rowHistogram`; the C++ gives each record's count to its
first matching row, `lib::table::table_internal::first_match_counts`). -/
def rowCountNat (rd : ir.Valuation I) (t : ℕ) (ns : List (I (ir.chalField (ir.alphaOf t))).K)
    (j : Fin (ir.tableSize t)) : ℕ :=
  match (ir.table t).rows with
  | .range _ => ns.count (j : (I (ir.chalField (ir.alphaOf t))).K)
  | _ =>
    if ∀ k : Fin (ir.tableSize t), k < j →
        ir.tableRow rd (ir.chalField (ir.alphaOf t)) t k ≠
          ir.tableRow rd (ir.chalField (ir.alphaOf t)) t j then
      ns.count (ir.tableRow rd (ir.chalField (ir.alphaOf t)) t j)
    else 0

/-- **The honest count of a range's row `j`** is the number of needles equal to `j`. -/
theorem rowCountNat_of_isRange {t : ℕ} (hr : ir.IsRange t) (rd : ir.Valuation I)
    (ns : List (I (ir.chalField (ir.alphaOf t))).K) (j : Fin (ir.tableSize t)) :
    ir.rowCountNat rd t ns j = ns.count (j : (I (ir.chalField (ir.alphaOf t))).K) := by
  unfold rowCountNat
  split
  · rfl
  · rename_i hne
    exact absurd hr (hne _)

/-- **The honest counts of a row depend only on the values the rows read** (`tableRowReads`). -/
theorem rowCountNat_congr {rd rd' : ir.Valuation I} {t : ℕ}
    (h : ∀ w ∈ ir.tableRowReads t, rd w = rd' w) : ir.rowCountNat rd t = ir.rowCountNat rd' t := by
  funext ns j
  unfold rowCountNat
  rw [tableRow_congr_reads h]

/-- **The honest counts of a group are its rows' honest counts** (`rowCountNat`) over its needles,
cast to the field of the table's challenge. -/
theorem rowCountNat_groupNeedles (rd : ir.Valuation I) (t g : ℕ) (j : Fin (ir.tableSize t)) :
    ((ir.rowCountNat rd t (ir.groupNeedles rd (ir.chalField (ir.alphaOf t)) t g) j : ℕ) :
        (I (ir.chalField (ir.alphaOf t))).K) = ir.honestCounts rd t g j := by
  unfold rowCountNat honestCounts
  rcases (ir.table t).rows with _ | _ | _ <;> simp [Range.histogram, Range.rowHistogram]

/-- **No needle has no count.** -/
theorem rowCountNat_nil (rd : ir.Valuation I) (t : ℕ) (j : Fin (ir.tableSize t)) :
    ir.rowCountNat rd t [] j = 0 := by
  unfold rowCountNat
  split <;> simp

variable (ir) in
/-- **The members a static histogram counts** in group `g` of table `t`: with a late histogram
beside it, the members reading no late value (the late histogram counts the others); otherwise all
the group's members. -/
def staticMembers (t g : ℕ) : List Member :=
  if (ir.groupOf t g).lateMult.isSome then (ir.members t g).filter fun m => !ir.memberReadsLate m
  else ir.members t g

/-- **The honest count of row `j` of a table packed at a value** (`gammaPack?`, its powers' value
`P`, `A` columns of `b`) over the members `ms`, read by `rd` in the field of the table's challenge:
the records' counts (`lib::table::table_internal::first_match_counts`), at a first occurrence of
row `j`'s record (`tupleOf`) among the rows the number of the members' records (`memberTuples`)
equal to it, at a repeat `0`. -/
def tupleCountNat (rd : ir.Valuation I) (t P A : ℕ) (b : Expr) (ms : List Member)
    (j : Fin (ir.tableSize t)) : ℕ :=
  if ∀ k : Fin (ir.tableSize t), k < j → ir.tupleOf rd (ir.chalField (ir.alphaOf t)) A b k ≠
      ir.tupleOf rd (ir.chalField (ir.alphaOf t)) A b j then
    (ms.flatMap (ir.memberTuples rd (ir.chalField (ir.alphaOf t)) P A)).count
      (ir.tupleOf rd (ir.chalField (ir.alphaOf t)) A b j)
  else 0

/-- **The static histogram of group `g` of table `t`**, entry `j`, read by `rd` in the field of the
table's challenge: for a table packed at a value, the records' counts over the members it counts
(`tupleCountNat`, `staticMembers`); otherwise the honest count of row `j` (`rowCountNat`) over the
needles it counts (`staticHistNeedles`); `0` past the table's size. -/
def staticHistNat (rd : ir.Valuation I) (t g j : ℕ) : ℕ :=
  if h : j < ir.tableSize t then
    match ir.gammaPack? t with
    | some (P, A, b) => ir.tupleCountNat rd t P A b (ir.staticMembers t g) ⟨j, h⟩
    | none => ir.rowCountNat rd t (ir.staticHistNeedles rd (ir.chalField (ir.alphaOf t)) t g) ⟨j, h⟩
  else 0

/-- **The static histogram of a table packed at no value** is the rows' honest counts. -/
theorem staticHistNat_of_none {t : ℕ} (hp : ir.gammaPack? t = none) (rd : ir.Valuation I) (g : ℕ)
    (j : Fin (ir.tableSize t)) :
    ir.staticHistNat rd t g j =
      ir.rowCountNat rd t (ir.staticHistNeedles rd (ir.chalField (ir.alphaOf t)) t g) j := by
  simp [staticHistNat, j.isLt, hp]

/-- **The static histogram of a table packed at a value** is the records' counts. -/
theorem staticHistNat_of_some {t P A : ℕ} {b : Expr} (hp : ir.gammaPack? t = some (P, A, b))
    (rd : ir.Valuation I) (g : ℕ) (j : Fin (ir.tableSize t)) :
    ir.staticHistNat rd t g j = ir.tupleCountNat rd t P A b (ir.staticMembers t g) j := by
  simp [staticHistNat, j.isLt, hp]

/-- **A range is packed at no value.** -/
theorem gammaPack_of_isRange {t : ℕ} (hr : ir.IsRange t) : ir.gammaPack? t = none := by
  unfold gammaPack?
  rw [hr]

variable (ir I) in
/-- **The challenges the committed values are computed at**: every coordinate the default (the
committed values read no challenge). -/
def chal0 : ∀ k, (ir.layout I).Ch k := fun _ _ _ => default

/-! ## The honest environment at the source values -/

/-- **The honest assignment reads a value that is no pad copy** at its cells as the committed values,
`0` elsewhere. -/
theorem honestAsg_val_eq_ite {val : ir.Valuation I} {π : (ir.layout I).Pads} {v : ℕ}
    (hk : ∀ w m, (ir.value v).kind ≠ .padCopy w m) :
    (ir.honestAsg I val π).val v = fun i =>
      if (ir.value v).domain < ir.domains.length ∧
        CellKey.val v i ∈ ir.cellKeys (ir.value v).domain then val v i else 0 := by
  funext i
  split_ifs with h
  · rw [honestAsg_val h.1 h.2]
    simp only [copyVal]
  · simp only [honestAsg, ofAllCells]
    split
    · rename_i hd
      simp only [ofCells]
      rw [dite_eq_right_iff.2 fun hc => absurd ⟨hd, hc⟩ h]
    · rfl

/-- **A value bound to its digits has no cell.** -/
theorem notMem_cellKeys_of_isBound {v i d : ℕ} (hb : (ir.value v).kind.isBound = true) :
    CellKey.val v i ∉ ir.cellKeys d := fun h => by
  obtain ⟨-, hc, -⟩ := (ir.mem_cellKeys_val).1 h
  unfold isCellValue at hc
  revert hb hc
  cases (ir.value v).kind <;> simp [Kind.isBound]

/-- **The environment of an execution reads the committed assignment** at a value not bound to its
digits as the phase-`0` values at its cells, `0` elsewhere. -/
theorem execEnv_asg_val_of_not_bound (x s l : ir.Valuation I) (c : ∀ k, (ir.layout I).Ch k)
    {v : ℕ} (hb : (ir.value v).kind.isBound = false) :
    (ir.execEnv I x s l c).asg.val v = fun i =>
      if (ir.value v).domain < ir.domains.length ∧
        CellKey.val v i ∈ ir.cellKeys (ir.value v).domain then s v i else 0 := by
  funext i
  simp only [execEnv, ExecCoord, hb, Bool.false_eq_true, false_and, or_false]

/-- **The environment of an execution reads the committed assignment** at a value bound to its
digits as the phase-`0` values below its size, `0` past it. -/
theorem execEnv_asg_val_of_isBound (x s l : ir.Valuation I) (c : ∀ k, (ir.layout I).Ch k)
    {v : ℕ} (hb : (ir.value v).kind.isBound = true) :
    (ir.execEnv I x s l c).asg.val v = fun i => if i < (ir.value v).size then s v i else 0 := by
  funext i
  simp only [execEnv, ExecCoord, hb, notMem_cellKeys_of_isBound hb, and_false, true_and, false_or]

/-! ## The digits of a natural -/

/-- **The `k` base-`T` digits of a natural** recover it modulo `T^k` (`Nat.ofDigits`). -/
theorem ofDigits_range_digits (T : ℕ) : ∀ k n : ℕ,
    Nat.ofDigits T ((List.range k).map fun j => n / T ^ j % T) = n % T ^ k
  | 0, n => by simp [Nat.mod_one]
  | k + 1, n => by
    rw [List.range_succ, List.map_append, Nat.ofDigits_append, ofDigits_range_digits T k n,
      List.length_map, List.length_range, List.map_singleton, Nat.ofDigits_singleton,
      Nat.mod_pow_succ]

/-- **The `k` base-`T` digits of a natural, cast into a semiring**, have its cast modulo `T^k`. -/
theorem digitsVal_range_digits {K : Type} [Semiring K] (T k n : ℕ) :
    digitsVal (T : K) ((List.range k).map fun j => ((n / T ^ j % T : ℕ) : K)) =
      ((n % T ^ k : ℕ) : K) := by
  rw [← ofDigits_range_digits T k n, ← digitsVal_natCast, List.map_map]
  rfl

/-- **Zero digits have the value `0`.** -/
theorem digitsVal_map_zero {K : Type} [Semiring K] (T : K) {α : Type} (l : List α) :
    digitsVal T (l.map fun _ => (0 : K)) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [digitsVal, List.map_cons, List.foldr_cons] at ih ⊢
    rw [ih, mul_zero, add_zero]

/-- **A list mapped by a function of the positions**: where `f` reads each entry `l[j]` as `g j`, the
image of `l` is the image of its positions. -/
theorem map_eq_map_range {α β : Type} (l : List α) (f : α → β) (g : ℕ → β)
    (h : ∀ j (hj : j < l.length), f l[j] = g j) : l.map f = (List.range l.length).map g := by
  refine List.ext_getElem (by simp) fun j h1 _ => ?_
  simp only [List.getElem_map, List.getElem_range]
  exact h j (by simpa using h1)

variable {primeNodes : ℕ → List String} {L : ℕ → ℕ → Option Ivl}

/-- **An expression that is the number of its digits** (`digitsExprOk`), where the reader reads each
digit `us[j]` at coordinate `i` as digit `j` of `n` in base `T` (in the expression's field), reads
`n` modulo `T^k` there. -/
theorem evalE_of_digitsExprOk_digits (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I}
    {f T : ℕ} (hf : f < ir.fields.length) {x : Expr} {us : List ℕ}
    (hx : digitsExprOk (ir.charOf f) T x us = true) {n i : ℕ}
    (hdig : ∀ j (hj : j < us.length), (castElt (rd us[j] i) : (I f).K) = ((n / T ^ j % T : ℕ) : _)) :
    ir.evalE rd f x i = ((n % T ^ us.length : ℕ) : (I f).K) := by
  rw [evalE_of_digitsExprOk rd (fun c hc => hL.decode_natCast f hf c hc) hx i,
    map_eq_map_range us _ _ hdig, digitsVal_range_digits]

/-- **An expression that is the number of its digits** (`digitsExprOk`) reads `0` where the reader
reads every digit as `0`. -/
theorem evalE_of_digitsExprOk_zero (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I}
    {f T : ℕ} (hf : f < ir.fields.length) {x : Expr} {us : List ℕ}
    (hx : digitsExprOk (ir.charOf f) T x us = true) {i : ℕ}
    (hz : ∀ u ∈ us, (castElt (rd u i) : (I f).K) = 0) : ir.evalE rd f x i = 0 := by
  rw [evalE_of_digitsExprOk rd (fun c hc => hL.decode_natCast f hf c hc) hx i,
    List.map_congr_left hz, digitsVal_map_zero]

/-! ## Two-sided and digit lookups -/

/-- **A value whose memoized reads are empty reads nothing** (`mem_readsT`). -/
theorem notMem_nodeReads_of_isEmpty (hwf : ir.WellFormed) {w : ℕ}
    (hw : (ir.readsT.getD w []).isEmpty = true) (rd : Read) : rd ∉ ir.nodeReads ir.fuel w := by
  simp [mem_readsT hwf, List.isEmpty_iff.1 hw]

/-- **A value that reads no challenge and no late value** reads alike in the environments of two
executions with the same phase-`0` values. -/
theorem reader_execEnv_congr_of_isEmpty (hwf : ir.WellFormed) (x s l l' : ir.Valuation I)
    (c c' : ∀ k, (ir.layout I).Ch k) {w : ℕ} (hw : (ir.readsT.getD w []).isEmpty = true) :
    ir.reader (ir.execEnv I x s l c) w = ir.reader (ir.execEnv I x s l' c') w := by
  have hn := notMem_nodeReads_of_isEmpty hwf hw
  exact read_congr_vals (e := ir.execEnv I x s l c) (e' := ir.execEnv I x s l' c') rfl _ w
    (fun c hc => absurd hc (hn _)) (fun u hu => absurd hu (hn _)) fun _ _ => rfl

/-! ## The honest rows of a two-sided lookup -/

/-- **A field element that is the cast of a natural below `N ≤ p`** is the cast of its integer
reading, which is below `N`. -/
theorem natCast_toNat_of_isNatBelow (hL : I.Lawful ir primeNodes) {f N : ℕ}
    (hf : f < ir.fields.length) (hN : N ≤ ir.charOf f) {y : (I f).K} (h : IsNatBelow N y) :
    (((I f).toNat y : ℕ) : (I f).K) = y ∧ (I f).toNat y < N := by
  obtain ⟨m, hm, rfl⟩ := h
  rw [hL.toNat_natCast f hf m (by simp only [charOf] at hN; omega)]
  exact ⟨rfl, hm⟩

/-- **The digits of the record at a reader**: at every coordinate below the record's length, each
digit value `d_j` reads digit `j` in base `T` of the record's integer reading, and each second digit
`h_j` reads digit `j` of `N − 1` minus it (cast into the domain's field). -/
structure DigitsRead (rd : ir.Valuation I) (d : ℕ) (rec : Expr) (N : ℕ) (r : LookupRealization) :
    Prop where
  /-- The first digits. -/
  first : ∀ j (hj : j < r.digitValues.length), ∀ i < ir.exprLen rec,
    (castElt (rd r.digitValues[j] i) : (I (ir.domainField d)).K) =
      (((I (ir.domainField d)).toNat (ir.evalWith rd d rec i) / r.base ^ j % r.base : ℕ) : _)
  /-- The second digits. -/
  second : ∀ j (hj : j < r.second.length), ∀ i < ir.exprLen rec,
    (castElt (rd r.second[j] i) : (I (ir.domainField d)).K) =
      (((N - 1 - (I (ir.domainField d)).toNat (ir.evalWith rd d rec i)) / r.base ^ j %
        r.base : ℕ) : _)

/-! ## Values bound to their digits -/

variable (ir) in
/-- **Value `v` is the record of the `in` predicate `pid`, bound to its digits**, as a check: a
two-sided or digit lookup with one record and a range whose record is `v` or `v + c`, `v` bound to
its digits (`boundDigitsOk`), and `c` a constant of at most `v`'s size with entries below the
characteristic. -/
def boundRecAtB (v pid : ℕ) : Bool :=
  match (ir.predicate pid).body with
  | .mem d [rec] (.range _) (.lookup r) =>
    (r.kind == .twoSided || r.kind == .digits) && (ir.commRecOf? pid).isNone &&
      ir.boundDigitsOk d rec r &&
      match rec with
      | .leaf u => u == v
      | .add (.leaf u) (.leaf c) =>
        u == v && match (ir.value c).kind with
          | .constant es => decide (es.length ≤ (ir.value v).size) &&
              es.all (· < ir.charOf (ir.valueField c))
          | _ => false
      | _ => false
  | _ => false

variable (ir) in
/-- **Value `v` is the record of a two-sided or digit lookup, bound to its digits**, as a check. -/
def boundRecB (v : ℕ) : Bool := (List.range ir.predicates.length).any (ir.boundRecAtB v)

/-- **The lookup whose record a value bound to its digits is**: its body, the record `v` or `v + c`
with the constant `c`, and the record bound to the digits. -/
theorem exists_of_boundRecB {v : ℕ} (h : ir.boundRecB v = true) :
    ∃ pid < ir.predicates.length, ∃ d rec N r,
      (ir.predicate pid).body = .mem d [rec] (.range N) (.lookup r) ∧
        (r.kind = .twoSided ∨ r.kind = .digits) ∧ ir.commRecOf? pid = none ∧
          ir.boundDigitsOk d rec r = true ∧
        (rec = .leaf v ∨ ∃ c es, rec = .add (.leaf v) (.leaf c) ∧
          (ir.value c).kind = .constant es ∧ es.length ≤ (ir.value v).size ∧
            ∀ k ∈ es, k < ir.charOf (ir.valueField c)) := by
  obtain ⟨pid, hpid, h⟩ := List.any_eq_true.1 h
  rw [List.mem_range] at hpid
  unfold boundRecAtB at h
  split at h
  · rename_i d rec N r hb
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hk, hnc⟩, hbd⟩, hr⟩ := h
    refine ⟨pid, hpid, d, rec, N, r, hb, hk, Option.isNone_iff_eq_none.1 hnc, hbd, ?_⟩
    split at hr
    · rename_i u
      simp only [beq_iff_eq] at hr
      exact .inl (by rw [hr])
    · rename_i u c
      simp only [Bool.and_eq_true, beq_iff_eq] at hr
      obtain ⟨rfl, hc⟩ := hr
      split at hc
      · rename_i es hk'
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
        exact .inr ⟨c, es, rfl, hk', hc.1, hc.2⟩
      · cases hc
    · cases hr
  · cases h

/-! ## The program facts of the honest strategy from an execution -/

/-- Whether a kind is a pad copy. -/
def _root_.GordieHowe.RealizedProgram.Kind.isPadCopy : Kind → Bool
  | .padCopy _ _ => true
  | _ => false

/-- **A static histogram counts its members' needles** (`staticHistNeedles`, `staticMembers`). -/
theorem staticHistNeedles_eq (rd : ir.Valuation I) (f t g : ℕ) :
    ir.staticHistNeedles rd f t g = (ir.staticMembers t g).flatMap (ir.memberVals rd f) := by
  unfold staticHistNeedles staticMembers staticNeedles groupNeedles
  split <;> rfl

/-- **The needles of a list of members depend only on their values.** -/
theorem flatMap_memberVals_congr {rd rd' : ir.Valuation I} {f : ℕ} {ms : List Member}
    (h : ∀ m ∈ ms, ∀ v ∈ ir.exprNodes (ir.needleExpr m.pred m.needle), rd v = rd' v) :
    ms.flatMap (ir.memberVals rd f) = ms.flatMap (ir.memberVals rd' f) := by
  refine List.flatMap_congr fun m hm => ?_
  simp only [memberVals, evalE_congr (f := f) (h m hm)]

variable (ir) in
/-- **The values the honest static histogram reads of member `m`'s needle** in table `t`: for a
table packed at a value, its records' expression (`memberBase?`); otherwise the needle's values. -/
def histNodes (t : ℕ) (m : Member) : List ℕ :=
  match ir.gammaPack? t with
  | some (P, A, _) =>
    match ir.memberBase? P A m with
    | some b => ir.exprNodes b
    | none => ir.exprNodes (ir.needleExpr m.pred m.needle)
  | none => ir.exprNodes (ir.needleExpr m.pred m.needle)

variable (ir) in
/-- **The values the honest static histogram reads of table `t`'s rows**: for a table packed at a
value, its records' expression's values; otherwise the rows' (`tableRowReads`). -/
def histRowNodes (t : ℕ) : List ℕ :=
  match ir.gammaPack? t with
  | some (_, _, b) => ir.exprNodes b
  | none => ir.tableRowReads t

variable (ir) in
/-- **Member `m`'s needle is packed at the value `P` with `A` columns**, as a check
(`memberBase?`): its coordinates within the needle's length, its records' expression reading only
source values. -/
def packMemberB (P A : ℕ) (m : Member) : Bool :=
  match ir.memberBase? P A m with
  | some b => decide (m.first + m.count ≤ ir.exprLen (ir.needleExpr m.pred m.needle)) &&
      (ir.exprNodes b).all fun w => decide (ir.IsSourceValue w)
  | none => false

variable (ir) in
/-- **The static members of group `g` of a table packed at a value are packed alike**, as a check:
the powers' value and the rows' records read only source values, and every member it counts is
packed at the table's value and arity (`packMemberB`); a table packed at no value passes. -/
def packGroupB (t g : ℕ) : Bool :=
  match ir.gammaPack? t with
  | some (P, A, b) => decide (ir.IsSourceValue P) &&
      (ir.exprNodes b).all (fun w => decide (ir.IsSourceValue w)) &&
      (ir.staticMembers t g).all (ir.packMemberB P A)
  | none => true

/-- **The static histogram depends only on the values it reads** (`histNodes`, `histRowNodes`). -/
theorem staticHistNat_congr {rd rd' : ir.Valuation I} {t g : ℕ}
    (hn : ∀ m ∈ ir.staticMembers t g, ∀ w ∈ ir.histNodes t m, rd w = rd' w)
    (hr : ∀ w ∈ ir.histRowNodes t, rd w = rd' w) :
    ir.staticHistNat rd t g = ir.staticHistNat rd' t g := by
  funext j
  by_cases hj : j < ir.tableSize t
  swap
  · simp [staticHistNat, hj]
  rcases hp : ir.gammaPack? t with _ | ⟨P, A, b⟩
  · simp only [histNodes, hp] at hn
    simp only [histRowNodes, hp] at hr
    rw [staticHistNat_of_none hp rd g ⟨j, hj⟩, staticHistNat_of_none hp rd' g ⟨j, hj⟩,
      staticHistNeedles_eq, staticHistNeedles_eq, flatMap_memberVals_congr hn, rowCountNat_congr hr]
  · simp only [histNodes, hp] at hn
    simp only [histRowNodes, hp] at hr
    rw [staticHistNat_of_some hp rd g ⟨j, hj⟩, staticHistNat_of_some hp rd' g ⟨j, hj⟩]
    have ht : ir.tupleOf rd (ir.chalField (ir.alphaOf t)) A b =
        ir.tupleOf rd' (ir.chalField (ir.alphaOf t)) A b := funext fun i => by
      simp only [tupleOf, evalE_congr hr]
    have hm : (ir.staticMembers t g).flatMap (ir.memberTuples rd (ir.chalField (ir.alphaOf t)) P A) =
        (ir.staticMembers t g).flatMap (ir.memberTuples rd' (ir.chalField (ir.alphaOf t)) P A) :=
      List.flatMap_congr fun m hm' => by
        have hw := hn m hm'
        unfold memberTuples
        split
        · rename_i b' hb'
          simp only [hb'] at hw
          simp only [tupleOf, evalE_congr hw]
        · rfl
    unfold tupleCountNat
    rw [ht, hm]

variable (ir) in
/-- **A committed cell's node and type, as a check**: a node, and for a source value a type the
node's subgroup contains: the node's subfield, `Bit`, or `Field` at the node of the domain's field
itself (the root of its packing tree, the whole field, `Interp.Lawful.rootNode`). -/
def cellNodeB (v : ℕ) : Bool :=
  match (ir.value v).node with
  | some nr => !decide (ir.IsSourceValue v) ||
      ((ir.value v).type == .sub nr.name || (ir.value v).type == .bit ||
        ((ir.value v).type == .field &&
          nr.name == (ir.field (ir.domainField (ir.value v).domain)).name))
  | none => false

variable (ir I) in
/-- **The subgroup of value `v`'s node contains `1`**, as a check (the node's membership test, in
its domain's field). -/
def oneMemB (v : ℕ) : Bool :=
  match (ir.value v).node with
  | some nr => @decide ((1 : (I (ir.domainField (ir.value v).domain)).K) ∈
      (I (ir.domainField (ir.value v).domain)).node nr.name)
      ((I (ir.domainField (ir.value v).domain)).memDec nr.name 1)
  | none => true

/-- **A node passing the check contains `1`.** -/
theorem one_mem_of_oneMemB {v : ℕ} (h : ir.oneMemB I v = true) {nr : NodeRef}
    (hn : (ir.value v).node = some nr) :
    (1 : (I (ir.domainField (ir.value v).domain)).K) ∈
      (I (ir.domainField (ir.value v).domain)).node nr.name := by
  unfold oneMemB at h
  rw [hn] at h
  exact @of_decide_eq_true _ ((I (ir.domainField (ir.value v).domain)).memDec nr.name 1) h

/-- **A node containing `1` passes the check.** -/
theorem oneMemB_of_mem {v : ℕ} {nr : NodeRef} (hn : (ir.value v).node = some nr)
    (h : (1 : (I (ir.domainField (ir.value v).domain)).K) ∈
      (I (ir.domainField (ir.value v).domain)).node nr.name) : ir.oneMemB I v = true := by
  unfold oneMemB
  rw [hn]
  exact @decide_eq_true _ ((I (ir.domainField (ir.value v).domain)).memDec nr.name 1) h

variable (ir I) in
/-- **The type of value `v` contains the naturals by its node**: the field, or a node whose subgroup
contains `1`. -/
def NatTyped (v : ℕ) : Prop :=
  match (ir.value v).type with
  | .field => True
  | .sub E => (1 : (I (ir.valueField v)).K) ∈ (I (ir.valueField v)).node E
  | .bit => False

/-- **A value whose type contains the naturals by its node** has every natural in its type. -/
theorem NatTyped.inType {v : ℕ} (h : ir.NatTyped I v) (n : ℕ) :
    (I (ir.valueField v)).InType (ir.value v).type (n : (I (ir.valueField v)).K) := by
  unfold NatTyped at h
  unfold FieldInterp.InType
  split at h
  · rename_i ht
    rw [ht]
    trivial
  · rename_i E ht
    rw [ht]
    have := AddSubgroup.nsmul_mem _ h n
    simpa using this
  · exact h.elim

/-! ### Nodes containing `1` -/

/-- **A list of nodes containing `1`**: each pair `(f, S)` is a field identifier and a node of
that field's interpretation whose subgroup contains `1` (a property of the interpretation, proved
once per family). -/
def OneNodes (I : Interp) (L : List (ℕ × String)) : Prop := ∀ p ∈ L, (1 : (I p.1).K) ∈ (I p.1).node p.2

variable (ir) in
/-- **Value `v`'s committed cell is at a listed node**, as a check: its node, in the field of its
domain, is in `L`. -/
def cellNodeInB (L : List (ℕ × String)) (v : ℕ) : Bool :=
  match (ir.value v).node with
  | some nr => L.contains (ir.domainField (ir.value v).domain, nr.name)
  | none => false

/-- **A committed cell at a listed node** passes the check that its node contains `1`. -/
theorem oneMemB_of_cellNodeInB {L : List (ℕ × String)} (hL : OneNodes I L) {v : ℕ}
    (h : ir.cellNodeInB L v = true) : ir.oneMemB I v = true := by
  unfold cellNodeInB at h
  cases hn : (ir.value v).node with
  | none =>
    rw [hn] at h
    cases h
  | some nr =>
    rw [hn, List.contains_iff_mem] at h
    exact oneMemB_of_mem hn (hL _ h)

variable (ir) in
/-- **Value `v`'s type contains the naturals by a listed node**, as a check: the field, or a
subfield type whose node, in the value's field, is in `L`. -/
def natTypedInB (L : List (ℕ × String)) (v : ℕ) : Bool :=
  match (ir.value v).type with
  | .field => true
  | .sub E => L.contains (ir.valueField v, E)
  | .bit => false

/-- **A value whose type is the field or a listed node's** has a type containing the naturals. -/
theorem natTyped_of_natTypedInB {L : List (ℕ × String)} (hL : OneNodes I L) {v : ℕ}
    (h : ir.natTypedInB L v = true) : ir.NatTyped I v := by
  unfold natTypedInB at h
  unfold NatTyped
  split at h
  · trivial
  · rw [List.contains_iff_mem] at h
    exact hL _ h
  · cases h

/-- **Every committed cell's node contains `1`** where each is a listed node (`HonestFacts.oneMem`). -/
theorem oneMem_of_cellNodeIn {L : List (ℕ × String)} (hL : OneNodes I L)
    (h : ∀ v < ir.values.length, ir.isCellValue (ir.value v).domain v = true →
      ir.cellNodeInB L v = true) :
    ∀ v < ir.values.length, ir.isCellValue (ir.value v).domain v = true → ir.oneMemB I v = true :=
  fun v hv hc => oneMemB_of_cellNodeInB hL (h v hv hc)

/-- **Every realization value typed by its node is a committed cell whose type contains the
naturals** where each is a committed cell of the field or a listed node's type
(`HonestFacts.realTypes`). -/
theorem realTypes_of_natTypedIn {L : List (ℕ × String)} (hL : OneNodes I L)
    (h : ∀ v < ir.values.length, (ir.value v).typeSource = .node → ¬ ir.IsLate v →
      ¬ ir.IsSourceValue v → ir.privCellB v = true ∧ ir.natTypedInB L v = true) :
    ∀ v < ir.values.length, (ir.value v).typeSource = .node → ¬ ir.IsLate v →
      ¬ ir.IsSourceValue v → ir.privCellB v = true ∧ ir.NatTyped I v := fun v hv hts hl hs => by
  obtain ⟨hp, ht⟩ := h v hv hts hl hs
  exact ⟨hp, natTyped_of_natTypedInB hL ht⟩

variable (ir primeNodes) in
/-- **The values' intervals the honest checks read**: `leafIvl` at the declared statement bounds, one
choice of justified intervals (`leafIvl_justified`). -/
abbrev srcLeafIvl : ℕ → ℕ → Option Ivl := fun f v => ir.leafIvl primeNodes f v ir.declaredRanges

variable (ir L) in
/-- **The interval of an expression in field `f` from the source values' intervals** (`ivlOf` at the
values' intervals `L` restricted to the source values of the program). -/
def srcIvl (f : ℕ) (e : Expr) : Option Ivl :=
  ir.ivlOf (ir.charOf f) (fun v => if v < ir.values.length ∧ ir.IsSourceValue v then
    L f v else none) e

variable (ir L) in
/-- **Predicate `rid` is the quotient's `in` of the one-digit `mod_q` `m`, whose honest quotient
lies in its range**, as a check: `m` is a source `mod_q` in the one-digit form with `q > 0` and
`p > 2`, its quotient derived from the sides (`quotDerivedB`), `rid` its quotient's direct `in`
`Q ∈ [0, N)` (`quotRangeB`), and by the sides' intervals from the source values (`srcIvl`,
`[l, h]` and `[l', h']`) the honest quotient `(e − e')/q − qlo` lies in `[0, N)`:
`h' − l + q · qlo < q` and `(h − l')/q − qlo < N`. -/
def oneDigitQuotAtB (m rid : ℕ) : Bool :=
  match (ir.predicate m).body with
  | .mod d q e e' real =>
    ir.inSource (ir.predicate m) && real.form == .oneDigit && decide (0 < q) &&
      decide (2 < ir.charOf (ir.domainField d)) && ir.quotDerivedB d q e e' real &&
      ir.quotRangeB d q e real rid &&
      match ir.srcIvl L (ir.domainField d) e, ir.srcIvl L (ir.domainField d) e',
        (ir.predicate rid).body with
      | some J, some J', .mem _ [_] (.range N) _ =>
        decide (J'.hi - J.lo + q * real.quotientLo < q) &&
          decide ((J.hi - J'.lo) / q - real.quotientLo < N)
      | _, _, _ => false
  | _ => false

variable (ir) in
/-- **Predicate `q` is the Boolean check of a pad copy**, as a check: `v · v = v` in a domain of
`v`'s field, `v` a pad copy that is a committed cell of its domain. -/
def padCopyBoolB (q : ℕ) : Bool :=
  match (ir.predicate q).body with
  | .equal d (.mul (.leaf a) (.leaf b)) (.leaf v) _ =>
    a == v && b == v && (ir.value v).kind.isPadCopy && decide (v < ir.values.length) &&
      decide ((ir.value v).domain < ir.domains.length) &&
      ir.isCellValue (ir.value v).domain v && decide (ir.domainField d = ir.valueField v)
  | _ => false

variable (ir) in
/-- **Predicate `q` is the field equation of a source `mod_q` in the field form**, as a check: the
row `e + (p − 1) e' = 0` of a source `mod_q` of sides `e`, `e'` whose realization has the field
form (`fieldRowB`). -/
def fieldRowRealB (q : ℕ) : Bool :=
  (ir.predicates.filter fun p => ir.inSource p &&
      match p.body with
      | .mod _ _ _ _ real => real.form == .field
      | _ => false).any fun p => ir.inSource p &&
    match p.body with
    | .mod d _ a b real => real.form == .field && ir.fieldRowB d a b (ir.predicateT q).body
    | _ => false

theorem fieldRowRealB_eq (q : ℕ) : ir.fieldRowRealB q = ir.predicates.any fun p => ir.inSource p &&
    match p.body with
    | .mod d _ a b real => real.form == .field && ir.fieldRowB d a b (ir.predicate q).body
    | _ => false := by
  unfold fieldRowRealB
  rw [predicateT_eq, any_filter_eq]
  intro p _ hp
  cases hs : ir.inSource p
  · rfl
  · rw [hs, Bool.true_and] at hp
    simp only [Bool.true_and]
    split
    · rename_i d q' a b real hb
      rw [hb] at hp
      simp only [beq_eq_false_iff_ne] at hp
      simp [hp]
    · rfl

/-- **A field `equal` row `e + (p − 1) e' = 0` holds exactly where `e = e'`** in the field
(`fieldRowB`): its right side is a constant `0` and `p − 1` is `−1`. -/
theorem holdsAt_fieldRow_iff (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) (e : ir.Env I) {d : ℕ} {a b : Expr} {body : PredBody}
    (hrow : ir.fieldRowB d a b body = true) :
    ir.HoldsAt e body ↔
      ∀ i < ir.exprLen a, ir.evalWith (ir.reader e) d a i = ir.evalWith (ir.reader e) d b i := by
  unfold fieldRowB at hrow
  split at hrow
  · rename_i d' e₁ c e₂ z tgt
    simp only [Bool.and_eq_true, beq_iff_eq] at hrow
    obtain ⟨⟨⟨⟨hd', h1⟩, h2⟩, hc⟩, hz⟩ := hrow
    subst d'
    rw [Expr.eq_of_beq h1, Expr.eq_of_beq h2]
    have hzc : ∃ es, (ir.value z).kind = .constant es ∧ ir.valueField z = ir.domainField d := by
      unfold constAll at hz
      split at hz
      · rename_i es hk
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hz
        exact ⟨es, hk, hz.2⟩
      · cases hz
    obtain ⟨es, hkz, hvz⟩ := hzc
    have hzl : z < ir.values.length := by
      by_contra hzl
      rw [value_eq_default (Nat.le_of_not_lt hzl)] at hkz
      cases hkz
    have hdF : ir.domainField d < ir.fields.length := hvz ▸ valueField_lt hwf hzl
    have := charP_field hI hdF
    have hcl : c < (ir.field (ir.domainField d)).characteristic := by
      have hc' : c + 1 = (ir.field (ir.domainField d)).characteristic := hc
      omega
    have hc1 : ((c : ℕ) : (I (ir.domainField d)).K) = -1 := by
      have h0 : ((c + 1 : ℕ) : (I (ir.domainField d)).K) = 0 := by
        rw [hc]
        exact CharP.cast_eq_zero _ _
      push_cast at h0
      linear_combination h0
    have hrd : ∀ i < ir.exprLen a, ir.evalWith (ir.reader e) d
        (.add a (.scale (.const c) b)) i - ir.evalWith (ir.reader e) d (.leaf z) i =
          ir.evalWith (ir.reader e) d a i - ir.evalWith (ir.reader e) d b i := fun i hi => by
      have hzi := evalE_leaf_constAll_of hL (rd := ir.reader e)
        (fun v es hk i => reader_of_constant e hk i) hz hdF (by omega) hi
      simp only [evalWith, evalE_add, evalE_scale_const]
      rw [hzi, Nat.cast_zero, hL.decode_natCast _ hdF c hcl, hc1]
      ring
    change (∀ i < ir.exprLen a, _ = _) ↔ _
    exact forall₂_congr fun i hi => by rw [← sub_eq_zero, hrd i hi, sub_eq_zero]
  · cases hrow

/-- **The field equation of a source field-form `mod_q` holds** where the source field-form
`mod_q`s hold as their field equations (`FieldEqsAt`, `holdsAt_fieldRow_iff`). -/
theorem holds_fieldRow (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {e : ir.Env I} (hE : ir.FieldEqsAt I e) {q : ℕ} (h : ir.fieldRowRealB q = true) :
    ir.HoldsAt e (ir.predicate q).body := by
  rw [fieldRowRealB_eq] at h
  obtain ⟨p, hp, hpq⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true] at hpq
  obtain ⟨hsrc, hpq⟩ := hpq
  split at hpq
  · rename_i d q' a b real hb
    simp only [Bool.and_eq_true, beq_iff_eq] at hpq
    exact (holdsAt_fieldRow_iff hwf hI hL e hpq.2).2 (hE p hp hsrc d q' a b real hb hpq.1)
  · cases hpq

variable (ir) in
/-- **Every source `mod_q` in the field form has its field equation as a row of the program**, as
a check (`fieldRowB`; the realization's `FieldFormOk.row`). -/
def fieldRowsB : Bool :=
  ir.predicates.all fun p => !ir.inSource p ||
    match p.body with
    | .mod d _ a b real => !(real.form == .field) || ir.predicates.any fun r => ir.fieldRowB d a b r.body
    | _ => true

/-- **The source field-form `mod_q`s hold as their field equations where their rows hold**
(`fieldRowsB`, `holdsAt_fieldRow_iff`). -/
theorem fieldEqsAt_of_rows (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) (hB : ir.fieldRowsB = true) {e : ir.Env I}
    (hH : ∀ r < ir.predicates.length, ir.fieldRowRealB r = true → ir.HoldsAt e (ir.predicate r).body) :
    ir.FieldEqsAt I e := by
  intro p hp hsrc d q a b real hb hform
  have hp' := List.all_eq_true.1 hB p hp
  rw [hsrc, hb] at hp'
  simp only [Bool.not_true, Bool.false_or, hform, beq_self_eq_true] at hp'
  obtain ⟨r, hr, hrow⟩ := List.any_eq_true.1 hp'
  obtain ⟨k, hk, rfl⟩ := exists_index_of_mem hr
  have hreal : ir.fieldRowRealB k = true := by
    rw [fieldRowRealB_eq]
    exact List.any_eq_true.2 ⟨p, hp, by rw [hsrc, hb]; simp [hform, hrow]⟩
  exact (holdsAt_fieldRow_iff hwf hI hL e hrow).1 (hH k hk hreal)

/-- **The value a quadratic root equation is on** (`quadRootView`'s `v₁`), read off the equation. -/
def quadVar? (pr : Predicate) : Option ℕ :=
  match pr.body with
  | .equal _ (.mul (.add (.leaf _) (.scale (.const _) (.leaf v₁))) _) (.leaf _) _ => some v₁
  | _ => none

theorem quadVar?_of_quadRootView {v : ℕ} {pr : Predicate}
    (h : (ir.quadRootView v pr).isSome = true) : quadVar? pr = some v := by
  unfold quadRootView at h
  split at h
  · next hb =>
    split at h
    · split_ifs at h with hc
      · simp only [quadVar?, hb]
        exact congrArg some hc.1
      · simp at h
    · simp at h
  · simp at h

variable (ir) in
/-- **The value a root-set equation is on** (`rootSetView`'s first reading of the root product),
read off the equation. -/
def rootSetVar? (pr : Predicate) : Option ℕ :=
  match pr.body with
  | .equal d lhs (.leaf _) _ => (ir.rootsAt (ir.domainField d) rootFuel ir.exprs.length 0 lhs).map (·.1)
  | _ => none

theorem rootSetVar?_of_rootSetView {v : ℕ} {pr : Predicate}
    (h : (ir.rootSetView v pr).isSome = true) : ir.rootSetVar? pr = some v := by
  unfold rootSetView at h
  split at h
  · rename_i d lhs z t hb
    split_ifs at h with hc
    · rw [rootSetVar?, hb]
      exact hc.1
    · simp at h
  · simp at h

/-- **A value with a root interval in an equation** is the equation's quadratic or root-set
value. -/
theorem mem_rootVars {v : ℕ} {pr : Predicate} (h : ir.rootEqB v pr = true) :
    v ∈ (quadVar? pr).toList ++ (ir.rootSetVar? pr).toList := by
  unfold rootEqB at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · simp [quadVar?_of_quadRootView (ir := ir) h]
  · simp [rootSetVar?_of_rootSetView (ir := ir) h]

variable (ir) in
/-- **The values whose type predicate is each predicate**: key `q` holds the values `v` with
`typeSource = .pred q`. -/
def typePredTab : NatTrie (List ℕ) :=
  ir.values.zipIdx.foldl (fun t xv =>
    match xv.1.typeSource with
    | .pred q => t.set q (xv.2 :: t.getD q [])
    | _ => t) .nil

theorem mem_foldl_typePred : ∀ (L : List (Value × ℕ)) (t : NatTrie (List ℕ)) (q v : ℕ),
    v ∈ (L.foldl (fun t xv =>
      match xv.1.typeSource with
      | .pred q => t.set q (xv.2 :: t.getD q [])
      | _ => t) t).getD q [] ↔
      v ∈ t.getD q [] ∨ ∃ x, (x, v) ∈ L ∧ x.typeSource = .pred q
  | [], t, q, v => by simp
  | (x, w) :: L, t, q, v => by
    rw [List.foldl_cons, mem_foldl_typePred L]
    cases hx : x.typeSource with
    | pred q' =>
      simp only [hx, NatTrie.getD_set]
      by_cases hq : q = q'
      · subst hq
        simp only [if_true, List.mem_cons, List.mem_cons, Prod.mk.injEq]
        constructor
        · rintro ((rfl | h) | ⟨y, hy, hy'⟩)
          · exact .inr ⟨x, .inl ⟨rfl, rfl⟩, hx⟩
          · exact .inl h
          · exact .inr ⟨y, .inr hy, hy'⟩
        · rintro (h | ⟨y, (⟨rfl, rfl⟩ | hy), hy'⟩)
          · exact .inl (.inr h)
          · exact .inl (.inl rfl)
          · exact .inr ⟨y, hy, hy'⟩
      · simp only [hq, if_false, List.mem_cons, Prod.mk.injEq]
        constructor
        · rintro (h | ⟨y, hy, hy'⟩)
          · exact .inl h
          · exact .inr ⟨y, .inr hy, hy'⟩
        · rintro (h | ⟨y, (⟨rfl, rfl⟩ | hy), hy'⟩)
          · exact .inl h
          · rw [hx] at hy'
            cases hy'
            exact absurd rfl hq
          · exact .inr ⟨y, hy, hy'⟩
    | node =>
      simp only [hx, List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro (h | ⟨y, hy, hy'⟩)
        · exact .inl h
        · exact .inr ⟨y, .inr hy, hy'⟩
      · rintro (h | ⟨y, (⟨rfl, rfl⟩ | hy), hy'⟩)
        · exact .inl h
        · rw [hx] at hy'
          cases hy'
        · exact .inr ⟨y, hy, hy'⟩
    | none =>
      simp only [hx, List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro (h | ⟨y, hy, hy'⟩)
        · exact .inl h
        · exact .inr ⟨y, .inr hy, hy'⟩
      · rintro (h | ⟨y, (⟨rfl, rfl⟩ | hy), hy'⟩)
        · exact .inl h
        · rw [hx] at hy'
          cases hy'
        · exact .inr ⟨y, hy, hy'⟩

/-- **A value whose type predicate is `q`** is listed at key `q` of `typePredTab`. -/
theorem mem_typePredTab {v q : ℕ} (hv : v < ir.values.length)
    (h : (ir.value v).typeSource = .pred q) : v ∈ ir.typePredTab.getD q [] := by
  unfold typePredTab
  rw [mem_foldl_typePred]
  refine .inr ⟨ir.value v, ?_, h⟩
  rw [List.mem_zipIdx_iff_getElem?]
  simp only [Nat.sub_zero]
  rw [value, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hv]
  rfl

variable (ir) in
/-- **The predicates the source values' intervals read are source predicates**, at predicate `q`,
as a check: a source predicate; or a direct, digit or two-sided `in` on no source value or on no
source value plus a value; or a field `equal` that is the type predicate or a root equation
(`rootEqB`) of no source value. -/
def ivlSourceB (q : ℕ) : Bool :=
  ir.inSource (ir.predicateT q) ||
    match (ir.predicateT q).body with
    | .mem _ [rec] _ (.lookup r) =>
      !(r.kind == .direct || r.kind == .digits || r.kind == .twoSided) ||
        match rec with
        | .leaf v => !decide (ir.IsSourceValue v)
        | .add (.leaf v) (.leaf _) => !decide (ir.IsSourceValue v)
        | _ => true
    | .equal .. =>
      ((quadVar? (ir.predicateT q)).toList ++ (ir.rootSetVar? (ir.predicateT q)).toList ++
          ir.typePredTab.getD q []).all fun v =>
        !(decide (v < ir.values.length) && decide (ir.IsSourceValue v) &&
          (ir.rootEqB v (ir.predicateT q) || (ir.value v).typeSource == .pred q))
    | _ => true

/-- **A field `equal` that is the type predicate or a root equation of a source value is a source
predicate** (`ivlSourceB`). -/
theorem inSource_of_ivlSourceB_equal {q v : ℕ} (h : ir.ivlSourceB q = true)
    (he : (ir.predicate q).body.isEqual = true) (hv : v < ir.values.length)
    (hsrc : ir.IsSourceValue v)
    (hr : ir.rootEqB v (ir.predicate q) = true ∨ (ir.value v).typeSource = .pred q) :
    ir.inSource (ir.predicate q) = true := by
  unfold ivlSourceB at h
  simp only [predicateT_eq] at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · exact h
  exfalso
  obtain ⟨d, L, R', t, hb⟩ : ∃ d L R t, (ir.predicate q).body = .equal d L R t := by
    revert he
    cases (ir.predicate q).body <;> simp [PredBody.isEqual]
  rw [hb] at h
  have hmem : v ∈ (quadVar? (ir.predicate q)).toList ++ (ir.rootSetVar? (ir.predicate q)).toList ++
      ir.typePredTab.getD q [] := by
    rcases hr with hr | hr
    · exact List.mem_append_left _ (mem_rootVars hr)
    · exact List.mem_append_right _ (mem_typePredTab hv hr)
  have := List.all_eq_true.1 h v hmem
  rcases hr with hr | hr <;> simp [hsrc, hr, hv] at this

/-- **A direct, digit or two-sided `in` on a source value, or on it plus a value, is a source
predicate** (`ivlSourceB`). -/
theorem inSource_of_ivlSourceB_lookup {q v d : ℕ} {rec : Expr} {set : InSet}
    {r : LookupRealization} (h : ir.ivlSourceB q = true)
    (hb : (ir.predicate q).body = .mem d [rec] set (.lookup r))
    (hk : r.kind = .direct ∨ r.kind = .digits ∨ r.kind = .twoSided)
    (hrec : rec = .leaf v ∨ ∃ c, rec = .add (.leaf v) (.leaf c)) (hsrc : ir.IsSourceValue v) :
    ir.inSource (ir.predicate q) = true := by
  unfold ivlSourceB at h
  simp only [predicateT_eq] at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · exact h
  exfalso
  rw [hb] at h
  have hk' : (r.kind == .direct || r.kind == .digits || r.kind == .twoSided) = true := by
    rcases hk with hk | hk | hk <;> simp [hk]
  simp only [hk', Bool.not_true, Bool.false_or] at h
  rcases hrec with rfl | ⟨c, rfl⟩ <;> simp [hsrc] at h

/-! ## The source environment of the honest committed values -/

/-- **No value past the program's values is bound to its digits.** -/
theorem isBound_eq_false_of_le {v : ℕ} (hv : ir.values.length ≤ v) :
    (ir.value v).kind.isBound = false := by
  rw [value_eq_default hv]
  rfl

/-- **A value bound to its digits is a value of the program.** -/
theorem lt_of_isBound {v : ℕ} (h : (ir.value v).kind.isBound = true) : v < ir.values.length := by
  by_contra hv
  rw [isBound_eq_false_of_le (Nat.le_of_not_lt hv)] at h
  cases h

variable {Inp : Type} {relH : Set (ir.Valuation I × Inp)}

/-- **The honest assignment reads a checked committed value** below its size as the committed
values. -/
theorem honestAsg_val_of_privCellB {val : ir.Valuation I} {π : (ir.layout I).Pads} {u i : ℕ}
    (h : ir.privCellB u = true) (hi : i < (ir.value u).size) :
    (ir.honestAsg I val π).val u i = val u i := by
  have hk := kind_of_privCellB h
  unfold privCellB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rw [honestAsg_val h.1.2 ((ir.mem_cellKeys_val).2 ⟨h.1.1.2, h.2, hi⟩)]
  simp only [copyVal, hk]

/-- **The honest assignment reads `0` past a checked committed value's size.** -/
theorem honestAsg_val_of_privCellB_of_le {val : ir.Valuation I} {π : (ir.layout I).Pads} {u i : ℕ}
    (h : ir.privCellB u = true) (hi : (ir.value u).size ≤ i) :
    (ir.honestAsg I val π).val u i = 0 := by
  have hk := kind_of_privCellB h
  rw [honestAsg_val_eq_ite fun w m h' => by rw [hk] at h'; cases h']
  simp only
  rw [if_neg fun hc => absurd ((ir.mem_cellKeys_val).1 hc.2).2.2 (by omega)]

/-- **The committed reader reads a committed value from the committed values.** -/
theorem committedRead_of_priv (a : ir.Assignment I) {u : ℕ} (hk : (ir.value u).kind = .priv) :
    ir.committedRead a u = a.val u := by
  funext i
  simp only [committedRead, hk]

/-- **A value bound to its digits reads alike at every pad vector** of the honest assignment: its
expression reads no pad copy (`BoundNoCopy`). -/
theorem bindAsg_bound_pads (hbc : ir.BoundNoCopy) (V : ir.Valuation I) (π π' : (ir.layout I).Pads)
    {v : ℕ} {e : Expr} (hk : (ir.value v).kind = .bound e) :
    (ir.bindAsg (ir.honestAsg I V π)).val v = (ir.bindAsg (ir.honestAsg I V π')).val v := by
  funext i
  simp only [bindAsg, hk]
  refine congrFun (evalE_congr fun w hw => funext fun j => ?_) i
  simp only [committedRead]
  split
  · rfl
  · rw [honestAsg_val_congr_of_not V π π' (hbc v e hk w hw)]

variable (I) in
/-- **The phase-`0` values of an execution read off honest committed values** `V`: `V` at every
value not bound to its digits, and a value bound to them as their number in `V` (`bindAsg`, at the
zero pads; a bound value reads no pad copy). The family proofs state the source program at the
source environment of `V`; the execution's phase-`0` values are these. -/
def execOf (V : ir.Valuation I) : ir.Valuation I := fun v i =>
  if (ir.value v).kind.isBound then (ir.bindAsg (ir.honestAsg I V 0)).val v i else V v i

/-- **A source environment agrees with the environment of an execution on the source values**
where its source late values are the execution's (`hLl`), its committed values are the phase-`0`
values at the source values (`hV`), no source value is a pad copy, and the values bound to their
digits read the phase-`0` values (`hbnd`): a source value reads its phase-`0` value at its cells in
both. -/
theorem agreeOnSourceVals_srcEnv_of {x V L s l : ir.Valuation I} (c : ∀ k, (ir.layout I).Ch k)
    (π : (ir.layout I).Pads)
    (hLl : ∀ u, ir.IsSourceValue u → ir.IsLate u → ∀ i < (ir.value u).size, L u i = l u i)
    (hpc : ∀ u < ir.values.length, ir.IsSourceValue u → (ir.value u).kind.isPadCopy = false)
    (hbnd : ∀ u, ir.IsSourceValue u → (ir.value u).kind.isBound = true →
      (ir.bindAsg (ir.honestAsg I V π)).val u = fun i => if i < (ir.value u).size then s u i else 0)
    (hV : ∀ u, ir.IsSourceValue u → (ir.value u).kind.isBound = false → V u = s u) :
    Env.AgreeOnSourceVals (ir.srcEnvL I x V L c π) (ir.execEnv I x s l c) where
  stmt := rfl
  chal _ _ := rfl
  late u hu := by
    funext i
    show ir.srcLateOf I L u i =
      if u < ir.values.length ∧ ir.IsLate u ∧ i < (ir.value u).size then l u i else 0
    unfold srcLateOf
    by_cases h : ir.IsLate u ∧ i < (ir.value u).size
    · rw [if_pos ⟨hu, h⟩, if_pos ⟨lt_of_isLate h.1, h⟩, hLl u hu h.1 i h.2]
    · rw [if_neg fun h' => h h'.2, if_neg fun h' => h h'.2]
  val u hu := by
    rcases hb : (ir.value u).kind.isBound
    · have hpc' : ∀ w m, (ir.value u).kind ≠ .padCopy w m := fun w m hk => by
        by_cases hlt : u < ir.values.length
        · have := hpc u hlt hu
          rw [hk] at this
          cases this
        · rw [value_eq_default (Nat.le_of_not_lt hlt)] at hk
          cases hk
      change (ir.bindAsg (ir.honestAsg I V π)).val u = _
      rw [ir.bindAsg_val_of_isBound _ hb, honestAsg_val_eq_ite hpc', hV u hu hb,
        execEnv_asg_val_of_not_bound x s l c hb]
    · change (ir.bindAsg (ir.honestAsg I V π)).val u = _
      rw [hbnd u hu hb, execEnv_asg_val_of_isBound x s l c hb]

/-- **A cast of an integer is the cast of its integer reading** in a field of positive
characteristic `p` whose integer readings are lawful: it is the cast of a natural below `p`. -/
theorem natCast_toNat_of_intCast (hL : I.Lawful ir primeNodes) {f : ℕ}
    (hf : f < ir.fields.length) (hp : 0 < ir.charOf f) (hchar : CharP (I f).K (ir.charOf f))
    {y : (I f).K} (hy : y ∈ (Int.castRingHom (I f).K).range) :
    (((I f).toNat y : ℕ) : (I f).K) = y := by
  obtain ⟨z, rfl⟩ := hy
  set p := ir.charOf f
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have hnn : 0 ≤ z % p := Int.emod_nonneg z (by omega)
  have hlt : z % p < p := Int.emod_lt_of_pos z hp'
  have hcast : ((z : ℤ) : (I f).K) = (((z % p).toNat : ℕ) : (I f).K) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn, ← sub_eq_zero, ← Int.cast_sub,
      CharP.intCast_eq_zero_iff (I f).K p]
    exact ⟨z / p, by rw [Int.emod_def]; ring⟩
  have hn : (z % p).toNat < p := by
    have := Int.toNat_of_nonneg hnn
    omega
  rw [eq_intCast, hcast, hL.toNat_natCast f hf _ hn]

section SrcEnv

variable (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
  {x s l : ir.Valuation I} {c : ∀ k, (ir.layout I).Ch k}
  (hA : ir.SourceAcceptingAt I (ir.execEnv I x s l c)) (π : (ir.layout I).Pads)

/-! ## The realization's obligations at the source environment -/

/-- **The Boolean check of a pad copy holds at the source environment** of the honest committed
values (`padCopyBoolB`): the pad copy reads `0` or `1` (`reader_srcEnv_padCopy`). -/
theorem holds_padCopyBool_srcEnv (x val L : ir.Valuation I) (c : ∀ k, (ir.layout I).Ch k)
    (π : (ir.layout I).Pads) {q : ℕ} (h : ir.padCopyBoolB q = true) :
    ir.HoldsWith (ir.reader (ir.srcEnvL I x val L c π)) (ir.predicate q).body := by
  unfold padCopyBoolB at h
  split at h
  · rename_i d a b v t hbody
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, hpc⟩, hv⟩, hd⟩, hc⟩, hf⟩ := h
    rw [hbody]
    intro i hi
    simp only [exprLen, Expr.len] at hi
    obtain ⟨w, m, hk⟩ : ∃ w m, (ir.value b).kind = .padCopy w m := by
      revert hpc
      cases (ir.value b).kind <;> simp [Kind.isPadCopy]
    rw [evalWith, evalE_mul, evalE_leaf, evalWith, evalE_leaf,
      reader_srcEnvL_padCopy x val L c π hk hd ((ir.mem_cellKeys_val).2 ⟨hv, hc, hi⟩)]
    cases I.padCopyBit m (ir.padsOf I π w 0) i <;>
      simp [FieldInterp.ofBool, castElt_one_of_eq hf.symm]
  · cases h

/-! ## The committed digits at the source environment -/

/-- **The honest quotient of a committed-digits `mod_q`** at the source environment of the honest
committed values where the execution accepts: it lies below `R^K`, and the sides satisfy
`e − e' = q·qlo + q·Q` in the field. -/
structure CommQuotSpec (rd : ir.Valuation I) (d q : ℕ) (e e' : Expr) (real : ModRealization)
    (i Q : ℕ) : Prop where
  /-- The quotient lies below `R^K`. -/
  lt : Q < real.radix ^ real.digits.length
  /-- The sides' difference is `q·qlo + q·Q`. -/
  sides : ir.evalWith rd d e i - ir.evalWith rd d e' i =
    (((q : ℤ) * real.quotientLo : ℤ) : (I (ir.domainField d)).K) +
      ((q * Q : ℕ) : (I (ir.domainField d)).K)

end SrcEnv

/-! ## The honest strategy -/

/-- **The source program's late values of an execution**, in their pad spaces (`padSpaceLate`). -/
def SourceExecutionCore.srcLate (E : ir.SourceExecutionCore I relH) : ir.SrcLate I Inp where
  late y c := ir.padSpaceLate I (E.late y c)
  mem y c l _ i := padSpaceLate_mem (E.late y c) l.1 i
  respects y v hs hl c c' h := by
    funext i
    simp only [padSpaceLate, E.respects y v hs hl c c' h]

open Classical in
/-- **The completeness error `errc` of an execution over the prover's coins**
(`HonestCore.CoinComplete` at the execution's events): for honest inputs `J` related to statements
by `relJ`, read with uniform coins `ω` as the inputs `inp y ω`, on `relJ`, over uniform coins and
challenges, the input with its coins is off the relation or the challenges meet some completeness
event with probability at most `errc`. -/
def SourceExecutionCore.CoinComplete (E : ir.SourceExecutionCore I relH) {J Ω : Type} [Fintype Ω]
    [Nonempty Ω] (relJ : Set (ir.Valuation I × J)) (inp : J → Ω → Inp)
    (errc : ir.Valuation I → ℝ≥0) : Prop :=
  ∀ x y, (x, y) ∈ relJ → Pr[u ← (Ω × ∀ k, (ir.layout I).Ch k) :
    (x, inp y u.1) ∉ relH ∨ ∃ k, E.bad k x (inp y u.1) u.2] ≤ errc x

/-! ## The accepting execution from the source program's predicates -/

variable (ir) in
/-- **Value `v` has a Boolean check**, as a check: its type is `Bit`, enforced by a source
predicate `v · v = v` in a domain of its field. -/
def boolCheckB (v : ℕ) : Bool :=
  match (ir.value v).typeSource with
  | .pred q =>
    decide (q < ir.predicates.length) && (ir.value v).type == .bit &&
      ir.inSource (ir.predicate q) &&
      match (ir.predicate q).body with
      | .equal d (.mul (.leaf a) (.leaf b)) (.leaf c) _ =>
        a == v && b == v && c == v && decide (ir.domainField d = ir.valueField v)
      | _ => false
  | _ => false

variable (ir) in
/-- **Every `kpriv` source value whose type no node states has a checked type**: type `Field`, a
Boolean check (`boolCheckB`), or bound to its digits with a type other than `Bit`. -/
def KprivTyped : Prop :=
  ∀ v < ir.values.length, ir.IsSourceValue v → (ir.value v).kind.isKpriv = true →
    (ir.value v).typeSource ≠ .node →
      (ir.value v).type = .field ∨ ir.boolCheckB v = true ∨
        ((ir.value v).kind.isBound = true ∧ (ir.value v).type ≠ .bit)

instance : Decidable ir.KprivTyped := by
  unfold KprivTyped
  exact Nat.decidableBallLT _ _

variable (ir I) in
/-- **The subfield type of every bound value contains `1`.** -/
def BoundOneMem : Prop :=
  ∀ v < ir.values.length, (ir.value v).kind.isBound = true → ∀ E,
    (ir.value v).type = .sub E → (1 : (I (ir.valueField v)).K) ∈ (I (ir.valueField v)).node E

/-- **The bound values' subfield types contain `1`** where each bound value's type is the field
or a listed node's (`natTypedInB`). -/
theorem boundOneMem_of_natTypedIn {L : List (ℕ × String)} (hL : OneNodes I L)
    (h : ∀ v < ir.values.length, (ir.value v).kind.isBound = true → ir.natTypedInB L v = true) :
    ir.BoundOneMem I := fun v hv hb E hE => by
  have h' := h v hv hb
  unfold natTypedInB at h'
  rw [hE, List.contains_iff_mem] at h'
  exact hL _ h'

/-- **A field element equal to its square is `0` or `1`.** -/
theorem eq_zero_or_one_of_mul_self {K : Type} [Field K] {a : K} (h : a * a = a) : a = 0 ∨ a = 1 := by
  have : a * (a - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.1 this with h0 | h1
  · exact .inl h0
  · exact .inr (sub_eq_zero.1 h1)

end

end GordieHowe.RealizedProgram
