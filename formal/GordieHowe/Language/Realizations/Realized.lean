-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Protocol
public import GordieHowe.Language.Realizations.MAC
public import GordieHowe.Language.Realizations.CommittedLookup

@[expose] public section

/-!
# GordieHowe: the realized semantics of the plan's program

The realization step of the plan-level theorem (phase 3, stage A) lowers the program's predicates
(`GordieHowe.RealizedProgram.Pred`, `GordieHowe/Language/RealizedProgram/Semantics.lean`) to the constraint the proof system enforces, on
the same committed assignment. This file states that constraint and its events.

* **Group membership** (`Member`, `GordieHowe.RealizedProgram.members`): each table group's LogUp sum reads the
  coordinates `[first, first + count)` of needle `needle` of the `in` predicate `pred`, its members
  in sum order (`TableGroup.members`).
* **The LogUp identity of a group** (`GordieHowe.RealizedProgram.LogupHolds`, `GordieHowe.RealizedProgram.logupAt`): for a range table
  `[0, T)`, `Range.rangeArgument` on the group's needles (`GordieHowe.RealizedProgram.groupNeedles`), its static
  histogram and its late histogram (`GordieHowe.RealizedProgram.histRead`), at the verifier's weights `(α − j)⁻¹`
  (`Range.logupTcoef`); for any other table, whose rows are the coordinates of a value or of an
  expression (`GordieHowe.RealizedProgram.tableRow`), the identity with its denominators cleared (`Range.committedArgument`),
  its counts the two histograms' sum. `α` is the table's challenge (`GordieHowe.RealizedProgram.alphaOf`). Every value
  is read in `α`'s field.
* **The realized semantics** (`GordieHowe.RealizedProgram.RealizedAt`): every field `equal` holds (source and
  realization rows, type checks), every `mod_0` has its field equation `e = e'` (the integer
  equality follows from the sides' intervals, `GordieHowe/Language/Realizations/RealizeInteger.lean`), every
  group's LogUp identity holds, every node-typed value lies in its type, and the H half of every
  hosted cross-field `equal` the compiler states by its own circuit holds (`GordieHowe.RealizedProgram.MacHHoldsAt`: the tag
  is `Σ_c β^(c+1) · chunk_c(X_H)`). A `mod_q` in the one-digit or the digit form needs no field: its
  quotient (top digit) is derived from the sides, so its field equation holds at every reader, and
  its ranges are `in`s of the program. `GordieHowe.RealizedProgram.Realized` is the constraint of the layout, at the
  realized assignment (`GordieHowe.RealizedProgram.bindAsg`: a value bound to its digits read through them).
* **The events** (`GordieHowe.RealizedProgram.RealEvent`): at a table's challenge `α`, `α` is a root of the lookup
  polynomial of one of the table's groups (`GordieHowe.RealizedProgram.LookupEvent`, `Range.lookupEvent`,
  `Range.committedEvent`); at a MAC's
  key, the key is a root of the MAC's binding polynomial (`GordieHowe.RealizedProgram.MacEvent`, `GordieHowe.RealizedProgram.macEvent`:
  the H operand's chunks and the tag's pad against the A operand's chunks and the blind where the
  `x` domain hosts the MAC; the two operands' chunks and their blinds where no domain hosts it).
  Their error at challenge `j` is `GordieHowe.RealizedProgram.realError`, a sum over the groups at `j` of
  `(N_g + T − 1)/(|F| − tmax)` and over the MACs keyed by `j` of `chunks/(|F| − tmax)`
  (`GordieHowe.RealizedProgram.realErrorTerms`).
* **Sampled environments** (`GordieHowe.RealizedProgram.Env.Sampled`): every challenge coordinate is a value of its
  sampler, as in the layout's environments (`GordieHowe.RealizedProgram.layoutEnv_sampled`); the lookup challenge then
  avoids the table values by its type (`Range.LookupChallenge`).
-/

namespace GordieHowe.RealizedProgram

open Export Range IOP
open scoped NNReal

/-! ## Group membership -/

/-- **A member of a table group's LogUp sum**: `(pred, needle, first, count)`, the coordinates
`[first, first + count)` of needle `needle` (an index into the `in` predicate's needles) of the `in`
predicate `pred` (`TableGroup.members`). -/
abbrev Member : Type := ℕ × ℕ × ℕ × ℕ

namespace Member

/-- The `in` predicate of a member. -/
def pred (m : Member) : ℕ := m.1

/-- The needle of a member, an index into its predicate's needles. -/
def needle (m : Member) : ℕ := m.2.1

/-- The first coordinate of a member. -/
def first (m : Member) : ℕ := m.2.2.1

/-- The number of coordinates of a member. -/
def count (m : Member) : ℕ := m.2.2.2

end Member

section

variable (ir : RealizedProgram)

/-! ## The data of a lookup -/

/-- **The lookup realization of a predicate body**: an `in` realized by lookups. -/
def lookupOf? : PredBody → Option LookupRealization
  | .mem _ _ _ (.lookup r) => some r
  | _ => none

/-- **Needle `n` of predicate `p`**, an expression of its lookup realization (a default expression
when `p` has none). -/
def needleExpr (p n : ℕ) : Expr :=
  ((lookupOf? (ir.predicate p).body).map fun r => r.needles.getD n default).getD default

/-- **The size `T` of table `t`**: the range `[0, T)`, the size of a committed table's first
column (the one a single-record `in` reads, `RealizedProgram.InRows`), or the length of the expression whose
coordinates are the rows. -/
def tableSize (t : ℕ) : ℕ :=
  match (ir.table t).rows with
  | .range T => T
  | .columns cols => (ir.value (cols.headD 0)).size
  | .expr e' => ir.exprLen e'

/-- **The challenge `α` of table `t`.** -/
def alphaOf (t : ℕ) : ℕ := (ir.table t).alpha

/-- **Group `g` of table `t`.** -/
def groupOf (t g : ℕ) : TableGroup := (ir.table t).groups.getD g default

/-- **The members of group `g` of table `t`**, in the order its LogUp sum reads them. -/
def members (t g : ℕ) : List Member := (ir.groupOf t g).members

/-- **The number of needles of group `g` of table `t`**: the coordinates of its members. -/
def groupCount (t g : ℕ) : ℕ := ((ir.members t g).map Member.count).sum

/-- **The number of groups of table `t`.** -/
def groupCountOf (t : ℕ) : ℕ := (ir.table t).groups.length

/-- **The largest table challenge `j` avoids**: `tmax` for the sampler `fieldMinusTables (range
tmax)`, `0` otherwise. -/
def tmaxOf (j : ℕ) : ℕ :=
  match (ir.challenge j).sampler with
  | .fieldMinusTables (.range T) => T
  | _ => 0

variable {I : Interp}

/-- **The coordinates of a member** in field `f`, reading values by `rd`: coordinates
`first, …, first + count − 1` of its needle. -/
def memberVals (rd : ir.Valuation I) (f : ℕ) (m : Member) : List (I f).K :=
  (List.range m.count).map fun c => ir.evalE rd f (ir.needleExpr m.pred m.needle) (m.first + c)

/-- **The needles of group `g` of table `t`** in field `f`, reading values by `rd`: its members'
coordinates in sum order. -/
def groupNeedles (rd : ir.Valuation I) (f t g : ℕ) : List (I f).K :=
  (ir.members t g).flatMap (ir.memberVals rd f)

variable {ir} in
/-- **A group has its members' coordinates as needles.** -/
theorem length_groupNeedles (rd : ir.Valuation I) (f t g : ℕ) :
    (ir.groupNeedles rd f t g).length = ir.groupCount t g := by
  simp only [groupNeedles, groupCount, List.length_flatMap, memberVals,
    List.length_map, List.length_range]

/-- **A histogram on `[0, T)`** in field `f`, reading values by `rd`: entry `j` is coordinate `j`
of the value `v` below its size, `0` past it or without a value. -/
def histRead (rd : ir.Valuation I) (f T : ℕ) : Option ℕ → Fin T → (I f).K
  | none, _ => 0
  | some v, j => if (j : ℕ) < (ir.value v).size then castElt (rd v j) else 0

/-- **The static histogram of group `g` of table `t`** in field `f`. -/
def staticHist (rd : ir.Valuation I) (f t g : ℕ) : Fin (ir.tableSize t) → (I f).K :=
  ir.histRead rd f (ir.tableSize t) (ir.groupOf t g).staticMult

/-- **The late histogram of group `g` of table `t`** in field `f`. -/
def lateHist (rd : ir.Valuation I) (f t g : ℕ) : Fin (ir.tableSize t) → (I f).K :=
  ir.histRead rd f (ir.tableSize t) (ir.groupOf t g).lateMult

/-- **Row `j` of table `t`** in field `f`, reading values by `rd`: `j` for a range; coordinate `j`
of the first column for a committed table; coordinate `j` of the expression for a table of an
expression's coordinates. -/
def tableRow (rd : ir.Valuation I) (f t : ℕ) (j : Fin (ir.tableSize t)) : (I f).K :=
  match (ir.table t).rows with
  | .range _ => (j : (I f).K)
  | .columns cols => castElt (rd (cols.headD 0) j)
  | .expr e' => ir.evalE rd f e' j

/-- **The lookup polynomial of group `g` of table `t`** in field `f`, from its needles, its rows and
its histograms read by `rd`: for a range, the range argument's (`Range.lookupEvent`); for any
other table, the cleared identity's (`Range.committedEvent`), its counts the static plus the late
histogram (`Range.combined`). -/
noncomputable def groupEvent (rd : ir.Valuation I) (f t g : ℕ) :
    ChallengeEvent (I f).K :=
  match (ir.table t).rows with
  | .range _ => lookupEvent (ir.groupNeedles rd f t g) (ir.staticHist rd f t g) (ir.lateHist rd f t g)
  | .columns _ => committedEvent (ir.groupNeedles rd f t g) (ir.tableRow rd f t)
      (combined (ir.staticHist rd f t g) (ir.lateHist rd f t g))
  | .expr _ => committedEvent (ir.groupNeedles rd f t g) (ir.tableRow rd f t)
      (combined (ir.staticHist rd f t g) (ir.lateHist rd f t g))

/-- **A group's lookup polynomial has degree at most `N_g + T − 1`**, for a range or a committed
table. -/
theorem groupEvent_deg (rd : ir.Valuation I) (f t g : ℕ) :
    (ir.groupEvent rd f t g).deg = ir.groupCount t g + ir.tableSize t - 1 := by
  have hl := length_groupNeedles rd f t g
  unfold groupEvent
  split <;> simp [lookupEvent, committedEvent, hl]

/-- **The LogUp identity of group `g` of table `t`** at `α`, reading values by `rd`, every value read
in `α`'s field: for a range, the range argument at the verifier's weights `(α − j)⁻¹`
(`Range.rangeArgument`, `Range.logupTcoef`); for any other table, the identity with its
denominators cleared (`Range.committedArgument`, the paper's `lem:logup-point`(3)), its counts the
static plus the late histogram. -/
def logupAt (rd : ir.Valuation I) (t g : ℕ) (α : (I (ir.chalField (ir.alphaOf t))).K) : Bool :=
  match (ir.table t).rows with
  | .range _ => rangeArgument le_rfl (ir.groupNeedles rd (ir.chalField (ir.alphaOf t)) t g)
      (logupTcoef (ir.tableSize t) α) (ir.staticHist rd (ir.chalField (ir.alphaOf t)) t g)
      (ir.lateHist rd (ir.chalField (ir.alphaOf t)) t g) α
  | .columns _ => committedArgument (ir.groupNeedles rd (ir.chalField (ir.alphaOf t)) t g)
      (ir.tableRow rd (ir.chalField (ir.alphaOf t)) t)
      (combined (ir.staticHist rd (ir.chalField (ir.alphaOf t)) t g)
        (ir.lateHist rd (ir.chalField (ir.alphaOf t)) t g)) α
  | .expr _ => committedArgument (ir.groupNeedles rd (ir.chalField (ir.alphaOf t)) t g)
      (ir.tableRow rd (ir.chalField (ir.alphaOf t)) t)
      (combined (ir.staticHist rd (ir.chalField (ir.alphaOf t)) t g)
        (ir.lateHist rd (ir.chalField (ir.alphaOf t)) t g)) α

/-! ## The realized semantics -/

/-- **The LogUp identity of group `g` of table `t`** in the environment `e` (`logupAt`), `α`
coordinate `0` of the table's challenge. -/
def LogupHolds (e : ir.Env I) (t g : ℕ) : Prop :=
  ir.logupAt (ir.reader e) t g (e.chal (ir.alphaOf t) 0) = true

/-- Whether a predicate body is a field `equal`. -/
def _root_.GordieHowe.RealizedProgram.PredBody.isEqual : PredBody → Bool
  | .equal _ _ _ _ => true
  | _ => false

/-- Whether a predicate body is a `mod_0` (an integer equality). -/
def _root_.GordieHowe.RealizedProgram.PredBody.isIntEq : PredBody → Bool
  | .mod _ 0 _ _ _ => true
  | _ => false

/-! ## The MAC of a cross-field `equal` -/

/-- **Coordinate `i` of the expression `e` padded by zeros** (compiler/mac.h: a MAC's operand of
fewer than `chunks · width` bits is padded to them), in domain `d`, reading values by `rd`: the
coordinate below `e`'s length, `0` past it. -/
def evalPad (rd : ir.Valuation I) (d : ℕ) (e : Expr) (i : ℕ) : (I (ir.domainField d)).K :=
  if i < ir.exprLen e then ir.evalWith rd d e i else 0

/-- **Chunk `c` of the H operand** `x` (domain `dx`) of a cross-field `equal`, read into the MAC
field `f`: `Σ_{i<w} g^i · x[c w + i]`, `g` the field's polynomial generator (the encoding `2`;
`fromDigits w x` of compiler/mac.h), `x` padded by zeros past its length (`evalPad`). -/
def macChunkH (rd : ir.Valuation I) (f dx : ℕ) (x : Expr) (w c : ℕ) : (I f).K :=
  ∑ i : Fin w, (I f).decode 2 ^ (i : ℕ) * castElt (ir.evalPad rd dx x (c * w + i))

/-- **The H half of the MAC** of a cross-field `equal` (`<mac>.H`, compiler/mac.h) with H operand
`x` in domain `dx`, at the reader `rd` and the key's value `β`: the tag `U` is
`Σ_c β^(c+1) · chunk_c(X_H)`. -/
def MacHHoldsAt (rd : ir.Valuation I) (dx : ℕ) (x : Expr) (real : MacRealization)
    (β : (I real.macField).K) : Prop :=
  (castElt (rd real.tag 0) : (I real.macField).K) =
    ∑ c : Fin real.chunks, β ^ ((c : ℕ) + 1) * ir.macChunkH rd real.macField dx x real.width c

/-- **Chunk `c` of the A operand** `y` (domain `dy`) of a cross-field `equal`, its coordinates equal
to `1` read into the MAC field `f`: `Σ_{i<w} g^i · [y[c w + i] = 1]`, `y` padded by zeros past its
length (`evalPad`). -/
def macChunkA (rd : ir.Valuation I) (f dy : ℕ) (y : Expr) (w c : ℕ) : (I f).K :=
  ∑ i : Fin w, (I f).decode 2 ^ (i : ℕ) * if ir.evalPad rd dy y (c * w + i) = 1 then 1 else 0

/-- **The tag of a MAC that no domain hosts** (compiler/mac.h, `mac_odd`), with `x` operand `x` in
domain `dx`, at the reader `rd` and the key's value `β`: the tag `U` is `Σ_c β^(c+1) · chunk_c(X_A)`,
the chunks of the coordinates of `x` equal to `1` (`macChunkA`). Its message is `T = U + P`, `P` the
tag's pad, and both blinds are the pad copy `polynomialBits` of `P`. -/
def MacTwoTagAt (rd : ir.Valuation I) (dx : ℕ) (x : Expr) (real : MacRealization)
    (β : (I real.macField).K) : Prop :=
  (castElt (rd real.tag 0) : (I real.macField).K) =
    ∑ c : Fin real.chunks, β ^ ((c : ℕ) + 1) * ir.macChunkA rd real.macField dx x real.width c

/-- **The honest tag of a MAC**: the H half (`MacHHoldsAt`) where `x`'s domain hosts the MAC
(`blindX = none`), the tag of the `x` side's chunks (`MacTwoTagAt`) where no domain does. -/
def MacTagAt (rd : ir.Valuation I) (dx : ℕ) (x : Expr) (real : MacRealization)
    (β : (I real.macField).K) : Prop :=
  match real.blindX with
  | none => ir.MacHHoldsAt rd dx x real β
  | some _ => ir.MacTwoTagAt rd dx x real β

variable {ir} in
/-- **A hosted MAC's honest tag is its H half.** -/
theorem MacTagAt.hosted {rd : ir.Valuation I} {dx : ℕ} {x : Expr} {real : MacRealization}
    {β : (I real.macField).K} (h : ir.MacTagAt rd dx x real β) (hx : real.blindX = none) :
    ir.MacHHoldsAt rd dx x real β := by
  unfold MacTagAt at h
  rw [hx] at h
  exact h

/-- **The blind's tag**: the coordinates of the blind `b` equal to `1` read into the MAC field `f`,
`Σ_{i<w} g^i · [b_i = 1]`. -/
def macBlindTag (rd : ir.Valuation I) (f b w : ℕ) : (I f).K :=
  ∑ i : Fin w, (I f).decode 2 ^ (i : ℕ) * if rd b i = 1 then 1 else 0

/-- **The binding event of a cross-field `equal`'s MAC** in the environment `e`: the MAC polynomial
of the two operands' chunks and the two blinds is nonzero (`MAC.bindingEvent`, of degree
`chunks`). Where `x`'s domain hosts the MAC (no `x`-side blind), the `x` side is the H operand's
chunks with the tag's pad; between two domains neither of which hosts it (`blindX = some bx`), the
`x` side is the coordinates of `x` equal to `1` with the blind `bx`'s tag, as the `y` side. -/
noncomputable def macEvent (e : ir.Env I) (dx : ℕ) (x : Expr) (dy : ℕ) (y : Expr)
    (real : MacRealization) : ChallengeEvent (I real.macField).K :=
  match real.blindX with
  | none =>
    MAC.bindingEvent
      (fun c : Fin real.chunks => ir.macChunkH (ir.reader e) real.macField dx x real.width c)
      (fun c => ir.macChunkA (ir.reader e) real.macField dy y real.width c)
      (castElt (e.asg.pad real.tag 0))
      (ir.macBlindTag (ir.reader e) real.macField (real.blind.getD 0) real.width)
  | some bx =>
    MAC.bindingEvent
      (fun c : Fin real.chunks => ir.macChunkA (ir.reader e) real.macField dx x real.width c)
      (fun c => ir.macChunkA (ir.reader e) real.macField dy y real.width c)
      (ir.macBlindTag (ir.reader e) real.macField bx real.width)
      (ir.macBlindTag (ir.reader e) real.macField (real.blind.getD 0) real.width)

/-- **The realized program holds in the environment `e`**: every field `equal` holds, every
`mod_0` has its field equation, every table group's LogUp identity holds, every node-typed value
lies in its type, and the H half of every hosted cross-field `equal` the compiler states by its own
circuit holds (`MacHHoldsAt` at the key, coordinate `0`; an `<mac>.H` predicate is a field
`equal`; a MAC that no domain hosts, `blindX = some _`, has no H half). -/
structure RealizedAt (e : ir.Env I) : Prop where
  /-- Every field `equal` holds. -/
  equal : ∀ p ∈ ir.predicates, p.body.isEqual = true → ir.HoldsAt e p.body
  /-- Every `mod_0` has its field equation. -/
  integer : ∀ p ∈ ir.predicates, ∀ d lhs rhs real, p.body = .mod d 0 lhs rhs real →
    ∀ i < ir.exprLen lhs, ir.evalWith (ir.reader e) d lhs i = ir.evalWith (ir.reader e) d rhs i
  /-- Every group's LogUp identity holds. -/
  logup : ∀ t < ir.tables.length, ∀ g < ir.groupCountOf t, ir.LogupHolds e t g
  /-- Every node-typed value lies in its type. -/
  types : ir.TypesHold e
  /-- The H half of every hosted cross-field `equal` without an `<mac>.H` predicate holds. -/
  macH : ∀ p ∈ ir.predicates, ∀ dx x dy y k real, p.body = .cross dx x dy y k real →
    real.hPredicate = none → real.blindX = none →
      ir.MacHHoldsAt (ir.reader e) dx x real (castElt (e.chal real.key 0))

variable (I) in
/-- **The realized program as a constraint of the layout**: `RealizedAt` at the layout's
environment of the realized assignment (`bindAsg`). -/
def Realized : (ir.layout I).Constraint (ir.Valuation I) (ir.Assignment I) :=
  fun x a r => ir.RealizedAt (ir.layoutEnv I x (ir.bindAsg a) r)

/-! ## The events -/

/-- **The lookup event at challenge `j`** in the environment `e`: `j` is the challenge of a table
one of whose groups has `α` (coordinate `0` of `j`) as a root of its lookup polynomial. -/
def LookupEvent (j : ℕ) (e : ir.Env I) : Prop :=
  ∃ t < ir.tables.length, ir.alphaOf t = j ∧ ∃ g < ir.groupCountOf t,
    (ir.groupEvent (ir.reader e) (ir.chalField j) t g).BadAt (e.chal j 0)

/-- **The MAC event at challenge `j`** in the environment `e`: `j` is the key of a cross-field
`equal` whose binding event (`macEvent`) has coordinate `0` of `j` as a root. -/
def MacEvent (j : ℕ) (e : ir.Env I) : Prop :=
  ∃ p < ir.predicates.length, ∃ dx x dy y k real,
    (ir.predicate p).body = .cross dx x dy y k real ∧ real.key = j ∧
      (ir.macEvent e dx x dy y real).BadAt (castElt (e.chal j 0))

/-- **The realization event at challenge `j`**: the lookup event or the MAC event at `j`. -/
def RealEvent (j : ℕ) (e : ir.Env I) : Prop := ir.LookupEvent j e ∨ ir.MacEvent j e

/-- **The groups at challenge `j`**: the pairs `(t, g)` of a table `t` with challenge `j` and one
of its groups `g`. -/
def realGroups (j : ℕ) : List (ℕ × ℕ) :=
  ((List.range ir.tables.length).filter fun t => ir.alphaOf t = j).flatMap fun t =>
    (List.range (ir.groupCountOf t)).map fun g => (t, g)

/-- **The chunk count of predicate `p`'s MAC when keyed by challenge `j`**: for a cross-field
`equal` whose key is `j`, its chunk count. -/
def macChunksOf (j p : ℕ) : Option ℕ :=
  match (ir.predicate p).body with
  | .cross _ _ _ _ _ real => if real.key = j then some real.chunks else none
  | _ => none

/-- **The chunk counts of the MACs keyed by challenge `j`**: one per cross-field `equal` whose key
is `j`. -/
def macChunksAt (j : ℕ) : List ℕ :=
  (List.range ir.predicates.length).filterMap (ir.macChunksOf j)

/-- **The error terms at challenge `j`**: per group at `j`, its lookup polynomial's degree bound
`N_g + T − 1` (`N_g` needles, `T` rows: the range `[0, T)` or another table's) and the number `tmax` of values `j` avoids; per
MAC keyed by `j`, its binding polynomial's degree `chunks` (`macChunksAt`). -/
def realErrorTerms (j : ℕ) : List (ℕ × ℕ) :=
  (ir.realGroups j).map (fun tg => (ir.groupCount tg.1 tg.2 + ir.tableSize tg.1 - 1, ir.tmaxOf j)) ++
    (ir.macChunksAt j).map fun n => (n, ir.tmaxOf j)

variable (I) in
/-- **The error at challenge `j`**: the sum over the error terms `(n, u)` of `n / (|F| − u)`, `F`
the field of `j`. -/
noncomputable def realError (j : ℕ) : ℝ≥0 :=
  ((ir.realErrorTerms j).map fun nu =>
    ((nu.1 : ℝ≥0) / (Fintype.card (I (ir.chalField j)).K - nu.2 : ℕ))).sum

/-- **The error at challenge `j`** is the groups' degree bounds over `|F| − tmax`. -/
theorem realError_eq (j : ℕ) :
    ir.realError I j =
      (((ir.realErrorTerms j).map Prod.fst).sum : ℝ≥0) /
        (Fintype.card (I (ir.chalField j)).K - ir.tmaxOf j : ℕ) := by
  have key : ∀ L : List (ℕ × ℕ), (∀ nu ∈ L, nu.2 = ir.tmaxOf j) →
      (L.map fun nu => ((nu.1 : ℝ≥0) / (Fintype.card (I (ir.chalField j)).K - nu.2 : ℕ))).sum =
        ((L.map Prod.fst).sum : ℝ≥0) / (Fintype.card (I (ir.chalField j)).K - ir.tmaxOf j : ℕ) := by
    intro L hL
    induction L with
    | nil => simp
    | cons nu L ih =>
      rw [List.map_cons, List.sum_cons, ih fun x hx => hL x (List.mem_cons_of_mem _ hx),
        hL nu List.mem_cons_self, List.map_cons, List.sum_cons, Nat.cast_add, add_div]
  refine key _ fun nu hnu => ?_
  simp only [realErrorTerms, List.mem_append, List.mem_map] at hnu
  rcases hnu with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl

/-! ## Sampled environments -/

/-- **Every challenge coordinate is a value of its sampler** in the environment `e`, at every
challenge of a phase the program has. The layout's environments are sampled
(`layoutEnv_sampled`). -/
def Env.Sampled (e : ir.Env I) : Prop :=
  ∀ j, ir.IsPhaseChal j → ∀ i < (ir.challenge j).size,
    ∃ x : (I (ir.chalField j)).SamplerTy (ir.challenge j).sampler,
      e.chal j i = (I (ir.chalField j)).samplerVal _ x

variable {ir}

/-- **The layout's environments are sampled**: their challenges are the run's. -/
theorem layoutEnv_sampled (x : ir.Valuation I) (a : ir.Assignment I) (r : (ir.layout I).Run) :
    Env.Sampled ir (ir.layoutEnv I x a r) := by
  intro j hj i hi
  refine ⟨(show ir.ChalVal I j from r.chal ⟨(ir.challenge j).phase - 1, by
    have := hj.2.1; have := hj.2.2; omega⟩ ⟨⟨j, hj.1⟩, by have := hj.2.1; simp only; omega⟩)
    ⟨i, hi⟩, ?_⟩
  change ir.chalRead I r.chal j i = _
  unfold chalRead
  rw [dite_eq_left_of_eq_true (eq_true ⟨hj.1, hj.2.1, hj.2.2, hi⟩)]

end

end GordieHowe.RealizedProgram
