-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Realized
public import GordieHowe.Language.RealizedProgram.Interval

@[expose] public section

/-!
# GordieHowe: the validity of the realizations

The conditions on the realizations that the derivation rules (`GordieHowe/Language/Realizations/Derivation.lean`)
and the completeness checks read, each with a Boolean checker: the recognized shapes of the
realizations, the values' intervals the shapes read, the tables and groups, and the bound values.
The checkers read the shared expressions and the values' reads through the tables of
`GordieHowe/Language/RealizedProgram/Check.lean`.

* **Shapes**: a field `equal` is realized as itself; an `in` realized by
  lookups must have a shape the lemmas cover: the direct lookup (`DirectOk`: one record, one needle,
  the needle the record or a shared expression equal to it, the set the table's range, its rows or
  the entries of the expression its rows are), the
  complement (the needle `(N − 1) − v` into a table of `T` rows, the record's
  interval within `[0, p − T]`), the digits (`DigitsOk`: the needles the digits `d_j` in base `T`,
  the record their number by a reconstruction row or bound to them, `T^k ≤ N`), and two digit sets (`TwoSidedOk`: the needles the digits
  `d_j` and `h_j` in base `T`, `v = Σ_j T^j d_j` by the reconstruction row `v − Σ_j T^j d_j = 0`
  among the predicates or by `v` bound to its digits (`boundDigitsOk`, also `v + c` with `v` bound
  to the digits' number minus `c`), the top row `(N − 1) − v − Σ_j T^j h_j = 0` among the
  predicates, `2 (T^k − 1) < p`); an `in` implied by intervals must be a sum of terms `c_j · a_j`
  with direct `in`s on the `a_j` whose largest value is below its bound; a `mod_q` must
  be the integer form `mod_0` (`IntegerOk`: the exported intervals contain the computed ones
  (`GordieHowe.RealizedProgram.exprIvl`), their span is below `p` and every value read has an interval), the one-digit
  form (`OneDigitOk`: the quotient derived from the sides, `q · (qlo + Q) = e − e'` by their linear
  forms, `quotDerivedB`, `linForm`; the
  computed intervals within the exported ones; the quotient bounded by a direct `in` `Q ∈ [0, N)`
  with the no-wrap conditions `lhsHi − rhsLo < p` and `q (N − 1) + rhsHi − lhsLo < p`,
  `quotRangeB`), or the digit form (`DigitsFormOk`: the left side committed by an accumulator row
  `acc − e = 0` among the predicates, `accRowB`; the top digit derived from the accumulator, the
  right side and the lower digits, `topDerivedB`; each digit bounded by a direct `in`
  `d_j ∈ [0, N_j)`; the computed intervals within the exported ones; the no-wrap conditions
  `lhsHi − rhsLo < p` and `q Σ_j B^j (N_j − 1) + rhsHi − lhsLo < p`), the grouped form
  (`GroupedFormOk`: a left side `b + macConv(r)(y)` in the MAC unit form whose chunks are summed in
  groups by accumulator rows, `groupRowB`, each group's sum within `[0, smax]`, `smax < p`, by the
  interval evaluator; committed base-`T` quotient digits per group with a direct `in`; residues
  `S_g − q Q_g` with a Boolean check or a direct `in` below `Rb`, `residuesB`, `residueBound`; the
  tail `(Rb − 1) + q Σ_j T^j (N_d − 1) < p`; the final sum `b + Σ_g r_g` in the one-digit form
  against the right side, `finalQuotB`), or the field form (`FieldFormOk`: `q = p`, the field
  equation a field `equal` of the program, `fieldRowB`, and both sides' integer readings the
  projections of their values, `projOkB`); a cross-field `equal` must have a MAC's shape
  (`MacRealizable`): hosted by the `x` domain (`MacShapeOk`: key, tag, blind, tail `mod_2`, operands
  read before the key, `y` read as bits, the H half the compiler's own circuit or the H predicate
  `<mac>.H`, `macHalfB`), or hosted by no domain (`MacTwoTailOk`: key, tag, a blind and a tail for
  the MAC check over each field, each field of odd characteristic,
  `GordieHowe.RealizedProgram.MacOddFieldOk`, or of characteristic `2`,
  `GordieHowe.RealizedProgram.MacTwoFieldOk`, whose operand reads bits by the program, `exprBitsB`).
  The scaled and shifted lookups and the other `mod_q` forms (constant, Bit) are rejected. A `mod_q`
  may also be in the committed-digits form (`CommittedFormOk`: the field equation
  `e − e' − q·qlo − q·Σ_j R^j d_j = 0` a field `equal` of the program, `commRowB`; each committed
  digit bounded by a direct or digit `in`; the computed intervals within the exported ones; the
  no-wrap conditions `lhsHi − rhsLo − q·qlo < p` and
  `q Σ_j R^j (N_j − 1) + q·qlo + rhsHi − lhsLo < p`).
* **Intervals of the values** (`GordieHowe.RealizedProgram.LeafIvlsOk`, in odd characteristic): the
  conditions read the values' intervals `L`, each justified by a source
  (`GordieHowe.RealizedProgram.IvlSource`, checked locally by `GordieHowe.RealizedProgram.ivlAt`): a
  constant its centred entries (and `0` when it has fewer entries than coordinates); an opaque `Bit`
  value computed from arguments `[0, 1]`; an entry `(v, N)` of the value ranges `[0, N − 1]`; a
  bound value the `in` on it or on it plus a constant, read centred; a direct or digit `in` `v ∈ [0,
  N)` the interval `[0, N − 1]`; a quadratic root equation `[0, c]`; root-set equations covering
  every coordinate the hull of their roots; a value of type `Bit` read in the prime subfield `[0,
  1]`, and any other value stored in a prime-subfield node `[0, p − 1]`.
  `GordieHowe.RealizedProgram.leafIvl` is one choice of justified intervals, the checker's
  (`GordieHowe.RealizedProgram.leafIvl_justified`).
* **Coverage** (`DirectOk.covered`, …): the members of the table's groups, in group order, tile the
  coordinates `[0, len)` of every needle of every `in` predicate (`tiles`), so every needle
  coordinate lies in exactly one group.
* **Members** (`MemberOk`): every member is a needle of an `in` predicate looking up into its table;
  the needle's values read only what is fixed before the table's challenge `α`, and not `α`
  (`ReadsBefore`; the histograms likewise, `GroupOk.hists`).
* **Sources**: the source predicates read only values of role `source`
  (`Value.role`), so the source program `Π_P` is closed.
* **Bound values** (`BoundOk`): the expression of a value bound to its digits reads only committed
  values and constants, so the realized assignment (`GordieHowe.RealizedProgram.bindAsg`) evaluates it from the
  committed values.
* **Modeled circuits**: no realization circuit or input is `unmodeled` (an `assert_in`
  lookup the program does not export).
* **Sizes** (`GroupOk.size`, `TableOk`): every group has fewer needles than the characteristic of
  `α`'s field; `α`'s sampler is `fieldMinusTables (range tmax)` with `tmax` below the
  characteristic; every table is a range `[0, T)` with `T ≤ tmax`, a committed table whose rows
  (its first column, `ColumnsOk`) read only what is fixed before `α`, and not `α`, or the
  coordinates of an expression that reads likewise (`ExprRowsOk`, `RowsOk`). `α` is a challenge of
  one coordinate of a phase the program has, in the field of the table's domain. The complement,
  digit and two-sided lookups look up into a range (`IsRange`); a direct lookup into a range
  `[0, N)` does too, one into the rows of a table may use a committed table, and one into the
  entries of an expression `e'` uses a table whose rows are `e'`'s coordinates (`DirectSet`).

The prime-subfield nodes of each domain (`primeNodes`, from the plan: `GordieHowe.RealizedProgram.primeNodesOf`) are a
parameter.
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## Tilings -/

/-- **The runs `(first, count)` tile `[pos, len)` in order**: each run starts where the previous
one ends, and the last ends at `len`. -/
def tiles : List (ℕ × ℕ) → ℕ → ℕ → Bool
  | [], pos, len => pos == len
  | fc :: rest, pos, len => fc.1 == pos && tiles rest (pos + fc.2) len

/-- A tiling of `[pos, len)` has `pos ≤ len`. -/
theorem le_of_tiles : ∀ {l : List (ℕ × ℕ)} {pos len : ℕ}, tiles l pos len = true → pos ≤ len
  | [], _, _, h => by simp only [tiles, beq_iff_eq] at h; omega
  | _ :: _, _, _, h => by
    simp only [tiles, Bool.and_eq_true, beq_iff_eq] at h
    have := le_of_tiles h.2
    omega

/-- **Every run of a tiling of `[pos, len)` lies in it.** -/
theorem tiles_bound : ∀ {l : List (ℕ × ℕ)} {pos len : ℕ}, tiles l pos len = true →
    ∀ fc ∈ l, pos ≤ fc.1 ∧ fc.1 + fc.2 ≤ len
  | [], _, _, _, _, h => absurd h List.not_mem_nil
  | _ :: _, _, _, h, fc, hfc => by
    simp only [tiles, Bool.and_eq_true, beq_iff_eq] at h
    rcases List.mem_cons.1 hfc with rfl | hfc
    · exact ⟨h.1.ge, h.1 ▸ le_of_tiles h.2⟩
    · have := tiles_bound h.2 fc hfc
      omega

/-- **A tiling of `[pos, len)` covers it**: every `i` in it lies in a run. -/
theorem tiles_cover : ∀ {l : List (ℕ × ℕ)} {pos len : ℕ}, tiles l pos len = true →
    ∀ i, pos ≤ i → i < len → ∃ fc ∈ l, fc.1 ≤ i ∧ i < fc.1 + fc.2
  | [], _, _, h, _, h1, h2 => by simp only [tiles, beq_iff_eq] at h; omega
  | fc :: _, pos, _, h, i, h1, h2 => by
    simp only [tiles, Bool.and_eq_true, beq_iff_eq] at h
    by_cases hi : i < pos + fc.2
    · exact ⟨fc, List.mem_cons_self .., by omega, by omega⟩
    · obtain ⟨fc', hfc', h'⟩ := tiles_cover h.2 i (by omega) h2
      exact ⟨fc', List.mem_cons_of_mem _ hfc', h'⟩

/-- **A sum over a tiled range is the sum over its runs**: where the runs `(first, count)` tile
`[pos, len)`, the sum of `F` over `[pos, len)` is the sum over the runs of the sums of `F` over
`[first, first + count)`. -/
theorem sum_tiles {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∀ {l : List (ℕ × ℕ)} {pos len : ℕ}, tiles l pos len = true →
      ∑ c ∈ Finset.Ico pos len, F c = (l.map fun fc => ∑ c ∈ Finset.range fc.2, F (fc.1 + c)).sum
  | [], pos, len, h => by
    simp only [tiles, beq_iff_eq] at h
    simp [h]
  | fc :: rest, pos, len, h => by
    simp only [tiles, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    have hle := le_of_tiles h
    rw [← Finset.sum_Ico_consecutive F (Nat.le_add_right fc.1 fc.2) hle, sum_tiles F h,
      Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, List.map_cons, List.sum_cons]

/-- **The bound `N` of a range set** `[0, N)` (`0` for a table or an expression's entries). -/
def InSet.bound : InSet → ℕ
  | .range N => N
  | .table _ => 0
  | .expr _ => 0

/-- **The hull of the interval `J` and the centred constants `es`** at the characteristic `p`. -/
def constIvlFrom (p : ℕ) (J : Ivl) (es : List ℕ) : Ivl :=
  es.foldr (fun c J => J.hull ⟨centeredZ p c, centeredZ p c⟩) J

/-- **The interval of the centred constants `es` and `0`** at the characteristic `p`. -/
def constIvl (p : ℕ) (es : List ℕ) : Ivl := constIvlFrom p ⟨0, 0⟩ es

/-- **A member of `J` lies in the hull of `J` and the constants.** -/
theorem mem_constIvlFrom_of_mem {p : ℕ} {J : Ivl} {x : ℤ} (hx : x ∈ J) :
    ∀ es : List ℕ, x ∈ constIvlFrom p J es
  | [] => hx
  | _ :: es => Ivl.hull_mem_left (J := constIvlFrom p J es) (mem_constIvlFrom_of_mem hx es)

/-- **Every constant lies in the hull of `J` and the constants**, read centred. -/
theorem mem_constIvlFrom {p : ℕ} {J : Ivl} : ∀ (es : List ℕ) (i : ℕ), i < es.length →
    centeredZ p (es.getD i 0) ∈ constIvlFrom p J es
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | c :: es, 0, _ => Ivl.hull_mem_right ⟨le_rfl, le_rfl⟩
  | c :: es, i + 1, h => Ivl.hull_mem_left (J := constIvlFrom p J es) (by
    rw [List.getD_cons_succ]
    exact mem_constIvlFrom es i (by simpa using h))

/-- **The interval of a constant of `n` coordinates** with entries `es`: the hull of its entries
when it has at least `n` of them (every coordinate read is an entry), else the hull of its entries
and `0` (`constIvl`; a coordinate past the entries reads `0`). -/
def constIvlOf (p n : ℕ) : List ℕ → Ivl
  | [] => ⟨0, 0⟩
  | c :: es =>
    if n ≤ es.length + 1 then constIvlFrom p ⟨centeredZ p c, centeredZ p c⟩ es
    else constIvl p (c :: es)

/-- **Every coordinate of a constant lies in its interval**, read centred (`0` past its entries). -/
theorem mem_constIvl {p : ℕ} (hp : 0 < p) : ∀ (es : List ℕ) (i : ℕ),
    centeredZ p (es.getD i 0) ∈ constIvl p es
  | [], _ => by simp [constIvl, constIvlFrom, centeredZ, hp, Ivl.mem_def]
  | c :: es, 0 => Ivl.hull_mem_right ⟨le_rfl, le_rfl⟩
  | c :: es, i + 1 => Ivl.hull_mem_left (J := constIvl p es) (by
    rw [List.getD_cons_succ]
    exact mem_constIvl hp es i)

/-- **Every coordinate below `n` of a constant of `n` coordinates lies in its interval**
(`constIvlOf`), read centred. -/
theorem mem_constIvlOf {p : ℕ} (hp : 0 < p) {n : ℕ} : ∀ (es : List ℕ) {i : ℕ}, i < n →
    centeredZ p (es.getD i 0) ∈ constIvlOf p n es
  | [], i, _ => by simp [constIvlOf, centeredZ, hp, Ivl.mem_def]
  | c :: es, i, hi => by
    simp only [constIvlOf]
    split_ifs with hn
    · rcases i with _ | i
      · exact mem_constIvlFrom_of_mem ⟨le_rfl, le_rfl⟩ es
      · rw [List.getD_cons_succ]
        exact mem_constIvlFrom es i (by omega)
    · exact mem_constIvl hp _ i

/-- **The last term `c · u` of a sum** `rest + c · u`, `c` a constant and `u` a value. -/
def peelStep : Expr → Option (Expr × ℕ × ℕ)
  | .add rest (.scale (.const c) (.leaf u)) => some (rest, c, u)
  | _ => none

theorem eq_of_peelStep {e rest : Expr} {c u : ℕ} (h : peelStep e = some (rest, c, u)) :
    e = .add rest (.scale (.const c) (.leaf u)) := by
  unfold peelStep at h
  split at h
  · cases h
    rfl
  · cases h

/-- **The terms `c_j · u_j` of a left-nested sum** `((h + c_0 u_0) + c_1 u_1) + …` of `n` terms,
`c_j` constants and `u_j` values: the head `h` and the terms in order. -/
def peel : ℕ → Expr → Option (Expr × List (ℕ × ℕ))
  | 0, e => some (e, [])
  | n + 1, e =>
    (peelStep e).bind fun rcu => (peel n rcu.1).map fun ht => (ht.1, ht.2 ++ [(rcu.2.1, rcu.2.2)])

/-- **The terms are `−T^j · u_j`** at the characteristic `p`, from the power `pw = T^j` on: each
constant is `p − pw`, the values are `us` in order. -/
def chainOk (p T : ℕ) : ℕ → List (ℕ × ℕ) → List ℕ → Bool
  | _, [], [] => true
  | pw, (c, u) :: ts, u' :: us => u == u' && c + pw == p && 0 < pw && chainOk p T (pw * T) ts us
  | _, _, _ => false

/-- **The terms are `T^j · u_j`** below the characteristic `p`, from the power `pw = T^j` on: each
constant is `pw < p`, the values are `us` in order. -/
def posChainOk (p T : ℕ) : ℕ → List (ℕ × ℕ) → List ℕ → Bool
  | _, [], [] => true
  | pw, (c, u) :: ts, u' :: us =>
    u == u' && c == pw && decide (pw < p) && posChainOk p T (pw * T) ts us
  | _, _, _ => false

/-- **The expression `x` is the number of the digits `us` in base `T`**: `u_0 + Σ_{j ≥ 1} T^j · u_j`
as a left-nested sum (`peel`) whose head is the first digit and whose terms are `T^j · u_j`
(`posChainOk`), the constants below the characteristic `p` (`RangePolicy::bind_digit_views`,
compiler/range.h). -/
def digitsExprOk (p T : ℕ) (x : Expr) : List ℕ → Bool
  | [] => false
  | u :: us =>
    match peel us.length x with
    | some (.leaf h, ts) => h == u && posChainOk p T T ts us
    | _ => false

/-- **The quotient of a `mod_q`** (`ModRealization.quotient`; a default expression when it has
none). -/
def ModRealization.quotExpr (real : ModRealization) : Expr := real.quotient.getD default

section

variable (ir : RealizedProgram)

/-! ## Reads before a challenge -/

/-- **A read fixed before challenge `j` and other than `j`**: a challenge other than `j` drawn no
later than `j` (`ChalBefore`), a late value of a phase before `j`'s, or a pad. -/
def ReadBefore (j : ℕ) : Read → Prop
  | .chal c => c ≠ j ∧ ir.ChalBefore c j
  | .late u => (ir.value u).phase < (ir.challenge j).phase
  | .pad _ => True

instance (j : ℕ) (rd : Read) : Decidable (ir.ReadBefore j rd) := by
  cases rd <;> unfold ReadBefore <;> try unfold ChalBefore
  all_goals infer_instance

/-- **Value `v` reads only what is fixed before challenge `j`**, and not `j`. -/
def ReadsBefore (j v : ℕ) : Prop := ∀ rd ∈ ir.nodeReads ir.fuel v, ir.ReadBefore j rd

/-- **`ReadsBefore j v`**, through the reads table. -/
def readsBeforeB (j v : ℕ) : Bool := (ir.readsT.getD v []).all fun rd => decide (ir.ReadBefore j rd)

/-! ## The conditions -/

/-- **The runs of needle `n` of predicate `pid` in table `t`**: the members of the table's groups,
in group order, that are coordinates of that needle, as `(first, count)`. -/
def coverRuns (t pid n : ℕ) : List (ℕ × ℕ) :=
  ((List.range (ir.groupCountOf t)).flatMap fun g => ir.members t g).filterMap fun m =>
    if m.pred = pid ∧ m.needle = n then some (m.first, m.count) else none

/-- **Predicate `p` looks up into table `t` with a needle `n`**. -/
def LooksUp (p t n : ℕ) : Prop :=
  match lookupOf? (ir.predicate p).body with
  | some r => r.table = t ∧ n < r.needles.length
  | none => False

instance (p t n : ℕ) : Decidable (ir.LooksUp p t n) := by
  unfold LooksUp
  split <;> infer_instance

/-- **A member of a group of table `t` is valid**: a needle of an `in` predicate that looks up into
`t`, whose shared expressions exist and whose values read only what is fixed before `t`'s
challenge, and not it. -/
structure MemberOk (t : ℕ) (m : Member) : Prop where
  /-- The predicate exists. -/
  pred : m.pred < ir.predicates.length
  /-- The predicate looks up into `t`, with the needle. -/
  looksUp : ir.LooksUp m.pred t m.needle
  /-- The needle's shared expressions exist. -/
  refs : ∀ k ∈ (ir.needleExpr m.pred m.needle).refs, k < ir.exprs.length
  /-- The needle's values read only what is fixed before the challenge. -/
  reads : ∀ v ∈ ir.exprNodes (ir.needleExpr m.pred m.needle), ir.ReadsBefore (ir.alphaOf t) v

/-- **The histogram values of group `g` of table `t`**. -/
def histValues (t g : ℕ) : List ℕ :=
  (ir.groupOf t g).staticMult.toList ++ (ir.groupOf t g).lateMult.toList

/-- **Group `g` of table `t` is valid**: its members are; it has fewer needles than the
characteristic of `α`'s field; its histograms read only what is fixed before `α`, and not it. -/
structure GroupOk (t g : ℕ) : Prop where
  /-- Every member is valid. -/
  members : ∀ m ∈ ir.members t g, ir.MemberOk t m
  /-- Fewer needles than the characteristic. -/
  size : ir.groupCount t g < (ir.field (ir.chalField (ir.alphaOf t))).characteristic
  /-- The histograms read only what is fixed before the challenge. -/
  hists : ∀ v ∈ ir.histValues t g, ir.ReadsBefore (ir.alphaOf t) v

/-- **Table `t` is a range** `[0, T)`. -/
def IsRange (t : ℕ) : Prop := (ir.table t).rows = .range (ir.tableSize t)

instance (t : ℕ) : Decidable (ir.IsRange t) := by
  unfold IsRange
  infer_instance

/-- **The columns `cols` of a committed table `t` are valid**: there is one, and the first, which
holds the rows (`tableRow`), reads only what is fixed before `t`'s challenge `α`, and not `α`. -/
structure ColumnsOk (t : ℕ) (cols : List ℕ) : Prop where
  /-- There is a column. -/
  nonempty : cols ≠ []
  /-- The rows read only what is fixed before the challenge. -/
  reads : ir.ReadsBefore (ir.alphaOf t) (cols.headD 0)

/-- **The rows of table `t`, the coordinates of the expression `e'`, are valid**: `e'`'s shared
expressions exist, and every value it reads reads only what is fixed before `t`'s challenge `α`,
and not `α`. -/
structure ExprRowsOk (t : ℕ) (e' : Expr) : Prop where
  /-- The shared expressions exist. -/
  refs : ∀ k ∈ e'.refs, k < ir.exprs.length
  /-- The rows read only what is fixed before the challenge. -/
  reads : ∀ v ∈ ir.exprNodes e', ir.ReadsBefore (ir.alphaOf t) v

/-- **The rows of table `t` are valid**: a range `[0, T)` within the values `t`'s challenge avoids,
`T ≤ tmax`; committed columns (`ColumnsOk`); or the coordinates of an expression read before `α`
(`ExprRowsOk`). -/
def RowsOk (t : ℕ) : TableRows → Prop
  | .range T => T ≤ ir.tmaxOf (ir.alphaOf t)
  | .columns cols => ir.ColumnsOk t cols
  | .expr e' => ir.ExprRowsOk t e'

/-- **Table `t` is valid**: its rows are (`RowsOk`: a range `[0, T)` with `T ≤ tmax`, committed
columns read before `α`, or an expression's coordinates read before `α`); its challenge `α` is a challenge of one coordinate, of a phase the
program has, in the field of the table's domain, drawn outside `[0, tmax)` with `tmax` below the
characteristic; its groups are valid. -/
structure TableOk (t : ℕ) : Prop where
  /-- The rows are valid. -/
  rows : ir.RowsOk t (ir.table t).rows
  /-- `α` is a challenge of a phase the program has. -/
  alpha : ir.IsPhaseChal (ir.alphaOf t)
  /-- `α` has one coordinate. -/
  size : (ir.challenge (ir.alphaOf t)).size = 1
  /-- `α` is drawn outside `[0, tmax)`. -/
  sampler : (ir.challenge (ir.alphaOf t)).sampler =
    .fieldMinusTables (.range (ir.tmaxOf (ir.alphaOf t)))
  /-- `α`'s field is a field of the program. -/
  field : ir.chalField (ir.alphaOf t) < ir.fields.length
  /-- `α`'s field is the table's domain's. -/
  domain : ir.chalField (ir.alphaOf t) = ir.domainField (ir.table t).domain
  /-- `tmax` is below the characteristic. -/
  char : ir.tmaxOf (ir.alphaOf t) < (ir.field (ir.chalField (ir.alphaOf t))).characteristic
  /-- Every group is valid. -/
  groups : ∀ g < ir.groupCountOf t, ir.GroupOk t g

variable {ir} in
/-- **A valid range table lies within `[0, tmax)`.** -/
theorem TableOk.tmax {t : ℕ} (ht : ir.TableOk t) (hr : ir.IsRange t) :
    ir.tableSize t ≤ ir.tmaxOf (ir.alphaOf t) := by
  have h := ht.rows
  rw [hr] at h
  exact h

/-- **The needle `e'` is the record `e`**: the same expression, or a shared expression that is. -/
def needleMatches (e' e : Expr) : Bool :=
  e'.beq e ||
    match e' with
    | .ref k => decide (k < ir.exprs.length) && (ir.expr k).beq e
    | _ => false

/-- **One record and one needle, the needle matching the record** (`needleMatches`). -/
def singleMatch : List Expr → List Expr → Bool
  | [e], [e'] => ir.needleMatches e' e
  | _, _ => false

/-- **The set of a direct lookup into table `t`**: the range of a range table, the rows of `t`, or
the entries of the expression whose coordinates are `t`'s rows (`TableRows.expr`). -/
def DirectSet (t : ℕ) : InSet → Prop
  | .range n => n = ir.tableSize t ∧ ir.IsRange t
  | .table t' => t' = t
  | .expr e' => (ir.table t).rows = .expr e'

instance (t : ℕ) (set : InSet) : Decidable (ir.DirectSet t set) := by
  cases set <;> unfold DirectSet <;> infer_instance

/-- **A direct lookup** of predicate `pid` in domain `d` with records `recs` into the set `set`:
the table exists and is of the domain; the set is the range of a range table, the table's rows (a
range, a committed table or an expression's coordinates), or the entries of the expression whose
coordinates are the table's rows (`DirectSet`); one record and one needle matching it; the needles' shared
expressions exist; and the members of the table's groups tile the coordinates of every needle. -/
structure DirectOk (pid d : ℕ) (recs : List Expr) (set : InSet)
    (r : LookupRealization) : Prop where
  /-- The table exists. -/
  table : r.table < ir.tables.length
  /-- The table is of the domain. -/
  domain : d = (ir.table r.table).domain
  /-- The set is the range of a range table, the table's rows, or the entries of the table's
  expression. -/
  set : ir.DirectSet r.table set
  /-- One record and one needle matching it. -/
  record : ir.singleMatch recs r.needles = true
  /-- The needles' shared expressions exist. -/
  refs : ∀ e ∈ r.needles, ∀ k ∈ e.refs, k < ir.exprs.length
  /-- The members tile every needle's coordinates. -/
  covered : ∀ n < r.needles.length,
    tiles (ir.coverRuns r.table pid n) 0 (ir.exprLen (r.needles.getD n default)) = true

/-! ## The values' intervals -/

/-- **The characteristic of field `f`.** -/
abbrev charOf (f : ℕ) : ℕ := (ir.field f).characteristic

/-- **Predicate `q` is the Boolean check `v · v = v` of value `v`** in a domain of `v`'s field. -/
def boolCheckOk (v q : ℕ) : Bool :=
  decide (q < ir.predicates.length) &&
    match (ir.predicate q).body with
    | .equal d (.mul (.leaf a) (.leaf b)) (.leaf c) _ =>
      a == v && b == v && c == v && decide (ir.domainField d = ir.valueField v)
    | _ => false

/-- **Value `v` is read in the prime subfield** (`primeNodes d` the prime-subfield nodes of domain
`d`): its domain exists, and it is of type `Bit` at a node or with its Boolean check
(`boolCheckOk`), or of type `Sub(E)` stored at the prime-subfield node `E`. -/
def primeRead (primeNodes : ℕ → List String) (v : ℕ) : Bool :=
  decide ((ir.value v).domain < ir.domains.length) &&
    match (ir.value v).type, (ir.value v).typeSource with
    | .bit, .node => true
    | .bit, .pred q => ir.boolCheckOk v q
    | .sub E, .node => decide (E ∈ primeNodes (ir.value v).domain)
    | _, _ => false

/-- **The bound of an `in` on value `v`** in predicate `p`: `N` for the `in` `v ∈ [0, N)` realized
by a direct or a digit lookup, with `0 < N` at most the characteristic, in a domain of `v`'s
field. -/
def rangeBoundOf (v : ℕ) (p : Predicate) : Option ℕ :=
  match p.body with
  | .mem d [.leaf u] (.range N) (.lookup r) =>
    if u = v ∧ (r.kind = .direct ∨ r.kind = .digits) ∧ 0 < N ∧ N ≤ ir.charOf (ir.valueField v) ∧
        ir.domainField d = ir.valueField v then some N else none
  | _ => none

/-- **The bound of value `v`**: the first direct or digit `in` on it (`rangeBoundOf`). -/
def rangeBound (v : ℕ) : Option ℕ := ir.predicates.findSome? (ir.rangeBoundOf v)

/-- **The constant value `u` holds `c` at its first `n` coordinates**, a value of field `f`. -/
def constAll (u c n f : ℕ) : Bool :=
  match (ir.value u).kind with
  | .constant es => decide (n ≤ es.length) && es.all (· == c) && decide (ir.valueField u = f)
  | _ => false

/-- **The constant entry of value `c` at `n` coordinates** in field `f`: `k` when `c` is a constant of
field `f` holding `k` at its first `n` coordinates (`constAll`). -/
def constEntry (c n f : ℕ) : Option ℕ :=
  match (ir.value c).kind with
  | .constant (k :: _) => if ir.constAll c k n f = true ∧ k < ir.charOf f then some k else none
  | _ => none

/-- **The range of an `in` on value `v` or on `v + c`** in predicate `p`: `(c₀, N)`
for the `in` `v + c ∈ [0, N)` with `c` a constant holding `c₀` (read centred), or `(0, N)` for
`v ∈ [0, N)`, realized by a direct, digit or two-sided lookup, with `0 < N` at most the
characteristic, in a domain of `v`'s field. -/
def shiftRangeOf (v : ℕ) (p : Predicate) : Option (ℤ × ℕ) :=
  match p.body with
  | .mem d [rec] (.range N) (.lookup r) =>
    if 0 < N ∧ N ≤ ir.charOf (ir.valueField v) ∧ ir.domainField d = ir.valueField v ∧
        (r.kind = .direct ∨ r.kind = .digits ∨ r.kind = .twoSided) then
      match rec with
      | .leaf u => if u = v then some (0, N) else none
      | .add (.leaf u) (.leaf c) =>
        if u = v then
          (ir.constEntry c (ir.value v).size (ir.valueField v)).map fun k =>
            (centeredZ (ir.charOf (ir.valueField v)) k, N)
        else none
      | _ => none
    else none
  | _ => none

/-- **The interval of a centred range** `(c₀, N)` of value `v` (`shiftRangeOf`):
`v ∈ [−c₀, N − 1 − c₀]`, when both ends lie in `(−p/2, p/2)`. -/
def centredIvl (v : ℕ) (cN : ℤ × ℕ) : Option Ivl :=
  if 2 * |-cN.1| < ir.charOf (ir.valueField v) ∧
      2 * |(cN.2 : ℤ) - 1 - cN.1| < ir.charOf (ir.valueField v)
  then some ⟨-cN.1, (cN.2 : ℤ) - 1 - cN.1⟩ else none

/-- **The interval of value `v` from the `in` of predicate `q`** read centred
(`RealizedProgram.intOf`): the `in` on `v` or `v + c` of predicate `q` (`shiftRangeOf`), with its
interval (`centredIvl`). -/
def shiftIvl (v q : ℕ) : Option Ivl :=
  if q < ir.predicates.length then
    match ir.shiftRangeOf v (ir.predicate q) with
    | some cN => ir.centredIvl v cN
    | none => none
  else none

/-- **The interval of a bound value** read centred (`RealizedProgram.intOf`): from the first `in` on `v` or
`v + c` (`shiftRangeOf`), with its interval (`centredIvl`). -/
def boundIvl (v : ℕ) : Option Ivl :=
  match ir.predicates.findSome? (ir.shiftRangeOf v) with
  | some cN => ir.centredIvl v cN
  | none => none

/-- **The constant read by an expression of `n` coordinates in field `f`**: `k` for a constant leaf
holding `k` at its first `n` coordinates (`constEntry`), or a view of a constant holding `k` at
every coordinate whose first `n` entries stay inside the constant; none otherwise. -/
def constOf (n f : ℕ) : Expr → Option ℕ
  | .leaf c => ir.constEntry c n f
  | .reindex idx (.leaf c) =>
    if (List.range n).all fun i => decide (idx.entry i < (ir.value c).size) then
      ir.constEntry c (ir.value c).size f
    else none
  | _ => none

/-- **A quadratic root equation on value `v`** in predicate `pr`: the field `equal`
`(m − v)(m − (c − v)) = 0` (`v` a root of the quadratic whose roots are `m` and `c − m`, the
compiler's magnitude equations `magnitudes.s1`, `magnitudes.s2`), written
`(m + a v) · (m + a (a v + C)) = z` with `a = p − 1`, `z` a constant holding `0`, `C` a constant
expression holding `c` (`constOf`), `m` a value of `v`'s field: the value `m` and the constant
`c`. -/
def quadRootView (v : ℕ) (pr : Predicate) : Option (ℕ × ℕ) :=
  match pr.body with
  | .equal d lhs (.leaf z) _ =>
    match lhs with
    | .mul (.add (.leaf m) (.scale (.const a) (.leaf v₁)))
        (.add (.leaf m₂) (.scale (.const a₂) (.add (.scale (.const a₃) (.leaf v₂)) C))) =>
      if v₁ = v ∧ v₂ = v ∧ m₂ = m ∧ a + 1 = ir.charOf (ir.valueField v) ∧ a₂ = a ∧ a₃ = a ∧
          ir.domainField d = ir.valueField v ∧ ir.valueField m = ir.valueField v ∧
          ir.valueField z = ir.valueField v ∧ (ir.value v).size ≤ ir.exprLen lhs ∧
          ir.zeroConstB z = true then
        (ir.constOf (ir.value v).size (ir.valueField v) C).map fun c => (m, c)
      else none
    | _ => none
  | _ => none

/-- **The interval of a quadratic root** `v` with the constant `c` (`quadRootView`), its `m` with
the interval `J`: `[0, c]` when `J = [0, M]` with `M ≤ c`. -/
def quadIvl (c : ℕ) (J : Ivl) : Option Ivl :=
  if J.lo = 0 ∧ J.hi ≤ c then some ⟨0, c⟩ else none

/-- **The interval of value `v` from a quadratic root equation** in predicate `pr` (`quadRootView`),
its `m` with the interval of an `in` (`boundIvl`): `quadIvl`. -/
def quadRootOf (v : ℕ) (pr : Predicate) : Option Ivl :=
  match ir.quadRootView v pr with
  | some (m, c) =>
    match ir.boundIvl m with
    | some J => quadIvl c J
    | none => none
  | none => none

/-- **The depth of a root product** the root-set rule follows (`rootsAt`): a product deeper than
this is not read as one. -/
def rootFuel : ℕ := 64

/-- **The value and index map of a chain of `reindex`es over a leaf**, through shared expressions
at `level` levels, with `fuel` steps: `(u, g)` when coordinate `i` of the expression is coordinate
`g i` of value `u`. -/
def leafViewAt : ℕ → ℕ → Expr → Option (ℕ × (ℕ → ℕ))
  | _, _, .leaf u => some (u, id)
  | fuel + 1, level, .reindex idx e =>
    (leafViewAt fuel level e).map fun ug => (ug.1, fun i => ug.2 (idx.entry i))
  | fuel + 1, level + 1, .ref k => leafViewAt fuel level (ir.expr k)
  | _, _, _ => none

/-- **The entries a constant expression reads** in field `f` (`leafViewAt`): `cv` when coordinate
`i` of the expression is the entry `cv i` of a constant of field `f`. -/
def constReadAt (f fuel level : ℕ) (C : Expr) : Option (ℕ → ℕ) :=
  match ir.leafViewAt fuel level C with
  | some (c, gc) =>
    match (ir.value c).kind with
    | .constant es => if ir.valueField c = f then some fun i => es.getD (gc i) 0 else none
    | _ => none
  | none => none

/-- **The roots of a factor's constant part** in field `f` at its first `L` coordinates
(`constReadAt`): `ρ` when the factor `X + C` vanishes exactly at `X = ρ i`. For `C = a C'` with
`a = p − 1` (`−C'`), the entries of `C'`; for any other constant `C`, the entries `(p − c) mod p`
of `−C`. The entries read lie below the characteristic `p`. -/
def factorRoots (f fuel level L : ℕ) (C : Expr) : Option (ℕ → ℕ) :=
  match C with
  | .scale (.const a) C' =>
    match ir.constReadAt f fuel level C' with
    | some cv => if a + 1 = ir.charOf f ∧ ∀ i < L, cv i < ir.charOf f then some cv else none
    | none => none
  | _ =>
    match ir.constReadAt f fuel level C with
    | some cv =>
      if ∀ i < L, cv i < ir.charOf f then some fun i => (ir.charOf f - cv i) % ir.charOf f
      else none
    | none => none

/-- **A root product** in field `f` at its first `L` coordinates, through shared expressions at
`level` levels, with `fuel` steps: `(u, j, r)` when coordinate `i < L` of the expression is
`κ · ∏_{ρ ∈ r i} (u_{j i} − ρ)` for a nonzero `κ`, so that it vanishes only when `u_{j i}` is one of
the roots `r i`. The factors are `X` (the root `0`) and `X + C`, `X` a chain of `reindex`es of `u`
(`leafViewAt`) and `C` a constant part (`factorRoots`); products are `mul` (of equal reads of `u`), `prod n` (of `n`
factors reading the same coordinate of `u`) and `scale` by a nonzero constant below `p`. -/
def rootsAt (f : ℕ) : ℕ → ℕ → ℕ → Expr → Option (ℕ × (ℕ → ℕ) × (ℕ → List ℕ))
  | 0, _, _, _ => none
  | fuel + 1, level, L, e =>
    match e with
    | .mul a b =>
      match rootsAt f fuel level L a with
      | some (u, g, r) =>
        match rootsAt f fuel level L b with
        | some (u', g', r') =>
          if u = u' ∧ ∀ i < L, g i = g' i then some (u, g, fun i => r i ++ r' i) else none
        | none => none
      | none => none
    | .ref k =>
      match level with
      | 0 => none
      | level + 1 => rootsAt f fuel level L (ir.expr k)
    | .scale (.const s) a =>
      if 0 < s ∧ s < ir.charOf f then rootsAt f fuel level L a else none
    | .prod n a =>
      match rootsAt f fuel level (L * n) a with
      | some (u, g, r) =>
        if ∀ i < L, ∀ t < n, g (i * n + t) = g (i * n) then
          some (u, fun i => g (i * n), fun i => (List.range n).flatMap fun t => r (i * n + t))
        else none
      | none => none
    | .add X C =>
      match ir.leafViewAt fuel level X, ir.factorRoots f fuel level L C with
      | some (u, g), some ρ => some (u, g, fun i => [ρ i])
      | _, _ => none
    | X => (ir.leafViewAt fuel level X).map fun ug => (ug.1, ug.2, fun _ => [0])

/-- **A root-set equation on value `v`** in predicate `pr`: the field `equal` `P = z` with `z` a
constant holding `0` and `P` a root product on `v` in `v`'s field at the equation's coordinates
(`rootsAt`; first read at no coordinates, so that the equation's length is computed only for a
root product on `v`), whose roots lie below the characteristic: the coordinates `j i` of `v` it reads, its
number `L` of coordinates, and the interval `[min, max]` of its roots. -/
def rootSetView (v : ℕ) (pr : Predicate) : Option ((ℕ → ℕ) × ℕ × Ivl) :=
  match pr.body with
  | .equal d lhs (.leaf z) _ =>
    if (ir.rootsAt (ir.domainField d) rootFuel ir.exprs.length 0 lhs).map (·.1) = some v ∧
        ir.zeroConstB z = true then
      let L := ir.exprLen lhs
      match ir.rootsAt (ir.domainField d) rootFuel ir.exprs.length L lhs with
      | some (u, j, r) =>
        let rs := (List.range L).flatMap r
        let lo := rs.foldl min (rs.headD 0)
        let hi := rs.foldl max 0
        if u = v ∧ ir.domainField d = ir.valueField v ∧ ir.valueField z = ir.valueField v ∧
            ∀ i < L, ∀ ρ ∈ r i, lo ≤ ρ ∧ ρ ≤ hi ∧ ρ < ir.charOf (ir.valueField v) then
          some (j, L, ⟨lo, hi⟩)
        else none
      | none => none
    else none
  | _ => none

/-- **Predicate `pr` is a root equation on value `v`**: a quadratic root equation (`quadRootView`)
or a root-set equation (`rootSetView`) on it. The values' intervals read only these equations'
facts (`RealizedProgram.IvlFacts.roots`). -/
def rootEqB (v : ℕ) (pr : Predicate) : Bool :=
  (ir.quadRootView v pr).isSome || (ir.rootSetView v pr).isSome

/-- **The interval of value `v` from the root-set equations `ws`** (`rootSetView`): when they
together read every coordinate of `v`, the interval `[lo, hi]` holding every one of their
intervals. -/
def rootSetHull (v : ℕ) (ws : List ((ℕ → ℕ) × ℕ × Ivl)) : Option Ivl :=
  let lo := (ws.map fun w => w.2.2.lo).foldl min ((ws.map fun w => w.2.2.lo).headD 0)
  let hi := (ws.map fun w => w.2.2.hi).foldl max ((ws.map fun w => w.2.2.hi).headD 0)
  if (∀ c < (ir.value v).size, ∃ w ∈ ws, ∃ i < w.2.1, w.1 i = c) ∧
      ∀ w ∈ ws, lo ≤ w.2.2.lo ∧ w.2.2.hi ≤ hi then
    some ⟨lo, hi⟩
  else none

/-- **The interval of value `v` from its root-set equations** (`rootSetView`, `rootSetHull`): the
hull of every root-set equation on `v`, when there is one. A `Bit` value has none (its interval is
its type's, `restIvl`). -/
def rootSetIvl (v : ℕ) : Option Ivl :=
  if (ir.value v).type = .bit then none else
  let ws := ir.predicates.filterMap (ir.rootSetView v)
  if ws.isEmpty then none else ir.rootSetHull v ws

/-- **The interval of value `v` from its root equations**: the first quadratic root equation on it
(`quadRootOf`), else its root-set equations (`rootSetIvl`). -/
def rootIvl (v : ℕ) : Option Ivl :=
  match ir.predicates.findSome? (ir.quadRootOf v) with
  | some J => some J
  | none => ir.rootSetIvl v

/-- **The interval of value `v` from its range or its node** (`leafIvl`'s fallback): a value with
a direct or digit `in` `v ∈ [0, N)` the interval `[0, N − 1]` (`rangeBound`); else a prime-subfield
read (`primeRead`) `[0, 1]` for `Bit` and `[0, p − 1]` otherwise; none otherwise. -/
def restIvl (primeNodes : ℕ → List String) (f v : ℕ) : Option Ivl :=
  match ir.rangeBound v with
  | some N => some ⟨0, (N : ℤ) - 1⟩
  | none =>
    if ir.primeRead primeNodes v then
      some (if (ir.value v).type = .bit then ⟨0, 1⟩ else ⟨0, (ir.charOf f : ℤ) - 1⟩)
    else none

/-- **The interval of value `v`'s coordinates read in field `f`** at the value ranges `sr` (see
`restIvl`, `boundIvl`; `(value, bound)` entries: the declared statement bounds and the ranges of
opaque functions, `RealizedProgram.ShiftFacts.stmt`): a constant below the characteristic its centred
entries (`constIvlOf`); an opaque value computed from arguments `[0, 1]` if of type `Bit`, else
`[0, N − 1]` if listed in `sr` with the bound `N`; a bound value its `boundIvl`; an opaque statement
value with no arguments listed in `sr` with the bound `N` the interval `[0, N − 1]`; else the
interval of a root equation on it (`rootIvl`) or `restIvl`. One choice of intervals the sources
justify (`RealizedProgram.leafIvl_justified`). -/
def leafIvl (primeNodes : ℕ → List String) (f v : ℕ) (sr : List (ℕ × ℕ) := []) : Option Ivl :=
  if v < ir.values.length ∧ ir.valueField v = f ∧ f < ir.fields.length ∧ 2 < ir.charOf f then
    match (ir.value v).kind with
    | .constant es =>
      if es.all (· < ir.charOf f) then some (constIvlOf (ir.charOf f) (ir.value v).size es)
      else none
    | .pub (.opaque _ (_ :: _)) =>
      if (ir.value v).type = .bit then some ⟨0, 1⟩
      else
        match sr.lookup v with
        | some N => if 0 < N ∧ N ≤ ir.charOf f then some ⟨0, (N : ℤ) - 1⟩ else none
        | none => none
    | .pub (.opaque _ []) =>
      match sr.lookup v with
      | some N => if 0 < N ∧ N ≤ ir.charOf f then some ⟨0, (N : ℤ) - 1⟩ else none
      | none => ir.restIvl primeNodes f v
    | .bound _ => ir.boundIvl v
    | _ =>
      match ir.rootIvl v with
      | some J => some J
      | none => ir.restIvl primeNodes f v
  else none

/-! ### The sources of the values' intervals -/

/-- **The source of a value's interval**: the rule, with the predicates or the entry it reads, that
justifies the interval (`RealizedProgram.ivlAt`). -/
inductive IvlSource where
  /-- A constant: its centred entries. -/
  | const
  /-- An opaque value of type `Bit` computed from arguments: `[0, 1]`. -/
  | opaqueBit
  /-- Entry `k` of the value ranges: the value with its bound `N`, `[0, N − 1]`. -/
  | declared (k : ℕ)
  /-- A bound value: the `in` on it or on it plus a constant of predicate `q`, read centred. -/
  | shiftRange (q : ℕ)
  /-- The direct or digit `in` `v ∈ [0, N)` of predicate `q`: `[0, N − 1]`. -/
  | range (q : ℕ)
  /-- The quadratic root equation of predicate `q`, its `m` with the interval of the `in` of
  predicate `r` (`shiftRange r`): `[0, c]`. -/
  | quadRoot (q r : ℕ)
  /-- The root-set equations of the predicates `qs`, covering every coordinate: the hull of their
  intervals. -/
  | rootSet (qs : List ℕ)
  /-- A prime-subfield read: `[0, 1]` for `Bit`, else `[0, p − 1]`. -/
  | prime
  deriving Repr, DecidableEq, Inhabited

/-- **The sources a value of kind `k` takes**: a constant only its entries; an opaque value
computed from arguments its `Bit` type or a value range; an opaque statement value with no arguments
a value range, a range or a prime-subfield read; a bound value an `in` read centred; any other
value a root equation, a range or a prime-subfield read. -/
def IvlSource.allows : Kind → IvlSource → Bool
  | .constant _, .const => true
  | .constant _, _ => false
  | .pub (.opaque _ (_ :: _)), .opaqueBit => true
  | .pub (.opaque _ (_ :: _)), .declared _ => true
  | .pub (.opaque _ (_ :: _)), _ => false
  | .pub (.opaque _ []), .declared _ => true
  | .pub (.opaque _ []), .range _ => true
  | .pub (.opaque _ []), .prime => true
  | .pub (.opaque _ []), _ => false
  | .bound _, .shiftRange _ => true
  | .bound _, _ => false
  | _, .quadRoot _ _ => true
  | _, .rootSet _ => true
  | _, .range _ => true
  | _, .prime => true
  | _, _ => false

/-- **A constant takes only its entries**, and only a constant does. -/
theorem IvlSource.allows_const {k : Kind} (h : IvlSource.allows k .const = true) :
    ∃ es, k = .constant es := by
  rcases k with _ | ⟨_ | ⟨n, _ | ⟨a, as⟩⟩ | x⟩ | es | c | _ | ⟨w, sel⟩ | ⟨u, mp⟩ | u | x <;>
    simp_all [IvlSource.allows]

/-- **Only an opaque value computed from arguments takes its `Bit` type.** -/
theorem IvlSource.allows_opaqueBit {k : Kind} (h : IvlSource.allows k .opaqueBit = true) :
    ∃ name a args, k = .pub (.opaque name (a :: args)) := by
  rcases k with _ | ⟨_ | ⟨n, _ | ⟨a, as⟩⟩ | x⟩ | es | c | _ | ⟨w, sel⟩ | ⟨u, mp⟩ | u | x <;>
    simp_all [IvlSource.allows]

/-- **Only a bound value takes an `in` read centred.** -/
theorem IvlSource.allows_shiftRange {k : Kind} {q : ℕ}
    (h : IvlSource.allows k (.shiftRange q) = true) : ∃ x, k = .bound x := by
  rcases k with _ | ⟨_ | ⟨n, _ | ⟨a, as⟩⟩ | x⟩ | es | c | _ | ⟨w, sel⟩ | ⟨u, mp⟩ | u | x <;>
    simp_all [IvlSource.allows]

/-- **A value taking a source other than its entries or an `in` read centred is neither a constant
nor bound.** -/
theorem IvlSource.allows_other {k : Kind} {s : IvlSource} (h : s.allows k = true)
    (hc : s ≠ .const) (hb : ∀ q, s ≠ .shiftRange q) :
    (∀ es, k ≠ .constant es) ∧ ∀ x, k ≠ .bound x := by
  constructor
  · rintro es rfl
    cases s <;> simp_all [IvlSource.allows]
  · rintro x rfl
    cases s <;> simp_all [IvlSource.allows]

/-- **The interval of entry `k` of the value ranges `sr`** for value `v` of field `f`: `[0, N − 1]`
for the entry `(v, N)` with `0 < N` at most the characteristic. -/
def declaredIvl (sr : List (ℕ × ℕ)) (f v k : ℕ) : Option Ivl :=
  match sr[k]? with
  | some (u, N) => if u = v ∧ 0 < N ∧ N ≤ ir.charOf f then some ⟨0, (N : ℤ) - 1⟩ else none
  | none => none

/-- **The interval of value `v` from the `in` of predicate `q`** (`rangeBoundOf`): `[0, N − 1]`. -/
def rangeIvl (v q : ℕ) : Option Ivl :=
  if q < ir.predicates.length then
    (ir.rangeBoundOf v (ir.predicate q)).map fun N : ℕ => ⟨0, (N : ℤ) - 1⟩
  else none

/-- **The interval of a prime-subfield read** `v` of field `f` (`primeRead`): `[0, 1]` for `Bit`,
else `[0, p − 1]`. -/
def primeIvl (primeNodes : ℕ → List String) (f v : ℕ) : Option Ivl :=
  if ir.primeRead primeNodes v then
    some (if (ir.value v).type = .bit then ⟨0, 1⟩ else ⟨0, (ir.charOf f : ℤ) - 1⟩)
  else none

/-- **The interval of value `v` from the quadratic root equation of predicate `q`**
(`quadRootView`), its `m` with the interval of the `in` of predicate `r` (`shiftIvl`): `quadIvl`. -/
def quadRootIvl (v q r : ℕ) : Option Ivl :=
  if q < ir.predicates.length then
    match ir.quadRootView v (ir.predicate q) with
    | some (m, c) =>
      match ir.shiftIvl m r with
      | some J => quadIvl c J
      | none => none
    | none => none
  else none

/-- **The root-set equations on value `v` of the predicates `qs`** (`rootSetView`). -/
def rootSetViews (v : ℕ) (qs : List ℕ) : List ((ℕ → ℕ) × ℕ × Ivl) :=
  qs.filterMap fun q => if q < ir.predicates.length then ir.rootSetView v (ir.predicate q) else none

/-- **The interval of value `v` from the root-set equations of the predicates `qs`**
(`rootSetViews`, `rootSetHull`). -/
def rootSetIvlAt (v : ℕ) (qs : List ℕ) : Option Ivl := ir.rootSetHull v (ir.rootSetViews v qs)

/-- **The interval rule `s` at value `v` of field `f`** at the value ranges `sr`, checked locally
(`primeNodes d` the prime-subfield nodes of domain `d`): see `IvlSource`. -/
def ruleIvl (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (f v : ℕ) : IvlSource → Option Ivl
  | .const =>
    match (ir.value v).kind with
    | .constant es =>
      if es.all (· < ir.charOf f) then some (constIvlOf (ir.charOf f) (ir.value v).size es)
      else none
    | _ => none
  | .opaqueBit => if (ir.value v).type = .bit then some ⟨0, 1⟩ else none
  | .declared k => ir.declaredIvl sr f v k
  | .shiftRange q => ir.shiftIvl v q
  | .range q => ir.rangeIvl v q
  | .quadRoot q r => ir.quadRootIvl v q r
  | .rootSet qs => ir.rootSetIvlAt v qs
  | .prime => ir.primeIvl primeNodes f v

/-- **The interval source `s` justifies an interval of value `v`'s coordinates read in field `f`**
at the value ranges `sr`: under `leafIvl`'s guards (a value of the program and of field `f`, of
characteristic above `2`), a source the value's kind takes (`IvlSource.allows`), and its rule
(`ruleIvl`). -/
def ivlAt (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (f v : ℕ) (s : IvlSource) :
    Option Ivl :=
  if v < ir.values.length ∧ ir.valueField v = f ∧ f < ir.fields.length ∧ 2 < ir.charOf f ∧
      s.allows (ir.value v).kind = true then
    ir.ruleIvl primeNodes sr f v s
  else none

/-- **Value `v`'s coordinates read in field `f` have the interval `J`** at the value ranges `sr`:
some source justifies it (`ivlAt`). -/
def HasIvl (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (f v : ℕ) (J : Ivl) : Prop :=
  ∃ s, ir.ivlAt primeNodes sr f v s = some J

/-- **The values' intervals `L` are justified** at the value ranges `sr`: every interval
`L f v = some J` has a source (`HasIvl`). -/
def LeafIvlsOk (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (L : ℕ → ℕ → Option Ivl) :
    Prop :=
  ∀ f v J, L f v = some J → ir.HasIvl primeNodes sr f v J

/-- **The interval of an expression of field `f`** at the values' intervals `L`
(`RealizedProgram.ivlOf`). -/
def exprIvl (L : ℕ → ℕ → Option Ivl) (f : ℕ) (e : Expr) : Option Ivl :=
  ir.ivlOf (ir.charOf f) (L f) e

/-! ### `leafIvl` is justified -/

variable {ir} in
/-- **A predicate of the program is a predicate at an index.** -/
theorem exists_index_of_mem {p : Predicate} (hp : p ∈ ir.predicates) :
    ∃ pid < ir.predicates.length, ir.predicate pid = p := by
  obtain ⟨pid, hpid, rfl⟩ := List.getElem_of_mem hp
  exact ⟨pid, hpid, by rw [predicate, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpid,
    Option.getD_some]⟩

/-- **A list search along the predicates finds a predicate at an index.** -/
theorem exists_index_of_findSome? {α : Type*} {g : Predicate → Option α} {a : α}
    (h : ir.predicates.findSome? g = some a) :
    ∃ q < ir.predicates.length, g (ir.predicate q) = some a := by
  obtain ⟨p, hp, hg⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨q, hq, rfl⟩ := exists_index_of_mem hp
  exact ⟨q, hq, hg⟩

/-- **The predicates are the predicates at the indices below their number.** -/
theorem map_predicate_range : (List.range ir.predicates.length).map ir.predicate = ir.predicates :=
    by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, predicate, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h2, Option.getD_some]

/-- **A listed value range is an entry of the value ranges.** -/
theorem exists_index_of_lookup : ∀ {sr : List (ℕ × ℕ)} {v N : ℕ}, sr.lookup v = some N →
    ∃ k : ℕ, sr[k]? = some (v, N)
  | [], _, _, h => by simp at h
  | (u, M) :: sr, v, N, h => by
    by_cases hu : v = u
    · subst hu
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
      exact ⟨0, by simp [h]⟩
    · simp only [List.lookup, show (v == u) = false from beq_false_of_ne hu] at h
      obtain ⟨k, hk⟩ := exists_index_of_lookup h
      exact ⟨k + 1, by simpa using hk⟩

/-- **The interval of a bound value is the interval of the `in` of a predicate** (`boundIvl`,
`shiftIvl`). -/
theorem exists_shiftIvl_of_boundIvl {v : ℕ} {J : Ivl} (h : ir.boundIvl v = some J) :
    ∃ q, ir.shiftIvl v q = some J := by
  unfold boundIvl at h
  split at h
  · rename_i cN hcN
    obtain ⟨q, hq, hg⟩ := ir.exists_index_of_findSome? hcN
    exact ⟨q, by simp only [shiftIvl, if_pos hq, hg, h]⟩
  · cases h

/-- **The fallback interval is a range's or a prime-subfield read's** (`restIvl`, `rangeIvl`,
`primeIvl`). -/
theorem exists_rule_of_restIvl {primeNodes : ℕ → List String} {sr : List (ℕ × ℕ)} {f v : ℕ}
    {J : Ivl} (h : ir.restIvl primeNodes f v = some J) :
    ∃ s, (s = .prime ∨ ∃ q, s = .range q) ∧ ir.ruleIvl primeNodes sr f v s = some J := by
  unfold restIvl at h
  split at h
  · rename_i N hN
    obtain ⟨q, hq, hg⟩ := ir.exists_index_of_findSome? hN
    exact ⟨.range q, .inr ⟨q, rfl⟩, by simp only [ruleIvl, rangeIvl, if_pos hq, hg, h,
      Option.map_some]⟩
  · exact ⟨.prime, .inl rfl, by simp only [ruleIvl, primeIvl]; exact h⟩

/-- **The interval of a root equation is a quadratic root's or a root set's** (`rootIvl`,
`quadRootIvl`, `rootSetIvlAt`). -/
theorem exists_rule_of_rootIvl {primeNodes : ℕ → List String} {sr : List (ℕ × ℕ)} {f v : ℕ}
    {J : Ivl} (h : ir.rootIvl v = some J) :
    ∃ s, ((∃ q r, s = .quadRoot q r) ∨ ∃ qs, s = .rootSet qs) ∧
      ir.ruleIvl primeNodes sr f v s = some J := by
  unfold rootIvl at h
  split at h
  · rename_i J' hJ'
    cases h
    obtain ⟨q, hq, hg⟩ := ir.exists_index_of_findSome? hJ'
    unfold quadRootOf at hg
    split at hg
    · rename_i m c hview
      split at hg
      · rename_i Jm hJm
        obtain ⟨r, hr⟩ := ir.exists_shiftIvl_of_boundIvl hJm
        exact ⟨.quadRoot q r, .inl ⟨q, r, rfl⟩, by
          simp only [ruleIvl, quadRootIvl, if_pos hq, hview, hr, hg]⟩
      · cases hg
    · cases hg
  · unfold rootSetIvl at h
    simp only at h
    split_ifs at h
    refine ⟨.rootSet (List.range ir.predicates.length), .inr ⟨_, rfl⟩, ?_⟩
    simp only [ruleIvl, rootSetIvlAt]
    rw [← h]
    congr 1
    unfold rootSetViews
    rw [List.filterMap_congr (g := fun q => ir.rootSetView v (ir.predicate q)) fun q hq => by
      rw [if_pos (List.mem_range.1 hq)]]
    conv_rhs => rw [← map_predicate_range, List.filterMap_map]
    rfl

/-- **`leafIvl` is one choice of justified intervals**: each of its branches is a source's rule
(`ivlAt`). -/
theorem leafIvl_justified (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) :
    ir.LeafIvlsOk primeNodes sr fun f v => ir.leafIvl primeNodes f v sr := by
  intro f v J h
  simp only at h
  unfold leafIvl at h
  by_cases hg : v < ir.values.length ∧ ir.valueField v = f ∧ f < ir.fields.length ∧ 2 < ir.charOf f
  swap
  · rw [if_neg hg] at h
    cases h
  rw [if_pos hg] at h
  obtain ⟨hv, hf, hfl, h2⟩ := hg
  have key : ∀ s, s.allows (ir.value v).kind = true → ir.ruleIvl primeNodes sr f v s = some J →
      ir.HasIvl primeNodes sr f v J := fun s ha hr =>
    ⟨s, by rw [ivlAt, if_pos ⟨hv, hf, hfl, h2, ha⟩]; exact hr⟩
  have decl : ∀ N, sr.lookup v = some N →
      (if 0 < N ∧ N ≤ ir.charOf f then some (⟨0, (N : ℤ) - 1⟩ : Ivl) else none) = some J →
      ∃ k, ir.ruleIvl primeNodes sr f v (.declared k) = some J := fun N hN hJ => by
    obtain ⟨k, hk⟩ := exists_index_of_lookup hN
    refine ⟨k, ?_⟩
    split_ifs at hJ with hc
    simp only [ruleIvl, declaredIvl, hk, true_and, if_pos hc]
    exact hJ
  have rest : ∀ k : Kind, (ir.value v).kind = k → (∀ q, IvlSource.allows k (.range q) = true) →
      IvlSource.allows k .prime = true → ir.restIvl primeNodes f v = some J →
      ir.HasIvl primeNodes sr f v J := fun k hk hr hp h => by
    obtain ⟨s, hs, hR⟩ := ir.exists_rule_of_restIvl (sr := sr) h
    refine key s ?_ hR
    rw [hk]
    rcases hs with rfl | ⟨q, rfl⟩
    exacts [hp, hr q]
  generalize hk : (ir.value v).kind = k at h
  rcases k with _ | ⟨_ | ⟨n, _ | ⟨a, as⟩⟩ | x⟩ | es | c | _ | ⟨w, sel⟩ | ⟨u, mp⟩ | u | x
  all_goals try simp only at h
  -- every kind but a constant, an opaque value and a bound value
  all_goals first
    | (split at h
       · rename_i J' hJ'
         cases h
         obtain ⟨s, hs, hR⟩ := ir.exists_rule_of_rootIvl (sr := sr) (f := f)
           (primeNodes := primeNodes)
           hJ'
         refine key s ?_ hR
         rw [hk]
         rcases hs with ⟨q, r, rfl⟩ | ⟨qs, rfl⟩ <;> rfl
       · exact rest _ hk (fun _ => rfl) rfl h)
    | skip
  · -- an opaque statement value with no arguments
    split at h
    · rename_i N hN
      obtain ⟨k, hR⟩ := decl N hN h
      exact key _ (by rw [hk]; rfl) hR
    · exact rest _ hk (fun _ => rfl) rfl h
  · -- an opaque value computed from arguments
    split_ifs at h with hb
    · exact key .opaqueBit (by rw [hk]; rfl) (by simp only [ruleIvl, if_pos hb]; exact h)
    · split at h
      · rename_i N hN
        obtain ⟨k, hR⟩ := decl N hN h
        exact key _ (by rw [hk]; rfl) hR
      · cases h
  · -- a constant
    exact key .const (by rw [hk]; rfl) (by simp only [ruleIvl, hk]; exact h)
  · -- a bound value
    obtain ⟨q, hq⟩ := ir.exists_shiftIvl_of_boundIvl h
    exact key (.shiftRange q) (by rw [hk]; rfl) (by simp only [ruleIvl]; exact hq)

/-! ## The integer form of `mod_q` -/

/-- **A `mod_0` realized in the integer form** (`assert_int_equal`) in domain `d` with sides `e`,
`e'`: the computed intervals of the sides (`exprIvl`, at the value ranges `sr`: the declared
statement bounds and the opaque functions' ranges) lie within the exported ones, the exported
span is `max(lhsHi, rhsHi) − min(lhsLo, rhsLo)` and lies below the characteristic `p > 2`. The field
equation's target is checked by `RealizedProgram.TargetsAdmit` (`BodyAdmitted`). -/
structure IntegerOk (L : ℕ → ℕ → Option Ivl) (d : ℕ) (e e' : Expr) (real : ModRealization) :
    Prop where
  /-- The integer form. -/
  form : real.form = .integer
  /-- The characteristic exceeds `2`. -/
  char : 2 < ir.charOf (ir.domainField d)
  /-- The left side's interval lies within the exported one. -/
  lhs : IvlWithin (ir.exprIvl L (ir.domainField d) e) real.lhsLo real.lhsHi
  /-- The right side's interval lies within the exported one. -/
  rhs : IvlWithin (ir.exprIvl L (ir.domainField d) e') real.rhsLo real.rhsHi
  /-- The exported span. -/
  span : real.span = some (max real.lhsHi real.rhsHi - min real.lhsLo real.rhsLo).toNat
  /-- The span lies below the characteristic. -/
  spanLt : max real.lhsHi real.rhsHi - min real.lhsLo real.rhsLo < ir.charOf (ir.domainField d)

/-! ## The complement and two digit sets -/

/-- **One step of dereferencing**: a reference to an existing shared expression is that entry. -/
def deref : Expr → Expr
  | .ref k => if k < ir.exprs.length then ir.expr k else .ref k
  | e => e

/-- **The needle `ne` is `(N − 1) − rec`** in domain `d`: (one dereference of) `top + c · rec'` with
`c = p − 1`, `top` a constant holding `N − 1`, `rec'` matching the record `rec`
(`needleMatches`), of the record's length. -/
def complementMatch (d N : ℕ) (rec ne : Expr) : Bool :=
  decide (ir.exprLen ne = ir.exprLen rec) &&
    match ir.deref ne with
    | .add (.leaf top) (.scale (.const c) rec') =>
      decide (c + 1 = ir.charOf (ir.domainField d)) && ir.needleMatches rec' rec &&
        ir.constAll top (N - 1) (ir.exprLen rec) (ir.domainField d)
    | _ => false

/-- **The reconstruction row of a two-sided lookup** in domain `d` for the record `rec`: the field
`equal` `rec' + Σ_j (p − T^j) · d_j = z`, `rec'` matching the record (`needleMatches`), `d_j` the
digit values in order (`chainOk`), `z` a constant holding `0`. -/
def reconMatch (d : ℕ) (rec : Expr) (r : LookupRealization) : PredBody → Bool
  | .equal d' L (.leaf z) _ =>
    d' == d && ir.constAll z 0 (ir.exprLen rec) (ir.domainField d) &&
      match peel r.digits L with
      | some (h, ts) =>
        ir.needleMatches h rec && chainOk (ir.charOf (ir.domainField d)) r.base 1 ts r.digitValues
      | none => false
  | _ => false

/-- **The top row of a two-sided lookup** in domain `d` for the record `rec` and the range `[0, N)`:
the field `equal` `top + (p − 1) · rec' + Σ_j (p − T^j) · h_j = z`, `top` a constant of the
record's length holding `N − 1`, `rec'` matching the record, `h_j` the second digit set in order,
`z` a constant holding `0`. -/
def topMatch (d N : ℕ) (rec : Expr) (r : LookupRealization) : PredBody → Bool
  | .equal d' L (.leaf z) _ =>
    d' == d && ir.constAll z 0 (ir.exprLen rec) (ir.domainField d) &&
      match peel r.digits L with
      | some (.add (.leaf top) (.scale (.const c) rec'), ts) =>
        decide (c + 1 = ir.charOf (ir.domainField d)) && ir.needleMatches rec' rec &&
          chainOk (ir.charOf (ir.domainField d)) r.base 1 ts r.second &&
          ir.constAll top (N - 1) (ir.exprLen rec) (ir.domainField d) &&
          decide ((ir.value top).size = ir.exprLen rec)
      | _ => false
  | _ => false

/-- **The record `rec` is a value bound to the digits of `r`** in domain `d`: `rec` is a value `v` of
the program, of the domain's field, bound to the number of the digit values `d_j` in base `T`
(`digitsExprOk`), so it has no reconstruction row; or `rec` is `v + c` for a value `v` of the
domain's field bound to that number minus `c` (`x + (p − 1) · c`, a request on `v + c`,
`RangePolicy::bind_digit_views`, compiler/range.h). The realized assignment reads `v` through its
digits (`RealizedProgram.bindAsg`). Or `rec` is a shared expression whose entry is the digits' number (a
committed-digits quotient `d_0 + T d_1 + …`, compiler/mod.h). -/
def boundDigitsOk (d : ℕ) (rec : Expr) (r : LookupRealization) : Bool :=
  match rec with
  | .leaf v =>
    decide (v < ir.values.length) && decide (ir.valueField v = ir.domainField d) &&
      match (ir.value v).kind with
      | .bound x => digitsExprOk (ir.charOf (ir.domainField d)) r.base x r.digitValues
      | _ => false
  | .add (.leaf v) (.leaf u) =>
    decide (v < ir.values.length) && decide (ir.valueField v = ir.domainField d) &&
      match (ir.value v).kind with
      | .bound (.add x (.scale (.const c) (.leaf u'))) =>
        u' == u && decide (c + 1 = ir.charOf (ir.domainField d)) &&
          digitsExprOk (ir.charOf (ir.domainField d)) r.base x r.digitValues
      | _ => false
  | .ref k =>
    decide (k < ir.exprs.length) &&
      digitsExprOk (ir.charOf (ir.domainField d)) r.base (ir.expr k) r.digitValues
  | _ => false

/-- **A two-sided lookup** of predicate `pid` in domain `d` with records `recs` into the set `set`
`[0, N)`, `N ≤ p`: the table exists and is of the domain, of `T` rows for the base `T`; one record
`v`; the needles the `k` digit values `d_j`, then the `k` values `h_j` (`range.<r>.d<j>`,
`range.<r>.h<j>`), each of the record's length in the domain's field; `v = Σ_j T^j d_j`, by the
reconstruction row `v − Σ_j T^j d_j = 0` among the predicates (`reconMatch`) or by `v` being bound
to its digits (`boundDigitsOk`); the top row `(N − 1) − v − Σ_j T^j h_j = 0` among the predicates
(`topMatch`); `T > 1`, `2 (T^k − 1) < p` and `p > 2`; the members of the table's groups tile every
needle's coordinates. -/
structure TwoSidedOk (pid d : ℕ) (recs : List Expr) (set : InSet) (r : LookupRealization) :
    Prop where
  /-- The table exists. -/
  table : r.table < ir.tables.length
  /-- The table is of the domain. -/
  domain : d = (ir.table r.table).domain
  /-- The table is a range. -/
  rangeTable : ir.IsRange r.table
  /-- One record. -/
  single : recs.length = 1
  /-- The set is a range. -/
  range : set = .range set.bound
  /-- The range is nonempty. -/
  pos : 0 < set.bound
  /-- The base is the table's size. -/
  base : r.base = ir.tableSize r.table
  /-- The base exceeds `1`. -/
  baseGt : 1 < r.base
  /-- `k` digits in each set. -/
  digitsLen : r.digitValues.length = r.digits ∧ r.second.length = r.digits
  /-- The range lies within the characteristic. -/
  rangeLe : set.bound ≤ ir.charOf (ir.domainField d)
  /-- The needles are the digit values. -/
  needles : Expr.beqList r.needles ((r.digitValues ++ r.second).map .leaf) = true
  /-- The digit values have the record's length, in the domain's field. -/
  sizes : ∀ u ∈ r.digitValues ++ r.second,
    (ir.value u).size = ir.exprLen (recs.headD default) ∧ ir.valueField u = ir.domainField d
  /-- The record is the number of its digits: a reconstruction row, or bound to its digits. -/
  recon : (ir.predicates.any (fun q => ir.reconMatch d (recs.headD default) r q.body) ||
    ir.boundDigitsOk d (recs.headD default) r) = true
  /-- The top row. -/
  top : ir.predicates.any (fun q => ir.topMatch d set.bound (recs.headD default) r q.body) = true
  /-- The characteristic exceeds `2`. -/
  char : 2 < ir.charOf (ir.domainField d)
  /-- The two digit numbers' sum stays below the characteristic. -/
  fits : 2 * (r.base ^ r.digits - 1) < ir.charOf (ir.domainField d)
  /-- The members tile every needle's coordinates. -/
  covered : ∀ n < r.needles.length,
    tiles (ir.coverRuns r.table pid n) 0 (ir.exprLen (r.needles.getD n default)) = true

theorem twoSidedOk_iff (pid d : ℕ) (recs : List Expr) (set : InSet) (r : LookupRealization) :
    ir.TwoSidedOk pid d recs set r ↔
      r.table < ir.tables.length ∧ d = (ir.table r.table).domain ∧ ir.IsRange r.table ∧
        recs.length = 1 ∧ set = .range set.bound ∧ 0 < set.bound ∧
        r.base = ir.tableSize r.table ∧ 1 < r.base ∧
        (r.digitValues.length = r.digits ∧ r.second.length = r.digits) ∧
        set.bound ≤ ir.charOf (ir.domainField d) ∧
        Expr.beqList r.needles ((r.digitValues ++ r.second).map .leaf) = true ∧
        (∀ u ∈ r.digitValues ++ r.second,
          (ir.value u).size = ir.exprLen (recs.headD default) ∧
            ir.valueField u = ir.domainField d) ∧
        (ir.predicates.any (fun q => ir.reconMatch d (recs.headD default) r q.body) ||
          ir.boundDigitsOk d (recs.headD default) r) = true ∧
        ir.predicates.any (fun q => ir.topMatch d set.bound (recs.headD default) r q.body) =
          true ∧
        2 < ir.charOf (ir.domainField d) ∧
        2 * (r.base ^ r.digits - 1) < ir.charOf (ir.domainField d) ∧
        ∀ n < r.needles.length,
          tiles (ir.coverRuns r.table pid n) 0 (ir.exprLen (r.needles.getD n default)) = true :=
  ⟨fun h => ⟨h.table, h.domain, h.rangeTable, h.single, h.range, h.pos, h.base, h.baseGt,
      h.digitsLen, h.rangeLe, h.needles, h.sizes, h.recon, h.top, h.char, h.fits, h.covered⟩,
    fun ⟨h1, h2, h2', h3, h4, h5, h6, h6', h6'', h6''', h7, h8, h9, h10, h11, h12, h13⟩ =>
      ⟨h1, h2, h2', h3, h4, h5, h6, h6', h6'', h6''', h7, h8, h9, h10, h11, h12, h13⟩⟩

instance (pid d : ℕ) (recs : List Expr) (set : InSet) (r : LookupRealization) :
    Decidable (ir.TwoSidedOk pid d recs set r) :=
  decidable_of_iff _ (ir.twoSidedOk_iff pid d recs set r).symm

/-! ## Digit lookups -/

/-- **A digit lookup** of predicate `pid` in domain `d` with records `recs` into the set `set`
`[0, N)`: the table exists and is of the domain, of `T` rows for the base `T > 1`; one record `v`,
the number of its `k` digit values `d_j`, by the reconstruction row `v − Σ_j T^j d_j = 0` among the
predicates (`reconMatch`) or by `v` being bound to its digits (`boundDigitsOk`: `v = Σ_j T^j d_j` in
the realized assignment); the needles the digit values (`range.<r>.d<j>`), each of the record's
length in the domain's field; `T^k ≤ N`; the members of the table's groups tile every needle's
coordinates. Each digit in the table makes `v` a natural below `T^k ≤ N`; the digits' number needs
no bound by the characteristic, as it is read as a natural below `T^k` before it is cast. -/
structure DigitsOk (pid d : ℕ) (recs : List Expr) (set : InSet) (r : LookupRealization) :
    Prop where
  /-- The table exists. -/
  table : r.table < ir.tables.length
  /-- The table is of the domain. -/
  domain : d = (ir.table r.table).domain
  /-- The table is a range. -/
  rangeTable : ir.IsRange r.table
  /-- One record. -/
  single : recs.length = 1
  /-- The set is a range. -/
  range : set = .range set.bound
  /-- The base is the table's size. -/
  base : r.base = ir.tableSize r.table
  /-- The base exceeds `1`. -/
  baseGt : 1 < r.base
  /-- `k` digits. -/
  digitsLen : r.digitValues.length = r.digits
  /-- The digits' numbers lie below the range's bound. -/
  le : r.base ^ r.digits ≤ set.bound
  /-- The needles are the digit values. -/
  needles : Expr.beqList r.needles (r.digitValues.map .leaf) = true
  /-- The digit values have the record's length, in the domain's field. -/
  sizes : ∀ u ∈ r.digitValues,
    (ir.value u).size = ir.exprLen (recs.headD default) ∧ ir.valueField u = ir.domainField d
  /-- The record is the number of its digits: a reconstruction row, or bound to its digits. -/
  recon : (ir.predicates.any (fun q => ir.reconMatch d (recs.headD default) r q.body) ||
    ir.boundDigitsOk d (recs.headD default) r) = true
  /-- The members tile every needle's coordinates. -/
  covered : ∀ n < r.needles.length,
    tiles (ir.coverRuns r.table pid n) 0 (ir.exprLen (r.needles.getD n default)) = true

theorem digitsOk_iff (pid d : ℕ) (recs : List Expr) (set : InSet) (r : LookupRealization) :
    ir.DigitsOk pid d recs set r ↔
      r.table < ir.tables.length ∧ d = (ir.table r.table).domain ∧ ir.IsRange r.table ∧
        recs.length = 1 ∧ set = .range set.bound ∧
        r.base = ir.tableSize r.table ∧ 1 < r.base ∧ r.digitValues.length = r.digits ∧
        r.base ^ r.digits ≤ set.bound ∧
        Expr.beqList r.needles (r.digitValues.map .leaf) = true ∧
        (∀ u ∈ r.digitValues,
          (ir.value u).size = ir.exprLen (recs.headD default) ∧
            ir.valueField u = ir.domainField d) ∧
        (ir.predicates.any (fun q => ir.reconMatch d (recs.headD default) r q.body) ||
          ir.boundDigitsOk d (recs.headD default) r) = true ∧
        ∀ n < r.needles.length,
          tiles (ir.coverRuns r.table pid n) 0 (ir.exprLen (r.needles.getD n default)) = true :=
  ⟨fun h => ⟨h.table, h.domain, h.rangeTable, h.single, h.range, h.base, h.baseGt, h.digitsLen,
      h.le, h.needles, h.sizes, h.recon, h.covered⟩,
    fun ⟨h1, h2, h2', h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ =>
      ⟨h1, h2, h2', h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩⟩

instance (pid d : ℕ) (recs : List Expr) (set : InSet) (r : LookupRealization) :
    Decidable (ir.DigitsOk pid d recs set r) :=
  decidable_of_iff _ (ir.digitsOk_iff pid d recs set r).symm

/-! ## The one-digit form of `mod_q` -/

/-- **An expression as a linear form** `c + Σ_j a_j · t_j` over the integers, read in field `f` at
its first `n` coordinates: sums, differences and constant multiples (by constants below the
characteristic) are expanded, a constant leaf holding one entry below the characteristic at its
first `n` coordinates (`constEntry`) is that constant, and any other expression is a term of
coefficient `1`; `none` where a multiple's constant reaches the characteristic. -/
def linForm (f n : ℕ) : Expr → Option (ℤ × List (ℤ × Expr))
  | .add a b => (linForm f n a).bind fun x => (linForm f n b).map fun y =>
      (x.1 + y.1, x.2 ++ y.2)
  | .sub a b => (linForm f n a).bind fun x => (linForm f n b).map fun y =>
      (x.1 - y.1, x.2 ++ y.2.map fun t => (-t.1, t.2))
  | .scale (.const k) a =>
      if k < ir.charOf f then
        (linForm f n a).map fun x => ((k : ℤ) * x.1, x.2.map fun t => ((k : ℤ) * t.1, t.2))
      else none
  | .leaf v =>
      match ir.constEntry v n f with
      | some c => some ((c : ℤ), [])
      | none => some (0, [(1, .leaf v)])
  | e => some (0, [(1, e)])

/-- **A linear form vanishes modulo `p`**: its constant is divisible by `p`, and so is the sum of
the coefficients of the terms equal to each term. -/
def linZeroB (p : ℕ) (x : ℤ × List (ℤ × Expr)) : Bool :=
  x.1 % p == 0 &&
    x.2.all fun t => ((x.2.filter fun u => u.2.beq t.2).map (·.1)).sum % p == 0

/-- **The quotient of a `mod_q` is derived from its sides** in domain `d` with characteristic `p`
(compiler/mod.h, `quotient`: `Q = q⁻¹ · (e − e' − q · qlo)`, in any arrangement of its terms): `q`
is invertible modulo `p`, and the linear form (`linForm`, at the left side's length) of
`q · Q − e + e' + q · qlo`, with `Q` the quotient (one dereference of it), vanishes modulo `p`
(`linZeroB`). Then `e − e' = q · (qlo + Q)` in the field (`RealizedProgram.fieldEq_of_quotDerived`). -/
def quotDerivedB (d q : ℕ) (e e' : Expr) (real : ModRealization) : Bool :=
  decide (q % ir.charOf (ir.domainField d) ≠ 0) &&
    match ir.linForm (ir.domainField d) (ir.exprLen e) (ir.deref real.quotExpr),
      ir.linForm (ir.domainField d) (ir.exprLen e) e,
      ir.linForm (ir.domainField d) (ir.exprLen e) e' with
    | some xQ, some x, some x' =>
      linZeroB (ir.charOf (ir.domainField d))
        ((q : ℤ) * xQ.1 - x.1 + x'.1 + q * real.quotientLo,
          xQ.2.map (fun t => ((q : ℤ) * t.1, t.2)) ++ x.2.map (fun t => (-t.1, t.2)) ++ x'.2)
    | _, _, _ => false

/-- **Predicate `rid` bounds the quotient of a `mod_q` in domain `d` without wrapping** (the left
side `e`): a direct `in` `Q' ∈ [0, N)` of domain `d` with `Q'` the quotient, of the left side's
length, `0 < N`, and `q (N − 1) + q · qlo + rhsHi − lhsLo < p` (the right half of the no-wrap
condition: `e − e' − q (qlo + Q)` lies above `−p`). -/
def quotRangeB (d q : ℕ) (e : Expr) (real : ModRealization) (rid : ℕ) : Bool :=
  decide (rid < ir.predicates.length) &&
    match (ir.predicate rid).body with
    | .mem d' [Q'] (.range N) (.lookup r) =>
      decide (d' = d) && decide (r.kind = .direct) && Q'.beq real.quotExpr &&
        decide (ir.exprLen Q' = ir.exprLen e) && decide (0 < N) &&
        decide (((q * (N - 1) : ℕ) : ℤ) + q * real.quotientLo + real.rhsHi - real.lhsLo <
          ir.charOf (ir.domainField d))
    | _ => false

/-- **The accumulator row's left side** `acc + (p − 1)·t_0 + (p − 1)·t_1 + …` for the left side
`e = t_0 + t_1 + …` (left-nested on both sides), at the characteristic `p`: its value is
`acc − e` (`RealizedProgram.evalE_of_accTerms`). -/
def accTerms (p acc : ℕ) : Expr → Expr → Bool
  | .add L (.scale (.const c) t), .add e₁ e₂ => c + 1 == p && t.beq e₂ && accTerms p acc L e₁
  | .add (.leaf a) (.scale (.const c) t), e => a == acc && c + 1 == p && t.beq e
  | _, _ => false

/-- **Value `acc` commits the left side `e`** in domain `d` (compiler/mod.h, `one_group`: the
accumulator of a side no circuit reads): `acc` is a value of the domain's field of `e`'s length, and
a field `equal` of domain `d` states `acc + (p − 1)·t_0 + … = z` for `e = t_0 + …` (`accTerms`) and
`z` a constant holding `0`; or `acc` is `e` itself. -/
def accRowB (d acc : ℕ) (e : Expr) : Bool :=
  (Expr.leaf acc).beq e ||
    decide (acc < ir.values.length) && decide (ir.valueField acc = ir.domainField d) &&
      decide ((ir.value acc).size = ir.exprLen e) &&
      ir.predicates.any fun q =>
        match q.body with
        | .equal d' L (.leaf z) _ =>
          d' == d && ir.constAll z 0 (ir.exprLen e) (ir.domainField d) &&
            accTerms (ir.charOf (ir.domainField d)) acc L e
        | _ => false

/-- **The quotient of a `mod_q` is derived from an accumulator of its left side** in domain `d`
(compiler/mod.h, `quotient` on the accumulator `acc` of a side no circuit reads, `accRowB`):
`qlo = 0` and (one dereference of) the quotient is `a · acc + b · e'` with constants `a, b < p`,
`q · a ≡ 1` and `q · b ≡ −1` modulo `p`, `acc` committing `e`. Then `e − e' = q · Q` in the field
where the accumulator row holds. -/
def quotDerivedAccB (d q : ℕ) (e e' : Expr) (real : ModRealization) : Bool :=
  decide (real.quotientLo = 0) &&
    match ir.deref real.quotExpr with
    | .add (.scale (.const a) (.leaf acc)) (.scale (.const b) e₂) =>
      ir.accRowB d acc e && e₂.beq e' && decide (a < ir.charOf (ir.domainField d)) &&
        decide (b < ir.charOf (ir.domainField d)) &&
        decide (q * a % ir.charOf (ir.domainField d) = 1) &&
        decide ((q * b + 1) % ir.charOf (ir.domainField d) = 0)
    | _ => false

/-- **The accumulator of a one-digit `mod_q`** whose quotient is derived from it
(`quotDerivedAccB`), read off the quotient (`0` when it has none). -/
def oneDigitAcc (real : ModRealization) : ℕ :=
  match ir.deref real.quotExpr with
  | .add (.scale (.const _) (.leaf acc)) (.scale (.const _) _) => acc
  | _ => 0

/-- **A `mod_q` realized in the one-digit form** (compiler/mod.h, `kOneDigit`) in domain `d` with
sides `e`, `e'`: `q > 0`, `p > 2`; the quotient is derived from the sides (`quotDerivedB`) or, with
`qlo = 0`, from an accumulator of the left side (`quotDerivedAccB`), so `e − e' = q · (qlo + Q)`
in the field; the computed intervals of the sides (`exprIvl`) lie within the exported ones; the
no-wrap conditions `lhsHi − rhsLo − q · qlo < p` and, through the quotient's direct `in`
`Q ∈ [0, N)` among the exported ranges, `q (N − 1) + q · qlo + rhsHi − lhsLo < p` (`quotRangeB`).
The field equation then lifts to `e − e' = q · (qlo + Q)` over the integers. -/
structure OneDigitOk (L : ℕ → ℕ → Option Ivl) (d q : ℕ) (e e' : Expr)
    (real : ModRealization) : Prop where
  /-- The one-digit form. -/
  form : real.form = .oneDigit
  /-- The modulus is positive. -/
  qpos : 0 < q
  /-- The characteristic exceeds `2`. -/
  char : 2 < ir.charOf (ir.domainField d)
  /-- The quotient is derived from the sides, or from an accumulator of the left side. -/
  derived : ir.quotDerivedB d q e e' real = true ∨ ir.quotDerivedAccB d q e e' real = true
  /-- The left side's interval lies within the exported one. -/
  lhs : IvlWithin (ir.exprIvl L (ir.domainField d) e) real.lhsLo real.lhsHi
  /-- The right side's interval lies within the exported one. -/
  rhs : IvlWithin (ir.exprIvl L (ir.domainField d) e') real.rhsLo real.rhsHi
  /-- The left half of the no-wrap condition. -/
  noWrap : real.lhsHi - real.rhsLo - q * real.quotientLo < ir.charOf (ir.domainField d)
  /-- A direct `in` bounds the quotient, with the right half of the no-wrap condition. -/
  range : real.ranges.any (ir.quotRangeB d q e real) = true

/-! ## The digit form of `mod_q` -/

/-- **The top digit of a `mod_q` is derived** in domain `d` with the left side committed by `acc`
(compiler/mod.h, `digits`: `top = (q B^{k−1})⁻¹ · (acc − e' − Σ_{j<k−1} q B^j d_j)`): `qlo = 0`, the
digits are the lower digits `d_j` (values, `k − 1 ≥ 1` of them) then the top, and (one dereference
of) the top is `a · acc + b · e' + Σ_j c_j · d_j` (left-nested, `peel`) with constants below the
characteristic `p`, `P a ≡ 1`, `P b ≡ −1` and `P c_j + q B^j ≡ 0` modulo `p` for `P = q B^{k−1}`.
Then `q · Σ_j B^j d_j = acc − e'` in the field (`RealizedProgram.fieldEq_of_topDerived`). -/
def topDerivedB (d q : ℕ) (e' : Expr) (real : ModRealization) (acc : ℕ) : Bool :=
  decide (real.quotientLo = 0) &&
    match real.digits.reverse with
    | top :: lowerRev =>
      let lower := lowerRev.reverse
      let p := ir.charOf (ir.domainField d)
      let P := q * real.radix ^ lower.length
      decide (0 < lower.length) &&
      match peel lower.length (ir.deref top) with
      | some (.add (.scale (.const a) (.leaf acc')) (.scale (.const b) e₂), ts) =>
        acc' == acc && e₂.beq e' && decide (a < p) && decide (b < p) &&
          decide (P * a % p = 1) && decide ((P * b + 1) % p = 0) &&
          Expr.beqList lower (ts.map fun cu => .leaf cu.2) &&
          (ts.zipIdx.all fun cuj => decide (cuj.1.1 < p) &&
            decide ((P * cuj.1.1 + q * real.radix ^ cuj.2) % p = 0))
      | _ => false
    | [] => false

/-- **Predicate `rid` bounds digit `D` of a `mod_q` in domain `d`** (the left side `e`): a direct
`in` `D' ∈ [0, N)` of domain `d` with `D'` the digit, of the left side's length, `0 < N`; its bound
`N`. -/
def digitRangeOf (d : ℕ) (e D : Expr) (rid : ℕ) : Option ℕ :=
  if rid < ir.predicates.length then
    match (ir.predicate rid).body with
    | .mem d' [D'] (.range N) (.lookup r) =>
      if d' = d ∧ r.kind = .direct ∧ D'.beq D = true ∧ ir.exprLen D' = ir.exprLen e ∧ 0 < N then
        some N
      else none
    | _ => none
  else none

/-- **The bounds of a `mod_q`'s digits** in domain `d`: digit `j` bounded by the `j`-th of the
ranges (`digitRangeOf`), one range per digit; none when one is missing. -/
def digitBounds (d : ℕ) (e : Expr) (real : ModRealization) : Option (List ℕ) :=
  if real.digits.length = real.ranges.length then
    (real.digits.zip real.ranges).mapM fun Dr => ir.digitRangeOf d e Dr.1 Dr.2
  else none

/-- **The largest quotient of digits below their bounds** `N_j` in base `B`: `Σ_j B^j (N_j − 1)`. -/
def digitsMax (B : ℕ) : List ℕ → ℕ
  | [] => 0
  | n :: N => (n - 1) + B * digitsMax B N

/-- **The accumulator of a `mod_q` in the digit form**: the value of the derived top digit's
accumulator term (`topDerivedB`), read off the top digit (`0` when it has none). -/
def digitsAcc (real : ModRealization) : ℕ :=
  match real.digits.reverse with
  | top :: lowerRev =>
    match peel lowerRev.reverse.length (ir.deref top) with
    | some (.add (.scale (.const _) (.leaf acc)) _, _) => acc
    | _ => 0
  | [] => 0

/-- **The digits' bounds of a `mod_q`** in domain `d` (`digitBounds`; empty when one is missing). -/
def digitsN (d : ℕ) (e : Expr) (real : ModRealization) : List ℕ := (ir.digitBounds d e real).getD []

/-- **A `mod_q` realized in the digit form** (compiler/mod.h, `kDigits`) in domain `d` with sides
`e`, `e'`: `q > 0`, `p > 2`; the left side committed by the accumulator read off the top digit
(`digitsAcc`, `accRowB`); the top digit derived (`topDerivedB`), so `e − e' = q · Σ_j B^j d_j` in
the field; each digit bounded by a direct `in` `d_j ∈ [0, N_j)` among the exported ranges
(`digitBounds`, `digitsN`); the computed intervals of the sides within the exported ones; and the
no-wrap conditions `lhsHi − rhsLo < p` and `q · Σ_j B^j (N_j − 1) + rhsHi − lhsLo < p`. The field
equation then lifts to `e − e' = q · Σ_j B^j d_j` over the integers. -/
structure DigitsFormOk (L : ℕ → ℕ → Option Ivl) (d q : ℕ) (e e' : Expr)
    (real : ModRealization) : Prop where
  /-- The digit form. -/
  form : real.form = .digits
  /-- The modulus is positive. -/
  qpos : 0 < q
  /-- The characteristic exceeds `2`. -/
  char : 2 < ir.charOf (ir.domainField d)
  /-- The accumulator commits the left side. -/
  acc : ir.accRowB d (ir.digitsAcc real) e = true
  /-- The top digit is derived. -/
  derived : ir.topDerivedB d q e' real (ir.digitsAcc real) = true
  /-- Every digit is bounded. -/
  bounds : ir.digitBounds d e real = some (ir.digitsN d e real)
  /-- The left side's interval lies within the exported one. -/
  lhs : IvlWithin (ir.exprIvl L (ir.domainField d) e) real.lhsLo real.lhsHi
  /-- The right side's interval lies within the exported one. -/
  rhs : IvlWithin (ir.exprIvl L (ir.domainField d) e') real.rhsLo real.rhsHi
  /-- The left half of the no-wrap condition. -/
  noWrap : real.lhsHi - real.rhsLo < ir.charOf (ir.domainField d)
  /-- The right half of the no-wrap condition. -/
  noWrapDigits : ((q * digitsMax real.radix (ir.digitsN d e real) : ℕ) : ℤ) + real.rhsHi -
    real.lhsLo < ir.charOf (ir.domainField d)

/-- **The bound of a direct `in` on the expression `e`** in domain `d`, in predicate `q`: `N` for a
direct `in` `[e'] ∈ [0, N)` of domain `d` with `e'` structurally `e` and `0 < N`. -/
def exprRangeOf (d : ℕ) (e : Expr) (q : Predicate) : Option ℕ :=
  match q.body with
  | .mem d' [e'] (.range N) (.lookup r) =>
    if d' = d ∧ r.kind = .direct ∧ e'.beq e = true ∧ 0 < N then some N else none
  | _ => none

/-- **The bound of a direct `in` on the expression `e`** in domain `d`: the first
(`exprRangeOf`). -/
def exprRange (d : ℕ) (e : Expr) : Option ℕ := ir.predicates.findSome? (exprRangeOf d e)

/-- **The index map of the MAC powers**: entry `c · nch + t` is `0` (the key) for `t ≤ c` and `1`
(the constant one) otherwise, so the products of `nch` consecutive entries of
`reindex · (concat key one)` are `β^(c+1)`. -/
def powersMap (nch : ℕ) : List ℕ :=
  (List.range (nch * nch)).map fun i => if i % nch ≤ i / nch then 0 else 1

/-- **Two index maps have the same entries**, run by run, in `n` steps: empty runs are dropped; of
two head runs `(s, d, c + 1)`, `(s', d', c' + 1)` with `s = s'` (and `d = d'` past one entry), the
shorter is split off both, the remainder `(s + d k, d, …)` of the longer starting at a natural. -/
def IndexMap.sameB : ℕ → IndexMap → IndexMap → Bool
  | 0, _, _ => false
  | _ + 1, [], [] => true
  | n + 1, (_, _, 0) :: m, m' => IndexMap.sameB n m m'
  | n + 1, m, (_, _, 0) :: m' => IndexMap.sameB n m m'
  | n + 1, (s, d, c + 1) :: m, (s', d', c' + 1) :: m' =>
    s == s' && (min c c' == 0 || d == d') &&
      if c ≤ c' then
        if c = c' then IndexMap.sameB n m m'
        else decide (0 ≤ (s' : ℤ) + d' * (c + 1 : ℕ)) &&
          IndexMap.sameB n m ((((s' : ℤ) + d' * (c + 1 : ℕ)).toNat, d', c' - c) :: m')
      else decide (0 ≤ (s : ℤ) + d * (c' + 1 : ℕ)) &&
        IndexMap.sameB n ((((s : ℤ) + d * (c' + 1 : ℕ)).toNat, d, c - c') :: m) m'
  | _ + 1, _, _ => false

/-- The entries of a run and the rest. -/
theorem IndexMap.toList_cons (s : ℕ) (d : ℤ) (c : ℕ) (m : IndexMap) :
    IndexMap.toList ((s, d, c) :: m) =
      (List.range c).map (fun t : ℕ => ((s : ℤ) + d * t).toNat) ++ IndexMap.toList m := by
  simp [IndexMap.toList]

/-- **A run splits after `k` entries**, the rest starting at a natural. -/
theorem IndexMap.range_split (s : ℕ) (d : ℤ) {k r : ℕ} (h : 0 ≤ (s : ℤ) + d * k) :
    (List.range (k + r)).map (fun t : ℕ => ((s : ℤ) + d * t).toNat) =
      (List.range k).map (fun t : ℕ => ((s : ℤ) + d * t).toNat) ++
        (List.range r).map (fun t : ℕ => (((((s : ℤ) + d * k).toNat : ℕ) : ℤ) + d * t).toNat) := by
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp, Int.toNat_of_nonneg h]
  congr 1
  push_cast
  ring

/-- **Two runs agree on their first `k` entries** when they start alike and, past one entry,
step alike. -/
theorem IndexMap.range_prefix {s : ℕ} {d d' : ℤ} {k : ℕ} (h : k ≤ 1 ∨ d = d') :
    (List.range k).map (fun t : ℕ => ((s : ℤ) + d * t).toNat) =
      (List.range k).map (fun t : ℕ => ((s : ℤ) + d' * t).toNat) := by
  rcases h with h | rfl
  · refine List.map_congr_left fun t ht => ?_
    have : t = 0 := by simp at ht; omega
    subst this
    simp
  · rfl

/-- **`sameB` decides equal entries** (one direction: equal entries when it accepts). -/
theorem IndexMap.toList_of_sameB : ∀ (n : ℕ) (m m' : IndexMap), IndexMap.sameB n m m' = true →
    m.toList = m'.toList
  | 0, _, _, h => by simp [IndexMap.sameB] at h
  | n + 1, [], [], _ => rfl
  | n + 1, (s, d, 0) :: m, m', h => by
    simp only [IndexMap.sameB] at h
    rw [IndexMap.toList_cons, IndexMap.toList_of_sameB n m m' h]
    simp
  | n + 1, [], (s', d', 0) :: m', h => by
    simp only [IndexMap.sameB] at h
    rw [IndexMap.toList_cons, ← IndexMap.toList_of_sameB n [] m' h]
    simp
  | n + 1, (s, d, c + 1) :: m, (s', d', 0) :: m', h => by
    simp only [IndexMap.sameB] at h
    rw [IndexMap.toList_cons (c := 0), ← IndexMap.toList_of_sameB n _ m' h]
    simp
  | n + 1, [], (_, _, _ + 1) :: _, h => by simp [IndexMap.sameB] at h
  | n + 1, (_, _, _ + 1) :: _, [], h => by simp [IndexMap.sameB] at h
  | n + 1, (s, d, c + 1) :: m, (s', d', c' + 1) :: m', h => by
    simp only [IndexMap.sameB, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
    obtain ⟨⟨rfl, hd⟩, h⟩ := h
    have hk : ∀ k, k ≤ min c c' + 1 → k ≤ 1 ∨ d = d' := fun k hk => by
      rcases hd with hd | hd
      · left
        omega
      · exact .inr hd
    rw [IndexMap.toList_cons, IndexMap.toList_cons]
    split_ifs at h with hle heq
    · subst heq
      rw [IndexMap.toList_of_sameB n m m' h, IndexMap.range_prefix (hk (c + 1) (by omega))]
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hnn, h⟩ := h
      rw [IndexMap.toList_of_sameB n _ _ h, IndexMap.toList_cons,
        show c' + 1 = (c + 1) + (c' - c) by omega, IndexMap.range_split s d' hnn,
        IndexMap.range_prefix (hk (c + 1) (by omega)), List.append_assoc]
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hnn, h⟩ := h
      rw [← IndexMap.toList_of_sameB n _ _ h, IndexMap.toList_cons,
        show c + 1 = (c' + 1) + (c - c') by omega, IndexMap.range_split s d hnn,
        IndexMap.range_prefix (hk (c' + 1) (by omega)), List.append_assoc]

/-- **The runs of the MAC powers map** (`powersMap`): row `c < nch` reads `c + 1` zeros (the key)
then `nch − c − 1` ones. -/
def powersRuns (nch : ℕ) : IndexMap :=
  (List.range nch).flatMap fun c => [(0, 0, c + 1), (1, 0, nch - c - 1)]

theorem toList_powersRuns (nch : ℕ) : (powersRuns nch).toList = powersMap nch := by
  have hrow : ∀ c < nch, (List.range nch).map (fun t => if t ≤ c then 0 else 1) =
      IndexMap.toList [(0, 0, c + 1), (1, 0, nch - c - 1)] := by
    intro c hc
    rw [IndexMap.toList_cons, IndexMap.toList_cons, show IndexMap.toList [] = [] from rfl,
      List.append_nil]
    refine List.ext_getElem (by simp; omega) fun t h1 h2 => ?_
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_range]
    by_cases ht : t ≤ c
    · rw [if_pos ht, List.getElem_append_left (by simp; omega)]
      simp
    · rw [if_neg ht, List.getElem_append_right (by simp; omega)]
      simp
  have hk : ∀ k ≤ nch, (List.range (k * nch)).map
      (fun i => if i % nch ≤ i / nch then 0 else 1) =
        IndexMap.toList ((List.range k).flatMap fun c => [(0, 0, c + 1), (1, 0, nch - c - 1)]) := by
    intro k
    induction k with
    | zero => intro _; simp [IndexMap.toList]
    | succ k ih =>
      intro hkn
      rw [Nat.succ_mul, List.range_add, List.map_append, ih (by omega), List.range_succ,
        List.flatMap_append, List.flatMap_singleton]
      simp only [IndexMap.toList, List.flatMap_append]
      congr 1
      rw [List.map_map]
      have := hrow k (by omega)
      simp only [IndexMap.toList] at this
      rw [← this]
      refine List.map_congr_left fun t ht => ?_
      simp only [List.mem_range] at ht
      simp only [Function.comp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
      rw [show (k * nch + t) / nch = k by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt ht, Nat.zero_add]]
      rw [show (k * nch + t) % nch = t by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]]
  unfold powersMap powersRuns
  rw [hk nch le_rfl]

/-- **Value `r` holds the MAC powers** `r_c = β^(c+1)`, `c < nch`, of challenge `key`
(`<mac>.powers`), in field `f`: the public expression
`prod nch (reindex idx (concat (leaf kv) (leaf one)))` with `idx` the powers map (`powersMap`,
checked run by run against `powersRuns`), `kv`
the key's value (one coordinate) and `one` a constant holding `1`, all of field `f`, the key's
field. -/
def powersB (r key nch f : ℕ) : Bool :=
  decide (r < ir.values.length) && decide (ir.valueField r = f) && decide (ir.chalField key = f) &&
    match (ir.value r).kind with
    | .pub (.expr (.prod n (.reindex idx (.concat (.leaf kv) (.leaf one))))) =>
      n == nch &&
        IndexMap.sameB (idx.length + (powersRuns nch).length + 1) idx (powersRuns nch) &&
        decide (kv < ir.values.length) &&
        decide ((ir.value kv).size = 1) && decide (ir.valueField kv = f) &&
        (match (ir.value kv).kind with
          | .challenge c => c == key
          | _ => false) &&
        ir.constAll one 1 1 f
    | _ => false

/-! ## The grouped form of `mod_q` -/

/-- **The entries `s, s + 1, …, s + n − 1`** of an index map of one run. -/
def runList (s n : ℕ) : List ℕ := (List.range n).map (s + ·)

/-- **A left side in the MAC unit form** `b + macConv(r, w, nch, taps)(y)` (compiler/mac.h, the MAC's
tail): the blind `b` (unit `0`) and the convolution's `nch` chunks (units `1, …, nch`). -/
structure MacUnits where
  /-- The blind. -/
  blind : ℕ
  /-- The powers. -/
  powers : ℕ
  /-- The chunk width. -/
  width : ℕ
  /-- The number of chunks. -/
  chunks : ℕ
  /-- The reduction taps. -/
  taps : List ℕ
  /-- The A operand. -/
  operand : Expr

/-- **The units of a left side in the MAC unit form** (`MacUnits`); `none` for any other form. -/
def macUnits? : Expr → Option MacUnits
  | .add (.leaf b) (.apply (.macConv r w nch taps) y) => some ⟨b, r, w, nch, taps, y⟩
  | _ => none

/-- **The chunk runs of a grouping**: group `(first, count)` of units covers the chunks
`[first − 1, first − 1 + count)` (unit `0` is the blind). -/
def _root_.GordieHowe.RealizedProgram.GroupedMod.chunkRuns (G : GroupedMod) : List (ℕ × ℕ) :=
  G.groups.map fun fc => (fc.1 - 1, fc.2)

/-- **Value `r` holds the powers `β^(c+1)`, `c < nch`, of some MAC key** (`powersB` at the key the
public expression reads), in a field of the program of characteristic above `1`. -/
def macPowersB (r nch : ℕ) : Bool :=
  decide (ir.valueField r < ir.fields.length) && decide (1 < ir.charOf (ir.valueField r)) &&
    match (ir.value r).kind with
    | .pub (.expr (.prod _ (.reindex _ (.concat (.leaf kv) _)))) =>
      match (ir.value kv).kind with
      | .challenge key => ir.powersB r key nch (ir.valueField r)
      | _ => false
    | _ => false

/-- **The units of a grouped left side are well formed** in domain `d`: the blind is a value of the
domain's field of `w > 0` coordinates; the operand has `nch · w` coordinates; the powers are a MAC
key's (`macPowersB`); the taps give a `convMax` (`macConvMax?`) and `2 w` is below the characteristic
(the convolution's entries, in `[0, w]`, read as themselves on the integers); no group holds the blind, and the groups' chunk runs tile
`[0, nch)` in order. -/
def macUnitsOkB (d : ℕ) (u : MacUnits) (G : GroupedMod) : Bool :=
  ir.macPowersB u.powers u.chunks &&
  decide (u.blind < ir.values.length) && decide (ir.valueField u.blind = ir.domainField d) &&
    decide ((ir.value u.blind).size = u.width) && decide (0 < u.width) &&
    decide (ir.exprLen u.operand = u.chunks * u.width) &&
    (match macConvMax? u.width u.taps with
      | some _ => decide (2 * u.width < ir.charOf (ir.domainField d))
      | none => false) &&
    G.groups.all (fun fc => decide (1 ≤ fc.1)) && tiles G.chunkRuns 0 u.chunks

/-- **Value `rg` holds the powers `r_s, …, r_{s + n − 1}`** of value `r`: a public expression
`reindex idx (leaf r)` of `r`'s field with `idx` the run `[s, s + n)`. -/
def subPowersB (rg r s n : ℕ) : Bool :=
  decide (rg < ir.values.length) && decide (r < ir.values.length) &&
    decide (ir.valueField rg = ir.valueField r) &&
    match (ir.value rg).kind with
    | .pub (.expr (.reindex idx (.leaf r'))) => r' == r && idx.toList == runList s n
    | _ => false

/-- **Predicate body `b` is the accumulator row of group `g`** (`<name>.A.g<g>`, compiler/mod.h,
`group_residues`) of a grouped `mod_q` in domain `d` with units `u`, accumulators `acc` and the
group's units `fc = (first, count)`: `acc[g w + i] + (p − 1) · macConv(rg, w, count, taps)(Y)_i = z_i`
for `i < w`, with `rg` the powers `r_{first − 1}, …` (`subPowersB`), `Y` (one dereference) the view of
the operand's chunks `[first − 1, first − 1 + count)`, `z` a constant holding `0`; the group's
convolution has `w` coordinates, well-formed shape and shared expressions, and its interval within
`[0, smax]` (the interval evaluator, `exprIvl`). -/
def groupRowB (L : ℕ → ℕ → Option Ivl) (d : ℕ) (u : MacUnits) (G : GroupedMod) (acc g : ℕ)
    (fc : ℕ × ℕ) (b : PredBody) : Bool :=
  match b with
  | .equal d' (.add (.reindex ia (.leaf acc')) (.scale (.const c)
      (.apply (.macConv rg w cnt taps) Y))) (.leaf z) _ =>
    d' == d && acc' == acc && c + 1 == ir.charOf (ir.domainField d) && w == u.width &&
      cnt == fc.2 && taps == u.taps && ia.toList == runList (g * u.width) u.width &&
      ir.subPowersB rg u.powers (fc.1 - 1) fc.2 &&
      (match ir.deref Y with
        | .reindex iy y' => y'.beq u.operand &&
          iy.toList == runList ((fc.1 - 1) * u.width) (fc.2 * u.width)
        | _ => false) &&
      ir.constAll z 0 u.width (ir.domainField d) &&
      decide (ir.exprLen (.apply (.macConv rg w cnt taps) Y) = u.width) &&
      ir.exprShapeOk (.apply (.macConv rg w cnt taps) Y) &&
      Y.refs.all (· < ir.exprs.length) &&
      decide (IvlWithin (ir.exprIvl L (ir.domainField d)
        (.apply (.macConv rg w cnt taps) Y)) 0 G.groupBound)
  | _ => false

/-- **The residues of a grouped `mod_q`** in domain `d` with units `u` and accumulators `acc`
(compiler/mod.h, `r_g = S_g − q · from_digits_T(gq_g)`): (one dereference of) the residues is
`acc + c · batched(groups · w, fromDigits(k, T))(gq)` with `c + q = p`, `T` the base below `p`,
`k` the digit count, `gq` the group digits, a value of the domain's field of `groups · w · k`
coordinates; `acc` a value of the domain's field of `groups · w` coordinates; the residues have
`groups · w` coordinates. -/
def residuesB (d q : ℕ) (u : MacUnits) (G : GroupedMod) (acc : ℕ) : Bool :=
  decide (acc < ir.values.length) && decide (ir.valueField acc = ir.domainField d) &&
    decide ((ir.value acc).size = G.groups.length * u.width) &&
    decide (ir.exprLen G.residues = G.groups.length * u.width) &&
    G.residues.refs.all (· < ir.exprs.length) &&
    match ir.deref G.residues, G.groupDigits with
    | .add (.leaf acc') (.scale (.const c) (.apply (.batched bb (.fromDigits k T)) (.leaf gq'))),
        .leaf gq =>
      acc' == acc && gq' == gq && c + q == ir.charOf (ir.domainField d) &&
        bb == G.groups.length * u.width && k == G.digitCount && T == G.base &&
        decide (T < ir.charOf (ir.domainField d)) && decide (gq < ir.values.length) &&
        decide (ir.valueField gq = ir.domainField d) &&
        decide ((ir.value gq).size = G.groups.length * u.width * G.digitCount)
    | _, _ => false

/-- **The bound of the residues** in domain `d`: `2` when a field `equal` `R · R = R` of domain `d`
is their Boolean check (compiler/mod.h, `q = 2`), else the bound of a direct `in` on them
(`exprRange`); `none` without either. -/
def residueBound (d : ℕ) (R : Expr) : Option ℕ :=
  if ir.predicates.any (fun q =>
      match q.body with
      | .equal d' (.mul R₁ R₂) R₃ _ => d' == d && R₁.beq R && R₂.beq R && R₃.beq R
      | _ => false) then some 2
  else ir.exprRange d R

/-- **The first term `a · b` of a final sum**: the blind `b` at the coefficient `a`. -/
def finHeadB (a b : ℕ) : Expr → Bool
  | .scale (.const a') (.leaf b') => a' == a && b' == b
  | _ => false

/-- **Term `g` of a final sum** `a · R[idx_g]`: group `g`'s residues `R` at the coefficient `a`, read
through the run `[g w, g w + w)`. -/
def finTermB (a : ℕ) (R : Expr) (w g : ℕ) : Expr → Bool
  | .scale (.const a') (.reindex ia R') => a' == a && R'.beq R && ia.toList == runList (g * w) w
  | _ => false

/-- **The final sum's terms** `a · b + a · R[idx_0] + … + a · R[idx_{g−1}]` (left-nested) of a
grouped `mod_q`: the blind `b` (`finHeadB`) and the `g` groups' residues `R` (`finTermB`). -/
def finSumB (a b : ℕ) (R : Expr) (w : ℕ) : ℕ → Expr → Bool
  | 0, F => finHeadB a b F
  | g + 1, F =>
    match F with
    | .add F' t => finTermB a R w g t && finSumB a b R w g F'
    | _ => false

/-- **The coefficient of a final sum's first term** (`finSumB`). -/
def finCoef? : Expr → Option ℕ
  | .scale (.const a) _ => some a
  | .add F _ => finCoef? F
  | _ => none

/-- **The final quotient of a grouped `mod_q` is derived** in domain `d` with right side `e'` and
units `u` (compiler/mod.h, the final sum in the one-group form: `Q = q⁻¹ · (fin − e')` with
`fin = b + Σ_g r_g`): `qlo = 0` and (one dereference of) the quotient is `F + c · e'` with `F` the
final sum's terms at a coefficient `a` (`finSumB`), `a, c < p`, `q a ≡ 1` and `q c ≡ −1` modulo
`p`. -/
def finalQuotB (d q : ℕ) (e' : Expr) (u : MacUnits) (G : GroupedMod) (real : ModRealization) :
    Bool :=
  decide (real.quotientLo = 0) &&
    match ir.deref real.quotExpr with
    | .add F (.scale (.const c) e₂) =>
      match finCoef? F with
      | some a =>
        finSumB a u.blind G.residues u.width G.groups.length F && e₂.beq e' &&
          decide (a < ir.charOf (ir.domainField d)) && decide (c < ir.charOf (ir.domainField d)) &&
          decide (q * a % ir.charOf (ir.domainField d) = 1) &&
          decide ((q * c + 1) % ir.charOf (ir.domainField d) = 0)
      | none => false
    | _ => false

/-- **The shape of a grouped `mod_q`** in domain `d` with sides `e`, `e'` (compiler/mod.h,
`kGrouped`): the left side in the MAC unit form with well-formed units (`macUnitsOkB`); accumulators
`acc` with an accumulator row for every group (`groupRowB`); the residues (`residuesB`); the final
quotient derived from the final sum and the right side (`finalQuotB`). -/
def groupedShapeB (L : ℕ → ℕ → Option Ivl) (d q : ℕ) (e e' : Expr) (real : ModRealization) :
    Bool :=
  match real.grouped, macUnits? e with
  | some G, some u =>
    match G.accumulators with
    | some (.leaf acc) =>
      ir.macUnitsOkB d u G &&
        (List.range G.groups.length).all (fun g =>
          ir.predicates.any fun p => ir.groupRowB L d u G acc g (G.groups.getD g default) p.body) &&
        ir.residuesB d q u G acc && ir.finalQuotB d q e' u G real
    | _ => false
  | _, _ => false

/-- **The largest quotient of `k` digits below `N` in base `T`**: `Σ_{j<k} T^j (N − 1)`
(`digitsMax`). -/
def groupQuotMax (T k N : ℕ) : ℕ := digitsMax T (List.replicate k N)

/-- **The bounds of a grouped `mod_q`** in domain `d` with left side `e`: the residues bounded by
`Rb` (`residueBound`), the digits by a direct `in` `[0, N_d)` (`exprRange`), the blind with an
interval `J_b` (`exprIvl`); the group bound below `p`; the group tail `(Rb − 1) + q Σ_j T^j (N_d − 1)`
below `p` (so `S_g = r_g + q Q_g` lifts to the integers); and the final sum `b + Σ_g r_g`, in
`[J_b.lo, J_b.hi + groups (Rb − 1)]`, with the no-wrap conditions of the one-digit form against the
right side's exported interval: `J_b.hi + groups (Rb − 1) − rhsLo < p`, and through the final
quotient's direct `in` `Q ∈ [0, N)` among the exported ranges, `q (N − 1) + rhsHi − J_b.lo < p`. -/
def groupedBoundsB (L : ℕ → ℕ → Option Ivl) (d q : ℕ) (e : Expr) (real : ModRealization) :
    Bool :=
  match real.grouped, macUnits? e with
  | some G, some u =>
    match ir.residueBound d G.residues, ir.exprRange d G.groupDigits,
        ir.exprIvl L (ir.domainField d) (.leaf u.blind) with
    | some Rb, some Nd, some Jb =>
      decide (G.groupBound < ir.charOf (ir.domainField d)) &&
        decide (Rb - 1 + q * groupQuotMax G.base G.digitCount Nd < ir.charOf (ir.domainField d)) &&
        decide (Jb.hi + ((G.groups.length * (Rb - 1) : ℕ) : ℤ) - real.rhsLo <
          ir.charOf (ir.domainField d)) &&
        real.ranges.any (fun rid =>
          match ir.digitRangeOf d e real.quotExpr rid with
          | some N => decide (((q * (N - 1) : ℕ) : ℤ) + real.rhsHi - Jb.lo <
              ir.charOf (ir.domainField d))
          | none => false)
    | _, _, _ => false
  | _, _ => false

/-- **A `mod_q` realized in the grouped form** (compiler/mod.h, `kGrouped`) in domain `d` with sides
`e`, `e'`: the left side `b + Σ_c macConv(r_c)(y_c)` reaches `p`, so its chunks are summed in groups
`S_g < p` with accumulator rows; each group has committed quotient digits and a residue
`r_g = S_g − q · Q_g` (Boolean for `q = 2`, else a direct `in` below `Rb`); the final sum
`b + Σ_g r_g` satisfies the one-digit form against `e'`. `q > 0`, `p > 2`; the shape
(`groupedShapeB`) and the bounds (`groupedBoundsB`); the right side's computed interval within the
exported one. The per-group congruences `S_g ≡ r_g` and the final one add up to `e ≡ e' (mod q)`
over the integers (`RealizedProgram.holdsWith_mod_of_grouped`). -/
structure GroupedFormOk (L : ℕ → ℕ → Option Ivl) (d q : ℕ) (e e' : Expr)
    (real : ModRealization) : Prop where
  /-- The final quotient is one digit. -/
  form : real.form = .oneDigit
  /-- The modulus is positive. -/
  qpos : 0 < q
  /-- The characteristic exceeds `2`. -/
  char : 2 < ir.charOf (ir.domainField d)
  /-- The shape. -/
  shape : ir.groupedShapeB L d q e e' real = true
  /-- The bounds. -/
  bounds : ir.groupedBoundsB L d q e real = true
  /-- The right side's interval lies within the exported one. -/
  rhs : IvlWithin (ir.exprIvl L (ir.domainField d) e') real.rhsLo real.rhsHi

theorem groupedFormOk_iff (L : ℕ → ℕ → Option Ivl) (d q : ℕ) (e e' : Expr)
    (real : ModRealization) : ir.GroupedFormOk L d q e e' real ↔
      real.form = .oneDigit ∧ 0 < q ∧ 2 < ir.charOf (ir.domainField d) ∧
        ir.groupedShapeB L d q e e' real = true ∧
        ir.groupedBoundsB L d q e real = true ∧
        IvlWithin (ir.exprIvl L (ir.domainField d) e') real.rhsLo real.rhsHi :=
  ⟨fun h => ⟨h.form, h.qpos, h.char, h.shape, h.bounds, h.rhs⟩,
    fun ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨h1, h2, h3, h4, h5, h6⟩⟩

instance (L : ℕ → ℕ → Option Ivl) (d q : ℕ) (e e' : Expr) (real : ModRealization) :
    Decidable (ir.GroupedFormOk L d q e e' real) :=
  decidable_of_iff _ (ir.groupedFormOk_iff L d q e e' real).symm

/-! ## The field form of `mod_q` -/

/-- **A named operator whose block is linear in its input**, as the field form reads it
(`NamedOp.block_eq_sum`): the negacyclic convolution (either form), a number from its digits, a sum
of groups, and a batch of these. -/
def _root_.GordieHowe.RealizedProgram.NamedOp.linB : NamedOp → Bool
  | .negacyclicConv _ _ => true
  | .fromDigits _ _ => true
  | .sum _ => true
  | .batched _ op => op.linB
  | _ => false

/-- **An expression whose integer reading is the projection of its value** in field `f`
(`RealizedProgram.evalIntWith_proj`): an expression with an interval (`exprIvl`: its integer reading casts
to its value), a sum or difference of such expressions, a constant multiple `c · e` with `c < p`, or
a linear named operator (`NamedOp.linB`) with any public operand on an expression with an
interval. -/
def projOkB (L : ℕ → ℕ → Option Ivl) (f : ℕ) (e : Expr) : Bool :=
  (ir.exprIvl L f e).isSome ||
    match e with
    | .add a b => projOkB L f a && projOkB L f b
    | .sub a b => projOkB L f a && projOkB L f b
    | .scale (.const c) a => decide (c < ir.charOf f) && projOkB L f a
    | .apply op a => op.linB && (ir.exprIvl L f a).isSome
    | _ => false

/-- **Predicate body `b` is the field equation of a `mod_p`** in domain `d` with sides `e`, `e'`
(compiler/mod.h, `m = p`: `assert_zero(lhs − rhs)`): `e + (p − 1) · e' = z` in domain `d`, `z` a
constant holding `0` at `e`'s coordinates. -/
def fieldRowB (d : ℕ) (e e' : Expr) (b : PredBody) : Bool :=
  match b with
  | .equal d' (.add e₁ (.scale (.const c) e₂)) (.leaf z) _ =>
    d' == d && e₁.beq e && e₂.beq e' && c + 1 == ir.charOf (ir.domainField d) &&
      ir.constAll z 0 (ir.exprLen e) (ir.domainField d)
  | _ => false

/-- **A `mod_q` realized in the field form** (compiler/mod.h, `m = p`) in domain `d` with sides `e`,
`e'`: `q` is the characteristic `p > 2`, the field equation `e − e' = 0` is a field `equal` of the
program (`fieldRowB`), and both sides' integer readings are the projections of their values
(`projOkB`), so under a model whose integer reading is linear over the prime field
(`FieldInterp.ReadLinear`) the field equation gives `p ∣ e − e'` over the integers
(`RealizedProgram.holdsWith_mod_of_field`). -/
structure FieldFormOk (L : ℕ → ℕ → Option Ivl) (d q : ℕ) (e e' : Expr)
    (real : ModRealization) : Prop where
  /-- The field form. -/
  form : real.form = .field
  /-- The modulus is the characteristic. -/
  char : q = ir.charOf (ir.domainField d)
  /-- The characteristic exceeds `2`. -/
  two : 2 < q
  /-- The field equation is a field `equal` of the program. -/
  row : ir.predicates.any (fun p => ir.fieldRowB d e e' p.body) = true
  /-- The left side's integer reading is the projection of its value. -/
  lhs : ir.projOkB L (ir.domainField d) e = true
  /-- The right side's integer reading is the projection of its value. -/
  rhs : ir.projOkB L (ir.domainField d) e' = true

/-! ## The committed-digits form of `mod_q` -/

/-- **One term `c · D` of a left-nested sum** `rest + c · D`: `(rest, c, D)`. -/
def peelTerm : Expr → Option (Expr × ℕ × Expr)
  | .add rest (.scale (.const c) D) => some (rest, c, D)
  | _ => none

theorem eq_of_peelTerm {e rest D : Expr} {c : ℕ} (h : peelTerm e = some (rest, c, D)) :
    e = .add rest (.scale (.const c) D) := by
  unfold peelTerm at h
  split at h
  · cases h
    rfl
  · cases h

/-- **The digit terms of a committed-digits row** at the characteristic `p`, modulus `q` and radix
`R`: the left-nested sum `(…(h + c_0 · D_0) + …) + c_{k−1} · D_{k−1}` peeled from the right, the
pairs `(D_j, j)` given last first, each `c_j < p` with `c_j + q R^j ≡ 0` modulo `p` (so `c_j`
decodes to `−q R^j`); the head `h`. -/
def commPeel (p q R : ℕ) : Expr → List (Expr × ℕ) → Option Expr
  | L, [] => some L
  | L, (D', j) :: ts =>
    match peelTerm L with
    | some (rest, c, D) =>
      if D.beq D' = true ∧ c < p ∧ (c + q * R ^ j) % p = 0 then commPeel p q R rest ts else none
    | none => none

/-- **The shift of a committed-digits `mod_q`** at the characteristic `p`: `q · qlo` reduced
modulo `p`, the constant the row subtracts. -/
def commShift (p q : ℕ) (real : ModRealization) : ℕ :=
  Int.toNat (((q : ℤ) * real.quotientLo) % (p : ℤ))

/-- **`a · t` is the negation of the term `v`** at the characteristic `p`: `v = c · t` with
`a + c ≡ 0`, or `v = t` with `a = p − 1`. -/
def _root_.GordieHowe.RealizedProgram.negTermB (p : ℕ) (v : Expr) (a : ℕ) (t : Expr) : Bool :=
  match v with
  | .scale (.const c) t' => t'.beq t && decide (c < p) && decide (a < p) && (a + c) % p == 0
  | _ => v.beq t && a + 1 == p

/-- **`X` is `e − e'`** at the characteristic `p`, term by term (the compiler's rows distribute the
negated right side): `X = e + (p − 1) · e'`; or `X = Y + a · t` with `a · t` the negation of the
last term `v` of `e' = u + v` (`negTermB`) and `Y` the difference `e − u`, or of `e'` itself with
`Y = e`. -/
def _root_.GordieHowe.RealizedProgram.subB (p : ℕ) (e : Expr) : Expr → Expr → Bool
  | e', .add Y (.scale (.const a) t) =>
    (a + 1 == p && t.beq e' && Y.beq e) ||
      match e' with
      | .add u v => negTermB p v a t && subB p e u Y
      | _ => negTermB p e' a t && Y.beq e
  | _, _ => false

/-- **The head of a committed-digits row** in domain `d` for sides `e`, `e'`:
`(e − e') + (p − 1) · s` (`subB`) with `s` a constant holding `q · qlo` modulo `p`
(`commShift`) at `e`'s coordinates. -/
def commHeadB (d q : ℕ) (e e' : Expr) (real : ModRealization) : Expr → Bool
  | .add X (.scale (.const b) (.leaf sh)) =>
    subB (ir.charOf (ir.domainField d)) e e' X &&
      b + 1 == ir.charOf (ir.domainField d) &&
      ir.constAll sh (commShift (ir.charOf (ir.domainField d)) q real) (ir.exprLen e)
        (ir.domainField d)
  | _ => false

/-- **Predicate body `b` is the field equation of a committed-digits `mod_q`** in domain `d`
(compiler/mod.h, `kCommittedDigits`: `assert_zero(lhs − rhs − q·qlo − q·Σ_j R^j d_j)`):
`e + (p − 1) · e' + (p − 1) · s + Σ_j c_j · D_j = z` with the digit terms of the realization's
digits (`commPeel`), the head `commHeadB`, `z` a constant holding `0` at `e`'s coordinates. -/
def commRowB (d q : ℕ) (e e' : Expr) (real : ModRealization) (b : PredBody) : Bool :=
  match b with
  | .equal d' L (.leaf z) _ =>
    d' == d && ir.constAll z 0 (ir.exprLen e) (ir.domainField d) &&
      match commPeel (ir.charOf (ir.domainField d)) q real.radix L real.digits.zipIdx.reverse with
      | some h => ir.commHeadB d q e e' real h
      | none => false
  | _ => false

/-- **Predicate `rid` bounds digit `D` of a committed-digits `mod_q`** in domain `d` (the left side
`e`): a direct or digit `in` `D' ∈ [0, N)` of domain `d` with `D'` the digit, of the left side's
length, `0 < N`; its bound `N`. -/
def commRangeOf (d : ℕ) (e D : Expr) (rid : ℕ) : Option ℕ :=
  if rid < ir.predicates.length then
    match (ir.predicate rid).body with
    | .mem d' [D'] (.range N) (.lookup r) =>
      if d' = d ∧ (r.kind = .direct ∨ r.kind = .digits) ∧ D'.beq D = true ∧
          ir.exprLen D' = ir.exprLen e ∧ 0 < N then
        some N
      else none
    | _ => none
  else none

/-- **The bounds of a committed-digits `mod_q`'s digits** in domain `d`: digit `j` bounded by the
`j`-th of the ranges (`commRangeOf`); none when one is missing. -/
def commBounds (d : ℕ) (e : Expr) (real : ModRealization) : Option (List ℕ) :=
  if real.digits.length = real.ranges.length then
    (real.digits.zip real.ranges).mapM fun Dr => ir.commRangeOf d e Dr.1 Dr.2
  else none

/-- **The digits' bounds of a committed-digits `mod_q`** (`commBounds`; empty when one is
missing). -/
def commN (d : ℕ) (e : Expr) (real : ModRealization) : List ℕ := (ir.commBounds d e real).getD []

/-- **A `mod_q` realized in the committed-digits form** (compiler/mod.h, `kCommittedDigits`) in
domain `d` with sides `e`, `e'`: `q > 0`, `p > 2`; the field equation
`e − e' − q·qlo − q·Σ_j R^j d_j = 0` a field `equal` of the program (`commRowB`); each digit bounded
by a direct or digit `in` `d_j ∈ [0, N_j)` (`commBounds`, `commN`); the computed intervals of the
sides within the exported ones; and the no-wrap conditions `lhsHi − rhsLo − q·qlo < p` and
`q·Σ_j R^j (N_j − 1) + q·qlo + rhsHi − lhsLo < p`. The field equation then lifts to
`e − e' = q (qlo + Σ_j R^j d_j)` over the integers (`RealizedProgram.holdsWith_mod_of_committed`). -/
structure CommittedFormOk (L : ℕ → ℕ → Option Ivl) (d q : ℕ) (e e' : Expr)
    (real : ModRealization) : Prop where
  /-- The committed-digits form. -/
  form : real.form = .committedDigits
  /-- The modulus is positive. -/
  qpos : 0 < q
  /-- The characteristic exceeds `2`. -/
  char : 2 < ir.charOf (ir.domainField d)
  /-- The field equation is a field `equal` of the program. -/
  row : ir.predicates.any (fun pr => ir.commRowB d q e e' real pr.body) = true
  /-- Every digit is bounded. -/
  bounds : ir.commBounds d e real = some (ir.commN d e real)
  /-- The left side's interval lies within the exported one. -/
  lhs : IvlWithin (ir.exprIvl L (ir.domainField d) e) real.lhsLo real.lhsHi
  /-- The right side's interval lies within the exported one. -/
  rhs : IvlWithin (ir.exprIvl L (ir.domainField d) e') real.rhsLo real.rhsHi
  /-- The left half of the no-wrap condition. -/
  noWrap : real.lhsHi - real.rhsLo - (q : ℤ) * real.quotientLo < ir.charOf (ir.domainField d)
  /-- The right half of the no-wrap condition. -/
  noWrapDigits : ((q * digitsMax real.radix (ir.commN d e real) : ℕ) : ℤ) +
    (q : ℤ) * real.quotientLo + real.rhsHi - real.lhsLo < ir.charOf (ir.domainField d)

/-! ## The MAC of a cross-field `equal` -/

/-- **Value `tb` holds the bits of the MAC target** (`<mac>.target_bits`) in domain `dy`: an opaque
value of type `Bit` of domain `dy` whose one argument is the message of the tag `tag`, of the tag's
field. -/
def targetBitsB (tb dy tag : ℕ) : Bool :=
  decide (tb < ir.values.length) && decide (ir.valueField tb = ir.domainField dy) &&
    decide ((ir.value tb).type = .bit) &&
    match (ir.value tb).kind with
    | .pub (.opaque _ [m]) =>
      decide (m < ir.values.length) && decide (ir.valueField m = ir.valueField tag) &&
        match (ir.value m).kind with
        | .message u => u == tag
        | _ => false
    | _ => false

/-- **The key of the MAC of predicate `pid`** (`<mac>.beta`): a challenge of a phase the program has,
of one coordinate, uniform in the MAC field, owned by `pid`. -/
def macKeyB (pid : ℕ) (real : MacRealization) : Bool :=
  decide (ir.IsPhaseChal real.key) && decide ((ir.challenge real.key).size = 1) &&
    decide ((ir.challenge real.key).sampler = .full) &&
    decide (ir.chalField real.key = real.macField) &&
    (ir.challenge real.key).role == .realization pid

/-- **The tag of a MAC** (`<mac>.value`): a late value of the MAC field. -/
def macTagB (real : MacRealization) : Bool :=
  decide (real.tag < ir.values.length) && decide (ir.valueField real.tag = real.macField) &&
    decide (0 < (ir.value real.tag).size) &&
    match (ir.value real.tag).kind with
    | .late => true
    | _ => false

/-- **The blind of a MAC** (`<mac>.blind`): a value of domain `dy`'s field of `width` coordinates,
read as bits (interval `[0, 1]`). -/
def macBlindB (L : ℕ → ℕ → Option Ivl) (dy : ℕ) (real : MacRealization) : Bool :=
  match real.blind with
  | some b =>
    decide (b < ir.values.length) && decide (ir.valueField b = ir.domainField dy) &&
      decide ((ir.value b).size = real.width) &&
      decide (IvlWithin (ir.exprIvl L (ir.domainField dy) (.leaf b)) 0 1)
  | none => false

/-- **A predicate index search is a list search**: some index below the length whose predicate
satisfies `g`, exactly when some predicate of the list does. -/
theorem exists_lt_and_iff_any (g : Predicate → Bool) :
    (∃ t < ir.predicates.length, (decide (t < ir.predicates.length) && g (ir.predicate t)) = true) ↔
      ir.predicates.any g = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨t, ht, h⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨ir.predicate t, ?_, h.2⟩
    rw [predicate, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
    exact List.getElem_mem ht
  · rintro ⟨pr, hpr, hg⟩
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hpr
    refine ⟨t, ht, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨ht, ?_⟩
    rwa [predicate, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]

/-- **Where coordinate `i` of the view `e` reads from**, in field `f`, with `n` levels: through
`reindex`, `concat` and shared-expression views down to `some (b, j)`, coordinate `j` of an
expression `b` that is no such view (or `e` itself past the levels); `none` where it reads `0` (a
constant holding `0` of field `f`). -/
def viewSrc (f : ℕ) : ℕ → Expr → ℕ → Option (Expr × ℕ)
  | 0, e, i => some (e, i)
  | n + 1, e, i =>
    match e with
    | .reindex idx e' => viewSrc f n e' (idx.entry i)
    | .concat a b =>
      if i < ir.exprLen a then viewSrc f n a i else viewSrc f n b (i - ir.exprLen a)
    | .leaf c =>
      match (ir.value c).kind with
      | .constant es =>
        if es.getD i 0 = 0 ∧ ir.valueField c = f ∧ i < (ir.value c).size then none else some (e, i)
      | _ => some (e, i)
    | .ref k => if k < ir.exprs.length then viewSrc f n (ir.expr k) i else some (e, i)
    | _ => some (e, i)

/-- **Two view sources agree** (`viewSrc`): both `0`, or the same coordinate of the same
expression. -/
def srcEqB : Option (Expr × ℕ) → Option (Expr × ℕ) → Bool
  | none, none => true
  | some (a, i), some (b, j) => a.beq b && i == j
  | _, _ => false

/-- **The levels a padding view is followed through.** -/
def padFuel : ℕ := 16

/-- **`z'` reads `z` followed by zeros to `N` coordinates** in field `f`, coordinate by coordinate (compiler/mac.h:
a MAC's operand of fewer than `chunks · width` bits is read padded to them): `z'` has `N`
coordinates and `z` at most `N`; coordinate `i < N` of `z'` reads where coordinate `i` of `z` reads
below `z`'s length and `0` past it (`viewSrc`, through `reindex`, `concat` and shared-expression views
and constants holding `0`). -/
def zeroPadWalkB (f N : ℕ) (z' z : Expr) : Bool :=
  decide (ir.exprLen z' = N) && decide (ir.exprLen z ≤ N) &&
    (List.range N).all fun i =>
      srcEqB (ir.viewSrc f padFuel z' i) (if i < ir.exprLen z then ir.viewSrc f padFuel z i else none)

/-- **`z'` is `z` padded by zeros to `N` coordinates**, as a check: `z'` is `z` itself of `N`
coordinates (one comparison of the expressions), or the coordinatewise check `zeroPadWalkB`. -/
def zeroPadB (f N : ℕ) (z' z : Expr) : Bool :=
  (z'.beq z && decide (ir.exprLen z = N)) || ir.zeroPadWalkB f N z' z

/-- **The tail of the MAC of predicate `pid`** (compiler/mac.h: `mod_2(b + macConv(r)(y), bits(T))`):
predicate `t`, of role `realization pid`, is `mod_2(b + macConv(r, w, nch, taps)(y'), tb)` in domain
`dy`, with `y'` the operand `y` padded by zeros to `nch · w` coordinates (`zeroPadB`), `b` the
blind, `w` and `nch` the MAC's width and chunks, `r` the key's powers
(`powersB`), `tb` the target's bits (`targetBitsB`); the taps give a `convMax` (`macConvMax?`) and
`2 w < p`, so the convolution's matrix entries, in `[0, w]`, read as themselves on the integers. The tail's own realization (a
`mod_q` form, checked like any other `mod_q`) gives its integer congruence; the MAC needs no bound on
the left side. -/
def macTailB (pid dy : ℕ) (y : Expr) (real : MacRealization) (t : ℕ) : Bool :=
  decide (t < ir.predicates.length) && (ir.predicate t).role == .realization pid &&
    match (ir.predicate t).body with
    | .mod d 2 (.add (.leaf b) (.apply (.macConv r w nch taps) y')) (.leaf tb) _ =>
      d == dy && some b == real.blind && w == real.width && nch == real.chunks &&
        ir.zeroPadB (ir.domainField dy) (real.chunks * real.width) y' y &&
        ir.powersB r real.key real.chunks real.macField && ir.targetBitsB tb dy real.tag &&
        match macConvMax? w taps with
        | some _ => decide (2 * w < ir.charOf (ir.domainField dy))
        | none => false
    | _ => false

/-- **The index map of the generator's powers in the H predicate**: entry `c · w + i` is `i`, for
`nch` chunks of `w`. -/
def genPowsMap (nch w : ℕ) : List ℕ := (List.range (nch * w)).map (· % w)

/-- **Value `g` holds the generator's powers** `2^i`, `i < w`, as constants of field `f` (decoded,
`2^i` is the `i`-th power of the generator in a binary field's polynomial basis,
`FieldInterp.MacFieldOk.decodePow`). -/
def genPowsB (g w f : ℕ) : Bool :=
  decide (g < ir.values.length) && decide (ir.valueField g = f) &&
    match (ir.value g).kind with
    | .constant es => es == (List.range w).map (2 ^ ·)
    | _ => false

/-- **The generator's powers read at coordinate `c w + i`, `c < nch`** (the H predicate's
weights): `reindex idx (leaf g)` with `idx` the map `c w + i ↦ i` (`genPowsMap`), or `leaf g` for
one chunk, `g` the powers (`genPowsB`). -/
def genViewB (nch w f : ℕ) : Expr → Bool
  | .reindex idx (.leaf g) => idx.toList == genPowsMap nch w && ir.genPowsB g w f
  | .leaf g => nch == 1 && ir.genPowsB g w f
  | _ => false

/-- **Predicate `p` is the H predicate `<mac>.H` of the MAC of predicate `pid`** with H operand `x`
in domain `dx` (`equal(U, Σ_c r_c · chunk_c(X_H))`, `chunk_c(X_H) = Σ_i x^i X_H[c][i]`): a predicate
of role `realization pid`, in a MAC field of characteristic `2`, with body
`U + Σ_c r_c · Σ_i X_H[c w + i] · g_i = 0` in domain `dx`, written
`equal(add(leaf U, sum nch (mul (leaf r) (sum w (mul x (reindex idx (leaf g)))))), leaf z)`: `U` the
tag, `r` the key's powers (`powersB`), `idx` the map `c w + i ↦ i` (`genPowsMap`), `g` the
generator's powers (`genPowsB`; `leaf g` itself for one chunk, `genViewB`) and `z` a constant holding
`0`; `x` is read padded by zeros to `chunks · width` coordinates (`zeroPadB`). In characteristic `2` it states the
H half (`RealizedProgram.MacHHoldsAt`). It is an ordinary affine row of its domain; its truth is a field
`equal` of the realized program. -/
def macHPredB (pid dx : ℕ) (x : Expr) (real : MacRealization) (p : ℕ) : Bool :=
  decide (p < ir.predicates.length) && (ir.predicate p).role == .realization pid &&
    decide (ir.charOf real.macField = 2) &&
    match (ir.predicate p).body with
    | .equal d (.add (.leaf u) (.apply (.sum n) (.mul (.leaf r)
        (.apply (.sum w) (.mul x' G))))) (.leaf z) _ =>
      d == dx && u == real.tag && n == real.chunks && w == real.width &&
        ir.zeroPadB (ir.domainField dx) (real.chunks * real.width) x' x &&
        ir.powersB r real.key real.chunks real.macField &&
        ir.genViewB real.chunks real.width real.macField G &&
        ir.constAll z 0 1 real.macField
    | _ => false

/-- **The H half of the MAC of predicate `pid`**: the compiler's own circuit (no `<mac>.H`
predicate, `RealizedAt.macH`), or the H predicate `<mac>.H` (`macHPredB`). -/
def macHalfB (pid dx : ℕ) (x : Expr) (real : MacRealization) : Bool :=
  match real.hPredicate with
  | none => true
  | some p => ir.macHPredB pid dx x real p

/-- **The operands of a MAC read only what is fixed before its key** (and not the key): every value
the operands `x`, `y`, the blind and the blind of the check over `x`'s field read (`ReadsBefore`).
-/
def macReadsBeforeB (x y : Expr) (real : MacRealization) : Bool :=
  (ir.nodesOf x ++ ir.nodesOf y ++ real.blind.toList ++ real.blindX.toList).all
    (ir.readsBeforeB real.key)

/-! ### The two-tail form: a MAC that no domain hosts -/

/-- **The blind `b` of a MAC check over a field in domain `d`** (`<mac>.blind:<D>`): a value of `d`'s field of
`width` coordinates, read as bits (interval `[0, 1]`). `macBlindB` is the blind of the check over
`y`'s field, `real.blind`. -/
def macBlindAtB (L : ℕ → ℕ → Option Ivl) (d b : ℕ) (real : MacRealization) : Bool :=
  decide (b < ir.values.length) && decide (ir.valueField b = ir.domainField d) &&
    decide ((ir.value b).size = real.width) &&
    decide (IvlWithin (ir.exprIvl L (ir.domainField d) (.leaf b)) 0 1)

/-- **The interval-free part of `macBlindAtB`**: a value of `d`'s field of `width` coordinates. -/
def macBlindCoreB (d b : ℕ) (real : MacRealization) : Bool :=
  decide (b < ir.values.length) && decide (ir.valueField b = ir.domainField d) &&
    decide ((ir.value b).size = real.width)

variable {ir} in
theorem macBlindCoreB_of_at {L : ℕ → ℕ → Option Ivl} {d b : ℕ} {real : MacRealization}
    (h : ir.macBlindAtB L d b real = true) : ir.macBlindCoreB d b real = true := by
  simp only [macBlindAtB, Bool.and_eq_true] at h
  simp only [macBlindCoreB, Bool.and_eq_true]
  exact h.1

/-- **The tail of a MAC check over a field of odd characteristic** (compiler/mac.h, `mac_odd`:
`mod_2(b + macConv(r)(z), bits_D(T))`): predicate `t`, of role `realization pid`, is
`mod_2(b + macConv(r, w, nch, taps)(z), tb)` in domain `d`, with `b` the check's blind, `w` and
`nch` the MAC's width and chunks, `r` the key's powers (`powersB`), `tb` the target's bits in `d`
(`targetBitsB`); the taps give a `convMax` and `2 w < p`. `macTailB` is the tail of the check over
`y`'s field, with blind `real.blind`. -/
def macTailAtB (pid d : ℕ) (z : Expr) (b : ℕ) (real : MacRealization) (t : ℕ) : Bool :=
  decide (t < ir.predicates.length) && (ir.predicate t).role == .realization pid &&
    match (ir.predicate t).body with
    | .mod d' 2 (.add (.leaf b') (.apply (.macConv r w nch taps) z')) (.leaf tb) _ =>
      d' == d && b' == b && w == real.width && nch == real.chunks && z'.beq z &&
        ir.powersB r real.key real.chunks real.macField && ir.targetBitsB tb d real.tag &&
        match macConvMax? w taps with
        | some _ => decide (2 * w < ir.charOf (ir.domainField d))
        | none => false
    | _ => false

/-- **`macTailAtB` on one predicate `pr`**: its conditions after the index's bound. -/
def macTailAtOfB (pid d : ℕ) (z : Expr) (b : ℕ) (real : MacRealization) (pr : Predicate) : Bool :=
  pr.role == .realization pid &&
    match pr.body with
    | .mod d' 2 (.add (.leaf b') (.apply (.macConv r w nch taps) z')) (.leaf tb) _ =>
      d' == d && b' == b && w == real.width && nch == real.chunks && z'.beq z &&
        ir.powersB r real.key real.chunks real.macField && ir.targetBitsB tb d real.tag &&
        match macConvMax? w taps with
        | some _ => decide (2 * w < ir.charOf (ir.domainField d))
        | none => false
    | _ => false

theorem macTailAtB_eq_of (pid d : ℕ) (z : Expr) (b : ℕ) (real : MacRealization) (t : ℕ) :
    ir.macTailAtB pid d z b real t =
      (decide (t < ir.predicates.length) &&
        ir.macTailAtOfB pid d z b real (ir.predicate t)) := by
  unfold macTailAtB macTailAtOfB
  rw [Bool.and_assoc]

theorem macTailAtB_exists_iff (pid d : ℕ) (z : Expr) (b : ℕ) (real : MacRealization) :
    (∃ t < ir.predicates.length, ir.macTailAtB pid d z b real t = true) ↔
      ir.predicates.any (ir.macTailAtOfB pid d z b real) = true := by
  simp only [macTailAtB_eq_of]
  exact ir.exists_lt_and_iff_any _

/-- **The tail of a MAC check over a field of characteristic `2`** (the paper's Section 4.1.4, Cross-field links:
a field of characteristic `2` that need not contain the MAC field checks `acc = bits(T)` entrywise):
predicate `t`, of role `realization pid`, is the field `equal`
`b + macConv(r, w, nch, taps)(z) = tb` in domain `d` of characteristic `2`, with `b` the check's
blind, `r` the key's powers (`powersB`) and `tb` the target's bits in `d` (`targetBitsB`). In
characteristic `2` the field computes each accumulator entry modulo `2`. The C++ compiler does not
emit this form. -/
def macTailTwoB (pid d : ℕ) (z : Expr) (b : ℕ) (real : MacRealization) (t : ℕ) : Bool :=
  decide (t < ir.predicates.length) && (ir.predicate t).role == .realization pid &&
    decide (ir.charOf (ir.domainField d) = 2) &&
    match (ir.predicate t).body with
    | .equal d' (.add (.leaf b') (.apply (.macConv r w nch _) z')) (.leaf tb) _ =>
      d' == d && b' == b && w == real.width && nch == real.chunks && z'.beq z &&
        ir.powersB r real.key real.chunks real.macField && ir.targetBitsB tb d real.tag
    | _ => false

/-- **`macTailTwoB` on one predicate `pr`**: its conditions after the index's bound. -/
def macTailTwoOfB (pid d : ℕ) (z : Expr) (b : ℕ) (real : MacRealization) (pr : Predicate) : Bool :=
  pr.role == .realization pid &&
    decide (ir.charOf (ir.domainField d) = 2) &&
    match pr.body with
    | .equal d' (.add (.leaf b') (.apply (.macConv r w nch _) z')) (.leaf tb) _ =>
      d' == d && b' == b && w == real.width && nch == real.chunks && z'.beq z &&
        ir.powersB r real.key real.chunks real.macField && ir.targetBitsB tb d real.tag
    | _ => false

theorem macTailTwoB_eq_of (pid d : ℕ) (z : Expr) (b : ℕ) (real : MacRealization) (t : ℕ) :
    ir.macTailTwoB pid d z b real t =
      (decide (t < ir.predicates.length) &&
        ir.macTailTwoOfB pid d z b real (ir.predicate t)) := by
  unfold macTailTwoB macTailTwoOfB
  simp only [Bool.and_assoc]

theorem macTailTwoB_exists_iff (pid d : ℕ) (z : Expr) (b : ℕ) (real : MacRealization) :
    (∃ t < ir.predicates.length, ir.macTailTwoB pid d z b real t = true) ↔
      ir.predicates.any (ir.macTailTwoOfB pid d z b real) = true := by
  simp only [macTailTwoB_eq_of]
  exact ir.exists_lt_and_iff_any _

/-- **A cross-field `equal` has the realization of the MAC** (compiler/mac.h) as predicate `pid`,
`x` of domain `dx` and `y` of domain `dy`: bits (`width = 1`); `dx`'s field is the MAC field; the
key (`macKeyB`), the tag (`macTagB`) and the blind (`macBlindB`); `x` and `y` of as many
coordinates, at most `chunks · width` (the tail and the H half read them padded by zeros,
`padsB`), `y` read as bits; the tail `mod_2` (`macTailB`); the operands and the blind read only
what is fixed before the key (`macReadsBeforeB`); `p > 2` in `dy`; the H half the compiler's own
circuit (`RealizedAt.macH`) or the H predicate `<mac>.H` (`macHalfB`). The Booleanity of `x` is not
part of the shape: the cross-field `equal`'s meaning leaves it to the caller
(`RealizedProgram.HoldsWith`). -/
structure MacShapeOk (primeNodes : ℕ → List String) (pid dx : ℕ) (x : Expr) (dy : ℕ) (y : Expr)
    (k : CrossKind) (real : MacRealization) : Prop where
  /-- Bits. -/
  width : k.width = 1
  /-- The chunk width is positive. -/
  pos : 0 < real.width
  /-- The MAC field is a field of the program. -/
  field : real.macField < ir.fields.length
  /-- `x`'s domain is of the MAC field. -/
  hField : ir.domainField dx = real.macField
  /-- The key. -/
  key : ir.macKeyB pid real = true
  /-- The tag. -/
  tag : ir.macTagB real = true
  /-- The blind (`macBlindB`) and `y` read as bits, at values' intervals justified at no value
  range. -/
  ivls : ∃ L, ir.LeafIvlsOk primeNodes [] L ∧ ir.macBlindB L dy real = true ∧
    IvlWithin (ir.exprIvl L (ir.domainField dy) y) 0 1
  /-- `x` has at most `chunks · width` coordinates (the MAC reads it padded by zeros). -/
  lenX : ir.exprLen x ≤ real.chunks * real.width
  /-- `y` has as many coordinates as `x`. -/
  lenY : ir.exprLen y = ir.exprLen x
  /-- The tail. -/
  tail : ∃ t < ir.predicates.length, ir.macTailB pid dy y real t = true
  /-- The operands read only what is fixed before the key. -/
  before : ir.macReadsBeforeB x y real = true
  /-- The characteristic of `dy` exceeds `2`. -/
  char : 2 < ir.charOf (ir.domainField dy)
  /-- The H half: the compiler's own circuit or the H predicate. -/
  half : ir.macHalfB pid dx x real = true
  /-- `x`'s domain hosts the MAC: no blind for `x`'s field. -/
  noBlindX : real.blindX = none

/-! ### Operands read as bits in any characteristic -/

/-- **Value `v` is a bit in its domain** (`RealizedProgram.TypeSources`; the paper's condition that every
phase-0 `Bit` value is stored at the node of its type or has its Boolean check): a value of type
`Bit` read in the prime subfield (`primeRead`: stored at its packing-tree node `bit`, or with its
Boolean check `v · v = v`, `boolCheckOk`). -/
def bitLeafB (primeNodes : ℕ → List String) (v : ℕ) : Bool :=
  decide (v < ir.values.length) && decide ((ir.value v).type = .bit) && ir.primeRead primeNodes v

/-- **An expression is a view of bits** at the leaves `bl` and the shared expressions `rb`, the
shared expressions having lengths `rl`: a leaf in `bl`, a reindexing within its operand's length,
a concatenation of two views, or a shared expression in `rb`. Every coordinate of such a view below
its length is a coordinate of a leaf below its size. -/
def bitsB (bl rb : ℕ → Bool) (rl : ℕ → ℕ) : Expr → Bool
  | .leaf v => bl v
  | .reindex idx e => bitsB bl rb rl e && idx.inRange (Expr.len ir rl e)
  | .concat a b => bitsB bl rb rl a && bitsB bl rb rl b
  | .ref k => rb k
  | _ => false

/-- **The shared expressions that are views of bits** at the leaves `bl`, with `n` levels
(`0`: none). -/
def refBitsT (bl : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, _ => false
  | n + 1, k => decide (k < ir.exprs.length) &&
      ir.bitsB bl (refBitsT bl n) (ir.refLen ir.exprs.length) (ir.expr k)

/-- **An expression reads bits** (in any characteristic): a view of bits (`bitsB`) whose leaves are
bits of their domains (`bitLeafB`), through the shared expressions at the program's depth. The
compiler's MAC operands (the joined copies of the shared bits, `<mac>.xa`, `<mac>.xb`) are such
views. -/
def exprBitsB (primeNodes : ℕ → List String) (e : Expr) : Bool :=
  ir.bitsB (ir.bitLeafB primeNodes) (ir.refBitsT (ir.bitLeafB primeNodes) ir.exprs.length)
    (ir.refLen ir.exprs.length) e

/-- **A MAC check over a field of odd characteristic** (compiler/mac.h, `mac_odd`), operand `z` of domain `d`
with blind `b`: `p > 2` in `d`; the blind (`macBlindAtB`); `z` read as bits; the tail `mod_2`
(`macTailAtB`). -/
structure MacOddFieldOk (L : ℕ → ℕ → Option Ivl) (pid d : ℕ) (z : Expr) (b : ℕ)
    (real : MacRealization) : Prop where
  /-- The characteristic of `d` exceeds `2`. -/
  char : 2 < ir.charOf (ir.domainField d)
  /-- The blind. -/
  blind : ir.macBlindAtB L d b real = true
  /-- `z` reads bits. -/
  bits : IvlWithin (ir.exprIvl L (ir.domainField d) z) 0 1
  /-- The tail. -/
  tail : ∃ t < ir.predicates.length, ir.macTailAtB pid d z b real t = true

theorem macOddFieldOk_iff (L : ℕ → ℕ → Option Ivl) (pid d : ℕ) (z : Expr) (b : ℕ)
    (real : MacRealization) :
    ir.MacOddFieldOk L pid d z b real ↔
      2 < ir.charOf (ir.domainField d) ∧ ir.macBlindAtB L d b real = true ∧
        IvlWithin (ir.exprIvl L (ir.domainField d) z) 0 1 ∧
        ∃ t < ir.predicates.length, ir.macTailAtB pid d z b real t = true :=
  ⟨fun h => ⟨h.char, h.blind, h.bits, h.tail⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

/-- `MacOddFieldOk` is decided with the tail searched along the predicates. -/
instance (L : ℕ → ℕ → Option Ivl) (pid d : ℕ) (z : Expr) (b : ℕ) (real : MacRealization) :
    Decidable (ir.MacOddFieldOk L pid d z b real) :=
  decidable_of_iff (2 < ir.charOf (ir.domainField d) ∧ ir.macBlindAtB L d b real = true ∧
        IvlWithin (ir.exprIvl L (ir.domainField d) z) 0 1 ∧
        ir.predicates.any (ir.macTailAtOfB pid d z b real) = true)
    (by rw [macOddFieldOk_iff, macTailAtB_exists_iff])

/-- **A MAC check over a field of characteristic `2`**, operand `z` of domain `d` with blind `b`: the blind is a
value of `d`'s field of `width` coordinates, `z` reads bits by the program (`exprBitsB`: views of
`Bit` values, each stored at its node `bit` or with its Boolean check), and the tail is the field
`equal` `b + macConv(r)(z) = bits(T)` (`macTailTwoB`). The blind's Booleanity follows from the
tail. -/
structure MacTwoFieldOk (primeNodes : ℕ → List String) (pid d : ℕ) (z : Expr) (b : ℕ)
    (real : MacRealization) : Prop where
  /-- The blind is a value of `d`'s field. -/
  blindField : ir.valueField b = ir.domainField d
  /-- The blind has `width` coordinates. -/
  blindSize : (ir.value b).size = real.width
  /-- `z` reads bits. -/
  bits : ir.exprBitsB primeNodes z = true
  /-- The tail. -/
  tail : ∃ t < ir.predicates.length, ir.macTailTwoB pid d z b real t = true

theorem macTwoFieldOk_iff (primeNodes : ℕ → List String) (pid d : ℕ) (z : Expr) (b : ℕ)
    (real : MacRealization) :
    ir.MacTwoFieldOk primeNodes pid d z b real ↔
      ir.valueField b = ir.domainField d ∧ (ir.value b).size = real.width ∧
        ir.exprBitsB primeNodes z = true ∧
        ∃ t < ir.predicates.length, ir.macTailTwoB pid d z b real t = true :=
  ⟨fun h => ⟨h.blindField, h.blindSize, h.bits, h.tail⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4⟩⟩

/-- `MacTwoFieldOk` is decided with the tail searched along the predicates. -/
instance (primeNodes : ℕ → List String) (pid d : ℕ) (z : Expr) (b : ℕ) (real : MacRealization) :
    Decidable (ir.MacTwoFieldOk primeNodes pid d z b real) :=
  decidable_of_iff (ir.valueField b = ir.domainField d ∧ (ir.value b).size = real.width ∧
        ir.exprBitsB primeNodes z = true ∧
        ir.predicates.any (ir.macTailTwoOfB pid d z b real) = true)
    (by rw [macTwoFieldOk_iff, macTailTwoB_exists_iff])

/-- **A MAC check over a field that no domain hosts**: of odd characteristic (`MacOddFieldOk`) or of
characteristic `2` (`MacTwoFieldOk`). -/
def MacTailFieldOk (primeNodes : ℕ → List String) (L : ℕ → ℕ → Option Ivl) (pid d : ℕ) (z : Expr)
    (b : ℕ) (real : MacRealization) : Prop :=
  ir.MacOddFieldOk L pid d z b real ∨ ir.MacTwoFieldOk primeNodes pid d z b real

/-- **A cross-field `equal` has the two-tail realization of the MAC** (compiler/mac.h, `mac_odd`):
no domain hosts the MAC. Bits (`width = 1`); the MAC field is a field of the program; the key
(`macKeyB`) and the tag (`macTagB`, a late value of the MAC field, of no domain when no domain has
that field); no H predicate; `x` and `y` of `chunks · width` coordinates; the MAC check over each
operand's field (`MacTailFieldOk`), over `x`'s field with blind `bx` and over `y`'s field with blind
`b`, of odd characteristic (`MacOddFieldOk`) or of characteristic `2` (`MacTwoFieldOk`), so every
pair of characteristics; the operands and both blinds read only what is fixed before the key
(`macReadsBeforeB`). The check over each field gives the target `T` as the masked MAC of its operand
with its blind, so the two operands' chunks agree or the key is a root of their binding polynomial.
-/
structure MacTwoTailOk (primeNodes : ℕ → List String) (pid dx : ℕ) (x : Expr) (dy : ℕ) (y : Expr)
    (k : CrossKind) (real : MacRealization) (bx b : ℕ) : Prop where
  /-- Bits. -/
  width : k.width = 1
  /-- The chunk width is positive. -/
  pos : 0 < real.width
  /-- The MAC field is a field of the program. -/
  field : real.macField < ir.fields.length
  /-- The key. -/
  key : ir.macKeyB pid real = true
  /-- The tag. -/
  tag : ir.macTagB real = true
  /-- No H predicate. -/
  noH : real.hPredicate = none
  /-- `x` has `chunks · width` coordinates. -/
  lenX : ir.exprLen x = real.chunks * real.width
  /-- `y` has `chunks · width` coordinates. -/
  lenY : ir.exprLen y = real.chunks * real.width
  /-- The MAC checks over `x`'s and `y`'s fields, at values' intervals justified at no value
  range. -/
  ivls : ∃ L, ir.LeafIvlsOk primeNodes [] L ∧ ir.MacTailFieldOk primeNodes L pid dx x bx real ∧
    ir.MacTailFieldOk primeNodes L pid dy y b real
  /-- The operands and the blinds read only what is fixed before the key. -/
  before : ir.macReadsBeforeB x y real = true

/-- **A cross-field `equal` has a covered MAC realization**: the host form (`MacShapeOk`, no
blind for `x`'s field) or the two-tail form (`MacTwoTailOk`, with both blinds). -/
def MacRealizable (primeNodes : ℕ → List String) (pid dx : ℕ) (x : Expr) (dy : ℕ) (y : Expr)
    (k : CrossKind) (real : MacRealization) : Prop :=
  match real.blindX, real.blind with
  | none, _ => ir.MacShapeOk primeNodes pid dx x dy y k real
  | some bx, some b => ir.MacTwoTailOk primeNodes pid dx x dy y k real bx b
  | some _, none => False

/-! ## Covered shapes -/

/-- Whether value `u` is a committed value or a constant. -/
def isPrivOrConst (u : ℕ) : Bool :=
  match (ir.value u).kind with
  | .priv => true
  | .constant _ => true
  | _ => false

/-- **Value `v`, when bound to its digits, reads only committed values and constants**: its
expression's shared expressions exist and every value it reads is a committed value or a constant
(`isPrivOrConst`). -/
def BoundOk (v : ℕ) : Prop :=
  match (ir.value v).kind with
  | .bound e => (∀ k ∈ e.refs, k < ir.exprs.length) ∧ ∀ u ∈ ir.exprNodes e, ir.isPrivOrConst u = true
  | _ => True

/-! ## The checker -/

/-- **`MemberOk t m`**, through the tables. -/
def memberOkB (t : ℕ) (m : Member) : Bool :=
  decide (m.pred < ir.predicates.length) && decide (ir.LooksUp m.pred t m.needle) &&
    (ir.needleExpr m.pred m.needle).refs.all (· < ir.exprs.length) &&
    (ir.nodesOf (ir.needleExpr m.pred m.needle)).all (ir.readsBeforeB (ir.alphaOf t))

/-- **`GroupOk t g`**, through the tables. -/
def groupOkB (t g : ℕ) : Bool :=
  (ir.members t g).all (ir.memberOkB t) &&
    decide (ir.groupCount t g < (ir.field (ir.chalField (ir.alphaOf t))).characteristic) &&
    (ir.histValues t g).all (ir.readsBeforeB (ir.alphaOf t))

/-- **`RowsOk t rows`**, through the tables. -/
def rowsOkB (t : ℕ) : TableRows → Bool
  | .range T => decide (T ≤ ir.tmaxOf (ir.alphaOf t))
  | .columns cols => !cols.isEmpty && ir.readsBeforeB (ir.alphaOf t) (cols.headD 0)
  | .expr e' => e'.refs.all (· < ir.exprs.length) && (ir.nodesOf e').all (ir.readsBeforeB (ir.alphaOf t))

/-- **`TableOk t`**, through the tables. -/
def tableOkB (t : ℕ) : Bool :=
  ir.rowsOkB t (ir.table t).rows && decide (ir.IsPhaseChal (ir.alphaOf t)) &&
    decide ((ir.challenge (ir.alphaOf t)).size = 1) &&
    decide ((ir.challenge (ir.alphaOf t)).sampler =
      .fieldMinusTables (.range (ir.tmaxOf (ir.alphaOf t)))) &&
    decide (ir.chalField (ir.alphaOf t) < ir.fields.length) &&
    decide (ir.chalField (ir.alphaOf t) = ir.domainField (ir.table t).domain) &&
    decide (ir.tmaxOf (ir.alphaOf t) < (ir.field (ir.chalField (ir.alphaOf t))).characteristic) &&
    (List.range (ir.groupCountOf t)).all (ir.groupOkB t)

/-- **`DirectOk pid d recs set r`**, through the tables. -/
def directOkB (pid d : ℕ) (recs : List Expr) (set : InSet)
    (r : LookupRealization) : Bool :=
  decide (r.table < ir.tables.length) && decide (d = (ir.table r.table).domain) &&
    decide (ir.DirectSet r.table set) &&
    ir.singleMatch recs r.needles &&
    r.needles.all (fun e => e.refs.all (· < ir.exprs.length)) &&
    (List.range r.needles.length).all fun n =>
      tiles (ir.coverRuns r.table pid n) 0 (ir.lenOf (r.needles.getD n default))

/-- Whether value `u` is a committed value or a constant, through the table (`isPrivOrConst`). -/
def isPrivOrConstT (u : ℕ) : Bool :=
  match (ir.valueT u).kind with
  | .priv => true
  | .constant _ => true
  | _ => false

theorem isPrivOrConstT_eq (u : ℕ) : ir.isPrivOrConstT u = ir.isPrivOrConst u := by
  rw [isPrivOrConstT, valueT_eq]
  rfl

/-- **`BoundOk v`**, on value `v`, through the tables. -/
def boundOkV (x : Value) : Bool :=
  match x.kind with
  | .bound e => e.refs.all (· < ir.exprs.length) && ir.closAll Expr.directNodes ir.isPrivOrConstT e
  | _ => true

/-! ## The checkers decide the conditions -/

section Checker

variable {ir}

theorem readsBeforeB_iff (hwf : ir.WellFormed) (j v : ℕ) :
    ir.readsBeforeB j v = true ↔ ir.ReadsBefore j v := by
  simp only [readsBeforeB, ReadsBefore, List.all_eq_true, decide_eq_true_eq]
  exact forall_congr' fun rd => imp_congr_left (mem_readsT hwf v rd).symm

theorem memberOkB_iff (hwf : ir.WellFormed) (t : ℕ) (m : Member) :
    ir.memberOkB t m = true ↔ ir.MemberOk t m := by
  constructor
  · intro h
    simp only [memberOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    have hr : ∀ k ∈ (ir.needleExpr m.pred m.needle).refs, k < ir.exprs.length := fun k hk => by
      simpa using h3 k hk
    exact ⟨h1, h2, hr, fun v hv => (readsBeforeB_iff hwf _ v).1
      (h4 v ((mem_nodesOf hwf.refsOrdered hr v).2 hv))⟩
  · intro h
    simp only [memberOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨⟨⟨h.pred, h.looksUp⟩, fun k hk => by simpa using h.refs k hk⟩, fun v hv => ?_⟩
    exact (readsBeforeB_iff hwf _ v).2 (h.reads v ((mem_nodesOf hwf.refsOrdered h.refs v).1 hv))

theorem groupOkB_iff (hwf : ir.WellFormed) (t g : ℕ) :
    ir.groupOkB t g = true ↔ ir.GroupOk t g := by
  simp only [groupOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, memberOkB_iff hwf,
    readsBeforeB_iff hwf]
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, fun h => ⟨⟨h.members, h.size⟩, h.hists⟩⟩

theorem rowsOkB_iff (hwf : ir.WellFormed) (t : ℕ) (rows : TableRows) :
    ir.rowsOkB t rows = true ↔ ir.RowsOk t rows := by
  cases rows with
  | range T => simp [rowsOkB, RowsOk]
  | columns cols =>
    simp only [rowsOkB, RowsOk, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      readsBeforeB_iff hwf]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun h => ⟨h.nonempty, h.reads⟩⟩
  | expr e' =>
    simp only [rowsOkB, RowsOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    constructor
    · intro ⟨h1, h2⟩
      have hr : ∀ k ∈ e'.refs, k < ir.exprs.length := fun k hk => by simpa using h1 k hk
      exact ⟨hr, fun v hv => (readsBeforeB_iff hwf _ v).1
        (h2 v ((mem_nodesOf hwf.refsOrdered hr v).2 hv))⟩
    · intro h
      refine ⟨fun k hk => by simpa using h.refs k hk, fun v hv => ?_⟩
      exact (readsBeforeB_iff hwf _ v).2 (h.reads v ((mem_nodesOf hwf.refsOrdered h.refs v).1 hv))

theorem tableOkB_iff (hwf : ir.WellFormed) (t : ℕ) :
    ir.tableOkB t = true ↔ ir.TableOk t := by
  simp only [tableOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    groupOkB_iff hwf, rowsOkB_iff hwf]
  exact ⟨fun ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h8⟩, h9⟩ => ⟨h1, h2, h3, h4, h5, h6, h8, h9⟩,
    fun h => ⟨⟨⟨⟨⟨⟨⟨h.rows, h.alpha⟩, h.size⟩, h.sampler⟩, h.field⟩, h.domain⟩, h.char⟩,
      h.groups⟩⟩

theorem directOkB_iff (hwf : ir.WellFormed) (pid d : ℕ) (recs : List Expr)
    (set : InSet) (r : LookupRealization) :
    ir.directOkB pid d recs set r = true ↔ ir.DirectOk pid d recs set r := by
  have hlen : (∀ e ∈ r.needles, ∀ k ∈ e.refs, k < ir.exprs.length) → ∀ n,
      ir.lenOf (r.needles.getD n default) = ir.exprLen (r.needles.getD n default) := by
    intro hr n
    refine lenOf_eq hwf.refsOrdered fun k hk => ?_
    rw [List.getD_eq_getElem?_getD] at hk
    cases hn : r.needles[n]? with
    | none => rw [hn, Option.getD_none] at hk; exact absurd hk List.not_mem_nil
    | some e => rw [hn, Option.getD_some] at hk; exact hr e (List.mem_of_getElem? hn) k hk
  constructor
  · intro h
    simp only [directOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
      at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    have hr : ∀ e ∈ r.needles, ∀ k ∈ e.refs, k < ir.exprs.length := fun e he k hk => by
      simpa using h5 e he k hk
    exact ⟨h1, h2, h3, h4, hr, fun n hn => hlen hr n ▸ h6 n hn⟩
  · intro h
    simp only [directOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    exact ⟨⟨⟨⟨⟨h.table, h.domain⟩, h.set⟩, h.record⟩, fun e he k hk => by simpa using h.refs e he k hk⟩,
      fun n hn => (hlen h.refs n).symm ▸ h.covered n hn⟩

theorem boundOkV_iff (hwf : ir.WellFormed) (v : ℕ) :
    ir.boundOkV (ir.value v) = true ↔ ir.BoundOk v := by
  unfold boundOkV BoundOk
  split
  · rename_i e _
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun u hu => ?_⟩
      rw [← isPrivOrConstT_eq]
      exact (closAll_iff hwf.refsOrdered _ _ h1).1 h2 u hu
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (closAll_iff hwf.refsOrdered _ _ h1).2 fun u hu => by
        rw [isPrivOrConstT_eq]
        exact h2 u hu⟩
  · simp

end Checker

end

end GordieHowe.RealizedProgram
