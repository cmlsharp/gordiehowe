-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Realized
public import GordieHowe.Language.RealizedProgram.Interval
public import GordieHowe.Language.RealizedProgram.IvlSource
public import GordieHowe.Language.RealizedProgram.StructureCheck
public import GordieHoweNative.Language.RealizedProgram.RealizationValid

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
  `T^k ≤ N`), and two digit sets (`TwoSidedOk`: the needles the digits `d_j` and `h_j` in base `T`,
  `2 (T^k − 1) < p`; the reconstruction and top rows, `reconMatch` and `topMatch`, are cited by
  the derivations' steps); an `in` implied by intervals must be a sum of terms `c_j · a_j`
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
  The compiler names each value's source in the structure records (`Structure.ivlSources`); the
  intervals the checks read are those sources' (`GordieHowe.RealizedProgram.ivlTab`), justified by
  construction (`GordieHowe.RealizedProgram.ivlTab_justified`).
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

The definitions are in `GordieHoweNative/Language/RealizedProgram/RealizationValid.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## Tilings -/

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

theorem centeredZ_eq_key (p c : ℕ) : centeredZ p c = (centeredKey p c : ℤ) - p := by
  unfold centeredZ centeredKey
  split_ifs <;> push_cast <;> ring

/-- **The keys' hull bounds `lo`, `hi` and every entry's key.** -/
theorem keyHull_spec (p : ℕ) : ∀ (lo hi : ℕ) (es : List ℕ), lo ≤ hi →
    (keyHull p lo hi es).1 ≤ lo ∧ hi ≤ (keyHull p lo hi es).2 ∧
      ∀ c ∈ es, (keyHull p lo hi es).1 ≤ centeredKey p c ∧ centeredKey p c ≤ (keyHull p lo hi es).2
  | lo, hi, [], _ => by simp [keyHull]
  | lo, hi, c :: es, hlh => by
    have step : ∀ lo' hi' : ℕ, lo' ≤ hi' → lo' ≤ lo → hi ≤ hi' → lo' ≤ centeredKey p c →
        centeredKey p c ≤ hi' → keyHull p lo' hi' es = keyHull p lo hi (c :: es) →
        (keyHull p lo hi (c :: es)).1 ≤ lo ∧ hi ≤ (keyHull p lo hi (c :: es)).2 ∧
          ∀ x ∈ c :: es, (keyHull p lo hi (c :: es)).1 ≤ centeredKey p x ∧
            centeredKey p x ≤ (keyHull p lo hi (c :: es)).2 := by
      intro lo' hi' hlh' hl hh hkl hkh he
      rw [← he]
      obtain ⟨ha, hb, hall⟩ := keyHull_spec p lo' hi' es hlh'
      refine ⟨by omega, by omega, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨by omega, by omega⟩
      · exact hall x hx
    have tle : ∀ {a b : ℕ}, a.ble b = true → a ≤ b := Nat.le_of_ble_eq_true
    have fle : ∀ {a b : ℕ}, a.ble b = false → b < a := fun h =>
      Nat.lt_of_not_le fun hab => by rw [Nat.ble_eq_true_of_le hab] at h; cases h
    cases h1 : lo.ble (centeredKey p c) <;> cases h2 : (centeredKey p c).ble hi
    · have := fle h1
      exact step _ _ (by omega) (by omega) le_rfl le_rfl (by omega) (by simp [keyHull, h1, h2])
    · have := fle h1
      exact step _ _ (by omega) (by omega) le_rfl le_rfl (by omega) (by simp [keyHull, h1, h2])
    · have := tle h1
      have := fle h2
      exact step _ _ (by omega) le_rfl (by omega) (tle h1) le_rfl (by simp [keyHull, h1, h2])
    · exact step _ _ hlh le_rfl le_rfl (tle h1) (tle h2) (by simp [keyHull, h1, h2])

/-- **Every coordinate below `n` of a constant of `n` coordinates lies in its interval**
(`constIvlOf`), read centred (`0` past its entries). -/
theorem mem_constIvlOf {p n : ℕ} : ∀ (es : List ℕ) {i : ℕ}, i < n →
    centeredZ p (es.getD i 0) ∈ constIvlOf p n es
  | [], i, _ => by
    simp only [List.getD_nil, constIvlOf, centeredZ, Ivl.mem_mk]
    split_ifs <;> omega
  | c :: es, i, hi => by
    set L := if n ≤ es.length + 1 then es else 0 :: es with hL
    obtain ⟨h1, h2, hall⟩ := keyHull_spec p (centeredKey p c) (centeredKey p c) L le_rfl
    have hk : ∀ x, (keyHull p (centeredKey p c) (centeredKey p c) L).1 ≤ centeredKey p x →
        centeredKey p x ≤ (keyHull p (centeredKey p c) (centeredKey p c) L).2 →
        centeredZ p x ∈ constIvlOf p n (c :: es) := by
      intro x hx1 hx2
      simp only [constIvlOf, ← hL, centeredZ_eq_key, Ivl.mem_mk]
      constructor <;> omega
    rcases i with _ | i
    · exact hk c h1 h2
    · rw [List.getD_cons_succ]
      rcases Nat.lt_or_ge i es.length with hl | hl
      · have hm : es.getD i 0 ∈ L := by
          rw [getD_of_lt _ hl, hL]
          split_ifs
          · exact List.getElem_mem hl
          · exact List.mem_cons_of_mem _ (List.getElem_mem hl)
        exact hk _ (hall _ hm).1 (hall _ hm).2
      · rw [getD_of_ge _ hl]
        have hm : 0 ∈ L := by
          rw [hL, if_neg (by omega)]
          exact List.mem_cons_self
        exact hk 0 (hall _ hm).1 (hall _ hm).2

theorem eq_of_peelStep {e rest : Expr} {c u : ℕ} (h : peelStep e = some (rest, c, u)) :
    e = .add rest (.scale (.const c) (.leaf u)) := by
  unfold peelStep at h
  split at h
  · cases h
    rfl
  · cases h

section

variable (ir : RealizedProgram)

/-! ## Reads before a challenge -/

/-- **Value `v` reads only what is fixed before challenge `j`**, and not `j`. -/
def ReadsBefore (j v : ℕ) : Prop := ∀ rd ∈ ir.nodeReads ir.fuel v, ir.ReadBefore j rd

/-! ## The conditions -/

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

/-- **Group `g` of table `t` is valid**: its members are; it has fewer needles than the
characteristic of `α`'s field; its histograms read only what is fixed before `α`, and not it. -/
structure GroupOk (t g : ℕ) : Prop where
  /-- Every member is valid. -/
  members : ∀ m ∈ ir.members t g, ir.MemberOk t m
  /-- Fewer needles than the characteristic. -/
  size : ir.groupCount t g < (ir.field (ir.chalField (ir.alphaOf t))).characteristic
  /-- The histograms read only what is fixed before the challenge. -/
  hists : ∀ v ∈ ir.histValues t g, ir.ReadsBefore (ir.alphaOf t) v

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

/-! ### The sources of the values' intervals -/
/-- **Value `v`'s coordinates read in field `f` have the interval `J`** at the value ranges `sr`:
some source justifies it (`ivlAt`). -/
def HasIvl (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (f v : ℕ) (J : Ivl) : Prop :=
  ∃ s, ir.ivlAt primeNodes sr f v s = some J

/-- **The values' intervals `L` are justified** at the value ranges `sr`: every interval
`L f v = some J` has a source (`HasIvl`). -/
def LeafIvlsOk (primeNodes : ℕ → List String) (sr : List (ℕ × ℕ)) (L : ℕ → ℕ → Option Ivl) :
    Prop :=
  ∀ f v J, L f v = some J → ir.HasIvl primeNodes sr f v J

/-! ### The values' intervals at the exported sources -/

variable {ir} in
/-- **A predicate of the program is a predicate at an index.** -/
theorem exists_index_of_mem {p : Predicate} (hp : p ∈ ir.predicates) :
    ∃ pid < ir.predicates.length, ir.predicate pid = p := by
  obtain ⟨pid, hpid, rfl⟩ := List.getElem_of_mem hp
  exact ⟨pid, hpid, by rw [predicate_eq_getD,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpid,
    Option.getD_some]⟩

/-- **The intervals at the exported sources are justified**: every interval `ivlTab` gives is its
source's (`HasIvl`). -/
theorem ivlTab_justified (primeNodes : ℕ → List String) (T : NatTrie IvlSource)
    (sr : List (ℕ × ℕ)) : ir.LeafIvlsOk primeNodes sr (ir.ivlTab primeNodes T sr) := by
  intro f v J h
  obtain ⟨s, -, hs⟩ := Option.bind_eq_some_iff.1 h
  exact ⟨s, hs⟩

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

/-! ## The one-digit form of `mod_q` -/

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

/-- **The bounds of a `mod_q`'s digits** in domain `d`: digit `j` bounded by the `j`-th of the
ranges (`digitRangeOf`), one range per digit; none when one is missing. -/
def digitBounds (d : ℕ) (e : Expr) (real : ModRealization) : Option (List ℕ) :=
  if real.digits.length = real.ranges.length then
    (real.digits.zip real.ranges).mapM fun Dr => ir.digitRangeOf d e Dr.1 Dr.2
  else none

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

/-! ## The grouped form of `mod_q` -/

/-- **The bound of the residues** in domain `d`: `2` when a field `equal` `R · R = R` of domain `d`
is their Boolean check (compiler/mod.h, `q = 2`), else the bound of a direct `in` on them
(`exprRange`); `none` without either. -/
def residueBound (d : ℕ) (R : Expr) : Option ℕ :=
  if ir.predicates.any (fun q =>
      match q.body with
      | .equal d' (.mul R₁ R₂) R₃ _ => d' == d && R₁.beq R && R₂.beq R && R₃.beq R
      | _ => false) then some 2
  else ir.exprRange d R

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

section FieldRow

open GordieHowe.Twin

/-- **`fieldRowAtE` as a `Bool`.** -/
def fieldRowAtB (m r : ℕ) : Bool := okB (ir.fieldRowAtE m r)

theorem fieldRowAtB_iff {m r : ℕ} : ir.fieldRowAtB m r = true ↔
    r < ir.predicates.length ∧ (ir.predicate r).role = .realization m ∧
      (match (ir.predicate m).body with
        | .mod d _ e e' real => real.form == .field && ir.fieldRowB d e e' (ir.predicate r).body
        | _ => false) = true := by
  simp only [fieldRowAtB, fieldRowAtE, okB_seqE, okB_guardE, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq]
  exact Iff.rfl

/-- **The row at a checked pointer is a field equation of the program** for `m`'s sides. -/
theorem any_fieldRowB_of_fieldRowAtB {m r d q : ℕ} {e e' : Expr} {real : ModRealization}
    (hm : (ir.predicate m).body = .mod d q e e' real) (h : ir.fieldRowAtB m r = true) :
    ir.predicates.any (fun p => ir.fieldRowB d e e' p.body) = true := by
  obtain ⟨hr, -, hb⟩ := ir.fieldRowAtB_iff.1 h
  rw [hm] at hb
  simp only [Bool.and_eq_true] at hb
  refine List.any_eq_true.2 ⟨ir.predicate r, ?_, hb.2⟩
  rw [predicate_eq_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some]
  exact List.getElem_mem hr

/-- **A pointer that checks names a checked row.** -/
theorem exists_fieldRowAtB_of_ptr {S : Structure} {m : ℕ} (h : okB (ir.fieldRowPtrE S m) = true) :
    ∃ r, ir.fieldRowAtB m r = true := by
  unfold fieldRowPtrE at h
  rw [okB_thenE] at h
  cases hx : fieldRowRecE S m with
  | error e => simp [hx, Except.toOption] at h
  | ok r => exact ⟨r, by simpa [hx, Except.toOption, fieldRowAtB] using h⟩

/-- **A list check passing passes at every index** (`allE`). -/
theorem okB_of_okB_allE {ε α : Type} {f : ℕ → α → Except ε Unit} :
    ∀ {i : ℕ} {l : List α}, okB (allE f i l) = true →
      ∀ j (hj : j < l.length), okB (f (i + j) l[j]) = true
  | _, [], _, _, hj => absurd hj (by simp)
  | i, x :: xs, hok, j, hj => by
    rw [allE, okB_seqE, Bool.and_eq_true] at hok
    cases j with
    | zero => simpa using hok.1
    | succ j =>
      have := okB_of_okB_allE hok.2 j (by simpa using hj)
      rw [show i + (j + 1) = i + 1 + j by omega]
      simpa using this

end FieldRow

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

theorem eq_of_peelTerm {e rest D : Expr} {c : ℕ} (h : peelTerm e = some (rest, c, D)) :
    e = .add rest (.scale (.const c) D) := by
  unfold peelTerm at h
  split at h
  · cases h
    rfl
  · cases h

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
    rw [predicate_eq_getD,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
    exact List.getElem_mem ht
  · rintro ⟨pr, hpr, hg⟩
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hpr
    refine ⟨t, ht, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨ht, ?_⟩
    rwa [predicate_eq_getD,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]

/-! ### The two-tail form: a MAC that no domain hosts -/

variable {ir} in
theorem macBlindCoreB_of_at {L : ℕ → ℕ → Option Ivl} {d b : ℕ} {real : MacRealization}
    (h : ir.macBlindAtB L d b real = true) : ir.macBlindCoreB d b real = true := by
  simp only [macBlindAtB, Bool.and_eq_true] at h
  simp only [macBlindCoreB, Bool.and_eq_true]
  exact h.1

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

variable {ir} in
/-- **`macOddFieldAtB` is sound** (`MacOddFieldOk`, its tail at `t`). -/
theorem macOddFieldOk_of_atB {L : ℕ → ℕ → Option Ivl} {pid d : ℕ} {z : Expr} {b : ℕ}
    {real : MacRealization} {t : ℕ} (h : ir.macOddFieldAtB L pid d z b real t = true) :
    ir.MacOddFieldOk L pid d z b real := by
  simp only [macOddFieldAtB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hc, hb⟩, hz⟩, ht⟩ := h
  have hlt : t < ir.predicates.length := by
    unfold macTailAtB at ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    exact ht.1.1
  exact ⟨hc, hb, hz, t, hlt, ht⟩

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

variable {ir} in
/-- **`macTwoFieldAtB` is sound** (`MacTwoFieldOk`, its tail at `t`). -/
theorem macTwoFieldOk_of_atB {primeNodes : ℕ → List String} {pid d : ℕ} {z : Expr} {b : ℕ}
    {real : MacRealization} {t : ℕ} (h : ir.macTwoFieldAtB primeNodes pid d z b real t = true) :
    ir.MacTwoFieldOk primeNodes pid d z b real := by
  simp only [macTwoFieldAtB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hf, hs⟩, hz⟩, ht⟩ := h
  have hlt : t < ir.predicates.length := by
    unfold macTailTwoB at ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    exact ht.1.1.1
  exact ⟨hf, hs, hz, t, hlt, ht⟩

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

theorem isPrivOrConstT_eq (u : ℕ) : ir.isPrivOrConstT u = ir.isPrivOrConst u := by
  rw [isPrivOrConstT, valueT_eq]
  rfl

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
  cases (ir.value v).kind with
  | bound e =>
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
  | _ => simp

end Checker

end

section Centred

variable (ir : RealizedProgram)

/-- **`centredIvl` with absolute values**: the bounds' absolute values doubled are below the
characteristic. -/
theorem centredIvl_eq (v : ℕ) (cN : ℤ × ℕ) : ir.centredIvl v cN =
    if 2 * |-cN.1| < ir.charOf (ir.valueField v) ∧
        2 * |(cN.2 : ℤ) - 1 - cN.1| < ir.charOf (ir.valueField v)
    then some ⟨-cN.1, (cN.2 : ℤ) - 1 - cN.1⟩ else none := by
  rw [centredIvl, abs_eq_max_neg, abs_eq_max_neg]

end Centred

end GordieHowe.RealizedProgram
