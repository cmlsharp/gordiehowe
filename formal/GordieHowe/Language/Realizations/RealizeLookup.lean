-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.RealizeInteger
public import GordieHowe.Language.Library.Eval
public import GordieHowe.Foundations.Probability.RangeGroups

@[expose] public section

/-!
# GordieHowe: the lookups of the realized program

The lemmas that turn a group's LogUp identity (`GordieHowe.RealizedProgram.LogupHolds`) into its needles in the table
or a bad `α`, bound that event, and turn needles in the table into the `in` predicates they
realize.

* **A group's identity** (`GordieHowe.RealizedProgram.needlesIn_or_logupBad`): every needle is a row of the table
  (`GordieHowe.RealizedProgram.NeedlesIn`), or `α` is a root of the group's lookup polynomial. For a range,
  `Range.rangeArgument_sound`, with `α` outside the table values by the type of its sampler
  (`GordieHowe.RealizedProgram.Env.Sampled`, `Range.LookupChallenge`); for any other table (committed columns or an
  expression's coordinates), `Range.committedArgument_sound`, at every `α`. Both need the group's size below the
  characteristic.
* **The bad `α`** (`GordieHowe.RealizedProgram.probUniform_exists_logupBad_le`, `probUniform_exists_badAt_compl_le`):
  for lookup polynomials fixed before `α` is drawn, `α` uniform outside `[0, tmax)` is a root of
  one of them with probability at most the sum of their degrees over `|F| − tmax`; a group's
  degree is `N_g + T − 1`.
* **Covered needles**: where every group of the table has its needles
  in the table, every coordinate of a needle the groups' members tile is the cast of a natural
  below `T`.
* **Direct lookups** (`GordieHowe.RealizedProgram.memHolds_of_lookup`): the needle is the record, a row of the range,
  of the committed table or of the table of an expression's coordinates; for an `in` into the
  entries of an expression `e'` (`InSet.expr`, the paper's `in(e, e')`), the table's rows are `e'`'s
  coordinates (`DirectSet`). Conversely an `in` that holds puts the coordinates of its needle among the
  rows (`GordieHowe.RealizedProgram.needleRows_of_memHolds`).
* **Complement lookups**: the needle
  `(N − 1) − v` is a natural `k < T` and the record's integer reading `V` lies in `[0, p − T]`
  (`exprIvl_within`), so `N − 1 − V − k` is a multiple of `p` of absolute value below `p`, so zero:
  `V ≤ N − 1`. Conversely `v < N` puts the needle `N − 1 − v` in `[0, N) ⊆ [0, T)`
  (`GordieHowe.RealizedProgram.needle_isNatBelow_of_complement`).
* **Values bound to their digits** (`boundDigitsOk`): where
  every bound value reads its expression (`GordieHowe.RealizedProgram.BoundReads`, the realized assignment), a record
  bound to the sum `d_0 + Σ_{j ≥ 1} T^j d_j` (`peel_spec`, `posChainOk_sum`) is the value of its
  digits in base `T`.
* **Two-sided lookups** (`TwoSidedOk`): the digits are naturals
  below `T`; the reconstruction row (`peel_spec`, `chainOk_sum`, `digitsVal_natCast`), or the record
  bound to its digits, makes the record the number `A < T^k` of the digits `d_j`, and the top row
  makes `N − 1` the number `A + B` with `B < T^k`; as `A + B < p`, `A ≤ N − 1`. The honest prover
  reads the digits below `T` (`GordieHowe.RealizedProgram.DigitsBelow`).
* **Digit lookups** (`DigitsOk`): the digits are naturals below `T`
  and the reconstruction row, or the record bound to them, makes the record
  their number `A < T^k ≤ N`.
* **The honest prover**: where the program holds and the two-sided
  and digit lookups' digits are below their bases, every group of a table has its needles among
  the table's rows.
-/

namespace GordieHowe.RealizedProgram

open Export Range IOP
open scoped NNReal ENNReal

/-! ## Uniform challenges -/

/-- **Lookup polynomials at a challenge uniform outside `U`**: some event of the list `l` is bad
with probability at most the sum of their degrees over `|F| − |U|`. -/
theorem probUniform_exists_badAt_compl_le {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    (U : Finset F) [Nonempty {x : F // x ∉ U}] (l : List ι) (ev : ι → ChallengeEvent F) :
    Pr[a ← {x : F // x ∉ U} : ∃ i ∈ l, (ev i).BadAt a] ≤
      (((((l.map fun i => (ev i).deg).sum : ℕ) : ℝ≥0) / (Fintype.card F - U.card : ℕ) : ℝ≥0) :
        ℝ≥0∞) := by
  induction l with
  | nil =>
    have : {a : {x : F // x ∉ U} | ∃ i ∈ ([] : List ι), (ev i).BadAt a} = ∅ := by simp
    simp only [probUniform, this, MeasureTheory.measure_empty]
    exact zero_le
  | cons i l ih =>
    simp only [List.mem_cons, exists_eq_or_imp]
    refine (probUniform_or_le_add (ChallengeEvent.probUniform_badAt_le_compl (ev i) U) ih).trans
      (le_of_eq ?_)
    rw [List.map_cons, List.sum_cons, Nat.cast_add, add_div]

/-- **One coordinate of a challenge of one coordinate drawn outside `[0, T)`** is uniform among
the lookup challenges. -/
theorem probUniform_lookupCoord {F : FieldInterp} {n : ℕ} (hn : n = 1) (h0 : 0 < n) {s : Sampler}
    {T : ℕ} (hs : s = .fieldMinusTables (.range T)) (P : F.K → Prop) :
    Pr[c ← (Fin n → F.SamplerTy s) : P (F.samplerVal s (c ⟨0, h0⟩))] =
      Pr[a ← LookupChallenge F.K T : P a.val] := by
  subst hn hs
  exact Uniform.probUniform_comp (f := fun c : Fin 1 → LookupChallenge F.K T => c ⟨0, h0⟩)
    (Uniform.of_equiv (Equiv.funUnique (Fin 1) (LookupChallenge F.K T))) fun a => P a.val

/-- **A value of the sampler outside `[0, T)` is not a table value** when `T` is below the
characteristic. -/
theorem samplerVal_notMem_tableValues {F : FieldInterp} {p : ℕ} [CharP F.K p] {s : Sampler}
    {T : ℕ} (hs : s = .fieldMinusTables (.range T)) (hT : T < p) (x : F.SamplerTy s) :
    F.samplerVal s x ∉ tableValues T := by
  subst hs
  change x.val ∉ tableValues T
  rw [← excluded_of_lt_char hT]
  exact x.2

section

variable {ir : RealizedProgram} {I : Interp}

/-! ## Fields -/

/-- **An expression's coordinate read in two equal fields** is the cast of a natural below `T` in
both or in neither. -/
theorem isNatBelow_evalE_iff {f f' : ℕ} (h : f = f') (rd : ir.Valuation I) (e : Expr) (i T : ℕ) :
    IsNatBelow T (ir.evalE rd f e i) ↔ IsNatBelow T (ir.evalE rd f' e i) := by
  subst h
  rfl

/-! ## Shared expressions -/

/-- **A matching needle has its record's values.** -/
theorem evalE_of_needleMatches (ho : ir.RefsOrdered) {e' e : Expr}
    (h : ir.needleMatches e' e = true) (rd : ir.Valuation I) (f : ℕ) :
    ir.evalE rd f e' = ir.evalE rd f e := by
  unfold needleMatches at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · rw [Expr.eq_of_beq h]
  · cases e' with
    | ref k =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rw [evalE_ref ho rd f h.1, Expr.eq_of_beq h.2]
    | _ => exact absurd h Bool.false_ne_true

/-- **A matching needle has its record's length.** -/
theorem exprLen_of_needleMatches (ho : ir.RefsOrdered) {e' e : Expr}
    (h : ir.needleMatches e' e = true) : ir.exprLen e' = ir.exprLen e := by
  unfold needleMatches at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · rw [Expr.eq_of_beq h]
  · cases e' with
    | ref k =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rw [exprLen_ref ho h.1, Expr.eq_of_beq h.2]
    | _ => exact absurd h Bool.false_ne_true

/-- **One record and one needle matching it.** -/
theorem exists_of_singleMatch {recs needles : List Expr} (h : ir.singleMatch recs needles = true) :
    ∃ e e', recs = [e] ∧ needles = [e'] ∧ ir.needleMatches e' e = true := by
  match recs, needles, h with
  | [e], [e'], h => exact ⟨e, e', rfl, rfl, h⟩

/-! ## Members -/

/-- **The lookup realization of an `in`.** -/
theorem lookupOf?_eq_some {b : PredBody} {r : LookupRealization} :
    lookupOf? b = some r ↔ ∃ d recs set, b = .mem d recs set (.lookup r) := by
  constructor
  · intro h
    rcases b with _ | ⟨d, recs, set, r' | _⟩ | _ | _ <;> simp [lookupOf?] at h
    exact ⟨d, recs, set, by rw [h]⟩
  · rintro ⟨d, recs, set, rfl⟩
    rfl

/-- **The needle of an `in`**: needle `n` of predicate `pid` is needle `n` of its realization. -/
theorem needleExpr_eq {pid d n : ℕ} {recs : List Expr} {set : InSet} {r : LookupRealization}
    (hp : (ir.predicate pid).body = .mem d recs set (.lookup r)) :
    ir.needleExpr pid n = r.needles.getD n default := by
  simp [needleExpr, hp, lookupOf?]

/-- **The runs of a needle** are the coordinates of the members of the table's groups for it. -/
theorem mem_coverRuns {t pid n : ℕ} {fc : ℕ × ℕ} :
    fc ∈ ir.coverRuns t pid n ↔ ∃ g < ir.groupCountOf t, ∃ m ∈ ir.members t g,
      m.pred = pid ∧ m.needle = n ∧ (m.first, m.count) = fc := by
  simp only [coverRuns, List.mem_filterMap, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨m, ⟨g, hg, hm⟩, h⟩
    split_ifs at h with hc
    exact ⟨g, hg, m, hm, hc.1, hc.2, Option.some.inj h⟩
  · rintro ⟨g, hg, m, hm, h1, h2, h3⟩
    exact ⟨m, ⟨g, hg, hm⟩, by simp only [h1, h2, and_self, ↓reduceIte, h3]⟩

/-- **A member's coordinate is a needle of its group.** -/
theorem mem_groupNeedles {rd : ir.Valuation I} {f t g : ℕ} {m : Member}
    (hm : m ∈ ir.members t g) {c : ℕ} (hc : c < m.count) :
    ir.evalE rd f (ir.needleExpr m.pred m.needle) (m.first + c) ∈ ir.groupNeedles rd f t g :=
  List.mem_flatMap.2 ⟨m, hm, List.mem_map.2 ⟨c, List.mem_range.2 hc, rfl⟩⟩

/-- **A needle of a group is a member's coordinate.** -/
theorem exists_of_mem_groupNeedles {rd : ir.Valuation I} {f t g : ℕ}
    {v : (I f).K} (hv : v ∈ ir.groupNeedles rd f t g) :
    ∃ m ∈ ir.members t g, ∃ c < m.count, ir.evalE rd f (ir.needleExpr m.pred m.needle) (m.first + c) = v := by
  obtain ⟨m, hm, hv⟩ := List.mem_flatMap.1 hv
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hv
  exact ⟨m, hm, c, List.mem_range.1 hc, rfl⟩

/-! ## Rows -/

/-- **Every needle of group `g` of table `t` is a row of the table**, reading values by `rd`, in
`α`'s field. -/
def NeedlesIn (rd : ir.Valuation I) (t g : ℕ) : Prop :=
  Range.InRows (ir.tableRow rd (ir.chalField (ir.alphaOf t)) t)
    (ir.groupNeedles rd (ir.chalField (ir.alphaOf t)) t g)

/-- **A table whose rows are a range is a range.** -/
theorem isRange_of_rows {t T : ℕ} (h : (ir.table t).rows = .range T) : ir.IsRange t := by
  simp [IsRange, tableSize, h]

/-- **The size of a committed table** is its column's. -/
theorem tableSize_of_columns {t : ℕ} {cols : List ℕ} (h : (ir.table t).rows = .columns cols) :
    ir.tableSize t = (ir.value (cols.headD 0)).size := by
  simp [tableSize, h]

/-- **Row `j` of a range** is `j`. -/
theorem tableRow_of_isRange {t : ℕ} (hr : ir.IsRange t) (rd : ir.Valuation I) (f : ℕ)
    (j : Fin (ir.tableSize t)) : ir.tableRow rd f t j = (j : (I f).K) := by
  unfold tableRow
  split
  · rfl
  · rename_i cols h
    rw [IsRange, h] at hr
    cases hr
  · rename_i e' h
    rw [IsRange, h] at hr
    cases hr

/-- **Row `j` of a committed table** is coordinate `j` of its column. -/
theorem tableRow_of_columns {t : ℕ} {cols : List ℕ} (h : (ir.table t).rows = .columns cols)
    (rd : ir.Valuation I) (f : ℕ) (j : Fin (ir.tableSize t)) :
    ir.tableRow rd f t j = castElt (rd (cols.headD 0) j) := by
  unfold tableRow
  split
  · rename_i T h'
    rw [h] at h'
    cases h'
  · rename_i cols' h'
    rw [h] at h'
    cases h'
    rfl
  · rename_i e' h'
    rw [h] at h'
    cases h'

/-- **The size of a table of an expression's coordinates** is the expression's length. -/
theorem tableSize_of_expr {t : ℕ} {e' : Expr} (h : (ir.table t).rows = .expr e') :
    ir.tableSize t = ir.exprLen e' := by
  simp [tableSize, h]

/-- **Row `j` of a table of an expression's coordinates** is coordinate `j` of the expression. -/
theorem tableRow_of_expr {t : ℕ} {e' : Expr} (h : (ir.table t).rows = .expr e')
    (rd : ir.Valuation I) (f : ℕ) (j : Fin (ir.tableSize t)) :
    ir.tableRow rd f t j = ir.evalE rd f e' j := by
  unfold tableRow
  split
  · rename_i T h'
    rw [h] at h'
    cases h'
  · rename_i cols h'
    rw [h] at h'
    cases h'
  · rename_i e'' h'
    rw [h] at h'
    cases h'
    rfl

/-- **Row equality in two equal fields**: a value is a row in both or in neither. -/
theorem exists_tableRow_eq_iff {f f' : ℕ} (h : f = f') (rd : ir.Valuation I) (t : ℕ) (e : Expr)
    (i : ℕ) : (∃ j, ir.tableRow rd f t j = ir.evalE rd f e i) ↔
      ∃ j, ir.tableRow rd f' t j = ir.evalE rd f' e i := by
  subst h
  rfl

/-- **The needles of a range's group are rows iff they lie in the table.** -/
theorem needlesIn_iff_inTable {t : ℕ} (hr : ir.IsRange t) (rd : ir.Valuation I) (g : ℕ) :
    ir.NeedlesIn rd t g ↔
      InTable (ir.tableSize t) (ir.groupNeedles rd (ir.chalField (ir.alphaOf t)) t g) := by
  unfold NeedlesIn
  rw [show ir.tableRow rd (ir.chalField (ir.alphaOf t)) t =
      fun j : Fin (ir.tableSize t) => (j : (I (ir.chalField (ir.alphaOf t))).K) from
    funext (tableRow_of_isRange hr rd _), inRows_natCast_iff]

/-! ## A group's identity -/

/-- **`α` avoids a range's values**: in a sampled environment, coordinate `0` of a valid range
table's challenge is a value of its sampler, outside `[0, tmax) ⊇ [0, T)`. -/
theorem alpha_notMem_tableValues {t : ℕ} (hv : ir.TableOk t) (hr : ir.IsRange t)
    (hI : I.Registered ir) {e : ir.Env I} (he : Env.Sampled ir e) :
    e.chal (ir.alphaOf t) 0 ∉ tableValues (ir.tableSize t) := by
  have := charP_field hI hv.field
  obtain ⟨x, hx⟩ := he _ hv.alpha 0 (by rw [hv.size]; omega)
  rw [hx]
  exact fun h => samplerVal_notMem_tableValues hv.sampler hv.char x
    (tableValues_mono (hv.tmax hr) h)

/-- **A group's LogUp identity**: its needles are rows of the table, or `α` is a root of its lookup
polynomial: for a range by `Range.rangeArgument_sound`, `α` outside the table values; for any
other table (committed columns, an expression's coordinates) by `Range.committedArgument_sound`, at every `α` (the paper's `lem:logup-point`,
parts (1) and (3)). -/
theorem needlesIn_or_logupBad {t g : ℕ} (hv : ir.TableOk t)
    (hg : g < ir.groupCountOf t) (hI : I.Registered ir) {e : ir.Env I} (he : Env.Sampled ir e)
    (h : ir.LogupHolds e t g) :
    ir.NeedlesIn (ir.reader e) t g ∨
      (ir.groupEvent (ir.reader e) (ir.chalField (ir.alphaOf t)) t g).BadAt
        (e.chal (ir.alphaOf t) 0) := by
  have := charP_field hI hv.field
  have hsize : (ir.groupNeedles (ir.reader e) (ir.chalField (ir.alphaOf t)) t g).length <
      (ir.field (ir.chalField (ir.alphaOf t))).characteristic := by
    rw [length_groupNeedles]
    exact (hv.groups g hg).size
  unfold LogupHolds logupAt at h
  unfold groupEvent
  rcases hrows : (ir.table t).rows with T | cols | e'
  · simp only [hrows] at h ⊢
    rw [needlesIn_iff_inTable (isRange_of_rows hrows)]
    exact rangeArgument_sound hsize le_rfl
      (alpha_notMem_tableValues hv (isRange_of_rows hrows) hI he) h
  · simp only [hrows] at h ⊢
    exact committedArgument_sound hsize h
  · simp only [hrows] at h ⊢
    exact committedArgument_sound hsize h

/-! ## The bad `α` -/

/-- **Lookup polynomials fixed before `α`** at a valid table's challenge `α`: some event of the
list `l` is bad at `α` with probability at most the sum of their degrees over `|F| − tmax`. -/
theorem probUniform_exists_logupBad_le {t : ℕ} (hv : ir.TableOk t)
    (hI : I.Registered ir) {ι : Type} (l : List ι)
    (ev : ι → ChallengeEvent (I (ir.chalField (ir.alphaOf t))).K) (e : ir.Env I) :
    Pr[c ← ir.ChalVal I (ir.alphaOf t) :
        ∃ i ∈ l, (ev i).BadAt ((e.setChal (ir.alphaOf t) c).chal (ir.alphaOf t) 0)] ≤
      (((((l.map fun i => (ev i).deg).sum : ℕ) : ℝ≥0) /
        (Fintype.card (I (ir.chalField (ir.alphaOf t))).K - ir.tmaxOf (ir.alphaOf t) : ℕ) :
          ℝ≥0) : ℝ≥0∞) := by
  have := charP_field hI hv.field
  have h0 : 0 < (ir.challenge (ir.alphaOf t)).size := by rw [hv.size]; omega
  simp only [setChal_chal_zero e _ h0]
  rw [probUniform_lookupCoord hv.size h0 hv.sampler
    (fun x => ∃ i ∈ l, (ev i).BadAt x)]
  have h := probUniform_exists_badAt_compl_le (excluded (I (ir.chalField (ir.alphaOf t))).K
    (ir.tmaxOf (ir.alphaOf t))) l ev
  rwa [card_excluded_of_lt_char hv.char] at h

/-! ## Direct lookups -/

/-- **A record in the range `[0, T)`**: the coordinate is the cast of a natural below `T`. -/
theorem inRows_range_iff (rd : ir.Valuation I) (d : ℕ) (e : Expr) (i T : ℕ) :
    ir.InRows rd d [e] i (.range T) ↔ IsNatBelow T (ir.evalWith rd d e i) := by
  simp only [InRows, List.mem_singleton, forall_eq, IsNatBelow]
  exact exists_congr fun k => and_congr_right fun _ => eq_comm

/-- **A record in the rows of a valid table**, for a direct lookup's set: the coordinate is a row
(`tableRow`), read in the domain's field. For a range, the cast of a natural below `T`; for a
committed table (one record against its first column, `InRows`), a coordinate of the column; for
the entries of an expression `e'` (`InSet.expr`), or a table whose rows are `e'`'s coordinates, a
coordinate of `e'`. -/
theorem inSetWith_iff_tableRow {pid d : ℕ} {recs : List Expr} {set : InSet}
    {r : LookupRealization} (hd : ir.DirectOk pid d recs set r) (ht : ir.TableOk r.table)
    (rd : ir.Valuation I) (e : Expr) (i : ℕ) :
    ir.InSetWith rd d [e] i set ↔
      ∃ j, ir.tableRow rd (ir.domainField d) r.table j = ir.evalWith rd d e i := by
  have hrange : ir.IsRange r.table → (IsNatBelow (ir.tableSize r.table) (ir.evalWith rd d e i) ↔
      ∃ j, ir.tableRow rd (ir.domainField d) r.table j = ir.evalWith rd d e i) := fun hr => by
    simp only [tableRow_of_isRange hr, isNatBelow_iff_exists_fin]
  have hexpr : ∀ e', (ir.table r.table).rows = .expr e' →
      (ir.InRows rd d [e] i (.expr e') ↔
        ∃ j, ir.tableRow rd (ir.domainField d) r.table j = ir.evalWith rd d e i) := by
    intro e' hrows
    simp only [InRows, List.mem_singleton, forall_eq, tableRow_of_expr hrows, Fin.exists_iff,
      tableSize_of_expr hrows, evalWith]
    exact exists_congr fun j => ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩
  have hs := hd.set
  cases set with
  | range n =>
    obtain ⟨rfl, hr⟩ := hs
    exact (inRows_range_iff rd d e i _).trans (hrange hr)
  | expr e' => exact hexpr e' hs
  | table t' =>
    obtain rfl : t' = r.table := hs
    change ir.InRows rd d [e] i (ir.table r.table).rows ↔ _
    rcases hrows : (ir.table r.table).rows with T | cols | e'
    · have hr := isRange_of_rows hrows
      have hT : ir.tableSize r.table = T := by simp [tableSize, hrows]
      rw [← hrange hr, hT]
      exact inRows_range_iff rd d e i T
    · have hc : ir.ColumnsOk r.table cols := by
        have := ht.rows
        rw [hrows] at this
        exact this
      obtain ⟨c, rest, rfl⟩ := List.exists_cons_of_ne_nil hc.nonempty
      simp only [InRows, List.headD_cons, List.zip_cons_cons, List.zip_nil_left,
        List.mem_singleton, forall_eq, tableRow_of_columns hrows, Fin.exists_iff,
        tableSize_of_columns hrows]
      exact exists_congr fun j => ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩
    · exact hexpr e' hrows

/-- **A direct `in` holds where its needle's coordinates are rows of the table**, read in `α`'s
field. -/
theorem holdsWith_iff_of_direct (ho : ir.RefsOrdered) {pid d : ℕ}
    {recs : List Expr} {set : InSet} {r : LookupRealization} (hd : ir.DirectOk pid d recs set r)
    (ht : ir.TableOk r.table) (rd : ir.Valuation I) :
    ir.HoldsWith rd (.mem d recs set (.lookup r)) ↔
      ∀ i < ir.exprLen (r.needles.getD 0 default), ∃ j,
        ir.tableRow rd (ir.chalField (ir.alphaOf r.table)) r.table j =
          ir.evalE rd (ir.chalField (ir.alphaOf r.table)) (r.needles.getD 0 default) i := by
  obtain ⟨e, e', rfl, hn, hm⟩ := exists_of_singleMatch hd.record
  have hf : ir.chalField (ir.alphaOf r.table) = ir.domainField d := by rw [ht.domain, hd.domain]
  simp only [HoldsWith, List.headD_cons, inSetWith_iff_tableRow hd ht, hn, List.getD_cons_zero,
    exprLen_of_needleMatches ho hm, evalE_of_needleMatches ho hm, evalWith,
    exists_tableRow_eq_iff hf]

/-- **A coordinate covered by the groups' members is a needle of one of the groups**. -/
theorem exists_mem_groupNeedles {pid d n : ℕ} {recs : List Expr} {set : InSet}
    {r : LookupRealization} (hp : (ir.predicate pid).body = .mem d recs set (.lookup r))
    (rd : ir.Valuation I) (f : ℕ)
    (hcov : tiles (ir.coverRuns r.table pid n) 0 (ir.exprLen (r.needles.getD n default)) = true)
    {i : ℕ} (hi : i < ir.exprLen (r.needles.getD n default)) :
    ∃ g < ir.groupCountOf r.table,
      ir.evalE rd f (r.needles.getD n default) i ∈ ir.groupNeedles rd f r.table g := by
  obtain ⟨fc, hfc, h1, h2⟩ := tiles_cover hcov i (Nat.zero_le i) hi
  obtain ⟨g, hg, m, hm, hpred, hneedle, hfc'⟩ := mem_coverRuns.1 hfc
  subst hfc'
  have hmem := mem_groupNeedles (rd := rd) (f := f) hm (c := i - m.first) (by simp only at h2; omega)
  rw [hpred, hneedle, needleExpr_eq hp, Nat.add_sub_cancel' h1] at hmem
  exact ⟨g, hg, hmem⟩

/-- **A needle covered by the groups' members has its coordinates among the rows** where every group
of the table has its needles among them (`exists_mem_groupNeedles`). -/
theorem needle_mem_rows {pid d n : ℕ} {recs : List Expr} {set : InSet} {r : LookupRealization}
    (hp : (ir.predicate pid).body = .mem d recs set (.lookup r)) {rd : ir.Valuation I}
    (hcov : tiles (ir.coverRuns r.table pid n) 0 (ir.exprLen (r.needles.getD n default)) = true)
    (hin : ∀ g < ir.groupCountOf r.table, ir.NeedlesIn rd r.table g)
    {i : ℕ} (hi : i < ir.exprLen (r.needles.getD n default)) :
    ∃ j, ir.tableRow rd (ir.chalField (ir.alphaOf r.table)) r.table j =
      ir.evalE rd (ir.chalField (ir.alphaOf r.table)) (r.needles.getD n default) i := by
  obtain ⟨g, hg, hmem⟩ := exists_mem_groupNeedles hp rd _ hcov hi
  exact (hin g hg : Range.InRows _ _) _ hmem

/-- **A direct `in` holds where every group of its table has its needles among the rows**: the
groups' members cover every coordinate of its needle and the needle is its
record. -/
theorem memHolds_of_lookup (ho : ir.RefsOrdered) {pid d : ℕ} {recs : List Expr}
    {set : InSet} {r : LookupRealization} (hp : (ir.predicate pid).body = .mem d recs set (.lookup r))
    (hd : ir.DirectOk pid d recs set r) (ht : ir.TableOk r.table) {rd : ir.Valuation I}
    (hin : ∀ g < ir.groupCountOf r.table, ir.NeedlesIn rd r.table g) :
    ir.HoldsWith rd (.mem d recs set (.lookup r)) := by
  rw [holdsWith_iff_of_direct ho hd ht]
  intro i hi
  have hlen : 0 < r.needles.length := by
    obtain ⟨_, _, _, hn, _⟩ := exists_of_singleMatch hd.record
    rw [hn]
    exact Nat.zero_lt_one
  exact needle_mem_rows hp (hd.covered 0 hlen) hin hi

/-- **An `in` that holds puts its needle's coordinates among the rows.** -/
theorem needleRows_of_memHolds (ho : ir.RefsOrdered) {pid d : ℕ}
    {recs : List Expr} {set : InSet} {r : LookupRealization} (hd : ir.DirectOk pid d recs set r)
    (ht : ir.TableOk r.table) {rd : ir.Valuation I}
    (h : ir.HoldsWith rd (.mem d recs set (.lookup r))) {i : ℕ}
    (hi : i < ir.exprLen (r.needles.getD 0 default)) :
    ∃ j, ir.tableRow rd (ir.chalField (ir.alphaOf r.table)) r.table j =
      ir.evalE rd (ir.chalField (ir.alphaOf r.table)) (r.needles.getD 0 default) i :=
  (holdsWith_iff_of_direct ho hd ht rd).1 h i hi

/-! ## Complement lookups -/

/-- **One step of dereferencing keeps an expression's values.** -/
theorem evalE_deref (ho : ir.RefsOrdered) (rd : ir.Valuation I) (f : ℕ) (e : Expr) :
    ir.evalE rd f (ir.deref e) = ir.evalE rd f e := by
  cases e with
  | ref k =>
    simp only [deref]
    split_ifs with hk
    · exact (evalE_ref ho rd f hk).symm
    · rfl
  | _ => rfl

variable {primeNodes : ℕ → List String} {L : ℕ → ℕ → Option Ivl}

/-- **The value of `top + (p − 1) · rec'`** at a coordinate below the record's length: `(N − 1) − v`
for `top` a constant holding `N − 1` and `rec'` matching the record `rec`. -/
theorem evalE_minus (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I} (hF : ir.LeafFacts rd) {d N top c : ℕ} {rec rec' : Expr}
    (hd : d < ir.domains.length) (hc : c + 1 = ir.charOf (ir.domainField d))
    (hnm : ir.needleMatches rec' rec = true)
    (hca : ir.constAll top (N - 1) (ir.exprLen rec) (ir.domainField d) = true)
    (hN : N - 1 < ir.charOf (ir.domainField d)) {i : ℕ} (hi : i < ir.exprLen rec) :
    ir.evalE rd (ir.domainField d) (.add (.leaf top) (.scale (.const c) rec')) i =
      ((N - 1 : ℕ) : (I (ir.domainField d)).K) - ir.evalE rd (ir.domainField d) rec i := by
  have hf := domainField_lt hwf hd
  have hchar := charP_field hI hf
  rw [evalE_add, evalE_scale_const, evalE_of_needleMatches hwf.refsOrdered hnm,
    evalE_leaf_constAll hL hF hca hf hN hi,
    hL.decode_natCast _ hf c (by simp only [charOf] at hc; omega)]
  have hc1 : ((c : ℕ) : (I (ir.domainField d)).K) = -1 := by
    rw [eq_neg_iff_add_eq_zero, ← Nat.cast_one, ← Nat.cast_add, hc]
    exact CharP.cast_eq_zero _ _
  rw [hc1]
  ring

/-- **The value of a complement needle** at a coordinate below the record's length: `(N − 1) − v`
(`complementMatch`). -/
theorem evalE_complement (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} (hF : ir.LeafFacts rd) {d N : ℕ}
    {rec ne : Expr} (hd : d < ir.domains.length) (hm : ir.complementMatch d N rec ne = true)
    (hN : N - 1 < ir.charOf (ir.domainField d)) {i : ℕ} (hi : i < ir.exprLen rec) :
    ir.evalE rd (ir.domainField d) ne i =
      ((N - 1 : ℕ) : (I (ir.domainField d)).K) - ir.evalE rd (ir.domainField d) rec i := by
  unfold complementMatch at hm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
  obtain ⟨-, hm⟩ := hm
  rw [← evalE_deref hwf.refsOrdered]
  split at hm
  · rename_i top c rec' hne
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
    obtain ⟨⟨hc, hnm⟩, hca⟩ := hm
    rw [hne]
    exact evalE_minus hwf hI hL hF hd hc hnm hca hN hi
  · cases hm

/-- The record of a one-record `in`. -/
theorem eq_singleton_headD {recs : List Expr} (h : recs.length = 1) :
    recs = [recs.headD default] := by
  match recs, h with
  | [e], _ => rfl

variable (ir) in
/-- **A complement lookup's shape without the record's interval** (the record's interval left
out). -/
structure ComplementCore (pid d : ℕ) (recs : List Expr) (set : InSet) (r : LookupRealization) :
    Prop where
  table : r.table < ir.tables.length
  domain : d = (ir.table r.table).domain
  rangeTable : ir.IsRange r.table
  single : recs.length = 1
  range : set = .range set.bound
  pos : 0 < set.bound
  le : set.bound ≤ ir.tableSize r.table
  needle : r.needles.length = 1
  complement : ir.complementMatch d set.bound (recs.headD default) (r.needles.headD default) = true
  char : 2 < ir.charOf (ir.domainField d)
  refs : ∀ e ∈ r.needles, ∀ k ∈ e.refs, k < ir.exprs.length
  covered : ∀ n < r.needles.length,
    tiles (ir.coverRuns r.table pid n) 0 (ir.exprLen (r.needles.getD n default)) = true

theorem complementCore_iff (pid d : ℕ) (recs : List Expr) (set : InSet) (r : LookupRealization) :
    ir.ComplementCore pid d recs set r ↔
      r.table < ir.tables.length ∧ d = (ir.table r.table).domain ∧ ir.IsRange r.table ∧
        recs.length = 1 ∧ set = .range set.bound ∧ 0 < set.bound ∧
        set.bound ≤ ir.tableSize r.table ∧ r.needles.length = 1 ∧
        ir.complementMatch d set.bound (recs.headD default) (r.needles.headD default) = true ∧
        2 < ir.charOf (ir.domainField d) ∧ (∀ e ∈ r.needles, ∀ k ∈ e.refs, k < ir.exprs.length) ∧
        ∀ n < r.needles.length,
          tiles (ir.coverRuns r.table pid n) 0 (ir.exprLen (r.needles.getD n default)) = true :=
  ⟨fun h => ⟨h.table, h.domain, h.rangeTable, h.single, h.range, h.pos, h.le, h.needle,
      h.complement, h.char, h.refs, h.covered⟩,
    fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩⟩

instance (pid d : ℕ) (recs : List Expr) (set : InSet) (r : LookupRealization) :
    Decidable (ir.ComplementCore pid d recs set r) :=
  decidable_of_iff _ (complementCore_iff pid d recs set r).symm

/-- **A complement `in` that holds puts its needle's coordinates in the table**: the record is the
cast of a natural `k < N`, so the needle is the cast of `N − 1 − k < N ≤ T`. -/
theorem needle_isNatBelow_of_complement (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {pid d : ℕ} {recs : List Expr} {set : InSet}
    {r : LookupRealization} (hpid : pid < ir.predicates.length)
    (hp : (ir.predicate pid).body = .mem d recs set (.lookup r))
    (hc : ir.ComplementCore pid d recs set r) (ht : ir.TableOk r.table)
    {rd : ir.Valuation I} (hF : ir.LeafFacts rd) (h : ir.HoldsWith rd (.mem d recs set (.lookup r)))
    {i : ℕ} (hi : i < ir.exprLen (r.needles.getD 0 default)) :
    IsNatBelow (ir.tableSize r.table)
      (ir.evalE rd (ir.chalField (ir.alphaOf r.table)) (r.needles.getD 0 default) i) := by
  have hpo := hwf.predicates _ (predicate_mem hpid)
  rw [hp] at hpo
  have hrecs := eq_singleton_headD hc.single
  have hneed := eq_singleton_headD hc.needle
  set rec := recs.headD default
  set ne := r.needles.headD default
  set N := set.bound
  have he := hpo.1 (d, rec) (by simp [PredBody.exprs, hrecs])
  have hαf : ir.chalField (ir.alphaOf r.table) = ir.domainField d := by
    rw [ht.domain, hc.domain]
  have hT := ht.tmax hc.rangeTable
  have hTp := ht.char
  rw [hαf] at hTp
  have hm := hc.complement
  have hlen : ir.exprLen ne = ir.exprLen rec := by
    unfold complementMatch at hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
    exact hm.1
  rw [hneed, List.getD_cons_zero] at hi ⊢
  rw [isNatBelow_evalE_iff hαf]
  rw [hrecs, hc.range] at h
  obtain ⟨k, hkN, hk⟩ := h i (by simpa [hlen] using hi) _ (List.mem_singleton_self _)
  have hN1 : N - 1 < ir.charOf (ir.domainField d) := by
    have := hc.le
    have := hc.pos
    simp only [charOf]
    omega
  have hle := hc.le
  refine ⟨N - 1 - k, by omega, ?_⟩
  rw [evalE_complement hwf hI hL hF he.1 hm hN1 (by rw [← hlen]; exact hi)]
  change _ = _ - ir.evalWith rd d rec i
  rw [hk, Nat.cast_sub (by omega)]

/-! ## Two-sided lookups -/

/-- **A left-nested sum peeled** (`peel`): its coordinates are the head's plus the terms
`decode c · u`, and its length is the head's. -/
theorem peel_spec (rd : ir.Valuation I) (f : ℕ) : ∀ (n : ℕ) (L : Expr) {h : Expr}
    {ts : List (ℕ × ℕ)}, peel n L = some (h, ts) →
      (∀ i, ir.evalE rd f L i = ir.evalE rd f h i +
        (ts.map fun cu => (I f).decode cu.1 * castElt (rd cu.2 i)).sum) ∧
      ir.exprLen L = ir.exprLen h
  | 0, L, h, ts, hp => by
    simp only [peel, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    simp
  | n + 1, L, h, ts, hp => by
    simp only [peel, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at hp
    obtain ⟨⟨rest, c, u⟩, hs, ⟨h', ts'⟩, hp', rfl, rfl⟩ := hp
    rw [eq_of_peelStep hs]
    obtain ⟨hev, hlen⟩ := peel_spec rd f n rest hp'
    refine ⟨fun i => ?_, ?_⟩
    · rw [evalE_add, evalE_scale_const, evalE_leaf, hev i, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      ring
    · simp only [exprLen, Expr.len] at hlen ⊢
      exact hlen

/-- **The value of the digits `ys` in base `T`**, least significant first. -/
def digitsVal {K : Type} [Semiring K] (T : K) (ys : List K) : K :=
  ys.foldr (fun y acc => y + T * acc) 0

/-- **Digits that are casts of naturals** have the cast of their number (`Nat.ofDigits`). -/
theorem digitsVal_natCast {K : Type} [Semiring K] (T : ℕ) :
    ∀ as : List ℕ, digitsVal (T : K) (as.map (fun a : ℕ => (a : K))) = ((Nat.ofDigits T as : ℕ) : K)
  | [] => by simp [digitsVal]
  | a :: as => by
    have := digitsVal_natCast (K := K) T as
    simp only [digitsVal] at this ⊢
    simp only [List.map_cons, List.foldr_cons, this, Nat.ofDigits_cons, Nat.cast_add,
      Nat.cast_mul]

/-- **The terms of a peeled sum are `−T^j · u_j`** (`chainOk` from the power `pw`): their sum is
`−pw` times the value of the `u_j` in base `T`. -/
theorem chainOk_sum {K : Type} [Field K] {p T : ℕ} [CharP K p] (dec : ℕ → K)
    (hdec : ∀ c < p, dec c = (c : K)) (x : ℕ → K) :
    ∀ (pw : ℕ) (ts : List (ℕ × ℕ)) (us : List ℕ), chainOk p T pw ts us = true →
      (ts.map fun cu => dec cu.1 * x cu.2).sum = -(pw : K) * digitsVal (T : K) (us.map x)
  | _, [], [], _ => by simp [digitsVal]
  | pw, (c, u) :: ts, u' :: us, h => by
    simp only [chainOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hu, hc⟩, hpw⟩, hrest⟩ := h
    subst hu
    have hcK : (c : K) = -(pw : K) := by
      rw [eq_neg_iff_add_eq_zero, ← Nat.cast_add, hc, CharP.cast_eq_zero]
    rw [List.map_cons, List.sum_cons, chainOk_sum dec hdec x (pw * T) ts us hrest,
      hdec c (by omega), hcK]
    simp only [List.map_cons, digitsVal, List.foldr_cons, Nat.cast_mul]
    ring
  | _, [], _ :: _, h | _, _ :: _, [], h => by simp [chainOk] at h

/-- **The terms of a peeled sum are `T^j · u_j`** (`posChainOk` from the power `pw`): their sum is
`pw` times the value of the `u_j` in base `T`. -/
theorem posChainOk_sum {K : Type} [CommSemiring K] {p T : ℕ} (dec : ℕ → K)
    (hdec : ∀ c < p, dec c = (c : K)) (x : ℕ → K) :
    ∀ (pw : ℕ) (ts : List (ℕ × ℕ)) (us : List ℕ), posChainOk p T pw ts us = true →
      (ts.map fun cu => dec cu.1 * x cu.2).sum = (pw : K) * digitsVal (T : K) (us.map x)
  | _, [], [], _ => by simp [digitsVal]
  | pw, (c, u) :: ts, u' :: us, h => by
    simp only [posChainOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hu, hc⟩, hpw⟩, hrest⟩ := h
    subst hu hc
    rw [List.map_cons, List.sum_cons, posChainOk_sum dec hdec x (c * T) ts us hrest, hdec c hpw]
    simp only [List.map_cons, digitsVal, List.foldr_cons, Nat.cast_mul]
    ring
  | _, [], _ :: _, h | _, _ :: _, [], h => by simp [posChainOk] at h

/-- **An expression that is the number of its digits** (`digitsExprOk`) has, at every coordinate,
the value of the digits in base `T`, the constants below the characteristic decoding to their
casts. -/
theorem evalE_of_digitsExprOk (rd : ir.Valuation I) {f p T : ℕ}
    (hdec : ∀ c < p, (I f).decode c = (c : (I f).K)) {x : Expr} :
    ∀ {us : List ℕ}, digitsExprOk p T x us = true → ∀ i,
      ir.evalE rd f x i = digitsVal (T : (I f).K) (us.map fun u => castElt (rd u i))
  | [], h => absurd h (by simp [digitsExprOk])
  | u :: us, h => by
    simp only [digitsExprOk] at h
    rcases hpl : peel us.length x with _ | ⟨hd, ts⟩
    · rw [hpl] at h
      cases h
    · rw [hpl] at h
      cases hd with
      | leaf w =>
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, hch⟩ := h
        obtain ⟨hev, -⟩ := peel_spec rd f _ _ hpl
        intro i
        rw [hev i, evalE_leaf, posChainOk_sum _ hdec (fun u => castElt (rd u i)) T ts us hch]
        simp [digitsVal]
      | _ => simp at h

/-- **An expression's coordinate cast between equal field identifiers** is its coordinate in the
other. -/
theorem castElt_evalE {f f' : ℕ} (h : f = f') (rd : ir.Valuation I) (e : Expr) (i : ℕ) :
    (castElt (ir.evalE rd f e i) : (I f').K) = ir.evalE rd f' e i := by
  subst h
  simp

/-- **Every value bound to its digits reads its expression** at the reader `rd`: the realized
assignment (`RealizedProgram.bindAsg`) reads a bound value through its digits. -/
def BoundReads (rd : ir.Valuation I) : Prop :=
  ∀ v < ir.values.length, ∀ x, (ir.value v).kind = .bound x →
    rd v = ir.evalE rd (ir.valueField v) x

/-! ## The honest prover -/

/-- **The digits of the two-sided and digit lookups are below their bases** at the reader `rd`:
every coordinate of every digit value `d_j`, `h_j` of a two-sided or digit `in` is the cast of a
natural below the base. A property of honest assignments (the honest prover computes the
digits). -/
def DigitsBelow (rd : ir.Valuation I) : Prop :=
  ∀ pid < ir.predicates.length, ∀ r, lookupOf? (ir.predicate pid).body = some r →
    r.kind = .twoSided ∨ r.kind = .digits → ∀ u ∈ r.digitValues ++ r.second,
      ∀ i < (ir.value u).size, IsNatBelow r.base (rd u i)

/-- **A value is a row of a range iff it lies in the table.** -/
theorem exists_tableRow_iff_isNatBelow {t : ℕ} (hr : ir.IsRange t) (rd : ir.Valuation I) (f : ℕ)
    (x : (I f).K) : (∃ j, ir.tableRow rd f t j = x) ↔ IsNatBelow (ir.tableSize t) x := by
  simp only [tableRow_of_isRange hr, isNatBelow_iff_exists_fin]

variable (ir) in
/-- **A lookup `in`'s shape without intervals** (a complement lookup at `ComplementCore`). -/
def LookupCore (pid d : ℕ) (recs : List Expr) (set : InSet) (r : LookupRealization) : Prop :=
  match r.kind with
  | .direct => ir.DirectOk pid d recs set r
  | .digits => ir.DigitsOk pid d recs set r
  | .twoSided => ir.TwoSidedOk pid d recs set r
  | .complement => ir.ComplementCore pid d recs set r
  | _ => False

/-- **The groups of a table whose `in` predicates hold have their needles among its rows**, where the digits of the two-sided and digit lookups are below their bases: a
member of a direct `in` is a coordinate of its record, of a complement `in` a coordinate of
`(N − 1) − v` for `v < N` (`needle_isNatBelow_of_complement`), of a two-sided or digit `in` a
coordinate of a digit value (`DigitsBelow`); the last three look up into ranges. -/
theorem groupNeedles_inRows_core (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) (htab : ∀ t < ir.tables.length, ir.TableOk t)
    (hlk : ∀ pid < ir.predicates.length, ∀ d recs set r,
      (ir.predicate pid).body = .mem d recs set (.lookup r) → ir.LookupCore pid d recs set r)
    {t g : ℕ}
    (htl : t < ir.tables.length) (hg : g < ir.groupCountOf t) {rd : ir.Valuation I}
    (hF : ir.LeafFacts rd)
    (hpreds : ∀ pid < ir.predicates.length, ir.HoldsWith rd (ir.predicate pid).body)
    (hdig : ir.DigitsBelow rd) : ir.NeedlesIn rd t g := by
  have ho := hwf.refsOrdered
  unfold NeedlesIn
  intro v hv'
  obtain ⟨m, hm, c, hc, rfl⟩ := exists_of_mem_groupNeedles hv'
  have hmo := ((htab t htl).groups g hg).members m hm
  have hl := hmo.looksUp
  unfold LooksUp at hl
  split at hl
  · rename_i r hr
    obtain ⟨d, recs, set, hp⟩ := lookupOf?_eq_some.1 hr
    obtain ⟨hrt, hn⟩ := hl
    subst hrt
    have hreal := hlk m.pred hmo.pred _ _ _ _ hp
    simp only [LookupCore] at hreal
    rw [needleExpr_eq hp]
    split at hreal
    · obtain ⟨_, _, _, hns, _⟩ := exists_of_singleMatch hreal.record
      have hn0 : m.needle = 0 := by rw [hns] at hn; simpa using hn
      have hb := tiles_bound (hreal.covered m.needle hn) (m.first, m.count)
        (mem_coverRuns.2 ⟨g, hg, m, hm, rfl, rfl, rfl⟩)
      have := needleRows_of_memHolds ho hreal (htab _ htl) (hp ▸ hpreds m.pred hmo.pred)
        (i := m.first + c) (by rw [← hn0]; simp only at hb; omega)
      rwa [hn0]
    all_goals try exact hreal.elim
    · rename_i hkind
      rw [exists_tableRow_iff_isNatBelow hreal.rangeTable]
      have hneed : r.needles = r.digitValues.map .leaf := Expr.eq_of_beqList hreal.needles
      have hnl : m.needle < r.digitValues.length := by
        rw [hneed] at hn
        simpa using hn
      set u := r.digitValues[m.needle]
      have hu : u ∈ r.digitValues := List.getElem_mem _
      have hgn : r.needles.getD m.needle default = .leaf u := by
        rw [hneed, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hnl]
        rfl
      have hb := tiles_bound (hreal.covered m.needle hn) (m.first, m.count)
        (mem_coverRuns.2 ⟨g, hg, m, hm, rfl, rfl, rfl⟩)
      rw [hgn] at hb ⊢
      have hdu := hdig m.pred hmo.pred r (by rw [hp]; rfl) (.inr hkind) u
        (List.mem_append_left _ hu) (m.first + c) (by simp only [exprLen, Expr.len] at hb; omega)
      have hαf : ir.chalField (ir.alphaOf r.table) = ir.valueField u := by
        rw [(htab _ htl).domain, ← hreal.domain, (hreal.sizes u hu).2]
      rw [evalE_leaf, ← hreal.base]
      obtain ⟨k, hk, hku⟩ := hdu
      exact ⟨k, hk, by rw [← hku, castElt_natCast hαf.symm]⟩
    · rename_i hkind
      rw [exists_tableRow_iff_isNatBelow hreal.rangeTable]
      have hneed : r.needles = (r.digitValues ++ r.second).map .leaf :=
        Expr.eq_of_beqList hreal.needles
      have hnl : m.needle < (r.digitValues ++ r.second).length := by
        rw [hneed] at hn
        simpa using hn
      set u := (r.digitValues ++ r.second)[m.needle]
      have hu : u ∈ r.digitValues ++ r.second := List.getElem_mem _
      have hgn : r.needles.getD m.needle default = .leaf u := by
        rw [hneed, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hnl]
        rfl
      have hb := tiles_bound (hreal.covered m.needle hn) (m.first, m.count)
        (mem_coverRuns.2 ⟨g, hg, m, hm, rfl, rfl, rfl⟩)
      rw [hgn] at hb ⊢
      have hdu := hdig m.pred hmo.pred r (by rw [hp]; rfl) (.inl hkind) u hu (m.first + c)
        (by simp only [exprLen, Expr.len] at hb; omega)
      have hαf : ir.chalField (ir.alphaOf r.table) = ir.valueField u := by
        rw [(htab _ htl).domain, ← hreal.domain, (hreal.sizes u hu).2]
      rw [evalE_leaf, ← hreal.base]
      obtain ⟨k, hk, hku⟩ := hdu
      exact ⟨k, hk, by rw [← hku, castElt_natCast hαf.symm]⟩
    · rw [exists_tableRow_iff_isNatBelow hreal.rangeTable]
      have hn0 : m.needle = 0 := by rw [hreal.needle] at hn; omega
      have hb := tiles_bound (hreal.covered m.needle hn) (m.first, m.count)
        (mem_coverRuns.2 ⟨g, hg, m, hm, rfl, rfl, rfl⟩)
      have := needle_isNatBelow_of_complement hwf hI hL hmo.pred hp hreal (htab _ htl) hF
        (hp ▸ hpreds m.pred hmo.pred) (i := m.first + c) (by rw [← hn0]; simp only at hb; omega)
      rwa [hn0]
  · exact hl.elim

end

end GordieHowe.RealizedProgram
