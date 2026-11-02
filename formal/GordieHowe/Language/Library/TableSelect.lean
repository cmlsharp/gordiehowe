-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Library.Table

@[expose] public section

/-!
# GordieHowe frontend: the selection of a public table's row

The theorem of `lib/gordiehowe/lib/table.h`'s `select_row` at the realized program, generic in the
program at the program facts `TableSelect` (a `TableShape` and its checks, decided per program by
the matchers of `GordieHowe/Language/Library/Table.lean`):

* **The matchers are sound** (`gatherL_spec`, `powSym_sound`, `sliceOf_sound`, `sumTerm_sound`,
  `recTermsOk_sound`, `gatherIdx_sound`, `foldOf_sound`, `gMatch_sound`, `digestsOk_sound`): each
  reads the expression it matched.
* **Row maps** (`RowLeaf.apply`, `rowApply`, `cellExp`, `gVal`, `sum_gVal`): the power indices
  `e(c)` are distinct and below the width `W` (`cellExp_inj`, `cellExp_lt`, from the bit reversal's
  injectivity); the transposition `Σ_c row_c (Mᵀ g)_c = Σ_c M(row)_c γ^(e(c))`, a scheme-order
  leaf reindexed by the bit reversal.
* **The selection** (`TableSelect.evalE_lhs`, `TableSelect.select_eq`): where the selection's
  predicate and the index bits' check hold, the record's fingerprint `Σ_c rec_c γ^(e(c))` is the
  selected row's `Σ_c M(row_i)_c γ^(e(c))`, `i` the index the bits name (`TableSelect.idxOf`, a
  padding row read as its original, `TableSelect.rowIdx`).
* **The event** (`TableSelect.selEvent`, `TableSelect.SelBad`, `TableSelect.selBad_use`,
  `TableSelect.selBad_bound`, `TableSelect.record_eq_of_not_bad`): unless `γ` is a root of the
  nonzero polynomial `Σ_c (rec_c − M(row_i)_c) X^(e(c))` (degree at most `W − 1`, probability at
  most `(W − 1)/|F|` at the table's challenge, Schwartz–Zippel), the record is `M(row_i)`
  coordinatewise. The event is a `GordieHowe.ChallengeEvent` read by the challenge-use rule
  `GordieHowe.RealizedProgram.ChallengeUseAt`, for `GordieHowe.RealizedProgram.rbr_of_events`.
-/

namespace GordieHowe.RealizedProgram

open Export IOP
open scoped NNReal ENNReal

/-! ## Gathers -/

/-- **A run has its count of entries.** -/
theorem idxRunList_length (r : ℕ × ℤ × ℕ) : (idxRunList r).length = r.2.2 := by simp [idxRunList]

/-- **Entry `i` of a run** is `start + step · i`. -/
theorem idxRunList_getD (r : ℕ × ℤ × ℕ) {i : ℕ} (hi : i < r.2.2) :
    (idxRunList r).getD i 0 = ((r.1 : ℤ) + r.2.1 * i).toNat := by
  simp [idxRunList, List.getD_eq_getElem?_getD, hi]

/-- **`y` is what the index map `m` reads of `x`**: `y[i] = x[m[i]]`, every entry inside `x`. -/
def GatherSpec (x : List ℕ) (m : IndexMap) (y : List ℕ) : Prop :=
  y.length = m.size ∧ ∀ i < y.length, m.entry i < x.length ∧ y.getD i 0 = x.getD (m.entry i) 0

/-- **One run's gather reads what the run indexes.** -/
theorem gatherRunL_spec {x : List ℕ} {r : ℕ × ℤ × ℕ} {y : List ℕ} (h : gatherRunL x r = some y) :
    GatherSpec x [r] y := by
  obtain ⟨s, d, c⟩ := r
  simp only [gatherRunL] at h
  by_cases h1 : d = 1
  · subst h1
    rw [if_pos rfl] at h
    split_ifs at h with h2
    cases h
    refine ⟨by simp; omega, fun i hi => ?_⟩
    have hi' : i < c := by simp at hi; omega
    rw [IndexMap.entry_step_one hi']
    refine ⟨by omega, ?_⟩
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi', List.getElem?_drop]
  rw [if_neg h1] at h
  by_cases h3 : d = 0
  · subst h3
    rw [if_pos rfl] at h
    by_cases hc : c = 0
    · rw [if_pos hc] at h
      cases h
      exact ⟨by simp [hc], fun i hi => by simp at hi⟩
    rw [if_neg hc] at h
    split_ifs at h with h4
    cases h
    refine ⟨by simp, fun i hi => ?_⟩
    have hi' : i < c := by simpa using hi
    rw [IndexMap.entry_step_zero hi']
    exact ⟨h4, by simp [List.getD_eq_getElem?_getD, hi']⟩
  rw [if_neg h3] at h
  split_ifs at h with h5
  cases h
  refine ⟨by simp [idxRunList_length], fun i hi => ?_⟩
  have hi' : i < c := by simpa [idxRunList_length] using hi
  rw [IndexMap.entry_single hi']
  have hr := idxRunList_getD (s, d, c) hi'
  simp only at hr
  have hmem := List.all_eq_true.1 h5 ((idxRunList (s, d, c)).getD i 0)
    (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [idxRunList_length]; exact hi')]
        exact List.getElem_mem _)
  rw [hr] at hmem
  refine ⟨by simpa using hmem, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem
    (by rw [idxRunList_length]; exact hi'), Option.map_some, Option.getD_some]
  have hl : i < (idxRunList (s, d, c)).length := by rw [idxRunList_length]; exact hi'
  rw [← hr, List.getD_eq_getElem _ _ hl]

/-- **An index map's gather reads what the map indexes**, run by run. -/
theorem gatherL_spec {x : List ℕ} : ∀ {m : IndexMap} {y : List ℕ}, gatherL x m = some y →
    GatherSpec x m y
  | [], y, h => by
    simp only [gatherL, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun i hi => by simp at hi⟩
  | r :: m, y, h => by
    simp only [gatherL] at h
    split at h
    · rename_i a b ha hb
      cases h
      obtain ⟨la, hra⟩ := gatherRunL_spec ha
      obtain ⟨lb, hrb⟩ := gatherL_spec hb
      have hsz : IndexMap.size [r] = r.2.2 := by simp [IndexMap.size]
      refine ⟨by rw [List.length_append, la, lb]; simp [IndexMap.size], fun i hi => ?_⟩
      obtain ⟨s, d, c⟩ := r
      simp only at hsz
      by_cases hic : i < c
      · have hia : i < a.length := by rw [la, hsz]; exact hic
        obtain ⟨h1, h2⟩ := hra i hia
        have he : IndexMap.entry ((s, d, c) :: m) i = IndexMap.entry [(s, d, c)] i := by
          simp [IndexMap.entry, hic]
        rw [he, List.getD_append _ _ _ _ hia]
        exact ⟨h1, h2⟩
      · have hia : a.length ≤ i := by rw [la, hsz]; omega
        have hib : i - a.length < b.length := by rw [List.length_append] at hi; omega
        obtain ⟨h1, h2⟩ := hrb _ hib
        have he : IndexMap.entry ((s, d, c) :: m) i = IndexMap.entry m (i - a.length) := by
          simp only [IndexMap.entry, if_neg hic]
          rw [la, hsz]
        rw [he, List.getD_append_right _ _ _ _ hia]
        exact ⟨h1, h2⟩
    · cases h

/-! ## Shared expressions past the table -/

section Refs

variable {ir : RealizedProgram} {I : Interp}

/-- **A reference reads its shared expression**, also past the table (both read the default
expression, a leaf). -/
theorem evalE_ref_of (ho : ir.RefsOrdered) (hne : 0 < ir.exprs.length) (rd : ir.Valuation I)
    (f k : ℕ) : ir.evalE rd f (.ref k) = ir.evalE rd f (ir.expr k) := by
  by_cases hk : k < ir.exprs.length
  · exact evalE_ref ho rd f hk
  · have hd : ir.expr k = default := by
      simp only [expr_eq_getD]
      exact List.getD_eq_default _ _ (by omega)
    obtain ⟨L, hL⟩ : ∃ L, ir.exprs.length = L + 1 := ⟨ir.exprs.length - 1, by omega⟩
    funext i
    simp only [evalE, Expr.eval, hL, refVal]
    rw [hd]
    rfl

/-- **A reference has its shared expression's length**, also past the table. -/
theorem exprLen_ref_of (ho : ir.RefsOrdered) (hne : 0 < ir.exprs.length) (k : ℕ) :
    ir.exprLen (.ref k) = ir.exprLen (ir.expr k) := by
  by_cases hk : k < ir.exprs.length
  · exact exprLen_ref ho hk
  · have hd : ir.expr k = default := by
      simp only [expr_eq_getD]
      exact List.getD_eq_default _ _ (by omega)
    obtain ⟨L, hL⟩ : ∃ L, ir.exprs.length = L + 1 := ⟨ir.exprs.length - 1, by omega⟩
    simp only [exprLen, Expr.len, hL, refLen]
    rw [hd]
    rfl

end Refs

/-! ## The symbolic powers are sound -/

section Pow

variable {ir : RealizedProgram} {I : Interp} (rd : ir.Valuation I) (f : ℕ) (γ : (I f).K)

/-- **Coordinate `i` of `E` is `γ^(l[i])`**, `E` of `l`'s length. -/
def PowsAt (E : Expr) (l : List ℕ) : Prop :=
  ir.exprLen E = l.length ∧ ∀ i < l.length, ir.evalE rd f E i = γ ^ l.getD i 0

/-- **A context whose values and known expression are the powers it names.** -/
structure PowCtx.Sound (c : PowCtx) : Prop where
  /-- The values. -/
  pub : ∀ v l, c.pub v = some l → PowsAt rd f γ (.leaf v) l
  /-- The known expression. -/
  known : ∀ K ks, c.known = some (K, ks) → PowsAt rd f γ K ks

variable {rd f γ}

/-- **The symbolic powers are the expression's coordinates.** -/
theorem powSym_sound (ho : ir.RefsOrdered) (hne : 0 < ir.exprs.length) {c : PowCtx}
    (hc : c.Sound rd f γ) : ∀ n E l, ir.powSym c n E = some l → PowsAt rd f γ E l
  | 0, _, _, h => by simp [powSym] at h
  | n + 1, E, l, h => by
    simp only [powSym] at h
    split at h
    · rename_i ks hk
      cases h
      unfold PowCtx.knownOf? at hk
      split at hk
      · rename_i K ks' hK
        split_ifs at hk with hb
        cases hk
        rw [Expr.eq_of_beq hb]
        exact hc.known _ _ hK
      · cases hk
    · split at h
      · exact hc.pub _ _ h
      · rename_i a b _
        split at h
        · rename_i x y hx hy
          split_ifs at h with hl
          cases h
          obtain ⟨lx, vx⟩ := powSym_sound ho hne hc n a x hx
          obtain ⟨-, vy⟩ := powSym_sound ho hne hc n b y hy
          refine ⟨by rw [exprLen_mul, lx, List.length_zipWith, hl, Nat.min_self], fun i hi => ?_⟩
          rw [List.length_zipWith, hl, Nat.min_self] at hi
          rw [evalE_mul, vx i (by omega), vy i hi, ← pow_add]
          congr 1
          simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith, List.getElem?_eq_getElem hi,
            List.getElem?_eq_getElem (show i < x.length by omega)]
        · cases h
      · rename_i a b _
        split at h
        · rename_i x y hx hy
          cases h
          obtain ⟨lx, vx⟩ := powSym_sound ho hne hc n a x hx
          obtain ⟨ly, vy⟩ := powSym_sound ho hne hc n b y hy
          refine ⟨by rw [exprLen_concat, lx, ly, List.length_append], fun i hi => ?_⟩
          rw [evalE_concat, lx]
          split_ifs with hix
          · rw [vx i hix, List.getD_append _ _ _ _ hix]
          · rw [List.length_append] at hi
            rw [vy _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
        · cases h
      · rename_i m a _
        split at h
        · rename_i x hx
          obtain ⟨lx, vx⟩ := powSym_sound ho hne hc n a x hx
          obtain ⟨hl, hy⟩ := gatherL_spec h
          refine ⟨by rw [exprLen_reindex, hl], fun i hi => ?_⟩
          obtain ⟨h1, h2⟩ := hy i hi
          rw [evalE_reindex, vx _ h1, h2]
        · cases h
      · rename_i k _
        obtain ⟨hl, hv⟩ := powSym_sound ho hne hc n _ l h
        exact ⟨by rw [exprLen_ref_of ho hne, hl], fun i hi => by rw [evalE_ref_of ho hne, hv i hi]⟩
      · cases h

end Pow

/-! ## Row maps -/

section RowMaps

variable {K : Type*} [Field K]

namespace RowLeaf

/-- **The leaf applied to a row's block** (`RowMap::apply`): the identity, or the transform at
`ψ` in its order. -/
def apply (dec : ℕ → K) (l : RowLeaf) (row : ℕ → K) (k : ℕ) : K :=
  if l.ntt then
    if l.natural then Ops.nttNatural l.n (dec l.psi) row k else Ops.nttScheme l.n (dec l.psi) row k
  else row k

/-- **The leaf's block of `Mᵀ g`** before its multiplier (`RowMap::transposed`): `γ^k`, or the
transposed transform of `γ^0, …, γ^(n−1)`. -/
def tcol (dec : ℕ → K) (γ : K) (l : RowLeaf) (k : ℕ) : K :=
  if l.ntt then Ops.nttTranspose l.n (dec l.psi) (fun m => γ ^ m) k else γ ^ k

/-- **A well-formed scheme-order leaf has `2^lg` cells.** -/
theorem lg_spec {l : RowLeaf} (hw : l.wf = true) (hs : l.scheme = true) : l.n = 2 ^ l.lg := by
  simp only [wf, hs, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hw
  exact hw.2

/-- **A leaf's power indices are below its width.** -/
theorem perm_lt {l : RowLeaf} (hw : l.wf = true) {k : ℕ} (hk : k < l.n) : l.perm k < l.n := by
  unfold perm
  split_ifs with hs
  · rw [lg_spec hw hs]
    exact bitRevNat_lt _ _
  · exact hk

/-- **Distinct cells of a leaf have distinct power indices.** -/
theorem perm_inj {l : RowLeaf} (hw : l.wf = true) {k k' : ℕ} (hk : k < l.n) (hk' : k' < l.n)
    (h : l.perm k = l.perm k') : k = k' := by
  unfold perm at h
  split_ifs at h with hs
  · rw [lg_spec hw hs] at hk hk'
    exact bitRevNat_injOn hk hk' h
  · exact h

/-- **A well-formed leaf has a cell.** -/
theorem n_pos {l : RowLeaf} (hw : l.wf = true) : 0 < l.n := by
  simp only [wf, Bool.and_eq_true, decide_eq_true_eq] at hw
  exact hw.1

/-- **A sum over the scheme's order is a sum over the natural order.** -/
theorem sum_bitRev (L : ℕ) (g : ℕ → K) :
    ∑ k ∈ Finset.range (2 ^ L), g (bitRevNat L k) = ∑ k ∈ Finset.range (2 ^ L), g k := by
  rw [Finset.sum_range (fun k => g (bitRevNat L k)), Finset.sum_range g]
  exact Equiv.sum_comp (bitRev L) (fun k : Fin (2 ^ L) => g k)

/-- **The transposed transform** reads the natural-order transform's fingerprint. -/
theorem sum_tcol_ntt (dec : ℕ → K) (γ : K) {l : RowLeaf} (hn : l.ntt = true) (row : ℕ → K) :
    ∑ k ∈ Finset.range l.n, row k * l.tcol dec γ k =
      ∑ m ∈ Finset.range l.n, Ops.nttNatural l.n (dec l.psi) row m * γ ^ m := by
  have ht : ∀ k ∈ Finset.range l.n, row k * l.tcol dec γ k =
      ∑ m ∈ Finset.range l.n, row k * dec l.psi ^ ((2 * m + 1) * k) * γ ^ m := fun k hk => by
    rw [Finset.mem_range] at hk
    simp only [tcol, hn, if_true, Ops.nttTranspose, if_pos hk, Finset.mul_sum]
    rw [← Finset.sum_range (fun m => row k * (dec l.psi ^ ((2 * m + 1) * k) * γ ^ m))]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [Finset.sum_congr rfl ht, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  rw [Ops.nttNatural_apply _ _ _ hm, Finset.sum_mul, ← Finset.sum_range
    (fun i => row i * dec l.psi ^ ((2 * m + 1) * i) * γ ^ m)]

/-- **A leaf's transposition**: `Σ_k row_k (Mᵀ g)_k = Σ_k M(row)_k γ^(perm k)`. -/
theorem sum_tcol (dec : ℕ → K) (γ : K) {l : RowLeaf} (hw : l.wf = true) (row : ℕ → K) :
    ∑ k ∈ Finset.range l.n, row k * l.tcol dec γ k =
      ∑ k ∈ Finset.range l.n, l.apply dec row k * γ ^ l.perm k := by
  by_cases hn : l.ntt = true
  · rw [sum_tcol_ntt dec γ hn]
    by_cases hnat : l.natural = true
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp [apply, perm, scheme, hn, hnat]
    · have hs : l.scheme = true := by simp [scheme, hn, hnat]
      have hL := lg_spec hw hs
      have hlog : Nat.log2 l.n = l.lg := by rw [hL, Nat.log2_two_pow]
      have : ∀ k ∈ Finset.range l.n, l.apply dec row k * γ ^ l.perm k =
          (fun m => Ops.nttNatural l.n (dec l.psi) row m * γ ^ m) (bitRevNat l.lg k) :=
        fun k hk => by
          rw [Finset.mem_range] at hk
          simp only [apply, hn, hnat, if_true, Bool.false_eq_true, if_false, Ops.nttScheme,
            if_pos hk, perm, hs, hlog]
      rw [Finset.sum_congr rfl this, hL]
      exact (sum_bitRev l.lg (fun m => Ops.nttNatural (2 ^ l.lg) (dec l.psi) row m * γ ^ m)).symm
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [apply, tcol, perm, scheme, hn]

end RowLeaf

/-- **The power index of cell `c`** of a row map, from its first cell (`RowMap::perm` at each
leaf's offset). -/
def cellExp : List RowLeaf → ℕ → ℕ
  | [], c => c
  | l :: ls, c => if c < l.n then l.perm c else l.n + cellExp ls (c - l.n)

/-- **A row map applied to a row** (`RowMap::apply`). -/
def rowApply (dec : ℕ → K) : List RowLeaf → (ℕ → K) → ℕ → K
  | [], _, _ => 0
  | l :: ls, row, c =>
    if c < l.n then l.apply dec row c else rowApply dec ls (fun i => row (l.n + i)) (c - l.n)

/-- **`Mᵀ g`** (`RowMap::transposed`): each leaf's block times `γ^off`. -/
def gVal (dec : ℕ → K) (γ : K) : List RowLeaf → ℕ → K
  | [], _ => 0
  | l :: ls, c => if c < l.n then γ ^ l.off * l.tcol dec γ c else gVal dec γ ls (c - l.n)

/-- **The width of a row map** is its first leaf's plus the rest's. -/
theorem mapWidth_cons (l : RowLeaf) (ls : List RowLeaf) :
    mapWidth (l :: ls) = l.n + mapWidth ls := by
  simp [mapWidth]

/-- **A row map is well formed from `o`** when its first leaf sits at `o`, is well formed, and
the rest is well formed after it. -/
theorem mapWfFrom_cons {o : ℕ} {l : RowLeaf} {ls : List RowLeaf} :
    mapWfFrom o (l :: ls) = true ↔ l.off = o ∧ l.wf = true ∧ mapWfFrom (o + l.n) ls = true := by
  simp [mapWfFrom, Bool.and_eq_true, beq_iff_eq, and_assoc]

/-- **The leaves of a well-formed row map are well formed.** -/
theorem mapWfFrom_wf : ∀ {o : ℕ} {m : List RowLeaf}, mapWfFrom o m = true → ∀ l ∈ m, l.wf = true
  | _, [], _, _, h => by simp at h
  | _, l :: ls, hw, l', h => by
    rw [mapWfFrom_cons] at hw
    rcases List.mem_cons.1 h with rfl | h
    · exact hw.2.1
    · exact mapWfFrom_wf hw.2.2 l' h

/-- **The power indices are below the width.** -/
theorem cellExp_lt : ∀ {o : ℕ} {m : List RowLeaf}, mapWfFrom o m = true → ∀ {c : ℕ},
    c < mapWidth m → cellExp m c < mapWidth m
  | _, [], _, c, hc => by simp [mapWidth] at hc
  | _, l :: ls, hw, c, hc => by
    rw [mapWfFrom_cons] at hw
    rw [mapWidth_cons] at hc ⊢
    unfold cellExp
    split_ifs with h
    · have := RowLeaf.perm_lt hw.2.1 h
      omega
    · have := cellExp_lt hw.2.2 (c := c - l.n) (by omega)
      omega

/-- **Distinct cells have distinct power indices.** -/
theorem cellExp_inj : ∀ {o : ℕ} {m : List RowLeaf}, mapWfFrom o m = true → ∀ {c c' : ℕ},
    c < mapWidth m → c' < mapWidth m → cellExp m c = cellExp m c' → c = c'
  | _, [], _, c, _, hc, _, _ => by simp [mapWidth] at hc
  | _, l :: ls, hw, c, c', hc, hc', h => by
    rw [mapWfFrom_cons] at hw
    rw [mapWidth_cons] at hc hc'
    unfold cellExp at h
    split_ifs at h with h1 h2 h2
    · exact RowLeaf.perm_inj hw.2.1 h1 h2 h
    · have := RowLeaf.perm_lt hw.2.1 h1
      omega
    · have := RowLeaf.perm_lt hw.2.1 h2
      omega
    · have := cellExp_inj hw.2.2 (c := c - l.n) (c' := c' - l.n) (by omega) (by omega) (by omega)
      omega

/-- **The transposition of a row map**: `Σ_c row_c (Mᵀ g)_c = Σ_c M(row)_c γ^(o + e(c))`, `e` the
power indices, for leaves from offset `o`. -/
theorem sum_gVal (dec : ℕ → K) (γ : K) : ∀ {o : ℕ} {m : List RowLeaf}, mapWfFrom o m = true →
    ∀ row : ℕ → K, ∑ c ∈ Finset.range (mapWidth m), row c * gVal dec γ m c =
      ∑ c ∈ Finset.range (mapWidth m), rowApply dec m row c * γ ^ (o + cellExp m c)
  | _, [], _, _ => by simp [mapWidth]
  | o, l :: ls, hw, row => by
    rw [mapWfFrom_cons] at hw
    obtain ⟨hoff, hl, hls⟩ := hw
    rw [mapWidth_cons, Finset.sum_range_add, Finset.sum_range_add]
    congr 1
    · have h1 : ∀ k ∈ Finset.range l.n, row k * gVal dec γ (l :: ls) k =
          γ ^ o * (row k * l.tcol dec γ k) := fun k hk => by
        rw [Finset.mem_range] at hk
        simp only [gVal, if_pos hk, hoff]
        ring
      have h2 : ∀ k ∈ Finset.range l.n,
          rowApply dec (l :: ls) row k * γ ^ (o + cellExp (l :: ls) k) =
            γ ^ o * (l.apply dec row k * γ ^ l.perm k) := fun k hk => by
        rw [Finset.mem_range] at hk
        simp only [rowApply, cellExp, if_pos hk, pow_add]
        ring
      rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, ← Finset.mul_sum, ← Finset.mul_sum,
        RowLeaf.sum_tcol dec γ hl]
    · have h1 : ∀ c ∈ Finset.range (mapWidth ls),
          row (l.n + c) * gVal dec γ (l :: ls) (l.n + c) = row (l.n + c) * gVal dec γ ls c :=
        fun c _ => by
          simp only [gVal, if_neg (Nat.not_lt.2 (Nat.le_add_right _ _)), Nat.add_sub_cancel_left]
      have h2 : ∀ c ∈ Finset.range (mapWidth ls), rowApply dec (l :: ls) row (l.n + c) *
          γ ^ (o + cellExp (l :: ls) (l.n + c)) =
          rowApply dec ls (fun i => row (l.n + i)) c * γ ^ (o + l.n + cellExp ls c) :=
        fun c _ => by
          simp only [rowApply, cellExp, if_neg (Nat.not_lt.2 (Nat.le_add_right _ _)),
            Nat.add_sub_cancel_left, Nat.add_assoc]
      rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
      exact sum_gVal dec γ hls (fun i => row (l.n + i))

/-- **A sum over a row map's leaves is a sum over its cells**: leaf `l`'s cell `k` is cell
`l.off + k`, of power index `l.off + perm k`. -/
theorem sum_leaves (F : ℕ → ℕ → K) : ∀ {o : ℕ} {m : List RowLeaf}, mapWfFrom o m = true →
    (m.map fun l => ∑ k ∈ Finset.range l.n, F (l.off + k) (l.off + l.perm k)).sum =
      ∑ c ∈ Finset.range (mapWidth m), F (o + c) (o + cellExp m c)
  | _, [], _ => by simp [mapWidth]
  | o, l :: ls, hw => by
    rw [mapWfFrom_cons] at hw
    obtain ⟨hoff, _, hls⟩ := hw
    rw [List.map_cons, List.sum_cons, mapWidth_cons, Finset.sum_range_add, sum_leaves F hls]
    congr 1
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      simp only [cellExp, if_pos hk, hoff]
    · refine Finset.sum_congr rfl fun c _ => ?_
      simp only [cellExp, if_neg (Nat.not_lt.2 (Nat.le_add_right _ _)), Nat.add_sub_cancel_left]
      congr 1 <;> ring

end RowMaps

/-! ## The matchers are sound -/

/-- **An index map has as many entries as its list.** -/
theorem IndexMap.size_eq_length_toList (m : IndexMap) : m.size = m.toList.length := by
  simp [IndexMap.size, IndexMap.toList, List.length_flatMap]

/-- **The number of the bits `b_0, …, b_(t−1)`**: `Σ_{i<t} b_i 2^i`. -/
def idxVal (b : ℕ → ℕ) (t : ℕ) : ℕ := ∑ i ∈ Finset.range t, b i * 2 ^ i

/-- **One more bit** adds `b_t 2^t`. -/
theorem idxVal_succ (b : ℕ → ℕ) (t : ℕ) : idxVal b (t + 1) = idxVal b t + b t * 2 ^ t := by
  simp [idxVal, Finset.sum_range_succ]

/-- **`t` bits name a number below `2^t`.** -/
theorem idxVal_lt {b : ℕ → ℕ} (hb : ∀ i, b i ≤ 1) : ∀ t, idxVal b t < 2 ^ t
  | 0 => by simp [idxVal]
  | t + 1 => by
    rw [idxVal_succ, pow_succ]
    have := idxVal_lt hb t
    have := hb t
    nlinarith

/-- **A multiplexer on a bit** selects its first operand at `1`, its second at `0`. -/
theorem mux_bit {K : Type*} [Field K] {b : ℕ} (hb : b ≤ 1) (x y : K) :
    (b : K) * x + (1 - (b : K)) * y = if b = 1 then x else y := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with rfl | rfl <;> simp

section Matchers

variable {ir : RealizedProgram} {I : Interp} (rd : ir.Valuation I) (f : ℕ)

/-- **A slice of the record reads the record.** -/
theorem sliceOf_sound {rec : Expr} : ∀ {R : Expr} {s w : ℕ}, sliceOf? rec R = some (s, w) →
    ir.exprLen R = w ∧ ∀ k < w, ir.evalE rd f R k = ir.evalE rd f rec (s + k)
  | .reindex m e, s, w, h => by
    unfold sliceOf? at h
    split at h
    · rename_i s0 d c e' heq
      obtain ⟨rfl, rfl⟩ := Expr.reindex.inj heq
      split_ifs at h with hd hb
      · cases h
        subst hd
        refine ⟨by simp [exprLen_reindex], fun k hk => ?_⟩
        rw [evalE_reindex, IndexMap.entry_step_one hk, Expr.eq_of_beq hb]
      · split at h
        · rename_i s' c' he
          split_ifs at h with hle
          cases h
          obtain ⟨hl, hv⟩ := sliceOf_sound he
          subst hd
          refine ⟨by simp [exprLen_reindex], fun k hk => ?_⟩
          rw [evalE_reindex, IndexMap.entry_step_one hk, hv _ (by omega), Nat.add_assoc]
        · cases h
    · cases h
  | .leaf _, _, _, h | .add _ _, _, _, h | .sub _ _, _, _, h | .scale _ _, _, _, h
  | .mul _ _, _, _, h | .concat _ _, _, _, h | .linear _ _, _, _, h | .prod _ _, _, _, h
  | .mux _ _ _, _, _, h | .apply _ _, _, _, h | .ref _, _, _, h | .logic _ _ _, _, _, h => by
    simp [sliceOf?] at h

variable {γ : (I f).K}

/-- **A sum term of the record's digest**: `Σ_k rec[s + k] γ^(p_k)`. -/
theorem sumTerm_sound (ho : ir.RefsOrdered) (hne : 0 < ir.exprs.length) {c : PowCtx}
    (hc : c.Sound rd f γ) {rec S : Expr} {s n : ℕ} {ps : List ℕ}
    (h : ir.sumTerm? rec c S = some (s, n, ps)) :
    ps.length = n ∧ (0 < n → ir.exprLen S = 1) ∧
      ir.evalE rd f S 0 = ∑ k ∈ Finset.range n, ir.evalE rd f rec (s + k) * γ ^ ps.getD k 0 := by
  unfold sumTerm? at h
  split at h
  · rename_i n0 R P
    split at h
    · rename_i s0 w ps0 hR hP
      split_ifs at h with hw
      cases h
      obtain ⟨hlR, hvR⟩ := sliceOf_sound rd f hR
      obtain ⟨hlP, hvP⟩ := powSym_sound ho hne hc _ _ _ hP
      refine ⟨hw.2, fun hn => ?_, ?_⟩
      · rw [exprLen_apply, exprLen_mul, hlR, hw.1]
        simp [NamedOp.rows, NamedOp.cols, Nat.div_self hn]
      · rw [evalE_apply_sum, ← Finset.sum_range (fun t => ir.evalE rd f (.mul R P) (0 * n + t))]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.mem_range] at hk
        rw [Nat.zero_mul, Nat.zero_add, evalE_mul, hvR k (by omega), hvP k (by omega)]
    · cases h
  · cases h

/-- **Leaf `l`'s term of the record's digest** is `Σ_k rec[off + k] γ^(off + perm k)`. -/
theorem recTermOk_sound (ho : ir.RefsOrdered) (hne : 0 < ir.exprs.length) {c : PowCtx}
    (hc : c.Sound rd f γ) {rec : Expr} {l : RowLeaf} (hw : l.wf = true) {t : Expr}
    (h : ir.recTermOk rec c l t = true) :
    ir.exprLen t = 1 ∧ ir.evalE rd f t 0 =
      ∑ k ∈ Finset.range l.n, ir.evalE rd f rec (l.off + k) * γ ^ (l.off + l.perm k) := by
  have hperm : ∀ k ∈ Finset.range l.n, l.permList.getD k 0 = l.perm k := fun k hk => by
    rw [Finset.mem_range] at hk
    simp [RowLeaf.permList, List.getD_eq_getElem?_getD, hk]
  have hn := RowLeaf.n_pos hw
  unfold recTermOk at h
  split at h
  · rename_i M S
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
    obtain ⟨⟨-, hM⟩, hS⟩ := h
    obtain ⟨lM, vM⟩ := powSym_sound ho hne hc _ _ _ hM
    obtain ⟨-, hlS, vS⟩ := sumTerm_sound rd f ho hne hc hS
    refine ⟨by rw [exprLen_mul, lM]; rfl, ?_⟩
    rw [evalE_mul, vM 0 (by simp), vS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hperm k hk, pow_add]
    simp only [List.getD_cons_zero]
    ring
  · rename_i S _
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨hoff, hS⟩ := h
    obtain ⟨-, hlS, vS⟩ := sumTerm_sound rd f ho hne hc hS
    refine ⟨hlS hn, ?_⟩
    rw [vS]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hperm k hk, hoff, Nat.zero_add, Nat.zero_add]

/-- **A left-nested sum is the sum of its terms**, of its first term's length. -/
theorem evalE_addSpine : ∀ T : Expr, (∀ i, ir.evalE rd f T i =
    ((addSpine T).map fun t => ir.evalE rd f t i).sum) ∧
      ∃ t0 rest, addSpine T = t0 :: rest ∧ ir.exprLen T = ir.exprLen t0
  | .add a b => by
    obtain ⟨ha, t0, rest, hs, hl⟩ := evalE_addSpine a
    refine ⟨fun i => ?_, t0, rest ++ [b], ?_, ?_⟩
    · rw [evalE_add, ha i]
      simp [addSpine]
    · simp [addSpine, hs]
    · rw [exprLen_add, hl]
  | .leaf _ | .sub _ _ | .scale _ _ | .mul _ _ | .reindex _ _ | .concat _ _ | .linear _ _
  | .prod _ _ | .mux _ _ _ | .apply _ _ | .ref _ | .logic _ _ _ =>
    ⟨fun i => by simp [addSpine], _, [], rfl, rfl⟩

/-- **The record's digest terms** sum to the leaves' sums. -/
theorem recTermsOk_sound (ho : ir.RefsOrdered) (hne : 0 < ir.exprs.length) {c : PowCtx}
    (hc : c.Sound rd f γ) {rec : Expr} : ∀ {o : ℕ} {m : List RowLeaf} {ts : List Expr},
    mapWfFrom o m = true → ir.recTermsOk rec c m ts = true →
      (ts.map fun t => ir.evalE rd f t 0).sum = (m.map fun l =>
        ∑ k ∈ Finset.range l.n, ir.evalE rd f rec (l.off + k) * γ ^ (l.off + l.perm k)).sum ∧
      ∀ t0 rest, ts = t0 :: rest → ir.exprLen t0 = 1
  | _, [], [], _, _ => ⟨by simp, fun _ _ h => by cases h⟩
  | _, l :: ls, t :: ts, hw, h => by
    rw [mapWfFrom_cons] at hw
    simp only [recTermsOk, Bool.and_eq_true] at h
    obtain ⟨hl, hv⟩ := recTermOk_sound rd f ho hne hc hw.2.1 h.1
    obtain ⟨hs, -⟩ := recTermsOk_sound ho hne hc hw.2.2 h.2
    refine ⟨by rw [List.map_cons, List.sum_cons, hv, hs, List.map_cons, List.sum_cons],
      fun t0 rest he => ?_⟩
    cases he
    exact hl
  | _, [], _ :: _, _, h | _, _ :: _, [], _, h => by simp [recTermsOk] at h

/-- **A gather of `base` reads `base`.** -/
theorem gatherIdx_sound {base : Expr} : ∀ {E : Expr} {l : List ℕ}, gatherIdx? base E = some l →
    ir.exprLen E = l.length ∧ ∀ i < l.length, ir.evalE rd f E i = ir.evalE rd f base (l.getD i 0)
  | .reindex m e, l, h => by
    simp only [gatherIdx?] at h
    split_ifs at h with hb
    · cases h
      refine ⟨by rw [exprLen_reindex, IndexMap.size_eq_length_toList], fun i _ => ?_⟩
      rw [evalE_reindex, Expr.eq_of_beq hb, IndexMap.entry_eq_getD_toList]
    · split at h
      · rename_i l0 he
        obtain ⟨hl0, hv0⟩ := gatherIdx_sound he
        obtain ⟨hlen, hg⟩ := gatherL_spec h
        refine ⟨by rw [exprLen_reindex, hlen], fun i hi => ?_⟩
        obtain ⟨h1, h2⟩ := hg i hi
        rw [evalE_reindex, hv0 _ h1, h2]
      · cases h
  | .leaf _, _, h | .add _ _, _, h | .sub _ _, _, h | .scale _ _, _, h
  | .mul _ _, _, h | .concat _ _, _, h | .linear _ _, _, h | .prod _ _, _, h
  | .mux _ _ _, _, h | .apply _ _, _, h | .ref _, _, h | .logic _ _ _, _, h => by
    simp [gatherIdx?] at h

/-- **The fold's levels**: after `t` levels, entry `j` is digest `2^t j + Σ_{i<t} b_i 2^i`, at
bits `b` of the index. -/
theorem foldOf_sound (ho : ir.RefsOrdered) (hne : 0 < ir.exprs.length) {idx dig nd kb : ℕ}
    (hnd : (ir.value dig).size = nd) {b : ℕ → ℕ} (hb : ∀ i, b i ≤ 1)
    (hbit : ∀ i < kb, ir.evalE rd f (.leaf idx) i = (b i : (I f).K)) :
    ∀ n E t w, ir.foldOf? idx dig nd kb n E = some (t, w) → ir.exprLen E = w ∧
      ∀ j < w, ir.evalE rd f E j = ir.evalE rd f (.leaf dig) (2 ^ t * j + idxVal b t)
  | 0, _, _, _, h => by simp [foldOf?] at h
  | n + 1, E, t, w, h => by
    simp only [foldOf?] at h
    split at h
    · rename_i v
      split_ifs at h with hv
      cases h
      subst hv
      exact ⟨by rw [exprLen_leaf, hnd], fun j _ => by simp [idxVal]⟩
    · rename_i k
      obtain ⟨hl, hv⟩ := foldOf_sound ho hne hnd hb hbit n _ t w h
      exact ⟨by rw [exprLen_ref_of ho hne, hl], fun j hj => by rw [evalE_ref_of ho hne, hv j hj]⟩
    · rename_i B mh Xe ml Xe'
      split_ifs at h with hX
      split at h
      · rename_i t0 c2 hf
        split_ifs at h with hc
        cases h
        obtain ⟨ht, hc2, hmh, hml, hB⟩ := hc
        obtain ⟨hlX, hvX⟩ := foldOf_sound ho hne hnd hb hbit n Xe t0 c2 hf
        obtain ⟨hlB, hvB⟩ := gatherIdx_sound rd f hB
        refine ⟨by rw [exprLen_mux, exprLen_reindex, IndexMap.size_eq_length_toList], fun j hj => ?_⟩
        have hBj : ir.evalE rd f B j = (b t0 : (I f).K) := by
          rw [hvB j (by simpa using hj)]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hj, Option.getD_some]
          exact hbit _ ht
        have hHj : IndexMap.entry mh j = 2 * j + 1 := by
          rw [IndexMap.entry_eq_getD_toList, hmh]
          simp [List.getD_eq_getElem?_getD, hj]
        have hLj : IndexMap.entry ml j = 2 * j := by
          rw [IndexMap.entry_eq_getD_toList, hml]
          simp [List.getD_eq_getElem?_getD, hj]
        rw [evalE_mux, hBj, evalE_reindex, evalE_reindex, hHj, hLj, ← Expr.eq_of_beq hX,
          hvX _ (by omega), hvX _ (by omega), mux_bit (hb t0), idxVal_succ, pow_succ]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hb t0) with h0 | h1
        · rw [if_neg (by omega), h0]
          congr 1
          ring
        · rw [if_pos h1, h1]
          congr 1
          ring
      · cases h
    · cases h

end Matchers

/-! ## The digests' matchers are sound -/

section RowsOf

variable {K : Type*} [Field K]

/-- **Row `r` of a table of column blocks** `(value, width)`, the entries read by `rd`: entry `c`
of the block holding it. -/
def rowOf (rd : ℕ → ℕ → K) : List (ℕ × ℕ) → ℕ → ℕ → K
  | [], _, _ => 0
  | (v, w) :: ps, r, c => if c < w then rd v (r * w + c) else rowOf rd ps r (c - w)

/-- **The width of concatenated row maps** is the sum of their widths. -/
theorem mapWidth_append (a b : List RowLeaf) : mapWidth (a ++ b) = mapWidth a + mapWidth b := by
  simp [mapWidth]

/-- **`Mᵀ g` of concatenated row maps** reads the first map's block, then the second's. -/
theorem gVal_append (dec : ℕ → K) (γ : K) : ∀ (a b : List RowLeaf) (k : ℕ),
    gVal dec γ (a ++ b) k = if k < mapWidth a then gVal dec γ a k else gVal dec γ b (k - mapWidth a)
  | [], b, k => by simp [mapWidth]
  | l :: a, b, k => by
    rw [List.cons_append, mapWidth_cons]
    simp only [gVal]
    by_cases h : k < l.n
    · rw [if_pos h, if_pos (by omega), if_pos h]
    · rw [if_neg h, if_neg h, gVal_append dec γ a b]
      by_cases h' : k - l.n < mapWidth a
      · rw [if_pos h', if_pos (by omega)]
      · rw [if_neg h', if_neg (by omega), Nat.sub_sub]

end RowsOf

section GMatch

variable {ir : RealizedProgram} {I : Interp} (rd : ir.Valuation I) (f : ℕ) {γ : (I f).K}

/-- **A named operator on coordinate `k` of its first block.** -/
theorem evalE_apply_lt (op : NamedOp) (E : Expr) {k : ℕ} (hk : k < NamedOp.rows ir op) :
    ir.evalE rd f (.apply op E) k = NamedOp.block ir f rd op (ir.evalE rd f E) k := by
  rw [evalE_apply]
  simp only [NamedOp.apply, Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk, Nat.zero_mul, Nat.zero_add]

/-- **A leaf's column vector** is `γ^k`, or the transposed transform of the powers. -/
theorem xOk_sound (ho : ir.RefsOrdered) (hne : 0 < ir.exprs.length) {c : PowCtx}
    (hc : c.Sound rd f γ) {l : RowLeaf} (hw : l.wf = true) {Xv : Expr} (h : ir.xOk c l Xv = true) :
    ir.exprLen Xv = l.n ∧ ∀ k < l.n, ir.evalE rd f Xv k = l.tcol (I f).decode γ k := by
  have hn := RowLeaf.n_pos hw
  unfold xOk at h
  split at h
  · rename_i n psi Ye
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hntt, rfl⟩, rfl⟩, hY⟩ := h
    obtain ⟨hlY, hvY⟩ := powSym_sound ho hne hc _ _ _ hY
    rw [List.length_range] at hlY hvY
    refine ⟨?_, fun k hk => ?_⟩
    · rw [exprLen_apply, hlY]
      simp [NamedOp.rows, NamedOp.cols, Nat.div_self hn]
    · rw [evalE_apply_lt rd f _ _ (by simpa [NamedOp.rows] using hk)]
      simp only [NamedOp.block, RowLeaf.tcol, hntt, if_true, Ops.nttTranspose, if_pos hk]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hvY m m.isLt]
      simp [List.getD_eq_getElem?_getD, m.isLt]
  · rename_i m Ye
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
    obtain ⟨⟨hntt, -⟩, hY⟩ := h
    obtain ⟨hlY, hvY⟩ := powSym_sound ho hne hc _ _ _ hY
    rw [List.length_range] at hlY hvY
    refine ⟨hlY, fun k hk => ?_⟩
    rw [hvY k hk]
    simp [RowLeaf.tcol, hntt, List.getD_eq_getElem?_getD, hk]
  · cases h

/-- **A leaf's block of `Mᵀ g`** is `γ^off` times its column vector. -/
theorem leafGOk_sound (ho : ir.RefsOrdered) (hne : 0 < ir.exprs.length) {c : PowCtx}
    (hc : c.Sound rd f γ) {l : RowLeaf} (hw : l.wf = true) {E : Expr}
    (h : ir.leafGOk c l E = true) :
    ir.exprLen E = l.n ∧ ∀ k < l.n, ir.evalE rd f E k = γ ^ l.off * l.tcol (I f).decode γ k := by
  unfold leafGOk at h
  split at h
  · rename_i M Xv
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
    obtain ⟨⟨-, hM⟩, hX⟩ := h
    obtain ⟨hlM, hvM⟩ := powSym_sound ho hne hc _ _ _ hM
    obtain ⟨-, hvX⟩ := xOk_sound rd f ho hne hc hw hX
    rw [List.length_replicate] at hlM hvM
    refine ⟨by rw [exprLen_mul, hlM], fun k hk => ?_⟩
    rw [evalE_mul, hvM k hk, hvX k hk]
    simp [List.getD_eq_getElem?_getD, hk]
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hoff, hX⟩ := h
    obtain ⟨hl, hv⟩ := xOk_sound rd f ho hne hc hw hX
    exact ⟨hl, fun k hk => by rw [hv k hk, hoff, pow_zero, one_mul]⟩

/-- **`Mᵀ g` as leaf blocks**: the expression is `Mᵀ g` of the leaves it consumes. -/
theorem gMatch_sound (ho : ir.RefsOrdered) (hne : 0 < ir.exprs.length) {c : PowCtx}
    (hc : c.Sound rd f γ) : ∀ n (ls : List RowLeaf) (E : Expr) (ls' : List RowLeaf),
    (∀ l ∈ ls, l.wf = true) → ir.gMatch c n ls E = some ls' → ∃ pre, ls = pre ++ ls' ∧
      ir.exprLen E = mapWidth pre ∧ ∀ k < mapWidth pre,
        ir.evalE rd f E k = gVal (I f).decode γ pre k
  | 0, _, _, _, _, h => by simp [gMatch] at h
  | _ + 1, [], _, _, _, h => by simp [gMatch] at h
  | n + 1, l :: rest, E, ls', hw, h => by
    simp only [gMatch] at h
    split_ifs at h with hl
    · cases h
      obtain ⟨hlen, hv⟩ := leafGOk_sound rd f ho hne hc (hw l (by simp)) hl
      refine ⟨[l], rfl, by rw [hlen, mapWidth_cons]; simp [mapWidth], fun k hk => ?_⟩
      rw [mapWidth_cons] at hk
      simp only [mapWidth, List.map_nil, List.sum_nil, Nat.add_zero] at hk
      rw [hv k hk]
      simp [gVal, hk]
    · split at h
      · rename_i j _
        obtain ⟨pre, he, hlen, hv⟩ := gMatch_sound ho hne hc n _ _ _ hw h
        exact ⟨pre, he, by rw [exprLen_ref_of ho hne, hlen],
          fun k hk => by rw [evalE_ref_of ho hne, hv k hk]⟩
      · rename_i a b _
        split at h
        · rename_i ls1 ha
          obtain ⟨pa, hea, hla, hva⟩ := gMatch_sound ho hne hc n _ _ _ hw ha
          have hw1 : ∀ l ∈ ls1, l.wf = true := fun l' hl' => hw l' (by rw [hea]; simp [hl'])
          obtain ⟨pb, heb, hlb, hvb⟩ := gMatch_sound ho hne hc n _ _ _ hw1 h
          refine ⟨pa ++ pb, by rw [hea, heb, List.append_assoc], ?_, fun k hk => ?_⟩
          · rw [exprLen_concat, hla, hlb, mapWidth_append]
          · rw [evalE_concat, hla, gVal_append]
            rw [mapWidth_append] at hk
            split_ifs with hk'
            · exact hva k hk'
            · exact hvb _ (by omega)
        · cases h
      · rename_i s d w e
        split_ifs at h with hsd
        obtain ⟨rfl, rfl⟩ := hsd
        split at h
        · rename_i ls1 he
          split_ifs at h with hwid
          cases h
          obtain ⟨pre, hpre, hlen, hv⟩ := gMatch_sound ho hne hc n _ _ _ hw he
          have hW : w = mapWidth pre := by
            rw [hpre, mapWidth_append] at hwid
            omega
          subst hW
          refine ⟨pre, hpre, by simp [exprLen_reindex], fun k hk => ?_⟩
          rw [evalE_reindex, IndexMap.entry_step_one hk, Nat.zero_add, hv k hk]
        · cases h
      · cases h

end GMatch

section Digests

variable {ir : RealizedProgram} {I : Interp} (rd : ir.Valuation I) (f : ℕ) {γ : (I f).K}

/-- **The rows' entries read in field `f`.** -/
def rowRead (v j : ℕ) : (I f).K := castElt (rd v j)

/-- **A block's term of the digests**: row `r`'s block against `G[o, o + w)`. -/
theorem digTermOk_sound {rows o v w : ℕ} {G t : Expr} (h : digTermOk rows o v w G t = true)
    {r : ℕ} (hr : r < rows) : ir.evalE rd f t r =
      ∑ c ∈ Finset.range w, rowRead rd f v (r * w + c) * ir.evalE rd f G (o + c) := by
  unfold digTermOk at h
  split at h
  · rename_i M R W o' d cc G'
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hG⟩ := h
    rw [evalE_apply_lt rd f _ _ (by simpa [NamedOp.rows] using hr)]
    simp only [NamedOp.block, Ops.rowDot, if_pos hr]
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [evalE_reindex, IndexMap.entry_step_one c.isLt, Expr.eq_of_beq hG]
    rfl
  · cases h

/-- **The digests' block terms** sum to row `r` against `G` from offset `o`. -/
theorem digTermsOk_sound {rows : ℕ} {G : Expr} : ∀ {o : ℕ} {ps : List (ℕ × ℕ)} {ts : List Expr},
    digTermsOk rows G o ps ts = true → ∀ {r : ℕ}, r < rows →
      (ts.map fun t => ir.evalE rd f t r).sum = ∑ c ∈ Finset.range (ps.map (·.2)).sum,
        rowOf (rowRead rd f) ps r c * ir.evalE rd f G (o + c)
  | _, [], [], _, _, _ => by simp
  | o, (v, w) :: ps, t :: ts, h, r, hr => by
    simp only [digTermsOk, Bool.and_eq_true] at h
    rw [List.map_cons, List.sum_cons, digTermOk_sound rd f h.1 hr, digTermsOk_sound h.2 hr,
      List.map_cons, List.sum_cons, Finset.sum_range_add]
    congr 1
    · refine Finset.sum_congr rfl fun c hc => ?_
      rw [Finset.mem_range] at hc
      simp [rowOf, hc]
    · refine Finset.sum_congr rfl fun c _ => ?_
      simp only [rowOf, if_neg (Nat.not_lt.2 (Nat.le_add_right _ _)), Nat.add_sub_cancel_left,
        Nat.add_assoc]
  | _, [], _ :: _, h, _, _ | _, _ :: _, [], h, _, _ => by simp [digTermsOk] at h

/-- **The digests' sum**: row `r` against `Mᵀ g`. -/
theorem digSumOk_sound (ho : ir.RefsOrdered) (hne : 0 < ir.exprs.length) {c : PowCtx}
    (hc : c.Sound rd f γ) {m : List RowLeaf} (hw : ∀ l ∈ m, l.wf = true) {parts : List (ℕ × ℕ)}
    (hW : mapWidth m = (parts.map (·.2)).sum) {rows : ℕ} {S : Expr}
    (h : ir.digSumOk c m parts rows S = true) {r : ℕ} (hr : r < rows) :
    ir.evalE rd f S r = ∑ c ∈ Finset.range (mapWidth m),
      rowOf (rowRead rd f) parts r c * gVal (I f).decode γ m c := by
  simp only [digSumOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨ht, hg⟩ := h
  obtain ⟨pre, hpre, -, hv⟩ := gMatch_sound rd f ho hne hc _ _ _ _ hw hg
  rw [List.append_nil] at hpre
  subst hpre
  rw [(evalE_addSpine rd f S).1 r, digTermsOk_sound rd f ht hr, ← hW]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [Nat.zero_add, hv k hk]

/-- **The digests** (`<table>.digests`): entry `r` is row `r` (row `r − rows` of a padding row)
against `Mᵀ g`. -/
theorem digestsOk_sound (ho : ir.RefsOrdered) (hne : 0 < ir.exprs.length) {c : PowCtx}
    (hc : c.Sound rd f γ) {m : List RowLeaf} (hw : ∀ l ∈ m, l.wf = true) {parts : List (ℕ × ℕ)}
    (hW : mapWidth m = (parts.map (·.2)).sum) {rows nd : ℕ} {E : Expr}
    (h : ir.digestsOk c m parts rows nd E = true) {r : ℕ} (hr : r < nd) :
    ir.evalE rd f E r = ∑ c ∈ Finset.range (mapWidth m),
      rowOf (rowRead rd f) parts (if r < rows then r else r - rows) c *
        gVal (I f).decode γ m c := by
  unfold digestsOk at h
  split at h
  · rename_i pm S
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, rfl⟩, hS⟩ := h
    rw [evalE_reindex]
    have he : IndexMap.entry [(0, 1, rows), (0, 1, nd - rows)] r =
        if r < rows then r else r - rows := by
      rw [show ([(0, (1 : ℤ), rows), (0, 1, nd - rows)] : IndexMap) =
          [(0, (1 : ℤ), rows)] ++ [(0, 1, nd - rows)] from rfl, IndexMap.entry_append,
        IndexMap.size_single]
      split_ifs with h3
      · rw [IndexMap.entry_step_one h3, Nat.zero_add]
      · rw [IndexMap.entry_step_one (by omega), Nat.zero_add]
    rw [he]
    exact digSumOk_sound rd f ho hne hc hw hW hS (by split_ifs <;> omega)
  · rename_i S _
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hS⟩ := h
    rw [if_pos hr]
    exact digSumOk_sound rd f ho hne hc hw hW hS hr

end Digests

/-- **The selection's body**: `Σ_b T_b − fold(digests, index) = 0`. -/
theorem TableShape.bodyOk_spec {ir : RealizedProgram} {t : TableShape} {b : PredBody}
    (h : t.bodyOk ir b = true) : ∃ T F tg,
      b = .equal t.dom (.add T (.scale (.const t.mOne) F)) (.leaf t.zero) tg ∧
      ir.recTermsOk t.record t.predCtx t.map (addSpine T) = true ∧
      ir.foldOf? t.idx t.dig (2 ^ t.bits) t.bits (2 * t.bits + 2) F = some (t.bits, 1) := by
  unfold TableShape.bodyOk at h
  split at h
  · rename_i d T c F z tg
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hT⟩, hF⟩ := h
    exact ⟨T, F, tg, rfl, hT, hF⟩
  · cases h

/-! ## The selection -/

/-- **The field facts a selection reads** in a field interpretation: the constant `negOne` decodes
to `−1`, `0` and `1` decode to themselves and read back as `0` and `1`. -/
class SelectField (FA : FieldInterp) (negOne : ℕ) : Prop where
  /-- `negOne` decodes to `−1`. -/
  decode_negOne : FA.decode negOne = -1
  /-- `0` decodes to `0`. -/
  decode_zero : FA.decode 0 = 0
  /-- `1` decodes to `1`. -/
  decode_one : FA.decode 1 = 1
  /-- `0` reads as `0`. -/
  toNat_zero : FA.toNat 0 = 0
  /-- `1` reads as `1`. -/
  toNat_one : FA.toNat 1 = 1

/-- **The program facts of a table's selection** (`lib/gordiehowe/lib/table.h`, `select_row`;
decided per program): the shape (`TableShape`) and its checks, which read the powers
(`<table>.powers`), the digests (`<table>.digests`) and the selection's predicate through the
matchers of `GordieHowe/Language/Library/Table.lean`; the index bits' check, the constants, the
challenge, the fields and sizes of the values read; the record reads only committed values and
constants, the rows only the statement. -/
class TableSelect (program : RealizedProgram) where
  /-- The identifiers and the row map. -/
  shape : TableShape
  /-- The shared expressions read only earlier entries. -/
  refsOrdered : program.RefsOrdered
  /-- The program has shared expressions. -/
  exprs_pos : 0 < program.exprs.length
  /-- The program has values. -/
  values_pos : 0 < program.values.length
  /-- The row map is well formed. -/
  mapWf : mapWfFrom 0 shape.map = true
  /-- The column blocks hold the map's width. -/
  width : mapWidth shape.map = (shape.parts.map (·.2)).sum
  /-- The powers' exponents. -/
  powOk : program.powSym ⟨onePub shape.one shape.gamma, none⟩ powFuel (shape.powExpr program) =
    some (powerExps shape.map)
  /-- The digests. -/
  digOk : program.digestsOk (shape.pubCtx program) shape.map shape.parts shape.rows
    (2 ^ shape.bits) (shape.digExpr program) = true
  /-- The selection's predicate. -/
  bodyOk : shape.bodyOk program (program.predicate shape.pred).body = true
  /-- The powers are a public expression. -/
  powKind : (program.value shape.pow).kind = .pub (.expr (shape.powExpr program))
  /-- The digests are a public expression. -/
  digKind : (program.value shape.dig).kind = .pub (.expr (shape.digExpr program))
  /-- The index bits' check. -/
  idxBool : ∃ t, (program.predicate shape.idxPred).body =
    .equal shape.dom (.mul (.leaf shape.idx) (.leaf shape.idx)) (.leaf shape.idx) t
  /-- The two predicates are source predicates. -/
  inSource : ∀ p ∈ [shape.pred, shape.idxPred],
    p < program.predicates.length ∧ program.inSource (program.predicate p) = true
  /-- The constants `1` and `0`. -/
  consts : program.isConstant shape.one = true ∧ (program.constEntries shape.one).getD 0 0 = 1 ∧
    program.isConstant shape.zero = true ∧ (program.constEntries shape.zero).getD 0 0 = 0
  /-- `γ` is its challenge. -/
  gammaKind : (program.value shape.gamma).kind = .challenge shape.chal
  /-- The challenge is one coordinate drawn from the domain's field. -/
  chalOk : (program.challenge shape.chal).size = 1 ∧
    (program.challenge shape.chal).sampler = .full ∧
    program.chalField shape.chal = program.domainField shape.dom
  /-- The values read are of the domain's field. -/
  fields : ∀ v ∈ [shape.one, shape.zero, shape.gamma, shape.pow, shape.dig, shape.idx] ++
    shape.parts.map (·.1), program.valueField v = program.domainField shape.dom
  /-- The sizes of the values read. -/
  sizes : (program.value shape.one).size = 1 ∧ (program.value shape.gamma).size = 1 ∧
    (program.value shape.idx).size = shape.bits ∧ (program.value shape.dig).size = 2 ^ shape.bits ∧
    (program.value shape.pow).size = (powerExps shape.map).length
  /-- The index bits are committed. -/
  idxPriv : (program.value shape.idx).kind = .priv
  /-- The record reads only values fixed by the statement and the committed assignment. -/
  recordReads : ∀ v ∈ program.exprNodes shape.record, program.nodeReads program.fuel v = []
  /-- The rows read only the statement. -/
  rowReads : ∀ p ∈ shape.parts, program.nodeReads program.values.length p.1 = []

namespace TableSelect

variable {program : RealizedProgram} [TableSelect program] {I : Interp} (f : ℕ)

/-- **The table's width** `W`. -/
abbrev W (program : RealizedProgram) [TableSelect program] : ℕ := mapWidth (shape program).map

/-- **The challenge `γ`** read in field `f`. -/
def gammaOf (e : program.Env I) : (I f).K := castElt (e.chal (shape program).chal 0)

/-- **The record** (`select_row`'s parts, concatenated). -/
def recOf (e : program.Env I) (c : ℕ) : (I f).K := program.evalE (program.reader e) f (shape program).record c

/-- **The index bits** as naturals, `0` past the last. -/
def bitsOf (e : program.Env I) (i : ℕ) : ℕ :=
  if i < (shape program).bits then (I f).toNat (program.evalE (program.reader e) f (.leaf (shape program).idx) i) else 0

/-- **The index** the bits name. -/
def idxOf (e : program.Env I) : ℕ := idxVal (bitsOf f e) (shape program).bits

/-- **The row the index names** (`public_table` pads the rows by repeating them). -/
def rowIdx (e : program.Env I) : ℕ := if idxOf f e < (shape program).rows then idxOf f e else idxOf f e - (shape program).rows

/-- **Row `r` of the table**, read off the statement. -/
def rowAt (e : program.Env I) (r c : ℕ) : (I f).K :=
  rowOf (rowRead (program.read e program.values.length) f) (shape program).parts r c

/-- **The row map applied to the selected row**: `M(row_i)`. -/
def mapOf (e : program.Env I) (c : ℕ) : (I f).K :=
  rowApply (I f).decode (shape program).map (rowAt f e (rowIdx f e)) c

/-- **The selection's predicates hold**: the selection and the index bits' check. -/
def Preds (e : program.Env I) : Prop :=
  ∀ p ∈ [(shape program).pred, (shape program).idxPred], program.HoldsAt e (program.predicate p).body

/-- **The selection's predicates hold** where the source program holds. -/
theorem preds_of_source {e : program.Env I} (hs : program.SourceSatAt e) : Preds e :=
  fun p hp => hs.preds _ (predicate_mem (inSource p hp).1) (inSource p hp).2

/-- **The values read are of field `f`.** -/
theorem fields_mem {v : ℕ} (hv : v ∈ [(shape program).one, (shape program).zero, (shape program).gamma, (shape program).pow, (shape program).dig, (shape program).idx] ++
    (shape program).parts.map (·.1)) (hf : program.domainField (shape program).dom = f) : program.valueField v = f :=
  (fields v hv).trans hf

/-- **The program has a value.** -/
theorem values_length_succ : ∃ n, program.values.length = n + 1 :=
  ⟨program.values.length - 1, by have := values_pos (program := program); omega⟩

variable {f}

/-- **The constant `1` and `γ`, one level down.** -/
theorem pubCtx_one_sound [SelectField (I f) (shape program).mOne] (hf : program.domainField (shape program).dom = f)
    (e : program.Env I) :
    (PowCtx.Sound (program.read e program.values.length) f (gammaOf f e)
      ⟨onePub (shape program).one (shape program).gamma, none⟩) := by
  obtain ⟨n, hn⟩ := values_length_succ (program := program)
  refine ⟨fun v l h => ?_, fun _ _ h => by cases h⟩
  simp only [onePub] at h
  split_ifs at h with h1 h2 <;> cases h
  · subst h1
    obtain ⟨c0, e0, -⟩ := consts (program := program)
    refine ⟨by rw [exprLen_leaf, sizes.1]; rfl, fun i hi => ?_⟩
    simp only [List.length_singleton, Nat.lt_one_iff] at hi
    subst hi
    rw [evalE_leaf, hn]
    simp only [read, kind_of_isConstant c0]
    rw [castElt_decode (fields_mem f (by simp) hf), e0, SelectField.decode_one (negOne := (shape program).mOne)]
    simp
  · subst h2
    refine ⟨by rw [exprLen_leaf, sizes.2.1]; rfl, fun i hi => ?_⟩
    simp only [List.length_singleton, Nat.lt_one_iff] at hi
    subst hi
    rw [evalE_leaf, hn]
    simp only [read, gammaKind (program := program)]
    rw [castElt_castElt_eq, if_pos ((chalOk (program := program)).2.2.trans
      (fields _ (by simp)).symm)]
    simp [gammaOf]

/-- **The powers, one level down**: `γ^(powerExps)`. -/
theorem powExpr_powsAt [SelectField (I f) (shape program).mOne] (hf : program.domainField (shape program).dom = f)
    (e : program.Env I) :
    PowsAt (program.read e program.values.length) f (gammaOf f e) ((shape program).powExpr program)
      (powerExps (shape program).map) :=
  powSym_sound refsOrdered exprs_pos (pubCtx_one_sound hf e) _ _ _ powOk

/-- **The context of the public expressions** is sound one level down. -/
theorem pubCtx_sound [SelectField (I f) (shape program).mOne] (hf : program.domainField (shape program).dom = f)
    (e : program.Env I) :
    PowCtx.Sound (program.read e program.values.length) f (gammaOf f e) ((shape program).pubCtx program) :=
  ⟨(pubCtx_one_sound hf e).pub, fun K ks h => by
    simp only [TableShape.pubCtx, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact powExpr_powsAt hf e⟩

/-- **A public expression's leaf** reads its expression one level down. -/
theorem evalE_leaf_pub (e : program.Env I) {v : ℕ} {E : Expr}
    (hk : (program.value v).kind = .pub (.expr E)) (hf : program.valueField v = f) (i : ℕ) :
    program.evalE (program.reader e) f (.leaf v) i =
      program.evalE (program.read e program.values.length) f E i := by
  rw [evalE_leaf]
  simp only [reader, fuel, read, hk]
  subst hf
  exact castElt_self _

/-- **The context of the selection's predicate** is sound. -/
theorem predCtx_sound [SelectField (I f) (shape program).mOne] (hf : program.domainField (shape program).dom = f)
    (e : program.Env I) :
    PowCtx.Sound (program.reader e) f (gammaOf f e) ((shape program).predCtx) := by
  refine ⟨fun v l h => ?_, fun _ _ h => by cases h⟩
  simp only [TableShape.predCtx] at h
  split_ifs at h with hv
  cases h
  subst hv
  obtain ⟨-, hp⟩ := powExpr_powsAt hf e
  refine ⟨by rw [exprLen_leaf, sizes.2.2.2.2], fun i hi => ?_⟩
  rw [evalE_leaf_pub e powKind (fields_mem f (by simp) hf), hp i hi]

/-- **The digests**: digest `r` is the selected row's fingerprint `Σ_c M(row_r)_c γ^(e(c))`. -/
theorem evalE_dig [SelectField (I f) (shape program).mOne] (hf : program.domainField (shape program).dom = f)
    (e : program.Env I) {r : ℕ} (hr : r < 2 ^ (shape program).bits) :
    program.evalE (program.reader e) f (.leaf (shape program).dig) r =
      ∑ c ∈ Finset.range (W program), rowApply (I f).decode (shape program).map
        (rowAt f e (if r < (shape program).rows then r else r - (shape program).rows)) c * gammaOf f e ^ cellExp (shape program).map c := by
  have hw := mapWfFrom_wf (mapWf (program := program))
  rw [evalE_leaf_pub e digKind (fields_mem f (by simp) hf),
    digestsOk_sound _ f refsOrdered exprs_pos (pubCtx_sound hf e) hw width digOk hr,
    sum_gVal _ _ mapWf]
  simp only [Nat.zero_add]
  rfl

end TableSelect

namespace TableSelect

variable {program : RealizedProgram} [TableSelect program] {I : Interp} {f : ℕ}

/-- **The selection's left side** `Σ_b T_b − fold(digests, index)`, at index bits that are bits:
the record's fingerprint `Σ_c rec_c γ^(e(c))` less the selected row's `Σ_c M(row_i)_c γ^(e(c))`
(`e` the power indices, `cellExp`). -/
theorem evalE_lhs [SelectField (I f) (shape program).mOne]
    (hf : program.domainField (shape program).dom = f) (e : program.Env I) {T F : Expr}
    (hT : program.recTermsOk (shape program).record (shape program).predCtx (shape program).map
      (addSpine T) = true)
    (hF : program.foldOf? (shape program).idx (shape program).dig (2 ^ (shape program).bits)
      (shape program).bits (2 * (shape program).bits + 2) F = some ((shape program).bits, 1))
    (hb : ∀ i < (shape program).bits, bitsOf f e i ≤ 1 ∧
      program.evalE (program.reader e) f (.leaf (shape program).idx) i = (bitsOf f e i : (I f).K)) :
    program.exprLen (.add T (.scale (.const (shape program).mOne) F)) = 1 ∧
      program.evalE (program.reader e) f (.add T (.scale (.const (shape program).mOne) F)) 0 =
        ∑ c ∈ Finset.range (W program), recOf f e c * gammaOf f e ^ cellExp (shape program).map c -
          ∑ c ∈ Finset.range (W program),
            mapOf f e c * gammaOf f e ^ cellExp (shape program).map c := by
  obtain ⟨hsum, t0, rest, hsp, hlen⟩ := evalE_addSpine (program.reader e) f T
  obtain ⟨hv, hl⟩ := recTermsOk_sound (program.reader e) f refsOrdered exprs_pos
    (predCtx_sound hf e) mapWf hT
  have hb' : ∀ i, bitsOf f e i ≤ 1 := fun i => by
    by_cases hi : i < (shape program).bits
    · exact (hb i hi).1
    · simp [bitsOf, hi]
  obtain ⟨-, hvF⟩ := foldOf_sound (program.reader e) f refsOrdered exprs_pos sizes.2.2.2.1 hb'
    (fun i hi => (hb i hi).2) _ F _ _ hF
  refine ⟨by rw [exprLen_add, hlen, hl t0 rest hsp], ?_⟩
  have h1 := sum_leaves (fun c x => recOf f e c * gammaOf f e ^ x) (mapWf (program := program))
  simp only [Nat.zero_add] at h1
  rw [evalE_add, hsum 0, hv, evalE_scale_const, SelectField.decode_negOne, hvF 0 (by omega),
    Nat.mul_zero, Nat.zero_add, evalE_dig hf e (idxVal_lt hb' _)]
  unfold recOf at h1 ⊢
  rw [h1, neg_one_mul, ← sub_eq_add_neg]
  rfl

/-- **The index bits are bits** where the selection's predicates hold. -/
theorem bitsOf_spec [SelectField (I f) (shape program).mOne]
    (hf : program.domainField (shape program).dom = f) {e : program.Env I} (hs : Preds e) {i : ℕ}
    (hi : i < (shape program).bits) : bitsOf f e i ≤ 1 ∧
      program.evalE (program.reader e) f (.leaf (shape program).idx) i = (bitsOf f e i : (I f).K) := by
  obtain ⟨t, hbody⟩ := idxBool (program := program)
  have h := hs (shape program).idxPred (by simp)
  rw [HoldsAt, hbody] at h
  have hx := h i (by rw [exprLen_mul, exprLen_leaf, sizes.2.2.1]; exact hi)
  unfold evalWith at hx
  rw [hf, evalE_mul] at hx
  unfold bitsOf
  rw [if_pos hi]
  rcases eq_zero_or_one_of_sq_eq_self ((sq _).trans hx) with h0 | h1
  · rw [h0, SelectField.toNat_zero (negOne := (shape program).mOne), Nat.cast_zero]
    exact ⟨by norm_num, rfl⟩
  · rw [h1, SelectField.toNat_one (negOne := (shape program).mOne), Nat.cast_one]
    exact ⟨le_rfl, rfl⟩

/-- **The index is below `2^bits`.** -/
theorem idxOf_lt [SelectField (I f) (shape program).mOne]
    (hf : program.domainField (shape program).dom = f) {e : program.Env I} (hs : Preds e) :
    idxOf f e < 2 ^ (shape program).bits :=
  idxVal_lt (fun i => by
    by_cases hi : i < (shape program).bits
    · exact (bitsOf_spec hf hs hi).1
    · simp [bitsOf, hi]) _

/-- **The selected row is a row of the table.** -/
theorem rowIdx_lt [SelectField (I f) (shape program).mOne]
    (hf : program.domainField (shape program).dom = f) {e : program.Env I} (hs : Preds e) :
    rowIdx f e < (shape program).rows := by
  have hi := idxOf_lt hf hs
  have hd := digOk (program := program)
  unfold digestsOk at hd
  have hle : 2 ^ (shape program).bits ≤ 2 * (shape program).rows := by
    split at hd
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
      omega
    · simp only [Bool.and_eq_true, beq_iff_eq] at hd
      omega
  unfold rowIdx
  split_ifs with h
  · exact h
  · omega

/-- **The zero constant** reads `0`. -/
theorem evalE_zero [SelectField (I f) (shape program).mOne]
    (hf : program.domainField (shape program).dom = f) (e : program.Env I) :
    program.evalE (program.reader e) f (.leaf (shape program).zero) 0 = 0 := by
  obtain ⟨-, -, c1, e1⟩ := consts (program := program)
  rw [evalE_leaf_of_isConstant e c1, constRead_of_valueField (fields_mem f (by simp) hf), e1,
    SelectField.decode_zero (negOne := (shape program).mOne)]

/-- **The selection** (`select_row`): where its predicates hold, the record's fingerprint is the
selected row's, `Σ_c rec_c γ^(e(c)) = Σ_c M(row_i)_c γ^(e(c))`. -/
theorem select_eq [SelectField (I f) (shape program).mOne]
    (hf : program.domainField (shape program).dom = f) {e : program.Env I} (hs : Preds e) :
    ∑ c ∈ Finset.range (W program), recOf f e c * gammaOf f e ^ cellExp (shape program).map c =
      ∑ c ∈ Finset.range (W program), mapOf f e c * gammaOf f e ^ cellExp (shape program).map c := by
  obtain ⟨T, F, tg, hbody, hT, hF⟩ := TableShape.bodyOk_spec (bodyOk (program := program))
  obtain ⟨hlen, hval⟩ := evalE_lhs hf e hT hF fun i hi => bitsOf_spec hf hs hi
  have h := hs (shape program).pred (by simp)
  rw [HoldsAt, hbody] at h
  have hx := h 0 (by rw [hlen]; omega)
  unfold evalWith at hx
  rw [hf, hval, evalE_zero hf e] at hx
  exact sub_eq_zero.1 hx

/-! ## The selection's event -/

/-- **The selection's polynomial**: `Σ_c (rec_c − M(row_i)_c) X^(e(c))`. -/
noncomputable def selPoly (f : ℕ) (e : program.Env I) : Polynomial (I f).K :=
  ∑ c ∈ Finset.range (W program),
    Polynomial.C (recOf f e c - mapOf f e c) * Polynomial.X ^ cellExp (shape program).map c

/-- **The selection's polynomial has degree at most `W − 1`** (`cellExp_lt`). -/
theorem selPoly_natDegree (e : program.Env I) : (selPoly f e).natDegree ≤ W program - 1 := by
  unfold selPoly
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun c hc => ?_
  have := cellExp_lt mapWf (Finset.mem_range.1 hc)
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by unfold W; omega)

/-- **The selection's event**: `γ` is a root of the selection's polynomial, which is nonzero
(degree at most `W − 1`). -/
noncomputable def selEvent (f : ℕ) (e : program.Env I) : ChallengeEvent (I f).K :=
  ⟨selPoly f e, W program - 1, selPoly_natDegree e⟩

/-- **The selection's event at challenge `j`** (`RealizedProgram.rbr_of_events`' events): `j` is
the table's challenge and `γ` is a root of the selection's polynomial. -/
def SelBad (f : ℕ) (j : ℕ) (e : program.Env I) : Prop :=
  j = (shape program).chal ∧ (selEvent f e).BadAt (gammaOf f e)

/-- **A row reads only its blocks' values.** -/
theorem rowOf_congr {K : Type*} [Field K] {rd rd' : ℕ → ℕ → K} :
    ∀ {ps : List (ℕ × ℕ)}, (∀ p ∈ ps, rd p.1 = rd' p.1) → rowOf rd ps = rowOf rd' ps
  | [], _ => rfl
  | (v, w) :: ps, h => by
    funext r c
    simp only [rowOf]
    rw [h (v, w) (by simp), rowOf_congr (fun p hp => h p (by simp [hp]))]

/-- **The record is fixed by the statement and the committed assignment**
(`TableSelect.recordReads`). -/
theorem recOf_congr {e e' : program.Env I} (hs : e.stmt = e'.stmt) (ha : e.asg = e'.asg) :
    recOf f e = recOf f e' := by
  funext c
  unfold recOf
  rw [evalE_congr fun v hv => reader_eq_of_nodeReads_nil (recordReads v hv) hs ha]

/-- **The index bits are fixed by the committed assignment.** -/
theorem bitsOf_congr {e e' : program.Env I} (ha : e.asg = e'.asg) : bitsOf f e = bitsOf f e' := by
  funext i
  unfold bitsOf
  rw [evalE_leaf, evalE_leaf, reader_of_priv e idxPriv, reader_of_priv e' idxPriv, ha]

/-- **The selected row's image is fixed by the statement and the committed assignment**
(`TableSelect.rowReads`). -/
theorem mapOf_congr {e e' : program.Env I} (hs : e.stmt = e'.stmt) (ha : e.asg = e'.asg) :
    mapOf f e = mapOf f e' := by
  have hr : rowAt f e = rowAt f e' := by
    unfold rowAt
    have h : rowOf (rowRead (program.read e program.values.length) f) (shape program).parts =
        rowOf (rowRead (program.read e' program.values.length) f) (shape program).parts := by
      refine rowOf_congr fun p hp => ?_
      have hag : Env.AgreeOn (program.nodeReads program.values.length p.1) e e' :=
        ⟨hs, ha, fun _ h => by simp [rowReads p hp] at h, fun _ h => by simp [rowReads p hp] at h⟩
      funext j
      unfold rowRead
      rw [read_congr _ p.1 hag]
    rw [h]
  have hi : rowIdx f e = rowIdx f e' := by
    unfold rowIdx idxOf
    rw [bitsOf_congr ha]
  unfold mapOf
  rw [hr, hi]

/-- **The selection's event is fixed by the statement and the committed assignment.** -/
theorem selEvent_congr {e e' : program.Env I} (hs : e.stmt = e'.stmt) (ha : e.asg = e'.asg) :
    selEvent f e = selEvent f e' := by
  simp only [selEvent, selPoly, recOf_congr hs ha, mapOf_congr hs ha]

/-- **The challenge-use rule** (`RealizedProgram.ChallengeUseAt`): the event reads the statement, the
committed assignment and the table's challenge. -/
theorem selBad_use : ChallengeUseAt program I (SelBad (program := program) f) := by
  intro j e e' h
  unfold SelBad
  rw [selEvent_congr h.stmt h.asg]
  by_cases hj : j = (shape program).chal
  · subst hj
    unfold gammaOf
    rw [h.chal (shape program).chal (Or.inr ⟨rfl, le_refl _⟩)]
  · simp [hj]

/-- **The event's probability**: at most `(W − 1)/|F|` at the table's challenge
(`RealizedProgram.probUniform_badAt_setChal_le`, Schwartz–Zippel). -/
theorem selBad_bound (hf : program.domainField (shape program).dom = f) (e : program.Env I) :
    Pr[c ← program.ChalVal I (shape program).chal :
        SelBad f (shape program).chal (e.setChal (shape program).chal c)] ≤
      ((((W program - 1 : ℕ) : ℝ≥0) / Fintype.card (I f).K : ℝ≥0) : ℝ≥0∞) := by
  have hset : ∀ c, SelBad f (shape program).chal (e.setChal (shape program).chal c) ↔
      (selEvent f e).BadAt (castElt ((e.setChal (shape program).chal c).chal
        (shape program).chal 0)) := fun c => by
    simp only [SelBad, true_and]
    rw [selEvent_congr (e := e.setChal (shape program).chal c) (e' := e) rfl rfl]
    rfl
  simp only [hset]
  obtain ⟨hsz, hsm, hcf⟩ := chalOk (program := program)
  exact probUniform_badAt_setChal_le hsz hsm (hcf.trans hf) (selEvent f e) e

/-- **Without the event, the record is the selected row's image** `M(row_i)`, coordinatewise: the
fingerprints agree (`select_eq`), so `γ` is a root of the selection's polynomial, which is then
`0`, and the power indices are distinct (`cellExp_inj`). -/
theorem record_eq_of_not_bad [SelectField (I f) (shape program).mOne]
    (hf : program.domainField (shape program).dom = f) {e : program.Env I} (hs : Preds e)
    (hev : ¬ SelBad f (shape program).chal e) {c : ℕ} (hc : c < W program) :
    recOf f e c = mapOf f e c := by
  have heval : (selPoly f e).eval (gammaOf f e) = 0 := by
    rw [selPoly, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      sub_mul, Finset.sum_sub_distrib]
    rw [select_eq hf hs, sub_self]
  have hz : selPoly f e = 0 := by
    by_contra hne
    exact hev ⟨rfl, hne, heval⟩
  have hco := congrArg (fun p => p.coeff (cellExp (shape program).map c)) hz
  simp only [selPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at hco
  rw [Finset.sum_eq_single c (fun c' hc' hne => if_neg fun h =>
      hne (cellExp_inj mapWf (Finset.mem_range.1 hc') hc h.symm))
    (fun h => absurd (Finset.mem_range.2 hc) h), if_pos rfl] at hco
  exact sub_eq_zero.1 hco

end TableSelect

end GordieHowe.RealizedProgram
