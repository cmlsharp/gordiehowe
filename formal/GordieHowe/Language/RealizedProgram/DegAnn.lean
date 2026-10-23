-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Check

@[expose] public section

/-!
# GordieHowe: the exported degrees through degree annotations

`degreesAtB c` builds the per-coordinate degrees of every value and shared expression in
challenge `c` as runs (`valDegT`, `refDegVT`). The compiler emits, per challenge, a **degree
annotation** (`DegAnn`): for every value and every shared expression a bound on its coordinates'
degrees, two packed tables of fixed-width entries. One local rule per entry checks the bound from
its expression's degree (`Expr.deg`, the largest over its coordinates, a product's the sum) at its
children's bounds, and every predicate's and public expression's exported degree is checked
against those bounds (`degAnnOkB`). A coordinate's degree is at most its expression's
(`Expr.degAt_le`), so the annotation's check gives `degreesAtB c` (`degreesAtB_of_ann`) without
building the runs.
-/

namespace GordieHowe.RealizedProgram

/-! ## Bounds on lists -/

theorem foldr_max_le {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x ≤ B) : l.foldr max 0 ≤ B := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    exact max_le (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem le_foldr_max {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons a l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem maxBelow_le {n : ℕ} {g : ℕ → ℕ} {B : ℕ} (h : ∀ t < n, g t ≤ B) : maxBelow n g ≤ B :=
  foldr_max_le fun x hx => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    exact h t (List.mem_range.1 ht)

theorem sum_le_length_mul {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x ≤ B) : l.sum ≤ l.length * B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
    have := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    have := h a List.mem_cons_self
    omega

/-! ## A coordinate's degree is at most the expression's -/

section

variable (ir : RealizedProgram)

theorem Coef.degAt_le {nd : ℕ → ℕ → ℕ} {ndU : ℕ → ℕ} (hn : ∀ v i, nd v i ≤ ndU v) (c : Coef) :
    c.degAt nd ≤ (c.nodes.map ndU).foldr max 0 := by
  cases c with
  | const _ => exact Nat.zero_le _
  | node v i => exact le_trans (hn v i) (le_max_left _ _)

mutual

/-- **A coordinate's degree is at most the expression's**, for value and shared-expression degrees
that bound every coordinate's. -/
theorem Expr.degAt_le {nd rd : ℕ → ℕ → ℕ} {ndU rdU : ℕ → ℕ} (hn : ∀ v i, nd v i ≤ ndU v)
    (hr : ∀ k i, rd k i ≤ rdU k) (rl : ℕ → ℕ) :
    ∀ (e : Expr) (i : ℕ), Expr.degAt ir nd rd rl e i ≤ e.deg ndU rdU
  | .leaf v, i => hn v i
  | .add e e', i => max_le_max (Expr.degAt_le hn hr rl e i) (Expr.degAt_le hn hr rl e' i)
  | .sub e e', i => max_le_max (Expr.degAt_le hn hr rl e i) (Expr.degAt_le hn hr rl e' i)
  | .scale c e, i => Nat.add_le_add (Coef.degAt_le hn c) (Expr.degAt_le hn hr rl e i)
  | .mul e e', i => Nat.add_le_add (Expr.degAt_le hn hr rl e i) (Expr.degAt_le hn hr rl e' i)
  | .reindex idx e, i => Expr.degAt_le hn hr rl e (idx.entry i)
  | .concat e e', i => by
    simp only [Expr.degAt, Expr.deg]
    split
    · exact le_trans (Expr.degAt_le hn hr rl e i) (le_max_left _ _)
    · exact le_trans (Expr.degAt_le hn hr rl e' _) (le_max_right _ _)
  | .linear rows e, i => by
    simp only [Expr.degAt, Expr.deg]
    refine foldr_max_le fun x hx => ?_
    obtain ⟨r, hr', rfl⟩ := List.mem_map.1 hx
    refine Nat.add_le_add ?_ (Expr.degAt_le hn hr rl e r.1)
    refine le_trans (Coef.degAt_le hn r.2) (foldr_max_le fun y hy => le_foldr_max ?_)
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hy
    refine List.mem_map_of_mem (List.mem_flatMap.2 ⟨r.2, ?_, hu⟩)
    have hrow : rows.getD i [] ∈ rows := by
      by_cases hi : i < rows.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        exact List.getElem_mem hi
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hr'
        simp at hr'
    simp only [Expr.rowCoefs, List.mem_flatMap, List.mem_map]
    exact ⟨_, hrow, r, hr', rfl⟩
  | .prod n e, i => by
    simp only [Expr.degAt, Expr.deg]
    have h := sum_le_length_mul
      (l := (List.range n).map fun t => Expr.degAt ir nd rd rl e (i * n + t))
      (B := e.deg ndU rdU) fun x hx => by
        obtain ⟨t, -, rfl⟩ := List.mem_map.1 hx
        exact Expr.degAt_le hn hr rl e (i * n + t)
    simpa using h
  | .mux b t e, i => Nat.add_le_add (Expr.degAt_le hn hr rl b i)
      (max_le_max (Expr.degAt_le hn hr rl t i) (Expr.degAt_le hn hr rl e i))
  | .apply op e, i => by
    simp only [Expr.degAt, Expr.deg, NamedOp.opDeg]
    refine Nat.add_le_add (foldr_max_le fun x hx => ?_)
      (maxBelow_le fun t _ => Expr.degAt_le hn hr rl e _)
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hx
    exact maxBelow_le fun t _ => le_trans (hn v t) (le_foldr_max (List.mem_map_of_mem hv))
  | .ref k, i => hr k i
  | .logic _ w args, i => by
    simp only [Expr.degAt, Expr.deg]
    exact Nat.mul_le_mul_left _ (Expr.degAtList_le hn hr rl args i w)

/-- The coordinates' degrees of a list of expressions, at most their degrees. -/
theorem Expr.degAtList_le {nd rd : ℕ → ℕ → ℕ} {ndU rdU : ℕ → ℕ} (hn : ∀ v i, nd v i ≤ ndU v)
    (hr : ∀ k i, rd k i ≤ rdU k) (rl : ℕ → ℕ) :
    ∀ (args : List Expr) (i w : ℕ),
      ((Expr.degAtList ir nd rd rl args).map fun g =>
        maxBelow w fun t => g (i * w + t)).foldr max 0 ≤ (Expr.degList ndU rdU args).foldr max 0
  | [], _, _ => Nat.zero_le _
  | e :: es, i, w => by
    simp only [Expr.degAtList, Expr.degList, List.map_cons, List.foldr_cons]
    exact max_le_max (maxBelow_le fun t _ => Expr.degAt_le hn hr rl e (i * w + t))
      (Expr.degAtList_le hn hr rl es i w)

end

end

/-! ## The annotation -/

/-- **A degree annotation in one challenge**: packed tables of `w`-bit bounds on the degrees of the
values' (`vals`) and the shared expressions' (`refs`) coordinates. -/
structure DegAnn where
  /-- The values' bounds. -/
  vals : ℕ
  /-- The shared expressions' bounds. -/
  refs : ℕ
  /-- The width of a bound. -/
  w : ℕ
  deriving Repr, Inhabited

namespace DegAnn

/-- **Entry `i` of a packed table** of `w`-bit entries: bits `[w i, w (i + 1))` of `T`. -/
def entry (T w i : ℕ) : ℕ := (T >>> (w * i)) % 2 ^ w

/-- The bound of value `v`. -/
def val (a : DegAnn) (v : ℕ) : ℕ := entry a.vals a.w v

/-- The bound of shared expression `k` among `n` (past them, value `0`'s: what the default
expression `leaf 0` reads). -/
def ref (a : DegAnn) (n k : ℕ) : ℕ := if k < n then entry a.refs a.w k else a.val 0

end DegAnn

section Check

variable (ir : RealizedProgram)

/-- **The degree annotation in challenge `c` checks**, in one pass over each list: every value's
bound covers its expression's degree at the bounds (a public expression) or its own (a value of
challenge `c`); every shared expression's covers its expression's; every predicate's expressions'
degrees are within its exported degree at the bounds, or else its exact degree (`exprDegM`, the
per-coordinate check, for a predicate the bounds do not settle), and every public expression's
bound within its own. -/
def degAnnOkB (c : ℕ) (a : DegAnn) : Bool :=
  allIdx (fun v x => match x.kind with
    | .pub (.expr e) =>
      decide (e.deg a.val (a.ref ir.exprs.length) ≤ a.val v) &&
        decide (a.val v ≤ (x.degree.lookup c).getD 0)
    | .challenge c' => decide ((if c' = c then 1 else 0) ≤ a.val v)
    | _ => true) ir.values 0 &&
  allIdx (fun k e => decide (e.deg a.val (a.ref ir.exprs.length) ≤ a.ref ir.exprs.length k))
    ir.exprs 0 &&
  ir.predicates.all fun p =>
    (p.body.exprs.all fun de => decide (de.2.deg a.val (a.ref ir.exprs.length) ≤ p.deg c)) ||
      decide (ir.exprDegM c p.body ≤ p.deg c)

end Check

variable {ir : RealizedProgram}

/-- **The annotation's bounds cover the shared expressions' coordinates' degrees**, at value
degrees its bounds cover. -/
theorem refDegAt_le_ann {a : DegAnn}
    (hk : ∀ k < ir.exprs.length,
      (ir.expr k).deg a.val (a.ref ir.exprs.length) ≤ a.ref ir.exprs.length k)
    {nd : ℕ → ℕ → ℕ} (hn : ∀ v i, nd v i ≤ a.val v) :
    ∀ m k i, ir.refDegAt nd m k i ≤ a.ref ir.exprs.length k
  | 0, _, _ => Nat.zero_le _
  | m + 1, k, i => by
    simp only [refDegAt]
    have h := Expr.degAt_le ir hn (refDegAt_le_ann hk hn m) (ir.refLen ir.exprs.length) (ir.expr k) i
    by_cases hkl : k < ir.exprs.length
    · exact le_trans h (hk k hkl)
    · have he : ir.expr k = .leaf 0 := by
        rw [RealizedProgram.expr, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      rw [he] at h ⊢
      simp only [DegAnn.ref, if_neg hkl]
      simpa [Expr.degAt] using hn 0 i

/-- **The annotation's bounds cover the values' coordinates' degrees** in challenge `c`. -/
theorem nodeDegAt_le_ann {c : ℕ} {a : DegAnn} (h : ir.degAnnOkB c a = true) :
    ∀ n v i, ir.nodeDegAt c n v i ≤ a.val v := by
  unfold degAnnOkB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hv, hk⟩, -⟩ := h
  rw [allIdx_iff] at hv hk
  have hk' : ∀ k < ir.exprs.length,
      (ir.expr k).deg a.val (a.ref ir.exprs.length) ≤ a.ref ir.exprs.length k := fun k hkl => by
    have := hk k hkl
    simp only [Nat.zero_add, decide_eq_true_eq] at this
    exact this
  intro n
  induction n with
  | zero => intro v i; exact Nat.zero_le _
  | succ n ih =>
    intro v i
    simp only [nodeDegAt]
    by_cases hvl : v < ir.values.length
    · have hc := hv v hvl
      simp only [Nat.zero_add] at hc
      change (match (ir.value v).kind with
        | .pub (.expr e) =>
          decide (e.deg a.val (a.ref ir.exprs.length) ≤ a.val v) &&
            decide (a.val v ≤ ((ir.value v).degree.lookup c).getD 0)
        | .challenge c' => decide ((if c' = c then 1 else 0) ≤ a.val v)
        | _ => true) = true at hc
      split
      · rename_i e he
        rw [he] at hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact le_trans (Expr.degAt_le ir ih (refDegAt_le_ann hk' ih _) _ e i) hc.1
      · rename_i c' he
        rw [he] at hc
        simpa using hc
      · exact Nat.zero_le _
    · have hd : ir.value v = default := by
        rw [RealizedProgram.value, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      rw [hd]
      exact Nat.zero_le _

/-- **The exported degrees in challenge `c` are sound** from a degree annotation that checks. -/
theorem degreesAtB_of_ann (hwf : ir.WellFormed) {c : ℕ} {a : DegAnn}
    (h : ir.degAnnOkB c a = true) : ir.degreesAtB c = true := by
  have hn := nodeDegAt_le_ann h
  have h' := h
  unfold degAnnOkB at h'
  simp only [Bool.and_eq_true] at h'
  obtain ⟨⟨hv, hk⟩, hp⟩ := h'
  rw [allIdx_iff] at hv hk
  have hk' : ∀ k < ir.exprs.length,
      (ir.expr k).deg a.val (a.ref ir.exprs.length) ≤ a.ref ir.exprs.length k := fun k hkl => by
    have := hk k hkl
    simp only [Nat.zero_add, decide_eq_true_eq] at this
    exact this
  have hdeg : ∀ e i, ir.degAtOf (ir.nodeDegAt c ir.fuel) e i ≤
      e.deg a.val (a.ref ir.exprs.length) := fun e i =>
    Expr.degAt_le ir (hn ir.fuel) (refDegAt_le_ann hk' (hn ir.fuel) _) _ e i
  unfold degreesAtB
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨fun p hpm => ?_, ?_⟩
  · rcases Bool.or_eq_true_iff.1 (List.all_eq_true.1 hp p hpm) with hs | hx
    · rw [exprDegM_eq hwf hpm, exprDeg]
      refine foldr_max_le fun x hx => ?_
      obtain ⟨de, hde, rfl⟩ := List.mem_map.1 hx
      have hb := List.all_eq_true.1 hs de hde
      refine maxBelow_le fun i _ => le_trans (hdeg de.2 i) ?_
      simpa using hb
    · simpa using hx
  · rw [allIdx_iff]
    intro v hvl
    have hc := hv v hvl
    simp only [Nat.zero_add] at hc ⊢
    have hx : ir.values.getD v default = ir.value v := rfl
    rw [hx] at hc ⊢
    rw [Bool.or_eq_true, Bool.not_eq_true']
    cases hk : (ir.value v).kind with
    | pub d =>
      cases d with
      | expr e =>
        right
        rw [hk] at hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        rw [decide_eq_true_eq, RunVec.maxUpTo_eq]
        refine maxBelow_le fun i _ => ?_
        rw [valDegM_get hwf c hvl i]
        exact le_trans (hn ir.fuel v i) hc.2
      | _ => left; rfl
    | _ => left; rfl

end GordieHowe.RealizedProgram
