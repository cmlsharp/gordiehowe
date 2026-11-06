-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Check
public import GordieHowe.Language.RealizedProgram.StructureCheck
public import GordieHoweNative.Language.RealizedProgram.Annotations

@[expose] public section

/-!
# GordieHowe: structural annotations of the shared expressions, as checked data

`WellFormed`'s checker (`wellFormedB`) reads, for every expression of the program, the closures of
its shared expressions under three node functions (`closAll` through `closureT`: the values read,
the values read in the expression's field, the public coefficient values) and their lengths
(`lenT`). The kernel builds each of these tables, one `NatTrie` of lists or lengths per module.

The compiler emits **annotations** (`ExprAnn`) per shared expression. The checks read four: an
upper bound on the values its closure reads (`maxId`, one past the largest), the set of fields of
the values it reads in its own field (`fields`, a bit set), whether every coefficient value it
reads is public (`pub`, a bit mask over the shared expressions), and its length (`len`). The first, second and fourth are
packed tables of fixed-width entries (`packedGet`), read with `Nat` shifts. Each is checked by one
local rule per shared expression, from the expression and the annotations of the entries it
references (`exprAnnOkB`), in one pass; the rules give the closures' facts at every entry
(`refClosure_of_rule`) and the lengths (`len_eq_lenT`), so `wellFormedA` with the annotations
decides `wellFormedB` (`wellFormedB_of_ann`) without building the tables.

Everything here is stated for any realized program.

The definitions are in `GordieHoweNative/Language/RealizedProgram/Annotations.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

/-! ## Packed tables -/

section Rules

variable {ir : RealizedProgram}

/-- **A local rule gives the closure**: when every shared expression's annotation `A k` covers
(`R`) the values `g` gives the expression, and every annotation of an entry it references covers
only what `A k` covers, `A k` covers the closure of entry `k` at every fuel above it. -/
theorem refClosure_of_rule {α : Type} (ho : ir.RefsOrdered) (g : Expr → List ℕ) (A : ℕ → α)
    (R : α → ℕ → Prop)
    (hstep : ∀ k < ir.exprs.length, (∀ x ∈ g (ir.expr k), R (A k) x) ∧
      ∀ j ∈ (ir.expr k).refs, ∀ x, R (A j) x → R (A k) x) :
    ∀ n k, k < n → k < ir.exprs.length → ∀ x ∈ ir.refClosure g n k, R (A k) x
  | 0, _, hk, _, _, _ => absurd hk (Nat.not_lt_zero _)
  | n + 1, k, hkn, hk, x, hx => by
    rw [refClosure, List.mem_append, List.mem_flatMap] at hx
    rcases hx with hx | ⟨j, hj, hx⟩
    · exact (hstep k hk).1 x hx
    · have hjk := ho k hk j hj
      exact (hstep k hk).2 j hj x
        (refClosure_of_rule ho g A R hstep n j (by omega) (by omega) x hx)

/-- **A closure's test through the annotations**: `closAll g p e` holds when `g e` passes and the
annotation of every entry `e` references covers only values passing `p`. -/
theorem closAll_of_rule {α : Type} (ho : ir.RefsOrdered) (g : Expr → List ℕ) (A : ℕ → α)
    (R : α → ℕ → Prop)
    (hstep : ∀ k < ir.exprs.length, (∀ x ∈ g (ir.expr k), R (A k) x) ∧
      ∀ j ∈ (ir.expr k).refs, ∀ x, R (A j) x → R (A k) x)
    (p : ℕ → Bool) {e : Expr} (he : ∀ k ∈ e.refs, k < ir.exprs.length)
    (hd : (g e).all p = true) (hr : ∀ k ∈ e.refs, ∀ x, R (A k) x → p x = true) :
    ir.closAll g p e = true := by
  rw [closAll, Bool.and_eq_true]
  refine ⟨hd, List.all_eq_true.2 fun k hk => List.all_eq_true.2 fun x hx => ?_⟩
  have hk' := he k hk
  have hx' := (mem_closureT ho g (Nat.lt_succ_self k) hk' x).2 hx
  exact hr k hk x (refClosure_of_rule ho g A R hstep (k + 1) k (Nat.lt_succ_self k) hk' x hx')

end Rules

/-! ## Lists with the same elements -/

theorem testBit_bitsOf (l : List ℕ) (w : ℕ) : (bitsOf l).testBit w = decide (w ∈ l) := by
  induction l with
  | nil => simp [bitsOf]
  | cons x l ih =>
    simp only [bitsOf, List.foldr_cons] at ih ⊢
    rw [Nat.testBit_or, Nat.testBit_two_pow, ih]
    by_cases h : w = x
    · subst h
      simp
    · simp [h, Ne.symm h]

theorem sameMemB_iff {a b : List ℕ} : sameMemB a b = true ↔ ∀ w, w ∈ a ↔ w ∈ b := by
  simp only [sameMemB, beq_iff_eq]
  constructor
  · intro h w
    have := testBit_bitsOf a w
    rw [h, testBit_bitsOf] at this
    simpa using this.symm
  · intro h
    refine Nat.eq_of_testBit_eq fun w => ?_
    rw [testBit_bitsOf, testBit_bitsOf]
    simp [h w]

/-! ## The shared expressions' values as packed lists -/

section Packed

variable (ir : RealizedProgram)

variable {ir}

/-- **The packed lists hold the closures** (`refClosure Expr.directNodes`) at every fuel above
the entry. -/
theorem mem_get_of_closuresOk {c : PackedLists} (h : ir.closuresOkB c = true) :
    ∀ n k, k < n → k < ir.exprs.length → ∀ v,
      v ∈ ir.refClosure Expr.directNodes n k ↔ v ∈ c.get k
  | 0, _, hk, _, _ => absurd hk (Nat.not_lt_zero _)
  | n + 1, k, hkn, hk, v => by
    have hall := h
    rw [closuresOkB, allIdx_iff] at hall
    have hk' := hall k hk
    rw [Nat.zero_add] at hk'
    have he : ir.exprs.getD k default = ir.expr k := (ir.expr_eq_getD k).symm
    rw [he, Bool.and_eq_true, List.all_eq_true] at hk'
    obtain ⟨hr, hs⟩ := hk'
    rw [sameMemB_iff] at hs
    rw [hs v, refClosure]
    simp only [List.mem_append, List.mem_flatMap]
    refine or_congr Iff.rfl (exists_congr fun k' => and_congr_right fun hk'm => ?_)
    have hlt : k' < k := by simpa using hr k' hk'm
    exact mem_get_of_closuresOk h n k' (by omega) (by omega) v

end Packed

/-! ## The annotations -/

section Ann

variable (ir : RealizedProgram)

/-- The field set of a list of values. -/
def fieldSet (vs : List ℕ) : ℕ := vs.foldl (fun s v => s ||| 1 <<< ir.valueFieldT v) 0

variable {ir}

theorem annAt_of_ok {a : ExprAnn} (h : ir.exprAnnOkB a = true) {k : ℕ} (hk : k < ir.exprs.length) :
    ir.annAtB a k (ir.expr k) = true := by
  rw [exprAnnOkB, allIdx_iff] at h
  have := h k hk
  rwa [Nat.zero_add, ← expr_eq_getD] at this

theorem refsOrdered_of_ann {a : ExprAnn} (h : ir.exprAnnOkB a = true) : ir.RefsOrdered := by
  intro k hk j hj
  have := annAt_of_ok h hk
  simp only [annAtB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
  exact this.1.1.1.1.1.1 j hj

theorem testBit_fieldSet (vs : List ℕ) (v : ℕ) (hv : v ∈ vs) :
    (ir.fieldSet vs).testBit (ir.valueFieldT v) = true := by
  unfold fieldSet
  suffices ∀ s, ((vs.foldl (fun s v => s ||| 1 <<< ir.valueFieldT v) s).testBit
      (ir.valueFieldT v) = true) from this 0
  induction vs with
  | nil => simp at hv
  | cons w vs ih =>
    intro s
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hv with rfl | hv
    · suffices ∀ (L : List ℕ) (t : ℕ), t.testBit (ir.valueFieldT v) = true →
          (L.foldl (fun s v => s ||| 1 <<< ir.valueFieldT v) t).testBit (ir.valueFieldT v) = true
        from this vs _ (by simp [Nat.one_shiftLeft])
      intro L
      induction L with
      | nil => exact fun t ht => ht
      | cons u L ih' =>
        intro t ht
        rw [List.foldl_cons]
        exact ih' _ (by simp [ht])
    · exact ih hv _

/-- **The bounds cover the values read.** -/
theorem max_rule {a : ExprAnn} (h : ir.exprAnnOkB a = true) :
    ∀ k < ir.exprs.length, (∀ x ∈ Expr.directNodes (ir.expr k), x < a.maxAt k) ∧
      ∀ j ∈ (ir.expr k).refs, ∀ x, x < a.maxAt j → x < a.maxAt k := by
  intro k hk
  have := annAt_of_ok h hk
  simp only [annAtB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1.1.1.1.2, fun j hj x hx => by
    have := this.1.1.1.1.2 j hj
    omega⟩

/-- **The field sets cover the fields of the values read in the expression's field.** -/
theorem field_rule {a : ExprAnn} (h : ir.exprAnnOkB a = true) :
    ∀ k < ir.exprs.length, (∀ x ∈ Expr.fieldNodes (ir.expr k),
      (a.fieldsAt k).testBit (ir.valueFieldT x) = true) ∧
      ∀ j ∈ (ir.expr k).refs, ∀ x, (a.fieldsAt j).testBit (ir.valueFieldT x) = true →
        (a.fieldsAt k).testBit (ir.valueFieldT x) = true := by
  intro k hk
  have := annAt_of_ok h hk
  simp only [annAtB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at this
  refine ⟨this.1.1.1.2, fun j hj x hx => ?_⟩
  have hs := this.1.1.2 j hj
  rw [← hs, Nat.testBit_and] at hx
  simp only [Bool.and_eq_true] at hx
  exact hx.2

/-- **The public mask covers the coefficient values read.** -/
theorem pub_rule {a : ExprAnn} (h : ir.exprAnnOkB a = true) :
    ∀ k < ir.exprs.length, (∀ x ∈ Expr.pubNodes (ir.expr k),
      a.pub.testBit k = true → ir.isPublicT x = true) ∧
      ∀ j ∈ (ir.expr k).refs, ∀ x, (a.pub.testBit j = true → ir.isPublicT x = true) →
        a.pub.testBit k = true → ir.isPublicT x = true := by
  intro k hk
  have := annAt_of_ok h hk
  simp only [annAtB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    at this
  refine ⟨fun x hx hb => ?_, fun j hj x hx hb => ?_⟩
  · rcases this.1.2 with hn | ⟨hc, _⟩
    · rw [hb] at hn; cases hn
    · exact hc x hx
  · rcases this.1.2 with hn | ⟨_, hr⟩
    · rw [hb] at hn; cases hn
    · exact hx (hr j hj)

/-- **The lengths are the shared expressions' lengths** (`refLen`) at every fuel above the
entry. -/
theorem refLen_eq_lenAt {a : ExprAnn} (h : ir.exprAnnOkB a = true) :
    ∀ n k, k < n → k < ir.exprs.length → ir.refLen n k = a.lenAt k
  | 0, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | n + 1, k, hkn, hk => by
    have ho := refsOrdered_of_ann h
    have hrule := annAt_of_ok h hk
    simp only [annAtB, Bool.and_eq_true, beq_iff_eq] at hrule
    rw [refLen, hrule.2, lenV_eq]
    exact Expr.len_congr ir _ fun j hj => by
      have := ho k hk j hj
      exact refLen_eq_lenAt h n j (by omega) (by omega)

/-- **The length table is the annotations' lengths.** -/
theorem lenT_eq_lenAt {a : ExprAnn} (h : ir.exprAnnOkB a = true) {k : ℕ}
    (hk : k < ir.exprs.length) : ir.lenT.getD k 0 = a.lenAt k := by
  rw [← lenT_getD (refsOrdered_of_ann h) (Nat.lt_succ_self k) hk,
    refLen_eq_lenAt h (k + 1) k (Nat.lt_succ_self k) hk]

end Ann

/-! ## The degrees and the vanishing at zero -/

section DegZero

variable (ir : RealizedProgram)

variable {ir}

theorem degZeroAt_of_ok {a : ExprAnn} (h : ir.degZeroOkB a = true) {k : ℕ}
    (hk : k < ir.exprs.length) :
    (∀ j ∈ (ir.expr k).refs, j < k) ∧ a.degAt k = (ir.expr k).deg ir.cellNdT a.degAt ∧
      a.zeroAt k = (ir.expr k).zeroAtZero a.zeroAt := by
  rw [degZeroOkB, allIdx_iff] at h
  have := h k hk
  rw [Nat.zero_add, ← expr_eq_getD] at this
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem refDeg_eq_degAt {a : ExprAnn} (h : ir.degZeroOkB a = true) :
    ∀ n k, k < n → k < ir.exprs.length → ir.refDeg ir.cellNdT n k = a.degAt k
  | 0, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | n + 1, k, hkn, hk => by
    obtain ⟨hr, hd, _⟩ := degZeroAt_of_ok h hk
    rw [refDeg, hd]
    exact Expr.deg_congr _ (fun _ _ => rfl) fun j hj => by
      have := hr j hj
      exact refDeg_eq_degAt h n j (by omega) (by omega)

theorem refZero_eq_zeroAt {a : ExprAnn} (h : ir.degZeroOkB a = true) :
    ∀ n k, k < n → k < ir.exprs.length → ir.refZero n k = a.zeroAt k
  | 0, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | n + 1, k, hkn, hk => by
    obtain ⟨hr, _, hz⟩ := degZeroAt_of_ok h hk
    rw [refZero, hz]
    exact Expr.zeroAtZero_congr _ fun j hj => by
      have := hr j hj
      exact refZero_eq_zeroAt h n j (by omega) (by omega)

theorem ordered_of_degZero {a : ExprAnn} (h : ir.degZeroOkB a = true) : ir.RefsOrdered :=
  fun k hk j hj => (degZeroAt_of_ok h hk).1 j hj

theorem degM_eq_ann {a : ExprAnn} (h : ir.degZeroOkB a = true) {e : Expr}
    (he : ∀ k ∈ e.refs, k < ir.exprs.length) :
    ir.degM ir.cellNdT e = e.deg ir.cellNdT a.degAt :=
  Expr.deg_congr e (fun _ _ => rfl) fun k hk => by
    rw [← degT_getD (ordered_of_degZero h) ir.cellNdT (Nat.lt_succ_self k) (he k hk),
      refDeg_eq_degAt h (k + 1) k (Nat.lt_succ_self k) (he k hk)]

theorem zeroM_eq_ann {a : ExprAnn} (h : ir.degZeroOkB a = true) {e : Expr}
    (he : ∀ k ∈ e.refs, k < ir.exprs.length) : ir.zeroM e = e.zeroAtZero a.zeroAt :=
  Expr.zeroAtZero_congr e fun k hk => by
    rw [← zeroT_getD (ordered_of_degZero h) (Nat.lt_succ_self k) (he k hk),
      refZero_eq_zeroAt h (k + 1) k (Nat.lt_succ_self k) (he k hk)]

/-- **A closure's test through the packed closures.** -/
theorem closAll_of_packed {c : PackedLists} (hc : ir.closuresOkB c = true) (p : ℕ → Bool)
    {e : Expr} (he : ∀ k ∈ e.refs, k < ir.exprs.length)
    (h : (e.directNodes.all p && e.refs.all fun k => (c.get k).all p) = true) :
    ir.closAll Expr.directNodes p e = true := by
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  have ho : ir.RefsOrdered := fun k hk j hj => by
    have := hc
    rw [closuresOkB, allIdx_iff] at this
    have h2 := this k hk
    rw [Nat.zero_add, ← expr_eq_getD] at h2
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h2
    exact h2.1 j hj
  rw [closAll, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun x hx => h.1 x hx, List.all_eq_true.2 fun k hk => List.all_eq_true.2 fun x hx => ?_⟩
  have hx' := (mem_closureT ho Expr.directNodes (Nat.lt_succ_self k) (he k hk) x).2 hx
  exact h.2 k hk x ((mem_get_of_closuresOk hc (k + 1) k (Nat.lt_succ_self k) (he k hk) x).1 hx')

end DegZero

/-! ## `WellFormed` through the annotations -/

section WellFormed

variable (ir : RealizedProgram) (a : ExprAnn)

/-- **`closAll Expr.fieldNodes (valueFieldT · == f)`, through the field sets.** -/
def inFieldA (f : ℕ) (e : Expr) : Bool :=
  (e.fieldNodes.all fun v => ir.valueFieldT v == f) &&
    e.refs.all fun j => a.fieldsAt j == 0 || a.fieldsAt j == 1 <<< f

/-- **`closAll Expr.pubNodes isPublicT`, through the public mask.** -/
def pubA (e : Expr) : Bool := e.pubNodes.all ir.isPublicT && e.refs.all fun j => a.pub.testBit j

/-! ### One walk for the three node tests -/

theorem all_and3 (l : List ℕ) (p q r : ℕ → Bool) :
    l.all (fun v => p v && q v && r v) = (l.all p && l.all q && l.all r) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.all_cons, ih]
    cases p x <;> cases q x <;> cases r x <;> simp

theorem all_and2 (l : List ℕ) (p r : ℕ → Bool) :
    l.all (fun v => p v && r v) = (l.all p && l.all r) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.all_cons, ih]
    cases p x <;> cases r x <;> simp

mutual

theorem Expr.walk3_eq (p q r : ℕ → Bool) : ∀ e : Expr,
    Expr.walk3 p q r e = (e.directNodes.all p && e.fieldNodes.all q && e.pubNodes.all r)
  | .leaf v => by simp [Expr.walk3, Expr.directNodes, Expr.fieldNodes, Expr.pubNodes]
  | .add e e' | .sub e e' | .mul e e' | .concat e e' => by
    simp only [Expr.walk3, Expr.directNodes, Expr.fieldNodes, Expr.pubNodes, List.all_append,
      Expr.walk3_eq p q r e, Expr.walk3_eq p q r e']
    cases e.directNodes.all p <;> cases e.fieldNodes.all q <;> cases e.pubNodes.all r <;>
      cases e'.directNodes.all p <;> cases e'.fieldNodes.all q <;> cases e'.pubNodes.all r <;> rfl
  | .scale c e => by
    simp only [Expr.walk3, Expr.directNodes, Expr.fieldNodes, Expr.pubNodes, List.all_append,
      Expr.walk3_eq p q r e, all_and3]
    cases c.nodes.all p <;> cases c.nodes.all q <;> cases c.nodes.all r <;>
      cases e.directNodes.all p <;> cases e.fieldNodes.all q <;> cases e.pubNodes.all r <;> rfl
  | .reindex _ e | .prod _ e => by
    simp only [Expr.walk3, Expr.directNodes, Expr.fieldNodes, Expr.pubNodes, Expr.walk3_eq p q r e]
  | .linear rows e => by
    simp only [Expr.walk3, Expr.directNodes, Expr.fieldNodes, Expr.pubNodes, List.all_append,
      Expr.walk3_eq p q r e, all_and3]
    generalize (rows.flatMap (·.flatMap fun t => t.2.nodes)) = L
    cases L.all p <;> cases L.all q <;> cases L.all r <;>
      cases e.directNodes.all p <;> cases e.fieldNodes.all q <;> cases e.pubNodes.all r <;> rfl
  | .mux b t e => by
    simp only [Expr.walk3, Expr.directNodes, Expr.fieldNodes, Expr.pubNodes, List.all_append,
      Expr.walk3_eq p q r b, Expr.walk3_eq p q r t, Expr.walk3_eq p q r e]
    cases b.directNodes.all p <;> cases b.fieldNodes.all q <;> cases b.pubNodes.all r <;>
      cases t.directNodes.all p <;> cases t.fieldNodes.all q <;> cases t.pubNodes.all r <;>
      cases e.directNodes.all p <;> cases e.fieldNodes.all q <;> cases e.pubNodes.all r <;> rfl
  | .apply op e => by
    simp only [Expr.walk3, Expr.directNodes, Expr.fieldNodes, Expr.pubNodes, List.all_append,
      Expr.walk3_eq p q r e, all_and3, all_and2]
    cases op.operands.all p <;> cases op.operands.all q <;> cases op.pubOperands.all r <;>
      cases op.foreignOperands.all p <;> cases op.foreignOperands.all r <;>
      cases e.directNodes.all p <;> cases e.fieldNodes.all q <;> cases e.pubNodes.all r <;> rfl
  | .ref _ => rfl
  | .logic _ _ args => by
    simp only [Expr.walk3, Expr.directNodes, Expr.fieldNodes, Expr.pubNodes,
      Expr.walk3List_eq p q r args]

theorem Expr.walk3List_eq (p q r : ℕ → Bool) : ∀ es : List Expr,
    Expr.walk3List p q r es = ((Expr.directNodesList es).all p &&
      (Expr.fieldNodesList es).all q && (Expr.pubNodesList es).all r)
  | [] => rfl
  | e :: es => by
    simp only [Expr.walk3List, Expr.directNodesList, Expr.fieldNodesList, Expr.pubNodesList,
      List.all_append, Expr.walk3_eq p q r e, Expr.walk3List_eq p q r es]
    cases e.directNodes.all p <;> cases e.fieldNodes.all q <;> cases e.pubNodes.all r <;>
      cases (Expr.directNodesList es).all p <;> cases (Expr.fieldNodesList es).all q <;>
      cases (Expr.pubNodesList es).all r <;> rfl

end

/-- **`exprOkB`, through the annotations.** -/
def exprOkA (f : ℕ) (e : Expr) : Bool :=
  e.refs.all (· < ir.exprs.length) && belowA a ir.values.length e && ir.inFieldA a f e &&
    ir.pubA a e && ir.shapeOkV a.lenAt e

variable {ir a}

theorem lenV_lenAt (h : ir.exprAnnOkB a = true) {e : Expr}
    (he : ∀ k ∈ e.refs, k < ir.exprs.length) : ir.lenV a.lenAt e = ir.lenOf e := by
  rw [lenOf, lenV_eq, lenV_eq]
  exact Expr.len_congr ir e fun k hk => (lenT_eq_lenAt h (he k hk)).symm

theorem shapeOkV_lenAt (h : ir.exprAnnOkB a = true) {e : Expr}
    (he : ∀ k ∈ e.refs, k < ir.exprs.length) :
    ir.shapeOkV a.lenAt e = ir.shapeOkV (ir.lenT.getD · 0) e := by
  rw [shapeOkV_eq, shapeOkV_eq]
  exact shapeOkWith_congr ir e fun k hk => (lenT_eq_lenAt h (he k hk)).symm

theorem closAll_below (h : ir.exprAnnOkB a = true) {b : ℕ} {e : Expr}
    (he : ∀ k ∈ e.refs, k < ir.exprs.length) (hb : belowA a b e = true) :
    ir.closAll Expr.directNodes (· < b) e = true := by
  simp only [belowA, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hb
  refine closAll_of_rule (refsOrdered_of_ann h) Expr.directNodes a.maxAt (fun m x => x < m)
    (max_rule h) _ he (List.all_eq_true.2 fun x hx => by simpa using hb.1 x hx) fun k hk x hx => ?_
  have := hb.2 k hk
  simp only [decide_eq_true_eq]
  omega

theorem closAll_inField (h : ir.exprAnnOkB a = true) {f : ℕ} {e : Expr}
    (he : ∀ k ∈ e.refs, k < ir.exprs.length) (hf : ir.inFieldA a f e = true) :
    ir.closAll Expr.fieldNodes (fun v => ir.valueFieldT v == f) e = true := by
  simp only [inFieldA, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hf
  refine closAll_of_rule (refsOrdered_of_ann h) Expr.fieldNodes a.fieldsAt
    (fun s x => s.testBit (ir.valueFieldT x) = true) (field_rule h) _ he
    (List.all_eq_true.2 fun x hx => by simpa using hf.1 x hx) fun k hk x hx => ?_
  rcases hf.2 k hk with h0 | h1
  · rw [h0, Nat.zero_testBit] at hx
    cases hx
  · rw [h1, Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_eq] at hx
    simp [hx]

theorem closAll_pub (h : ir.exprAnnOkB a = true) {e : Expr}
    (he : ∀ k ∈ e.refs, k < ir.exprs.length) (hp : ir.pubA a e = true) :
    ir.closAll Expr.pubNodes ir.isPublicT e = true := by
  simp only [pubA, Bool.and_eq_true, List.all_eq_true] at hp
  exact closAll_of_rule (refsOrdered_of_ann h) Expr.pubNodes (fun k => a.pub.testBit k)
    (fun b x => b = true → ir.isPublicT x = true) (pub_rule h) _ he
    (List.all_eq_true.2 hp.1) fun k hk x hx => hx (hp.2 k hk)

theorem all_and3' {α : Type} (l : List α) (p q r : α → Bool) :
    l.all (fun v => p v && q v && r v) = (l.all p && l.all q && l.all r) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.all_cons, ih]
    cases p x <;> cases q x <;> cases r x <;> simp

theorem exprOkF_eq (f : ℕ) (e : Expr) : ir.exprOkF a f e = ir.exprOkA a f e := by
  simp only [exprOkF, exprOkA, belowA, inFieldA, pubA, Expr.walk3_eq, all_and3']
  cases e.refs.all (· < ir.exprs.length) <;>
    cases e.directNodes.all (· < ir.values.length) <;>
    cases e.fieldNodes.all (fun v => ir.valueFieldT v == f) <;>
    cases e.pubNodes.all ir.isPublicT <;>
    cases e.refs.all (fun j => a.maxAt j ≤ ir.values.length) <;>
    cases e.refs.all (fun j => a.fieldsAt j == 0 || a.fieldsAt j == 1 <<< f) <;>
    cases e.refs.all (fun j => a.pub.testBit j) <;> cases ir.shapeOkV a.lenAt e <;> rfl

theorem exprOkB_of_A (h : ir.exprAnnOkB a = true) {f : ℕ} {e : Expr}
    (hA : ir.exprOkA a f e = true) : ir.exprOkB f e = true := by
  simp only [exprOkA, Bool.and_eq_true] at hA
  obtain ⟨⟨⟨⟨hr, hb⟩, hf⟩, hp⟩, hs⟩ := hA
  have he : ∀ k ∈ e.refs, k < ir.exprs.length := by simpa using hr
  simp only [exprOkB, Bool.and_eq_true]
  exact ⟨⟨⟨⟨hr, closAll_below h he hb⟩, closAll_inField h he hf⟩, closAll_pub h he hp⟩,
    (shapeOkV_lenAt h he) ▸ hs⟩

theorem refs_of_exprOkA {f : ℕ} {e : Expr} (hA : ir.exprOkA a f e = true) :
    ∀ k ∈ e.refs, k < ir.exprs.length := by
  simp only [exprOkA, Bool.and_eq_true] at hA
  simpa using hA.1.1.1.1

theorem kindOkB_of_A (h : ir.exprAnnOkB a = true) {v : ℕ} {k : Kind}
    (hA : ir.kindOkA a v k = true) : ir.kindOkB v k = true := by
  rcases k with _ | ⟨_ | _ | e⟩ | _ | _ | _ | _ | _ | _ | e
  all_goals first
    | exact hA
    | (simp only [kindOkA, Bool.and_eq_true] at hA
       simp only [kindOkB, Bool.and_eq_true]
       rw [exprOkF_eq] at hA
       exact ⟨exprOkB_of_A h hA.1, closAll_below h (refs_of_exprOkA hA.1) hA.2⟩)

theorem lensOkB_of_A (h : ir.exprAnnOkB a = true) {b : PredBody} (hb : ir.BodyRefsOk b)
    (hA : ir.lensOkA a b = true) : ir.lensOkB b = true := by
  cases b with
  | equal d e e' t =>
    simp only [BodyRefsOk, PredBody.exprs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    simp only [lensOkA, lensOkB] at hA ⊢
    rwa [← lenV_lenAt h hb.1, ← lenV_lenAt h hb.2]
  | mem _ _ _ _ => rfl
  | mod d q e e' r =>
    have hb1 := hb (d, e) (by simp [PredBody.exprs])
    have hb2 := hb (d, e') (by simp [PredBody.exprs])
    simp only [lensOkA, lensOkB] at hA ⊢
    rwa [← lenV_lenAt h hb1, ← lenV_lenAt h hb2]
  | cross dx x dy y k r =>
    simp only [BodyRefsOk, PredBody.exprs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    simp only [lensOkA, lensOkB] at hA ⊢
    rwa [← lenV_lenAt h hb.1, ← lenV_lenAt h hb.2]

theorem predOkB_of_A (h : ir.exprAnnOkB a = true) {b : PredBody}
    (hA : ir.predOkA a b = true) : ir.predOkB b = true := by
  simp only [predOkA, Bool.and_eq_true, List.all_eq_true, exprOkF_eq] at hA
  have hb : ir.BodyRefsOk b := fun de hde => refs_of_exprOkA (hA.1 de hde).2
  simp only [predOkB, Bool.and_eq_true, List.all_eq_true]
  exact ⟨fun de hde => ⟨(hA.1 de hde).1, exprOkB_of_A h (hA.1 de hde).2⟩,
    lensOkB_of_A h hb hA.2⟩

/-- **`wellFormedA` with checked annotations gives `wellFormedB`.** -/
theorem wellFormedB_of_ann (h : ir.exprAnnOkB a = true) (hA : ir.wellFormedA a = true) :
    ir.wellFormedB = true := by
  have ho := refsOrdered_of_ann h
  simp only [wellFormedA, Bool.and_eq_true] at hA
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h7⟩ := hA
  simp only [wellFormedB, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨(refsOrderedB_iff ir).2 ho, h1⟩, ?_⟩, ?_⟩, ?_⟩, h5⟩, h7⟩
  · rw [allIdx_iff] at h2 ⊢
    intro v hv
    have := h2 v hv
    simp only [Bool.and_eq_true] at this ⊢
    exact ⟨this.1, kindOkB_of_A h this.2⟩
  · rw [allIdx_iff] at h3 ⊢
    intro k hk
    have h3k := h3 k hk
    have hr : ∀ j ∈ (ir.exprs.getD k default).refs, j < ir.exprs.length := fun j hj => by
      have := ho k hk j (by rwa [expr_eq_getD])
      omega
    rw [← shapeOkV_lenAt h hr]
    exact h3k
  · rw [List.all_eq_true] at h4 ⊢
    exact fun p hp => predOkB_of_A h (h4 p hp)

/-- **`WellFormed`, through checked annotations** and the member checks (decided at the structure
records' pointers, `RealizedProgram.checksOk_of_memberValuesB`). -/
theorem wellFormed_of_ann (h : ir.exprAnnOkB a = true) (hA : ir.wellFormedA a = true)
    (hc : ∀ m ∈ ir.statement.checks, ir.CheckOk m) : ir.WellFormed :=
  ir.wellFormedB_iff.1 ⟨wellFormedB_of_ann h hA, hc⟩

end WellFormed

/-! ## `TargetsAdmit` through the annotations -/

section Targets

variable (ir : RealizedProgram) (a : ExprAnn) (c : PackedLists) (S : Structure)

variable {ir a c S}

/-- **The realized route admits the field equation** (`RealizedAdmits`). -/
theorem realizedAdmits_of_realizedAtS {pid d q : ℕ} {e e' : Expr}
    (h : ir.realizedAtS S pid d e e' q = true) : ir.RealizedAdmits d e e' q := by
  unfold realizedAtS at h
  split at h
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ir.realizedAdmits_of_atB h.2
  · cases h

theorem targetAdmitsB_of_A (hl : ir.exprAnnOkB a = true) (hd : ir.degZeroOkB a = true)
    (hc : ir.closuresOkB c = true) {pid d : ℕ} {e e' : Expr}
    (he : ∀ k ∈ e.refs, k < ir.exprs.length) (he' : ∀ k ∈ e'.refs, k < ir.exprs.length)
    (t : Target) (h : ir.targetAdmitsA a c S pid d e e' t = true) :
    ir.targetAdmitsB pid d e e' t = true := by
  cases t with
  | affine =>
    simp only [targetAdmitsA, targetAdmitsB] at h ⊢
    rwa [degM_eq_ann hd he, degM_eq_ann hd he']
  | quadratic => exact h
  | batch b =>
    simp only [targetAdmitsA, targetAdmitsB, batchAdmitsA, batchAdmitsB, Bool.and_eq_true] at h ⊢
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, closAll_of_packed hc _ he h3⟩, closAll_of_packed hc _ he' h4⟩, h5⟩,
      ?_⟩, ?_⟩, ?_⟩, ?_⟩, h10⟩, ?_⟩, h12⟩
    · rwa [degM_eq_ann hd he]
    · rwa [degM_eq_ann hd he']
    · rwa [zeroM_eq_ann hd he]
    · rwa [zeroM_eq_ann hd he']
    · rwa [← lenV_lenAt hl he]
  | gkr cc =>
    simp only [targetAdmitsA, targetAdmitsB, gkrAdmitsA, gkrAdmitsB, Bool.and_eq_true] at h ⊢
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    exact ⟨⟨⟨h1, h2⟩, closAll_of_packed hc _ he h3⟩, closAll_of_packed hc _ he' h4⟩
  | realized q => exact decide_eq_true (realizedAdmits_of_realizedAtS h)

theorem bodyAdmittedB_of_A (hl : ir.exprAnnOkB a = true) (hd : ir.degZeroOkB a = true)
    (hc : ir.closuresOkB c = true) {pid : ℕ} {b : PredBody} (hb : ir.BodyRefsOk b)
    (h : ir.bodyAdmittedA a c S pid b = true) : ir.bodyAdmittedB pid b = true := by
  cases b with
  | equal d e e' t =>
    simp only [BodyRefsOk, PredBody.exprs, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hb
    exact targetAdmitsB_of_A hl hd hc hb.1 hb.2 t h
  | mem _ _ _ _ => rfl
  | mod d q e e' real =>
    have hb1 := hb (d, e) (by simp [PredBody.exprs])
    have hb2 := hb (d, e') (by simp [PredBody.exprs])
    simp only [bodyAdmittedA, bodyAdmittedB, Bool.and_eq_true] at h ⊢
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    revert h2
    cases real.target with
    | none => exact fun _ => rfl
    | some t => exact fun h2 => targetAdmitsB_of_A hl hd hc hb1 hb2 t h2
  | cross _ _ _ _ _ _ => rfl

variable (S) in
/-- **`targetsB` from `targetsA`, with checked annotations and closures.** -/
theorem targetsB_of_ann (hwf : ir.WellFormed) (hl : ir.exprAnnOkB a = true)
    (hd : ir.degZeroOkB a = true) (hc : ir.closuresOkB c = true)
    (h : ir.targetsA a c S = true) : ir.targetsB = true := by
  simp only [targetsA, Bool.and_eq_true] at h
  simp only [targetsB, Bool.and_eq_true]
  refine ⟨⟨?_, h.1.2⟩, h.2⟩
  have h1 := h.1.1
  rw [allIdx_iff] at h1 ⊢
  intro pid hpid
  have := h1 pid hpid
  rw [Nat.zero_add] at this ⊢
  exact bodyAdmittedB_of_A hl hd hc (hwf.bodyRefsOk (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpid]
    exact List.getElem_mem hpid)) this

variable (S) in
/-- **`TargetsAdmit`, through checked annotations and closures.** -/
theorem targetsAdmit_of_ann (hwf : ir.WellFormed) (hl : ir.exprAnnOkB a = true)
    (hd : ir.degZeroOkB a = true) (hc : ir.closuresOkB c = true)
    (h : ir.targetsA a c S = true) : ir.TargetsAdmit :=
  (targetsB_iff hwf).1 (targetsB_of_ann S hwf hl hd hc h)

end Targets

/-! ## The degree checks through the annotations' lengths -/

section Degrees

variable (ir : RealizedProgram)

mutual

/-- **An expression's runs depend only on its shared expressions' lengths.** -/
theorem Expr.degV_congr_rl {nv rv : ℕ → RunVec} {rl rl' : ℕ → ℕ} :
    ∀ e : Expr, (∀ k ∈ e.refs, rl k = rl' k) →
      Expr.degV ir nv rv rl e = Expr.degV ir nv rv rl' e
  | .leaf _, _ | .ref _, _ => rfl
  | .add e e', h | .sub e e', h | .mul e e', h => by
    simp only [Expr.refs, List.mem_append] at h
    simp only [Expr.degV, Expr.degV_congr_rl e fun k hk => h k (.inl hk),
      Expr.degV_congr_rl e' fun k hk => h k (.inr hk)]
  | .concat e e', h => by
    simp only [Expr.refs, List.mem_append] at h
    simp only [Expr.degV, Expr.degV_congr_rl e fun k hk => h k (.inl hk),
      Expr.degV_congr_rl e' fun k hk => h k (.inr hk), lenV_eq,
      Expr.len_congr ir e fun k hk => h k (.inl hk)]
  | .scale _ e, h | .reindex _ e, h | .prod _ e, h | .linear _ e, h | .apply _ e, h => by
    simp only [Expr.refs] at h
    simp only [Expr.degV, Expr.degV_congr_rl e h]
  | .mux b t e, h => by
    simp only [Expr.refs, List.mem_append] at h
    simp only [Expr.degV, Expr.degV_congr_rl b fun k hk => h k (.inl (.inl hk)),
      Expr.degV_congr_rl t fun k hk => h k (.inl (.inr hk)),
      Expr.degV_congr_rl e fun k hk => h k (.inr hk)]
  | .logic _ _ args, h => by
    simp only [Expr.refs] at h
    simp only [Expr.degV, Expr.degVList_congr_rl args h]

theorem Expr.degVList_congr_rl {nv rv : ℕ → RunVec} {rl rl' : ℕ → ℕ} :
    ∀ es : List Expr, (∀ k ∈ Expr.refsList es, rl k = rl' k) →
      Expr.degVList ir nv rv rl es = Expr.degVList ir nv rv rl' es
  | [], _ => rfl
  | e :: es, h => by
    simp only [Expr.refsList, List.mem_append] at h
    simp only [Expr.degVList, Expr.degV_congr_rl e fun k hk => h k (.inl hk),
      Expr.degVList_congr_rl es fun k hk => h k (.inr hk)]

end

/-- **A table depends only on its steps at the list's entries.** -/
theorem memoAux_congr {γ β : Type} [Inhabited γ] {F F' : (ℕ → β) → ℕ → γ → β} {d : β} :
    ∀ (xs : List γ) (j : ℕ) (t : NatTrie β),
      (∀ i < xs.length, ∀ r, F r (j + i) (xs.getD i default) = F' r (j + i) (xs.getD i default)) →
      memoAux F d xs j t = memoAux F' d xs j t
  | [], _, _, _ => rfl
  | x :: xs, j, t, h => by
    have h0 := h 0 (by simp) (t.getD · d)
    simp only [Nat.add_zero, List.getD_cons_zero] at h0
    rw [memoAux, memoAux, h0]
    exact memoAux_congr xs (j + 1) _ fun i hi r => by
      have := h (i + 1) (by simpa using hi) r
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

theorem memo_congr {γ β : Type} [Inhabited γ] {F F' : (ℕ → β) → ℕ → γ → β} {d : β}
    {L : List γ} (h : ∀ j < L.length, ∀ r, F r j (L.getD j default) = F' r j (L.getD j default)) :
    memo F d L = memo F' d L := by
  rw [memo_eq, memo_eq]
  exact memoAux_congr L 0 .nil fun i hi r => by simpa using h i hi r

/-- `refDegVT` at the lengths `rl`. -/
def refDegVTW (rl : ℕ → ℕ) (nv : ℕ → RunVec) : NatTrie RunVec :=
  memo (fun rv _ e => Expr.degV ir nv rv rl e) default ir.exprs

/-- `degVM` at the lengths `rl`. -/
def degVMW (rl : ℕ → ℕ) (nv : ℕ → RunVec) (e : Expr) : RunVec :=
  Expr.degV ir nv ((ir.refDegVTW rl nv).getD · default) rl e

/-- `valDegStep` at the lengths `rl`. -/
def valDegStepW (rl : ℕ → ℕ) (c : ℕ) (r : ℕ → RunVec) (_ : ℕ) (x : Value) : RunVec :=
  match x.kind with
  | .pub (.expr e) => ir.degVMW rl r e
  | .challenge c' => RunVec.const (if c' = c then 1 else 0)
  | _ => RunVec.const 0

/-- `valDegT` at the lengths `rl`. -/
def valDegTW (rl : ℕ → ℕ) (c : ℕ) : NatTrie RunVec := memo (ir.valDegStepW rl c) default ir.values

/-- `valDegM` at the lengths `rl`. -/
def valDegMW (rl : ℕ → ℕ) (c v : ℕ) : RunVec := (ir.valDegTW rl c).getD v default

/-- `exprDegM` at the lengths `rl`. -/
def exprDegMW (rl : ℕ → ℕ) (c : ℕ) (b : PredBody) : ℕ :=
  (b.exprs.map fun de => (ir.degVMW rl (ir.valDegMW rl c) de.2).maxUpTo (ir.lenV rl de.2)).foldr
    max 0

/-- **`degreesAtB` at the lengths `rl`.** -/
def degreesAtW (rl : ℕ → ℕ) (c : ℕ) : Bool :=
  ir.predicates.all (fun p => ir.exprDegMW rl c p.body ≤ p.deg c) &&
    allIdx (fun v x => !x.kind.isPubExpr ||
      (ir.valDegMW rl c v).maxUpTo x.size ≤ (x.degree.lookup c).getD 0) ir.values 0

theorem degreesAtB_eq_W (c : ℕ) : ir.degreesAtB c = ir.degreesAtW (ir.lenT.getD · 0) c := rfl

variable {ir}

theorem refDegVTW_congr (ho : ir.RefsOrdered) {rl rl' : ℕ → ℕ}
    (hrl : ∀ k < ir.exprs.length, rl k = rl' k) (nv : ℕ → RunVec) :
    ir.refDegVTW rl nv = ir.refDegVTW rl' nv :=
  memo_congr fun j hj r => Expr.degV_congr_rl ir _ fun k hk => hrl k (by
    have := ho j hj k (by rwa [expr_eq_getD])
    omega)

theorem degVMW_congr (ho : ir.RefsOrdered) {rl rl' : ℕ → ℕ}
    (hrl : ∀ k < ir.exprs.length, rl k = rl' k) (nv : ℕ → RunVec) {e : Expr}
    (he : ∀ k ∈ e.refs, k < ir.exprs.length) : ir.degVMW rl nv e = ir.degVMW rl' nv e := by
  rw [degVMW, degVMW, refDegVTW_congr ho hrl nv]
  exact Expr.degV_congr_rl ir e fun k hk => hrl k (he k hk)

theorem valDegTW_congr (hwf : ir.WellFormed) {rl rl' : ℕ → ℕ}
    (hrl : ∀ k < ir.exprs.length, rl k = rl' k) (c : ℕ) : ir.valDegTW rl c = ir.valDegTW rl' c := by
  refine memo_congr fun v hv r => ?_
  have hok := (hwf.values v hv).2
  have hx : ir.values.getD v default = ir.value v := (ir.value_eq_getD v).symm
  rw [hx]
  unfold valDegStepW
  split
  · rename_i e he
    rw [he] at hok
    exact degVMW_congr hwf.refsOrdered hrl r hok.1.refs
  · rfl
  · rfl

/-- **The degree checks at two length readers agreeing on the shared expressions agree.** -/
theorem degreesAtW_congr (hwf : ir.WellFormed) {rl rl' : ℕ → ℕ}
    (hrl : ∀ k < ir.exprs.length, rl k = rl' k) (c : ℕ) :
    ir.degreesAtW rl c = ir.degreesAtW rl' c := by
  have hv : ir.valDegMW rl c = ir.valDegMW rl' c := by
    funext v
    rw [valDegMW, valDegMW, valDegTW_congr hwf hrl c]
  unfold degreesAtW
  rw [hv]
  congr 1
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  refine forall₂_congr fun p hp => ?_
  have hb := hwf.bodyRefsOk hp
  have he : ir.exprDegMW rl c p.body = ir.exprDegMW rl' c p.body := by
    unfold exprDegMW
    rw [hv]
    congr 1
    refine List.map_congr_left fun de hde => ?_
    rw [degVMW_congr hwf.refsOrdered hrl _ (hb de hde), lenV_eq, lenV_eq,
      Expr.len_congr ir _ fun k hk => hrl k (hb de hde k hk)]
  rw [he]

/-- **The degree check at a challenge, through the annotations' lengths.** -/
theorem degreesAt_of_ann (hwf : ir.WellFormed) {a : ExprAnn} (h : ir.exprAnnOkB a = true)
    {c : ℕ} (hA : ir.degreesAtW a.lenAt c = true) : ir.degreesAtB c = true := by
  rw [degreesAtB_eq_W, degreesAtW_congr hwf (rl' := a.lenAt) fun k hk => lenT_eq_lenAt h hk]
  exact hA

end Degrees

end GordieHowe.RealizedProgram
