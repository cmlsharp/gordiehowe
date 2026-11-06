-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Library.Eval
public import GordieHoweNative.Language.Library.Table

@[expose] public section

/-!
# GordieHowe frontend: the matchers of a public table's row selection

`lib/gordiehowe/lib/table.h` proves that a committed record is `M(row_i)` of a public table for
committed index bits `i` (`public_table`, `select_row`): one challenge `γ`, its powers
(`<table>.powers`: `γ^0, …, γ^(wmax−1)`, then `γ^off` per leaf at a nonzero offset), the rows'
digests against `Mᵀ g`, `g_c = γ^(e(c))` (`<table>.digests`), a multiplexer fold of the digests by
the index bits, and one equality `Σ_c rec_c γ^(e(c)) = fold(digests, i)`. The data and the
`Bool`/`Option` matchers the program facts are decided with are in
`GordieHoweNative/Language/Library/Table.lean`, so that the program check runs them compiled; this
file holds their equation lemmas and their congruence on a replica of the shared expressions, and
their soundness and the selection's theorems are `GordieHowe/Language/Library/TableSelect.lean`.

* **Row maps** (`RowLeaf`, `mapWidth`, `mapWfFrom`): a map is leaves end to end, each the identity
  or the negacyclic transform of length `n` at `ψ` in natural or scheme order (`RowMap::Leaf`);
  cell `k` of a leaf has power index `perm k` (`RowLeaf.perm`: `brv(k)` in scheme order, else `k`).
* **Symbolic powers** (`powSym`, `PowCtx`, `gatherL`): the exponent of each coordinate of an
  expression of powers of `γ` (products add, concatenations append, index maps gather), through the
  shared expressions, with the exponents of some values and of one known expression given.
* **The record's digest** (`sliceOf?`, `sumTerm?`, `recTermOk`, `recTermsOk`, `addSpine`): one sum
  `Σ_k rec[off + k] γ^(off + perm k)` per leaf (`table_internal::record_digest`).
* **The fold** (`gatherIdx?`, `foldOf?`): levels `mux(b_t, d[2j+1], d[2j])` (`table_internal::fold`).
* **The digests** (`xOk`, `leafGOk`, `gMatch`, `digTermOk`, `digTermsOk`, `digSumOk`,
  `digestsOk`): `Mᵀ g` as concatenated leaf blocks and one `rowDot` per column block, padded
  (`table_internal::digest_exprs`).
* **The shape** (`TableShape`, `TableShape.okB`, `powerExps`): the identifiers of a selection and
  its checks.
-/

namespace GordieHowe.RealizedProgram

open Export IOP
open scoped NNReal ENNReal

variable (ir : RealizedProgram)

/-! ## Named matcher equations -/

/-- Reading an explicitly given symbolic-power context. -/
theorem PowCtx.knownOf?_eq (pub : Nat → Option (List Nat))
    (known : Option (Expr × List Nat)) (E : Expr) :
    (PowCtx.mk pub known).knownOf? E = match known with
    | some (K, ks) => if E.beq K then some ks else none
    | none => none := rfl

/-- The exponent lists attached to the constant one and challenge value. -/
theorem onePub_eq (one gamma v : Nat) : onePub one gamma v =
    (if v = one then some [0] else if v = gamma then some [1] else none) := rfl


/-- A constructor equation for `powSym_leaf`, with no program-table reduction. -/
theorem powSym_leaf_eq (c : PowCtx) (n : Nat) (v : Nat) :
    ir.powSym c (n + 1) (.leaf v) =
      (match c.knownOf? (.leaf v) with
      | some ks => some ks
      | none => c.pub v) := rfl

/-- A constructor equation for `powSym_ref`, with no program-table reduction. -/
theorem powSym_ref_eq (c : PowCtx) (n : Nat) (k : Nat) :
    ir.powSym c (n + 1) (.ref k) =
      (match c.knownOf? (.ref k) with
      | some ks => some ks
      | none => ir.powSym c n (ir.expr k)) := rfl

/-- A constructor equation for `powSym_mul`, with no program-table reduction. -/
theorem powSym_mul_eq (c : PowCtx) (n : Nat) (a b : Expr) :
    ir.powSym c (n + 1) (.mul a b) =
      (match c.knownOf? (.mul a b) with
      | some ks => some ks
      | none => match ir.powSym c n a, ir.powSym c n b with
      | some x, some y => if x.length = y.length then some (List.zipWith (· + ·) x y) else none
      | _, _ => none) := rfl

/-- A constructor equation for `powSym_concat`, with no program-table reduction. -/
theorem powSym_concat_eq (c : PowCtx) (n : Nat) (a b : Expr) :
    ir.powSym c (n + 1) (.concat a b) =
      (match c.knownOf? (.concat a b) with
      | some ks => some ks
      | none => match ir.powSym c n a, ir.powSym c n b with
      | some x, some y => some (x ++ y)
      | _, _ => none) := rfl

/-- A constructor equation for `powSym_reindex`, with no program-table reduction. -/
theorem powSym_reindex_eq (c : PowCtx) (n : Nat) (m : IndexMap) (a : Expr) :
    ir.powSym c (n + 1) (.reindex m a) =
      (match c.knownOf? (.reindex m a) with
      | some ks => some ks
      | none => match ir.powSym c n a with
      | some x => gatherL x m
      | none => none) := rfl

/-- A constructor equation for `recTermsOk_nil_nil`, with no program-table reduction. -/
theorem recTermsOk_nil_nil (rec : Expr) (c : PowCtx) :
    ir.recTermsOk rec c [] [] = true := rfl
/-- A constructor equation for `recTermsOk_cons_cons`, with no program-table reduction. -/
theorem recTermsOk_cons_cons (rec : Expr) (c : PowCtx) (l : RowLeaf) (ls : List RowLeaf)
    (t : Expr) (ts : List Expr) :
    ir.recTermsOk rec c (l :: ls) (t :: ts) =
      (ir.recTermOk rec c l t && ir.recTermsOk rec c ls ts) := rfl

/-- A constructor equation for `addSpine_apply`, with no program-table reduction. -/
theorem addSpine_apply (op : NamedOp) (e : Expr) :
    addSpine (.apply op e) = [.apply op e] := rfl
/-- A constructor equation for `digG_apply_reindex`, with no program-table reduction. -/
theorem digG_apply_reindex (op : NamedOp) (m : IndexMap) (e : Expr) (es : List Expr) :
    digG (.apply op (.reindex m e) :: es) = e := rfl
/-- The constructor equation for the symbolic table matcher `sumTerm?`. -/
theorem sumTerm?_eq (rec : Expr) (c : PowCtx) (E : Expr) :
    ir.sumTerm? rec c E = match E with
  | .apply (.sum n) (.mul R P) =>
    match sliceOf? rec R, ir.powSym c powFuel P with
    | some (s, w), some ps => if w = n ∧ ps.length = n then some (s, n, ps) else none
    | _, _ => none
  | _ => none := by cases E <;> rfl

/-- The constructor equation for the symbolic table matcher `recTermOk`. -/
theorem recTermOk_eq (rec : Expr) (c : PowCtx) (l : RowLeaf) (E : Expr) :
    ir.recTermOk rec c l E = match E with
  | .mul M S =>
    l.off != 0 && decide (ir.powSym c powFuel M = some [l.off]) &&
      decide (ir.sumTerm? rec c S = some (l.off, l.n, l.permList))
  | S => l.off == 0 && decide (ir.sumTerm? rec c S = some (l.off, l.n, l.permList)) := by cases E <;> rfl

/-- The constructor equation for the symbolic table matcher `foldOf?`. -/
theorem foldOf?_eq (idx dig nd kb n : ℕ) (E : Expr) :
    ir.foldOf? idx dig nd kb n E = match n, E with
  | 0, _ => none
  | n + 1, E =>
    match E with
    | .leaf v => if v = dig then some (0, nd) else none
    | .ref j => ir.foldOf? idx dig nd kb n (ir.expr j)
    | .mux B (.reindex mh Xe) (.reindex ml Xe') =>
      if Xe.beq Xe' then
        match ir.foldOf? idx dig nd kb n Xe with
        | some (t, c2) =>
          if t < kb ∧ c2 = 2 * mh.toList.length ∧
              mh.toList = (List.range mh.toList.length).map (fun i => 2 * i + 1) ∧
              ml.toList = (List.range mh.toList.length).map (fun i => 2 * i) ∧
              gatherIdx? (.leaf idx) B = some (List.replicate mh.toList.length t) then
            some (t + 1, mh.toList.length)
          else none
        | none => none
      else none
    | _ => none := by cases n <;> rfl

/-- The constructor equation for the symbolic table matcher `xOk`. -/
theorem xOk_eq (c : PowCtx) (l : RowLeaf) (E : Expr) :
    ir.xOk c l E = match E with
  | .apply (.nttTranspose n psi) Ye =>
    l.ntt && n == l.n && psi == l.psi && decide (ir.powSym c powFuel Ye = some (List.range l.n))
  | .reindex m Ye =>
    !l.ntt && m.size == l.n && decide (ir.powSym c powFuel (.reindex m Ye) = some (List.range l.n))
  | _ => false := by cases E <;> rfl

/-- The constructor equation for the symbolic table matcher `leafGOk`. -/
theorem leafGOk_eq (c : PowCtx) (l : RowLeaf) (E : Expr) :
    ir.leafGOk c l E = match E with
  | .mul M Xe =>
    l.off != 0 && decide (ir.powSym c powFuel M = some (List.replicate l.n l.off)) &&
      ir.xOk c l Xe
  | E => l.off == 0 && ir.xOk c l E := by cases E <;> rfl

/-- The constructor equation for the symbolic table matcher `gMatch`. -/
theorem gMatch_eq (c : PowCtx) (n : ℕ) (ls : List RowLeaf) (E : Expr) :
    ir.gMatch c n ls E = match n, ls, E with
  | 0, _, _ => none
  | _ + 1, [], _ => none
  | n + 1, l :: rest, E =>
    if ir.leafGOk c l E then some rest
    else
      match E with
      | .ref j => ir.gMatch c n (l :: rest) (ir.expr j)
      | .concat a b =>
        match ir.gMatch c n (l :: rest) a with
        | some ls' => ir.gMatch c n ls' b
        | none => none
      | .reindex [(s, d, w)] e =>
        if s = 0 ∧ d = 1 then
          match ir.gMatch c n (l :: rest) e with
          | some ls' => if mapWidth (l :: rest) = w + mapWidth ls' then some ls' else none
          | none => none
        else none
      | _ => none := by cases n <;> cases ls <;> rfl

/-- The constructor equation for the symbolic table matcher `digestsOk`. -/
theorem digestsOk_eq (c : PowCtx) (m : List RowLeaf) (parts : List (ℕ × ℕ)) (rows nd : ℕ) (E : Expr) :
    ir.digestsOk c m parts rows nd E = match E with
  | .reindex pm S =>
    rows < nd && nd - rows ≤ rows && decide (pm = [(0, 1, rows), (0, 1, nd - rows)]) &&
      ir.digSumOk c m parts rows S
  | S => nd == rows && ir.digSumOk c m parts rows S := by cases E <;> rfl

/-- The digest sum separates finite term checks from the shared-expression matcher. -/
theorem digSumOk_eq (c : PowCtx) (m : List RowLeaf) (parts : List (ℕ × ℕ)) (rows : ℕ) (S : Expr) :
    ir.digSumOk c m parts rows S = (
  digTermsOk rows (digG (addSpine S)) 0 parts (addSpine S) &&
    decide (ir.gMatch c gFuel m (digG (addSpine S)) = some [])) := rfl

/-! ## The table's selection -/

namespace TableShape

variable (t : TableShape)

/-- The public context uses the named powers expression. -/
theorem pubCtx_eq : t.pubCtx ir = ⟨onePub t.one t.gamma, some (t.powExpr ir, powerExps t.map)⟩ := rfl

/-- The selection predicate context reads only its named powers value. -/
theorem predCtx_eq (t : TableShape) :
    t.predCtx = ⟨fun v => if v = t.pow then some (powerExps t.map) else none, none⟩ := rfl

/-- The selection-body equation exposes only the finite matcher inputs. -/
theorem bodyOk_eq (b : PredBody) : t.bodyOk ir b = match b with
  | .equal d (.add T (.scale (.const c) F)) (.leaf z) _ =>
    d == t.dom && c == t.mOne && z == t.zero &&
      ir.recTermsOk t.record t.predCtx t.map (addSpine T) &&
      decide (ir.foldOf? t.idx t.dig (2 ^ t.bits) t.bits (2 * t.bits + 2) F = some (t.bits, 1))
  | _ => false := by cases b <;> rfl

variable {ir t}

/-- **The powers are their expression** when value `t.pow` is a public expression. -/
theorem powKind_of_exists (h : ∃ E, (ir.value t.pow).kind = .pub (.expr E)) :
    (ir.value t.pow).kind = .pub (.expr (t.powExpr ir)) := by
  obtain ⟨E, hE⟩ := h
  simp only [powExpr, hE]

/-- **The digests are their expression** when value `t.dig` is a public expression. -/
theorem digKind_of_exists (h : ∃ E, (ir.value t.dig).kind = .pub (.expr E)) :
    (ir.value t.dig).kind = .pub (.expr (t.digExpr ir)) := by
  obtain ⟨E, hE⟩ := h
  simp only [digExpr, hE]

/-- The powers expression follows the checked public-expression body. -/
theorem powExpr_of_kind {e : Expr} (h : (ir.value t.pow).kind = .pub (.expr e)) :
    t.powExpr ir = e := by simp only [powExpr, h]

/-- The digests expression follows the checked public-expression body. -/
theorem digExpr_of_kind {e : Expr} (h : (ir.value t.dig).kind = .pub (.expr e)) :
    t.digExpr ir = e := by simp only [digExpr, h]

end TableShape

/-! ## The table's checks on a replica of the shared expressions

The checks above (`powSym`, `foldOf?`, `gMatch` and their callers) read a program only through its
shared expressions. So they compute the same result on a small program holding the entries they
reach, which the kernel evaluates without reading the rest of the program. -/

section Replica

variable {ir₁ ir₂ : RealizedProgram} {K : ℕ}

/-- **`ir₂` holds `ir₁`'s shared expressions below `K`**, and those read only entries below `K`. -/
structure AgreesBelow (ir₁ ir₂ : RealizedProgram) (K : ℕ) : Prop where
  /-- The entries below `K` agree. -/
  expr_eq : ∀ k < K, ir₁.expr k = ir₂.expr k
  /-- They read only entries below `K`. -/
  closed : ∀ k < K, ∀ k' ∈ (ir₂.expr k).refs, k' < K

/-- **The small program** holding the given shared expressions. -/
def replica (es : List Expr) : RealizedProgram :=
  { phases := 0, fields := [], domains := [], values := [], exprs := es, predicates := [] }

/-- A program whose first shared expressions are a checked table agrees with the table's replica,
where the table's entries read only table entries. -/
theorem agreesBelow_replica {es : List Expr}
    (h : ∀ j < es.length, ir₁.expr j = es.getD j default)
    (hc : ∀ k < es.length, ∀ k' ∈ (es.getD k default).refs, k' < es.length) :
    AgreesBelow ir₁ (replica es) es.length where
  expr_eq k hk := by rw [h k hk, expr_eq_getD]; rfl
  closed k hk k' hk' := hc k hk k' (by rw [expr_eq_getD] at hk'; exact hk')

variable (h : AgreesBelow ir₁ ir₂ K)
include h

theorem powSym_congr (c : PowCtx) :
    ∀ (n : ℕ) (e : Expr), (∀ k ∈ e.refs, k < K) → ir₁.powSym c n e = ir₂.powSym c n e := by
  intro n
  induction n with
  | zero => intro e _; rfl
  | succ n ih =>
    intro e he
    cases e with
    | ref k =>
      have hk := he k (by simp [Expr.refs])
      simp only [powSym]
      rw [h.expr_eq k hk, ih _ (h.closed k hk)]
    | mul a b =>
      simp only [Expr.refs, List.mem_append] at he
      simp only [powSym]
      rw [ih a fun k hk => he k (Or.inl hk), ih b fun k hk => he k (Or.inr hk)]
    | concat a b =>
      simp only [Expr.refs, List.mem_append] at he
      simp only [powSym]
      rw [ih a fun k hk => he k (Or.inl hk), ih b fun k hk => he k (Or.inr hk)]
    | reindex m a =>
      simp only [Expr.refs] at he
      simp only [powSym]
      rw [ih a he]
    | _ => simp only [powSym]

theorem foldOf_congr (idx dig nd kb : ℕ) :
    ∀ (n : ℕ) (e : Expr), (∀ k ∈ e.refs, k < K) →
      ir₁.foldOf? idx dig nd kb n e = ir₂.foldOf? idx dig nd kb n e := by
  intro n
  induction n with
  | zero => intro e _; rfl
  | succ n ih =>
    intro e he
    match e, he with
    | .ref k, he =>
      have hk := he k (by simp [Expr.refs])
      simp only [foldOf?]
      rw [h.expr_eq k hk, ih _ (h.closed k hk)]
    | .mux B (.reindex mh Xe) (.reindex ml Xe'), he =>
      simp only [Expr.refs, List.mem_append] at he
      simp only [foldOf?]
      rw [ih Xe fun k hk => he k (Or.inl (Or.inr hk))]
    | .leaf _, _ | .add _ _, _ | .sub _ _, _ | .scale _ _, _ | .mul _ _, _ | .reindex _ _, _
    | .concat _ _, _ | .linear _ _, _ | .prod _ _, _ | .apply _ _, _ | .logic _ _ _, _ =>
      simp only [foldOf?]
    | .mux _ (.leaf _) _, _ | .mux _ (.add _ _) _, _ | .mux _ (.sub _ _) _, _
    | .mux _ (.scale _ _) _, _ | .mux _ (.mul _ _) _, _ | .mux _ (.concat _ _) _, _
    | .mux _ (.linear _ _) _, _ | .mux _ (.prod _ _) _, _ | .mux _ (.mux _ _ _) _, _
    | .mux _ (.apply _ _) _, _ | .mux _ (.ref _) _, _ | .mux _ (.logic _ _ _) _, _ =>
      simp only [foldOf?]
    | .mux _ (.reindex _ _) (.leaf _), _ | .mux _ (.reindex _ _) (.add _ _), _
    | .mux _ (.reindex _ _) (.sub _ _), _ | .mux _ (.reindex _ _) (.scale _ _), _
    | .mux _ (.reindex _ _) (.mul _ _), _ | .mux _ (.reindex _ _) (.concat _ _), _
    | .mux _ (.reindex _ _) (.linear _ _), _ | .mux _ (.reindex _ _) (.prod _ _), _
    | .mux _ (.reindex _ _) (.mux _ _ _), _ | .mux _ (.reindex _ _) (.apply _ _), _
    | .mux _ (.reindex _ _) (.ref _), _ | .mux _ (.reindex _ _) (.logic _ _ _), _ =>
      simp only [foldOf?]

theorem xOk_congr (c : PowCtx) (l : RowLeaf) (e : Expr) (he : ∀ k ∈ e.refs, k < K) :
    ir₁.xOk c l e = ir₂.xOk c l e := by
  cases e with
  | apply op a =>
    cases op <;> simp only [xOk]
    all_goals rw [powSym_congr h]; exact he
  | reindex m a =>
    simp only [xOk]
    rw [powSym_congr h _ _ _ he]
  | _ => simp only [xOk]

theorem leafGOk_congr (c : PowCtx) (l : RowLeaf) (e : Expr) (he : ∀ k ∈ e.refs, k < K) :
    ir₁.leafGOk c l e = ir₂.leafGOk c l e := by
  cases e with
  | mul M Xe =>
    simp only [Expr.refs, List.mem_append] at he
    simp only [leafGOk]
    rw [powSym_congr h _ _ M fun k hk => he k (Or.inl hk), xOk_congr h _ _ Xe fun k hk => he k (Or.inr hk)]
  | _ => simp only [leafGOk]; rw [xOk_congr h _ _ _ he]

theorem gMatch_congr (c : PowCtx) :
    ∀ (n : ℕ) (ls : List RowLeaf) (e : Expr), (∀ k ∈ e.refs, k < K) →
      ir₁.gMatch c n ls e = ir₂.gMatch c n ls e := by
  intro n
  induction n with
  | zero => intro ls e _; simp only [gMatch]
  | succ n ih =>
    intro ls e he
    cases ls with
    | nil => simp only [gMatch]
    | cons l rest =>
      simp only [gMatch]
      rw [leafGOk_congr h c l e he]
      match e, he with
      | .ref k, he =>
        have hk := he k (by simp [Expr.refs])
        simp only
        rw [h.expr_eq k hk, ih _ _ (h.closed k hk)]
      | .concat a b, he =>
        simp only [Expr.refs, List.mem_append] at he
        simp only
        rw [ih _ a fun k hk => he k (Or.inl hk)]
        cases ir₂.gMatch c n (l :: rest) a with
        | none => rfl
        | some ls' => simp only [ih ls' b fun k hk => he k (Or.inr hk)]
      | .reindex [(s, d, w)] a, he =>
        simp only [Expr.refs] at he
        simp only
        rw [ih _ a he]
      | .reindex [] _, _ | .reindex (_ :: _ :: _) _, _ | .leaf _, _ | .add _ _, _ | .sub _ _, _
      | .scale _ _, _ | .mul _ _, _ | .linear _ _, _ | .prod _ _, _ | .mux _ _ _, _ | .apply _ _, _
      | .logic _ _ _, _ => rfl

omit h in
theorem addSpine_ne_nil (e : Expr) : addSpine e ≠ [] := by
  cases e <;> simp [addSpine]

omit h in
/-- The blocks the digests' first term reads are read by the digests. -/
theorem refs_digG_addSpine : ∀ (S : Expr), ∀ k ∈ (digG (addSpine S)).refs, k ∈ S.refs
  | .add a b, k, hk => by
    have hne := addSpine_ne_nil a
    have hd : digG (addSpine a ++ [b]) = digG (addSpine a) := by
      cases hl : addSpine a with
      | nil => exact absurd hl hne
      | cons x xs => cases x <;> try rfl
                     all_goals rename_i ax
                     all_goals cases ax <;> rfl
    simp only [addSpine, hd] at hk
    simp only [Expr.refs, List.mem_append]
    exact Or.inl (refs_digG_addSpine a k hk)
  | .apply _ (.reindex _ G), k, hk => by simpa [addSpine, digG, Expr.refs] using hk
  | .leaf _, _, hk | .sub _ _, _, hk | .scale _ _, _, hk | .mul _ _, _, hk | .reindex _ _, _, hk
  | .concat _ _, _, hk | .linear _ _, _, hk | .prod _ _, _, hk | .mux _ _ _, _, hk
  | .ref _, _, hk | .logic _ _ _, _, hk => by simp [addSpine, digG, Expr.refs] at hk
  | .apply _ (.leaf _), _, hk | .apply _ (.add _ _), _, hk | .apply _ (.sub _ _), _, hk
  | .apply _ (.scale _ _), _, hk | .apply _ (.mul _ _), _, hk | .apply _ (.concat _ _), _, hk
  | .apply _ (.linear _ _), _, hk | .apply _ (.prod _ _), _, hk | .apply _ (.mux _ _ _), _, hk
  | .apply _ (.apply _ _), _, hk | .apply _ (.ref _), _, hk | .apply _ (.logic _ _ _), _, hk => by
    simp [addSpine, digG, Expr.refs] at hk

theorem digSumOk_congr (c : PowCtx) (m : List RowLeaf) (parts : List (ℕ × ℕ)) (rows : ℕ) (S : Expr)
    (hS : ∀ k ∈ S.refs, k < K) : ir₁.digSumOk c m parts rows S = ir₂.digSumOk c m parts rows S := by
  simp only [digSumOk]
  rw [gMatch_congr h c _ _ _ fun k hk => hS k (refs_digG_addSpine S k hk)]

theorem sumTerm_congr (rec : Expr) (c : PowCtx) (e : Expr) (he : ∀ k ∈ e.refs, k < K) :
    ir₁.sumTerm? rec c e = ir₂.sumTerm? rec c e := by
  unfold sumTerm?
  split
  · rename_i n R P
    simp only [Expr.refs, List.mem_append] at he
    rw [powSym_congr h c _ P fun k hk => he k (Or.inr hk)]
  · rfl

theorem recTermOk_congr (rec : Expr) (c : PowCtx) (l : RowLeaf) (e : Expr)
    (he : ∀ k ∈ e.refs, k < K) : ir₁.recTermOk rec c l e = ir₂.recTermOk rec c l e := by
  cases e with
  | mul M S =>
    simp only [Expr.refs, List.mem_append] at he
    simp only [recTermOk]
    rw [powSym_congr h c _ M fun k hk => he k (Or.inl hk),
      sumTerm_congr h rec c S fun k hk => he k (Or.inr hk)]
  | _ => simp only [recTermOk]; rw [sumTerm_congr h rec c _ he]

theorem recTermsOk_congr (rec : Expr) (c : PowCtx) :
    ∀ (ls : List RowLeaf) (ts : List Expr), (∀ t ∈ ts, ∀ k ∈ t.refs, k < K) →
      ir₁.recTermsOk rec c ls ts = ir₂.recTermsOk rec c ls ts
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | l :: ls, t :: ts, ht => by
    simp only [recTermsOk]
    rw [recTermOk_congr h rec c l t (ht t (by simp)),
      recTermsOk_congr rec c ls ts fun t' ht' => ht t' (by simp [ht'])]

omit h in
theorem refs_of_mem_addSpine : ∀ (T t : Expr), t ∈ addSpine T → ∀ k ∈ t.refs, k ∈ T.refs
  | .add a b, t, ht, k, hk => by
    simp only [addSpine, List.mem_append, List.mem_singleton] at ht
    simp only [Expr.refs, List.mem_append]
    rcases ht with ht | rfl
    · exact Or.inl (refs_of_mem_addSpine a t ht k hk)
    · exact Or.inr hk
  | .leaf _, t, ht, k, hk | .sub _ _, t, ht, k, hk | .scale _ _, t, ht, k, hk | .mul _ _, t, ht, k, hk
  | .reindex _ _, t, ht, k, hk | .concat _ _, t, ht, k, hk | .linear _ _, t, ht, k, hk
  | .prod _ _, t, ht, k, hk | .mux _ _ _, t, ht, k, hk | .apply _ _, t, ht, k, hk
  | .ref _, t, ht, k, hk | .logic _ _ _, t, ht, k, hk => by
    simp only [addSpine, List.mem_singleton] at ht
    subst ht
    exact hk

end Replica

end GordieHowe.RealizedProgram
