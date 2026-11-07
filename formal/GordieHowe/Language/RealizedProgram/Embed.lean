-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Library.Eval
public import GordieHowe.Language.RealizedProgram.Interval
public import GordieHowe.Language.RealizedProgram.Affine
public import GordieHowe.Language.RealizedProgram.Source
public import GordieHoweNative.Language.RealizedProgram.Embed

@[expose] public section

/-!
# GordieHowe: programs that share a part up to a renaming

Two realized programs of one interpretation can hold one part (a set of values, shared
expressions and predicates) up to a renaming of the value, shared-expression and challenge
identifiers: the emulated ML-DSA program at the ROM parameters holds the native one's domain `H`
with every value identifier one larger and every shared-expression identifier two larger (export
`c825eb05`), and the ML-DSA ring programs hold parts of the ML-DSA programs with every challenge
identifier one larger. This file transports that part's semantics:

* **the renaming** (`Renaming`, `Renaming.expr`, `Renaming.kind?`) of an expression's leaves,
  coefficients and references and of a value's kind;
* **expressions** (`Renaming.len_expr`, `Renaming.eval_expr`, `Renaming.evalInt_expr`): a renamed
  expression has the original's length and value, in the field and on the integers, where the
  renamed values have the originals' sizes and readings, for an expression whose named operators
  read no value (`Expr.opsFree`, `NamedOp.valueFree`);
* **the embedding** (`GordieHowe.RealizedProgram.Embedding`, decided per program pair): the values `V` and shared
  expressions `R` of the part, renamed, with their kinds, sizes, fields and types, closed under
  what they read;
* **environments** (`GordieHowe.RealizedProgram.pullEnv`): an environment of the larger program read as one of the
  smaller, through the renaming, `0` outside `V`; the readers agree on `V` (`reader_pullEnv`),
  as do the integer readings (`intOf_pullEnv`) and the shared expressions on `R`, and a renamed
  predicate `equal` holds in one exactly when it holds in the other (`holdsAt_pullEnv`), as does
  a renamed range `in` or `mod_q` (`bodyCorrB`, `holdsAt_pullEnv_body`).

The values a program reads must be read in identifier order (`GordieHowe.RealizedProgram.ValuesOrdered`), so a
value's reading does not depend on the fuel past its identifier.
-/

namespace GordieHowe.RealizedProgram

/-! ## Operators that read no value -/

theorem NamedOp.cols_of_valueFree {ir ir' : RealizedProgram} :
    ∀ {op : NamedOp}, op.valueFree = true → NamedOp.cols ir op = NamedOp.cols ir' op
  | .ntt _ _ _, _ | .inverseNtt _ _, _ | .nttTranspose _ _, _ | .sum _, _
  | .fromDigits _ _, _ => rfl
  | .batched b op, h => by
    simp only [NamedOp.cols, NamedOp.cols_of_valueFree (ir := ir) (ir' := ir') (op := op) h]

theorem NamedOp.rows_of_valueFree {ir ir' : RealizedProgram} :
    ∀ {op : NamedOp}, op.valueFree = true → NamedOp.rows ir op = NamedOp.rows ir' op
  | .ntt _ _ _, _ | .inverseNtt _ _, _ | .nttTranspose _ _, _ | .sum _, _
  | .fromDigits _ _, _ => rfl
  | .batched b op, h => by
    simp only [NamedOp.rows, NamedOp.rows_of_valueFree (ir := ir) (ir' := ir') (op := op) h]

theorem NamedOp.block_of_valueFree {ir ir' : RealizedProgram} {I : Interp} {f : ℕ}
    {leaf : ir.Valuation I} {leaf' : ir'.Valuation I} :
    ∀ {op : NamedOp}, op.valueFree = true →
      NamedOp.block ir f leaf op = NamedOp.block ir' f leaf' op
  | .ntt _ _ o, _ => by cases o <;> rfl
  | .inverseNtt _ _, _ | .nttTranspose _ _, _ | .sum _, _ | .fromDigits _ _, _ => rfl
  | .batched b op, h => by
    funext x j
    simp only [NamedOp.block, NamedOp.rows_of_valueFree (ir := ir) (ir' := ir') (op := op) h,
      NamedOp.cols_of_valueFree (ir := ir) (ir' := ir') (op := op) h,
      NamedOp.block_of_valueFree (leaf := leaf) (leaf' := leaf') (op := op) h]

/-! ## The renaming -/

namespace Renaming

variable (σ : Renaming)

/-- Renaming a private value preserves its private kind. -/
theorem kindCorr_priv {k : Kind} (h : σ.kindCorr .priv k = true) : k = .priv := by
  cases k <;> simp_all [kindCorr, kind?]

/-! ## Renamed expressions -/

section Expr

variable {ir ir' : RealizedProgram} {I : Interp}

mutual

theorem len_expr {rl rl' : ℕ → ℕ} : ∀ (e : Expr), e.opsFree = true →
    (∀ v ∈ e.directNodes, (ir'.value (σ.val v)).size = (ir.value v).size) →
    (∀ k ∈ e.refs, rl' (σ.ref k) = rl k) →
    Expr.len ir' rl' (σ.expr e) = Expr.len ir rl e
  | .leaf v, _, hs, _ => by
    simp only [expr, Expr.len]
    exact hs v (by simp [Expr.directNodes])
  | .add e e', ho, hs, hr | .sub e e', ho, hs, hr | .mul e e', ho, hs, hr => by
    simp only [Expr.opsFree, Bool.and_eq_true] at ho
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at hs hr
    simp only [expr, Expr.len]
    exact len_expr e ho.1 (fun v hv => hs v (.inl hv)) fun k hk => hr k (.inl hk)
  | .concat e e', ho, hs, hr => by
    simp only [Expr.opsFree, Bool.and_eq_true] at ho
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at hs hr
    simp only [expr, Expr.len]
    rw [len_expr e ho.1 (fun v hv => hs v (.inl hv)) fun k hk => hr k (.inl hk),
      len_expr e' ho.2 (fun v hv => hs v (.inr hv)) fun k hk => hr k (.inr hk)]
  | .scale c e, ho, hs, hr => by
    simp only [Expr.opsFree] at ho
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at hs hr
    simp only [expr, Expr.len]
    exact len_expr e ho (fun v hv => hs v (.inr hv)) hr
  | .prod n e, ho, hs, hr => by
    simp only [Expr.opsFree] at ho
    simp only [Expr.directNodes, Expr.refs] at hs hr
    simp only [expr, Expr.len]
    rw [len_expr e ho hs hr]
  | .reindex _ _, _, _, _ => rfl
  | .linear rows _, _, _, _ => by simp [expr, Expr.len]
  | .mux b t e, ho, hs, hr => by
    simp only [Expr.opsFree, Bool.and_eq_true] at ho
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at hs hr
    simp only [expr, Expr.len]
    exact len_expr t ho.1.2 (fun v hv => hs v (.inl (.inr hv))) fun k hk => hr k (.inl (.inr hk))
  | .apply op e, ho, hs, hr => by
    simp only [Expr.opsFree, Bool.and_eq_true] at ho
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at hs hr
    simp only [expr, Expr.len]
    rw [len_expr e ho.2 (fun v hv => hs v (.inr hv)) hr,
      NamedOp.cols_of_valueFree (ir := ir') (ir' := ir) ho.1,
      NamedOp.rows_of_valueFree (ir := ir') (ir' := ir) ho.1]
  | .ref k, _, _, hr => by
    simp only [expr, Expr.len]
    exact hr k (by simp [Expr.refs])
  | .logic _ w args, ho, hs, hr => by
    simp only [Expr.opsFree] at ho
    simp only [Expr.directNodes, Expr.refs] at hs hr
    simp only [expr, Expr.len]
    rw [lenList_exprs args ho hs hr]

theorem lenList_exprs {rl rl' : ℕ → ℕ} : ∀ (es : List Expr), Expr.opsFreeList es = true →
    (∀ v ∈ Expr.directNodesList es, (ir'.value (σ.val v)).size = (ir.value v).size) →
    (∀ k ∈ Expr.refsList es, rl' (σ.ref k) = rl k) →
    Expr.lenList ir' rl' (σ.exprs es) = Expr.lenList ir rl es
  | [], _, _, _ => rfl
  | e :: es, ho, hs, hr => by
    simp only [Expr.opsFreeList, Bool.and_eq_true] at ho
    simp only [Expr.directNodesList, Expr.refsList, List.mem_append] at hs hr
    simp only [exprs, Expr.lenList]
    rw [len_expr e ho.1 (fun v hv => hs v (.inl hv)) (fun k hk => hr k (.inl hk)),
      lenList_exprs es ho.2 (fun v hv => hs v (.inr hv)) fun k hk => hr k (.inr hk)]

end

theorem coef_eval {f : ℕ} {leaf : ir.Valuation I} {leaf' : ir'.Valuation I} {c : Coef}
    (hl : ∀ v ∈ c.nodes, ∀ i, (castElt (leaf' (σ.val v) i) : (I f).K) = castElt (leaf v i)) :
    Coef.eval ir' f leaf' (σ.coef c) = Coef.eval ir f leaf c := by
  cases c with
  | const => rfl
  | node v i => exact hl v (by simp [Coef.nodes]) i

mutual

theorem eval_expr {f : ℕ} {leaf : ir.Valuation I} {leaf' : ir'.Valuation I}
    {ref ref' : ℕ → ℕ → (I f).K} {rl rl' : ℕ → ℕ} : ∀ (e : Expr), e.opsFree = true →
    (∀ v ∈ e.directNodes, (ir'.value (σ.val v)).size = (ir.value v).size ∧
      ∀ i, (castElt (leaf' (σ.val v) i) : (I f).K) = castElt (leaf v i)) →
    (∀ k ∈ e.refs, rl' (σ.ref k) = rl k ∧ ref' (σ.ref k) = ref k) →
    Expr.eval ir' f leaf' ref' rl' (σ.expr e) = Expr.eval ir f leaf ref rl e
  | .leaf v, _, hs, _ => by
    funext i
    exact (hs v (by simp [Expr.directNodes])).2 i
  | .add e e', ho, hs, hr | .sub e e', ho, hs, hr | .mul e e', ho, hs, hr => by
    simp only [Expr.opsFree, Bool.and_eq_true] at ho
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at hs hr
    funext i
    simp only [expr, Expr.eval,
      eval_expr e ho.1 (fun v hv => hs v (.inl hv)) fun k hk => hr k (.inl hk),
      eval_expr e' ho.2 (fun v hv => hs v (.inr hv)) fun k hk => hr k (.inr hk)]
  | .concat e e', ho, hs, hr => by
    simp only [Expr.opsFree, Bool.and_eq_true] at ho
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at hs hr
    funext i
    simp only [expr, Expr.eval,
      eval_expr e ho.1 (fun v hv => hs v (.inl hv)) fun k hk => hr k (.inl hk),
      eval_expr e' ho.2 (fun v hv => hs v (.inr hv)) fun k hk => hr k (.inr hk),
      len_expr σ e ho.1 (fun v hv => (hs v (.inl hv)).1) fun k hk => (hr k (.inl hk)).1]
  | .scale c e, ho, hs, hr => by
    simp only [Expr.opsFree] at ho
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at hs hr
    funext i
    simp only [expr, Expr.eval, eval_expr e ho (fun v hv => hs v (.inr hv)) hr,
      coef_eval σ fun v hv => (hs v (.inl hv)).2]
  | .reindex idx e, ho, hs, hr => by
    simp only [Expr.opsFree] at ho
    simp only [Expr.directNodes, Expr.refs] at hs hr
    funext i
    simp only [expr, Expr.eval, eval_expr e ho hs hr]
  | .prod n e, ho, hs, hr => by
    simp only [Expr.opsFree] at ho
    simp only [Expr.directNodes, Expr.refs] at hs hr
    funext i
    simp only [expr, Expr.eval, eval_expr e ho hs hr]
  | .linear rows e, ho, hs, hr => by
    simp only [Expr.opsFree] at ho
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at hs hr
    funext i
    simp only [expr, Expr.eval, eval_expr e ho (fun v hv => hs v (.inr hv)) hr]
    rw [show (rows.map (·.map fun t => (t.1, σ.coef t.2))).getD i [] =
        (rows.getD i []).map (fun t => (t.1, σ.coef t.2)) by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases rows[i]? <;> rfl, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    simp only [Function.comp]
    rw [coef_eval σ fun v hv => (hs v (.inl (mem_rowNodes_of_mem_getD ht hv))).2]
  | .mux b t e, ho, hs, hr => by
    simp only [Expr.opsFree, Bool.and_eq_true] at ho
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at hs hr
    funext i
    simp only [expr, Expr.eval,
      eval_expr b ho.1.1 (fun v hv => hs v (.inl (.inl hv))) fun k hk => hr k (.inl (.inl hk)),
      eval_expr t ho.1.2 (fun v hv => hs v (.inl (.inr hv))) fun k hk => hr k (.inl (.inr hk)),
      eval_expr e ho.2 (fun v hv => hs v (.inr hv)) fun k hk => hr k (.inr hk)]
  | .apply op e, ho, hs, hr => by
    simp only [Expr.opsFree, Bool.and_eq_true] at ho
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at hs hr
    funext i
    simp only [expr, Expr.eval, NamedOp.apply, eval_expr e ho.2 (fun v hv => hs v (.inr hv)) hr,
      NamedOp.cols_of_valueFree (ir := ir') (ir' := ir) ho.1,
      NamedOp.rows_of_valueFree (ir := ir') (ir' := ir) ho.1,
      NamedOp.block_of_valueFree (leaf := leaf') (leaf' := leaf) ho.1]
  | .ref k, _, _, hr => by
    funext i
    simp only [expr, Expr.eval, (hr k (by simp [Expr.refs])).2]
  | .logic op w args, ho, hs, hr => by
    simp only [Expr.opsFree] at ho
    simp only [Expr.directNodes, Expr.refs] at hs hr
    funext i
    simp only [expr, Expr.eval, evalList_exprs args ho hs hr]

theorem evalList_exprs {f : ℕ} {leaf : ir.Valuation I} {leaf' : ir'.Valuation I}
    {ref ref' : ℕ → ℕ → (I f).K} {rl rl' : ℕ → ℕ} : ∀ (es : List Expr),
    Expr.opsFreeList es = true →
    (∀ v ∈ Expr.directNodesList es, (ir'.value (σ.val v)).size = (ir.value v).size ∧
      ∀ i, (castElt (leaf' (σ.val v) i) : (I f).K) = castElt (leaf v i)) →
    (∀ k ∈ Expr.refsList es, rl' (σ.ref k) = rl k ∧ ref' (σ.ref k) = ref k) →
    Expr.evalList ir' f leaf' ref' rl' (σ.exprs es) = Expr.evalList ir f leaf ref rl es
  | [], _, _, _ => rfl
  | e :: es, ho, hs, hr => by
    simp only [Expr.opsFreeList, Bool.and_eq_true] at ho
    simp only [Expr.directNodesList, Expr.refsList, List.mem_append] at hs hr
    simp only [exprs, Expr.evalList,
      eval_expr e ho.1 (fun v hv => hs v (.inl hv)) (fun k hk => hr k (.inl hk)),
      evalList_exprs es ho.2 (fun v hv => hs v (.inr hv)) fun k hk => hr k (.inr hk)]

end

/-- **A coefficient's integer value renamed** is the original's, where the renamed values have the
originals' integer readings. -/
theorem coef_evalInt {f : ℕ} {il il' : ℕ → ℕ → ℤ} {c : Coef}
    (hl : ∀ v ∈ c.nodes, ∀ i, il' (σ.val v) i = il v i) :
    Coef.evalInt (I := I) f il' (σ.coef c) = Coef.evalInt (I := I) f il c := by
  cases c with
  | const => rfl
  | node v i => exact hl v (by simp [Coef.nodes]) i

/-- **A named operator that reads no value has the same integer form in every program.** -/
theorem applyInt_of_valueFree {f : ℕ} {leaf : ir.Valuation I} {leaf' : ir'.Valuation I}
    {op : NamedOp} (h : op.valueFree = true) :
    NamedOp.applyInt ir' f leaf' op = NamedOp.applyInt ir f leaf op := by
  funext x j
  unfold NamedOp.applyInt
  rw [NamedOp.block_of_valueFree (leaf := leaf') (leaf' := leaf) h,
    NamedOp.rows_of_valueFree (ir := ir') (ir' := ir) h,
    NamedOp.cols_of_valueFree (ir := ir') (ir' := ir) h]

mutual

/-- **A renamed expression has the original's integer value**, where the renamed values have the
originals' sizes and integer readings and the renamed shared expressions the originals' lengths
and integer values, for an expression whose named operators read no value. -/
theorem evalInt_expr {f : ℕ} {leaf : ir.Valuation I} {leaf' : ir'.Valuation I}
    {il il' : ℕ → ℕ → ℤ} {iref iref' : ℕ → ℕ → ℤ} {rl rl' : ℕ → ℕ} : ∀ (e : Expr),
    e.opsFree = true →
    (∀ v ∈ e.directNodes, (ir'.value (σ.val v)).size = (ir.value v).size ∧
      ∀ i, il' (σ.val v) i = il v i) →
    (∀ k ∈ e.refs, rl' (σ.ref k) = rl k ∧ iref' (σ.ref k) = iref k) →
    Expr.evalInt ir' f leaf' il' iref' rl' (σ.expr e) = Expr.evalInt ir f leaf il iref rl e
  | .leaf v, _, hs, _ => by
    funext i
    exact (hs v (by simp [Expr.directNodes])).2 i
  | .add e e', ho, hs, hr | .sub e e', ho, hs, hr | .mul e e', ho, hs, hr => by
    simp only [Expr.opsFree, Bool.and_eq_true] at ho
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at hs hr
    funext i
    simp only [expr, Expr.evalInt,
      evalInt_expr (leaf := leaf) (leaf' := leaf')
        e ho.1 (fun v hv => hs v (.inl hv)) fun k hk => hr k (.inl hk),
      evalInt_expr (leaf := leaf) (leaf' := leaf')
        e' ho.2 (fun v hv => hs v (.inr hv)) fun k hk => hr k (.inr hk)]
  | .concat e e', ho, hs, hr => by
    simp only [Expr.opsFree, Bool.and_eq_true] at ho
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at hs hr
    funext i
    simp only [expr, Expr.evalInt,
      evalInt_expr (leaf := leaf) (leaf' := leaf')
        e ho.1 (fun v hv => hs v (.inl hv)) fun k hk => hr k (.inl hk),
      evalInt_expr (leaf := leaf) (leaf' := leaf')
        e' ho.2 (fun v hv => hs v (.inr hv)) fun k hk => hr k (.inr hk),
      len_expr σ e ho.1 (fun v hv => (hs v (.inl hv)).1) fun k hk => (hr k (.inl hk)).1]
  | .scale c e, ho, hs, hr => by
    simp only [Expr.opsFree] at ho
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at hs hr
    funext i
    simp only [expr, Expr.evalInt, evalInt_expr (leaf := leaf) (leaf' := leaf')
                            e ho (fun v hv => hs v (.inr hv)) hr,
      coef_evalInt σ fun v hv => (hs v (.inl hv)).2]
  | .reindex idx e, ho, hs, hr => by
    simp only [Expr.opsFree] at ho
    simp only [Expr.directNodes, Expr.refs] at hs hr
    funext i
    simp only [expr, Expr.evalInt, evalInt_expr (leaf := leaf) (leaf' := leaf') e ho hs hr]
  | .prod n e, ho, hs, hr => by
    simp only [Expr.opsFree] at ho
    simp only [Expr.directNodes, Expr.refs] at hs hr
    funext i
    simp only [expr, Expr.evalInt, evalInt_expr (leaf := leaf) (leaf' := leaf') e ho hs hr]
  | .linear rows e, ho, hs, hr => by
    simp only [Expr.opsFree] at ho
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at hs hr
    funext i
    simp only [expr, Expr.evalInt, evalInt_expr (leaf := leaf) (leaf' := leaf')
                            e ho (fun v hv => hs v (.inr hv)) hr]
    rw [show (rows.map (·.map fun t => (t.1, σ.coef t.2))).getD i [] =
        (rows.getD i []).map (fun t => (t.1, σ.coef t.2)) by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases rows[i]? <;> rfl, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    simp only [Function.comp]
    rw [coef_evalInt σ fun v hv => (hs v (.inl (mem_rowNodes_of_mem_getD ht hv))).2]
  | .mux b t e, ho, hs, hr => by
    simp only [Expr.opsFree, Bool.and_eq_true] at ho
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at hs hr
    funext i
    simp only [expr, Expr.evalInt,
      evalInt_expr (leaf := leaf) (leaf' := leaf')
        b ho.1.1 (fun v hv => hs v (.inl (.inl hv))) fun k hk => hr k (.inl (.inl hk)),
      evalInt_expr (leaf := leaf) (leaf' := leaf')
        t ho.1.2 (fun v hv => hs v (.inl (.inr hv))) fun k hk => hr k (.inl (.inr hk)),
      evalInt_expr (leaf := leaf) (leaf' := leaf')
        e ho.2 (fun v hv => hs v (.inr hv)) fun k hk => hr k (.inr hk)]
  | .apply op e, ho, hs, hr => by
    simp only [Expr.opsFree, Bool.and_eq_true] at ho
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at hs hr
    funext i
    simp only [expr, Expr.evalInt, evalInt_expr (leaf := leaf) (leaf' := leaf')
                            e ho.2 (fun v hv => hs v (.inr hv)) hr,
      applyInt_of_valueFree (leaf := leaf) (leaf' := leaf') ho.1]
  | .ref k, _, _, hr => by
    funext i
    simp only [expr, Expr.evalInt, (hr k (by simp [Expr.refs])).2]
  | .logic op w args, ho, hs, hr => by
    simp only [Expr.opsFree] at ho
    simp only [Expr.directNodes, Expr.refs] at hs hr
    funext i
    simp only [expr, Expr.evalInt, evalIntList_exprs (leaf := leaf) (leaf' := leaf') args ho hs hr]

theorem evalIntList_exprs {f : ℕ} {leaf : ir.Valuation I} {leaf' : ir'.Valuation I}
    {il il' : ℕ → ℕ → ℤ} {iref iref' : ℕ → ℕ → ℤ} {rl rl' : ℕ → ℕ} : ∀ (es : List Expr),
    Expr.opsFreeList es = true →
    (∀ v ∈ Expr.directNodesList es, (ir'.value (σ.val v)).size = (ir.value v).size ∧
      ∀ i, il' (σ.val v) i = il v i) →
    (∀ k ∈ Expr.refsList es, rl' (σ.ref k) = rl k ∧ iref' (σ.ref k) = iref k) →
    Expr.evalIntList ir' f leaf' il' iref' rl' (σ.exprs es) =
      Expr.evalIntList ir f leaf il iref rl es
  | [], _, _, _ => rfl
  | e :: es, ho, hs, hr => by
    simp only [Expr.opsFreeList, Bool.and_eq_true] at ho
    simp only [Expr.directNodesList, Expr.refsList, List.mem_append] at hs hr
    simp only [exprs, Expr.evalIntList,
      evalInt_expr (leaf := leaf) (leaf' := leaf')
        e ho.1 (fun v hv => hs v (.inl hv)) (fun k hk => hr k (.inl hk)),
      evalIntList_exprs (leaf := leaf) (leaf' := leaf')
        es ho.2 (fun v hv => hs v (.inr hv)) fun k hk => hr k (.inr hk)]

end

/-- **A list of expressions renamed** is the list of the renamed expressions. -/
theorem exprs_eq_map : ∀ es : List Expr, σ.exprs es = es.map σ.expr
  | [] => rfl
  | e :: es => by rw [exprs, exprs_eq_map es, List.map_cons]

mutual

theorem mem_refs_expr {k : ℕ} : ∀ {e : Expr}, k ∈ e.refs → σ.ref k ∈ (σ.expr e).refs
  | .leaf _, h => by simp [Expr.refs] at h
  | .add e e', h | .sub e e', h | .mul e e', h | .concat e e', h => by
    simp only [Expr.refs, List.mem_append] at h
    simp only [expr, Expr.refs, List.mem_append]
    exact h.imp mem_refs_expr mem_refs_expr
  | .scale _ e, h | .reindex _ e, h | .linear _ e, h | .prod _ e, h | .apply _ e, h => by
    simp only [Expr.refs] at h
    simp only [expr, Expr.refs]
    exact mem_refs_expr h
  | .mux b t e, h => by
    simp only [Expr.refs, List.mem_append] at h
    simp only [expr, Expr.refs, List.mem_append]
    exact h.imp (fun h => h.imp mem_refs_expr mem_refs_expr) mem_refs_expr
  | .ref k', h => by
    simp only [Expr.refs, List.mem_singleton] at h
    subst h
    simp [expr, Expr.refs]
  | .logic _ _ args, h => by
    simp only [Expr.refs] at h
    simp only [expr, Expr.refs]
    exact mem_refsList_exprs h

theorem mem_refsList_exprs {k : ℕ} : ∀ {es : List Expr}, k ∈ Expr.refsList es →
    σ.ref k ∈ Expr.refsList (σ.exprs es)
  | [], h => by simp [Expr.refsList] at h
  | e :: es, h => by
    simp only [Expr.refsList, List.mem_append] at h
    simp only [exprs, Expr.refsList, List.mem_append]
    exact h.imp mem_refs_expr mem_refsList_exprs

end

end Expr

end Renaming

/-! ## Casts between equal field identifiers -/

section Casts

variable {I : Interp}

theorem castElt_ofBool_of_eq {a b : ℕ} (h : a = b) (c : Bool) :
    (castElt ((I a).ofBool c) : (I b).K) = (I b).ofBool c := by
  subst h
  exact castElt_self _

theorem coord_castElt_of_eq {a b : ℕ} (h : a = b) (E : String) (x : (I a).K) (j : ℕ) :
    (I b).coord E (castElt x : (I b).K) j = (I a).coord E x j := by
  subst h
  rw [castElt_self]

theorem inType_castElt_of_eq {a b : ℕ} (h : a = b) (t : VType) {x : (I a).K}
    (hx : (I a).InType t x) : (I b).InType t (castElt x : (I b).K) := by
  subst h
  rwa [castElt_self]

end Casts

/-! ## Values read in identifier order -/

section

variable {ir ir' : RealizedProgram} {I : Interp}

variable (ir) in
/-- **The values read values of smaller identifiers** (`RealizedProgram.valueDeps`), so a value's reading
is fixed once the fuel passes its identifier (`read_stable`). -/
def ValuesOrdered : Prop := ∀ v < ir.values.length, ∀ u ∈ ir.valueDeps v, u < v

instance : Decidable ir.ValuesOrdered := by unfold ValuesOrdered; infer_instance

/-- **One more level of fuel does not change a value's reading** past its identifier. -/
theorem read_succ (ho : ir.ValuesOrdered) (e : ir.Env I) :
    ∀ n v, v < ir.values.length → v < n → ir.read e (n + 1) v = ir.read e n v
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, v, hv, _ => by
    funext i
    have hdep := ho v hv
    rw [read.eq_2 ir e v i (m + 1), read.eq_2 ir e v i m]
    rcases hk : (ir.value v).kind with _ | ⟨_ | ⟨name, args⟩ | x⟩ | es | c | _ | ⟨w, sel⟩ |
      ⟨u, mp⟩ | u | x <;> simp only [valueDeps, hk] at hdep <;> simp only
    · split_ifs
      · rfl
      · have hargs : args.map (fun u j => (I (ir.valueField u)).toNat (ir.read e (m + 1) u j)) =
            args.map (fun u j => (I (ir.valueField u)).toNat (ir.read e m u j)) :=
          List.map_congr_left fun u hu => by
            have := hdep u hu
            rw [read_succ ho e m u (by omega) (by omega)]
        rw [hargs]
    · exact congrFun (evalE_congr fun u hu => by
        have := hdep u hu
        exact read_succ ho e m u (by omega) (by omega)) i
    · have := hdep w (List.mem_singleton_self _)
      simp only [bitView, read_succ ho e m w (by omega) (by omega)]

/-- **A value's reading does not depend on the fuel** past its identifier. -/
theorem read_stable (ho : ir.ValuesOrdered) (e : ir.Env I) {v : ℕ} (hv : v < ir.values.length) :
    ∀ {n m}, v < n → n ≤ m → ir.read e m v = ir.read e n v
  | n, m, hn, hm => by
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih => rw [read_succ ho e m v hv (by omega), ih]

/-- **The reader is the reading at any fuel past the identifier.** -/
theorem reader_eq_read (ho : ir.ValuesOrdered) (e : ir.Env I) {v : ℕ} (hv : v < ir.values.length)
    {n : ℕ} (hn : ir.fuel ≤ n) : ir.reader e v = ir.read e n v :=
  (read_stable ho e hv (by simp only [fuel]; omega) hn).symm

/-! ## The embedding -/

variable (ir ir') in
/-- **Program `ir`'s values `V` and shared expressions `R` are held by `ir'` up to the renaming
`σ`**: both programs read their values in identifier order and their shared expressions read
earlier entries; every value of `V` is renamed to a value of `ir'` of the same field, size, type
and phase, of the renamed kind (`Renaming.kindCorr`), reading only values of `V`; a challenge
value's challenge and its renamed challenge have the same field; every shared expression of `R`
is renamed to `ir'`'s entry, reads only values of `V` and entries of `R`, and has no named
operator reading a value. -/
structure Embedding (σ : Renaming) (V R : List ℕ) : Prop where
  /-- `ir` reads its values in identifier order. -/
  ordered : ir.ValuesOrdered
  /-- `ir'` reads its values in identifier order. -/
  ordered' : ir'.ValuesOrdered
  /-- `ir`'s shared expressions read earlier entries. -/
  refsOrdered : ir.RefsOrdered
  /-- `ir'`'s shared expressions read earlier entries. -/
  refsOrdered' : ir'.RefsOrdered
  /-- The values of `V`, renamed. -/
  vals : ∀ v ∈ V, v < ir.values.length ∧ σ.val v < ir'.values.length ∧
    ir'.valueField (σ.val v) = ir.valueField v ∧
    (ir'.value (σ.val v)).size = (ir.value v).size ∧
    (ir'.value (σ.val v)).type = (ir.value v).type ∧
    (ir'.value (σ.val v)).phase = (ir.value v).phase ∧
    σ.kindCorr (ir.value v).kind (ir'.value (σ.val v)).kind = true ∧
    ∀ u ∈ ir.valueDeps v, u ∈ V
  /-- A challenge value's challenge and its renamed challenge have the same field. -/
  chal : ∀ v ∈ V, ∀ c ∈ (ir.value v).kind.challenge?, ir'.chalField (σ.chal c) = ir.chalField c
  /-- The shared expressions of `R`, renamed. -/
  refs : ∀ k ∈ R, k < ir.exprs.length ∧ σ.ref k < ir'.exprs.length ∧
    (σ.expr (ir.expr k)).beq (ir'.expr (σ.ref k)) = true ∧ (ir.expr k).opsFree = true ∧
    (∀ v ∈ (ir.expr k).directNodes, v ∈ V) ∧ ∀ k' ∈ (ir.expr k).refs, k' ∈ R

theorem embedding_iff {σ : Renaming} {V R : List ℕ} : ir.Embedding ir' σ V R ↔
    ir.ValuesOrdered ∧ ir'.ValuesOrdered ∧ ir.refsOrderedB = true ∧ ir'.refsOrderedB = true ∧
    (∀ v ∈ V, v < ir.values.length ∧ σ.val v < ir'.values.length ∧
      ir'.valueField (σ.val v) = ir.valueField v ∧
      (ir'.value (σ.val v)).size = (ir.value v).size ∧
      (ir'.value (σ.val v)).type = (ir.value v).type ∧
      (ir'.value (σ.val v)).phase = (ir.value v).phase ∧
      σ.kindCorr (ir.value v).kind (ir'.value (σ.val v)).kind = true ∧
      ∀ u ∈ ir.valueDeps v, u ∈ V) ∧
    (∀ v ∈ V, ∀ c ∈ (ir.value v).kind.challenge?, ir'.chalField (σ.chal c) = ir.chalField c) ∧
    (∀ k ∈ R, k < ir.exprs.length ∧ σ.ref k < ir'.exprs.length ∧
      (σ.expr (ir.expr k)).beq (ir'.expr (σ.ref k)) = true ∧ (ir.expr k).opsFree = true ∧
      (∀ v ∈ (ir.expr k).directNodes, v ∈ V) ∧ ∀ k' ∈ (ir.expr k).refs, k' ∈ R) :=
  ⟨fun h => ⟨h.1, h.2, (refsOrderedB_iff ir).2 h.3, (refsOrderedB_iff ir').2 h.4, h.5, h.6, h.7⟩,
    fun h => ⟨h.1, h.2.1, (refsOrderedB_iff ir).1 h.2.2.1, (refsOrderedB_iff ir').1 h.2.2.2.1,
      h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩⟩

/-! ## Environments read through the renaming -/

variable (ir) in
/-- **An environment of `ir'` read as one of `ir`** through the renaming `σ`: the statement, the
committed assignment and the late values of value `v ∈ V` are those of `σ.val v`, `0` outside
`V`; challenge `j` is `ir'`'s challenge `σ.chal j`. -/
def pullEnv (σ : Renaming) (V : List ℕ) (e' : ir'.Env I) : ir.Env I where
  stmt v i := if v ∈ V then castElt (e'.stmt (σ.val v) i) else 0
  asg := ⟨fun v i => if v ∈ V then castElt (e'.asg.val (σ.val v) i) else 0,
    fun v i => if v ∈ V then castElt (e'.asg.pad (σ.val v) i) else 0⟩
  chal j i := castElt (e'.chal (σ.chal j) i)
  late v i := if v ∈ V then castElt (e'.late (σ.val v) i) else 0

variable {σ : Renaming} {V R : List ℕ}

/-- **The readings agree on `V`** at every fuel. -/
theorem read_pullEnv (hE : ir.Embedding ir' σ V R) (e' : ir'.Env I) :
    ∀ n, ∀ v ∈ V, ∀ i, ir.read (ir.pullEnv σ V e') n v i = castElt (ir'.read e' n (σ.val v) i)
  | 0, _, _, _ => by simp [read]
  | n + 1, v, hv, i => by
    obtain ⟨-, -, hf, hsz, hty, -, hk, hdep⟩ := hE.vals v hv
    rw [read.eq_2 ir _ v i n, read.eq_2 ir' e' (σ.val v) i n]
    rcases hkv : (ir.value v).kind with _ | ⟨_ | ⟨name, _ | ⟨a, args⟩⟩ | x⟩ | es | c | _ |
      ⟨w, sel⟩ | ⟨u, mp⟩ | u | x <;>
    rcases hkv' : (ir'.value (σ.val v)).kind with _ | ⟨_ | ⟨name', _ | ⟨a', args'⟩⟩ | x'⟩ | es' |
      c' | _ | ⟨w', sel'⟩ | ⟨u', mp'⟩ | u' | x' <;>
    simp only [Renaming.kindCorr, Renaming.kind?, hkv, hkv', reduceCtorEq] at hk
    · simp only [pullEnv, if_pos hv]
    · simp only [pullEnv, if_pos hv]
    · simp only [pullEnv, if_pos hv, if_true]
    · simp only [beq_iff_eq] at hk
      subst hk
      exact (castElt_decode hf _).symm
    · simp only [beq_iff_eq] at hk
      subst hk
      have hc := hE.chal v hv c (by simp [hkv, Kind.challenge?])
      simp only [pullEnv]
      rw [castElt_castElt_eq, castElt_castElt_eq, if_pos hc, hf]
      split_ifs with h
      · rfl
      · exact castElt_of_ne h _
    · simp only [pullEnv, if_pos hv]
    · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hk
      obtain ⟨rfl, rfl⟩ := hk
      have hw := hdep w (by simp [valueDeps, hkv])
      obtain ⟨-, -, hfw, -, htyw, -⟩ := hE.vals w hw
      simp only [bitView, read_pullEnv hE e' n w hw, hsz, hty, htyw,
        coord_castElt_of_eq hfw, castElt_ofBool_of_eq hf]
    · simp only [pullEnv, if_pos hv]
    · simp only [pullEnv, if_pos hv]

/-- **The readers agree on `V`.** -/
theorem reader_pullEnv (hE : ir.Embedding ir' σ V R) (e' : ir'.Env I) {v : ℕ} (hv : v ∈ V)
    (i : ℕ) : ir.reader (ir.pullEnv σ V e') v i = castElt (ir'.reader e' (σ.val v) i) := by
  obtain ⟨hl, hl', -⟩ := hE.vals v hv
  rw [reader_eq_read hE.ordered _ hl (le_max_left ir.fuel ir'.fuel),
    reader_eq_read hE.ordered' _ hl' (le_max_right ir.fuel ir'.fuel), read_pullEnv hE e' _ v hv]

/-! ## Shared expressions and predicates through the renaming -/

theorem castElt_castElt_of_src {a b c : ℕ} (h : a = b) (x : (I a).K) :
    (castElt (castElt x : (I b).K) : (I c).K) = castElt x := by
  rw [castElt_castElt_eq, if_pos h]

theorem expr_eq (hE : ir.Embedding ir' σ V R) {k : ℕ} (hk : k ∈ R) :
    ir'.expr (σ.ref k) = σ.expr (ir.expr k) :=
  (Expr.eq_of_beq (hE.refs k hk).2.2.1).symm

/-- **The renamed shared expressions have the originals' lengths.** -/
theorem refLen_rename (hE : ir.Embedding ir' σ V R) :
    ∀ k ∈ R, ir'.refLen ir'.exprs.length (σ.ref k) = ir.refLen ir.exprs.length k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    obtain ⟨hl, hl', -, ho, hv, hr⟩ := hE.refs k hk
    rw [refLen_eq_len hE.refsOrdered hl, refLen_eq_len hE.refsOrdered' hl', expr_eq hE hk]
    exact Renaming.len_expr σ _ ho (fun v hv' => (hE.vals v (hv v hv')).2.2.2.1)
      fun k' hk' => ih k' (hE.refsOrdered k hl k' hk') (hr k' hk')

/-- **The renamed shared expressions have the originals' values**, where the values of `V` read
alike. -/
theorem refVal_rename (hE : ir.Embedding ir' σ V R) {f : ℕ} {leaf : ir.Valuation I}
    {leaf' : ir'.Valuation I}
    (hl : ∀ v ∈ V, ∀ i, (castElt (leaf' (σ.val v) i) : (I f).K) = castElt (leaf v i)) :
    ∀ k ∈ R, ir'.refVal leaf' ir'.exprs.length f (σ.ref k) =
      ir.refVal leaf ir.exprs.length f k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    obtain ⟨hlt, hlt', -, ho, hv, hr⟩ := hE.refs k hk
    rw [refVal_stable hE.refsOrdered leaf f k hlt _ (k + 1) hlt (by omega),
      refVal_stable hE.refsOrdered' leaf' f (σ.ref k) hlt' _ (σ.ref k + 1) hlt' (by omega)]
    simp only [refVal]
    rw [expr_eq hE hk]
    refine Renaming.eval_expr σ _ ho
      (fun v hv' => ⟨(hE.vals v (hv v hv')).2.2.2.1, hl v (hv v hv')⟩) fun k' hk' => ?_
    have hkk := hE.refsOrdered k hlt k' hk'
    have hk'R := hr k' hk'
    obtain ⟨hlt₁, hlt₁', -⟩ := hE.refs k' hk'R
    have hσ : σ.ref k' < σ.ref k := hE.refsOrdered' (σ.ref k) hlt' (σ.ref k')
      (by rw [expr_eq hE hk]; exact σ.mem_refs_expr hk')
    refine ⟨refLen_rename hE k' hk'R, ?_⟩
    rw [refVal_stable hE.refsOrdered' leaf' f (σ.ref k') hlt₁' (σ.ref k) ir'.exprs.length hσ hlt₁',
      refVal_stable hE.refsOrdered leaf f k' hlt₁ k ir.exprs.length hkk hlt₁]
    exact ih k' hkk hk'R

/-- **A renamed expression has the original's length**, for an expression of `V` and `R` whose
named operators read no value. -/
theorem exprLen_rename (hE : ir.Embedding ir' σ V R) {e : Expr} (ho : e.opsFree = true)
    (hv : ∀ v ∈ e.directNodes, v ∈ V) (hr : ∀ k ∈ e.refs, k ∈ R) :
    ir'.exprLen (σ.expr e) = ir.exprLen e :=
  Renaming.len_expr σ e ho (fun v hv' => (hE.vals v (hv v hv')).2.2.2.1)
    fun k hk => refLen_rename hE k (hr k hk)

/-- **A renamed expression has the original's value** in the environment read through the
renaming. -/
theorem evalE_rename (hE : ir.Embedding ir' σ V R) (e' : ir'.Env I) {f : ℕ} {e : Expr}
    (ho : e.opsFree = true) (hv : ∀ v ∈ e.directNodes, v ∈ V) (hr : ∀ k ∈ e.refs, k ∈ R) :
    ir'.evalE (ir'.reader e') f (σ.expr e) = ir.evalE (ir.reader (ir.pullEnv σ V e')) f e := by
  have hl : ∀ v ∈ V, ∀ i, (castElt (ir'.reader e' (σ.val v) i) : (I f).K) =
      castElt (ir.reader (ir.pullEnv σ V e') v i) := fun v hv' i => by
    rw [reader_pullEnv hE e' hv', castElt_castElt_of_src (hE.vals v hv').2.2.1]
  funext i
  simp only [evalE]
  rw [Renaming.eval_expr σ e ho (fun v hv' => ⟨(hE.vals v (hv v hv')).2.2.2.1, hl v (hv v hv')⟩)
    fun k hk => ⟨refLen_rename hE k (hr k hk), refVal_rename hE hl k (hr k hk)⟩]

/-- **A renamed predicate `equal` holds in an environment of `ir'`** exactly when the original
holds in the environment read through the renaming. -/
theorem holdsAt_pullEnv (hE : ir.Embedding ir' σ V R) (e' : ir'.Env I) {b b' : PredBody}
    (hb : ir.equalCorrB ir' σ V R b b' = true) :
    ir'.HoldsAt e' b' ↔ ir.HoldsAt (ir.pullEnv σ V e') b := by
  unfold equalCorrB at hb
  split at hb
  · rename_i d x y _ d' x' y' _
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_append, List.all_eq_true,
      decide_eq_true_eq] at hb
    obtain ⟨⟨⟨⟨⟨⟨⟨rfl, hd⟩, hx⟩, hy⟩, hox⟩, hoy⟩, hvx, hvy⟩, hrx, hry⟩ := hb
    rw [← Expr.eq_of_beq hx, ← Expr.eq_of_beq hy]
    simp only [HoldsAt, HoldsWith, evalWith]
    rw [exprLen_rename hE hox hvx hrx, hd, evalE_rename hE e' hox hvx hrx,
      evalE_rename hE e' hoy hvy hry]
  · exact absurd hb Bool.false_ne_true

/-! ## Integer readings through the renaming -/

theorem centered_of_eq {a b : ℕ} (h : a = b) (c : ℕ) : (I b).centered c = (I a).centered c := by
  subst h
  rfl

/-- **The integer readings agree on `V`** (`RealizedProgram.intOf`): a constant's entries, a bound
value's and any other value's readings are the renamed value's. -/
theorem intOf_pullEnv (hE : ir.Embedding ir' σ V R) (e' : ir'.Env I) {v : ℕ} (hv : v ∈ V)
    (i : ℕ) : ir'.intOf (ir'.reader e') (σ.val v) i =
      ir.intOf (ir.reader (ir.pullEnv σ V e')) v i := by
  obtain ⟨-, -, hf, -, -, -, hk, -⟩ := hE.vals v hv
  have hr := reader_pullEnv hE e' hv i
  rcases hkv : (ir.value v).kind with _ | ⟨_ | ⟨name, _ | ⟨a, args⟩⟩ | x⟩ | es | c | _ |
      ⟨w, sel⟩ | ⟨u, mp⟩ | u | x <;>
    rcases hkv' : (ir'.value (σ.val v)).kind with _ | ⟨_ | ⟨name', _ | ⟨a', args'⟩⟩ | x'⟩ | es' |
      c' | _ | ⟨w', sel'⟩ | ⟨u', mp'⟩ | u' | x' <;>
    simp only [Renaming.kindCorr, Renaming.kind?, hkv, hkv', reduceCtorEq] at hk <;>
    simp only [intOf, hkv, hkv', hr, toNat_castElt hf]
  · simp only [beq_iff_eq] at hk
    rw [hk, centered_of_eq hf]
  · rw [centered_of_eq hf]

/-- **A shared expression's integer value does not depend on the levels** past its index, when the
shared expressions read only entries of smaller index. -/
private theorem refInt_levels (ho : ir.RefsOrdered) (rd : ir.Valuation I) (f : ℕ) :
    ∀ k, k < ir.exprs.length → ∀ n m, k < n → k < m → ir.refInt rd f n k = ir.refInt rd f m k
  | k, hk, n + 1, m + 1, hn, hm => by
    funext i
    simp only [refInt]
    exact congrFun (Expr.evalInt_congr ir (ir.expr k) (fun _ _ => ⟨rfl, rfl⟩) fun k' hk' =>
      have := ho k hk k' hk'
      refInt_levels ho rd f k' (by omega) n m (by omega) (by omega)) i

/-- **The renamed shared expressions have the originals' integer values**, where the values of `V`
have alike integer readings. -/
theorem refInt_rename (hE : ir.Embedding ir' σ V R) {f : ℕ} {rd : ir.Valuation I}
    {rd' : ir'.Valuation I} (hl : ∀ v ∈ V, ∀ i, ir'.intOf rd' (σ.val v) i = ir.intOf rd v i) :
    ∀ k ∈ R, ir'.refInt rd' f ir'.exprs.length (σ.ref k) = ir.refInt rd f ir.exprs.length k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    obtain ⟨hlt, hlt', -, ho, hv, hr⟩ := hE.refs k hk
    rw [refInt_levels hE.refsOrdered rd f k hlt _ (k + 1) hlt (by omega),
      refInt_levels hE.refsOrdered' rd' f (σ.ref k) hlt' _ (σ.ref k + 1) hlt' (by omega)]
    simp only [refInt]
    rw [expr_eq hE hk]
    refine Renaming.evalInt_expr σ _ ho
      (fun v hv' => ⟨(hE.vals v (hv v hv')).2.2.2.1, hl v (hv v hv')⟩) fun k' hk' => ?_
    have hkk := hE.refsOrdered k hlt k' hk'
    have hk'R := hr k' hk'
    obtain ⟨hlt₁, hlt₁', -⟩ := hE.refs k' hk'R
    have hσ : σ.ref k' < σ.ref k := hE.refsOrdered' (σ.ref k) hlt' (σ.ref k')
      (by rw [expr_eq hE hk]; exact σ.mem_refs_expr hk')
    refine ⟨refLen_rename hE k' hk'R, ?_⟩
    rw [refInt_levels hE.refsOrdered' rd' f (σ.ref k') hlt₁' (σ.ref k) ir'.exprs.length hσ hlt₁',
      refInt_levels hE.refsOrdered rd f k' hlt₁ k ir.exprs.length hkk hlt₁]
    exact ih k' hkk hk'R

/-- **A renamed expression has the original's integer value** in domain `d` in the environment
read through the renaming, the domain having one field in both programs. -/
theorem evalIntWith_rename (hE : ir.Embedding ir' σ V R) (e' : ir'.Env I) {d : ℕ}
    (hd : ir'.domainField d = ir.domainField d) {e : Expr} (ho : e.opsFree = true)
    (hv : ∀ v ∈ e.directNodes, v ∈ V) (hr : ∀ k ∈ e.refs, k ∈ R) :
    ir'.evalIntWith (ir'.reader e') d (σ.expr e) =
      ir.evalIntWith (ir.reader (ir.pullEnv σ V e')) d e := by
  have hl := fun v (hv' : v ∈ V) i => intOf_pullEnv hE e' hv' i
  funext i
  simp only [evalIntWith]
  rw [hd, Renaming.evalInt_expr σ e ho (leaf := ir.reader (ir.pullEnv σ V e'))
    (fun v hv' => ⟨(hE.vals v (hv v hv')).2.2.2.1, hl v (hv v hv')⟩)
    fun k hk => ⟨refLen_rename hE k (hr k hk), refInt_rename hE hl k (hr k hk)⟩]

/-! ## Ranges and congruences through the renaming -/

theorem partExprB_iff {x : Expr} : partExprB V R x = true ↔
    x.opsFree = true ∧ (∀ v ∈ x.directNodes, v ∈ V) ∧ ∀ k ∈ x.refs, k ∈ R := by
  simp only [partExprB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, and_assoc]

theorem exprCorrB_iff {x x' : Expr} : exprCorrB σ V R x x' = true ↔
    x' = σ.expr x ∧ x.opsFree = true ∧ (∀ v ∈ x.directNodes, v ∈ V) ∧ ∀ k ∈ x.refs, k ∈ R := by
  rw [exprCorrB, Bool.and_eq_true, partExprB_iff]
  exact ⟨fun h => ⟨(Expr.eq_of_beq h.1).symm, h.2⟩,
    fun h => ⟨by rw [h.1]; exact Expr.beq_self _, h.2⟩⟩

/-- **A renamed range `in` or `mod_q` holds in an environment of `ir'`**, as a renamed `equal`
does (`holdsAt_pullEnv`), exactly when the original holds in the environment read through the
renaming. -/
theorem holdsAt_pullEnv_body (hE : ir.Embedding ir' σ V R) (e' : ir'.Env I) {b b' : PredBody}
    (hb : ir.bodyCorrB ir' σ V R b b' = true) :
    ir'.HoldsAt e' b' ↔ ir.HoldsAt (ir.pullEnv σ V e') b := by
  unfold bodyCorrB at hb
  split at hb
  · exact holdsAt_pullEnv hE e' hb
  · rename_i d rs n _ d' rs' n' _
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.all_eq_true] at hb
    obtain ⟨⟨⟨⟨⟨rfl, hd⟩, rfl⟩, hne⟩, hrs⟩, hok⟩ := hb
    have hok' := fun x (hx : x ∈ rs) => partExprB_iff.1 (hok x hx)
    rw [← Expr.eq_of_beqList hrs, Renaming.exprs_eq_map]
    have hhead : (rs.map σ.expr).headD default = σ.expr (rs.headD default) := by
      cases rs with
      | nil => exact absurd rfl hne
      | cons => rfl
    have hmem : rs.headD default ∈ rs := by
      cases rs with
      | nil => exact absurd rfl hne
      | cons => simp
    simp only [HoldsAt, HoldsWith, InSetWith, InRows, evalWith, hhead]
    rw [exprLen_rename hE (hok' _ hmem).1 (hok' _ hmem).2.1 (hok' _ hmem).2.2, hd]
    refine forall_congr' fun i => imp_congr_right fun _ => ?_
    rw [List.forall_mem_map]
    refine forall₂_congr fun x hx => ?_
    rw [evalE_rename hE e' (hok' x hx).1 (hok' x hx).2.1 (hok' x hx).2.2]
  · rename_i d q x y real d' q' x' y' real'
    simp only [Bool.and_eq_true, beq_iff_eq] at hb
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨rfl, hd⟩, rfl⟩, hx⟩, hy⟩, hprod⟩, hlo⟩, hqmax⟩, hq⟩ := hb
    obtain ⟨rfl, hX⟩ := exprCorrB_iff.1 hx
    obtain ⟨rfl, hY⟩ := exprCorrB_iff.1 hy
    simp only [HoldsAt, HoldsWith]
    rw [exprLen_rename hE hX.1 hX.2.1 hX.2.2, evalIntWith_rename hE e' hd hX.1 hX.2.1 hX.2.2,
      evalIntWith_rename hE e' hd hY.1 hY.2.1 hY.2.2]
    refine and_congr Iff.rfl ?_
    rcases hQ : real.quotient with _ | Q <;> rcases hQ' : real'.quotient with _ | Q' <;>
      simp only [quotCorrB, hQ, hQ', reduceCtorEq] at hq
    · simp only [ProductQuotWith, hQ, hQ']
    · obtain ⟨rfl, hQo⟩ := exprCorrB_iff.1 hq
      simp only [ProductQuotWith, hQ, hQ', evalWith, hprod, hlo, hqmax]
      rw [exprLen_rename hE hX.1 hX.2.1 hX.2.2, evalIntWith_rename hE e' hd hX.1 hX.2.1 hX.2.2,
        evalIntWith_rename hE e' hd hY.1 hY.2.1 hY.2.2,
        evalIntWith_rename hE e' hd hQo.1 hQo.2.1 hQo.2.2, hd,
        evalE_rename hE e' hX.1 hX.2.1 hX.2.2, evalE_rename hE e' hY.1 hY.2.1 hY.2.2,
        evalE_rename hE e' hQo.1 hQo.2.1 hQo.2.2]
  · exact absurd hb Bool.false_ne_true

/-- **A value of `V` lies in its type** in the environment read through the renaming where its
renamed value does. -/
theorem inType_pullEnv (hE : ir.Embedding ir' σ V R) (e' : ir'.Env I) {v : ℕ} (hv : v ∈ V)
    {i : ℕ} (h : (I (ir'.valueField (σ.val v))).InType (ir'.value (σ.val v)).type
      (ir'.reader e' (σ.val v) i)) :
    (I (ir.valueField v)).InType (ir.value v).type (ir.reader (ir.pullEnv σ V e') v i) := by
  obtain ⟨-, -, hf, -, hty, -⟩ := hE.vals v hv
  rw [reader_pullEnv hE e' hv, ← hty]
  exact inType_castElt_of_eq hf _ h

/-- **Environments agreeing on what is fixed when challenge `σ.chal j` is drawn agree, read
through the renaming, on what is fixed when challenge `j` is drawn**, each renamed challenge
having the original's phase and the challenge renaming keeping the order. -/
theorem eqUpTo_pullEnv (hE : ir.Embedding ir' σ V R)
    (hph : ∀ j, (ir'.challenge (σ.chal j)).phase = (ir.challenge j).phase)
    (hmono : Monotone σ.chal) {j : ℕ} {e₁ e₂ : ir'.Env I}
    (h : Env.EqUpTo (σ.chal j) e₁ e₂) : Env.EqUpTo j (ir.pullEnv σ V e₁) (ir.pullEnv σ V e₂) where
  stmt := by simp only [pullEnv, h.stmt]
  asg := by simp only [pullEnv, h.asg]
  chal j' hj := by
    have : ir'.ChalBefore (σ.chal j') (σ.chal j) := by
      unfold ChalBefore at hj ⊢
      rw [hph, hph]
      exact hj.imp_right fun h' => ⟨h'.1, hmono h'.2⟩
    simp only [pullEnv, h.chal (σ.chal j') this]
  late v hv := by
    funext i
    simp only [pullEnv]
    split_ifs with hvV
    · rw [h.late (σ.val v) (by rw [(hE.vals v hvV).2.2.2.2.2.1, hph]; exact hv)]
    · rfl

end

/-! ## The check of an embedding -/

namespace Renaming

mutual

/-- Renamings that agree on what an expression reads rename it alike. -/
theorem expr_congr {σ σ' : Renaming} : ∀ (e : Expr),
    (∀ v ∈ e.directNodes, σ.val v = σ'.val v) → (∀ k ∈ e.refs, σ.ref k = σ'.ref k) →
    σ.expr e = σ'.expr e
  | .leaf v, hv, _ => by simp [expr, hv v (by simp [Expr.directNodes])]
  | .add e e', hv, hr | .sub e e', hv, hr | .mul e e', hv, hr | .concat e e', hv, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at hv hr
    simp only [expr]
    rw [expr_congr e (fun v h => hv v (.inl h)) fun k h => hr k (.inl h),
      expr_congr e' (fun v h => hv v (.inr h)) fun k h => hr k (.inr h)]
  | .scale c e, hv, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at hv hr
    simp only [expr]
    rw [expr_congr e (fun v h => hv v (.inr h)) hr, coef_congr fun v h => hv v (.inl h)]
  | .reindex _ e, hv, hr | .prod _ e, hv, hr => by
    simp only [Expr.directNodes, Expr.refs] at hv hr
    simp only [expr]
    rw [expr_congr e hv hr]
  | .apply op e, hv, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at hv hr
    simp only [expr]
    rw [expr_congr e (fun v h => hv v (.inr h)) hr]
  | .linear rows e, hv, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append, List.mem_flatMap] at hv hr
    simp only [expr]
    rw [expr_congr e (fun v h => hv v (.inr h)) hr]
    congr 1
    refine List.map_congr_left fun row hrow => List.map_congr_left fun t ht => ?_
    rw [coef_congr fun v h => hv v (.inl ⟨row, hrow, t, ht, h⟩)]
  | .mux b t e, hv, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at hv hr
    simp only [expr]
    rw [expr_congr b (fun v h => hv v (.inl (.inl h))) fun k h => hr k (.inl (.inl h)),
      expr_congr t (fun v h => hv v (.inl (.inr h))) fun k h => hr k (.inl (.inr h)),
      expr_congr e (fun v h => hv v (.inr h)) fun k h => hr k (.inr h)]
  | .ref k, _, hr => by simp [expr, hr k (by simp [Expr.refs])]
  | .logic op w args, hv, hr => by
    simp only [Expr.directNodes, Expr.refs] at hv hr
    simp only [expr]
    rw [exprs_congr args hv hr]

/-- Renamings that agree on what a list of expressions reads rename it alike. -/
theorem exprs_congr {σ σ' : Renaming} : ∀ (es : List Expr),
    (∀ v ∈ Expr.directNodesList es, σ.val v = σ'.val v) →
    (∀ k ∈ Expr.refsList es, σ.ref k = σ'.ref k) → σ.exprs es = σ'.exprs es
  | [], _, _ => rfl
  | e :: es, hv, hr => by
    simp only [Expr.directNodesList, Expr.refsList, List.mem_append] at hv hr
    simp only [exprs]
    rw [expr_congr e (fun v h => hv v (.inl h)) fun k h => hr k (.inl h),
      exprs_congr es (fun v h => hv v (.inr h)) fun k h => hr k (.inr h)]

/-- Renamings that agree on a coefficient's values rename it alike. -/
theorem coef_congr {σ σ' : Renaming} {c : Coef} (h : ∀ v ∈ c.nodes, σ.val v = σ'.val v) :
    σ.coef c = σ'.coef c := by
  cases c with
  | const _ => rfl
  | node v i => simp [coef, h v (by simp [Coef.nodes])]

end

end Renaming

/-- Each identifier of the data's lists has the image the renaming gives it. -/
structure EmbedData.Agrees (d : EmbedData) (σ : Renaming) : Prop where
  val : ∀ v < d.vals.length, σ.val v = d.vals.getD v v
  ref : ∀ k < d.refs.length, σ.ref k = d.refs.getD k k
  chal : ∀ j < d.chals.length, σ.chal j = d.chals.getD j j

/-- **What the check of an embedding gives**, at every renaming that agrees with its data: the
embedding, and the listed predicates' correspondences, each pair a predicate of the smaller program
and one of the larger program, which for an equality is a source predicate. -/
structure EmbedData.Holds (d : EmbedData) (ir' : RealizedProgram) (σ : Renaming) : Prop where
  embedding : d.source.Embedding ir' σ d.V d.R
  equals : ∀ p ∈ d.equals, d.source.equalCorrB ir' σ d.V d.R (d.source.predicate p.1).body
      (ir'.predicate p.2).body = true ∧ p.1 < d.source.predicates.length ∧
    p.2 < ir'.predicates.length ∧ ir'.inSource (ir'.predicate p.2) = true
  bodies : ∀ p ∈ d.bodies, d.source.bodyCorrB ir' σ d.V d.R (d.source.predicate p.1).body
      (ir'.predicate p.2).body = true ∧ p.1 < d.source.predicates.length ∧
    p.2 < ir'.predicates.length
  sources : ∀ p ∈ d.sources, ir'.inSource (ir'.predicate p) = true
  chalCount : d.source.challenges.length = d.chals.length
  chalPhase : ∀ j < d.chals.length, (ir'.challenge (σ.chal j)).phase = (d.source.challenge j).phase

theorem valuesOrdered_of_valuesOrderedB {ir : RealizedProgram} (ho : ir.RefsOrdered)
    (h : valuesOrderedB ir = true) : ir.ValuesOrdered := by
  intro v hv u hu
  have h1 := (allIdx_iff _ ir.values 0).1 h v hv
  rw [zero_add, ← value_eq_getD, Bool.and_eq_true, List.all_eq_true] at h1
  refine of_decide_eq_true (h1.2 u ?_)
  obtain ⟨hr, -⟩ := h1
  rw [valueDeps] at hu
  rw [valueDepsOf]
  rw [refsInB] at hr
  rcases hk : (ir.value v).kind with _ | ⟨_ | ⟨_, args⟩ | e⟩ | _ | _ | _ | ⟨w, sel⟩ | _ | _ <;>
    rw [hk] at hu hr <;> try exact hu
  rw [List.all_eq_true] at hr
  exact (mem_nodesOf ho (fun k hk => of_decide_eq_true (hr k hk)) u).2 hu

section Sound

variable {d : EmbedData} {ir' : RealizedProgram} {σ : Renaming}

theorem EmbedData.renaming_val (v : ℕ) : d.renaming.val v = d.vals.getD v v :=
  NatTrie.getD_ofSeq _ _ _

theorem EmbedData.renaming_ref (k : ℕ) : d.renaming.ref k = d.refs.getD k k :=
  NatTrie.getD_ofSeq _ _ _

theorem EmbedData.renaming_chal (j : ℕ) : d.renaming.chal j = d.chals.getD j j := rfl

/-- The correspondence of an equality, read through two renamings that agree on the part. -/
theorem equalCorrB_congr {ir ir' : RealizedProgram} {σ σ' : Renaming} {V R : List ℕ}
    (hv : ∀ v ∈ V, σ.val v = σ'.val v) (hr : ∀ k ∈ R, σ.ref k = σ'.ref k) {b b' : PredBody}
    (h : ir.equalCorrB ir' σ V R b b' = true) : ir.equalCorrB ir' σ' V R b b' = true := by
  unfold equalCorrB at h ⊢
  split at h
  · simp only [Bool.and_eq_true, List.all_eq_true, List.mem_append, decide_eq_true_eq] at h ⊢
    obtain ⟨⟨⟨⟨⟨⟨⟨hd, hf⟩, hx⟩, hy⟩, hox⟩, hoy⟩, hN⟩, hR⟩ := h
    rw [← Renaming.expr_congr _ (fun v h => hv v (hN v (.inl h))) fun k h => hr k (hR k (.inl h)),
      ← Renaming.expr_congr _ (fun v h => hv v (hN v (.inr h))) fun k h => hr k (hR k (.inr h))]
    exact ⟨⟨⟨⟨⟨⟨⟨hd, hf⟩, hx⟩, hy⟩, hox⟩, hoy⟩, hN⟩, hR⟩
  · simp at h

theorem exprCorrB_congr {σ σ' : Renaming} {V R : List ℕ}
    (hv : ∀ v ∈ V, σ.val v = σ'.val v) (hr : ∀ k ∈ R, σ.ref k = σ'.ref k) {x x' : Expr}
    (h : exprCorrB σ V R x x' = true) : exprCorrB σ' V R x x' = true := by
  rw [exprCorrB_iff] at h ⊢
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by
    rw [h1]
    exact Renaming.expr_congr _ (fun v h => hv v (h3 v h)) fun k h => hr k (h4 k h), h2, h3, h4⟩

theorem quotCorrB_congr {σ σ' : Renaming} {V R : List ℕ}
    (hv : ∀ v ∈ V, σ.val v = σ'.val v) (hr : ∀ k ∈ R, σ.ref k = σ'.ref k) {q q' : Option Expr}
    (h : quotCorrB σ V R q q' = true) : quotCorrB σ' V R q q' = true := by
  cases q <;> cases q' <;> simp_all only [quotCorrB]
  exact exprCorrB_congr hv hr h

/-- The correspondence of a body, read through two renamings that agree on the part. -/
theorem bodyCorrB_congr {ir ir' : RealizedProgram} {σ σ' : Renaming} {V R : List ℕ}
    (hv : ∀ v ∈ V, σ.val v = σ'.val v) (hr : ∀ k ∈ R, σ.ref k = σ'.ref k) {b b' : PredBody}
    (h : ir.bodyCorrB ir' σ V R b b' = true) : ir.bodyCorrB ir' σ' V R b b' = true := by
  unfold bodyCorrB at h ⊢
  split at h
  · exact equalCorrB_congr hv hr h
  · simp only [Bool.and_eq_true] at h ⊢
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    have hp := List.all_eq_true.mp h6
    have he : σ'.exprs _ = σ.exprs _ := (Renaming.exprs_eq_map _ _).trans
      ((List.map_congr_left fun e he => by
        obtain ⟨-, h7, h8⟩ := partExprB_iff.mp (hp e he)
        exact (Renaming.expr_congr e (fun v h => hv v (h7 v h)) fun k h => hr k (h8 k h)).symm).trans
        (Renaming.exprs_eq_map _ _).symm)
    exact ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, by rw [he]; exact h5⟩, h6⟩
  · simp only [Bool.and_eq_true] at h ⊢
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
    exact ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, exprCorrB_congr hv hr h4⟩, exprCorrB_congr hv hr h5⟩, h6⟩, h7⟩, h8⟩,
      quotCorrB_congr hv hr h9⟩
  · simp at h

theorem Renaming.kind?_congr {σ σ' : Renaming} {k : Kind}
    (hc : ∀ c, k = .challenge c → σ.chal c = σ'.chal c)
    (hb : ∀ w s, k = .bits w s → σ.val w = σ'.val w)
    (hp : ∀ v m, k = .padCopy v m → σ.val v = σ'.val v)
    (he : ∀ e, k = .bound e → σ.expr e = σ'.expr e) : σ.kind? k = σ'.kind? k := by
  cases k with
  | challenge c => simp only [Renaming.kind?, hc c rfl]
  | bits w s => simp only [Renaming.kind?, hb w s rfl]
  | padCopy v m => simp only [Renaming.kind?, hp v m rfl]
  | bound e => simp only [Renaming.kind?, he e rfl]
  | priv | constant _ | late | message _ => rfl
  | pub d =>
    cases d with
    | input | expr _ => rfl
    | «opaque» n args => cases args <;> rfl

/-- **A list read as the images of the identifiers from `i` on** agrees with `f`, entry by entry.
The check walks the list once. -/
def listAgreesB (f : ℕ → ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | i, x :: xs => f i == x && listAgreesB f (i + 1) xs

theorem listAgreesB_getD {f : ℕ → ℕ} :
    ∀ {i : ℕ} {l : List ℕ}, listAgreesB f i l = true →
      ∀ k < l.length, f (i + k) = l.getD k (i + k)
  | _, [], _, k, hk => absurd hk (Nat.not_lt_zero k)
  | i, x :: xs, h, k, hk => by
    simp only [listAgreesB, Bool.and_eq_true, beq_iff_eq] at h
    cases k with
    | zero => simpa using h.1
    | succ k =>
      have := listAgreesB_getD h.2 k (by simpa using hk)
      simp only [List.getD_cons_succ]
      rw [show i + (k + 1) = i + 1 + k by omega, this]

/-- **An embedding's lists agree with a renaming**, checked by one walk over each list. -/
theorem EmbedData.agrees_of_checks {d : EmbedData} {σ : Renaming}
    (hv : listAgreesB σ.val 0 d.vals = true) (hr : listAgreesB σ.ref 0 d.refs = true)
    (hc : listAgreesB σ.chal 0 d.chals = true) : d.Agrees σ where
  val v h := by simpa using listAgreesB_getD hv v h
  ref k h := by simpa using listAgreesB_getD hr k h
  chal j h := by simpa using listAgreesB_getD hc j h

theorem EmbedData.Agrees.val_eq (ha : d.Agrees σ) {v : ℕ} (h : v < d.vals.length) :
    d.renaming.val v = σ.val v := by
  rw [EmbedData.renaming_val, ha.val v h]

theorem EmbedData.Agrees.ref_eq (ha : d.Agrees σ) {k : ℕ} (h : k < d.refs.length) :
    d.renaming.ref k = σ.ref k := by
  rw [EmbedData.renaming_ref, ha.ref k h]

theorem EmbedData.Agrees.chal_eq (ha : d.Agrees σ) {j : ℕ} (h : j < d.chals.length) :
    d.renaming.chal j = σ.chal j := by
  rw [EmbedData.renaming_chal, ha.chal j h]

theorem EmbedData.kindCorr_of_covered (ha : d.Agrees σ) {k k' : Kind}
    (hc : d.kindCoveredB k = true) (h : d.renaming.kindCorr k k' = true) :
    σ.kindCorr k k' = true := by
  have he : d.renaming.kind? k = σ.kind? k := by
    apply Renaming.kind?_congr
    · rintro c rfl
      exact ha.chal_eq (of_decide_eq_true hc)
    · rintro w s rfl
      exact ha.val_eq (of_decide_eq_true hc)
    · rintro v m rfl
      exact ha.val_eq (of_decide_eq_true hc)
    · rintro e rfl
      simp only [EmbedData.kindCoveredB, Bool.and_eq_true, List.all_eq_true,
        decide_eq_true_eq] at hc
      exact Renaming.expr_congr e (fun v hv => ha.val_eq (hc.1 v hv))
        fun k hk => ha.ref_eq (hc.2 k hk)
  unfold Renaming.kindCorr at h ⊢
  rw [← he]
  exact h

/-- **The check of an embedding is sound**, at every renaming that agrees with its data. -/
theorem embeddingB_sound (h : embeddingB ir' d = true) (ha : d.Agrees σ) : d.Holds ir' σ := by
  simp only [embeddingB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, hV⟩, hR⟩, hE⟩, hB⟩, hS⟩, hC⟩, hP⟩ := h
  have hVparts := fun v (hv : v ∈ d.V) => by
    have := hV v hv
    simp only [EmbedData.valueB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      List.all_eq_true] at this
    exact this
  have hRparts := fun k (hk : k ∈ d.R) => by
    have := hR k hk
    simp only [EmbedData.refB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at this
    exact this
  have hvσ : ∀ v ∈ d.V, d.renaming.val v = σ.val v := fun v hv =>
    ha.val_eq (hVparts v hv).1.1.1.1.1.1.1.1.1.2
  have hrσ : ∀ k ∈ d.R, d.renaming.ref k = σ.ref k := fun k hk =>
    ha.ref_eq (hRparts k hk).1.1.1.1.1.2
  refine ⟨⟨valuesOrdered_of_valuesOrderedB ((refsOrderedB_iff _).1 h3) h1,
    valuesOrdered_of_valuesOrderedB ((refsOrderedB_iff _).1 h4) h2,
    (refsOrderedB_iff _).1 h3, (refsOrderedB_iff _).1 h4, ?_, ?_, ?_⟩, ?_, ?_, hS,
    beq_iff_eq.mp hC, ?_⟩
  · intro v hv
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, -⟩ := hVparts v hv
    rw [hvσ v hv] at a3 a4 a5 a6 a7 a8
    exact ⟨a1, a3, a4, a5, a6, a7, EmbedData.kindCorr_of_covered ha a9 a8, a10⟩
  · intro v hv c hc
    obtain ⟨-, a⟩ := hVparts v hv
    cases hk : (d.source.value v).kind with
    | challenge c' =>
      rw [hk] at a hc
      obtain rfl : c' = c := by simpa [Kind.challenge?] using hc
      have hcv : c' < d.chals.length := by
        have := (hVparts v hv).1.1.2
        rw [hk] at this
        exact of_decide_eq_true this
      have a' : ir'.chalField (d.renaming.chal c') = d.source.chalField c' := by simpa using a
      rw [← ha.chal_eq hcv]
      exact a'
    | _ => rw [hk] at hc; simp [Kind.challenge?] at hc
  · intro k hk
    obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩ := hRparts k hk
    rw [hrσ k hk] at a3 a4
    have he : d.renaming.expr (d.source.expr k) = σ.expr (d.source.expr k) :=
      Renaming.expr_congr _ (fun v hv => hvσ v (a6 v hv)) fun j hj => hrσ j (a7 j hj)
    rw [he] at a4
    exact ⟨a1, a3, a4, a5, a6, a7⟩
  · intro p hp
    simp only [decide_eq_true_eq] at hE
    obtain ⟨⟨⟨a, b⟩, c⟩, e⟩ := hE p hp
    exact ⟨equalCorrB_congr hvσ hrσ a, b, c, e⟩
  · intro p hp
    simp only [decide_eq_true_eq] at hB
    obtain ⟨⟨a, b⟩, c⟩ := hB p hp
    exact ⟨bodyCorrB_congr hvσ hrσ a, b, c⟩
  · intro j hj
    have := beq_iff_eq.mp (hP j (List.mem_range.mpr hj))
    rwa [ha.chal_eq hj] at this

/-- The embedding the check gives, at the data's program and lists named by the caller. -/
theorem EmbedData.Holds.embedding_at {ir : RealizedProgram} {V R : List ℕ} (h : d.Holds ir' σ)
    (hs : d.source = ir) (hV : d.V = V) (hR : d.R = R) : ir.Embedding ir' σ V R := by
  subst hs hV hR
  exact h.embedding

/-- A listed equality's correspondence, at the data's program and lists named by the caller. -/
theorem EmbedData.Holds.equals_at {ir : RealizedProgram} {V R : List ℕ} (h : d.Holds ir' σ)
    (hs : d.source = ir) (hV : d.V = V) (hR : d.R = R) {p p' : ℕ} (hp : (p, p') ∈ d.equals) :
    ir.equalCorrB ir' σ V R (ir.predicate p).body (ir'.predicate p').body = true ∧
      p' < ir'.predicates.length ∧ ir'.inSource (ir'.predicate p') = true := by
  subst hs hV hR
  obtain ⟨a, -, b, c⟩ := h.equals _ hp
  exact ⟨a, b, c⟩

/-- A listed predicate's correspondence, at the data's program and lists named by the caller. -/
theorem EmbedData.Holds.bodies_at {ir : RealizedProgram} {V R : List ℕ} (h : d.Holds ir' σ)
    (hs : d.source = ir) (hV : d.V = V) (hR : d.R = R) {p p' : ℕ} (hp : (p, p') ∈ d.bodies) :
    ir.bodyCorrB ir' σ V R (ir.predicate p).body (ir'.predicate p').body = true ∧
      p' < ir'.predicates.length := by
  subst hs hV hR
  obtain ⟨a, -, b⟩ := h.bodies _ hp
  exact ⟨a, b⟩

end Sound


end GordieHowe.RealizedProgram
