-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Library.Eval
public import GordieHowe.Language.RealizedProgram.Interval
public import GordieHowe.Language.RealizedProgram.Affine
public import GordieHowe.Language.RealizedProgram.Source

@[expose] public section

/-!
# GordieHowe: programs that share a part up to a renaming

Two realized programs of one interpretation can hold one part (a set of values, shared
expressions and predicates) up to a renaming of the value and shared-expression identifiers: the
emulated ML-DSA program at the ROM parameters holds the native one's domain `H` with every value identifier one
larger and every shared-expression identifier two larger (export `c825eb05`). This file transports
that part's semantics:

* **the renaming** (`Renaming`, `Renaming.expr`, `Renaming.kind`) of an expression's leaves,
  coefficients and references and of a value's kind;
* **expressions** (`Renaming.len_expr`, `Renaming.eval_expr`): a renamed expression has the
  original's length and value, where the renamed values have the originals' sizes and readings,
  for an expression whose named operators read no value (`Expr.opsFree`, `NamedOp.valueFree`);
* **the embedding** (`GordieHowe.RealizedProgram.Embedding`, decided per program pair): the values `V` and shared
  expressions `R` of the part, renamed, with their kinds, sizes, fields and types, closed under
  what they read;
* **environments** (`GordieHowe.RealizedProgram.pullEnv`): an environment of the larger program read as one of the
  smaller, through the renaming, `0` outside `V`; the readers agree on `V` (`reader_pullEnv`),
  the shared expressions on `R`, and a renamed predicate `equal` holds in one exactly when it
  holds in the other (`holdsAt_pullEnv`).

The values a program reads must be read in identifier order (`GordieHowe.RealizedProgram.ValuesOrdered`), so a
value's reading does not depend on the fuel past its identifier.
-/

namespace GordieHowe.RealizedProgram

/-! ## Operators that read no value -/

/-- **A named operator reads no value**: the transforms, sums of groups and digit
recompositions, possibly batched. Its block, rows and columns are the same in every program. -/
def NamedOp.valueFree : NamedOp → Bool
  | .ntt _ _ _ | .inverseNtt _ _ | .nttTranspose _ _ | .sum _ | .fromDigits _ _ => true
  | .batched _ op => op.valueFree
  | _ => false

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

mutual

/-- **Every named operator of an expression reads no value** (`NamedOp.valueFree`). -/
def Expr.opsFree : Expr → Bool
  | .leaf _ | .ref _ => true
  | .add e e' | .sub e e' | .mul e e' | .concat e e' => e.opsFree && e'.opsFree
  | .scale _ e | .reindex _ e | .linear _ e | .prod _ e => e.opsFree
  | .mux b t e => b.opsFree && t.opsFree && e.opsFree
  | .apply op e => op.valueFree && e.opsFree
  | .logic _ _ args => Expr.opsFreeList args

/-- Every named operator of a list of expressions reads no value. -/
def Expr.opsFreeList : List Expr → Bool
  | [] => true
  | e :: es => e.opsFree && Expr.opsFreeList es

end

/-! ## The renaming -/

/-- **A renaming of identifiers**: of values (`val`) and of shared expressions (`ref`). -/
structure Renaming where
  /-- The new identifier of a value. -/
  val : ℕ → ℕ
  /-- The new identifier of a shared expression. -/
  ref : ℕ → ℕ

namespace Renaming

variable (σ : Renaming)

/-- A coefficient, its value renamed. -/
def coef : Coef → Coef
  | .const c => .const c
  | .node v i => .node (σ.val v) i

mutual

/-- **An expression renamed**: its leaves, coefficients' values and references. Named operators
are kept (renamed expressions are read for operators that read no value, `Expr.opsFree`). -/
def expr : Expr → Expr
  | .leaf v => .leaf (σ.val v)
  | .add e e' => .add (expr e) (expr e')
  | .sub e e' => .sub (expr e) (expr e')
  | .scale c e => .scale (σ.coef c) (expr e)
  | .mul e e' => .mul (expr e) (expr e')
  | .reindex idx e => .reindex idx (expr e)
  | .concat e e' => .concat (expr e) (expr e')
  | .linear rows e => .linear (rows.map (·.map fun t => (t.1, σ.coef t.2))) (expr e)
  | .prod n e => .prod n (expr e)
  | .mux b t e => .mux (expr b) (expr t) (expr e)
  | .apply op e => .apply op (expr e)
  | .ref k => .ref (σ.ref k)
  | .logic op w args => .logic op w (exprs args)

/-- A list of expressions renamed. -/
def exprs : List Expr → List Expr
  | [] => []
  | e :: es => expr e :: exprs es

end

/-- **A value's kind renamed**, for the kinds an embedding holds: a bit view's words and a pad
copy's late value renamed, the others kept; `none` for a public expression, an opaque function of
arguments, a message and a bound value. -/
def kind? : Kind → Option Kind
  | .priv => some .priv
  | .pub .input => some (.pub .input)
  | .pub (.opaque n []) => some (.pub (.opaque n []))
  | .constant es => some (.constant es)
  | .challenge c => some (.challenge c)
  | .late => some .late
  | .bits w sel => some (.bits (σ.val w) sel)
  | .padCopy v m => some (.padCopy (σ.val v) m)
  | _ => none

/-- **A value's kind corresponds**: the larger program's kind is the renamed kind (`kind?`). -/
def kindCorr (k k' : Kind) : Bool :=
  match σ.kind? k, k' with
  | some .priv, .priv => true
  | some (.pub .input), .pub .input => true
  | some (.pub (.opaque n [])), .pub (.opaque n' []) => n == n'
  | some (.constant es), .constant es' => es == es'
  | some (.challenge c), .challenge c' => c == c'
  | some .late, .late => true
  | some (.bits w sel), .bits w' sel' => w == w' && decide (sel = sel')
  | some (.padCopy v m), .padCopy v' m' => v == v' && m == m'
  | _, _ => false

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
value's challenge has the same field in both; every shared expression of `R` is renamed to `ir'`'s
entry, reads only values of `V` and entries of `R`, and has no named operator reading a value. -/
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
  /-- A challenge value's challenge has the same field in both programs. -/
  chal : ∀ v ∈ V, ∀ c ∈ (ir.value v).kind.challenge?, ir'.chalField c = ir.chalField c
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
    (∀ v ∈ V, ∀ c ∈ (ir.value v).kind.challenge?, ir'.chalField c = ir.chalField c) ∧
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
`V`; the challenges are `ir'`'s. -/
def pullEnv (σ : Renaming) (V : List ℕ) (e' : ir'.Env I) : ir.Env I where
  stmt v i := if v ∈ V then castElt (e'.stmt (σ.val v) i) else 0
  asg := ⟨fun v i => if v ∈ V then castElt (e'.asg.val (σ.val v) i) else 0,
    fun v i => if v ∈ V then castElt (e'.asg.pad (σ.val v) i) else 0⟩
  chal j i := castElt (e'.chal j i)
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

variable (ir ir') in
/-- **A predicate `equal` of `ir'` is a renamed one of `ir`**: one domain of one field in both,
the renamed sides of `V` and `R`, whose named operators read no value. -/
def equalCorrB (σ : Renaming) (V R : List ℕ) : PredBody → PredBody → Bool
  | .equal d x y _, .equal d' x' y' _ =>
    d == d' && ir'.domainField d == ir.domainField d && (σ.expr x).beq x' && (σ.expr y).beq y' &&
      x.opsFree && y.opsFree && (x.directNodes ++ y.directNodes).all (· ∈ V) &&
      (x.refs ++ y.refs).all (· ∈ R)
  | _, _ => false

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

/-- **A value of `V` lies in its type** in the environment read through the renaming where its
renamed value does. -/
theorem inType_pullEnv (hE : ir.Embedding ir' σ V R) (e' : ir'.Env I) {v : ℕ} (hv : v ∈ V)
    {i : ℕ} (h : (I (ir'.valueField (σ.val v))).InType (ir'.value (σ.val v)).type
      (ir'.reader e' (σ.val v) i)) :
    (I (ir.valueField v)).InType (ir.value v).type (ir.reader (ir.pullEnv σ V e') v i) := by
  obtain ⟨-, -, hf, -, hty, -⟩ := hE.vals v hv
  rw [reader_pullEnv hE e' hv, ← hty]
  exact inType_castElt_of_eq hf _ h

/-- **Environments agreeing on what is fixed when challenge `j` is drawn agree read through the
renaming**, the challenges having the same phases in both programs. -/
theorem eqUpTo_pullEnv (hE : ir.Embedding ir' σ V R)
    (hph : ∀ j, (ir'.challenge j).phase = (ir.challenge j).phase) {j : ℕ} {e₁ e₂ : ir'.Env I}
    (h : Env.EqUpTo j e₁ e₂) : Env.EqUpTo j (ir.pullEnv σ V e₁) (ir.pullEnv σ V e₂) where
  stmt := by simp only [pullEnv, h.stmt]
  asg := by simp only [pullEnv, h.asg]
  chal j' hj := by
    have : ir'.ChalBefore j' j := by
      unfold ChalBefore at hj ⊢
      rwa [hph, hph]
    simp only [pullEnv, h.chal j' this]
  late v hv := by
    funext i
    simp only [pullEnv]
    split_ifs with hvV
    · rw [h.late (σ.val v) (by rw [(hE.vals v hvV).2.2.2.2.2.1, hph]; exact hv)]
    · rfl

end

end GordieHowe.RealizedProgram
