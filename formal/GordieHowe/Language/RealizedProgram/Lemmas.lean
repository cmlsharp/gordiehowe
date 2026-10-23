-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Valid
public import GordieHowe.Headline

@[expose] public section

/-!
# GordieHowe: what the validity items give the proof system

Generic facts about a program (`GordieHowe.RealizedProgram`) that the proof system (`GordieHowe.RealizedProgram.ProofSystem`) consumes:

* **Meaning depends on the reads.** An expression's value depends only on the values it reads,
  directly and through its shared expressions (`Expr.eval_congr`, `GordieHowe.RealizedProgram.refVal_congr`,
  `GordieHowe.RealizedProgram.evalE_congr`, and their integer forms); a value's reading depends only on what it reads
  from the environment (`GordieHowe.RealizedProgram.read_congr`, with `GordieHowe.RealizedProgram.Env.AgreeOn`); so a predicate's truth
  depends only on its computed reads (`GordieHowe.RealizedProgram.holdsAt_congr`), hence on its exported reads under
  `GordieHowe.RealizedProgram.ReadsSound`.
* **Causality and the pad order from `GordieHowe.RealizedProgram.ChallengeOrder` and `GordieHowe.RealizedProgram.PadOrderValid`.** An
  honest computation of the late values that reads only what each late value's exported reads list
  (`GordieHowe.RealizedProgram.RespectsReads`) is computed after its phase's challenge
  (`GordieHowe.RealizedProgram.challengeCausal_of_respectsReads`, from the part of `GordieHowe.RealizedProgram.ChallengeOrder` that bounds
  the challenges a late value reads) and reads only the pads of earlier messages
  (`GordieHowe.RealizedProgram.padOrder_of_respectsReads`, from `GordieHowe.RealizedProgram.PadOrderValid`: the DAG lemma, giving
  `PadMasked` along `MsgBefore`).
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP

/-- An element of an entry of `l.getD i []` is an element of some entry of `l`. -/
theorem exists_mem_of_mem_getD {α : Type} {l : List (List α)} {i : ℕ} {x : α}
    (h : x ∈ l.getD i []) : ∃ row ∈ l, x ∈ row := by
  rw [List.getD_eq_getElem?_getD] at h
  cases hi : l[i]? with
  | none => simp [hi] at h
  | some row =>
    rw [hi, Option.getD_some] at h
    exact ⟨row, List.mem_of_getElem? hi, h⟩

/-- A value of a sparse row's coefficient is a value of the rows' coefficients. -/
theorem mem_rowNodes_of_mem_getD {rows : List (List (ℕ × Coef))} {i : ℕ} {t : ℕ × Coef}
    (ht : t ∈ rows.getD i []) {v : ℕ} (hv : v ∈ t.2.nodes) :
    v ∈ rows.flatMap (·.flatMap fun t => t.2.nodes) := by
  obtain ⟨row, hrow, ht'⟩ := exists_mem_of_mem_getD ht
  exact List.mem_flatMap.2 ⟨row, hrow, List.mem_flatMap.2 ⟨t, ht', hv⟩⟩

/-! ## Expressions depend only on the values they read -/

section Congr

variable (ir : RealizedProgram) {I : Interp}

/-- **A named operator's block depends only on its operands.** -/
theorem NamedOp.block_congr {f : ℕ} {leaf leaf' : ir.Valuation I} :
    ∀ (op : NamedOp), (∀ v ∈ op.operands ++ op.foreignOperands, leaf v = leaf' v) →
      NamedOp.block ir f leaf op = NamedOp.block ir f leaf' op
  | .negacyclicConv h form, hl => by
    simp only [NamedOp.block, hl h (by simp [NamedOp.operands])]
  | .polyMatVec a K L form, hl => by
    simp only [NamedOp.block, hl a (by simp [NamedOp.operands])]
  | .polyBroadcast t K form, hl => by
    simp only [NamedOp.block, hl t (by simp [NamedOp.operands])]
  | .ntt n psi o, _ => by cases o <;> rfl
  | .inverseNtt n psi, _ => rfl
  | .nttTranspose n psi, _ => rfl
  | .rowDot M R W, hl => by
    simp only [NamedOp.block, hl M (by simp [NamedOp.operands])]
  | .macConv r w nch taps, hl => by
    simp only [NamedOp.block, hl r (by simp [NamedOp.foreignOperands])]
  | .acyclicConv h lx, hl => by
    simp only [NamedOp.block, hl h (by simp [NamedOp.operands])]
  | .diagonal d, hl => by
    simp only [NamedOp.block, hl d (by simp [NamedOp.operands])]
  | .scale c, hl => by
    simp only [NamedOp.block, hl c (by simp [NamedOp.operands])]
  | .constDiagonal d, hl => by
    simp only [NamedOp.block, hl d (by simp [NamedOp.operands])]
  | .sum w, _ => rfl
  | .fromDigits k base, _ => rfl
  | .batched b op, hl => by
    have ih := NamedOp.block_congr (f := f) op fun v hv => hl v (by
      simpa [NamedOp.operands, NamedOp.foreignOperands] using hv)
    funext x j
    simp only [NamedOp.block, ih]

/-- A coefficient's value depends only on the values it reads. -/
theorem Coef.eval_congr {f : ℕ} {rd rd' : ir.Valuation I} {c : Coef}
    (h : ∀ v ∈ c.nodes, rd v = rd' v) : Coef.eval ir f rd c = Coef.eval ir f rd' c := by
  cases c with
  | const => rfl
  | node v i => simp only [Coef.eval, h v (by simp [Coef.nodes])]

mutual

/-- **An expression's value depends only on the values and shared expressions it reads
directly.** -/
theorem Expr.eval_congr {f : ℕ} {leaf leaf' : ir.Valuation I} {ref ref' : ℕ → ℕ → (I f).K}
    {rl : ℕ → ℕ} : ∀ (e : Expr), (∀ v ∈ e.directNodes, leaf v = leaf' v) →
      (∀ k ∈ e.refs, ref k = ref' k) →
      Expr.eval ir f leaf ref rl e = Expr.eval ir f leaf' ref' rl e
  | .leaf v, h, _ => by
    funext i
    simp only [Expr.eval, h v (by simp [Expr.directNodes])]
  | .add e e', h, hr | .sub e e', h, hr | .mul e e', h, hr | .concat e e', h, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr
    funext i
    simp only [Expr.eval, Expr.eval_congr e (fun v hv => h v (.inl hv)) (fun k hk => hr k (.inl hk)),
      Expr.eval_congr e' (fun v hv => h v (.inr hv)) (fun k hk => hr k (.inr hk))]
  | .scale c e, h, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr
    funext i
    simp only [Expr.eval, Expr.eval_congr e (fun v hv => h v (.inr hv)) hr,
      Coef.eval_congr ir (f := f) fun v hv => h v (.inl hv)]
  | .reindex idx e, h, hr => by
    simp only [Expr.directNodes, Expr.refs] at h hr
    funext i
    simp only [Expr.eval, Expr.eval_congr e h hr]
  | .prod n e, h, hr => by
    simp only [Expr.directNodes, Expr.refs] at h hr
    funext i
    simp only [Expr.eval, Expr.eval_congr e h hr]
  | .linear rows e, h, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr
    funext i
    simp only [Expr.eval, Expr.eval_congr e (fun v hv => h v (.inr hv)) hr]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    rw [Coef.eval_congr ir (f := f) fun v hv => h v (.inl (mem_rowNodes_of_mem_getD ht hv))]
  | .mux b t e, h, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr
    funext i
    simp only [Expr.eval, Expr.eval_congr b (fun v hv => h v (.inl (.inl hv)))
        (fun k hk => hr k (.inl (.inl hk))),
      Expr.eval_congr t (fun v hv => h v (.inl (.inr hv))) (fun k hk => hr k (.inl (.inr hk))),
      Expr.eval_congr e (fun v hv => h v (.inr hv)) (fun k hk => hr k (.inr hk))]
  | .apply op e, h, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr
    funext i
    simp only [Expr.eval, NamedOp.apply, Expr.eval_congr e (fun v hv => h v (.inr hv)) hr,
      NamedOp.block_congr ir op fun v hv => h v (.inl (List.mem_append.1 hv))]
  | .ref k, _, hr => by
    funext i
    simp only [Expr.eval, hr k (by simp [Expr.refs])]
  | .logic op w args, h, hr => by
    simp only [Expr.directNodes, Expr.refs] at h hr
    funext i
    simp only [Expr.eval, Expr.evalList_congr args h hr]

/-- The values of a list of expressions depend only on what they read directly. -/
theorem Expr.evalList_congr {f : ℕ} {leaf leaf' : ir.Valuation I} {ref ref' : ℕ → ℕ → (I f).K}
    {rl : ℕ → ℕ} : ∀ (es : List Expr), (∀ v ∈ Expr.directNodesList es, leaf v = leaf' v) →
      (∀ k ∈ Expr.refsList es, ref k = ref' k) →
      Expr.evalList ir f leaf ref rl es = Expr.evalList ir f leaf' ref' rl es
  | [], _, _ => rfl
  | e :: es, h, hr => by
    simp only [Expr.directNodesList, Expr.refsList, List.mem_append] at h hr
    simp only [Expr.evalList, Expr.eval_congr e (fun v hv => h v (.inl hv)) (fun k hk => hr k (.inl hk)),
      Expr.evalList_congr es (fun v hv => h v (.inr hv)) (fun k hk => hr k (.inr hk))]

end

/-- **A named operator on the integers depends only on its operands.** -/
theorem NamedOp.applyInt_congr {f : ℕ} {leaf leaf' : ir.Valuation I} (op : NamedOp)
    (h : ∀ v ∈ op.operands ++ op.foreignOperands, leaf v = leaf' v) :
    NamedOp.applyInt ir f leaf op = NamedOp.applyInt ir f leaf' op := by
  funext x j
  simp only [NamedOp.applyInt, NamedOp.block_congr ir op h]

/-- A coefficient's integer value depends only on the values it reads. -/
theorem Coef.evalInt_congr {f : ℕ} {rd rd' : ℕ → ℕ → ℤ} {c : Coef}
    (h : ∀ v ∈ c.nodes, rd v = rd' v) :
    Coef.evalInt (I := I) f rd c = Coef.evalInt (I := I) f rd' c := by
  cases c with
  | const => rfl
  | node v i => simp only [Coef.evalInt, h v (by simp [Coef.nodes])]

mutual

/-- **An expression's integer value depends only on the values and shared expressions it reads
directly.** -/
theorem Expr.evalInt_congr {f : ℕ} {leaf leaf' : ir.Valuation I} {il il' : ℕ → ℕ → ℤ}
    {ref ref' : ℕ → ℕ → ℤ} {rl : ℕ → ℕ} : ∀ (e : Expr),
      (∀ v ∈ e.directNodes, leaf v = leaf' v ∧ il v = il' v) → (∀ k ∈ e.refs, ref k = ref' k) →
      Expr.evalInt ir f leaf il ref rl e = Expr.evalInt ir f leaf' il' ref' rl e
  | .leaf v, h, _ => by
    funext i
    simp only [Expr.evalInt, (h v (by simp [Expr.directNodes])).2]
  | .add e e', h, hr | .sub e e', h, hr | .mul e e', h, hr | .concat e e', h, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr
    funext i
    simp only [Expr.evalInt, Expr.evalInt_congr e (fun v hv => h v (.inl hv))
        (fun k hk => hr k (.inl hk)),
      Expr.evalInt_congr e' (fun v hv => h v (.inr hv)) (fun k hk => hr k (.inr hk))]
  | .scale c e, h, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr
    funext i
    simp only [Expr.evalInt, Expr.evalInt_congr e (fun v hv => h v (.inr hv)) hr,
      Coef.evalInt_congr (I := I) (f := f) fun v hv => (h v (.inl hv)).2]
  | .reindex idx e, h, hr => by
    simp only [Expr.directNodes, Expr.refs] at h hr
    funext i
    simp only [Expr.evalInt, Expr.evalInt_congr e h hr]
  | .prod n e, h, hr => by
    simp only [Expr.directNodes, Expr.refs] at h hr
    funext i
    simp only [Expr.evalInt, Expr.evalInt_congr e h hr]
  | .linear rows e, h, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr
    funext i
    simp only [Expr.evalInt, Expr.evalInt_congr e (fun v hv => h v (.inr hv)) hr]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    rw [Coef.evalInt_congr (I := I) (f := f) fun v hv =>
      (h v (.inl (mem_rowNodes_of_mem_getD ht hv))).2]
  | .mux b t e, h, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr
    funext i
    simp only [Expr.evalInt, Expr.evalInt_congr b (fun v hv => h v (.inl (.inl hv)))
        (fun k hk => hr k (.inl (.inl hk))),
      Expr.evalInt_congr t (fun v hv => h v (.inl (.inr hv))) (fun k hk => hr k (.inl (.inr hk))),
      Expr.evalInt_congr e (fun v hv => h v (.inr hv)) (fun k hk => hr k (.inr hk))]
  | .apply op e, h, hr => by
    simp only [Expr.directNodes, Expr.refs, List.mem_append] at h hr
    funext i
    simp only [Expr.evalInt, Expr.evalInt_congr e (fun v hv => h v (.inr hv)) hr,
      NamedOp.applyInt_congr ir op fun v hv => (h v (.inl (List.mem_append.1 hv))).1]
  | .ref k, _, hr => by
    funext i
    simp only [Expr.evalInt, hr k (by simp [Expr.refs])]
  | .logic op w args, h, hr => by
    simp only [Expr.directNodes, Expr.refs] at h hr
    funext i
    simp only [Expr.evalInt, Expr.evalIntList_congr args h hr]

/-- The integer values of a list of expressions depend only on what they read directly. -/
theorem Expr.evalIntList_congr {f : ℕ} {leaf leaf' : ir.Valuation I} {il il' : ℕ → ℕ → ℤ}
    {ref ref' : ℕ → ℕ → ℤ} {rl : ℕ → ℕ} : ∀ (es : List Expr),
      (∀ v ∈ Expr.directNodesList es, leaf v = leaf' v ∧ il v = il' v) →
      (∀ k ∈ Expr.refsList es, ref k = ref' k) →
      Expr.evalIntList ir f leaf il ref rl es = Expr.evalIntList ir f leaf' il' ref' rl es
  | [], _, _ => rfl
  | e :: es, h, hr => by
    simp only [Expr.directNodesList, Expr.refsList, List.mem_append] at h hr
    simp only [Expr.evalIntList, Expr.evalInt_congr e (fun v hv => h v (.inl hv))
        (fun k hk => hr k (.inl hk)),
      Expr.evalIntList_congr es (fun v hv => h v (.inr hv)) (fun k hk => hr k (.inr hk))]

end

end Congr

section

variable {ir : RealizedProgram} {I : Interp}

/-! ## Through the shared expressions -/

/-- A value read by a shared expression `k'` that entry `k` reads is read by entry `k`. -/
theorem refClosure_mono_ref {α : Type} {g : Expr → List α} {n k k' : ℕ}
    (hk : k' ∈ (ir.expr k).refs) {x : α} (hx : x ∈ ir.refClosure g n k') :
    x ∈ ir.refClosure g (n + 1) k :=
  List.mem_append_right _ (List.mem_flatMap.2 ⟨k', hk, hx⟩)

/-- **A shared expression's value depends only on the values it reads.** -/
theorem refVal_congr {leaf leaf' : ir.Valuation I} {f : ℕ} :
    ∀ n k, (∀ v ∈ ir.refClosure Expr.directNodes n k, leaf v = leaf' v) →
      ir.refVal leaf n f k = ir.refVal leaf' n f k
  | 0, _, _ => rfl
  | n + 1, k, h => by
    funext i
    simp only [refVal]
    rw [Expr.eval_congr ir (ir.expr k) (fun v hv => h v (List.mem_append_left _ hv))
      fun k' hk' => refVal_congr n k' fun v hv => h v (refClosure_mono_ref hk' hv)]

/-- **An expression's value depends only on the values it reads**, through its shared
expressions (`RealizedProgram.exprNodes`). -/
theorem evalE_congr {leaf leaf' : ir.Valuation I} {f : ℕ} {e : Expr}
    (h : ∀ v ∈ ir.exprNodes e, leaf v = leaf' v) : ir.evalE leaf f e = ir.evalE leaf' f e := by
  funext i
  simp only [evalE]
  rw [Expr.eval_congr ir e (fun v hv => h v (List.mem_append_left _ hv))
    fun k hk => refVal_congr _ k fun v hv =>
      h v (List.mem_append_right _ (List.mem_flatMap.2 ⟨k, hk, hv⟩))]

/-- **A value's integer reading depends only on its reading.** -/
theorem intOf_congr {rd rd' : ir.Valuation I} {v : ℕ} (h : rd v = rd' v) :
    ir.intOf rd v = ir.intOf rd' v := by
  funext j
  simp only [intOf, h]

/-- **A shared expression's integer value depends only on the values it reads.** -/
theorem refInt_congr {rd rd' : ir.Valuation I} {f : ℕ} :
    ∀ n k, (∀ v ∈ ir.refClosure Expr.directNodes n k, rd v = rd' v) →
      ir.refInt rd f n k = ir.refInt rd' f n k
  | 0, _, _ => rfl
  | n + 1, k, h => by
    funext i
    simp only [refInt]
    rw [Expr.evalInt_congr ir (il := ir.intOf rd) (il' := ir.intOf rd') (ir.expr k)
      (fun v hv => ⟨h v (List.mem_append_left _ hv), intOf_congr (h v (List.mem_append_left _ hv))⟩)
      fun k' hk' => refInt_congr n k' fun v hv => h v (refClosure_mono_ref hk' hv)]

/-- **An expression's integer value depends only on the values it reads.** -/
theorem evalIntWith_congr {rd rd' : ir.Valuation I} {d : ℕ} {e : Expr}
    (h : ∀ v ∈ ir.exprNodes e, rd v = rd' v) : ir.evalIntWith rd d e = ir.evalIntWith rd' d e := by
  funext i
  simp only [evalIntWith]
  rw [Expr.evalInt_congr ir (il := ir.intOf rd) (il' := ir.intOf rd') e
    (fun v hv => ⟨h v (List.mem_append_left _ hv), intOf_congr (h v (List.mem_append_left _ hv))⟩)
    fun k hk => refInt_congr _ k fun v hv =>
      h v (List.mem_append_right _ (List.mem_flatMap.2 ⟨k, hk, hv⟩))]

/-! ## Predicates depend only on the values they read -/

/-- **A predicate's truth depends only on the values it reads** (`RealizedProgram.predNodes`). -/
theorem holdsWith_congr {rd rd' : ir.Valuation I} {b : PredBody}
    (h : ∀ v ∈ ir.predNodes b, rd v = rd' v) : ir.HoldsWith rd b ↔ ir.HoldsWith rd' b := by
  have hx : ∀ d e, (d, e) ∈ b.exprs → ∀ v ∈ ir.exprNodes e, rd v = rd' v := fun d e hde v hv =>
    h v (List.mem_append_left _ (List.mem_flatMap.2 ⟨(d, e), hde, hv⟩))
  have hev : ∀ d e, (d, e) ∈ b.exprs → ir.evalWith rd d e = ir.evalWith rd' d e :=
    fun d e hde => funext fun i => congrFun (evalE_congr (f := ir.domainField d) (hx d e hde)) i
  have hint : ∀ d e, (d, e) ∈ b.exprs → ir.evalIntWith rd d e = ir.evalIntWith rd' d e :=
    fun d e hde => evalIntWith_congr (hx d e hde)
  cases b with
  | equal d e e' t =>
    simp only [HoldsWith, hev d e (by simp [PredBody.exprs]), hev d e' (by simp [PredBody.exprs])]
  | mod d q e e' real =>
    simp only [HoldsWith, hint d e (by simp [PredBody.exprs]),
      hint d e' (by simp [PredBody.exprs])]
  | cross dx x dy y k real =>
    simp only [HoldsWith, hev dx x (by simp [PredBody.exprs]), hev dy y (by simp [PredBody.exprs])]
  | mem d records set real =>
    have hr : ∀ e ∈ records, ir.evalWith rd d e = ir.evalWith rd' d e := fun e he =>
      hev d e (List.mem_map_of_mem (List.mem_append_left _ he))
    simp only [HoldsWith]
    refine forall₂_congr fun i _ => ?_
    have hrows : ∀ rows, (∀ u ∈ (match rows with
          | TableRows.columns cols => cols
          | TableRows.range _ => []
          | TableRows.expr e' => ir.exprNodes e'), rd u = rd' u) →
        (ir.InRows rd d records i rows ↔ ir.InRows rd' d records i rows) := by
      intro rows hc
      cases rows with
      | range n => exact forall₂_congr fun e he => by rw [hr e he]
      | columns cols =>
        refine exists_congr fun j => and_congr_right fun _ => forall₂_congr fun ec hec => ?_
        rw [hr ec.1 (List.of_mem_zip hec).1, hc ec.2 (List.of_mem_zip hec).2]
      | expr e' =>
        have he' : ir.evalWith rd d e' = ir.evalWith rd' d e' := funext fun j =>
          congrFun (evalE_congr (f := ir.domainField d) hc) j
        exact forall₂_congr fun e he => by rw [hr e he, he']
    cases set with
    | range n => exact hrows (.range n) fun _ hu => nomatch hu
    | table t =>
      refine hrows _ fun u hu => h u (List.mem_append_right _ ?_)
      simp only [tableCols]
      exact hu
    | expr e' =>
      exact hrows (.expr e') fun u hu => hx d e' (List.mem_map_of_mem (by simp)) u hu

/-! ## Values depend only on what they read from the environment -/

/-- **Two environments agree on the reads `R`**: they have one statement and one committed
assignment, and agree on every challenge and every late value in `R`. -/
structure Env.AgreeOn (R : List Read) (e e' : ir.Env I) : Prop where
  /-- The statements agree. -/
  stmt : e.stmt = e'.stmt
  /-- The committed assignments agree. -/
  asg : e.asg = e'.asg
  /-- The challenges agree. -/
  chal : ∀ c, Read.chal c ∈ R → e.chal c = e'.chal c
  /-- The late values agree. -/
  late : ∀ v, Read.late v ∈ R → e.late v = e'.late v

/-- Environments agreeing on reads agree on fewer reads. -/
theorem Env.AgreeOn.mono {R R' : List Read} {e e' : ir.Env I} (h : Env.AgreeOn R e e')
    (hsub : ∀ rd ∈ R', rd ∈ R) : Env.AgreeOn R' e e' :=
  ⟨h.stmt, h.asg, fun c hc => h.chal c (hsub _ hc), fun v hv => h.late v (hsub _ hv)⟩

/-- **A value's reading depends only on what it reads from the environment**
(`RealizedProgram.nodeReads`). -/
theorem read_congr {e e' : ir.Env I} :
    ∀ n v, Env.AgreeOn (ir.nodeReads n v) e e' → ir.read e n v = ir.read e' n v
  | 0, _, _ => rfl
  | n + 1, v, h => by
    funext i
    have hstmt := h.stmt
    have hasg := h.asg
    rcases hk : (ir.value v).kind with _ | ⟨_ | ⟨name, args⟩ | x⟩ | es | c | _ | ⟨w, sel⟩ | ⟨u, m⟩ |
      u <;> simp only [nodeReads, hk] at h <;> simp only [read, hk, hstmt, hasg]
    · have hargs : args.map (fun u j => (I (ir.valueField u)).toNat (ir.read e n u j)) =
          args.map (fun u j => (I (ir.valueField u)).toNat (ir.read e' n u j)) :=
        List.map_congr_left fun u hu => by
          rw [read_congr n u (h.mono fun rd hrd => List.mem_flatMap.2 ⟨u, hu, hrd⟩)]
      rw [hargs]
    · exact congrFun (evalE_congr fun u hu => read_congr n u
        (h.mono fun rd hrd => List.mem_flatMap.2 ⟨u, hu, hrd⟩)) i
    · rw [h.chal c (List.mem_singleton_self _)]
    · rw [h.late v (List.mem_singleton_self _)]
    · simp only [bitView, read_congr n w h]
    · rw [h.late u (List.mem_singleton_self _)]

/-- **A predicate's truth depends only on what it reads from the environment**
(`RealizedProgram.predReads`). -/
theorem holdsAt_congr {e e' : ir.Env I} {b : PredBody} (h : Env.AgreeOn (ir.predReads b) e e') :
    ir.HoldsAt e b ↔ ir.HoldsAt e' b :=
  holdsWith_congr fun v hv => read_congr _ v
    (h.mono fun _ hrd => List.mem_flatMap.2 ⟨v, hv, hrd⟩)

/-! ## The challenge-use rule of `RealizedProgram.ChallengeOrder` -/

/-- **The challenge values are fixed through phase `k + 1`**: challenge vectors agreeing on the
indices up to `k` agree on every challenge of phase at most `k + 1`. -/
theorem chalRead_eq_of_le {c c' : ∀ k, (ir.layout I).Ch k} {k : Fin ir.phases}
    (h : ∀ k' ≤ k, c k' = c' k') {j : ℕ} (hj : (ir.challenge j).phase ≤ k + 1) :
    ir.chalRead I c j = ir.chalRead I c' j := by
  funext i
  unfold chalRead
  split_ifs with hv
  · rw [h ⟨(ir.challenge j).phase - 1, by omega⟩ (Fin.le_def.2 (by simp only; omega))]
  · rfl

/-- **The phase of a late value of the layout.** -/
theorem layout_phase (l : (ir.layout I).Late) :
    ((ir.layout I).phase l : ℕ) = (ir.value l.1).phase - 1 :=
  rfl

/-- **The messages are fixed before phase `k + 1`**: runs agreeing on the messages of indices below
`k` agree on every late value of phase at most `k`. -/
theorem msgRead_eq_of_lt {r r' : (ir.layout I).Run} {k : Fin ir.phases}
    (h : ∀ l, (ir.layout I).phase l < k → r.msg l = r'.msg l) {u : ℕ}
    (hu : (ir.value u).phase < k + 1) : ir.msgRead I r u = ir.msgRead I r' u := by
  funext i
  unfold msgRead
  split_ifs with hv
  · rw [h ⟨⟨u, hv.1⟩, hv.2.1⟩ (Fin.lt_def.2 (by
    have h1 := hv.2.1.2.1
    change (ir.value u).phase - 1 < (k : ℕ)
    omega))]
  · rfl

/-! ## Causality and the pad order from `RealizedProgram.ChallengeOrder` and `RealizedProgram.PadOrderValid` -/

/-- **An honest computation of the late values reads only what each late value's exported reads
list**: its value at late value `l` is unchanged when the challenges `l` reads and the pads `l`
reads are unchanged. -/
def RespectsReads
    (late : (∀ k, (ir.layout I).Ch k) → (ir.layout I).Pads → ∀ l, (ir.layout I).Mask l) : Prop :=
  ∀ (l : ir.Late) ⦃c c' : ∀ k, (ir.layout I).Ch k⦄ ⦃π π' : (ir.layout I).Pads⦄,
    (∀ j, Read.chal j ∈ (ir.value l.1).reads → ir.chalRead I c j = ir.chalRead I c' j) →
    (∀ u : ir.Late, Read.pad u.1 ∈ (ir.value l.1).reads → π u = π' u) →
      late c π l = late c' π' l

/-- **Late values are computed after their phase's challenge** (`RealizedProgram.ChallengeOrder`: a late
value of phase `k` reads only challenges of phases at most `k`): an honest computation that respects
the exported reads is challenge-causal at every pad vector. -/
theorem challengeCausal_of_respectsReads (horder : ir.ChallengeOrder)
    {late : (∀ k, (ir.layout I).Ch k) → (ir.layout I).Pads → ∀ l, (ir.layout I).Mask l}
    (hl : ir.RespectsReads late) (π : (ir.layout I).Pads) :
    (ir.layout I).ChallengeCausal fun c => late c π := by
  intro l c c' hc
  have hlate : ir.IsLate l.1 := l.2
  refine hl l (fun j hj => chalRead_eq_of_le hc ?_) fun _ _ => rfl
  have hle : (ir.challenge j).phase ≤ (ir.value l.1).phase :=
    horder.late l.1 l.1.2 hlate.1 _ hj
  rw [layout_phase]
  omega

/-- **The message order on the layout is the message order on identifiers.** -/
theorem msgBefore_iff (u l : ir.Late) :
    (ir.layout I).MsgBefore u l ↔ ir.MsgBeforeId u.1 l.1 := by
  have hu : ir.IsLate u.1 := u.2
  have hl : ir.IsLate l.1 := l.2
  unfold IsLate at hu hl
  unfold ProofSystem.PhaseLayout.MsgBefore MsgBeforeId
  simp only [Prod.Lex.toLex_lt_toLex, Fin.lt_def, Fin.ext_iff]
  rw [show u < l ↔ (u.1 : ℕ) < l.1 from Iff.rfl]
  omega

/-- **The pad order from `RealizedProgram.PadOrderValid`** (the DAG lemma): an honest computation that
respects the exported reads, whose pad reads are pads of strictly earlier messages, reads only the
pads of earlier messages in `MsgBefore` order (`PadMasked`), at every challenge vector. -/
theorem padOrder_of_respectsReads (hpads : ir.PadOrderValid)
    {late : (∀ k, (ir.layout I).Ch k) → (ir.layout I).Pads → ∀ l, (ir.layout I).Mask l}
    (hl : ir.RespectsReads late) : (ir.layout I).PadOrder late := by
  intro c l π π' hπ
  have hlate : ir.IsLate l.1 := l.2
  refine hl l (fun _ _ => rfl) fun u hu => hπ u ?_
  obtain ⟨-, -, -, hb⟩ := hpads l.1 l.1.2 hlate.1 u.1 (List.mem_filterMap.2 ⟨_, hu, rfl⟩)
  exact (msgBefore_iff u l).2 hb

/-- **Paper `lem:phases` (3) for a program**: under `RealizedProgram.PadOrderValid`, an honest computation
of the late values that respects the exported reads sends, under uniform challenges and uniform
pads, a run with the law of the uniform simulator, which draws every challenge and every message (in
the masking space of its pad) uniformly and independently (`PadOrder.honestRun_uniform` at
`padOrder_of_respectsReads`). -/
@[headline]
theorem honestRun_uniform_of_respectsReads (hpads : ir.PadOrderValid)
    {late : (∀ k, (ir.layout I).Ch k) → (ir.layout I).Pads → ∀ l, (ir.layout I).Mask l}
    (hl : ir.RespectsReads late) :
    Uniform fun x : (∀ k, (ir.layout I).Ch k) × (ir.layout I).Pads =>
      (ir.layout I).honestRun late x.1 x.2 :=
  (padOrder_of_respectsReads hpads hl).honestRun_uniform

end

end GordieHowe.RealizedProgram
