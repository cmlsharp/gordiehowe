-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.CircuitInput
public import GordieHowe.ProofSystem.GKR.Rel
public import GordieHoweNative.ProofSystem.GKR.RelCert
public import GordieHoweNative.Data
public import GordieHoweNative.Language.Realizations.Circuit.Emit

@[expose] public section

/-!
# GordieHowe: the emitted expression DAG (the node table)

A GKR circuit's emitter walks, per circuit entry, the C++ expression DAG
(`lib/gordiehowe/expr.h`, `ExprEmitter::operator()`) and reads values through their placements
(`lib/gordiehowe/compiler/compiled_domain.h`, `CompiledDomain::view`). The exporter writes the trees
it walked as a *node table*: one node per `ExprOp` or value read, in completion order (kids below
their node), with the facts the printed Lean `Expr` drops (chain flattening, the mux's Bit flag, an
NTT's stage mask, `materialize`, the `.ref` a node is printed as) and, per coordinate, the wire
(`GKR.Rel.Wire`) the emitter produced for it. This file holds the table, its meaning and its check
against the printed program; the relational check of the wires is `Circuit/RelTable.lean`.

* **Substituting shared expressions** (`GordieHowe.RealizedProgram.Expr.substRefs`): every
  `.ref k` replaced by an expression; its length and value read the replacements' lengths and
  values (`Expr.len_substRefs`, `Expr.eval_substRefs`).
* **The nodes** (`GordieHowe.RealizedProgram.ENode`, `GordieHowe.RealizedProgram.ENodeInfo`) and
  the table (`GordieHowe.RealizedProgram.ETable`, a trie by id). A node's *row*
  (`GordieHowe.RealizedProgram.ENode.row`) is its printed form one level deep, each kid `a` written
  `.ref a`. The leaf is a value read through its placement (`ENode.value`, printed `.leaf u`); a
  derived value printed `.ref j` is the node computing its definition, marked
  `ENodeInfo.ref = some j`. A realization's raw-call results are no nodes: its entry's family
  record holds their wires (`GKR.Rel.FamCert`).
* **Rendering** (`GordieHowe.RealizedProgram.ETable.render`): a node's row with every kid rendered
  in turn: with no `.ref` (`ETable.treeErase`), or stopping at a node printed as `.ref j`
  (`ETable.print`). The meaning of a node (`GordieHowe.RealizedProgram.nodeSem`) is its erased
  tree's value; it unfolds one level per node (`GordieHowe.RealizedProgram.nodeSem_eq`).
* **The check** (`GordieHowe.RealizedProgram.ETable.eqB`,
  `GordieHowe.RealizedProgram.emitTableOkB`): a printed expression is the node's print; once per
  table, every node's kids lie below it, its length is its row's, and a node printed as `.ref j`
  has the shared expression `j` as its row.
  Its lemma (`GordieHowe.RealizedProgram.eqB_sound`): the printed expression has the node's length
  and meaning.
* **Chain combines**: a chain node's meaning is its combine of its kids'
  (`GordieHowe.RealizedProgram.BinOp.sem`, `GordieHowe.RealizedProgram.nodeSem_bin`), every combine
  associative (`BinOp.sem_assoc`).
* **The environment** (`GordieHowe.RealizedProgram.TEnv`): the constant table, the code
  arithmetic, the codes of `−1` and `1/2`, the characteristic-two flag and the input count, its
  codes checked once per circuit (`TEnv.arithB`, `TEnv.arithOk_of_arithB`).

The definitions are in `GordieHoweNative/Language/Realizations/Circuit/Emit.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

/-! ## Substituting shared expressions -/

mutual

/-- **A substitution depends only on the replacements of the references read.** -/
theorem Expr.substRefs_congr {g g' : ℕ → Expr} :
    ∀ e : Expr, (∀ k ∈ e.refs, g k = g' k) → e.substRefs g = e.substRefs g'
  | .leaf _, _ => rfl
  | .add e e', h | .sub e e', h | .mul e e', h | .concat e e', h => by
    simp only [Expr.refs, List.mem_append] at h
    simp only [Expr.substRefs, Expr.substRefs_congr e fun k hk => h k (.inl hk),
      Expr.substRefs_congr e' fun k hk => h k (.inr hk)]
  | .scale _ e, h | .reindex _ e, h | .linear _ e, h | .prod _ e, h | .apply _ e, h => by
    simp only [Expr.refs] at h
    simp only [Expr.substRefs, Expr.substRefs_congr e h]
  | .mux b t e, h => by
    simp only [Expr.refs, List.mem_append] at h
    simp only [Expr.substRefs, Expr.substRefs_congr b fun k hk => h k (.inl (.inl hk)),
      Expr.substRefs_congr t fun k hk => h k (.inl (.inr hk)),
      Expr.substRefs_congr e fun k hk => h k (.inr hk)]
  | .ref k, h => by simp only [Expr.substRefs, h k (by simp [Expr.refs])]
  | .logic _ _ args, h => by
    simp only [Expr.refs] at h
    simp only [Expr.substRefs, Expr.substRefsList_congr args h]

/-- A substitution in a list depends only on the replacements of the references read. -/
theorem Expr.substRefsList_congr {g g' : ℕ → Expr} :
    ∀ es : List Expr, (∀ k ∈ Expr.refsList es, g k = g' k) →
      Expr.substRefsList g es = Expr.substRefsList g' es
  | [], _ => rfl
  | e :: es, h => by
    simp only [Expr.refsList, List.mem_append] at h
    simp only [Expr.substRefsList, Expr.substRefs_congr e fun k hk => h k (.inl hk),
      Expr.substRefsList_congr es fun k hk => h k (.inr hk)]

end

section Subst

variable (ir : RealizedProgram) {I : Interp}

mutual

/-- **The length of a substitution** reads the replacements' lengths. -/
theorem Expr.len_substRefs (rl : ℕ → ℕ) (g : ℕ → Expr) :
    ∀ e : Expr, Expr.len ir rl (e.substRefs g) = Expr.len ir (fun k => Expr.len ir rl (g k)) e
  | .leaf _ => by simp only [Expr.substRefs, Expr.len]
  | .add e _ | .sub e _ | .mul e _ => by
    simp only [Expr.substRefs, Expr.len, Expr.len_substRefs rl g e]
  | .scale _ e | .prod _ e | .apply _ e => by
    simp only [Expr.substRefs, Expr.len, Expr.len_substRefs rl g e]
  | .reindex _ _ | .linear _ _ => by simp only [Expr.substRefs, Expr.len]
  | .concat e e' => by
    simp only [Expr.substRefs, Expr.len, Expr.len_substRefs rl g e, Expr.len_substRefs rl g e']
  | .mux _ t _ => by simp only [Expr.substRefs, Expr.len, Expr.len_substRefs rl g t]
  | .ref _ => by simp only [Expr.substRefs, Expr.len]
  | .logic _ _ args => by simp only [Expr.substRefs, Expr.len, Expr.lenList_substRefs rl g args]

/-- The lengths of a substituted list read the replacements' lengths. -/
theorem Expr.lenList_substRefs (rl : ℕ → ℕ) (g : ℕ → Expr) :
    ∀ es : List Expr, Expr.lenList ir rl (Expr.substRefsList g es) =
      Expr.lenList ir (fun k => Expr.len ir rl (g k)) es
  | [] => rfl
  | e :: es => by
    simp only [Expr.substRefsList, Expr.lenList, Expr.len_substRefs rl g e,
      Expr.lenList_substRefs rl g es]

end

mutual

/-- **The value of a substitution** reads the replacements' values and lengths. -/
theorem Expr.eval_substRefs {f : ℕ} (leaf : ir.Valuation I) (ref : ℕ → ℕ → (I f).K)
    (rl : ℕ → ℕ) (g : ℕ → Expr) :
    ∀ e : Expr, Expr.eval ir f leaf ref rl (e.substRefs g) =
      Expr.eval ir f leaf (fun k => Expr.eval ir f leaf ref rl (g k))
        (fun k => Expr.len ir rl (g k)) e
  | .leaf _ => by simp only [Expr.substRefs, Expr.eval]
  | .add e e' | .sub e e' | .mul e e' => by
    funext i
    simp only [Expr.substRefs, Expr.eval, Expr.eval_substRefs leaf ref rl g e,
      Expr.eval_substRefs leaf ref rl g e']
  | .concat e e' => by
    funext i
    simp only [Expr.substRefs, Expr.eval, Expr.eval_substRefs leaf ref rl g e,
      Expr.eval_substRefs leaf ref rl g e', Expr.len_substRefs]
  | .scale _ e | .reindex _ e | .linear _ e | .prod _ e | .apply _ e => by
    funext i
    simp only [Expr.substRefs, Expr.eval, Expr.eval_substRefs leaf ref rl g e]
  | .mux b t e => by
    funext i
    simp only [Expr.substRefs, Expr.eval, Expr.eval_substRefs leaf ref rl g b,
      Expr.eval_substRefs leaf ref rl g t, Expr.eval_substRefs leaf ref rl g e]
  | .ref _ => by simp only [Expr.substRefs, Expr.eval]
  | .logic _ _ args => by
    funext i
    simp only [Expr.substRefs, Expr.eval, Expr.evalList_substRefs leaf ref rl g args]

/-- The values of a substituted list read the replacements' values and lengths. -/
theorem Expr.evalList_substRefs {f : ℕ} (leaf : ir.Valuation I) (ref : ℕ → ℕ → (I f).K)
    (rl : ℕ → ℕ) (g : ℕ → Expr) :
    ∀ es : List Expr, Expr.evalList ir f leaf ref rl (Expr.substRefsList g es) =
      Expr.evalList ir f leaf (fun k => Expr.eval ir f leaf ref rl (g k))
        (fun k => Expr.len ir rl (g k)) es
  | [] => rfl
  | e :: es => by
    simp only [Expr.substRefsList, Expr.evalList, Expr.eval_substRefs leaf ref rl g e,
      Expr.evalList_substRefs leaf ref rl g es]

end

mutual

/-- **An expression's value depends only on the lengths of the shared expressions it reads.** -/
theorem Expr.eval_congr_len {f : ℕ} {leaf : ir.Valuation I} {ref : ℕ → ℕ → (I f).K}
    {rl rl' : ℕ → ℕ} :
    ∀ e : Expr, (∀ k ∈ e.refs, rl k = rl' k) →
      Expr.eval ir f leaf ref rl e = Expr.eval ir f leaf ref rl' e
  | .leaf _, _ => rfl
  | .add e e', h | .sub e e', h | .mul e e', h => by
    simp only [Expr.refs, List.mem_append] at h
    funext i
    simp only [Expr.eval, Expr.eval_congr_len e fun k hk => h k (.inl hk),
      Expr.eval_congr_len e' fun k hk => h k (.inr hk)]
  | .concat e e', h => by
    simp only [Expr.refs, List.mem_append] at h
    funext i
    simp only [Expr.eval, Expr.eval_congr_len e fun k hk => h k (.inl hk),
      Expr.eval_congr_len e' fun k hk => h k (.inr hk),
      Expr.len_congr ir e fun k hk => h k (.inl hk)]
  | .scale _ e, h | .reindex _ e, h | .linear _ e, h | .prod _ e, h | .apply _ e, h => by
    simp only [Expr.refs] at h
    funext i
    simp only [Expr.eval, Expr.eval_congr_len e h]
  | .mux b t e, h => by
    simp only [Expr.refs, List.mem_append] at h
    funext i
    simp only [Expr.eval, Expr.eval_congr_len b fun k hk => h k (.inl (.inl hk)),
      Expr.eval_congr_len t fun k hk => h k (.inl (.inr hk)),
      Expr.eval_congr_len e fun k hk => h k (.inr hk)]
  | .ref _, _ => rfl
  | .logic _ _ args, h => by
    simp only [Expr.refs] at h
    funext i
    simp only [Expr.eval, Expr.evalList_congr_len args h]

/-- The values of a list depend only on the lengths of the shared expressions they read. -/
theorem Expr.evalList_congr_len {f : ℕ} {leaf : ir.Valuation I} {ref : ℕ → ℕ → (I f).K}
    {rl rl' : ℕ → ℕ} :
    ∀ es : List Expr, (∀ k ∈ Expr.refsList es, rl k = rl' k) →
      Expr.evalList ir f leaf ref rl es = Expr.evalList ir f leaf ref rl' es
  | [], _ => rfl
  | e :: es, h => by
    simp only [Expr.refsList, List.mem_append] at h
    simp only [Expr.evalList, Expr.eval_congr_len e fun k hk => h k (.inl hk),
      Expr.evalList_congr_len es fun k hk => h k (.inr hk)]

end

/-- **The length of a substitution in the program** (`exprLen`): the expression's length at the
replacements' lengths `L`. -/
theorem exprLen_substRefs (r : Expr) {g : ℕ → Expr} {L : ℕ → ℕ}
    (h : ∀ a ∈ r.refs, ir.exprLen (g a) = L a) :
    ir.exprLen (r.substRefs g) = Expr.len ir L r := by
  rw [exprLen, Expr.len_substRefs]
  exact Expr.len_congr ir r h

/-- **The value of a substitution in the program** (`evalE`): the expression's value at the
replacements' values and lengths `L`. -/
theorem evalE_substRefs (rd : ir.Valuation I) (f : ℕ) (r : Expr) {g : ℕ → Expr} {L : ℕ → ℕ}
    (h : ∀ a ∈ r.refs, ir.exprLen (g a) = L a) :
    ir.evalE rd f (r.substRefs g) = Expr.eval ir f rd (fun a => ir.evalE rd f (g a)) L r := by
  funext i
  simp only [evalE, Expr.eval_substRefs]
  exact congrFun (Expr.eval_congr_len ir r h) i

end Subst

/-! ## The environment -/

/-- **The checks of the environment's codes**, once per circuit: `−1 + 1 = 0`; in characteristic
two `1 + 1 = 0`, otherwise `1/2 + 1/2 = 1`. -/
def TEnv.arithB (env : TEnv) : Bool :=
  Nat.beq (env.ar.add env.neg1 1) 0 &&
    cond env.char2 (Nat.beq (env.ar.add 1 1) 0) (Nat.beq (env.ar.add env.half env.half) 1)

/-- **The environment's codes decode as named** under the decoding `κc`: the code arithmetic is the
field's, `neg1` decodes to `−1`, `half` to an element whose double is `1` in odd characteristic,
and `1 + 1 = 0` in characteristic two. -/
structure TEnv.ArithOk {F : Type*} [CommRing F] (env : TEnv) (κc : ℕ → F) : Prop where
  /-- The code arithmetic is the field's. -/
  hom : env.ar.Hom κc
  /-- `neg1` decodes to `−1`. -/
  neg1 : κc env.neg1 = -1
  /-- In odd characteristic, `half` decodes to a half of `1`. -/
  half : env.char2 = false → κc env.half + κc env.half = 1
  /-- In characteristic two, `1 + 1 = 0`. -/
  char2 : env.char2 = true → (1 : F) + 1 = 0

/-- **The checked codes decode as named**, where the code arithmetic is the field's. -/
theorem TEnv.arithOk_of_arithB {F : Type*} [CommRing F] {env : TEnv} {κc : ℕ → F}
    (hA : env.ar.Hom κc) (h : env.arithB = true) : env.ArithOk κc := by
  simp only [TEnv.arithB, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨hn, hc⟩ := h
  refine ⟨hA, hA.neg_one hn, fun h2 => ?_, fun h2 => ?_⟩
  · rw [h2] at hc
    simp only [Bool.cond_false, Nat.beq_eq] at hc
    rw [← hA.add, hc, hA.one]
  · rw [h2] at hc
    simp only [Bool.cond_true, Nat.beq_eq] at hc
    rw [← hA.one, ← hA.add, hc, hA.zero]

/-! ## Rendering -/

/-- **The erased tree of node `k`**: its printed form with every kid expanded and no `.ref`. -/
def ETable.treeErase (env : TEnv) (E : ETable) (k : ℕ) : Expr := E.render env false (k + 1) k

section Table

variable (ir : RealizedProgram)

/-- **The check of entry `nd` as node `k`**: its kids lie below `k`, its length is its row's at the
kids' lengths, and when it is printed as `.ref j`, the shared expression `j` exists and is its row
at the kids' prints. -/
def nodeRowOkB (env : TEnv) (E : ETable) (k : ℕ) (nd : ENodeInfo) : Bool :=
  (nd.node.row env).refs.all (fun a => Nat.blt a k) &&
    Nat.beq nd.len (Expr.len ir (fun a => (E.get a).len) (nd.node.row env)) &&
    match nd.ref with
    | some j =>
      Nat.blt j ir.exprs.length && ((nd.node.row env).substRefs (E.print env)).beq (ir.expr j)
    | none => true

/-- **The check of node `k`** (`nodeRowOkB` on its entry). -/
def nodeOkB (env : TEnv) (E : ETable) (k : ℕ) : Bool := ir.nodeRowOkB env E k (E.get k)

/-- **`p` holds below `n`**, a `Bool` loop counting down. -/
def allBelow (p : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => p n && allBelow p n

/-- **The check of the table**, once per circuit: every node below the node count. -/
def emitTableOkB (env : TEnv) (E : ETable) : Bool := allBelow (ir.nodeOkB env E) E.size

/-- **Every node of the table checks.** -/
def EmitTableOk (env : TEnv) (E : ETable) : Prop := ∀ k, ir.nodeOkB env E k = true

end Table

theorem allBelow_iff {p : ℕ → Bool} : ∀ {n : ℕ}, allBelow p n = true ↔ ∀ k < n, p k = true
  | 0 => by simp [allBelow]
  | n + 1 => by
    rw [allBelow, Bool.and_eq_true, allBelow_iff]
    constructor
    · rintro ⟨hn, h⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact h k hk
      · exact hn
    · intro h
      exact ⟨h n (Nat.lt_succ_self n), fun k hk => h k (Nat.lt_succ_of_lt hk)⟩

variable {ir : RealizedProgram} {env : TEnv} {E : ETable}

/-- **The table check gives every node's check**: below the node count by the loop, past it for
the default entry (an empty gather of length `0`). -/
theorem emitTableOk_of_emitTableOkB (h : ir.emitTableOkB env E = true) : ir.EmitTableOk env E := by
  intro k
  by_cases hk : k < E.size
  · exact allBelow_iff.1 h k hk
  · have hd : E.get k = default := by
      unfold ETable.get
      cases hb : Nat.blt k E.size
      · rfl
      · exact absurd (by simpa using hb) hk
    simp only [nodeOkB, hd, nodeRowOkB]
    rfl

namespace EmitTableOk

variable (hE : ir.EmitTableOk env E)
include hE

/-- **A node's kids lie below it.** -/
theorem kids_lt {k a : ℕ} (ha : a ∈ ((E.get k).node.row env).refs) : a < k := by
  have h := hE k
  simp only [nodeOkB, nodeRowOkB, Bool.and_eq_true, List.all_eq_true, Nat.blt_eq] at h
  exact h.1.1 a ha

/-- **A node's length is its row's** at the kids' lengths. -/
theorem len_eq (k : ℕ) :
    (E.get k).len = Expr.len ir (fun a => (E.get a).len) ((E.get k).node.row env) := by
  have h := hE k
  simp only [nodeOkB, nodeRowOkB, Bool.and_eq_true, Nat.beq_eq] at h
  exact h.1.2

/-- **A node printed as `.ref j`**: the shared expression `j` exists and is the node's row at the
kids' prints. -/
theorem ref_eq {k j : ℕ} (hj : (E.get k).ref = some j) :
    j < ir.exprs.length ∧ ((E.get k).node.row env).substRefs (E.print env) = ir.expr j := by
  have h := hE k
  simp only [nodeOkB, nodeRowOkB, hj, Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨h.2.1, Expr.eq_of_beq h.2.2⟩

/-- **Rendering past a node's id does not change it.** -/
theorem render_stable (b : Bool) :
    ∀ k n, k < n → E.render env b n k = E.render env b (k + 1) k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hs : ((E.get k).node.row env).substRefs (E.render env b m) =
        ((E.get k).node.row env).substRefs (E.render env b k) :=
      Expr.substRefs_congr _ fun a ha => by
        have hak := hE.kids_lt ha
        rw [ih a hak m (by omega), ih a hak k hak]
    simp only [ETable.render, hs]

/-- **The erased tree unfolds one level**: the row with every kid's erased tree. -/
theorem treeErase_eq (k : ℕ) :
    E.treeErase env k = ((E.get k).node.row env).substRefs (E.treeErase env) := by
  change ((E.get k).node.row env).substRefs (E.render env false k) = _
  exact Expr.substRefs_congr _ fun a ha => hE.render_stable false a k (hE.kids_lt ha)

omit hE in
/-- **The print of a node printed as `.ref j`** is `.ref j`. -/
theorem print_of_ref {k j : ℕ} (hj : (E.get k).ref = some j) : E.print env k = .ref j := by
  simp only [ETable.print, ETable.render, hj]

/-- **The print of any other node unfolds one level**: the row with every kid's print. -/
theorem print_of_none {k : ℕ} (hj : (E.get k).ref = none) :
    E.print env k = ((E.get k).node.row env).substRefs (E.print env) := by
  simp only [ETable.print, ETable.render, hj]
  exact Expr.substRefs_congr _ fun a ha => hE.render_stable true a k (hE.kids_lt ha)

/-- **The erased tree has the node's length.** -/
theorem exprLen_treeErase : ∀ k, ir.exprLen (E.treeErase env k) = (E.get k).len := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [hE.treeErase_eq, exprLen_substRefs ir _ fun a ha => ih a (hE.kids_lt ha), hE.len_eq k]

end EmitTableOk

/-! ## The meaning of a node -/

section Sem

variable (ir) {I : Interp}

/-- **The meaning of node `k`** in domain `d` at the reader `rd`: its erased tree's value. -/
def nodeSem (env : TEnv) (E : ETable) (rd : ir.Valuation I) (d k : ℕ) :
    ℕ → (I (ir.domainField d)).K :=
  ir.evalWith rd d (E.treeErase env k)

end Sem

variable {I : Interp}

/-- **The meaning of a node unfolds one level**: its row's value, each kid `a` read as its meaning
with the node's length. -/
theorem nodeSem_eq (hE : ir.EmitTableOk env E) (rd : ir.Valuation I) (d k : ℕ) :
    ir.nodeSem env E rd d k =
      Expr.eval ir (ir.domainField d) rd (fun a => ir.nodeSem env E rd d a)
        (fun a => (E.get a).len) ((E.get k).node.row env) := by
  funext i
  change ir.evalE rd _ (E.treeErase env k) i = _
  rw [hE.treeErase_eq k, evalE_substRefs ir rd _ _ fun a _ => hE.exprLen_treeErase a]
  rfl

/-- **`eqB` lemma, in every field**: the print of a node has the node's length and the value of its
erased tree, where the shared expressions read only earlier ones. -/
theorem print_spec (ho : ir.RefsOrdered) (hE : ir.EmitTableOk env E) (rd : ir.Valuation I) :
    ∀ k, ir.exprLen (E.print env k) = (E.get k).len ∧
      ∀ f, ir.evalE rd f (E.print env k) = ir.evalE rd f (E.treeErase env k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hp : ∀ a ∈ ((E.get k).node.row env).refs, ir.exprLen (E.print env a) = (E.get a).len :=
      fun a ha => (ih a (hE.kids_lt ha)).1
    have hT : ∀ a ∈ ((E.get k).node.row env).refs,
        ir.exprLen (E.treeErase env a) = (E.get a).len :=
      fun a _ => hE.exprLen_treeErase a
    have hlen : ir.exprLen (((E.get k).node.row env).substRefs (E.print env)) = (E.get k).len := by
      rw [exprLen_substRefs ir _ hp, hE.len_eq k]
    have hval : ∀ f, ir.evalE rd f (((E.get k).node.row env).substRefs (E.print env)) =
        ir.evalE rd f (E.treeErase env k) := fun f => by
      rw [hE.treeErase_eq k, evalE_substRefs ir rd f _ hp, evalE_substRefs ir rd f _ hT]
      exact Expr.eval_congr ir _ (fun _ _ => rfl) fun a ha => (ih a (hE.kids_lt ha)).2 f
    cases hj : (E.get k).ref with
    | none =>
      rw [hE.print_of_none hj]
      exact ⟨hlen, hval⟩
    | some j =>
      obtain ⟨hjl, hje⟩ := hE.ref_eq hj
      rw [EmitTableOk.print_of_ref hj]
      refine ⟨?_, fun f => ?_⟩
      · rw [exprLen_ref ho hjl, ← hje, hlen]
      · rw [evalE_ref ho rd f hjl, ← hje, hval f]

/-- **`eqB_sound`**: a printed expression that checks against node `k` has the node's length and
meaning, where the shared expressions read only earlier ones and the table checks. -/
theorem eqB_sound (ho : ir.RefsOrdered) (hE : ir.EmitTableOk env E) (rd : ir.Valuation I) (d : ℕ)
    {k : ℕ} {e : Expr} (h : E.eqB env k e = true) :
    ir.exprLen e = (E.get k).len ∧ ir.evalWith rd d e = ir.nodeSem env E rd d k := by
  obtain rfl := Expr.eq_of_beq h
  exact ⟨(print_spec ho hE rd k).1, (print_spec ho hE rd k).2 _⟩

/-! ## Chain combines and operators -/

/-- **The value of a chain combine** on field elements: the sum, the product (`and` too), `or` as
`x + y − x y`, `xor` as `x + y` in characteristic two and `x + y − 2 x y` otherwise (the printed
forms of `ENode.row`). -/
def BinOp.sem {F : Type*} [CommRing F] (char2 : Bool) : BinOp → F → F → F
  | .add, x, y => x + y
  | .mul, x, y => x * y
  | .and, x, y => x * y
  | .or, x, y => x + y - x * y
  | .xor, x, y => cond char2 (x + y) (x + y - 2 * (x * y))

/-- **Every chain combine is associative**, so a balanced tree over a chain's leaves has the value
of the printed left-nested tree. -/
theorem BinOp.sem_assoc {F : Type*} [CommRing F] (char2 : Bool) (op : BinOp) (x y z : F) :
    op.sem char2 (op.sem char2 x y) z = op.sem char2 x (op.sem char2 y z) := by
  cases op <;> simp only [BinOp.sem]
  · ring
  · ring
  · ring
  · ring
  · cases char2 <;> simp only [Bool.cond_true, Bool.cond_false] <;> ring

/-- **A chain node's meaning is its combine** of its kids' meanings, where the code arithmetic is
the field's (the code of `2` in the odd `xor`). -/
theorem nodeSem_bin {d : ℕ} (hA : env.ar.Hom (I (ir.domainField d)).decode)
    (hE : ir.EmitTableOk env E) (rd : ir.Valuation I) {k a b : ℕ} {op : BinOp}
    (hk : (E.get k).node = .bin op a b) (i : ℕ) :
    ir.nodeSem env E rd d k i =
      op.sem env.char2 (ir.nodeSem env E rd d a i) (ir.nodeSem env E rd d b i) := by
  rw [nodeSem_eq hE rd d k, hk]
  cases op <;> simp only [ENode.row, Expr.eval, BinOp.sem]
  cases env.char2 <;> simp only [Bool.cond_true, Bool.cond_false, Expr.eval, Coef.eval]
  rw [hA.add, hA.one]
  ring

end GordieHowe.RealizedProgram
