-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.Causal
public import GordieHowe.Model.IOP.Completeness

@[expose] public section

/-!
# Causal provers, runs and completeness of series–parallel compositions

A causal prover (`CausalProver`) runs, at each leaf, a prover of the leaf's component whose
statement is the composite statement together with the leaf's causal context: the full
transcripts of the leaves sequenced before it. `CausalProver.run` is the composite transcript on a
challenge assignment, by recursion on the term: a sequence runs its first subterm and then its
second on the statement extended by the first's transcripts, a parallel node runs both.

`GordieHowe.IOP.CausalComplete` is completeness of an honest family at a composite verifier.
`GordieHowe.IOP.CausalComplete.seq`: completeness errors add, with an honest split of the witness
(`split_witness`) for the second part from any prefix transcript the first part's verifier
accepts; `GordieHowe.IOP.CausalComplete.par`, `GordieHowe.IOP.CausalComplete.nodeN`: parts that do not read each
other's transcripts, side by side or one after the other; errors add.
-/

namespace GordieHowe.IOP

open scoped NNReal
open SPTerm

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}

/-! ### Provers with a changed statement -/

section Comap

variable {m : ℕ} {Q : ProtocolSpec m} {S S' : Type}

/-- A prover run on a statement computed from another: `prv` at `g x`. -/
def Prover.comap (prv : Prover Q S) (g : S' → S) : Prover Q S' :=
  fun i x tr => prv i (g x) tr

/-- The runs of `prv.comap g` at `x` are those of `prv` at `g x`. -/
theorem Prover.runTo_comap (prv : Prover Q S) (g : S' → S) (x : S') (ch : Q.Challenges) (k : ℕ)
    (hk : k ≤ m) : (prv.comap g).runTo x ch k hk = prv.runTo (g x) ch k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Prover.runTo, ih]
    rfl

theorem Prover.run_comap (prv : Prover Q S) (g : S' → S) (x : S') (ch : Q.Challenges) :
    (prv.comap g).run x ch = prv.run (g x) ch :=
  Prover.runTo_comap prv g x ch m le_rfl

end Comap

/-! ### Causal contexts built from parts -/

namespace CausalCtx

variable {k : Comp} {a b : SPTerm ι}

/-- The causal context of the leaf of a one-component term: empty. -/
def ofHere (j : ι) : CausalCtx P (Leaf.here j) :=
  fun ⟨q, h⟩ => by
    cases q
    exact False.elim h

/-- The causal context of the leaf of a one-component term is unique. -/
theorem eq_ofHere {j : ι} (ctx : CausalCtx P (Leaf.here j)) : ctx = ofHere j := by
  funext ⟨q, h⟩
  cases q
  exact False.elim h

/-- The context of a first-subterm leaf of a node from its context in the first subterm. -/
def toLeft {p : a.Leaf} (ctx : CausalCtx P p) : CausalCtx P (Leaf.left (k := k) (b := b) p) :=
  fun ⟨q, h⟩ => match q, h with
    | .left q, h => ctx ⟨q, h⟩
    | .right _, h => False.elim h

/-- The context of a second-subterm leaf of `seq a b` from `a`'s full transcripts and its context
in `b`. -/
def toSeqRight {p : b.Leaf} (f : FullTr P a) (ctx : CausalCtx P p) :
    CausalCtx P (Leaf.right (k := .seq) (a := a) p) :=
  fun ⟨q, h⟩ => match q, h with
    | .left q, _ => f q
    | .right q, h => ctx ⟨q, h⟩

/-- The context of a second-subterm leaf of `par a b` from its context in `b`. -/
def toParRight {p : b.Leaf} (ctx : CausalCtx P p) :
    CausalCtx P (Leaf.right (k := .par) (a := a) p) :=
  fun ⟨q, h⟩ => match q, h with
    | .left _, h => nomatch h
    | .right q, h => ctx ⟨q, h⟩

end CausalCtx

/-! ### Causal provers and their runs -/

variable (P) in
/-- **A causal prover** of the composite `t`: at each leaf, a prover of the leaf's component on
the composite statement and the leaf's causal context. -/
abbrev CausalProver (t : SPTerm ι) (Stmt : Type) : Type :=
  (p : t.Leaf) → Prover (P p.label) (Stmt × CausalCtx P p)

namespace CausalProver

variable {Stmt : Type} {a b : SPTerm ι}

/-- The first subterm's provers of a node. -/
def left {k : Comp} (prv : CausalProver P (node k a b) Stmt) : CausalProver P a Stmt :=
  fun p => (prv (.left p)).comap fun s => (s.1, s.2.toLeft)

/-- The second subterm's provers of `seq a b`, on the statement extended by `a`'s transcripts. -/
def seqRight (prv : CausalProver P (SPTerm.seq a b) Stmt) : CausalProver P b (Stmt × FullTr P a) :=
  fun p => (prv (.right p)).comap fun s => (s.1.1, CausalCtx.toSeqRight s.1.2 s.2)

/-- The second subterm's provers of `par a b`. -/
def parRight (prv : CausalProver P (SPTerm.par a b) Stmt) : CausalProver P b Stmt :=
  fun p => (prv (.right p)).comap fun s => (s.1, s.2.toParRight)

/-- **The composite transcript** of a causal prover on the statement `x` and the challenges `ch`:
each leaf's prover runs on its own challenges, with the transcripts of the leaves before it as
its causal context. -/
def run : {t : SPTerm ι} → {Stmt : Type} → CausalProver P t Stmt → Stmt → Chs P t → FullTr P t
  | nil, _, _, _, _ => fun p => nomatch p
  | leaf j, _, prv, x, ch => fun p => match p with
    | .here _ => (prv (.here j)).run (x, CausalCtx.ofHere j) (ch.at (.here j))
  | node .seq _ _, _, prv, x, ch =>
    FullTr.join (run prv.left x ch.left) (run prv.seqRight (x, run prv.left x ch.left) ch.right)
  | node .par _ _, _, prv, x, ch =>
    FullTr.join (run prv.left x ch.left) (run prv.parRight x ch.right)

/-- **The composite of a sequence of causal provers**: `prv₁` at `a`'s leaves, `prv₂` at `b`'s on
the statement extended by `a`'s transcripts. -/
def seq (prv₁ : CausalProver P a Stmt) (prv₂ : CausalProver P b (Stmt × FullTr P a)) :
    CausalProver P (SPTerm.seq a b) Stmt
  | .left p => (prv₁ p).comap fun s => (s.1, s.2.ofLeft)
  | .right p => (prv₂ p).comap fun s => ((s.1, s.2.fst), s.2.ofRight)

/-- **The composite of causal provers whose second part does not read the first's
transcripts**: side by side, or one after the other. -/
def par {k : Comp} (prv₁ : CausalProver P a Stmt) (prv₂ : CausalProver P b Stmt) :
    CausalProver P (node k a b) Stmt
  | .left p => (prv₁ p).comap fun s => (s.1, s.2.ofLeft)
  | .right p => (prv₂ p).comap fun s => (s.1, s.2.ofRight)

/-- **A causal prover that reads its strategy off the statement.** -/
def ofStmt {t : SPTerm ι} (F : Stmt → CausalProver P t Stmt) : CausalProver P t Stmt :=
  fun p i s tr => F s.1 p i s tr

theorem seq_left (prv₁ : CausalProver P a Stmt) (prv₂ : CausalProver P b (Stmt × FullTr P a)) :
    (seq prv₁ prv₂).left = prv₁ := rfl

theorem seq_seqRight (prv₁ : CausalProver P a Stmt)
    (prv₂ : CausalProver P b (Stmt × FullTr P a)) : (seq prv₁ prv₂).seqRight = prv₂ := rfl

/-- **A causal prover on a statement computed from another**: every leaf's prover at `g` of the
statement. -/
def comapStmt {t : SPTerm ι} {Stmt' : Type} (g : Stmt' → Stmt) (prv : CausalProver P t Stmt) :
    CausalProver P t Stmt' :=
  fun p => (prv p).comap fun s => (g s.1, s.2)

/-- The run of a sequence: the first part's run, then the second part's on the statement extended
by it. -/
theorem run_seq (prv₁ : CausalProver P a Stmt) (prv₂ : CausalProver P b (Stmt × FullTr P a))
    (x : Stmt) (ch : Chs P (SPTerm.seq a b)) :
    (seq prv₁ prv₂).run x ch =
      FullTr.join (prv₁.run x ch.left) (prv₂.run (x, prv₁.run x ch.left) ch.right) := rfl

/-- The run of `comapStmt g prv` at `y` is the run of `prv` at `g y`. -/
theorem run_comapStmt : {t : SPTerm ι} → {Stmt Stmt' : Type} → (g : Stmt' → Stmt) →
    (prv : CausalProver P t Stmt) → (y : Stmt') → (ch : Chs P t) →
    (comapStmt g prv).run y ch = prv.run (g y) ch
  | nil, _, _, _, _, _, _ => funext fun p => nomatch p
  | leaf j, _, _, g, prv, y, ch => funext fun p => by
    cases p
    exact Prover.run_comap (prv (.here j)) _ _ _
  | node .seq _ _, _, _, g, prv, y, ch => by
    have h₁ := run_comapStmt g prv.left y ch.left
    have h₂ := run_comapStmt (fun z : _ × _ => (g z.1, z.2)) prv.seqRight
      (y, prv.left.run (g y) ch.left) ch.right
    change FullTr.join ((comapStmt g prv.left).run y ch.left)
      ((comapStmt (fun z : _ × _ => (g z.1, z.2)) prv.seqRight).run
        (y, (comapStmt g prv.left).run y ch.left) ch.right) = _
    rw [h₁, h₂]
    rfl
  | node .par _ _, _, _, g, prv, y, ch => by
    have h₁ := run_comapStmt g prv.left y ch.left
    have h₂ := run_comapStmt g prv.parRight y ch.right
    change FullTr.join ((comapStmt g prv.left).run y ch.left)
      ((comapStmt g prv.parRight).run y ch.right) = _
    rw [h₁, h₂]
    rfl

/-- The run of a composite with independent parts: both parts' runs. -/
theorem run_par {k : Comp} (prv₁ : CausalProver P a Stmt) (prv₂ : CausalProver P b Stmt)
    (x : Stmt) (ch : Chs P (node k a b)) :
    (par (k := k) prv₁ prv₂).run x ch =
      FullTr.join (prv₁.run x ch.left) (prv₂.run x ch.right) := by
  cases k
  · change FullTr.join (prv₁.run x ch.left)
      ((comapStmt Prod.fst prv₂).run (x, prv₁.run x ch.left) ch.right) = _
    rw [run_comapStmt]
  · rfl

/-- The run of `ofStmt F` at `x` is the run of `F x`. -/
theorem run_ofStmt : {t : SPTerm ι} → {Stmt : Type} → (F : Stmt → CausalProver P t Stmt) →
    (x : Stmt) → (ch : Chs P t) → (ofStmt F).run x ch = (F x).run x ch
  | nil, _, _, _, _ => funext fun p => nomatch p
  | leaf j, _, F, x, ch => funext fun p => by
    cases p
    exact Prover.run_ofStatement (fun s => F s.1 (.here j)) _ _
  | node .seq _ _, _, F, x, ch => by
    have h₁ := run_ofStmt (fun y => (F y).left) x ch.left
    have h₂ := run_ofStmt (fun y : _ × _ => (F y.1).seqRight) (x, (F x).left.run x ch.left)
      ch.right
    change FullTr.join ((ofStmt fun y => (F y).left).run x ch.left)
      ((ofStmt fun y : _ × _ => (F y.1).seqRight).run
        (x, (ofStmt fun y => (F y).left).run x ch.left) ch.right) = _
    rw [h₁, h₂]
    rfl
  | node .par _ _, _, F, x, ch => by
    have h₁ := run_ofStmt (fun y => (F y).left) x ch.left
    have h₂ := run_ofStmt (fun y => (F y).parRight) x ch.right
    change FullTr.join ((ofStmt fun y => (F y).left).run x ch.left)
      ((ofStmt fun y => (F y).parRight).run x ch.right) = _
    rw [h₁, h₂]
    rfl

/-- **A one-component causal prover** from a prover of the component. -/
def ofLeaf {j : ι} (prv : Prover (P j) Stmt) : CausalProver P (leaf j) Stmt
  | .here _ => prv.comap Prod.fst

/-- The run of a one-component causal prover is the component prover's run. -/
theorem run_ofLeaf {j : ι} (prv : Prover (P j) Stmt) (x : Stmt) (ch : Chs P (leaf j)) :
    (ofLeaf prv).run x ch (.here j) = prv.run x (Chs.equivLeaf ch) :=
  Prover.run_comap prv Prod.fst _ _

/-- **`m` causal provers composed by `k`**, none reading another's transcripts. -/
def nodeN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} → (∀ i, CausalProver P (c i) Stmt) →
    CausalProver P (SPTerm.nodeN k m c) Stmt
  | 0, _, _ => fun p => nomatch p
  | m + 1, _, prv => (prv 0).par (nodeN k m fun i => prv i.succ)

end CausalProver

/-! ### Completeness -/

section Completeness

variable [∀ j (i : (P j).ChallengeIdx), Fintype ((P j).Challenge i)]
  [∀ j (i : (P j).ChallengeIdx), Nonempty ((P j).Challenge i)] {Stmt Wit : Type}

/-- **Completeness of a causal honest prover family at an error of the statement**: on every pair
`(x, w)` of `rel`, the composite verifier rejects the run of `honest w` with probability at most
`δ x` over uniform challenges. -/
def CausalCompleteStmt {t : SPTerm ι} (rel : Set (Stmt × Wit)) (V : Stmt → FullTr P t → Bool)
    (honest : Wit → CausalProver P t Stmt) (δ : Stmt → ℝ≥0) : Prop :=
  ∀ x w, (x, w) ∈ rel → Pr[ch ← Chs P t : V x ((honest w).run x ch) ≠ true] ≤ δ x

/-- **Completeness of a causal honest prover family** at the error `δ` at every statement
(`CausalCompleteStmt` at the constant error). -/
abbrev CausalComplete {t : SPTerm ι} (rel : Set (Stmt × Wit)) (V : Stmt → FullTr P t → Bool)
    (honest : Wit → CausalProver P t Stmt) (δ : ℝ≥0) : Prop :=
  CausalCompleteStmt rel V honest fun _ => δ

/-- **Completeness of a causal honest prover family with coins**: on every pair `(x, w)` of `rel`,
the composite verifier rejects the run of `honest w ω` with probability at most `δ x` over uniform
coins `ω` and uniform challenges (the paper's `def:iop-complete`, after DFMS22 p. 10: an error of
the statement, over the challenges and the prover's coins); a constant error is `fun _ => δ`. -/
def causalCompletenessCoins {t : SPTerm ι} (rel : Set (Stmt × Wit)) (V : Stmt → FullTr P t → Bool)
    {Ω : Type} [Fintype Ω] [Nonempty Ω] (honest : Wit → Ω → CausalProver P t Stmt)
    (δ : Stmt → ℝ≥0) : Prop :=
  ∀ x w, (x, w) ∈ rel → Pr[u ← (Ω × Chs P t) : V x ((honest w u.1).run x u.2) ≠ true] ≤ δ x

variable {a b : SPTerm ι}

/-- A larger error and a smaller relation keep completeness. -/
theorem CausalComplete.mono {t : SPTerm ι} {rel rel' : Set (Stmt × Wit)}
    {V : Stmt → FullTr P t → Bool} {honest : Wit → CausalProver P t Stmt} {δ δ' : ℝ≥0}
    (h : CausalComplete rel V honest δ) (hrel : rel' ⊆ rel) (hδ : δ ≤ δ') :
    CausalComplete rel' V honest δ' :=
  fun x w hw => (h x w (hrel hw)).trans (by exact_mod_cast hδ)

/-- **Completeness of a sequence.** The honest first part produces a transcript in the event
`good` except with probability `δ₁`; the second part, on statements extended by the first part's
transcripts, is complete for `rel₂` at `V₂` with error `δ₂`; and from every pair of `rel` and every
first-part transcript in `good`, `wit` gives a witness of `rel₂` (`split_witness`). The composite
of the honest provers, the second reading its witness off its statement, is complete for `rel` at
`V₂` read on the parts, with error `δ₁ + δ₂`. With `good` the acceptance of a first-part verifier
this adds the completeness errors of the two parts. -/
theorem CausalComplete.seq {Wit₂ : Type} {rel : Set (Stmt × Wit)}
    {rel₂ : Set ((Stmt × FullTr P a) × Wit₂)} {V₂ : Stmt × FullTr P a → FullTr P b → Bool}
    {honest₁ : Wit → CausalProver P a Stmt}
    {honest₂ : Wit₂ → CausalProver P b (Stmt × FullTr P a)} {δ₁ δ₂ : ℝ≥0}
    (good : Stmt → Wit → FullTr P a → Prop)
    (h₁ : ∀ x w, (x, w) ∈ rel → Pr[ch ← Chs P a : ¬ good x w ((honest₁ w).run x ch)] ≤ δ₁)
    (h₂ : CausalComplete rel₂ V₂ honest₂ δ₂) (wit : Stmt → Wit → FullTr P a → Wit₂)
    (split_witness : ∀ x w, (x, w) ∈ rel → ∀ f, good x w f → ((x, f), wit x w f) ∈ rel₂) :
    CausalComplete rel (fun x f => V₂ (x, f.left) f.right)
      (fun w => (honest₁ w).seq (CausalProver.ofStmt fun y => honest₂ (wit y.1 w y.2)))
      (δ₁ + δ₂) := by
  intro x w hw
  rw [probUniform_equiv Chs.equivNode]
  have key := probUniform_prod_le_add (A := Chs P a) (C := Chs P b) (c := (δ₂ : ENNReal))
    (fun c => V₂ (x, (honest₁ w).run x c.1) ((honest₂ (wit x w ((honest₁ w).run x c.1))).run
        (x, (honest₁ w).run x c.1) c.2) ≠ true)
    (fun c₁ => ¬ good x w ((honest₁ w).run x c₁)) fun c₁ hc₁ =>
      h₂ _ _ (split_witness x w hw _ (not_not.mp hc₁))
  refine (probUniform_mono fun c hc => ?_).trans (key.trans ?_)
  · rw [CausalProver.run_seq, CausalProver.run_ofStmt] at hc
    exact hc
  · rw [add_comm, ENNReal.coe_add]
    exact add_le_add_left (h₁ x w hw) _

/-- **Completeness of a composite with independent parts**: honest families complete for `rel₁`
at `V₁` and for `rel₂` at `V₂`, on the same statements and witnesses, run side by side or one
after the other without reading each other's transcripts, are complete for both relations at the
conjunction of the verifiers with error `δ₁ + δ₂`. -/
theorem CausalComplete.par {k : Comp} {rel₁ rel₂ : Set (Stmt × Wit)}
    {V₁ : Stmt → FullTr P a → Bool}
    {V₂ : Stmt → FullTr P b → Bool} {honest₁ : Wit → CausalProver P a Stmt}
    {honest₂ : Wit → CausalProver P b Stmt} {δ₁ δ₂ : ℝ≥0}
    (h₁ : CausalComplete rel₁ V₁ honest₁ δ₁) (h₂ : CausalComplete rel₂ V₂ honest₂ δ₂) :
    CausalComplete (rel₁ ∩ rel₂)
      (fun x (f : FullTr P (node k a b)) => V₁ x f.left && V₂ x f.right)
      (fun w => (honest₁ w).par (honest₂ w)) (δ₁ + δ₂) := by
  intro x w hw
  rw [probUniform_equiv Chs.equivNode]
  have key := probUniform_prod_le_add (A := Chs P a) (C := Chs P b) (c := (δ₂ : ENNReal))
    (fun c => V₁ x ((honest₁ w).run x c.1) ≠ true ∨ V₂ x ((honest₂ w).run x c.2) ≠ true)
    (fun c₁ => V₁ x ((honest₁ w).run x c₁) ≠ true) fun c₁ hc₁ =>
      (probUniform_mono fun _ hc => hc.resolve_left hc₁).trans (h₂ x w hw.2)
  refine (probUniform_mono fun c hc => ?_).trans (key.trans ?_)
  · rw [CausalProver.run_par] at hc
    simp only [FullTr.left_join, FullTr.right_join, ne_eq, Bool.and_eq_true, not_and_or] at hc
    exact hc
  · rw [add_comm, ENNReal.coe_add]
    exact add_le_add_left (h₁ x w hw.1) _

/-- **Completeness of `m` composites** side by side or one after the other, none reading
another's transcripts: errors add, for the intersection of the relations at the conjunction of
the verifiers. -/
theorem CausalComplete.nodeN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} →
    {rel : Fin m → Set (Stmt × Wit)} → {V : ∀ i, Stmt → FullTr P (c i) → Bool} →
    {honest : ∀ i, Wit → CausalProver P (c i) Stmt} → {δ : Fin m → ℝ≥0} →
    (∀ i, CausalComplete (rel i) (V i) (honest i) (δ i)) →
    CausalComplete {p | ∀ i, p ∈ rel i} (verifierN k m V)
      (fun w => CausalProver.nodeN k m fun i => honest i w) (∑ i, δ i)
  | 0, _, _, _, _, _, _ => fun x w _ =>
    (probUniform_mono fun _ h => h rfl).trans (by simp [probUniform])
  | m + 1, _, _, _, _, δ, h =>
    (par (k := k) (h 0) (nodeN k m fun i => h i.succ)).mono
      (fun _ hp => ⟨hp 0, fun i => hp i.succ⟩) (by rw [Fin.sum_univ_succ])

/-- **Completeness of a component as a one-component composite**, on statements `y` read through
`σ` and witnesses through `ω`: the component's honest prover on `σ y` with the witness `ω y w`. -/
theorem CausalComplete.ofLeaf {j : ι} {Y W StmtC WitC : Type} {relC : Set (StmtC × WitC)}
    {V : Verifier (P j) StmtC} {honest : WitC → Prover (P j) StmtC} {δ : ℝ≥0}
    (h : completenessAt relC V honest δ) (σ : Y → StmtC) (ω : Y → W → WitC) :
    CausalComplete {p | (σ p.1, ω p.1 p.2) ∈ relC} (fun y f => V (σ y) (f (.here j)))
      (fun w => CausalProver.ofLeaf
        (Prover.ofStatement fun y => (honest (ω y w)).comap σ)) δ := by
  intro y w hw
  rw [probUniform_equiv Chs.equivLeaf]
  have hrun : ∀ c, (CausalProver.ofLeaf (Prover.ofStatement fun y => (honest (ω y w)).comap σ)).run
      y (Chs.equivLeaf.symm c) (.here j) = (honest (ω y w)).run (σ y) c := fun c => by
    rw [CausalProver.run_ofLeaf, Prover.run_ofStatement, Prover.run_comap, Equiv.apply_symm_apply]
  simp only [hrun]
  exact h _ _ hw

end Completeness

end GordieHowe.IOP
