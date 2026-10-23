-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.RBR

@[expose] public section

/-!
# Series–parallel composition of protocols: terms, causal pasts, causal round-by-round soundness

Components are ordinary protocols on their own schedules: `P j : ProtocolSpec (n j)` for labels
`j : ι`. A composition is a series–parallel term `SPTerm ι` over the labels: `seq a b` runs `b`
after `a`, `par a b` runs `a` and `b` side by side, `nil` is the empty composition. The leaves of a
term (`SPTerm.Leaf`) are its occurrences of components; a leaf is the path from the root to it
(`left`/`right` at each node), so a component used twice gives two leaves.

`q.Before p`: leaf `q` is sequenced before leaf `p`, that is, some `seq a b` of the term has `q`
in `a` and `p` in `b`. Leaves in different branches of a `par` are unordered.

* `FullTr P t`: a full transcript of every leaf.
* `CausalCtx P p`: the full transcripts of the leaves sequenced before `p`, a function on those
  leaves. `FullTr.ctx` reads it off a composite transcript by restricting the function, and
  `CausalCtx.restrict` restricts the context of `p` to that of an earlier leaf.
* `ChIdx P t`: a challenge of the composite, a leaf with one of its component's challenge rounds;
  `Chs P t` assigns a challenge to each.
* `CausalPast P c`: the causal past of the challenge `c`, the causal context of its leaf and the
  leaf's own messages before the challenge round. A Fiat–Shamir compiler hashes it, encoded as the
  leaf paths and the messages, to derive the challenge.

**Causal round-by-round soundness** (`CausalRBRStmt`, with errors that may depend on the statement;
`CausalRBR` at errors that do not; the name is ours). A state function assigns to
every leaf, prefix length, statement, causal context and own prefix a proposition
(`CausalStateFn`), and a causal extractor reads a candidate witness off the causal past of a
challenge (`CausalExtractor`). The two conditions:
* `exists_flip`: on a composite transcript whose output claim holds, when the input claim fails
  and the extractor fails on the causal past of every challenge, some challenge moves its leaf's
  state from false to true (`FlipAt`), read on that challenge's causal past;
* `rbr`: for every challenge and every causal past, the probability over the fresh challenge that
  it moves the state from false to true while the extractor fails on the past is at most the
  challenge's own error `ε x c` at the statement `x`.

Both conditions read the state only through causal pasts, so a compiler that derives each
challenge from a hash of its causal past charges each query only the error of the challenge it
answers. For one protocol, `exists_flip` is what `KnowledgeStateFunction.exists_flip` and the
straight-line extractor (`knowledgeSoundness_count_of_rbr_count`) give; here it is the defining
condition, since the composite has no single round order from which to derive it.
`GordieHowe.IOP.CausalRBRKnowledgeSoundStmt` is the case with input claim false and output claim
acceptance (the paper's `def:rbr`), and `GordieHowe.IOP.CausalRBRKnowledgeSound` its case at errors
that do not depend on the statement.
-/

namespace GordieHowe.IOP

open scoped NNReal

/-- How a node of a series–parallel term composes its two subterms. -/
inductive Comp where
  /-- The second subterm runs after the first. -/
  | seq
  /-- The two subterms run side by side. -/
  | par
  deriving DecidableEq

/-- **A series–parallel term** over component labels `ι`. -/
inductive SPTerm (ι : Type) where
  /-- The empty composition. -/
  | nil
  /-- One component. -/
  | leaf (j : ι)
  /-- Two subterms, composed by `k`. -/
  | node (k : Comp) (a b : SPTerm ι)

namespace SPTerm

variable {ι : Type}

/-- `b` after `a`. -/
abbrev seq (a b : SPTerm ι) : SPTerm ι := node .seq a b

/-- `a` and `b` side by side. -/
abbrev par (a b : SPTerm ι) : SPTerm ι := node .par a b

/-- **A leaf of a term**: the path from the root to an occurrence of a component. -/
inductive Leaf : SPTerm ι → Type
  /-- The leaf of a one-component term. -/
  | here (j : ι) : Leaf (leaf j)
  /-- A leaf of the first subterm. -/
  | left {k : Comp} {a b : SPTerm ι} : Leaf a → Leaf (node k a b)
  /-- A leaf of the second subterm. -/
  | right {k : Comp} {a b : SPTerm ι} : Leaf b → Leaf (node k a b)

namespace Leaf

/-- The component at a leaf. -/
def label : {t : SPTerm ι} → t.Leaf → ι
  | _, here j => j
  | _, left p => p.label
  | _, right p => p.label

@[simp] theorem label_here (j : ι) : (here j).label = j := rfl
@[simp] theorem label_left {k : Comp} {a b : SPTerm ι} (p : a.Leaf) :
    (left (k := k) (b := b) p).label = p.label := rfl
@[simp] theorem label_right {k : Comp} {a b : SPTerm ι} (p : b.Leaf) :
    (right (k := k) (a := a) p).label = p.label := rfl

/-- **Sequenced before**: `q.Before p` when some `seq a b` of the term has `q` in `a` and `p` in
`b`. -/
def Before : {t : SPTerm ι} → t.Leaf → t.Leaf → Prop
  | _, here _, here _ => False
  | _, left q, left p => q.Before p
  | _, right q, right p => q.Before p
  | node k _ _, left _, right _ => k = .seq
  | _, right _, left _ => False

@[simp] theorem before_left_left {k : Comp} {a b : SPTerm ι} (q p : a.Leaf) :
    (left (k := k) (b := b) q).Before (left p) ↔ q.Before p := Iff.rfl
@[simp] theorem before_right_right {k : Comp} {a b : SPTerm ι} (q p : b.Leaf) :
    (right (k := k) (a := a) q).Before (right p) ↔ q.Before p := Iff.rfl
@[simp] theorem before_left_right {k : Comp} {a b : SPTerm ι} (q : a.Leaf) (p : b.Leaf) :
    (left (k := k) q).Before (right p) ↔ k = .seq := Iff.rfl
@[simp] theorem not_before_right_left {k : Comp} {a b : SPTerm ι} (q : b.Leaf) (p : a.Leaf) :
    ¬ (right (k := k) q).Before (left p) := id

/-- `Before` is irreflexive. -/
theorem not_before_self {t : SPTerm ι} (p : t.Leaf) : ¬ p.Before p := by
  induction p with
  | here _ => exact id
  | left _ ih => exact ih
  | right _ ih => exact ih

/-- `Before` is transitive. -/
theorem Before.trans {t : SPTerm ι} {r q p : t.Leaf} (h₁ : r.Before q) (h₂ : q.Before p) :
    r.Before p := by
  induction t with
  | nil => cases r
  | leaf j =>
    cases r
    cases q
    exact False.elim h₁
  | node k a b iha ihb =>
    cases r <;> cases q <;> cases p
    all_goals first
      | exact iha h₁ h₂
      | exact ihb h₁ h₂
      | exact h₁
      | exact h₂
      | exact False.elim h₁
      | exact False.elim h₂

/-- `Before` is asymmetric. -/
theorem Before.asymm {t : SPTerm ι} {q p : t.Leaf} (h₁ : q.Before p) (h₂ : p.Before q) : False :=
  not_before_self q (h₁.trans h₂)

/-- The leaves of a node are those of its two subterms. -/
def equivNode {k : Comp} {a b : SPTerm ι} : (node k a b).Leaf ≃ a.Leaf ⊕ b.Leaf where
  toFun
    | left p => .inl p
    | right p => .inr p
  invFun
    | .inl p => left p
    | .inr p => right p
  left_inv p := by cases p <;> rfl
  right_inv s := by cases s <;> rfl

/-- A term has finitely many leaves. -/
instance fintype : (t : SPTerm ι) → Fintype t.Leaf
  | nil => ⟨∅, fun p => nomatch p⟩
  | leaf j => ⟨{here j}, fun p => by cases p; simp⟩
  | node _ a b =>
    letI := fintype a
    letI := fintype b
    Fintype.ofEquiv _ equivNode.symm

/-- The leaves of a term have decidable equality. -/
instance decEq : (t : SPTerm ι) → DecidableEq t.Leaf
  | nil => fun p => nomatch p
  | leaf _ => fun p q => by
    cases p
    cases q
    exact isTrue rfl
  | node _ a b =>
    letI := decEq a
    letI := decEq b
    equivNode.decidableEq

end Leaf

end SPTerm

open SPTerm

variable {ι : Type} {n : ι → ℕ} (P : (j : ι) → ProtocolSpec (n j))

/-- **A full composite transcript**: the full transcript of every leaf's component. -/
def FullTr (t : SPTerm ι) : Type :=
  (p : t.Leaf) → (P p.label).Transcript (Fin.last (n p.label))

/-- **The causal context of a leaf**: the full transcripts of the leaves sequenced before it. -/
def CausalCtx {t : SPTerm ι} (p : t.Leaf) : Type :=
  (q : {q : t.Leaf // q.Before p}) → (P q.1.label).Transcript (Fin.last (n q.1.label))

variable {P}

/-- The causal context of a leaf read off a composite transcript: the restriction of the
transcript to the leaves sequenced before it. -/
def FullTr.ctx {t : SPTerm ι} (f : FullTr P t) (p : t.Leaf) : CausalCtx P p :=
  fun q => f q.1

/-- The causal context of `p` restricted to that of an earlier leaf `q`. -/
def CausalCtx.restrict {t : SPTerm ι} {q p : t.Leaf} (ctx : CausalCtx P p) (h : q.Before p) :
    CausalCtx P q :=
  fun r => ctx ⟨r.1, r.2.trans h⟩

@[simp] theorem FullTr.ctx_restrict {t : SPTerm ι} (f : FullTr P t) {q p : t.Leaf}
    (h : q.Before p) : (f.ctx p).restrict h = f.ctx q :=
  rfl

/-- The first subterm's part of a composite transcript of a node. -/
def FullTr.left {k : Comp} {a b : SPTerm ι} (f : FullTr P (node k a b)) : FullTr P a :=
  fun p => f (.left p)

/-- The second subterm's part of a composite transcript of a node. -/
def FullTr.right {k : Comp} {a b : SPTerm ι} (f : FullTr P (node k a b)) : FullTr P b :=
  fun p => f (.right p)

/-- The composite transcript of a node from those of its subterms. -/
def FullTr.join {k : Comp} {a b : SPTerm ι} (f₁ : FullTr P a) (f₂ : FullTr P b) :
    FullTr P (node k a b)
  | .left p => f₁ p
  | .right p => f₂ p

@[simp] theorem FullTr.left_join {k : Comp} {a b : SPTerm ι} (f₁ : FullTr P a) (f₂ : FullTr P b) :
    (FullTr.join (k := k) f₁ f₂).left = f₁ := rfl
@[simp] theorem FullTr.right_join {k : Comp} {a b : SPTerm ι} (f₁ : FullTr P a) (f₂ : FullTr P b) :
    (FullTr.join (k := k) f₁ f₂).right = f₂ := rfl

/-! ### Causal contexts at the leaves of a node -/

namespace CausalCtx

variable {k : Comp} {a b : SPTerm ι}

/-- The context of a first-subterm leaf of a node is its context in the first subterm. -/
def ofLeft {p : a.Leaf} (ctx : CausalCtx P (Leaf.left (k := k) (b := b) p)) : CausalCtx P p :=
  fun q => ctx ⟨.left q.1, q.2⟩

/-- The context of a second-subterm leaf of a node, restricted to the second subterm. -/
def ofRight {p : b.Leaf} (ctx : CausalCtx P (Leaf.right (k := k) (a := a) p)) : CausalCtx P p :=
  fun q => ctx ⟨.right q.1, q.2⟩

/-- The first subterm's full transcripts in the context of a second-subterm leaf of `seq a b`. -/
def fst {p : b.Leaf} (ctx : CausalCtx P (Leaf.right (k := .seq) (a := a) p)) : FullTr P a :=
  fun q => ctx ⟨.left q, rfl⟩

end CausalCtx

@[simp] theorem FullTr.ctx_ofLeft {k : Comp} {a b : SPTerm ι} (f : FullTr P (node k a b))
    (p : a.Leaf) : (f.ctx (.left p)).ofLeft = f.left.ctx p := rfl
@[simp] theorem FullTr.ctx_ofRight {k : Comp} {a b : SPTerm ι} (f : FullTr P (node k a b))
    (p : b.Leaf) : (f.ctx (.right p)).ofRight = f.right.ctx p := rfl
@[simp] theorem FullTr.ctx_fst {a b : SPTerm ι} (f : FullTr P (seq a b)) (p : b.Leaf) :
    (f.ctx (.right p)).fst = f.left := rfl

/-! ### Challenges -/

variable (P) in
/-- **A challenge of the composite**: a leaf and one of its component's challenge rounds. -/
structure ChIdx (t : SPTerm ι) where
  /-- The leaf. -/
  leaf : t.Leaf
  /-- The challenge round of the leaf's component. -/
  idx : (P leaf.label).ChallengeIdx

namespace ChIdx

variable {t : SPTerm ι}

/-- The challenges of the composite are the pairs of a leaf and a challenge round. -/
def equivSigma : ChIdx P t ≃ Σ p : t.Leaf, (P p.label).ChallengeIdx where
  toFun c := ⟨c.leaf, c.idx⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A composite has finitely many challenges. -/
instance : Fintype (ChIdx P t) := Fintype.ofEquiv _ equivSigma.symm

/-- The challenges of a composite have decidable equality. -/
instance : DecidableEq (ChIdx P t) := equivSigma.decidableEq

/-- A challenge of the first subterm, as one of the node. -/
abbrev left {k : Comp} {a b : SPTerm ι} (c : ChIdx P a) : ChIdx P (node k a b) :=
  ⟨.left c.leaf, c.idx⟩

/-- A challenge of the second subterm, as one of the node. -/
abbrev right {k : Comp} {a b : SPTerm ι} (c : ChIdx P b) : ChIdx P (node k a b) :=
  ⟨.right c.leaf, c.idx⟩

/-- Every challenge of a node is one of its first or of its second subterm. -/
theorem left_or_right {k : Comp} {a b : SPTerm ι} (c : ChIdx P (node k a b)) :
    (∃ c₁ : ChIdx P a, c = c₁.left) ∨ ∃ c₂ : ChIdx P b, c = c₂.right := by
  obtain ⟨p, i⟩ := c
  cases p with
  | left p => exact .inl ⟨⟨p, i⟩, rfl⟩
  | right p => exact .inr ⟨⟨p, i⟩, rfl⟩

end ChIdx

/-- The challenge type of a composite challenge. -/
abbrev ChIdx.Challenge {t : SPTerm ι} (c : ChIdx P t) : Type := (P c.leaf.label).Challenge c.idx

variable (P) in
/-- **A challenge for every challenge round of every leaf.** -/
abbrev Chs (t : SPTerm ι) : Type := (c : ChIdx P t) → c.Challenge

/-- The challenges of one leaf. -/
def Chs.at {t : SPTerm ι} (ch : Chs P t) (p : t.Leaf) : (P p.label).Challenges :=
  fun i => ch ⟨p, i⟩

/-- The first subterm's challenges. -/
def Chs.left {k : Comp} {a b : SPTerm ι} (ch : Chs P (node k a b)) : Chs P a :=
  fun c => ch c.left

/-- The second subterm's challenges. -/
def Chs.right {k : Comp} {a b : SPTerm ι} (ch : Chs P (node k a b)) : Chs P b :=
  fun c => ch c.right

/-- The challenges of a node are those of its two subterms. -/
def Chs.equivNode {k : Comp} {a b : SPTerm ι} : Chs P (node k a b) ≃ Chs P a × Chs P b where
  toFun ch := (ch.left, ch.right)
  invFun ch c := match c with
    | ⟨.left p, i⟩ => ch.1 ⟨p, i⟩
    | ⟨.right p, i⟩ => ch.2 ⟨p, i⟩
  left_inv ch := by
    funext c
    obtain ⟨p, i⟩ := c
    cases p <;> rfl
  right_inv _ := rfl

/-- The challenges of a one-component term are the component's challenges. -/
def Chs.equivLeaf {j : ι} : Chs P (leaf j) ≃ (P j).Challenges where
  toFun ch := ch.at (.here j)
  invFun ch c := match c with
    | ⟨.here _, i⟩ => ch i
  left_inv ch := by
    funext c
    obtain ⟨p, i⟩ := c
    cases p
    rfl
  right_inv _ := rfl

/-- The challenges of a full composite transcript. -/
def FullTr.challenges {t : SPTerm ι} (f : FullTr P t) : Chs P t :=
  fun c => f c.leaf c.idx.1

/-- A uniform probability is monotone in the event. -/
theorem probUniform_mono {C : Type*} [Fintype C] [Nonempty C] {p q : C → Prop}
    (h : ∀ c, p c → q c) : Pr[c ← C : p c] ≤ Pr[c ← C : q c] :=
  (PMF.uniformOfFintype C).toOuterMeasure.mono fun c hc => h c hc

/-- A uniform probability read through an equivalence of the sample spaces. -/
theorem probUniform_equiv {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ≃ β) (p : α → Prop) : Pr[a ← α : p a] = Pr[b ← β : p (e.symm b)] := by
  classical
  rw [probUniform_eq_card_div, probUniform_eq_card_div, Fintype.card_congr e]
  congr 2
  exact_mod_cast Finset.card_equiv e fun a => by simp

/-! ### Many subterms -/

/-- **`m` subterms composed by `k`**: `c 0` composed with the rest, ending with `nil`. With
`k = .par` the subterms run side by side (`SPTerm.parN`); with `k = .seq` they run one after the
other (`SPTerm.chainN`). -/
def SPTerm.nodeN (k : Comp) : (m : ℕ) → (Fin m → SPTerm ι) → SPTerm ι
  | 0, _ => nil
  | m + 1, c => node k (c 0) (nodeN k m fun i => c i.succ)

/-- **`m` subterms side by side.** -/
abbrev SPTerm.parN (m : ℕ) (c : Fin m → SPTerm ι) : SPTerm ι := SPTerm.nodeN .par m c

/-- **`m` subterms one after the other.** -/
abbrev SPTerm.chainN (m : ℕ) (c : Fin m → SPTerm ι) : SPTerm ι := SPTerm.nodeN .seq m c

/-- The conjunction of verifiers of the subterms, each on its part of the transcript. -/
def verifierN {Stmt : Type} (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} →
    (∀ i, Stmt → FullTr P (c i) → Bool) → Stmt → FullTr P (SPTerm.nodeN k m c) → Bool
  | 0, _, _, _, _ => true
  | m + 1, _, V, x, f => V 0 x f.left && verifierN k m (fun i => V i.succ) x f.right

/-! ### Causal pasts, extractors and state functions -/

variable (P) in
/-- **The causal past of a challenge**: the causal context of its leaf and the leaf's messages
before the challenge round. -/
structure CausalPast {t : SPTerm ι} (c : ChIdx P t) where
  /-- The full transcripts of the leaves sequenced before. -/
  ctx : CausalCtx P c.leaf
  /-- The leaf's own messages before the challenge round. -/
  own : (P c.leaf.label).Transcript c.idx.1.castSucc

/-- The causal past of a challenge read off a composite transcript. -/
def FullTr.past {t : SPTerm ι} (f : FullTr P t) (c : ChIdx P t) : CausalPast P c :=
  ⟨f.ctx c.leaf, (f c.leaf).take c.idx.1.castSucc (Fin.le_last _)⟩

variable (P) in
/-- **A causal one-shot extractor**: a candidate witness from the statement and the causal past of
a challenge. The causal analogue of `Extractor`. It must run in polynomial time (CMS19 Definition
8.5 asks for a polynomial-time extractor); as for `Extractor`, every value is a named definition
whose docstring has a "Running time" paragraph arguing polynomial running time in the number of
components, the transcript lengths and the running times of the extractors it calls; the Lean
lint `scripts/CostLint.lean` checks that the paragraph is present. -/
structure CausalExtractor (t : SPTerm ι) (Stmt Wit : Type) where
  /-- The candidate witness at the causal past of a challenge. -/
  extract : (c : ChIdx P t) → Stmt → CausalPast P c → Wit

/-- A causal extractor applies as a function. -/
instance {t : SPTerm ι} {Stmt Wit : Type} :
    CoeFun (CausalExtractor P t Stmt Wit) fun _ => (c : ChIdx P t) → Stmt → CausalPast P c → Wit :=
  ⟨CausalExtractor.extract⟩

variable (P) in
/-- **A causal state function**: for each leaf, a proposition about the statement, the leaf's
causal context and a prefix of the leaf's own transcript. Not required to be efficient. -/
abbrev CausalStateFn (t : SPTerm ι) (Stmt : Type) : Type :=
  (p : t.Leaf) → (k : Fin (n p.label + 1)) → Stmt → CausalCtx P p →
    (P p.label).Transcript k → Prop

/-- **The challenge `ch` at the causal past `past` of `c` moves the state from false to true**:
the leaf's state is false on its prefix before the challenge round and true after appending
`ch`. -/
def FlipAt {t : SPTerm ι} {Stmt : Type} (S : CausalStateFn P t Stmt) (c : ChIdx P t) (x : Stmt)
    (past : CausalPast P c) (ch : c.Challenge) : Prop :=
  ¬ S c.leaf c.idx.1.castSucc x past.ctx past.own ∧
    S c.leaf c.idx.1.succ x past.ctx ((P c.leaf.label).concat past.own ch)

/-- **Causal round-by-round soundness** of the state function `S` at the causal extractor `E` for
`rel`, with per-challenge errors `ε` that may depend on the statement, reducing the input claim
`claim` to the output claim `claimOut` (module docstring). -/
structure CausalRBRStmt [∀ j (i : (P j).ChallengeIdx), Fintype ((P j).Challenge i)]
    [∀ j (i : (P j).ChallengeIdx), Nonempty ((P j).Challenge i)] {t : SPTerm ι} {Stmt Wit : Type}
    (rel : Set (Stmt × Wit)) (E : CausalExtractor P t Stmt Wit) (S : CausalStateFn P t Stmt)
    (ε : Stmt → ChIdx P t → ℝ≥0) (claim : Stmt → Prop) (claimOut : Stmt → FullTr P t → Prop) :
    Prop where
  /-- When the output claim holds, the input claim fails and the extractor fails on the causal
  past of every challenge, some challenge moves its leaf's state from false to true. -/
  exists_flip : ∀ x (f : FullTr P t), claimOut x f → ¬ claim x →
    (∀ c, (x, E c x (f.past c)) ∉ rel) → ∃ c, FlipAt S c x (f.past c) (f.challenges c)
  /-- At every causal past of every challenge, a uniform fresh challenge moves the state from
  false to true while the extractor fails on the past with probability at most `ε x c`. -/
  rbr : ∀ (c : ChIdx P t) (x : Stmt) (past : CausalPast P c),
    Pr[ch ← c.Challenge : (x, E c x past) ∉ rel ∧ FlipAt S c x past ch] ≤ ε x c

/-- **Causal round-by-round soundness** with per-challenge errors `ε` that do not depend on the
statement (`CausalRBRStmt` at the constant errors). -/
abbrev CausalRBR [∀ j (i : (P j).ChallengeIdx), Fintype ((P j).Challenge i)]
    [∀ j (i : (P j).ChallengeIdx), Nonempty ((P j).Challenge i)] {t : SPTerm ι} {Stmt Wit : Type}
    (rel : Set (Stmt × Wit)) (E : CausalExtractor P t Stmt Wit) (S : CausalStateFn P t Stmt)
    (ε : ChIdx P t → ℝ≥0) (claim : Stmt → Prop) (claimOut : Stmt → FullTr P t → Prop) : Prop :=
  CausalRBRStmt rel E S (fun _ => ε) claim claimOut

/-- **Causal round-by-round knowledge soundness** of the composite verifier `V` with per-challenge
errors `ε` that may depend on the statement (the paper's `def:rbr`): `CausalRBRStmt` with the input
claim false and the output claim that `V` accepts. -/
abbrev CausalRBRKnowledgeSoundStmt [∀ j (i : (P j).ChallengeIdx), Fintype ((P j).Challenge i)]
    [∀ j (i : (P j).ChallengeIdx), Nonempty ((P j).Challenge i)] {t : SPTerm ι} {Stmt Wit : Type}
    (rel : Set (Stmt × Wit)) (V : Stmt → FullTr P t → Bool) (E : CausalExtractor P t Stmt Wit)
    (S : CausalStateFn P t Stmt) (ε : Stmt → ChIdx P t → ℝ≥0) : Prop :=
  CausalRBRStmt rel E S ε (fun _ => False) fun x f => V x f = true

/-- **Causal round-by-round knowledge soundness** of the composite verifier `V` with per-challenge
errors `ε` that do not depend on the statement: `CausalRBR` with the input claim false and the
output claim that `V` accepts (`CausalRBRKnowledgeSoundStmt` at the constant errors). -/
abbrev CausalRBRKnowledgeSound [∀ j (i : (P j).ChallengeIdx), Fintype ((P j).Challenge i)]
    [∀ j (i : (P j).ChallengeIdx), Nonempty ((P j).Challenge i)] {t : SPTerm ι} {Stmt Wit : Type}
    (rel : Set (Stmt × Wit)) (V : Stmt → FullTr P t → Bool) (E : CausalExtractor P t Stmt Wit)
    (S : CausalStateFn P t Stmt) (ε : ChIdx P t → ℝ≥0) : Prop :=
  CausalRBR rel E S ε (fun _ => False) fun x f => V x f = true

end GordieHowe.IOP
