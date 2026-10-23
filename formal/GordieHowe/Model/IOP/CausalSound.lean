-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.Causal
public import GordieHowe.Model.IOP.Append
public import GordieHowe.Model.IOP.ClaimReduction
public import GordieHowe.Headline

@[expose] public section

/-!
# Causal round-by-round soundness: one component, sequence, parallel

* `CausalRBR.seq`: a composite `a` reducing `claim₁` to `claimOut₁`, followed by a composite `b`
  on statements that carry `a`'s full transcripts, whose input claim implies `claimOut₁` (`h`, as
  in `ClaimReduction.append`), is causally round-by-round sound for `seq a b` with every challenge
  keeping its error (`errNode`). The extractor is `CausalExtractor.seq`: `b`'s extractor may read
  `a`'s transcripts, which is how an extractor is composed through the prefix's extractor.
* `GordieHowe.IOP.CausalRBR.par`, `CausalRBR.nodeN`: composites side by side, or one after the other without
  reading each other's transcripts, reduce the conjunction of their
  input claims to the conjunction of their output claims; every challenge keeps its error.
* One component: `CausalRBR.ofClaimPhase` (a claim-producing phase with an extractor),
  `CausalRBR.ofKnowledge` (round-by-round knowledge soundness) and `CausalRBR.ofLanguage` (the
  state of a knowledge-sound component, conjoined with "the component statement has no witness",
  which reduces "the component statement has a witness" to acceptance without using the
  component's extractor).
* `CausalRBRStmt.seq`, `CausalRBRStmt.par`, `CausalRBRStmt.nodeN`: the same compositions at errors
  that depend on the statement (`CausalRBRStmt`); the `CausalRBR` forms are their case at errors
  that do not.
-/

namespace GordieHowe.IOP

open scoped NNReal
open SPTerm

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}

/-! ### Combinators on a node -/

/-- **The error of a node's challenge**: the first subterm's error at its challenges and the
second's at its own. -/
def errNode {k : Comp} {a b : SPTerm ι} (ε₁ : ChIdx P a → ℝ≥0) (ε₂ : ChIdx P b → ℝ≥0) :
    ChIdx P (node k a b) → ℝ≥0
  | ⟨.left p, i⟩ => ε₁ ⟨p, i⟩
  | ⟨.right p, i⟩ => ε₂ ⟨p, i⟩

@[simp] theorem errNode_left {k : Comp} {a b : SPTerm ι} (ε₁ : ChIdx P a → ℝ≥0)
    (ε₂ : ChIdx P b → ℝ≥0) (c : ChIdx P a) : errNode (k := k) ε₁ ε₂ c.left = ε₁ c := rfl
@[simp] theorem errNode_right {k : Comp} {a b : SPTerm ι} (ε₁ : ChIdx P a → ℝ≥0)
    (ε₂ : ChIdx P b → ℝ≥0) (c : ChIdx P b) : errNode (k := k) ε₁ ε₂ c.right = ε₂ c := rfl

/-- A bound on both subterms' errors bounds the node's. -/
theorem errNode_le {k : Comp} {a b : SPTerm ι} {ε₁ : ChIdx P a → ℝ≥0} {ε₂ : ChIdx P b → ℝ≥0}
    {δ : ℝ≥0} (h₁ : ∀ c, ε₁ c ≤ δ) (h₂ : ∀ c, ε₂ c ≤ δ) : ∀ c, errNode (k := k) ε₁ ε₂ c ≤ δ
  | ⟨.left p, i⟩ => h₁ ⟨p, i⟩
  | ⟨.right p, i⟩ => h₂ ⟨p, i⟩

/-- The statements of a second subterm after a first subterm `a`: the statement and `a`'s full
transcripts. -/
abbrev SeqStmt (Stmt : Type) (P : (j : ι) → ProtocolSpec (n j)) (a : SPTerm ι) : Type :=
  Stmt × FullTr P a

/-- A relation read on the statement part of a `SeqStmt`. -/
def Set.onStmt {Stmt Wit : Type} {a : SPTerm ι} (rel : Set (Stmt × Wit)) :
    Set (SeqStmt Stmt P a × Wit) :=
  {p | (p.1.1, p.2) ∈ rel}

@[simp] theorem Set.mem_onStmt {Stmt Wit : Type} {a : SPTerm ι} {rel : Set (Stmt × Wit)}
    {x : Stmt} {f : FullTr P a} {w : Wit} : ((x, f), w) ∈ Set.onStmt (P := P) rel ↔ (x, w) ∈ rel :=
  Iff.rfl

namespace CausalExtractor

variable {Stmt Wit : Type} {a b : SPTerm ι}

/-- **The extractor of `seq a b`**: `E₁` at `a`'s challenges, and `E₂` at `b`'s, reading the
statement together with `a`'s full transcripts from the causal context.

Running time: one call of `E₁` or of `E₂` (their own Running time paragraphs) on the causal past
with the context restricted to the subterm, a selection of entries linear in the number of leaves
and the transcript lengths; polynomial when `E₁` and `E₂` are. This running time is argued here, not
proved in Lean. -/
def seq (E₁ : CausalExtractor P a Stmt Wit) (E₂ : CausalExtractor P b (SeqStmt Stmt P a) Wit) :
    CausalExtractor P (SPTerm.seq a b) Stmt Wit where
  extract
    | ⟨.left p, i⟩, x, past => E₁ ⟨p, i⟩ x ⟨past.ctx.ofLeft, past.own⟩
    | ⟨.right p, i⟩, x, past => E₂ ⟨p, i⟩ (x, past.ctx.fst) ⟨past.ctx.ofRight, past.own⟩

/-- **The extractor of a node whose second part does not read the first's transcripts**: `E₁` at
`a`'s challenges and `E₂` at `b`'s.

Running time: one call of `E₁` or of `E₂` (their own Running time paragraphs) on the causal past
with the context restricted to the subterm, a selection of entries linear in the number of leaves
and the transcript lengths; polynomial when `E₁` and `E₂` are. This running time is argued here, not
proved in Lean. -/
def par {k : Comp} (E₁ : CausalExtractor P a Stmt Wit) (E₂ : CausalExtractor P b Stmt Wit) :
    CausalExtractor P (node k a b) Stmt Wit where
  extract
    | ⟨.left p, i⟩, x, past => E₁ ⟨p, i⟩ x ⟨past.ctx.ofLeft, past.own⟩
    | ⟨.right p, i⟩, x, past => E₂ ⟨p, i⟩ x ⟨past.ctx.ofRight, past.own⟩

end CausalExtractor

namespace CausalStateFn

variable {Stmt : Type} {a b : SPTerm ι}

/-- The state function of `seq a b`: `S₁` at `a`'s leaves, `S₂` at `b`'s on the statement with
`a`'s full transcripts. -/
def seq (S₁ : CausalStateFn P a Stmt) (S₂ : CausalStateFn P b (SeqStmt Stmt P a)) :
    CausalStateFn P (SPTerm.seq a b) Stmt
  | .left p, k, x, ctx, tr => S₁ p k x ctx.ofLeft tr
  | .right p, k, x, ctx, tr => S₂ p k (x, ctx.fst) ctx.ofRight tr

/-- The state function of a node whose second part does not read the first's transcripts: `S₁`
at `a`'s leaves, `S₂` at `b`'s. -/
def par {k : Comp} (S₁ : CausalStateFn P a Stmt) (S₂ : CausalStateFn P b Stmt) :
    CausalStateFn P (node k a b) Stmt
  | .left p, r, x, ctx, tr => S₁ p r x ctx.ofLeft tr
  | .right p, r, x, ctx, tr => S₂ p r x ctx.ofRight tr

end CausalStateFn

/-! ### Sequence and parallel -/

section Node

variable [∀ j (i : (P j).ChallengeIdx), Fintype ((P j).Challenge i)]
  [∀ j (i : (P j).ChallengeIdx), Nonempty ((P j).Challenge i)] {Stmt Wit : Type} {a b : SPTerm ι}
  {rel : Set (Stmt × Wit)}

/-- **Sequence, at errors of the statement.** `a` reduces `claim₁` to `claimOut₁`; `b`, on
statements carrying `a`'s full transcripts, reduces `claim₂` to `claimOut₂` at errors read on the
statement part (`ε₂ ∘ Prod.fst`), and `claim₂` implies `claimOut₁` (`h`). Then `seq a b` reduces
`claim₁` to `claimOut₂` read on the transcripts, and at every statement every challenge keeps its
error. -/
theorem CausalRBRStmt.seq {E₁ : CausalExtractor P a Stmt Wit}
    {E₂ : CausalExtractor P b (SeqStmt Stmt P a) Wit} {S₁ : CausalStateFn P a Stmt}
    {S₂ : CausalStateFn P b (SeqStmt Stmt P a)} {ε₁ : Stmt → ChIdx P a → ℝ≥0}
    {ε₂ : Stmt → ChIdx P b → ℝ≥0} {claim₁ : Stmt → Prop} {claimOut₁ : Stmt → FullTr P a → Prop}
    {claim₂ : SeqStmt Stmt P a → Prop} {claimOut₂ : SeqStmt Stmt P a → FullTr P b → Prop}
    (h₁ : CausalRBRStmt rel E₁ S₁ ε₁ claim₁ claimOut₁)
    (h₂ : CausalRBRStmt (Set.onStmt rel) E₂ S₂ (ε₂ ∘ Prod.fst) claim₂ claimOut₂)
    (h : ∀ x f, claim₂ (x, f) → claimOut₁ x f) :
    CausalRBRStmt rel (E₁.seq E₂) (S₁.seq S₂) (fun x => errNode (ε₁ x) (ε₂ x)) claim₁
      fun x f => claimOut₂ (x, f.left) f.right where
  exists_flip x f hout hclaim hE := by
    by_cases hc₂ : claim₂ (x, f.left)
    · obtain ⟨c, hc⟩ := h₁.exists_flip x f.left (h x _ hc₂) hclaim fun c => hE c.left
      exact ⟨c.left, hc⟩
    · obtain ⟨c, hc⟩ := h₂.exists_flip (x, f.left) f.right hout hc₂ fun c => hE c.right
      exact ⟨c.right, hc⟩
  rbr c x past := by
    rcases ChIdx.left_or_right c with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact h₁.rbr c x ⟨past.ctx.ofLeft, past.own⟩
    · exact h₂.rbr c (x, past.ctx.fst) ⟨past.ctx.ofRight, past.own⟩

/-- **Sequence.** `a` reduces `claim₁` to `claimOut₁`; `b`, on statements carrying `a`'s full
transcripts, reduces `claim₂` to `claimOut₂`, and `claim₂` implies `claimOut₁` (`h`). Then
`seq a b` reduces `claim₁` to `claimOut₂` read on the transcripts, and every challenge keeps its
error. `CausalRBRStmt.seq` at errors that do not depend on the statement. -/
theorem CausalRBR.seq {E₁ : CausalExtractor P a Stmt Wit}
    {E₂ : CausalExtractor P b (SeqStmt Stmt P a) Wit} {S₁ : CausalStateFn P a Stmt}
    {S₂ : CausalStateFn P b (SeqStmt Stmt P a)} {ε₁ : ChIdx P a → ℝ≥0} {ε₂ : ChIdx P b → ℝ≥0}
    {claim₁ : Stmt → Prop} {claimOut₁ : Stmt → FullTr P a → Prop}
    {claim₂ : SeqStmt Stmt P a → Prop} {claimOut₂ : SeqStmt Stmt P a → FullTr P b → Prop}
    (h₁ : CausalRBR rel E₁ S₁ ε₁ claim₁ claimOut₁)
    (h₂ : CausalRBR (Set.onStmt rel) E₂ S₂ ε₂ claim₂ claimOut₂)
    (h : ∀ x f, claim₂ (x, f) → claimOut₁ x f) :
    CausalRBR rel (E₁.seq E₂) (S₁.seq S₂) (errNode ε₁ ε₂) claim₁
      fun x f => claimOut₂ (x, f.left) f.right :=
  CausalRBRStmt.seq (ε₂ := fun _ => ε₂) h₁ h₂ h

/-- **Independent parts, at errors of the statement.** Composites `a` and `b` on the same
statements, composed by a node in which `b` does not read `a`'s transcripts (side by side, or `b`
after `a`), reduce the conjunction of their input claims to the conjunction of their output claims,
and at every statement every challenge keeps its error. -/
theorem CausalRBRStmt.par {k : Comp} {E₁ : CausalExtractor P a Stmt Wit}
    {E₂ : CausalExtractor P b Stmt Wit}
    {S₁ : CausalStateFn P a Stmt} {S₂ : CausalStateFn P b Stmt} {ε₁ : Stmt → ChIdx P a → ℝ≥0}
    {ε₂ : Stmt → ChIdx P b → ℝ≥0} {claim₁ claim₂ : Stmt → Prop}
    {claimOut₁ : Stmt → FullTr P a → Prop} {claimOut₂ : Stmt → FullTr P b → Prop}
    (h₁ : CausalRBRStmt rel E₁ S₁ ε₁ claim₁ claimOut₁)
    (h₂ : CausalRBRStmt rel E₂ S₂ ε₂ claim₂ claimOut₂) :
    CausalRBRStmt rel (E₁.par E₂) (S₁.par (k := k) S₂) (fun x => errNode (ε₁ x) (ε₂ x))
      (fun x => claim₁ x ∧ claim₂ x)
      fun x f => claimOut₁ x f.left ∧ claimOut₂ x f.right where
  exists_flip x f hout hclaim hE := by
    by_cases hc₁ : claim₁ x
    · obtain ⟨c, hc⟩ := h₂.exists_flip x f.right hout.2 (fun hc₂ => hclaim ⟨hc₁, hc₂⟩)
        fun c => hE c.right
      exact ⟨c.right, hc⟩
    · obtain ⟨c, hc⟩ := h₁.exists_flip x f.left hout.1 hc₁ fun c => hE c.left
      exact ⟨c.left, hc⟩
  rbr c x past := by
    rcases ChIdx.left_or_right c with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact h₁.rbr c x ⟨past.ctx.ofLeft, past.own⟩
    · exact h₂.rbr c x ⟨past.ctx.ofRight, past.own⟩

/-- **Independent parts.** Composites `a` and `b` on the same statements, composed by a node in
which `b` does not read `a`'s transcripts (side by side, or `b` after `a`), reduce the conjunction
of their input claims to the conjunction of their output claims, and every challenge keeps its
error. `CausalRBRStmt.par` at errors that do not depend on the statement. -/
theorem CausalRBR.par {k : Comp} {E₁ : CausalExtractor P a Stmt Wit}
    {E₂ : CausalExtractor P b Stmt Wit}
    {S₁ : CausalStateFn P a Stmt} {S₂ : CausalStateFn P b Stmt} {ε₁ : ChIdx P a → ℝ≥0}
    {ε₂ : ChIdx P b → ℝ≥0} {claim₁ claim₂ : Stmt → Prop} {claimOut₁ : Stmt → FullTr P a → Prop}
    {claimOut₂ : Stmt → FullTr P b → Prop}
    (h₁ : CausalRBR rel E₁ S₁ ε₁ claim₁ claimOut₁) (h₂ : CausalRBR rel E₂ S₂ ε₂ claim₂ claimOut₂) :
    CausalRBR rel (E₁.par E₂) (S₁.par (k := k) S₂) (errNode ε₁ ε₂)
      (fun x => claim₁ x ∧ claim₂ x)
      fun x f => claimOut₁ x f.left ∧ claimOut₂ x f.right :=
  CausalRBRStmt.par h₁ h₂

/-- A stronger input claim and a stronger output claim, at the same state, extractor and errors of
the statement. -/
theorem CausalRBRStmt.mono {t : SPTerm ι} {E : CausalExtractor P t Stmt Wit}
    {S : CausalStateFn P t Stmt} {ε : Stmt → ChIdx P t → ℝ≥0} {claim claim' : Stmt → Prop}
    {claimOut claimOut' : Stmt → FullTr P t → Prop}
    (h : CausalRBRStmt rel E S ε claim claimOut) (hclaim : ∀ x, claim x → claim' x)
    (hout : ∀ x f, claimOut' x f → claimOut x f) : CausalRBRStmt rel E S ε claim' claimOut' where
  exists_flip x f ho hc hE := h.exists_flip x f (hout x f ho) (fun h' => hc (hclaim x h')) hE
  rbr := h.rbr

/-- A stronger input claim and a stronger output claim, at the same state, extractor and errors. -/
theorem CausalRBR.mono {t : SPTerm ι} {E : CausalExtractor P t Stmt Wit}
    {S : CausalStateFn P t Stmt} {ε : ChIdx P t → ℝ≥0} {claim claim' : Stmt → Prop}
    {claimOut claimOut' : Stmt → FullTr P t → Prop}
    (h : CausalRBR rel E S ε claim claimOut) (hclaim : ∀ x, claim x → claim' x)
    (hout : ∀ x f, claimOut' x f → claimOut x f) : CausalRBR rel E S ε claim' claimOut' :=
  CausalRBRStmt.mono h hclaim hout

/-- **Extractors with the same values** give the same reduction. -/
theorem CausalRBR.congr_extractor {t : SPTerm ι} {E E' : CausalExtractor P t Stmt Wit}
    {S : CausalStateFn P t Stmt} {ε : ChIdx P t → ℝ≥0} {claim : Stmt → Prop}
    {claimOut : Stmt → FullTr P t → Prop} (h : CausalRBR rel E S ε claim claimOut)
    (hE : ∀ c x past, E c x past = E' c x past) : CausalRBR rel E' S ε claim claimOut where
  exists_flip x f ho hc hE' := h.exists_flip x f ho hc fun c => by rw [hE]; exact hE' c
  rbr c x past := by
    simp only [← hE]
    exact h.rbr c x past

/-- **An extractor's witness mapped by `g`**, which may read the statement.

Running time: one run of `E` and one application of `g`. This running time is argued here, not
proved in Lean. -/
def CausalExtractor.mapWit {t : SPTerm ι} {Wit' : Type} (E : CausalExtractor P t Stmt Wit)
    (g : Stmt → Wit → Wit') : CausalExtractor P t Stmt Wit' :=
  ⟨fun c x past => g x (E c x past)⟩

/-- **A reduction for `rel` is one for `rel'`** at the extractor mapped by `g`, when `g` maps the
witnesses of `rel` to witnesses of `rel'`. -/
theorem CausalRBR.mapWit {t : SPTerm ι} {Wit' : Type} {rel' : Set (Stmt × Wit')}
    {E : CausalExtractor P t Stmt Wit} {S : CausalStateFn P t Stmt} {ε : ChIdx P t → ℝ≥0}
    {claim : Stmt → Prop} {claimOut : Stmt → FullTr P t → Prop}
    (h : CausalRBR rel E S ε claim claimOut) {g : Stmt → Wit → Wit'}
    (hg : ∀ x w, (x, w) ∈ rel → (x, g x w) ∈ rel') :
    CausalRBR rel' (E.mapWit g) S ε claim claimOut where
  exists_flip x f ho hc hE := h.exists_flip x f ho hc fun c hw => hE c (hg _ _ hw)
  rbr c x past := (probUniform_mono fun ch hch => ⟨fun hw => hch.1 (hg _ _ hw), hch.2⟩).trans
    (h.rbr c x past)

/-- **A claim on the statement alone** conjoined with both claims: the same state, extractor and
errors. A fact the composite's rounds do not touch (fixed affine claims of a domain) travels this
way from the input claim to the output claim. -/
theorem CausalRBR.and_stmt {t : SPTerm ι} {E : CausalExtractor P t Stmt Wit}
    {S : CausalStateFn P t Stmt} {ε : ChIdx P t → ℝ≥0} {claim : Stmt → Prop}
    {claimOut : Stmt → FullTr P t → Prop} (h : CausalRBR rel E S ε claim claimOut)
    (R : Stmt → Prop) :
    CausalRBR rel E S ε (fun x => claim x ∧ R x) fun x f => claimOut x f ∧ R x where
  exists_flip x f ho hc hE := h.exists_flip x f ho.1 (fun h' => hc ⟨h', ho.2⟩) hE
  rbr := h.rbr

/-- **Sequence with a check on the first part**: as `CausalRBR.seq`, where the second part's
input claim gives, on first-part transcripts passing the check `G` (the verifier's own check after
the prefix), the first part's output claim or a witness from the second part's extractor at one of
its challenges, and the output claim conjoins `G`. The second alternative covers a first part whose
claim can only become true at a challenge it does not have: the second part's challenges then carry
the extraction. -/
theorem CausalRBR.seq_guard {E₁ : CausalExtractor P a Stmt Wit}
    {E₂ : CausalExtractor P b (SeqStmt Stmt P a) Wit} {S₁ : CausalStateFn P a Stmt}
    {S₂ : CausalStateFn P b (SeqStmt Stmt P a)} {ε₁ : ChIdx P a → ℝ≥0} {ε₂ : ChIdx P b → ℝ≥0}
    {claim₁ : Stmt → Prop} {claimOut₁ : Stmt → FullTr P a → Prop}
    {claim₂ : SeqStmt Stmt P a → Prop} {claimOut₂ : SeqStmt Stmt P a → FullTr P b → Prop}
    (h₁ : CausalRBR rel E₁ S₁ ε₁ claim₁ claimOut₁)
    (h₂ : CausalRBR (Set.onStmt rel) E₂ S₂ ε₂ claim₂ claimOut₂) (G : Stmt → FullTr P a → Prop)
    (h : ∀ x f (g : FullTr P b), claim₂ (x, f) → G x f →
      claimOut₁ x f ∨ ∃ c, (x, E₂ c (x, f) (g.past c)) ∈ rel) :
    CausalRBR rel (E₁.seq E₂) (S₁.seq S₂) (errNode ε₁ ε₂) claim₁
      fun x f => claimOut₂ (x, f.left) f.right ∧ G x f.left where
  exists_flip x f hout hclaim hE := by
    by_cases hc₂ : claim₂ (x, f.left)
    · rcases h x f.left f.right hc₂ hout.2 with hout₁ | ⟨c, hc⟩
      · obtain ⟨c, hc⟩ := h₁.exists_flip x f.left hout₁ hclaim fun c => hE c.left
        exact ⟨c.left, hc⟩
      · exact (hE c.right hc).elim
    · obtain ⟨c, hc⟩ := h₂.exists_flip (x, f.left) f.right hout.1 hc₂ fun c => hE c.right
      exact ⟨c.right, hc⟩
  rbr c x past := by
    rcases ChIdx.left_or_right c with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact h₁.rbr c x ⟨past.ctx.ofLeft, past.own⟩
    · exact h₂.rbr c (x, past.ctx.fst) ⟨past.ctx.ofRight, past.own⟩

end Node

/-! ### One component -/

/-- **A challenge round moves a family of prefix propositions from false to true** on a full
transcript, when the family is false on the empty prefix, true on the full transcript and never
made true by a prover message. The prover-free form of `KnowledgeStateFunction.exists_flip`. -/
theorem ProtocolSpec.Transcript.exists_flip {m : ℕ} {Q : ProtocolSpec m}
    (S : (k : Fin (m + 1)) → Q.Transcript k → Prop)
    (next : ∀ k : Fin m, Q.dir k = .P_to_V → ∀ (tr : Q.Transcript k.castSucc) msg,
      ¬ S k.castSucc tr → ¬ S k.succ (Q.concat tr msg))
    (tr : Q.Transcript (Fin.last m)) (h0 : ¬ S 0 (tr.take 0 (Fin.zero_le _)))
    (hlast : S (Fin.last m) tr) :
    ∃ i : Q.ChallengeIdx, ¬ S i.1.castSucc (tr.take i.1.castSucc (Fin.le_last _)) ∧
      S i.1.succ (Q.concat (tr.take i.1.castSucc (Fin.le_last _)) (tr i.1)) := by
  by_contra hne
  push Not at hne
  have hall : ∀ k : Fin (m + 1), ¬ S k (tr.take k (Fin.le_last _)) := by
    intro k
    induction k using Fin.induction with
    | zero => exact h0
    | succ j ih =>
      have e : Q.concat (tr.take j.castSucc (Fin.le_last _)) (tr j) =
          tr.take j.succ (Fin.le_last _) :=
        Q.concat_take_succ (tr.take j.succ (Fin.le_last _))
      cases hd : Q.dir j with
      | P_to_V =>
        have key := next j hd _ (tr j) ih
        rwa [e] at key
      | V_to_P =>
        have key := hne ⟨j, hd⟩ ih
        rw [e] at key
        exact fun h => key h
  exact hall (Fin.last m) hlast

/-- **The error of a one-component composite**: the component's error at its challenge round. -/
def errLeaf {j : ι} (ε : (P j).ChallengeIdx → ℝ≥0) : ChIdx P (leaf j) → ℝ≥0
  | ⟨.here _, i⟩ => ε i

/-- A bound on the component's errors bounds the one-component composite's. -/
theorem errLeaf_le {j : ι} {ε : (P j).ChallengeIdx → ℝ≥0} {δ : ℝ≥0} (h : ∀ i, ε i ≤ δ) :
    ∀ c, errLeaf ε c ≤ δ
  | ⟨.here _, i⟩ => h i

/-- The state function of a one-component composite: the component's state, which has no causal
context. -/
def CausalStateFn.ofLeaf {j : ι} {Stmt : Type}
    (S : (k : Fin (n j + 1)) → Stmt → (P j).Transcript k → Prop) : CausalStateFn P (leaf j) Stmt
  | .here _, k, x, _, tr => S k x tr

/-- **The extractor of a one-component composite**: the component's one-shot extractor on the
leaf's prefix before the challenge round.

Running time: one call of `E` (its own Running time paragraph) on the leaf's own prefix;
polynomial when `E` is. This running time is argued here, not proved in Lean. -/
def CausalExtractor.ofLeaf {j : ι} {Stmt Wit : Type} (E : Extractor (P j) Stmt Wit) :
    CausalExtractor P (leaf j) Stmt Wit where
  extract
    | ⟨.here _, i⟩, x, past => E i.1.castSucc x past.own

/-- **An extractor that reads only the statement**: `g` on the statement. Used after a prefix
whose extractor reads the prefix transcript carried in the statement (`SeqStmt`).

Running time: one evaluation of `g`; polynomial when `g` is. This running time is argued here, not
proved in Lean. -/
def CausalExtractor.ofStmt {t : SPTerm ι} {Stmt Wit : Type} (g : Stmt → Wit) :
    CausalExtractor P t Stmt Wit where
  extract _ x _ := g x

/-- **The causal context of a one-component composite's leaf**: it is empty, since no leaf is
sequenced before it. -/
def CausalCtx.here (j : ι) : CausalCtx P (Leaf.here j) :=
  fun ⟨q, hq⟩ => by
    cases q
    exact (Leaf.not_before_self _ hq).elim

/-- A one-component composite's leaf has one causal context. -/
theorem CausalCtx.eq_here {j : ι} (ctx : CausalCtx P (Leaf.here j)) : ctx = CausalCtx.here j :=
  funext fun ⟨q, hq⟩ => by
    cases q
    exact (Leaf.not_before_self _ hq).elim

/-- A causal past of a challenge of a one-component composite is determined by the leaf's own
messages. -/
theorem CausalPast.eq_here {j : ι} {i : (P j).ChallengeIdx}
    (past : CausalPast P (⟨.here j, i⟩ : ChIdx P (leaf j))) :
    past = ⟨CausalCtx.here j, past.own⟩ := by
  obtain ⟨ctx, own⟩ := past
  rw [CausalCtx.eq_here ctx]

/-- On a one-component composite, a flip reads only the leaf's own messages. -/
theorem flipAt_here_iff {j : ι} {Stmt : Type} {S : CausalStateFn P (leaf j) Stmt}
    {i : (P j).ChallengeIdx} {x : Stmt} {past : CausalPast P (⟨.here j, i⟩ : ChIdx P (leaf j))}
    {ch : (P j).Challenge i} :
    FlipAt S ⟨.here j, i⟩ x past ch ↔ ¬ S (.here j) i.1.castSucc x (CausalCtx.here j) past.own ∧
      S (.here j) i.1.succ x (CausalCtx.here j) ((P j).concat past.own ch) := by
  rw [CausalPast.eq_here past]
  rfl

/-- **The composite transcript of a one-component composite** with the leaf's transcript `tr`. -/
def FullTr.ofHere {j : ι} (tr : (P j).Transcript (Fin.last (n j))) : FullTr P (leaf j)
  | .here _ => tr

/-- **The flip event at challenge round `i`** of a one-component composite, read on a transcript
`tr` of the first `i + 1` rounds: the extractor `E` succeeds on the prefix before round `i`, or the
causal state `S` is false on that prefix and true on `tr`. -/
def TotalFlip {j : ι} {Stmt Wit : Type} (rel : Set (Stmt × Wit)) (E : Extractor (P j) Stmt Wit)
    (S : CausalStateFn P (leaf j) Stmt) (i : (P j).ChallengeIdx) (x : Stmt)
    (tr : (P j).Transcript i.1.succ) : Prop :=
  (x, E i.1.castSucc x (tr.take i.1.castSucc (Fin.castSucc_le_succ _))) ∈ rel ∨
    ¬ S (.here j) i.1.castSucc x (CausalCtx.here j)
        (tr.take i.1.castSucc (Fin.castSucc_le_succ _)) ∧
      S (.here j) i.1.succ x (CausalCtx.here j) tr

/-- **The prefix state of a causal state on one component**: true on a prefix when the flip event
`TotalFlip` happens at some challenge round in it. Not required to be efficient. -/
def totalState {j : ι} {Stmt Wit : Type} (rel : Set (Stmt × Wit)) (E : Extractor (P j) Stmt Wit)
    (S : CausalStateFn P (leaf j) Stmt) (m : Fin (n j + 1)) (x : Stmt) (tr : (P j).Transcript m) :
    Prop :=
  ∃ (i : (P j).ChallengeIdx) (hi : i.1.succ ≤ m), TotalFlip rel E S i x (tr.take i.1.succ hi)

section Leaf

variable [∀ j (i : (P j).ChallengeIdx), Fintype ((P j).Challenge i)]
  [∀ j (i : (P j).ChallengeIdx), Nonempty ((P j).Challenge i)] {j : ι} {Stmt Wit : Type}
  {rel : Set (Stmt × Wit)}

open Classical in
/-- The round-by-round count of a claim-producing phase, as a probability. -/
theorem ClaimPhase.rbr_prob {ε : (P j).ChallengeIdx → ℝ≥0} (A : ClaimPhase (P j) Stmt Wit rel ε)
    (x : Stmt) (i : (P j).ChallengeIdx) (past : CausalPast P (⟨.here j, i⟩ : ChIdx P (leaf j))) :
    Pr[ch ← (P j).Challenge i : (x, A.E i.1.castSucc x past.own) ∉ rel ∧
      ¬ A.S i.1.castSucc x past.own ∧ A.S i.1.succ x ((P j).concat past.own ch)] ≤ ε i :=
  (card_le_iff_probUniform_le _ _ _).mp (A.rbr x i past.own)

open Classical in
/-- **A claim-producing phase as a one-component composite**: the phase's state, extractor and
errors; the input claim is false and the output claim is the phase's claim. -/
theorem CausalRBR.ofClaimPhase {ε : (P j).ChallengeIdx → ℝ≥0}
    (A : ClaimPhase (P j) Stmt Wit rel ε) :
    CausalRBR rel (CausalExtractor.ofLeaf A.E) (CausalStateFn.ofLeaf A.S) (errLeaf ε)
      (fun _ => False) fun x f => A.claim x (f (.here j)) where
  exists_flip x f hc _ _ := by
    obtain ⟨i, hi⟩ := ProtocolSpec.Transcript.exists_flip (fun k tr => A.S k x tr)
      (fun k hk tr msg => A.next k hk x tr msg) (f (.here j)) (A.empty x _) (A.full x _ hc)
    exact ⟨⟨.here j, i⟩, hi⟩
  rbr c x past := by
    obtain ⟨p, i⟩ := c
    cases p
    exact A.rbr_prob x i past

open Classical in
/-- The round-by-round count of a claim-proving phase, as a probability. -/
theorem ClaimProof.rbr_prob {ε : (P j).ChallengeIdx → ℝ≥0} (B : ClaimProof (P j) Stmt ε) (x : Stmt)
    (i : (P j).ChallengeIdx) (past : CausalPast P (⟨.here j, i⟩ : ChIdx P (leaf j))) :
    Pr[ch ← (P j).Challenge i : ¬ B.S i.1.castSucc x past.own ∧
      B.S i.1.succ x ((P j).concat past.own ch)] ≤ ε i :=
  (card_le_iff_probUniform_le _ _ _).mp (B.rbr x i past.own)

/-- **A claim-proving phase as a one-component composite**: the phase's state and errors, reducing
its claim to its verifier's acceptance, for every relation and extractor of the composite. -/
theorem CausalRBR.ofClaimProof {ε : (P j).ChallengeIdx → ℝ≥0} (B : ClaimProof (P j) Stmt ε)
    (rel : Set (Stmt × Wit)) (E : CausalExtractor P (leaf j) Stmt Wit) :
    CausalRBR rel E (CausalStateFn.ofLeaf B.S) (errLeaf ε) B.claim
      fun x f => B.V x (f (.here j)) = true where
  exists_flip x f hV hc _ := by
    obtain ⟨i, hi⟩ := ProtocolSpec.Transcript.exists_flip (fun k tr => B.S k x tr)
      (fun k hk tr msg => B.next k hk x tr msg) (f (.here j)) (B.start x _ hc) (B.full x _ hV)
    exact ⟨⟨.here j, i⟩, hi⟩
  rbr c x past := by
    obtain ⟨p, i⟩ := c
    cases p
    exact (probUniform_mono fun ch hch => hch.2).trans (B.rbr_prob x i past)

open Classical in
/-- **A claim reduction as a one-component composite**: on statements read through `σ`, the
reduction's state and errors reduce its input claim to its output claim on the leaf's transcript,
for every relation and extractor of the composite. A branch of a series–parallel composition (a masked reduction
leaving claims on the committed cells) enters the composite this way. -/
theorem CausalRBR.ofClaimReduction {Ctx : Type} {ε : (P j).ChallengeIdx → ℝ≥0}
    (R : ClaimReduction (P j) Ctx ε) (σ : Stmt → Ctx) (rel : Set (Stmt × Wit))
    (E : CausalExtractor P (leaf j) Stmt Wit) :
    CausalRBR rel E (CausalStateFn.ofLeaf fun k x tr => R.S k (σ x) tr) (errLeaf ε)
      (fun x => R.claim (σ x)) fun x f => R.claimOut (σ x) (f (.here j)) where
  exists_flip x f hout hc _ := by
    obtain ⟨i, hi⟩ := ProtocolSpec.Transcript.exists_flip (fun k tr => R.S k (σ x) tr)
      (fun k hk tr msg => R.next k hk (σ x) tr msg) (f (.here j)) (R.start (σ x) _ hc)
      (R.full (σ x) _ hout)
    exact ⟨⟨.here j, i⟩, hi⟩
  rbr c x past := by
    obtain ⟨p, i⟩ := c
    cases p
    exact (probUniform_mono fun ch hch => hch.2).trans
      ((card_le_iff_probUniform_le _ _ _).mp (R.rbr (σ x) i past.own))

open Classical in
/-- **A round-by-round knowledge-sound protocol as a one-component composite**, at errors that
may depend on the statement: the same extractor, state and errors, for the verifier read on the
leaf's transcript. -/
theorem CausalRBRStmt.ofKnowledge {V : Verifier (P j) Stmt} {E : Extractor (P j) Stmt Wit}
    {S : KnowledgeStateFunction V} {ε : Stmt → (P j).ChallengeIdx → ℝ≥0}
    (h : rbrKnowledgeSoundnessStmt rel V E S ε) :
    CausalRBRKnowledgeSoundStmt rel (fun x f => V x (f (.here j))) (CausalExtractor.ofLeaf E)
      (CausalStateFn.ofLeaf S.toFun) (fun x => errLeaf (ε x)) where
  exists_flip x f hV _ _ := by
    obtain ⟨i, hi⟩ := ProtocolSpec.Transcript.exists_flip (fun k tr => S.toFun k x tr)
      (fun k hk tr msg => S.toFun_next k hk x tr msg) (f (.here j)) (S.toFun_empty x _)
      (S.toFun_full x _ hV)
    exact ⟨⟨.here j, i⟩, hi⟩
  rbr c x past := by
    obtain ⟨p, i⟩ := c
    cases p
    exact h x i past.own

/-- **A round-by-round knowledge-sound protocol as a one-component composite**: the same
extractor, state and errors, for the verifier read on the leaf's transcript
(`CausalRBRStmt.ofKnowledge` at errors that do not depend on the statement). -/
theorem CausalRBR.ofKnowledge {V : Verifier (P j) Stmt} {E : Extractor (P j) Stmt Wit}
    {S : KnowledgeStateFunction V} {ε : (P j).ChallengeIdx → ℝ≥0}
    (h : rbrKnowledgeSoundness rel V E S ε) :
    CausalRBRKnowledgeSound rel (fun x f => V x (f (.here j))) (CausalExtractor.ofLeaf E)
      (CausalStateFn.ofLeaf S.toFun) (errLeaf ε) :=
  CausalRBRStmt.ofKnowledge (ε := fun _ => ε) h

/-! ### The total order: causal and prefix round-by-round knowledge soundness agree -/

/-- **The prefix state function of a causal round-by-round knowledge-sound component**
(`totalState`): false on the empty transcript, unchanged by a prover message, and true on every
accepted full transcript by `exists_flip`. -/
def KnowledgeStateFunction.ofCausal {V : Verifier (P j) Stmt} {E : Extractor (P j) Stmt Wit}
    {S : CausalStateFn P (leaf j) Stmt} {ε : Stmt → ChIdx P (leaf j) → ℝ≥0}
    (h : CausalRBRKnowledgeSoundStmt rel (fun x f => V x (f (.here j))) (CausalExtractor.ofLeaf E)
      S ε) :
    KnowledgeStateFunction V where
  toFun := totalState rel E S
  toFun_empty x tr := by
    rintro ⟨i, hi, -⟩
    exact Fin.succ_ne_zero _ (Fin.le_zero_iff.mp hi)
  toFun_next m hm x tr msg hn := by
    rintro ⟨i, hi, hflip⟩
    have hi' := ProtocolSpec.succ_le_castSucc_of_message hm hi
    rw [ProtocolSpec.take_concat tr msg _ hi'] at hflip
    exact hn ⟨i, hi', hflip⟩
  toFun_full x tr hV := by
    by_contra hno
    obtain ⟨c, hc⟩ := h.exists_flip x (FullTr.ofHere tr) hV id fun c hc => by
      obtain ⟨p, i⟩ := c
      cases p
      exact hno ⟨i, Fin.le_last _, Or.inl hc⟩
    obtain ⟨p, i⟩ := c
    cases p
    have e : (P j).concat (tr.take i.1.castSucc (Fin.le_last _)) (tr i.1) =
        tr.take i.1.succ (Fin.le_last _) :=
      (P j).concat_take_succ (tr.take i.1.succ (Fin.le_last _))
    obtain ⟨hn, hs⟩ := flipAt_here_iff.mp hc
    exact hno ⟨i, Fin.le_last _,
      Or.inr ⟨hn, (congrArg (fun t => S (.here j) i.1.succ x (CausalCtx.here j) t) e).mp hs⟩⟩

open Classical in
/-- **A causal round-by-round knowledge-sound component is round-by-round knowledge sound** in
the sense of CMS19 Definition 8.5 (p. 40) with per-round errors (Chiesa–Yogev 2024 Definition
31.1.6, p. 386), at errors that may depend on the statement: the same extractor and errors, at the
prefix state `KnowledgeStateFunction.ofCausal`. The converse of `CausalRBRStmt.ofKnowledge`. -/
theorem CausalRBRKnowledgeSoundStmt.toKnowledge {V : Verifier (P j) Stmt}
    {E : Extractor (P j) Stmt Wit} {S : CausalStateFn P (leaf j) Stmt}
    {ε : Stmt → (P j).ChallengeIdx → ℝ≥0}
    (h : CausalRBRKnowledgeSoundStmt rel (fun x f => V x (f (.here j))) (CausalExtractor.ofLeaf E)
      S (fun x => errLeaf (ε x))) :
    rbrKnowledgeSoundnessStmt rel V E (KnowledgeStateFunction.ofCausal h) ε := by
  intro x i tr
  refine (probUniform_mono fun ch hch => ?_).trans (h.rbr ⟨.here j, i⟩ x ⟨CausalCtx.here j, tr⟩)
  obtain ⟨hE, hn, i', hi', hflip⟩ := hch
  by_cases hlt : i'.1.succ ≤ i.1.castSucc
  · rw [ProtocolSpec.take_concat tr ch _ hlt] at hflip
    exact (hn ⟨i', hlt, hflip⟩).elim
  · obtain ⟨iv, hdir⟩ := i
    obtain ⟨iv', hdir'⟩ := i'
    obtain rfl : iv' = iv := Fin.ext (by
      simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at hi' hlt
      omega)
    have e := ProtocolSpec.take_concat tr ch iv'.castSucc le_rfl
    rcases hflip with hE' | ⟨hn', hs⟩
    · exact (hE ((congrArg (fun t => (x, E iv'.castSucc x t) ∈ rel) e).mp hE')).elim
    · refine ⟨hE, fun h' => hn' ?_, hs⟩
      exact (congrArg (fun t => S (.here j) iv'.castSucc x (CausalCtx.here j) t) e).mpr h'

/-- **`lem:rbr-total`: under a total order the two round-by-round knowledge notions agree.** A
component protocol, whose messages are totally ordered, has round-by-round knowledge errors `ε` in
the sense of CMS19 Definition 8.5 (p. 40), with per-round errors as in Chiesa–Yogev 2024
Definition 31.1.6 (p. 386) that may depend on the statement (`rbrKnowledgeSoundnessStmt`), at the
extractor `E` if and only if, as a one-component composite, it has causal round-by-round knowledge
errors `ε` (`CausalRBRKnowledgeSoundStmt`) at the same extractor. -/
@[headline]
theorem rbrKnowledgeSoundness_total_iff (j : ι) {V : Verifier (P j) Stmt}
    {E : Extractor (P j) Stmt Wit} {ε : Stmt → (P j).ChallengeIdx → ℝ≥0} :
    (∃ S : KnowledgeStateFunction V, rbrKnowledgeSoundnessStmt rel V E S ε) ↔
      ∃ S : CausalStateFn P (leaf j) Stmt, CausalRBRKnowledgeSoundStmt rel
        (fun x f => V x (f (.here j))) (CausalExtractor.ofLeaf E) S (fun x => errLeaf (ε x)) :=
  ⟨fun ⟨_, h⟩ => ⟨_, CausalRBRStmt.ofKnowledge h⟩, fun ⟨_, h⟩ => ⟨_, h.toKnowledge⟩⟩

/-- **The language state of a component**: the component's state at the component statement
`σ y`, while `σ y` has no witness for `relC`. Not required to be efficient. -/
def languageState {StmtC WitC Y : Type} (relC : Set (StmtC × WitC)) {V : Verifier (P j) StmtC}
    (S : KnowledgeStateFunction V) (σ : Y → StmtC) : CausalStateFn P (leaf j) Y :=
  CausalStateFn.ofLeaf fun k y tr => S.toFun k (σ y) tr ∧ ¬ ∃ w, (σ y, w) ∈ relC

/-- **A knowledge-sound component as a reduction of its language**: on statements `y` read
through `σ`, the component reduces "`σ y` has a witness for `relC`" to acceptance, at its
language state (`languageState`) with its own errors, for every relation and extractor of the
composite. While `σ y` has no witness the component's extractor fails, so its flips are bounded by
its round-by-round knowledge soundness. -/
theorem CausalRBR.ofLanguage {Y W StmtC WitC : Type} {relC : Set (StmtC × WitC)}
    {V : Verifier (P j) StmtC} {Ec : Extractor (P j) StmtC WitC} {S : KnowledgeStateFunction V}
    {ε : (P j).ChallengeIdx → ℝ≥0} (h : rbrKnowledgeSoundness relC V Ec S ε) (σ : Y → StmtC)
    (rel : Set (Y × W)) (E : CausalExtractor P (leaf j) Y W) :
    CausalRBR rel E (languageState relC S σ) (errLeaf ε) (fun y => ∃ w, (σ y, w) ∈ relC)
      fun y f => V (σ y) (f (.here j)) = true where
  exists_flip y f hV hno _ := by
    obtain ⟨i, hi⟩ := ProtocolSpec.Transcript.exists_flip
      (fun k tr => S.toFun k (σ y) tr ∧ ¬ ∃ w, (σ y, w) ∈ relC)
      (fun k hk tr msg hn hs => S.toFun_next k hk (σ y) tr msg (fun h' => hn ⟨h', hs.2⟩) hs.1)
      (f (.here j)) (fun h0 => S.toFun_empty _ _ h0.1) ⟨S.toFun_full _ _ hV, hno⟩
    exact ⟨⟨.here j, i⟩, hi⟩
  rbr c y past := by
    obtain ⟨p, i⟩ := c
    cases p
    refine (probUniform_mono fun ch hch => ?_).trans (h (σ y) i past.own)
    obtain ⟨-, hn, hs, hno⟩ := hch
    exact ⟨fun hw => hno ⟨_, hw⟩, fun h' => hn ⟨h', hno⟩, hs⟩

end Leaf

/-! ### Many composites -/

section NodeN

variable {Stmt Wit : Type}

/-- The extractor of `nodeN k m c` from extractors of the composites (`CausalExtractor.par`).

Running time: following the challenge's leaf path through at most `m` nodes to its composite, then
one call of that composite's extractor `E i` (their own Running time paragraphs); polynomial when
every `E i` is and `m` is polynomial. This running time is argued here, not proved in Lean. -/
def CausalExtractor.nodeN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} →
    (∀ i, CausalExtractor P (c i) Stmt Wit) → CausalExtractor P (SPTerm.nodeN k m c) Stmt Wit
  | 0, _, _ => ⟨fun ⟨p, _⟩ _ _ => nomatch p⟩
  | m + 1, _, E => (E 0).par (CausalExtractor.nodeN k m fun i => E i.succ)

/-- **An extractor reading only the statement**, on every composite of a node, is the extractor
of the node reading only the statement. -/
theorem CausalExtractor.nodeN_ofStmt (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} →
    (g : Stmt → Wit) → ∀ (d : ChIdx P (SPTerm.nodeN k m c)) x past,
      (CausalExtractor.nodeN (P := P) k m (c := c) fun _ => CausalExtractor.ofStmt g) d x past = g x
  | 0, _, _, ⟨p, _⟩, _, _ => nomatch p
  | m + 1, _, g, ⟨.left _, _⟩, _, _ => rfl
  | m + 1, c, g, ⟨.right p, i⟩, x, past =>
    CausalExtractor.nodeN_ofStmt k m (c := fun i => c i.succ) g ⟨p, i⟩ x _

/-- The state function of `nodeN k m c` from state functions of the composites. -/
def CausalStateFn.nodeN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} →
    (∀ i, CausalStateFn P (c i) Stmt) → CausalStateFn P (SPTerm.nodeN k m c) Stmt
  | 0, _, _ => fun p => nomatch p
  | m + 1, _, S => (S 0).par (CausalStateFn.nodeN k m fun i => S i.succ)

/-- The errors of `nodeN k m c`: each composite's errors at its challenges. -/
def errN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} → (∀ i, ChIdx P (c i) → ℝ≥0) →
    ChIdx P (SPTerm.nodeN k m c) → ℝ≥0
  | 0, _, _ => fun ⟨p, _⟩ => nomatch p
  | m + 1, _, ε => errNode (ε 0) (errN k m fun i => ε i.succ)

/-- A bound on every composite's errors bounds those of `nodeN k m c`. -/
theorem errN_le (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} → {ε : ∀ i, ChIdx P (c i) → ℝ≥0} →
    {δ : ℝ≥0} → (∀ i d, ε i d ≤ δ) → ∀ d, errN k m ε d ≤ δ
  | 0, _, _, _, _ => fun ⟨p, _⟩ => nomatch p
  | m + 1, _, _, _, h => errNode_le (h 0) (errN_le k m fun i => h i.succ)

/-- **Component `i`'s challenge `d` as a challenge of `nodeN k m c`.** -/
def ChIdx.inN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} → (i : Fin m) → ChIdx P (c i) →
    ChIdx P (SPTerm.nodeN k m c)
  | 0, _, i, _ => i.elim0
  | m + 1, c, i, d =>
    Fin.cases (motive := fun i => ChIdx P (c i) → ChIdx P (SPTerm.nodeN k (m + 1) c))
    (fun d => d.left) (fun i d => (ChIdx.inN k m (c := fun i => c i.succ) i d).right) i d

/-- **Every component challenge keeps its component's error**, whichever way the components are
composed (`k = .par` side by side, `k = .seq` one after the other). -/
theorem errN_inN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} → (ε : ∀ i, ChIdx P (c i) → ℝ≥0) →
    (i : Fin m) → (d : ChIdx P (c i)) → errN k m ε (ChIdx.inN k m i d) = ε i d
  | 0, _, _, i, _ => i.elim0
  | m + 1, c, ε, i, d => by
    induction i using Fin.cases with
    | zero => rfl
    | succ i => exact errN_inN k m (c := fun i => c i.succ) (fun i => ε i.succ) i d

/-- The conjunction of output claims of the composites, each on its part of the transcript. -/
def claimOutN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} → (∀ i, Stmt → FullTr P (c i) → Prop) →
    Stmt → FullTr P (SPTerm.nodeN k m c) → Prop
  | 0, _, _, _, _ => True
  | m + 1, _, Q, x, f => Q 0 x f.left ∧ claimOutN k m (fun i => Q i.succ) x f.right

/-- `verifierN` accepts when every composite's verifier accepts its part. -/
theorem verifierN_eq_true (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} →
    (V : ∀ i, Stmt → FullTr P (c i) → Bool) → (x : Stmt) → (f : FullTr P (SPTerm.nodeN k m c)) →
    verifierN k m V x f = true → claimOutN k m (fun i x f => V i x f = true) x f
  | 0, _, _, _, _, _ => trivial
  | m + 1, _, V, x, f, h => by
    rw [verifierN, Bool.and_eq_true] at h
    exact ⟨h.1, verifierN_eq_true k m (fun i => V i.succ) x f.right h.2⟩

/-- **The part of subterm `i`** of a composite transcript of `nodeN k m c`. -/
def FullTr.partN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} → FullTr P (SPTerm.nodeN k m c) →
    (i : Fin m) → FullTr P (c i)
  | 0, _, _, i => i.elim0
  | m + 1, c, f, i =>
    Fin.cases (motive := fun i => FullTr P (c i)) f.left
      (fun i => FullTr.partN k m (c := fun i => c i.succ) f.right i) i

/-- **The challenges of subterm `i`** of the challenges of `nodeN k m c`. -/
def Chs.partN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} → Chs P (SPTerm.nodeN k m c) →
    (i : Fin m) → Chs P (c i)
  | 0, _, _, i => i.elim0
  | m + 1, c, ch, i =>
    Fin.cases (motive := fun i => Chs P (c i)) ch.left
      (fun i => Chs.partN k m (c := fun i => c i.succ) ch.right i) i

/-- **The challenges of a part** are the part of the challenges. -/
theorem FullTr.challenges_partN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} →
    (f : FullTr P (SPTerm.nodeN k m c)) → (i : Fin m) →
    (f.partN k m i).challenges = f.challenges.partN k m i
  | 0, _, _, i => i.elim0
  | m + 1, c, f, i => by
    induction i using Fin.cases with
    | zero => rfl
    | succ i => exact FullTr.challenges_partN k m (c := fun i => c i.succ) f.right i

/-- **`verifierN` reads every composite's verifier on its part**: verifiers agreeing on the parts
give the same verdict. -/
theorem verifierN_congr (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} →
    {V V' : ∀ i, Stmt → FullTr P (c i) → Bool} → {x x' : Stmt} → (f : FullTr P (SPTerm.nodeN k m c)) →
    (∀ i, V i x (f.partN k m i) = V' i x' (f.partN k m i)) → verifierN k m V x f = verifierN k m V' x' f
  | 0, _, _, _, _, _, _, _ => rfl
  | m + 1, c, V, V', x, x', f, h => by
    rw [verifierN, verifierN, verifierN_congr k m (c := fun i => c i.succ) f.right fun i => h i.succ]
    exact congrArg (· && _) (h 0)

/-- **The conjunction of output claims** is every composite's claim on its part. -/
theorem claimOutN_iff (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} →
    (Q : ∀ i, Stmt → FullTr P (c i) → Prop) → (x : Stmt) → (f : FullTr P (SPTerm.nodeN k m c)) →
    (claimOutN k m Q x f ↔ ∀ i, Q i x (f.partN k m i))
  | 0, _, _, _, _ => ⟨fun _ i => i.elim0, fun _ => trivial⟩
  | m + 1, c, Q, x, f => by
    rw [claimOutN, claimOutN_iff k m (c := fun i => c i.succ) (fun i => Q i.succ) x f.right]
    constructor
    · rintro ⟨h0, hs⟩ i
      induction i using Fin.cases with
      | zero => exact h0
      | succ i => exact hs i
    · intro h
      exact ⟨h 0, fun i => h i.succ⟩

variable [∀ j (i : (P j).ChallengeIdx), Fintype ((P j).Challenge i)]
  [∀ j (i : (P j).ChallengeIdx), Nonempty ((P j).Challenge i)] {rel : Set (Stmt × Wit)}

/-- **Many composites, at errors of the statement**, side by side or one after the other on the
same statements, reduce the conjunction of their input claims to the conjunction of their output
claims (`claimOutN`), and at every statement every challenge keeps its error. -/
theorem CausalRBRStmt.nodeN (k : Comp) : (m : ℕ) → {c : Fin m → SPTerm ι} →
    {E : ∀ i, CausalExtractor P (c i) Stmt Wit} → {S : ∀ i, CausalStateFn P (c i) Stmt} →
    {ε : ∀ i, Stmt → ChIdx P (c i) → ℝ≥0} → {claim : Fin m → Stmt → Prop} →
    {claimOut : ∀ i, Stmt → FullTr P (c i) → Prop} →
    (∀ i, CausalRBRStmt rel (E i) (S i) (ε i) (claim i) (claimOut i)) →
    CausalRBRStmt rel (CausalExtractor.nodeN k m E) (CausalStateFn.nodeN k m S)
      (fun x => errN k m fun i => ε i x) (fun x => ∀ i, claim i x) (claimOutN k m claimOut)
  | 0, _, _, _, _, _, _, _ =>
    { exists_flip := fun _ _ _ hc _ => absurd (fun i => i.elim0) hc
      rbr := fun ⟨p, _⟩ => nomatch p }
  | m + 1, _, _, _, _, _, _, h =>
    ((h 0).par (k := k) (CausalRBRStmt.nodeN k m fun i => h i.succ)).mono
      (fun _ hc => Fin.cases hc.1 hc.2) fun _ _ ho => ho

/-- **Many composites**, side by side or one after the other on the same statements, reduce the
conjunction of their input claims to the conjunction of their output claims (`claimOutN`), and
every challenge keeps its error. `CausalRBRStmt.nodeN` at errors that do not depend on the
statement. -/
theorem CausalRBR.nodeN (k : Comp) (m : ℕ) {c : Fin m → SPTerm ι}
    {E : ∀ i, CausalExtractor P (c i) Stmt Wit} {S : ∀ i, CausalStateFn P (c i) Stmt}
    {ε : ∀ i, ChIdx P (c i) → ℝ≥0} {claim : Fin m → Stmt → Prop}
    {claimOut : ∀ i, Stmt → FullTr P (c i) → Prop}
    (h : ∀ i, CausalRBR rel (E i) (S i) (ε i) (claim i) (claimOut i)) :
    CausalRBR rel (CausalExtractor.nodeN k m E) (CausalStateFn.nodeN k m S) (errN k m ε)
      (fun x => ∀ i, claim i x) (claimOutN k m claimOut) :=
  CausalRBRStmt.nodeN k m h

end NodeN

/-! ### A claim-producing prefix followed by components in parallel -/

end GordieHowe.IOP
