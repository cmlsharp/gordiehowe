-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.CausalSound
public import GordieHowe.Model.IOP.CausalComplete
public import GordieHowe.Foundations.ToMathlib.PMFUniform
public import GordieHowe.Headline
public import GordieHowe.Model.IOP.UniformTranscript

@[expose] public section

/-!
# Reductions on committed data and their series and parallel composition

Paper `def:red`, `def:red-sec`, `def:claims` (4), `def:red-comp` and `lem:red-sp` (a)-(c), after
CDHZ25 section 3.4 (Definitions 3.2-3.4, printed p. 25) and ChiFenWei26 Theorem 4.5 (printed p. 32).

A reduction on committed data `D` (`GordieHowe.IOP.Reduction`) runs over a series–parallel term `t` of
components `P` (`GordieHowe/Model/IOP/Causal.lean`; a term whose leaves are single rounds is a
series–parallel order on the rounds, and a leaf that is a chain of rounds is a `seq` of such
leaves). Its prover is a causal prover on the statement and the committed data, so every round's
message is a function of the statement, the committed data and the rounds of its past
(`CausalProver`). Its output map sends the statement and the full transcript to an output
statement without reading the committed data.

* `GordieHowe.IOP.Reduction.RBR`: round-by-round soundness errors (`def:red-sec` (a)) of a state function
  on the statement, the committed data and a causal past, with per-challenge errors;
* `GordieHowe.IOP.Reduction.Complete`: completeness on a set of committed data with an error
  (`def:red-sec` (b));
* `GordieHowe.IOP.Reduction.seq`, `GordieHowe.IOP.Reduction.par`: series and parallel composition
  (`def:red-comp`), the second part of a series reading its statement off the first part's
  output; `relConj` is the conjunction of relations on committed data (`def:claims` (4));
* `RBR.seq`, `RBR.par`: every round keeps its error (`lem:red-sp` (a));
  `Complete.seq`, `Complete.par`: completeness errors add on the intersection of the honest sets
  (`lem:red-sp` (b)).
* `RBR.toCausalRBR`: a reduction's round-by-round soundness is causal round-by-round soundness
  (`CausalRBR`) at the empty relation, reducing the input relation to the output relation.
* `GordieHowe.IOP.Reduction.HVZK` (`def:red-sec` (c)): honest-verifier zero knowledge with error `0`
  with respect to the uniform simulator, for committed data `join w m` built from a witness `w`
  and masks `m` that the honest prover draws from `μ`. `HVZK.seq`, `HVZK.par` (`lem:red-sp` (c)):
  with committed data `join w m₁ m₂` from the masks `m₁` and `m₂` of the two parts, each part zero
  knowledge for every value of the other's masks, and the honest transcript of the first part (in a
  parallel composition, the part designated first) independent of the second part's masks
  (`IgnoresMasks`), the composition is zero knowledge with the masks drawn from `maskProd μ₁ μ₂`.
  Without `IgnoresMasks` this fails: over `F₂²`, two parts each sending `d₀ + d₁`, one masking
  `d₀` and the other `d₁`, are each zero knowledge, while the composite view `(s, s)` is not
  uniform.
-/

namespace GordieHowe.IOP

open scoped NNReal
open SPTerm

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}

/-- **The conjunction of relations on committed data** (paper `def:claims` (4)): a pair of
statements and committed data in both relations. -/
def relConj {X₁ X₂ D : Type} (R₁ : Set (X₁ × D)) (R₂ : Set (X₂ × D)) : Set ((X₁ × X₂) × D) :=
  {p | (p.1.1, p.2) ∈ R₁ ∧ (p.1.2, p.2) ∈ R₂}

@[simp] theorem mem_relConj {X₁ X₂ D : Type} {R₁ : Set (X₁ × D)} {R₂ : Set (X₂ × D)} {x₁ : X₁}
    {x₂ : X₂} {d : D} : ((x₁, x₂), d) ∈ relConj R₁ R₂ ↔ (x₁, d) ∈ R₁ ∧ (x₂, d) ∈ R₂ :=
  Iff.rfl

variable (P) in
/-- **A reduction on committed data** (paper `def:red`) over the series–parallel term `t`, from
statements `X₁` to statements `X₂`, on committed data `D`: a deterministic causal prover on the
statement and the committed data, and an output map that does not read the committed data. -/
structure Reduction (t : SPTerm ι) (D X₁ X₂ : Type) where
  /-- The honest prover: each leaf's messages from the statement, the committed data and the
  leaf's causal past. -/
  prover : CausalProver P t (X₁ × D)
  /-- The output statement from the statement and the full transcript. -/
  out : X₁ → FullTr P t → X₂

namespace Reduction

variable {t a b : SPTerm ι} {D X₁ X₂ : Type}

section Security

variable [∀ j (i : (P j).ChallengeIdx), Fintype ((P j).Challenge i)]
  [∀ j (i : (P j).ChallengeIdx), Nonempty ((P j).Challenge i)]

/-- **Round-by-round soundness errors** `ε` of the reduction `A` from `R₁` to `R₂` at the state
function `S` (paper `def:red-sec` (a); CDHZ25 Definition 3.4 at proximity bound `0`, with the
state read on causal pasts): on every full transcript whose output lies in `R₂` while the input
does not lie in `R₁`, some challenge moves its leaf's state from false to true; and at every
causal past of a challenge on which the state is false, a uniform challenge makes it true with
probability at most the challenge's error. The state function need not be efficient. -/
structure RBR (A : Reduction P t D X₁ X₂) (R₁ : Set (X₁ × D)) (R₂ : Set (X₂ × D))
    (S : CausalStateFn P t (X₁ × D)) (ε : ChIdx P t → ℝ≥0) : Prop where
  /-- A false input claim with a true output claim has a challenge that flips the state. -/
  exists_flip : ∀ x d (f : FullTr P t), (x, d) ∉ R₁ → (A.out x f, d) ∈ R₂ →
    ∃ c, FlipAt S c (x, d) (f.past c) (f.challenges c)
  /-- From a false state, a uniform challenge makes it true with probability at most `ε c`. -/
  rbr : ∀ (c : ChIdx P t) x d (past : CausalPast P c),
    ¬ S c.leaf c.idx.1.castSucc (x, d) past.ctx past.own →
      Pr[ch ← c.Challenge :
        S c.leaf c.idx.1.succ (x, d) past.ctx ((P c.leaf.label).concat past.own ch)] ≤ ε c

/-- **Completeness on `Hon` with error `δ`** of the reduction `A` from `R₁` to `R₂` (paper
`def:red-sec` (b)): on every statement and committed data in `Hon` with the pair in `R₁`, the
output of the honest prover's transcript, at uniform challenges, lies outside `R₂` with probability
at most `δ`. -/
def Complete (A : Reduction P t D X₁ X₂) (R₁ : Set (X₁ × D)) (R₂ : Set (X₂ × D))
    (Hon : Set D) (δ : ℝ≥0) : Prop :=
  ∀ x d, d ∈ Hon → (x, d) ∈ R₁ →
    Pr[ch ← Chs P t : (A.out x (A.prover.run (x, d) ch), d) ∉ R₂] ≤ δ

/-- The probability of a flip is at most the error, at every causal past. -/
theorem RBR.flip_le {A : Reduction P t D X₁ X₂} {R₁ : Set (X₁ × D)}
    {R₂ : Set (X₂ × D)} {S : CausalStateFn P t (X₁ × D)} {ε : ChIdx P t → ℝ≥0}
    (h : A.RBR R₁ R₂ S ε) (c : ChIdx P t) (x : X₁) (d : D) (past : CausalPast P c) :
    Pr[ch ← c.Challenge : FlipAt S c (x, d) past ch] ≤ ε c := by
  by_cases hs : S c.leaf c.idx.1.castSucc (x, d) past.ctx past.own
  · exact (probUniform_mono (q := fun _ => False) fun _ hch => hch.1 hs).trans (by
      simp [probUniform])
  · exact (probUniform_mono fun _ hch => hch.2).trans (h.rbr c x d past hs)

/-- **A reduction's round-by-round soundness is causal round-by-round soundness** at the empty
relation (no extractor succeeds), reducing the input relation to the output relation, on statements
that carry the committed data. -/
theorem RBR.toCausalRBR {A : Reduction P t D X₁ X₂} {R₁ : Set (X₁ × D)}
    {R₂ : Set (X₂ × D)} {S : CausalStateFn P t (X₁ × D)} {ε : ChIdx P t → ℝ≥0}
    (h : A.RBR R₁ R₂ S ε) {Wit : Type} (E : CausalExtractor P t (X₁ × D) Wit) :
    CausalRBR (∅ : Set ((X₁ × D) × Wit)) E S ε (fun s => s ∈ R₁)
      fun s f => (A.out s.1 f, s.2) ∈ R₂ where
  exists_flip s f hout hin _ := h.exists_flip s.1 s.2 f hin hout
  rbr c s past := (probUniform_mono fun _ hch => hch.2).trans (h.flip_le c s.1 s.2 past)

end Security

/-! ### Series composition -/

section Seq

variable {Xin Xout : Type}

/-- **The series composition** `A₂ ∘ A₁` (paper `def:red-comp` (1), `lem:red-sp` (1)): `A₁`'s
rounds, then `A₂`'s on the statement `A₁` outputs for it (the first component of `A₁`'s output),
with the output statement `A₂`'s output and the second component of `A₁`'s. -/
def seq (A₁ : Reduction P a D X₁ (Xin × Xout))
    (A₂ : Reduction P b D Xin X₂) :
    Reduction P (SPTerm.seq a b) D X₁ (X₂ × Xout) where
  prover := A₁.prover.seq (A₂.prover.comapStmt fun z => ((A₁.out z.1.1 z.2).1, z.1.2))
  out x f := (A₂.out (A₁.out x f.left).1 f.right, (A₁.out x f.left).2)

/-- **The state function of a series composition**: `A₁`'s at its leaves, `A₂`'s at its own on the
statement `A₁` outputs and the committed data. -/
def seqState (A₁ : Reduction P a D X₁ (Xin × Xout)) (S₁ : CausalStateFn P a (X₁ × D))
    (S₂ : CausalStateFn P b (Xin × D)) : CausalStateFn P (SPTerm.seq a b) (X₁ × D) :=
  S₁.seq fun p k z ctx tr => S₂ p k ((A₁.out z.1.1 z.2).1, z.1.2) ctx tr

/-- The run of a series composition: `A₁`'s run, then `A₂`'s on the statement `A₁` outputs. -/
theorem run_seq (A₁ : Reduction P a D X₁ (Xin × Xout))
    (A₂ : Reduction P b D Xin X₂) (x : X₁) (d : D) (ch : Chs P (SPTerm.seq a b)) :
    (A₁.seq A₂).prover.run (x, d) ch =
      FullTr.join (A₁.prover.run (x, d) ch.left)
        (A₂.prover.run ((A₁.out x (A₁.prover.run (x, d) ch.left)).1, d) ch.right) := by
  rw [seq, CausalProver.run_seq, CausalProver.run_comapStmt]

variable [∀ j (i : (P j).ChallengeIdx), Fintype ((P j).Challenge i)]
  [∀ j (i : (P j).ChallengeIdx), Nonempty ((P j).Challenge i)]

/-- **Paper `lem:red-sp` (1)(a), series**: if `A₁` reduces `R₁` to `Rin ∧ Rout` and `A₂` reduces
`Rin` to `R₂`, with round-by-round soundness errors `ε₁` and `ε₂`, then `A₂ ∘ A₁` reduces `R₁` to
`R₂ ∧ Rout` with every round keeping its error (`errNode`). -/
@[headline]
theorem RBR.seq {A₁ : Reduction P a D X₁ (Xin × Xout)}
    {A₂ : Reduction P b D Xin X₂} {R₁ : Set (X₁ × D)} {Rin : Set (Xin × D)}
    {Rout : Set (Xout × D)} {R₂ : Set (X₂ × D)} {S₁ : CausalStateFn P a (X₁ × D)}
    {S₂ : CausalStateFn P b (Xin × D)} {ε₁ : ChIdx P a → ℝ≥0} {ε₂ : ChIdx P b → ℝ≥0}
    (h₁ : A₁.RBR R₁ (relConj Rin Rout) S₁ ε₁) (h₂ : A₂.RBR Rin R₂ S₂ ε₂) :
    (A₁.seq A₂).RBR R₁ (relConj R₂ Rout) (A₁.seqState S₁ S₂) (errNode ε₁ ε₂) where
  exists_flip x d f hin hout := by
    obtain ⟨hout₂, houtOut⟩ := hout
    by_cases hmid : ((A₁.out x f.left).1, d) ∈ Rin
    · obtain ⟨c, hc⟩ := h₁.exists_flip x d f.left hin ⟨hmid, houtOut⟩
      exact ⟨c.left, hc⟩
    · obtain ⟨c, hc⟩ := h₂.exists_flip _ d f.right hmid hout₂
      exact ⟨c.right, hc⟩
  rbr c x d past := by
    rcases ChIdx.left_or_right c with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact h₁.rbr c x d ⟨past.ctx.ofLeft, past.own⟩
    · exact h₂.rbr c _ d ⟨past.ctx.ofRight, past.own⟩

/-- **Paper `lem:red-sp` (1)(b), series**: if `A₁` is complete from `R₁` to `Rin ∧ Rout` on `Hon₁`
with error `δ₁` and `A₂` from `Rin` to `R₂` on `Hon₂` with error `δ₂`, then `A₂ ∘ A₁` is complete
from `R₁` to `R₂ ∧ Rout` on `Hon₁ ∩ Hon₂` with error `δ₁ + δ₂`. -/
@[headline]
theorem Complete.seq {A₁ : Reduction P a D X₁ (Xin × Xout)}
    {A₂ : Reduction P b D Xin X₂} {R₁ : Set (X₁ × D)} {Rin : Set (Xin × D)}
    {Rout : Set (Xout × D)} {R₂ : Set (X₂ × D)} {Hon₁ Hon₂ : Set D} {δ₁ δ₂ : ℝ≥0}
    (h₁ : A₁.Complete R₁ (relConj Rin Rout) Hon₁ δ₁) (h₂ : A₂.Complete Rin R₂ Hon₂ δ₂) :
    (A₁.seq A₂).Complete R₁ (relConj R₂ Rout) (Hon₁ ∩ Hon₂) (δ₁ + δ₂) := by
  intro x d hd hx
  rw [probUniform_equiv Chs.equivNode]
  have key := probUniform_prod_le_add (A := Chs P a) (C := Chs P b) (c := (δ₂ : ENNReal))
    (fun c => ((A₂.out (A₁.out x (A₁.prover.run (x, d) c.1)).1
        (A₂.prover.run ((A₁.out x (A₁.prover.run (x, d) c.1)).1, d) c.2), d) ∈ R₂ ∧
      ((A₁.out x (A₁.prover.run (x, d) c.1)).2, d) ∈ Rout) → False)
    (fun c₁ => (A₁.out x (A₁.prover.run (x, d) c₁), d) ∉ relConj Rin Rout) fun c₁ hc₁ => by
      have hmid := not_not.mp hc₁
      refine (probUniform_mono fun c₂ hc₂ => ?_).trans (h₂ _ d hd.2 hmid.1)
      exact fun h => hc₂ ⟨h, hmid.2⟩
  refine (probUniform_mono fun c hc => ?_).trans (key.trans ?_)
  · change (((A₁.seq A₂).out x ((A₁.seq A₂).prover.run (x, d) (Chs.equivNode.symm c))).1, d) ∈
        R₂ ∧ _ → False at hc
    simp only [run_seq] at hc ⊢
    exact hc
  · rw [add_comm, ENNReal.coe_add]
    exact add_le_add_left (h₁ x d hd.1 hx) _

end Seq

/-! ### Parallel composition -/

section Par

variable {Y₁ Y₂ : Type}

/-- **The parallel composition** `A₁ ∥ A₂` (paper `def:red-comp` (2), `lem:red-sp` (2)): on the
statement `(x₁, x₂)`, `A₁` on `x₁` and `A₂` on `x₂` side by side, with the pair of their outputs
as the output statement. -/
def par (A₁ : Reduction P a D X₁ Y₁) (A₂ : Reduction P b D X₂ Y₂) :
    Reduction P (SPTerm.par a b) D (X₁ × X₂) (Y₁ × Y₂) where
  prover := (A₁.prover.comapStmt fun s => (s.1.1, s.2)).par
    (A₂.prover.comapStmt fun s => (s.1.2, s.2))
  out x f := (A₁.out x.1 f.left, A₂.out x.2 f.right)

/-- **The state function of a parallel composition**: `A₁`'s at its leaves on `x₁`, `A₂`'s at its
own on `x₂`. -/
def parState (S₁ : CausalStateFn P a (X₁ × D)) (S₂ : CausalStateFn P b (X₂ × D)) :
    CausalStateFn P (SPTerm.par a b) ((X₁ × X₂) × D) :=
  CausalStateFn.par (k := .par) (fun p k s ctx tr => S₁ p k (s.1.1, s.2) ctx tr)
    fun p k s ctx tr => S₂ p k (s.1.2, s.2) ctx tr

/-- The run of a parallel composition: both parts' runs. -/
theorem run_par (A₁ : Reduction P a D X₁ Y₁) (A₂ : Reduction P b D X₂ Y₂)
    (x₁ : X₁) (x₂ : X₂) (d : D) (ch : Chs P (SPTerm.par a b)) :
    (A₁.par A₂).prover.run ((x₁, x₂), d) ch =
      FullTr.join (A₁.prover.run (x₁, d) ch.left) (A₂.prover.run (x₂, d) ch.right) := by
  rw [par, CausalProver.run_par, CausalProver.run_comapStmt, CausalProver.run_comapStmt]

variable [∀ j (i : (P j).ChallengeIdx), Fintype ((P j).Challenge i)]
  [∀ j (i : (P j).ChallengeIdx), Nonempty ((P j).Challenge i)]

/-- **Paper `lem:red-sp` (2)(a), parallel**: if `A₁` reduces `R₁` to `R₂` and `A₂` reduces `R₁'` to
`R₂'`, with round-by-round soundness errors `ε₁` and `ε₂`, then `A₁ ∥ A₂` reduces `R₁ ∧ R₁'` to
`R₂ ∧ R₂'` with every round keeping its error (`errNode`). -/
@[headline]
theorem RBR.par {A₁ : Reduction P a D X₁ Y₁} {A₂ : Reduction P b D X₂ Y₂}
    {R₁ : Set (X₁ × D)} {R₂ : Set (Y₁ × D)} {R₁' : Set (X₂ × D)} {R₂' : Set (Y₂ × D)}
    {S₁ : CausalStateFn P a (X₁ × D)} {S₂ : CausalStateFn P b (X₂ × D)} {ε₁ : ChIdx P a → ℝ≥0}
    {ε₂ : ChIdx P b → ℝ≥0} (h₁ : A₁.RBR R₁ R₂ S₁ ε₁) (h₂ : A₂.RBR R₁' R₂' S₂ ε₂) :
    (A₁.par A₂).RBR (relConj R₁ R₁') (relConj R₂ R₂') (parState S₁ S₂) (errNode ε₁ ε₂) where
  exists_flip x d f hin hout := by
    by_cases h₁in : (x.1, d) ∈ R₁
    · obtain ⟨c, hc⟩ := h₂.exists_flip x.2 d f.right (fun h => hin ⟨h₁in, h⟩) hout.2
      exact ⟨c.right, hc⟩
    · obtain ⟨c, hc⟩ := h₁.exists_flip x.1 d f.left h₁in hout.1
      exact ⟨c.left, hc⟩
  rbr c x d past := by
    rcases ChIdx.left_or_right c with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact h₁.rbr c x.1 d ⟨past.ctx.ofLeft, past.own⟩
    · exact h₂.rbr c x.2 d ⟨past.ctx.ofRight, past.own⟩

/-- **Paper `lem:red-sp` (2)(b), parallel**: if `A₁` is complete from `R₁` to `R₂` on `Hon₁` with
error `δ₁` and `A₂` from `R₁'` to `R₂'` on `Hon₂` with error `δ₂`, then `A₁ ∥ A₂` is complete from
`R₁ ∧ R₁'` to `R₂ ∧ R₂'` on `Hon₁ ∩ Hon₂` with error `δ₁ + δ₂`. -/
@[headline]
theorem Complete.par {A₁ : Reduction P a D X₁ Y₁} {A₂ : Reduction P b D X₂ Y₂}
    {R₁ : Set (X₁ × D)} {R₂ : Set (Y₁ × D)} {R₁' : Set (X₂ × D)} {R₂' : Set (Y₂ × D)}
    {Hon₁ Hon₂ : Set D} {δ₁ δ₂ : ℝ≥0} (h₁ : A₁.Complete R₁ R₂ Hon₁ δ₁)
    (h₂ : A₂.Complete R₁' R₂' Hon₂ δ₂) :
    (A₁.par A₂).Complete (relConj R₁ R₁') (relConj R₂ R₂') (Hon₁ ∩ Hon₂) (δ₁ + δ₂) := by
  rintro ⟨x₁, x₂⟩ d hd hx
  rw [probUniform_equiv Chs.equivNode]
  have key := probUniform_prod_le_add (A := Chs P a) (C := Chs P b) (c := (δ₂ : ENNReal))
    (fun c => (A₁.out x₁ (A₁.prover.run (x₁, d) c.1), d) ∉ R₂ ∨
      (A₂.out x₂ (A₂.prover.run (x₂, d) c.2), d) ∉ R₂')
    (fun c₁ => (A₁.out x₁ (A₁.prover.run (x₁, d) c₁), d) ∉ R₂) fun c₁ hc₁ =>
      (probUniform_mono fun _ hc => hc.resolve_left hc₁).trans (h₂ x₂ d hd.2 hx.2)
  refine (probUniform_mono fun c hc => ?_).trans (key.trans ?_)
  · change ¬ ((((A₁.par A₂).out (x₁, x₂)
        ((A₁.par A₂).prover.run ((x₁, x₂), d) (Chs.equivNode.symm c))).1, d) ∈ R₂ ∧
      (((A₁.par A₂).out (x₁, x₂)
        ((A₁.par A₂).prover.run ((x₁, x₂), d) (Chs.equivNode.symm c))).2, d) ∈ R₂') at hc
    simp only [run_par] at hc
    exact not_and_or.mp hc
  · rw [add_comm, ENNReal.coe_add]
    exact add_le_add_left (h₁ x₁ d hd.1 hx.1) _

end Par

/-! ### Zero knowledge -/

section ZK

/-- **The law of two masks drawn independently**: `m₁` from `μ₁` and `m₂` from `μ₂`. -/
noncomputable def maskProd {M₁ M₂ : Type} (μ₁ : PMF M₁) (μ₂ : PMF M₂) : PMF (M₁ × M₂) :=
  μ₁.bind fun m₁ => μ₂.map (Prod.mk m₁)

/-- **Two independent uniform draws joined through an equivalence** are uniform. With `F₁` the
first part's transcript from its mask `m₁`, the other mask `m₂` (which it does not read, `hign`) and
its challenges, and `F₂` the second part's from the first part's transcript, both masks and its
challenges: if the first part's transcript is uniform at every `m₂` (`h₁`) and the second part's is
uniform at every first-part transcript and every `m₁` (`h₂`), the joined transcript is uniform. The
probability step of `lem:red-sp` (c). -/
theorem law_join_uniform {M₁ M₂ C₁ C₂ T₁ T₂ T : Type} [Fintype C₁] [Nonempty C₁] [Fintype C₂]
    [Nonempty C₂] [Fintype T₁] [Nonempty T₁] [Fintype T₂] [Nonempty T₂] [Fintype T] [Nonempty T]
    (μ₁ : PMF M₁) (μ₂ : PMF M₂) (F₁ : M₁ → M₂ → C₁ → T₁) (F₂ : T₁ → M₁ → M₂ → C₂ → T₂)
    (e : T₁ × T₂ ≃ T) (hign : ∀ m₁ m₂ m₂' c, F₁ m₁ m₂ c = F₁ m₁ m₂' c)
    (h₁ : ∀ m₂, (μ₁.bind fun m₁ => (PMF.uniformOfFintype C₁).map (F₁ m₁ m₂)) =
      PMF.uniformOfFintype T₁)
    (h₂ : ∀ f m₁, (μ₂.bind fun m₂ => (PMF.uniformOfFintype C₂).map (F₂ f m₁ m₂)) =
      PMF.uniformOfFintype T₂) :
    ((maskProd μ₁ μ₂).bind fun m => (PMF.uniformOfFintype (C₁ × C₂)).map fun c =>
      e (F₁ m.1 m.2 c.1, F₂ (F₁ m.1 m.2 c.1) m.1 m.2 c.2)) = PMF.uniformOfFintype T := by
  obtain ⟨m₂₀, -⟩ := μ₂.support_nonempty
  obtain ⟨G, hGdef⟩ : ∃ G : M₁ → C₁ → T₁, G = fun m₁ c => F₁ m₁ m₂₀ c := ⟨_, rfl⟩
  have h₁' : (μ₁.bind fun m₁ => (PMF.uniformOfFintype C₁).map (G m₁)) =
      PMF.uniformOfFintype T₁ := by
    subst hGdef
    exact h₁ m₂₀
  have hG' : ∀ m₁ m₂ c, F₁ m₁ m₂ c = G m₁ c := fun m₁ m₂ c => by
    rw [hGdef]
    exact hign m₁ m₂ m₂₀ c
  simp only [hG']
  rw [maskProd, PMF.bind_bind]
  simp only [PMF.bind_map, PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind, PMF.map_comp,
    Function.comp_def]
  have hin : ∀ m₁ c₁, (μ₂.bind fun m₂ => (PMF.uniformOfFintype C₂).map
      fun c₂ => e (G m₁ c₁, F₂ (G m₁ c₁) m₁ m₂ c₂)) =
      (PMF.uniformOfFintype T₂).map fun f₂ => e (G m₁ c₁, f₂) := fun m₁ c₁ => by
    rw [← h₂ (G m₁ c₁) m₁, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]
  calc (μ₁.bind fun m₁ => μ₂.bind fun m₂ => (PMF.uniformOfFintype C₁).bind fun c₁ =>
          (PMF.uniformOfFintype C₂).map fun c₂ => e (G m₁ c₁, F₂ (G m₁ c₁) m₁ m₂ c₂))
      = μ₁.bind fun m₁ => (PMF.uniformOfFintype C₁).bind fun c₁ => μ₂.bind fun m₂ =>
          (PMF.uniformOfFintype C₂).map fun c₂ => e (G m₁ c₁, F₂ (G m₁ c₁) m₁ m₂ c₂) := by
        congr 1
        funext m₁
        exact PMF.bind_comm _ _ _
    _ = μ₁.bind fun m₁ => (PMF.uniformOfFintype C₁).bind fun c₁ =>
          (PMF.uniformOfFintype T₂).map fun f₂ => e (G m₁ c₁, f₂) := by
        simp only [hin]
    _ = (μ₁.bind fun m₁ => (PMF.uniformOfFintype C₁).map (G m₁)).bind fun f₁ =>
          (PMF.uniformOfFintype T₂).map fun f₂ => e (f₁, f₂) := by
        simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
    _ = PMF.uniformOfFintype T := by
        rw [h₁', ← PMF.map_uniformOfFintype_equiv e, PMF.uniformOfFintype_prod_eq_bind,
          PMF.map_bind]
        simp only [PMF.map_comp, Function.comp_def]

variable [∀ j (i : Fin (n j)), Fintype ((P j).Type i)] [∀ j (i : Fin (n j)), Nonempty ((P j).Type i)]

/-- The full composite transcripts of finite components are finite. -/
instance FullTr.instFintype (t : SPTerm ι) : Fintype (FullTr P t) :=
  inferInstanceAs (Fintype ((p : t.Leaf) → (P p.label).Transcript (Fin.last (n p.label))))

/-- The full composite transcripts of nonempty components are nonempty. -/
instance FullTr.instNonempty (t : SPTerm ι) : Nonempty (FullTr P t) :=
  inferInstanceAs (Nonempty ((p : t.Leaf) → (P p.label).Transcript (Fin.last (n p.label))))

/-- **The full transcripts of a node are pairs of its subterms' full transcripts.** -/
def FullTr.equivNode {k : Comp} {a b : SPTerm ι} : FullTr P a × FullTr P b ≃ FullTr P (node k a b) where
  toFun f := FullTr.join f.1 f.2
  invFun f := (f.left, f.right)
  left_inv _ := rfl
  right_inv f := by
    funext p
    cases p <;> rfl

variable {W M M₁ M₂ : Type}

/-- **The view of a reduction** at the statement `x` and committed data `d m` with the masks
`m` drawn from `μ` (paper `def:red-sec` (c)): the law of the honest prover's full
transcript, the uniform challenges and the prover's messages. -/
noncomputable def viewLaw (A : Reduction P t D X₁ X₂) (x : X₁) (d : M → D) (μ : PMF M) :
    PMF (FullTr P t) :=
  μ.bind fun m => (PMF.uniformOfFintype (Chs P t)).map fun ch => A.prover.run (x, d m) ch

/-- **Honest-verifier zero knowledge with error `0` with respect to the uniform simulator** (paper
`def:red-sec` (c); ChiFenWei26 Definitions 4.1-4.2 for a distinguisher that makes no queries): for
committed data `join w m` built from a witness `w` and masks `m` drawn from `μ`, at every statement
and every witness the view is the law of the uniform simulator,
which draws every challenge and every message uniformly and independently (the uniform law on full
transcripts). -/
def HVZK (A : Reduction P t D X₁ X₂) (join : W → M → D) (μ : PMF M) : Prop :=
  ∀ x w, A.viewLaw x (join w) μ = PMF.uniformOfFintype (FullTr P t)

/-- **The honest transcript does not read the masks `m₂`**: for committed data
`join w m₁ m₂`, the honest prover's full transcript is a function of the statement, the witness
`w`, the reduction's own masks `m₁` and the challenges. -/
def IgnoresMasks (A : Reduction P t D X₁ X₂) (join : W → M₁ → M₂ → D) : Prop :=
  ∀ x w m₁ m₂ m₂' ch, A.prover.run (x, join w m₁ m₂) ch = A.prover.run (x, join w m₁ m₂') ch

/-- The uniform law on a node's challenges is the joint uniform law on its subterms'. -/
theorem uniform_chs_node {k : Comp} {a b : SPTerm ι} :
    PMF.uniformOfFintype (Chs P (node k a b)) =
      (PMF.uniformOfFintype (Chs P a × Chs P b)).map Chs.equivNode.symm :=
  (PMF.map_uniformOfFintype_equiv _).symm

section Seq

variable {Xin Xout : Type}

/-- **`lem:red-sp` (1)(c), series**: let the committed data be `join w m₁ m₂`, with `m₁` the masks
of `A₁` and `m₂` those of `A₂`. If `A₁` is zero knowledge with masks from `μ₁` at every
value of `m₂` (`h₁`), `A₂` with masks from `μ₂` at every value of `m₁` (`h₂`), and `A₁`'s honest
transcript does not read `m₂` (`hign`), then `A₂ ∘ A₁` is zero knowledge with both masks drawn
independently (`maskProd μ₁ μ₂`). -/
@[headline]
theorem HVZK.seq {A₁ : Reduction P a D X₁ (Xin × Xout)}
    {A₂ : Reduction P b D Xin X₂} {join : W → M₁ → M₂ → D} {μ₁ : PMF M₁} {μ₂ : PMF M₂}
    (h₁ : A₁.HVZK (fun (wm : W × M₂) m₁ => join wm.1 m₁ wm.2) μ₁)
    (h₂ : A₂.HVZK (fun (wm : W × M₁) m₂ => join wm.1 wm.2 m₂) μ₂)
    (hign : A₁.IgnoresMasks join) :
    (A₁.seq A₂).HVZK (fun w (m : M₁ × M₂) => join w m.1 m.2) (maskProd μ₁ μ₂) := by
  intro x w
  rw [viewLaw, uniform_chs_node]
  simp only [PMF.map_comp, Function.comp_def, run_seq]
  exact law_join_uniform μ₁ μ₂ (fun m₁ m₂ c => A₁.prover.run (x, join w m₁ m₂) c)
    (fun f m₁ m₂ c => A₂.prover.run ((A₁.out x f).1, join w m₁ m₂) c) (FullTr.equivNode (k := .seq))
    (fun m₁ m₂ m₂' c => hign x w m₁ m₂ m₂' c) (fun m₂ => h₁ x (w, m₂))
    (fun f m₁ => h₂ _ (w, m₁))

end Seq

section Par

variable {Y₁ Y₂ : Type}

/-- **`lem:red-sp` (2)(c), parallel**: let the committed data be `join w m₁ m₂`, with `m₁` the masks
of `A₁` and `m₂` those of `A₂`. If `A₁` is zero knowledge with masks from `μ₁` at every
value of `m₂` (`h₁`), `A₂` with masks from `μ₂` at every value of `m₁` (`h₂`), and the honest
transcript of `A₁`, the designated part, does not read `m₂` (`hign`), then `A₁ ∥ A₂` is zero
knowledge with both masks drawn independently (`maskProd μ₁ μ₂`). -/
@[headline]
theorem HVZK.par {A₁ : Reduction P a D X₁ Y₁} {A₂ : Reduction P b D X₂ Y₂}
    {join : W → M₁ → M₂ → D} {μ₁ : PMF M₁} {μ₂ : PMF M₂}
    (h₁ : A₁.HVZK (fun (wm : W × M₂) m₁ => join wm.1 m₁ wm.2) μ₁)
    (h₂ : A₂.HVZK (fun (wm : W × M₁) m₂ => join wm.1 wm.2 m₂) μ₂)
    (hign : A₁.IgnoresMasks join) :
    (A₁.par A₂).HVZK (fun w (m : M₁ × M₂) => join w m.1 m.2) (maskProd μ₁ μ₂) := by
  rintro ⟨x₁, x₂⟩ w
  rw [viewLaw, uniform_chs_node]
  simp only [PMF.map_comp, Function.comp_def, run_par]
  exact law_join_uniform μ₁ μ₂ (fun m₁ m₂ c => A₁.prover.run (x₁, join w m₁ m₂) c)
    (fun _ m₁ m₂ c => A₂.prover.run (x₂, join w m₁ m₂) c) (FullTr.equivNode (k := .par))
    (fun m₁ m₂ m₂' c => hign x₁ w m₁ m₂ m₂' c) (fun m₂ => h₁ x₁ (w, m₂))
    (fun _ m₁ => h₂ x₂ (w, m₁))

end Par

end ZK

end Reduction

end GordieHowe.IOP
