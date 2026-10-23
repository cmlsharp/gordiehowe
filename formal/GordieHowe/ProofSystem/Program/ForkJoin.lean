-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.AppPhase
public import GordieHowe.ProofSystem.FieldProof.Fork
public import GordieHowe.Model.IOP.CausalSound
public import GordieHowe.ProofSystem.Program.ForkJoinShape

@[expose] public section

/-!
# Multi-circuit IOPs with forked domains: the series–parallel composite and its soundness

A multi-circuit IOP whose circuit proofs are forked (`GordieHowe.FieldProof.BranchShape`, `GordieHowe/ProofSystem/FieldProof/Fork.lean`)
runs as the series–parallel composite of the proof system's series–parallel term
(`GordieHowe/ProofSystem/Program/ForkJoinShape.lean`):

    seq prefix (par over d of (seq (par over b of branch d b) (join d)))

* the prefix (`Shape.Idx.pre`): the commitment round with every domain's oracle message, the
  domains' commit rounds in order, then the application phase (`GordieHowe.RealizedProgram.ProofSystem.PhaseStep.committedSpec`);
* branch `b` of domain `d` (`.br d b`): the domain's branch protocol, on the statement the prefix
  fixes (`domainStmt`: the domain's public input from the application phase, its oracle message and
  its commit rounds);
* the join part of domain `d` (`.jn d`): the domain's join protocol, on the domain's statement and
  its branches' full transcripts.

The composite verifier (`verifier`) accepts when the application phase's check passes and every
domain's verdict accepts. **Causal round-by-round knowledge soundness** (`causal_rbr`): at the
extractor that reads the circuits' witnesses from the prefix's commit phase and applies the
application phase's `extract` (`extractor`), every challenge keeps its own error (`error`): the
commit rounds' and the application phase's at the prefix, each branch's reduction errors at its
rounds, each join's at its rounds. The prefix is a claim-producing phase (`prefixPhase`: the
application phase's state after the commit phase, `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.committedState`, whose condition
switches on at a challenge round of the application phase); each branch a claim reduction
(`CausalRBR.ofClaimReduction`); each join a claim-proving phase (`CausalRBR.ofClaimProof`); the
domain's fixed claim travels with the branches' claims (`CausalRBR.and_stmt`); the application
phase's check enters at the sequence (`CausalRBR.seq_guard`). When the application phase has no
challenge round, its condition is the relation on the extracted witness, and the extractor gives
that witness at every challenge of the domains (every join draws one,
`GordieHowe.FieldProof.BranchShape.joinNonemptyIdx`), so no state needs to switch.
-/

namespace GordieHowe

open IOP IOP.ProtocolSpec IOP.SPTerm
open scoped NNReal

/-- **A multi-circuit IOP with forked domains** (module docstring): `m ≥ 1` domains, each a forked
circuit proof of its relation `holds d` with the reading of its oracle message, and the application
phase. -/
structure RealizedProgram.ProofSystem.IOP (Stmt W : Type) (rel : Set (Stmt × W)) where
  /-- The number of domains. -/
  m : ℕ
  /-- There is a domain. -/
  [neZero : NeZero m]
  /-- The domains' public inputs. -/
  Pub : Fin m → Type
  /-- The domains' witnesses. -/
  Wit : Fin m → Type
  /-- The domains' relations. -/
  holds : ∀ d, Pub d → Wit d → Prop
  /-- The domains' forked circuit proofs. -/
  circuit : ∀ d, FieldProof.BranchShape (Pub d) (Wit d)
  /-- How each domain's verdict reads its oracle message. -/
  oracle : ∀ d, (circuit d).Oracle
  /-- The application phase. -/
  app : PhaseStep Stmt W rel Pub Wit holds

attribute [instance] RealizedProgram.ProofSystem.IOP.neZero

namespace RealizedProgram.ProofSystem.IOP

variable {Stmt W : Type} {rel : Set (Stmt × W)} (C : IOP Stmt W rel)

/-! ### The commit phase of all domains -/

/-- The domains' oracle messages, one family in the commitment round. -/
abbrev Com : Type := ∀ d, (C.circuit d).Com

/-- The number of commit rounds: the domains' in order. -/
abbrev nc : ℕ := lenN C.m fun d => (C.circuit d).nc

/-- The commit rounds: the domains' in order. -/
abbrev commitRounds : ProtocolSpec C.nc := appendN C.m fun d => (C.circuit d).commitRounds

/-- The domains' witnesses extracted from the commit phase, domain by domain. -/
def ext (O : C.Com) (r : C.commitRounds.Transcript (Fin.last C.nc)) (d : Fin C.m) : C.Wit d :=
  (C.circuit d).ext (O d) (Transcript.part C.m r d)

/-! ### The series–parallel composite -/

/-- **The series–parallel shape**: the domains, each with its branches. -/
abbrev shape : IOP.Shape where
  nd := C.m
  nb d := (C.circuit d).nb
  nb_pos d := (C.circuit d).nb_pos

/-- The number of rounds of each component. Defined by `Shape.Idx.casesOn` rather than by
equations, so that two composites with the same components have definitionally equal rounds at a
variable component (an equation compiler definition does not unfold there). -/
def rounds (j : C.shape.Idx) : ℕ :=
  Shape.Idx.casesOn (motive := fun _ => ℕ) j (1 + (C.nc + C.app.n)) (fun d b => (C.circuit d).bn b)
    fun d => (C.circuit d).jn

/-- **The components**: the prefix (commit phase and application phase), the branches and the
join parts (by `Shape.Idx.casesOn`, as `rounds`). -/
def P (j : C.shape.Idx) : ProtocolSpec (C.rounds j) :=
  Shape.Idx.casesOn (motive := fun j => ProtocolSpec (C.rounds j)) j
    (C.app.committedSpec C.Com C.commitRounds) (fun d b => (C.circuit d).branch b)
    fun d => (C.circuit d).join

instance instFintypeP : ∀ j i, Fintype ((C.P j).Challenge i)
  | .pre, i => (inferInstance : ∀ i, Fintype ((C.app.committedSpec C.Com C.commitRounds).Challenge i)) i
  | .br d b, i => (C.circuit d).branchFintype b i
  | .jn d, i => (C.circuit d).joinFintype i

instance instDecEqP : ∀ j i, DecidableEq ((C.P j).Challenge i)
  | .pre, i => (inferInstance : ∀ i, DecidableEq ((C.app.committedSpec C.Com C.commitRounds).Challenge i)) i
  | .br d b, i => (C.circuit d).branchDecEq b i
  | .jn d, i => (C.circuit d).joinDecEq i

instance instNonemptyP : ∀ j i, Nonempty ((C.P j).Challenge i)
  | .pre, i => (inferInstance : ∀ i, Nonempty ((C.app.committedSpec C.Com C.commitRounds).Challenge i)) i
  | .br d b, i => (C.circuit d).branchNonempty b i
  | .jn d, i => (C.circuit d).joinNonempty i

/-- The series–parallel term. -/
abbrev term : SPTerm C.shape.Idx := C.shape.term

/-- The prefix's term. -/
abbrev preTerm : SPTerm C.shape.Idx := leaf .pre

/-- The prefix's leaf in its term. -/
abbrev preHere : C.preTerm.Leaf := Leaf.here (IOP.Shape.Idx.pre (S := C.shape))

/-- The statements after the prefix: the statement and the prefix's full transcript. -/
abbrev PostStmt : Type := SeqStmt Stmt C.P C.preTerm

/-- **The context after the prefix**: the statement and the prefix's transcript. -/
def context (y : C.PostStmt) : C.app.CommittedContext C.Com C.commitRounds :=
  ⟨y.1, y.2 C.preHere⟩

/-- **Domain `d`'s statement** after the prefix: its public input from the application phase, its
oracle message and its commit rounds. -/
def domainStmt (d : Fin C.m) (y : C.PostStmt) : (C.circuit d).Stmt :=
  ⟨C.app.pub d (C.context y).stmt (C.context y).app, (C.context y).com d,
    Transcript.part C.m (C.context y).rounds d⟩

/-- Domain `d`'s branches as a term. -/
abbrev branchTerm (d : Fin C.m) : SPTerm C.shape.Idx :=
  parN ((C.circuit d).nb) fun b => leaf (.br d b)

/-- Domain `d`'s term: its branches side by side, then its join part. -/
abbrev domainTerm (d : Fin C.m) : SPTerm C.shape.Idx :=
  seq (C.branchTerm d) (leaf (.jn d))

/-- **The branches' full transcripts** in a composite transcript of domain `d`'s branches. -/
def branchTrs (d : Fin C.m) (f : FullTr C.P (C.branchTerm d)) : (C.circuit d).BranchTrs :=
  fun b => (f.partN .par _ b) (Leaf.here (IOP.Shape.Idx.br (S := C.shape) d b))

/-- **The join's statement** of domain `d`: the domain's statement and its branches' full
transcripts. -/
def joinStmt (d : Fin C.m) (z : SeqStmt C.PostStmt C.P (C.branchTerm d)) :
    (C.circuit d).JoinStmt :=
  ⟨C.domainStmt d z.1, C.branchTrs d z.2⟩

/-- Domain `d`'s verdict on the prefix and its part of the composite transcript. -/
def domainV (d : Fin C.m) (y : C.PostStmt) (f : FullTr C.P (C.domainTerm d)) : Bool :=
  (C.circuit d).V (C.domainStmt d y).pub (C.domainStmt d y).com (C.domainStmt d y).rounds
    (C.branchTrs d f.left) (f.right (Leaf.here (IOP.Shape.Idx.jn (S := C.shape) d)))

/-- **The composite verifier**: every domain's verdict on its statement, its branches'
transcripts and its join's transcript, and the application phase's check. -/
def verifier (x : Stmt) (f : FullTr C.P C.term) : Bool :=
  verifierN .par C.m C.domainV (x, f.left) f.right && C.app.ok x (C.context (x, f.left)).app

/-! ### Soundness -/

/-- **Soundness of a multi-circuit IOP with forked domains**: every domain's forked soundness and
the application phase's errors with their event bound. -/
structure Sound where
  /-- The domains' soundness. -/
  circuit : ∀ d, (C.circuit d).Sound (C.holds d)
  /-- The application phase's errors. -/
  εapp : C.app.spec.ChallengeIdx → ℝ≥0
  /-- The application phase's events are bounded by its errors. -/
  eventBound : C.app.EventBound εapp

variable {C} (S : C.Sound)

/-- The commit phase's bad events: some domain's (`BadState.orN`). -/
def Sound.commit : BadState C.commitRounds C.Com (ProtocolSpec.errN C.m fun d => (S.circuit d).εc) :=
  BadState.orN C.m fun d => (S.circuit d).commit.comap fun O => O d

/-- **The prefix's errors**: the commit rounds' and the application phase's. -/
def Sound.preError : (C.P .pre).ChallengeIdx → ℝ≥0 :=
  C.app.committedError C.commitRounds (ProtocolSpec.errN C.m fun d => (S.circuit d).εc) S.εapp

section Extraction

variable [Inhabited W]

/-- **The prefix's extractor**: the application phase's (`PhaseStep.extractor`), reading the
domains' witnesses from the commit phase with `ext`.

Running time: one call of every domain's `ext` and one of `extract`.
This running time is argued here, not proved in Lean. -/
def preExtractor : Extractor (C.P .pre) Stmt W := C.app.extractor C.ext

/-- The claim the prefix produces: a bad commit phase, or a challenge round of the application phase
and its condition at the witnesses read from the commit phase. Not required to be efficient. -/
def Sound.preClaim (S : C.Sound) (x : Stmt) (tr : (C.P .pre).Transcript (Fin.last (C.rounds .pre))) : Prop :=
  PhaseStep.CommittedContext.Bad S.commit (⟨x, tr⟩ : C.app.CommittedContext C.Com C.commitRounds) ∨
    (Nonempty C.app.spec.ChallengeIdx ∧ C.app.committedCond C.ext ⟨x, tr⟩)

open Classical in
/-- **The prefix as a claim-producing phase**: the application phase's state after the commit
phase (`PhaseStep.committedState`), its extractor, and the claim `preClaim`. -/
def Sound.prefixPhase : ClaimPhase (C.P .pre) Stmt W rel S.preError where
  E := C.preExtractor
  claim := S.preClaim
  S := C.app.committedState C.ext S.commit
  empty := C.app.committedState_zero C.ext S.commit
  next := C.app.committedState_next C.ext S.commit
  full x tr h := (C.app.committedState_last_iff C.ext S.commit ⟨x, tr⟩).mpr h
  rbr x i tr := by
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card fun c hc =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩))
      (C.app.committedState_flip_card C.ext S.commit S.eventBound x i tr)
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hc
    exact ⟨.inr h1, h2⟩

/-- **The extractor of the composite**: the prefix's extractor at the prefix's challenges; at every
other challenge, the prefix's extractor on the full prefix transcript.

Running time: one call of `preExtractor` (its paragraph) on the challenge's causal past, read from
its prefix part; polynomial. This running time is argued here, not proved in Lean. -/
def extractor : CausalExtractor C.P C.term Stmt W :=
  (CausalExtractor.ofLeaf C.preExtractor).seq
    (CausalExtractor.ofStmt fun y => C.preExtractor (Fin.last _) y.1 (y.2 C.preHere))

/-- **The state function of the composite**: the prefix's state at the prefix, each branch's
reduction state on its domain's statement, each join's state on its statement. Not required to be
efficient. -/
def Sound.stateFn : CausalStateFn C.P C.term Stmt :=
  (CausalStateFn.ofLeaf (P := C.P) (j := .pre) (C.app.committedState C.ext S.commit)).seq
    (CausalStateFn.nodeN .par C.m fun d =>
      (CausalStateFn.nodeN .par (C.circuit d).nb fun b =>
        CausalStateFn.ofLeaf (P := C.P) (j := .br d b) fun k y tr => ((S.circuit d).red b).S k (C.domainStmt d y) tr).seq
      (CausalStateFn.ofLeaf (P := C.P) (j := .jn d) fun k z tr => (S.circuit d).proof.S k (C.joinStmt d z) tr))

/-- **The errors of the composite**: the prefix's at its challenges, each branch's and each join's
at theirs. -/
def Sound.error : ChIdx C.P C.term → ℝ≥0 :=
  errNode (errLeaf (P := C.P) (j := .pre) S.preError)
    (IOP.errN .par C.m fun d =>
      errNode (IOP.errN .par (C.circuit d).nb fun b => errLeaf (P := C.P) (j := .br d b) ((S.circuit d).εb b))
        (errLeaf (P := C.P) (j := .jn d) (S.circuit d).εj))

/-- **A bound on every round's error** (each round on its own): the domains' commit rounds, the
application phase's, every branch's and every join's. -/
theorem Sound.error_le {δ : ℝ≥0} (hcommit : ∀ d j, (S.circuit d).εc j ≤ δ) (happ : ∀ j, S.εapp j ≤ δ)
    (hbranch : ∀ d b j, (S.circuit d).εb b j ≤ δ) (hjoin : ∀ d j, (S.circuit d).εj j ≤ δ) :
    ∀ c, S.error c ≤ δ :=
  errNode_le (errLeaf_le (C.app.committedError_le (ProtocolSpec.errN_le fun d j => hcommit d j) happ))
    (IOP.errN_le .par C.m fun d => errNode_le (IOP.errN_le .par (C.circuit d).nb fun b =>
      errLeaf_le (hbranch d b)) (errLeaf_le (hjoin d)))

/-- **Domain `d` reduces its branches' input claims and its fixed claim to its verdict.** -/
theorem Sound.domain_rbr (d : Fin C.m) :
    CausalRBR (Set.onStmt (a := C.preTerm) rel)
      (CausalExtractor.ofStmt fun y => C.preExtractor (Fin.last _) y.1 (y.2 C.preHere))
      ((CausalStateFn.nodeN .par (C.circuit d).nb fun b =>
        CausalStateFn.ofLeaf (P := C.P) (j := .br d b) fun k y tr => ((S.circuit d).red b).S k (C.domainStmt d y) tr).seq
        (CausalStateFn.ofLeaf (P := C.P) (j := .jn d) fun k z tr => (S.circuit d).proof.S k (C.joinStmt d z) tr))
      (errNode (IOP.errN .par (C.circuit d).nb fun b => errLeaf (P := C.P) (j := .br d b) ((S.circuit d).εb b))
        (errLeaf (P := C.P) (j := .jn d) (S.circuit d).εj))
      (fun y => (∀ b, ((S.circuit d).red b).claim (C.domainStmt d y)) ∧
        (S.circuit d).fixed (C.domainStmt d y))
      fun y f => C.domainV d y f = true := by
  have hbr := (CausalRBR.nodeN (rel := Set.onStmt (a := C.preTerm) rel) .par (C.circuit d).nb
    (E := fun _ => CausalExtractor.ofStmt fun y => C.preExtractor (Fin.last _) y.1 (y.2 C.preHere))
    fun b => CausalRBR.ofClaimReduction (P := C.P) (j := .br d b) ((S.circuit d).red b) (C.domainStmt d) _ _).and_stmt
    fun y => (S.circuit d).fixed (C.domainStmt d y)
  have hjn := CausalRBR.ofClaimProof (P := C.P) (j := .jn d) ((S.circuit d).proof.comap (C.joinStmt d))
    (Set.onStmt (a := C.branchTerm d) (Set.onStmt (a := C.preTerm) rel))
    (CausalExtractor.ofStmt fun z => C.preExtractor (Fin.last _) z.1.1 (z.1.2 C.preHere))
  refine (((hbr.seq hjn fun y f h => ?_).mono (fun _ h => h) fun y f hV => ?_).congr_extractor
    fun c y past => ?_)
  · obtain ⟨hout, hfix⟩ := (S.circuit d).join_claim _ h
    exact ⟨(claimOutN_iff .par _ _ y f).mpr fun b => hout b, hfix⟩
  · change (S.circuit d).proof.V (C.joinStmt d (y, f.left)) (f.right (Leaf.here (IOP.Shape.Idx.jn (S := C.shape) d))) = true
    exact ((S.circuit d).V_eq _ _).trans hV
  · rcases ChIdx.left_or_right c with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact CausalExtractor.nodeN_ofStmt .par _ _ c y _
    · rfl

/-- **Causal round-by-round knowledge soundness of a multi-circuit IOP with forked domains**
(module docstring): at the composite verifier, the extractor `extractor`, the state function
`stateFn` and the errors `error`. -/
theorem Sound.causal_rbr :
    CausalRBRKnowledgeSound rel C.verifier C.extractor S.stateFn S.error := by
  have hpre := CausalRBR.ofClaimPhase S.prefixPhase
  have hdom := CausalRBR.nodeN (rel := Set.onStmt (a := C.preTerm) rel) .par C.m
    (E := fun _ => CausalExtractor.ofStmt fun y => C.preExtractor (Fin.last _) y.1 (y.2 C.preHere))
    fun d => S.domain_rbr d
  refine ((hpre.seq_guard hdom (fun x f => C.app.ok x (C.context (x, f)).app = true)
    fun x f g hall hok => ?_).mono (fun _ h => h) fun x f hV => ?_).congr_extractor
      fun c x past => ?_
  · classical
    by_cases hh : AllHold C.holds (fun d => C.app.pub d x (C.context (x, f)).app)
        (C.ext (C.context (x, f)).com (C.context (x, f)).rounds)
    · have hc : C.app.committedCond C.ext (C.context (x, f)) :=
        C.app.committedCond_of_claim C.ext ⟨hok, hh⟩
      by_cases hne : Nonempty C.app.spec.ChallengeIdx
      · exact .inl (.inr ⟨hne, hc⟩)
      · obtain ⟨j⟩ := (C.circuit ⟨0, Nat.pos_of_neZero C.m⟩).joinNonemptyIdx
        refine .inr ⟨ChIdx.inN .par C.m ⟨0, Nat.pos_of_neZero C.m⟩ (ChIdx.right
          ⟨Leaf.here (IOP.Shape.Idx.jn (S := C.shape) ⟨0, Nat.pos_of_neZero C.m⟩), j⟩), ?_⟩
        rw [CausalExtractor.nodeN_ofStmt]
        change (x, C.app.extractor C.ext (Fin.last _) (C.context (x, f)).stmt
          (C.context (x, f)).transcript) ∈ rel
        rw [PhaseStep.extractor_last]
        exact C.app.mem_of_cond hne hc
    · obtain ⟨d, hd⟩ := not_forall.mp hh
      have hb := ((S.circuit d).claim_imp _ (hall d).1 (hall d).2).resolve_right hd
      exact .inl (.inl (S.commit.full _ _ (BadState.bad_orN_of C.m _ _ _ d hb)))
  · have hV : (verifierN .par C.m C.domainV (x, f.left) f.right &&
        C.app.ok x (C.context (x, f.left)).app) = true := hV
    rw [Bool.and_eq_true] at hV
    exact ⟨verifierN_eq_true .par C.m _ _ _ hV.1, hV.2⟩
  · rcases ChIdx.left_or_right c with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · rfl
    · exact CausalExtractor.nodeN_ofStmt .par _ _ c _ _

end Extraction

end RealizedProgram.ProofSystem.IOP

end GordieHowe
