-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkJoin
public import GordieHowe.Model.IOP.SPIOP

@[expose] public section

/-!
# A multi-circuit IOP with forked domains as a composite IOP

The composite IOP (`GordieHowe.IOP.SPIOP`) of a multi-circuit IOP with forked domains (`GordieHowe.RealizedProgram.ProofSystem.IOP`), the
input of spBCS (`GordieHowe.SPBCS.Setting`): the prefix's first message is the
family of the domains' oracle messages, one tree per domain with the domain's leaves
(`GordieHowe.FieldProof.BranchShape.Oracle`); every other message of every component is read in full; the query positions
are, domain by domain, the leaves the domain's verdict reads at its join part's challenges
(`queryList`), and query locality follows from the domains' (`GordieHowe.FieldProof.BranchShape.Oracle.reads`).
-/

namespace GordieHowe

open IOP IOP.ProtocolSpec IOP.SPTerm SPBCS
open scoped NNReal

namespace RealizedProgram.ProofSystem.IOP

variable {Stmt W : Type} {rel : Set (Stmt × W)} (C : IOP Stmt W rel)

/-- The prefix has a first round. -/
theorem pos_rounds_pre : 0 < C.rounds .pre := by
  change 0 < 1 + (C.nc + C.app.n)
  omega

/-- The prefix's first message: the domains' oracle messages. -/
def oracleIdx : (C.P .pre).MessageIdx := ⟨⟨0, C.pos_rounds_pre⟩, rfl⟩

/-- The prefix's first message is the family of the domains' oracle messages. -/
theorem type_zero : (C.P .pre).Type ⟨0, C.pos_rounds_pre⟩ = C.Com :=
  append_Type_castAdd (P₁ := commitSpec C.Com) (P₂ := C.commitRounds ++ C.app.spec) ⟨0, Nat.one_pos⟩

/-- **The family of oracle messages as tables of leaves**, domain by domain. -/
def leavesEquiv : C.Com ≃ ((d : Fin C.m) → Fin (C.oracle d).nLeaves → (C.oracle d).Leaf) :=
  Equiv.piCongrRight fun d => (C.oracle d).leafEquiv

/-- **How the prefix's messages are read**: the first as the table of the domains' trees, every
later one in full. -/
def preShape (i : (C.P .pre).MessageIdx) : MessageShape ((C.P .pre).Type i.1) :=
  if h : (i.1 : ℕ) = 0 then
    .trees C.m (fun d => (C.oracle d).nLeaves) (fun d => (C.oracle d).Leaf)
      (fun d => (C.oracle d).leafDefault)
      ((Equiv.cast (congrArg (C.P .pre).Type (Fin.ext h : i.1 = ⟨0, C.pos_rounds_pre⟩))).trans
        ((Equiv.cast C.type_zero).trans C.leavesEquiv))
  else .plain _

/-- **The message structure of each component**: the prefix's (`preShape`), every message of a
branch or a join part read in full. -/
def comp : (j : C.shape.Idx) → CompIOP (C.P j)
  | .pre => CompIOP.ofShape C.preShape
  | .br _ _ => CompIOP.plain _
  | .jn _ => CompIOP.plain _

/-- The prefix's leaf in the series–parallel term. -/
abbrev preLeafT : C.term.Leaf := .left (.here (IOP.Shape.Idx.pre (S := C.shape)))

/-- **Domain `d`'s join part's challenges** among the composite challenges. -/
def joinCh (d : Fin C.m) (ch : Chs C.P C.term) : (C.circuit d).join.Challenges :=
  ((Chs.right ch).partN .par C.m d).right.at (.here (IOP.Shape.Idx.jn (S := C.shape) d))

/-- **Leaf `j` of domain `d`'s tree** as a query position. -/
def oraclePos (d : Fin C.m) (j : Fin (C.oracle d).nLeaves) : CausalPos (t := C.term) C.comp :=
  ⟨C.preLeafT, ⟨C.oracleIdx, d, j⟩⟩

theorem oraclePos_injective_right (d : Fin C.m) : Function.Injective (C.oraclePos d) := by
  intro j j' h
  cases h
  rfl

/-- **The queried leaves** at the composite challenges: domain by domain, the leaves its verdict
reads at its join part's challenges, in increasing order. -/
def queryList (ch : Chs C.P C.term) : List (CausalPos (t := C.term) C.comp) :=
  (List.finRange C.m).flatMap fun d =>
    (((C.oracle d).queries (C.joinCh d ch)).sort (· ≤ ·)).map (C.oraclePos d)

theorem mem_queryList {ch : Chs C.P C.term} {d : Fin C.m} {j : Fin (C.oracle d).nLeaves}
    (hj : j ∈ (C.oracle d).queries (C.joinCh d ch)) : C.oraclePos d j ∈ C.queryList ch :=
  List.mem_flatMap.2 ⟨d, List.mem_finRange d,
    List.mem_map.2 ⟨j, (Finset.mem_sort _).2 hj, rfl⟩⟩

theorem queryList_nodup (ch : Chs C.P C.term) : (C.queryList ch).Nodup := by
  refine List.nodup_flatMap.mpr ⟨fun d _ => (Finset.sort_nodup _ _).map
    (C.oraclePos_injective_right d), ?_⟩
  refine (List.nodup_finRange C.m).pairwise_of_forall_ne fun d _ d' _ hne => ?_
  refine List.disjoint_left.mpr fun q hq hq' => hne ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hq
  obtain ⟨j', -, e⟩ := List.mem_map.mp hq'
  have e' := congrArg (fun q : CausalPos (t := C.term) C.comp => q.pos.tree.1) e
  exact Fin.ext e'.symm

/-- A component with no tree reads a message off its non-oracle part. -/
theorem CompIOP.eq_of_nonOracle {m : ℕ} {Q : ProtocolSpec m} (c : CompIOP Q) {i : Q.MessageIdx}
    (h : c.nTrees i = 0) {a a' : Q.Type i.1}
    (e : ((c.parts i) a).nonOracle = ((c.parts i) a').nonOracle) : a = a' :=
  (c.parts i).injective (MessageParts.ext e (funext fun t => (Fin.cast h t).elim0))

/-- Only the prefix's messages carry trees, and only its first. -/
theorem nTrees_comp_eq_zero {j : C.shape.Idx} (i : (C.P j).MessageIdx)
    (h : j ≠ .pre ∨ (i.1 : ℕ) ≠ 0) : (C.comp j).nTrees i = 0 := by
  cases j with
  | pre =>
    have hi := h.resolve_left (fun h' => h' rfl)
    change (C.preShape i).nTrees = 0
    rw [preShape, dif_neg hi]
    rfl
  | br d b => rfl
  | jn d => rfl

/-- The leaves other than the prefix's are not labelled with the prefix. -/
theorem label_ne_pre {q : C.term.Leaf} (hq : q ≠ C.preLeafT) : q.label ≠ .pre := fun h =>
  hq (IOP.Shape.eq_leafOf_of_label h)

/-- **The oracle message of the prefix's first message**: its commitment family. -/
theorem com₀_left (tr : (C.P .pre).Transcript (Fin.last (C.rounds .pre))) :
    PhaseStep.com₀ (Transcript.left (P₁ := commitSpec C.Com) (P₂ := C.commitRounds ++ C.app.spec) tr) =
      cast C.type_zero (tr ⟨0, C.pos_rounds_pre⟩) :=
  rfl

/-- **The leaves of the prefix's first message** are the domains' leaves of its commitment. -/
theorem leaves_preShape (tr : (C.P .pre).Transcript (Fin.last (C.rounds .pre))) (d : Fin C.m)
    (j : Fin (C.oracle d).nLeaves) :
    ((C.comp .pre).parts C.oracleIdx (tr C.oracleIdx.1)).leaves d j =
      (C.oracle d).leaf (cast C.type_zero (tr ⟨0, C.pos_rounds_pre⟩) d) j :=
  rfl

/-- **Query locality of the composite verifier**: transcripts with the same challenges, the same
non-oracle parts and the same leaves at the queried positions get the same verdict. -/
theorem verifier_reads (x : Stmt) (f f' : FullTr C.P C.term)
    (hc : ∀ c : ChIdx C.P C.term, f.challenges c = f'.challenges c)
    (hn : ∀ (p : C.term.Leaf) (i : (C.P p.label).MessageIdx),
      ((C.comp p.label).parts i (f p i.1)).nonOracle = ((C.comp p.label).parts i (f' p i.1)).nonOracle)
    (hl : ∀ q ∈ C.queryList f.challenges,
      ((C.comp q.leaf.label).parts q.pos.msg (f q.leaf q.pos.msg.1)).leaves q.pos.tree q.pos.leaf =
        ((C.comp q.leaf.label).parts q.pos.msg (f' q.leaf q.pos.msg.1)).leaves q.pos.tree
          q.pos.leaf) :
    C.verifier x f = C.verifier x f' := by
  have hleaf : ∀ q : C.term.Leaf, q ≠ C.preLeafT → f q = f' q := fun q hq =>
    Transcript.ext_of_messages (ch := f.challenges.at q) (fun _ => rfl)
      (fun i => (hc ⟨q, i⟩).symm)
      fun i => CompIOP.eq_of_nonOracle _ (C.nTrees_comp_eq_zero i (.inl (C.label_ne_pre hq))) (hn q i)
  have hright : f.right = f'.right := funext fun p => hleaf (.right p) (by simp [preLeafT])
  set tr := f C.preLeafT with htr
  set tr' := f' C.preLeafT with htr'
  have hmsg : ∀ i : (C.P .pre).MessageIdx, (i.1 : ℕ) ≠ 0 → tr i.1 = tr' i.1 := fun i hi =>
    CompIOP.eq_of_nonOracle _ (C.nTrees_comp_eq_zero i (.inr hi)) (hn C.preLeafT i)
  have htrr : Transcript.right (P₁ := commitSpec C.Com) (P₂ := C.commitRounds ++ C.app.spec) tr =
      Transcript.right (P₁ := commitSpec C.Com) (P₂ := C.commitRounds ++ C.app.spec) tr' := by
    refine Transcript.ext_of_messages
      (ch := fun i => Transcript.right (P₁ := commitSpec C.Com) (P₂ := C.commitRounds ++ C.app.spec)
        tr i.1) (fun _ => rfl) (fun i => ?_) fun i => ?_
    · change cast _ (tr' (Fin.natAdd 1 i.1)) = cast _ (tr (Fin.natAdd 1 i.1))
      congr 1
      exact (hc ⟨C.preLeafT, ChallengeIdx.inr i⟩).symm
    · change cast _ (tr (Fin.natAdd 1 i.1)) = cast _ (tr' (Fin.natAdd 1 i.1))
      congr 1
      exact hmsg (MessageIdx.inr i) (by simp [MessageIdx.val_inr])
  have hdom : ∀ d, C.domainV d (x, f.left) (f.right.partN .par C.m d) =
      C.domainV d (x, f'.left) (f.right.partN .par C.m d) := fun d => by
    change (C.circuit d).V (C.app.pub d x
        (Transcript.right (P₁ := C.commitRounds) (P₂ := C.app.spec)
          (Transcript.right (P₁ := commitSpec C.Com) (P₂ := C.commitRounds ++ C.app.spec) tr)))
        (PhaseStep.com₀ (Transcript.left (P₁ := commitSpec C.Com)
          (P₂ := C.commitRounds ++ C.app.spec) tr) d)
        (Transcript.part C.m (Transcript.left (P₁ := C.commitRounds) (P₂ := C.app.spec)
          (Transcript.right (P₁ := commitSpec C.Com) (P₂ := C.commitRounds ++ C.app.spec) tr)) d)
        (C.branchTrs d (f.right.partN .par C.m d).left)
        ((f.right.partN .par C.m d).right (.here (IOP.Shape.Idx.jn (S := C.shape) d))) =
      (C.circuit d).V (C.app.pub d x
        (Transcript.right (P₁ := C.commitRounds) (P₂ := C.app.spec)
          (Transcript.right (P₁ := commitSpec C.Com) (P₂ := C.commitRounds ++ C.app.spec) tr')))
        (PhaseStep.com₀ (Transcript.left (P₁ := commitSpec C.Com)
          (P₂ := C.commitRounds ++ C.app.spec) tr') d)
        (Transcript.part C.m (Transcript.left (P₁ := C.commitRounds) (P₂ := C.app.spec)
          (Transcript.right (P₁ := commitSpec C.Com) (P₂ := C.commitRounds ++ C.app.spec) tr')) d)
        (C.branchTrs d (f.right.partN .par C.m d).left)
        ((f.right.partN .par C.m d).right (.here (IOP.Shape.Idx.jn (S := C.shape) d)))
    rw [← htrr]
    refine (C.oracle d).reads _ _ _ _ _ (C.joinCh d f.challenges) _ (fun i => ?_) fun j hj => ?_
    · exact congrArg (fun g : Chs C.P (C.domainTerm d) =>
        g.right.at (.here (IOP.Shape.Idx.jn (S := C.shape) d)) i)
        (FullTr.challenges_partN .par C.m (c := C.domainTerm) f.right d)
    · have h := hl (C.oraclePos d j) (C.mem_queryList hj)
      change ((C.comp .pre).parts C.oracleIdx (tr C.oracleIdx.1)).leaves d j =
        ((C.comp .pre).parts C.oracleIdx (tr' C.oracleIdx.1)).leaves d j at h
      exact h
  change (verifierN .par C.m C.domainV (x, f.left) f.right &&
      C.app.ok x (Transcript.right (P₁ := C.commitRounds) (P₂ := C.app.spec)
        (Transcript.right (P₁ := commitSpec C.Com) (P₂ := C.commitRounds ++ C.app.spec) tr))) =
    (verifierN .par C.m C.domainV (x, f'.left) f'.right &&
      C.app.ok x (Transcript.right (P₁ := C.commitRounds) (P₂ := C.app.spec)
        (Transcript.right (P₁ := commitSpec C.Com) (P₂ := C.commitRounds ++ C.app.spec) tr')))
  rw [← hright, htrr]
  exact congrArg (fun b => b && _) (verifierN_congr .par C.m (c := C.domainTerm) f.right hdom)

/-- **A multi-circuit IOP with forked domains as a composite IOP** (module docstring). -/
def toCausalIOP : SPIOP C.P C.term Stmt where
  comp := C.comp
  V := C.verifier
  pos := C.queryList
  pos_nodup := C.queryList_nodup
  reads := C.verifier_reads

end RealizedProgram.ProofSystem.IOP

end GordieHowe
