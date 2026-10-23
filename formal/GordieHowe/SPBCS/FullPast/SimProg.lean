-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.FullPast.ZeroKnowledge
public import GordieHowe.SPBCS.Merkle.TreeProg
public import GordieHowe.Model.Quantum.Interactive.ZeroKnowledge

@[expose] public section

/-!
# The simulator of the composite as a counted oracle program

The pieces of the composite's simulator as a counted classical oracle program
(`GordieHowe.NARG.Simulator`) at the series–parallel base model (`GordieHowe.SPBCS.FullPast`): the chains from
writes (`writeLeaf`), the proof from heaps (`proofOfHeaps`, `HeapsOf`), the default leaf
(`defaultProg`) and the assignments at the keys (`assignOfKeys`). The spBCS compiler's key program
(`GordieHowe.SPBCS.keyProg`), its program of the reply (`GordieHowe.SPBCS.jointProg`: the `leaf`
queries of the opened positions, the default leaf if some tree is empty, the `node` queries of each
tree's heap and one `transcript` query per challenge) and its simulator `GordieHowe.SPBCS.niSimulator`
are in `GordieHowe/SPBCS/SimProg.lean`, with the query bound
`GordieHowe.SPBCS.length_trace_jointProg_le`.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped BigOperators

variable {k kN kS L e : ℕ}

namespace Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι}
  {X : Type} (M : Base P t X k kN kS L e)

/-! ### The chains from writes and the proof from heaps -/

/-- The writes of every prover round of every leaf. -/
abbrev WriteAll : Type := (p : t.Leaf) → (i : (P p.label).MessageIdx) → (M.comp p.label).MessageWrite i

/-- Round `r` of leaf `p`'s chain with the writes `ws` and the streams `ρ`. -/
def writeItem (ρ : ChIdx P t → Out k e) (ws : M.WriteAll) (p : t.Leaf) (r : ℕ) :
    Item k (M.comp p.label).W :=
  if hr : r < n p.label then
    if hd : (P p.label).dir ⟨r, hr⟩ = .P_to_V then .write ⟨⟨⟨r, hr⟩, hd⟩, ws p _⟩
    else .absorb (ρ ⟨p, (P p.label).chIdx ⟨r, hr⟩ hd⟩).digest
  else .absorb fun _ => 0

/-- The first `r` items of leaf `p`'s chain with the writes `ws` and the streams `ρ`. -/
def writeLeaf (ρ : ChIdx P t → Out k e) (ws : M.WriteAll) (p : t.Leaf) : ℕ → M.Items p
  | 0 => []
  | r + 1 => writeLeaf ρ ws p r ++ [M.writeItem ρ ws p r]

theorem length_writeLeaf (ρ : ChIdx P t → Out k e) (ws : M.WriteAll) (p : t.Leaf) :
    ∀ r, (M.writeLeaf ρ ws p r).length = r
  | 0 => rfl
  | r + 1 => by simp [writeLeaf, length_writeLeaf ρ ws p r]

/-- Item `j < r` of the first `r` items of a written chain is `writeItem` at `j`. -/
theorem writeLeaf_getElem? (ρ : ChIdx P t → Out k e) (ws : M.WriteAll) (p : t.Leaf) :
    ∀ r j, j < r → (M.writeLeaf ρ ws p r)[j]? = some (M.writeItem ρ ws p j)
  | 0, _, hj => absurd hj (Nat.not_lt_zero _)
  | r + 1, j, hj => by
    rw [writeLeaf]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
    · rw [List.getElem?_append_left (by rw [length_writeLeaf]; exact hj'),
        writeLeaf_getElem? ρ ws p r j hj']
    · rw [List.getElem?_append_right (by rw [length_writeLeaf]), length_writeLeaf]
      simp

/-- **A prefix of a written chain is the shorter written chain.** -/
theorem writeLeaf_take (ρ : ChIdx P t → Out k e) (ws : M.WriteAll) (p : t.Leaf) {r r' : ℕ}
    (h : r ≤ r') : (M.writeLeaf ρ ws p r').take r = M.writeLeaf ρ ws p r := by
  induction r' with
  | zero =>
    obtain rfl : r = 0 := by omega
    rfl
  | succ r' ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le h) with h' | rfl
    · rw [writeLeaf, List.take_append_of_le_length (by rw [length_writeLeaf]; omega),
        ih (by omega)]
    · rw [List.take_of_length_le (by rw [length_writeLeaf])]

/-- **A written chain reads only its own streams and writes below its length.** -/
theorem writeLeaf_congr {ρ ρ' : ChIdx P t → Out k e} {ws ws' : M.WriteAll} {p : t.Leaf} :
    ∀ r, (∀ c : (P p.label).ChallengeIdx, c.1.1 < r → ρ ⟨p, c⟩ = ρ' ⟨p, c⟩) →
      (∀ i : (P p.label).MessageIdx, i.1.1 < r → ws p i = ws' p i) →
      M.writeLeaf ρ ws p r = M.writeLeaf ρ' ws' p r
  | 0, _, _ => rfl
  | r + 1, hρ, hw => by
    rw [writeLeaf, writeLeaf, writeLeaf_congr r (fun c hc => hρ c (by omega))
      (fun i hi => hw i (by omega))]
    congr 2
    unfold writeItem
    by_cases hr : r < n p.label
    · rw [dite_eq_left hr, dite_eq_left hr]
      by_cases hd : (P p.label).dir ⟨r, hr⟩ = .P_to_V
      · rw [dite_eq_left hd, dite_eq_left hd, hw ⟨⟨r, hr⟩, hd⟩ (by simp)]
      · rw [dite_eq_right hd, dite_eq_right hd,
          hρ ((P p.label).chIdx ⟨r, hr⟩ hd) (by simp [ProtocolSpec.chIdx])]
    · rw [dite_eq_right hr, dite_eq_right hr]

/-- **A written chain has a write at every prover round below its length.** -/
theorem writeLeaf_getElem?_write (ρ : ChIdx P t → Out k e) (ws : M.WriteAll) (p : t.Leaf)
    (i : (P p.label).MessageIdx) : (M.writeLeaf ρ ws p (n p.label))[i.1.1]? =
      some (.write ⟨i, ws p i⟩) := by
  rw [M.writeLeaf_getElem? ρ ws p _ _ i.1.2]
  unfold writeItem
  rw [dite_eq_left i.1.2, dite_eq_left i.2]
  rfl

variable (h : Query k kN kS L → Out k e)

/-- **The proof from writes and heaps**: the salt, the writes at the roots `hp τ 1` of the heaps,
the opened leaves `ops` at the positions `ps`, and each tree's opening read from its heap. -/
def proofOfHeaps (σ : FiatShamirSalt kS) (wr : M.RootWriteFn) (hp : M.Tree → ℕ → Digest k)
    (ops : List (MerkleLeaf kN L)) (ps : List M.Pos) : M.NIProof where
  salt := σ
  writes p i := wr p i fun τ => hp ⟨p, ⟨i, τ⟩⟩ 1
  leaves := ops
  paths τ := (M.opening.sibs ((M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree)
    ((M.openedIn τ ps ops).map Prod.fst)).map (hp τ)

/-- **A proof from heaps is in the format `B`** when its opened leaves number at most `B` and every
tree has at most `B` leaves. -/
theorem bounded_proofOfHeaps (σ : FiatShamirSalt kS) (wr : M.RootWriteFn)
    (hp : M.Tree → ℕ → Digest k) (ops : List (MerkleLeaf kN L)) (ps : List M.Pos) {B : ℕ}
    (hops : ops.length ≤ B) (hleaves : ∀ (p : t.Leaf) i τ, (M.comp p.label).nLeaves i τ ≤ B) :
    M.Bounded B (M.proofOfHeaps σ wr hp ops ps) := by
  refine ⟨hops, fun τ => ?_⟩
  simp only [proofOfHeaps, List.length_map]
  refine M.opening.length_sibs_le (fun j hj => ?_) ?_ (hleaves _ _ _)
  · obtain ⟨⟨j', a⟩, hm, rfl⟩ := List.mem_map.1 hj
    exact M.lt_of_mem_openedIn hm
  · rw [List.length_map]
    exact (M.length_openedIn_le τ ps ops).trans hops

variable {M h}

/-! ### Pieces of the program -/

variable (M)

/-- The trees of the composite in order (computable). -/
def treeList : List M.Tree :=
  t.leaves.flatMap fun p => (TreeIdx.list (P p.label) (M.comp p.label).nTrees).map fun τ => ⟨p, τ⟩

theorem mem_treeList (τ : M.Tree) : τ ∈ M.treeList :=
  List.mem_flatMap.2 ⟨τ.leaf, mem_leaves _, List.mem_map.2 ⟨τ.tree, TreeIdx.mem_list _, rfl⟩⟩

theorem nodup_treeList : M.treeList.Nodup := by
  refine List.nodup_flatMap.2 ⟨fun p _ => TreeIdx.nodup_list.map fun a b hab => ?_, ?_⟩
  · exact eq_of_heq (Tree.mk.inj hab).2
  · refine (nodup_leaves t).pairwise_of_forall_ne fun p _ q _ hpq => ?_
    simp only [Function.onFun, List.disjoint_left, List.mem_map]
    rintro _ ⟨τ, -, rfl⟩ ⟨τ', -, hτ⟩
    exact hpq (congrArg Tree.leaf hτ).symm

theorem sum_map_treeList {A : Type*} [AddCommMonoid A] (f : M.Tree → A) :
    (M.treeList.map f).sum = ∑ τ, f τ := by
  classical
  rw [← List.sum_toFinset _ M.nodup_treeList]
  congr 1
  ext τ
  simp [M.mem_treeList]

/-- The number of positions is the sum of the leaf counts of the trees. -/
theorem sum_nLeaves : ∑ τ : M.Tree, (M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree =
    Fintype.card M.Pos := by
  classical
  rw [Fintype.card_congr (Pos.equivSigma M), Fintype.card_sigma,
    ← (Tree.equivSigma M).symm.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Fintype.card_congr Position.equivSigma, Fintype.card_sigma,
    ← TreeIdx.equivSigma.symm.sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.card_sigma]
  simp [TreeIdx.equivSigma, Tree.equivSigma]

open Classical in
/-- The default-leaf program: if some tree has no leaves, the `leaf` query of the default leaf. -/
def defaultProg : OracleProg (Query k kN kS L) (Out k e) (Digest k) :=
  if ∃ τ : M.Tree, (M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree = 0 then
    MerkleTree.leafProg (⟨fun _ => 0, ⟨0, Fin.elim0⟩⟩ : MerkleLeaf kN L)
  else .pure fun _ => 0

open Classical in
theorem length_trace_defaultProg :
    ((M.defaultProg).trace h).length =
      if ∃ τ : M.Tree, (M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree = 0 then 1 else 0 := by
  unfold defaultProg
  split_ifs <;> rfl

/-- The leaf digests of tree `τ` read from a digest per position, with `dflt` past the last leaf. -/
def extD (ld : M.Pos → Digest k) (dflt : Digest k) (τ : M.Tree) (j : ℕ) : Digest k :=
  if hj : j < (M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree then
    ld ⟨τ.leaf, ⟨τ.tree.msg, τ.tree.tree, ⟨j, hj⟩⟩⟩ else dflt

/-- The assignment list of the keys, in global round order. -/
def assignOfKeys (σ : FiatShamirSalt kS) (ρ : ChIdx P t → Out k e) (keys : ChIdx P t → Digest k) :
    List (Assignment (Query k kN kS L) (Out k e)) :=
  (chList P t).map fun c => ⟨.xof (keys c) σ, ρ c⟩

/-- With a tree, some global round is a prover round, so there are fewer challenges than rounds. -/
theorem length_chList_lt (τ : M.Tree) : (chList P t).length < t.size n := by
  rw [chList, List.length_filterMap_eq_countP, List.countP_eq_length_filter, ← length_slots n t]
  refine List.length_filter_lt_length_iff_exists.2 ⟨⟨τ.leaf, τ.tree.msg.1⟩,
    List.mem_of_getElem? (slots_getElem n τ.leaf τ.tree.msg.1), ?_⟩
  simp [τ.tree.msg.2]

omit [(j : ι) → (i : (P j).ChallengeIdx) → Fintype ((P j).Challenge i)] [(j : ι) → (i : (P j).ChallengeIdx) → DecidableEq ((P j).Challenge i)] in
theorem length_chList_le : (chList P t).length ≤ t.size n := by
  rw [chList, ← length_slots n t]
  exact List.length_filterMap_le _ _

end Base

namespace FullPast

open Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι}
  {X : Type} (M : FullPast P t X k kN kS L e)

variable (h : Query k kN kS L → Out k e)

/-- The built chains are the chains of their writes at the roots of the leaf digests. -/
theorem buildLeaf_eq_writeLeaf (ρ : ChIdx P t → Out k e) (wr : M.RootWriteFn) (ld : M.Pos → Digest k)
    (p : t.Leaf) : ∀ r, M.buildLeaf h ρ wr ld p r =
      M.writeLeaf ρ (fun q i => wr q i (M.rootsOf h ld q i)) p r
  | 0 => rfl
  | r + 1 => by
    rw [buildLeaf, writeLeaf, buildLeaf_eq_writeLeaf ρ wr ld p r]
    rfl

/-- **The heaps of the trees over the leaf digests `ld`.** -/
def HeapsOf (ld : M.Pos → Digest k) (hp : M.Tree → ℕ → Digest k) : Prop :=
  ∀ (τ : M.Tree) (j : ℕ), MerkleTree.InWindow ((M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree) j →
    hp τ j = MerkleTree.nodeDigest h ((M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree)
      (M.leafDigestsOf h ld τ.leaf τ.tree.msg τ.tree.tree) j

variable {M h}

theorem heapsOf_nodeDigest {ld : M.Pos → Digest k} {f : M.Tree → ℕ → Digest k}
    (hf : ∀ (τ : M.Tree) (j : ℕ) (hj : j < (M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree),
      f τ j = ld ⟨τ.leaf, ⟨τ.tree.msg, τ.tree.tree, ⟨j, hj⟩⟩⟩)
    (h1 : ∀ τ : M.Tree, (M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree = 0 →
      f τ 1 = defaultLeafDigest h) :
    M.HeapsOf h ld fun τ =>
      MerkleTree.nodeDigest h ((M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree) (f τ) := by
  intro τ _ hj
  refine MerkleTree.nodeDigest_congr_window h (fun j hj => ?_) (fun h0 => ?_) hj
  · rw [hf τ j hj, leafDigestsOf, dite_eq_left hj]
  · rw [h1 τ h0, leafDigestsOf, dite_eq_right (by omega)]

theorem HeapsOf.rootsOf {ld : M.Pos → Digest k} {hp : M.Tree → ℕ → Digest k}
    (hh : M.HeapsOf h ld hp) : M.rootsOf h ld = fun p i τ => hp ⟨p, ⟨i, τ⟩⟩ 1 := by
  funext p i τ
  exact (hh ⟨p, ⟨i, τ⟩⟩ 1 (Or.inr rfl)).symm

/-- **The built proof is the proof from the heaps.** -/
theorem HeapsOf.buildProof_eq {ld : M.Pos → Digest k} {hp : M.Tree → ℕ → Digest k}
    (hh : M.HeapsOf h ld hp) (σ : FiatShamirSalt kS) (wr : M.RootWriteFn)
    (ops : List (MerkleLeaf kN L)) (ps : List M.Pos) :
    M.buildProof h σ wr ld ops ps = M.proofOfHeaps σ wr hp ops ps := by
  simp only [buildProof, proofOfHeaps, hh.rootsOf]
  congr 1
  funext τ
  refine List.map_congr_left fun c hc => (hh τ c ?_).symm
  have := M.opening.sibs_bounds hc
  exact Or.inl ⟨by omega, this.2⟩

/-- **The built chains are the chains of the writes at the roots of the heaps.** -/
theorem HeapsOf.buildLeaf_eq {ld : M.Pos → Digest k} {hp : M.Tree → ℕ → Digest k}
    (hh : M.HeapsOf h ld hp) (ρ : ChIdx P t → Out k e) (wr : M.RootWriteFn) (p : t.Leaf) (r : ℕ) :
    M.buildLeaf h ρ wr ld p r = M.writeLeaf ρ (fun q i => wr q i fun τ => hp ⟨q, ⟨i, τ⟩⟩ 1) p r := by
  rw [buildLeaf_eq_writeLeaf, hh.rootsOf]

/-! ### Pieces of the program -/

variable (M)

theorem run_defaultProg {τ : M.Tree} (hτ : (M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree = 0) :
    (M.defaultProg).run h = defaultLeafDigest h := by
  rw [defaultProg, if_pos ⟨τ, hτ⟩]
  rfl

end FullPast

end GordieHowe.SPBCS
