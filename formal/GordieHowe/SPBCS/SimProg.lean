-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.ZeroKnowledge
public import GordieHowe.SPBCS.Bytes
public import GordieHowe.SPBCS.SimAssign
public import GordieHowe.SPBCS.Merkle.TreeProg
public import GordieHowe.Model.Quantum.Interactive.ZeroKnowledge

@[expose] public section

/-!
# The simulator of the spBCS compiler as a counted oracle program

The simulator of the spBCS compiler `niSimulator` (paper `prot:bcs-simulator`), a classical oracle
program (`GordieHowe.NARG.Simulator`) against the compiler's oracle, with the
pieces below: the `leaf` queries of the opened positions, the default leaf if
some tree is empty, the `node` queries of each tree's heap, one `transcript` query per branch (its
final input, `finalsProg`) and one `transcript` query per challenge (its chain input); at most
`2 |Pos| + t.size n + |sites|` queries (`length_trace_jointProg_le`), the paper's
`q_S = 2 n_pos + n_msg + n_B` (`prot:bcs-simulator`). It returns a proof in the format `B` or fails
where the simulated view does not decode. The hybrid argument of
`GordieHowe/SPBCS/ZeroKnowledge.lean` is stated for `niJointSimulator`, whose replies use the proof
device `SPBCS.Internal.encodeTotal`; run through `queryEncoding`, `niSimulator` is that simulator
within the format bounds of the views (`niSimulator_eq`, `encode_niSimulator`,
`toFn_niJointSimulatorProg`).

A counted program needs the sites as a list (`SiteLayout`, `GordieHowe/SPBCS/Bytes.lean`): the final
inputs are queried in the order `siteOrder`, the sites sorted by the number of branches hidden
from their sinks, so every branch hidden from a sink is queried before it (`hiders_sink_ssubset`)
and each final input is queried once with the final digests it holds (`run_finalsProg`).

Every assignment of the reply program programs the `xof` point of the salt at the digest of a
queried chain input holding the salted statement (`assignsAtKeys_jointProg`, the property
`AssignsAtKeys` that simulation-sound extractability uses).
-/

/-!
## The pieces of the simulator as a counted oracle program

The pieces of the simulator as a counted classical oracle program (`GordieHowe.NARG.Simulator`):
the chains from writes (`writeLeaf`), the proof from heaps (`proofOfHeaps`, `HeapsOf`), the
default leaf (`defaultProg`) and the assignments at the keys (`assignOfKeys`). The key program
(`keyProg`), the program of the reply (`jointProg`: the `leaf` queries of the opened positions, the
default leaf if some tree is empty, the `node` queries of each tree's heap and one `transcript`
query per challenge) and the simulator `niSimulator` follow, with the query bound
`length_trace_jointProg_le`.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped BigOperators

variable {k kN kS L e : ℕ}

section

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι} {Mg : Merges t}
  {X : Type} (M : SPBCS Mg P X k kN kS L e)

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

end

section

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι} {Mg : Merges t}
  {X : Type} (M : SPBCS Mg P X k kN kS L e)

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

end

end GordieHowe.SPBCS

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm Quantum GordieHowe.QROM
open scoped BigOperators

variable {ι : Type} {k kN kS L e : ℕ} {t : SPTerm ι}

section

variable {Mg : Merges t} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}
  (M : SPBCS Mg P X k kN kS L e)

/-! ### The order of the final inputs -/

section Order

variable (Λ : SiteLayout Mg)

/-- The number of branches hidden from the sink of a site. -/
def siteRank (s : Mg.Site) : ℕ := (Merges.hiders (M := Mg) (.sink s)).card

/-- **The sites in the order their final inputs are queried**: sorted by `siteRank`. -/
def siteOrder : List Mg.Site := Λ.sites.mergeSort fun a b => decide (siteRank a ≤ siteRank b)

theorem pairwise_siteOrder : (siteOrder Λ).Pairwise fun a b => siteRank a ≤ siteRank b := by
  have := List.pairwise_mergeSort (le := fun a b : Mg.Site => decide (siteRank a ≤ siteRank b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) Λ.sites
  exact this.imp fun h => by simpa using h

theorem perm_siteOrder : (siteOrder Λ).Perm Λ.sites := List.mergeSort_perm _ _

theorem nodup_siteOrder : (siteOrder Λ).Nodup := (perm_siteOrder Λ).nodup_iff.2 Λ.nodup

theorem mem_siteOrder (s : Mg.Site) : s ∈ siteOrder Λ := (perm_siteOrder Λ).mem_iff.2 (Λ.mem_sites s)

theorem length_siteOrder_le : (siteOrder Λ).length ≤ Fintype.card Mg.Site :=
  (nodup_siteOrder Λ).length_le_card

/-- **A branch hidden from a sink has a smaller rank.** -/
theorem siteRank_lt_of_hides {s s' : Mg.Site} (hs : Mg.Hides s' (.sink s)) :
    siteRank s' < siteRank s :=
  Finset.card_lt_card (Merges.hiders_sink_ssubset hs)

end Order

/-! ### The final-input program -/

section Finals

variable (ss : SaltedStatement kS X) (chs : M.Chains)

/-- **The final inputs of the sites of `l` in order**, from the final digests `fs`: the
`transcript` query of each site's final input at the digests so far, recording its digest. -/
def finalsProgFrom : List Mg.Site → (Mg.Site → Digest k) →
    OracleProg (Query k kN kS L) (Out k e) (Mg.Site → Digest k)
  | [], fs => .pure fs
  | s :: l, fs => .query (.transcript (M.senc.encode (finalContent ss chs fs s))) fun w =>
      finalsProgFrom l (Function.update fs s w.digest)

/-- **The final-input program**: the final inputs of all sites in the order `siteOrder`. -/
def finalsProg (Λ : SiteLayout Mg) : OracleProg (Query k kN kS L) (Out k e) (Mg.Site → Digest k) :=
  M.finalsProgFrom ss chs (siteOrder Λ) 0

variable (h : Query k kN kS L → Out k e)

theorem length_trace_finalsProgFrom : ∀ (l : List Mg.Site) (fs : Mg.Site → Digest k),
    ((M.finalsProgFrom ss chs l fs).trace h).length = l.length
  | [], _ => rfl
  | s :: l, fs => by
    simp only [finalsProgFrom, OracleProg.trace_query, List.length_cons,
      length_trace_finalsProgFrom l]

/-- **The final-input program from digests agreeing with the final digests off the sites still to
query** returns the final digests, when the sites are sorted by rank. -/
theorem run_finalsProgFrom : ∀ (l : List Mg.Site) (fs : Mg.Site → Digest k),
    l.Pairwise (fun a b => siteRank a ≤ siteRank b) → l.Nodup →
    (∀ s, s ∉ l → fs s = M.finalsWith h ss chs s) →
    (M.finalsProgFrom ss chs l fs).run h = M.finalsWith h ss chs
  | [], fs, _, _, hfs => funext fun s => hfs s List.not_mem_nil
  | s :: l, fs, hp, hnd, hfs => by
    rw [finalsProgFrom, OracleProg.run_query]
    refine run_finalsProgFrom l _ hp.of_cons hnd.of_cons fun s' hs' => ?_
    by_cases he : s' = s
    · subst he
      rw [Function.update_self, finalsWith_eq chs s']
      refine finalStep_congr (fun _ _ => rfl) fun s'' hs'' => hfs s'' fun hm => ?_
      have hlt := siteRank_lt_of_hides hs''
      rcases List.mem_cons.1 hm with rfl | hm
      · omega
      · have := List.rel_of_pairwise_cons hp hm
        omega
    · rw [Function.update_of_ne he]
      exact hfs s' fun hm => (List.mem_cons.1 hm).elim he hs'

/-- **The final-input program returns the final digests.** -/
theorem run_finalsProg (Λ : SiteLayout Mg) :
    (M.finalsProg ss chs Λ).run h = M.finalsWith h ss chs :=
  M.run_finalsProgFrom ss chs h _ 0 (pairwise_siteOrder Λ) (nodup_siteOrder Λ) fun s hs =>
    absurd (mem_siteOrder Λ s) hs

theorem length_trace_finalsProg_le (Λ : SiteLayout Mg) :
    ((M.finalsProg ss chs Λ).trace h).length ≤ Fintype.card Mg.Site := by
  rw [finalsProg, length_trace_finalsProgFrom]
  exact length_siteOrder_le Λ

end Finals

/-! ### Pieces of the program -/

/-- The key program: the `transcript` query of the chain input of leaf `p` with the chains `chs`,
the final digests `fs` and the own items `l`, returning the key. -/
def keyProg (ss : SaltedStatement kS X) (chs : M.Chains) (fs : Mg.Site → Digest k) (p : t.Leaf)
    (l : M.Items p) : OracleProg (Query k kN kS L) (Out k e) (Digest k) :=
  .query (.transcript (M.senc.encode (roundContent ss chs fs p l))) fun w => .pure w.digest

variable (h : Query k kN kS L → Out k e)

theorem length_trace_keyProg (ss : SaltedStatement kS X) (chs : M.Chains) (fs : Mg.Site → Digest k)
    (p : t.Leaf) (l : M.Items p) : ((M.keyProg ss chs fs p l).trace h).length = 1 := rfl

theorem run_keyProg (ss : SaltedStatement kS X) (chs : M.Chains) (fs : Mg.Site → Digest k)
    (p : t.Leaf) (l : M.Items p) : (M.keyProg ss chs fs p l).run h = M.key h ss chs fs p l := rfl

/-- **The assignment list of the keys is the built assignment list** when the keys are the
built keys. -/
theorem assignOfKeys_eq_buildAssign (ss : SaltedStatement kS X) (ρ : ChIdx P t → Out k e)
    (wr : M.RootWriteFn) (ld : M.Pos → Digest k) {keys : ChIdx P t → Digest k}
    (hk : ∀ c, keys c = M.buildKey h ss ρ wr ld c) :
    SPBCS.assignOfKeys ss.salt ρ keys = M.buildAssign h ss ρ wr ld := by
  unfold SPBCS.assignOfKeys buildAssign
  exact List.map_congr_left fun c _ => by rw [hk]

/-! ### The program of the reply -/

variable (Λ : SiteLayout Mg) (VR : M.ViewRead) (B : ℕ)

/-- **The queries of the simulator's reply at writes `wr`**: the `leaf` queries of the distinct
opened positions, the default leaf, the heaps, one `transcript` query per branch (its final digest,
`finalsProg`) and one per challenge (its key); then the response `fin hp` at the heaps `hp` and the
assignments of the streams at the keys. -/
def jointBody (x : X) (σ : FiatShamirSalt kS) (ch : Chs P t) (ρ : ChIdx P t → Out k e)
    (ν : M.Pos → MerkleSalt kN) (d : M.Pos → Digest k) (o : CausalView VR.MV) (wr : M.RootWriteFn)
    (fin : (M.Tree → ℕ → Digest k) → M.Response B) :
    OracleProg (Query k kN kS L) (Out k e) (NARG.SimOutput (Query k kN kS L) (Out k e) (M.Response B)) :=
  (OracleProg.tabulate d (VR.posC x ch).dedup fun q =>
    MerkleTree.leafProg ⟨ν q, VR.colOf x ch o q⟩).bind fun ld =>
  M.defaultProg.bind fun dflt =>
  (OracleProg.tabulate (fun _ _ => fun _ => 0) M.treeList fun τ =>
    MerkleTree.heapProg ((M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree)
      (M.extD ld dflt τ)).bind fun hp =>
  (M.finalsProg ⟨σ, x⟩
    (fun q => M.writeLeaf ρ (fun p i => wr p i fun τ => hp ⟨p, ⟨i, τ⟩⟩ 1) q (n q.label))
    Λ).bind fun fs =>
  (OracleProg.tabulate (fun _ => fun _ => 0) (SPBCS.chList P t) fun c =>
    M.keyProg ⟨σ, x⟩
      (fun q => M.writeLeaf ρ (fun p i => wr p i fun τ => hp ⟨p, ⟨i, τ⟩⟩ 1) q (n q.label)) fs
      c.leaf (M.writeLeaf ρ (fun p i => wr p i fun τ => hp ⟨p, ⟨i, τ⟩⟩ 1) c.leaf c.idx.1)).bind
    fun keys =>
  .pure ⟨fin hp, SPBCS.assignOfKeys σ ρ keys⟩

/-- **The program of the simulator's reply** built from challenges, streams and a view: where
writes `wr` can be read off the view, `jointBody` with the proof at the heaps, in the format `B` by
the format bounds `hsim` of the views; otherwise the simulator fails (`none`, no assignment). -/
def jointProgOpt (hsim : VR.FormatBounds B) (x : X) (σ : FiatShamirSalt kS) (ch : Chs P t)
    (ρ : ChIdx P t → Out k e) (ν : M.Pos → MerkleSalt kN) (d : M.Pos → Digest k)
    (o : CausalView VR.MV) :
    OracleProg (Query k kN kS L) (Out k e) (NARG.SimOutput (Query k kN kS L) (Out k e) (M.Response B)) :=
  match hw : VR.writesOf x ch o with
  | none => .pure ⟨none, []⟩
  | some wr => M.jointBody Λ VR B x σ ch ρ ν d o wr fun hp =>
      some ⟨M.proofOfHeaps σ wr hp ((VR.posC x ch).map fun q => ⟨ν q, VR.colOf x ch o q⟩)
        (VR.posC x ch), M.bounded_proofOfHeaps _ _ _ _ _
          (by rw [List.length_map]; exact hsim.posC_le x ch o wr hw) hsim.nLeaves_le⟩

/-- **The program of the reply with the total encoding** (`jointRun`): `jointBody` with the proof
at the heaps encoded by `SPBCS.Internal.encodeTotal`, a proof device of the hybrid argument. It
is `jointProgOpt` within the format bounds (`jointProgOpt_eq`). -/
def jointProg (x : X) (σ : FiatShamirSalt kS) (ch : Chs P t) (ρ : ChIdx P t → Out k e)
    (ν : M.Pos → MerkleSalt kN) (d : M.Pos → Digest k) (o : CausalView VR.MV) :
    OracleProg (Query k kN kS L) (Out k e) (NARG.SimOutput (Query k kN kS L) (Out k e) (M.Response B)) :=
  (VR.writesOf x ch o).elim (.pure ⟨none, []⟩) fun wr =>
    M.jointBody Λ VR B x σ ch ρ ν d o wr fun hp =>
      SPBCS.Internal.encodeTotal M B (M.proofOfHeaps σ wr hp
        ((VR.posC x ch).map fun q => ⟨ν q, VR.colOf x ch o q⟩) (VR.posC x ch))

/-- **Within the format bounds of the views the total encoding is not used**: the program of the
reply is `jointProgOpt`. -/
theorem jointProgOpt_eq (hsim : VR.FormatBounds B) (x : X) (σ : FiatShamirSalt kS) (ch : Chs P t)
    (ρ : ChIdx P t → Out k e) (ν : M.Pos → MerkleSalt kN) (d : M.Pos → Digest k)
    (o : CausalView VR.MV) :
    M.jointProgOpt Λ VR B hsim x σ ch ρ ν d o = M.jointProg Λ VR B x σ ch ρ ν d o := by
  unfold jointProgOpt jointProg
  split
  · next hw => rw [hw]; rfl
  · next wr hw =>
    have hr : (VR.writesOf x ch o).elim (OracleProg.pure ⟨none, []⟩) (fun wr =>
        M.jointBody Λ VR B x σ ch ρ ν d o wr fun hp =>
          SPBCS.Internal.encodeTotal M B (M.proofOfHeaps σ wr hp
            ((VR.posC x ch).map fun q => ⟨ν q, VR.colOf x ch o q⟩) (VR.posC x ch))) =
        M.jointBody Λ VR B x σ ch ρ ν d o wr fun hp =>
          SPBCS.Internal.encodeTotal M B (M.proofOfHeaps σ wr hp
            ((VR.posC x ch).map fun q => ⟨ν q, VR.colOf x ch o q⟩) (VR.posC x ch)) := by
      rw [hw]
      rfl
    rw [hr]
    refine congrArg (M.jointBody Λ VR B x σ ch ρ ν d o wr) (funext fun hp => ?_)
    exact (SPBCS.Internal.encodeTotal_of_bounded _ _).symm

variable [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)]

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
theorem run_jointProg (x : X) (σ : FiatShamirSalt kS) (ch : Chs P t)
    (ρ : ChIdx P t → Out k e) (ν : M.Pos → MerkleSalt kN) (d : M.Pos → Digest k)
    (o : CausalView VR.MV) :
    (M.jointProg Λ VR B x σ ch ρ ν d o).run h =
      (VR.writesOf x ch o).elim ⟨none, []⟩ fun wr =>
      ⟨SPBCS.Internal.encodeTotal M B (M.buildProof h σ wr (M.jointLeaf VR h x ch ν d o)
          ((VR.posC x ch).map fun q => ⟨ν q, VR.colOf x ch o q⟩) (VR.posC x ch)),
        M.buildAssign h ⟨σ, x⟩ ρ wr (M.jointLeaf VR h x ch ν d o)⟩ := by
  unfold jointProg jointBody
  cases hw : VR.writesOf x ch o with
  | none => rfl
  | some wr =>
    simp only [Option.elim, OracleProg.run_bind, OracleProg.run_tabulate, OracleProg.run_pure,
      M.mem_treeList, ite_true, SPBCS.mem_chList, MerkleTree.run_heapProg, run_keyProg,
      MerkleTree.run_leafProg, run_finalsProg]
    have hld : (fun q => if q ∈ (VR.posC x ch).dedup then
        MerkleTree.leafDigest h ⟨ν q, VR.colOf x ch o q⟩ else d q) = M.jointLeaf VR h x ch ν d o := by
      funext q
      simp only [List.mem_dedup, SPBCS.jointLeaf]
    rw [hld]
    have hh : M.HeapsOf h (M.jointLeaf VR h x ch ν d o) fun τ =>
        MerkleTree.nodeDigest h ((M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree)
          (M.extD (M.jointLeaf VR h x ch ν d o) ((M.defaultProg).run h) τ) :=
      SPBCS.heapsOf_nodeDigest (fun τ j hj => by rw [SPBCS.extD, dite_eq_left hj])
        (fun τ h0 => by rw [SPBCS.extD, dite_eq_right (by omega), M.run_defaultProg h0])
    have hch : (fun q => M.writeLeaf ρ (fun p i => wr p i fun τ => MerkleTree.nodeDigest h
        ((M.comp p.label).nLeaves i τ) (M.extD (M.jointLeaf VR h x ch ν d o) ((M.defaultProg).run h)
          ⟨p, ⟨i, τ⟩⟩) 1) q (n q.label)) = M.buildChains h ρ wr (M.jointLeaf VR h x ch ν d o) :=
      funext fun q => (hh.buildLeaf_eq ρ wr q _).symm
    rw [hch, hh.buildProof_eq, M.assignOfKeys_eq_buildAssign (h := h) ⟨σ, x⟩ ρ wr
      (M.jointLeaf VR h x ch ν d o) fun c => by
        rw [buildKey, buildFinals, hh.buildLeaf_eq ρ wr c.leaf]]

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The program of the reply makes at most `2 |Pos| + t.size n + |sites|` queries.** -/
theorem length_trace_jointProg_le (x : X) (σ : FiatShamirSalt kS) (ch : Chs P t)
    (ρ : ChIdx P t → Out k e) (ν : M.Pos → MerkleSalt kN) (d : M.Pos → Digest k)
    (o : CausalView VR.MV) :
    ((M.jointProg Λ VR B x σ ch ρ ν d o).trace h).length ≤
      2 * Fintype.card M.Pos + t.size n + Fintype.card Mg.Site := by
  classical
  unfold jointProg jointBody
  cases hw : VR.writesOf x ch o with
  | none => simp
  | some wr =>
    simp only [Option.elim, OracleProg.trace_bind, List.length_append, OracleProg.trace_pure,
      List.length_nil, add_zero, OracleProg.length_trace_tabulate, MerkleTree.length_trace_leafProg,
      MerkleTree.length_trace_heapProg, M.length_trace_defaultProg, M.length_trace_keyProg,
      finalsProg, M.length_trace_finalsProgFrom]
    have h1 : ((VR.posC x ch).dedup.map fun _ => 1).sum ≤ Fintype.card M.Pos := by
      rw [List.map_const', List.sum_replicate, smul_eq_mul, mul_one]
      exact (List.nodup_dedup _).length_le_card
    have h2 : ((M.treeList.map fun τ =>
        (M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree - 1)).sum ≤ Fintype.card M.Pos := by
      rw [M.sum_map_treeList, ← M.sum_nLeaves]
      exact Finset.sum_le_sum fun τ _ => Nat.sub_le _ _
    have h3 : (if ∃ τ : M.Tree, (M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree = 0 then 1 else 0) +
        ((SPBCS.chList P t).map fun _ => 1).sum ≤ t.size n := by
      rw [List.map_const', List.sum_replicate, smul_eq_mul, mul_one]
      split_ifs with hτ
      · obtain ⟨τ, -⟩ := hτ
        have := M.length_chList_lt τ
        omega
      · simpa using SPBCS.length_chList_le (P := P) (t := t)
    have h4 := length_siteOrder_le Λ
    omega

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **Every assignment of the reply program programs an `xof` point at the digest of a queried
chain input** holding the salt and the statement (`AssignsAtKeys`). Hypothesis: `hk`, a nonzero
digest length (a changed answer at a chain input changes its key). -/
theorem assignsAtKeys_jointProg (hk : 0 < k) (x : X) (σ : FiatShamirSalt kS) (ch : Chs P t)
    (ρ : ChIdx P t → Out k e) (ν : M.Pos → MerkleSalt kN) (d : M.Pos → Digest k)
    (o : CausalView VR.MV) : M.AssignsAtKeys (M.jointProg Λ VR B x σ ch ρ ν d o) ⟨σ, x⟩ := by
  classical
  intro O qa hqa
  rw [run_jointProg] at hqa
  rcases hw : VR.writesOf x ch o with _ | wr
  · rw [hw] at hqa
    simp at hqa
  rw [hw] at hqa
  simp only [Option.elim, buildAssign, List.mem_map] at hqa
  obtain ⟨cc, hcc, rfl⟩ := hqa
  set ld := M.jointLeaf VR O x ch ν d o
  set ss : SaltedStatement kS X := ⟨σ, x⟩
  set cont : M.MContent := roundContent ss (M.buildChains O ρ wr ld) (M.buildFinals O ss ρ wr ld)
    cc.leaf (M.buildLeaf O ρ wr ld cc.leaf cc.idx.1) with hcont
  have hwf : cont.WF n (fun j => chainWF (P j)) := M.wf_buildRound _ _ _ _ _ _ cc
  refine ⟨M.senc.encode cont, cont, ?_, M.senc.decode_encode _ hwf, rfl, rfl⟩
  set Tq : Query k kN kS L := .transcript (M.senc.encode cont) with hTdef
  obtain ⟨d', hd'⟩ : ∃ d' : Digest k, d' ≠ (O Tq).digest := by
    have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    exact exists_ne _
  set O'' := Function.update O Tq ⟨d', fun _ => 0⟩ with hO''
  apply OracleProg.mem_trace_of_run_update_ne _ (b := (⟨d', fun _ => 0⟩ : Out k e))
  intro hrun''
  rw [run_jointProg, run_jointProg] at hrun''
  have h2 := congrArg NARG.SimOutput.assignments hrun''
  simp only [hw, Option.elim] at h2
  have hleaf : ∀ a b, O'' (.leaf a b) = O (.leaf a b) := fun a b => by
    simp only [hO'']
    rw [Function.update_of_ne (by simp [hTdef])]
  have hnode : ∀ a b, O'' (.node a b) = O (.node a b) := fun a b => by
    simp only [hO'']
    rw [Function.update_of_ne (by simp [hTdef])]
  have hkey := (List.map_inj_left.1 h2) cc hcc
  simp only [Assignment.mk.injEq, Query.xof.injEq] at hkey
  have hk1 := hkey.1.1
  rw [M.jointLeaf_congr VR hleaf] at hk1
  have hch := M.buildChains_congr ρ wr ld hleaf hnode
  have hfin : M.buildFinals O'' ss ρ wr ld = M.buildFinals O ss ρ wr ld := by
    unfold buildFinals
    rw [hch]
    refine finalsWith_congr_oracle fun fs s => ?_
    simp only [hO'']
    refine Function.update_of_ne (fun he => ?_) _ _
    have := M.senc.encode_injective (M.wf_buildFinal _ _ _ _ _ fs s) hwf (Query.transcript.inj he)
    simp [hcont, roundContent, finalContent] at this
  unfold buildKey key at hk1
  rw [hch, M.buildLeaf_congr hleaf hnode, hfin] at hk1
  have e2 : (O'' Tq).digest = d' := by
    rw [hO'', Function.update_self]
  exact hd' (e2.symm.trans hk1.symm)

/-- **The simulator of the spBCS compiler** (paper `prot:bcs-simulator`): on the statement `x` and
the coins, the joint simulator's view at `pub x`, the streams drawn by preimage at its challenges,
and the program `jointProgOpt` at them, against the compiler's oracle `Query → Out`. It returns a
proof in the format `B` (by the format bounds `hsim` of the views), or fails (`none`, with no
assignment) where no writes can be read off the simulated view. Simulators that may fail are
standard; real views always decode (`ViewEncoder.writesOf_obs`), so the failure is charged to the
HVZK error and moves no bound. In the quantum random-oracle model it runs through `queryEncoding`.

Running time: polynomial in the proof size. One run of the joint simulator `Sim` and of each
challenge's preimage sampler (polynomial by their own Running time paragraphs); reading the writes
and the opened columns off the view with the read-off functions of the view laws; sorting the sites
of `Λ` by rank. Oracle queries: at most `|Pos|` `leaf` queries of opened positions, at most one
`leaf` query of the default leaf, `nLeaves - 1` `node` queries per tree (at most `|Pos|` in all),
one `transcript` query per site and one per challenge; at most `2 |Pos| + t.size n + |sites|` in
all, the count `q`. This running time is argued here, not proved in Lean. -/
def niSimulator (hsim : VR.FormatBounds B) {Pub : Type} (pub : X → Pub)
    (Sim : CausalJointSimulator VR.MV Pub) (T : M.Preimages) :
    NARG.Simulator (Query k kN kS L) (Out k e) X (Option (M.BProof B))
      (SaltedCoins (FiatShamirSalt kS) (M.JointSimCoins VR Sim T)) where
  prog x a := M.jointProgOpt Λ VR B hsim x a.salt (Sim.sim (pub x) a.coins.sim).challenges
    (Sampler.preStreams T (Sim.sim (pub x) a.coins.sim).challenges a.coins.pre) a.coins.merkleSalts
    a.coins.digests (Sim.sim (pub x) a.coins.sim)
  coins_nonempty := inferInstance
  q := 2 * Fintype.card M.Pos + t.size n + Fintype.card Mg.Site
  prog_queries x a h := by
    rw [jointProgOpt_eq]
    exact M.length_trace_jointProg_le (h := h) Λ VR B x _ _ _ _ _ _

/-- **The simulator with the total encoding** (a proof device of the hybrid argument): as
`niSimulator`, at `jointProg`. It is `niSimulator` within the format bounds of the views
(`niSimulator_eq`).

Running time: that of `niSimulator`. This running time is argued here, not proved in Lean. -/
def niSimulatorTotal {Pub : Type} (pub : X → Pub) (Sim : CausalJointSimulator VR.MV Pub)
    (T : M.Preimages) :
    NARG.Simulator (Query k kN kS L) (Out k e) X (Option (M.BProof B))
      (SaltedCoins (FiatShamirSalt kS) (M.JointSimCoins VR Sim T)) where
  prog x a := M.jointProg Λ VR B x a.salt (Sim.sim (pub x) a.coins.sim).challenges
    (Sampler.preStreams T (Sim.sim (pub x) a.coins.sim).challenges a.coins.pre) a.coins.merkleSalts
    a.coins.digests (Sim.sim (pub x) a.coins.sim)
  coins_nonempty := inferInstance
  q := 2 * Fintype.card M.Pos + t.size n + Fintype.card Mg.Site
  prog_queries x a h := M.length_trace_jointProg_le (h := h) Λ VR B x _ _ _ _ _ _

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **Within the format bounds of the views the simulator is the one with the total encoding.** -/
theorem niSimulator_eq (hsim : VR.FormatBounds B) {Pub : Type} (pub : X → Pub)
    (Sim : CausalJointSimulator VR.MV Pub) (T : M.Preimages) :
    M.niSimulator Λ VR B hsim pub Sim T = M.niSimulatorTotal Λ VR B pub Sim T := by
  unfold niSimulator niSimulatorTotal
  congr 1
  funext x a
  exact M.jointProgOpt_eq Λ VR B hsim _ _ _ _ _ _ _

/-- **The simulator of the zero-knowledge games as a counted program on the quantum oracle**:
`niSimulatorTotal` run through `queryEncoding`.

Running time: that of `niSimulatorTotal`, with one encoding per query and per assignment. This
running time is argued here, not proved in Lean. -/
def niJointSimulatorProg {Pub : Type} (pub : X → Pub) (Sim : CausalJointSimulator VR.MV Pub)
    (T : M.Preimages) :
    NARG.Simulator (Bits (queryBits k kN kS L)) (XOut k e) X (M.Response B)
      (SaltedCoins (FiatShamirSalt kS) (M.JointSimCoins VR Sim T)) :=
  (M.niSimulatorTotal Λ VR B pub Sim T).encode queryEncoding

omit [∀ j i, Nonempty ((P j).Challenge i)] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The counted program's classical semantics is the simulator** `niJointSimulator`. -/
theorem toFn_niJointSimulatorProg {Pub : Type} (pub : X → Pub)
    (Sim : CausalJointSimulator VR.MV Pub) (T : M.Preimages) :
    (M.niJointSimulatorProg Λ VR B pub Sim T).toFn = M.niJointSimulator VR B pub Sim T := by
  have hrun : ∀ H x a, (M.niJointSimulatorProg Λ VR B pub Sim T).toFn.run H x a =
      (M.niJointSimulator VR B pub Sim T).run H x a := by
    intro H x a
    rw [niJointSimulatorProg, NARG.Simulator.toFn_encode_run, NARG.Simulator.toFn_run,
      decode_queryEncoding, niSimulatorTotal]
    dsimp only
    rw [run_jointProg]
    simp only [niJointSimulator, jointRun]
    cases VR.writesOf x (Sim.sim (pub x) a.coins.sim).challenges (Sim.sim (pub x) a.coins.sim) <;> rfl
  unfold NARG.Simulator.toFn
  congr 1
  funext H x a
  exact hrun H x a

end

section

variable {Mg : Merges t} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}
  (M : SPBCS Mg P X k kN kS L e) [∀ j i, Nonempty ((P j).Challenge i)]

/-- **The format bounds of the simulated views follow from those of the query phases**: where
writes can be read off a view, the chains built from them have a write at every prover round, on
which the opened positions are those of the query phase (`ViewEncoder.pos_eq`). -/
theorem ViewEncoder.formatBounds (E : (j : ι) → (M.comp j).Encoder) {V : X → FullTr P t → Bool}
    {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E Qs) {B : ℕ} (hb : M.FormatBounds Qs B B) :
    VE.toViewRead.FormatBounds B where
  posC_le x ch o wr _ := by
    have h : Query k kN kS L → Out k e := fun _ => ⟨fun _ => 0, fun _ => 0⟩
    show (VE.posC x ch).length ≤ B
    rw [← VE.pos_eq x _ ch (M.writesAll_buildChains h (fun _ => h (.node (fun _ => 0) fun _ => 0)) wr
      (fun _ => fun _ => 0))]
    exact hb.pos_le x _ ch
  nLeaves_le := hb.nLeaves_le

variable [∀ j i, Fintype ((M.comp j).MessageWrite i)] (Λ : SiteLayout Mg)

/-- **Bridge to the hybrid argument**: the simulator run through `queryEncoding` is the simulator
of the zero-knowledge games `niJointSimulatorProg`, within the format bounds of the views. -/
theorem encode_niSimulator (E : (j : ι) → (M.comp j).Encoder) {V : X → FullTr P t → Bool}
    {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E Qs) {B : ℕ} (hb : M.FormatBounds Qs B B)
    {Pub : Type} (pub : X → Pub) (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages) :
    (M.niSimulator Λ VE.toViewRead B (ViewEncoder.formatBounds M E VE hb) pub Sim T).encode
      queryEncoding = M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T := by
  rw [niSimulator_eq]
  rfl

end

end GordieHowe.SPBCS
