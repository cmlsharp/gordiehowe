-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Encoding
public import GordieHowe.SPBCS.ComponentModel
public import GordieHowe.Model.IOP.CausalLeaves
public import GordieHowe.Model.QROM.Lifting
public import GordieHowe.Model.QROM.Expansion

@[expose] public section

/-!
# The spBCS compiler: the compiler on a series–parallel term with merges

The spBCS compiler (paper `prot:generalized-bcs`) on a series–parallel term `t` with merges
`Mg` (`GordieHowe/SPBCS/Merges.lean`): every leaf has its component's hash chain (`ComponentModel`,
`GordieHowe/SPBCS/ComponentModel.lean`), writes and Merkle trees, every stream point carries the
Fiat–Shamir salt, and every chain input holds its observer's view (`GordieHowe/SPBCS/Encoding.lean`):
the full chains of the leaves it reads in full and the final digests of the branches hidden from
it.

* `GordieHowe.SPBCS Mg P X k kN kS L e`: a component model for every component (`comp`), the
  Merkle opening format (`opening`, `GordieHowe/SPBCS/Merkle/Opening.lean`: the authentication
  paths of paper `prot:generalized-bcs` or the compressed multiproofs of the C++; every guarantee
  holds for every format), Fiat–Shamir salts of `kS` bytes, and the encoding `senc` of the chain
  inputs with merges.
* `NIProof`: the salt, the writes of every leaf, the opened leaves and the path digests of every
  tree, in the opening format. `IOPQueries V x`: the query phase of the composite verifier `V`
  and its laws. `gIdx`, `chOrder`: the global round of a challenge (round `r` of leaf `p` is global
  round `p.off + r`) and the order of the challenges by it.
* `roundContent`, `finalContent`: the content of a challenge round's chain input and of a
  branch's final input, from chains `chs` of all leaves and final digests `fs` of all branches.
* `finalStep`, `finalsWith chs`: the final digest of a branch is the digest of its final input,
  which holds the final digests of the branches hidden from its sink. These are fewer
  (`Merges.hiders_sink_ssubset`), so iterating `finalStep` as many times as there are branches
  gives the solution `finalsWith chs` of `fs s = finalStep chs fs s` (`finalsWith_eq`), the only
  one (`eq_finalsWith`).
* `chains`: the chains of all leaves (the causal fixpoint `SPTerm.solve`): a leaf's chain is its
  component's chain for the keys of its chain inputs, from the chains of the leaves before it and
  the final digests computed from them; `chains_eq` states it at the final chains and digests
  (`finals`).
* `chal`, `chV`: the challenges; `Accepts`: the compiled verifier.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm

variable {ι : Type} {k kN kS L e : ℕ} {t : SPTerm ι}

/-- **The spBCS compiler on a term with merges** (module docstring): a component model per
component, the Merkle opening format, and the encoding of the chain inputs with merges, with
salts of `kS` bytes. -/
structure _root_.GordieHowe.SPBCS (Mg : Merges t) {n : ι → ℕ} (P : (j : ι) → ProtocolSpec (n j))
    [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] (X : Type)
    (k kN kS L e : ℕ) where
  /-- The data of each component. -/
  comp : (j : ι) → ComponentModel (P j) k kN L e
  /-- How a proof opens the queried leaves of a tree. -/
  opening : MerkleOpening k kN kS L e
  /-- The encoding of the chain inputs with merges. -/
  senc : MergeEncoding k L Mg n (SaltedStatement kS X) (fun j => (comp j).W)
    (fun j => (comp j).roots) (fun j => chainWF (P j))

/-! ### Chains, positions, proofs and the query phase -/

section Data

variable {Mg : Merges t} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}
  (M : SPBCS Mg P X k kN kS L e)

/-- The items of leaf `p`'s chain. -/
abbrev Items (p : t.Leaf) : Type := List (Item k (M.comp p.label).W)

/-- **The causal context of chains at leaf `p`**: a chain for every leaf sequenced before `p`. -/
abbrev Ctx (p : t.Leaf) : Type := (q : {q : t.Leaf // q.Before p}) → M.Items q.1

/-- The chains of a causal context on all leaves, empty at the leaves not before `p`. -/
def chainsOf {p : t.Leaf} (ctx : M.Ctx p) (q : t.Leaf) : M.Items q :=
  if h : q.Before p then ctx ⟨q, h⟩ else []

theorem chainsOf_of_before {p q : t.Leaf} (ctx : M.Ctx p) (hq : q.Before p) :
    M.chainsOf ctx q = ctx ⟨q, hq⟩ :=
  dite_eq_left hq

theorem chainsOf_of_not_before {p q : t.Leaf} (ctx : M.Ctx p) (hq : ¬ q.Before p) :
    M.chainsOf ctx q = [] :=
  dite_eq_right hq

/-- The writes of every prover round of every leaf. -/
abbrev Writes : Type := (p : t.Leaf) → (i : (P p.label).MessageIdx) → (M.comp p.label).MessageWrite i

variable (h : Query k kN kS L → Out k e) (x : X) (σ : FiatShamirSalt kS)

/-! ### Positions, proofs and the verifier -/

/-- **A Merkle tree of the composite**: a leaf and one of its component's trees. -/
structure Tree where
  /-- The leaf. -/
  leaf : t.Leaf
  /-- The tree of the leaf's component. -/
  tree : TreeIdx (P leaf.label) (M.comp leaf.label).nTrees

/-- **A query position of the composite**: a leaf and one of its component's positions. -/
structure Pos where
  /-- The leaf. -/
  leaf : t.Leaf
  /-- The position in the leaf's component. -/
  pos : Position (P leaf.label) (M.comp leaf.label).nTrees (M.comp leaf.label).nLeaves

/-- A tree of the composite is a dependent pair of a leaf and a tree of its component. -/
def Tree.equivSigma : M.Tree ≃ Σ p : t.Leaf, TreeIdx (P p.label) (M.comp p.label).nTrees where
  toFun τ := ⟨τ.leaf, τ.tree⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A position of the composite is a dependent pair of a leaf and a position of its component. -/
def Pos.equivSigma :
    M.Pos ≃ Σ p : t.Leaf, Position (P p.label) (M.comp p.label).nTrees (M.comp p.label).nLeaves where
  toFun q := ⟨q.leaf, q.pos⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : DecidableEq M.Tree := (Tree.equivSigma M).decidableEq

instance : DecidableEq M.Pos := (Pos.equivSigma M).decidableEq

/-- The tree of a position. -/
def Pos.treeOf {M : SPBCS Mg P X k kN kS L e} (q : M.Pos) : M.Tree := ⟨q.leaf, q.pos.treeIdx⟩

/-- **A non-interactive proof** of the composite: the salt, the writes of every leaf, the opened
leaves in the order of the queried positions, and the path digests of every tree in the opening
format `opening`. -/
structure NIProof where
  /-- The Fiat–Shamir salt. -/
  salt : FiatShamirSalt kS
  /-- The writes of every leaf. -/
  writes : M.Writes
  /-- The opened leaves. -/
  leaves : List (MerkleLeaf kN L)
  /-- The path digests of each tree. -/
  paths : (τ : M.Tree) → List (Digest k)

/-- The Merkle views of every tree of every leaf. -/
abbrev Views : Type := (p : t.Leaf) → (i : (P p.label).MessageIdx) →
  (τ : Fin ((M.comp p.label).nTrees i)) → MerkleView k kN L ((M.comp p.label).nLeaves i τ)

/-- **Every leaf's chain has a write at every prover round.** -/
def WritesAll (chs : (p : t.Leaf) → M.Items p) : Prop :=
  ∀ (p : t.Leaf) (i : (P p.label).MessageIdx), ∃ w, (chs p)[i.1.1]? = some (.write ⟨i, w⟩)

/-- **The composite transcript's prover messages are read from the chains' writes** and the
views `vw`. -/
def MessagesFrom (chs : (p : t.Leaf) → M.Items p) (vw : M.Views) (tr : FullTr P t) : Prop :=
  ∀ (p : t.Leaf) (i : (P p.label).MessageIdx) (w : (M.comp p.label).MessageWrite i),
    (chs p)[i.1.1]? = some (.write ⟨i, w⟩) → tr p i.1 = (M.comp p.label).msg i w (vw p i)

/-- **The leaves at the positions `ps` in the views `vw` are `ans`**, in order. -/
def OpenedAs (vw : M.Views) (ps : List M.Pos) (ans : List (MerkleLeaf kN L)) : Prop :=
  List.Forall₂ (fun q a => (vw q.leaf q.pos.msg q.pos.tree).leaves q.pos.leaf = some a) ps ans

variable {M} in
/-- **The composite transcript's challenges are `ch`.** -/
def ChallengesAre (tr : FullTr P t) (ch : Chs P t) : Prop := tr.challenges = ch

/-- **The query phase of the composite verifier `V` on the statement `x`**: the queried positions
`pos` (distinct) and the decision `verdict` read from the chains and the challenges, with the laws
that `V` reads the prover messages only at those positions. -/
structure IOPQueries {StmtIn : Type} (V : StmtIn → FullTr P t → Bool) (x : StmtIn) where
  /-- The queried positions. -/
  pos : ((p : t.Leaf) → M.Items p) → Chs P t → List M.Pos
  /-- The decision on the opened leaves. -/
  verdict : ((p : t.Leaf) → M.Items p) → Chs P t → List (MerkleLeaf kN L) → Bool
  pos_nodup : ∀ chs ch, (pos chs ch).Nodup
  verdict_of_accept : ∀ chs ch (vw : M.Views) (tr : FullTr P t) ans, M.WritesAll chs →
    M.MessagesFrom chs vw tr → ChallengesAre tr ch → M.OpenedAs vw (pos chs ch) ans →
    V x tr = true → verdict chs ch ans = true
  accept_of_verdict : ∀ chs ch (vw : M.Views) (tr : FullTr P t) ans,
    M.MessagesFrom chs vw tr → ChallengesAre tr ch → M.OpenedAs vw (pos chs ch) ans →
    verdict chs ch ans = true → V x tr = true

/-- The trees of the positions `ps`, each once. -/
def trees (ps : List M.Pos) : List M.Tree := (ps.map Pos.treeOf).dedup

/-- The opened leaves of tree `τ`: the leaf index of each position of `ps` in `τ` with the leaf
paired with it in `as`, in the order of `ps`. -/
def openedIn (τ : M.Tree) (ps : List M.Pos) (as : List (MerkleLeaf kN L)) :
    List (ℕ × MerkleLeaf kN L) :=
  (ps.zip as).filterMap fun pa => if pa.1.treeOf = τ then some (pa.1.pos.leaf.1, pa.2) else none

/-- The leaf indices opened in a tree lie below its leaf count. -/
theorem lt_of_mem_openedIn {τ : M.Tree} {ps : List M.Pos} {as : List (MerkleLeaf kN L)} {j : ℕ}
    {a : MerkleLeaf kN L} (hm : (j, a) ∈ M.openedIn τ ps as) :
    j < (M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree := by
  obtain ⟨⟨q, a'⟩, -, hq⟩ := List.mem_filterMap.1 hm
  dsimp only at hq
  split_ifs at hq with hτ
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some_inj.1 hq)
  subst hτ
  exact q.pos.leaf.2

/-- A tree has at most as many opened leaves as there are leaves. -/
theorem length_openedIn_le (τ : M.Tree) (ps : List M.Pos) (as : List (MerkleLeaf kN L)) :
    (M.openedIn τ ps as).length ≤ as.length :=
  (List.length_filterMap_le _ _).trans (by rw [List.length_zip]; exact min_le_right _ _)

open Classical in
/-- The opened leaves of the trees of the positions `ps`, one per position. -/
theorem sum_length_openedIn {ps : List M.Pos} {as : List (MerkleLeaf kN L)}
    (hl : ps.length = as.length) :
    ((M.trees ps).map fun τ => (M.openedIn τ ps as).length).sum = ps.length := by
  have hfst : (ps.zip as).map (Pos.treeOf ∘ Prod.fst) = ps.map Pos.treeOf := by
    rw [← List.map_map, List.map_fst_zip hl.le]
  have hcount : ∀ τ, (M.openedIn τ ps as).length = (ps.map Pos.treeOf).count τ := by
    intro τ
    rw [← hfst, List.count, List.countP_map, openedIn, List.length_filterMap_eq_countP]
    congr 1
    funext pa
    by_cases hτ : pa.1.treeOf = τ <;> simp [hτ]
  simp only [hcount, trees]
  rw [List.sum_map_count_dedup_eq_length, List.length_map]

/-- The opened leaves of a tree among positions whose leaves are `f` of the position. -/
theorem openedIn_map (f : M.Pos → MerkleLeaf kN L) (τ : M.Tree) :
    ∀ ps : List M.Pos, M.openedIn τ ps (ps.map f) =
      (ps.filter fun q => decide (q.treeOf = τ)).map fun q => (q.pos.leaf.1, f q)
  | [] => rfl
  | q :: ps => by
    have ih := openedIn_map f τ ps
    unfold openedIn at ih ⊢
    rw [List.map_cons, List.zip_cons_cons, List.filterMap_cons, ih]
    by_cases hq : q.treeOf = τ
    · simp [hq]
    · simp [hq]

theorem mem_trees {ps : List M.Pos} {q : M.Pos} (hq : q ∈ ps) : q.treeOf ∈ M.trees ps :=
  List.mem_dedup.2 (List.mem_map.2 ⟨q, hq, rfl⟩)

theorem mem_openedIn {ps : List M.Pos} {as : List (MerkleLeaf kN L)} {q : M.Pos}
    {a : MerkleLeaf kN L} (hqa : (q, a) ∈ ps.zip as) :
    (q.pos.leaf.1, a) ∈ M.openedIn q.treeOf ps as :=
  List.mem_filterMap.2 ⟨(q, a), hqa, by simp⟩

/-- Two positions of one tree with the same leaf index are equal. -/
theorem Pos.eq_of_treeOf_eq {τ : M.Tree} {q q' : M.Pos} (hq : q.treeOf = τ) (hq' : q'.treeOf = τ)
    (hj : q.pos.leaf.1 = q'.pos.leaf.1) : q = q' := by
  obtain ⟨p, ⟨i, t₀, j⟩⟩ := q
  obtain ⟨p', ⟨i', t₀', j'⟩⟩ := q'
  have he : (⟨p, ⟨i, t₀⟩⟩ : M.Tree) = ⟨p', ⟨i', t₀'⟩⟩ := hq.trans hq'.symm
  obtain ⟨rfl, he⟩ := Tree.mk.inj he
  obtain ⟨rfl, he⟩ := TreeIdx.mk.inj (eq_of_heq he)
  obtain rfl := eq_of_heq he
  obtain rfl : j = j' := Fin.ext hj
  rfl

variable {M}

/-- The check of tree `τ`'s opening in `π` (`MerkleFormat.Check`) against its root in its round's
write, at the opened leaves of `τ` among the positions `ps`. -/
def checkTree (π : M.NIProof) (ps : List M.Pos) (τ : M.Tree) : Prop :=
  M.opening.Check h ((M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree)
    ((M.comp τ.leaf.label).rootOf τ.tree.msg (π.writes τ.leaf τ.tree.msg) τ.tree.tree)
    ((M.openedIn τ ps π.leaves).map Prod.fst) ((M.openedIn τ ps π.leaves).map Prod.snd)
    (π.paths τ)

/-- **The check of a tree's opening is decided** (`MerkleFormat.Check`). -/
instance (π : M.NIProof) (ps : List M.Pos) (τ : M.Tree) : Decidable (M.checkTree h π ps τ) :=
  inferInstanceAs (Decidable (M.opening.Check h _ _ _ _ _))

/-- **The challenges in global round order**, as a list: the challenge rounds among the slots. -/
def chList (P : (j : ι) → ProtocolSpec (n j)) (t : SPTerm ι) : List (ChIdx P t) :=
  (t.slots n).filterMap fun s =>
    if hd : (P s.leaf.label).dir s.round = .P_to_V then none
    else some ⟨s.leaf, (P s.leaf.label).chIdx s.round hd⟩

omit [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] in
theorem nodup_chList : (chList P t).Nodup := by
  have key : ∀ (s : SPTerm.Slot n t) (c : ChIdx P t),
      c ∈ (if hd : (P s.leaf.label).dir s.round = .P_to_V then none
        else some (⟨s.leaf, (P s.leaf.label).chIdx s.round hd⟩ : ChIdx P t)) →
      s = ⟨c.leaf, c.idx.1⟩ := by
    intro s c hc
    rw [Option.mem_def] at hc
    split_ifs at hc with hd
    obtain rfl := Option.some_inj.1 hc
    rfl
  exact (SPTerm.nodup_slots n t).filterMap fun s s' c hc hc' => (key s c hc).trans (key s' c hc').symm

omit [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] in
theorem mem_chList (c : ChIdx P t) : c ∈ chList P t := by
  have hmem : (⟨c.leaf, c.idx.1⟩ : SPTerm.Slot n t) ∈ t.slots n :=
    List.mem_of_getElem? (slots_getElem n c.leaf c.idx.1)
  refine List.mem_filterMap.2 ⟨_, hmem, ?_⟩
  have hd : ¬ (P c.leaf.label).dir c.idx.1 = .P_to_V := by
    have := c.idx.2
    intro h
    rw [h] at this
    exact absurd this (by decide)
  simp only [hd, ↓reduceDIte]
  rfl

/-! ### The global order of the challenges -/

/-- The global round of a challenge: round `c.idx` of its leaf, after the rounds of the leaves
before it in term order. -/
def gIdx (c : ChIdx P t) : ℕ := c.leaf.off n + c.idx.1.1

omit [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] in
/-- Distinct challenges have distinct global rounds. -/
theorem gIdx_injective : Function.Injective (gIdx (P := P) (t := t)) := fun c c' he => by
  have h1 := slots_getElem n c.leaf c.idx.1
  have h2 := slots_getElem n c'.leaf c'.idx.1
  rw [show c.leaf.off n + (c.idx.1 : ℕ) = c'.leaf.off n + (c'.idx.1 : ℕ) from he, h2] at h1
  obtain ⟨hl, hr⟩ := Slot.mk.inj (Option.some_inj.1 h1)
  obtain ⟨p, i⟩ := c
  obtain ⟨p', i'⟩ := c'
  dsimp only at hl hr
  subst hl
  have : i = i' := Subtype.ext (eq_of_heq hr).symm
  rw [this]

omit [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] in
theorem gIdx_lt_size (c : ChIdx P t) : gIdx c < t.size n := by
  have := Leaf.off_add_le n c.leaf
  have := c.idx.1.2
  unfold gIdx
  omega

/-- **The challenges in global round order** (not an instance, so that equality of challenges is
decided by its own instance alone). -/
abbrev chOrder (P : (j : ι) → ProtocolSpec (n j)) (t : SPTerm ι) : LinearOrder (ChIdx P t) :=
  LinearOrder.lift' gIdx gIdx_injective

end Data

section

variable {Mg : Merges t} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}
  (M : SPBCS Mg P X k kN kS L e)

/-- The content of a chain input of `M`. -/
abbrev MContent : Type := Content Mg k (fun j => (M.comp j).W) (SaltedStatement kS X)

/-- Chains of all leaves. -/
abbrev Chains : Type := (q : t.Leaf) → M.Items q

variable {M} in
/-- **The content of the chain input of leaf `p` at its own items `l`**: its view of the chains
`chs` and the final digests `fs`. -/
def roundContent (ss : SaltedStatement kS X) (chs : M.Chains) (fs : Mg.Site → Digest k)
    (p : t.Leaf) (l : M.Items p) : M.MContent :=
  .round ss p ((Merges.Obs.leaf p : Mg.Obs).viewChains (W := fun j => (M.comp j).W) chs)
    ((Merges.Obs.leaf p : Mg.Obs).viewDs fs) l

variable {M} in
/-- **The content of the final input of the branch of site `s`**: its sink's view of the chains
`chs` and the final digests `fs`. -/
def finalContent (ss : SaltedStatement kS X) (chs : M.Chains) (fs : Mg.Site → Digest k)
    (s : Mg.Site) : M.MContent :=
  .final ss s ((Merges.Obs.sink s : Mg.Obs).viewChains (W := fun j => (M.comp j).W) chs)
    ((Merges.Obs.sink s : Mg.Obs).viewDs fs)

variable (h : Query k kN kS L → Out k e) (ss : SaltedStatement kS X)

/-- **The key of a chain input of leaf `p`**: the digest of `h` at its encoding. -/
def key (chs : M.Chains) (fs : Mg.Site → Digest k) (p : t.Leaf) (l : M.Items p) : Digest k :=
  (h (.transcript (M.senc.encode (roundContent ss chs fs p l)))).digest

/-- **The final digest of a branch** at the chains `chs` and the final digests `fs`: the digest
of `h` at its final input. -/
def finalStep (chs : M.Chains) (fs : Mg.Site → Digest k) (s : Mg.Site) : Digest k :=
  (h (.transcript (M.senc.encode (finalContent ss chs fs s)))).digest

/-- **The final digests at the chains `chs`** (module docstring): `finalStep` iterated once per
branch from `0`. -/
def finalsWith (chs : M.Chains) : Mg.Site → Digest k :=
  (M.finalStep h ss chs)^[Fintype.card Mg.Site] 0

/-! ### What a key and a final digest read -/

section Reads

variable {M h ss}

/-- **A key reads the chains only at the leaves its leaf reads in full and the final digests only
at the branches hidden from its leaf.** -/
theorem key_congr {chs chs' : M.Chains} {fs fs' : Mg.Site → Digest k} {p : t.Leaf}
    (hc : ∀ q, (Merges.Obs.leaf p : Mg.Obs).Visible q → chs q = chs' q)
    (hf : ∀ s, Mg.Hides s (.leaf p) → fs s = fs' s) : M.key h ss chs fs p = M.key h ss chs' fs' p :=
  funext fun l => by
    unfold key roundContent
    rw [Merges.Obs.viewChains_congr _ hc, Merges.Obs.viewDs_congr _ hf]

/-- **A final digest reads the chains only at the leaves its sink reads in full and the final
digests only at the branches hidden from its sink.** -/
theorem finalStep_congr {chs chs' : M.Chains} {fs fs' : Mg.Site → Digest k} {s : Mg.Site}
    (hc : ∀ q, (Merges.Obs.sink s : Mg.Obs).Visible q → chs q = chs' q)
    (hf : ∀ s', Mg.Hides s' (.sink s) → fs s' = fs' s') :
    M.finalStep h ss chs fs s = M.finalStep h ss chs' fs' s := by
  unfold finalStep finalContent
  rw [Merges.Obs.viewChains_congr _ hc, Merges.Obs.viewDs_congr _ hf]

/-- The number of branches hidden from a sink is below the number of branches. -/
theorem card_hiders_sink_lt (s : Mg.Site) :
    (Merges.hiders (M := Mg) (.sink s)).card < Fintype.card Mg.Site :=
  Finset.card_lt_univ_of_notMem (Merges.mem_hiders.not.2 (Merges.not_hides_sink_self s))

/-- **The iterates of `finalStep` agree at a branch after more steps than the branches hidden
from its sink.** -/
theorem iterate_finalStep_eq (chs : M.Chains) : ∀ (c : ℕ) (s : Mg.Site),
    (Merges.hiders (M := Mg) (.sink s)).card = c → ∀ m m', c < m → c < m' →
    (M.finalStep h ss chs)^[m] 0 s = (M.finalStep h ss chs)^[m'] 0 s := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro s hc m m' hm hm'
    obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
    obtain ⟨a', rfl⟩ : ∃ a', m' = a' + 1 := ⟨m' - 1, by omega⟩
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine finalStep_congr (fun _ _ => rfl) fun s' hs' => ?_
    have hlt := Finset.card_lt_card (Merges.hiders_sink_ssubset hs')
    rw [hc] at hlt
    exact ih _ hlt s' rfl a a' (by omega) (by omega)

/-- **The final digests solve their equation**: each is the digest of its final input at the
final digests. -/
theorem finalsWith_eq (chs : M.Chains) (s : Mg.Site) :
    M.finalsWith h ss chs s = M.finalStep h ss chs (M.finalsWith h ss chs) s := by
  unfold finalsWith
  rw [← Function.iterate_succ_apply' (M.finalStep h ss chs)]
  exact iterate_finalStep_eq chs _ s rfl _ _ (card_hiders_sink_lt s) (by
    have := card_hiders_sink_lt s
    omega)

/-- **The final digests are the only solution of their equation.** -/
theorem eq_finalsWith {chs : M.Chains} {fs : Mg.Site → Digest k}
    (hfs : ∀ s, fs s = M.finalStep h ss chs fs s) : fs = M.finalsWith h ss chs := by
  funext s
  induction hc : (Merges.hiders (M := Mg) (.sink s)).card using Nat.strong_induction_on
    generalizing s with
  | _ c ih =>
    rw [hfs s, finalsWith_eq chs s]
    refine finalStep_congr (fun _ _ => rfl) fun s' hs' => ?_
    have hlt := Finset.card_lt_card (Merges.hiders_sink_ssubset hs')
    rw [hc] at hlt
    exact ih _ hlt s' rfl

/-- **A round content reads the chains only at the leaves its leaf reads in full and the final
digests only at the branches hidden from it.** -/
theorem roundContent_congr {chs chs' : M.Chains} {fs fs' : Mg.Site → Digest k} {p : t.Leaf}
    (hc : ∀ q, (Merges.Obs.leaf p : Mg.Obs).Visible q → chs q = chs' q)
    (hf : ∀ s, Mg.Hides s (.leaf p) → fs s = fs' s) (l : M.Items p) :
    roundContent ss chs fs p l = roundContent ss chs' fs' p l := by
  unfold roundContent
  rw [Merges.Obs.viewChains_congr _ hc, Merges.Obs.viewDs_congr _ hf]

/-- **A final content reads the chains only at the leaves its sink reads in full and the final
digests only at the branches hidden from its sink.** -/
theorem finalContent_congr {chs chs' : M.Chains} {fs fs' : Mg.Site → Digest k} {s : Mg.Site}
    (hc : ∀ q, (Merges.Obs.sink s : Mg.Obs).Visible q → chs q = chs' q)
    (hf : ∀ s', Mg.Hides s' (.sink s) → fs s' = fs' s') :
    finalContent ss chs fs s = finalContent ss chs' fs' s := by
  unfold finalContent
  rw [Merges.Obs.viewChains_congr _ hc, Merges.Obs.viewDs_congr _ hf]

/-- **Two oracles give the same final digests at the branches hidden from `o`** when they agree
at the final input of each such branch, built with the final digests of the second. -/
theorem finalsWith_congr_oracle_of_hides {h h' : Query k kN kS L → Out k e} {chs : M.Chains}
    {o : Mg.Obs}
    (hag : ∀ s, Mg.Hides s o →
      h (.transcript (M.senc.encode (finalContent ss chs (M.finalsWith h' ss chs) s))) =
        h' (.transcript (M.senc.encode (finalContent ss chs (M.finalsWith h' ss chs) s)))) :
    ∀ s, Mg.Hides s o → M.finalsWith h ss chs s = M.finalsWith h' ss chs s := by
  intro s hs
  induction hc : (Merges.hiders (M := Mg) (.sink s)).card using Nat.strong_induction_on
    generalizing s with
  | _ c ih =>
    rw [finalsWith_eq chs s, finalsWith_eq (h := h') chs s]
    unfold finalStep
    rw [finalContent_congr (fs' := M.finalsWith h' ss chs) (fun _ _ => rfl) fun s' hs' => by
      have hlt := Finset.card_lt_card (Merges.hiders_sink_ssubset hs')
      rw [hc] at hlt
      exact ih _ hlt s' (Merges.hides_of_hides_sink hs hs') rfl]
    rw [hag s hs]

/-- **Two oracles give the same final digests** when they agree at the final input of every
branch, built with the final digests of the second. -/
theorem finalsWith_eq_of_agree {h h' : Query k kN kS L → Out k e} {chs : M.Chains}
    (hag : ∀ s,
      h (.transcript (M.senc.encode (finalContent ss chs (M.finalsWith h' ss chs) s))) =
        h' (.transcript (M.senc.encode (finalContent ss chs (M.finalsWith h' ss chs) s)))) :
    M.finalsWith h ss chs = M.finalsWith h' ss chs :=
  (eq_finalsWith (h := h) fun s => by
    rw [finalsWith_eq (h := h') chs s]
    unfold finalStep
    rw [hag s]).symm

/-- **The final digests read the oracle only at final inputs.** -/
theorem finalsWith_congr_oracle {h₁ h₂ : Query k kN kS L → Out k e} {chs : M.Chains}
    (htr : ∀ fs s, h₁ (.transcript (M.senc.encode (finalContent ss chs fs s))) =
      h₂ (.transcript (M.senc.encode (finalContent ss chs fs s)))) :
    M.finalsWith h₁ ss chs = M.finalsWith h₂ ss chs :=
  finalsWith_eq_of_agree fun s => htr _ s

/-- **A final digest reads the chains only in the past of its sink.** -/
theorem finalsWith_congr {chs chs' : M.Chains} {s : Mg.Site}
    (hc : ∀ q, (Merges.Obs.sink s : Mg.Obs).Sees q → chs q = chs' q) :
    M.finalsWith h ss chs s = M.finalsWith h ss chs' s := by
  induction hcard : (Merges.hiders (M := Mg) (.sink s)).card using Nat.strong_induction_on
    generalizing s with
  | _ c ih =>
    rw [finalsWith_eq chs s, finalsWith_eq chs' s]
    refine finalStep_congr (fun q hq => hc q hq.1) fun s' hs' => ?_
    have hlt := Finset.card_lt_card (Merges.hiders_sink_ssubset hs')
    rw [hcard] at hlt
    exact ih _ hlt (fun q hq => hc q (Merges.sees_of_sees_sink hs' hq)) rfl

/-- **The final digests of the branches hidden from a leaf read only the chains before it.** -/
theorem finalsWith_congr_of_hides {chs chs' : M.Chains} {p : t.Leaf}
    (hc : ∀ q, q.Before p → chs q = chs' q) {s : Mg.Site} (hs : Mg.Hides s (.leaf p)) :
    M.finalsWith h ss chs s = M.finalsWith h ss chs' s :=
  finalsWith_congr fun q hq => hc q (Merges.sees_of_sees_sink hs hq)

end Reads

/-! ### The chains of a proof -/

/-- **A leaf's chain from the chains `chs` of the leaves before it**: its component's chain for the
keys of its chain inputs at `chs` and the final digests computed from `chs`. -/
def leafChain (wr : M.Writes) (p : t.Leaf) (chs : M.Chains) : M.Items p :=
  (M.comp p.label).chainWith (wr p) (M.key h ss chs (M.finalsWith h ss chs) p) ss.salt h
    (n p.label) le_rfl

/-- **The chains of all leaves** (the causal fixpoint, module docstring). -/
def chains (wr : M.Writes) : M.Chains :=
  SPTerm.solve fun p ctx => M.leafChain h ss wr p (M.chainsOf ctx)

/-- **The final digests of a proof**: those at its chains. -/
def finals (wr : M.Writes) : Mg.Site → Digest k := M.finalsWith h ss (M.chains h ss wr)

section Chains

variable {M h ss}

/-- **A leaf's chain reads only the chains before it.** -/
theorem leafChain_congr (wr : M.Writes) {p : t.Leaf} {chs chs' : M.Chains}
    (hc : ∀ q, q.Before p → chs q = chs' q) :
    M.leafChain h ss wr p chs = M.leafChain h ss wr p chs' := by
  unfold leafChain
  rw [key_congr (fun q hq => hc q hq.1) fun s hs => finalsWith_congr_of_hides hc hs]

/-- **The defining equation of the chains**: a leaf's chain is its component's chain for the keys
at the chains and final digests of the proof. -/
theorem chains_eq (wr : M.Writes) (p : t.Leaf) :
    M.chains h ss wr p = M.leafChain h ss wr p (M.chains h ss wr) := by
  rw [chains, SPTerm.solve_eq]
  refine leafChain_congr wr fun q hq => ?_
  rw [SPBCS.chainsOf_of_before _ _ hq]

theorem chains_eq_chainWith (wr : M.Writes) (p : t.Leaf) :
    M.chains h ss wr p = (M.comp p.label).chainWith (wr p)
      (M.key h ss (M.chains h ss wr) (M.finals h ss wr) p) ss.salt h (n p.label) le_rfl :=
  chains_eq wr p

/-- **The final digests of a proof solve their equation.** -/
theorem finals_eq (wr : M.Writes) (s : Mg.Site) :
    M.finals h ss wr s = M.finalStep h ss (M.chains h ss wr) (M.finals h ss wr) s :=
  finalsWith_eq _ s

theorem length_chains (wr : M.Writes) (p : t.Leaf) : (M.chains h ss wr p).length = n p.label := by
  rw [chains_eq_chainWith]
  exact ComponentModel.length_chainWith _ _ _ _ _ _ _

theorem chainWF_chains (wr : M.Writes) (p : t.Leaf) : chainWF (P p.label) (M.chains h ss wr p) := by
  rw [chains_eq_chainWith]
  exact ComponentModel.chainWF_chainWith _ _ _ _ _ _ _

/-- **The item of a prover round of a leaf's chain is the leaf's write.** -/
theorem chains_getElem?_message (wr : M.Writes) (p : t.Leaf) (i : (P p.label).MessageIdx) :
    (M.chains h ss wr p)[i.1.1]? = some (.write ⟨i, wr p i⟩) := by
  rw [chains_eq_chainWith, ComponentModel.chainWith_getElem? _ _ _ _ _ _ _ i.1 i.1.2]
  unfold ComponentModel.itemWith
  simp only [i.2, ↓reduceDIte]
  rfl

/-- **A leaf's chain reads only the writes of the leaf and of the leaves before it.** -/
theorem chains_congr {wr wr' : M.Writes} (p : t.Leaf)
    (hw : ∀ q, q.Before p ∨ q = p → wr q = wr' q) : M.chains h ss wr p = M.chains h ss wr' p := by
  induction p using (wellFounded_before t).induction with
  | _ p ih =>
    rw [chains_eq, chains_eq, leafChain_congr wr (chs' := M.chains h ss wr') fun q hq =>
      ih q hq fun r hr => hw r (Or.inl (hr.elim (·.trans hq) (· ▸ hq)))]
    unfold leafChain
    rw [hw p (Or.inr rfl)]

/-- **The final digest of a branch reads only the writes in the past of its sink.** -/
theorem finals_congr {wr wr' : M.Writes} {s : Mg.Site}
    (hw : ∀ q, (Merges.Obs.sink s : Mg.Obs).Sees q → wr q = wr' q) :
    M.finals h ss wr s = M.finals h ss wr' s := by
  refine finalsWith_congr fun q hq => chains_congr q fun r hr => hw r ?_
  rcases hr with hr | rfl
  · exact Merges.sees_sink_of_before hq hr
  · exact hq

end Chains

/-! ### Challenges and the verifier -/

/-- **The challenge `c`**, sampled from the stream at the key of its chain input and the
Fiat–Shamir salt, or `none` when the sampler rejects. -/
def chal (wr : M.Writes) (c : ChIdx P t) : Option c.Challenge :=
  (M.comp c.leaf.label).chalWith (wr c.leaf)
    (M.key h ss (M.chains h ss wr) (M.finals h ss wr) c.leaf) ss.salt h c.idx

/-- The challenges, with the sampler's default value where it rejects (the verifier rejects
then). -/
def chV (wr : M.Writes) : Chs P t := fun c =>
  (M.chal h ss wr c).getD ((M.comp c.leaf.label).sampler c.idx).default

/-- **The compiled spBCS verifier `V^h(x, π)` accepts**: recompute the chains and the final
digests from `h`, each challenge from the stream at its key and the Fiat–Shamir salt; the samplers
accept every stream (`sampled`); there is one opened leaf per queried position (`leaves_length`);
every tree's opening checks (`paths`); the query phase accepts (`decides`). -/
structure Accepts [∀ j i, Nonempty ((P j).Challenge i)] {V : X → FullTr P t → Bool} (x : X)
    (π : M.NIProof) (Q : M.IOPQueries V x) : Prop where
  /-- The sampler accepts the stream of every challenge. -/
  sampled : ∀ c, (M.chal h ⟨π.salt, x⟩ π.writes c).isSome
  /-- One opened leaf per queried position. -/
  leaves_length : (Q.pos (M.chains h ⟨π.salt, x⟩ π.writes) (M.chV h ⟨π.salt, x⟩ π.writes)).length =
    π.leaves.length
  /-- Every tree's opening checks. -/
  paths : ∀ τ ∈ M.trees (Q.pos (M.chains h ⟨π.salt, x⟩ π.writes) (M.chV h ⟨π.salt, x⟩ π.writes)),
    SPBCS.checkTree h π
      (Q.pos (M.chains h ⟨π.salt, x⟩ π.writes) (M.chV h ⟨π.salt, x⟩ π.writes)) τ
  /-- The query phase's decision accepts. -/
  decides : Q.verdict (M.chains h ⟨π.salt, x⟩ π.writes) (M.chV h ⟨π.salt, x⟩ π.writes) π.leaves =
    true

/-- **The compiled verifier's acceptance is decided**: each challenge's sampling, the number of
opened leaves, each tree's opening and the query phase's decision. -/
instance [∀ j i, Nonempty ((P j).Challenge i)] {V : X → FullTr P t → Bool} (x : X)
    (π : M.NIProof) (Q : M.IOPQueries V x) : Decidable (M.Accepts h x π Q) :=
  decidable_of_iff ((∀ c, (M.chal h ⟨π.salt, x⟩ π.writes c).isSome) ∧
      (Q.pos (M.chains h ⟨π.salt, x⟩ π.writes) (M.chV h ⟨π.salt, x⟩ π.writes)).length =
        π.leaves.length ∧
      (∀ τ ∈ M.trees (Q.pos (M.chains h ⟨π.salt, x⟩ π.writes) (M.chV h ⟨π.salt, x⟩ π.writes)),
        SPBCS.checkTree h π
          (Q.pos (M.chains h ⟨π.salt, x⟩ π.writes) (M.chV h ⟨π.salt, x⟩ π.writes)) τ) ∧
      Q.verdict (M.chains h ⟨π.salt, x⟩ π.writes) (M.chV h ⟨π.salt, x⟩ π.writes) π.leaves = true)
    ⟨fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩,
      fun h => ⟨h.sampled, h.leaves_length, h.paths, h.decides⟩⟩

end

end GordieHowe.SPBCS
