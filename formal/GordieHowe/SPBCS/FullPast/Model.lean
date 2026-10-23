-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.FullPast.Encoding
public import GordieHowe.SPBCS.Extraction.Transcript
public import GordieHowe.Model.QROM.Lifting
public import GordieHowe.Model.QROM.Expansion
public import GordieHowe.SPBCS.Merkle.Opening

@[expose] public section

/-!
# The compiler data of a series–parallel composition, and the full-past compiler

TODO: remove `FullPast`. The full-past compiler is a leftover of the causal model, which the merge
model superseded.

`GordieHowe.SPBCS.Base` is the compiler data of a series–parallel composition of public-coin
protocols (`GordieHowe/Model/IOP/Causal.lean`): the components `P j : ProtocolSpec (n j)` composed
by a term `t`, each leaf with its own hash chain. The spBCS compiler (`GordieHowe.SPBCS`,
`GordieHowe/SPBCS/Basic.lean`) extends it with the encoding of chain inputs with merges. The
namespace `Base` holds the declarations that the headline statements and the paper manifest reach
(the proofs, the query phases, the error terms, the adversary classes), with their lemmas.

`GordieHowe.SPBCS.FullPast` (proof-internal) is the full-past compiler, an abbreviation of `Base`
that the spBCS compiler's knowledge-soundness reduction uses: each challenge is derived from a hash
of its full causal past (`GordieHowe/SPBCS/FullPast/Encoding.lean`); a total order of the components
is the case of a single hash chain. What remains in the namespace `FullPast` is proof-internal: the
full-past chains and challenges (`leafChainFullPast`, `chainsFullPast`, `chalOf`), the compiled
verifier `AcceptsFullPast` and its query programs, the stability and extraction lemmas of the
knowledge-soundness reduction, the zero-knowledge and witness-indistinguishability hybrids, the ROM
simulation-extraction adversaries and the oracle-test devices. Field notation on an `M : SPBCS …`
reaches them through `M.toFullPast`.

* `ComponentModel P k kN L e`: the per-component data of one hash chain (writes, Merkle trees,
  messages read from writes and views, samplers).
* `GordieHowe.SPBCS.Base P t X k kN kS L e`: a component model for every component, one chain-input
  encoding (`CausalEncoding`) of the term, and the Merkle opening format (`MerkleOpening`,
  `GordieHowe/SPBCS/Merkle/Opening.lean`) with which a proof opens its trees: the authentication paths of
  paper `prot:generalized-bcs` (`PerLeaf.opening`) or the compressed multiproofs of the C++
  (`Multiproof.opening`). Every guarantee holds for every format.
* `Base.NIProof`: the salt, the writes of every leaf, the opened leaves and the path digests of every
  tree, in the opening format. `Base.IOPQueries V x`: the query phase of the composite verifier `V`
  and its laws.
* The chain of leaf `p` given the full chains of the leaves before it (`FullPast.leafChainFullPast`):
  item `r` is the prover's write at a prover round and, at a challenge round, the digest of the
  stream at the key of the chain input `(σ, x, p, earlier chains, first r items)` and the salt
  (the write-back). `FullPast.chainsFullPast` computes the chains of all leaves by the causal
  fixpoint (`SPTerm.solve`), each from the chains of the leaves before it; `FullPast.chalOf c`
  samples the challenge `c` from the stream at the key of its chain input.
  `FullPast.AcceptsFullPast`: the compiled full-past verifier.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open scoped ENNReal NNReal

variable {k kN kS L e : ℕ}

/-! ### Component models -/

/-- **The per-component data of one hash chain**: the write of each prover round, its Merkle
trees, the message read from a write and the views of its trees, and the sampler of each
challenge round. The fields carry correspondence obligations: the writes, roots and messages are
those of the C++ transcript, and each sampler is the C++ challenge reader of its round. -/
structure ComponentModel {m : ℕ} (P : ProtocolSpec m) (k kN L e : ℕ)
    [∀ i, Fintype (P.Challenge i)] [∀ i, DecidableEq (P.Challenge i)] where
  /-- The prover's write of each prover round. -/
  MessageWrite : P.MessageIdx → Type
  /-- The number of trees of each prover round. -/
  nTrees : P.MessageIdx → ℕ
  /-- The leaf count of each tree. -/
  nLeaves : (i : P.MessageIdx) → Fin (nTrees i) → ℕ
  /-- The root of each tree carried by a write. -/
  rootOf : (i : P.MessageIdx) → MessageWrite i → Fin (nTrees i) → Digest k
  /-- The message read from a write and the Merkle views of its trees. -/
  msg : (i : P.MessageIdx) → MessageWrite i →
    ((t : Fin (nTrees i)) → MerkleView k kN L (nLeaves i t)) → P.Type i.1
  /-- The sampler of each challenge round. -/
  sampler : (i : P.ChallengeIdx) → Sampler k e (P.Challenge i)

namespace ComponentModel

variable {m : ℕ} {P : ProtocolSpec m} [∀ i, Fintype (P.Challenge i)]
  [∀ i, DecidableEq (P.Challenge i)] (C : ComponentModel P k kN L e)

/-- A write of some round, tagged with its round. -/
abbrev W : Type := Σ i, C.MessageWrite i

/-- The roots a write carries. -/
def roots (w : C.W) : Finset (Digest k) := Finset.univ.image (C.rootOf w.1 w.2)

/-! #### A chain from a key function -/

variable {kS : ℕ} (wr : (i : P.MessageIdx) → C.MessageWrite i) (keyOf : List (Item k C.W) → Digest k)
  (salt : FiatShamirSalt kS) (h : Query k kN kS L → Out k e)

/-- **Item `r` of a chain after the items `l`**, for the keys `keyOf` and the Fiat–Shamir salt
`salt`: the write at a prover round, the digest of the stream at the key of `l` and the salt at a
challenge round (the write-back). -/
def itemWith (r : ℕ) (hr : r < m) (l : List (Item k C.W)) : Item k C.W :=
  if hd : P.dir ⟨r, hr⟩ = .P_to_V then .write ⟨⟨⟨r, hr⟩, hd⟩, wr ⟨⟨r, hr⟩, hd⟩⟩
  else .absorb (h (.xof (keyOf l) salt)).digest

/-- **The first `r` items of a chain** for the keys `keyOf` and the salt `salt`: the chain of a
compiler whose chain input at the items `l` has the key `keyOf l`. -/
def chainWith : (r : ℕ) → r ≤ m → List (Item k C.W)
  | 0, _ => []
  | r + 1, hr => chainWith r (by omega) ++ [C.itemWith wr keyOf salt h r (by omega) (chainWith r (by omega))]

theorem length_chainWith : ∀ r (hr : r ≤ m), (C.chainWith wr keyOf salt h r hr).length = r
  | 0, _ => rfl
  | r + 1, hr => by simp [chainWith, length_chainWith r]

theorem chainWith_getElem? : ∀ r (hr : r ≤ m) j (hj : j < r), (C.chainWith wr keyOf salt h r hr)[j]? =
    some (C.itemWith wr keyOf salt h j (by omega) (C.chainWith wr keyOf salt h j (by omega)))
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | r + 1, hr, j, hj => by
    rw [chainWith]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
    · rw [List.getElem?_append_left (by rw [length_chainWith]; exact hj'),
        chainWith_getElem? r (by omega) j hj']
    · rw [List.getElem?_append_right (by rw [length_chainWith]), length_chainWith]
      simp

variable {wr keyOf salt h} in
/-- **Two chains agree** when their key functions, salts and oracles give the same items at the
chain's own prefixes. -/
theorem chainWith_congr {keyOf' : List (Item k C.W) → Digest k} {kS' : ℕ}
    {salt' : FiatShamirSalt kS'} {h' : Query k kN kS' L → Out k e} :
    ∀ r (hr : r ≤ m), (∀ j (hj : j < r),
      (h (.xof (keyOf (C.chainWith wr keyOf salt h j (by omega))) salt)).digest =
        (h' (.xof (keyOf' (C.chainWith wr keyOf salt h j (by omega))) salt')).digest) →
      C.chainWith wr keyOf salt h r hr = C.chainWith wr keyOf' salt' h' r hr
  | 0, _, _ => rfl
  | r + 1, hr, hag => by
    have ih := chainWith_congr r (by omega) fun j hj => hag j (by omega)
    rw [chainWith, chainWith, ← ih]
    congr 2
    unfold itemWith
    split_ifs
    · rfl
    · rw [hag r (Nat.lt_succ_self r)]

variable {keyOf salt h} in
/-- **Two chains agree when their writes agree at the prover rounds before `r`.** -/
theorem chainWith_congr_wr {wr' : (i : P.MessageIdx) → C.MessageWrite i} :
    ∀ r (hr : r ≤ m), (∀ i : P.MessageIdx, i.1.1 < r → wr i = wr' i) →
      C.chainWith wr keyOf salt h r hr = C.chainWith wr' keyOf salt h r hr
  | 0, _, _ => rfl
  | r + 1, hr, hw => by
    have ih := chainWith_congr_wr r (by omega) fun i hi => hw i (by omega)
    rw [chainWith, chainWith, ← ih]
    congr 2
    unfold itemWith
    split_ifs with hd
    · rw [hw ⟨⟨r, by omega⟩, hd⟩ (Nat.lt_succ_self r)]
    · rfl

/-- **A chain from a key function is well formed**: a write at each prover round, an absorbed
digest at each challenge round. -/
theorem chainWF_chainWith (r : ℕ) (hr : r ≤ m) : chainWF P (C.chainWith wr keyOf salt h r hr) := by
  intro j hj
  rw [length_chainWith] at hj
  have hget := C.chainWith_getElem? wr keyOf salt h r hr j hj
  rw [List.getElem?_eq_getElem (by rw [length_chainWith]; exact hj), Option.some_inj] at hget
  rw [hget]
  unfold itemWith
  split_ifs with hd
  · rfl
  · exact ⟨by omega, by cases h' : P.dir ⟨j, by omega⟩ <;> simp_all⟩

/-- **The challenge `i` of a chain**, sampled from the stream at the key of its prefix and the
salt, or `none` when the sampler rejects. -/
def chalWith (i : P.ChallengeIdx) : Option (P.Challenge i) :=
  (C.sampler i).sample (h (.xof (keyOf (C.chainWith wr keyOf salt h i.1 i.1.2.le)) salt)).stream

end ComponentModel

/-! ### The compiler data over a term -/

variable {ι : Type} {n : ι → ℕ}

/-- **The compiler data of a series–parallel composition** of the components `P` by the term `t`,
for statements in `X`, which the spBCS compiler (`GordieHowe.SPBCS`) extends with the encoding of
chain inputs with merges: a component model per component, the encoding of chain inputs
(`CausalEncoding`) of the salted statement and the causal past, whose digests are the roots of the
writes and the absorbed digests, and the Merkle opening format. -/
structure Base (P : (j : ι) → ProtocolSpec (n j)) (t : SPTerm ι) (X : Type)
    (k kN kS L e : ℕ) [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
    where
  /-- The data of each component. -/
  comp : (j : ι) → ComponentModel (P j) k kN L e
  /-- The encoding of chain inputs. -/
  enc : CausalEncoding k L t n (SaltedStatement kS X) (fun j => (comp j).W)
    (fun j => (comp j).roots) (fun j => chainWF (P j))
  /-- How a proof opens the queried leaves of a tree. -/
  opening : MerkleOpening k kN kS L e

/-- **The full-past compiler** (proof-internal) used in the spBCS compiler's knowledge-soundness
reduction: the compiler data `Base`, whose challenges the declarations in the namespace
`FullPast` derive from a hash of the full causal past. Field notation on a `FullPast` reaches
these declarations and, through the abbreviation, those of `Base`. -/
abbrev FullPast (P : (j : ι) → ProtocolSpec (n j)) (t : SPTerm ι) (X : Type)
    (k kN kS L e : ℕ) [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] :=
  Base P t X k kN kS L e

namespace Base

variable {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι} {X : Type}
  (M : Base P t X k kN kS L e)

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

/-- The content of the chain input at leaf `p`, causal context `ctx` and own items `l`. -/
def content (p : t.Leaf) (ctx : M.Ctx p) (l : M.Items p) :
    CausalChain t k fun j => (M.comp j).W :=
  ⟨p, M.chainsOf ctx, l⟩

/-- **Content is determined by the context's chains at the leaves before.** -/
theorem content_congr {p : t.Leaf} {ctx ctx' : M.Ctx p}
    (h : ∀ q (hq : q.Before p), ctx ⟨q, hq⟩ = ctx' ⟨q, hq⟩) (l : M.Items p) :
    M.content p ctx l = M.content p ctx' l := by
  have hc : M.chainsOf ctx = M.chainsOf ctx' := funext fun q => by
    by_cases hq : q.Before p
    · rw [chainsOf_of_before M ctx hq, chainsOf_of_before M ctx' hq, h q hq]
    · rw [chainsOf_of_not_before M ctx hq, chainsOf_of_not_before M ctx' hq]
  simp only [content, hc]

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
def Pos.treeOf {M : Base P t X k kN kS L e} (q : M.Pos) : M.Tree := ⟨q.leaf, q.pos.treeIdx⟩

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
that `V` reads the prover messages only at those positions. Correspondence obligations of each IOP
stage. -/
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

/-- The check of tree `τ`'s opening in `π` (`MerkleFormat.check`) against its root in its round's
write, at the opened leaves of `τ` among the positions `ps`. -/
def checkTree (π : M.NIProof) (ps : List M.Pos) (τ : M.Tree) : Prop :=
  M.opening.check h ((M.comp τ.leaf.label).nLeaves τ.tree.msg τ.tree.tree)
    ((M.comp τ.leaf.label).rootOf τ.tree.msg (π.writes τ.leaf τ.tree.msg) τ.tree.tree)
    ((M.openedIn τ ps π.leaves).map Prod.fst) ((M.openedIn τ ps π.leaves).map Prod.snd)
    (π.paths τ)

variable (P t) in
/-- **The challenges in global round order**, as a list: the challenge rounds among the slots. -/
def chList : List (ChIdx P t) :=
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

end Base

namespace FullPast

open Base

variable {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι} {X : Type}
  (M : FullPast P t X k kN kS L e)

variable (h : Query k kN kS L → Out k e) (x : X) (σ : FiatShamirSalt kS)

/-- **The key of a chain input**: the digest of `h` at the encoded salted statement and causal
past (leaf `p`, context `ctx`, own items `l`). -/
def keyFullPast (p : t.Leaf) (ctx : M.Ctx p) (l : M.Items p) : Digest k :=
  (h (.transcript (M.enc.encode ⟨σ, x⟩ (M.content p ctx l)))).digest

/-- **Item `r` of leaf `p`'s chain after the items `l`**: the write at a prover round, the digest
of the stream at the key and the salt at a challenge round (the write-back). -/
def itemAt (wr : M.Writes) (p : t.Leaf) (ctx : M.Ctx p) (r : ℕ) (hr : r < n p.label)
    (l : M.Items p) : Item k (M.comp p.label).W :=
  if hd : (P p.label).dir ⟨r, hr⟩ = .P_to_V then .write ⟨⟨⟨r, hr⟩, hd⟩, wr p ⟨⟨r, hr⟩, hd⟩⟩
  else .absorb (h (.xof (M.keyFullPast h x σ p ctx l) σ)).digest

/-- **The first `r` items of leaf `p`'s chain** in the causal context `ctx`. -/
def leafChainFullPast (wr : M.Writes) (p : t.Leaf) (ctx : M.Ctx p) :
    (r : ℕ) → r ≤ n p.label → M.Items p
  | 0, _ => []
  | r + 1, hr => leafChainFullPast wr p ctx r (by omega) ++
      [M.itemAt h x σ wr p ctx r (by omega) (leafChainFullPast wr p ctx r (by omega))]

/-- **A leaf's chain is the chain of its component for the keys of its chain inputs.** -/
theorem leafChainFullPast_eq_chainWith (wr : M.Writes) (p : t.Leaf) (ctx : M.Ctx p) :
    ∀ r (hr : r ≤ n p.label), M.leafChainFullPast h x σ wr p ctx r hr =
      (M.comp p.label).chainWith (wr p) (M.keyFullPast h x σ p ctx) σ h r hr
  | 0, _ => rfl
  | r + 1, hr => by
    rw [leafChainFullPast, ComponentModel.chainWith, leafChainFullPast_eq_chainWith wr p ctx r]
    rfl

theorem length_leafChainFullPast (wr : M.Writes) (p : t.Leaf) (ctx : M.Ctx p) :
    ∀ r (hr : r ≤ n p.label), (M.leafChainFullPast h x σ wr p ctx r hr).length = r
  | 0, _ => rfl
  | r + 1, hr => by simp [leafChainFullPast, length_leafChainFullPast wr p ctx r]

/-- **The chains of all leaves** (the causal fixpoint): each leaf's full chain in the context of
the chains of the leaves before it. -/
def chainsFullPast (wr : M.Writes) : (p : t.Leaf) → M.Items p :=
  SPTerm.solve fun p ctx => M.leafChainFullPast h x σ wr p ctx (n p.label) le_rfl

/-- The causal context of leaf `p` in the chains of all leaves. -/
def ctxOf (wr : M.Writes) (p : t.Leaf) : M.Ctx p := fun q => M.chainsFullPast h x σ wr q.1

theorem leafChainFullPast_getElem? (wr : M.Writes) (p : t.Leaf) (ctx : M.Ctx p) :
    ∀ r (hr : r ≤ n p.label) j (hj : j < r), (M.leafChainFullPast h x σ wr p ctx r hr)[j]? =
      some (M.itemAt h x σ wr p ctx j (by omega) (M.leafChainFullPast h x σ wr p ctx j (by omega)))
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | r + 1, hr, j, hj => by
    rw [leafChainFullPast]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
    · rw [List.getElem?_append_left (by rw [length_leafChainFullPast]; exact hj'),
        leafChainFullPast_getElem? wr p ctx r (by omega) j hj']
    · rw [List.getElem?_append_right (by rw [length_leafChainFullPast]), length_leafChainFullPast]
      simp

theorem chainsFullPast_eq (wr : M.Writes) (p : t.Leaf) :
    M.chainsFullPast h x σ wr p = M.leafChainFullPast h x σ wr p (M.ctxOf h x σ wr p) (n p.label) le_rfl :=
  SPTerm.solve_eq _ p

/-- **The item of a prover round of a leaf's chain is the leaf's write.** -/
theorem chainsFullPast_getElem?_message (wr : M.Writes) (p : t.Leaf) (i : (P p.label).MessageIdx) :
    (M.chainsFullPast h x σ wr p)[i.1.1]? = some (.write ⟨i, wr p i⟩) := by
  rw [chainsFullPast_eq, leafChainFullPast_getElem? M h x σ wr p _ _ le_rfl i.1 i.1.2]
  unfold itemAt
  simp only [i.2, ↓reduceDIte]
  rfl

/-- **The challenge `c`** derived from the stream at the key of its chain input and the salt, or
`none` when the sampler rejects. -/
def chalOf (wr : M.Writes) (c : ChIdx P t) : Option c.Challenge :=
  ((M.comp c.leaf.label).sampler c.idx).sample (h (.xof (M.keyFullPast h x σ c.leaf
    (M.ctxOf h x σ wr c.leaf)
    (M.leafChainFullPast h x σ wr c.leaf (M.ctxOf h x σ wr c.leaf) c.idx.1 c.idx.1.2.le)) σ)).stream

/-- The derived challenges, with the sampler's default value where it rejects (the verifier
rejects then). -/
def chVFullPast (wr : M.Writes) : Chs P t := fun c =>
  (M.chalOf h x σ wr c).getD ((M.comp c.leaf.label).sampler c.idx).default

variable {M}

/-- **The compiled verifier `V^h(x, π)` accepts**: recompute the chains of all leaves, the keys,
the absorbed digests and the challenges from `h`, each challenge from its causal past; the
samplers accept every stream (`sampled`); there is one opened leaf per queried position
(`leaves_length`); every tree's opening checks (`paths`); the query phase accepts
(`decides`). -/
structure AcceptsFullPast [∀ j i, Nonempty ((P j).Challenge i)] {StmtIn : Type} {M : FullPast P t StmtIn k kN kS L e}
    {V : StmtIn → FullTr P t → Bool} (x : StmtIn) (π : M.NIProof) (Q : M.IOPQueries V x) : Prop where
  /-- The sampler accepts the stream of every challenge. -/
  sampled : ∀ c, (M.chalOf h x π.salt π.writes c).isSome
  /-- One opened leaf per queried position. -/
  leaves_length : (Q.pos (M.chainsFullPast h x π.salt π.writes) (M.chVFullPast h x π.salt π.writes)).length =
    π.leaves.length
  /-- Every tree's opening checks. -/
  paths : ∀ τ ∈ M.trees (Q.pos (M.chainsFullPast h x π.salt π.writes) (M.chVFullPast h x π.salt π.writes)),
    checkTree h π (Q.pos (M.chainsFullPast h x π.salt π.writes) (M.chVFullPast h x π.salt π.writes)) τ
  /-- The query phase's decision accepts. -/
  decides : Q.verdict (M.chainsFullPast h x π.salt π.writes) (M.chVFullPast h x π.salt π.writes) π.leaves = true

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

variable (P t) in
/-- **The challenges in global round order** (not an instance, so that equality of challenges is
decided by its own instance alone). -/
abbrev chOrder : LinearOrder (ChIdx P t) :=
  LinearOrder.lift' gIdx gIdx_injective

end FullPast

end GordieHowe.SPBCS
