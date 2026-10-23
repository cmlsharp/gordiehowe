-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.FinsetSingleton
public import GordieHowe.Model.QROM.Oracle

@[expose] public section

/-!
# Merkle tree extraction from an oracle database

The extractor `Extract(D, rt, d)` of Chiesa–Manohar–Spooner, "Succinct Arguments in the
Quantum Random Oracle Model" (CMS19, ePrint 2019/834, section 6.1, p. 31), with
Lemma 6.4 (`view_subtree_extend`, `extract_subtree_extend`) and Lemma 6.5
(`digest_mem_of_extract_ne`), over the domain-separated oracle of
`GordieHowe/Model/QROM/Oracle.lean`, and the one-query bound the knowledge argument consumes
(`prob_extract_change_le`).

Provenance: the top-down recurrence (a root label, its children read from the recorded
node query whose answer is that label, recursion into both children) follows VCVio's
`MerkleTreeExtractor.treeAt` (`VCVio/CryptoFoundations/MerkleTree/Extractor.lean`,
VCVio commit `eb0f6e4`, Apache-2.0, Quang Dao). Adapted: VCVio searches a query log for
the first matching entry over an inductive `Skeleton`; here the source is a database
`D : Query ⇀ Out`, a label is followed only when it has exactly one recorded preimage
(CMS19 step 2(c)), and the tree shape is Longfellow's heap layout. No VCVio code is
imported.

Tree shape. Longfellow's Merkle tree over `n ≥ 1` leaves (`lib/merkle/merkle_tree.h` at `ae30892`,
lines 105–117 and 148–153) stores the root at position `1`, the inner node at position `i` for
`1 ≤ i < n` is `hash2(layers[2i], layers[2i+1])`, and leaf `j < n` is at position `n + j`; `n` need
not be a power of two. The leaf digest is `H(salt ‖ column bytes)` with a `kN`-byte Merkle salt
(`MerkleSalt kN`; `lib/merkle/merkle_commitment.h` lines 31–44, 66–75 and 108–114; `kN = 2k` in the
C++, b90f5046). We model exactly this layout: `label D n rt p` is the digest extracted at position
`p`, with parent `p / 2` and inner positions `p < n`. The depth bound `d` of CMS19 is replaced by
the leaf count `n`, which fixes the layout. For `n = 2^d` this is CMS19's tree with vertex `(u, s)`
at heap position `2^|s| + s`.

Deviations from CMS19 section 6.1.
- A leaf is not a raw value: at leaf position `n + j` the extracted digest is opened
  through the recorded `leaf` query whose answer has that digest, giving the pair
  `(salt, column)` or `⊥` (`leafAt`).
- CMS19 step 2(b) returns `⊥` when a visited label has two preimages. `extract` returns
  `none` when some visited position `p < 2n` has a label with two or more recorded
  preimages (of any role: every answer's digest is compared). Below such a label
  `label` stops, since `preimage` is `none`.
- The extracted tree is the `MerkleView`: the partial labelling of positions and the
  partial leaf openings. "Subtree" (Lemma 6.4) is extension of both partial maps.
- Lemma 6.5 is proved without the collision-freeness hypotheses (only `x ∉ D` is
  used), and with `S(D)` for any transcript parse `digestsOf`.
-/

namespace GordieHowe.SPBCS
open GordieHowe.QROM

open GordieHowe.IOP
open scoped ENNReal

variable {k kN kS L e : ℕ}

/-! ### Preimages of a digest -/

/-- The recorded queries whose answer has digest `u`. -/
def preimages (D : ODB k kN kS L e) (u : Digest k) : Finset (Query k kN kS L) :=
  D.keys.filter fun q => (D.lookup q).map Out.digest = some u

variable {D : ODB k kN kS L e} {u : Digest k} {q x : Query k kN kS L} {y : Out k e}

theorem mem_preimages : q ∈ preimages D u ↔ q ∈ D ∧ (D.lookup q).map Out.digest = some u := by
  simp [preimages, Finmap.mem_keys]

/-- In a database without digest collisions every digest has at most one preimage. -/
theorem card_preimages_le_one (h : D ∉ digestCollision) (u : Digest k) :
    (preimages D u).card ≤ 1 := by
  refine Finset.card_le_one.2 fun a ha b hb => ?_
  by_contra hab
  rw [mem_preimages] at ha hb
  exact h ⟨a, ha.1, b, hb.1, hab, ha.2.trans hb.2.symm⟩

/-- The preimages after recording `x ↦ y` at a new input `x`. -/
theorem mem_preimages_extend (hx : x ∉ D) :
    q ∈ preimages (D.extend x y) u ↔ (q = x ∧ y.digest = u) ∨ q ∈ preimages D u := by
  rw [mem_preimages, mem_preimages, DB.mem_extend]
  by_cases hq : q = x
  · subst hq
    simp [hx]
  · simp [hq, DB.lookup_extend_of_ne hq]

theorem preimages_extend_of_ne (hx : x ∉ D) (hu : y.digest ≠ u) :
    preimages (D.extend x y) u = preimages D u := by
  ext q
  rw [mem_preimages_extend hx]
  simp [hu]

theorem preimages_subset_extend (hx : x ∉ D) : preimages D u ⊆ preimages (D.extend x y) u :=
  fun _ hq => (mem_preimages_extend hx).2 (Or.inr hq)

/-- The unique recorded preimage of `u`, or `none` when there is none or more than one
(CMS19 section 6.1, step 2(c)).

Running time: one scan of `D` collecting the recorded queries whose answer has digest `u`
(`preimages`), `O(|D|)`, then the element of the collected set if it has one
(`Finset.getSingleton?`). This running time is argued here, not proved in Lean. -/
def preimage (D : ODB k kN kS L e) (u : Digest k) : Option (Query k kN kS L) :=
  (preimages D u).getSingleton?

theorem preimage_eq_some_iff : preimage D u = some q ↔ preimages D u = {q} :=
  Finset.getSingleton?_eq_some_iff

/-- In a collision-free database, a recorded answer is the unique preimage of its digest. -/
theorem preimage_eq_of_lookup (hcol : D ∉ digestCollision) {v : Out k e}
    (h : D.lookup q = some v) : preimage D v.digest = some q := by
  rw [preimage_eq_some_iff]
  have hq : q ∈ preimages D v.digest := mem_preimages.2 ⟨DB.mem_iff_lookup.2 ⟨v, h⟩, by simp [h]⟩
  exact Finset.eq_singleton_iff_unique_mem.2
    ⟨hq, fun b hb => Finset.card_le_one.1 (card_preimages_le_one hcol _) b hb q hq⟩

theorem mem_of_preimage_eq_some (h : preimage D u = some q) : q ∈ D :=
  (mem_preimages.1 (by rw [preimage_eq_some_iff.1 h]; exact Finset.mem_singleton_self q)).1

theorem preimage_extend_of_ne (hx : x ∉ D) (hu : y.digest ≠ u) :
    preimage (D.extend x y) u = preimage D u := by
  unfold preimage
  simp only [preimages_extend_of_ne hx hu]

/-- A unique preimage stays the unique preimage in a collision-free extension. -/
theorem preimage_extend_of_eq_some (hx : x ∉ D) (hcol : D.extend x y ∉ digestCollision)
    (h : preimage D u = some q) : preimage (D.extend x y) u = some q := by
  rw [preimage_eq_some_iff] at h ⊢
  have hq : q ∈ preimages (D.extend x y) u :=
    preimages_subset_extend hx (by rw [h]; exact Finset.mem_singleton_self q)
  exact Finset.eq_singleton_iff_unique_mem.2
    ⟨hq, fun b hb => Finset.card_le_one.1 (card_preimages_le_one hcol u) b hb q hq⟩

/-! ### Reading node and leaf queries -/

/-- The children of a `node` query. -/
def _root_.GordieHowe.QROM.Query.children : Query k kN kS L → Option (Children k)
  | .node l r => some ⟨l, r⟩
  | _ => none

/-- The Merkle leaf (salt and column) of a `leaf` query. -/
def _root_.GordieHowe.QROM.Query.opening : Query k kN kS L → Option (MerkleLeaf kN L)
  | .leaf a c => some ⟨a, c⟩
  | _ => none

theorem _root_.GordieHowe.QROM.Query.eq_node_of_children_eq_some {c : Children k}
    (h : q.children = some c) : q = .node c.left c.right := by
  cases q with
  | node l r =>
    simp only [Query.children, Option.some_inj] at h
    subst h
    rfl
  | _ => simp [Query.children] at h

/-- The children of the node recorded with answer digest `u`. -/
def children (D : ODB k kN kS L e) (u : Digest k) : Option (Children k) :=
  (preimage D u).bind Query.children

/-- The leaf opening recorded with answer digest `u`. -/
def Merkle.opening (D : ODB k kN kS L e) (u : Digest k) : Option (MerkleLeaf kN L) :=
  (preimage D u).bind Query.opening

theorem children_extend_of_ne (hx : x ∉ D) (hu : y.digest ≠ u) :
    children (D.extend x y) u = children D u := by
  rw [children, children, preimage_extend_of_ne hx hu]

theorem Merkle.opening_extend_of_ne (hx : x ∉ D) (hu : y.digest ≠ u) :
    opening (D.extend x y) u = opening D u := by
  rw [opening, opening, preimage_extend_of_ne hx hu]

theorem children_extend_of_eq_some (hx : x ∉ D) (hcol : D.extend x y ∉ digestCollision)
    {c : Children k} (h : children D u = some c) :
    children (D.extend x y) u = some c := by
  obtain ⟨q, hq, hc⟩ := Option.bind_eq_some_iff.1 h
  rw [children, preimage_extend_of_eq_some hx hcol hq]
  exact hc

theorem opening_extend_of_eq_some (hx : x ∉ D) (hcol : D.extend x y ∉ digestCollision)
    {v : MerkleLeaf kN L} (h : Merkle.opening D u = some v) :
    Merkle.opening (D.extend x y) u = some v := by
  obtain ⟨q, hq, hc⟩ := Option.bind_eq_some_iff.1 h
  rw [Merkle.opening, preimage_extend_of_eq_some hx hcol hq]
  exact hc

/-- Both children of an extracted node lie in `S(D)`. -/
theorem mem_halfPre_of_children_eq_some {digestsOf : Bytes L → Finset (Digest k)}
    {c : Children k} (h : children D u = some c) :
    c.left ∈ halfPre digestsOf D ∧ c.right ∈ halfPre digestsOf D := by
  obtain ⟨q, hq, hc⟩ := Option.bind_eq_some_iff.1 h
  have hmem : Query.node c.left c.right ∈ D := Query.eq_node_of_children_eq_some hc ▸
    mem_of_preimage_eq_some hq
  exact ⟨left_mem_halfPre hmem, right_mem_halfPre hmem⟩

/-! ### The extracted labelling -/

/-- The child of position `p`'s parent selected by `p`: the left child at even `p`
(heap position `2i`), the right child at odd `p` (`2i + 1`). -/
def selectChild (p : ℕ) (c : Children k) : Digest k := if p % 2 = 0 then c.left else c.right

theorem selectChild_mem {s : Finset (Digest k)} (p : ℕ) {c : Children k}
    (h : c.left ∈ s ∧ c.right ∈ s) : selectChild p c ∈ s := by
  unfold selectChild; split_ifs <;> simp [h]

/-- The digest extracted at heap position `p` of an `n`-leaf tree rooted at `rt`
(`lib/merkle/merkle_tree.h` lines 112–117: position `i < n` is the node over `2i` and
`2i + 1`). Position `0` is unused, as in the C++. -/
def label (D : ODB k kN kS L e) (n : ℕ) (rt : Digest k) : ℕ → Option (Digest k)
  | 0 => none
  | 1 => some rt
  | p + 2 =>
    if (p + 2) / 2 < n then
      (label D n rt ((p + 2) / 2)).bind fun u => (children D u).map (selectChild (p + 2))
    else none
termination_by p => p
decreasing_by omega

variable {n : ℕ} {rt : Digest k}

theorem label_zero : label D n rt 0 = none := by rw [label]

theorem label_one : label D n rt 1 = some rt := by rw [label]

theorem label_succ_succ (p : ℕ) :
    label D n rt (p + 2) = if (p + 2) / 2 < n then
      (label D n rt ((p + 2) / 2)).bind fun u => (children D u).map (selectChild (p + 2))
    else none := by
  rw [label]

/-- Every extracted digest is the root or lies in `S(D)` (used by CMS19 Lemma 6.5). -/
theorem label_mem (digestsOf : Bytes L → Finset (Digest k)) :
    ∀ p, label D n rt p = some u → u = rt ∨ u ∈ halfPre digestsOf D := by
  intro p
  induction p using Nat.strong_induction_on generalizing u with
  | _ p ih =>
    match p with
    | 0 => simp [label_zero]
    | 1 => intro h; rw [label_one] at h; exact Or.inl (Option.some_inj.1 h).symm
    | p + 2 =>
      intro h
      rw [label_succ_succ] at h
      split_ifs at h
      obtain ⟨v, -, hv⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hv
      exact Or.inr (selectChild_mem _ (mem_halfPre_of_children_eq_some hc))

/-- CMS19 Lemma 6.4 on labels: a collision-free extension keeps every extracted digest. -/
theorem label_extend_of_eq_some (hx : x ∉ D) (hcol : D.extend x y ∉ digestCollision) :
    ∀ p, label D n rt p = some u → label (D.extend x y) n rt p = some u := by
  intro p
  induction p using Nat.strong_induction_on generalizing u with
  | _ p ih =>
    match p with
    | 0 => simp [label_zero]
    | 1 => simp [label_one]
    | p + 2 =>
      intro h
      rw [label_succ_succ] at h ⊢
      split_ifs at h ⊢ with hp
      obtain ⟨v, hv, hc⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨c, hc', rfl⟩ := Option.map_eq_some_iff.1 hc
      rw [ih _ (by omega) hv, Option.bind_some, children_extend_of_eq_some hx hcol hc',
        Option.map_some]

/-- A new answer whose digest is neither the root nor in `S(D)` changes no label. -/
theorem label_extend_of_notMem (hx : x ∉ D) {digestsOf : Bytes L → Finset (Digest k)}
    (hy : y.digest ≠ rt) (hy' : y.digest ∉ halfPre digestsOf D) :
    ∀ p, label (D.extend x y) n rt p = label D n rt p := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    match p with
    | 0 => simp [label_zero]
    | 1 => simp [label_one]
    | p + 2 =>
      rw [label_succ_succ, label_succ_succ, ih _ (by omega)]
      split_ifs
      · cases hv : label D n rt ((p + 2) / 2) with
        | none => rfl
        | some v =>
          have hne : y.digest ≠ v := by
            rintro rfl
            exact (label_mem digestsOf _ hv).elim hy hy'
          simp [children_extend_of_ne hx hne]
      · rfl

/-! ### The extracted tree -/

/-- The leaf opening `(salt, column)` extracted at leaf `j`, heap position `n + j`
(`lib/merkle/merkle_tree.h` lines 107–110 and 149). -/
def leafAt (D : ODB k kN kS L e) (n : ℕ) (rt : Digest k) (j : Fin n) :
    Option (MerkleLeaf kN L) :=
  (label D n rt (n + j)).bind (Merkle.opening D)

/-- An extracted tree: the partial labelling of heap positions and the partial leaf
openings (`leaves(T)` of CMS19 p. 31, with `⊥` as `none`). -/
@[ext] structure MerkleView (k kN L n : ℕ) where
  /-- The digest extracted at each heap position. -/
  label : ℕ → Option (Digest k)
  /-- The `(salt, column)` extracted at each leaf. -/
  leaves : Fin n → Option (MerkleLeaf kN L)

/-- `T₁` is a subtree of `T₂`: every label and every leaf of `T₁` is in `T₂`. -/
structure MerkleView.IsSubtree {n : ℕ} (T₁ T₂ : MerkleView k kN L n) : Prop where
  label : ∀ p u, T₁.label p = some u → T₂.label p = some u
  leaves : ∀ j v, T₁.leaves j = some v → T₂.leaves j = some v

/-- The tree read from `D` below `rt`, without the collision check. -/
def view (D : ODB k kN kS L e) (n : ℕ) (rt : Digest k) : MerkleView k kN L n :=
  ⟨label D n rt, leafAt D n rt⟩

/-- No visited position `p < 2n` carries a digest with two or more recorded preimages
(the check of CMS19 section 6.1, step 2(b)). -/
def NoVisitedCollision (D : ODB k kN kS L e) (n : ℕ) (rt : Digest k) : Prop :=
  ∀ p < 2 * n, ∀ u, label D n rt p = some u → (preimages D u).card ≤ 1

open Classical in
/-- `extract(D, rt)` (CMS19 section 6.1, p. 31) for Longfellow's `n`-leaf heap layout:
the extracted tree, or `⊥` when a visited digest has a collision. -/
noncomputable def extract (D : ODB k kN kS L e) (n : ℕ) (rt : Digest k) : Option (MerkleView k kN L n) :=
  if NoVisitedCollision D n rt then some (view D n rt) else none

theorem extract_eq_some (h : D ∉ digestCollision) : extract D n rt = some (view D n rt) := by
  have hn : NoVisitedCollision D n rt := fun _ _ u _ => card_preimages_le_one h u
  simp [extract, hn]

/-- CMS19 Lemma 6.4 (p. 31) on the extracted trees. -/
theorem view_subtree_extend (hx : x ∉ D) (hcol : D.extend x y ∉ digestCollision) :
    (view D n rt).IsSubtree (view (D.extend x y) n rt) where
  label p _ h := label_extend_of_eq_some hx hcol p h
  leaves j v h := by
    obtain ⟨u, hu, hv⟩ := Option.bind_eq_some_iff.1 h
    exact Option.bind_eq_some_iff.2
      ⟨u, label_extend_of_eq_some hx hcol _ hu, opening_extend_of_eq_some hx hcol hv⟩

/-- CMS19 Lemma 6.4 (p. 31): for `x ∉ supp(D)` and `D + [x ↦ y]` without digest
collisions, `extract(D, rt)` is a subtree of `extract(D + [x ↦ y], rt)`. -/
theorem extract_subtree_extend (hx : x ∉ D) (hcol : D.extend x y ∉ digestCollision) :
    ∃ T₁ T₂, extract D n rt = some T₁ ∧ extract (D.extend x y) n rt = some T₂ ∧
      T₁.IsSubtree T₂ :=
  ⟨_, _, extract_eq_some (notMem_collisionOn_of_extend hx hcol), extract_eq_some hcol,
    view_subtree_extend hx hcol⟩

/-- CMS19 Lemma 6.5 (p. 31): if recording `x ↦ y` at a new input changes the extracted
tree, then the digest of `y` is the root or lies in `S(D)`. The paper assumes `D` and
`D + [x ↦ y]` collision-free; the proof does not need it. -/
theorem digest_mem_of_extract_ne (hx : x ∉ D) (digestsOf : Bytes L → Finset (Digest k))
    (h : extract D n rt ≠ extract (D.extend x y) n rt) :
    y.digest ∈ insert rt (halfPre digestsOf D) := by
  rw [Finset.mem_insert]
  by_contra hy
  push Not at hy
  obtain ⟨hrt, hS⟩ := hy
  have hl := label_extend_of_notMem (n := n) hx hrt hS
  have hv : view (D.extend x y) n rt = view D n rt := by
    refine MerkleView.ext (funext hl) (funext fun j => ?_)
    simp only [view, leafAt, hl]
    cases hu : label D n rt (n + j) with
    | none => rfl
    | some u =>
      have hne : y.digest ≠ u := by
        rintro rfl
        exact (label_mem digestsOf _ hu).elim hrt hS
      simp [Merkle.opening_extend_of_ne hx hne]
  have hn : NoVisitedCollision (D.extend x y) n rt ↔ NoVisitedCollision D n rt := by
    refine forall₂_congr fun p _ => forall_congr' fun u => ?_
    rw [hl]
    refine imp_congr_right fun hu => ?_
    have hne : y.digest ≠ u := by
      rintro rfl
      exact (label_mem digestsOf _ hu).elim hrt hS
    rw [preimages_extend_of_ne hx hne]
  apply h
  unfold extract
  by_cases hA : NoVisitedCollision D n rt <;> simp [hA, hn, hv]

/-- The one-query bound the knowledge argument consumes: for `x ∉ supp(D)`, the probability over a
uniform answer `y` that `D + [x ↦ y]` has no digest collision and the extracted tree
changes is at most `(|S(D)| + 1) / 2^(8k)`. -/
theorem prob_extract_change_le (hx : x ∉ D) (digestsOf : Bytes L → Finset (Digest k)) :
    Pr[y ← Out k e : D.extend x y ∉ digestCollision ∧
        extract D n rt ≠ extract (D.extend x y) n rt] ≤
      ((halfPre digestsOf D).card + 1 : ℝ≥0∞) / 2 ^ (8 * k) := by
  calc Pr[y ← Out k e : D.extend x y ∉ digestCollision ∧
          extract D n rt ≠ extract (D.extend x y) n rt]
      ≤ Pr[y ← Out k e : y.digest ∈ insert rt (halfPre digestsOf D)] :=
        QROM.probUniform_mono fun y hy => digest_mem_of_extract_ne hx digestsOf hy.2
    _ = (insert rt (halfPre digestsOf D)).card / 2 ^ (8 * k) := Out.probUniform_digest_mem _
    _ ≤ ((halfPre digestsOf D).card + 1 : ℝ≥0∞) / 2 ^ (8 * k) := by
        gcongr
        exact_mod_cast Finset.card_insert_le _ _

/-- `prob_extract_change_le` with `|S(D)| ≤ max 2 c · |D|`, where a transcript prefix
contains at most `c` digests. -/
theorem prob_extract_change_le_size (hx : x ∉ D) {digestsOf : Bytes L → Finset (Digest k)}
    {c : ℕ} (hT : ∀ p, (digestsOf p).card ≤ c) :
    Pr[y ← Out k e : D.extend x y ∉ digestCollision ∧
        extract D n rt ≠ extract (D.extend x y) n rt] ≤
      ((max 2 c * D.size : ℕ) + 1 : ℝ≥0∞) / 2 ^ (8 * k) := by
  refine (prob_extract_change_le hx digestsOf).trans ?_
  gcongr
  exact_mod_cast card_halfPre_le hT

end GordieHowe.SPBCS
