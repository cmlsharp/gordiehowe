-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Merkle.Opening
public import GordieHowe.Model.QROM.Expansion

@[expose] public section

/-!
# Compressed Merkle multiproofs

The Merkle opening format (`MerkleOpening`, `GordieHowe/SPBCS/Merkle/Opening.lean`) that the C++ verifier
checks: one compressed multiproof per tree
(`BasicMerkleTreeVerifier::verify_compressed_proof`, `lib/merkle/merkle_tree.h` lines 165–214,
called by `BasicMerkleCommitmentVerifier::verify`, `lib/merkle/merkle_commitment.h` lines 95–111,
from the Ligero verifier's `merkle_check`, `lib/ligero/ligero_verifier.h` lines 166–178, at the
`nreq` columns `idx` of `gen_idx`, line 101). The prover's counterpart is
`BasicMerkleTree::generate_compressed_proof` (`merkle_tree.h` lines 125–146), called by
`BasicMerkleCommitment::open` (`merkle_commitment.h` lines 73–81) from the Ligero prover
(`lib/ligero/ligero_prover.h` line 151); the proof is serialized as the `nreq` Merkle salts, the
opened columns and the path digests with their count (`lib/zk/zk_proof.h` lines 220–251). A Merkle
salt has `kN` bytes (`MerkleSalt kN`; `2k` in the C++, b90f5046).

For an `n`-leaf tree in the heap layout of `GordieHowe/SPBCS/Merkle/Extract.lean` and opened leaf indices
`js`:
- `inTree n js i` is the set `TREE` of `compressed_merkle_proof_tree` (`merkle_tree.h` lines
  76–99): the heap positions on the path from the root to an opened leaf. The C++ computes it
  bottom-up (a leaf position `n + j` for `j ∈ js`, an inner node when a child is in `TREE`);
  `inTree_leaf_iff` and `inTree_node_iff` are that recurrence.
- `sibNodes n js` lists the positions whose digests the proof carries, in the proof's order: for
  each inner node of `TREE`, from position `n - 1` down to `1`, its child outside `TREE`, if any
  (`merkle_tree.h` lines 177–193 and 132–143).
- `reconProg` recomputes the digest at a position with the C++ rule (lines 199–213): an opened
  leaf has its leaf digest, a proof position its proof digest, and an inner node of `TREE` the
  hash of its children's digests, one `node` query, when both are defined. The C++ runs the
  bottom-up loop over all positions `n - 1, …, 1`; a position outside `TREE` never has both
  children defined (a child of a position outside `TREE` is neither in `TREE` nor a proof
  position), so the loop hashes exactly the inner nodes of `TREE` whose children are defined,
  which is what the top-down recursion computes. The node queries are the same set; their order
  differs (post-order here, descending positions in the C++), which the base game does not see.
- `treeProg` first makes the leaf queries `leaf salt column` of the opened leaves in order
  (`merkle_commitment.h` lines 99–106), then `reconProg` at the root; `format.check` is acceptance:
  distinct in-range indices (the C++ panics otherwise, `merkle_tree.h` lines 84–86), one opened
  leaf per index, exactly one path digest per proof position (lines 186–195), and the recomputed
  root is the root (line 213).

For the honest prover, over the honest tree `MerkleTree.treeDigest h n lf` (`GordieHowe/SPBCS/Merkle/Tree.lean`),
`format.path` is the compressed multiproof of `generate_compressed_proof` (`merkle_tree.h` lines
125–146): the digests of the honest tree at the proof positions `sibNodes n js`, in that order.
`check_path` is completeness: the honest leaves at distinct in-range indices, with the honest
path, are accepted against the honest root.

`leafAt_of_check` is the Merkle part of CMS19 Proposition 8.12 for multiproofs: an accepted
multiproof whose queries are recorded in a collision-free database opens, at each index, the
leaf that `extract` reads. `length_trace_treeProg_le` bounds the queries of an accepted
multiproof by `|js| · (1 + ⌊log₂ 2n⌋)`, the count of one authentication path per opened leaf.
`opening` is the format with these laws.
-/

namespace GordieHowe.SPBCS
open GordieHowe.QROM

open GordieHowe.IOP

variable {k kN kS L e : ℕ}

/-! ### The compressed multiproof -/

namespace Multiproof

/-- `TREE` of `compressed_merkle_proof_tree` (`lib/merkle/merkle_tree.h` lines 76–99): the
heap positions `i ≥ 1` on the path from the root to an opened leaf `n + j`, `j ∈ js`. -/
def inTree (n : ℕ) (js : List ℕ) (i : ℕ) : Prop := 1 ≤ i ∧ ∃ j ∈ js, OnPath i (n + j)

/-- Membership in `TREE` is decidable: a search over the opened indices and the halvings. -/
instance (n : ℕ) (js : List ℕ) (i : ℕ) : Decidable (inTree n js i) :=
  inferInstanceAs (Decidable (1 ≤ i ∧ ∃ j ∈ js, OnPath i (n + j)))

variable {n : ℕ} {js : List ℕ} {i : ℕ}

theorem inTree_leaf {j : ℕ} (hj : j ∈ js) (hn : j < n) : inTree n js (n + j) :=
  ⟨by omega, j, hj, onPath_self _⟩

/-- A position of `TREE` lies below `2n` (`merkle_tree.h` line 80) when the indices are below
`n`. -/
theorem lt_of_inTree (hjs : ∀ j ∈ js, j < n) (h : inTree n js i) : i < 2 * n := by
  obtain ⟨-, j, hj, hp⟩ := h
  have := hp.le
  have := hjs j hj
  omega

/-- The C++ rule at a leaf position (`merkle_tree.h` lines 83–88): `n + j` is in `TREE` exactly
for the opened indices `j`. -/
theorem inTree_leaf_iff (hjs : ∀ j ∈ js, j < n) (hi : n ≤ i) :
    inTree n js i ↔ ∃ j ∈ js, n + j = i := by
  constructor
  · rintro ⟨-, j, hj, m, hm⟩
    refine ⟨j, hj, ?_⟩
    cases m with
    | zero => simpa using hm
    | succ m =>
      have h1 : (n + j) / 2 ^ (m + 1) ≤ (n + j) / 2 :=
        Nat.div_le_div_left (by
          calc 2 = 2 ^ 1 := rfl
            _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)) (by norm_num)
      have := hjs j hj
      omega
  · rintro ⟨j, hj, rfl⟩
    exact inTree_leaf hj (hjs j hj)

/-- The C++ rule at an inner node (`merkle_tree.h` lines 90–93): `i` is in `TREE` exactly when a
child is. -/
theorem inTree_node_iff (hi : 1 ≤ i) (hin : i < n) :
    inTree n js i ↔ inTree n js (2 * i) ∨ inTree n js (2 * i + 1) := by
  constructor
  · rintro ⟨-, j, hj, hp⟩
    rcases hp.child (by omega) with h | h
    · exact Or.inl ⟨by omega, j, hj, h⟩
    · exact Or.inr ⟨by omega, j, hj, h⟩
  · rintro (⟨-, j, hj, hp⟩ | ⟨-, j, hj, hp⟩)
    · exact ⟨hi, j, hj, by simpa using hp.parent⟩
    · exact ⟨hi, j, hj, by simpa [show (2 * i + 1) / 2 = i by omega] using hp.parent⟩

/-- The parent of a position `i ≥ 2` of `TREE` is an inner node of `TREE`. -/
theorem inTree_parent (hjs : ∀ j ∈ js, j < n) (h : inTree n js i) (hi : 2 ≤ i) :
    inTree n js (i / 2) ∧ i / 2 < n := by
  have hlt := lt_of_inTree hjs h
  obtain ⟨-, j, hj, hp⟩ := h
  exact ⟨⟨by omega, j, hj, hp.parent⟩, by omega⟩

/-- The child of an inner node `i` of `TREE` that the proof carries: the left child `2i` if it
is outside `TREE`, else the right child `2i + 1` if it is outside, else none
(`merkle_tree.h` lines 179–185). -/
def sibling (n : ℕ) (js : List ℕ) (i : ℕ) : Option ℕ :=
  if inTree n js (2 * i) then (if inTree n js (2 * i + 1) then none else some (2 * i + 1))
  else some (2 * i)

/-- The positions whose digests the proof carries, in the proof's order: for each position
`i = n - 1, …, 1` of `TREE`, its child outside `TREE`, if any (`merkle_tree.h` lines 177–193;
the prover pushes in the same order, lines 132–143). -/
def sibNodes (n : ℕ) (js : List ℕ) : List ℕ :=
  ((List.range n).reverse.filter fun i => decide (inTree n js i)).filterMap (sibling n js)

/-- The digest of an inner node from its children's digests: one `node` query when both are
defined, `none` otherwise (`merkle_tree.h` lines 207–210). -/
def hashPair : Option (Digest k) → Option (Digest k) →
    GordieHowe.OracleProg (Query k kN kS L) (Out k e) (Option (Digest k))
  | some a, some b => .query (.node a b) fun w => .pure (some w.digest)
  | _, _ => .pure none

/-- **The digest the C++ verifier reconstructs at heap position `i`** (`merkle_tree.h` lines
198–213), with the leaf digests `lv j` of the opened indices and the proof digests `sv s` of the
proof positions: at a leaf position of `TREE`, its leaf digest; at an inner node of `TREE`, the
hash of the children's digests (`hashPair`); elsewhere, the proof digest of the position, if
any. -/
def reconProg (n : ℕ) (js : List ℕ) (lv sv : ℕ → Option (Digest k)) :
    ℕ → GordieHowe.OracleProg (Query k kN kS L) (Out k e) (Option (Digest k))
  | i =>
    if hi : inTree n js i then
      if hn : n ≤ i then .pure (lv (i - n))
      else (reconProg n js lv sv (2 * i)).bind fun a =>
        (reconProg n js lv sv (2 * i + 1)).bind fun b => hashPair a b
    else .pure (sv i)
termination_by i => 2 * n - i
decreasing_by all_goals (have := hi.1; omega)

variable {lv sv : ℕ → Option (Digest k)}

theorem reconProg_of_not_inTree (h : ¬ inTree n js i) :
    (reconProg n js lv sv i : GordieHowe.OracleProg (Query k kN kS L) (Out k e) _) = .pure (sv i) := by
  rw [reconProg, dif_neg h]

theorem reconProg_leaf (h : inTree n js i) (hn : n ≤ i) :
    (reconProg n js lv sv i : GordieHowe.OracleProg (Query k kN kS L) (Out k e) _) = .pure (lv (i - n)) := by
  rw [reconProg, dif_pos h, dif_pos hn]

theorem reconProg_node (h : inTree n js i) (hn : ¬ n ≤ i) :
    (reconProg n js lv sv i : GordieHowe.OracleProg (Query k kN kS L) (Out k e) _) =
      (reconProg n js lv sv (2 * i)).bind fun a =>
        (reconProg n js lv sv (2 * i + 1)).bind fun b => hashPair a b := by
  rw [reconProg, dif_pos h, dif_neg hn]

variable (h : Query k kN kS L → Out k e)

/-- An inner node's digest is defined only when both children's are, and it is then the digest
of the `node` query on them, the last query of the node's program. -/
theorem run_reconProg_node (hi : inTree n js i) (hn : ¬ n ≤ i) {v : Digest k}
    (hv : (reconProg n js lv sv i).run h = some v) :
    ∃ a b, (reconProg n js lv sv (2 * i)).run h = some a ∧
      (reconProg n js lv sv (2 * i + 1)).run h = some b ∧ v = (h (.node a b)).digest ∧
      (reconProg n js lv sv i).trace h = (reconProg n js lv sv (2 * i)).trace h ++
        ((reconProg n js lv sv (2 * i + 1)).trace h ++ [.node a b]) := by
  rw [reconProg_node hi hn] at hv ⊢
  simp only [GordieHowe.OracleProg.run_bind, GordieHowe.OracleProg.trace_bind] at hv ⊢
  cases ha : (reconProg n js lv sv (2 * i)).run h with
  | none => rw [ha] at hv; simp [hashPair] at hv
  | some a =>
    cases hb : (reconProg n js lv sv (2 * i + 1)).run h with
    | none => rw [ha, hb] at hv; simp [hashPair] at hv
    | some b =>
      rw [ha, hb] at hv
      simp only [hashPair, GordieHowe.OracleProg.run_query, GordieHowe.OracleProg.run_pure, Option.some_inj] at hv
      exact ⟨a, b, rfl, rfl, hv.symm, by simp [hashPair]⟩

/-- The one-tree program: the leaf queries of the opened leaves `lvs` in order
(`merkle_commitment.h` lines 99–106), then the reconstruction at the root with the leaf digests
at the indices `js` and the proof digests `path` at the proof positions. -/
def treeProg (n : ℕ) (js : List ℕ) (lvs : List (MerkleLeaf kN L))
    (path : List (Digest k)) : GordieHowe.OracleProg (Query k kN kS L) (Out k e) (Option (Digest k)) :=
  (GordieHowe.OracleProg.queryAll (lvs.map fun a => Query.leaf a.salt a.column)).bind fun ws =>
    reconProg n js (lookupAns js (ws.map Out.digest)) (lookupAns (sibNodes n js) path) 1

/-- The leaf digests of the opened leaves under `h`, read at the indices. -/
def leafDigests (js : List ℕ) (lvs : List (MerkleLeaf kN L)) :
    ℕ → Option (Digest k) :=
  lookupAns js (lvs.map fun a => (h (.leaf a.salt a.column)).digest)

theorem run_treeProg (lvs : List (MerkleLeaf kN L)) (path : List (Digest k)) :
    (treeProg n js lvs path).run h =
      (reconProg n js (leafDigests h js lvs) (lookupAns (sibNodes n js) path) 1).run h := by
  simp [treeProg, leafDigests]
  rfl

theorem trace_treeProg (lvs : List (MerkleLeaf kN L)) (path : List (Digest k)) :
    (treeProg n js lvs path).trace h = lvs.map (fun a => Query.leaf a.salt a.column) ++
      (reconProg n js (leafDigests h js lvs) (lookupAns (sibNodes n js) path) 1).trace h := by
  simp [treeProg, leafDigests]
  rfl

/-- **The compressed-multiproof format**: the proof positions `sibNodes n js` and the C++
verifier's program `treeProg`. Its acceptance `format.check` is that of
`BasicMerkleCommitmentVerifier::verify` (`merkle_commitment.h` lines 95–111, and
`verify_compressed_proof`, `merkle_tree.h` lines 165–214): the indices are distinct and below `n`
(lines 84–86, where the C++ panics), there is one leaf per index, the path has one digest per
proof position (lines 186–195), and the reconstructed root is the root (line 213). An honest
multiproof of a tree with at most `B` leaves has at most `B` digests (`length_sibNodes_le`). -/
def format : MerkleFormat k kN kS L e where
  sibs := sibNodes
  treeProg := treeProg
  pathCap B := B

/-! ### Extraction -/

variable {D : ODB k kN kS L e}

/-- In a collision-free database recording the queries of an accepted reconstruction, every
position of `TREE` has the extracted label, and the reconstructed digest there is defined and
its queries are among the root's. -/
theorem label_of_reconProg (hcol : D ∉ digestCollision) {rt : Digest k}
    (hjs : ∀ j ∈ js, j < n) (hrt : (reconProg n js lv sv 1).run h = some rt)
    (hq : ∀ q ∈ (reconProg n js lv sv 1).trace h, D.lookup q = some (h q)) :
    ∀ i, inTree n js i →
      label D n rt i = (reconProg n js lv sv i).run h ∧
        ((reconProg n js lv sv i).run h).isSome ∧
        (reconProg n js lv sv i).trace h ⊆ (reconProg n js lv sv 1).trace h := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h1 : i = 1
    · subst h1
      rw [label_one, hrt]
      exact ⟨rfl, rfl, fun _ h => h⟩
    have hi2 : 2 ≤ i := by have := hi.1; omega
    obtain ⟨hp, hpn⟩ := inTree_parent hjs hi hi2
    obtain ⟨hlp, hsp, htp⟩ := ih (i / 2) (by omega) hp
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hsp
    obtain ⟨a, b, ha, hb, rfl, htr⟩ := run_reconProg_node h hp (by omega) hv
    have hnode : D.lookup (.node a b) = some (h (.node a b)) :=
      hq _ (htp (by rw [htr]; simp))
    have hch : children D (h (.node a b)).digest = some ⟨a, b⟩ := by
      rw [children, preimage_eq_of_lookup hcol hnode]
      rfl
    obtain ⟨p', rfl⟩ : ∃ p', i = p' + 2 := ⟨i - 2, by omega⟩
    rw [label_succ_succ, if_pos hpn, hlp, hv, Option.bind_some, hch, Option.map_some]
    rcases Nat.even_or_odd' (p' + 2) with ⟨c, hc | hc⟩
    · have hc2 : (p' + 2) / 2 = c := by omega
      rw [hc2] at ha htr htp
      rw [hc] at ⊢
      simp only [selectChild, Nat.mul_mod_right, ↓reduceIte, ha, Option.isSome_some, true_and]
      exact fun q hq' => htp (by rw [htr]; exact List.mem_append_left _ hq')
    · have hc2 : (p' + 2) / 2 = c := by omega
      rw [hc2] at hb htr htp
      rw [hc] at ⊢
      simp only [selectChild, show (2 * c + 1) % 2 = 1 by omega, one_ne_zero, ↓reduceIte, hb,
        Option.isSome_some, true_and]
      exact fun q hq' => htp (by
        rw [htr]; exact List.mem_append_right _ (List.mem_append_left _ hq'))

/-- **The Merkle part of CMS19 Proposition 8.12** (p. 42) for compressed multiproofs: an
accepted multiproof whose queries are recorded in a collision-free database opens, at each index,
the leaf that `extract` reads. -/
theorem leafAt_of_check (hcol : D ∉ digestCollision) {rt : Digest k}
    {lvs : List (MerkleLeaf kN L)} {path : List (Digest k)}
    (hq : ∀ q ∈ (treeProg n js lvs path).trace h, D.lookup q = some (h q))
    (hc : format.check h n rt js lvs path) {j : ℕ} {a : MerkleLeaf kN L} (hja : (j, a) ∈ js.zip lvs)
    (hj : j < n) : leafAt D n rt ⟨j, hj⟩ = some a := by
  obtain ⟨hnd, hjs, -, -, hrt⟩ := hc
  change (treeProg n js lvs path).run h = some rt at hrt
  rw [run_treeProg] at hrt
  rw [trace_treeProg] at hq
  have hjm : j ∈ js := (List.of_mem_zip hja).1
  obtain ⟨hl, -, -⟩ := label_of_reconProg h hcol hjs hrt
    (fun q hq' => hq q (List.mem_append_right _ hq')) (n + j) (inTree_leaf hjm hj)
  rw [reconProg_leaf (inTree_leaf hjm hj) (by omega), GordieHowe.OracleProg.run_pure,
    show n + j - n = j by omega, leafDigests,
    lookupAns_map (fun a : MerkleLeaf kN L => (h (Query.leaf a.salt a.column)).digest) js lvs j,
    lookupAns_of_mem_zip hnd hja, Option.map_some] at hl
  have hleaf : D.lookup (.leaf a.salt a.column) = some (h (.leaf a.salt a.column)) :=
    hq _ (List.mem_append_left _ (List.mem_map.2 ⟨a, (List.of_mem_zip hja).2, rfl⟩))
  rw [leafAt, hl, Option.bind_some, Merkle.opening, preimage_eq_of_lookup hcol hleaf]
  rfl

/-! ### The honest multiproof -/

section Honest

open MerkleTree

/-- The root position is in `TREE` when some index is opened. -/
theorem inTree_one {j : ℕ} (hj : j ∈ js) (hjn : j < n) : inTree n js 1 := by
  refine ⟨le_rfl, j, hj, Nat.log 2 (n + j), ?_⟩
  have h0 : n + j ≠ 0 := by omega
  have h1 := Nat.pow_log_le_self 2 h0
  have h2 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (n + j)
  rw [pow_succ] at h2
  have hp : 0 < 2 ^ Nat.log 2 (n + j) := by positivity
  refine le_antisymm ?_ ((Nat.le_div_iff_mul_le hp).2 (by omega))
  exact Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hp).2 (by omega))

/-- A child of an inner node of `TREE` that is not in `TREE` is a proof position. -/
theorem mem_sibNodes {i c : ℕ} (hi : inTree n js i) (hn : i < n) (hc : c = 2 * i ∨ c = 2 * i + 1)
    (hnc : ¬ inTree n js c) : c ∈ sibNodes n js := by
  classical
  refine List.mem_filterMap.2 ⟨i, List.mem_filter.2 ⟨List.mem_reverse.2 (List.mem_range.2 hn),
    by simpa using hi⟩, ?_⟩
  rcases hc with rfl | rfl
  · simp [sibling, hnc]
  · have h2 : inTree n js (2 * i) :=
      ((inTree_node_iff hi.1 hn).1 hi).resolve_right hnc
    simp [sibling, h2, hnc]

variable {lf : ℕ → MerkleLeaf kN L} {lvs : List (MerkleLeaf kN L)}

/-- **The reconstruction of the honest multiproof is the honest tree**: at every position of
`TREE`, with the honest leaves at the indices and the honest path, the C++ verifier's digest is
the honest digest. -/
theorem run_reconProg_honest (hjs : ∀ j ∈ js, j < n)
    (hlv : List.Forall₂ (fun j a => a = lf j) js lvs) :
    ∀ i, inTree n js i → (reconProg n js (leafDigests h js lvs)
      (lookupAns (sibNodes n js) (format.path h n js lf)) i).run h = some (treeDigest h n lf i)
  | i, hi => by
    by_cases hn : n ≤ i
    · rw [reconProg_leaf hi hn, GordieHowe.OracleProg.run_pure, treeDigest_leaf h lf hn]
      obtain ⟨j, hj, rfl⟩ := (inTree_leaf_iff hjs hn).1 hi
      rw [show n + j - n = j by omega, leafDigests,
        lookupAns_map (fun a : MerkleLeaf kN L => (h (Query.leaf a.salt a.column)).digest) js lvs j,
        lookupAns_of_forall₂ (V := fun j => some (lf j))
          (hlv.imp fun _ _ h => h.symm ▸ rfl) j hj]
      rfl
    · have hchild : ∀ c, (c = 2 * i ∨ c = 2 * i + 1) → (reconProg n js (leafDigests h js lvs)
          (lookupAns (sibNodes n js) (format.path h n js lf)) c).run h = some (treeDigest h n lf c) := by
        intro c hc
        have := hi.1
        by_cases hct : inTree n js c
        · exact run_reconProg_honest hjs hlv c hct
        · rw [reconProg_of_not_inTree hct, GordieHowe.OracleProg.run_pure, MerkleFormat.path]
          exact lookupAns_map_self _ (mem_sibNodes hi (by omega) hc hct)
      rw [reconProg_node hi hn]
      simp only [GordieHowe.OracleProg.run_bind, hchild (2 * i) (Or.inl rfl),
        hchild (2 * i + 1) (Or.inr rfl), hashPair, GordieHowe.OracleProg.run_query, GordieHowe.OracleProg.run_pure]
      rw [treeDigest_node h lf (by omega) hi.1]
termination_by i => 2 * n - i
decreasing_by all_goals (have := hi.1; omega)

/-- **Completeness of the compressed multiproof**: the honest leaves at distinct indices below
`n`, at least one, with the honest path, are accepted against the honest root. -/
theorem check_path (hnd : js.Nodup) (hjs : ∀ j ∈ js, j < n) (hne : js ≠ [])
    (hlv : List.Forall₂ (fun j a => a = lf j) js lvs) :
    format.check h n (root h n lf) js lvs (format.path h n js lf) := by
  obtain ⟨j, hj⟩ := List.exists_mem_of_ne_nil js hne
  refine ⟨hnd, hjs, hlv.length_eq.symm, by simp [MerkleFormat.path, format], ?_⟩
  change (treeProg n js lvs (format.path h n js lf)).run h = some (root h n lf)
  rw [run_treeProg]
  exact run_reconProg_honest h hjs hlv 1 (inTree_one hj (hjs j hj))

end Honest

/-! ### The query count -/

/-- The opened indices whose leaf lies below position `i`. -/
def below (n : ℕ) (js : List ℕ) (i : ℕ) : ℕ :=
  js.countP fun j => decide (OnPath i (n + j))

theorem below_pos (hi : inTree n js i) : 0 < below n js i := by
  obtain ⟨-, j, hj, hp⟩ := hi
  exact List.countP_pos_iff.2 ⟨j, hj, by simpa using hp⟩

/-- `countP` of two disjoint predicates implying a third. -/
theorem countP_add_le {α : Type*} {p q r : α → Bool} :
    ∀ l : List α, (∀ x ∈ l, ¬ (p x ∧ q x)) → (∀ x ∈ l, p x ∨ q x → r x) →
      l.countP p + l.countP q ≤ l.countP r
  | [], _, _ => by simp
  | x :: l, hd, hr => by
    have ih := countP_add_le l (fun y hy => hd y (List.mem_cons_of_mem _ hy))
      (fun y hy => hr y (List.mem_cons_of_mem _ hy))
    have hx := hd x (List.mem_cons_self)
    have hrx := hr x (List.mem_cons_self)
    simp only [List.countP_cons]
    by_cases hp : p x <;> by_cases hq : q x <;> simp_all <;> omega

theorem below_children_le (hi : 1 ≤ i) :
    below n js (2 * i) + below n js (2 * i + 1) ≤ below n js i := by
  classical
  refine countP_add_le js (fun j _ hj => ?_) (fun j _ hj => ?_)
  · simp only [decide_eq_true_eq] at hj
    exact not_onPath_both hi hj.1 hj.2
  · simp only [decide_eq_true_eq] at hj ⊢
    rcases hj with hj | hj
    · simpa using hj.parent
    · simpa [show (2 * i + 1) / 2 = i by omega] using hj.parent

theorem below_le_length : below n js i ≤ js.length := List.countP_le_length

/-- `hashPair` makes at most one query. -/
theorem length_trace_hashPair_le (a b : Option (Digest k)) :
    ((hashPair a b : GordieHowe.OracleProg (Query k kN kS L) (Out k e) _).trace h).length ≤ 1 := by
  cases a <;> cases b <;> simp [hashPair]

/-- The reconstruction below position `i ≥ 1` makes at most `below i · (⌊log₂ 2n⌋ - ⌊log₂ i⌋)`
node queries. -/
theorem length_trace_reconProg_le (hjs : ∀ j ∈ js, j < n) (i : ℕ) (hi1 : 1 ≤ i) :
    ((reconProg n js lv sv i).trace h).length + below n js i * Nat.log 2 i ≤
      below n js i * Nat.log 2 (2 * n) := by
  by_cases hi : inTree n js i
  · by_cases hn : n ≤ i
    · rw [reconProg_leaf hi hn, GordieHowe.OracleProg.trace_pure, List.length_nil, zero_add]
      exact Nat.mul_le_mul_left _ (Nat.log_mono_right (lt_of_inTree hjs hi).le)
    · rw [reconProg_node hi hn]
      simp only [GordieHowe.OracleProg.trace_bind, List.length_append]
      have h0 := length_trace_reconProg_le hjs (2 * i) (by omega)
      have h1 := length_trace_reconProg_le hjs (2 * i + 1) (by omega)
      have hl0 : Nat.log 2 (2 * i) = Nat.log 2 i + 1 := by
        rw [Nat.log_of_one_lt_of_le (by norm_num) (by omega), show 2 * i / 2 = i by omega]
      have hl1 : Nat.log 2 (2 * i + 1) = Nat.log 2 i + 1 := by
        rw [Nat.log_of_one_lt_of_le (by norm_num) (by omega), show (2 * i + 1) / 2 = i by omega]
      rw [hl0] at h0
      rw [hl1] at h1
      have hH : Nat.log 2 i + 1 ≤ Nat.log 2 (2 * n) := by
        rw [← hl0]
        exact Nat.log_mono_right (by omega)
      have hsum := below_children_le (n := n) (js := js) hi1
      have hpos : 0 < below n js (2 * i) + below n js (2 * i + 1) := by
        rcases (inTree_node_iff hi1 (show i < n by omega)).1 hi with h' | h'
        · have := below_pos h'; omega
        · have := below_pos h'; omega
      have hq := length_trace_hashPair_le h
        ((reconProg n js lv sv (2 * i)).run h) ((reconProg n js lv sv (2 * i + 1)).run h)
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hH
      obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hsum
      rw [hd] at h0 h1 ⊢
      rw [hr]
      nlinarith
  · have h0 : below n js i = 0 :=
      List.countP_eq_zero.2 fun j hj hp => hi ⟨hi1, j, hj, by simpa using hp⟩
    rw [reconProg_of_not_inTree hi, h0]
    simp
termination_by 2 * n - i
decreasing_by all_goals omega

/-- **The queries of one tree**: at most `|js| · (1 + ⌊log₂ 2n⌋)` for indices below `n` and one
leaf per index, the count of one authentication path per opened leaf. -/
theorem length_trace_treeProg_le (hjs : ∀ j ∈ js, j < n) {lvs : List (MerkleLeaf kN L)}
    (hl : lvs.length = js.length) (path : List (Digest k)) :
    ((treeProg n js lvs path).trace h).length ≤ js.length * (1 + Nat.log 2 (2 * n)) := by
  rw [trace_treeProg, List.length_append, List.length_map, hl]
  have := length_trace_reconProg_le h (lv := leafDigests h js lvs)
    (sv := lookupAns (sibNodes n js) path) hjs 1 le_rfl
  rw [Nat.log_one_right, mul_zero, add_zero] at this
  have hb := below_le_length (n := n) (js := js) (i := 1)
  have := Nat.mul_le_mul_right (Nat.log 2 (2 * n)) hb
  rw [mul_add, mul_one]
  omega


/-! ### The format's laws -/

/-- A proof position lies in `[2, 2n)`: it is a child of an inner position below `n`. -/
theorem mem_sibNodes_bounds {c : ℕ} (hc : c ∈ sibNodes n js) : 2 ≤ c ∧ c < 2 * n := by
  classical
  obtain ⟨i, hi, hs⟩ := List.mem_filterMap.1 hc
  obtain ⟨hir, hit⟩ := List.mem_filter.1 hi
  have hin : i < n := List.mem_range.1 (List.mem_reverse.1 hir)
  have h1 : 1 ≤ i := (of_decide_eq_true hit).1
  unfold sibling at hs
  split_ifs at hs <;> (simp only [Option.some.injEq] at hs) <;> omega

/-- A compressed multiproof of a tree with `n` leaves has at most `n` digests (one per inner node
at most). -/
theorem length_sibNodes_le (n : ℕ) (js : List ℕ) : (sibNodes n js).length ≤ n := by
  rw [sibNodes]
  refine (List.length_filterMap_le _ _).trans ((List.length_filter_le _ _).trans ?_)
  simp

/-- `hashPair` makes only `node` queries. -/
theorem node_of_mem_trace_hashPair {a b : Option (Digest k)} {q : Query k kN kS L}
    (hq : q ∈ (hashPair a b : GordieHowe.OracleProg (Query k kN kS L) (Out k e) _).trace h) :
    ∃ l r, q = .node l r := by
  rcases a with _ | a <;> rcases b with _ | b <;> simp [hashPair] at hq
  exact ⟨a, b, hq⟩

/-- The reconstruction makes only `node` queries. -/
theorem node_of_mem_trace_reconProg {q : Query k kN kS L} :
    ∀ i, q ∈ (reconProg n js lv sv i).trace h → ∃ l r, q = .node l r := by
  intro i
  induction hm : 2 * n - i using Nat.strong_induction_on generalizing i with
  | _ m ih =>
    rw [reconProg]
    split_ifs with ht hn
    · simp
    · simp only [GordieHowe.OracleProg.trace_bind, List.mem_append]
      have h1 := ht.1
      rintro (hq | hq | hq)
      · exact ih (2 * n - 2 * i) (by omega) (2 * i) rfl hq
      · exact ih (2 * n - (2 * i + 1)) (by omega) (2 * i + 1) rfl hq
      · exact node_of_mem_trace_hashPair h hq
    · simp

/-- **The multiproof program makes only `leaf` and `node` queries.** -/
theorem merkle_of_mem_trace_treeProg {lvs : List (MerkleLeaf kN L)} {path : List (Digest k)}
    {q : Query k kN kS L} (hq : q ∈ (treeProg n js lvs path).trace h) :
    (∃ a b, q = .leaf a b) ∨ ∃ l r, q = .node l r := by
  rw [trace_treeProg] at hq
  rcases List.mem_append.1 hq with hq | hq
  · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hq
    exact Or.inl ⟨a.salt, a.column, rfl⟩
  · exact Or.inr (node_of_mem_trace_reconProg h 1 hq)

/-- **The compressed multiproof as a Merkle opening format** (`MerkleOpening`): the format
`format` with its laws. The configurations' compilers open their trees with it, as the C++ does. -/
def opening : MerkleOpening k kN kS L e where
  toMerkleFormat := format
  sibs_bounds := mem_sibNodes_bounds
  length_sibs_le := fun _ _ hn => (length_sibNodes_le _ _).trans hn
  merkle_of_mem_trace := fun hq => merkle_of_mem_trace_treeProg _ hq
  length_trace_le := fun h _ _ _ path hjs hl => length_trace_treeProg_le h hjs hl path
  leafAt_of_check := fun hcol hq hc _ _ hja hj => leafAt_of_check _ hcol hq hc hja hj
  check_path := fun h _ _ _ _ hnd hjs hne hlv => check_path h hnd hjs hne hlv

end Multiproof

end GordieHowe.SPBCS