-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Merkle.Extract

@[expose] public section

/-!
# Merkle trees in the heap layout

The objects shared by every Merkle opening format (`GordieHowe/SPBCS/Merkle/Opening.lean`): the heap layout of
`GordieHowe/SPBCS/Merkle/Extract.lean` (root at position `1`, inner node `i < n` over `2i` and `2i + 1`, leaf
`j < n` at position `n + j`), its paths to the root, and the honest tree.

- `lookupAns ps as p` reads an answer list against its positions.
- `OnPath i p`: heap position `i` is `p` or an ancestor of `p`.
- `MerkleTree.nodeDigest h n ld`: the tree over the leaf digests `ld`, one `node` query per inner
  node; `MerkleTree.treeDigest h n lf` the honest tree over the leaves `lf` (`BasicMerkleTree`,
  `lib/merkle/merkle_tree.h` lines 105–117 and 148–153), `MerkleTree.root` its root.
-/

namespace GordieHowe.SPBCS
open GordieHowe.QROM

open GordieHowe.IOP

variable {k kN kS L e : ℕ}

/-! ### Answers read against their positions -/

section LookupAns

variable {α β : Type*} [DecidableEq α]

/-- The answer recorded at position `p`: the first answer paired with `p`. -/
def lookupAns (ps : List α) (as : List β) (p : α) : Option β :=
  ((ps.zip as).find? fun pa => decide (pa.1 = p)).map Prod.snd

/-- An answer list read against its positions returns the answer of every listed position. -/
theorem lookupAns_of_forall₂ {V : α → Option β} :
    ∀ {ps : List α} {as : List β}, List.Forall₂ (fun p a => V p = some a) ps as →
      ∀ p ∈ ps, lookupAns ps as p = V p
  | _, _, .nil, _, hp => absurd hp (List.not_mem_nil)
  | p₀ :: _, a₀ :: _, .cons h₀ hrest, p, hp => by
    classical
    unfold lookupAns
    by_cases he : p₀ = p
    · subst he
      simp [h₀]
    · rw [List.zip_cons_cons, List.find?_cons_of_neg (by simpa using he)]
      exact lookupAns_of_forall₂ hrest p ((List.mem_cons.1 hp).resolve_left (Ne.symm he))

/-- With distinct positions, the answer read at a position is the answer paired with it. -/
theorem lookupAns_of_mem_zip :
    ∀ {ps : List α} {as : List β} {p : α} {a : β}, ps.Nodup → (p, a) ∈ ps.zip as →
      lookupAns ps as p = some a
  | [], _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | p₀ :: ps, a₀ :: as, p, a, hnd, h => by
    classical
    unfold lookupAns
    rw [List.zip_cons_cons, List.mem_cons] at h
    rcases h with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      simp
    · have hp : p ≠ p₀ := fun hp => (List.nodup_cons.1 hnd).1 (hp ▸ List.of_mem_zip h).1
      rw [List.zip_cons_cons, List.find?_cons_of_neg (by simpa using Ne.symm hp)]
      exact lookupAns_of_mem_zip (List.nodup_cons.1 hnd).2 h

/-- Answers listed as `f` of their positions are read back as `f`. -/
theorem lookupAns_map_self (f : α → β) :
    ∀ {ps : List α} {p : α}, p ∈ ps → lookupAns ps (ps.map f) p = some (f p)
  | [], _, h => absurd h (List.not_mem_nil)
  | p₀ :: ps, p, h => by
    classical
    unfold lookupAns
    by_cases he : p₀ = p
    · subst he
      simp
    · have ih := lookupAns_map_self f ((List.mem_cons.1 h).resolve_left (Ne.symm he))
      unfold lookupAns at ih
      rw [List.map_cons, List.zip_cons_cons, List.find?_cons_of_neg (by simpa using he)]
      exact ih

/-- Reading answers mapped by `f` is mapping the answer read. -/
theorem lookupAns_map {γ : Type*} (f : β → γ) :
    ∀ (ps : List α) (as : List β) (p : α),
      lookupAns ps (as.map f) p = (lookupAns ps as p).map f
  | [], _, _ => by simp [lookupAns]
  | _ :: _, [], _ => by simp [lookupAns]
  | p₀ :: ps, a₀ :: as, p => by
    classical
    have ih := lookupAns_map f ps as p
    unfold lookupAns at ih ⊢
    rw [List.map_cons, List.zip_cons_cons, List.zip_cons_cons]
    by_cases he : p₀ = p
    · simp [he]
    · rw [List.find?_cons_of_neg (by simpa using he), List.find?_cons_of_neg (by simpa using he)]
      exact ih

end LookupAns

/-! ### Paths to the root -/

/-- Heap position `i` is `p` or an ancestor of `p`: `p / 2^m = i` for some `m`. -/
def OnPath (i p : ℕ) : Prop := ∃ m, p / 2 ^ m = i

theorem onPath_self (p : ℕ) : OnPath p p := ⟨0, by simp⟩

/-- An ancestor of `p` is reached within `p + 2` halvings: beyond `p + 1` the quotient is `0`. -/
theorem onPath_iff_exists_lt (i p : ℕ) : OnPath i p ↔ ∃ m < p + 2, p / 2 ^ m = i := by
  constructor
  · rintro ⟨m, rfl⟩
    by_cases hm : m < p + 2
    · exact ⟨m, hm, rfl⟩
    · refine ⟨p + 1, by omega, ?_⟩
      have h1 : p < 2 ^ (p + 1) := (Nat.lt_two_pow_self).trans
        (Nat.pow_lt_pow_right (by norm_num) (by omega))
      have h2 : p < 2 ^ m := h1.trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.div_eq_of_lt h1, Nat.div_eq_of_lt h2]
  · rintro ⟨m, -, hm⟩
    exact ⟨m, hm⟩

/-- Being on the path to `p` is decided by the halvings of `p` (`onPath_iff_exists_lt`). -/
instance (i p : ℕ) : Decidable (OnPath i p) :=
  decidable_of_iff _ (onPath_iff_exists_lt i p).symm

theorem OnPath.le {i p : ℕ} (h : OnPath i p) : i ≤ p := by
  obtain ⟨m, rfl⟩ := h
  exact Nat.div_le_self _ _

/-- The parent of a position on the path is on the path. -/
theorem OnPath.parent {i p : ℕ} (h : OnPath i p) : OnPath (i / 2) p := by
  obtain ⟨m, rfl⟩ := h
  exact ⟨m + 1, by rw [pow_succ, Nat.div_div_eq_div_mul]⟩

/-- A proper ancestor of `p` is an ancestor or self of `p`'s parent. -/
theorem OnPath.of_lt {i p : ℕ} (h : OnPath i p) (hip : i < p) : OnPath i (p / 2) := by
  obtain ⟨m, rfl⟩ := h
  cases m with
  | zero => simp at hip
  | succ m => exact ⟨m, by rw [Nat.div_div_eq_div_mul, ← pow_succ']⟩

/-- A position on the path strictly below `p`'s level is the parent of a position on the path:
one of its two children. -/
theorem OnPath.child {i p : ℕ} (h : OnPath i p) (hip : i < p) :
    OnPath (2 * i) p ∨ OnPath (2 * i + 1) p := by
  obtain ⟨m, rfl⟩ := h
  cases m with
  | zero => simp at hip
  | succ m =>
    have hc : p / 2 ^ m / 2 = p / 2 ^ (m + 1) := by rw [pow_succ, Nat.div_div_eq_div_mul]
    rcases Nat.even_or_odd' (p / 2 ^ m) with ⟨c, hc' | hc'⟩
    · left
      refine ⟨m, ?_⟩
      rw [hc', ← hc, hc']
      omega
    · right
      refine ⟨m, ?_⟩
      rw [hc', ← hc, hc']
      omega

/-- The two children of a position `i ≥ 1` are not both on the path to `p`. -/
theorem not_onPath_both {i p : ℕ} (hi : 1 ≤ i) (h0 : OnPath (2 * i) p)
    (h1 : OnPath (2 * i + 1) p) : False := by
  obtain ⟨m, hm⟩ := h0
  obtain ⟨m', hm'⟩ := h1
  rcases lt_trichotomy m m' with hlt | rfl | hgt
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have : p / 2 ^ (m + d + 1) = p / 2 ^ m / 2 ^ (d + 1) := by
      rw [Nat.div_div_eq_div_mul, ← pow_add]; ring_nf
    rw [this, hm] at hm'
    have h2 : 2 * i / 2 ^ (d + 1) ≤ 2 * i / 2 :=
      Nat.div_le_div_left (by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)) (by norm_num)
    omega
  · omega
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    have : p / 2 ^ (m' + d + 1) = p / 2 ^ m' / 2 ^ (d + 1) := by
      rw [Nat.div_div_eq_div_mul, ← pow_add]; ring_nf
    rw [this, hm'] at hm
    have h2 : (2 * i + 1) / 2 ^ (d + 1) ≤ (2 * i + 1) / 2 :=
      Nat.div_le_div_left (by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)) (by norm_num)
    omega

/-! ### The honest tree -/

namespace MerkleTree

variable (h : Query k kN kS L → Out k e)

/-- The digest of the leaf `(salt, column)`. -/
def leafDigest (a : MerkleLeaf kN L) : Digest k := (h (.leaf a.salt a.column)).digest

/-- **The tree over leaf digests** `ld` at heap position `i`: a leaf position `n + j` has the
digest `ld j`, an inner position `1 ≤ i < n` the digest of the `node` query on its children's
digests. Position `0` is unused (the all-zero digest). The honest tree (`treeDigest`) is this
tree over the leaves' digests; the zero-knowledge argument also uses it over digests that are
not hashes of given leaves. -/
def nodeDigest (n : ℕ) (ld : ℕ → Digest k) : ℕ → Digest k
  | i =>
    if hn : n ≤ i then ld (i - n)
    else if hi : i = 0 then fun _ => 0
    else (h (.node (nodeDigest n ld (2 * i)) (nodeDigest n ld (2 * i + 1)))).digest
termination_by i => n - i
decreasing_by all_goals omega

theorem nodeDigest_leaf {n i : ℕ} (ld : ℕ → Digest k) (hn : n ≤ i) :
    nodeDigest h n ld i = ld (i - n) := by
  rw [nodeDigest, dif_pos hn]

theorem nodeDigest_node {n i : ℕ} (ld : ℕ → Digest k) (hn : i < n) (hi : 1 ≤ i) :
    nodeDigest h n ld i =
      (h (.node (nodeDigest h n ld (2 * i)) (nodeDigest h n ld (2 * i + 1)))).digest := by
  rw [nodeDigest, dif_neg (by omega), dif_neg (by omega)]

/-- The tree over leaf digests reads the oracle only at `node` queries. -/
theorem nodeDigest_congr {h₁ h₂ : Query k kN kS L → Out k e}
    (hnode : ∀ l r, h₁ (.node l r) = h₂ (.node l r)) (n : ℕ) (ld : ℕ → Digest k) :
    ∀ i, nodeDigest h₁ n ld i = nodeDigest h₂ n ld i
  | i => by
    by_cases hn : n ≤ i
    · rw [nodeDigest_leaf h₁ ld hn, nodeDigest_leaf h₂ ld hn]
    · by_cases hi : i = 0
      · rw [nodeDigest, dif_neg hn, dif_pos hi, nodeDigest, dif_neg hn, dif_pos hi]
      · rw [nodeDigest_node h₁ ld (by omega) (by omega), nodeDigest_node h₂ ld (by omega) (by omega),
          nodeDigest_congr hnode n ld (2 * i), nodeDigest_congr hnode n ld (2 * i + 1), hnode]
termination_by i => n - i
decreasing_by all_goals omega

/-- **The honest tree's digest at heap position `i`** over the leaves `lf` (`BasicMerkleTree`,
`merkle_tree.h` lines 105–117 and 148–153): the tree over the leaves' digests (`nodeDigest`): a
leaf position `n + j` has the digest of leaf `j`, an inner position `1 ≤ i < n` the digest of the
`node` query on its children's digests. Position `0` is unused (the all-zero digest). -/
def treeDigest (n : ℕ) (lf : ℕ → MerkleLeaf kN L) : ℕ → Digest k :=
  nodeDigest h n fun j => leafDigest h (lf j)

/-- The root of the honest tree. -/
def root (n : ℕ) (lf : ℕ → MerkleLeaf kN L) : Digest k := treeDigest h n lf 1


theorem treeDigest_leaf {n i : ℕ} (lf : ℕ → MerkleLeaf kN L) (hn : n ≤ i) :
    treeDigest h n lf i = leafDigest h (lf (i - n)) :=
  nodeDigest_leaf h _ hn

theorem treeDigest_node {n i : ℕ} (lf : ℕ → MerkleLeaf kN L) (hn : i < n) (hi : 1 ≤ i) :
    treeDigest h n lf i =
      (h (.node (treeDigest h n lf (2 * i)) (treeDigest h n lf (2 * i + 1)))).digest :=
  nodeDigest_node h _ hn hi

/-- The honest tree reads the oracle only at `leaf` and `node` queries. -/
theorem treeDigest_congr {h₁ h₂ : Query k kN kS L → Out k e}
    (hleaf : ∀ a b, h₁ (.leaf a b) = h₂ (.leaf a b)) (hnode : ∀ l r, h₁ (.node l r) = h₂ (.node l r))
    (n : ℕ) (lf : ℕ → MerkleLeaf kN L) : ∀ i, treeDigest h₁ n lf i = treeDigest h₂ n lf i
  | i => by
    by_cases hn : n ≤ i
    · rw [treeDigest_leaf h₁ lf hn, treeDigest_leaf h₂ lf hn, leafDigest, leafDigest, hleaf]
    · by_cases hi : i = 0
      · rw [treeDigest, nodeDigest, dif_neg hn, dif_pos hi, treeDigest, nodeDigest, dif_neg hn,
          dif_pos hi]
      · rw [treeDigest_node h₁ lf (by omega) (by omega), treeDigest_node h₂ lf (by omega) (by omega),
          treeDigest_congr hleaf hnode n lf (2 * i), treeDigest_congr hleaf hnode n lf (2 * i + 1),
          hnode]
termination_by i => n - i
decreasing_by all_goals omega

/-- The honest root reads the oracle only at `leaf` and `node` queries. -/
theorem root_congr {h₁ h₂ : Query k kN kS L → Out k e}
    (hleaf : ∀ a b, h₁ (.leaf a b) = h₂ (.leaf a b)) (hnode : ∀ l r, h₁ (.node l r) = h₂ (.node l r))
    (n : ℕ) (lf : ℕ → MerkleLeaf kN L) : root h₁ n lf = root h₂ n lf :=
  treeDigest_congr hleaf hnode n lf 1


end MerkleTree

end GordieHowe.SPBCS
