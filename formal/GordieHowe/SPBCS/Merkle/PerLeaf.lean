-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Merkle.Opening

@[expose] public section

/-!
# Authentication paths

The Merkle opening format of paper `prot:generalized-bcs`: the proof carries, for each opened
leaf, its authentication path, and the verifier checks every path against the root. As a
`MerkleOpening` (`GordieHowe/SPBCS/Merkle/Opening.lean`), over the heap layout of
`GordieHowe/SPBCS/Merkle/Tree.lean`:

- `pathPos i`: the positions of the authentication path of heap position `i`, the siblings of `i`
  and of its ancestors below the root, from `i` upward; `authPos n j` those of leaf `j` of an
  `n`-leaf tree; `sibs n js` their concatenation over the opened indices `js`, in order. A proof's
  path digests for a tree are the authentication paths of its opened leaves, concatenated.
- `climbProg i d ds`: the root recomputed along a path from the digest `d` at position `i`, one
  `node` query per level; `leafRootProg` adds the leaf's `leaf` query; `rootsProg` recomputes the
  root of every opened leaf from its own segment of the path digests; `treeProg` returns their
  common root (`commonRoot`), or `none` when two differ.

The laws (`opening`): the verifier makes `1 + ⌊log₂ (n + j)⌋ ≤ 1 + ⌊log₂ 2n⌋` queries for the
opened leaf `j`; an accepted opening whose queries are recorded in a collision-free database opens
the leaves that `leafAt` reads (`leafAt_of_check`); the honest paths are accepted
(`check_path`). An opening of at most `B` leaves of a tree with at most `B` leaves carries at most
`B · ⌊log₂ 2B⌋` digests.
-/

namespace GordieHowe.SPBCS
open GordieHowe.QROM

variable {k kN kS L e : ℕ}

namespace PerLeaf

/-! ### Path positions -/

/-- The sibling of heap position `i`: `i + 1` at an even position, `i - 1` at an odd one. -/
def sibling (i : ℕ) : ℕ := if i % 2 = 0 then i + 1 else i - 1

/-- **The authentication path positions of heap position `i`**: the siblings of `i` and of its
ancestors below the root, from `i` upward. -/
def pathPos (i : ℕ) : List ℕ :=
  if 2 ≤ i then sibling i :: pathPos (i / 2) else []
termination_by i
decreasing_by omega

theorem pathPos_of_two_le {i : ℕ} (hi : 2 ≤ i) : pathPos i = sibling i :: pathPos (i / 2) := by
  rw [pathPos, if_pos hi]

theorem pathPos_of_lt_two {i : ℕ} (hi : i < 2) : pathPos i = [] := by
  rw [pathPos, if_neg (by omega)]

/-- A path from heap position `i` has `⌊log₂ i⌋` positions. -/
theorem length_pathPos (i : ℕ) : (pathPos i).length = Nat.log 2 i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hi : 2 ≤ i
    · rw [pathPos_of_two_le hi, List.length_cons, ih (i / 2) (by omega),
        Nat.log_of_one_lt_of_le (by norm_num) hi]
    · rw [pathPos_of_lt_two (by omega)]
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp

/-- The positions of a path from `i` lie in `[2, i + 1]`, and `i + 1` only at an even `i`. -/
theorem mem_pathPos_bounds : ∀ {i c : ℕ}, c ∈ pathPos i →
    2 ≤ c ∧ c ≤ i + 1 ∧ (c = i + 1 → i % 2 = 0)
  | i, c, hc => by
    by_cases hi : 2 ≤ i
    · rw [pathPos_of_two_le hi, List.mem_cons] at hc
      rcases hc with rfl | hc
      · unfold sibling
        split_ifs <;> omega
      · have := mem_pathPos_bounds hc
        omega
    · rw [pathPos_of_lt_two (by omega)] at hc
      exact absurd hc List.not_mem_nil
termination_by i => i
decreasing_by omega

/-- **The sibling of every ancestor-or-self `i ≥ 2` of `p` is on the path of `p`.** -/
theorem sibling_mem_pathPos {i p : ℕ} (h : OnPath i p) (hi : 2 ≤ i) : sibling i ∈ pathPos p := by
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    have hle := h.le
    rw [pathPos_of_two_le (by omega)]
    rcases Nat.lt_or_eq_of_le hle with hlt | rfl
    · exact List.mem_cons_of_mem _ (ih (p / 2) (by omega) (h.of_lt hlt))
    · exact List.mem_cons_self

/-- **The authentication path positions of leaf `j`** of an `n`-leaf tree: those of its heap
position `n + j`; none past the last leaf. -/
def authPos (n j : ℕ) : List ℕ := if j < n then pathPos (n + j) else []

theorem authPos_of_lt {n j : ℕ} (hj : j < n) : authPos n j = pathPos (n + j) := if_pos hj

/-- **The authentication path positions of the indices `js`**, concatenated in the order of
`js`. -/
def sibs (n : ℕ) (js : List ℕ) : List ℕ := js.flatMap (authPos n)

/-- The positions of an opening lie in `[2, 2n)`. -/
theorem mem_sibs_bounds {n : ℕ} {js : List ℕ} {c : ℕ} (hc : c ∈ sibs n js) : 2 ≤ c ∧ c < 2 * n := by
  obtain ⟨j, -, hc⟩ := List.mem_flatMap.1 hc
  unfold authPos at hc
  split_ifs at hc with hj
  · have := mem_pathPos_bounds hc
    omega
  · exact absurd hc List.not_mem_nil

/-- The path of a leaf of an `n`-leaf tree has at most `⌊log₂ 2n⌋` positions. -/
theorem length_authPos_le (n j : ℕ) : (authPos n j).length ≤ Nat.log 2 (2 * n) := by
  unfold authPos
  split_ifs with hj
  · rw [length_pathPos]
    exact Nat.log_mono_right (by omega)
  · simp

/-- An opening of `|js|` indices of an `n`-leaf tree has at most `|js| · ⌊log₂ 2n⌋` positions. -/
theorem length_sibs_le (n : ℕ) : ∀ js : List ℕ, (sibs n js).length ≤ js.length * Nat.log 2 (2 * n)
  | [] => by simp [sibs]
  | j :: js => by
    have ih := length_sibs_le n js
    have hj := length_authPos_le n j
    simp only [sibs, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    rw [Nat.succ_mul]
    omega

/-! ### The verifier's program -/

/-- **The root recomputed along an authentication path** from the digest `d` at heap position `i`
and the path digests `ds`, from `i` upward: one `node` query per level below the root, with the
running digest as the left child at an even position and as the right child at an odd one;
`none` when the path has fewer digests than levels. -/
def climbProg : ℕ → Digest k → List (Digest k) →
    GordieHowe.OracleProg (Query k kN kS L) (Out k e) (Option (Digest k))
  | i, d, ds =>
    if 2 ≤ i then
      match ds with
      | [] => .pure none
      | s :: ds' => .query (if i % 2 = 0 then .node d s else .node s d) fun w =>
          climbProg (i / 2) w.digest ds'
    else .pure (some d)
termination_by i => i
decreasing_by omega

variable {i : ℕ} {d : Digest k} {ds : List (Digest k)}

theorem climbProg_of_lt_two (hi : i < 2) :
    (climbProg i d ds : GordieHowe.OracleProg (Query k kN kS L) (Out k e) _) = .pure (some d) := by
  unfold climbProg
  rw [if_neg (by omega)]

theorem climbProg_nil (hi : 2 ≤ i) :
    (climbProg i d [] : GordieHowe.OracleProg (Query k kN kS L) (Out k e) _) = .pure none := by
  unfold climbProg
  rw [if_pos hi]

theorem climbProg_cons (hi : 2 ≤ i) (s : Digest k) :
    (climbProg i d (s :: ds) : GordieHowe.OracleProg (Query k kN kS L) (Out k e) _) =
      .query (if i % 2 = 0 then .node d s else .node s d) fun w =>
        climbProg (i / 2) w.digest ds := by
  conv_lhs => unfold climbProg
  rw [if_pos hi]

/-- The root recomputed from the opened leaf `a` at index `j` of an `n`-leaf tree and its
authentication path `seg`: the leaf's `leaf` query, then `climbProg` from its heap position. -/
def leafRootProg (n j : ℕ) (a : MerkleLeaf kN L) (seg : List (Digest k)) :
    GordieHowe.OracleProg (Query k kN kS L) (Out k e) (Option (Digest k)) :=
  .query (.leaf a.salt a.column) fun w => climbProg (n + j) w.digest seg

/-- **The roots recomputed from the opened leaves** `lvs` at the indices `js`, each from its own
segment of the path digests `path`: the next `|authPos n j|` digests for the index `j`. -/
def rootsProg (n : ℕ) : List ℕ → List (MerkleLeaf kN L) → List (Digest k) →
    GordieHowe.OracleProg (Query k kN kS L) (Out k e) (List (Option (Digest k)))
  | j :: js, a :: lvs, path =>
    (leafRootProg n j a (path.take (authPos n j).length)).bind fun r =>
      (rootsProg n js lvs (path.drop (authPos n j).length)).bind fun rs => .pure (r :: rs)
  | _, _, _ => .pure []

/-- **The common root** of the recomputed roots: the first when every root equals it, `none` when
two differ or there is none. -/
def commonRoot : List (Option (Digest k)) → Option (Digest k)
  | r :: rs => if ∀ x ∈ rs, x = r then r else none
  | [] => none

/-- A common root is the root of every opened leaf. -/
theorem eq_of_commonRoot_eq_some {rs : List (Option (Digest k))} {r : Digest k}
    (h : commonRoot rs = some r) : ∀ x ∈ rs, x = some r := by
  cases rs with
  | nil => simp [commonRoot] at h
  | cons r₀ rs =>
    simp only [commonRoot] at h
    split_ifs at h with hall
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h
    · exact (hall x hx).trans h

/-- The common root of roots that all equal `r` is `r`. -/
theorem commonRoot_of_forall_eq {rs : List (Option (Digest k))} {r : Option (Digest k)}
    (hne : rs ≠ []) (h : ∀ x ∈ rs, x = r) : commonRoot rs = r := by
  cases rs with
  | nil => exact absurd rfl hne
  | cons r₀ rs =>
    have h₀ := h r₀ List.mem_cons_self
    subst h₀
    simp only [commonRoot]
    rw [if_pos fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- The common root of equal roots is that root. -/
theorem commonRoot_replicate {r : Option (Digest k)} {m : ℕ} (hm : m ≠ 0) :
    commonRoot (List.replicate m r) = r := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  simp [commonRoot, List.replicate_succ, List.mem_replicate]

/-- **The per-leaf program**: the roots of every opened leaf from its authentication path, and
their common root. -/
def treeProg (n : ℕ) (js : List ℕ) (lvs : List (MerkleLeaf kN L)) (path : List (Digest k)) :
    GordieHowe.OracleProg (Query k kN kS L) (Out k e) (Option (Digest k)) :=
  (rootsProg n js lvs path).bind fun rs => .pure (commonRoot rs)

/-- **The authentication-path format** of paper `prot:generalized-bcs`: the path positions `sibs`
of the opened leaves and the per-leaf program `treeProg`. An opening of at most `B` leaves of a
tree with at most `B` leaves carries at most `B · ⌊log₂ 2B⌋` digests. -/
def format : MerkleFormat k kN kS L e where
  sibs := sibs
  treeProg := treeProg
  pathCap B := B * Nat.log 2 (2 * B)

/-! ### Queries -/

variable (h : Query k kN kS L → Out k e)

theorem node_of_mem_trace_climbProg {q : Query k kN kS L} :
    ∀ {i : ℕ} {d : Digest k} {ds : List (Digest k)}, q ∈ (climbProg i d ds).trace h →
      ∃ l r, q = .node l r
  | i, d, ds, hq => by
    by_cases hi : 2 ≤ i
    · cases ds with
      | nil => rw [climbProg_nil hi] at hq; exact absurd hq List.not_mem_nil
      | cons s ds =>
        rw [climbProg_cons hi, GordieHowe.OracleProg.trace_query, List.mem_cons] at hq
        rcases hq with rfl | hq
        · split_ifs
          · exact ⟨_, _, rfl⟩
          · exact ⟨_, _, rfl⟩
        · exact node_of_mem_trace_climbProg hq
    · rw [climbProg_of_lt_two (by omega)] at hq
      exact absurd hq List.not_mem_nil
termination_by i => i
decreasing_by omega

/-- Recomputing along a path from position `i` makes at most `⌊log₂ i⌋` queries. -/
theorem length_trace_climbProg_le :
    ∀ (i : ℕ) (d : Digest k) (ds : List (Digest k)),
      ((climbProg i d ds : GordieHowe.OracleProg (Query k kN kS L) (Out k e) _).trace h).length ≤
        Nat.log 2 i
  | i, d, ds => by
    by_cases hi : 2 ≤ i
    · cases ds with
      | nil => rw [climbProg_nil hi]; simp
      | cons s ds =>
        rw [climbProg_cons hi, GordieHowe.OracleProg.trace_query, List.length_cons,
          Nat.log_of_one_lt_of_le (by norm_num) hi]
        exact Nat.add_le_add_right (length_trace_climbProg_le (i / 2) _ ds) 1
    · rw [climbProg_of_lt_two (by omega)]
      simp
termination_by i => i
decreasing_by omega

theorem trace_treeProg (n : ℕ) (js : List ℕ) (lvs : List (MerkleLeaf kN L))
    (path : List (Digest k)) :
    (treeProg n js lvs path).trace h = (rootsProg n js lvs path).trace h := by
  simp [treeProg, GordieHowe.OracleProg.trace_bind]

theorem run_treeProg (n : ℕ) (js : List ℕ) (lvs : List (MerkleLeaf kN L)) (path : List (Digest k)) :
    (treeProg n js lvs path).run h = commonRoot ((rootsProg n js lvs path).run h) := by
  simp [treeProg, GordieHowe.OracleProg.run_bind]

/-- **The roots of the opened leaves along paths read from a digest function** `f` at their path
positions: the root of each opened leaf from its own path. -/
theorem run_rootsProg_flatMap (n : ℕ) (f : ℕ → Digest k) :
    ∀ {js : List ℕ} {lvs : List (MerkleLeaf kN L)}, lvs.length = js.length →
      (rootsProg n js lvs (js.flatMap fun j => (authPos n j).map f)).run h =
        (js.zip lvs).map fun ja => (leafRootProg n ja.1 ja.2 ((authPos n ja.1).map f)).run h
  | [], [], _ => by simp [rootsProg]
  | j :: js, a :: lvs, hl => by
    have hlen : (authPos n j).length = ((authPos n j).map f).length := by simp
    simp only [List.flatMap_cons, rootsProg, GordieHowe.OracleProg.run_bind,
      GordieHowe.OracleProg.run_pure]
    rw [hlen, List.take_left', List.drop_left', run_rootsProg_flatMap n f (by simpa using hl)]
    · rfl
    all_goals rfl
  | [], _ :: _, hl => by simp at hl
  | _ :: _, [], hl => by simp at hl

/-- The queries of the per-leaf program along paths read from a digest function `f`: those of
each opened leaf's program, in order. -/
theorem trace_rootsProg_flatMap (n : ℕ) (f : ℕ → Digest k) :
    ∀ {js : List ℕ} {lvs : List (MerkleLeaf kN L)}, lvs.length = js.length →
      (rootsProg n js lvs (js.flatMap fun j => (authPos n j).map f)).trace h =
        (js.zip lvs).flatMap fun ja => (leafRootProg n ja.1 ja.2 ((authPos n ja.1).map f)).trace h
  | [], [], _ => by simp [rootsProg]
  | j :: js, a :: lvs, hl => by
    have hlen : (authPos n j).length = ((authPos n j).map f).length := by simp
    simp only [List.flatMap_cons, rootsProg, GordieHowe.OracleProg.trace_bind,
      GordieHowe.OracleProg.trace_pure, List.append_nil]
    rw [hlen, List.take_left', List.drop_left', trace_rootsProg_flatMap n f (by simpa using hl)]
    · simp
    all_goals rfl
  | [], _ :: _, hl => by simp at hl
  | _ :: _, [], hl => by simp at hl

/-- **The per-leaf program makes only `leaf` and `node` queries.** -/
theorem merkle_of_mem_trace_rootsProg (n : ℕ) {q : Query k kN kS L} :
    ∀ {js : List ℕ} {lvs : List (MerkleLeaf kN L)} {path : List (Digest k)},
      q ∈ (rootsProg n js lvs path).trace h → (∃ a b, q = .leaf a b) ∨ ∃ l r, q = .node l r
  | j :: js, a :: lvs, path, hq => by
    simp only [rootsProg, GordieHowe.OracleProg.trace_bind, GordieHowe.OracleProg.trace_pure,
      List.append_nil, List.mem_append, leafRootProg, GordieHowe.OracleProg.trace_query,
      List.mem_cons] at hq
    rcases hq with (rfl | hq) | hq
    · exact Or.inl ⟨_, _, rfl⟩
    · exact Or.inr (node_of_mem_trace_climbProg h hq)
    · exact merkle_of_mem_trace_rootsProg n hq
  | [], _, _, hq => by simp [rootsProg] at hq
  | _ :: _, [], _, hq => by simp [rootsProg] at hq

theorem merkle_of_mem_trace_treeProg {n : ℕ} {js : List ℕ} {lvs : List (MerkleLeaf kN L)}
    {path : List (Digest k)} {q : Query k kN kS L} (hq : q ∈ (treeProg n js lvs path).trace h) :
    (∃ a b, q = .leaf a b) ∨ ∃ l r, q = .node l r := by
  rw [trace_treeProg] at hq
  exact merkle_of_mem_trace_rootsProg h n hq

/-- **At most `1 + ⌊log₂ 2n⌋` queries per opened leaf** below `n`. -/
theorem length_trace_rootsProg_le {n : ℕ} :
    ∀ {js : List ℕ} {lvs : List (MerkleLeaf kN L)} (path : List (Digest k)), (∀ j ∈ js, j < n) →
      ((rootsProg n js lvs path).trace h).length ≤ js.length * (1 + Nat.log 2 (2 * n))
  | j :: js, a :: lvs, path, hjs => by
    have ih := length_trace_rootsProg_le (lvs := lvs) (path.drop (authPos n j).length)
      fun j' hj' => hjs j' (List.mem_cons_of_mem _ hj')
    have hc := length_trace_climbProg_le (kS := kS) (L := L) (kN := kN) (e := e) h (n + j)
      (h (.leaf a.salt a.column)).digest (path.take (authPos n j).length)
    have hl : Nat.log 2 (n + j) ≤ Nat.log 2 (2 * n) :=
      Nat.log_mono_right (by have := hjs j List.mem_cons_self; omega)
    simp only [rootsProg, GordieHowe.OracleProg.trace_bind, GordieHowe.OracleProg.trace_pure,
      List.append_nil, List.length_append, leafRootProg, GordieHowe.OracleProg.trace_query,
      List.length_cons] at ih ⊢
    rw [Nat.succ_mul]
    omega
  | [], _, _, _ => by simp [rootsProg]
  | _ :: _, [], _, _ => by simp [rootsProg]

/-! ### Extraction -/

variable {D : ODB k kN kS L e}

/-- **An accepted path labels its positions**: in a collision-free database recording the queries
of a path from position `1 ≤ i < 2n` that reaches the root `r`, the digest extracted at `i` below
`r` is the path's starting digest. -/
theorem label_of_run_climbProg (hcol : D ∉ digestCollision) {n : ℕ} :
    ∀ {i : ℕ} {d r : Digest k} {ds : List (Digest k)}, 1 ≤ i → i < 2 * n →
      (climbProg i d ds).run h = some r →
      (∀ q ∈ (climbProg i d ds).trace h, D.lookup q = some (h q)) → label D n r i = some d
  | i, d, r, ds, hi1, hin, hrun, hq => by
    by_cases hi : 2 ≤ i
    · cases ds with
      | nil => rw [climbProg_nil hi] at hrun; simp at hrun
      | cons s ds =>
        rw [climbProg_cons hi, GordieHowe.OracleProg.run_query] at hrun
        rw [climbProg_cons hi, GordieHowe.OracleProg.trace_query] at hq
        set q₀ : Query k kN kS L := if i % 2 = 0 then .node d s else .node s d with hq₀
        have hlab := label_of_run_climbProg hcol (n := n) (i := i / 2) (by omega) (by omega) hrun
          fun q hq' => hq q (List.mem_cons_of_mem _ hq')
        have hch : children D (h q₀).digest = some (if i % 2 = 0 then ⟨d, s⟩ else ⟨s, d⟩) := by
          rw [children, preimage_eq_of_lookup hcol (hq q₀ List.mem_cons_self), hq₀]
          split_ifs <;> rfl
        obtain ⟨p, rfl⟩ : ∃ p, i = p + 2 := ⟨i - 2, by omega⟩
        rw [label_succ_succ, if_pos (by omega), hlab, Option.bind_some, hch, Option.map_some]
        unfold selectChild
        split_ifs <;> rfl
    · obtain rfl : i = 1 := by omega
      rw [climbProg_of_lt_two (by omega), GordieHowe.OracleProg.run_pure, Option.some_inj] at hrun
      rw [label_one, hrun]
termination_by i => i
decreasing_by omega

/-- **An accepted authentication path opens its leaf**: in a collision-free database recording
the queries of the opened leaf `a` at index `j < n` and its path reaching `r`, the leaf that
`leafAt` reads at `j` below `r` is `a`. -/
theorem leafAt_of_run_leafRootProg (hcol : D ∉ digestCollision) {n j : ℕ} (hj : j < n)
    {a : MerkleLeaf kN L} {seg : List (Digest k)} {r : Digest k}
    (hrun : (leafRootProg n j a seg).run h = some r)
    (hq : ∀ q ∈ (leafRootProg n j a seg).trace h, D.lookup q = some (h q)) :
    leafAt D n r ⟨j, hj⟩ = some a := by
  rw [leafRootProg, GordieHowe.OracleProg.run_query] at hrun
  rw [leafRootProg, GordieHowe.OracleProg.trace_query] at hq
  have hl := label_of_run_climbProg h hcol (n := n) (by omega) (by omega) hrun
    fun q hq' => hq q (List.mem_cons_of_mem _ hq')
  have hleaf := hq _ List.mem_cons_self
  rw [leafAt, hl, Option.bind_some, Merkle.opening, preimage_eq_of_lookup hcol hleaf]
  rfl

/-- The program of every opened leaf runs inside the per-leaf program: its root is among the
roots and its queries among the queries. -/
theorem exists_leafRootProg_of_mem_zip (n : ℕ) {j : ℕ} {a : MerkleLeaf kN L} :
    ∀ {js : List ℕ} {lvs : List (MerkleLeaf kN L)} {path : List (Digest k)}, (j, a) ∈ js.zip lvs →
      ∃ seg, (leafRootProg n j a seg).run h ∈ (rootsProg n js lvs path).run h ∧
        (leafRootProg n j a seg).trace h ⊆ (rootsProg n js lvs path).trace h
  | j' :: js, a' :: lvs, path, hm => by
    simp only [rootsProg, GordieHowe.OracleProg.run_bind, GordieHowe.OracleProg.run_pure,
      GordieHowe.OracleProg.trace_bind, GordieHowe.OracleProg.trace_pure, List.append_nil]
    rw [List.zip_cons_cons, List.mem_cons] at hm
    rcases hm with hm | hm
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hm
      exact ⟨_, List.mem_cons_self, List.subset_append_left _ _⟩
    · obtain ⟨seg, hr, ht⟩ :=
        exists_leafRootProg_of_mem_zip n (path := path.drop (authPos n j').length) hm
      exact ⟨seg, List.mem_cons_of_mem _ hr, fun q hq => List.subset_append_right _ _ (ht hq)⟩
  | [], _, _, hm => by simp at hm
  | _ :: _, [], _, hm => by simp at hm

/-- **The Merkle part of CMS19 Proposition 8.12** (p. 42) for authentication paths: an accepted
opening whose queries are recorded in a collision-free database opens, at each index, the leaf
that `leafAt` reads. -/
theorem leafAt_of_check (hcol : D ∉ digestCollision) {n : ℕ} {rt : Digest k} {js : List ℕ}
    {lvs : List (MerkleLeaf kN L)} {path : List (Digest k)}
    (hq : ∀ q ∈ (treeProg n js lvs path).trace h, D.lookup q = some (h q))
    (hc : format.check h n rt js lvs path) {j : ℕ} {a : MerkleLeaf kN L} (hja : (j, a) ∈ js.zip lvs)
    (hj : j < n) : leafAt D n rt ⟨j, hj⟩ = some a := by
  obtain ⟨-, -, -, -, hrt⟩ := hc
  change (treeProg n js lvs path).run h = some rt at hrt
  rw [run_treeProg] at hrt
  rw [trace_treeProg] at hq
  obtain ⟨seg, hr, ht⟩ := exists_leafRootProg_of_mem_zip h n (path := path) hja
  exact leafAt_of_run_leafRootProg h hcol hj (eq_of_commonRoot_eq_some hrt _ hr)
    fun q hq' => hq q (ht hq')

/-! ### Completeness -/

section Honest

open MerkleTree

variable {n : ℕ} {lf : ℕ → MerkleLeaf kN L}

/-- **The honest path reaches the honest root**: from a position `1 ≤ i < 2n` with its honest
digest and the honest digests of its path. -/
theorem run_climbProg_honest : ∀ {i : ℕ}, 1 ≤ i → i < 2 * n →
    (climbProg i (treeDigest h n lf i) ((pathPos i).map (treeDigest h n lf))).run h =
      some (root h n lf)
  | i, hi1, hin => by
    by_cases hi : 2 ≤ i
    · rw [pathPos_of_two_le hi, List.map_cons, climbProg_cons hi, GordieHowe.OracleProg.run_query]
      have hnode := treeDigest_node h lf (n := n) (i := i / 2) (by omega) (by omega)
      have hq : (h (if i % 2 = 0 then .node (treeDigest h n lf i) (treeDigest h n lf (sibling i))
          else .node (treeDigest h n lf (sibling i)) (treeDigest h n lf i))).digest =
          treeDigest h n lf (i / 2) := by
        rw [hnode]
        unfold sibling
        split_ifs with he
        · rw [show 2 * (i / 2) = i by omega]
        · rw [show 2 * (i / 2) = i - 1 by omega, show i - 1 + 1 = i by omega]
      rw [hq]
      exact run_climbProg_honest (by omega) (by omega)
    · obtain rfl : i = 1 := by omega
      rw [climbProg_of_lt_two (by omega), GordieHowe.OracleProg.run_pure]
      rfl
termination_by i => i
decreasing_by omega

/-- **The honest leaves with their honest paths each reach the honest root.** -/
theorem run_rootsProg_honest :
    ∀ {js : List ℕ} {lvs : List (MerkleLeaf kN L)}, (∀ j ∈ js, j < n) →
      List.Forall₂ (fun j a => a = lf j) js lvs →
      (rootsProg n js lvs (format.path h n js lf)).run h =
        List.replicate js.length (some (root h n lf))
  | [], [], _, .nil => by simp [rootsProg]
  | j :: js, a :: lvs, hjs, .cons ha hlv => by
    subst ha
    have hj : j < n := hjs j List.mem_cons_self
    have hpath : format.path h n (j :: js) lf =
        (authPos n j).map (treeDigest h n lf) ++ format.path h n js lf := by
      simp [format, MerkleFormat.path, sibs, List.map_flatMap]
    have hlen : (authPos n j).length = ((authPos n j).map (treeDigest h n lf)).length := by simp
    simp only [rootsProg, GordieHowe.OracleProg.run_bind, GordieHowe.OracleProg.run_pure]
    rw [hpath, hlen, List.take_left', List.drop_left',
      run_rootsProg_honest (fun j' hj' => hjs j' (List.mem_cons_of_mem _ hj')) hlv,
      leafRootProg, GordieHowe.OracleProg.run_query, authPos_of_lt hj]
    have hleaf : (h (.leaf (lf j).salt (lf j).column)).digest = treeDigest h n lf (n + j) := by
      rw [treeDigest_leaf h lf (by omega), show n + j - n = j by omega]
      rfl
    rw [hleaf, run_climbProg_honest h (by omega) (by omega)]
    rfl
    all_goals rfl

/-- **Completeness of authentication paths**: the honest leaves at distinct indices below `n`,
at least one, with their honest paths, are accepted against the honest root. -/
theorem check_path {js : List ℕ} {lvs : List (MerkleLeaf kN L)} (hnd : js.Nodup)
    (hjs : ∀ j ∈ js, j < n) (hne : js ≠ []) (hlv : List.Forall₂ (fun j a => a = lf j) js lvs) :
    format.check h n (root h n lf) js lvs (format.path h n js lf) := by
  refine ⟨hnd, hjs, hlv.length_eq.symm, by simp [MerkleFormat.path, format], ?_⟩
  change (treeProg n js lvs (format.path h n js lf)).run h = some (root h n lf)
  rw [run_treeProg, run_rootsProg_honest h hjs hlv,
    commonRoot_replicate (by simpa using hne)]

end Honest

/-! ### The format -/

/-- **Authentication paths as a Merkle opening format** (`MerkleOpening`): the format of paper
`prot:generalized-bcs`, with its laws. -/
def opening : MerkleOpening k kN kS L e where
  toMerkleFormat := format
  sibs_bounds := mem_sibs_bounds
  length_sibs_le := fun {B n js} _ hB hn => (length_sibs_le n js).trans
    (Nat.mul_le_mul hB (Nat.log_mono_right (by omega)))
  merkle_of_mem_trace := fun hq => merkle_of_mem_trace_treeProg _ hq
  length_trace_le := fun h _ _ _ path hjs _ => by
    rw [show (format.treeProg _ _ _ path : GordieHowe.OracleProg (Query k kN kS L) (Out k e) _) =
      treeProg _ _ _ path from rfl, trace_treeProg]
    exact length_trace_rootsProg_le h path hjs
  leafAt_of_check := fun hcol hq hc _ _ hja hj => leafAt_of_check _ hcol hq hc hja hj
  check_path := fun h _ _ _ _ hnd hjs hne hlv => check_path h hnd hjs hne hlv

end PerLeaf

end GordieHowe.SPBCS
