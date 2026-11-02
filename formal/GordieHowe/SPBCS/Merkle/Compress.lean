-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Merkle.PerLeaf
public import GordieHowe.SPBCS.Merkle.Multiproof
public import GordieHowe.Headline

@[expose] public section

/-!
# Multiproofs as compressed authentication paths

The compressed multiproof (`Multiproof.opening`, what the C++ verifier checks) and the
authentication paths of paper `prot:generalized-bcs` (`PerLeaf.opening`) open a tree's leaves
interchangeably:

- `Multiproof.compress n js pl` reads, at each proof position of the multiproof of the indices
  `js`, the digest that the concatenated authentication paths `pl` carry there. The honest
  multiproof is the compression of the honest paths (`compress_path`): the multiproof is a
  function of the paths and the opened indices.
- `Multiproof.decompress h n js lvs path` reads the authentication paths off a multiproof: at each
  path position, the digest that the multiproof verifier reconstructs there. When the multiproof
  is accepted, so are these paths (`check_decompress`), and the per-leaf verifier's queries on
  them are among the multiproof verifier's queries (`trace_decompress_subset`).

The compiler's guarantees hold for every opening format (`GordieHowe.SPBCS.opening`) at errors that do not
depend on the format: both formats make at most `1 + ⌊log₂ 2n⌋` verifier queries per opened leaf
of an `n`-leaf tree (`MerkleOpening.length_trace_le`). The lemmas here relate the two formats
directly: a cheating multiproof yields accepted authentication paths, and the honest multiproof
is computed from the honest paths.
-/

namespace GordieHowe.SPBCS
open GordieHowe.QROM

variable {k kN kS L e : ℕ}

namespace Multiproof

open MerkleTree

variable {n : ℕ} {js : List ℕ}

/-- **Every proof position of a multiproof is on an authentication path** of an opened leaf: it is
the sibling of a position of `TREE`. -/
theorem mem_perLeaf_sibs_of_mem_sibNodes (hjs : ∀ j ∈ js, j < n) {c : ℕ}
    (hc : c ∈ sibNodes n js) : c ∈ PerLeaf.sibs n js := by
  classical
  obtain ⟨i, hi, hs⟩ := List.mem_filterMap.1 hc
  obtain ⟨hir, hit⟩ := List.mem_filter.1 hi
  have hin : i < n := List.mem_range.1 (List.mem_reverse.1 hir)
  have hiT : inTree n js i := of_decide_eq_true hit
  have hi1 := hiT.1
  obtain ⟨c', hc'T, hc'2, hsib⟩ : ∃ c', inTree n js c' ∧ 2 ≤ c' ∧ PerLeaf.sibling c' = c := by
    unfold sibling at hs
    split_ifs at hs with h0 h1
    · obtain rfl := Option.some_inj.1 hs
      refine ⟨2 * i, h0, by omega, ?_⟩
      unfold PerLeaf.sibling
      split_ifs <;> omega
    · obtain rfl := Option.some_inj.1 hs
      refine ⟨2 * i + 1, ((inTree_node_iff hi1 hin).1 hiT).resolve_left h0, by omega, ?_⟩
      unfold PerLeaf.sibling
      split_ifs <;> omega
  obtain ⟨-, j, hj, hp⟩ := hc'T
  refine List.mem_flatMap.2 ⟨j, hj, ?_⟩
  rw [PerLeaf.authPos_of_lt (hjs j hj), ← hsib]
  exact PerLeaf.sibling_mem_pathPos hp hc'2

/-- **The multiproof read off authentication paths**: at each proof position of the indices `js`
(`sibNodes`), the digest that the concatenated paths `pl` carry there (`PerLeaf.sibs`), the
all-zero digest if none. -/
def compress (n : ℕ) (js : List ℕ) (pl : List (Digest k)) : List (Digest k) :=
  (sibNodes n js).map fun c => (lookupAns (PerLeaf.sibs n js) pl c).getD fun _ => 0

/-- **The honest multiproof is the compression of the honest authentication paths.** -/
@[headline]
theorem compress_path (h : Query k kN kS L → Out k e) (hjs : ∀ j ∈ js, j < n)
    (lf : ℕ → MerkleLeaf kN L) :
    compress n js ((PerLeaf.format (kS := kS) (e := e)).path h n js lf) =
      (format (kS := kS) (e := e)).path h n js lf := by
  change (sibNodes n js).map (fun c => (lookupAns (PerLeaf.sibs n js)
      ((PerLeaf.sibs n js).map (treeDigest h n lf)) c).getD fun _ => 0) =
    (sibNodes n js).map (treeDigest h n lf)
  refine List.map_congr_left fun c hc => ?_
  rw [lookupAns_map_self _ (mem_perLeaf_sibs_of_mem_sibNodes hjs hc), Option.getD_some]

variable (h : Query k kN kS L → Out k e) {lv sv : ℕ → Option (Digest k)}

/-- **Every position of `TREE` below an accepted root is reconstructed**, with its queries among
the root's. -/
theorem isSome_of_run_reconProg_one (hjs : ∀ j ∈ js, j < n) {rt : Digest k}
    (hrt : (reconProg n js lv sv 1).run h = some rt) :
    ∀ i, inTree n js i → ((reconProg n js lv sv i).run h).isSome ∧
      (reconProg n js lv sv i).trace h ⊆ (reconProg n js lv sv 1).trace h := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h1 : i = 1
    · subst h1
      rw [hrt]
      exact ⟨rfl, fun _ h => h⟩
    have hi2 : 2 ≤ i := by have := hi.1; omega
    obtain ⟨hp, hpn⟩ := inTree_parent hjs hi hi2
    obtain ⟨hsp, htp⟩ := ih (i / 2) (by omega) hp
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hsp
    obtain ⟨a, b, ha, hb, -, htr⟩ := run_reconProg_node h hp (by omega) hv
    rcases Nat.even_or_odd' i with ⟨c, hc | hc⟩
    · have hc2 : i / 2 = c := by omega
      rw [hc2] at ha htr
      subst hc
      rw [ha]
      exact ⟨rfl, fun q hq => htp (by rw [hc2, htr]; exact List.mem_append_left _ hq)⟩
    · have hc2 : i / 2 = c := by omega
      rw [hc2] at hb htr
      subst hc
      rw [hb]
      exact ⟨rfl, fun q hq => htp (by
        rw [hc2, htr]; exact List.mem_append_right _ (List.mem_append_left _ hq))⟩

/-- The digest the multiproof verifier reconstructs at heap position `c`, the all-zero digest if
none. -/
def reconAt (n : ℕ) (js : List ℕ) (lv sv : ℕ → Option (Digest k)) (c : ℕ) : Digest k :=
  ((reconProg (k := k) (kN := kN) (kS := kS) (L := L) (e := e) n js lv sv c).run h).getD
    fun _ => 0

/-- **A path read off an accepted reconstruction reaches its root**: from a position of `TREE`
with its reconstructed digest, along the reconstructed digests at the path positions, with the
path's queries among the reconstruction's. -/
theorem run_climbProg_reconAt (hjs : ∀ j ∈ js, j < n) {rt : Digest k}
    (hrt : (reconProg n js lv sv 1).run h = some rt) :
    ∀ i, inTree n js i → ∀ {v : Digest k}, (reconProg n js lv sv i).run h = some v →
      (PerLeaf.climbProg i v ((PerLeaf.pathPos i).map (reconAt h n js lv sv))).run h = some rt ∧
      (PerLeaf.climbProg i v ((PerLeaf.pathPos i).map (reconAt h n js lv sv))).trace h ⊆
        (reconProg n js lv sv 1).trace h := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi v hv
    by_cases h1 : i = 1
    · subst h1
      rw [PerLeaf.pathPos_of_lt_two (by omega), List.map_nil,
        PerLeaf.climbProg_of_lt_two (by omega),
        GordieHowe.OracleProg.run_pure, GordieHowe.OracleProg.trace_pure]
      rw [hrt] at hv
      exact ⟨congrArg some (Option.some_inj.1 hv).symm, List.nil_subset _⟩
    have hi2 : 2 ≤ i := by have := hi.1; omega
    obtain ⟨hp, hpn⟩ := inTree_parent hjs hi hi2
    obtain ⟨hsp, htp⟩ := isSome_of_run_reconProg_one h hjs hrt (i / 2) hp
    obtain ⟨w₀, hw₀⟩ := Option.isSome_iff_exists.1 hsp
    obtain ⟨a, b, ha, hb, hw, htr⟩ := run_reconProg_node h hp (by omega) hw₀
    have hnode : Query.node a b ∈ (reconProg n js lv sv 1).trace h :=
      htp (by rw [htr]; simp)
    have hq : (if i % 2 = 0 then Query.node v (reconAt h n js lv sv (PerLeaf.sibling i))
        else Query.node (reconAt h n js lv sv (PerLeaf.sibling i)) v :
          Query k kN kS L) = .node a b := by
      unfold PerLeaf.sibling reconAt
      rcases Nat.even_or_odd' i with ⟨c, hc | hc⟩
      · have hc2 : i / 2 = c := by omega
        rw [hc2] at ha hb
        subst hc
        rw [if_pos (by omega), if_pos (by omega), ha] at *
        rw [hb, Option.getD_some, ← Option.some_inj.1 (hv.symm.trans ha)]
      · have hc2 : i / 2 = c := by omega
        rw [hc2] at ha hb
        subst hc
        rw [if_neg (show ¬ (2 * c + 1) % 2 = 0 by omega),
          if_neg (show ¬ (2 * c + 1) % 2 = 0 by omega), show 2 * c + 1 - 1 = 2 * c by omega, ha,
          Option.getD_some, ← Option.some_inj.1 (hv.symm.trans hb)]
    rw [PerLeaf.pathPos_of_two_le hi2, List.map_cons, PerLeaf.climbProg_cons hi2]
    rw [hq, GordieHowe.OracleProg.run_query, GordieHowe.OracleProg.trace_query]
    obtain ⟨hr, ht⟩ := ih (i / 2) (by omega) hp (v := (h (.node a b)).digest) (hw ▸ hw₀)
    exact ⟨hr, List.cons_subset.2 ⟨hnode, ht⟩⟩

/-- **The authentication paths read off a multiproof**: at each path position of the indices
`js` (`PerLeaf.sibs`), the digest that the multiproof verifier reconstructs there under `h` from
the leaves `lvs` and the proof digests `path` (`reconAt`). -/
def decompress (n : ℕ) (js : List ℕ) (lvs : List (MerkleLeaf kN L)) (path : List (Digest k)) :
    List (Digest k) :=
  (PerLeaf.sibs n js).map (reconAt h n js (leafDigests h js lvs) (lookupAns (sibNodes n js) path))

theorem decompress_eq_flatMap (n : ℕ) (js : List ℕ) (lvs : List (MerkleLeaf kN L))
    (path : List (Digest k)) :
    decompress h n js lvs path = js.flatMap fun j => (PerLeaf.authPos n j).map
      (reconAt h n js (leafDigests h js lvs) (lookupAns (sibNodes n js) path)) := by
  simp [decompress, PerLeaf.sibs, List.map_flatMap]

/-- A multiproof of no index carries no digest. -/
theorem sibNodes_nil (n : ℕ) : sibNodes n [] = [] := by
  simp [sibNodes, inTree]

/-- An accepted multiproof opens some index. -/
theorem ne_nil_of_check {rt : Digest k} {lvs : List (MerkleLeaf kN L)} {path : List (Digest k)}
    (hc : format.check h n rt js lvs path) : js ≠ [] := by
  rintro rfl
  obtain ⟨-, -, -, -, hrt⟩ := hc
  change (treeProg n [] lvs path).run h = some rt at hrt
  rw [run_treeProg, reconProg_of_not_inTree (by simp [inTree])] at hrt
  simp [sibNodes_nil, lookupAns] at hrt

/-- The leaf program of an opened leaf along the path read off an accepted multiproof reaches
the root, with its queries among the multiproof verifier's. -/
theorem leafRootProg_decompress {rt : Digest k} {lvs : List (MerkleLeaf kN L)}
    {path : List (Digest k)} (hc : format.check h n rt js lvs path) {j : ℕ} {a : MerkleLeaf kN L}
    (hja : (j, a) ∈ js.zip lvs) :
    (PerLeaf.leafRootProg n j a ((PerLeaf.authPos n j).map
        (reconAt h n js (leafDigests h js lvs) (lookupAns (sibNodes n js) path)))).run h = some rt ∧
      (PerLeaf.leafRootProg n j a ((PerLeaf.authPos n j).map
        (reconAt h n js (leafDigests h js lvs) (lookupAns (sibNodes n js) path)))).trace h ⊆
        (treeProg n js lvs path).trace h := by
  obtain ⟨hnd, hjs, -, -, hrt⟩ := hc
  change (treeProg n js lvs path).run h = some rt at hrt
  rw [run_treeProg] at hrt
  have hj : j ∈ js := (List.of_mem_zip hja).1
  have hjn := hjs j hj
  have hleaf :
      (reconProg n js (leafDigests h js lvs) (lookupAns (sibNodes n js) path) (n + j)).run h =
      some (h (.leaf a.salt a.column)).digest := by
    rw [reconProg_leaf (inTree_leaf hj hjn) (by omega), GordieHowe.OracleProg.run_pure,
      show n + j - n = j by omega, leafDigests,
      lookupAns_map (fun a : MerkleLeaf kN L => (h (Query.leaf a.salt a.column)).digest) js lvs j,
      lookupAns_of_mem_zip hnd hja, Option.map_some]
  obtain ⟨hr, ht⟩ := run_climbProg_reconAt h hjs hrt (n + j) (inTree_leaf hj hjn) hleaf
  rw [PerLeaf.authPos_of_lt hjn, PerLeaf.leafRootProg, GordieHowe.OracleProg.run_query,
    GordieHowe.OracleProg.trace_query, trace_treeProg]
  refine ⟨hr, List.cons_subset.2 ⟨List.mem_append_left _ (List.mem_map.2
    ⟨a, (List.of_mem_zip hja).2, rfl⟩), fun q hq => List.mem_append_right _ (ht hq)⟩⟩

/-- **An accepted multiproof yields accepted authentication paths**: the paths read off it
(`decompress`) are accepted by the per-leaf verifier against the same root. -/
@[headline]
theorem check_decompress {rt : Digest k} {lvs : List (MerkleLeaf kN L)} {path : List (Digest k)}
    (hc : format.check h n rt js lvs path) :
    (PerLeaf.format (kS := kS) (e := e)).check h n rt js lvs (decompress h n js lvs path) := by
  have hne := ne_nil_of_check h hc
  obtain ⟨hnd, hjs, hl, -, -⟩ := id hc
  refine ⟨hnd, hjs, hl, by simp [decompress, PerLeaf.format], ?_⟩
  change (PerLeaf.treeProg n js lvs (decompress h n js lvs path)).run h = some rt
  rw [PerLeaf.run_treeProg, decompress_eq_flatMap, PerLeaf.run_rootsProg_flatMap h n _ hl]
  refine PerLeaf.commonRoot_of_forall_eq (by
    obtain ⟨j, js', rfl⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨a, lvs', rfl⟩ := List.exists_cons_of_ne_nil (show lvs ≠ [] by rintro rfl; simp at hl)
    simp) fun x hx => ?_
  obtain ⟨ja, hja, rfl⟩ := List.mem_map.1 hx
  exact (leafRootProg_decompress h hc hja).1

/-- **The per-leaf verifier on the paths read off an accepted multiproof makes only the
multiproof verifier's queries.** -/
@[headline]
theorem trace_decompress_subset {rt : Digest k} {lvs : List (MerkleLeaf kN L)}
    {path : List (Digest k)} (hc : format.check h n rt js lvs path) :
    (PerLeaf.treeProg n js lvs (decompress h n js lvs path)).trace h ⊆
      (treeProg n js lvs path).trace h := by
  obtain ⟨-, -, hl, -, -⟩ := id hc
  rw [PerLeaf.trace_treeProg, decompress_eq_flatMap, PerLeaf.trace_rootsProg_flatMap h n _ hl]
  intro q hq
  obtain ⟨ja, hja, hq⟩ := List.mem_flatMap.1 hq
  exact (leafRootProg_decompress h hc hja).2 hq

end Multiproof

end GordieHowe.SPBCS
