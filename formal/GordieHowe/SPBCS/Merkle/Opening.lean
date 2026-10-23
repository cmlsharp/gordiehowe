-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Merkle.Tree
public import GordieHowe.Model.NARG.OracleProg

@[expose] public section

/-!
# Merkle opening formats

How a compiled proof opens the queried leaves of one Merkle tree. The compiler of a series–parallel
composition (`GordieHowe.SPBCS.FullPast`, `GordieHowe/SPBCS/FullPast/Model.lean`) takes the format as a parameter
(`GordieHowe.SPBCS.Base.opening`), and every guarantee of the compiler holds for every lawful format.

- `MerkleFormat`: the data of a format for the leaves at the indices `js` of an `n`-leaf tree in
  the heap layout of `GordieHowe/SPBCS/Merkle/Tree.lean`: the heap positions `sibs n js` whose digests the
  opening carries, in order; the verifier's program `treeProg n js lvs path` on the opened leaves
  `lvs` and the path digests `path`, which returns the root it reconstructs or `none`; and a bound
  `pathCap B` on the number of digests of an opening of at most `B` leaves of a tree with at most
  `B` leaves.
- `MerkleFormat.check`: acceptance: distinct indices below `n`, one leaf per index, one path digest
  per position of `sibs n js`, and the reconstructed root is the root.
- `MerkleFormat.path`: the honest opening, the honest tree's digests at the positions `sibs n js`.
- `MerkleOpening`: a format with the laws the compiler's proofs use: the positions lie in
  `[2, 2n)` and number at most `pathCap B`; the verifier's program makes only `leaf` and `node`
  queries, at most `1 + ⌊log₂ 2n⌋` per opened leaf; an accepted opening whose queries are recorded
  in a collision-free database opens the leaves that the database extractor reads (the Merkle
  part of CMS19 Proposition 8.12, p. 42); and the honest opening is accepted against the honest
  root.

The two formats: `PerLeaf.opening` (`GordieHowe/SPBCS/Merkle/PerLeaf.lean`), one authentication path per
opened leaf, as in paper `prot:generalized-bcs`; and `Multiproof.opening`
(`GordieHowe/SPBCS/Merkle/Multiproof.lean`), the compressed multiproof that the C++ verifier checks.
`GordieHowe/SPBCS/Merkle/Compress.lean` relates them: the honest multiproof is a function of the honest
authentication paths, and an accepted multiproof yields authentication paths that are accepted
with the same queries.
-/

namespace GordieHowe.SPBCS
open GordieHowe.QROM

variable {k kN kS L e : ℕ}

/-- **A Merkle opening format** (module docstring): the heap positions whose digests the opening
of the indices `js` of an `n`-leaf tree carries (`sibs`), the verifier's program (`treeProg`) and
a bound on the digests of an opening (`pathCap`). -/
structure MerkleFormat (k kN kS L e : ℕ) where
  /-- The heap positions whose digests the opening of the indices `js` of an `n`-leaf tree
  carries, in order. -/
  sibs : ℕ → List ℕ → List ℕ
  /-- The verifier's program on the leaves `lvs` at the indices `js` and the path digests `path`:
  the root it reconstructs, or `none`. -/
  treeProg : ℕ → List ℕ → List (MerkleLeaf kN L) → List (Digest k) →
    GordieHowe.OracleProg (Query k kN kS L) (Out k e) (Option (Digest k))
  /-- A bound on the digests of an opening of at most `B` leaves of a tree with at most `B`
  leaves. -/
  pathCap : ℕ → ℕ

namespace MerkleFormat

variable (F : MerkleFormat k kN kS L e) (h : Query k kN kS L → Out k e)

/-- **Acceptance of an opening** of the leaves `lvs` at the indices `js` of an `n`-leaf tree with
root `rt`: the indices are distinct and below `n`, there is one leaf per index, the path has one
digest per position of `sibs n js`, and the reconstructed root is `rt`. -/
def check (n : ℕ) (rt : Digest k) (js : List ℕ) (lvs : List (MerkleLeaf kN L))
    (path : List (Digest k)) : Prop :=
  js.Nodup ∧ (∀ j ∈ js, j < n) ∧ lvs.length = js.length ∧
    path.length = (F.sibs n js).length ∧ (F.treeProg n js lvs path).run h = some rt

/-- **The honest opening** of the indices `js` of the honest tree over the leaves `lf`: the
honest tree's digests at the positions `sibs n js`, in order. -/
def path (n : ℕ) (js : List ℕ) (lf : ℕ → MerkleLeaf kN L) : List (Digest k) :=
  (F.sibs n js).map (MerkleTree.treeDigest h n lf)

end MerkleFormat

/-- **A lawful Merkle opening format** (module docstring): a format with the laws the compiler's
proofs use. -/
structure MerkleOpening (k kN kS L e : ℕ) extends MerkleFormat k kN kS L e where
  /-- The positions of an opening lie in `[2, 2n)`. -/
  sibs_bounds : ∀ {n : ℕ} {js : List ℕ} {c : ℕ}, c ∈ sibs n js → 2 ≤ c ∧ c < 2 * n
  /-- An opening of at most `B` indices below `n ≤ B` carries at most `pathCap B` digests. -/
  length_sibs_le : ∀ {B n : ℕ} {js : List ℕ}, (∀ j ∈ js, j < n) → js.length ≤ B → n ≤ B →
    (sibs n js).length ≤ pathCap B
  /-- The verifier's program makes only `leaf` and `node` queries. -/
  merkle_of_mem_trace : ∀ {h : Query k kN kS L → Out k e} {n : ℕ} {js : List ℕ}
    {lvs : List (MerkleLeaf kN L)} {path : List (Digest k)} {q : Query k kN kS L},
    q ∈ (treeProg n js lvs path).trace h → (∃ a b, q = .leaf a b) ∨ ∃ l r, q = .node l r
  /-- The verifier's program makes at most `1 + ⌊log₂ 2n⌋` queries per opened leaf. -/
  length_trace_le : ∀ (h : Query k kN kS L → Out k e) {n : ℕ} {js : List ℕ}
    {lvs : List (MerkleLeaf kN L)} (path : List (Digest k)), (∀ j ∈ js, j < n) →
    lvs.length = js.length →
    ((treeProg n js lvs path).trace h).length ≤ js.length * (1 + Nat.log 2 (2 * n))
  /-- **The Merkle part of CMS19 Proposition 8.12** (p. 42): an accepted opening whose queries
  are recorded in a collision-free database opens, at each index, the leaf that `leafAt` reads. -/
  leafAt_of_check : ∀ {h : Query k kN kS L → Out k e} {D : ODB k kN kS L e} {n : ℕ}
    {rt : Digest k} {js : List ℕ} {lvs : List (MerkleLeaf kN L)} {path : List (Digest k)},
    D ∉ digestCollision → (∀ q ∈ (treeProg n js lvs path).trace h, D.lookup q = some (h q)) →
    (MerkleFormat.mk sibs treeProg pathCap).check h n rt js lvs path →
    ∀ {j : ℕ} {a : MerkleLeaf kN L}, (j, a) ∈ js.zip lvs → (hj : j < n) →
      leafAt D n rt ⟨j, hj⟩ = some a
  /-- **Completeness**: the honest leaves at distinct indices below `n`, at least one, with the
  honest opening, are accepted against the honest root. -/
  check_path : ∀ (h : Query k kN kS L → Out k e) {n : ℕ} {js : List ℕ} {lf : ℕ → MerkleLeaf kN L}
    {lvs : List (MerkleLeaf kN L)}, js.Nodup → (∀ j ∈ js, j < n) → js ≠ [] →
    List.Forall₂ (fun j a => a = lf j) js lvs →
    (MerkleFormat.mk sibs treeProg pathCap).check h n (MerkleTree.root h n lf) js lvs
      ((MerkleFormat.mk sibs treeProg pathCap).path h n js lf)

namespace MerkleOpening

variable (O : MerkleOpening k kN kS L e) (h : Query k kN kS L → Out k e)

/-- The verifier's program makes no `xof` query. -/
theorem not_xof_mem_trace {n : ℕ} {js : List ℕ} {lvs : List (MerkleLeaf kN L)}
    {path : List (Digest k)} (d : Digest k) (s : FiatShamirSalt kS) :
    Query.xof d s ∉ (O.treeProg n js lvs path).trace h := fun hq => by
  rcases O.merkle_of_mem_trace hq with ⟨a, b, hab⟩ | ⟨l, r, hlr⟩
  · cases hab
  · cases hlr

/-- The verifier's program makes no `transcript` query. -/
theorem not_transcript_mem_trace {n : ℕ} {js : List ℕ} {lvs : List (MerkleLeaf kN L)}
    {path : List (Digest k)} (c : Bytes L) :
    Query.transcript c ∉ (O.treeProg n js lvs path).trace h := fun hq => by
  rcases O.merkle_of_mem_trace hq with ⟨a, b, hab⟩ | ⟨l, r, hlr⟩
  · cases hab
  · cases hlr

end MerkleOpening

end GordieHowe.SPBCS
