-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Extract
public import GordieHowe.SPBCS.Merkle.Visited
public import GordieHowe.Model.QROM.Partition

@[expose] public section

/-!
# The targeted extractor

`targetedExtract D π ch E x` extracts along the proof `π` only: the composite transcript (`trT`)
has at each prover round the message of `π`'s write with the Merkle views of `D` at its roots, and
at each challenge round the challenge `ch` the verifier derived; the causal extractor `E` is
applied to every challenge's causal past in it. CMS19 Proposition 8.12 with the targeted
extractor is `GordieHowe.SPBCS.mem_of_verify_targeted` (`GordieHowe/SPBCS/Cover.lean`).

- `targetedExtract_extend_of_notMem`: the extraction depends on `D` only through the views at
  `π`'s roots, so recording a new answer whose digest is not among their visited digests
  (`visitedAll`, at most `visitBound` digests) leaves it unchanged;
  `prob_targetedExtract_change_le`: one more recorded query changes the outcome with probability
  at most `visitBound / 2^(8k)`.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open scoped ENNReal NNReal

variable {ι : Type} {t : SPTerm ι} {Mg : Merges t} {k kN kS L e : ℕ} {n : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type} (M : SPBCS Mg P X k kN kS L e)

section Targeted

variable (D : ODB k kN kS L e) (π : M.NIProof) (ch : Chs P t)

/-- **The composite transcript along the proof `π`**: at a prover round of a leaf, the message of
`π`'s write with the Merkle views of `D` at its roots; at a challenge round, the challenge `ch`. -/
def trT : FullTr P t := fun q r =>
  if hd : (P q.label).dir r = .P_to_V then
    (M.comp q.label).msg ⟨r, hd⟩ (π.writes q ⟨r, hd⟩)
      ((M.comp q.label).views D ⟨r, hd⟩ (π.writes q ⟨r, hd⟩))
  else ch ⟨q, (P q.label).chIdx r hd⟩

theorem trT_message (q : t.Leaf) (i : (P q.label).MessageIdx) :
    M.trT D π ch q i.1 = (M.comp q.label).msg i (π.writes q i)
      ((M.comp q.label).views D i (π.writes q i)) := by
  simp only [trT, i.2, ↓reduceDIte]
  rfl

theorem trT_challenge (c : ChIdx P t) : M.trT D π ch c.leaf c.idx.1 = ch c := by
  have hd : ¬ (P c.leaf.label).dir c.idx.1 = .P_to_V := by simp [c.idx.2]
  simp only [trT, hd, ↓reduceDIte]
  rfl

theorem challenges_trT : (M.trT D π ch).challenges = ch := by
  funext c
  have hd : ¬ (P c.leaf.label).dir c.idx.1 = .P_to_V := by simp [c.idx.2]
  simp only [FullTr.challenges, trT, hd, ↓reduceDIte]
  rfl

variable {Wit : Type} (E : CausalExtractor P t X Wit) (x : X)

/-- **The targeted extractor**: the causal extractor `E` at the causal past of every challenge in
the composite transcript along `π` (`trT`), with the challenges `ch` and the prover messages read
from the Merkle views of `D` at the roots of `π`'s writes.

Running time, in the database size `|D|` and the leaf counts: each prover round reads, for each
of its trees, the view below the root (at most `2 · nLeaves` digests, each one scan of `D`), plus
`msg`; then one call of `E` per challenge of the composite (`t.size n` calls at most). It is
polynomial when `E` and `msg` are. This running time is argued here, not proved in Lean. -/
def targetedExtract : Multiset Wit :=
  (Finset.univ : Finset (ChIdx P t)).val.map fun c => E c x ((M.trT D π ch).past c)

theorem mem_targetedExtract {w : Wit} :
    w ∈ M.targetedExtract D π ch E x ↔ ∃ c, E c x ((M.trT D π ch).past c) = w := by
  simp [targetedExtract]

/-- **The number of visited digests**: at most `2 · nLeaves + 1` per tree, over all trees of all
prover rounds of all leaves. -/
def visitBound : ℕ :=
  ∑ q : t.Leaf, ∑ i : (P q.label).MessageIdx, ∑ τ : Fin ((M.comp q.label).nTrees i),
    (2 * (M.comp q.label).nLeaves i τ + 1)

variable {D π}

theorem trT_congr {D' : ODB k kN kS L e}
    (hD : ∀ q i, (M.comp q.label).views D' i (π.writes q i) = (M.comp q.label).views D i (π.writes q i)) :
    M.trT D' π ch = M.trT D π ch := by
  funext q r
  unfold trT
  exact dite_congr rfl (fun hd => by rw [hD q ⟨r, hd⟩]) fun _ => rfl

variable (D π)

/-! ### The outcome depends on the database only through the views at `π`'s roots -/

/-- **The digests visited by the targeted extraction**: the visited digests of the views below
every root of `π`'s writes. -/
def visitedAll : Finset (Digest k) :=
  Finset.univ.biUnion fun q : t.Leaf => Finset.univ.biUnion fun i : (P q.label).MessageIdx =>
    Finset.univ.biUnion fun τ : Fin ((M.comp q.label).nTrees i) =>
      visited D ((M.comp q.label).nLeaves i τ) ((M.comp q.label).rootOf i (π.writes q i) τ)

theorem card_visitedAll_le : (M.visitedAll D π).card ≤ M.visitBound :=
  Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ =>
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ =>
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => card_visited_le _ _ _)))

variable {D π}

/-- **Recording a new answer whose digest is not visited leaves the extraction unchanged**
(`view_extend_of_notMem_visited`). -/
theorem targetedExtract_extend_of_notMem {q : Query k kN kS L} (hq : q ∉ D) {y : Out k e}
    (hy : y.digest ∉ M.visitedAll D π) :
    M.targetedExtract (D.extend q y) π ch E x = M.targetedExtract D π ch E x := by
  unfold targetedExtract
  rw [M.trT_congr ch fun r i => funext fun τ => view_extend_of_notMem_visited hq fun hmem => hy
    (Finset.mem_biUnion.2 ⟨r, Finset.mem_univ _, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _,
      Finset.mem_biUnion.2 ⟨τ, Finset.mem_univ _, hmem⟩⟩⟩)]

variable (D π)

/-- **One more recorded query changes the targeted extraction with probability at most
`visitBound / 2^(8k)`**, for every database. -/
theorem prob_targetedExtract_change_le {q : Query k kN kS L} (hq : q ∉ D) :
    Pr[y ← Out k e : M.targetedExtract (D.extend q y) π ch E x ≠ M.targetedExtract D π ch E x] ≤
      M.visitBound / 2 ^ (8 * k) := by
  calc Pr[y ← Out k e : M.targetedExtract (D.extend q y) π ch E x ≠ M.targetedExtract D π ch E x]
      ≤ Pr[y ← Out k e : y.digest ∈ M.visitedAll D π] := QROM.probUniform_mono fun y hy => by
        by_contra hy'
        exact hy (M.targetedExtract_extend_of_notMem ch E x hq hy')
    _ = (M.visitedAll D π).card / 2 ^ (8 * k) := Out.probUniform_digest_mem _
    _ ≤ M.visitBound / 2 ^ (8 * k) := by
        gcongr
        exact_mod_cast M.card_visitedAll_le D π

end Targeted

end GordieHowe.SPBCS
