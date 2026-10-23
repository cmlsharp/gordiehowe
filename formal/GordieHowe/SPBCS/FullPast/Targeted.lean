-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.FullPast.Verifier
public import GordieHowe.SPBCS.Merkle.Visited
public import GordieHowe.Model.QROM.Partition

@[expose] public section

/-!
# The targeted extractor of the series–parallel base model

`Base.targetedExtract D π ch E x` (for a composite) extracts along the proof `π` only: the
composite transcript (`trT`) has at each prover round the message of `π`'s write with the Merkle
views of `D` at its roots, and at each challenge round the challenge `ch` the verifier derived; the
causal extractor `E` is applied to every challenge's causal past in it.

- `mem_of_verifyFullPast_targeted`: a database that records the verifier's queries on an accepted proof
  with the answers of `h` has a digest collision, lies in the knowledge argument's bad set, or the
  targeted extractor at the verifier's challenges returns a witness (the argument of
  `mem_of_verifyFullPast`, where the database's challenges along `π` are the verifier's).
- `targetedExtract_extend_of_notMem`: the extraction depends on `D` only through the views at
  `π`'s roots, so recording a new answer whose digest is not among their visited digests
  (`visitedAll`, at most `visitBound` digests) leaves it unchanged;
  `prob_targetedExtract_change_le`: one more recorded query changes the outcome with probability
  at most `visitBound / 2^(8k)` (for the spBCS compiler, `GordieHowe.SPBCS.instabPart_targetedExtractorOf_le`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open scoped ENNReal NNReal

variable {k kN kS L e : ℕ}

namespace Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι}
  {X : Type} (M : Base P t X k kN kS L e)

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

end Targeted

end Base

namespace FullPast

open Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {t : SPTerm ι}
  {X : Type} (M : FullPast P t X k kN kS L e)

section Targeted

variable (D : ODB k kN kS L e) (π : M.NIProof) (ch : Chs P t)

variable {Wit : Type} (E : CausalExtractor P t X Wit) (x : X)

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

/-! ### Proposition 8.12 along the proof -/

section Prop812

variable [∀ j i, Nonempty ((P j).Challenge i)] {V : X → FullTr P t → Bool} {Wit : Type}
  (rel : Set (X × Wit)) (E : CausalExtractor P t X Wit) (S : CausalStateFn P t X)
  {ε : ChIdx P t → ℝ≥0}

/-- **CMS19 Proposition 8.12 along one accepted proof, with the targeted extractor**: a database
that records the verifier's queries on an accepted proof `π` of `x` with the answers of `h` has a
digest collision, lies in `badAny`, or the targeted extractor at the verifier's challenges returns
a witness for `x`. The composite transcript read from `D` along `π`'s chains is the targeted one
(`stepFullPast_chainsFullPast_message`, `stepFullPast_chainsFullPast_challenge`), and the flip comes from
`CausalRBR.exists_flip`. -/
theorem mem_of_verifyFullPast_targeted [DecidableEq X] (hrbr : CausalRBRKnowledgeSound rel V E S ε)
    (h : Query k kN kS L → Out k e) (x : X) (π : M.NIProof) (Q : M.IOPQueries V x)
    {D : ODB k kN kS L e} (hv : AcceptsFullPast h x π Q)
    (hQ : ∀ q ∈ M.queriesFullPast x π h Q, D.lookup q = some (h q)) :
    (∃ w ∈ M.targetedExtract D π (M.chVFullPast h x π.salt π.writes) E x, (x, w) ∈ rel) ∨
      D ∈ M.badAny rel E S ∪ digestCollision := by
  by_cases hcol : D ∈ digestCollision
  · exact Or.inr (Or.inr hcol)
  set chs := M.chainsFullPast h x π.salt π.writes
  set ch := M.chVFullPast h x π.salt π.writes
  set trF := M.trT D π ch
  have hsteps : ∀ q (r : ℕ) (hr : r < n q.label),
      M.step D x π.salt chs q (chs q) r hr = some (trF q (⟨r, hr⟩ : Fin (n q.label))) := by
    intro q r hr
    by_cases hd : (P q.label).dir ⟨r, hr⟩ = .P_to_V
    · rw [M.stepFullPast_chainsFullPast_message h x π D q ⟨⟨r, hr⟩, hd⟩]
      exact congrArg some (M.trT_message D π ch q ⟨⟨r, hr⟩, hd⟩).symm
    · have h1 := M.stepFullPast_chainsFullPast_challenge h x π Q hv hQ ⟨q, (P q.label).chIdx ⟨r, hr⟩ hd⟩
      exact h1.trans (congrArg some
        (M.trT_challenge D π ch ⟨q, (P q.label).chIdx ⟨r, hr⟩ hd⟩).symm)
  have htrF : ∀ q, M.extLeaf D x π.salt chs q (chs q) (n q.label) le_rfl = some (trF q) := by
    intro q
    obtain ⟨tr, htr⟩ := Option.isSome_iff_exists.1 (M.extLeaf_isSome D x π.salt chs q (chs q)
      (fun r hr => Option.isSome_iff_exists.2 ⟨_, hsteps q r hr⟩) _ le_rfl)
    rw [htr]
    congr 1
    funext r
    have h1 := M.step_of_extLeaf D x π.salt chs q (chs q) _ le_rfl htr r.1 r.2
    rw [hsteps q r.1 r.2] at h1
    exact (Option.some_inj.1 h1).symm
  have hchal : trF.challenges = ch := M.challenges_trT D π ch
  have hacc : V x trF = true := by
    refine Q.accept_of_verdict chs ch
      (fun p i => (M.comp p.label).views D i (π.writes p i)) trF _ ?_ hchal ?_ hv.decides
    · intro p i w hw
      have hw' : w = π.writes p i := by
        have h2 := M.chainsFullPast_getElem?_message h x π.salt π.writes p i
        rw [hw] at h2
        exact eq_of_heq (Sigma.mk.inj (Item.write.inj (Option.some_inj.1 h2))).2
      subst hw'
      exact M.trT_message D π ch p i
    · exact M.forall₂_leafAt h x π Q hcol hv hQ
  have hfull : ∀ p, M.ChainsFull chs p := fun p q _ => by
    show (M.chainsFullPast h x π.salt π.writes q).length = _
    rw [chainsFullPast_eq, length_leafChainFullPast]
  have hpast : ∀ c : ChIdx P t, M.extPast D x π.salt chs c
      ((chs c.leaf).take c.idx.1) = some (trF.past c) := by
    intro c
    have hctx : M.extCtx D x π.salt chs c.leaf = some (trF.ctx c.leaf) :=
      optAll_eq_some.2 fun q => htrF q.1
    rw [extPast, hctx, Option.bind_some, M.extLeaf_take D x π.salt chs c.leaf (chs c.leaf) _ _ le_rfl,
      M.extLeaf_of_le D x π.salt chs c.leaf (chs c.leaf) le_rfl (htrF c.leaf) _ c.idx.1.2.le,
      Option.map_some]
    rfl
  have hlen : ∀ c : ChIdx P t, ((chs c.leaf).take c.idx.1).length = c.idx.1.1 := fun c => by
    rw [List.length_take, show (chs c.leaf).length = n c.leaf.label by
      show (M.chainsFullPast h x π.salt π.writes c.leaf).length = _
      rw [chainsFullPast_eq, length_leafChainFullPast]]
    exact Nat.min_eq_left c.idx.1.2.le
  have hown : ∀ c : ChIdx P t, (chs c.leaf).take c.idx.1 =
      M.leafChainFullPast h x π.salt π.writes c.leaf (M.ctxOf h x π.salt π.writes c.leaf) c.idx.1
        c.idx.1.2.le := fun c => M.take_chainsFullPast h x π c.leaf c.idx.1 c.idx.1.2.le
  by_cases hE : ∃ c, (x, E c x (trF.past c)) ∈ rel
  · obtain ⟨c, hc⟩ := hE
    exact Or.inl ⟨_, (M.mem_targetedExtract D π ch E x).2 ⟨c, rfl⟩, hc⟩
  · push Not at hE
    obtain ⟨c, hflip⟩ := hrbr.exists_flip x trF hacc id hE
    obtain ⟨hm1, hm2⟩ := M.mem_queriesFullPast_challenge h x π Q c
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 (hv.sampled c)
    simp only [chalOf] at hs
    have hchc : ch c = s := by simp [ch, chVFullPast, chalOf, hs]
    refine Or.inr (Or.inl ⟨x, π.salt, c, chs, (chs c.leaf).take c.idx.1, trF.past c,
      h (.transcript (M.inputAt x π.salt chs c.leaf (M.leafChainFullPast h x π.salt π.writes c.leaf
        (M.ctxOf h x π.salt π.writes c.leaf) c.idx.1 c.idx.1.2.le))),
      h (.xof (M.keyFullPast h x π.salt c.leaf (M.ctxOf h x π.salt π.writes c.leaf)
        (M.leafChainFullPast h x π.salt π.writes c.leaf (M.ctxOf h x π.salt π.writes c.leaf) c.idx.1
          c.idx.1.2.le)) π.salt),
      trF.challenges c, hfull c.leaf, hlen c, hpast c, ?_, ?_, ?_, ⟨hE c, hflip⟩⟩)
    · rw [hown c]
      exact hQ _ hm1
    · exact hQ _ hm2
    · rw [hchal, hchc]
      exact hs

end Prop812

end FullPast

end GordieHowe.SPBCS
