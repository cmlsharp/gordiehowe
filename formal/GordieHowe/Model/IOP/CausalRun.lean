-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.CausalComplete
public import GordieHowe.Model.IOP.CausalLeaves
public import GordieHowe.Model.IOP.Append
public import GordieHowe.Model.IOP.Completeness

@[expose] public section

/-!
# Runs of causal provers read only causal pasts

Facts about `CausalProver.run` (`GordieHowe/Model/IOP/CausalComplete.lean`) used by a Fiat–Shamir
compiler that derives each challenge from its causal past.

* `CausalProver.run_apply`: the transcript of leaf `p` is `p`'s prover run on the statement and
  the transcripts of the leaves before `p`, at `p`'s challenges.
* `CausalProver.run_congr`: it depends only on the challenges of `p` and of the leaves before
  `p`.
* `CausalProver.run_message_congr`: the message of a prover round `i` of `p` depends only on the
  challenges of the leaves before `p` and on `p`'s challenges before round `i`.
-/

namespace GordieHowe.IOP

open SPTerm

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}

namespace SPTerm.Leaf

/-- The leaves before an earlier leaf are fewer. -/
theorem length_ctxList_lt {t : SPTerm ι} {q p : t.Leaf} (h : q.Before p) :
    q.ctxList.length < p.ctxList.length := by
  have hsub : q.ctxList.Sublist p.ctxList :=
    List.monotone_filter_right _ fun r hr => by simpa using (by simpa using hr : r.Before q).trans h
  rcases hsub.length_le.lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd ((hsub.eq_of_length heq) ▸ mem_ctxList.2 h) (not_mem_ctxList_self q)

end SPTerm.Leaf

namespace CausalProver

variable {Stmt : Type}

/-- **The transcript of a leaf** is its prover's run on the statement and the transcripts of the
leaves before it (its causal context in the composite run), at its own challenges. -/
theorem run_apply : {t : SPTerm ι} → {Stmt : Type} → (prv : CausalProver P t Stmt) → (x : Stmt) →
    (ch : Chs P t) → (p : t.Leaf) →
    prv.run x ch p = (prv p).run (x, (prv.run x ch).ctx p) (ch.at p)
  | leaf j, _, prv, x, ch, .here _ => by
    show (prv (.here j)).run (x, CausalCtx.ofHere j) _ = _
    congr 3
    funext q
    obtain ⟨⟨⟩, h⟩ := q
    exact False.elim h
  | node .seq a b, _, prv, x, ch, .left p => by
    show prv.left.run x ch.left p = _
    rw [run_apply prv.left x ch.left p]
    refine (Prover.run_comap _ _ _ _).trans ?_
    refine congrArg (fun c => Prover.run (prv _) (x, c) _) ?_
    funext q
    obtain ⟨q, h⟩ := q
    cases q with
    | left q => rfl
    | right q => exact False.elim h
  | node .seq a b, _, prv, x, ch, .right p => by
    show prv.seqRight.run (x, prv.left.run x ch.left) ch.right p = _
    rw [run_apply prv.seqRight _ ch.right p]
    refine (Prover.run_comap _ _ _ _).trans ?_
    refine congrArg (fun c => Prover.run (prv _) (x, c) _) ?_
    funext q
    obtain ⟨q, h⟩ := q
    cases q with
    | left q => rfl
    | right q => rfl
  | node .par a b, _, prv, x, ch, .left p => by
    show prv.left.run x ch.left p = _
    rw [run_apply prv.left x ch.left p]
    refine (Prover.run_comap _ _ _ _).trans ?_
    refine congrArg (fun c => Prover.run (prv _) (x, c) _) ?_
    funext q
    obtain ⟨q, h⟩ := q
    cases q with
    | left q => rfl
    | right q => exact False.elim h
  | node .par a b, _, prv, x, ch, .right p => by
    show prv.parRight.run x ch.right p = _
    rw [run_apply prv.parRight x ch.right p]
    refine (Prover.run_comap _ _ _ _).trans ?_
    refine congrArg (fun c => Prover.run (prv _) (x, c) _) ?_
    funext q
    obtain ⟨q, h⟩ := q
    cases q with
    | left q => exact False.elim (nomatch h)
    | right q => rfl

/-- The transcripts of the leaves before `p` depend only on the challenges of the leaves before
`p`. -/
theorem run_ctx_congr {t : SPTerm ι} (prv : CausalProver P t Stmt) (x : Stmt) {ch ch' : Chs P t}
    (p : t.Leaf) (h : ∀ c : ChIdx P t, c.leaf.Before p → ch c = ch' c) :
    (prv.run x ch).ctx p = (prv.run x ch').ctx p := by
  suffices H : ∀ m (p : t.Leaf), p.ctxList.length < m →
      (∀ c : ChIdx P t, c.leaf.Before p → ch c = ch' c) →
      (prv.run x ch).ctx p = (prv.run x ch').ctx p from H _ p (Nat.lt_succ_self _) h
  intro m
  induction m with
  | zero => intro p hp; exact absurd hp (Nat.not_lt_zero _)
  | succ m ih =>
    intro p hp h
    funext q
    obtain ⟨q, hq⟩ := q
    show prv.run x ch q = prv.run x ch' q
    rw [run_apply, run_apply, ih q (by have := Leaf.length_ctxList_lt hq; omega)
      fun c hc => h c (hc.trans hq)]
    congr 1
    funext i
    exact h ⟨q, i⟩ hq

/-- **The transcript of a leaf depends only on its own challenges and those of the leaves before
it.** -/
theorem run_congr {t : SPTerm ι} (prv : CausalProver P t Stmt) (x : Stmt) {ch ch' : Chs P t}
    (p : t.Leaf) (h : ∀ c : ChIdx P t, c.leaf = p ∨ c.leaf.Before p → ch c = ch' c) :
    prv.run x ch p = prv.run x ch' p := by
  rw [run_apply, run_apply, run_ctx_congr prv x p fun c hc => h c (.inr hc)]
  congr 1
  funext i
  exact h ⟨p, i⟩ (.inl rfl)

/-- **A message of a leaf depends only on the challenges of the leaves before it and on its own
challenges before the message.** -/
theorem run_message_congr {t : SPTerm ι} (prv : CausalProver P t Stmt) (x : Stmt)
    {ch ch' : Chs P t} (p : t.Leaf) (i : (P p.label).MessageIdx)
    (hb : ∀ c : ChIdx P t, c.leaf.Before p → ch c = ch' c)
    (ho : ∀ j : (P p.label).ChallengeIdx, j.1 < i.1 → ch ⟨p, j⟩ = ch' ⟨p, j⟩) :
    prv.run x ch p i.1 = prv.run x ch' p i.1 := by
  rw [run_apply, run_apply, run_ctx_congr prv x p hb]
  exact Prover.run_message_congr _ _ i ho

/-- **A full composite run carries the challenge at every challenge.** -/
theorem run_challenge {t : SPTerm ι} (prv : CausalProver P t Stmt) (x : Stmt) (ch : Chs P t)
    (c : ChIdx P t) : prv.run x ch c.leaf c.idx.1 = ch c := by
  rw [run_apply]
  exact Prover.run_challenge _ _ _ c.idx

/-- The challenges of a composite run are the challenges it was run on. -/
theorem challenges_run {t : SPTerm ι} (prv : CausalProver P t Stmt) (x : Stmt) (ch : Chs P t) :
    (prv.run x ch).challenges = ch :=
  funext fun c => run_challenge prv x ch c

end CausalProver

end GordieHowe.IOP
