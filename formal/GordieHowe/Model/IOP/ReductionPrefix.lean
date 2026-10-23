-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.Reduction
public import GordieHowe.Model.IOP.ChallengeEventReduction

@[expose] public section

/-!
# Round-by-round soundness of a reduction with a total order, on transcript prefixes

Paper `lem:red-prefix`, after CDHZ25 Definitions 3.3-3.4 (printed p. 25). A reduction on committed
data whose order on the rounds is total is a reduction over a one-leaf term `leaf j`: the leaf's
component is the chain of its rounds. For such a reduction, round-by-round soundness
(`Reduction.RBR`, paper `def:red-sec` (a)) is equivalent to the existence of a state function on
the transcript prefixes with the four conditions of `Reduction.PrefixRBR`.

* `Reduction.PrefixRBR.toRBR`: a prefix state function with (i)-(iv) is a state function of
  `def:red-sec` (a) with the same errors.
* `Reduction.RBR.prefixRBR`: conversely, from a state function of `def:red-sec` (a), the prefix
  state that is true when the input claim holds or when the state has moved from false to true at
  a challenge of the prefix (`ChallengeEventReduction.state`) satisfies (i)-(iv).
* `Reduction.rbr_iff_prefixRBR`: the equivalence.
-/

namespace GordieHowe.IOP

open scoped NNReal
open SPTerm

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}

namespace Reduction

variable [∀ j (i : (P j).ChallengeIdx), Fintype ((P j).Challenge i)]
  [∀ j (i : (P j).ChallengeIdx), Nonempty ((P j).Challenge i)] {j : ι} {D X₁ X₂ : Type}

/-- **Round-by-round soundness on transcript prefixes** (paper `lem:red-prefix` (i)-(iv); CDHZ25
Definitions 3.3-3.4 at proximity bound `0`) of a reduction `A` from `R₁` to `R₂` whose order is
total, at the state function `S` on the statement, the committed data and a prefix of the
transcript, with per-challenge errors `ε`. The state function need not be efficient. -/
structure PrefixRBR (A : Reduction P (leaf j) D X₁ X₂) (R₁ : Set (X₁ × D)) (R₂ : Set (X₂ × D))
    (S : (k : Fin (n j + 1)) → X₁ × D → (P j).Transcript k → Prop)
    (ε : (P j).ChallengeIdx → ℝ≥0) : Prop where
  /-- (i) The state is false on the empty prefix when the input is not in `R₁`. -/
  start : ∀ x d (tr : (P j).Transcript 0), (x, d) ∉ R₁ → ¬ S 0 (x, d) tr
  /-- (ii) A prover message does not make the state true. -/
  next : ∀ m : Fin (n j), (P j).dir m = .P_to_V → ∀ x d (tr : (P j).Transcript m.castSucc) msg,
    ¬ S m.castSucc (x, d) tr → ¬ S m.succ (x, d) ((P j).concat tr msg)
  /-- (iii) From a false state, a uniform challenge makes it true with probability at most
  `ε i`. -/
  rbr : ∀ (i : (P j).ChallengeIdx) x d (tr : (P j).Transcript i.1.castSucc),
    ¬ S i.1.castSucc (x, d) tr →
      Pr[ch ← (P j).Challenge i : S i.1.succ (x, d) ((P j).concat tr ch)] ≤ ε i
  /-- (iv) A full transcript with a false state has its output outside `R₂`. -/
  out_not_mem : ∀ x d (f : FullTr P (leaf j)), ¬ S (Fin.last (n j)) (x, d) (f (.here j)) →
    (A.out x f, d) ∉ R₂

/-- **The "if" direction of paper `lem:red-prefix`**: a prefix state function with (i)-(iv) is a
state function of `def:red-sec` (a) with the same errors. -/
theorem PrefixRBR.toRBR {A : Reduction P (leaf j) D X₁ X₂} {R₁ : Set (X₁ × D)}
    {R₂ : Set (X₂ × D)} {S : (k : Fin (n j + 1)) → X₁ × D → (P j).Transcript k → Prop}
    {ε : (P j).ChallengeIdx → ℝ≥0} (h : A.PrefixRBR R₁ R₂ S ε) :
    A.RBR R₁ R₂ (CausalStateFn.ofLeaf S) (errLeaf ε) where
  exists_flip x d f hin hout := by
    obtain ⟨i, hi⟩ := ProtocolSpec.Transcript.exists_flip (fun k tr => S k (x, d) tr)
      (fun k hk tr msg => h.next k hk x d tr msg) (f (.here j)) (h.start x d _ hin)
      (by_contra fun hS => h.out_not_mem x d f hS hout)
    exact ⟨⟨.here j, i⟩, hi⟩
  rbr c x d past hS := by
    obtain ⟨p, i⟩ := c
    cases p
    exact h.rbr i x d past.own hS

/-- The challenge `ch` after the prefix `tr` moves the leaf's state `S` from false to true, read
at the empty causal context. -/
abbrev leafFlip (S : CausalStateFn P (leaf j) (X₁ × D)) (i : (P j).ChallengeIdx) (s : X₁ × D)
    (tr : (P j).Transcript i.1.castSucc) (ch : (P j).Challenge i) : Prop :=
  FlipAt S ⟨.here j, i⟩ s ⟨CausalCtx.ofHere j, tr⟩ ch

/-- **The "only if" direction of paper `lem:red-prefix`**: from a state function of
`def:red-sec` (a), the prefix state that is true when the input is in `R₁` or the state has moved
from false to true at a challenge of the prefix satisfies (i)-(iv) with the same errors. -/
theorem RBR.prefixRBR {A : Reduction P (leaf j) D X₁ X₂} {R₁ : Set (X₁ × D)}
    {R₂ : Set (X₂ × D)} {S : CausalStateFn P (leaf j) (X₁ × D)} {ε : (P j).ChallengeIdx → ℝ≥0}
    (h : A.RBR R₁ R₂ S (errLeaf ε)) :
    A.PrefixRBR R₁ R₂ (ChallengeEventReduction.state (P j) (leafFlip S) (· ∈ R₁)) ε where
  start x d tr hin := by
    rintro (h' | h')
    · exact hin h'
    · exact ChallengeEventReduction.not_occurred_zero (P j) _ _ tr h'
  next m hm x d tr msg hn := by
    rintro (h' | h')
    · exact hn (.inl h')
    · exact hn (.inr
        ((ChallengeEventReduction.occurred_concat_prover_iff (P j) _ hm _ tr msg).mp h'))
  rbr i x d tr hn := by
    refine (probUniform_mono fun ch hch => ?_).trans
      (h.flip_le ⟨.here j, i⟩ x d ⟨CausalCtx.ofHere j, tr⟩)
    rcases hch with h' | h'
    · exact (hn (.inl h')).elim
    · rcases (ChallengeEventReduction.occurred_concat_challenge_iff (P j) _ i _ tr ch).mp h' with
        h' | h'
      · exact (hn (.inr h')).elim
      · exact h'
  out_not_mem x d f hS hout := by
    have hin : (x, d) ∉ R₁ := fun h' => hS (.inl h')
    obtain ⟨⟨p, i⟩, hc⟩ := h.exists_flip x d f hin hout
    cases p
    refine hS (.inr ⟨i, i.1.isLt, ?_⟩)
    have hctx : f.ctx (.here j) = CausalCtx.ofHere j := CausalCtx.eq_ofHere _
    simp only [FlipAt, FullTr.past, FullTr.challenges, hctx] at hc
    exact hc

/-- **Paper `lem:red-prefix`**: a reduction from `R₁` to `R₂` whose order is total (a one-leaf
term) has round-by-round soundness errors `ε` (`def:red-sec` (a)) if and only if some state
function on the transcript prefixes satisfies conditions (i)-(iv) (`PrefixRBR`). -/
@[headline]
theorem rbr_iff_prefixRBR {A : Reduction P (leaf j) D X₁ X₂} {R₁ : Set (X₁ × D)}
    {R₂ : Set (X₂ × D)} {ε : (P j).ChallengeIdx → ℝ≥0} :
    (∃ S, A.RBR R₁ R₂ S (errLeaf ε)) ↔ ∃ S, A.PrefixRBR R₁ R₂ S ε :=
  ⟨fun ⟨_, h⟩ => ⟨_, h.prefixRBR⟩, fun ⟨_, h⟩ => ⟨_, h.toRBR⟩⟩

end Reduction

end GordieHowe.IOP
