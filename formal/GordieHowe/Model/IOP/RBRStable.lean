-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.RBR

@[expose] public section

/-!
# Knowledge soundness at a one-shot extractor stable after the challenge prefixes

`knowledgeSoundness_of_rbr` reads a one-shot round-by-round extractor `E` on the full transcript
through `E.straightLine`, which tries every prefix. When `E` succeeding at the prefix before any
challenge round implies `E` succeeding on the full transcript (`StableAtChallenges`), the
straight-line search is not needed: knowledge soundness holds at `E` itself
(`knowledgeSoundness_of_rbr_of_stable`).

An extractor that reads a commit phase of several rounds is stable only after that phase
(`StableOutside`, outside the commit phase's challenge rounds). At those rounds the state may flip
only rarely whatever the extractor returns; then knowledge soundness again holds at `E` itself
(`knowledgeSoundness_of_rbr_of_stableOutside`). The extractors of the multi-circuit protocols read
the commitments and the circuits' commit rounds, so they are stable outside the commit rounds.
These are general facts about `rbrKnowledgeSoundness` and belong in `RBR.lean`; they live here so
that `RBR.lean`, imported by every protocol file, is not rebuilt for them.
-/

namespace GordieHowe.IOP

open ProtocolSpec
open scoped NNReal

variable {n : ℕ} {P : ProtocolSpec n} {StmtIn WitIn : Type}

/-- **Stability after the challenge prefixes**: whenever `E` returns a witness on the prefix
before a challenge round of a full transcript, it returns a witness on the full transcript. -/
def Extractor.StableAtChallenges (rel : Set (StmtIn × WitIn)) (E : Extractor P StmtIn WitIn) :
    Prop :=
  ∀ x (tr : P.Transcript (Fin.last n)) (i : P.ChallengeIdx),
    (x, E i.1.castSucc x (tr.take i.1.castSucc (Fin.le_last _))) ∈ rel →
      (x, E (Fin.last n) x tr) ∈ rel

/-- **Stability outside the challenge rounds `early`**: whenever `E` returns a witness on the
prefix before a challenge round of a full transcript that is not in `early`, it returns a witness
on the full transcript. -/
def Extractor.StableOutside (rel : Set (StmtIn × WitIn)) (E : Extractor P StmtIn WitIn)
    (early : P.ChallengeIdx → Prop) : Prop :=
  ∀ x (tr : P.Transcript (Fin.last n)) (i : P.ChallengeIdx), ¬ early i →
    (x, E i.1.castSucc x (tr.take i.1.castSucc (Fin.le_last _))) ∈ rel →
      (x, E (Fin.last n) x tr) ∈ rel

/-- Stability after every challenge prefix is stability outside no rounds. -/
theorem Extractor.StableAtChallenges.stableOutside {rel : Set (StmtIn × WitIn)}
    {E : Extractor P StmtIn WitIn} (h : E.StableAtChallenges rel) :
    E.StableOutside rel fun _ => False :=
  fun x tr i _ => h x tr i

open Classical Finset in
/-- `knowledgeSoundness_count_of_rbr_count` at an extractor stable outside the rounds `early`,
read on the full transcript: at a round of `early` the count bounds the state's flips whatever
the extractor returns. -/
theorem knowledgeSoundness_count_of_rbr_count_of_stableOutside [∀ i, Fintype (P.Challenge i)]
    [Fintype P.ChallengeIdx] {rel : Set (StmtIn × WitIn)} {V : Verifier P StmtIn}
    {ε : P.ChallengeIdx → ℝ≥0} (E : Extractor P StmtIn WitIn) {early : P.ChallengeIdx → Prop}
    (hstable : E.StableOutside rel early) (S : KnowledgeStateFunction V)
    (hE : ∀ (x : StmtIn) (i : P.ChallengeIdx) (tr : P.Transcript i.1.castSucc),
        ((Finset.univ.filter fun c : P.Challenge i =>
            (early i ∨ (x, E i.1.castSucc x tr) ∉ rel) ∧ ¬ S.toFun i.1.castSucc x tr ∧
              S.toFun i.1.succ x (P.concat tr c)).card : ℝ≥0) ≤
          ε i * Fintype.card (P.Challenge i))
    (x : StmtIn) (prv : Prover P StmtIn) :
    ((Finset.univ.filter fun ch : P.Challenges =>
        V x (prv.run x ch) = true ∧ (x, E (Fin.last n) x (prv.run x ch)) ∉ rel).card : ℝ≥0) ≤
      (∑ i, ε i) * Fintype.card P.Challenges := by
  let B : P.ChallengeIdx → Finset P.Challenges := fun i =>
    {ch | (early i ∨ (x, E i.1.castSucc x (prv.runTo x ch i.1 i.1.2.le)) ∉ rel) ∧
      ¬ S.toFun i.1.castSucc x (prv.runTo x ch i.1 i.1.2.le) ∧
      S.toFun i.1.succ x (P.concat (prv.runTo x ch i.1 i.1.2.le) (ch i))}
  have hsub : ({ch | V x (prv.run x ch) = true ∧ (x, E (Fin.last n) x (prv.run x ch)) ∉ rel} :
      Finset P.Challenges) ⊆ univ.biUnion B := by
    intro ch hch
    rw [mem_filter] at hch
    obtain ⟨i, hi⟩ := S.exists_flip (S.toFun_full x _ hch.2.1)
    have hpre : (prv.run x ch).take i.1.castSucc (Fin.le_last _) =
        prv.runTo x ch i.1 i.1.2.le :=
      prv.take_runTo x ch le_rfl i.1.castSucc (Fin.le_last _)
    have hfail : early i ∨ (x, E i.1.castSucc x (prv.runTo x ch i.1 i.1.2.le)) ∉ rel := by
      by_cases he : early i
      · exact .inl he
      · rw [← hpre]
        exact .inr fun h => hch.2.2 (hstable x _ i he h)
    exact mem_biUnion.mpr ⟨i, mem_univ i, mem_filter.mpr ⟨mem_univ ch, hfail, hi⟩⟩
  have hB : ∀ i, (#(B i) : ℝ≥0) ≤ ε i * Fintype.card P.Challenges := by
    intro i
    refine card_le_of_card_update_le i fun f => le_trans (Nat.cast_le.mpr (card_le_card ?_))
      (hE x i (prv.runTo x f i.1 i.1.2.le))
    intro c hc
    have hpre : prv.runTo x (Function.update f i c) i.1 i.1.2.le = prv.runTo x f i.1 i.1.2.le :=
      prv.runTo_congr x i.1.2.le fun j hj => Function.update_of_ne (by rintro rfl; omega) c f
    simp only [B, mem_filter, mem_univ, true_and, hpre, Function.update_self] at hc
    simpa only [mem_filter, mem_univ, true_and] using hc
  calc (#{ch | V x (prv.run x ch) = true ∧ (x, E (Fin.last n) x (prv.run x ch)) ∉ rel} : ℝ≥0)
      ≤ #(univ.biUnion B) := Nat.cast_le.mpr (card_le_card hsub)
    _ ≤ ∑ i, (#(B i) : ℝ≥0) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ i, ε i * Fintype.card P.Challenges := sum_le_sum fun i _ => hB i
    _ = (∑ i, ε i) * Fintype.card P.Challenges := (sum_mul ..).symm

open Classical Finset in
/-- `knowledgeSoundness_count_of_rbr_count` at a stable extractor read on the full
transcript. -/
theorem knowledgeSoundness_count_of_rbr_count_of_stable [∀ i, Fintype (P.Challenge i)]
    [Fintype P.ChallengeIdx] {rel : Set (StmtIn × WitIn)} {V : Verifier P StmtIn}
    {ε : P.ChallengeIdx → ℝ≥0} (E : Extractor P StmtIn WitIn) (hstable : E.StableAtChallenges rel)
    (S : KnowledgeStateFunction V)
    (hE : ∀ (x : StmtIn) (i : P.ChallengeIdx) (tr : P.Transcript i.1.castSucc),
        ((Finset.univ.filter fun c : P.Challenge i =>
            (x, E i.1.castSucc x tr) ∉ rel ∧ ¬ S.toFun i.1.castSucc x tr ∧
              S.toFun i.1.succ x (P.concat tr c)).card : ℝ≥0) ≤
          ε i * Fintype.card (P.Challenge i))
    (x : StmtIn) (prv : Prover P StmtIn) :
    ((Finset.univ.filter fun ch : P.Challenges =>
        V x (prv.run x ch) = true ∧ (x, E (Fin.last n) x (prv.run x ch)) ∉ rel).card : ℝ≥0) ≤
      (∑ i, ε i) * Fintype.card P.Challenges :=
  knowledgeSoundness_count_of_rbr_count_of_stableOutside E hstable.stableOutside S
    (fun x i tr => by simpa only [false_or] using hE x i tr) x prv

/-- **Round-by-round knowledge soundness implies knowledge soundness at a stable extractor**,
with the summed error, at the extractor itself (no straight-line search). -/
theorem knowledgeSoundness_of_rbr_of_stable [∀ i, Fintype (P.Challenge i)]
    [∀ i, Nonempty (P.Challenge i)] [Fintype P.ChallengeIdx] {rel : Set (StmtIn × WitIn)}
    {V : Verifier P StmtIn} {E : Extractor P StmtIn WitIn} {S : KnowledgeStateFunction V}
    {ε : P.ChallengeIdx → ℝ≥0} (h : rbrKnowledgeSoundness rel V E S ε)
    (hstable : E.StableAtChallenges rel) :
    knowledgeSoundness rel V E (∑ i, ε i) :=
  knowledgeSoundness_iff_count.mpr
    (knowledgeSoundness_count_of_rbr_count_of_stable E hstable S
      (rbrKnowledgeSoundness_iff_count.mp h))

open Classical in
/-- **The state flips at round `i` on at most `ε i · |C_i|` challenges** at every statement and
every prefix, whatever the extractor returns. -/
def KnowledgeStateFunction.FlipsAtMost [∀ i, Fintype (P.Challenge i)] {V : Verifier P StmtIn}
    (S : KnowledgeStateFunction V) (ε : P.ChallengeIdx → ℝ≥0) (i : P.ChallengeIdx) : Prop :=
  ∀ x (tr : P.Transcript i.1.castSucc),
    ((Finset.univ.filter fun c : P.Challenge i =>
        ¬ S.toFun i.1.castSucc x tr ∧ S.toFun i.1.succ x (P.concat tr c)).card : ℝ≥0) ≤
      ε i * Fintype.card (P.Challenge i)

/-- **Round-by-round knowledge soundness implies knowledge soundness at an extractor stable
outside the rounds `early`**, with the summed error, at the extractor itself, when at every round
of `early` at most `ε i · |C_i|` challenges flip the state whatever the extractor returns
(`hearly`). -/
theorem knowledgeSoundness_of_rbr_of_stableOutside [∀ i, Fintype (P.Challenge i)]
    [∀ i, Nonempty (P.Challenge i)] [Fintype P.ChallengeIdx] {rel : Set (StmtIn × WitIn)}
    {V : Verifier P StmtIn} {E : Extractor P StmtIn WitIn} {S : KnowledgeStateFunction V}
    {ε : P.ChallengeIdx → ℝ≥0} (h : rbrKnowledgeSoundness rel V E S ε)
    {early : P.ChallengeIdx → Prop} (hearly : ∀ i, early i → S.FlipsAtMost ε i)
    (hstable : E.StableOutside rel early) :
    knowledgeSoundness rel V E (∑ i, ε i) := by
  refine knowledgeSoundness_iff_count.mpr
    (knowledgeSoundness_count_of_rbr_count_of_stableOutside E hstable S (fun x i tr => ?_))
  by_cases he : early i
  · refine le_trans (Nat.cast_le.mpr (Finset.card_le_card fun c hc => ?_)) (hearly i he x tr)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact hc.2
  · refine le_trans (Nat.cast_le.mpr (Finset.card_le_card fun c hc => ?_))
      (rbrKnowledgeSoundness_iff_count.mp h x i tr)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact ⟨hc.1.resolve_left he, hc.2⟩

end GordieHowe.IOP
