-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Ligero.TwoStageTest

@[expose] public section

/-!
# Round-by-round knowledge soundness of a two-stage test

The two-stage test (`TwoStageTest.spec`: a prover message, an algebraic challenge, a response, a
query) as a protocol with its own statement, verdict and extractor, without a claim fixed before
the protocol. The state function (`knowledgeState`) is `TwoStageTest.state` with the claim false:
false before the algebraic challenge, the bad event `bad` of the prover message and the challenge
after it, and the bad event or acceptance on the full transcript. Round-by-round knowledge
soundness (`rbrKnowledgeSoundness_of_counts`) then follows from two counts:

* at the algebraic challenge, at most `εtest · |Challenge|` challenges are bad for every prover
  message (`htest`);
* at the query, at every prefix where the extractor fails and the challenge was not bad, at most
  `εquery · |Query|` queries are accepted (`hquery`).

The extractor is read only at the query round: before the algebraic challenge the state flips only
through `bad`, whatever the extractor returns. This is the shape of Ligero when the low-degree
challenge is sent with the constraint challenge (`GordieHowe.Ligero.LongfellowOrder`): the extractor reads the
low-degree response, sent after the joint challenge.
-/

namespace GordieHowe.Ligero.TwoStageTest
open IOP

open scoped NNReal

variable {Aux Challenge Response Query Ctx : Type}

/-- **The verdict of a two-stage test**: `accept` on the context and the four messages. -/
def verifier (accept : Ctx → Aux → Challenge → Response → Query → Bool) :
    Verifier (spec Aux Challenge Response Query) Ctx :=
  fun c tr => accept c (tr ⟨0, by decide +revert⟩) (tr ⟨1, by decide +revert⟩)
    (tr ⟨2, by decide +revert⟩) (tr ⟨3, by decide⟩)

variable (bad : Ctx → Aux → Challenge → Prop)
  (accept : Ctx → Aux → Challenge → Response → Query → Bool)

/-- **The knowledge state function of a two-stage test** (CMS19 Definition 8.3): the state
`TwoStageTest.state` with the claim false, so false before the algebraic challenge, `bad` on the
prover message and the challenge after it, and `bad` or acceptance on the full transcript. Not
required to be efficient. -/
def knowledgeState : KnowledgeStateFunction (verifier accept) where
  toFun := state (fun _ : Ctx => False) bad accept
  toFun_empty _ _ h := h
  toFun_next m hdir c tr msg hn := by
    fin_cases m
    · exact hn
    · change Direction.V_to_P = Direction.P_to_V at hdir; cases hdir
    · change ¬(False ∨ bad c
        ((spec Aux Challenge Response Query).concat (m := ⟨2, by decide⟩) tr msg ⟨0, by decide⟩)
        ((spec Aux Challenge Response Query).concat (m := ⟨2, by decide⟩) tr msg ⟨1, by decide⟩))
      rw [concat2_0, concat2_1]
      exact hn
    · change Direction.V_to_P = Direction.P_to_V at hdir; cases hdir
  toFun_full _ _ h := Or.inr (Or.inr h)

open scoped Classical in
/-- **The algebraic challenge of a two-stage test**: before it the state is false, and after it
the state is `bad`, so at most the bad challenges flip it, whatever the extractor returns. -/
theorem test_knowledge_bound [Fintype Challenge] {W : Type} (rel : Set (Ctx × W))
    (E : Extractor (spec Aux Challenge Response Query) Ctx W) (εtest : ℝ≥0)
    (htest : ∀ c a,
      ((Finset.univ.filter fun ch => bad c a ch).card : ℝ≥0) ≤ εtest * Fintype.card Challenge)
    (c : Ctx) (tr : (spec Aux Challenge Response Query).Transcript ⟨1, by decide⟩) :
    ((Finset.univ.filter fun ch : Challenge =>
      (c, E ⟨1, by decide⟩ c tr) ∉ rel ∧ ¬ state (fun _ : Ctx => False) bad accept ⟨1, by decide⟩ c tr ∧
        state (fun _ : Ctx => False) bad accept ⟨2, by decide⟩ c
          ((spec Aux Challenge Response Query).concat (m := ⟨1, by decide⟩) tr ch)).card : ℝ≥0) ≤
      εtest * Fintype.card Challenge :=
  le_trans (Nat.cast_le.mpr (Finset.card_le_card fun _ hch =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hch).2.2⟩))
    (test_flip_bound (fun _ : Ctx => False) bad accept εtest (fun c a _ => htest c a) c tr)

open scoped Classical in
/-- **The query round of a two-stage test**: at a prefix where the extractor fails and the
challenge was not bad, the state becomes true only through acceptance, so at most the accepted
queries flip it. -/
theorem query_knowledge_bound [Fintype Query] {W : Type} (rel : Set (Ctx × W))
    (E : Extractor (spec Aux Challenge Response Query) Ctx W) (εquery : ℝ≥0)
    (hquery : ∀ c (tr : (spec Aux Challenge Response Query).Transcript ⟨3, by decide⟩),
      (c, E ⟨3, by decide⟩ c tr) ∉ rel → ¬ bad c (tr ⟨0, by decide⟩) (tr ⟨1, by decide⟩) →
      ((Finset.univ.filter fun q =>
          accept c (tr ⟨0, by decide⟩) (tr ⟨1, by decide⟩) (tr ⟨2, by decide⟩) q = true).card :
            ℝ≥0) ≤ εquery * Fintype.card Query)
    (c : Ctx) (tr : (spec Aux Challenge Response Query).Transcript ⟨3, by decide⟩) :
    ((Finset.univ.filter fun q : Query =>
      (c, E ⟨3, by decide⟩ c tr) ∉ rel ∧ ¬ state (fun _ : Ctx => False) bad accept ⟨3, by decide⟩ c tr ∧
        state (fun _ : Ctx => False) bad accept ⟨4, by decide⟩ c
          ((spec Aux Challenge Response Query).concat (m := ⟨3, by decide⟩) tr q)).card : ℝ≥0) ≤
      εquery * Fintype.card Query := by
  by_cases hE : (c, E ⟨3, by decide⟩ c tr) ∈ rel
  · refine le_trans (Nat.cast_le.mpr (Finset.card_le_card
      (t := (∅ : Finset Query)) fun q hq => ?_)) (by simp)
    exact absurd hE (Finset.mem_filter.mp hq).2.1
  · by_cases hb : bad c (tr ⟨0, by decide⟩) (tr ⟨1, by decide⟩)
    · refine le_trans (Nat.cast_le.mpr (Finset.card_le_card
        (t := (∅ : Finset Query)) fun q hq => ?_)) (by simp)
      exact absurd (Or.inr hb) (Finset.mem_filter.mp hq).2.2.1
    · refine le_trans (Nat.cast_le.mpr (Finset.card_le_card fun q hq => ?_)) (hquery c tr hE hb)
      have h4 := (Finset.mem_filter.mp hq).2.2.2
      rw [state_4, concat3_0, concat3_1, concat3_2, concat3_3] at h4
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ((h4.resolve_left id).resolve_left hb)⟩

open scoped Classical in
/-- **Round-by-round knowledge soundness of a two-stage test**, at the extractor `E`, the state
function `knowledgeState` and the errors `εtest` at the algebraic challenge and `εquery` at the
query: from the count of bad challenges at every prover message (`htest`) and the count of
accepted queries at every prefix where the extractor fails and the challenge was not bad
(`hquery`). -/
theorem rbrKnowledgeSoundness_of_counts [Fintype Challenge] [Fintype Query] [Nonempty Challenge]
    [Nonempty Query] {W : Type} (rel : Set (Ctx × W))
    (E : Extractor (spec Aux Challenge Response Query) Ctx W) (εtest εquery : ℝ≥0)
    (htest : ∀ c a,
      ((Finset.univ.filter fun ch => bad c a ch).card : ℝ≥0) ≤ εtest * Fintype.card Challenge)
    (hquery : ∀ c (tr : (spec Aux Challenge Response Query).Transcript ⟨3, by decide⟩),
      (c, E ⟨3, by decide⟩ c tr) ∉ rel → ¬ bad c (tr ⟨0, by decide⟩) (tr ⟨1, by decide⟩) →
      ((Finset.univ.filter fun q =>
          accept c (tr ⟨0, by decide⟩) (tr ⟨1, by decide⟩) (tr ⟨2, by decide⟩) q = true).card :
            ℝ≥0) ≤ εquery * Fintype.card Query) :
    rbrKnowledgeSoundness rel (verifier accept) E (knowledgeState bad accept)
      (error εtest εquery) := by
  refine rbrKnowledgeSoundness_iff_count.mpr fun c i tr => ?_
  rcases i with ⟨⟨k, hk⟩, hd⟩
  match k with
  | 0 => cases hd
  | 1 => exact test_knowledge_bound bad accept rel E εtest htest c tr
  | 2 => cases hd
  | j + 3 =>
    have hj : j = 0 := by omega
    subst j
    exact query_knowledge_bound bad accept rel E εquery hquery c tr

end GordieHowe.Ligero.TwoStageTest
