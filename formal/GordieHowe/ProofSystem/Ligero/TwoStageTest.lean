-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.Append
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Two-stage algebraic and query tests

A prover fixes auxiliary data before an algebraic challenge, then fixes its
response before the column query. Explicit finite counting bounds yield a
round-by-round `ClaimProof`; auxiliary data and responses can be infinite types.
The first bound quantifies over every auxiliary message, and the second over
every response outside the first-stage bad event.
-/

namespace GordieHowe.Ligero.TwoStageTest
open IOP

open scoped NNReal

variable (Aux Challenge Response Query : Type)

abbrev spec : ProtocolSpec 4 where
  dir i := if i.val = 1 ∨ i.val = 3 then .V_to_P else .P_to_V
  «Type» i := match i.val with
    | 0 => Aux
    | 1 => Challenge
    | 2 => Response
    | _ => Query

/-- The test round: the verifier's first challenge. -/
abbrev testRound : (spec Aux Challenge Response Query).ChallengeIdx := ⟨1, rfl⟩
/-- The query round: the verifier's second challenge, the opened columns. -/
abbrev queryRound : (spec Aux Challenge Response Query).ChallengeIdx := ⟨3, rfl⟩

theorem challenge_cases (i : (spec Aux Challenge Response Query).ChallengeIdx) :
    i = testRound Aux Challenge Response Query ∨ i = queryRound Aux Challenge Response Query := by
  rcases i with ⟨i, hi⟩
  fin_cases i
  · change Direction.P_to_V = Direction.V_to_P at hi; cases hi
  · exact Or.inl rfl
  · change Direction.P_to_V = Direction.V_to_P at hi; cases hi
  · exact Or.inr rfl

instance [Fintype Challenge] [Fintype Query]
    (i : (spec Aux Challenge Response Query).ChallengeIdx) :
    Fintype ((spec Aux Challenge Response Query).Challenge i) := by
  rcases i with ⟨⟨n, hn⟩, hi⟩
  match n with
  | 0 => cases hi
  | 1 => exact inferInstanceAs (Fintype Challenge)
  | 2 => cases hi
  | k + 3 =>
    have hk : k = 0 := by omega
    subst k
    exact inferInstanceAs (Fintype Query)

instance [DecidableEq Challenge] [DecidableEq Query]
    (i : (spec Aux Challenge Response Query).ChallengeIdx) :
    DecidableEq ((spec Aux Challenge Response Query).Challenge i) := by
  rcases i with ⟨⟨n, hn⟩, hi⟩
  match n with
  | 0 => cases hi
  | 1 => exact inferInstanceAs (DecidableEq Challenge)
  | 2 => cases hi
  | k + 3 =>
    have hk : k = 0 := by omega
    subst k
    exact inferInstanceAs (DecidableEq Query)

instance [Nonempty Challenge] [Nonempty Query]
    (i : (spec Aux Challenge Response Query).ChallengeIdx) :
    Nonempty ((spec Aux Challenge Response Query).Challenge i) := by
  rcases i with ⟨⟨n, hn⟩, hi⟩
  match n with
  | 0 => cases hi
  | 1 => exact inferInstanceAs (Nonempty Challenge)
  | 2 => cases hi
  | k + 3 =>
    have hk : k = 0 := by omega
    subst k
    exact inferInstanceAs (Nonempty Query)

instance : Fintype (spec Aux Challenge Response Query).ChallengeIdx :=
  inferInstanceAs (Fintype (Subtype _))

/-- The challenge of the query round is a `Tableau.Query`. -/
def queryEquiv : (spec Aux Challenge Response Query).Challenge (queryRound Aux Challenge Response Query) ≃ Query :=
  Equiv.refl _

variable {Aux Challenge Response Query} {Ctx : Type}

def error (εtest εquery : ℝ≥0)
    (i : (spec Aux Challenge Response Query).ChallengeIdx) : ℝ≥0 :=
  if i.val.val = 1 then εtest else εquery

theorem error_sum (εtest εquery : ℝ≥0) :
    ∑ i, error (Aux := Aux) (Challenge := Challenge) (Response := Response) (Query := Query) εtest εquery i =
      εtest + εquery := by
  classical
  have hu : (Finset.univ : Finset (spec Aux Challenge Response Query).ChallengeIdx) =
      {testRound Aux Challenge Response Query, queryRound Aux Challenge Response Query} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact challenge_cases Aux Challenge Response Query i
  rw [hu, Finset.sum_pair (by intro h; have hh := congrArg (fun i => i.val.val) h; change (1 : ℕ) = 3 at hh; omega)]
  rfl

@[simp] theorem concat1_0 (tr : (spec Aux Challenge Response Query).Transcript ⟨1, by decide⟩)
    (msg : Challenge) : (spec Aux Challenge Response Query).concat (m := ⟨1, by decide⟩) tr msg
      ⟨0, by decide⟩ = tr ⟨0, by decide⟩ :=
  ProtocolSpec.concat_apply_of_lt (P := spec Aux Challenge Response Query) (m := ⟨1, by decide⟩) tr msg 0 (by decide)

@[simp] theorem concat1_1 (tr : (spec Aux Challenge Response Query).Transcript ⟨1, by decide⟩)
    (msg : Challenge) : (spec Aux Challenge Response Query).concat (m := ⟨1, by decide⟩) tr msg
      ⟨1, by decide⟩ = msg :=
  ProtocolSpec.concat_apply_last (P := spec Aux Challenge Response Query) (m := ⟨1, by decide⟩) tr msg

@[simp] theorem concat2_0 (tr : (spec Aux Challenge Response Query).Transcript ⟨2, by decide⟩)
    (msg : Response) : (spec Aux Challenge Response Query).concat (m := ⟨2, by decide⟩) tr msg
      ⟨0, by decide⟩ = tr ⟨0, by decide⟩ :=
  ProtocolSpec.concat_apply_of_lt (P := spec Aux Challenge Response Query) (m := ⟨2, by decide⟩) tr msg 0 (by decide)

@[simp] theorem concat2_1 (tr : (spec Aux Challenge Response Query).Transcript ⟨2, by decide⟩)
    (msg : Response) : (spec Aux Challenge Response Query).concat (m := ⟨2, by decide⟩) tr msg
      ⟨1, by decide⟩ = tr ⟨1, by decide⟩ :=
  ProtocolSpec.concat_apply_of_lt (P := spec Aux Challenge Response Query) (m := ⟨2, by decide⟩) tr msg 1 (by decide)

@[simp] theorem concat2_2 (tr : (spec Aux Challenge Response Query).Transcript ⟨2, by decide⟩)
    (msg : Response) : (spec Aux Challenge Response Query).concat (m := ⟨2, by decide⟩) tr msg
      ⟨2, by decide⟩ = msg :=
  ProtocolSpec.concat_apply_last (P := spec Aux Challenge Response Query) (m := ⟨2, by decide⟩) tr msg

@[simp] theorem concat3_0 (tr : (spec Aux Challenge Response Query).Transcript ⟨3, by decide⟩)
    (msg : Query) : (spec Aux Challenge Response Query).concat (m := ⟨3, by decide⟩) tr msg
      ⟨0, by decide⟩ = tr ⟨0, by decide⟩ :=
  ProtocolSpec.concat_apply_of_lt (P := spec Aux Challenge Response Query) (m := ⟨3, by decide⟩) tr msg 0 (by decide)

@[simp] theorem concat3_1 (tr : (spec Aux Challenge Response Query).Transcript ⟨3, by decide⟩)
    (msg : Query) : (spec Aux Challenge Response Query).concat (m := ⟨3, by decide⟩) tr msg
      ⟨1, by decide⟩ = tr ⟨1, by decide⟩ :=
  ProtocolSpec.concat_apply_of_lt (P := spec Aux Challenge Response Query) (m := ⟨3, by decide⟩) tr msg 1 (by decide)

@[simp] theorem concat3_2 (tr : (spec Aux Challenge Response Query).Transcript ⟨3, by decide⟩)
    (msg : Query) : (spec Aux Challenge Response Query).concat (m := ⟨3, by decide⟩) tr msg
      ⟨2, by decide⟩ = tr ⟨2, by decide⟩ :=
  ProtocolSpec.concat_apply_of_lt (P := spec Aux Challenge Response Query) (m := ⟨3, by decide⟩) tr msg 2 (by decide)

@[simp] theorem concat3_3 (tr : (spec Aux Challenge Response Query).Transcript ⟨3, by decide⟩)
    (msg : Query) : (spec Aux Challenge Response Query).concat (m := ⟨3, by decide⟩) tr msg
      ⟨3, by decide⟩ = msg :=
  ProtocolSpec.concat_apply_last (P := spec Aux Challenge Response Query) (m := ⟨3, by decide⟩) tr msg


variable (claim : Ctx → Prop) (bad : Ctx → Aux → Challenge → Prop)
    (accept : Ctx → Aux → Challenge → Response → Query → Bool)

/-- At the algebraic challenge the state can become true through `bad`; at the
query challenge it can additionally become true through acceptance. -/
def state (m : Fin 5) (c : Ctx) (tr : (spec Aux Challenge Response Query).Transcript m) : Prop :=
  if h : m.val < 2 then claim c else
    let b := bad c (tr ⟨0, by omega⟩) (tr ⟨1, by omega⟩)
    if h' : m.val < 4 then claim c ∨ b else
      claim c ∨ b ∨ accept c (tr ⟨0, by omega⟩) (tr ⟨1, by omega⟩)
        (tr ⟨2, by omega⟩) (tr ⟨3, by omega⟩) = true

theorem state_0 (c : Ctx) (tr : (spec Aux Challenge Response Query).Transcript ⟨0, by decide⟩) :
    state claim bad accept ⟨0, by decide⟩ c tr ↔ claim c := Iff.rfl

theorem state_1 (c : Ctx) (tr : (spec Aux Challenge Response Query).Transcript ⟨1, by decide⟩) :
    state claim bad accept ⟨1, by decide⟩ c tr ↔ claim c := Iff.rfl

theorem state_2 (c : Ctx) (tr : (spec Aux Challenge Response Query).Transcript ⟨2, by decide⟩) :
    state claim bad accept ⟨2, by decide⟩ c tr ↔ claim c ∨ bad c (tr ⟨0, by decide +revert⟩) (tr ⟨1, by decide⟩) := Iff.rfl

theorem state_3 (c : Ctx) (tr : (spec Aux Challenge Response Query).Transcript ⟨3, by decide⟩) :
    state claim bad accept ⟨3, by decide⟩ c tr ↔ claim c ∨ bad c (tr ⟨0, by decide +revert⟩) (tr ⟨1, by decide⟩) := Iff.rfl

theorem state_4 (c : Ctx) (tr : (spec Aux Challenge Response Query).Transcript ⟨4, by decide⟩) :
    state claim bad accept ⟨4, by decide⟩ c tr ↔ claim c ∨ bad c (tr ⟨0, by decide +revert⟩) (tr ⟨1, by decide⟩) ∨ accept c (tr ⟨0, by decide +revert⟩) (tr ⟨1, by decide +revert⟩) (tr ⟨2, by decide +revert⟩) (tr ⟨3, by decide⟩) = true := Iff.rfl


open scoped Classical

variable [Fintype Challenge] [Fintype Query] (εtest εquery : ℝ≥0)
    (htest : ∀ c a, ¬ claim c →
      ((Finset.univ.filter fun ch => bad c a ch).card : ℝ≥0) ≤ εtest * Fintype.card Challenge)
    (hquery : ∀ c a ch r, ¬ claim c → ¬ bad c a ch →
      ((Finset.univ.filter fun q => accept c a ch r q = true).card : ℝ≥0) ≤
        εquery * Fintype.card Query)

omit [Fintype Query] in
include htest in
theorem test_flip_bound (c : Ctx)
    (tr : (spec Aux Challenge Response Query).Transcript ⟨1, by decide⟩) :
    ((Finset.univ.filter fun ch : Challenge =>
      ¬ state claim bad accept ⟨1, by decide⟩ c tr ∧
      state claim bad accept ⟨2, by decide⟩ c
        ((spec Aux Challenge Response Query).concat (m := ⟨1, by decide⟩) tr ch)).card : ℝ≥0) ≤
      εtest * Fintype.card Challenge := by
  simp only [state_1, state_2, concat1_0, concat1_1]
  by_cases hc : claim c
  · simp [hc]
  · refine le_of_eq_of_le ?_ (htest c (tr ⟨0, by decide⟩) hc)
    congr 2
    ext ch
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hc, not_false_eq_true, false_or]

omit [Fintype Challenge] in
include hquery in
theorem query_flip_bound (c : Ctx)
    (tr : (spec Aux Challenge Response Query).Transcript ⟨3, by decide⟩) :
    ((Finset.univ.filter fun q : Query =>
      ¬ state claim bad accept ⟨3, by decide⟩ c tr ∧
      state claim bad accept ⟨4, by decide⟩ c
        ((spec Aux Challenge Response Query).concat (m := ⟨3, by decide⟩) tr q)).card : ℝ≥0) ≤
      εquery * Fintype.card Query := by
  simp only [state_3, state_4, concat3_0, concat3_1, concat3_2, concat3_3]
  by_cases hc : claim c
  · simp [hc]
  · by_cases hb : bad c (tr ⟨0, by decide⟩) (tr ⟨1, by decide⟩)
    · refine le_trans (Nat.cast_le.mpr (Finset.card_le_card
        (t := (∅ : Finset Query)) ?_)) (by simp)
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      exact (hq.1 (Or.inr hb)).elim
    · refine le_of_eq_of_le ?_
        (hquery c (tr ⟨0, by decide⟩) (tr ⟨1, by decide⟩) (tr ⟨2, by decide⟩) hc hb)
      congr 2
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hc, hb, false_or, not_false_eq_true]

include htest hquery in
/-- The two stage counting bounds control each verifier round's state flip. -/
theorem rbr_bound (c : Ctx) (i : (spec Aux Challenge Response Query).ChallengeIdx)
    (tr : (spec Aux Challenge Response Query).Transcript i.val.castSucc) :
    ((Finset.univ.filter fun ch : (spec Aux Challenge Response Query).Challenge i =>
      ¬ state claim bad accept i.val.castSucc c tr ∧
        state claim bad accept i.val.succ c ((spec Aux Challenge Response Query).concat tr ch)).card : ℝ≥0) ≤
      error εtest εquery i * Fintype.card ((spec Aux Challenge Response Query).Challenge i) := by
  rcases i with ⟨⟨k, hk⟩, hd⟩
  match k with
  | 0 => cases hd
  | 1 => exact test_flip_bound claim bad accept εtest htest c tr
  | 2 => cases hd
  | j + 3 =>
    have hj : j = 0 := by omega
    subst j
    exact query_flip_bound claim bad accept εquery hquery c tr

/-- Assemble the two counting lemmas into the four-round interactive protocol.
Neither stage assumes soundness of an entire proof system. -/
def proof : ClaimProof (spec Aux Challenge Response Query) Ctx (error εtest εquery) where
  claim := claim
  V c tr := accept c (tr ⟨0, by decide +revert⟩) (tr ⟨1, by decide +revert⟩) (tr ⟨2, by decide +revert⟩) (tr ⟨3, by decide⟩)
  S := state claim bad accept
  start c tr hc := by simpa [state] using hc
  next m hdir c tr msg hn := by
    fin_cases m
    · exact hn
    · change Direction.V_to_P = Direction.P_to_V at hdir; cases hdir
    · change ¬(claim c ∨ bad c
        ((spec Aux Challenge Response Query).concat (m := ⟨2, by decide⟩) tr msg ⟨0, by decide⟩)
        ((spec Aux Challenge Response Query).concat (m := ⟨2, by decide⟩) tr msg ⟨1, by decide⟩))
      rw [concat2_0, concat2_1]
      exact hn
    · change Direction.V_to_P = Direction.P_to_V at hdir; cases hdir
  full c tr h := by
    change claim c ∨ bad c (tr ⟨0, by decide +revert⟩) (tr ⟨1, by decide⟩) ∨ _
    exact Or.inr (Or.inr h)
  rbr := rbr_bound claim bad accept εtest εquery htest hquery

end GordieHowe.Ligero.TwoStageTest
