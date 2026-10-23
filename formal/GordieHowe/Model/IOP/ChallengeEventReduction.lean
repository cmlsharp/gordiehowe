-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.ClaimReduction

@[expose] public section

/-!
# Constructing a reduction from local challenge events

The local counting premise must hold at every adversarial prefix. The final
soundness implication is a deterministic composition obligation, not an
external assumption about any particular proof system. Applications discharge
both premises with their concrete transition and polynomial lemmas.
-/

namespace GordieHowe.IOP.ChallengeEventReduction

open scoped Classical NNReal

variable {n : ℕ} (P : ProtocolSpec n) {Ctx : Type}
    (bad : (i : P.ChallengeIdx) → Ctx → P.Transcript i.1.castSucc → P.Challenge i → Prop)

/-- A local challenge event that occurred in the available transcript prefix. -/
def Occurred (m : Fin (n + 1)) (c : Ctx) (tr : P.Transcript m) : Prop :=
  ∃ i : P.ChallengeIdx, ∃ hi : i.1.val < m.val,
    bad i c (tr.take i.1.castSucc (by change i.1.val ≤ m.val; omega))
      (tr ⟨i.1.val, hi⟩)

theorem not_occurred_zero (c : Ctx) (tr : P.Transcript 0) : ¬ Occurred P bad 0 c tr := by
  rintro ⟨i, hi, _⟩
  exact Nat.not_lt_zero _ hi

/-- Restricting an already restricted transcript is just restriction. -/
theorem take_take {k j m : Fin (n + 1)} (tr : P.Transcript k)
    (hjk : j ≤ k) (hmj : m ≤ j) :
    (tr.take j hjk).take m hmj = tr.take m (hmj.trans hjk) := by
  funext i
  rfl

/-- An earlier event remains the same after a prover or verifier message. -/
theorem occurred_concat_of_occurred {m : Fin n} (c : Ctx)
    (tr : P.Transcript m.castSucc) (msg : P.Type m)
    (h : Occurred P bad m.castSucc c tr) :
    Occurred P bad m.succ c (P.concat tr msg) := by
  obtain ⟨i, hi, hb⟩ := h
  change i.1.val < m.val at hi
  refine ⟨i, by simpa using Nat.lt_succ_of_lt hi, ?_⟩
  have hle : i.1.castSucc ≤ m.castSucc := by change i.1.val ≤ m.val; omega
  rw [P.take_concat tr msg i.1.castSucc hle]
  simpa only [P.concat_apply_of_lt tr msg i.1.val hi] using hb

/-- An event strictly before the appended round already occurred before it. -/
theorem earlier_of_concat {m : Fin n} (c : Ctx)
    (tr : P.Transcript m.castSucc) (msg : P.Type m)
    (i : P.ChallengeIdx) (hi : i.1.val < m.val)
    (hb : bad i c ((P.concat tr msg).take i.1.castSucc (by change i.1.val ≤ m.val+1; omega))
      ((P.concat tr msg) ⟨i.1.val, by change i.1.val < m.val+1; omega⟩)) :
    Occurred P bad m.castSucc c tr := by
  refine ⟨i, hi, ?_⟩
  have hle : i.1.castSucc ≤ m.castSucc := by change i.1.val ≤ m.val; omega
  rw [P.take_concat tr msg i.1.castSucc hle] at hb
  simpa only [P.concat_apply_of_lt tr msg i.1.val hi] using hb

/-- Appending a prover message cannot introduce a new challenge event. -/
theorem occurred_concat_prover_iff {m : Fin n} (hm : P.dir m = .P_to_V)
    (c : Ctx) (tr : P.Transcript m.castSucc) (msg : P.Type m) :
    Occurred P bad m.succ c (P.concat tr msg) ↔ Occurred P bad m.castSucc c tr := by
  constructor
  · rintro ⟨i, hi, hb⟩
    have hne : i.1 ≠ m := by
      intro he
      have hv := i.2
      rw [he, hm] at hv
      cases hv
    have hlt : i.1.val < m.val := by
      have hn : i.1.val ≠ m.val := fun he => hne (Fin.ext he)
      change i.1.val < m.val + 1 at hi
      omega
    exact earlier_of_concat P bad c tr msg i hlt hb
  · exact occurred_concat_of_occurred P bad c tr msg

/-- A verifier message introduces only its own local event. -/
theorem occurred_concat_challenge_iff (i : P.ChallengeIdx) (c : Ctx)
    (tr : P.Transcript i.1.castSucc) (ch : P.Challenge i) :
    Occurred P bad i.1.succ c (P.concat tr ch) ↔
      Occurred P bad i.1.castSucc c tr ∨ bad i c tr ch := by
  constructor
  · rintro ⟨j, hj, hb⟩
    by_cases he : j = i
    · subst j
      right
      have ht : (P.concat tr ch).take i.1.castSucc (Fin.castSucc_le_succ i.1) = tr := by
        rw [P.take_concat tr ch i.1.castSucc le_rfl]
        rfl
      rw [ht] at hb
      simpa only [P.concat_apply_last tr ch] using hb
    · left
      have hlt : j.1.val < i.1.val := by
        have hn : j.1.val ≠ i.1.val := fun h => he (Subtype.ext (Fin.ext h))
        change j.1.val < i.1.val + 1 at hj
        omega
      exact earlier_of_concat P bad c tr ch j hlt hb
  · rintro (h | h)
    · exact occurred_concat_of_occurred P bad c tr ch h
    · refine ⟨i, by simp, ?_⟩
      rw [P.take_concat tr ch i.1.castSucc le_rfl]
      have ht : tr.take i.1.castSucc le_rfl = tr := by funext j; rfl
      rw [ht]
      simpa only [P.concat_apply_last tr ch] using h

variable (claim : Ctx → Prop)

def state (m : Fin (n + 1)) (c : Ctx) (tr : P.Transcript m) : Prop :=
  claim c ∨ Occurred P bad m c tr

variable [∀ i, Fintype (P.Challenge i)]
    (terminal : Ctx → P.Transcript (Fin.last n) → Prop)
    (ε : P.ChallengeIdx → ℝ≥0)
    (hcount : ∀ c i (tr : P.Transcript i.1.castSucc),
      ((Finset.univ.filter (bad i c tr)).card : ℝ≥0) ≤ ε i * Fintype.card (P.Challenge i))
    (hsound : ∀ c tr, terminal c tr → claim c ∨ Occurred P bad (Fin.last n) c tr)

/-- Generic cumulative-event reduction. Its two premises are obligations to
prove for a concrete protocol, and are retained explicitly in this constructor. -/
def reduction : ClaimReduction P Ctx ε where
  claim := claim
  claimOut := terminal
  S := state P bad claim
  start c tr hc := by
    rintro (h | h)
    · exact hc h
    · exact not_occurred_zero P bad c tr h
  next m hm c tr msg hn := by
    rintro (hc | he)
    · exact hn (Or.inl hc)
    · exact hn (Or.inr ((occurred_concat_prover_iff P bad hm c tr msg).mp he))
  full := hsound
  rbr c i tr := by
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (hcount c i tr)
    intro ch hch
    obtain ⟨hn, hs⟩ := (Finset.mem_filter.mp hch).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hs with hc | he
    · exact (hn (Or.inl hc)).elim
    · rcases (occurred_concat_challenge_iff P bad i c tr ch).mp he with he | hb
      · exact (hn (Or.inr he)).elim
      · exact hb

end GordieHowe.IOP.ChallengeEventReduction
