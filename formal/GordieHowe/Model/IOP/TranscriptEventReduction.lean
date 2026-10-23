-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.ChallengeEventReduction

@[expose] public section

/-!
# Causal events expressed on complete transcripts

A full-transcript presentation is convenient for circuit semantics. Causality
ensures that an event at a challenge depends only on the prefix through that
challenge. Completing unavailable messages with defaults therefore introduces
no foresight. Concrete protocols must prove causality, each replacement count,
and the deterministic soundness implication.
-/
namespace GordieHowe.IOP.TranscriptEventReduction

open scoped Classical NNReal
variable {n : ℕ} (P : ProtocolSpec n) [∀ i, Inhabited (P.Type i)]

def complete {m : Fin (n + 1)} (tr : P.Transcript m) :
    P.Transcript (Fin.last n) :=
  fun j => if h : j.val < m.val then tr ⟨j.val, h⟩ else default

theorem complete_at {m : Fin (n + 1)} (tr : P.Transcript m)
    (j : Fin n) (h : j.val < m.val) :
    complete P tr j = tr ⟨j.val, h⟩ := by
  simp only [complete, dite_eq_left h]

variable {Ctx : Type}
    (bad : P.ChallengeIdx → Ctx → P.Transcript (Fin.last n) → Prop)

def Causal : Prop :=
  ∀ i c tr tr', (∀ j : Fin n, j.val ≤ i.1.val → tr j = tr' j) →
    (bad i c tr ↔ bad i c tr')

def localBad (i : P.ChallengeIdx) (c : Ctx)
    (tr : P.Transcript i.1.castSucc) (ch : P.Challenge i) : Prop :=
  bad i c (complete P (P.concat tr ch))

theorem complete_concat_agrees (i : P.ChallengeIdx)
    (tr : P.Transcript i.1.castSucc) (ch : P.Challenge i)
    (j : Fin n) (hj : j.val ≤ i.1.val) :
    complete P (P.concat tr ch) j =
      Function.update (complete P tr) i.1 ch j := by
  rcases i with ⟨i, hi⟩
  change j.val ≤ i.val at hj
  change complete P (P.concat (m := i) tr ch) j = Function.update (complete P tr) i ch j
  by_cases he : j = i
  · subst j
    exact (complete_at P (P.concat tr ch) i (by simp)).trans
      ((P.concat_apply_last tr ch).trans (Function.update_self i ch (complete P tr)).symm)
  · have hlt : j.val < i.val := by
      have hn : j.val ≠ i.val := fun h => he (Fin.ext h)
      omega
    exact (complete_at P (P.concat tr ch) j (by simpa using Nat.lt_succ_of_lt hlt)).trans
      ((P.concat_apply_of_lt tr ch j.val hlt).trans
        ((complete_at P tr j hlt).symm.trans
          (Function.update_of_ne he ch (complete P tr)).symm))

theorem localBad_iff (hcausal : Causal P bad) (i : P.ChallengeIdx) (c : Ctx)
    (tr : P.Transcript i.1.castSucc) (ch : P.Challenge i) :
    localBad P bad i c tr ch ↔
      bad i c (Function.update (complete P tr) i.1 ch) :=
  hcausal i c _ _ (complete_concat_agrees P i tr ch)

theorem occurred_iff (hcausal : Causal P bad) (c : Ctx)
    (tr : P.Transcript (Fin.last n)) :
    ChallengeEventReduction.Occurred P (localBad P bad) (Fin.last n) c tr ↔
      ∃ i, bad i c tr := by
  have he : ∀ i : P.ChallengeIdx,
      localBad P bad i c (tr.take i.1.castSucc (Fin.le_last _)) (tr i.1) ↔ bad i c tr := by
    intro i
    rcases i with ⟨i, hi⟩
    unfold localBad
    apply hcausal
    intro j hj
    change j.val ≤ i.val at hj
    rw [complete_at P _ _ (by change j.val < i.val + 1; omega)]
    by_cases heq : j = i
    · subst j
      exact P.concat_apply_last _ _
    · have hlt : j.val < i.val := by
        have hn : j.val ≠ i.val := fun h => heq (Fin.ext h)
        omega
      rw [P.concat_apply_of_lt _ _ j.val hlt]
      rfl
  constructor
  · rintro ⟨i, hi, hb⟩
    exact ⟨i, (he i).mp hb⟩
  · rintro ⟨i, hb⟩
    exact ⟨i, i.1.isLt, (he i).mpr hb⟩

variable [∀ i, Fintype (P.Challenge i)]

/-- Construct an actual prefix-based RBR reduction from proved causal events. -/
def reduction (hcausal : Causal P bad)
    (claim : Ctx → Prop) (terminal : Ctx → P.Transcript (Fin.last n) → Prop)
    (ε : P.ChallengeIdx → NNReal)
    (hcount : ∀ c i (tr : P.Transcript (Fin.last n)),
      ((Finset.univ.filter fun ch : P.Challenge i =>
        bad i c (Function.update tr i.1 ch)).card : NNReal) ≤
          ε i * Fintype.card (P.Challenge i))
    (hsound : ∀ c tr, terminal c tr → claim c ∨ ∃ i, bad i c tr) :
    ClaimReduction P Ctx ε :=
  ChallengeEventReduction.reduction P (localBad P bad) claim terminal ε
    (by
      intro c i tr
      simp only [localBad_iff P bad hcausal]
      exact hcount c i (complete P tr))
    (by
      intro c tr ht
      rcases hsound c tr ht with hc | hb
      · exact Or.inl hc
      · exact Or.inr ((occurred_iff P bad hcausal c tr).mpr hb))

end GordieHowe.IOP.TranscriptEventReduction
