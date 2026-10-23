-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Format.SpecWrites
public import GordieHowe.SPBCS.Sampler.ChallengeReader
public import GordieHowe.ProofSystem.Program.Basic

@[expose] public section

/-!
# Loads at the rounds' own stream lengths

The overrun of a transcript is bounded round by round on the round's own stream, the default
budget plus the round's grant (`CReader.grant`, the C++ `extend_point_budget_for`). The predicate
`SpecReaders.AllGranted good` asks `good g L` of every round's grant `g` and load `L`; a predicate
on loads alone transfers to it when larger grants only help (`AllGranted.of_allLoads`), so only the
rounds whose load needs their grant are checked at it (`AllGranted.one`). The overrun bound from it
is `GordieHowe.SPBCS.ProofSystemTranscript.overrun_le_at_granted`.
-/

namespace GordieHowe.SPBCS

open GordieHowe.IOP IOP.ProtocolSpec

namespace SpecReaders

variable {n n₁ n₂ : ℕ}

/-- **Every round's grant and load satisfy `good`.** -/
def AllGranted {P : ProtocolSpec n} (rd : SpecReaders P) (good : ℕ → Load → Prop) : Prop :=
  ∀ i, good (rd i).grant (rd i).load

/-- **A predicate on loads that larger grants keep** transfers from the loads at grant `0`. -/
theorem AllGranted.of_allLoads {P : ProtocolSpec n} {rd : SpecReaders P}
    {good : ℕ → Load → Prop} (hg : ∀ g L, good 0 L → good g L) (h : rd.AllLoads (good 0)) :
    rd.AllGranted good :=
  fun i => hg _ _ (h i)

/-- A challenge round of one message, at its reader's grant and load. -/
theorem AllGranted.one {C : Type} (r : CReader C) {good : ℕ → Load → Prop}
    (h : good r.grant r.load) : (SpecReaders.one C r).AllGranted good :=
  fun _ => h

theorem AllGranted.append {P₁ : ProtocolSpec n₁} {P₂ : ProtocolSpec n₂} {r₁ : SpecReaders P₁}
    {r₂ : SpecReaders P₂} {good : ℕ → Load → Prop} (h₁ : r₁.AllGranted good)
    (h₂ : r₂.AllGranted good) : (r₁ ++ r₂).AllGranted good := by
  change (r₁.append r₂).AllGranted good
  intro i
  unfold SpecReaders.append
  split
  · rw [CReader.cast_load, CReader.cast_grant]
    exact h₁ _
  · rw [CReader.cast_load, CReader.cast_grant]
    exact h₂ _

theorem AllGranted.appendN {good : ℕ → Load → Prop} : (m : ℕ) → {n : Fin m → ℕ} →
    {P : (i : Fin m) → ProtocolSpec (n i)} → {r : ∀ i, SpecReaders (P i)} →
    (∀ i, (r i).AllGranted good) → (SpecReaders.appendN m r).AllGranted good
  | 0, _, _, _, _ => fun i => i.1.elim0
  | 1, _, _, _, h => h 0
  | m + 2, _, _, _, h => (h 0).append (AllGranted.appendN (m + 1) fun i => h i.succ)

end SpecReaders

/-- **The grant of `n` draws in order** is `n` times the reader's. -/
theorem CReader.pi_grant {C : Type} [Fintype C] (n : ℕ) (r : CReader C) :
    (CReader.pi n r).grant = n * r.grant := by
  change ∑ _i : Fin n, r.grant = _
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end GordieHowe.SPBCS
