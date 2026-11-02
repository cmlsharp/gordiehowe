-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Format.SpecWrites
public import GordieHowe.SPBCS.Sampler.ChallengeReader
public import GordieHowe.ProofSystem.Program.Basic
public import GordieHowe.ProofSystem.Program.Transcript.CircuitCodecs

@[expose] public section

/-!
# Loads at the rounds' own stream lengths

The overrun of a transcript is bounded round by round on the round's own stream, the default
budget plus the round's grant (`CReader.grant`, the C++ `extend_point_budget_for`). The predicate
`SpecReaders.AllGranted good` asks `good g L` of every round's grant `g` and load `L`; a predicate
on loads alone transfers to it when larger grants only help (`AllGranted.of_allLoads`), so only the
rounds whose load needs their grant are checked at it (`AllGranted.one`). The overrun bound from it
is `GordieHowe.SPBCS.ProofSystemTranscript.overrun_le_at_granted`.

The largest grant of a round (`SpecReaders.maxGrant`) is at most `m` exactly when every round's
grant is (`maxGrant_le_iff`), so it is computed part by part: an append's is the larger of its
parts' (`maxGrant_append`), a round's its reader's (`maxGrant_one`). Readers built from a field
reader that grants nothing grant nothing (`Ungranted`): the GKR rounds (`gkrSpec_ungranted`,
`sourceInteraction_ungranted`) and Ligero's commit rounds (`ldtCommit_ungranted`); Ligero's proof
phase grants exactly its constraint challenge's grant (`maxGrant_listRadius`).
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

namespace SpecReaders

variable {n n₁ n₂ : ℕ}

/-! ### The largest grant -/

/-- **No round is granted extra stream bytes.** -/
abbrev Ungranted {P : ProtocolSpec n} (rd : SpecReaders P) : Prop :=
  rd.AllGranted fun g _ => g = 0

/-- A round's grant is at most the largest. -/
theorem grant_le_maxGrant {P : ProtocolSpec n} (rd : SpecReaders P) (i : P.ChallengeIdx) :
    (rd i).grant ≤ rd.maxGrant :=
  Finset.le_sup (f := fun i => (rd i).grant) (Finset.mem_univ i)

/-- **The largest grant is at most `m`** exactly when every round's grant is. -/
theorem maxGrant_le_iff {P : ProtocolSpec n} {rd : SpecReaders P} {m : ℕ} :
    rd.maxGrant ≤ m ↔ rd.AllGranted fun g _ => g ≤ m :=
  Finset.sup_le_iff.trans ⟨fun h i => h i (Finset.mem_univ _), fun h i _ => h i⟩

/-- Readers that grant nothing have largest grant `0`. -/
theorem Ungranted.maxGrant_eq {P : ProtocolSpec n} {rd : SpecReaders P} (h : rd.Ungranted) :
    rd.maxGrant = 0 :=
  Nat.le_zero.1 (maxGrant_le_iff.2 fun i => (h i).le)

/-- **The first part's grants** of an append satisfy what the append's do. -/
theorem AllGranted.of_append_left {P₁ : ProtocolSpec n₁} {P₂ : ProtocolSpec n₂}
    {r₁ : SpecReaders P₁} {r₂ : SpecReaders P₂} {good : ℕ → Load → Prop}
    (h : (r₁ ++ r₂).AllGranted good) : r₁.AllGranted good := by
  intro j
  have hj := h (ChallengeIdx.inl (P₂ := P₂) j)
  change good ((r₁.append r₂) _).grant ((r₁.append r₂) _).load at hj
  unfold SpecReaders.append at hj
  split at hj
  · rename_i j' h'
    rw [challengeIdxEquiv_inl] at h'
    obtain rfl := Sum.inl_injective h'
    rwa [CReader.cast_load, CReader.cast_grant] at hj
  · rename_i _ h'
    rw [challengeIdxEquiv_inl] at h'
    exact absurd h' (by simp)

/-- **The second part's grants** of an append satisfy what the append's do. -/
theorem AllGranted.of_append_right {P₁ : ProtocolSpec n₁} {P₂ : ProtocolSpec n₂}
    {r₁ : SpecReaders P₁} {r₂ : SpecReaders P₂} {good : ℕ → Load → Prop}
    (h : (r₁ ++ r₂).AllGranted good) : r₂.AllGranted good := by
  intro j
  have hj := h (ChallengeIdx.inr (P₁ := P₁) j)
  change good ((r₁.append r₂) _).grant ((r₁.append r₂) _).load at hj
  unfold SpecReaders.append at hj
  split at hj
  · rename_i _ h'
    rw [challengeIdxEquiv_inr] at h'
    exact absurd h' (by simp)
  · rename_i j' h'
    rw [challengeIdxEquiv_inr] at h'
    obtain rfl := Sum.inr_injective h'
    rwa [CReader.cast_load, CReader.cast_grant] at hj

/-- **The largest grant of an append** is the larger of its parts'. -/
theorem maxGrant_append {P₁ : ProtocolSpec n₁} {P₂ : ProtocolSpec n₂} (r₁ : SpecReaders P₁)
    (r₂ : SpecReaders P₂) : (r₁ ++ r₂).maxGrant = max r₁.maxGrant r₂.maxGrant := by
  refine le_antisymm (maxGrant_le_iff.2 (AllGranted.append ?_ ?_)) ?_
  · exact maxGrant_le_iff.1 (le_max_left _ _)
  · exact maxGrant_le_iff.1 (le_max_right _ _)
  · have h := maxGrant_le_iff.1 (le_refl (r₁ ++ r₂).maxGrant)
    exact max_le (maxGrant_le_iff.2 h.of_append_left) (maxGrant_le_iff.2 h.of_append_right)

/-- **The largest grant of a challenge round of one message** is its reader's. -/
theorem maxGrant_one (C : Type) (r : CReader C) : (one C r).maxGrant = r.grant :=
  le_antisymm (maxGrant_le_iff.2 (AllGranted.one r le_rfl)) (grant_le_maxGrant (one C r) ⟨0, rfl⟩)

theorem Ungranted.oneP (M : Type) : (oneP M).Ungranted :=
  fun i => absurd i.2 (by simp [GKR.Schedule.one])

theorem Ungranted.empty : empty.Ungranted := fun i => i.1.elim0

/-- **The largest grant after dropping a prover message** is the protocol's. -/
theorem maxGrant_dropMsg {Q : ProtocolSpec n} (r : SpecReaders Q) {s : Fin n}
    (hs : Q.dir s = .P_to_V) : (r.dropMsg s).maxGrant = r.maxGrant := by
  refine le_antisymm (maxGrant_le_iff.2 fun i => grant_le_maxGrant r _)
    (maxGrant_le_iff.2 fun i => ?_)
  have h := grant_le_maxGrant (r.dropMsg s) ((dropChallengeIdxEquiv hs).symm i)
  change (r (dropChallengeIdx _)).grant ≤ _ at h
  rwa [← dropChallengeIdxEquiv_apply hs, Equiv.apply_symm_apply] at h

end SpecReaders

/-- **The grant of a pair of draws** is the sum of the readers'. -/
theorem CReader.prod_grant {C D : Type} [Fintype C] [Fintype D] (r : CReader C) (r' : CReader D) :
    (r.prod r').grant = r.grant + r'.grant :=
  rfl

/-- **The choice of `k` of `n` indices** grants nothing. -/
theorem CReader.choose_grant (n k : ℕ) (hk : k ≤ n) : (CReader.choose n k hk).grant = 0 := by
  change ∑ _i : Fin k, 0 = 0
  exact Finset.sum_const_zero

namespace SpecReaders

/-! ### Readers that grant nothing -/

section GKR

variable {F : Type} [Fintype F] {r : CReader F} (hr : r.grant = 0)
include hr

omit [Fintype F] in
theorem gkrRounds_ungranted : (k : ℕ) → (gkrRounds r k).Ungranted
  | 0 => Ungranted.empty
  | k + 1 => AllGranted.append (Ungranted.oneP _)
      (AllGranted.append (AllGranted.one r hr) (gkrRounds_ungranted k))

theorem gkrCircuit_ungranted {d : ℕ} (C : GKR.Circuit F d) : (gkrCircuit r C).Ungranted := by
  induction C with
  | input d => exact AllGranted.one r hr
  | layer Q tail ih =>
    refine AllGranted.append (AllGranted.one _ ?_)
      (AllGranted.append (gkrRounds_ungranted hr _) (AllGranted.append (Ungranted.oneP _) ih))
    rw [CReader.prod_grant, hr]

/-- **The GKR rounds of a circuit grant nothing** when the field reader grants nothing. -/
theorem gkrSpec_ungranted {d : ℕ} (C : GKR.Circuit F d) : (gkrSpec r C).Ungranted := by
  refine AllGranted.append (AllGranted.one _ ?_) (gkrCircuit_ungranted hr C)
  rw [CReader.pi_grant, hr, mul_zero]

/-- **The GKR rounds of a source circuit grant nothing** when the field reader grants nothing. -/
theorem sourceInteraction_ungranted [Field F] [DecidableEq F] {d : ℕ}
    (S : GordieHowe.GKR.LayeredCircuit F d) (nodes : Sumcheck.Nodes F) :
    (sourceInteraction r S nodes).Ungranted := by
  cases S with
  | mk outDim inDim terms Q tail hdim =>
    cases hdim
    exact gkrSpec_ungranted hr _

/-- **Ligero's commit rounds grant nothing** when the field reader grants nothing. -/
theorem ldtCommit_ungranted (R k nrep : ℕ) : (ldtCommit r R k nrep).Ungranted
  | ⟨⟨0, _⟩, _⟩ => by
    change (CReader.pi nrep (CReader.pi R r)).grant = 0
    rw [CReader.pi_grant, CReader.pi_grant, hr, mul_zero, mul_zero]
  | ⟨⟨1, _⟩, h⟩ => absurd h (by simp)

/-- **The largest grant of Ligero's proof phase** is its constraint challenge's grant `g` when
the field reader grants nothing. -/
theorem maxGrant_listRadius {N nL nQ k t : ℕ} (htN : t ≤ N) (g : ℕ) :
    (listRadius (F := F) (N := N) (nL := nL) (nQ := nQ) (k := k) r htN g).maxGrant = g := by
  unfold listRadius
  rw [maxGrant_dropMsg _ (by rfl)]
  have hC : (((CReader.pi nL r).prod (CReader.pi nQ r)).extend g).grant = g := by
    rw [CReader.extend_grant, CReader.prod_grant, CReader.pi_grant, CReader.pi_grant, hr]
    simp
  refine le_antisymm (maxGrant_le_iff.2 ?_) ?_
  · rintro ⟨⟨_ | _ | _ | _ | _, hi⟩, h⟩
    · exact absurd h (by simp)
    · exact hC.le
    · exact absurd h (by simp)
    · exact (CReader.choose_grant N t htN).le.trans (Nat.zero_le g)
    · omega
  · refine le_trans ?_ (grant_le_maxGrant _ ⟨⟨1, ?h1⟩, ?h2⟩)
    case h1 => decide
    case h2 => rfl
    exact hC.symm.le

end GKR

end SpecReaders

end GordieHowe.SPBCS
