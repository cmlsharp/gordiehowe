-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.AppendN
public import GordieHowe.Model.IOP.ClaimReduction

@[expose] public section

/-!
# The bad events of a phase

A commit phase of several rounds (the rounds after an oracle message and before the context, as
FRI's commit phase is interactive, BCIKS20 §8.2) carries its own soundness events: an event per
challenge round, a function of a context (the oracle message) and the transcript up to and
including that challenge, of small probability over the challenge at every prefix. Nothing after
the phase can lower their probability, so a protocol that runs the phase charges them as round
errors at their rounds.

* `EventOccurs event c tr`: the event of some challenge round occurred on the full transcript.
* `BadState P Ctx ε`: the events as a state on the partial transcripts: false on the empty
  transcript, never made true by a prover message, true at the end when the phase is bad
  (`bad`), and made true from false by at most `ε i · |C_i|` challenges of round `i`. It is the
  form that composes: `BadState.ofEvents` (from bounded events), `comap`, `or` (two phases in
  sequence: either was bad), `orN` (the `m`-fold append, `bad_orN_of`).
* `ClaimReduction.orConst`: a reduction whose claims and state are disjoined with a fact about
  the context that no round changes, such as a bad commit phase.
-/

namespace GordieHowe.IOP

open scoped NNReal
open ProtocolSpec

variable {n n₁ n₂ : ℕ}

/-- **An event of a phase occurred** on the full transcript `tr` at the context `c`: the event of
some challenge round `i`, on the transcript up to and including round `i`. -/
def EventOccurs {P : ProtocolSpec n} {Ctx : Type}
    (event : (i : P.ChallengeIdx) → Ctx → P.Transcript i.1.succ → Prop) (c : Ctx)
    (tr : P.Transcript (Fin.last n)) : Prop :=
  ∃ i, event i c (tr.upTo i)

open Classical in
/-- **The events of a phase have small probability**: at every context and every prefix before
challenge round `i`, the event of round `i` has probability at most `ε i` over the challenge of
round `i`. -/
def ProtocolSpec.EventBound (P : ProtocolSpec n) [∀ i, Fintype (P.Challenge i)]
    [∀ i, Nonempty (P.Challenge i)] {Ctx : Type}
    (event : (i : P.ChallengeIdx) → Ctx → P.Transcript i.1.succ → Prop)
    (ε : P.ChallengeIdx → ℝ≥0) : Prop :=
  ∀ i c (tr : P.Transcript i.1.castSucc), Pr[ch ← P.Challenge i : event i c (P.concat tr ch)] ≤ ε i

/-- A phase without challenge rounds has no event. -/
theorem not_eventOccurs {P : ProtocolSpec n} [IsEmpty P.ChallengeIdx] {Ctx : Type}
    {event : (i : P.ChallengeIdx) → Ctx → P.Transcript i.1.succ → Prop} {c : Ctx}
    {tr : P.Transcript (Fin.last n)} : ¬ EventOccurs event c tr :=
  fun ⟨i, _⟩ => isEmptyElim i

open Classical in
/-- **The bad events of a phase as a state** at the context `c`, with round errors `ε`: the state is
false on the empty transcript, a prover message does not make it true, it is true at the end of a
bad phase, and at every prefix before a challenge round `i` at most `ε i · |C_i|` challenges make it
true from false. The fields are those of `ClaimProof` with the claim false and acceptance replaced
by `bad`. -/
structure BadState (P : ProtocolSpec n) (Ctx : Type) [∀ i, Fintype (P.Challenge i)]
    (ε : P.ChallengeIdx → ℝ≥0) where
  /-- The phase was bad, on the full transcript. -/
  bad : Ctx → P.Transcript (Fin.last n) → Prop
  /-- The state. -/
  S : (k : Fin (n + 1)) → Ctx → P.Transcript k → Prop
  /-- The state is false on the empty transcript. -/
  start : ∀ c tr, ¬ S 0 c tr
  /-- A prover message does not make the state true. -/
  next : ∀ (m : Fin n), P.dir m = .P_to_V → ∀ c (tr : P.Transcript m.castSucc) msg,
    ¬ S m.castSucc c tr → ¬ S m.succ c (P.concat tr msg)
  /-- The state is true at the end of a bad phase. -/
  full : ∀ c tr, bad c tr → S (Fin.last n) c tr
  /-- At every prefix before a challenge round, at most `ε i · |C_i|` challenges make the state
  true from false. -/
  rbr : ∀ c (i : P.ChallengeIdx) (tr : P.Transcript i.1.castSucc),
    ((Finset.univ.filter fun ch : P.Challenge i =>
        ¬ S i.1.castSucc c tr ∧ S i.1.succ c (P.concat tr ch)).card : ℝ≥0) ≤
      ε i * Fintype.card (P.Challenge i)

namespace BadState

section One

variable {P : ProtocolSpec n} {Ctx : Type} [∀ i, Fintype (P.Challenge i)]
  {ε : P.ChallengeIdx → ℝ≥0}

/-- **The events up to a prefix**: the event of a challenge round before the prefix of length
`k` occurred. -/
def EventBefore (event : (i : P.ChallengeIdx) → Ctx → P.Transcript i.1.succ → Prop)
    (k : Fin (n + 1)) (c : Ctx) (tr : P.Transcript k) : Prop :=
  ∃ i : P.ChallengeIdx, ∃ h : i.1.succ ≤ k, event i c (tr.take i.1.succ h)

open Classical in
/-- **The state of bounded events**: the event of a challenge round before the prefix occurred
(`EventBefore`); the phase is bad when an event occurred (`EventOccurs`). `bound`: the events have
probability at most `ε` (`ProtocolSpec.EventBound`). -/
def ofEvents [∀ i, Nonempty (P.Challenge i)]
    (event : (i : P.ChallengeIdx) → Ctx → P.Transcript i.1.succ → Prop)
    (bound : P.EventBound event ε) : BadState P Ctx ε where
  bad := EventOccurs event
  S := EventBefore event
  start c tr := by
    rintro ⟨i, hi, -⟩
    exact absurd hi (by simp)
  next m hm c tr msg hnot := by
    rintro ⟨i, hi, he⟩
    have hi' := ProtocolSpec.succ_le_castSucc_of_message hm hi
    refine hnot ⟨i, hi', ?_⟩
    rwa [← ProtocolSpec.take_concat tr msg i.1.succ hi']
  full c tr := by
    rintro ⟨i, he⟩
    exact ⟨i, Fin.le_last _, he⟩
  rbr c i tr := by
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card fun ch hch => ?_))
      ((card_le_iff_probUniform_le _ _ _).mpr (bound i c tr))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
    obtain ⟨hnot, j, hj, he⟩ := hch
    by_cases e : j = i
    · subst e
      exact he
    · exfalso
      have hle : j.1.succ ≤ i.1.castSucc := by
        have hne : (j.1 : ℕ) ≠ i.1 := fun h => e (Subtype.ext (Fin.ext h))
        rw [Fin.le_def] at hj ⊢
        simp only [Fin.val_succ, Fin.val_castSucc] at hj ⊢
        omega
      refine hnot ⟨j, hle, ?_⟩
      rwa [← ProtocolSpec.take_concat tr ch j.1.succ hle]

@[simp] theorem ofEvents_bad [∀ i, Nonempty (P.Challenge i)]
    {event : (i : P.ChallengeIdx) → Ctx → P.Transcript i.1.succ → Prop} {bound}
    (c : Ctx) (tr : P.Transcript (Fin.last n)) :
    (ofEvents (ε := ε) event bound).bad c tr ↔ EventOccurs event c tr :=
  Iff.rfl

/-- The bad events read at the context computed by `f`. -/
def comap {Ctx' : Type} (B : BadState P Ctx ε) (f : Ctx' → Ctx) : BadState P Ctx' ε where
  bad c tr := B.bad (f c) tr
  S k c tr := B.S k (f c) tr
  start c tr := B.start (f c) tr
  next m hm c tr msg h := B.next m hm (f c) tr msg h
  full c tr h := B.full (f c) tr h
  rbr c i tr := B.rbr (f c) i tr

@[simp] theorem comap_bad {Ctx' : Type} (B : BadState P Ctx ε) (f : Ctx' → Ctx) (c : Ctx')
    (tr : P.Transcript (Fin.last n)) : (B.comap f).bad c tr ↔ B.bad (f c) tr :=
  Iff.rfl

/-- A state true at a prefix before every challenge round is false: prover messages never make
it true. -/
theorem not_S_before (B : BadState P Ctx ε) {c : Ctx} :
    ∀ {k : Fin (n + 1)}, (∀ i : P.ChallengeIdx, k ≤ i.1.castSucc) → ∀ {tr : P.Transcript k},
      ¬ B.S k c tr := by
  intro k
  induction k using Fin.induction with
  | zero => exact fun _ tr => B.start c tr
  | succ j ih =>
    intro hk tr h
    have hdir : P.dir j = .P_to_V := by
      cases hd : P.dir j with
      | P_to_V => rfl
      | V_to_P =>
        have := hk ⟨j, hd⟩
        rw [Fin.le_def] at this
        simp at this
    refine B.next j hdir c _ (tr ⟨j, by simp⟩)
      (ih (fun i => (Fin.castSucc_le_succ j).trans (hk i))
        (tr := tr.take j.castSucc (Fin.castSucc_le_succ j))) ?_
    rwa [ProtocolSpec.concat_take_succ tr]

/-- A phase without challenge rounds is never bad. -/
theorem not_bad [IsEmpty P.ChallengeIdx] (B : BadState P Ctx ε) {c : Ctx}
    {tr : P.Transcript (Fin.last n)} : ¬ B.bad c tr :=
  fun h => B.not_S_before (fun i => isEmptyElim i) (B.full c tr h)

end One

/-- **The phase of no rounds** is never bad. -/
def none (P : ProtocolSpec 0) [∀ i, Fintype (P.Challenge i)] (ε : P.ChallengeIdx → ℝ≥0)
    {Ctx : Type} : BadState P Ctx ε where
  bad _ _ := False
  S _ _ _ := False
  start _ _ h := h
  next m := m.elim0
  full _ _ h := h
  rbr _ i := i.1.elim0

section Append

variable {P₁ : ProtocolSpec n₁} {P₂ : ProtocolSpec n₂} [∀ i, Fintype (P₁.Challenge i)]
  [∀ i, Fintype (P₂.Challenge i)] {ε₁ : P₁.ChallengeIdx → ℝ≥0} {ε₂ : P₂.ChallengeIdx → ℝ≥0}
  {Ctx : Type}

/-- **Two phases in sequence**: the sequence is bad when either phase was. The state is `B₁`'s on
the part-1 transcript, then `B₁`'s final state or `B₂`'s state on the part-2 transcript; each
round keeps its error. -/
def or (B₁ : BadState P₁ Ctx ε₁) (B₂ : BadState P₂ Ctx ε₂) :
    BadState (P₁ ++ P₂) Ctx (appendError ε₁ ε₂) where
  bad c tr := B₁.bad c tr.left ∨ B₂.bad c tr.right
  S m c := appendState (fun k tr₁ => B₁.S k c tr₁)
    (fun tr₁ k tr₂ => B₁.S (Fin.last n₁) c tr₁ ∨ B₂.S k c tr₂) m
  start c tr h :=
    B₁.start c _ (appendState_of_le (fun _ tr₂ h => h.resolve_right (B₂.start c tr₂)) (k₁ := 0)
      rfl h)
  next m hdir c tr msg hnot := by
    induction m using Fin.addCases with
    | left j =>
      intro h
      have hflip := appendState_flip_castAdd
        (fun _ tr₂ h => h.resolve_right (B₂.start c tr₂)) j tr msg hnot h
      exact B₁.next j (by simpa using hdir) c _ _ hflip.1 hflip.2
    | right j =>
      intro h
      obtain ⟨hn, hs⟩ := (appendState_flip_natAdd j tr msg).mp ⟨hnot, h⟩
      exact B₂.next j (by simpa using hdir) c _ _ (fun h' => hn (.inr h'))
        (hs.resolve_left fun h' => hn (.inl h'))
  full c tr h :=
    (appendState_iff_of_eq_add (k₂ := Fin.last n₂) (by simp) tr).mpr
      (h.imp (B₁.full c _) (B₂.full c _))
  rbr c i tr := by
    rcases ChallengeIdx.inl_or_inr i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [appendError_inl]
      refine card_le_of_mapsTo_cast (append_Challenge_inl j) (fun ch hch => ?_)
        (B₁.rbr c j (tr.fst j.1.castSucc (by simp)))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
      exact appendState_flip_castAdd (fun _ tr₂ h => h.resolve_right (B₂.start c tr₂)) j.1 tr ch
        hch.1 hch.2
    · rw [appendError_inr]
      refine card_le_of_mapsTo_cast (append_Challenge_inr j) (fun ch hch => ?_)
        (B₂.rbr c j (tr.snd j.1.castSucc (by simp)))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
      obtain ⟨hn, hs⟩ := (appendState_flip_natAdd j.1 tr ch).mp hch
      exact ⟨fun h' => hn (.inr h'), hs.resolve_left fun h' => hn (.inl h')⟩

@[simp] theorem or_bad (B₁ : BadState P₁ Ctx ε₁) (B₂ : BadState P₂ Ctx ε₂) (c : Ctx)
    (tr : (P₁ ++ P₂).Transcript (Fin.last (n₁ + n₂))) :
    (B₁.or B₂).bad c tr ↔ B₁.bad c tr.left ∨ B₂.bad c tr.right :=
  Iff.rfl

end Append

/-- **Phases in sequence** (the `m`-fold append): the sequence is bad when some phase was
(`bad_orN_of`), with the parts' errors (`errN`). For `m = 2` it is `BadState.or` by
definition. -/
def orN : (m : ℕ) → {n : Fin m → ℕ} → {P : (i : Fin m) → ProtocolSpec (n i)} →
    [∀ i j, Fintype ((P i).Challenge j)] → {ε : ∀ i, (P i).ChallengeIdx → ℝ≥0} → {Ctx : Type} →
    (∀ i, BadState (P i) Ctx (ε i)) → BadState (appendN m P) Ctx (ProtocolSpec.errN m ε)
  | 0, _, _, _, _, _, _ => @none _ (fun k => k.1.elim0) _ _
  | 1, _, _, _, _, _, B => B 0
  | m + 2, _, _, _, _, _, B => (B 0).or (orN (m + 1) fun i => B i.succ)

/-- **A bad part makes the sequence bad.** -/
theorem bad_orN_of : (m : ℕ) → {n : Fin m → ℕ} → {P : (i : Fin m) → ProtocolSpec (n i)} →
    [∀ i j, Fintype ((P i).Challenge j)] → {ε : ∀ i, (P i).ChallengeIdx → ℝ≥0} → {Ctx : Type} →
    (B : ∀ i, BadState (P i) Ctx (ε i)) → (c : Ctx) →
    (tr : (appendN m P).Transcript (Fin.last (lenN m n))) → (i : Fin m) →
    (B i).bad c (Transcript.part m tr i) → (orN m B).bad c tr
  | 0, _, _, _, _, _, _, _, _, i, _ => i.elim0
  | 1, _, _, _, _, _, B, c, tr, i, h => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact h
  | m + 2, _, _, _, _, _, B, c, tr, i, h => by
    cases i using Fin.cases with
    | zero => exact .inl h
    | succ i => exact .inr (bad_orN_of (m + 1) (fun i => B i.succ) c tr.right i h)

end BadState

namespace ClaimReduction

variable {P : ProtocolSpec n} {Ctx : Type} [∀ i, Fintype (P.Challenge i)]
  {ε : P.ChallengeIdx → ℝ≥0}

/-- **Disjoin a fact `Q` about the context** with the input claim, the output claim and the
state, such as a bad commit phase before the reduction. No round changes `Q`, so the errors are
unchanged. -/
def orConst (R : ClaimReduction P Ctx ε) (Q : Ctx → Prop) : ClaimReduction P Ctx ε where
  claim c := Q c ∨ R.claim c
  claimOut c tr := Q c ∨ R.claimOut c tr
  S m c tr := Q c ∨ R.S m c tr
  start c tr hc h := hc (h.imp id R.claim_of_S)
  next m hdir c tr msg hnot h :=
    R.next m hdir c tr msg (fun h' => hnot (.inr h')) (h.resolve_left fun hq => hnot (.inl hq))
  full c tr h := h.imp id (R.full c tr)
  rbr c i tr := by
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card ?_)) (R.rbr c i tr)
    intro ch hch
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
    exact ⟨fun h' => hch.1 (.inr h'), hch.2.resolve_left fun hq => hch.1 (.inl hq)⟩

@[simp] theorem orConst_claim (R : ClaimReduction P Ctx ε) (Q : Ctx → Prop) (c : Ctx) :
    (R.orConst Q).claim c ↔ Q c ∨ R.claim c :=
  Iff.rfl

@[simp] theorem orConst_claimOut (R : ClaimReduction P Ctx ε) (Q : Ctx → Prop) (c : Ctx)
    (tr : P.Transcript (Fin.last n)) : (R.orConst Q).claimOut c tr ↔ Q c ∨ R.claimOut c tr :=
  Iff.rfl

end ClaimReduction

end GordieHowe.IOP
