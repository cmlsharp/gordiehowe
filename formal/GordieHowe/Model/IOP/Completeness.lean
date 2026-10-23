-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.RBR

@[expose] public section

/-!
# Honest strategies and interactive completeness

Completeness uses the same causal `Prover` and verifier as soundness. Failure
is a probability over uniform verifier challenges for each fixed valid input. Randomness in
an input-generation algorithm, such as a hash sampler, needs a separate bound.
-/
namespace GordieHowe.IOP
open scoped NNReal
open scoped Classical

variable {n : ℕ} {P : ProtocolSpec n} {Stmt Wit : Type}

/-- **Completeness of the honest prover family `honest`**: on every valid statement/witness
pair `honest w` is rejected with probability at most `δ` over uniform verifier challenges.
The challenge types are nonempty, so the uniform distribution exists;
`completenessAt_iff_count` is the equivalent counting form. -/
def completenessAt [∀ i, Fintype (P.Challenge i)] [∀ i, Nonempty (P.Challenge i)]
    (rel : Set (Stmt × Wit)) (V : Verifier P Stmt) (honest : Wit → Prover P Stmt) (δ : ℝ≥0) :
    Prop :=
  ∀ x w, (x, w) ∈ rel → Pr[ch ← P.Challenges : V x ((honest w).run x ch) ≠ true] ≤ δ

/-- Completeness for some honest prover family: `completenessAt` at some `honest`. A statement
about a named prover uses `completenessAt`. -/
def completeness [∀ i, Fintype (P.Challenge i)] [∀ i, Nonempty (P.Challenge i)]
    (rel : Set (Stmt × Wit)) (V : Verifier P Stmt) (δ : ℝ≥0) : Prop :=
  ∃ honest : Wit → Prover P Stmt, completenessAt rel V honest δ

/-- **Completeness transfers to a decoded honest input**: if the honest prover family `honest`
on inputs `I` is complete for `relI`, and `dec` decodes an input of `relI` from every pair of
`rel`, then the prover that decodes its input from the statement and the witness
(`Prover.ofStatement`) is complete for `rel` with the same error. -/
theorem completenessAt.decode [∀ i, Fintype (P.Challenge i)] [∀ i, Nonempty (P.Challenge i)]
    {I : Type} {relI : Set (Stmt × I)} {rel : Set (Stmt × Wit)} {V : Verifier P Stmt}
    {honest : I → Prover P Stmt} {δ : ℝ≥0} (h : completenessAt relI V honest δ)
    (dec : Stmt → Wit → I) (hdec : ∀ x w, (x, w) ∈ rel → (x, dec x w) ∈ relI) :
    completenessAt rel V (fun w => Prover.ofStatement fun x => honest (dec x w)) δ :=
  fun x w hw => by
    simp only [Prover.run_ofStatement]
    exact h x (dec x w) (hdec x w hw)

/-- `completenessAt` as a count: at most `δ · |C|` challenge tuples make the verifier reject the
honest run. -/
theorem completenessAt_iff_count [∀ i, Fintype (P.Challenge i)] [∀ i, Nonempty (P.Challenge i)]
    {rel : Set (Stmt × Wit)} {V : Verifier P Stmt} {honest : Wit → Prover P Stmt} {δ : ℝ≥0} :
    completenessAt rel V honest δ ↔
      ∀ x w, (x, w) ∈ rel →
        ((Finset.univ.filter fun ch : P.Challenges =>
          V x ((honest w).run x ch) ≠ true).card : ℝ≥0) ≤
            δ * Fintype.card P.Challenges :=
  forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    (card_le_iff_probUniform_le P.Challenges _ _).symm

/-- `completeness` as a count. -/
theorem completeness_iff_count [∀ i, Fintype (P.Challenge i)] [∀ i, Nonempty (P.Challenge i)]
    {rel : Set (Stmt × Wit)} {V : Verifier P Stmt} {δ : ℝ≥0} :
    completeness rel V δ ↔
      ∃ honest : Wit → Prover P Stmt, ∀ x w, (x, w) ∈ rel →
        ((Finset.univ.filter fun ch : P.Challenges =>
          V x ((honest w).run x ch) ≠ true).card : ℝ≥0) ≤
            δ * Fintype.card P.Challenges :=
  exists_congr fun _ => completenessAt_iff_count

/-- Acceptance of `honest` outside a counted failure event yields its completeness. The event
may depend on the honest input; it cannot be silently excluded from the coins. -/
theorem completenessAt_of_failure_event [∀ i, Fintype (P.Challenge i)]
    [∀ i, Nonempty (P.Challenge i)]
    (rel : Set (Stmt × Wit)) (V : Verifier P Stmt) (δ : ℝ≥0)
    (honest : Wit → Prover P Stmt) (bad : Stmt → Wit → P.Challenges → Prop)
    (haccept : ∀ x w, (x,w) ∈ rel → ∀ ch, ¬ bad x w ch →
      V x ((honest w).run x ch) = true)
    (hcount : ∀ x w, (x,w) ∈ rel →
      ((Finset.univ.filter (bad x w)).card : ℝ≥0) ≤ δ * Fintype.card P.Challenges) :
    completenessAt rel V honest δ := by
  rw [completenessAt_iff_count]
  intro x w hw
  apply le_trans _ (hcount x w hw)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro ch hch
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hch ⊢
  by_contra hb
  exact hch (haccept x w hw ch hb)

/-- Acceptance outside a counted failure event yields completeness. -/
theorem completeness_of_failure_event [∀ i, Fintype (P.Challenge i)] [∀ i, Nonempty (P.Challenge i)]
    (rel : Set (Stmt × Wit)) (V : Verifier P Stmt) (δ : ℝ≥0)
    (honest : Wit → Prover P Stmt) (bad : Stmt → Wit → P.Challenges → Prop)
    (haccept : ∀ x w, (x,w) ∈ rel → ∀ ch, ¬ bad x w ch →
      V x ((honest w).run x ch) = true)
    (hcount : ∀ x w, (x,w) ∈ rel →
      ((Finset.univ.filter (bad x w)).card : ℝ≥0) ≤ δ * Fintype.card P.Challenges) :
    completeness rel V δ :=
  ⟨honest, completenessAt_of_failure_event rel V δ honest bad haccept hcount⟩

/-- A failure predicate on one fresh challenge has the same probability
bound inside the full product of verifier coins. -/
theorem coordinate_failure_count [∀ i, Fintype (P.Challenge i)]
    (i : P.ChallengeIdx) (bad : P.Challenge i → Prop) (δ : ℝ≥0)
    (hbad : ((Finset.univ.filter bad).card : ℝ≥0) ≤ δ * Fintype.card (P.Challenge i)) :
    ((Finset.univ.filter fun ch : P.Challenges => bad (ch i)).card : ℝ≥0) ≤
      δ * Fintype.card P.Challenges := by
  apply card_le_of_card_update_le i
  intro ch
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Function.update_self] using hbad

/-- A family of full transcripts with the required challenge messages and
causal prover messages. This is a construction interface, not an assumption
that accepting transcripts can be chosen after seeing future challenges. -/
structure CausalTranscript (P : ProtocolSpec n) where
  transcript : P.Challenges → P.Transcript (Fin.last n)
  challenge : ∀ ch (i : P.ChallengeIdx), transcript ch i.1 = ch i
  causal : ∀ (i : P.MessageIdx) ch ch',
    (∀ j : P.ChallengeIdx, j.1 < i.1 → ch j = ch' j) →
      transcript ch i.1 = transcript ch' i.1

namespace CausalTranscript

/-- Complete the already received challenges by a fixed default for future
rounds. Only the received part can affect the next honest prover message. -/
def completeChallenges (default : P.Challenges) {m : Fin n}
    (tr : P.Transcript m.castSucc) : P.Challenges :=
  fun i => if h : i.1 < m then tr ⟨i.1, h⟩ else default i

/-- Realize a causal transcript family as an actual online prover. -/
def prover (H : CausalTranscript P) (default : P.Challenges) : Prover P Unit :=
  fun i _ tr => H.transcript (completeChallenges default tr) i.1

/-- The online prover reproduces the specified transcript prefix. -/
theorem runTo_eq (H : CausalTranscript P) (default ch : P.Challenges)
    (k : ℕ) (hk : k ≤ n) :
    (H.prover default).runTo () ch k hk =
      (H.transcript ch).take ⟨k, by omega⟩ hk := by
  induction k with
  | zero => funext i; exact i.elim0
  | succ k ih =>
      rw [Prover.runTo]
      split
      next hdir =>
        have hc : H.transcript
            (completeChallenges default (m := ⟨k, hk⟩) ((H.prover default).runTo () ch k (by omega)))
            ⟨k, hk⟩ = H.transcript ch ⟨k, hk⟩ := by
          apply H.causal ⟨⟨k, by omega⟩, hdir⟩
          intro j hj
          simp only [completeChallenges, hj, dite_true, ih,
            ProtocolSpec.Transcript.take]
          exact H.challenge ch j
        funext i
        by_cases hi : i.val < k
        · rw [ProtocolSpec.concat_apply_of_lt _ _ i.val hi]
          rw [ih]
          rfl
        · have he : i = ⟨k, by simp⟩ := by
            apply Fin.ext
            change i.val = k
            have hit : i.val < k+1 := i.isLt
            omega
          subst i
          rw [ProtocolSpec.concat_apply_last]
          exact hc
      next hdir =>
        have hd : P.dir ⟨k, by omega⟩ = .V_to_P := by
          cases h : P.dir ⟨k, by omega⟩ <;> simp_all
        funext i
        by_cases hi : i.val < k
        · rw [ProtocolSpec.concat_apply_of_lt _ _ i.val hi]
          rw [ih]
          rfl
        · have he : i = ⟨k, by simp⟩ := by
            apply Fin.ext
            change i.val = k
            have hit : i.val < k+1 := i.isLt
            omega
          subst i
          rw [ProtocolSpec.concat_apply_last]
          exact (H.challenge ch ⟨⟨k, by omega⟩, hd⟩).symm

/-- No future challenge is available to the realized honest prover. -/
theorem run_eq (H : CausalTranscript P) (default ch : P.Challenges) :
    (H.prover default).run () ch = H.transcript ch := by
  exact H.runTo_eq default ch n le_rfl

/-- Choose the honest transcript construction from the public statement. -/
def proverFor (H : Stmt → CausalTranscript P) (default : P.Challenges) : Prover P Stmt :=
  fun i x tr => (H x).prover default i () tr

theorem runTo_proverFor (H : Stmt → CausalTranscript P) (default ch : P.Challenges)
    (x : Stmt) (k : ℕ) (hk : k ≤ n) :
    (proverFor H default).runTo x ch k hk = ((H x).prover default).runTo () ch k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [Prover.runTo, proverFor, ih]

theorem run_proverFor (H : Stmt → CausalTranscript P) (default ch : P.Challenges) (x : Stmt) :
    (proverFor H default).run x ch = (H x).transcript ch :=
  (runTo_proverFor H default ch x n le_rfl).trans ((H x).run_eq default ch)

/-- **A causal transcript family realized as a prover**: `proverFor` with the future challenges
filled by a classically chosen value of each challenge type. The value is never read: every run is
the family's transcript (`run_realize`). A computable realization would need a chosen element of
every challenge type. -/
noncomputable def realize [∀ i, Nonempty (P.Challenge i)] (H : Stmt → CausalTranscript P) :
    Prover P Stmt :=
  proverFor H fun _ => Classical.arbitrary _

theorem run_realize [∀ i, Nonempty (P.Challenge i)] (H : Stmt → CausalTranscript P)
    (ch : P.Challenges) (x : Stmt) : (realize H).run x ch = (H x).transcript ch :=
  run_proverFor H _ ch x

end CausalTranscript

/-- **Completeness of a prover that runs a causal family**: if every run of `honest w` is the
transcript of the family `H w`, acceptance of the family outside a counted failure event gives
the completeness of `honest`. -/
theorem completenessAt_of_causal [∀ i, Fintype (P.Challenge i)] [∀ i, Nonempty (P.Challenge i)]
    (rel : Set (Stmt × Wit)) (V : Verifier P Stmt) (δ : ℝ≥0) (honest : Wit → Prover P Stmt)
    (H : Wit → Stmt → CausalTranscript P)
    (hrun : ∀ w x ch, (honest w).run x ch = (H w x).transcript ch)
    (bad : Stmt → Wit → P.Challenges → Prop)
    (haccept : ∀ x w, (x,w) ∈ rel → ∀ ch, ¬ bad x w ch →
      V x ((H w x).transcript ch) = true)
    (hcount : ∀ x w, (x,w) ∈ rel →
      ((Finset.univ.filter (bad x w)).card : ℝ≥0) ≤ δ * Fintype.card P.Challenges) :
    completenessAt rel V honest δ :=
  completenessAt_of_failure_event rel V δ honest bad
    (fun x w hw ch hch => (hrun w x ch).symm ▸ haccept x w hw ch hch) hcount

/-- A causally constructed family and an explicit failure-event count give
the online completeness statement. Future coins are filled with `default`
only to realize the strategy; causality makes that choice immaterial. -/
theorem completeness_of_causal [∀ i, Fintype (P.Challenge i)] [∀ i, Nonempty (P.Challenge i)]
    (rel : Set (Stmt × Wit)) (V : Verifier P Stmt) (δ : ℝ≥0)
    (H : Wit → Stmt → CausalTranscript P) (default : P.Challenges)
    (bad : Stmt → Wit → P.Challenges → Prop)
    (haccept : ∀ x w, (x,w) ∈ rel → ∀ ch, ¬ bad x w ch →
      V x ((H w x).transcript ch) = true)
    (hcount : ∀ x w, (x,w) ∈ rel →
      ((Finset.univ.filter (bad x w)).card : ℝ≥0) ≤ δ * Fintype.card P.Challenges) :
    completeness rel V δ :=
  ⟨_, completenessAt_of_causal rel V δ (fun w => CausalTranscript.proverFor (H w) default) H
    (fun w x ch => CausalTranscript.run_proverFor (H w) default ch x) bad haccept hcount⟩

end GordieHowe.IOP
