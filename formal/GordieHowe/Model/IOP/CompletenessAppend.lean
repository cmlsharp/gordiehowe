-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.Completeness
public import GordieHowe.Model.IOP.Append

@[expose] public section

/-! Sequential composition of causal honest transcript families. -/
namespace GordieHowe.IOP
open ProtocolSpec
variable {n n₁ n₂ : ℕ} {P : ProtocolSpec n}
  {P₁ : ProtocolSpec n₁} {P₂ : ProtocolSpec n₂}

namespace ProtocolSpec

def Challenges.left (ch : (P₁ ++ P₂).Challenges) : P₁.Challenges :=
  fun i => cast (append_Challenge_inl i) (ch (ChallengeIdx.inl i))

def Challenges.right (ch : (P₁ ++ P₂).Challenges) : P₂.Challenges :=
  fun i => cast (append_Challenge_inr i) (ch (ChallengeIdx.inr i))

/-- **`ChallengeIdx.inl` is injective.** -/
theorem ChallengeIdx.inl_injective : Function.Injective (ChallengeIdx.inl (P₁ := P₁) (P₂ := P₂)) :=
  fun i i' h => by simpa using congrArg ChallengeIdx.toSum h

/-- **`ChallengeIdx.inr` is injective.** -/
theorem ChallengeIdx.inr_injective : Function.Injective (ChallengeIdx.inr (P₁ := P₁) (P₂ := P₂)) :=
  fun i i' h => by simpa using congrArg ChallengeIdx.toSum h

/-- **`ChallengeIdx.inl` and `ChallengeIdx.inr` have disjoint images.** -/
theorem ChallengeIdx.inl_ne_inr (i : P₁.ChallengeIdx) (i' : P₂.ChallengeIdx) :
    ChallengeIdx.inl (P₂ := P₂) i ≠ ChallengeIdx.inr i' := fun h => by
  simpa using congrArg ChallengeIdx.toSum h

/-- **Updating a challenge of the first part** updates the first part's challenges at it. -/
theorem Challenges.left_update_inl (ch : (P₁ ++ P₂).Challenges) (i : P₁.ChallengeIdx)
    (c : (P₁ ++ P₂).Challenge (ChallengeIdx.inl i)) :
    Challenges.left (Function.update ch (ChallengeIdx.inl i) c) =
      Function.update (Challenges.left ch) i (cast (append_Challenge_inl i) c) := by
  funext i'
  by_cases h : i' = i
  · subst h
    simp only [Challenges.left, Function.update_self]
  · simp only [Challenges.left, Function.update_of_ne h,
      Function.update_of_ne fun e => h (ChallengeIdx.inl_injective e)]

/-- **Updating a challenge of the second part** keeps the first part's challenges. -/
theorem Challenges.left_update_inr (ch : (P₁ ++ P₂).Challenges) (i : P₂.ChallengeIdx)
    (c : (P₁ ++ P₂).Challenge (ChallengeIdx.inr i)) :
    Challenges.left (Function.update ch (ChallengeIdx.inr i) c) = Challenges.left ch := by
  funext i'
  simp only [Challenges.left, Function.update_of_ne (ChallengeIdx.inl_ne_inr i' i)]

/-- **Updating a challenge of the first part** keeps the second part's challenges. -/
theorem Challenges.right_update_inl (ch : (P₁ ++ P₂).Challenges) (i : P₁.ChallengeIdx)
    (c : (P₁ ++ P₂).Challenge (ChallengeIdx.inl i)) :
    Challenges.right (Function.update ch (ChallengeIdx.inl i) c) = Challenges.right ch := by
  funext i'
  simp only [Challenges.right, Function.update_of_ne (ChallengeIdx.inl_ne_inr i i').symm]

/-- **Updating a challenge of the second part** updates the second part's challenges at it. -/
theorem Challenges.right_update_inr (ch : (P₁ ++ P₂).Challenges) (i : P₂.ChallengeIdx)
    (c : (P₁ ++ P₂).Challenge (ChallengeIdx.inr i)) :
    Challenges.right (Function.update ch (ChallengeIdx.inr i) c) =
      Function.update (Challenges.right ch) i (cast (append_Challenge_inr i) c) := by
  funext i'
  by_cases h : i' = i
  · subst h
    simp only [Challenges.right, Function.update_self]
  · simp only [Challenges.right, Function.update_of_ne h,
      Function.update_of_ne fun e => h (ChallengeIdx.inr_injective e)]

/-- Concatenate full transcripts without changing their message types. -/
def Transcript.join (tr₁ : P₁.Transcript (Fin.last n₁))
    (tr₂ : P₂.Transcript (Fin.last n₂)) :
    (P₁ ++ P₂).Transcript (Fin.last (n₁+n₂)) :=
  fun i => Fin.addCases
    (fun j => cast (append_Type_castAdd j).symm (tr₁ j))
    (fun j => cast (append_Type_natAdd j).symm (tr₂ j)) i

@[simp] theorem Transcript.join_left (tr₁ : P₁.Transcript (Fin.last n₁))
    (tr₂ : P₂.Transcript (Fin.last n₂)) (i : Fin n₁) :
    Transcript.join tr₁ tr₂ (Fin.castAdd n₂ i) =
      cast (append_Type_castAdd i).symm (tr₁ i) := by
  simp [Transcript.join]

@[simp] theorem Transcript.join_right (tr₁ : P₁.Transcript (Fin.last n₁))
    (tr₂ : P₂.Transcript (Fin.last n₂)) (i : Fin n₂) :
    Transcript.join tr₁ tr₂ (Fin.natAdd n₁ i) =
      cast (append_Type_natAdd i).symm (tr₂ i) := by
  simp [Transcript.join]

@[simp] theorem Transcript.left_join (tr₁ : P₁.Transcript (Fin.last n₁))
    (tr₂ : P₂.Transcript (Fin.last n₂)) : (Transcript.join tr₁ tr₂).left = tr₁ := by
  funext i
  change cast (append_Type_castAdd i) (Transcript.join tr₁ tr₂ (Fin.castAdd n₂ i)) = _
  simp

@[simp] theorem Transcript.right_join (tr₁ : P₁.Transcript (Fin.last n₁))
    (tr₂ : P₂.Transcript (Fin.last n₂)) : (Transcript.join tr₁ tr₂).right = tr₂ := by
  funext i
  change cast (append_Type_natAdd i) (Transcript.join tr₁ tr₂ (Fin.natAdd n₁ i)) = _
  simp

@[simp] theorem Transcript.join_fst (tr₁ : P₁.Transcript (Fin.last n₁))
    (tr₂ : P₂.Transcript (Fin.last n₂)) :
    (Transcript.join tr₁ tr₂).fst (Fin.last n₁) (by simp) = tr₁ :=
  Transcript.left_join tr₁ tr₂

@[simp] theorem Transcript.join_snd (tr₁ : P₁.Transcript (Fin.last n₁))
    (tr₂ : P₂.Transcript (Fin.last n₂)) :
    (Transcript.join tr₁ tr₂).snd (Fin.last n₂) (by simp) = tr₂ :=
  Transcript.right_join tr₁ tr₂

end ProtocolSpec

namespace CausalTranscript

/-- The empty protocol has one empty honest transcript. -/
def empty (P : ProtocolSpec 0) : CausalTranscript P where
  transcript _ := fun i => i.elim0
  challenge _ i := i.1.elim0
  causal i := i.1.elim0

/-- A fixed prover message chosen before this one-move phase starts. -/
def oneMessage {Msg : Type} (msg : Msg) :
    CausalTranscript (⟨fun _ : Fin 1 => .P_to_V, fun _ => Msg⟩ : ProtocolSpec 1) where
  transcript _ _ := msg
  challenge _ i := by cases i.2
  causal _ _ _ _ := rfl

/-- The verifier's one-move phase simply records its fresh challenge. -/
def oneChallenge (Msg : Type) :
    CausalTranscript (⟨fun _ : Fin 1 => .V_to_P, fun _ => Msg⟩ : ProtocolSpec 1) where
  transcript ch _ := ch ⟨0,rfl⟩
  challenge ch i := by
    have hi : i = ⟨0,rfl⟩ := Subtype.ext (Subsingleton.elim _ _)
    subst i
    rfl
  causal i := by cases i.2

/-- Agreement on earlier verifier moves fixes every earlier transcript entry. -/
theorem entry_congr (H : CausalTranscript P) (ch ch' : P.Challenges)
    (i : Fin n) (h : ∀ j : P.ChallengeIdx, j.1 ≤ i → ch j = ch' j) :
    H.transcript ch i = H.transcript ch' i := by
  cases hd : P.dir i with
  | P_to_V => exact H.causal ⟨i,hd⟩ ch ch' (fun j hj => h j hj.le)
  | V_to_P =>
      rw [H.challenge ch ⟨i,hd⟩, H.challenge ch' ⟨i,hd⟩]
      exact h ⟨i,hd⟩ le_rfl

/-- The second honest phase may depend on the completed first phase, which is
available before any second-phase message is sent. -/
def append (H₁ : CausalTranscript P₁)
    (H₂ : P₁.Transcript (Fin.last n₁) → CausalTranscript P₂) :
    CausalTranscript (P₁ ++ P₂) where
  transcript ch :=
    let tr₁ := H₁.transcript ch.left
    Transcript.join tr₁ ((H₂ tr₁).transcript ch.right)
  challenge ch i := by
    rcases ChallengeIdx.inl_or_inr i with ⟨j,rfl⟩ | ⟨j,rfl⟩
    · simp only [ChallengeIdx.val_inl, Transcript.join_left, H₁.challenge,
        Challenges.left, cast_cast]
      rfl
    · simp only [ChallengeIdx.val_inr, Transcript.join_right,
        CausalTranscript.challenge, Challenges.right, cast_cast]
      rfl
  causal i ch ch' h := by
    rcases i with ⟨i,hi⟩
    induction i using Fin.addCases with
    | left i =>
        simp only [Transcript.join_left]
        apply congrArg
        apply H₁.causal ⟨i, by simpa using hi⟩
        intro j hj
        apply congrArg
        exact h (ChallengeIdx.inl j) (by exact hj)
    | right i =>
        have hfirst : ch.left = ch'.left := by
          funext j
          apply congrArg
          exact h (ChallengeIdx.inl j) (by
            change j.1.val < n₁ + i.val
            have := j.1.isLt
            omega)
        simp only [Transcript.join_right]
        rw [hfirst]
        apply congrArg
        apply (H₂ (H₁.transcript ch'.left)).causal ⟨i, by simpa using hi⟩
        intro j hj
        apply congrArg
        exact h (ChallengeIdx.inr j) (by simpa using hj)

@[simp] theorem append_left (H₁ : CausalTranscript P₁)
    (H₂ : P₁.Transcript (Fin.last n₁) → CausalTranscript P₂)
    (ch : (P₁ ++ P₂).Challenges) :
    ((H₁.append H₂).transcript ch).left = H₁.transcript ch.left :=
  Transcript.left_join _ _

@[simp] theorem append_right (H₁ : CausalTranscript P₁)
    (H₂ : P₁.Transcript (Fin.last n₁) → CausalTranscript P₂)
    (ch : (P₁ ++ P₂).Challenges) :
    ((H₁.append H₂).transcript ch).right = (H₂ (H₁.transcript ch.left)).transcript ch.right :=
  Transcript.right_join _ _

end CausalTranscript
end GordieHowe.IOP
