-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.Schedule
public import GordieHowe.Model.IOP.AppendView
public import GordieHowe.Model.IOP.TranscriptEventReduction
public import GordieHowe.Foundations.Probability.ChallengeEventCount
public import GordieHowe.Model.IOP.CompletenessAppend

@[expose] public section

/-!
# Alternating rounds of messages and challenges

`alt M C k`: `k` rounds, each a prover message in `M` followed by a verifier challenge in `C`, as a
protocol specification, with its values (`altValues`), its challenge indices (`altChallenge`,
`altIndex`) and the instances a phase built from it needs. A complete transcript of such a phase is
determined by its parts (`one_ext`, `split_ext`, `alt_ext`). The honest transcript pieces
(`CausalTranscript`): a fixed prover message and a fresh verifier challenge at a one-move spec
(`oneMsg`, `oneChal`), and the honest alternating rounds (`altFamily`), whose round `j` message reads
only the challenges before `j`, the challenges not yet drawn filled with zero (`altFamily_fst`). The
univariate-skip and batched zerocheck phases are built from these.
-/

namespace GordieHowe.HashCircuit.Skip

open IOP GKR.Schedule
open scoped NNReal

/-! ### Alternating rounds -/

section Alt

variable (M C : Type)

/-- `k` rounds, each a prover message of type `M` followed by a challenge of type `C`. -/
def alt : (k : ℕ) → ProtocolSpec (roundLength k)
  | 0 => empty
  | k + 1 => one .P_to_V M ++ (one .V_to_P C ++ alt k)

/-- The message and challenge of each round. -/
def altValues : (k : ℕ) → (alt M C k).Transcript (Fin.last (roundLength k)) → Fin k → M × C
  | 0, _ => Fin.elim0
  | k + 1, tr => Fin.cases (oneValue tr.left, oneValue tr.right.left)
      (altValues k tr.right.right)

/-- The challenge of round `j`. -/
def altChallenge : (k : ℕ) → Fin k → (alt M C k).ChallengeIdx
  | 0, j => j.elim0
  | k + 1, j => Fin.cases
      (ProtocolSpec.ChallengeIdx.inr (ProtocolSpec.ChallengeIdx.inl ⟨0, rfl⟩))
      (fun i => ProtocolSpec.ChallengeIdx.inr (ProtocolSpec.ChallengeIdx.inr (altChallenge k i))) j

theorem altChallenge_val (k : ℕ) (j : Fin k) : (altChallenge M C k j).1.val = 2 * j.val + 1 := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    refine Fin.cases rfl (fun i => ?_) j
    change 1 + (1 + (altChallenge M C k i).1.val) = 2 * (i.val + 1) + 1
    rw [ih]
    omega

theorem altChallenge_type (k : ℕ) (j : Fin k) : (alt M C k).Challenge (altChallenge M C k j) = C := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    refine Fin.cases rfl (fun i => ?_) j
    change (one .P_to_V M ++ (one .V_to_P C ++ alt M C k)).Challenge
      (ProtocolSpec.ChallengeIdx.inr (ProtocolSpec.ChallengeIdx.inr (altChallenge M C k i))) = C
    rw [ProtocolSpec.append_Challenge_inr, ProtocolSpec.append_Challenge_inr]
    exact ih i

/-- The rounds' challenges are the rounds. -/
def altIndex : (k : ℕ) → (alt M C k).ChallengeIdx ≃ Fin k
  | 0 => { toFun := fun i => i.1.elim0, invFun := Fin.elim0,
           left_inv := fun i => i.1.elim0, right_inv := fun i => i.elim0 }
  | k + 1 => (skipProver M _).trans
      (ProtocolSpec.challengeIdxEquiv.trans
        ((Equiv.sumCongr (verifierIndex C) (altIndex k)).trans (unitFin k)))

theorem altIndex_altChallenge (k : ℕ) (j : Fin k) : altIndex M C k (altChallenge M C k j) = j := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    refine Fin.cases rfl (fun i => ?_) j
    change unitFin k ((Equiv.sumCongr (verifierIndex C) (altIndex M C k))
      (ProtocolSpec.challengeIdxEquiv (skipProver M _
        (ProtocolSpec.ChallengeIdx.inr (ProtocolSpec.ChallengeIdx.inr
          (altChallenge M C k i)))))) = i.succ
    rw [skipProver_inr, ProtocolSpec.challengeIdxEquiv_inr]
    exact congrArg Fin.succ (ih i)

/-- The challenge of round `j` is its raw transcript entry. -/
theorem altValues_snd (k : ℕ) (tr : (alt M C k).Transcript (Fin.last (roundLength k))) (j : Fin k) :
    (altValues M C k tr j).2 = cast (altChallenge_type M C k j) (tr (altChallenge M C k j).1) := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [altValues, altChallenge, Fin.cases_zero, oneValue,
        ProtocolSpec.Transcript.left, ProtocolSpec.Transcript.right, ProtocolSpec.Transcript.fst,
        ProtocolSpec.Transcript.snd]
      rfl
    · refine (ih tr.right.right j).trans ?_
      dsimp only [ProtocolSpec.Transcript.left, ProtocolSpec.Transcript.right, ProtocolSpec.Transcript.snd]
      exact (cast_cast _ _ _).trans (cast_cast _ _ _)

/-- The message of round `j` is fixed by the entries through position `2j`. -/
theorem altValues_fst_congr (k : ℕ) (j : Fin k)
    (tr tr' : (alt M C k).Transcript (Fin.last (roundLength k)))
    (h : ∀ i, i.val ≤ 2 * j.val → tr i = tr' i) :
    (altValues M C k tr j).1 = (altValues M C k tr' j).1 := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    revert h
    refine Fin.cases (fun h => ?_) (fun j h => ?_) j
    · exact left_agrees tr tr' 0 (fun i hi => h i hi) ⟨0, by decide⟩ le_rfl
    · exact ih j tr.right.right tr'.right.right (right_agrees tr.right tr'.right
        (2 * j.val) (right_agrees tr tr' (1 + 2 * j.val) fun i hi => h i (by
          change i.val ≤ 2 * (j.val + 1); omega)))

/-- The challenge of round `j` is fixed by the entries through position `2j + 1`. -/
theorem altValues_snd_congr (k : ℕ) (j : Fin k)
    (tr tr' : (alt M C k).Transcript (Fin.last (roundLength k)))
    (h : ∀ i, i.val ≤ 2 * j.val + 1 → tr i = tr' i) :
    (altValues M C k tr j).2 = (altValues M C k tr' j).2 := by
  rw [altValues_snd, altValues_snd, h _ (altChallenge_val M C k j).le]

instance inhabitedAppend {a b : ℕ} {A : ProtocolSpec a} {B : ProtocolSpec b}
    [fa : ∀ i, Inhabited (A.Type i)] [fb : ∀ i, Inhabited (B.Type i)] :
    ∀ i, Inhabited ((A ++ B).Type i) := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [ProtocolSpec.append_Type_castAdd]
    exact fa j
  · rw [ProtocolSpec.append_Type_natAdd]
    exact fb j

instance alt_inhabited [Inhabited M] [Inhabited C] (k : ℕ) :
    ∀ i, Inhabited ((alt M C k).Type i) := by
  induction k with
  | zero => exact fun i => i.elim0
  | succ k ih => exact inhabitedAppend

instance fintypeAppend {a b : ℕ} {A : ProtocolSpec a} {B : ProtocolSpec b}
    [fa : ∀ i, Fintype (A.Challenge i)] [fb : ∀ i, Fintype (B.Challenge i)] :
    ∀ i : (A ++ B).ChallengeIdx, Fintype ((A ++ B).Challenge i) := by
  intro i
  infer_instance

instance alt_fintype [Fintype M] [Fintype C] (k : ℕ) :
    ∀ i : (alt M C k).ChallengeIdx, Fintype ((alt M C k).Challenge i) := by
  induction k with
  | zero => exact empty_fintype
  | succ k ih => exact fintypeAppend

instance alt_decidableEq [DecidableEq M] [DecidableEq C] :
    (k : ℕ) → ∀ i : (alt M C k).ChallengeIdx, DecidableEq ((alt M C k).Challenge i)
  | 0 => empty_decidableEq
  | k + 1 =>
    @ProtocolSpec.append_challenge_decidableEq _ _ (one .P_to_V M) (one .V_to_P C ++ alt M C k)
      one_decidableEq
      (@ProtocolSpec.append_challenge_decidableEq _ _ (one .V_to_P C) (alt M C k) one_decidableEq
        (alt_decidableEq k))

instance alt_nonempty [Nonempty M] [Nonempty C] (k : ℕ) :
    ∀ i : (alt M C k).ChallengeIdx, Nonempty ((alt M C k).Challenge i) := by
  induction k with
  | zero => exact empty_nonempty
  | succ k ih => exact ProtocolSpec.append_challenge_nonempty

end Alt

/-! ### The empty phase -/

/-- The empty phase has no challenge. -/
instance empty_isEmpty : IsEmpty empty.ChallengeIdx := ⟨fun i => i.1.elim0⟩

/-- The empty phase has no move. -/
instance empty_inhabited : ∀ i, Inhabited (empty.Type i) := fun i => i.elim0

/-! ### Which entries each value reads -/

/-- A transcript updated at position `i` agrees with the original below `i`. -/
theorem update_agrees {N : ℕ} {β : Fin N → Type} (tr : (j : Fin N) → β j) (i : Fin N) (x : β i)
    {k : ℕ} (hk : k < i.val) : ∀ j, j.val ≤ k → Function.update tr i x j = tr j := by
  intro j hj
  exact Function.update_of_ne (fun he => by rw [he] at hj; omega) x tr

/-! ### Counting -/

open Classical in
/-- A count transported along an equality of challenge types. -/
theorem card_filter_cast_le {α β : Type} [Fintype α] [Fintype β] (h : α = β) (P : β → Prop)
    {ε : ℝ≥0} (hP : ((Finset.univ.filter P).card : ℝ≥0) ≤ ε * Fintype.card β) :
    ((Finset.univ.filter fun x : α => P (cast h x)).card : ℝ≥0) ≤ ε * Fintype.card α := by
  subst h
  simp only [cast_eq]
  convert hP

/-! ### A complete transcript from its parts -/

section Ext

theorem one_ext {dir : Direction} {Msg : Type} {tr tr' : (one dir Msg).Transcript (Fin.last 1)}
    (h : oneValue tr = oneValue tr') : tr = tr' := by
  funext i
  have hi : i = ⟨0, by decide⟩ := Fin.ext (by have := i.isLt; simp at this; omega)
  subst hi
  exact h

theorem split_ext {n₁ n₂ : ℕ} {P₁ : ProtocolSpec n₁} {P₂ : ProtocolSpec n₂}
    {tr tr' : (P₁ ++ P₂).Transcript (Fin.last (n₁ + n₂))}
    (h₁ : tr.left = tr'.left) (h₂ : tr.right = tr'.right) : tr = tr' := by
  rw [← ProtocolSpec.Transcript.join_left_right tr, ← ProtocolSpec.Transcript.join_left_right tr', h₁, h₂]

theorem alt_ext (M C : Type) : (k : ℕ) → {tr tr' : (alt M C k).Transcript (Fin.last (roundLength k))} →
    altValues M C k tr = altValues M C k tr' → tr = tr'
  | 0, _, _, _ => funext fun i => i.elim0
  | k + 1, _, _, h => by
    have h0 := congrFun h 0
    simp only [altValues, Fin.cases_zero, Prod.mk.injEq] at h0
    exact split_ext (one_ext h0.1) (split_ext (one_ext h0.2)
      (alt_ext M C k (funext fun j => by simpa only [altValues, Fin.cases_succ] using congrFun h j.succ)))

end Ext

/-! ### One-move phases at `GKR.Schedule.one` -/

/-- A fixed prover message, at the spec `one .P_to_V Msg` the skip phase is written in. -/
def oneMsg {Msg : Type} (msg : Msg) : CausalTranscript (one .P_to_V Msg) :=
  CausalTranscript.oneMessage msg

/-- A fresh verifier challenge, at the spec `one .V_to_P Msg`. -/
def oneChal (Msg : Type) : CausalTranscript (one .V_to_P Msg) :=
  CausalTranscript.oneChallenge Msg

/-! ### Alternating rounds -/

section AltFamily

variable {M C : Type} [Zero C]

/-- The honest alternating rounds: the message of round `j` is `f s j`, with the challenges
`s_j, s_{j+1}, …` not yet drawn filled with zero. -/
def altFamily : (k : ℕ) → ((Fin k → C) → Fin k → M) → CausalTranscript (alt M C k)
  | 0, _ => CausalTranscript.empty _
  | k + 1, f => (oneMsg (f 0 0)).append fun _ =>
      (oneChal C).append fun tr =>
        altFamily k fun s j => f (Fin.cons (tr ⟨0, by decide⟩) s) j.succ

/-- The message of round `j` is `f` at the challenges before `j`, the rest zero. -/
theorem altFamily_fst (k : ℕ) (f : (Fin k → C) → Fin k → M) (ch : (alt M C k).Challenges)
    (j : Fin k) :
    (altValues M C k ((altFamily k f).transcript ch) j).1 =
      f (fun v => if v < j then (altValues M C k ((altFamily k f).transcript ch) v).2 else 0) j := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    have hl := CausalTranscript.append_left (oneMsg (f 0 0))
      (fun _ => (oneChal C).append fun tr =>
        altFamily k fun s j => f (Fin.cons (tr ⟨0, by decide⟩) s) j.succ) ch
    have hr := CausalTranscript.append_right (oneMsg (f 0 0))
      (fun _ => (oneChal C).append fun tr =>
        altFamily k fun s j => f (Fin.cons (tr ⟨0, by decide⟩) s) j.succ) ch
    have hil := CausalTranscript.append_left (oneChal C)
      (fun tr => altFamily k fun s j => f (Fin.cons (tr ⟨0, by decide⟩) s) j.succ) ch.right
    have hir := CausalTranscript.append_right (oneChal C)
      (fun tr => altFamily k fun s j => f (Fin.cons (tr ⟨0, by decide⟩) s) j.succ) ch.right
    set c : C := (oneChal C).transcript ch.right.left ⟨0, by decide⟩
    set f' : (Fin k → C) → Fin k → M := fun s j => f (Fin.cons c s) j.succ
    have hv : altValues M C (k + 1) ((altFamily (k + 1) f).transcript ch) =
        Fin.cases (f 0 0, c) (altValues M C k ((altFamily k f').transcript ch.right.right)) := by
      change Fin.cases (motive := fun _ => M × C) (oneValue ((altFamily (k + 1) f).transcript ch).left,
          oneValue ((altFamily (k + 1) f).transcript ch).right.left)
        (altValues M C k ((altFamily (k + 1) f).transcript ch).right.right) = _
      erw [hl, hr, hil, hir]
      rfl
    rw [hv]
    cases j using Fin.cases with
    | zero =>
      simp only [Fin.cases_zero]
      congr 1
    | succ j =>
      simp only [Fin.cases_succ]
      rw [ih f' ch.right.right j]
      show f (Fin.cons c _) j.succ = _
      congr 1
      funext v
      cases v using Fin.cases with
      | zero => simp [Fin.succ_pos]
      | succ v => simp [Fin.succ_lt_succ_iff]

end AltFamily

end GordieHowe.HashCircuit.Skip
