-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Keccak.HashCircuit.Relation
public import GordieHowe.ProofSystem.GKR.Schedule
public import GordieHowe.Model.IOP.TranscriptEventReduction
public import GordieHowe.Foundations.Probability.ChallengeEventCount

@[expose] public section

/-!
# The univariate-skip phase of the batched-Keccak H as a claim reduction

The skip's messages and challenges as a typed protocol phase, and the claim
reduction "the skip relation holds on the committed operands, or a skip event
occurred at a challenge already drawn" (`reduction`). The state is
`TranscriptEventReduction`'s: each verifier move charges only its own event,
built from the transcript before it and the committed operands and pads.

The phase is stated followed by any prover moves `R` that have no challenge (`phase K w n R`,
`IsEmpty R.ChallengeIdx`): the batched H circuit's skip phase (`spec`) ends with the sixteen reveals
`M_k` (`Reveals`), GordieHowe's bit-packed batch (`GordieHowe.BatchedZerocheck.spec` at `D = 2`,
`e = w − 1`) with no move (`R = empty`). The readers, events, counts and the reduction do not read
`R`.

Message order (`lib/sumcheck/keccak_skip_argument.h` on main at `41f8aa26`, `constraints`, lines
311-359, and `finish`, lines 361-364; run from `KeccakSkipCircuitLink::constraints` in
`keccak_skip_circuit_link.h`, after the Falcon `Kmac`/reveal prefix and before the H GKR):

| Move | Sender | Value | Source |
|---|---|---|---|
| `ρ ∈ K^n` | verifier | zerocheck point | lines 314-316 |
| skip message | prover | `w - 1` masked values | line 317 |
| `r ∈ K` | verifier | skip evaluation point | line 318 |
| round `i` | prover, then verifier | two masked coefficients `q1, q2`, then `s_i` | lines 332-333 |
| terminal | prover | three masked operand claims | line 352 |
| `u ∈ K^3` | verifier | batching scalars | lines 354-355 |
| `M_k` | prover | sixteen masked opening forms | `finish`, line 364 |

Events, charged at their challenges: `rhoEvent` (degree `n` in `ρ`,
`ChallengeEventMv`), `rEvent` (degree `2(w-1)`), `roundEvent i` (degree `3`),
`uEvent` (degree `1` in `u`, `ChallengeEventMv`). The errors sum to
`n/|K| + 2(w-1)/|K| + 3n/|K| + 1/|K|` (`error_sum`). The `M_k` message is
unrestricted; its meaning comes from the opening rows checked by Ligero.
-/

namespace GordieHowe.HashCircuit.Skip

open IOP GKR.Schedule Sumcheck.UnivariateSkip
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

/-! ### The skip phase -/

variable (K : Type) (w n : ℕ) {mR : ℕ} (R : ProtocolSpec mR)

/-- The empty phase has no challenge. -/
instance empty_isEmpty : IsEmpty empty.ChallengeIdx := ⟨fun i => i.1.elim0⟩

/-- The empty phase has no move. -/
instance empty_inhabited : ∀ i, Inhabited (empty.Type i) := fun i => i.elim0

variable {K w n R}

variable (K w n R)

variable {K w n R}

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

end GordieHowe.HashCircuit.Skip
