-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.Schedule

@[expose] public section

/-! Typed challenge replacement preserves both preceding prover values. -/
namespace GordieHowe.GKR.Schedule
open IOP
variable (F : Type) [Field F]

def roundPair : (k : ℕ) → Fin k → Fin (roundLength k)
  | 0, j => j.elim0
  | k+1, j => Fin.cases (Fin.castAdd _ (0 : Fin 1))
      (fun i => Fin.natAdd 1 (Fin.natAdd 1 (roundPair k i))) j

theorem roundPair_val (k : ℕ) (j : Fin k) : (roundPair k j).val = 2*j.val := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    refine Fin.cases rfl (fun i => ?_) j
    change 1+(1+(roundPair k i).val) = 2*(i.val+1)
    rw [ih]
    omega

omit [Field F] in
theorem roundPair_type (k : ℕ) (j : Fin k) : (rounds F k).Type (roundPair k j) = (F×F) := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    refine Fin.cases rfl (fun i => ?_) j
    change (one .P_to_V (F×F) ++ (one .V_to_P F ++ rounds F k)).Type
      (Fin.natAdd 1 (Fin.natAdd 1 (roundPair k i))) = (F×F)
    rw [ProtocolSpec.append_Type_natAdd, ProtocolSpec.append_Type_natAdd]
    exact ih i

theorem roundMessages_pair (k : ℕ)
    (tr : (rounds F k).Transcript (Fin.last (roundLength k))) (j : Fin k) :
    ((roundMessages F k tr j).p0, (roundMessages F k tr j).p2) =
      cast (roundPair_type F k j) (tr (roundPair k j)) := by
  induction k with
  | zero => exact j.elim0
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [roundMessages, roundPair, Fin.cases_zero, oneValue,
        ProtocolSpec.Transcript.left, ProtocolSpec.Transcript.right, ProtocolSpec.Transcript.fst]
      rfl
    · refine (ih tr.right.right j).trans ?_
      dsimp only [ProtocolSpec.Transcript.left, ProtocolSpec.Transcript.right, ProtocolSpec.Transcript.snd]
      exact (cast_cast _ _ _).trans (cast_cast _ _ _)

theorem roundUpdate_pair (k : ℕ)
    (tr : (rounds F k).Transcript (Fin.last (roundLength k))) (i j : Fin k) (x : F) :
    ((roundMessages F k (roundUpdate F k tr i x) j).p0,
      (roundMessages F k (roundUpdate F k tr i x) j).p2) =
      ((roundMessages F k tr j).p0, (roundMessages F k tr j).p2) := by
  rw [roundMessages_pair, roundMessages_pair]
  apply congrArg
  unfold roundUpdate
  apply Function.update_of_ne
  intro h
  have he := congrArg Fin.val h
  rw [roundPair_val, roundChallenge_val] at he
  omega

theorem roundUpdate_challenge_ne (k : ℕ)
    (tr : (rounds F k).Transcript (Fin.last (roundLength k))) (i j : Fin k) (x : F)
    (hji : j ≠ i) :
    (roundMessages F k (roundUpdate F k tr i x) j).challenge =
      (roundMessages F k tr j).challenge := by
  rw [roundMessages_challenge, roundMessages_challenge]
  apply congrArg
  unfold roundUpdate
  apply Function.update_of_ne
  intro h
  have he := congrArg Fin.val h
  rw [roundChallenge_val, roundChallenge_val] at he
  exact hji (Fin.ext (by omega))

omit [Field F] in
theorem message_ext {a b : LayerProtocol.Message F}
    (hp : (a.p0,a.p2) = (b.p0,b.p2)) (hc : a.challenge = b.challenge) : a = b := by
  cases a
  cases b
  simp_all

theorem roundMessages_update (k : ℕ)
    (tr : (rounds F k).Transcript (Fin.last (roundLength k))) (i : Fin k) (x : F) :
    roundMessages F k (roundUpdate F k tr i x) =
      Function.update (roundMessages F k tr) i { roundMessages F k tr i with challenge := x } := by
  funext j
  by_cases hji : j = i
  · subst j
    rw [Function.update_self]
    apply message_ext F
    · exact roundUpdate_pair F k tr i i x
    · exact (roundMessages_challenge F k _ i).trans (roundUpdate_at F k tr i x)
  · rw [Function.update_of_ne hji]
    exact message_ext F (roundUpdate_pair F k tr i j x)
      (roundUpdate_challenge_ne F k tr i j x hji)

end GordieHowe.GKR.Schedule
