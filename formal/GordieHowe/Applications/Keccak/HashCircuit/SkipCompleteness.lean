-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Keccak.HashCircuit.Skip
public import GordieHowe.Model.IOP.CompletenessAppend
public import GordieHowe.ProofSystem.GKR.Schedule
public import GordieHowe.ProofSystem.Ligero.Tableau
public import GordieHowe.ProofSystem.GKR.SourceCircuit

@[expose] public section

/-!
# The honest transcript pieces of the skip phase

The honest transcript pieces (`CausalTranscript`) the skip phase is built from: a fixed
prover message and a fresh verifier challenge at a one-move spec (`oneMsg`, `oneChal`), and the
honest alternating rounds (`altFamily`), whose round `j` message reads only the challenges before
`j`, the challenges not yet drawn filled with zero (`altFamily_fst`). The honest transcript family
of the batch phase built from them is `GordieHowe.BatchedZerocheck.phaseFamily`.
-/

namespace GordieHowe.HashCircuit.Skip

open IOP GKR.Schedule Sumcheck.UnivariateSkip

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
