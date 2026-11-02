-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.Adversary

@[expose] public section

/-!
# A bound on the schedule of a game adversary

An adversary of the class of `GordieHowe/Model/RingSignature/Adversary.lean`
(`RingSignature.GameAdversary`) bounds its oracle queries (`t`), and every challenger answers at
most `Q` requests; the number of slots of its schedule (query and request slots) is not bounded by
either, since a request slot past the `Q`-th is answered by nothing. A reduction that runs the
adversary's whole schedule inside a game whose challenger must answer each of its steps needs the
schedule's length bounded uniformly over the start input and the auxiliary input: the role a
running-time bound plays for an efficient adversary.

- `RingSignature.GameAdversary.ScheduleLE A S w P`: on every start input and auxiliary value, the
  adversary's algorithm has at most `S` slots, query width at most `w` and at most `P` post batches.
- `RingSignature.GameAdversary.exists_scheduleLE`: every adversary with finitely many start inputs
  and auxiliary values has a schedule bound (satisfiability).
- `RingSignature.GameAdversary.ScheduleLE.depth_le`: the composition of the algorithm with a
  challenger with `q` queries per reply has depth at most `S · (q + w) + w · P`
  (`Quantum.AdaptiveIAlg.compose_depth`).
-/

namespace GordieHowe.RingSignature

open GordieHowe.Quantum

namespace GameAdversary

variable {X Y Req Resp In O : Type} [Fintype X] [Fintype Y] [Fintype Req] [Fintype Resp]
  [DecidableEq X] [DecidableEq Y] [DecidableEq Req] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {t : ℕ}

/-- **A bound on the adversary's schedule**, uniform over the start input and the auxiliary input:
at most `S` slots, query width at most `w`, at most `P` post batches. It plays the role of a
running-time bound for reductions that run the whole schedule. -/
structure ScheduleLE (A : GameAdversary X Y Req Resp In O t) (S w P : ℕ) : Prop where
  /-- At most `S` slots. -/
  slots_le : ∀ inp a, ((A inp).alg a).slots ≤ S
  /-- Query width at most `w`. -/
  width_le : ∀ inp a, ((A inp).alg a).width ≤ w
  /-- At most `P` post batches. -/
  post_le : ∀ inp a, ((A inp).alg a).post ≤ P

/-- **Every adversary with finitely many start inputs and auxiliary values has a schedule bound**:
the sums of the slots, the widths and the post batches over all of them. -/
theorem exists_scheduleLE (A : GameAdversary X Y Req Resp In O t) [Finite In]
    (hA : ∀ inp, Finite (A inp).Aux) : ∃ S w P, A.ScheduleLE S w P := by
  classical
  have := Fintype.ofFinite In
  have : ∀ inp, Fintype (A inp).Aux := fun inp => @Fintype.ofFinite _ (hA inp)
  have hle : ∀ (g : ∀ inp, (A inp).Aux → ℕ) inp a, g inp a ≤ ∑ inp', ∑ a', g inp' a' :=
    fun g inp a => (Finset.single_le_sum (f := fun a' => g inp a') (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ a)).trans (Finset.single_le_sum (f := fun inp' => ∑ a', g inp' a')
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ inp))
  exact ⟨_, _, _, ⟨hle fun inp a => ((A inp).alg a).slots, hle fun inp a => ((A inp).alg a).width,
    hle fun inp a => ((A inp).alg a).post⟩⟩

/-- **The depth of a composition is bounded by the schedule bound**: `S · (q + w) + w · P` for a
challenger with `q` queries per reply. -/
theorem ScheduleLE.depth_le {A : GameAdversary X Y Req Resp In O t} {S w P : ℕ}
    (h : A.ScheduleLE S w P) (inp : In) (a : (A inp).Aux) (C : Challenger X Y Req Resp) :
    (((A inp).alg a).compose C).depth ≤ S * (C.q + w) + w * P := by
  rw [AdaptiveIAlg.compose_depth]
  have h1 := h.slots_le inp a
  have h2 := h.width_le inp a
  have h3 := h.post_le inp a
  exact Nat.add_le_add (Nat.mul_le_mul h1 (Nat.add_le_add_left h2 _)) (Nat.mul_le_mul h2 h3)

end GameAdversary

end GordieHowe.RingSignature
