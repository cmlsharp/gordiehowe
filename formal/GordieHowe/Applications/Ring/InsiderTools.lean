-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.AbsorbRelay
public import GordieHowe.Model.Quantum.Interactive.ThenProg
public import GordieHowe.Model.NARG.VerifierProg
public import GordieHowe.Applications.Ring.Scheme
public import GordieHowe.Model.Quantum.Interactive.SplitHybrid
public import GordieHowe.SPBCS.Extraction.OnlineExtractTest
public import GordieHowe.SPBCS.Online
public import GordieHowe.SPBCS.ProverProg

@[expose] public section

/-!
# Tools for the reduction of BKM06 Definition 7 at every base-message map

Facts about the model used by the unforgeability reductions of the ring signature `ofBase`.

- `NARG.Verifier.prog` (`GordieHowe/Model/NARG/VerifierProg.lean`): a verifier as a classical
  oracle program.
- `Quantum.KindAlg.postAss_eq_nil`: a challenger whose replies carry no assignments leaves the
  oracle unchanged.
- `Quantum.KindAlg.map_request_history_stateAt`: the requests of a challenger's history are the
  first `Q` logged requests.
- `Quantum.Alg.toOuterMeasure_realLaw_eq_tsum`: an event of the real law is the oracle average of
  the output law's.
-/

namespace GordieHowe

open Quantum
open scoped ENNReal

/-! ### Challengers without assignments, and their histories -/

namespace Quantum.KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {ksA : KindShape X Y Req Resp} (A : KindAlg ksA O) (C : Challenger X Y Req Resp)

/-- **A challenger whose replies carry no assignments leaves the oracle unchanged**: the
assignments in force after the slots are empty. -/
theorem postAss_eq_nil (hC : ∀ ω hist req ans, (C.outWith ω hist req ans).assignments = [])
    (u : A.CCl C) : A.postAss C u = [] := by
  unfold postAss stateAt Challenger.regState
  suffices ∀ n, (Challenger.regStateOf C.Q C.respond u.coins u.logs (A.ansOf C u) n).assignments
      = [] from this _
  intro n
  induction n with
  | zero => rfl
  | succ j ih =>
    simp only [Challenger.regStateOf]
    by_cases hj : j < A.slots
    · simp only [hj, dite_true]
      split
      · exact ih
      · by_cases hQ : (Challenger.regStateOf C.Q C.respond u.coins u.logs (A.ansOf C u)
          j).history.length < C.Q
        · simp only [hQ, ite_true, ih, List.nil_append]; exact hC _ _ _ _
        · simp only [hQ, ite_false]; exact ih
    · simp only [hj, dite_false]; exact ih

/-- **The requests of the challenger's history after the slots below `j` are the first `Q`
logged requests.** -/
theorem map_request_history_stateAt (u : A.CCl C) (j : ℕ) :
    (A.stateAt C u j).history.map HistoryEntry.request = (requestsBefore u.logs j).take C.Q := by
  unfold stateAt Challenger.regState
  induction j with
  | zero => simp [Challenger.regStateOf, requestsBefore]
  | succ j ih =>
    have hlen := congrArg List.length ih
    simp only [List.length_map, List.length_take] at hlen
    simp only [Challenger.regStateOf, requestsBefore]
    by_cases hj : j < A.slots
    · simp only [hj, dite_true]
      split
      · next heq => simp [heq, ih]
      · next r heq =>
        simp only [heq, Option.toList_some]
        by_cases hQ : (Challenger.regStateOf C.Q C.respond u.coins u.logs (A.ansOf C u)
          j).history.length < C.Q
        · simp only [hQ, ite_true]
          have hl : (requestsBefore u.logs j).length < C.Q := by omega
          rw [List.map_append, ih, List.take_of_length_le hl.le,
            List.take_of_length_le (by simp only [List.length_append]; simp; omega)]
          rfl
        · simp only [hQ, ite_false]
          rw [ih, List.take_append_of_le_length (by omega)]
    · simp [hj, ih]

end Quantum.KindAlg

namespace Quantum.Alg

variable {X Y O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  (A : Alg X Y O)

/-- **An event of the real law is the oracle average of the output law's**: the oracle uniform, the
event on the output and the oracle read through `e`. -/
theorem toOuterMeasure_realLaw_eq_tsum [Nonempty Y] {B : Type} (e : Y ≃ B)
    (P : O → (X → B) → Prop) :
    (A.realLaw e).toOuterMeasure {p | ∃ v ∈ p.out, P v p.oracle} =
      ∑' H, PMF.uniformOfFintype (X → Y) H * (A.outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v (e ∘ H)} := by
  rw [Alg.realLaw, PMF.toOuterMeasure_bind_apply]
  congr 1
  funext H
  rw [PMF.toOuterMeasure_map_apply]
  rfl

end Quantum.Alg

end GordieHowe
