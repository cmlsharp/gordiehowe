-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.AbsorbAssign
public import GordieHowe.Model.Quantum.Interactive.HiddenReadsEvent

@[expose] public section

/-!
# The final oracle in force, and side coins of a relaying challenger

- `QueryBoundedAdversary.assignLaw_eq_transcriptLawIn`: the two laws of the output, the answered
  requests and the final oracle in force agree. `assignLaw`
  (`GordieHowe/Model/Quantum/Interactive/AbsorbAssign.lean`) reads the oracle as the base oracle
  reprogrammed by the final assignments and the requests from the answered history;
  `transcriptLawIn` (`GordieHowe/Model/RingSignature/RevealedReprogram.lean`) reads the pure
  game's oracle at the coins and logs and the first `C.Q` logged requests.
- `QueryBoundedAdversary.assignLaw_eq_sum_of_relays`: when a challenger `C` draws side coins
  `s ← σ` and main coins, and relays a main challenger `C'` through `G s`, its events are the
  `σ`-average of the events against challengers `D s` that relay `C'` through `G s` with no side
  coins. Both sides are the same average of the patched absorbed adversary
  (`AdaptiveIAlg.toOuterMeasure_eq_sum_absorbAssignP`).
- `AdaptiveIAlg.outLaw_composeBothOut_thenProgOut_chal`, `QueryBoundedAdversary.assignLaw_thenProgOut`:
  the adversary followed by a program on its output (`thenProgOut`), against every challenger:
  the program runs at the final oracle in force, and `assignLaw` maps each output `(o, rs, G)` to
  `((o, (P o).run G), rs, G)`.
-/

open scoped ENNReal

namespace GordieHowe.Quantum

namespace AdaptiveIAlg

variable {X Y Req Resp O R : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (P : O → GordieHowe.OracleProg X Y R) (q : ℕ)
  (hP : ∀ o, (P o).QueriesLE q) (C : Challenger X Y Req Resp)

/-- **The adversary followed by a program on its output, with a readout of the challenger's
registers**: for every readout `F` of the output and the challenger's registers, the output law
of the composition at `H` is the law of `A`'s composition read as `F (o, (P o).run H') u`, where
`o` is `A`'s output, `u` the challenger's registers and `H'` the oracle `H` reprogrammed by the
final assignments. -/
theorem outLaw_composeBothOut_thenProgOut_chal {O' : Type} (F : O × R → A.toKindAlg.CCl C → O')
    (H : X → Y) :
    ((A.thenProgOut P q hP).toKindAlg.composeBothOut C fun v =>
        F ((A.thenProgOut P q hP).output C v) v.chal).outLaw H =
      (A.toKindAlg.composeBothOut C fun v =>
        F (A.output C v, (P (A.output C v)).run (H.reprogram (A.toKindAlg.postAss C v.chal)))
          v.chal).outLaw H := by
  refine (A.outLaw_composeBothOut_thenProgWith (A.progOn P) q (fun w => hP (A.out w)) _ C F
    H).trans (congrArg (fun f => (A.toKindAlg.composeBothOut C f).outLaw H) (funext fun v => ?_))
  show F (A.out _, A.progRes (A.progOn P) q _ _ (Quantum.OracleProg.tab _ q _ _ q)) _ = _
  rw [A.progRes_tab (A.progOn P) q (fun w => hP (A.out w))]
  rfl

end AdaptiveIAlg

namespace QueryBoundedAdversary

variable {X Y Req Resp O Req' Resp' Xs Ys : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req] [Inhabited X]
  [Inhabited Req'] [Nonempty X] [AddGroup Y] [Nonempty Y] {t : ℕ}

omit [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req]
  [Inhabited Req'] [Inhabited X] in
/-- **The two transcript laws with the final oracle in force agree**: `assignLaw` (the base oracle
reprogrammed by the final assignments, the requests of the answered history) is
`transcriptLawIn` (the pure game's oracle, the first `C.Q` logged requests). -/
theorem assignLaw_eq_transcriptLawIn (𝒜 : QueryBoundedAdversary X Y Req Resp O t)
    (C : Challenger X Y Req Resp) (H : X → Y) :
    𝒜.assignLaw C H = 𝒜.transcriptLawIn C H := by
  unfold assignLaw transcriptLawIn
  congr 1
  funext a
  unfold AdaptiveIAlg.assignReadout
  simp_rw [AdaptiveIAlg.map_request_history]
  exact (𝒜.alg a).toKindAlg.outLaw_composeBothOut_postAss C
    (fun v G => ((𝒜.alg a).output C v, (requests v.chal.logs).take C.Q, G)) H

/-- **Side coins of a relaying challenger average out**: when `C` draws side coins `s ← σ` and
the coins of `C'` (`e`, `hcoins`) and relays `C'` through `G s` (`hrel`), and each `D s`, with
the coins of `C'` alone (`eD`, `hcoinsD`), relays `C'` through `G s` (`hrelD`) for the same number
of requests (`hQ`), an event of the output, the answered requests and the final oracle in force
against `C` is the `σ`-average of the event against `D s`. The relay's assignments must be safe
for `C'` (`hS`). -/
theorem assignLaw_eq_sum_of_relays (𝒜 : QueryBoundedAdversary X Y Req Resp O t) {S : Type}
    [Fintype S] (σ : PMF S) (G : S → AssignRelay X Y Req Resp Req' Resp' Xs Ys)
    {C : Challenger X Y Req Resp} {C' : Challenger X Y Req' Resp'} (D : S → Challenger X Y Req Resp)
    (e : C.Coins ≃ S × C'.Coins) (hcoins : ∀ s c', C.coins (e.symm (s, c')) = σ s * C'.coins c')
    (hrel : ∀ s c', (G s).RelaysChallenger C (e.symm (s, c')) C' c')
    (eD : ∀ s, (D s).Coins ≃ Unit × C'.Coins)
    (hcoinsD : ∀ s c', (D s).coins ((eD s).symm ((), c')) = C'.coins c')
    (hrelD : ∀ s c', (G s).RelaysChallenger (D s) ((eD s).symm ((), c')) C' c')
    (hQ : ∀ s, (D s).Q = C.Q) (hS : ∀ s, AssignRelay.SafeAssign C' (G s)) (H : X → Y)
    (E : O × List Req × (X → Y) → Prop) :
    (𝒜.assignLaw C H).toOuterMeasure {x | ∃ p ∈ x, E p} =
      ∑ s, σ s * (𝒜.assignLaw (D s) H).toOuterMeasure {x | ∃ p ∈ x, E p} := by
  have hD : ∀ s a, (((𝒜.alg a).toKindAlg.composeBothOut (D s)
      ((𝒜.alg a).assignReadout (D s) H)).outLaw H).toOuterMeasure {x | ∃ p ∈ x, E p} =
      ((((𝒜.alg a).absorbAssignP Req' Resp' C.Q).toKindAlg.composeBothOut
        (AssignRelay.chalT C' (G s) C.Q) ((𝒜.alg a).patchReadout (G s) C.Q C' H)).outLaw
          H).toOuterMeasure {x | ∃ p ∈ x, E p} := by
    intro s a
    have h := (𝒜.alg a).toOuterMeasure_eq_sum_absorbAssignP (PMF.pure ()) (fun _ => G s) (eD s)
      (fun _ c' => by rw [hcoinsD, PMF.pure_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl), one_mul])
      (fun _ c' => hrelD s c') (fun _ => hS s) H E
    rw [Fintype.sum_unique, PMF.pure_apply, ite_eq_left_of_eq_true _ _ (eq_true rfl), one_mul,
      hQ s] at h
    exact h
  unfold assignLaw
  simp_rw [PMF.toOuterMeasure_bind_apply, hD,
    (𝒜.alg _).toOuterMeasure_eq_sum_absorbAssignP σ G e hcoins hrel hS H E]
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun a => ?_
  ring

omit [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req]
  [Inhabited Req'] [Inhabited X] in
/-- **The transcript with the final oracle of the adversary followed by a program on its output**:
against every challenger, the law `assignLaw` of `A` with each `(o, rs, G)` replaced by
`((o, (P o).run G), rs, G)`; the program reads the final oracle in force `G`. -/
theorem assignLaw_thenProgOut {R : Type} (𝒜 : QueryBoundedAdversary X Y Req Resp O t)
    (P : O → GordieHowe.OracleProg X Y R) (q : ℕ) (hP : ∀ o, (P o).QueriesLE q) (s : ℕ)
    (hs : ∀ a, (𝒜.alg a).width * q ≤ s) (C : Challenger X Y Req Resp) (H : X → Y) :
    (𝒜.thenProgOut P q hP s hs).assignLaw C H =
      (𝒜.assignLaw C H).map (Option.map fun x => ((x.1, (P x.1).run x.2.2), x.2.1, x.2.2)) := by
  simp only [assignLaw, PMF.map_bind]
  refine congrArg 𝒜.aux.bind (funext fun a => ?_)
  unfold AdaptiveIAlg.assignReadout
  refine ((𝒜.alg a).outLaw_composeBothOut_thenProgOut_chal P q hP C (fun oo u =>
      (oo, ((𝒜.alg a).toKindAlg.stateAt C u (𝒜.alg a).toKindAlg.slots).history.map
        HistoryEntry.request, H.reprogram ((𝒜.alg a).toKindAlg.postAss C u))) H).trans ?_
  rw [← KindAlg.outLaw_composeBothOut_map]
  rfl

omit [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req]
  [Inhabited Req'] [Inhabited X] in
/-- **An event of the transcript implies an event of the adversary followed by a program**: when
`E (o, rs, G)` implies `E' ((o, (P o).run G), rs, G)`, the event `E` of `A` has at most the
probability of `E'` of `A.thenProgOut` (`assignLaw_thenProgOut`). -/
theorem assignLaw_le_thenProgOut {R : Type} (𝒜 : QueryBoundedAdversary X Y Req Resp O t)
    (P : O → GordieHowe.OracleProg X Y R) (q : ℕ) (hP : ∀ o, (P o).QueriesLE q) (s : ℕ)
    (hs : ∀ a, (𝒜.alg a).width * q ≤ s) (C : Challenger X Y Req Resp) (H : X → Y)
    (E : O × List Req × (X → Y) → Prop) (E' : (O × R) × List Req × (X → Y) → Prop)
    (himp : ∀ o rs G, E (o, rs, G) → E' ((o, (P o).run G), rs, G)) :
    (𝒜.assignLaw C H).toOuterMeasure {x | ∃ p ∈ x, E p} ≤
      ((𝒜.thenProgOut P q hP s hs).assignLaw C H).toOuterMeasure {x | ∃ p ∈ x, E' p} := by
  rw [assignLaw_thenProgOut, PMF.toOuterMeasure_map_apply]
  refine MeasureTheory.measure_mono fun x hx => ?_
  obtain ⟨p, hp, h⟩ := hx
  rcases x with _ | x
  · cases hp
  · cases hp
    exact ⟨_, rfl, himp _ _ _ h⟩

end QueryBoundedAdversary

end GordieHowe.Quantum
