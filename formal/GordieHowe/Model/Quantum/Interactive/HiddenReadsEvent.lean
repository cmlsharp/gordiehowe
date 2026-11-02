-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.HiddenReadsPair
public import GordieHowe.Model.Quantum.Interactive.RecordReplies
public import GordieHowe.Model.Quantum.Interactive.ThenProgOut
public import GordieHowe.Model.Quantum.Interactive.SplitHybrid
public import GordieHowe.Model.RingSignature.RevealedReprogram
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

@[expose] public section

/-!
# Hidden points with the challenger's reads, for events at the final oracle in force

`AdaptiveIAlg.advantage_outLaw_le_of_hiddenReadsPair`
(`GordieHowe/Model/Quantum/Interactive/HiddenReadsPair.lean`) bounds the change of an output
probability between the two challengers of a `Challenger.HiddenReadsPair`. This file carries the
bound to events of the output `o`, the answered requests `rs` and the final oracle in force `G`
(the readout of `QueryBoundedAdversary.transcriptLawIn`) that read `G` only through a classical
program `Pv o` with at most `q` queries: events `Ev o rs ((Pv o).run G)`.

Such an event is the event that a derived adversary outputs `true`
(`AdaptiveIAlg.eventOut`): `A` recording its replies (`AdaptiveIAlg.recordReplies`), followed by
`Pv` on its output (`AdaptiveIAlg.thenProgOut`), its output mapped to the truth value of the
event (`AdaptiveIAlg.mapOut`). The bound is that of the single output `true` of the derived
adversary, with `q` more post batches; it does not grow with the number of outputs.

- `KindAlg.outLaw_composeBothOut_postAss`: the base oracle reprogrammed by the final
  assignments may be replaced, in a readout, by the pure game's oracle at the coins and logs.
- `KindAlg.toOuterMeasure_outLaw_eq_some_true`: an event of a readout is the probability that
  its truth value is `true`.
- `AdaptiveIAlg.outLaw_compose_mapOut_output`: the output law of `A.mapOut g`
  (`GordieHowe/Model/RingSignature/Transcript.lean`) is `A`'s composition read as `g` of the
  output.
- `AdaptiveIAlg.outLaw_recordReplies_with`: `outLaw_recordReplies` with a further readout of the
  challenger's coins and logs.
- `AdaptiveIAlg.toOuterMeasure_transcriptIn_eq_eventOut`: against every challenger, the event at
  the readout of `transcriptLawIn` is the probability that `eventOut` outputs `true`.
- `AdaptiveIAlg.advantage_transcriptIn_le_of_hiddenReadsPair`: for a hidden-reads pair, the
  event probabilities averaged over the uniform oracle differ by at most
  `2 √(n + Q') √((width n + qC Q) ∑ j, ε j)` with `n = budget + post + q`.
- `QueryBoundedAdversary.advantage_transcriptLawIn_le_of_hiddenReadsPair`: the same for a
  `t`-query adversary with `width q ≤ s` at every auxiliary value, with `n` and `width n`
  replaced by `t + s`.
- `RingSignature.gameAdvantage_runLawIn_le_of_hiddenReadsPair`: the game form over start draws
  `k`, at the average over `k` of `∑ j, ε k j` (Jensen).
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

/-! ### Readouts of a composition -/

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O) (C : Challenger X Y Req Resp)

/-- **The final oracle in force in a readout**: the base oracle `H` reprogrammed by the final
assignments may be replaced by the pure game's oracle at the challenger's coins and logs. -/
theorem outLaw_composeBothOut_postAss {O' : Type} (G : B.CW C → (X → Y) → O') (H : X → Y) :
    (B.composeBothOut C fun v => G v (H.reprogram (B.postAss C v.chal))).outLaw H =
      (B.composeBothOut C fun v =>
        G v (C.toPureEnv.oracle (H, v.chal.coins) v.chal.logs)).outLaw H := by
  refine B.outLaw_composeBothOut_congr_emb C H fun c r => ?_
  rw [B.reprogram_postAss_emb C H c r]
  rfl

/-- **An event of a readout is the probability of its truth value `true`.** -/
theorem toOuterMeasure_outLaw_eq_some_true {O' : Type} (f : B.CW C → O') (P : O' → Prop)
    [DecidablePred P] (H : X → Y) :
    ((B.composeBothOut C f).outLaw H).toOuterMeasure {x | ∃ p ∈ x, P p} =
      (B.composeBothOut C fun v => decide (P (f v))).outLaw H (some true) := by
  rw [show (B.composeBothOut C fun v => decide (P (f v))).outLaw H = _ from
    B.outLaw_composeBothOut_map C f (fun p => decide (P p)) H,
    ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  congr 1
  ext x
  rcases x with _ | p <;> simp

end KindAlg

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O)

variable [Nonempty X] [AddGroup Y] [Nonempty Y]

/-- **The output law of the adversary with its output mapped** (`mapOut`,
`GordieHowe/Model/RingSignature/Transcript.lean`) is `A`'s composition read as `g` of `A`'s
output. -/
theorem outLaw_compose_mapOut_output {O' : Type} (g : O → O') (C : Challenger X Y Req Resp)
    (H : X → Y) :
    ((A.mapOut g).compose C).outLaw H =
      (A.toKindAlg.composeBothOut C fun v => g (A.output C v)).outLaw H :=
  (A.outLaw_compose_mapOut g C H).trans (A.toKindAlg.outLaw_composeBothOut_map C
    (fun v => (A.output C v, A.history C v)) (fun p => g p.1) H).symm

/-! ### The recorded replies with the coins and the logs -/

variable [Inhabited Req]

/-- **The law of the recorded replies, with a readout of the coins and the logs**: as
`outLaw_recordReplies`, with `f` of the challenger's coins and logs read on both sides. -/
theorem outLaw_recordReplies_with {Z : Type} (C : Challenger X Y Req Resp) (H : X → Y)
    (f : C.Coins → LogReg Req A.slots → Z) :
    (A.recordReplies.toKindAlg.composeBothOut C fun v =>
        ((((A.recordReplies.output C v).1, A.recordReplies.history C v),
          (A.recordReplies.output C v).2.take C.Q), f v.chal.coins v.chal.logs)).outLaw H =
      (A.toKindAlg.composeBothOut C fun v =>
        (((A.output C v, A.history C v), (A.history C v).map HistoryEntry.toPair),
          f v.chal.coins v.chal.logs)).outLaw H := by
  classical
  refine PMF.ext_of_apply_some fun o => ?_
  rw [KindAlg.outLaw_composeBothOut_some, KindAlg.outLaw_composeBothOut_some]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  have hite : ∀ (p : Prop) [Decidable p] (x : ℝ), (if p then x else 0) = (if p then 1 else 0) * x :=
    fun p _ x => by split_ifs <;> simp
  rw [Finset.sum_congr rfl fun r' _ => hite _ _, Finset.sum_congr rfl fun r _ => hite _ _]
  refine (A.sum_diag_mgRun_absorb (SideRelay.idRelay Req Resp) C.toPureEnv (H, c) C.toPureEnv (H, c)
    (SideRelay.relays_idRelay _ _ _) SideRelay.idRelay_route_injective _).trans ?_
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 2
  obtain ⟨⟨⟨w, k⟩, rq, rs, lg⟩, qs⟩ := r
  have hst : A.storeBelow (SideRelay.idRelay Req Resp) C.toPureEnv (H, c) (A.slots + A.post) lg =
      fun j => C.toPureEnv.answer (H, c) lg j := by
    funext j
    simp only [storeBelow, mainAns, SideRelay.logs_idRelay]
    simp only [show (j : ℕ) < A.slots + A.post by omega, ↓reduceIte]
  have e1 : A.recordReplies.output C (A.recordReplies.toKindAlg.emb C H c A.slots
      (A.placeClean (SideRelay.idRelay Req Resp) C.toPureEnv (H, c) (A.slots + A.post)
        ((((w, k), rq, rs, lg), qs)))).1 =
      (A.out w, records lg fun j => C.toPureEnv.answer (H, c) lg j) := by
    show (A.out w, records lg (A.storeBelow (SideRelay.idRelay Req Resp) C.toPureEnv (H, c)
      (A.slots + A.post) lg)) = _
    rw [hst]
  have e2 : A.recordReplies.history C (A.recordReplies.toKindAlg.emb C H c A.slots
      (A.placeClean (SideRelay.idRelay Req Resp) C.toPureEnv (H, c) (A.slots + A.post)
        ((((w, k), rq, rs, lg), qs)))).1 = (C.stateAfter H c (requests lg)).hist := by
    refine (KindAlg.stateAt_emb_history A.recordReplies.toKindAlg C H c
      (A.placeClean (SideRelay.idRelay Req Resp) C.toPureEnv (H, c) (A.slots + A.post)
        ((((w, k), rq, rs, lg), qs)))).trans ?_
    show (C.stateAfter H c (requests ((SideRelay.idRelay Req Resp).logs lg))).hist = _
    rw [SideRelay.logs_idRelay]
  have e3 : A.history C (A.toKindAlg.emb C H c A.slots ((((w, k), rq, rs, lg), qs))).1 =
      (C.stateAfter H c (requests lg)).hist :=
    KindAlg.stateAt_emb_history A.toKindAlg C H c ((((w, k), rq, rs, lg), qs))
  have e4 : (records lg fun j => C.toPureEnv.answer (H, c) lg j).take C.Q =
      (C.stateAfter H c (requests lg)).hist.map HistoryEntry.toPair :=
    (C.map_toPair_stateAfter_hist H c lg A.slots).symm
  have e5 : f (A.recordReplies.toKindAlg.emb C H c A.slots
      (A.placeClean (SideRelay.idRelay Req Resp) C.toPureEnv (H, c) (A.slots + A.post)
        ((((w, k), rq, rs, lg), qs)))).1.chal.coins
      (A.recordReplies.toKindAlg.emb C H c A.slots
      (A.placeClean (SideRelay.idRelay Req Resp) C.toPureEnv (H, c) (A.slots + A.post)
        ((((w, k), rq, rs, lg), qs)))).1.chal.logs = f c lg := by
    show f c ((SideRelay.idRelay Req Resp).logs lg) = f c lg
    rw [SideRelay.logs_idRelay]
  have e6 : f (A.toKindAlg.emb C H c A.slots ((((w, k), rq, rs, lg), qs))).1.chal.coins
      (A.toKindAlg.emb C H c A.slots ((((w, k), rq, rs, lg), qs))).1.chal.logs = f c lg := rfl
  have gen : ∀ (oo : O × List (Req × Option Resp)) (h₁ h₂ : List (HistoryEntry Req Resp))
      (z₁ z₂ : Z),
      oo = (A.out w, records lg fun j => C.toPureEnv.answer (H, c) lg j) →
      h₁ = (C.stateAfter H c (requests lg)).hist → h₂ = (C.stateAfter H c (requests lg)).hist →
      z₁ = f c lg → z₂ = f c lg →
      (((oo.1, h₁), oo.2.take C.Q), z₁) = (((A.out w, h₂), h₂.map HistoryEntry.toPair), z₂) := by
    rintro oo h₁ h₂ z₁ z₂ rfl rfl rfl rfl rfl
    rw [e4]
  have key := gen _ _ _ _ _ e1 e2 e3 e5 e6
  exact congrArg (· = o) key

/-! ### The adversary deciding an event at the final oracle in force -/

variable {R : Type} (Pv : O → GordieHowe.OracleProg X Y R) (q : ℕ) (hP : ∀ o, (Pv o).QueriesLE q)

open Classical in
/-- **The adversary deciding an event at the final oracle in force** (module docstring): `A`
recording its replies, followed by the program `Pv` on its output, with output the truth value
of `Ev o rs r` at `A`'s output `o`, the requests `rs` of the first `Q` recorded pairs and the
program's result `r`.

Running time: that of `thenProgOut` (its paragraph) on `A` recording its replies, plus one decision
of `Ev`; polynomial when `A`, `Pv` and the decision of `Ev` are. This running time is argued here,
not proved in Lean. -/
noncomputable def eventOut (Q : ℕ) (Ev : O → List Req → R → Prop) :=
  (A.recordReplies.thenProgOut (fun p => Pv p.1) q fun p => hP p.1).mapOut fun p =>
    decide (Ev p.1.1 ((p.1.2.take Q).map Prod.fst) p.2)

omit [Nonempty Y] in
@[simp] theorem eventOut_width (Q : ℕ) (Ev : O → List Req → R → Prop) :
    (A.eventOut Pv q hP Q Ev).width = A.width := rfl

omit [Nonempty Y] in
@[simp] theorem eventOut_post (Q : ℕ) (Ev : O → List Req → R → Prop) :
    (A.eventOut Pv q hP Q Ev).post = A.post + q := rfl

omit [Nonempty Y] in
@[simp] theorem eventOut_budget (Q : ℕ) (Ev : O → List Req → R → Prop) :
    (A.eventOut Pv q hP Q Ev).budget = A.budget := rfl

open Classical in
/-- **An event at the final oracle in force is an output of `eventOut`** (main identity): against
every challenger `C`, also one that reprograms, at every oracle `H`, the probability that the
output `o`, the answered requests `rs` and the final oracle in force `G` (the readout of
`QueryBoundedAdversary.transcriptLawIn`) satisfy `Ev o rs ((Pv o).run G)` is the probability
that `A.eventOut Pv q hP C.Q Ev` outputs `true`. -/
theorem toOuterMeasure_transcriptIn_eq_eventOut (C : Challenger X Y Req Resp) (H : X → Y)
    (Q : ℕ) (hQ : C.Q = Q) (Ev : O → List Req → R → Prop) :
    ((A.toKindAlg.composeBothOut C fun v => (A.output C v, (requests v.chal.logs).take C.Q,
        C.toPureEnv.oracle (H, v.chal.coins) v.chal.logs)).outLaw H).toOuterMeasure
        {x | ∃ p ∈ x, Ev p.1 p.2.1 ((Pv p.1).run p.2.2)} =
      ((A.eventOut Pv q hP Q Ev).compose C).outLaw H (some true) := by
  subst hQ
  set D := A.recordReplies.thenProgOut (fun p => Pv p.1) q fun p => hP p.1
  set φ : (O × List (Req × Option Resp)) × R → Bool :=
    fun p => decide (Ev p.1.1 ((p.1.2.take C.Q).map Prod.fst) p.2)
  set ψ : ((O × List (HistoryEntry Req Resp)) × List (Req × Option Resp)) × (X → Y) → Bool :=
    fun z => decide (Ev z.1.1.1 (z.1.2.map Prod.fst) ((Pv z.1.1.1).run z.2))
  have h1 : ((A.eventOut Pv q hP C.Q Ev).compose C).outLaw H =
      (A.recordReplies.toKindAlg.composeBothOut C fun v =>
        φ (A.recordReplies.output C v, (Pv (A.recordReplies.output C v).1).run
          (H.reprogram (A.recordReplies.toKindAlg.postAss C v.chal)))).outLaw H := by
    rw [eventOut, outLaw_compose_mapOut_output]
    exact A.recordReplies.outLaw_composeBothOut_thenProgOut (fun p => Pv p.1) q (fun p => hP p.1) C
      (fun oo _ => φ oo) H
  have h2 := A.recordReplies.toKindAlg.outLaw_composeBothOut_postAss C
    (fun v G => φ (A.recordReplies.output C v, (Pv (A.recordReplies.output C v).1).run G)) H
  have h3 : (A.recordReplies.toKindAlg.composeBothOut C fun v =>
      φ (A.recordReplies.output C v, (Pv (A.recordReplies.output C v).1).run
        (C.toPureEnv.oracle (H, v.chal.coins) v.chal.logs))).outLaw H =
      (A.toKindAlg.composeBothOut C fun v => ψ
        (((A.output C v, A.history C v), (A.history C v).map HistoryEntry.toPair),
          C.toPureEnv.oracle (H, v.chal.coins) v.chal.logs)).outLaw H := by
    refine (A.recordReplies.toKindAlg.outLaw_composeBothOut_map C (fun v =>
      ((((A.recordReplies.output C v).1, A.recordReplies.history C v),
        (A.recordReplies.output C v).2.take C.Q),
        C.toPureEnv.oracle (H, v.chal.coins) v.chal.logs)) ψ H).trans ?_
    refine (congrArg (PMF.map (Option.map ψ))
      (A.outLaw_recordReplies_with C H fun c lg => C.toPureEnv.oracle (H, c) lg)).trans ?_
    exact (A.toKindAlg.outLaw_composeBothOut_map C (fun v =>
      (((A.output C v, A.history C v), (A.history C v).map HistoryEntry.toPair),
        C.toPureEnv.oracle (H, v.chal.coins) v.chal.logs)) ψ H).symm
  rw [h1, h2, h3, KindAlg.toOuterMeasure_outLaw_eq_some_true]
  refine congrArg (fun f => (A.toKindAlg.composeBothOut C f).outLaw H (some true))
    (funext fun v => ?_)
  have hr : ((A.history C v).map HistoryEntry.toPair).map Prod.fst =
      (requests v.chal.logs).take C.Q := by
    rw [List.map_map]
    exact A.map_request_history C v
  simp only [ψ, hr]

/-! ### The hidden-reads bound for events at the final oracle in force -/

omit [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [AddGroup Y] [Inhabited Req] in
/-- **The bounds of a hidden-point condition are nonnegative.** -/
theorem _root_.GordieHowe.Quantum.Challenger.HiddenReadsPair.eps_nonneg [Nonempty Req]
    {C C' : Challenger X Y Req Resp} {qC : ℕ} (P : C.HiddenReadsPair C' qC) (ε : Fin C.Q → ℝ)
    (hfind : ∀ (j : Fin C.Q) H ω₀ c rs₀ req, rs₀.length = (j : ℕ) → ∀ g : Option Resp → X,
      (P.ζ.toOuterMeasure {a | g (C.respAt (P.enc (ω₀, Function.update c j a)) H rs₀ req) ∈
        P.hidden H ω₀ (Function.update c j a) rs₀ req}).toReal ≤ ε j)
    (j : Fin C.Q) : 0 ≤ ε j := by
  obtain ⟨ω₀, -⟩ := P.ν.support_nonempty
  obtain ⟨c₀, -⟩ := P.ζ.support_nonempty
  exact ENNReal.toReal_nonneg.trans (hfind j (fun _ => Classical.arbitrary Y) ω₀ (fun _ => c₀)
    (List.replicate j (Classical.arbitrary Req)) (Classical.arbitrary Req)
    List.length_replicate (fun _ => Classical.arbitrary X))

include hP in
open Classical in
/-- **Hidden points with the challenger's reads, for an event at the final oracle in force**:
for a `HiddenReadsPair` of challengers and `ε j` bounding the probability, over the fresh coins
of request `j`, that a guess from its response is a hidden point of it, the probabilities of
`Ev o rs ((Pv o).run G)` at the output `o`, the answered requests `rs` and the final oracle in
force `G`, averaged over the uniform oracle, differ by at most
`2 √(n + Q') √((width n + qC Q) ∑ j, ε j)` with `n = budget + post + q` and `Q' = 0` if
`qC = 0`, `Q` otherwise (`advantage_outLaw_le_of_hiddenReadsPair` at the output `true` of
`eventOut`). -/
theorem advantage_transcriptIn_le_of_hiddenReadsPair [Nonempty Req]
    {C C' : Challenger X Y Req Resp} {qC : ℕ} (P : C.HiddenReadsPair C' qC) (ε : Fin C.Q → ℝ)
    (hfind : ∀ (j : Fin C.Q) H ω₀ c rs₀ req, rs₀.length = (j : ℕ) → ∀ g : Option Resp → X,
      (P.ζ.toOuterMeasure {a | g (C.respAt (P.enc (ω₀, Function.update c j a)) H rs₀ req) ∈
        P.hidden H ω₀ (Function.update c j a) rs₀ req}).toReal ≤ ε j)
    (Ev : O → List Req → R → Prop) :
    GordieHowe.advantage
      (∑ H, (PMF.uniformOfFintype (X → Y) H).toReal *
        (((A.toKindAlg.composeBothOut C fun v => (A.output C v, (requests v.chal.logs).take C.Q,
          C.toPureEnv.oracle (H, v.chal.coins) v.chal.logs)).outLaw H).toOuterMeasure
          {x | ∃ p ∈ x, Ev p.1 p.2.1 ((Pv p.1).run p.2.2)}).toReal)
      (∑ H, (PMF.uniformOfFintype (X → Y) H).toReal *
        (((A.toKindAlg.composeBothOut C' fun v => (A.output C' v,
          (requests v.chal.logs).take C'.Q,
          C'.toPureEnv.oracle (H, v.chal.coins) v.chal.logs)).outLaw H).toOuterMeasure
          {x | ∃ p ∈ x, Ev p.1 p.2.1 ((Pv p.1).run p.2.2)}).toReal) ≤
        2 * √((A.budget + (A.post + q) : ℕ) + if qC = 0 then 0 else C.Q) *
          √((A.width * (A.budget + (A.post + q) : ℕ) + qC * C.Q) * ∑ j, ε j) := by
  simp only [A.toOuterMeasure_transcriptIn_eq_eventOut Pv q hP C _ C.Q rfl,
    A.toOuterMeasure_transcriptIn_eq_eventOut Pv q hP C' _ C.Q P.Q_eq]
  exact (A.eventOut Pv q hP C.Q Ev).advantage_outLaw_le_of_hiddenReadsPair P ε hfind true

end AdaptiveIAlg

/-! ### Query-bounded adversaries -/

namespace QueryBoundedAdversary

variable {X Y Req Resp O R : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Inhabited Req] [Nonempty X]
  [AddGroup Y] [Nonempty Y] {t : ℕ}

omit [Inhabited Req] in
/-- **An event of `transcriptLawIn`, averaged over the uniform oracle**, is the average over the
auxiliary input of the averaged events of the compositions. -/
theorem sum_toReal_transcriptLawIn (A : QueryBoundedAdversary X Y Req Resp O t)
    (C : Challenger X Y Req Resp) (S : Set (Option (O × List Req × (X → Y)))) :
    ∑ H, (PMF.uniformOfFintype (X → Y) H).toReal *
        ((A.transcriptLawIn C H).toOuterMeasure S).toReal =
      (∑' a, A.aux a * ∑' H, PMF.uniformOfFintype (X → Y) H *
        (((A.alg a).toKindAlg.composeBothOut C fun v => ((A.alg a).output C v,
          (requests v.chal.logs).take C.Q,
          C.toPureEnv.oracle (H, v.chal.coins) v.chal.logs)).outLaw H).toOuterMeasure
          S).toReal := by
  refine (PMF.toReal_tsum_mul_fintype _ (p := fun H => (A.transcriptLawIn C H).toOuterMeasure S)
    fun _ => PMF.toOuterMeasure_apply_le_one _ _).symm.trans ?_
  congr 1
  simp only [transcriptLawIn, PMF.toOuterMeasure_bind_apply, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => tsum_congr fun H => ?_
  ring

open Classical in
/-- **Hidden points with the challenger's reads, for an event at the final oracle in force, for
`t`-query adversaries** (`AdaptiveIAlg.advantage_transcriptIn_le_of_hiddenReadsPair` at each
auxiliary value): when the program `Pv` makes at most `q` queries and `width q ≤ s` at every
auxiliary value, the probabilities under `transcriptLawIn` of `Ev o rs ((Pv o).run G)`, averaged
over the uniform oracle, differ by at most `2 √(t + s + Q') √((t + s + qC Q) ∑ j, ε j)`. -/
theorem advantage_transcriptLawIn_le_of_hiddenReadsPair [Nonempty Req]
    (A : QueryBoundedAdversary X Y Req Resp O t) (Pv : O → GordieHowe.OracleProg X Y R)
    (q s : ℕ) (hP : ∀ o, (Pv o).QueriesLE q) (hs : ∀ a, (A.alg a).width * q ≤ s)
    {C C' : Challenger X Y Req Resp} {qC : ℕ} (P : C.HiddenReadsPair C' qC) (ε : Fin C.Q → ℝ)
    (hfind : ∀ (j : Fin C.Q) H ω₀ c rs₀ req, rs₀.length = (j : ℕ) → ∀ g : Option Resp → X,
      (P.ζ.toOuterMeasure {a | g (C.respAt (P.enc (ω₀, Function.update c j a)) H rs₀ req) ∈
        P.hidden H ω₀ (Function.update c j a) rs₀ req}).toReal ≤ ε j)
    (Ev : O → List Req → R → Prop) :
    GordieHowe.advantage
      (∑ H, (PMF.uniformOfFintype (X → Y) H).toReal * ((A.transcriptLawIn C H).toOuterMeasure
        {x | ∃ p ∈ x, Ev p.1 p.2.1 ((Pv p.1).run p.2.2)}).toReal)
      (∑ H, (PMF.uniformOfFintype (X → Y) H).toReal * ((A.transcriptLawIn C' H).toOuterMeasure
        {x | ∃ p ∈ x, Ev p.1 p.2.1 ((Pv p.1).run p.2.2)}).toReal) ≤
      2 * √(t + s + (if qC = 0 then 0 else C.Q : ℝ)) * √((t + s + qC * C.Q : ℝ) * ∑ j, ε j) := by
  have hε0 : 0 ≤ ∑ j, ε j := Finset.sum_nonneg fun j _ => P.eps_nonneg ε hfind j
  rw [GordieHowe.advantage, sum_toReal_transcriptLawIn, sum_toReal_transcriptLawIn]
  refine PMF.abs_toReal_tsum_mul_sub_le _
    (fun _ => PMF.tsum_mul_le_one _ fun _ => PMF.toOuterMeasure_apply_le_one _ _)
    (fun _ => PMF.tsum_mul_le_one _ fun _ => PMF.toOuterMeasure_apply_le_one _ _) fun a => ?_
  rw [PMF.toReal_tsum_mul_fintype _ fun _ => PMF.toOuterMeasure_apply_le_one _ _,
    PMF.toReal_tsum_mul_fintype _ fun _ => PMF.toOuterMeasure_apply_le_one _ _]
  have h := (A.alg a).advantage_transcriptIn_le_of_hiddenReadsPair Pv q hP P ε hfind Ev
  rw [GordieHowe.advantage] at h
  refine h.trans ?_
  -- the derived adversary's queries are at most `t + s`
  have hwn : (A.alg a).width * ((A.alg a).budget + ((A.alg a).post + q)) ≤ t + s := by
    have h1 := A.queries_le a
    have h2 := hs a
    rw [show (A.alg a).budget + ((A.alg a).post + q) =
      ((A.alg a).budget + (A.alg a).post) + q by omega, Nat.mul_add]
    omega
  have hn : (A.alg a).budget + ((A.alg a).post + q) ≤
      (A.alg a).width * ((A.alg a).budget + ((A.alg a).post + q)) :=
    Nat.le_mul_of_pos_left _ (A.alg a).width_pos
  have hwn' : ((A.alg a).width : ℝ) * (((A.alg a).budget + ((A.alg a).post + q) : ℕ) : ℝ) ≤
      t + s := by exact_mod_cast hwn
  have hn' : (((A.alg a).budget + ((A.alg a).post + q) : ℕ) : ℝ) ≤ t + s := by
    exact_mod_cast hn.trans hwn
  have hQ0 : (0 : ℝ) ≤ if qC = 0 then 0 else (C.Q : ℝ) := by split_ifs <;> positivity
  have hif : ((if qC = 0 then 0 else C.Q : ℕ) : ℝ) = if qC = 0 then 0 else (C.Q : ℝ) := by
    split_ifs <;> simp
  have e1 : √((((A.alg a).budget + ((A.alg a).post + q) : ℕ) : ℝ) +
      ((if qC = 0 then 0 else C.Q : ℕ) : ℝ)) ≤ √(t + s + if qC = 0 then 0 else (C.Q : ℝ)) :=
    Real.sqrt_le_sqrt (by rw [hif]; linarith)
  have e2 : √((((A.alg a).width : ℝ) * (((A.alg a).budget + ((A.alg a).post + q) : ℕ) : ℝ) +
      qC * C.Q) * ∑ j, ε j) ≤ √((t + s + qC * C.Q) * ∑ j, ε j) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (by linarith) hε0)
  exact mul_le_mul (mul_le_mul_of_nonneg_left e1 (by norm_num)) e2 (Real.sqrt_nonneg _)
    (by positivity)

end QueryBoundedAdversary

end GordieHowe.Quantum

/-! ### The game form over start draws -/

namespace GordieHowe.RingSignature

open Quantum

variable {X Y Req Resp O R : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Inhabited Req] [Nonempty X]
  [AddGroup Y] [Nonempty Y] {t : ℕ}

open Classical in
/-- **Hidden points with the challenger's reads in a game's run, for events at the final oracle
in force**: with start draws `k`, for every `k` a `HiddenReadsPair` of challengers `C k` and
`C' k` with `Q` requests and bounds `ε k j`, an adversary `A k` independent of the oracle, and a
program `Pv k o` with at most `q` queries with `width q ≤ s` at every auxiliary value, the
probabilities of `Ev k o rs ((Pv k o).run G)` at the output `o`, the answered requests `rs` and
the final oracle in force `G` differ by at most `2 √(t + s + Q') √((t + s + qC Q) ε̄)` at the
average `ε̄ = ∑ k, ∑ j, ε k j / |K|`. -/
theorem gameAdvantage_runLawIn_le_of_hiddenReadsPair {K : Type} [Fintype K] [Nonempty K]
    [Nonempty Req] (A : K → QueryBoundedAdversary X Y Req Resp O t)
    (Pv : K → O → GordieHowe.OracleProg X Y R) (q s : ℕ) (hP : ∀ k o, (Pv k o).QueriesLE q)
    (hs : ∀ k a, ((A k).alg a).width * q ≤ s) {C C' : K → Challenger X Y Req Resp} {qC Q : ℕ}
    (P : ∀ k, (C k).HiddenReadsPair (C' k) qC) (hQ : ∀ k, (C k).Q = Q)
    (ε : ∀ k, Fin (C k).Q → ℝ)
    (hfind : ∀ k (j : Fin (C k).Q) H ω₀ c rs₀ req, rs₀.length = (j : ℕ) →
      ∀ g : Option Resp → X, ((P k).ζ.toOuterMeasure
        {a | g ((C k).respAt ((P k).enc (ω₀, Function.update c j a)) H rs₀ req) ∈
          (P k).hidden H ω₀ (Function.update c j a) rs₀ req}).toReal ≤ ε k j)
    (Ev : K → O → List Req → R → Prop) :
    gameAdvantage (runLawIn (fun k _ => A k) C) (runLawIn (fun k _ => A k) C')
        {x | ∃ p ∈ x.2.2, Ev x.1 p.1 p.2.1 ((Pv x.1 p.1).run p.2.2)} ≤
      2 * √(t + s + (if qC = 0 then 0 else Q : ℝ)) *
        √((t + s + qC * Q : ℝ) * ∑ k, (Fintype.card K : ℝ)⁻¹ * ∑ j, ε k j) := by
  set E : Set (K × (X → Y) × Option (O × List Req × (X → Y))) :=
    {x | ∃ p ∈ x.2.2, Ev x.1 p.1 p.2.1 ((Pv x.1 p.1).run p.2.2)}
  set a₀ : ℝ := t + s + (if qC = 0 then 0 else Q : ℝ)
  set W : ℝ := t + s + qC * Q
  have hW0 : 0 ≤ W := by positivity
  set e : K → ℝ := fun k => ∑ j, ε k j
  have he : ∀ k, 0 ≤ e k := fun k =>
    Finset.sum_nonneg fun j _ => (P k).eps_nonneg (ε k) (hfind k) j
  set u : ℝ := (Fintype.card K : ℝ)⁻¹ with hu
  have hu0 : 0 ≤ u := by positivity
  have hsum_u : ∑ _k : K, u = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hu,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)]
  set inner : (K → Challenger X Y Req Resp) → K → ℝ≥0∞ := fun C k =>
    ∑' H, PMF.uniformOfFintype (X → Y) H *
      ((A k).transcriptLawIn (C k) H).toOuterMeasure {o | (k, H, o) ∈ E} with hinner
  have hle : ∀ C k, inner C k ≤ 1 := fun C k =>
    PMF.tsum_mul_le_one _ fun _ => PMF.toOuterMeasure_apply_le_one _ _
  -- the bound at each start draw
  have hk : ∀ k, |(inner C k).toReal - (inner C' k).toReal| ≤ 2 * √a₀ * √(W * e k) := by
    intro k
    have h := (A k).advantage_transcriptLawIn_le_of_hiddenReadsPair (Pv k) q s (hP k) (hs k)
      (P k) (ε k) (hfind k) (Ev k)
    rw [GordieHowe.advantage] at h
    have hQk : ((C k).Q : ℝ) = Q := by rw [hQ k]
    rw [hQk] at h
    simp only [hinner]
    rw [PMF.toReal_tsum_mul_fintype _ fun _ => PMF.toOuterMeasure_apply_le_one _ _,
      PMF.toReal_tsum_mul_fintype _ fun _ => PMF.toOuterMeasure_apply_le_one _ _]
    exact h
  rw [gameAdvantage]
  change |((runLawIn _ C).toOuterMeasure E).toReal - ((runLawIn _ C').toOuterMeasure E).toReal|
    ≤ _
  rw [toOuterMeasure_runLawIn, toOuterMeasure_runLawIn]
  change |(∑' k, PMF.uniformOfFintype K k * inner C k).toReal -
    (∑' k, PMF.uniformOfFintype K k * inner C' k).toReal| ≤ _
  rw [PMF.toReal_tsum_mul_fintype _ (hle C), PMF.toReal_tsum_mul_fintype _ (hle C'),
    ← Finset.sum_sub_distrib]
  have hpu : ∀ k, (PMF.uniformOfFintype K k).toReal = u := fun k => by
    rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp only [hpu, ← mul_sub]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ k : K, |u * ((inner C k).toReal - (inner C' k).toReal)| ≤
      2 * √a₀ * (u * √(W * e k)) := fun k => by
    rw [abs_mul, abs_of_nonneg hu0]
    calc u * |(inner C k).toReal - (inner C' k).toReal| ≤ u * (2 * √a₀ * √(W * e k)) :=
          mul_le_mul_of_nonneg_left (hk k) hu0
      _ = 2 * √a₀ * (u * √(W * e k)) := by ring
  refine (Finset.sum_le_sum fun k _ => hterm k).trans ?_
  rw [← Finset.mul_sum]
  -- Jensen: the square root is concave
  have hjensen : ∑ k : K, u * √(W * e k) ≤ √(W * ∑ k : K, u * e k) := by
    have h := (Real.strictConcaveOn_sqrt.concaveOn).le_map_sum (t := Finset.univ)
      (w := fun _ : K => u) (p := fun k => W * e k) (fun _ _ => hu0) hsum_u
      (fun k _ => Set.mem_Ici.2 (mul_nonneg hW0 (he k)))
    simp only [smul_eq_mul] at h
    calc ∑ k : K, u * √(W * e k) ≤ √(∑ k : K, u * (W * e k)) := h
      _ = √(W * ∑ k : K, u * e k) := by
        rw [Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun k _ => by ring
  exact mul_le_mul_of_nonneg_left hjensen (by positivity)

end GordieHowe.RingSignature
