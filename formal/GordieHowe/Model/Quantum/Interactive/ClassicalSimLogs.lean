-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.ClassicalSim
public import GordieHowe.Model.Quantum.Interactive.Absorb

@[expose] public section

/-!
# The classical simulation of interactive adversaries with the request logs and the coins

`GordieHowe/Model/Quantum/Interactive/ClassicalSim.lean` identifies the output law of the
composition of an interactive quantum adversary with a classical challenger with the output law
of the adversary's classical strategy (`KindAlg.classicalSim`). This file identifies the joint
law of the adversary's output, the challenger's request logs and its coins: at every oracle `H`,
an event of these three registers of the composition has, at each coin `c`, the probability of
the classical continuation from the empty history at `c` (`Interaction.cont`) that the strategy
outputs `some o` with the event holding at `o`, the moves of the classical history read as logs
(`Distinguisher.movesOf`), and `c`.

- `KindAlg.dilateIn`: the dilated distinguisher accepting when the halting flag is clear and the
  output lies in a set `T` (`KindAlg.dilate` for `T = {o}`).
- `KindAlg.mgAcceptOn`: the probability that the mixed game outputs in `T` with logs in `L`;
  `mgAcceptOn_deph`: the same with and without the measurement of the requests.
- `KindAlg.acceptProbOnAt_dilateIn`: the pure game of `dilateIn T` accepts with logs in `L` with
  the probability `mgAcceptOn T L`.
- `KindAlg.mgAcceptOn_eq_cont`: **one coin**: `mgAcceptOn T L` at the tape `(H, c)` is the
  probability that the classical continuation at `c` has moves in `L` and output in `T`.
- `KindAlg.toOuterMeasure_outLaw_composeBothOut_logs_coins`: **the joint law of the output, the
  logs and the coins** of the composition, as the coin average of the classical continuations;
  `AdaptiveIAlg.toOuterMeasure_outLaw_composeBothOut_logs_coins` for `toKindAlg`.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [AddGroup Y]
  {ksA : KindShape X Y Req Resp} (A : KindAlg ksA O)

/-- **The dilated distinguisher accepting on a set of outputs** `T`: `KindAlg.dilate` with the
accepting set the basis states whose halting flag is clear and whose output lies in `T`. -/
noncomputable def dilateIn (T : Set O) : Distinguisher A.DW X Y Req Resp A.width A.slots where
  kind w := A.kind w.1 || w.2.1
  init := Quantum.relabel A.relD A.dInitVec
  norm_init := by rw [LinearIsometryEquiv.norm_map, A.norm_dInitVec]
  step k := A.uStepD k
  accept := {x | x.1.1.2.1 = false ∧ A.out x.1.1.1 ∈ T}

theorem classicalSim_eq_dilateIn (T : Set O) :
    A.classicalSim = ((A.dilateIn T).classical A.postOp).mapOut A.dilOut :=
  rfl

theorem acceptEvent_dilateIn (T : Set O) (L : Set (LogReg Req A.slots)) :
    (A.dilateIn T).acceptEvent L =
      Prod.map id A.dilOut ⁻¹' {p : Interaction.Hist (Option Req) (Option Resp × (X → Y)) ×
        Option O | Distinguisher.movesOf p.1 ∈ L ∧ ∃ o ∈ T, p.2 = some o} := by
  ext p
  simp only [Distinguisher.acceptEvent, dilateIn, Set.mem_ofPred_eq, Set.mem_preimage, Prod.map,
    dilOut]
  split_ifs with h <;> simp [h]

variable {Ω St : Type} {Q : ℕ} [OracleState St X Y] (E : Env Ω Req Resp X Y Q St)

open Classical in
/-- The probability that the mixed game outputs in `T` with logs in `L`. -/
noncomputable def mgAcceptOn (T : Set O) (L : Set (LogReg Req A.slots)) (ω : Ω) (deph : Bool) :
    ℝ :=
  ∑ r : A.G, if A.out r.1.1 ∈ T ∧ (splitLogs r).2 ∈ L then (A.mgRun E ω deph r r).re else 0

/-- **Deferred measurement for the logged acceptance probability**: `mgAccept_deph` with the
logs restricted to `L`. -/
theorem mgAcceptOn_deph (T : Set O) (L : Set (LogReg Req A.slots)) (ω : Ω) :
    A.mgAcceptOn E T L ω true = A.mgAcceptOn E T L ω false := by
  simp only [mgAcceptOn, A.mgRun_deph E ω, dephase_apply_self]

/-- **The pure game of `dilateIn T` accepts with logs in `L` with the probability of the mixed
game** outputting in `T` with logs in `L` (`acceptProbAt_dilate`, without the measurement of the
requests). -/
theorem acceptProbOnAt_dilateIn (T : Set O) (L : Set (LogReg Req A.slots)) (ω : Ω) :
    (A.dilateIn T).acceptProbOnAt E A.postOp L ω = A.mgAcceptOn E T L ω false := by
  classical
  rcases isEmpty_or_nonempty O with hO | ⟨⟨o⟩⟩
  · have : IsEmpty A.W := ⟨fun w => hO.elim (A.out w)⟩
    simp [Distinguisher.acceptProbOnAt, mgAcceptOn, prob, EuclideanSpace.norm_eq]
  have hspec := A.gameMixed.hybrid_spec (fun k => A.evPermB E ω k) () A.uG
    (fun k φ hφ => A.uStepD_logControlled k hφ) (A.slots + A.post)
  have hfin : (A.dilateIn T).final E A.postOp ω = Quantum.relabel A.relG.symm
      (hybrid A.uG (fun k => permOp (MixedAlg.liftPerm (A.evPermB E ω k)))
        (A.gameMixed.dilInit ()) (A.slots + A.post)) := by
    rw [← A.final_dilate E o ω, relabel_symm_relabel]
    exact Distinguisher.final_congr_steps _ E (A.dilate_kind o).symm (A.dilate_init o).symm
      (funext fun k => (A.dilate_step o k).symm) _ ω
  have hn : ‖hybrid A.uG (fun k => permOp (MixedAlg.liftPerm (A.evPermB E ω k)))
      (A.gameMixed.dilInit ()) (A.slots + A.post)‖ = 1 := by
    rw [norm_hybrid, A.gameMixed.norm_dilInit]
  rw [Distinguisher.acceptProbOnAt, hfin, prob_relabel]
  have hset : (A.relG.symm ⁻¹' ((A.dilateIn T).gameAccept ∩ logsIn L)) =
      {p : A.GB × A.DAnc | p.1 ∈ {gb : A.GB | (gb.2 = false ∧ A.out gb.1.1.1 ∈ T) ∧
        (splitLogs gb.1).2 ∈ L}} := by
    ext ⟨⟨g, b⟩, a⟩
    rfl
  rw [hset, ← probIn_reduceMState _ hn, MState.probIn]
  simp only [reduceMState_mat, hspec.2]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Set.indicator, Set.mem_ofPred_eq, Bool.true_eq_false, false_and,
    ite_false, zero_add, true_and]
  unfold KindAlg.mgAcceptOn
  rw [mgRun_false_eq, ← A.ffBlock_stageV E ω]
  rfl

end KindAlg

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {ksA : KindShape X Y Req Resp} (A : KindAlg ksA O)

omit [Nonempty X] in
/-- **The classical simulation at one coin, with the logs**: at the tape `(H, c)`, the mixed game
with measured requests outputs in `T` with logs in `L` with the probability that the classical
continuation of the adversary's classical strategy against the challenger at `H`, from the empty
history at the coin `c`, has moves in `L` and outputs `some o` with `o ∈ T`. -/
theorem mgAcceptOn_eq_cont (C : Challenger X Y Req Resp) (H : X → Y) (c : C.Coins) (T : Set O)
    (L : Set (LogReg Req A.slots)) :
    A.mgAcceptOn C.toPureEnv T L (H, c) true =
      ((Interaction.cont A.classicalSim (C.classicalAt H) c [] A.slots).toOuterMeasure
        {p | Distinguisher.movesOf p.1 ∈ L ∧ ∃ o ∈ T, p.2 = some o}).toReal := by
  have h := (A.dilateIn T).acceptProbOnAt_eq_cont C.toPureEnv A.postOp C.coins
    (fun c => (H, c)) L c
  rw [acceptEvent_dilateIn, ← PMF.toOuterMeasure_map_apply, ← Interaction.cont_mapOut,
    ← classicalSim_eq_dilateIn, acceptProbOnAt_dilateIn] at h
  rw [mgAcceptOn_deph]
  exact h

open Classical in
/-- **The joint law of the output, the request logs and the coins in the classical simulation**:
at every oracle `H`, the probability that the composition of the adversary with the challenger
terminates with adversary output `o`, request logs `lg` and challenger coins `c` with `S o lg c`
is the coin average, over `c`, of the probability that the classical continuation of the
adversary's classical strategy from the empty history at the coin `c` outputs `some o` with
`S o lg c` for the logs `lg` read from the moves of the classical history. -/
theorem toOuterMeasure_outLaw_composeBothOut_logs_coins (C : Challenger X Y Req Resp) (H : X → Y)
    (S : O → LogReg Req A.slots → C.Coins → Prop) :
    ((A.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, S (A.out v.adv.workspace) v.chal.logs v.chal.coins} =
      ∑' c, C.coins c * (Interaction.cont A.classicalSim (C.classicalAt H) c [] A.slots).toOuterMeasure
        {p | ∃ o, p.2 = some o ∧ S o (Distinguisher.movesOf p.1) c} := by
  rw [A.toOuterMeasure_outLaw_composeBothOut_id C H
    (fun v => S (A.out v.adv.workspace) v.chal.logs v.chal.coins)]
  have hc : ∀ c : C.Coins, (∑ r : A.G,
      if S (A.out (A.emb C H c A.slots r).1.adv.workspace) (A.emb C H c A.slots r).1.chal.logs
        (A.emb C H c A.slots r).1.chal.coins then
        (A.mgRun C.toPureEnv (H, c) true r r).re else 0) =
      ((Interaction.cont A.classicalSim (C.classicalAt H) c [] A.slots).toOuterMeasure
        {p | ∃ o, p.2 = some o ∧ S o (Distinguisher.movesOf p.1) c}).toReal := by
    intro c
    have hr : ∀ r : A.G, (if S (A.out (A.emb C H c A.slots r).1.adv.workspace)
        (A.emb C H c A.slots r).1.chal.logs (A.emb C H c A.slots r).1.chal.coins then
        (A.mgRun C.toPureEnv (H, c) true r r).re else 0) =
        ∑ lg : LogReg Req A.slots, if A.out r.1.1 ∈ {o | S o lg c} ∧
          (splitLogs r).2 ∈ ({lg} : Set (LogReg Req A.slots)) then
          (A.mgRun C.toPureEnv (H, c) true r r).re else 0 := fun r => by
      rw [Finset.sum_eq_single (splitLogs r).2 (fun lg _ hlg => ite_eq_right_iff.2 fun h => absurd h.2.symm hlg)
        (fun h => absurd (Finset.mem_univ _) h)]
      exact if_congr ⟨fun h => ⟨h, rfl⟩, fun h => h.1⟩ rfl rfl
    rw [Finset.sum_congr rfl fun r _ => hr r, Finset.sum_comm]
    have hlg : ∀ lg : LogReg Req A.slots, (∑ r : A.G,
        if A.out r.1.1 ∈ {o | S o lg c} ∧ (splitLogs r).2 ∈ ({lg} : Set _) then
          (A.mgRun C.toPureEnv (H, c) true r r).re else 0) =
        A.mgAcceptOn C.toPureEnv {o | S o lg c} {lg} (H, c) true := fun lg => by
      unfold mgAcceptOn
      exact Finset.sum_congr rfl fun r _ => by congr
    simp only [hlg, mgAcceptOn_eq_cont]
    rw [← ENNReal.toReal_sum fun lg _ => ne_top_of_le_ne_top ENNReal.one_ne_top
      (PMF.toOuterMeasure_apply_le_one _ _)]
    congr 1
    simp only [PMF.toOuterMeasure_apply]
    rw [← ENNReal.tsum_finset_sum_comm]
    refine tsum_congr fun p => ?_
    simp only [Set.indicator_apply]
    rw [Finset.sum_eq_single (Distinguisher.movesOf p.1)
      (fun lg _ hlg => ite_eq_right_iff.2 fun h => absurd h.1.symm hlg) (fun h => absurd (Finset.mem_univ _) h)]
    refine if_congr ⟨?_, ?_⟩ rfl rfl
    · rintro ⟨-, o, ho, hp⟩
      exact ⟨o, hp, ho⟩
    · rintro ⟨o, hp, ho⟩
      exact ⟨rfl, o, ho, hp⟩
  simp only [hc]
  rw [ENNReal.ofReal_sum_of_nonneg fun c _ => mul_nonneg ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg, tsum_fintype]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (PMF.apply_ne_top _ _),
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
      (PMF.toOuterMeasure_apply_le_one _ _))]

end KindAlg

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O)

/-- **`KindAlg.toOuterMeasure_outLaw_composeBothOut_logs_coins` for adversaries with run-time
kinds and a query budget**: the joint law of the output, the logs and the coins of the
composition with a challenger is the coin average of the classical continuations. -/
theorem toOuterMeasure_outLaw_composeBothOut_logs_coins (C : Challenger X Y Req Resp) (H : X → Y)
    (S : O → LogReg Req A.slots → C.Coins → Prop) :
    ((A.toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, S (A.toKindAlg.out v.adv.workspace) v.chal.logs v.chal.coins} =
      ∑' c, C.coins c * (Interaction.cont A.toKindAlg.classicalSim (C.classicalAt H) c []
        A.slots).toOuterMeasure {p | ∃ o, p.2 = some o ∧ S o (Distinguisher.movesOf p.1) c} :=
  A.toKindAlg.toOuterMeasure_outLaw_composeBothOut_logs_coins C H S

end AdaptiveIAlg

end GordieHowe.Quantum
