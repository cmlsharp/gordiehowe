-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.TestClasses
public import GordieHowe.Model.Quantum.Interactive.AdaptiveTest
public import GordieHowe.Model.Quantum.Interactive.AdaptiveTP

@[expose] public section

/-!
# The test keeps the copied output and the challenger's registers, with run-time kinds

For an adversary with run-time kinds followed by a test (`AdaptiveIAlg.withTest`), in the composition of its trace-preserving form with a challenger
(`AdaptiveIAlg.toTPKindAlg`, `KindAlg.composeBothOut`): every Kraus map after the junction keeps the
copy register and the challenger's registers (`AdaptiveIAlg.copyChal`), so the composed core
algorithm satisfies `Alg.StepsKeep` after the adversary's queries
(`AdaptiveIAlg.stepsKeep_composeBothOut_withTest`). The test's channels are trace preserving, so
the halting operators of the trace-preserving form vanish there (`KrausMap.haltOp_eq_zero`).
-/

open Finset Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

namespace GordieHowe.Quantum

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {A : AdaptiveIAlg X Y Req Resp O} (T : A.QTest) (C : Challenger X Y Req Resp)

/-- **The copy register and the challenger's registers** of a composed register of `A^Π`. -/
noncomputable def copyChal (v : (A.withTest T).toTPKindAlg.CW C) :
    A.W × ChallengerRegs X Y Req A.slots C.q C.Coins :=
  (v.adv.workspace.1.2, v.chal)

/-- **A channel on `A`'s registers, lifted to `A^Π`, keeps the copy register.** -/
theorem keeps_liftCopy {R : Type} [Fintype R]
    (K : KrausChannel R (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp)) :
    (A.liftCopy K.toKrausMap).Keeps fun p : DReg (A.W × A.W) A.width X Y Req Resp => p.1.1.2 :=
  (((KrausMap.keeps_const (K := K.toKrausMap) K.sum_conjTranspose_mul ()).tensorId_prod
    (A := A.W)).map Prod.snd).reindex
    A.copySplit.symm fun _ => rfl

/-- **A step of the test keeps the copy register** of `A^Π`. -/
theorem keeps_withTestStep {k : StepIdx A.slots (A.post + T.batches)} (hk : A.slots + A.post < k) :
    (A.withTest T |>.step k).Keeps fun p : DReg (A.W × A.W) A.width X Y Req Resp => p.1.1.2 := by
  show (withTestStep T k).Keeps _
  unfold withTestStep
  rw [dif_neg (by omega), if_neg (by omega)]
  exact (keeps_liftCopy _).embedIdx _

/-- **A step of the trace-preserving form of `A^Π` in the test keeps the copy register**: the
adversary's step on each counter value, and no halting, since the test's channels are trace
preserving. -/
theorem keeps_tpStep_test {k : StepIdx (A.withTest T).slots (A.withTest T).post}
    (hk : A.slots + A.post < (k : ℕ)) :
    ((A.withTest T).toTPKindAlg.step k).Keeps
      fun p : (A.withTest T).CReg => p.workspace.1.2 where
  tp := (A.withTest T).toTPKindAlg_step_tp k
  keeps z y x h := by
    have hks := keeps_withTestStep T (k := k) hk
    have hnot : ¬ (k : ℕ) < (A.withTest T).slots := by
      show ¬ (k : ℕ) < A.slots
      omega
    change (A.withTest T).tpOp k z y x ≠ 0 at h
    rcases z with r | r | c
    · simp only [tpOp, hnot, if_false] at h
      rw [cntKraus_op_apply] at h
      exact hks.keeps r _ _ (left_ne_zero_of_mul h)
    · simp [tpOp, hnot] at h
    · simp only [tpOp, Matrix.submatrix_apply, Matrix.kroneckerMap_apply] at h
      rw [KrausMap.haltOp_eq_zero (K := (A.withTest T).step k) hks.tp, Matrix.zero_apply,
        zero_mul] at h
      exact absurd rfl h

/-- **An adversary Kraus map of the test keeps `copyChal`** on the composed registers. -/
theorem keeps_advKraus_test {k : StepIdx A.slots (A.post + T.batches)} (hk : A.slots + A.post < k) :
    ((A.withTest T).toTPKindAlg.advKraus C k).Keeps fun i => copyChal T C i.1 :=
  ((keeps_tpStep_test T (k := k) hk).tensorId_prod (A := CRest X Y Req A.slots C.q C.Coins)).map
    (fun p => (p.1, p.2.1)) |>.reindex _ fun _ => rfl

/-- **The adversary's queries of a batch keep `copyChal`.** -/
theorem allKeep_advQueries (ass : (A.withTest T).toTPKindAlg.CW C → List (Assignment X Y)) :
    ReprogrammedCircuit.AllKeep (copyChal T C) ((A.withTest T).toTPKindAlg.advQueries C ass) := by
  unfold KindAlg.advQueries
  refine ReprogrammedCircuit.allKeep_concat fun c hc => ?_
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hc
  exact ⟨KrausMap.keeps_ofPerm fun _ => rfl, KrausMap.keeps_ofPerm fun _ => rfl, trivial⟩

/-- A post batch of the test keeps `copyChal`. -/
theorem allKeep_postCirc_test {b : Fin (A.post + T.batches)} (hb : A.post < b) :
    ReprogrammedCircuit.AllKeep (copyChal T C) ((A.withTest T).toTPKindAlg.postCirc C b) :=
  ⟨keeps_advKraus_test T C (k := postStep b) (by simp; omega), allKeep_advQueries T C _⟩

/-- The junction's post batch keeps `copyChal` after its first Kraus map. -/
theorem headKeep_postCirc_junction (b : Fin (A.post + T.batches)) :
    ReprogrammedCircuit.HeadKeep (copyChal T C) ((A.withTest T).toTPKindAlg.postCirc C b) :=
  ⟨_, inferInstance, _, _, rfl, allKeep_advQueries T C _⟩

/-- **The composed circuit of `A^Π` keeps `copyChal` after the adversary's part.** -/
theorem fullCircBoth_withTest_split [Nonempty X] [AddGroup Y] :
    ∃ R₁ R₂ : ReprogrammedCircuit ((A.withTest T).toTPKindAlg.CW C) X Y,
      (A.withTest T).toTPKindAlg.fullCircBoth C = R₁ ++ R₂ ∧
      ReprogrammedCircuit.HeadKeep (copyChal T C) R₂ ∧ R₂.queries = T.queries := by
  set W' := (A.withTest T).toTPKindAlg
  have hsplit : (List.finRange W'.post).map (W'.postCirc C) =
      (List.finRange A.post).map (fun b => W'.postCirc C (Fin.castAdd T.batches b)) ++
        (List.finRange T.batches).map (fun b => W'.postCirc C (Fin.natAdd A.post b)) := by
    rw [← List.ofFn_eq_map, ← List.ofFn_eq_map, ← List.ofFn_eq_map]
    exact List.ofFn_add (m := T.batches) (n := A.post) (f := W'.postCirc C)
  refine ⟨ReprogrammedCircuit.concat ((List.finRange W'.slots).map fun j => W'.slotCircBoth C j) ++
      ReprogrammedCircuit.concat ((List.finRange A.post).map
        fun b => W'.postCirc C (Fin.castAdd T.batches b)),
    ReprogrammedCircuit.concat ((List.finRange T.batches).map
        fun b => W'.postCirc C (Fin.natAdd A.post b)) ++
      .kraus (W'.advKraus C lastStep) .nil, ?_, ?_, ?_⟩
  · show ReprogrammedCircuit.concat _ ++ ReprogrammedCircuit.concat
      ((List.finRange W'.post).map (W'.postCirc C)) ++ _ = _
    rw [hsplit, ReprogrammedCircuit.concat_append]
    simp only [ReprogrammedCircuit.append_assoc]
    rfl
  · refine ReprogrammedCircuit.headKeep_concat_finRange _ _ _ (fun _ => ?_) (fun hb => ?_)
      (fun _ => headKeep_postCirc_junction T C _) (fun i hi => allKeep_postCirc_test T C ?_)
    · exact ⟨_, inferInstance, _, _, rfl, trivial⟩
    · exact ⟨keeps_advKraus_test T C (k := lastStep) (by simp; omega), trivial⟩
    · simp only [Fin.natAdd]
      omega
  · rw [ReprogrammedCircuit.queries_append, ReprogrammedCircuit.queries_concat, List.map_map]
    have h : (List.finRange T.batches).map (ReprogrammedCircuit.queries ∘
        fun b => W'.postCirc C (Fin.natAdd A.post b)) =
        (List.finRange T.batches).map fun _ => A.width :=
      List.map_congr_left fun b _ => W'.queries_postCirc C _
    rw [h]
    simp [ReprogrammedCircuit.queries, QTest.queries, mul_comm]

/-- **The composed core algorithm of the trace-preserving form of `A^Π` keeps `copyChal` after the
adversary's queries**: its Kraus maps after step `depth − T.queries` are trace preserving and keep
the copy register and the challenger's registers. -/
theorem stepsKeep_composeBothOut_withTest [Nonempty X] [AddGroup Y] [Nonempty Y] {O' : Type}
    (f : (A.withTest T).toTPKindAlg.CW C → O') :
    ((A.withTest T).toTPKindAlg.composeBothOut C f).StepsKeep
      (((A.withTest T).toTPKindAlg.composeBothOut C f).depth - T.queries)
      fun v => copyChal T C v.1 := by
  obtain ⟨R₁, R₂, heq, ⟨R, _, J, c', rfl, hc'⟩, hq⟩ := fullCircBoth_withTest_split T C
  have hcirc : ((A.withTest T).toTPKindAlg.fullCircBoth C).toCircuit =
      R₁.toCircuit ++ Circuit.kraus J.liftAnc c'.toCircuit := by
    rw [heq, ReprogrammedCircuit.toCircuit_append]
    rfl
  have hdepth : ((A.withTest T).toTPKindAlg.composeBothOut C f).depth - T.queries =
      R₁.toCircuit.queries := by
    show ((A.withTest T).toTPKindAlg.fullCircBoth C).toCircuit.queries - T.queries = _
    rw [hcirc, Circuit.queries_append]
    simp only [Circuit.queries, ReprogrammedCircuit.queries_toCircuit]
    rw [← hq]
    simp [ReprogrammedCircuit.queries]
  rw [hdepth]
  show ((((A.withTest T).toTPKindAlg.fullCircBoth C).toCircuit).toAlg _ _).StepsKeep _ _
  rw [hcirc]
  exact Circuit.stepsKeep_toAlg R₁.toCircuit J.liftAnc c'.toCircuit
    (ReprogrammedCircuit.allKeep_toCircuit hc') _ _

end AdaptiveIAlg

end GordieHowe.Quantum
