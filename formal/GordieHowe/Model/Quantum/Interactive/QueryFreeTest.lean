-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.TestLift

@[expose] public section

/-!
# Query-free tests of an adversary with run-time kinds

A **query-free test** of the residual state of an adversary `A` (`AdaptiveIAlg.QFTest`): one
channel on `A`'s registers and an outcome predicate of the workspace measured afterwards; it makes
no oracle query (Unruh 2017, ePrint 2017/398, Definition 14, p. 21, the test `Π_{x‖π}`, restricted to
tests without queries, as Unruh proposes on p. 19). As a test with no query batch
(`QFTest.toQTest`) it gives the adversary followed by the test, `A.withTest T.toQTest`
(`GordieHowe/Model/Quantum/Interactive/AdaptiveTest.lean`).

The composition of `A^Π` with a challenger acts, until its junction, on its registers as the
composition of `A` with the copy register as an extra factor (`AdaptiveIAlg.lifted_preCirc`); the
junction is `A`'s last Kraus map, the copy of the output and the test's channel. So the final state
of the composition of `A^Π` is the test's channel applied, on `A`'s registers, to the final state of
the composition of `A` with the output copied (`AdaptiveIAlg.run_fullCircBoth_withTest_apply`).
-/

open Finset Matrix
open scoped BigOperators Kronecker ENNReal

namespace GordieHowe.Quantum

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {A : AdaptiveIAlg X Y Req Resp O}

/-- **A query-free test of the residual state** (Unruh 2017, Definition 14, p. 21, the test
`Π_{x‖π}` without oracle queries): a channel on the adversary's registers and the outcome, a
predicate of the workspace measured in the computational basis afterwards. -/
structure QFTest (A : AdaptiveIAlg X Y Req Resp O) where
  /-- The index type of the channel's Kraus operators. -/
  R : Type
  [instFintypeR : Fintype R]
  /-- The channel on the adversary's registers. -/
  step : KrausChannel R (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp)
  /-- The outcome: the test accepts on the measured workspaces satisfying `ok`. -/
  ok : A.W → Prop

attribute [instance] QFTest.instFintypeR

/-- **A query-free test as a test with no query batch.** -/
def QFTest.toQTest (T : A.QFTest) : A.QTest where
  batches := 0
  R := T.R
  step _ := T.step
  ok := T.ok

theorem QFTest.queries_toQTest (T : A.QFTest) : T.toQTest.queries = 0 :=
  Nat.mul_zero _

variable (T : A.QFTest) (C : Challenger X Y Req Resp)

/-- The adversary's registers of `(A^Π).toKindAlg` as those of `A.toKindAlg` and the copy
register. -/
def cntCopy : DReg (A.withTest T.toQTest).toKindAlg.W A.width X Y Req Resp ≃
    DReg A.toKindAlg.W A.width X Y Req Resp × A.W where
  toFun p := (((((p.1.1.1.1, p.1.1.2), p.1.2.1, p.1.2.2)), p.2), p.1.1.1.2)
  invFun q := (((((q.1.1.1.1, q.2), q.1.1.1.2), q.1.1.2.1, q.1.1.2.2)), q.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The composed registers of `(A^Π).toKindAlg` as those of `A.toKindAlg` and the copy
register. -/
def cwCopy : (A.withTest T.toQTest).toKindAlg.CW C ≃ A.toKindAlg.CW C × A.W where
  toFun v := (⟨(cntCopy T v.adv).1, v.chal⟩, (cntCopy T v.adv).2)
  invFun u := ⟨(cntCopy T).symm (u.1.adv, u.2), u.1.chal⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The adversary's Kraus maps before the junction lift `A`'s** along the copy register. -/
theorem lifts_step {k : StepIdx A.slots A.post} (hk : (k : ℕ) < A.slots + A.post) :
    ((A.withTest T.toQTest).toKindAlg.step k).Lifts (cntCopy T) (A.toKindAlg.step k) := by
  have hstep : (A.withTest T.toQTest).step k =
      (A.liftCopy (A.step k)).embedIdx (A.embA T.toQTest.R) := by
    show withTestStep T.toQTest k = _
    unfold withTestStep
    rw [dif_pos hk]
  have hcopy : ((A.withTest T.toQTest).step k).Lifts A.copySplit (A.step k) := by
    rw [hstep]
    exact (KrausMap.lifts_reindex_tensorId A.copySplit (A.step k)).embedIdx _
  have hcnt : ((A.withTest T.toQTest).cntKraus k).Lifts (cntCopy T) (A.cntKraus k) :=
    (hcopy.tensorId (Fin (A.budget + 2)) (E₂ := liftProd A.copySplit _) fun _ _ => rfl).reindex
      fun _ => rfl
  change KrausMap.Lifts (cntCopy T)
    (if (k : ℕ) < A.slots then (((A.withTest T.toQTest).cntKraus k).restrict
      (A.withTest T.toQTest).inBudget).permConj (Equiv.refl _) (A.withTest T.toQTest).cntShift
      else (A.withTest T.toQTest).cntKraus k)
    (if (k : ℕ) < A.slots then ((A.cntKraus k).restrict A.inBudget).permConj (Equiv.refl _) A.cntShift
      else A.cntKraus k)
  refine KrausMap.Lifts.ite (fun _ => ?_) fun _ => hcnt
  have h1 : (((A.withTest T.toQTest).cntKraus k).restrict
      (A.withTest T.toQTest).inBudget).Lifts (cntCopy T) ((A.cntKraus k).restrict A.inBudget) :=
    hcnt.restrict fun x => by
      obtain ⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩ := x
      rfl
  have hσ : ∀ x, cntCopy T ((Equiv.refl (A.withTest T.toQTest).CReg).symm x) =
      ((Equiv.refl A.CReg).symm (cntCopy T x).1, (cntCopy T x).2) := fun _ => rfl
  have hτ : ∀ x, cntCopy T ((A.withTest T.toQTest).cntShift x) =
      (A.cntShift (cntCopy T x).1, (cntCopy T x).2) := fun x => by
    obtain ⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩ := x
    simp only [cntShift, cntCopy, Equiv.prodCongr_apply, Prod.map,
      Equiv.prodShear_apply, Equiv.refl_apply]
    rfl
  exact h1.permConj hσ (perm_symm_lift _ hτ)

open ReprogrammedCircuit (liftEquiv Lifted)

/-- **The adversary's Kraus maps before the junction, on the composed registers, lift `A`'s.** -/
theorem lifts_advKraus {k : StepIdx A.slots A.post} (hk : (k : ℕ) < A.slots + A.post) :
    ((A.withTest T.toQTest).toKindAlg.advKraus C k).Lifts (liftEquiv (cwCopy T C))
      (A.toKindAlg.advKraus C k) :=
  ((lifts_step T hk).tensorId _ (E₂ := liftProd (cntCopy T) _) fun _ _ => rfl).reindex fun _ => rfl

theorem lifts_measReq [Nonempty X] [AddGroup Y] (j : Fin A.slots) :
    ((A.withTest T.toQTest).toKindAlg.measReq C j).Lifts (liftEquiv (cwCopy T C))
      (A.toKindAlg.measReq C j) := by
  refine KrausMap.Lifts.comp (KrausMap.lifts_ofPerm _ (perm_symm_lift _ fun x => ?_))
    (KrausMap.lifts_measureFn _ fun x => ?_)
  · obtain ⟨⟨⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩, u⟩, qr⟩ := x
    show liftEquiv (cwCopy T C) (if A.kind w then _ else _) =
      ((if A.kind w then _ else _), _)
    by_cases hk : A.kind w = true
    · rw [if_pos hk, if_pos hk]
      rfl
    · rw [if_neg hk, if_neg hk]
  · obtain ⟨⟨⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩, u⟩, qr⟩ := x
    rfl

theorem lifts_writeReply [Nonempty X] [AddGroup Y] (j : Fin A.slots) :
    (KrausMap.ofPerm ((A.withTest T.toQTest).toKindAlg.writeReply C j)).Lifts
      (liftEquiv (cwCopy T C)) (KrausMap.ofPerm (A.toKindAlg.writeReply C j)) := by
  refine KrausMap.lifts_ofPerm _ (perm_symm_lift _ fun x => ?_)
  obtain ⟨⟨⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩, u⟩, qr⟩ := x
  show liftEquiv (cwCopy T C) (if (u.logs j).isSome then _ else _) =
    ((if (u.logs j).isSome then _ else _), _)
  by_cases hl : (u.logs j).isSome = true
  · rw [if_pos hl, if_pos hl]
    rfl
  · rw [if_neg hl, if_neg hl]

theorem lifted_advQueries [Nonempty X] [AddGroup Y]
    (ass : A.toKindAlg.CW C → List (Assignment X Y)) :
    Lifted (cwCopy T C) ((A.withTest T.toQTest).toKindAlg.advQueries C fun v => ass (cwCopy T C v).1)
      (A.toKindAlg.advQueries C ass) := by
  refine Lifted.concat_map (fun k => ReprogrammedCircuit.lifted_kraus ?_ (ReprogrammedCircuit.lifted_rquery (fun v => rfl)
    (ReprogrammedCircuit.lifted_kraus ?_ (by exact ReprogrammedCircuit.lifted_nil)))) _
  all_goals
    refine KrausMap.lifts_ofPerm _ (perm_symm_lift _ fun x => ?_)
    obtain ⟨⟨⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩, u⟩, qr⟩ := x
    rfl

theorem lifted_chalQueries [Nonempty X] [AddGroup Y] (j : Fin A.slots) :
    Lifted (cwCopy T C) ((A.withTest T.toQTest).toKindAlg.chalQueries C j)
      (A.toKindAlg.chalQueries C j) := by
  unfold KindAlg.chalQueries
  refine Lifted.concat_map (fun i => ?_) _
  have hp : ∀ (π' : Equiv.Perm (QueryReg ((A.withTest T.toQTest).toKindAlg.CW C) 1 X Y))
      (π : Equiv.Perm (QueryReg (A.toKindAlg.CW C) 1 X Y)), (∀ x, liftEquiv (cwCopy T C) (π' x) = (π (liftEquiv (cwCopy T C) x).1,
      (liftEquiv (cwCopy T C) x).2)) →
      (KrausMap.ofPerm π').Lifts (liftEquiv (cwCopy T C)) (KrausMap.ofPerm π) :=
    fun _ _ h => KrausMap.lifts_ofPerm _ (perm_symm_lift _ h)
  refine ReprogrammedCircuit.lifted_kraus (hp _ _ fun x => ?_)
    (ReprogrammedCircuit.lifted_rquery (fun v => rfl)
      (ReprogrammedCircuit.lifted_kraus (hp _ _ fun x => ?_) (by exact ReprogrammedCircuit.lifted_nil)))
  all_goals
    obtain ⟨⟨⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩, u⟩, qr⟩ := x
    rfl

theorem lifted_slotCircBoth [Nonempty X] [AddGroup Y] (j : Fin A.slots) :
    Lifted (cwCopy T C) ((A.withTest T.toQTest).toKindAlg.slotCircBoth C j)
      (A.toKindAlg.slotCircBoth C j) :=
  ReprogrammedCircuit.lifted_kraus (lifts_advKraus T C (k := slotStep j) (by simp; omega))
    (ReprogrammedCircuit.lifted_kraus (lifts_measReq T C j)
      ((lifted_chalQueries T C j).append (ReprogrammedCircuit.lifted_kraus (lifts_writeReply T C j)
        (lifted_advQueries T C fun u => A.toKindAlg.advAss C j u.chal))))

theorem lifted_postCirc [Nonempty X] [AddGroup Y] (b : Fin A.post) :
    Lifted (cwCopy T C) ((A.withTest T.toQTest).toKindAlg.postCirc C b) (A.toKindAlg.postCirc C b) :=
  ReprogrammedCircuit.lifted_kraus (lifts_advKraus T C (k := postStep b) (by simp))
    (lifted_advQueries T C fun u => A.toKindAlg.postAss C u.chal)

/-- **The composed circuit before the junction**: the slots and the post batches. -/
noncomputable def preCirc [Nonempty X] [AddGroup Y] (B : KindAlg X Y Req Resp O) :
    ReprogrammedCircuit (B.CW C) X Y :=
  ReprogrammedCircuit.concat ((List.finRange B.slots).map fun j => B.slotCircBoth C j) ++
    ReprogrammedCircuit.concat ((List.finRange B.post).map (B.postCirc C))

theorem fullCircBoth_eq [Nonempty X] [AddGroup Y] (B : KindAlg X Y Req Resp O) :
    B.fullCircBoth C = preCirc C B ++ .kraus (B.advKraus C lastStep) .nil :=
  rfl

/-- **Before the junction, the composition of `A^Π` lifts that of `A`**, with the copy register as
the extra factor. -/
theorem lifted_preCirc [Nonempty X] [AddGroup Y] :
    Lifted (cwCopy T C) (preCirc C (A.withTest T.toQTest).toKindAlg) (preCirc C A.toKindAlg) :=
  (Lifted.concat_map (fun j => lifted_slotCircBoth T C j) _).append
    (Lifted.concat_map (fun b => lifted_postCirc T C b) (List.finRange A.post))

/-- **The initial state of `(A^Π).toKindAlg`** is that of `A.toKindAlg` with the blank copy. -/
theorem init_withTest_apply (w c w' c' : A.W) (n n' : Fin (A.budget + 2)) (rq rq' : Req)
    (rs rs' : Option Resp) (pr pr' : Fin A.width → X × Y) :
    (A.withTest T.toQTest).toKindAlg.init.mat ((((w, c), n), rq, rs), pr)
        ((((w', c'), n'), rq', rs'), pr') =
      A.toKindAlg.init.mat ((((w, n), rq, rs), pr)) ((((w', n'), rq', rs'), pr')) *
        Matrix.single A.copyBlank A.copyBlank (1 : ℂ) c c' := by
  show A.init.mat ((w, rq, rs), pr) ((w', rq', rs'), pr') *
      Matrix.single A.copyBlank A.copyBlank (1 : ℂ) c c' * Matrix.single 0 0 (1 : ℂ) n n' =
    A.init.mat ((w, rq, rs), pr) ((w', rq', rs'), pr') * Matrix.single 0 0 (1 : ℂ) n n' *
      Matrix.single A.copyBlank A.copyBlank (1 : ℂ) c c'
  ring

/-- **The initial state of the composition of `A^Π`** is that of `A` with the blank copy
register. -/
theorem initSys_withTest [Nonempty X] [AddGroup Y] [Nonempty Y] :
    ((A.withTest T.toQTest).toKindAlg.initSys C).mat =
      liftMat (liftEquiv (cwCopy T C)) (A.toKindAlg.initSys C).mat
        (Matrix.single A.copyBlank A.copyBlank 1) := by
  ext x y
  obtain ⟨⟨⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩, u⟩, qr⟩ := x
  obtain ⟨⟨⟨⟨⟨⟨w', c'⟩, n'⟩, rq', rs'⟩, pr'⟩, u'⟩, qr'⟩ := y
  rw [liftMat_apply]
  simp only [KindAlg.initSys, MState.mix]
  rw [Matrix.sum_apply, Matrix.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]
  congr 1
  set z : CRest X Y Req A.slots C.q C.Coins := (⟨fun _ => none, fun _ _ => (KindAlg.x₀, 0), ω⟩,
    fun _ => (KindAlg.x₀, 0))
  show (A.withTest T.toQTest).toKindAlg.init.mat ((((w, c), n), rq, rs), pr)
      ((((w', c'), n'), rq', rs'), pr') * Matrix.single z z (1 : ℂ) (u, qr) (u', qr') =
    A.toKindAlg.init.mat ((((w, n), rq, rs), pr)) ((((w', n'), rq', rs'), pr')) *
      Matrix.single z z (1 : ℂ) (u, qr) (u', qr') * Matrix.single A.copyBlank A.copyBlank 1 c c'
  exact (congrArg (· * Matrix.single z z (1 : ℂ) (u, qr) (u', qr'))
    (init_withTest_apply T w c w' c' n n' rq rq' rs rs' pr pr')).trans (by ring)

/-! ### The adversary's maps on the composed registers -/

section Composed

variable (A₀ : AdaptiveIAlg X Y Req Resp O)

/-- **The composed registers of `A₀.toKindAlg`** as the adversary's registers and the rest (its
query counter, the challenger's registers and the query register). -/
def composedSplit : QueryReg (A₀.toKindAlg.CW C) 1 X Y ≃
    DReg A₀.W A₀.width X Y Req Resp × (Fin (A₀.budget + 2) × CRest X Y Req A₀.slots C.q C.Coins) where
  toFun p := ((A₀.cntSplit p.1.adv).1, ((A₀.cntSplit p.1.adv).2, (p.1.chal, p.2)))
  invFun q := (⟨A₀.cntSplit.symm (q.1, q.2.1), q.2.2.1⟩, q.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **A Kraus map on the adversary's registers, on the composed registers of `A₀.toKindAlg`**: the
identity on the query counter, the challenger's registers and the query register. -/
def composedLift {R : Type} [Fintype R]
    (K : KrausMap R (DReg A₀.W A₀.width X Y Req Resp) (DReg A₀.W A₀.width X Y Req Resp)) :
    KrausMap R (QueryReg (A₀.toKindAlg.CW C) 1 X Y) (QueryReg (A₀.toKindAlg.CW C) 1 X Y) :=
  (((K.tensorId (Fin (A₀.budget + 2))).reindex A₀.cntSplit.symm).tensorId
    (CRest X Y Req A₀.slots C.q C.Coins)).reindex (A₀.toKindAlg.advSplit C)

theorem lifts_composedLift {R : Type} [Fintype R]
    (K : KrausMap R (DReg A₀.W A₀.width X Y Req Resp) (DReg A₀.W A₀.width X Y Req Resp)) :
    (composedLift C A₀ K).Lifts (composedSplit C A₀) K :=
  ((KrausMap.lifts_reindex_tensorId A₀.cntSplit K).tensorId_right _
    (E₂ := rightProd A₀.cntSplit _) fun _ _ => rfl).reindex_left fun _ => rfl

/-- **The adversary's Kraus maps after the slots** are `composedLift` of its own. -/
theorem advKraus_eq_composedLift {k : StepIdx A₀.slots A₀.post} (hk : ¬ (k : ℕ) < A₀.slots) :
    A₀.toKindAlg.advKraus C k = composedLift C A₀ (A₀.step k) := by
  unfold KindAlg.advKraus composedLift
  rw [toKindAlg_step, if_neg hk]
  rfl

end Composed

/-- **The junction of `A^Π` on the composed registers**: the last Kraus map of the composition of
`A^Π` lifts the junction (`A`'s last Kraus map, the copy of the output, the test's channel). -/
theorem lifts_advKraus_last :
    ((A.withTest T.toQTest).toKindAlg.advKraus C
      (lastStep : StepIdx (A.withTest T.toQTest).slots (A.withTest T.toQTest).post)).Lifts
      (composedSplit C (A.withTest T.toQTest)) (junction T.toQTest) := by
  have hk : ¬ ((lastStep : StepIdx (A.withTest T.toQTest).slots (A.withTest T.toQTest).post) : ℕ) <
      (A.withTest T.toQTest).slots := by
    rw [Fin.val_mk]
    omega
  have h1 := advKraus_eq_composedLift C (A.withTest T.toQTest) hk
  have hl : ((lastStep : StepIdx (A.withTest T.toQTest).slots (A.withTest T.toQTest).post) : ℕ) =
      A.slots + A.post := by
    simp [withTest, QFTest.toQTest]
  have hstep : (A.withTest T.toQTest).step lastStep =
      (junction T.toQTest).embedIdx (A.embAT T.toQTest.R) := by
    show withTestStep T.toQTest lastStep = _
    unfold withTestStep
    rw [dif_neg (by simp [QFTest.toQTest])]
    exact if_pos hl
  have h2 : (composedLift C (A.withTest T.toQTest) ((A.withTest T.toQTest).step lastStep)).Lifts
      (composedSplit C (A.withTest T.toQTest)) (junction T.toQTest) :=
    (lifts_composedLift C _ _).congr_right fun ρ => by
      rw [hstep]
      exact KrausMap.embedIdx_apply _ _ ρ
  exact h2.congr_left fun ρ => by
    rw [h1]
    exact rfl

/-- **The block of a lifted state at the rest of the composed registers of `A^Π`** is the block of
`A`'s state with the copy register. -/
theorem blockAt_liftMat_cwCopy (ρ : Matrix (QueryReg (A.toKindAlg.CW C) 1 X Y)
      (QueryReg (A.toKindAlg.CW C) 1 X Y) ℂ) (τ : Matrix A.W A.W ℂ)
    (z z' : Fin (A.budget + 2) × CRest X Y Req A.slots C.q C.Coins) :
    blockAt (composedSplit C (A.withTest T.toQTest)) (liftMat (liftEquiv (cwCopy T C)) ρ τ) z z' =
      liftMat A.copySplit (blockAt (composedSplit C A) ρ z z') τ := by
  ext d d'
  rfl

/-- The basis states of `A`'s registers whose output has the representative `c`. -/
def repIs (c : A.W) : Set (DReg A.W A.width X Y Req Resp) :=
  {d | A.outRep d.workspace = c}

/-- **The copy of the output, read through the split of the copy register**: on the blank copy
`copyBlank` it writes the representative of the output, and conversely. -/
theorem copySplit_copyOut_symm (a : DReg A.W A.width X Y Req Resp) (c : A.W) :
    A.copySplit (A.copyOut.symm (A.copySplit.symm (a, c))) =
      (a, Equiv.swap A.copyBlank (A.outRep a.workspace) c) :=
  rfl

theorem lifts_liftCopy {R : Type} [Fintype R]
    (K : KrausMap R (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp)) :
    (A.liftCopy K).Lifts A.copySplit K :=
  KrausMap.lifts_reindex_tensorId _ _

/-- **The junction on a state with a blank copy**: at a basis state with copy register `c`, the
diagonal is the test's channel applied to `A`'s last Kraus map's output cut to the basis states
whose output has the representative `c`. -/
theorem junction_liftMat_apply (σ : Matrix (DReg A.W A.width X Y Req Resp)
      (DReg A.W A.width X Y Req Resp) ℂ) (d : DReg (A.W × A.W) A.width X Y Req Resp) :
    junction T.toQTest (liftMat A.copySplit σ (Matrix.single A.copyBlank A.copyBlank 1)) d d =
      T.step (cutTo (repIs (A.copySplit d).2) (A.step lastStep σ)) (A.copySplit d).1
        (A.copySplit d).1 := by
  have hP : ((A.liftCopy (A.step lastStep)).permConj (Equiv.refl _) A.copyOut)
      (liftMat A.copySplit σ (Matrix.single A.copyBlank A.copyBlank 1)) =
      (liftMat A.copySplit (A.step lastStep σ) (Matrix.single A.copyBlank A.copyBlank 1)).submatrix
        A.copyOut.symm A.copyOut.symm := by
    rw [KrausMap.permConj_apply]
    simp only [Equiv.refl_symm, Equiv.coe_refl, Matrix.submatrix_id_id]
    rw [lifts_liftCopy (A.step lastStep) σ]
  rw [junction, KrausMap.comp_apply]
  refine ((lifts_liftCopy (T.toQTest.step 0).toKrausMap).apply_apply _ d d).trans ?_
  rw [hP]
  have hb : blockAt A.copySplit
      ((liftMat A.copySplit (A.step lastStep σ) (Matrix.single A.copyBlank A.copyBlank 1)).submatrix
        A.copyOut.symm A.copyOut.symm) (A.copySplit d).2 (A.copySplit d).2 =
      cutTo (repIs (A.copySplit d).2) (A.step lastStep σ) := by
    ext a b
    rw [blockAt_apply, Matrix.submatrix_apply, liftMat_apply, copySplit_copyOut_symm,
      copySplit_copyOut_symm]
    have hs : ∀ r x : A.W, A.copyBlank = Equiv.swap A.copyBlank r x ↔ x = r := fun r x => by
      rw [eq_comm, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
    simp only [cutTo, repIs, Set.mem_setOf_eq, Matrix.single_apply, hs]
    by_cases ha : A.outRep a.workspace = (A.copySplit d).2 <;>
      by_cases hb : A.outRep b.workspace = (A.copySplit d).2 <;> simp [ha, hb, eq_comm]
  rw [hb]
  rfl

section Run

variable [Nonempty X] [AddGroup Y] [Nonempty Y]

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
/-- **The last Kraus map of `A`'s composition lifts `A`'s last Kraus map.** -/
theorem lifts_advKraus_last_self :
    (A.toKindAlg.advKraus C (lastStep : StepIdx A.slots A.post)).Lifts (composedSplit C A)
      (A.step lastStep) := by
  have hk : ¬ ((lastStep : StepIdx A.slots A.post) : ℕ) < A.slots := by
    rw [Fin.val_mk]
    omega
  have h1 := advKraus_eq_composedLift C A hk
  exact (lifts_composedLift C A (A.step lastStep)).congr_left fun ρ => by
    rw [h1]
    exact rfl

omit [Nonempty Y] in
/-- **The final state of `A`'s composition, block by block**: at the rest `z` of the registers,
`A`'s last Kraus map applied to the block of the state before it. -/
theorem blockAt_run_fullCircBoth (H : X → Y) (z z' : Fin (A.budget + 2) × CRest X Y Req A.slots C.q C.Coins) :
    blockAt (composedSplit C A) ((A.toKindAlg.fullCircBoth C).run H (A.toKindAlg.initSys C).mat) z z' =
      A.step lastStep (blockAt (composedSplit C A)
        ((preCirc C A.toKindAlg).run H (A.toKindAlg.initSys C).mat) z z') := by
  rw [fullCircBoth_eq, ReprogrammedCircuit.run_append]
  ext d d'
  simp only [ReprogrammedCircuit.run, blockAt_apply]
  refine ((lifts_advKraus_last_self C).apply_apply _ _ _).trans ?_
  simp

/-- **The final state of the composition of `A^Π`, on the diagonal**: at a basis state with
adversary's registers `d₀`, copy register `c` and rest `z`, the test's channel applied to `A`'s last
Kraus map's output on the block at `z` of `A`'s state before it, cut to the basis states whose
output has the representative `c`. -/
theorem run_fullCircBoth_withTest_apply (H : X → Y)
    (x : QueryReg ((A.withTest T.toQTest).toKindAlg.CW C) 1 X Y) :
    ((A.withTest T.toQTest).toKindAlg.fullCircBoth C).run H
        ((A.withTest T.toQTest).toKindAlg.initSys C).mat x x =
      T.step (cutTo (repIs (A.copySplit (composedSplit C (A.withTest T.toQTest) x).1).2)
        (A.step lastStep (blockAt (composedSplit C A)
          ((preCirc C A.toKindAlg).run H (A.toKindAlg.initSys C).mat)
          (composedSplit C (A.withTest T.toQTest) x).2 (composedSplit C (A.withTest T.toQTest) x).2)))
        (A.copySplit (composedSplit C (A.withTest T.toQTest) x).1).1
        (A.copySplit (composedSplit C (A.withTest T.toQTest) x).1).1 := by
  rw [fullCircBoth_eq, ReprogrammedCircuit.run_append, initSys_withTest,
    (lifted_preCirc T C).run H]
  simp only [ReprogrammedCircuit.run]
  refine ((lifts_advKraus_last T C).apply_apply _ _ _).trans ?_
  exact (congrArg (fun M => junction T.toQTest M (composedSplit C (A.withTest T.toQTest) x).1
      (composedSplit C (A.withTest T.toQTest) x).1) (blockAt_liftMat_cwCopy T C _ _ _ _)).trans
    (junction_liftMat_apply T _ _)

end Run

/-! ### Sums over the outputs -/

section Outputs

variable (A₀ : AdaptiveIAlg X Y Req Resp O)

open Classical in
/-- **The outputs of the adversary's workspaces.** -/
noncomputable def outputs : Finset O :=
  Finset.univ.image A₀.out

/-- The basis states of the adversary's registers whose workspace has the output `o`. -/
def outIs (o : O) : Set (DReg A₀.W A₀.width X Y Req Resp) :=
  {d | A₀.out d.workspace = o}

variable {A₀}

/-- **Summing over the copy register is summing over the outputs**: a sum over the values `c` of
the copy register of a function of the output of `c` and the set of basis states whose output has
the representative `c` is the sum over the outputs `o` of the function at `o` and the basis states
with output `o`, when the function vanishes on the empty set. -/
theorem sum_repIs {M : Type*} [AddCommMonoid M] (F : O → Set (DReg A₀.W A₀.width X Y Req Resp) → M)
    (h0 : ∀ o, F o ∅ = 0) :
    ∑ c, F (A₀.out c) (repIs c) = ∑ o ∈ outputs A₀, F o (outIs A₀ o) := by
  classical
  have hrep : ∀ w : A₀.W, repIs (A₀.outRep w) = outIs A₀ (A₀.out w) := fun w => by
    ext d
    simp only [repIs, outIs, Set.mem_setOf_eq]
    constructor
    · intro h
      rw [← A₀.out_outRep d.workspace, h, A₀.out_outRep]
    · exact A₀.outRep_eq_of_out_eq
  have hnot : ∀ c, c ∉ Finset.univ.image A₀.outRep → repIs c = (∅ : Set (DReg A₀.W A₀.width X Y Req Resp)) :=
    fun c hc => by
      ext d
      simp only [repIs, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hc (Finset.mem_image.2 ⟨d.workspace, Finset.mem_univ _, h⟩)
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image A₀.outRep)) fun c _ hc => by
    rw [hnot c hc, h0]]
  have himg : outputs A₀ = (Finset.univ.image A₀.outRep).image A₀.out := by
    ext o
    simp only [outputs, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨A₀.outRep w, ⟨w, rfl⟩, A₀.out_outRep w⟩
    · rintro ⟨c, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, (A₀.out_outRep w).symm⟩
  have hinj : Set.InjOn A₀.out ↑(Finset.univ.image A₀.outRep) := by
    intro c₁ h₁ c₂ h₂ h
    obtain ⟨w₁, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 h₁)
    obtain ⟨w₂, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 h₂)
    rw [A₀.out_outRep, A₀.out_outRep] at h
    exact A₀.outRep_eq_of_out_eq h
  rw [himg, Finset.sum_image (f := fun o => F o (outIs A₀ o)) hinj]
  refine Finset.sum_congr rfl fun c hc => ?_
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hc
  rw [hrep, A₀.out_outRep]

end Outputs

/-! ### Prove with a query-free test -/

section Prove

variable [Nonempty X] [AddGroup Y] [Nonempty Y]

/-- **The diagonal of the final state of the composition of `A^Π`, summed against a function of the
copied output, the challenger's registers and `A`'s workspace**, is the sum over the outputs `o` of
the diagonal of the test's channel applied to the final state of the composition of `A` cut to the
output `o`: measuring the output before the test's channel (Unruh's order) and copying it into the
workspace before the channel give the same joint law. -/
theorem sum_diag_withTest (H : X → Y)
    (g : O → ChallengerRegs X Y Req A.slots C.q C.Coins → A.W → ℝ≥0∞) :
    ∑ x : QueryReg ((A.withTest T.toQTest).toKindAlg.CW C) 1 X Y,
        g (A.out x.1.adv.workspace.1.2) x.1.chal x.1.adv.workspace.1.1 *
          ENNReal.ofReal ((((A.withTest T.toQTest).toKindAlg.fullCircBoth C).run H
            ((A.withTest T.toQTest).toKindAlg.initSys C).mat) x x).re =
      ∑ o ∈ outputs A, ∑ q : QueryReg (A.toKindAlg.CW C) 1 X Y,
        g o q.1.chal q.1.adv.workspace.1 *
          ENNReal.ofReal ((composedLift C A T.step.toKrausMap
            (cutTo {q : QueryReg (A.toKindAlg.CW C) 1 X Y | A.out q.1.adv.workspace.1 = o}
              ((A.toKindAlg.fullCircBoth C).run H (A.toKindAlg.initSys C).mat))) q q).re := by
  set ρ := (preCirc C A.toKindAlg).run H (A.toKindAlg.initSys C).mat
  set L : Fin (A.budget + 2) × CRest X Y Req A.slots C.q C.Coins → Matrix (DReg A.W A.width X Y Req Resp)
      (DReg A.W A.width X Y Req Resp) ℂ := fun z => A.step lastStep (blockAt (composedSplit C A) ρ z z)
  have hL : ∀ x, ((A.withTest T.toQTest).toKindAlg.fullCircBoth C).run H
      ((A.withTest T.toQTest).toKindAlg.initSys C).mat x x =
      T.step (cutTo (repIs (A.copySplit (composedSplit C (A.withTest T.toQTest) x).1).2)
        (L (composedSplit C (A.withTest T.toQTest) x).2))
        (A.copySplit (composedSplit C (A.withTest T.toQTest) x).1).1
        (A.copySplit (composedSplit C (A.withTest T.toQTest) x).1).1 :=
    fun x => run_fullCircBoth_withTest_apply T C H x
  have hR : ∀ o (q : QueryReg (A.toKindAlg.CW C) 1 X Y), composedLift C A T.step.toKrausMap
      (cutTo {q : QueryReg (A.toKindAlg.CW C) 1 X Y | A.out q.1.adv.workspace.1 = o}
        ((A.toKindAlg.fullCircBoth C).run H (A.toKindAlg.initSys C).mat)) q q =
      T.step (cutTo (outIs A o) (L (composedSplit C A q).2)) (composedSplit C A q).1
        (composedSplit C A q).1 := fun o q => by
    refine ((lifts_composedLift C A T.step.toKrausMap).apply_apply _ q q).trans ?_
    have hb := blockAt_cutTo (composedSplit C A)
      (S := {q : QueryReg (A.toKindAlg.CW C) 1 X Y | A.out q.1.adv.workspace.1 = o})
      (S' := outIs A o) (fun _ => Iff.rfl)
      ((A.toKindAlg.fullCircBoth C).run H (A.toKindAlg.initSys C).mat)
      (composedSplit C A q).2 (composedSplit C A q).2
    rw [hb, blockAt_run_fullCircBoth]
    rfl
  -- the summand at the split coordinates
  set G : DReg A.W A.width X Y Req Resp → Fin (A.budget + 2) × CRest X Y Req A.slots C.q C.Coins →
      O → Set (DReg A.W A.width X Y Req Resp) → ℝ≥0∞ := fun d₀ z o S =>
    g o z.2.1 d₀.workspace * ENNReal.ofReal (T.step (cutTo S (L z)) d₀ d₀).re
  have hG0 : ∀ d₀ z o, G d₀ z o ∅ = 0 := fun d₀ z o => by
    have : cutTo (∅ : Set (DReg A.W A.width X Y Req Resp)) (L z) = 0 := by
      ext a b
      simp [cutTo]
    simp only [G, this]
    simp [KrausChannel.apply]
  calc _ = ∑ p : DReg (A.W × A.W) A.width X Y Req Resp ×
          (Fin (A.budget + 2) × CRest X Y Req A.slots C.q C.Coins),
        G (A.copySplit p.1).1 p.2 (A.out (A.copySplit p.1).2) (repIs (A.copySplit p.1).2) :=
        Fintype.sum_equiv (composedSplit C (A.withTest T.toQTest)) _ _ fun x => by
          rw [hL x]
          rfl
    _ = ∑ dc : DReg A.W A.width X Y Req Resp × A.W, ∑ z : Fin (A.budget + 2) ×
          CRest X Y Req A.slots C.q C.Coins, G dc.1 z (A.out dc.2) (repIs dc.2) := by
        rw [Fintype.sum_prod_type]
        exact Fintype.sum_equiv A.copySplit _ _ fun d => rfl
    _ = ∑ d₀ : DReg A.W A.width X Y Req Resp, ∑ z : Fin (A.budget + 2) ×
          CRest X Y Req A.slots C.q C.Coins, ∑ o ∈ outputs A, G d₀ z o (outIs A o) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun d₀ _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun z _ => sum_repIs (G d₀ z) (hG0 d₀ z)
    _ = ∑ d₀ : DReg A.W A.width X Y Req Resp, ∑ o ∈ outputs A, ∑ z : Fin (A.budget + 2) ×
          CRest X Y Req A.slots C.q C.Coins, G d₀ z o (outIs A o) :=
        Finset.sum_congr rfl fun d₀ _ => Finset.sum_comm
    _ = ∑ o ∈ outputs A, ∑ d₀ : DReg A.W A.width X Y Req Resp, ∑ z : Fin (A.budget + 2) ×
          CRest X Y Req A.slots C.q C.Coins, G d₀ z o (outIs A o) :=
        Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [← Fintype.sum_prod_type']
        refine Fintype.sum_equiv (composedSplit C A).symm _ _ fun p => ?_
        rw [hR]
        simp only [Equiv.apply_symm_apply]
        rfl

/-- **The final state of a composition** is the run of its circuit on the initial state, with the
clean ancilla. -/
theorem final_composeBothOut {B : KindAlg X Y Req Resp O} {O' : Type} (f : B.CW C → O') (H : X → Y) :
    (B.composeBothOut C f).final H =
      liftMat (ancSplit (B.CW C) X Y) ((B.fullCircBoth C).run H (B.initSys C).mat)
        (reprogAnc KindAlg.x₀) := by
  rw [Circuit.toAlg_final]
  exact ReprogrammedCircuit.run_toCircuit H _ _ _

/-- **The test's channel on the composed registers of `A`**, with the ancilla: the channel on the
adversary's registers, the identity on the query counter, the challenger's registers, the query
register and the ancilla. -/
noncomputable def testOnComposed :
    KrausMap T.R (ReprogrammedQueryReg (A.toKindAlg.CW C) X Y)
      (ReprogrammedQueryReg (A.toKindAlg.CW C) X Y) :=
  (composedLift C A T.step.toKrausMap).liftAnc

/-- **Prove with a query-free test** (Unruh 2017, Definition 14, p. 21, Prove followed by the test
`Π_{x‖π}(S_A)`, for a test that makes no oracle query): the probability, with `H` uniform, that the
run of the composition of `A` with the challenger, followed by the measurement of `A`'s output `o`,
the test's channel on the unmeasured registers and the measurement of all registers, satisfies the
event `E` of the output `o`, the challenger's registers and `H`, and the test accepts on the measured
workspace. The output is measured before the test's channel acts, as in Unruh's game. -/
noncomputable def proveTestProb
    (E : O → ChallengerRegs X Y Req A.slots C.q C.Coins → (X → Y) → Prop) : ℝ≥0∞ :=
  ∑' H, PMF.uniformOfFintype (X → Y) H * ∑ o ∈ outputs A,
    ∑ p : ReprogrammedQueryReg (A.toKindAlg.CW C) X Y,
      Set.indicator {p : ReprogrammedQueryReg (A.toKindAlg.CW C) X Y |
          E o p.1.1.chal H ∧ T.ok p.1.1.adv.workspace.1}
        (fun p => ENNReal.ofReal ((testOnComposed T C
          (cutTo {p : ReprogrammedQueryReg (A.toKindAlg.CW C) X Y | A.out p.1.1.adv.workspace.1 = o}
            ((A.toKindAlg.composeBothOut C id).final H))) p p).re) p

/-- **The probability of the event for the adversary followed by the test**: the composition of
`A^Π` with the challenger, all registers measured at the end; the event `E` of the copied output,
the challenger's registers and the oracle, and the test's outcome on `A`'s part of the workspace. -/
noncomputable def proveFoldedProb {Bt : Type} (e : Y ≃ Bt)
    (E : O → ChallengerRegs X Y Req A.slots C.q C.Coins → (X → Y) → Prop) : ℝ≥0∞ :=
  (((A.withTest T.toQTest).toKindAlg.composeBothOut C id).realLaw e).toOuterMeasure
    {p | ∃ v, p.out = some v ∧ E (A.out v.adv.workspace.1.2) v.chal (e.symm ∘ p.oracle) ∧
      T.ok v.adv.workspace.1.1}

/-- **Test absorption in Unruh's Prove**: for every event `E` of the output, the challenger's
registers and the oracle, the probability that the adversary followed by a query-free test (`A^Π`,
`AdaptiveIAlg.withTest`) satisfies `E` and the test accepts, with all registers measured at the end,
is the probability of Unruh's Prove with the test: the output measured, then the test's channel on
the unmeasured registers, then the measurement. -/
theorem proveFoldedProb_eq {Bt : Type} (e : Y ≃ Bt)
    (E : O → ChallengerRegs X Y Req A.slots C.q C.Coins → (X → Y) → Prop) :
    proveFoldedProb T C e E = proveTestProb T C E := by
  classical
  refine (Alg.toOuterMeasure_realLaw_out _ e (fun (v : (A.withTest T.toQTest).toKindAlg.CW C) h =>
    E (A.out v.adv.workspace.1.2) v.chal (e.symm ∘ h) ∧ T.ok v.adv.workspace.1.1)).trans ?_
  refine tsum_congr fun H => ?_
  congr 1
  have hH : e.symm ∘ (e ∘ H) = H := by
    funext x
    simp
  simp only [hH]
  -- the folded side
  have hB := sum_liftMat_diag (ancSplit ((A.withTest T.toQTest).toKindAlg.CW C) X Y)
    (ReprogrammedCircuit.posSemidef_run H ((A.withTest T.toQTest).toKindAlg.fullCircBoth C)
      ((A.withTest T.toQTest).toKindAlg.initSys C).posSemidef)
    (posSemidef_reprogAnc KindAlg.x₀) (trace_reprogAnc KindAlg.x₀)
    (fun q => if E (A.out q.1.adv.workspace.1.2) q.1.chal H ∧ T.ok q.1.adv.workspace.1.1 then 1 else 0)
  have hL : ∀ i : ReprogrammedQueryReg ((A.withTest T.toQTest).toKindAlg.CW C) X Y,
      Set.indicator {i : ReprogrammedQueryReg ((A.withTest T.toQTest).toKindAlg.CW C) X Y |
          E (A.out (id i.1.1).adv.workspace.1.2) (id i.1.1).chal H ∧ T.ok (id i.1.1).adv.workspace.1.1}
        (fun i => ENNReal.ofReal
          ((((A.withTest T.toQTest).toKindAlg.composeBothOut C id).final H) i i).re) i =
      (if E (A.out (ancSplit _ X Y i).1.1.adv.workspace.1.2) (ancSplit _ X Y i).1.1.chal H ∧
          T.ok (ancSplit _ X Y i).1.1.adv.workspace.1.1 then 1 else 0) *
        ENNReal.ofReal (liftMat (ancSplit _ X Y)
          (((A.withTest T.toQTest).toKindAlg.fullCircBoth C).run H
            ((A.withTest T.toQTest).toKindAlg.initSys C).mat) (reprogAnc KindAlg.x₀) i i).re := by
    intro i
    rw [final_composeBothOut]
    simp only [Set.indicator, Set.mem_setOf_eq, id]
    split_ifs <;> simp_all [ancSplit]
  simp only [hL]
  rw [hB]
  refine (sum_diag_withTest T C H (fun o u w => if E o u H ∧ T.ok w then 1 else 0)).trans ?_
  refine Finset.sum_congr rfl fun o _ => ?_
  -- the side of Unruh's game
  have hA := sum_liftMat_diag (ancSplit (A.toKindAlg.CW C) X Y)
    ((composedLift C A T.step.toKrausMap).posSemidef_apply (posSemidef_cutTo
      {q : QueryReg (A.toKindAlg.CW C) 1 X Y | A.out q.1.adv.workspace.1 = o}
      (ReprogrammedCircuit.posSemidef_run H (A.toKindAlg.fullCircBoth C) (A.toKindAlg.initSys C).posSemidef)))
    (posSemidef_reprogAnc KindAlg.x₀) (trace_reprogAnc KindAlg.x₀)
    (fun q => if E o q.1.chal H ∧ T.ok q.1.adv.workspace.1 then 1 else 0)
  have hR : ∀ p : ReprogrammedQueryReg (A.toKindAlg.CW C) X Y,
      Set.indicator {p : ReprogrammedQueryReg (A.toKindAlg.CW C) X Y |
          E o p.1.1.chal H ∧ T.ok p.1.1.adv.workspace.1}
        (fun p => ENNReal.ofReal ((testOnComposed T C
          (cutTo {p : ReprogrammedQueryReg (A.toKindAlg.CW C) X Y | A.out p.1.1.adv.workspace.1 = o}
            ((A.toKindAlg.composeBothOut C id).final H))) p p).re) p =
      (if E o (ancSplit _ X Y p).1.1.chal H ∧ T.ok (ancSplit _ X Y p).1.1.adv.workspace.1 then 1 else 0) *
        ENNReal.ofReal (liftMat (ancSplit _ X Y) (composedLift C A T.step.toKrausMap
          (cutTo {q : QueryReg (A.toKindAlg.CW C) 1 X Y | A.out q.1.adv.workspace.1 = o}
            ((A.toKindAlg.fullCircBoth C).run H (A.toKindAlg.initSys C).mat)))
          (reprogAnc KindAlg.x₀) p p).re := by
    intro p
    have hM : testOnComposed T C
        (cutTo {p : ReprogrammedQueryReg (A.toKindAlg.CW C) X Y | A.out p.1.1.adv.workspace.1 = o}
          ((A.toKindAlg.composeBothOut C id).final H)) =
        liftMat (ancSplit _ X Y) (composedLift C A T.step.toKrausMap
          (cutTo {q : QueryReg (A.toKindAlg.CW C) 1 X Y | A.out q.1.adv.workspace.1 = o}
            ((A.toKindAlg.fullCircBoth C).run H (A.toKindAlg.initSys C).mat)))
          (reprogAnc KindAlg.x₀) := by
      rw [final_composeBothOut, cutTo_liftMat (ancSplit _ X Y)
        (S := {p : ReprogrammedQueryReg (A.toKindAlg.CW C) X Y | A.out p.1.1.adv.workspace.1 = o})
        (S' := {q : QueryReg (A.toKindAlg.CW C) 1 X Y | A.out q.1.adv.workspace.1 = o})
        (fun _ => Iff.rfl)]
      exact KrausMap.lifts_reindex_tensorId (ancSplit _ X Y) _ _ _
    simp only [hM, Set.indicator, Set.mem_setOf_eq]
    split_ifs <;> simp_all [ancSplit]
  simp only [hR]
  rw [hA]

end Prove

end AdaptiveIAlg

end GordieHowe.Quantum
