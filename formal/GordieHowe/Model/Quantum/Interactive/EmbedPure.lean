-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.Embed
public import GordieHowe.Model.Quantum.Interactive.PureTest

@[expose] public section

/-!
# Adversaries with run-time kinds that make only queries and whose Kraus maps are unitary

The output law of a composition of an adversary with run-time kinds (`AdaptiveIAlg`) that never
asks for a request and whose Kraus maps have one operator each, from the pure run of its
operators, and the tools for the pure run of such an adversary followed by a test
(`AdaptiveIAlg.withTest`, written `A^Π`).

- `KindAlg.outLaw_composeBothOut_toAdaptive_of_pure`: for a kind algorithm `K` whose kinds are all
  queries, with the budget the number of query slots, the output law of `composeBothOut f` at `o`
  is the coin-average of the squared norm of the pure run of `K`'s operators on the registers
  whose composed register (the counter after the slots, blank logs, clean challenger registers)
  `f` reads as `o`. The proof is `KindAlg.mgRun_toAdaptive` (no branch is projected away by the
  budget) and `KindAlg.mgRun_false_of_pure`.
- `AdaptiveIAlg.core`: the kind algorithm of an adversary with run-time kinds (its fields without
  the budget), so that `A.core.toAdaptive A.budget = A`.
- `AdaptiveIAlg.copyVec v c`: a vector of `A`'s registers with the copy register of `A^Π` at `c`;
  `AdaptiveIAlg.copyMat U`: an operator of `A` acting on the registers of `A^Π`. The Kraus maps of
  `A^Π` have one operator (`withTestMat`) when those of `A` and of the test do
  (`withTestStep_pureAt`), its initial state is pure when `A`'s is (`withTest_init_of_proj`), and
  its slots act on `copyVec` as `A`'s slots act on `A`'s registers (`foldl_pureSlot_withTest`).
  The copy of the output writes the representative `c` of the output on a vector whose workspaces
  all have that output (`permOp_copyOut_copyVec`).
- `IAlg.cntLift`, `IAlg.QTest.toAdaptive`: a residual-state test of a fixed-schedule adversary as
  a test of its embedding `IAlg.toAdaptive`, acting on the registers without the slot counter.
-/

open Finset Matrix
open scoped BigOperators ENNReal Kronecker ComplexOrder

namespace GordieHowe.Quantum

/-! ### The output law of an adversary with run-time kinds that makes only queries -/

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] (K : KindAlg X Y Req Resp O) (C : Challenger X Y Req Resp)

/-- The composed register of `K`'s registers `d` with blank logs, clean challenger registers and
the coins `c`. -/
noncomputable def blankReg (d : DReg K.W K.width X Y Req Resp) (c : C.Coins) : K.CW C :=
  ⟨d, ⟨fun _ => none, fun _ _ => (KindAlg.x₀, 0), c⟩⟩

omit [Nonempty X] in
/-- **A kind algorithm whose kinds are all queries respects every all-query schedule**, with no
invariant. -/
theorem respects_of_kind_eq_false {sched : Fin K.slots → Bool} (hkind : ∀ w, K.kind w = false)
    (hsched : ∀ j, sched j = false) : K.Respects C sched fun _ => Set.univ where
  kind k σ _ := fun a b hab => by
    exfalso
    rcases hab with h | h <;> exact h (by simp [hkind, hsched])
  step _ _ _ _ _ := fun a b hab => by
    exfalso
    rcases hab with h | h <;> exact h (Set.mem_univ _)

/-- **The output law of an adversary with run-time kinds that makes only queries and whose Kraus
maps have one operator**: for the kind algorithm `K` with all kinds queries, its embedding with the
budget of the query slots of an all-query schedule, and `composeBothOut f` at `o`, the
coin-average of the squared norm of the pure run of `K`'s operators `U` with the oracle `H`, on
the registers whose composed register (the counter after the slots, blank logs, clean challenger
registers) `f` reads as `o`. -/
theorem outLaw_composeBothOut_toAdaptive_of_pure {sched : Fin K.slots → Bool}
    (hkind : ∀ w, K.kind w = false) (hsched : ∀ j, sched j = false)
    (U : StepIdx K.slots K.post →
      Matrix (DReg K.W K.width X Y Req Resp) (DReg K.W K.width X Y Req Resp) ℂ)
    (hU : ∀ k, ∃ r₀, (K.step k).PureAt r₀ (U k)) {ψ : QState (DReg K.W K.width X Y Req Resp)}
    (hinit : K.init.mat = proj ψ) {O' : Type} [DecidableEq O']
    (f : (K.toAdaptive (queryCount sched)).toKindAlg.CW C → O') (H : X → Y) (o : O') :
    ((K.toAdaptive (queryCount sched)).toKindAlg.composeBothOut C f).outLaw H (some o) =
      ENNReal.ofReal (∑ c, (C.coins c).toReal * ∑ d : DReg K.W K.width X Y Req Resp,
        if f (K.cwLift C _ (cntAt sched K.slots) (K.blankReg C d c)) = o then
          ‖K.pureRun U H ψ d‖ ^ 2 else 0) := by
  classical
  rw [outLaw_composeBothOut_some]
  congr 1
  refine sum_congr rfl fun c _ => ?_
  congr 1
  rw [K.mgRun_toAdaptive C (K.respects_of_kind_eq_false C hkind hsched)
    (fun _ _ hab => by rcases hab with h | h <;> exact absurd (Set.mem_univ _) h) H c]
  have h := embed_diag_of_injective (K.placeCnt_injective (queryCount sched) (cntAt sched K.slots))
    (K.mgRun C.toPureEnv (H, c) true)
    (fun i => if f ((K.toAdaptive (queryCount sched)).toKindAlg.emb C H c K.slots i).1 = o
      then 1 else 0)
  simp only [boole_mul] at h
  refine h.trans ?_
  simp only [emb_placeCnt]
  have hreq : Quantum.requests (fun _ => none : LogReg Req K.slots) = [] := by
    rw [requests_eq_requestsBefore (k := 0) fun _ _ => rfl]
    rfl
  have hH : K.blankOracle C.toPureEnv (H, c) = H := by
    simp only [KindAlg.blankOracle, Env.oracle]
    erw [hreq]
    rfl
  rw [KindAlg.mgRun_deph]
  simp only [dephase_apply_self]
  rw [K.mgRun_false_of_pure _ _ hkind hU _ hinit, hH]
  have hgar : K.garFill C H c (fun _ => none) K.slots = fun _ _ => (KindAlg.x₀, 0) := by
    funext j i
    simp only [KindAlg.garFill]
    split_ifs <;> rfl
  rw [← splitLogs.symm.sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single (fun _ => none)]
  · simp only [proj_apply, KindAlg.liftLogs, Equiv.apply_symm_apply,
      KindAlg.emb, KindAlg.advSplit, Equiv.coe_fn_mk]
    erw [hgar]
    simp only [↓reduceIte]
    rfl
  · intro y _ hy
    simp only [proj_apply, KindAlg.liftLogs_apply]
    erw [Equiv.apply_symm_apply]
    simp [hy]
  · simp

end KindAlg

/-! ### The pure run of an adversary with run-time kinds followed by a test -/

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (A : AdaptiveIAlg X Y Req Resp O)

/-- **The kind algorithm of an adversary with run-time kinds**: its fields without the budget
(`core_toAdaptive`).

Running time: that of `A`; the same registers, Kraus maps and output. This running time is argued
here, not proved in Lean. -/
def core : KindAlg X Y Req Resp O where
  W := A.W
  width := A.width
  width_pos := A.width_pos
  slots := A.slots
  post := A.post
  kind := A.kind
  R := A.R
  init := A.init
  step := A.step
  out := A.out

theorem core_toAdaptive : A.core.toAdaptive A.budget = A :=
  rfl

/-- Decidable equality of the registers of `A^Π`, built in steps (one instance search for the
whole product exceeds the default size limit of instance search). -/
instance instDecidableEqDRegCopy : DecidableEq (DReg (A.W × A.W) A.width X Y Req Resp) :=
  haveI : DecidableEq (A.W × A.W) := inferInstance
  haveI : DecidableEq ((A.W × A.W) × Req × Option Resp) := inferInstance
  inferInstance

/-- A vector of `A`'s registers with the copy register of `A^Π` at `c`. -/
noncomputable def copyVec (v : QState (DReg A.W A.width X Y Req Resp)) (c : A.W) :
    QState (DReg (A.W × A.W) A.width X Y Req Resp) :=
  WithLp.toLp 2 fun r => if (A.copySplit r).2 = c then v (A.copySplit r).1 else 0

/-- An operator of `A`'s registers acting on the registers of `A^Π`, the identity on the copy
register. -/
noncomputable def copyMat
    (U : Matrix (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp) ℂ) :
    Matrix (DReg (A.W × A.W) A.width X Y Req Resp) (DReg (A.W × A.W) A.width X Y Req Resp) ℂ :=
  (U ⊗ₖ (1 : Matrix A.W A.W ℂ)).submatrix A.copySplit A.copySplit

theorem liftCopy_pureAt {R : Type} [Fintype R]
    {K : KrausMap R (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp)} {r₀ : R}
    {U : Matrix (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp) ℂ}
    (h : K.PureAt r₀ U) : (A.liftCopy K).PureAt r₀ (A.copyMat U) :=
  (h.tensorId A.W).reindex A.copySplit.symm

theorem matApply_copyMat
    (U : Matrix (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp) ℂ)
    (v : QState (DReg A.W A.width X Y Req Resp)) (c : A.W) :
    matApply (A.copyMat U) (A.copyVec v c) = A.copyVec (matApply U v) c := by
  ext r
  rw [matApply_apply]
  refine (Fintype.sum_equiv A.copySplit _ (fun p => A.copyMat U r (A.copySplit.symm p) *
    A.copyVec v c (A.copySplit.symm p)) fun i => by simp).trans ?_
  rw [Fintype.sum_prod_type]
  simp only [copyMat, submatrix_apply, Equiv.apply_symm_apply, kroneckerMap_apply, copyVec,
    PiLp.toLp_apply]
  by_cases hc : (A.copySplit r).2 = c
  · simp only [hc, ↓reduceIte, matApply_apply]
    refine sum_congr rfl fun d _ => ?_
    rw [Finset.sum_eq_single c (fun c' _ hc' => by simp [hc']) (by simp)]
    simp [one_apply, hc]
  · simp only [hc, ↓reduceIte]
    refine sum_eq_zero fun d _ => sum_eq_zero fun c' _ => ?_
    by_cases hcc : c' = c
    · subst hcc
      simp [one_apply, hc]
    · simp [hcc]

variable [AddGroup Y] in
theorem permOp_queryPerm_copyVec (H : X → Y) (v : QState (DReg A.W A.width X Y Req Resp))
    (c : A.W) :
    permOp (queryPerm H) (A.copyVec v c) = A.copyVec (permOp (queryPerm H) v) c := by
  ext r
  rfl

/-- **The copy of the output** writes the representative `c` into the blank copy register, on a
vector whose workspaces all have the representative `c`. -/
theorem permOp_copyOut_copyVec (v : QState (DReg A.W A.width X Y Req Resp)) {c : A.W}
    (hc : ∀ d, v d ≠ 0 → A.outRep d.1.1 = c) :
    permOp A.copyOut (A.copyVec v A.copyBlank) = A.copyVec v c := by
  ext r
  obtain ⟨⟨⟨w, c'⟩, req, resp⟩, qs⟩ := r
  have hs : A.copyOut.symm (((w, c'), req, resp), qs) =
      (((w, Equiv.swap A.copyBlank (A.outRep w) c'), req, resp), qs) := rfl
  rw [permOp_apply, hs]
  simp only [copyVec, copySplit, Equiv.coe_fn_mk, PiLp.toLp_apply]
  by_cases hv : v ((w, req, resp), qs) = 0
  · simp [hv]
  · have hw := hc _ hv
    simp only at hw
    simp only [hw, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
    exact if_congr Iff.rfl rfl rfl

/-- The operator of the Kraus maps of `A^Π`, from those of `A` (`U`) and of the test (`V`). -/
noncomputable def withTestMat (T : A.QTest)
    (U : StepIdx A.slots A.post →
      Matrix (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp) ℂ)
    (V : Fin (T.batches + 1) →
      Matrix (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp) ℂ)
    (k : StepIdx A.slots (A.post + T.batches)) :
    Matrix (DReg (A.W × A.W) A.width X Y Req Resp) (DReg (A.W × A.W) A.width X Y Req Resp) ℂ :=
  if h : (k : ℕ) < A.slots + A.post then A.copyMat (U ⟨k, by omega⟩)
  else if (k : ℕ) = A.slots + A.post then
    A.copyMat (V 0) * (A.copyMat (U lastStep)).submatrix A.copyOut.symm (Equiv.refl _)
  else A.copyMat (V ⟨k - (A.slots + A.post), by omega⟩)

/-- **The Kraus maps of `A^Π` have one operator** when those of `A` and of the test do. -/
theorem withTestStep_pureAt (T : A.QTest)
    {U : StepIdx A.slots A.post →
      Matrix (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp) ℂ}
    {V : Fin (T.batches + 1) →
      Matrix (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp) ℂ}
    (hU : ∀ k, ∃ r₀, (A.step k).PureAt r₀ (U k))
    (hV : ∀ b, ∃ r₀, (T.step b).toKrausMap.PureAt r₀ (V b))
    (k : StepIdx A.slots (A.post + T.batches)) :
    ∃ r₀, (withTestStep T k).PureAt r₀ (A.withTestMat T U V k) := by
  unfold withTestStep withTestMat
  split_ifs with h1 h2
  · obtain ⟨r, hr⟩ := hU ⟨k, by omega⟩
    exact ⟨_, (A.liftCopy_pureAt hr).embedIdx (A.embA T.R)⟩
  · obtain ⟨r, hr⟩ := hU lastStep
    obtain ⟨s, hs⟩ := hV 0
    exact ⟨_, ((A.liftCopy_pureAt hs).comp
      ((A.liftCopy_pureAt hr).permConj (Equiv.refl _) A.copyOut)).embedIdx (A.embAT T.R)⟩
  · obtain ⟨s, hs⟩ := hV ⟨k - (A.slots + A.post), by omega⟩
    exact ⟨_, (A.liftCopy_pureAt hs).embedIdx (A.embT T.R)⟩

/-- **The initial state of `A^Π` is pure** when `A`'s is: `A`'s vector with the blank copy. -/
theorem withTest_init_of_proj {ψ : QState (DReg A.W A.width X Y Req Resp)}
    (hinit : A.init.mat = proj ψ) :
    (MState.reindex A.copySplit.symm (A.init.tensorKet A.copyBlank)).mat =
      proj (A.copyVec ψ A.copyBlank) := by
  ext r s
  obtain ⟨⟨⟨w, cr⟩, req, resp⟩, qs⟩ := r
  obtain ⟨⟨⟨w', cs⟩, req', resp'⟩, qs'⟩ := s
  simp only [MState.reindex, MState.tensorKet_mat, Equiv.symm_symm, submatrix_apply, hinit,
    kroneckerMap_apply, proj, vecMulVec_apply, copyVec, copySplit, Equiv.coe_fn_mk,
    PiLp.toLp_apply, Matrix.single_apply]
  by_cases h1 : cr = A.copyBlank <;> by_cases h2 : cs = A.copyBlank <;> simp [h1, h2, eq_comm]

variable [AddGroup Y]

/-- **The slots of `A^Π` act as `A`'s slots** on vectors with a fixed copy register. -/
theorem foldl_pureSlot_withTest (T : A.QTest)
    (U : StepIdx A.slots A.post →
      Matrix (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp) ℂ)
    (V : Fin (T.batches + 1) →
      Matrix (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp) ℂ)
    (H : X → Y) (c : A.W) :
    ∀ (l : List (Fin A.slots)) (v : QState (DReg A.W A.width X Y Req Resp)),
      l.foldl ((A.withTest T).core.pureSlot (A.withTestMat T U V) H) (A.copyVec v c) =
        A.copyVec (l.foldl (A.core.pureSlot U H) v) c
  | [], _ => rfl
  | k :: l, v => by
    have hk : (k : ℕ) < A.slots + A.post := by omega
    have h1 : (A.withTest T).core.pureSlot (A.withTestMat T U V) H (A.copyVec v c) k =
        A.copyVec (A.core.pureSlot U H v k) c := by
      show permOp (queryPerm H) (matApply (A.withTestMat T U V ⟨k, by omega⟩)
        (A.copyVec v c)) = _
      simp only [withTestMat, hk, ↓reduceDIte]
      rw [matApply_copyMat, permOp_queryPerm_copyVec]
      rfl
    exact (congrArg (fun u => List.foldl ((A.withTest T).core.pureSlot (A.withTestMat T U V) H)
      u l) h1).trans (foldl_pureSlot_withTest T U V H c l _)

end AdaptiveIAlg

/-! ### Tests of a fixed-schedule adversary as tests of its embedding -/

namespace IAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (A : IAlg X Y Req Resp O)

/-- An operator of `A`'s registers acting on the registers with the slot counter, the identity on
the counter. -/
noncomputable def cntLift
    (V : Matrix (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp) ℂ) :
    Matrix (DReg (A.W × Fin (A.slots + 1)) A.width X Y Req Resp)
      (DReg (A.W × Fin (A.slots + 1)) A.width X Y Req Resp) ℂ :=
  (V ⊗ₖ (1 : Matrix (Fin (A.slots + 1)) (Fin (A.slots + 1)) ℂ)).submatrix A.cntSplit A.cntSplit

theorem matApply_cntLift
    (V : Matrix (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp) ℂ)
    (v : QState (DReg A.W A.width X Y Req Resp)) (c : Fin (A.slots + 1)) :
    matApply (A.cntLift V) (A.liftCnt v c) = A.liftCnt (matApply V v) c := by
  ext r
  rw [matApply_apply]
  refine (Fintype.sum_equiv A.cntSplit _ (fun p => A.cntLift V r (A.cntSplit.symm p) *
    A.liftCnt v c (A.cntSplit.symm p)) fun i => by simp).trans ?_
  rw [Fintype.sum_prod_type]
  simp only [cntLift, submatrix_apply, Equiv.apply_symm_apply, kroneckerMap_apply, liftCnt,
    PiLp.toLp_apply]
  by_cases hc : (A.cntSplit r).2 = c
  · simp only [hc, ↓reduceIte, matApply_apply]
    refine sum_congr rfl fun d _ => ?_
    rw [Finset.sum_eq_single c (fun c' _ hc' => by simp [hc']) (by simp)]
    simp [one_apply, hc]
  · simp only [hc, ↓reduceIte]
    refine sum_eq_zero fun d _ => sum_eq_zero fun c' _ => ?_
    by_cases hcc : c' = c
    · subst hcc
      simp [one_apply, hc]
    · simp [hcc]

/-- **A residual-state test of `A` as a test of its embedding** `A.toAdaptive`: the same channels,
acting on `A`'s registers with the slot counter left alone, the same batches and the outcome read
from `A`'s part of the workspace. -/
noncomputable def QTest.toAdaptive {A : IAlg X Y Req Resp O} (T : A.QTest) :
    A.toAdaptive.QTest where
  batches := T.batches
  R := T.R
  step b := ((T.step b).tensorIdK (Fin (A.slots + 1))).reindexK A.cntSplit.symm
  ok w := T.ok w.1

theorem QTest.queries_toAdaptive {A : IAlg X Y Req Resp O} (T : A.QTest) :
    T.toAdaptive.queries = T.queries :=
  rfl

/-- **The channels of the lifted test have one operator** when those of the test do. -/
theorem QTest.toAdaptive_step_pureAt {A : IAlg X Y Req Resp O} (T : A.QTest) {b : Fin (T.batches + 1)}
    {r₀ : T.R} {V : Matrix (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp) ℂ}
    (h : (T.step b).toKrausMap.PureAt r₀ V) :
    (T.toAdaptive.step b).toKrausMap.PureAt r₀ (A.cntLift V) :=
  (h.tensorId (Fin (A.slots + 1))).reindex A.cntSplit.symm

end IAlg

end GordieHowe.Quantum
