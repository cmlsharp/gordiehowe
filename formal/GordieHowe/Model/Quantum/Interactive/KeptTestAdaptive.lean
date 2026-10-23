-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.KeptTest
public import GordieHowe.Model.Quantum.Interactive.EmbedPure

@[expose] public section

/-!
# The test of the kept registers for the embedded compiled program

The test of the kept registers (`OracleProg.keptTest`, `GordieHowe/Model/Quantum/Interactive/KeptTest.lean`) as a
test of the compiled program's embedding into the adversaries with run-time kinds
(`IAlg.QTest.toAdaptive`, `IAlg.toAdaptive`), and the pure run of the embedding followed by it
(`OracleProg.pureRun_withTest_keptTest_toAdaptive`): the counter after the slots, the copy
register holding the representative of the output, the table the answers of `H`, the query pair
the padded query `q`, and the kept pair the basis state `i₀`.
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.Quantum

namespace OracleProg

open GordieHowe.OracleProg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [AddCommGroup Y]
  [Nonempty Req] (p : OracleProg X Y O) (q : ℕ) (pad : X)

set_option hygiene false in
/-- The compiled program, in the proofs below. -/
local notation "𝔸" => toIAlg (Req := Req) (Resp := Resp) p q pad φ hφ

set_option hygiene false in
/-- The lifted test, in the proofs below. -/
local notation "𝕋" => (keptTest (Req := Req) (Resp := Resp) p q pad φ hφ i₀).toAdaptive

/-- **The pure run of the embedded compiled program followed by the lifted test** against `H`:
the counter after the slots, the copy register holding the representative of the output (read
from the table of answers), the table the answers of `H`, the query pair the padded query `q`, and
the kept pair the basis state `i₀`. -/
theorem pureRun_withTest_keptTest_toAdaptive (H : X → Y) (φ : QState (X × Y)) (hφ : ‖φ‖ = 1)
    (i₀ : X × Y) :
    ((toIAlg (Req := Req) (Resp := Resp) p q pad φ hφ).toAdaptive.withTest
      (keptTest p q pad φ hφ i₀).toAdaptive).core.pureRun
      ((toIAlg p q pad φ hφ).toAdaptive.withTestMat (keptTest p q pad φ hφ i₀).toAdaptive
        (fun k => (toIAlg p q pad φ hφ).cntMat
          ((1 : Matrix _ _ ℂ).submatrix (stepPerm p q pad k).symm (Equiv.refl _)) k)
        (fun b => (toIAlg p q pad φ hφ).cntLift (keptTestMat q φ hφ i₀ b))) H
      ((toIAlg p q pad φ hφ).toAdaptive.copyVec
        ((toIAlg p q pad φ hφ).liftCnt (initVec p q pad φ) 0)
        (toIAlg p q pad φ hφ).toAdaptive.copyBlank) =
      (toIAlg p q pad φ hφ).toAdaptive.copyVec
        ((toIAlg p q pad φ hφ).liftCnt
          (regVec q (tab p q pad H q) (xs p pad H q, 0) (EuclideanSpace.single i₀ 1))
          (toIAlg p q pad φ hφ).cntFinal)
        ((toIAlg p q pad φ hφ).toAdaptive.outRep
          ((tab p q pad H q, i₀), (toIAlg p q pad φ hφ).cntFinal)) := by
  have hslots : (𝔸).toAdaptive.slots = q + 1 := rfl
  have hpost : (𝔸).toAdaptive.post = 0 := rfl
  have hbatches : (𝕋).batches = 1 := rfl
  have hslots' : (𝔸).slots = q + 1 := rfl
  have hpost' : (𝔸).post = 0 := rfl
  set U : StepIdx (𝔸).slots (𝔸).post → Matrix (DReg (𝔸).W (𝔸).width X Y Req Resp)
      (DReg (𝔸).W (𝔸).width X Y Req Resp) ℂ :=
    fun k => (1 : Matrix _ _ ℂ).submatrix (stepPerm p q pad k).symm (Equiv.refl _)
  set U' : StepIdx (𝔸).toAdaptive.slots (𝔸).toAdaptive.post →
      Matrix (DReg (𝔸).toAdaptive.W (𝔸).toAdaptive.width X Y Req Resp)
        (DReg (𝔸).toAdaptive.W (𝔸).toAdaptive.width X Y Req Resp) ℂ :=
    fun k => (𝔸).cntMat (U k) k
  set V' : Fin ((𝕋).batches + 1) →
      Matrix (DReg (𝔸).toAdaptive.W (𝔸).toAdaptive.width X Y Req Resp)
        (DReg (𝔸).toAdaptive.W (𝔸).toAdaptive.width X Y Req Resp) ℂ :=
    fun b => (𝔸).cntLift (keptTestMat q φ hφ i₀ b)
  set ψ₀ : QState (DReg (𝔸).toAdaptive.W (𝔸).toAdaptive.width X Y Req Resp) :=
    (𝔸).liftCnt (initVec p q pad φ) 0
  have hA : (𝔸).toAdaptive.core.pureRun U' H ψ₀ =
      (𝔸).liftCnt (progVec q H φ (tab p q pad H q) (xs p pad H q, 0)) (𝔸).cntFinal :=
    ((𝔸).pureRun_toKindAlg U H _).trans
      (congrArg ((𝔸).liftCnt · _) (pureRun_toIAlg p q pad H φ hφ))
  have hA' : (𝔸).toAdaptive.core.pureRun U' H ψ₀ = matApply (U' lastStep)
      (List.foldl ((𝔸).toAdaptive.core.pureSlot U' H) ψ₀ (List.finRange (𝔸).toAdaptive.slots)) := by
    unfold KindAlg.pureRun
    rfl
  have hS := (𝔸).toAdaptive.foldl_pureSlot_withTest 𝕋 U' V' H (𝔸).toAdaptive.copyBlank
    (List.finRange (𝔸).toAdaptive.slots) ψ₀
  have hc : ∀ d, (𝔸).liftCnt (progVec (Req := Req) (Resp := Resp) q H φ (tab p q pad H q)
      (xs p pad H q, 0)) (𝔸).cntFinal d ≠ 0 →
      (𝔸).toAdaptive.outRep d.1.1 = (𝔸).toAdaptive.outRep ((tab p q pad H q, i₀), (𝔸).cntFinal) := by
    intro d hd
    refine (𝔸).toAdaptive.outRep_eq_of_out_eq ?_
    have hd' : progVec (Req := Req) (Resp := Resp) q H φ (tab p q pad H q) (xs p pad H q, 0)
        ((𝔸).cntSplit d).1 ≠ 0 := by
      intro h0
      apply hd
      simp only [IAlg.liftCnt, PiLp.toLp_apply]
      split_ifs <;> simp [h0]
    have hT : ((𝔸).cntSplit d).1.1.1.1 = tab p q pad H q := progVec_ne_zero q hd'
    show (OracleProgAns.result p (answers q d.1.1.1.1 q)).getD (p.run 0) =
      (OracleProgAns.result p (answers q (tab p q pad H q) q)).getD (p.run 0)
    rw [show d.1.1.1.1 = ((𝔸).cntSplit d).1.1.1.1 from rfl, hT]
  have hj : (𝔸).toAdaptive.withTestMat 𝕋 U' V' ⟨q + 1 + 0, by omega⟩ =
      (𝔸).toAdaptive.copyMat (V' 0) *
        ((𝔸).toAdaptive.copyMat (U' lastStep)).submatrix (𝔸).toAdaptive.copyOut.symm
          (Equiv.refl _) := by
    have h1 : (q + 1 + 0 < (𝔸).toAdaptive.slots + (𝔸).toAdaptive.post) = False :=
      eq_false (by omega)
    have h2 : (q + 1 + 0 = (𝔸).toAdaptive.slots + (𝔸).toAdaptive.post) = True :=
      eq_true (by omega)
    simp only [AdaptiveIAlg.withTestMat, h1, h2, ↓reduceDIte, ↓reduceIte]
  have hl : (𝔸).toAdaptive.withTestMat 𝕋 U' V' ⟨q + 1 + 1, by omega⟩ =
      (𝔸).toAdaptive.copyMat (V' 1) := by
    have h1 : (q + 1 + 1 < (𝔸).toAdaptive.slots + (𝔸).toAdaptive.post) = False :=
      eq_false (by omega)
    have h2 : (q + 1 + 1 = (𝔸).toAdaptive.slots + (𝔸).toAdaptive.post) = False :=
      eq_false (by omega)
    simp only [AdaptiveIAlg.withTestMat, h1, h2, ↓reduceDIte, ↓reduceIte]
    congr 2
    exact Fin.ext (by change q + 1 + 1 - (q + 1 + 0) = 1; omega)
  unfold KindAlg.pureRun
  erw [hS]
  show matApply ((𝔸).toAdaptive.withTestMat 𝕋 U' V' ⟨q + 1 + 1, by omega⟩)
    (List.foldl (fun v (b : Fin 1) => permOp (queryPerm H)
      (matApply ((𝔸).toAdaptive.withTestMat 𝕋 U' V' ⟨q + 1 + b, by omega⟩) v))
      ((𝔸).toAdaptive.copyVec (List.foldl ((𝔸).toAdaptive.core.pureSlot U' H) ψ₀
        (List.finRange (𝔸).toAdaptive.slots)) (𝔸).toAdaptive.copyBlank) (List.finRange 1)) = _
  rw [show List.finRange 1 = [0] from rfl, List.foldl_cons, List.foldl_nil]
  show matApply ((𝔸).toAdaptive.withTestMat 𝕋 U' V' ⟨q + 1 + 1, by omega⟩) (permOp (queryPerm H)
    (matApply ((𝔸).toAdaptive.withTestMat 𝕋 U' V' ⟨q + 1 + 0, by omega⟩) ((𝔸).toAdaptive.copyVec
      (List.foldl ((𝔸).toAdaptive.core.pureSlot U' H) ψ₀
        (List.finRange (𝔸).toAdaptive.slots)) (𝔸).toAdaptive.copyBlank))) = _
  rw [hj, hl, matApply_mul, matApply_submatrix_perm, AdaptiveIAlg.matApply_copyMat]
  erw [← hA']
  rw [hA, (𝔸).toAdaptive.permOp_copyOut_copyVec _ hc]
  erw [AdaptiveIAlg.matApply_copyMat, AdaptiveIAlg.permOp_queryPerm_copyVec,
    AdaptiveIAlg.matApply_copyMat]
  simp only [V']
  congr 1
  set v := progVec (Req := Req) (Resp := Resp) q H φ (tab p q pad H q) (xs p pad H q, 0)
  have e0 := (𝔸).matApply_cntLift (keptTestMat q φ hφ i₀ 0) v (𝔸).cntFinal
  have e1 := (𝔸).permOp_queryPerm_liftCnt H (matApply (keptTestMat q φ hφ i₀ 0) v) (𝔸).cntFinal
  have e2 := (𝔸).matApply_cntLift (keptTestMat q φ hφ i₀ 1)
    (permOp (queryPerm H) (matApply (keptTestMat q φ hφ i₀ 0) v)) (𝔸).cntFinal
  have e3 := keptTest_run (Req := Req) (Resp := Resp) (q := q) H φ hφ i₀ (tab p q pad H q)
    (xs p pad H q)
  exact (congrArg (fun z => matApply ((𝔸).cntLift (keptTestMat q φ hφ i₀ 1))
    (permOp (queryPerm H) z)) e0).trans ((congrArg (fun z =>
      matApply ((𝔸).cntLift (keptTestMat q φ hφ i₀ 1)) z) e1).trans
        (e2.trans (congrArg ((𝔸).liftCnt · (𝔸).cntFinal) e3)))

/-- **The final vector of the embedding is one basis state**: the copy register at `c`, the table
`T`, the kept pair at `i₀`, the counter at `n`, the blank request and response, the query pair at
`qp`. -/
theorem norm_copyVec_liftCnt_regVec_single_sq (φ : QState (X × Y)) (hφ : ‖φ‖ = 1)
    (T : Fin q → Y) (qp i₀ : X × Y) (n : Fin ((𝔸).slots + 1)) (c : (𝔸).toAdaptive.W)
    (d : DReg ((𝔸).toAdaptive.W × (𝔸).toAdaptive.W) (𝔸).toAdaptive.width X Y Req Resp) :
    ‖(𝔸).toAdaptive.copyVec ((𝔸).liftCnt (regVec q T qp (EuclideanSpace.single i₀ 1)) n) c d‖ ^ 2 =
      if d = (𝔸).toAdaptive.copySplit.symm
        ((𝔸).cntSplit.symm ((((T, i₀), (req₀, none)), fun _ => qp), n), c) then 1 else 0 := by
  have hd : (𝔸).toAdaptive.copySplit.symm
      ((𝔸).cntSplit.symm ((((T, i₀), (req₀, none)), fun _ => qp), n), c) =
      (show DReg ((𝔸).toAdaptive.W × (𝔸).toAdaptive.W) (𝔸).toAdaptive.width X Y Req Resp from
        (((((T, i₀), n), c), (req₀, none)), fun _ => qp)) := rfl
  rw [hd]
  obtain ⟨⟨⟨⟨⟨T', k⟩, n'⟩, c'⟩, rq⟩, qs⟩ := d
  simp only [AdaptiveIAlg.copyVec, AdaptiveIAlg.copySplit, IAlg.liftCnt, IAlg.cntSplit, regVec,
    Equiv.coe_fn_mk, PiLp.toLp_apply, PiLp.single_apply]
  by_cases h : c' = c ∧ n' = n ∧ T' = T ∧ rq = (req₀, none) ∧
      (show Fin 1 → X × Y from qs) 0 = qp ∧ k = i₀
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    have hq : qs = fun _ => qp := funext fun j => by rw [Fin.fin_one_eq_zero (j : Fin 1), h5]
    subst h1 h2 h3 h4 h6 hq
    simp
  · have hne : ¬ (show DReg ((𝔸).toAdaptive.W × (𝔸).toAdaptive.W) (𝔸).toAdaptive.width X Y Req Resp
        from (((((T', k), n'), c'), rq), qs)) = (((((T, i₀), n), c), (req₀, none)), fun _ => qp) := by
      intro he
      cases he
      exact h ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    split_ifs with hx <;> first
      | exact absurd hx hne
      | (simp_all <;> exact (hne rfl).elim)

end OracleProg

end GordieHowe.Quantum
