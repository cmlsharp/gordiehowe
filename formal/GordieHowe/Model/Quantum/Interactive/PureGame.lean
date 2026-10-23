-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.Bridge
public import GordieHowe.Model.Quantum.Pure.Bridge

@[expose] public section

/-!
# The dilated adversary and the pure game

`KindAlg.acceptProbAt_dilate`: the mixed game of an adversary with a kind register
(`GordieHowe/Model/Quantum/Interactive/Pure.lean`) without the request measurement is the pure game of
`GordieHowe/Model/Quantum/Pure/Game.lean` for the dilated adversary (`Quantum.KindAlg.dilate`) against the
challenger as an environment (`Challenger.toPureEnv`). The dilation adds a halting flag to make
the adversary's Kraus maps trace-preserving (`KrausMap.complete`) and replaces each by its
Stinespring unitary (`MixedAlg.dilStep`); the post phase becomes the unitary
`Quantum.KindAlg.postOp`, which depends on the whole oracle in force. With the output law of the
composition (`KindAlg.outLaw_composeBoth_some`) and deferred measurement (`mgAccept_deph`,
`GordieHowe/Model/Quantum/Interactive/Pure.lean`) it gives `KindAlg.composeBoth_eq_pureGame`
(`GordieHowe/Model/Quantum/Interactive/Adaptive.lean`).

## Dilation with a permutation per step

`MixedAlg.hybrid_spec`: for a general oracle algorithm and any unitaries that agree with its
Stinespring unitaries on the states with clean ancilla registers, the run alternating them with a
sequence of basis permutations purifies the mixed run with the same permutations
(`MixedAlg.stageV`). This is `MixedAlg.dilRun_spec` with a permutation per step.
-/

open Finset Matrix
open scoped BigOperators ENNReal Kronecker ComplexOrder

namespace GordieHowe.Quantum

namespace MixedAlg

variable {Z ι R M : Type*} [Fintype ι] [DecidableEq ι] [Fintype R] [Fintype M] {d : ℕ}
  (G : MixedAlg Z ι d R M)

/-- **The run of `G` with the permutation `π k` at oracle step `k`.** -/
def stageV (π : ℕ → Equiv.Perm ι) (z : Z) : ℕ → MState ι
  | 0 => G.applyAt z 0 (G.init z)
  | k + 1 => G.applyAt z (k + 1) ((stageV π z k).permute (π k))

variable [Nonempty R] [Nonempty M]

/-- **Dilation with a permutation per step**: unitaries that act as the Stinespring unitaries of
`G` on vectors clean from the current step on, alternating with `π k × id`, purify the run of `G`
with the permutations `π k`. -/
theorem hybrid_spec (π : ℕ → Equiv.Perm ι) (z : Z)
    (U : ℕ → QState (ι × Anc ι d R M) ≃ₗᵢ[ℂ] QState (ι × Anc ι d R M))
    (hU : ∀ k ψ, CleanVec k ψ → U k ψ = G.dilStep z k ψ) (k : ℕ) :
    CleanVec (k + 1) (hybrid U (fun j => permOp (liftPerm (π j))) (G.dilInit z) k) ∧
      reduce (hybrid U (fun j => permOp (liftPerm (π j))) (G.dilInit z) k) =
        (G.stageV π z k).mat := by
  induction k with
  | zero =>
    rw [hybrid_zero, hU 0 _ (G.cleanVec_dilInit z)]
    obtain ⟨h1, h2⟩ := G.dilStep_spec z (G.cleanVec_dilInit z)
    exact ⟨h1, h2 _ (G.reduce_dilInit z)⟩
  | succ k ih =>
    have hc := ih.1.permOp (π k)
    rw [hybrid_succ, hU (k + 1) _ hc]
    obtain ⟨h1, h2⟩ := G.dilStep_spec z hc
    refine ⟨h1, h2 _ ?_⟩
    rw [liftPerm, reduce_permOp_prodCongr, ih.2]
    rfl

end MixedAlg

/-! ### Trace-preserving Kraus families on a factor -/

namespace KrausChannel

variable {R ι : Type*} [Fintype R] [Fintype ι] [DecidableEq ι]

/-- A Kraus family on the first factor, the identity on the second. -/
def tensorIdK (K : KrausChannel R ι ι) (L : Type*) [Fintype L] [DecidableEq L] :
    KrausChannel R (ι × L) (ι × L) where
  op r := K.op r ⊗ₖ (1 : Matrix L L ℂ)
  sum_conjTranspose_mul := by
    have h : ∑ r, (K.op r ⊗ₖ (1 : Matrix L L ℂ))ᴴ * (K.op r ⊗ₖ (1 : Matrix L L ℂ)) =
        (∑ r, (K.op r)ᴴ * K.op r) ⊗ₖ (1 : Matrix L L ℂ) := by
      rw [sum_kronecker]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
    rw [h, K.sum_conjTranspose_mul, one_kronecker_one]

/-- A Kraus family moved along a basis equivalence. -/
def reindexK {κ : Type*} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (K : KrausChannel R ι ι) :
    KrausChannel R κ κ where
  op r := (K.op r).submatrix e.symm e.symm
  sum_conjTranspose_mul := by
    have h : ∑ r, ((K.op r).submatrix e.symm e.symm)ᴴ * (K.op r).submatrix e.symm e.symm =
        (∑ r, (K.op r)ᴴ * K.op r).submatrix e.symm e.symm := by
      rw [submatrix_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [conjTranspose_submatrix, submatrix_mul_equiv]
    rw [h, K.sum_conjTranspose_mul, submatrix_one_equiv]

end KrausChannel

/-! ### Purification on a support -/

/-- The purification of a mixed state vanishes on the basis states where the mixed state has no
weight. -/
theorem purify_apply_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : MState ι) {i : ι}
    (hi : ρ.mat i i = 0) (a : ι) : purify ρ (i, a) = 0 := by
  have h := (exists_eq_conjTranspose_mul_self ρ.posSemidef).choose_spec
  set B := (exists_eq_conjTranspose_mul_self ρ.posSemidef).choose
  have hsum : ∑ a', Complex.normSq (B a' i) = 0 := by
    have := congrFun (congrFun h i) i
    rw [hi, Matrix.mul_apply] at this
    have h2 := congrArg Complex.re this
    simp only [Complex.zero_re, Complex.re_sum, Matrix.conjTranspose_apply] at h2
    rw [h2]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Complex.normSq_apply]
    simp [Complex.mul_re]
  have hz : B a i = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun a' _ => Complex.normSq_nonneg (B a' i)).1 hsum a
      (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.1 this
  simp [purify, B, hz]

/-! ### The dilated adversary -/

instance {W : Type} {n : ℕ} {X Y Req A : Type} [DecidableEq W] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Req] [DecidableEq A] : DecidableEq (DReg W n X Y Req A × Bool) :=
  @instDecidableEqProd _ _ inferInstance inferInstance

instance {W : Type} {n : ℕ} {X Y Req A : Type} {m : ℕ} [DecidableEq W] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Req] [DecidableEq A] :
    DecidableEq ((DReg W n X Y Req A × Bool) × LogReg Req m) :=
  @instDecidableEqProd _ _ inferInstance inferInstance

instance {W : Type} {n : ℕ} {X Y Req A : Type} {m : ℕ} [DecidableEq W] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Req] [DecidableEq A] :
    DecidableEq (GameReg W n X Y Req A m × Bool) :=
  @instDecidableEqProd _ _ inferInstance inferInstance

/-! ### Permutations controlled by a flag -/

/-- The basis permutation of `ι × Bool` that applies `πF` at flag `false` and `πT` at flag
`true`, leaving the flag unchanged. -/
def flagPerm {ι : Type*} (πF πT : Equiv.Perm ι) : Equiv.Perm (ι × Bool) where
  toFun p := (cond p.2 (πT p.1) (πF p.1), p.2)
  invFun p := (cond p.2 (πT.symm p.1) (πF.symm p.1), p.2)
  left_inv p := by obtain ⟨i, b⟩ := p; cases b <;> simp
  right_inv p := by obtain ⟨i, b⟩ := p; cases b <;> simp

@[simp] theorem flagPerm_false {ι : Type*} (πF πT : Equiv.Perm ι) (i : ι) :
    flagPerm πF πT (i, false) = (πF i, false) :=
  rfl

@[simp] theorem flagPerm_true {ι : Type*} (πF πT : Equiv.Perm ι) (i : ι) :
    flagPerm πF πT (i, true) = (πT i, true) :=
  rfl

theorem flagPerm_symm_false {ι : Type*} (πF πT : Equiv.Perm ι) (i : ι) :
    (flagPerm πF πT).symm (i, false) = (πF.symm i, false) :=
  rfl

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] (A : KindAlg X Y Req Resp O)

/-- The game registers with the halting flag. -/
abbrev GB := A.G × Bool

/-- The game registers with the flag as the adversary's registers with the flag, and the logs. -/
def flagSplit : (DReg A.W A.width X Y Req Resp × Bool) × LogReg Req A.slots ≃ A.GB where
  toFun p := (splitLogs.symm (p.1.1, p.2), p.1.2)
  invFun q := (((splitLogs q.1).1, q.2), (splitLogs q.1).2)
  left_inv p := by simp
  right_inv q := by simp

/-- **The adversary's Kraus map number `k` with the halting flag, on the game registers**: the
completion of `A.step k` (`KrausMap.complete`), the identity on the logs. -/
noncomputable def gStep (k : StepIdx A.slots A.post) : KrausChannel (A.R ⊕ Bool) A.GB A.GB :=
  (((A.step k).complete).tensorIdK (LogReg Req A.slots)).reindexK A.flagSplit

/-- The operators of `gStep` are the lifted operators of the completion. -/
theorem gStep_op (k : StepIdx A.slots A.post) (x : A.R ⊕ Bool) :
    (A.gStep k).op x = (match x with
      | .inl r => (A.liftG k).op r ⊗ₖ Matrix.single false false 1
      | .inr false => (((A.step k).haltOp ⊗ₖ (1 : Matrix (LogReg Req A.slots) _ ℂ)).submatrix
          splitLogs splitLogs) ⊗ₖ Matrix.single true false 1
      | .inr true => (1 : Matrix A.G A.G ℂ) ⊗ₖ Matrix.single true true 1) := by
  ext ⟨g, b⟩ ⟨g', b'⟩
  rcases x with r | _ | _ <;>
    simp [gStep, KrausChannel.reindexK, KrausChannel.tensorIdK, KrausMap.complete, KrausMap.completeOp,
      flagSplit, liftG, KrausMap.reindex, KrausMap.tensorId, kroneckerMap_apply, Matrix.one_apply,
      Matrix.single_apply] <;> split_ifs <;> simp_all
  all_goals exact absurd (splitLogs.injective (Prod.ext (by assumption) (by assumption))) (by assumption)

/-- **The completed step acts as the adversary's Kraus map on the block at flag `false`.** -/
theorem ffBlock_gStep_apply (k : StepIdx A.slots A.post) (ρ : Matrix A.GB A.GB ℂ) :
    KrausMap.ffBlock ((A.gStep k) ρ) = (A.liftG k) (KrausMap.ffBlock ρ) := by
  rw [KrausChannel.apply, KrausMap.ffBlock, submatrix_sum, Fintype.sum_sum_type, Fintype.sum_bool]
  simp only [gStep_op, KrausMap.ffBlock_kronecker_single_mul]
  simp [KrausMap.apply, KrausMap.ffBlock]

/-- The trivial final measurement: one outcome. -/
def _root_.GordieHowe.Quantum.KrausChannel.trivial (ι : Type*) [Fintype ι] [DecidableEq ι] : KrausChannel Unit ι ι where
  op _ := 1
  sum_conjTranspose_mul := by simp

variable [AddGroup Y] {Ω St : Type} {Q : ℕ} [OracleState St X Y] (E : Env Ω Req Resp X Y Q St)

/-- The initial state of the mixed game as a mixed state. -/
def mgInitM : MState A.G :=
  MState.reindex splitLogs.symm (A.init.tensorKet (fun _ => none : LogReg Req A.slots))

/-- The basis permutation at oracle step `k` of the mixed game: the events of slot `k`, then the
post-phase queries. -/
def evPerm (ω : Ω) (k : ℕ) : Equiv.Perm A.G :=
  if h : k < A.slots then
    (A.copyG ⟨k, h⟩).trans ((A.respG E ω ⟨k, h⟩).trans (E.oraclePerm A.kind ω))
  else A.postG E ω

/-- The basis permutation at oracle step `k` on a halted branch: the events of slot `k` with every
branch requesting (the dilated distinguisher reads the halting flag as a request, `dilate`), then
the post-phase queries. -/
def evPermH (ω : Ω) (k : ℕ) : Equiv.Perm A.G :=
  if h : k < A.slots then
    (E.requestPerm (fun _ => true) ω ⟨k, h⟩).trans (E.oraclePerm (fun _ => true) ω)
  else A.postG E ω

/-- The basis permutation at oracle step `k` of the mixed game with the halting flag: `evPerm k`
at flag `false`, `evPermH k` at flag `true`. -/
def evPermB (ω : Ω) (k : ℕ) : Equiv.Perm A.GB :=
  flagPerm (A.evPerm E ω k) (A.evPermH E ω k)

/-- **The mixed game with the halting flag** as a general oracle algorithm on the game registers:
the completed Kraus maps (`gStep`) and, at oracle step `k`, the permutation `evPermB k`. -/
noncomputable def gameMixed :
    MixedAlg Unit A.GB (A.slots + A.post) (A.R ⊕ Bool) Unit where
  init _ := A.mgInitM.tensorKet false
  step _ k := A.gStep k
  meas _ := KrausChannel.trivial _

/-- The adversary's Kraus map number `k` on the game registers, indexed by `ℕ`. -/
def gK (k : ℕ) (ρ : Matrix A.G A.G ℂ) : Matrix A.G A.G ℂ :=
  if h : k < A.slots + A.post + 1 then (A.liftG ⟨k, h⟩) ρ else ρ

/-- The mixed game just before the adversary's Kraus map number `k`. -/
def mgU (ω : Ω) : ℕ → Matrix A.G A.G ℂ
  | 0 => A.mgInitM.mat
  | k + 1 => (A.gK k (mgU ω k)).submatrix (A.evPerm E ω k).symm (A.evPerm E ω k).symm

theorem mgRun_false_eq (ω : Ω) :
    A.mgRun E ω false = A.gK (A.slots + A.post) (A.mgU E ω (A.slots + A.post)) := by
  have hslots : ∀ (l : List (Fin A.slots)) (j : ℕ), l.map Fin.val = List.range' j l.length →
      (Circuit.concat (l.map fun k : Fin A.slots =>
        Circuit.kraus (A.liftG (slotStep k)) (A.eventCirc E ω k false))).run (Equiv.refl _)
          (A.mgU E ω j) = A.mgU E ω (j + l.length) := by
    intro l
    induction l with
    | nil => intro j _; rfl
    | cons k l ih =>
      intro j hl
      simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hl ⊢
      rw [Circuit.run_concat, ← hl.1]
      have hk : (Circuit.kraus (A.liftG (slotStep k)) (A.eventCirc E ω k false)).run (Equiv.refl _)
          (A.mgU E ω k) = A.mgU E ω (k + 1) := by
        simp only [eventCirc, Circuit.run, ↓reduceIte, Bool.false_eq_true, id, KrausMap.ofPerm_apply,
          submatrix_perm_submatrix_perm, mgU, gK, dif_pos (show (k : ℕ) < A.slots + A.post + 1 by omega),
          evPerm, dif_pos k.2, Equiv.trans_assoc]
      rw [hk, ih (k + 1) (by rw [hl.2, hl.1])]
      congr 1
      omega
  have hposts : ∀ (l : List (Fin A.post)) (j : ℕ), l.map Fin.val = List.range' j l.length →
      (Circuit.concat (l.map fun b : Fin A.post =>
        Circuit.kraus (A.liftG (postStep b))
          (.kraus (KrausMap.ofPerm (A.postG E ω)) .nil))).run (Equiv.refl _)
          (A.mgU E ω (A.slots + j)) = A.mgU E ω (A.slots + j + l.length) := by
    intro l
    induction l with
    | nil => intro j _; rfl
    | cons b l ih =>
      intro j hl
      simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hl ⊢
      rw [Circuit.run_concat, ← hl.1]
      have hb : (Circuit.kraus (A.liftG (postStep b))
          (.kraus (KrausMap.ofPerm (A.postG E ω)) .nil)).run (Equiv.refl _)
          (A.mgU E ω (A.slots + b)) = A.mgU E ω (A.slots + b + 1) := by
        simp only [Circuit.run, KrausMap.ofPerm_apply, mgU, gK,
          dif_pos (show A.slots + (b : ℕ) < A.slots + A.post + 1 by omega), evPerm,
          dif_neg (show ¬ (A.slots + (b : ℕ) < A.slots) by omega)]
      rw [hb, show A.slots + (b : ℕ) + 1 = A.slots + (b + 1) by omega, ih (b + 1) (by rw [hl.2, hl.1])]
      congr 1
      omega
  simp only [mgRun, mgCirc, Circuit.run_append]
  have hp := hposts (List.finRange A.post) 0 (by rw [List.map_coe_finRange_eq_range,
    List.range_eq_range', List.length_finRange])
  simp only [Nat.add_zero, List.length_finRange] at hp
  rw [show A.mgInit = A.mgU E ω 0 from rfl, hslots _ 0 (by rw [List.map_coe_finRange_eq_range,
    List.range_eq_range', List.length_finRange]), List.length_finRange, Nat.zero_add, hp]
  simp only [Circuit.run, gK, Nat.add_zero, dif_pos (show A.slots + A.post < A.slots + A.post + 1 by omega)]

theorem ffBlock_tensorKet_false (ρ : MState A.G) :
    KrausMap.ffBlock (ρ.tensorKet false).mat = ρ.mat := by
  ext g g'
  simp [KrausMap.ffBlock, MState.tensorKet_mat, kroneckerMap_apply]

/-- **The mixed game with the flag is the mixed game at flag `false`.** -/
theorem ffBlock_stageV (ω : Ω) (k : ℕ) :
    KrausMap.ffBlock ((A.gameMixed).stageV (fun j => A.evPermB E ω j) () k).mat =
      A.gK k (A.mgU E ω k) := by
  induction k with
  | zero =>
    simp only [MixedAlg.stageV, MixedAlg.applyAt, dif_pos (Nat.succ_pos _), KrausChannel.applyMState_mat,
      gameMixed]
    rw [ffBlock_gStep_apply, ffBlock_tensorKet_false]
    simp [gK, mgU]
  | succ k ih =>
    simp only [MixedAlg.stageV, MixedAlg.applyAt]
    by_cases hk : k + 1 < A.slots + A.post + 1
    · rw [dif_pos hk, KrausChannel.applyMState_mat,
        show A.gameMixed.step () ⟨k + 1, hk⟩ = A.gStep ⟨k + 1, hk⟩ from rfl, ffBlock_gStep_apply]
      have : KrausMap.ffBlock ((MixedAlg.stageV A.gameMixed
          (fun j => A.evPermB E ω j) () k).permute
            (A.evPermB E ω k)).mat =
          (A.gK k (A.mgU E ω k)).submatrix (A.evPerm E ω k).symm (A.evPerm E ω k).symm := by
        rw [← ih]
        rfl
      rw [this]
      simp [gK, mgU, dif_pos hk]
    · rw [dif_neg hk]
      have : KrausMap.ffBlock ((MixedAlg.stageV A.gameMixed
          (fun j => A.evPermB E ω j) () k).permute
            (A.evPermB E ω k)).mat =
          (A.gK k (A.mgU E ω k)).submatrix (A.evPerm E ω k).symm (A.evPerm E ω k).symm := by
        rw [← ih]
        rfl
      rw [this]
      simp [gK, mgU, dif_neg hk]

/-! #### The dilated distinguisher -/

/-- The ancilla of the dilation: a purifying copy of the game registers with the flag, one
register per Kraus map for its index (`MixedAlg.Anc`). -/
abbrev DAnc := MixedAlg.Anc A.GB (A.slots + A.post) (A.R ⊕ Bool) Unit

/-- The workspace of the dilated distinguisher: the adversary's workspace, the halting flag, the
ancilla. -/
abbrev DW := A.W × (Bool × A.DAnc)

/-- The adversary's registers with the flag and the ancilla, as the registers of the dilated
distinguisher. -/
def relD : (DReg A.W A.width X Y Req Resp × Bool) × A.DAnc ≃ DReg A.DW A.width X Y Req Resp where
  toFun p := (((p.1.1.1.1, (p.1.2, p.2)), p.1.1.1.2.1, p.1.1.1.2.2), p.1.1.2)
  invFun q := (((((q.1.1.1, q.1.2.1, q.1.2.2), q.2), q.1.1.2.1), q.1.1.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The dilated Kraus map number `k`**: the Stinespring unitary of the completed Kraus map on
the adversary's registers with the flag, on the register `k` of the ancilla. -/
noncomputable def uStep (k : ℕ) :
    QState ((DReg A.W A.width X Y Req Resp × Bool) × A.DAnc) ≃ₗᵢ[ℂ]
      QState ((DReg A.W A.width X Y Req Resp × Bool) × A.DAnc) :=
  if h : k < A.slots + A.post + 1 then
    stinespring (MixedAlg.stepSplit ⟨k, h⟩) (Classical.arbitrary (A.R ⊕ Bool))
      (A.step ⟨k, h⟩).complete
  else LinearIsometryEquiv.refl ℂ _

/-- The dilated Kraus map on the registers of the dilated distinguisher. -/
noncomputable def uStepD (k : ℕ) :
    QState (DReg A.DW A.width X Y Req Resp) ≃ₗᵢ[ℂ] QState (DReg A.DW A.width X Y Req Resp) :=
  ((Quantum.relabel A.relD).symm.trans (A.uStep k)).trans (Quantum.relabel A.relD)

/-- The game basis of the dilated distinguisher as the game registers with the flag and the
ancilla. -/
def relG : GameReg A.DW A.width X Y Req Resp A.slots ≃ A.GB × A.DAnc where
  toFun r := ((((r.1.1.1, r.1.2.1, r.1.2.2.1, r.1.2.2.2), r.2), r.1.1.2.1), r.1.1.2.2)
  invFun p := (((p.1.1.1.1, (p.1.2, p.2)), p.1.1.1.2.1, p.1.1.1.2.2.1, p.1.1.1.2.2.2), p.1.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The purified initial state of the mixed game with the flag vanishes off the blank logs. -/
theorem mgInitM_apply (g g' : A.G) :
    A.mgInitM.mat g g' = A.init.mat (splitLogs g).1 (splitLogs g').1 *
      (if (fun _ => none) = (splitLogs g).2 ∧ (fun _ => none) = (splitLogs g').2 then 1 else 0) := by
  simp only [mgInitM, MState.reindex, MState.tensorKet_mat, submatrix_apply, Equiv.symm_symm,
    kroneckerMap_apply, Matrix.single_apply]

theorem dilInit_eq_zero (g : A.GB) (hg : (splitLogs g.1).2 ≠ fun _ => none) (a : A.DAnc) :
    A.gameMixed.dilInit () (g, a) = 0 := by
  simp only [MixedAlg.dilInit, appendKet_apply]
  rw [purify_apply_eq_zero _ _ a.1, zero_mul]
  rw [show A.gameMixed.init () = A.mgInitM.tensorKet false from rfl, MState.tensorKet_mat,
    kroneckerMap_apply, mgInitM_apply, if_neg fun h => hg h.1.symm, mul_zero, zero_mul]

/-- **The initial state of the dilated distinguisher**: the purified initial state of the mixed
game with the flag, at blank logs. -/
noncomputable def dInitVec : QState ((DReg A.W A.width X Y Req Resp × Bool) × A.DAnc) :=
  WithLp.toLp 2 fun p => A.gameMixed.dilInit () ((splitLogs.symm (p.1.1, fun _ => none), p.1.2), p.2)

theorem norm_dInitVec : ‖A.dInitVec‖ = 1 := by
  classical
  let f : (DReg A.W A.width X Y Req Resp × Bool) × A.DAnc → A.GB × A.DAnc :=
    fun x => ((splitLogs.symm (x.1.1, fun _ => none), x.1.2), x.2)
  have hf : Function.Injective f := by
    intro x y h
    simp only [f, Prod.mk.injEq] at h
    have h1 := congrArg (fun r => (splitLogs r).1) h.1.1
    simp only [Equiv.apply_symm_apply] at h1
    exact Prod.ext (Prod.ext h1 h.1.2) h.2
  have h : ‖A.dInitVec‖ ^ 2 = ‖A.gameMixed.dilInit ()‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f)) fun y _ hy => by
      obtain ⟨⟨g, b⟩, a⟩ := y
      rw [A.dilInit_eq_zero _ (fun hg => hy (Finset.mem_image.2 ⟨(((splitLogs g).1, b), a),
        Finset.mem_univ _, by simp [f, ← hg]⟩)), norm_zero, sq, zero_mul]]
    rw [Finset.sum_image fun x _ y _ h => hf h]
    rfl
  rw [A.gameMixed.norm_dilInit, one_pow] at h
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 (by rw [h, one_pow])

/-- **The post phase as one unitary** depending on the oracle: the first `b` post batches of
queries, each followed by the dilated Kraus map. -/
noncomputable def postOpN (H : X → Y) : ℕ →
    (QState (DReg A.DW A.width X Y Req Resp) ≃ₗᵢ[ℂ] QState (DReg A.DW A.width X Y Req Resp))
  | 0 => LinearIsometryEquiv.refl ℂ _
  | b + 1 => (postOpN H b).trans ((permOp (queryPerm H)).trans (A.uStepD (A.slots + 1 + b)))

/-- The post phase of the dilated distinguisher. -/
noncomputable def postOp (H : X → Y) :
    QState (DReg A.DW A.width X Y Req Resp) ≃ₗᵢ[ℂ] QState (DReg A.DW A.width X Y Req Resp) :=
  A.postOpN H A.post

/-- **The dilated distinguisher** of `A`, accepting when the halting flag is clear and the output
is `o`: the workspace holds the flag and the ancilla of the dilation; its steps are the dilated
Kraus maps of the slots (`uStepD`), and its post phase is `postOp`. -/
noncomputable def dilate [DecidableEq O] (o : O) :
    Distinguisher A.DW X Y Req Resp A.width A.slots where
  kind w := A.kind w.1 || w.2.1
  init := Quantum.relabel A.relD A.dInitVec
  norm_init := by rw [LinearIsometryEquiv.norm_map, A.norm_dInitVec]
  step k := A.uStepD k
  accept := {x | x.1.1.2.1 = false ∧ A.out x.1.1.1 = o}

/-- The entries of the completed step on the game registers. -/
theorem gStep_op_apply (k : StepIdx A.slots A.post) (x : A.R ⊕ Bool) (g g' : A.G)
    (b b' : Bool) :
    (A.gStep k).op x (g, b) (g', b') =
      (A.step k).complete.op x ((splitLogs g).1, b) ((splitLogs g').1, b') *
        (if (splitLogs g).2 = (splitLogs g').2 then 1 else 0) := by
  simp [gStep, KrausChannel.reindexK, KrausChannel.tensorIdK, flagSplit, kroneckerMap_apply, Matrix.one_apply]

/-- **The dilated Kraus map of the distinguisher, controlled by nothing and acting on the game
registers, is the Stinespring map of the completed step** on vectors whose ancilla register
`k` is clean. -/
theorem uStepD_logControlled (k : ℕ) {ψ : QState (A.GB × A.DAnc)}
    (hψ : MixedAlg.CleanVec k ψ) :
    Quantum.relabel A.relG (logControlled (fun _ => A.uStepD k)
      (Quantum.relabel A.relG.symm ψ)) = A.gameMixed.dilStep () k ψ := by
  ext ⟨⟨g, b⟩, a⟩
  simp only [relabel_apply, logControlled_apply, uStepD, LinearIsometryEquiv.trans_apply,
    relabel_symm]
  by_cases hk : k < A.slots + A.post + 1
  · have hf := hψ.fresh (k := ⟨k, hk⟩) le_rfl
    simp only [uStep, dif_pos hk, MixedAlg.dilStep, stinespring_apply_of_fresh _ hf, Equiv.symm_symm]
    rw [stinespring_apply_of_fresh _ ?hfu]
    case hfu =>
      intro x a' ha'
      simp only [relabel_apply, Equiv.symm_symm]
      exact hf _ _ ha'
    have hr1 : A.relD.symm (splitLogs (A.relG.symm ((g, b), a))).1 = (((splitLogs g).1, b), a) := rfl
    have hr2 : (splitLogs (A.relG.symm ((g, b), a))).2 = (splitLogs g).2 := rfl
    rw [hr1, hr2, krausAct_apply, krausAct_apply]
    conv_rhs => rw [← Equiv.sum_comp A.flagSplit, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single (splitLogs g).2]
    · rw [show A.gameMixed.step () ⟨k, hk⟩ = A.gStep ⟨k, hk⟩ from rfl]
      simp only [flagSplit, Equiv.coe_fn_mk, gStep_op_apply, Equiv.apply_symm_apply, if_true,
        mul_one]
      rfl
    · intro lg _ hlg
      rw [show A.gameMixed.step () ⟨k, hk⟩ = A.gStep ⟨k, hk⟩ from rfl]
      simp only [flagSplit, Equiv.coe_fn_mk, gStep_op_apply, Equiv.apply_symm_apply,
        if_neg (Ne.symm hlg), mul_zero, zero_mul]
    · simp
  · simp only [uStep, dif_neg hk, MixedAlg.dilStep, LinearIsometryEquiv.coe_refl, id, relabel_apply]
    rfl

/-! #### The pure game of the dilated distinguisher -/

section LogControlled

variable {W : Type} {n m : ℕ} [Fintype W]

/-- The slice of a log-controlled unitary's output at the logs `lg` is the unitary at `lg` applied
to the slice. -/
theorem slice_logControlled
    (U : LogReg Req m → QState (DReg W n X Y Req Resp) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req Resp))
    (v : QState (GameReg W n X Y Req Resp m)) (lg : LogReg Req m) :
    (WithLp.toLp 2 fun d => logControlled U v (splitLogs.symm (d, lg)) :
      QState (DReg W n X Y Req Resp)) = U lg (WithLp.toLp 2 fun d => v (splitLogs.symm (d, lg))) := by
  ext d
  simp [logControlled_apply]

theorem logControlled_trans
    (U V : LogReg Req m → QState (DReg W n X Y Req Resp) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req Resp))
    (v : QState (GameReg W n X Y Req Resp m)) :
    logControlled (fun lg => (U lg).trans (V lg)) v = logControlled V (logControlled U v) := by
  ext r
  simp only [logControlled_apply, LinearIsometryEquiv.trans_apply, Equiv.apply_symm_apply]

theorem logControlled_refl (v : QState (GameReg W n X Y Req Resp m)) :
    logControlled (fun _ => LinearIsometryEquiv.refl ℂ (QState (DReg W n X Y Req Resp))) v = v := by
  ext r
  simp [logControlled_apply]

theorem logControlled_queryPerm (F : LogReg Req m → X → Y)
    (v : QState (GameReg W n X Y Req Resp m)) :
    logControlled (fun lg => permOp (queryPerm (F lg))) v =
      permOp (queryPermOf fun s : W × Req × Option Resp × LogReg Req m => F s.2.2.2) v := by
  ext r
  simp only [logControlled_apply, permOp_apply]
  rfl

end LogControlled

variable [DecidableEq O]

theorem gameInit_relG (o : O) :
    Quantum.relabel A.relG (A.dilate o).gameInit = A.gameMixed.dilInit () := by
  ext ⟨⟨g, b⟩, a⟩
  simp only [relabel_apply, Distinguisher.gameInit]
  have hs : (splitLogs (A.relG.symm ((g, b), a))).2 = (splitLogs g).2 := rfl
  rw [hs]
  split_ifs with h
  · simp only [dilate, relabel_apply, dInitVec]
    show A.gameMixed.dilInit () ((splitLogs.symm ((splitLogs g).1, fun _ => none), b), a) =
      A.gameMixed.dilInit () ((g, b), a)
    rw [show splitLogs.symm ((splitLogs g).1, fun _ => none) = g by rw [← h]; simp]
  · rw [A.dilInit_eq_zero _ h]

theorem relG_eventPerm (o : O) (ω : Ω) {k : ℕ} (hk : k < A.slots)
    (r : GameReg A.DW A.width X Y Req Resp A.slots) :
    MixedAlg.liftPerm (A.evPermB E ω k) (A.relG r) =
      A.relG ((A.dilate o).eventPerm E ω k r) := by
  obtain ⟨⟨⟨w, b, a⟩, req, resp, lg⟩, prs⟩ := r
  cases b <;> by_cases h : A.kind w <;>
    simp [Distinguisher.eventPerm, dif_pos hk, evPermB, evPerm, evPermH, Equiv.trans_apply,
      MixedAlg.liftPerm, relG, copyG, respG, Env.requestPerm, Env.oraclePerm, copyPerm_apply,
      respondPerm_apply, dilate, h, Env.answer, Env.oracle] <;> rfl

theorem relG_postPerm (ω : Ω) {k : ℕ} (hk : A.slots ≤ k)
    (r : GameReg A.DW A.width X Y Req Resp A.slots) :
    MixedAlg.liftPerm (A.evPermB E ω k) (A.relG r) =
      A.relG (queryPermOf (fun s : A.DW × Req × Option Resp × LogReg Req A.slots =>
        E.oracle ω s.2.2.2) r) := by
  obtain ⟨⟨⟨w, b, a⟩, req, resp, lg⟩, prs⟩ := r
  have h : ¬ k < A.slots := by omega
  cases b <;> simp only [evPermB, evPerm, evPermH, dif_neg h] <;> rfl

/-- The dilated Kraus map on the game registers with the flag and the ancilla. -/
noncomputable def uG (k : ℕ) : QState (A.GB × A.DAnc) ≃ₗᵢ[ℂ] QState (A.GB × A.DAnc) :=
  ((Quantum.relabel A.relG.symm).trans (logControlled fun _ => A.uStepD k)).trans
    (Quantum.relabel A.relG)

theorem uG_relabel (k : ℕ) (v : QState (GameReg A.DW A.width X Y Req Resp A.slots)) :
    A.uG k (Quantum.relabel A.relG v) =
      Quantum.relabel A.relG (logControlled (fun _ => A.uStepD k) v) := by
  simp only [uG, LinearIsometryEquiv.trans_apply, relabel_symm_relabel]

theorem stage_dilate (o : O) (ω : Ω) {n : ℕ} (hn : n ≤ A.slots) :
    Quantum.relabel A.relG ((A.dilate o).stage E ω n) =
      hybrid A.uG (fun k => permOp (MixedAlg.liftPerm (A.evPermB E ω k)))
        (A.gameMixed.dilInit ()) n := by
  have hstep : ∀ k ≤ A.slots, (A.dilate o).stepAt k = A.uStepD k := fun k hk => by
    simp only [Distinguisher.stepAt, dif_pos (Nat.lt_succ_of_le hk)]
    rfl
  induction n with
  | zero =>
    rw [Distinguisher.stage, hybrid_zero, hybrid_zero, Distinguisher.liftedStep, hstep 0 (by omega),
      ← uG_relabel, gameInit_relG]
  | succ n ih =>
    rw [Distinguisher.stage_succ, hybrid_succ, Distinguisher.liftedStep, hstep (n + 1) hn,
      ← uG_relabel, ← ih (by omega)]
    congr 1
    exact (OracleAlg.permOp_relabel A.relG (fun r => A.relG_eventPerm E o ω (by omega) r) _).symm

theorem final_dilate (o : O) (ω : Ω) :
    Quantum.relabel A.relG ((A.dilate o).final E A.postOp ω) =
      hybrid A.uG (fun k => permOp (MixedAlg.liftPerm (A.evPermB E ω k)))
        (A.gameMixed.dilInit ()) (A.slots + A.post) := by
  have key : ∀ b ≤ A.post, Quantum.relabel A.relG
      (logControlled (fun lg => A.postOpN (E.oracle ω lg) b) ((A.dilate o).run E ω)) =
      hybrid A.uG (fun k => permOp (MixedAlg.liftPerm (A.evPermB E ω k)))
        (A.gameMixed.dilInit ()) (A.slots + b) := by
    intro b
    induction b with
    | zero =>
      intro _
      simp only [postOpN, logControlled_refl, Nat.add_zero, Distinguisher.run]
      exact A.stage_dilate E o ω le_rfl
    | succ b ih =>
      intro hb
      simp only [postOpN]
      rw [logControlled_trans, logControlled_trans, logControlled_queryPerm, ← uG_relabel,
        ← OracleAlg.permOp_relabel A.relG (fun r => A.relG_postPerm E ω
          (k := A.slots + b) (by omega) r), ih (by omega),
        show A.slots + (b + 1) = A.slots + b + 1 by omega, hybrid_succ,
        show A.slots + 1 + b = A.slots + b + 1 by omega]
  exact key A.post le_rfl

/-- **The pure game of the dilated distinguisher accepts with the probability of the mixed
game** (without the measurement of the requests). -/
theorem acceptProbAt_dilate (o : O) (ω : Ω) :
    (A.dilate o).acceptProbAt E A.postOp ω = A.mgAccept E o ω false := by
  have hspec := A.gameMixed.hybrid_spec (fun k => A.evPermB E ω k) () A.uG
    (fun k φ hφ => A.uStepD_logControlled k hφ) (A.slots + A.post)
  have hfin : (A.dilate o).final E A.postOp ω = Quantum.relabel A.relG.symm
      (hybrid A.uG (fun k => permOp (MixedAlg.liftPerm (A.evPermB E ω k)))
        (A.gameMixed.dilInit ()) (A.slots + A.post)) := by
    rw [← A.final_dilate E o ω, relabel_symm_relabel]
  have hn : ‖hybrid A.uG (fun k => permOp (MixedAlg.liftPerm (A.evPermB E ω k)))
      (A.gameMixed.dilInit ()) (A.slots + A.post)‖ = 1 := by
    rw [norm_hybrid, A.gameMixed.norm_dilInit]
  rw [Distinguisher.acceptProbAt, hfin, prob_relabel]
  have hset : (A.relG.symm ⁻¹' (A.dilate o).gameAccept) =
      {p : A.GB × A.DAnc | p.1 ∈ {gb : A.GB | gb.2 = false ∧ A.out gb.1.1.1 = o}} := by
    ext ⟨⟨g, b⟩, a⟩
    rfl
  rw [hset, ← probIn_reduceMState _ hn, MState.probIn]
  simp only [reduceMState_mat, hspec.2]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Set.indicator, Set.mem_setOf_eq, Bool.true_eq_false, false_and,
    if_false, zero_add, true_and]
  unfold KindAlg.mgAccept
  rw [mgRun_false_eq, ← A.ffBlock_stageV E ω]
  rfl

end KindAlg

end GordieHowe.Quantum

namespace GordieHowe.Quantum

namespace IAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] [DecidableEq O] (A : IAlg X Y Req Resp O) (C : Challenger X Y Req Resp)

omit [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [DecidableEq O] in
theorem toPureEnv_μ_apply (H : X → Y) (c : C.Coins) :
    C.toPureEnv.μ (H, c) = (PMF.uniformOfFintype (X → Y)) H * C.coins c := by
  simp only [Challenger.toPureEnv, PMF.bind_apply, PMF.map_apply, tsum_fintype]
  rw [Finset.sum_eq_single H]
  · congr 1
    rw [Finset.sum_eq_single c (fun c' _ hc' => by simp [Ne.symm hc']) (by simp)]
    simp
  · intro H' _ hH'
    simp [Ne.symm hH']
  · simp

end IAlg

end GordieHowe.Quantum
