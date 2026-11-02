-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.PureGame
public import GordieHowe.Model.Quantum.Interactive.MultiRelay
public import GordieHowe.Model.Quantum.Pure.PostSlots
public import GordieHowe.Model.Quantum.Pure.LiveRun
public import GordieHowe.Model.Quantum.Interactive.RelayBlockEntry

@[expose] public section

/-!
# The dilation of steps with a leading unitary

A step `K` of a kind algorithm that is a Kraus map `K₁` after a basis permutation `P`
(`K.op r a b = K₁.op r a (P b)`) can be dilated as the Stinespring unitary of the completed `K₁`
after `P` on the live branches (`KindAlg.leadUStep`): a branch that halts at the step halts after
`P`. The dilated distinguisher of these steps (`KindAlg.leadDilate`, `AdaptiveIAlg.leadPureD`)
accepts with the same probability as the dilated distinguisher of the steps
(`AdaptiveIAlg.leadPureD_acceptProbOnAt`): a unitary cannot halt, so where the halting measurement
sits relative to it changes no outcome probability.

- `MixedAlg.cleanSet`, `MixedAlg.fresh_of_cleanSet`, `MixedAlg.cleanSet_stinespring`: the clean
  ancillas, and a Stinespring unitary on them.
- `stinespring_complete_false_apply`: the live rows of the Stinespring unitary of a completed Kraus
  map read only the live columns.
- `stinespring_complete_lead`, `stinespring_complete_dead`: the completed step and the completed
  `K₁` after `P` agree on the live rows; the halted branches stay halted.
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.Quantum

namespace MixedAlg

variable {ι σ R M : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ] [Fintype R] [Fintype M]
  {d : ℕ} [Nonempty R] [Nonempty M]

/-- The basis states whose ancilla is clean from `n` on (`MixedAlg.Clean`). -/
def cleanSet (n : ℕ) : Set (σ × Anc ι d R M) :=
  {p | Clean n p.2}

omit [DecidableEq σ] in
theorem cleanSet_mono {n : ℕ} :
    Supported (cleanSet (σ := σ) (ι := ι) (d := d) (R := R) (M := M) n) ≤
      Supported (cleanSet (n + 1)) :=
  fun _ h p hp => h p fun hc => hp hc.mono

omit [DecidableEq σ] in
/-- A vector with clean ancillas from `n` on is fresh in the register of step `k ≥ n`. -/
theorem fresh_of_cleanSet {n : ℕ} {ψ : QState (σ × Anc ι d R M)}
    (h : Supported (cleanSet n) ψ) {k : Fin (d + 1)} (hk : n ≤ k) :
    Fresh (stepSplit k) (Classical.arbitrary R) ψ :=
  fun i a ha => h (i, a) fun hc => ha (by simpa using hc.1 k hk)

/-- **The Stinespring unitary of step `n` keeps the ancillas clean from `n + 1` on.** -/
theorem cleanSet_stinespring {n : ℕ} (hn : n < d + 1) (K : KrausChannel R σ σ)
    {ψ : QState (σ × Anc ι d R M)} (hψ : Supported (cleanSet n) ψ) :
    Supported (cleanSet (n + 1))
      (stinespring (stepSplit ⟨n, hn⟩) (Classical.arbitrary R) K ψ) := by
  have hf := fresh_of_cleanSet hψ (k := ⟨n, hn⟩) le_rfl
  rintro ⟨i, a⟩ ha
  rw [stinespring_apply_of_fresh _ hf]
  refine krausAct_eq_zero_of _ (P := fun a => ¬ Clean (n + 1) a)
    (fun i a ha => hψ (i, a) fun hc => ha hc.mono) (fun a ha hc => ha ?_) i ha
  rw [stepSplit_symm_reset] at hc
  refine ⟨fun j hj => ?_, hc.2⟩
  have hne : j ≠ ⟨n, hn⟩ := fun hjk => by
    rw [hjk] at hj
    exact Nat.not_succ_le_self n hj
  have := hc.1 j hj
  simp only at this
  rwa [Function.update_of_ne hne] at this

end MixedAlg

section Entries

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **The entries of a unitary moved along a relabelling.** -/
theorem unitaryMat_relabel_conj (e : ι ≃ κ) (U : QState ι ≃ₗᵢ[ℂ] QState ι) (y x : κ) :
    unitaryMat (((Quantum.relabel e).symm.trans U).trans (Quantum.relabel e)) y x =
      unitaryMat U (e.symm y) (e.symm x) := by
  have h : (Quantum.relabel e).symm (EuclideanSpace.single x (1 : ℂ)) =
      EuclideanSpace.single (e.symm x) 1 := by
    ext i
    simp only [relabel_symm, relabel_apply, Equiv.symm_symm, PiLp.single_apply,
      Equiv.apply_eq_iff_eq_symm_apply]
  simp only [unitaryMat, LinearIsometryEquiv.trans_apply, h, relabel_apply]

/-- **The entries of a unitary after a basis permutation.** -/
theorem unitaryMat_trans_permOp (U : QState ι ≃ₗᵢ[ℂ] QState ι) (π : Equiv.Perm ι) (y x : ι) :
    unitaryMat (U.trans (permOp π)) y x = unitaryMat U (π.symm y) x := by
  simp only [unitaryMat, LinearIsometryEquiv.trans_apply, permOp_apply]

end Entries

section Lead

variable {σ R A C : Type*} [Fintype σ] [DecidableEq σ] [Fintype R] [Fintype A] [Fintype C]
  (e : A ≃ (R ⊕ Bool) × C) (r₀ : R ⊕ Bool)

/-- **The live rows of the Stinespring unitary of a completed Kraus map** read only the live
columns: on row `((y, false), a)` with register value `inl r` it is `K.op r` on the live columns,
with the register reset; with register value `inr _` it is `0`. -/
theorem stinespring_complete_false_apply (K : KrausMap R σ σ) {ψ : QState ((σ × Bool) × A)}
    (hψ : Fresh e r₀ ψ) (y : σ) (a : A) :
    stinespring e r₀ K.complete ψ ((y, false), a) =
      Sum.elim (fun r => ∑ j, K.op r y j * ψ ((j, false), e.symm (r₀, (e a).2))) (fun _ => 0)
        (e a).1 := by
  rw [stinespring_apply_of_fresh _ hψ, krausAct_apply, Fintype.sum_prod_type]
  rcases (e a).1 with r | b
  · simp only [Sum.elim_inl, KrausMap.complete, KrausMap.completeOp, kroneckerMap_apply,
      Matrix.single_apply, Fintype.sum_bool]
    simp
  · cases b <;> simp [KrausMap.complete, KrausMap.completeOp, kroneckerMap_apply,
      Matrix.single_apply]

/-- **The completed step and the completed `K₁` after `P` agree on the live rows**, for a step
`K.op r a b = K₁.op r a (P b)` and a fresh vector. -/
theorem stinespring_complete_lead {K K₁ : KrausMap R σ σ} {P : Equiv.Perm σ}
    (hK : ∀ r a b, K.op r a b = K₁.op r a (P b)) {ψ : QState ((σ × Bool) × A)}
    (hψ : Fresh e r₀ ψ) (y : σ) (a : A) :
    stinespring e r₀ K₁.complete
        (permOp (MixedAlg.liftPerm (flagPerm P (Equiv.refl σ))) ψ) ((y, false), a) =
      stinespring e r₀ K.complete ψ ((y, false), a) := by
  have hψ' : Fresh e r₀ (permOp (MixedAlg.liftPerm (flagPerm P (Equiv.refl σ))) ψ) :=
    fun i a ha => by
      rw [permOp_apply]
      exact hψ _ a ha
  rw [stinespring_complete_false_apply e r₀ K₁ hψ', stinespring_complete_false_apply e r₀ K hψ]
  rcases (e a).1 with r | b
  · simp only [Sum.elim_inl, permOp_apply, MixedAlg.liftPerm, Equiv.prodCongr_symm,
      Equiv.prodCongr_apply, Equiv.refl_symm, Equiv.refl_apply, Prod.map, flagPerm_symm_false]
    rw [← Equiv.sum_comp P]
    simp only [Equiv.symm_apply_apply, hK]
  · rfl

/-- **The halted branches stay halted**: the Stinespring unitary of a completed Kraus map maps a
fresh vector on the halted branches to the halted branches. -/
theorem stinespring_complete_dead (K : KrausMap R σ σ) {ψ : QState ((σ × Bool) × A)}
    (hψ : Fresh e r₀ ψ) (hd : ∀ y a, ψ ((y, false), a) = 0) (y : σ) (a : A) :
    stinespring e r₀ K.complete ψ ((y, false), a) = 0 := by
  rw [stinespring_complete_false_apply e r₀ K hψ]
  rcases (e a).1 with r | b
  · simp [hd]
  · rfl

end Lead


namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [AddGroup Y]
  {ksA : KindShape X Y Req Resp} (A : KindAlg ksA O)
  (K₁ : StepIdx A.slots A.post →
    KrausMap A.R (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp))
  (P : StepIdx A.slots A.post → Equiv.Perm (DReg A.W A.width X Y Req Resp))

/-- **The dilated step `k` with its leading unitary**: `P k` on the live branches (flag
`false`), then the Stinespring unitary of the completed `K₁ k` on the register `k` of the
ancilla; the identity after the last step. The halted branches are frozen, so `P k` acts only on
the live ones; a branch that halts at step `k` halts after `P k`. -/
noncomputable def leadUStep (k : ℕ) :
    QState ((DReg A.W A.width X Y Req Resp × Bool) × A.DAnc) ≃ₗᵢ[ℂ]
      QState ((DReg A.W A.width X Y Req Resp × Bool) × A.DAnc) :=
  if h : k < A.slots + A.post + 1 then
    (permOp (MixedAlg.liftPerm (flagPerm (P ⟨k, h⟩) (Equiv.refl _)))).trans
      (stinespring (MixedAlg.stepSplit ⟨k, h⟩) (Classical.arbitrary (A.R ⊕ Bool))
        (K₁ ⟨k, h⟩).complete)
  else LinearIsometryEquiv.refl ℂ _

/-- `leadUStep` on the registers of the dilated distinguisher. -/
noncomputable def leadUStepD (k : ℕ) :
    QState (DReg A.DW A.width X Y Req Resp) ≃ₗᵢ[ℂ] QState (DReg A.DW A.width X Y Req Resp) :=
  ((Quantum.relabel A.relD).symm.trans (A.leadUStep K₁ P k)).trans (Quantum.relabel A.relD)

/-- **The dilated distinguisher with leading unitaries**: `dilate o` with the steps
`leadUStepD`. -/
noncomputable def leadDilate [DecidableEq O] (o : O) :
    Distinguisher A.DW X Y Req Resp A.width A.slots :=
  { A.dilate o with step := fun k => A.leadUStepD K₁ P k }

/-- The live registers of the dilated distinguisher: the halting flag clear. -/
def liveW : Set A.DW := {w | w.2.1 = false}

/-- The registers of the dilated distinguisher whose ancilla is clean from `n` on. -/
def cleanW (n : ℕ) : Set A.DW := {w | MixedAlg.Clean n w.2.2}

variable {A K₁ P}

/-- **The dilated steps keep the ancillas clean**, with and without the leading unitary. -/
theorem uStepD_clean (k : ℕ) {v : QState (DReg A.DW A.width X Y Req Resp)}
    (hv : Supported (Distinguisher.wsSetD (A.cleanW k)) v) :
    Supported (Distinguisher.wsSetD (A.cleanW (k + 1))) (A.uStepD k v) ∧
      Supported (Distinguisher.wsSetD (A.cleanW (k + 1))) (A.leadUStepD K₁ P k v) := by
  have hv' : Supported (MixedAlg.cleanSet k) (Quantum.relabel A.relD.symm v) :=
    fun p hp => hv _ hp
  have hfin : ∀ u : QState ((DReg A.W A.width X Y Req Resp × Bool) × A.DAnc),
      Supported (MixedAlg.cleanSet (k + 1)) u →
      Supported (Distinguisher.wsSetD (A.cleanW (k + 1))) (Quantum.relabel A.relD u) :=
    fun u hu d hd => hu _ hd
  by_cases hk : k < A.slots + A.post + 1
  · refine ⟨hfin _ ?_, hfin _ ?_⟩
    · simp only [uStep, dif_pos hk]
      exact MixedAlg.cleanSet_stinespring hk _ hv'
    · simp only [leadUStep, dif_pos hk, LinearIsometryEquiv.trans_apply]
      exact MixedAlg.cleanSet_stinespring hk _ (hv'.permOp fun r hr => hr)
  · have hm := MixedAlg.cleanSet_mono _ hv'
    refine ⟨hfin _ ?_, hfin _ ?_⟩
    · simp only [uStep, dif_neg hk]
      exact hm
    · simp only [leadUStep, dif_neg hk]
      exact hm

/-- **The dilated steps keep the halted branches halted**, with and without the leading
unitary. -/
theorem uStepD_dead (k : ℕ) {v : QState (DReg A.DW A.width X Y Req Resp)}
    (hv : Supported (Distinguisher.wsSetD (A.cleanW k ∩ A.liveWᶜ)) v) :
    Supported (Distinguisher.wsSetD A.liveWᶜ) (A.uStepD k v) ∧
      Supported (Distinguisher.wsSetD A.liveWᶜ) (A.leadUStepD K₁ P k v) := by
  have hψ : Supported (MixedAlg.cleanSet k) (Quantum.relabel A.relD.symm v) :=
    fun p hp => hv _ fun h => hp h.1
  have hd : ∀ y a, Quantum.relabel A.relD.symm v ((y, false), a) = 0 :=
    fun y a => hv _ fun h => h.2 rfl
  have key : ∀ U : QState ((DReg A.W A.width X Y Req Resp × Bool) × A.DAnc) ≃ₗᵢ[ℂ]
      QState ((DReg A.W A.width X Y Req Resp × Bool) × A.DAnc),
      (∀ y a, U (Quantum.relabel A.relD.symm v) ((y, false), a) = 0) →
      Supported (Distinguisher.wsSetD A.liveWᶜ)
        (((Quantum.relabel A.relD).symm.trans U).trans (Quantum.relabel A.relD) v) := by
    intro U hU d hdl
    obtain ⟨⟨⟨w, f, a⟩, q, r⟩, qs⟩ := d
    have hf : f = false := by simpa [Distinguisher.wsSetD, liveW] using hdl
    subst hf
    exact hU (((w, q, r), qs)) a
  refine ⟨key _ fun y a => ?_, key _ fun y a => ?_⟩
  · by_cases hk : k < A.slots + A.post + 1
    · simp only [uStep, dif_pos hk]
      exact stinespring_complete_dead _ _ _ (MixedAlg.fresh_of_cleanSet hψ le_rfl) hd y a
    · simp only [uStep, dif_neg hk]
      exact hd y a
  · by_cases hk : k < A.slots + A.post + 1
    · simp only [leadUStep, dif_pos hk, LinearIsometryEquiv.trans_apply]
      refine stinespring_complete_dead _ _ _
        (MixedAlg.fresh_of_cleanSet (hψ.permOp fun r hr => hr) le_rfl) (fun y a => ?_) y a
      rw [permOp_apply]
      exact hd _ a
    · simp only [leadUStep, dif_neg hk]
      exact hd y a

/-- **The dilated steps with and without the leading unitary agree on the live branches**, on the
vectors whose ancilla is clean from `k` on, for steps `A.step k = K₁ k` after `P k`. -/
theorem uStepD_agree (hK : ∀ k r a b, (A.step k).op r a b = (K₁ k).op r a (P k b)) (k : ℕ)
    {v : QState (DReg A.DW A.width X Y Req Resp)}
    (hv : Supported (Distinguisher.wsSetD (A.cleanW k)) v) :
    mask (Distinguisher.wsSetD A.liveW) (A.leadUStepD K₁ P k v) =
      mask (Distinguisher.wsSetD A.liveW) (A.uStepD k v) := by
  have hψ : Supported (MixedAlg.cleanSet k) (Quantum.relabel A.relD.symm v) :=
    fun p hp => hv _ hp
  ext d
  by_cases hdl : d ∈ Distinguisher.wsSetD A.liveW
  · rw [mask_apply_of_mem _ hdl, mask_apply_of_mem _ hdl]
    obtain ⟨⟨⟨w, f, a⟩, q, r⟩, qs⟩ := d
    have hf : f = false := hdl
    subst hf
    change A.leadUStep K₁ P k (Quantum.relabel A.relD.symm v) ((((w, q, r), qs), false), a) =
      A.uStep k (Quantum.relabel A.relD.symm v) ((((w, q, r), qs), false), a)
    by_cases hk : k < A.slots + A.post + 1
    · simp only [leadUStep, uStep, dif_pos hk, LinearIsometryEquiv.trans_apply]
      exact stinespring_complete_lead _ _ (hK ⟨k, hk⟩)
        (MixedAlg.fresh_of_cleanSet hψ le_rfl) _ a
    · simp only [leadUStep, uStep, dif_neg hk]
  · rw [mask_apply_of_notMem _ hdl, mask_apply_of_notMem _ hdl]

variable (A) in
/-- A move of the adversary's registers on the registers of the dilated distinguisher, the halting
flag and the ancilla kept. -/
def sysLift (σ : Equiv.Perm (DReg A.W A.width X Y Req Resp)) :
    Equiv.Perm (DReg A.DW A.width X Y Req Resp) :=
  A.relD.permCongr ((σ.prodCongr (Equiv.refl _)).prodCongr (Equiv.refl _))

theorem relD_symm_sysLift (σ : Equiv.Perm (DReg A.W A.width X Y Req Resp))
    (d : DReg A.DW A.width X Y Req Resp) :
    A.relD.symm (A.sysLift σ d) =
      ((σ (A.relD.symm d).1.1, (A.relD.symm d).1.2), (A.relD.symm d).2) := by
  simp only [sysLift, Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply,
    Prod.map, Equiv.refl_apply]

open Classical in
/-- **The entries of the dilated step with its leading unitary on the clean columns**: the
completed operator of the row's ancilla register, from the column after `P` on the live branches;
the rest of the ancilla kept. -/
theorem unitaryMat_leadUStepD (k : ℕ) (hk : k < A.slots + A.post + 1)
    (y x : DReg A.DW A.width X Y Req Resp) (hx : (A.relD.symm x).2.2.1 ⟨k, hk⟩ =
      Classical.arbitrary (A.R ⊕ Bool)) :
    unitaryMat (A.leadUStepD K₁ P k) y x =
      (K₁ ⟨k, hk⟩).completeOp ((A.relD.symm y).2.2.1 ⟨k, hk⟩) (A.relD.symm y).1
        (flagPerm (P ⟨k, hk⟩) (Equiv.refl _) (A.relD.symm x).1) *
      (if (A.relD.symm x).2 = (MixedAlg.stepSplit ⟨k, hk⟩).symm
          (Classical.arbitrary _, (MixedAlg.stepSplit ⟨k, hk⟩ (A.relD.symm y).2).2)
        then 1 else 0) := by
  unfold leadUStepD
  rw [unitaryMat_relabel_conj]
  simp only [unitaryMat, leadUStep, dif_pos hk, LinearIsometryEquiv.trans_apply, permOp_single]
  rw [stinespring_single_apply _ (by exact hx)]
  rfl

open Classical in
/-- **The dilated step with its leading unitary along moves of the adversary's registers**: its
entries at a clean column are kept when the completed operators are. -/
theorem unitaryMat_leadUStepD_sysLift (k : ℕ) (hk : k < A.slots + A.post + 1)
    (y x : DReg A.DW A.width X Y Req Resp)
    (hx : (A.relD.symm x).2.2.1 ⟨k, hk⟩ = Classical.arbitrary (A.R ⊕ Bool))
    (σr σc : Equiv.Perm (DReg A.W A.width X Y Req Resp))
    (h : ∀ r, (K₁ ⟨k, hk⟩).completeOp r (σr (A.relD.symm y).1.1, (A.relD.symm y).1.2)
        (flagPerm (P ⟨k, hk⟩) (Equiv.refl _) (σc (A.relD.symm x).1.1, (A.relD.symm x).1.2)) =
      (K₁ ⟨k, hk⟩).completeOp r (A.relD.symm y).1
        (flagPerm (P ⟨k, hk⟩) (Equiv.refl _) (A.relD.symm x).1)) :
    unitaryMat (A.leadUStepD K₁ P k) (A.sysLift σr y) (A.sysLift σc x) =
      unitaryMat (A.leadUStepD K₁ P k) y x := by
  have hx' : (A.relD.symm (A.sysLift σc x)).2.2.1 ⟨k, hk⟩ = Classical.arbitrary (A.R ⊕ Bool) := by
    rw [relD_symm_sysLift]
    exact hx
  rw [unitaryMat_leadUStepD k hk _ _ hx', unitaryMat_leadUStepD k hk _ _ hx, relD_symm_sysLift,
    relD_symm_sysLift, h]

theorem cleanW_mono (k : ℕ) : A.cleanW k ⊆ A.cleanW (k + 1) :=
  fun _ hw => MixedAlg.Clean.mono hw

/-- **The dilated step `k` with and without its leading unitary are related on the live
branches**, for steps `A.step k = K₁ k` after `P k`. -/
theorem stepRel_uStepD (hK : ∀ k r a b, (A.step k).op r a b = (K₁ k).op r a (P k b)) (k : ℕ) :
    Distinguisher.StepRel A.liveW (A.cleanW k) (A.cleanW (k + 1)) (A.uStepD k)
      (A.leadUStepD K₁ P k) where
  clean _ hv := (uStepD_clean (K₁ := K₁) (P := P) k hv).1
  clean' _ hv := (uStepD_clean k hv).2
  dead _ hv := (uStepD_dead (K₁ := K₁) (P := P) k hv).1
  dead' _ hv := (uStepD_dead k hv).2
  agree _ hv := uStepD_agree hK k hv

/-- **The dilated distinguishers with and without the leading unitaries are related on the live
branches.** -/
theorem liveRel_leadDilate [DecidableEq O]
    (hK : ∀ k r a b, (A.step k).op r a b = (K₁ k).op r a (P k b)) (o : O) :
    Distinguisher.LiveRel (A.dilate o) (A.leadDilate K₁ P o) A.liveW A.cleanW where
  kind_eq := rfl
  init_eq := rfl
  accept_eq := rfl
  accept_live _ hd := by
    rw [A.dilate_accept o] at hd
    exact hd.1
  init_clean d hd := by
    rw [A.dilate_init o]
    change A.dInitVec (A.relD.symm d) = 0
    exact A.gameMixed.cleanVec_dilInit () _ _ hd
  step k := by
    by_cases hk : k < A.slots + 1
    · have h1 : (A.dilate o).stepAt k = A.uStepD k := A.stepAt_dilate o (Nat.lt_succ_iff.1 hk)
      have h2 : (A.leadDilate K₁ P o).stepAt k = A.leadUStepD K₁ P k := by
        simp only [Distinguisher.stepAt, dif_pos hk]
        rfl
      rw [h1, h2]
      exact stepRel_uStepD hK k
    · have h1 : (A.dilate o).stepAt k = LinearIsometryEquiv.refl ℂ _ := by
        simp only [Distinguisher.stepAt, dif_neg hk]
      have h2 : (A.leadDilate K₁ P o).stepAt k = LinearIsometryEquiv.refl ℂ _ := by
        simp only [Distinguisher.stepAt, dif_neg hk]
      rw [h1, h2]
      exact Distinguisher.StepRel.refl (cleanW_mono k)

end KindAlg

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ}

/-- The workspaces with a flag whose workspace lies in `B`. -/
def flagW (B : Set W) : Set (W × Bool) :=
  {w | w.1 ∈ B}

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] in
theorem compl_flagW (B : Set W) : (flagW B)ᶜ = flagW Bᶜ :=
  rfl

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] in
theorem inter_flagW (B B' : Set W) : flagW B ∩ flagW B' = flagW (B ∩ B') :=
  rfl

/-- `flagLift` of a unitary mapping the vectors with workspace in `B` to vectors with workspace
in `B'` does so with the flag. -/
theorem supported_flagLift {B B' : Set W}
    (U : QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (hU : ∀ v, Supported (wsSetD B) v → Supported (wsSetD B') (U v))
    {x : QState (DReg (W × Bool) n X Y Req A)} (hx : Supported (wsSetD (flagW B)) x) :
    Supported (wsSetD (flagW B')) (flagLift U x) := fun e he => by
  obtain ⟨g, d, rfl⟩ := exists_withFlag e
  rw [flagLift_apply]
  exact hU _ (fun d' hd' => by
    change x (withFlag g d') = 0
    exact hx _ hd') d he

/-- `flagLift` of two unitaries agreeing on `S` on the vectors with workspace in `B` agree with
the flag. -/
theorem mask_flagLift {B S : Set W}
    (U U' : QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (hU : ∀ v, Supported (wsSetD B) v → mask (wsSetD S) (U' v) = mask (wsSetD S) (U v))
    {x : QState (DReg (W × Bool) n X Y Req A)} (hx : Supported (wsSetD (flagW B)) x) :
    mask (wsSetD (flagW S)) (flagLift U' x) = mask (wsSetD (flagW S)) (flagLift U x) := by
  ext e
  obtain ⟨g, d, rfl⟩ := exists_withFlag e
  by_cases he : withFlag g d ∈ wsSetD (flagW S)
  · rw [mask_apply_of_mem _ he, mask_apply_of_mem _ he, flagLift_apply, flagLift_apply]
    have h := congrArg (fun u : QState (DReg W n X Y Req A) => u d)
      (hU (WithLp.toLp 2 fun d' => x (withFlag g d')) fun d' hd' => by
        change x (withFlag g d') = 0
        exact hx _ hd')
    simp only at h
    rwa [mask_apply_of_mem _ (show d ∈ wsSetD S from he),
      mask_apply_of_mem _ (show d ∈ wsSetD S from he)] at h
  · rw [mask_apply_of_notMem _ he, mask_apply_of_notMem _ he]

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] in
theorem flagFlip_mem_wsSetD {B : Set W} {e : DReg (W × Bool) n X Y Req A} :
    flagFlip e ∈ wsSetD (flagW B) ↔ e ∈ wsSetD (flagW B) := by
  obtain ⟨g, d, rfl⟩ := exists_withFlag e
  rw [flagFlip_withFlag]
  rfl

/-- `flagLift` keeps two unitaries related on the live branches, with the flag. -/
theorem StepRel.flagLift [DecidableEq Req] [DecidableEq A] {live C C' : Set W}
    {U U' : QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)}
    (h : StepRel live C C' U U') :
    StepRel (flagW live) (flagW C) (flagW C') (Quantum.flagLift U) (Quantum.flagLift U') where
  clean _ hv := supported_flagLift U h.clean hv
  clean' _ hv := supported_flagLift U' h.clean' hv
  dead _ hv := supported_flagLift U h.dead hv
  dead' _ hv := supported_flagLift U' h.dead' hv
  agree _ hv := mask_flagLift U U' h.agree hv

/-- Flipping the flag after two related unitaries keeps them related. -/
theorem StepRel.trans_flagFlip [DecidableEq Req] [DecidableEq A] {live C C' : Set W}
    {U U' : QState (DReg (W × Bool) n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg (W × Bool) n X Y Req A)}
    (h : StepRel (flagW live) (flagW C) (flagW C') U U') :
    StepRel (flagW live) (flagW C) (flagW C') (U.trans (permOp flagFlip))
      (U'.trans (permOp flagFlip)) := by
  have hs : ∀ {B : Set W} {v : QState (DReg (W × Bool) n X Y Req A)},
      Supported (wsSetD (flagW B)) v → Supported (wsSetD (flagW B)) (permOp flagFlip v) :=
    fun hv => hv.permOp fun e he => flagFlip_mem_wsSetD.2 he
  have hm : ∀ (v : QState (DReg (W × Bool) n X Y Req A)),
      mask (wsSetD (flagW live)) (permOp flagFlip v) =
        permOp flagFlip (mask (wsSetD (flagW live)) v) := fun v => by
    ext e
    have hme : flagFlip.symm e ∈ wsSetD (flagW live) ↔ e ∈ wsSetD (flagW live) := by
      conv_rhs => rw [← Equiv.apply_symm_apply flagFlip e]
      exact flagFlip_mem_wsSetD.symm
    by_cases he : e ∈ wsSetD (flagW live)
    · rw [mask_apply_of_mem _ he, permOp_apply, permOp_apply, mask_apply_of_mem _ (hme.2 he)]
    · rw [mask_apply_of_notMem _ he, permOp_apply,
        mask_apply_of_notMem _ fun h' => he (hme.1 h')]
  refine ⟨fun v hv => hs (h.clean v hv), fun v hv => hs (h.clean' v hv),
    fun v hv => hs (B := liveᶜ) (h.dead v hv), fun v hv => hs (B := liveᶜ) (h.dead' v hv),
    fun v hv => ?_⟩
  simp only [LinearIsometryEquiv.trans_apply]
  rw [hm, hm, h.agree v hv]

/-- **The post phases as slots keep two distinguishers related on their live branches**, for
post unitaries related on the live branches and growing sets `C`. -/
theorem LiveRel.withPostSlots [DecidableEq Req] [DecidableEq A] [AddGroup Y]
    {D D' : Distinguisher W X Y Req A n m} {live : Set W} {C : ℕ → Set W}
    (h : LiveRel D D' live C) (hmono : ∀ k, C k ⊆ C (k + 1))
    (U U' : ℕ → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)) (b : ℕ)
    (hU : ∀ k, m < k → StepRel live (C k) (C (k + 1)) (U (k - m - 1)) (U' (k - m - 1))) :
    LiveRel (D.withPostSlots U b) (D'.withPostSlots U' b) (flagW live) fun k => flagW (C k) where
  kind_eq := by
    show (fun w : W × Bool => D'.kind w.1 && !w.2) = fun w => D.kind w.1 && !w.2
    rw [h.kind_eq]
  init_eq := by
    show embV (withFlag false) D'.init = embV (withFlag false) D.init
    rw [h.init_eq]
  accept_eq := by
    show {d | (flagSplitD d).1 ∈ D'.accept} = {d | (flagSplitD d).1 ∈ D.accept}
    rw [h.accept_eq]
  accept_live d hd := h.accept_live _ hd
  init_clean e he := by
    obtain ⟨g, d, rfl⟩ := exists_withFlag e
    change embV (withFlag false) D.init (withFlag g d) = 0
    by_cases hg : g = false
    · subst hg
      rw [embV_apply_self (withFlag_injective false)]
      exact h.init_clean d he
    · exact embV_apply_of_notMem _ fun hr => hg (withFlag_mem_range_iff.1 hr)
  step k := by
    simp only [stepAt]
    split_ifs with hk
    · change StepRel _ _ _ (D.postSlotStep U k) (D'.postSlotStep U' k)
      unfold postSlotStep
      split_ifs with h1 h2
      · exact (h.step k).flagLift
      · subst h2
        exact (h.step k).flagLift.trans_flagFlip
      · exact (hU k (by omega)).flagLift
    · exact StepRel.refl fun w hw => hmono k hw

/-- A move of the registers with the flag kept. -/
def flagPermLift (τ : Equiv.Perm (DReg W n X Y Req A)) : Equiv.Perm (DReg (W × Bool) n X Y Req A) :=
  flagSplitD.symm.permCongr (τ.prodCongr (Equiv.refl _))

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] in
theorem flagPermLift_withFlag (τ : Equiv.Perm (DReg W n X Y Req A)) (g : Bool)
    (d : DReg W n X Y Req A) : flagPermLift τ (withFlag g d) = withFlag g (τ d) :=
  rfl

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] in
theorem flagFlip_flagPermLift (τ : Equiv.Perm (DReg W n X Y Req A))
    (e : DReg (W × Bool) n X Y Req A) :
    flagFlip (flagPermLift τ e) = flagPermLift τ (flagFlip e) := by
  obtain ⟨g, d, rfl⟩ := exists_withFlag e
  rfl

/-- **`flagLift` along moves of the registers that keep the flag.** -/
theorem unitaryMat_flagLift_perm [DecidableEq W] [DecidableEq X] [DecidableEq Y] [DecidableEq Req]
    [DecidableEq A] (U : QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (τr τc : Equiv.Perm (DReg W n X Y Req A)) (y x : DReg (W × Bool) n X Y Req A)
    (h : unitaryMat U (τr (flagSplitD y).1) (τc (flagSplitD x).1) =
      unitaryMat U (flagSplitD y).1 (flagSplitD x).1) :
    unitaryMat (Quantum.flagLift U) (flagPermLift τr y) (flagPermLift τc x) =
      unitaryMat (Quantum.flagLift U) y x := by
  have e : Quantum.flagLift U = (Quantum.relabel flagSplitD).trans
      ((controlled fun _ => U).trans (Quantum.relabel flagSplitD).symm) := by
    rw [relabel_symm]
    rfl
  rw [e, unitaryMat_relabel_controlled, unitaryMat_relabel_controlled]
  obtain ⟨g, d, rfl⟩ := exists_withFlag y
  obtain ⟨g', d', rfl⟩ := exists_withFlag x
  simp only [flagPermLift_withFlag]
  exact if_congr Iff.rfl h rfl

end Distinguisher

namespace KrausMap

variable {R ι κ : Type*} [Fintype R] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **`K` is `K₁` after the basis permutation `P`**: `K.op r a b = K₁.op r a (P b)`. -/
def LeadsBy (K K₁ : KrausMap R ι ι) (P : Equiv.Perm ι) : Prop :=
  ∀ r a b, K.op r a b = K₁.op r a (P b)

theorem leadsBy_refl (K : KrausMap R ι ι) : LeadsBy K K (Equiv.refl ι) :=
  fun _ _ _ => rfl

theorem ofPerm_op_apply' (π : Equiv.Perm ι) (r : Unit) (a b : ι) :
    (ofPerm π).op r a b = if π.symm a = b then 1 else 0 := by
  simp only [ofPerm, permConj, identity, Matrix.submatrix_apply, Equiv.refl_apply,
    Matrix.one_apply]
  congr

/-- A basis permutation `Q₂` before `K` moves into the leading permutation. -/
theorem LeadsBy.comp_ofPerm {K K₁ : KrausMap R ι ι} {Q₁ : Equiv.Perm ι} (h : LeadsBy K K₁ Q₁)
    (Q₂ : Equiv.Perm ι) :
    LeadsBy (K.comp (ofPerm Q₂)) (K₁.comp (ofPerm (Equiv.refl ι))) (Q₂.trans Q₁) := by
  rintro ⟨u, r⟩ a b
  change (K.op r * (ofPerm Q₂).op u) a b = (K₁.op r * (ofPerm (Equiv.refl ι)).op u) a _
  rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (Q₂ b),
    Finset.sum_eq_single (Q₁ (Q₂ b))]
  · simp [ofPerm_op_apply', h r a (Q₂ b)]
  · intro c _ hc
    rw [ofPerm_op_apply', if_neg (by simpa using hc), mul_zero]
  · simp
  · intro c _ hc
    rw [ofPerm_op_apply', if_neg (fun h' => hc (by rw [← h']; simp)), mul_zero]
  · simp

/-- A basis permutation after `K` stays after it. -/
theorem LeadsBy.ofPerm_comp {R' : Type*} [Fintype R'] {K K₁ : KrausMap R ι ι}
    {P : Equiv.Perm ι} (h : LeadsBy K K₁ P) (L : KrausMap R' ι ι) :
    LeadsBy (L.comp K) (L.comp K₁) P := by
  rintro ⟨r, r'⟩ a b
  change (L.op r' * K.op r) a b = (L.op r' * K₁.op r) a (P b)
  simp only [Matrix.mul_apply, h r]

theorem LeadsBy.tensorId {K K₁ : KrausMap R ι ι} {P : Equiv.Perm ι} (h : LeadsBy K K₁ P)
    (Z : Type*) [Fintype Z] [DecidableEq Z] :
    LeadsBy (K.tensorId Z) (K₁.tensorId Z) (P.prodCongr (Equiv.refl Z)) := by
  rintro r ⟨a, z⟩ ⟨b, z'⟩
  simp only [KrausMap.tensorId, kroneckerMap_apply, Equiv.prodCongr_apply, Prod.map,
    Equiv.refl_apply, h r]

theorem LeadsBy.reindex {K K₁ : KrausMap R ι ι} {P : Equiv.Perm ι} (h : LeadsBy K K₁ P)
    (e : ι ≃ κ) : LeadsBy (K.reindex e) (K₁.reindex e) (e.permCongr P) := by
  intro r a b
  simp only [KrausMap.reindex, Matrix.submatrix_apply, Equiv.permCongr_apply,
    Equiv.symm_apply_apply, h r]

theorem LeadsBy.restrict {K K₁ : KrausMap R ι ι} {P : Equiv.Perm ι} (h : LeadsBy K K₁ P)
    (p : ι → Bool) : LeadsBy (K.restrict p) (K₁.restrict p) P := by
  intro r a b
  simp only [KrausMap.restrict, Matrix.diagonal_mul, h r]

theorem LeadsBy.permConj_refl {K K₁ : KrausMap R ι ι} {P : Equiv.Perm ι} (h : LeadsBy K K₁ P)
    (τ : Equiv.Perm ι) :
    LeadsBy (K.permConj (Equiv.refl ι) τ) (K₁.permConj (Equiv.refl ι) τ) P := by
  intro r a b
  simp only [KrausMap.permConj, Matrix.submatrix_apply, Equiv.refl_apply, h r]

/-- **`K` keeps the basis permutation `σ`**: `K.op r (σ a) (σ b) = K.op r a b`. -/
def KeepsPerm (K : KrausMap R ι ι) (σ : Equiv.Perm ι) : Prop :=
  ∀ r a b, K.op r (σ a) (σ b) = K.op r a b

/-- **`K` reads the register `g` of its columns as `f` of its rows**: its nonzero entries have
rows `a` and columns `b` with `f a = g b`; with `f = g`, `K` keeps the register. -/
def KeepsReg {V : Type*} (K : KrausMap R ι ι) (f g : ι → V) : Prop :=
  ∀ r a b, K.op r a b ≠ 0 → f a = g b

theorem KeepsReg.mono_left {V : Type*} {K : KrausMap R ι ι} {f f' g : ι → V}
    (h : K.KeepsReg f g) (hf : ∀ a, f' a = f a) : K.KeepsReg f' g := fun r a b hab => by
  rw [hf]
  exact h r a b hab

theorem keepsPerm_ofPerm {π σ : Equiv.Perm ι} (h : ∀ a, π (σ a) = σ (π a)) :
    (ofPerm π).KeepsPerm σ := fun r a b => by
  have hs : π.symm (σ a) = σ (π.symm a) :=
    (Equiv.symm_apply_eq π).2 (by rw [h, Equiv.apply_symm_apply])
  rw [ofPerm_op_apply', ofPerm_op_apply', hs]
  exact if_congr σ.injective.eq_iff rfl rfl

theorem keepsReg_ofPerm {V : Type*} (π : Equiv.Perm ι) (g : ι → V) :
    (ofPerm π).KeepsReg (fun a => g (π.symm a)) g := fun r a b hab => by
  rw [ofPerm_op_apply'] at hab
  by_cases he : π.symm a = b
  · exact congrArg g he
  · exact absurd (if_neg he) hab

theorem keepsReg_ofPerm_of {V : Type*} {π : Equiv.Perm ι} {f : ι → V} (h : ∀ a, f (π a) = f a) :
    (ofPerm π).KeepsReg f f :=
  (keepsReg_ofPerm π f).mono_left fun a => by rw [← h (π.symm a), Equiv.apply_symm_apply]

theorem KeepsPerm.comp {R' : Type*} [Fintype R'] {K₂ : KrausMap R' ι ι} {K : KrausMap R ι ι}
    {σ : Equiv.Perm ι} (h₂ : K₂.KeepsPerm σ) (h : K.KeepsPerm σ) : (K₂.comp K).KeepsPerm σ := by
  rintro ⟨r, r'⟩ a b
  change (K₂.op r' * K.op r) (σ a) (σ b) = (K₂.op r' * K.op r) a b
  simp only [Matrix.mul_apply]
  rw [← Equiv.sum_comp σ]
  simp only [h₂ r', h r]

theorem KeepsReg.comp {R' V : Type*} [Fintype R'] {K₂ : KrausMap R' ι ι} {K : KrausMap R ι ι}
    {f h' g : ι → V} (h₂ : K₂.KeepsReg f h') (h : K.KeepsReg h' g) :
    (K₂.comp K).KeepsReg f g := by
  rintro ⟨r, r'⟩ a b hab
  change (K₂.op r' * K.op r) a b ≠ 0 at hab
  obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rwa [Matrix.mul_apply] at hab)
  exact (h₂ r' a c (left_ne_zero_of_mul hc)).trans (h r c b (right_ne_zero_of_mul hc))

theorem KeepsPerm.tensorId {K : KrausMap R ι ι} {σ : Equiv.Perm ι} (h : K.KeepsPerm σ)
    {Z : Type*} [Fintype Z] [DecidableEq Z] (τ : Equiv.Perm Z) :
    (K.tensorId Z).KeepsPerm (σ.prodCongr τ) := by
  rintro r ⟨a, c⟩ ⟨b, d⟩
  simp only [KrausMap.tensorId, kroneckerMap_apply, Equiv.prodCongr_apply, Prod.map, h r,
    Matrix.one_apply, τ.injective.eq_iff]

theorem keepsReg_tensorId_snd {V : Type*} (K : KrausMap R ι ι) {Z : Type*} [Fintype Z]
    [DecidableEq Z] (g : Z → V) : (K.tensorId Z).KeepsReg (fun p => g p.2) fun p => g p.2 := by
  rintro r ⟨a, c⟩ ⟨b, d⟩ hab
  simp only [KrausMap.tensorId, kroneckerMap_apply, Matrix.one_apply] at hab
  by_cases hcd : c = d
  · rw [hcd]
  · rw [if_neg hcd, mul_zero] at hab
    exact absurd rfl hab

theorem KeepsReg.tensorId_fst {V : Type*} {K : KrausMap R ι ι} {f g : ι → V}
    (h : K.KeepsReg f g) {Z : Type*} [Fintype Z] [DecidableEq Z] :
    (K.tensorId Z).KeepsReg (fun p => f p.1) fun p => g p.1 := by
  rintro r ⟨a, c⟩ ⟨b, d⟩ hab
  simp only [KrausMap.tensorId, kroneckerMap_apply] at hab
  exact h r a b (left_ne_zero_of_mul hab)

theorem KeepsReg.tensorId_pair {V : Type*} {K : KrausMap R ι ι} {f g : ι → V}
    (h : K.KeepsReg f g) {Z : Type*} [Fintype Z] [DecidableEq Z] :
    (K.tensorId Z).KeepsReg (fun p => (f p.1, p.2)) fun p => (g p.1, p.2) := by
  rintro r ⟨a, c⟩ ⟨b, d⟩ hab
  simp only [KrausMap.tensorId, kroneckerMap_apply, Matrix.one_apply] at hab
  by_cases hcd : c = d
  · subst hcd
    exact Prod.ext (h r a b (left_ne_zero_of_mul hab)) rfl
  · rw [if_neg hcd, mul_zero] at hab
    exact absurd rfl hab

theorem KeepsPerm.reindex {K : KrausMap R ι ι} {σ : Equiv.Perm ι} (h : K.KeepsPerm σ)
    (e : ι ≃ κ) : (K.reindex e).KeepsPerm (e.permCongr σ) := fun r a b => by
  simp only [KrausMap.reindex, Matrix.submatrix_apply, Equiv.permCongr_apply,
    Equiv.symm_apply_apply, h r]

theorem KeepsReg.reindex {V : Type*} {K : KrausMap R ι ι} {f g : ι → V} (h : K.KeepsReg f g)
    (e : ι ≃ κ) : (K.reindex e).KeepsReg (fun a => f (e.symm a)) fun a => g (e.symm a) :=
  fun r _ _ hab =>
  h r _ _ hab

theorem KeepsPerm.restrict {K : KrausMap R ι ι} {σ : Equiv.Perm ι} (h : K.KeepsPerm σ)
    {p : ι → Bool} (hp : ∀ a, p (σ a) = p a) : (K.restrict p).KeepsPerm σ := fun r a b => by
  simp only [KrausMap.restrict, Matrix.diagonal_mul, hp, h r]

theorem KeepsReg.restrict {V : Type*} {K : KrausMap R ι ι} {f g : ι → V} (h : K.KeepsReg f g)
    (p : ι → Bool) : (K.restrict p).KeepsReg f g := fun r a b hab => by
  simp only [KrausMap.restrict, Matrix.diagonal_mul] at hab
  exact h r a b (right_ne_zero_of_mul hab)

theorem KeepsPerm.permConj_refl {K : KrausMap R ι ι} {σ : Equiv.Perm ι} (h : K.KeepsPerm σ)
    {τ : Equiv.Perm ι} (hτ : ∀ a, τ (σ a) = σ (τ a)) :
    (K.permConj (Equiv.refl ι) τ).KeepsPerm σ := fun r a b => by
  have : τ.symm (σ a) = σ (τ.symm a) := by
    rw [Equiv.symm_apply_eq, hτ, Equiv.apply_symm_apply]
  simp only [KrausMap.permConj, Matrix.submatrix_apply, Equiv.refl_apply, this, h r]

theorem KeepsReg.permConj_refl {V : Type*} {K : KrausMap R ι ι} {f g : ι → V}
    (h : K.KeepsReg f g) (τ : Equiv.Perm ι) :
    (K.permConj (Equiv.refl ι) τ).KeepsReg (fun a => f (τ.symm a)) g := fun r a b hab => by
  simp only [KrausMap.permConj, Matrix.submatrix_apply, Equiv.refl_apply] at hab
  exact h r _ _ hab

omit [Fintype ι] [DecidableEq ι] in
/-- **An entry along a kept permutation**: if `M` keeps `π` and the register `f`, and `πr` agrees
with `π` on the rows with the column's `f` and keeps the rows with another `f` off the column's,
then `M (πr z) (π u) = M z u`. -/
theorem _root_.Matrix.entry_perm_of_keeps {V : Type*} {M : Matrix ι ι ℂ} {π πr : Equiv.Perm ι}
    {f : ι → V} (hc : ∀ a b, M (π a) (π b) = M a b) (hk : ∀ a b, M a b ≠ 0 → f a = f b)
    {u : ι} (h3 : ∀ z, f z = f u → πr z = π z) (h4 : ∀ z, f z ≠ f u → f (πr z) ≠ f (π u))
    (z : ι) : M (πr z) (π u) = M z u := by
  by_cases hz : f z = f u
  · rw [h3 z hz, hc]
  · have h1 : M z u = 0 := by
      by_contra h
      exact hz (hk _ _ h)
    have h2 : M (πr z) (π u) = 0 := by
      by_contra h
      exact h4 z hz (hk _ _ h)
    rw [h1, h2]

/-- **The completed operators along a move of the system that keeps the flag**, from the live
operators after `P`, the halting operator after `P`, and the identity on the halted branches. -/
theorem completeOp_flagPerm {K : KrausMap R ι ι} {P σrF σrT σc : Equiv.Perm ι} (a b : ι)
    (fa fb : Bool)
    (hl : fa = false → fb = false → ∀ r, K.op r (σrF a) (P (σc b)) = K.op r a (P b))
    (hh : fa = true → fb = false → K.haltOp (σrT a) (P (σc b)) = K.haltOp a (P b))
    (hf : fa = true → fb = true → (σrT a = σc b ↔ a = b)) (r : R ⊕ Bool) :
    K.completeOp r (cond fa (σrT a) (σrF a), fa) (flagPerm P (Equiv.refl ι) (σc b, fb)) =
      K.completeOp r (a, fa) (flagPerm P (Equiv.refl ι) (b, fb)) := by
  rcases r with r | _ | _ <;> cases fa <;> cases fb <;>
    simp only [completeOp, kroneckerMap_apply, Matrix.single_apply, flagPerm_false,
      flagPerm_true, cond_false, cond_true, Equiv.refl_apply] <;>
    simp_all [Matrix.one_apply]

end KrausMap

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [AddGroup Y]
  {ksA : KindShape X Y Req Resp} (A : KindAlg ksA O)
  (K₁ : StepIdx A.slots A.post →
    KrausMap A.R (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp))
  (P : StepIdx A.slots A.post → Equiv.Perm (DReg A.W A.width X Y Req Resp))

/-- **The dilated distinguisher with leading unitaries and its post batches as slots.** -/
noncomputable abbrev leadPost [DecidableEq O] (o : O) :=
  (A.leadDilate K₁ P o).withPostSlots (fun j => A.leadUStepD K₁ P (A.slots + 1 + j)) A.post

theorem flagPerm_refl_refl {ι : Type*} : flagPerm (Equiv.refl ι) (Equiv.refl ι) = Equiv.refl _ := by
  ext ⟨i, b⟩ <;> cases b <;> rfl

/-- With no leading unitaries the dilated step is the dilated step. -/
theorem leadUStepD_refl (k : ℕ) :
    A.leadUStepD (fun k => A.step k) (fun _ => Equiv.refl _) k = A.uStepD k := by
  unfold leadUStepD uStepD leadUStep uStep
  split_ifs
  · have hp : ∀ w : QState ((DReg A.W A.width X Y Req Resp × Bool) × A.DAnc),
        permOp ((Equiv.refl (DReg A.W A.width X Y Req Resp × Bool)).prodCongr
          (Equiv.refl A.DAnc)) w = w := fun w => by
      ext
      rfl
    ext v p
    simp only [LinearIsometryEquiv.trans_apply, flagPerm_refl_refl, MixedAlg.liftPerm, hp]
  · rfl

/-- **With no leading unitaries the dilated distinguisher with its post batches as slots is the
one of `dilate`.** -/
theorem leadPost_refl [DecidableEq O] (o : O) :
    A.leadPost (fun k => A.step k) (fun _ => Equiv.refl _) o =
      (A.dilate o).withPostSlots (fun j => A.uStepD (A.slots + 1 + j)) A.post := by
  have hD : A.leadDilate (fun k => A.step k) (fun _ => Equiv.refl _) o = A.dilate o := by
    simp only [leadDilate, leadUStepD_refl]
    exact Distinguisher.with_step_eq _ _ (funext fun k => (A.dilate_step o k).symm)
  simp only [leadPost, hD, leadUStepD_refl]

variable {A K₁ P}

open Classical in
/-- **The steps of the dilated distinguisher with leading unitaries and its post batches as slots
along moves of the adversary's registers**: its entries at a column whose ancilla register `k` is
clean are kept when the completed operators of step `k` are. -/
theorem unitaryMat_leadPost_stepAt [DecidableEq O] (o : O) (k : ℕ)
    (hk : k < A.slots + A.post + 1) (y x : DReg (A.DW × Bool) A.width X Y Req Resp)
    (hx : (A.relD.symm (flagSplitD x).1).2.2.1 ⟨k, hk⟩ = Classical.arbitrary (A.R ⊕ Bool))
    (σr σc : Equiv.Perm (DReg A.W A.width X Y Req Resp))
    (h : ∀ r, (K₁ ⟨k, hk⟩).completeOp r
        (σr (A.relD.symm (flagSplitD y).1).1.1, (A.relD.symm (flagSplitD y).1).1.2)
        (flagPerm (P ⟨k, hk⟩) (Equiv.refl _)
          (σc (A.relD.symm (flagSplitD x).1).1.1, (A.relD.symm (flagSplitD x).1).1.2)) =
      (K₁ ⟨k, hk⟩).completeOp r (A.relD.symm (flagSplitD y).1).1
        (flagPerm (P ⟨k, hk⟩) (Equiv.refl _) (A.relD.symm (flagSplitD x).1).1)) :
    unitaryMat ((A.leadPost K₁ P o).stepAt k)
        (Distinguisher.flagPermLift (A.sysLift σr) y)
        (Distinguisher.flagPermLift (A.sysLift σc) x) =
      unitaryMat ((A.leadPost K₁ P o).stepAt k) y x := by
  have hU : ∀ y' : DReg (A.DW × Bool) A.width X Y Req Resp,
      (flagSplitD y').1 = (flagSplitD y).1 →
      unitaryMat (A.leadUStepD K₁ P k) (A.sysLift σr (flagSplitD y').1)
        (A.sysLift σc (flagSplitD x).1) =
      unitaryMat (A.leadUStepD K₁ P k) (flagSplitD y').1 (flagSplitD x).1 :=
    fun y' hy' => by
      rw [hy']
      exact unitaryMat_leadUStepD_sysLift k hk _ _ hx σr σc h
  have hstep : (A.leadPost K₁ P o).stepAt k =
      (A.leadDilate K₁ P o).postSlotStep (fun j => A.leadUStepD K₁ P (A.slots + 1 + j)) k := by
    unfold Distinguisher.stepAt
    rw [dif_pos hk]
    rfl
  have hdil : ∀ j ≤ A.slots, (A.leadDilate K₁ P o).stepAt j = A.leadUStepD K₁ P j :=
    fun j hj => by
      unfold Distinguisher.stepAt
      rw [dif_pos (Nat.lt_succ_of_le hj)]
      rfl
  rw [hstep]
  unfold Distinguisher.postSlotStep
  split_ifs with h1 h2
  · rw [hdil k h1.le]
    exact Distinguisher.unitaryMat_flagLift_perm _ _ _ _ _ (hU y rfl)
  · subst h2
    rw [hdil A.slots le_rfl]
    change unitaryMat (flagLift (A.leadUStepD K₁ P A.slots))
        (flagFlip (Distinguisher.flagPermLift (A.sysLift σr) y))
        (Distinguisher.flagPermLift (A.sysLift σc) x) =
      unitaryMat (flagLift (A.leadUStepD K₁ P A.slots)) (flagFlip y) x
    erw [Distinguisher.flagFlip_flagPermLift]
    exact Distinguisher.unitaryMat_flagLift_perm _ _ _ _ _ (hU _ rfl)
  · have hk' : A.slots + 1 + (k - A.slots - 1) = k := by omega
    change unitaryMat (flagLift (A.leadUStepD K₁ P (A.slots + 1 + (k - A.slots - 1)))) _ _ =
      unitaryMat (flagLift (A.leadUStepD K₁ P (A.slots + 1 + (k - A.slots - 1)))) _ _
    rw [hk']
    exact Distinguisher.unitaryMat_flagLift_perm _ _ _ _ _ (hU y rfl)

open Classical in
/-- **The steps of the dilated distinguisher with its post batches as slots along moves of the
adversary's registers**: its entries at a column whose ancilla register `k` is clean are kept when
the completed operators of step `k` are. -/
theorem unitaryMat_dilatePost_stepAt {ksA : KindShape X Y Req Resp} (A : KindAlg ksA O) [DecidableEq O] (o : O) (k : ℕ)
    (hk : k < A.slots + A.post + 1) (y x : DReg (A.DW × Bool) A.width X Y Req Resp)
    (hx : (A.relD.symm (flagSplitD x).1).2.2.1 ⟨k, hk⟩ = Classical.arbitrary (A.R ⊕ Bool))
    (σr σc : Equiv.Perm (DReg A.W A.width X Y Req Resp))
    (h : ∀ r, (A.step ⟨k, hk⟩).completeOp r
        (σr (A.relD.symm (flagSplitD y).1).1.1, (A.relD.symm (flagSplitD y).1).1.2)
        (σc (A.relD.symm (flagSplitD x).1).1.1, (A.relD.symm (flagSplitD x).1).1.2) =
      (A.step ⟨k, hk⟩).completeOp r (A.relD.symm (flagSplitD y).1).1
        (A.relD.symm (flagSplitD x).1).1) :
    unitaryMat (((A.dilate o).withPostSlots (fun i => A.uStepD (A.slots + 1 + i)) A.post).stepAt k)
        (Distinguisher.flagPermLift (A.sysLift σr) y)
        (Distinguisher.flagPermLift (A.sysLift σc) x) =
      unitaryMat (((A.dilate o).withPostSlots (fun i => A.uStepD (A.slots + 1 + i))
          A.post).stepAt k)
        y x := by
  rw [← leadPost_refl]
  refine unitaryMat_leadPost_stepAt o k hk y x hx σr σc fun r => ?_
  simp only [flagPerm_refl_refl, Equiv.refl_apply]
  exact h r

open Classical in
/-- **The nonzero entries of the dilated distinguisher's steps with leading unitaries and post
batches as slots** at a column whose ancilla register `k` is clean: the post flag flipped exactly at
step `slots`, a nonzero completed operator of the row's ancilla register `k` from the column after
`P`, and the rest of the ancilla kept. -/
theorem leadPost_stepAt_ne_zero [DecidableEq O] (o : O) (k : ℕ)
    (hk : k < A.slots + A.post + 1) (y x : DReg (A.DW × Bool) A.width X Y Req Resp)
    (hx : (A.relD.symm (flagSplitD x).1).2.2.1 ⟨k, hk⟩ = Classical.arbitrary (A.R ⊕ Bool))
    (h : unitaryMat ((A.leadPost K₁ P o).stepAt k) y x ≠ 0) :
    (flagSplitD y).2 = (if k = A.slots then !(flagSplitD x).2 else (flagSplitD x).2) ∧
      (K₁ ⟨k, hk⟩).completeOp ((A.relD.symm (flagSplitD y).1).2.2.1 ⟨k, hk⟩)
        (A.relD.symm (flagSplitD y).1).1
        (flagPerm (P ⟨k, hk⟩) (Equiv.refl _) (A.relD.symm (flagSplitD x).1).1) ≠ 0 ∧
      (A.relD.symm (flagSplitD x).1).2 = (MixedAlg.stepSplit ⟨k, hk⟩).symm
        (Classical.arbitrary _, (MixedAlg.stepSplit ⟨k, hk⟩ (A.relD.symm (flagSplitD y).1).2).2)
            := by
  have hU : ∀ y' : DReg (A.DW × Bool) A.width X Y Req Resp,
      unitaryMat (A.leadUStepD K₁ P k) (flagSplitD y').1 (flagSplitD x).1 ≠ 0 →
      (K₁ ⟨k, hk⟩).completeOp ((A.relD.symm (flagSplitD y').1).2.2.1 ⟨k, hk⟩)
        (A.relD.symm (flagSplitD y').1).1
        (flagPerm (P ⟨k, hk⟩) (Equiv.refl _) (A.relD.symm (flagSplitD x).1).1) ≠ 0 ∧
      (A.relD.symm (flagSplitD x).1).2 = (MixedAlg.stepSplit ⟨k, hk⟩).symm
        (Classical.arbitrary _, (MixedAlg.stepSplit ⟨k, hk⟩ (A.relD.symm (flagSplitD y').1).2).2) :=
    fun y' h' => by
      rw [unitaryMat_leadUStepD k hk _ _ hx] at h'
      refine ⟨left_ne_zero_of_mul h', ?_⟩
      by_contra hne
      rw [if_neg hne, mul_zero] at h'
      exact h' rfl
  have hfl : ∀ (U : QState (DReg A.DW A.width X Y Req Resp) ≃ₗᵢ[ℂ]
      QState (DReg A.DW A.width X Y Req Resp)) (y' : DReg (A.DW × Bool) A.width X Y Req Resp),
      unitaryMat (flagLift U) y' x ≠ 0 →
      (flagSplitD y').2 = (flagSplitD x).2 ∧ unitaryMat U (flagSplitD y').1 (flagSplitD x).1 ≠ 0 :=
    fun U y' h' => by
      have e : flagLift U = (Quantum.relabel flagSplitD).trans
          ((controlled fun _ => U).trans (Quantum.relabel flagSplitD).symm) := by
        rw [relabel_symm]
        rfl
      rw [e, unitaryMat_relabel_controlled] at h'
      split_ifs at h' with hf
      · exact ⟨hf, h'⟩
      · exact absurd rfl h'
  have hstep : (A.leadPost K₁ P o).stepAt k =
      (A.leadDilate K₁ P o).postSlotStep (fun j => A.leadUStepD K₁ P (A.slots + 1 + j)) k := by
    unfold Distinguisher.stepAt
    rw [dif_pos hk]
    rfl
  have hdil : ∀ j ≤ A.slots, (A.leadDilate K₁ P o).stepAt j = A.leadUStepD K₁ P j :=
    fun j hj => by
      unfold Distinguisher.stepAt
      rw [dif_pos (Nat.lt_succ_of_le hj)]
      rfl
  rw [hstep] at h
  unfold Distinguisher.postSlotStep at h
  split_ifs at h with h1 h2
  · rw [hdil k h1.le] at h
    obtain ⟨hf, h'⟩ := hfl _ y h
    exact ⟨by rw [if_neg (by omega), hf], hU y h'⟩
  · subst h2
    rw [hdil A.slots le_rfl] at h
    change unitaryMat (flagLift (A.leadUStepD K₁ P A.slots)) (flagFlip y) x ≠ 0 at h
    obtain ⟨hf, h'⟩ := hfl _ _ h
    refine ⟨?_, hU (flagFlip y) h'⟩
    rw [if_pos rfl, ← hf]
    obtain ⟨g, d, rfl⟩ := exists_withFlag y
    rw [flagFlip_withFlag]
    simp [withFlag, flagSplitD]
  · have hk' : A.slots + 1 + (k - A.slots - 1) = k := by omega
    change unitaryMat (flagLift (A.leadUStepD K₁ P (A.slots + 1 + (k - A.slots - 1)))) y x ≠ 0
      at h
    rw [hk'] at h
    obtain ⟨hf, h'⟩ := hfl _ y h
    exact ⟨by rw [if_neg (by omega), hf], hU y h'⟩

open Classical in
/-- **The nonzero entries of the dilated distinguisher's steps with its post batches as slots** at
a column whose ancilla register `k` is clean (`leadPost_stepAt_ne_zero` without leading
unitaries). -/
theorem dilatePost_stepAt_ne_zero {ksA : KindShape X Y Req Resp} (A : KindAlg ksA O) [DecidableEq O] (o : O) (k : ℕ)
    (hk : k < A.slots + A.post + 1) (y x : DReg (A.DW × Bool) A.width X Y Req Resp)
    (hx : (A.relD.symm (flagSplitD x).1).2.2.1 ⟨k, hk⟩ = Classical.arbitrary (A.R ⊕ Bool))
    {inst : DecidableEq (DReg (A.DW × Bool) A.width X Y Req Resp)}
    (h : @unitaryMat _ _ inst (((A.dilate o).withPostSlots (fun i => A.uStepD (A.slots + 1 + i))
      A.post).stepAt k) y x ≠ 0) :
    (flagSplitD y).2 = (if k = A.slots then !(flagSplitD x).2 else (flagSplitD x).2) ∧
      (A.step ⟨k, hk⟩).completeOp ((A.relD.symm (flagSplitD y).1).2.2.1 ⟨k, hk⟩)
        (A.relD.symm (flagSplitD y).1).1 (A.relD.symm (flagSplitD x).1).1 ≠ 0 ∧
      (A.relD.symm (flagSplitD x).1).2 = (MixedAlg.stepSplit ⟨k, hk⟩).symm
        (Classical.arbitrary _, (MixedAlg.stepSplit ⟨k, hk⟩ (A.relD.symm (flagSplitD y).1).2).2)
            := by
  have h' : @unitaryMat _ _ (fun a b => DReg.instDecidableEq a b)
      (((A.dilate o).withPostSlots (fun i => A.uStepD (A.slots + 1 + i))
      A.post).stepAt k) y x ≠ 0 := by
    convert h
  rw [← leadPost_refl] at h'
  have := leadPost_stepAt_ne_zero o k hk y x hx h'
  rw [flagPerm_refl_refl, Equiv.refl_apply] at this
  exact this

/-- **A completed operator's nonzero entry at a live column** is a live entry of the operator when
the halting operator vanishes. -/
theorem _root_.GordieHowe.Quantum.KrausMap.completeOp_ne_zero_of_live {R ι : Type*} [Fintype R]
    [Fintype ι] [DecidableEq ι]
    {K : KrausMap R ι ι} (hK : K.haltOp = 0) {r : R ⊕ Bool} {a b : ι} {fa : Bool}
    (h : K.completeOp r (a, fa) (b, false) ≠ 0) :
    ∃ z, r = .inl z ∧ fa = false ∧ K.op z a b ≠ 0 := by
  rcases r with z | c
  · refine ⟨z, rfl, ?_⟩
    simp only [KrausMap.completeOp, kroneckerMap_apply, Matrix.single_apply] at h
    cases fa
    · exact ⟨rfl, by simpa using h⟩
    · simp at h
  · cases c <;> simp [KrausMap.completeOp, kroneckerMap_apply, Matrix.single_apply, hK] at h

/-- **The ancilla after step `k`, read from the column's**: clean from `k + 1` on when the
column's is clean from `k` on and differs from the row's only in register `k`. -/
theorem _root_.GordieHowe.Quantum.MixedAlg.clean_succ_of_reset {ι R M : Type*} [Nonempty R]
    [Nonempty M] {d n : ℕ}
    (hn : n < d + 1) {a b : MixedAlg.Anc ι d R M} (hb : MixedAlg.Clean n b)
    (hab : b = (MixedAlg.stepSplit ⟨n, hn⟩).symm
      (Classical.arbitrary R, (MixedAlg.stepSplit ⟨n, hn⟩ a).2)) : MixedAlg.Clean (n + 1) a := by
  rw [MixedAlg.stepSplit_symm_reset] at hab
  subst hab
  refine ⟨fun j hj => ?_, hb.2⟩
  have hne : j ≠ ⟨n, hn⟩ := fun h' => by
    rw [h'] at hj
    exact Nat.not_succ_le_self n hj
  have := hb.1 j (Nat.le_of_succ_le hj)
  simp only at this
  rwa [Function.update_of_ne hne] at this

end KindAlg

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [AddGroup Y]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O)
  (K₁ : StepIdx A.slots A.post →
    KrausMap (A.toTPKindAlg true).R (DReg (A.toTPKindAlg true).W A.width X Y Req Resp)
      (DReg (A.toTPKindAlg true).W A.width X Y Req Resp))
  (P : StepIdx A.slots A.post → Equiv.Perm (DReg (A.toTPKindAlg true).W A.width X Y Req Resp))

/-- The post batches of the dilated adversary with leading unitaries as unitaries. -/
noncomputable def leadPostU (j : ℕ) :
    QState (DReg (A.toTPKindAlg true).unitOut.DW (A.toTPKindAlg true).unitOut.width X Y Req Resp)
        ≃ₗᵢ[ℂ]
      QState (DReg (A.toTPKindAlg true).unitOut.DW (A.toTPKindAlg true).unitOut.width X Y Req
          Resp) :=
  (A.toTPKindAlg true).unitOut.leadUStepD K₁ P (A.slots + 1 + j)

/-- **The pure distinguisher of an adversary with leading unitaries**: `pureD` (the dilated
trace-preserving form) with the steps `(A.toTPKindAlg true).step k = K₁ k` after `P k` dilated
    with `P k`
before the completed `K₁ k` (`KindAlg.leadDilate`). -/
noncomputable abbrev leadPureD :=
  ((A.toTPKindAlg true).unitOut.leadDilate K₁ P ()).withPostSlots (A.leadPostU K₁ P) A.post

variable {A K₁ P}

/-- **The pure distinguisher with leading unitaries accepts as the pure distinguisher**, on every
set of logs, for a final unitary that keeps the halted branches halted: a unitary cannot halt, so
where the halting measurement sits relative to it changes no outcome probability. -/
theorem leadPureD_acceptProbOnAt
    (hK : ∀ k r a b, ((A.toTPKindAlg true).step k).op r a b = (K₁ k).op r a (P k b))
    {Ω : Type*} {St : Type _} {Q : ℕ} [OracleState St X Y] (E : Env Ω Req Resp X Y Q St)
    (post : (X → Y) → QState (DReg ((A.toTPKindAlg true).unitOut.DW × Bool) A.width X Y Req Resp)
        ≃ₗᵢ[ℂ]
      QState (DReg ((A.toTPKindAlg true).unitOut.DW × Bool) A.width X Y Req Resp))
    (hpost : ∀ H v, Supported (Distinguisher.wsSetD
        (Distinguisher.flagW (A.toTPKindAlg true).unitOut.liveW)ᶜ) v →
      Supported (Distinguisher.wsSetD (Distinguisher.flagW (A.toTPKindAlg true).unitOut.liveW)ᶜ)
        (post H v))
    (L : Set (LogReg Req (A.slots + A.post))) (ω : Ω) :
    (A.leadPureD K₁ P).acceptProbOnAt E post L ω = A.pureD.acceptProbOnAt E post L ω := by
  rw [A.pureD_eq]
  refine ((((A.toTPKindAlg true).unitOut.liveRel_leadDilate hK ()).withPostSlots
    KindAlg.cleanW_mono _ _ A.post fun k hk => ?_).acceptProbOnAt_eq E post hpost L ω)
  have hk' : A.slots + 1 + (k - A.slots - 1) = k := by
    change A.slots < k at hk
    omega
  change Distinguisher.StepRel _ _ _ ((A.toTPKindAlg true).unitOut.uStepD (A.slots + 1 + (k -
      A.slots - 1)))
    ((A.toTPKindAlg true).unitOut.leadUStepD K₁ P (A.slots + 1 + (k - A.slots - 1)))
  rw [hk']
  exact KindAlg.stepRel_uStepD hK k

end AdaptiveIAlg

end GordieHowe.Quantum
