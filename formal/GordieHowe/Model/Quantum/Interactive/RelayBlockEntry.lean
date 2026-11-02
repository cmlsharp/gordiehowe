-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.MultiRelayCount
public import GordieHowe.Model.Quantum.Interactive.PureTest

@[expose] public section

/-!
# The entries of the relayed distinguisher's steps

The matrix entries (`unitaryMat`) of the steps of the relayed distinguisher
(`Distinguisher.relay`, `GordieHowe/Model/Quantum/Pure/MultiRelay.lean`), read through its basis
permutations:

- `permOp_single`, `unitaryMat_permOp`: a basis permutation moves a basis vector.
- `unitaryMat_relabel_controlled`: the entries of a controlled unitary read through a split of the
  registers: those of the unitary of the control's value when the controls agree, else zero.
- `Distinguisher.preFun`: the tear-down, the clock, the side additions and the reply before step
  `k > 0`.
- `Distinguisher.ctrlU`, `Distinguisher.unitaryMat_ctrlStep`: the entries of the distinguisher's
  controlled step.
- `Distinguisher.unitaryMat_relay_step` (**the entries of a step**): the entry of step `k` at the
  rows `a` and the columns `b` is the controlled step's entry at the record and set-up of `a`
  undone and the tear-down, clock and reply of `b`.
- `Distinguisher.innerMap`, `Distinguisher.relaySplit_innerMap`, `Distinguisher.rest_innerMap`,
  `Distinguisher.unitaryMat_ctrlStep_innerMap`: permutations of the distinguisher's registers and of
  the rest on the relayed registers, and the controlled step's entries along two of them.
-/

open Matrix

namespace GordieHowe.Quantum

section Basic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A basis permutation moves a basis vector.** -/
theorem permOp_single (π : Equiv.Perm ι) (b : ι) :
    permOp π (EuclideanSpace.single b (1 : ℂ)) = EuclideanSpace.single (π b) 1 := by
  ext i
  simp only [permOp_apply, PiLp.single_apply, Equiv.symm_apply_eq]

/-- The entries of a basis permutation. -/
theorem unitaryMat_permOp (π : Equiv.Perm ι) (a b : ι) :
    unitaryMat (permOp π) a b = if a = π b then 1 else 0 := by
  simp only [unitaryMat, permOp_single, PiLp.single_apply]

/-- The entries of the identity. -/
theorem unitaryMat_refl (a b : ι) :
    unitaryMat (LinearIsometryEquiv.refl ℂ (QState ι)) a b = (1 : Matrix ι ι ℂ) a b := by
  change (EuclideanSpace.single b (1 : ℂ)) a = _
  simp only [PiLp.single_apply, Matrix.one_apply]

/-- **The entries of a controlled unitary read through a split of the registers**: those of the
unitary of the control's value when the controls agree, else zero. -/
theorem unitaryMat_relabel_controlled {κ L : Type*} [Fintype κ] [DecidableEq κ] [Fintype L]
    [DecidableEq L] (e : ι ≃ κ × L) (U : L → QState κ ≃ₗᵢ[ℂ] QState κ) (x y : ι) :
    unitaryMat ((relabel e).trans ((controlled U).trans (relabel e).symm)) x y =
      if (e x).2 = (e y).2 then unitaryMat (U (e y).2) (e x).1 (e y).1 else 0 := by
  have hv : (WithLp.toLp 2 fun i' => relabel e (EuclideanSpace.single y (1 : ℂ)) (i', (e x).2) :
      QState κ) = if (e x).2 = (e y).2 then EuclideanSpace.single (e y).1 1 else 0 := by
    by_cases h : (e x).2 = (e y).2
    · simp only [h, ↓reduceIte]
      ext i'
      simp [relabel_apply, PiLp.single_apply, Equiv.symm_apply_eq, Prod.ext_iff]
    · simp only [h, ↓reduceIte]
      ext i'
      simp [relabel_apply, Equiv.symm_apply_eq, Prod.ext_iff, h]
  simp only [unitaryMat, LinearIsometryEquiv.trans_apply, relabel_symm, relabel_apply,
    Equiv.symm_symm]
  rw [controlled_apply, hv]
  split_ifs with h
  · rw [h]
  · simp

end Basic

namespace Distinguisher

variable {W X Y Req Resp Req' Resp' Xs Ys : Type} [Fintype W] [DecidableEq W] [Fintype X]
  [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Inhabited X] [Inhabited Req'] [AddGroup Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] {n m : ℕ}
  (D : Distinguisher W X Y Req Resp n m) (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (b Q : ℕ)

local notation "RR" => RelayReg W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)

/-- **The tear-down, the clock, the side additions and the reply before step `k`** (nothing before
step `0`). -/
def preFun (k : ℕ) (d : RR) : RR :=
  if k = 0 then d else finalizeFun F b Q (sideAddsPerm F b Q (tickPerm F (teardownFun F b Q d)))

/-- **The distinguisher's step at the controls `rest`**: its step numbered by the started slots
when their blocks end at the clock, the identity otherwise. -/
noncomputable def ctrlU (rest : RelayRest X Y Req Req' Resp' m (relaySlots n m F) (Fin F.qS → Ys)) :
    QState (DReg W n X Y Req Resp) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req Resp) :=
  if F.startAt n b Q (MultiRelay.recList rest.1) (MultiRelay.recList rest.1).length =
      (rest.2.2.2.1 : ℕ) then D.stepAt (MultiRelay.recList rest.1).length
  else LinearIsometryEquiv.refl ℂ _

omit [Inhabited X] [Inhabited Req'] [AddGroup Y] in
/-- **The entries of the distinguisher's controlled step**: those of the distinguisher's step at
the controls when the rest of the registers agree, else zero. -/
theorem unitaryMat_ctrlStep (x y : RR) :
    unitaryMat (D.ctrlStep F b Q) x y =
      if rest F x = rest F y then
        unitaryMat (D.ctrlU F b Q (rest F y))
          (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys) x).1
          (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys) y).1
      else 0 :=
  unitaryMat_relabel_controlled _ _ x y

/-- **The entries of a step of the relayed distinguisher**: the entry of step `k` at the rows `a`
and the columns `c` is the controlled step's entry at the record and set-up of `a` undone and the
tear-down, clock, side additions and reply of `c`. -/
theorem unitaryMat_relay_step (k : Fin (relaySlots n m F + 1)) (a c : RR) :
    unitaryMat ((D.relay F b Q).step k) a c =
      unitaryMat (D.ctrlStep F b Q)
        (recordFun F b Q D.kind (setupFun F b Q a))
        (preFun F b Q k c) := by
  have hpre : ((if (k : ℕ) = 0 then LinearIsometryEquiv.refl ℂ (QState RR) else
      permOp ((((teardownPerm F b Q).trans (tickPerm F)).trans (sideAddsPerm F b Q)).trans
        (finalizePerm F b Q)))
        (EuclideanSpace.single c 1)) = EuclideanSpace.single (preFun F b Q k c) 1 := by
    unfold preFun
    split_ifs
    · rfl
    · rw [permOp_single]
      rfl
  change ((permOp (setupPerm F b Q)) ((permOp (recordPerm F b Q D.kind))
    (D.ctrlStep F b Q ((if (k : ℕ) = 0 then LinearIsometryEquiv.refl ℂ (QState RR) else
      permOp ((((teardownPerm F b Q).trans (tickPerm F)).trans (sideAddsPerm F b Q)).trans
        (finalizePerm F b Q)))
        (EuclideanSpace.single c 1))))) a = _
  rw [hpre, permOp_apply, permOp_apply]
  rfl

/-- **Permutations of the distinguisher's registers and of the rest on the relayed registers.** -/
def innerMap (π : Equiv.Perm (DReg W n X Y Req Resp))
    (ρ : Equiv.Perm (RelayRest X Y Req Req' Resp' m (relaySlots n m F) (Fin F.qS → Ys))) :
    Equiv.Perm RR :=
  (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)).trans
    ((π.prodCongr ρ).trans
      (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)).symm)

omit [Fintype W] [DecidableEq W] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited X] [Inhabited Req']
  [AddGroup Y] in
theorem relaySplit_innerMap (π : Equiv.Perm (DReg W n X Y Req Resp))
    (ρ : Equiv.Perm (RelayRest X Y Req Req' Resp' m (relaySlots n m F) (Fin F.qS → Ys))) (x : RR) :
    relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys) (innerMap F π ρ x) =
      (π (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys) x).1,
        ρ (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys) x).2) := by
  simp only [innerMap, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

omit [Fintype W] [DecidableEq W] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited X] [Inhabited Req']
  [AddGroup Y] in
theorem rest_innerMap (π : Equiv.Perm (DReg W n X Y Req Resp))
    (ρ : Equiv.Perm (RelayRest X Y Req Req' Resp' m (relaySlots n m F) (Fin F.qS → Ys))) (x : RR) :
    rest F (innerMap F π ρ x) = ρ (rest F x) := by
  simp only [rest, relaySplit_innerMap]

omit [Inhabited X] [Inhabited Req'] [AddGroup Y] in
/-- **The controlled step's entries along permutations of the distinguisher's registers and of the
rest**: its entry at `innerMap π' ρ y` and `innerMap π ρ x` is the distinguisher's controlled
entry at the moved registers and the moved rest. -/
theorem unitaryMat_ctrlStep_innerMap (π' π : Equiv.Perm (DReg W n X Y Req Resp))
    (ρ : Equiv.Perm (RelayRest X Y Req Req' Resp' m (relaySlots n m F) (Fin F.qS → Ys)))
    (x y : RR) :
    unitaryMat (D.ctrlStep F b Q) (innerMap F π' ρ y) (innerMap F π ρ x) =
      if rest F y = rest F x then
        unitaryMat (D.ctrlU F b Q (ρ (rest F x)))
          (π' (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys) y).1)
          (π (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys) x).1)
      else 0 := by
  rw [unitaryMat_ctrlStep, rest_innerMap, rest_innerMap, relaySplit_innerMap,
    relaySplit_innerMap]
  simp only [ρ.injective.eq_iff]

end Distinguisher

end GordieHowe.Quantum
