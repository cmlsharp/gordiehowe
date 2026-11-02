-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.MultiRelayTrailing
public import GordieHowe.Model.Quantum.Pure.MultiRelaySideStore

@[expose] public section

/-!
# The relayed step as the side-free step followed by the side additions

A step `k > 0` of the relayed distinguisher (`Distinguisher.relay`) applies the side additions
(`sideAddsPerm`) in the middle of the step: after the tear-down and the clock, before the reply of
a finished relayed request, the distinguisher's step, the record and the set-up. Only the side
additions read the side function `F.side`; at the zero side function they are the identity
(`sideAddsPerm_withSide_zero`). For a relay without trailing side reads
(`MultiRelay.NoTrailingSides`), the additions commute with the reply of a finished relayed request
(`finalizePerm_sideAddsPerm`): at the step that finalizes it they are the identity
(`sideAddsPerm_of_finalize`). They commute with the distinguisher's step (`ctrlStep_sideAddsPerm`),
whose control reads only the record and the clock and which acts only on the distinguisher's
registers, while the additions write only the side store. So the side additions occur mid-step and
are moved after the step by conjugation with the rest of the step, the record and the set-up
(`relay_step_eq_withSide_zero`).

- `MultiRelay.withSide`: the relay with another side function; `MultiRelay.stAt_withSide`,
  `MultiRelay.pendSt_withSide`,
  `MultiRelay.actAt_withSide`, `MultiRelay.lastReply_withSide` (only the side additions read the
  side function); `MultiRelay.addVec_withSide_zero`, `MultiRelay.addsVec_withSide_zero`,
  `MultiRelay.addsVec_len`.
- `Distinguisher.perms_withSide`, `Distinguisher.ctrlStep_withSide`,
  `Distinguisher.relay_step_of_ne_zero`, `Distinguisher.relay_step_withSide_zero`.
- `Distinguisher.sideRest`: the side additions on the registers beside the distinguisher's;
  `Distinguisher.relaySplit_sideAddsPerm`.
- `Distinguisher.sideAddsPerm_withSide_zero`, `Distinguisher.sideAddsPerm_of_finalize`,
  `Distinguisher.finalizePerm_sideAddsPerm`, `Distinguisher.ctrlStep_comm`,
  `Distinguisher.ctrlStep_sideAddsPerm`, `Distinguisher.relay_step_eq_withSide_zero`.
-/

namespace GordieHowe.Quantum

namespace MultiRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)

/-- **The relay with the side function `s`**, everything else kept. -/
abbrev withSide (s : Xs → Ys) : MultiRelay X Y Req Resp Req' Resp' Xs Ys :=
  { F with side := s }

/-- **The states of a relayed request do not read the side function.** -/
theorem stAt_withSide [Inhabited X] (s : Xs → Ys) (sa : ℕ → Xs → Ys) (r : Req)
    (g : ℕ → Option Resp' × (X × Y)) : ∀ i, (F.withSide s).stAt sa r g i = F.stAt sa r g i
  | 0 => rfl
  | i + 1 => by
    change (F.withSide s).close sa r ((F.withSide s).next r ((F.withSide s).stAt sa r g i) (g i)) =
      F.close sa r (F.next r (F.stAt sa r g i) (g i))
    rw [stAt_withSide s sa r g i]
    rfl

/-- **The action of a sub-slot does not read the side function.** -/
theorem actAt_withSide [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] (s : Xs → Ys)
    (n b Q : ℕ) {m S : ℕ} (rec : Fin m → Option (Option Req))
    (store : Fin S → Option Resp' × (X × Y)) (side : Fin m → Fin F.qS → Ys) (t : ℕ) :
    (F.withSide s).actAt n b Q rec store side t = F.actAt n b Q rec store side t := by
  unfold actAt
  simp only [stAt_withSide]
  rfl

/-- **The reply of the last started slot does not read the side function.** -/
theorem lastReply_withSide [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] (s : Xs → Ys)
    (n b Q : ℕ) {m S : ℕ} (rec : Fin m → Option (Option Req))
    (store : Fin S → Option Resp' × (X × Y)) (side : Fin m → Fin F.qS → Ys) :
    (F.withSide s).lastReply n b Q rec store side = F.lastReply n b Q rec store side := by
  unfold lastReply
  simp only [stAt_withSide]
  rfl

/-- **The state before the side reads after a sub-slot, and after `i` of them, does not read the
side function.** -/
theorem pendSt_withSide [Inhabited X] (s : Xs → Ys) (sa : ℕ → Xs → Ys) (r : Req)
    (g : ℕ → Option Resp' × (X × Y)) (sub i : ℕ) :
    (F.withSide s).pendSt sa r g sub i = F.pendSt sa r g sub i := by
  unfold pendSt
  cases sub with
  | zero => rfl
  | succ j =>
    change ((F.withSide s).sideStep sa r)^[i] ((F.withSide s).next r ((F.withSide s).stAt sa r g j)
      (g j)) = (F.sideStep sa r)^[i] (F.next r (F.stAt sa r g j) (g j))
    rw [stAt_withSide]
    rfl

variable [Inhabited X] [Zero Y] [AddGroup Ys] [Inhabited Req']

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
/-- **At the zero side function a side addition is the identity.** -/
theorem addVec_withSide_zero (r : Req) (g : ℕ → Option Resp' × (X × Y)) (sub i : ℕ) (sgn : Bool)
    (v : Fin F.qS → Ys) : (F.withSide 0).addVec r g sub i sgn v = v := by
  have h0 : ∀ x, (F.withSide 0).side x = 0 := fun _ => rfl
  unfold addVec
  rcases (F.withSide 0).progAct r ((F.withSide 0).pendSt ((F.withSide 0).vecSa v) r g sub i) with
    _ | ((x | x) | r')
  · rfl
  · rfl
  · simp only
    by_cases hk : ((F.withSide 0).pendSt ((F.withSide 0).vecSa v) r g sub i).ns < F.qS
    · simp only [hk, ↓reduceDIte, Pi.zero_apply, neg_zero, ite_self, add_zero]
      exact Function.update_eq_self _ _
    · simp only [hk, ↓reduceDIte]
  · rfl

omit [Zero Y] [Inhabited Req'] in
/-- **At the zero side function the side additions are the identity.** -/
theorem addsVec_withSide_zero (r : Req) (g : ℕ → Option Resp' × (X × Y)) (sub : ℕ)
    (v : Fin F.qS → Ys) : (F.withSide 0).addsVec r g sub v = v := by
  rw [addsVec_eq]
  generalize List.range (F.withSide 0).qS = L
  induction L generalizing v with
  | nil => rfl
  | cons i L ih =>
    rw [List.foldl_cons, F.addVec_withSide_zero]
    exact ih v

omit [Zero Y] [Inhabited Req'] in
/-- **The side additions after the last sub-slot are the identity** without trailing side
reads. -/
theorem addsVec_len (hT : F.NoTrailingSides) (r : Req) (g : ℕ → Option Resp' × (X × Y))
    (v : Fin F.qS → Ys) : F.addsVec r g F.len v = v := by
  rw [addsVec_eq]
  generalize List.range F.qS = L
  induction L generalizing v with
  | nil => rfl
  | cons i L ih =>
    rw [List.foldl_cons, F.addVec_len hT]
    exact ih v

end MultiRelay

namespace Distinguisher

variable {W X Y Req Resp Req' Resp' Xs Ys : Type} [Fintype W] [DecidableEq W] [Fintype X]
  [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Inhabited X] [Inhabited Req'] [AddGroup Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] {n m : ℕ}
  (D : Distinguisher W X Y Req Resp n m) (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (b Q : ℕ)

local notation "RR" => RelayReg W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)
local notation "RS" => RelayRest X Y Req Req' Resp' m (relaySlots n m F) (Fin F.qS → Ys)
local notation "SP" => relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F)
  (Fin F.qS → Ys)

/-- **The side additions on the registers beside the distinguisher's**: the side store after
them (`sideAfter`), everything else kept. -/
def sideRest (l : RS) : RS :=
  (l.1, l.2.1, sideAfter F b Q l.1 l.2.1 l.2.2.1 l.2.2.2.1, l.2.2.2)

omit [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req]
  [Fintype Resp] [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] [Fintype Ys]
  [DecidableEq Ys] in
/-- **The side additions keep the distinguisher's registers** and act on the rest by
`sideRest`. -/
theorem relaySplit_sideAddsPerm (d : RR) :
    SP (sideAddsPerm F b Q d) = ((SP d).1, sideRest F b Q (SP d).2) := by
  rw [sideAddsPerm_apply]
  rfl

omit [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req]
  [Fintype Resp] [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] [Fintype Ys]
  [DecidableEq Ys] in
/-- **At the zero side function the side additions are the identity.** -/
theorem sideAddsPerm_withSide_zero :
    (sideAddsPerm (F.withSide 0) b Q : Equiv.Perm RR) = Equiv.refl _ := by
  refine Equiv.ext fun d => ?_
  rw [sideAddsPerm_apply, Equiv.refl_apply]
  obtain ⟨⟨⟨inn, rec, store, side, t⟩, rq, rs⟩, pr⟩ := d
  simp only
  split
  · split_ifs
    · rw [MultiRelay.addsVec_withSide_zero, Function.update_eq_self]
    · rfl
  · rfl

omit [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req]
  [Fintype Resp] [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] [Fintype Ys]
  [DecidableEq Ys] in
/-- **At the step that finalizes a relayed request the side additions are the identity**,
without trailing side reads: the relayed request in progress has done all its `len`
sub-slots. -/
theorem sideAddsPerm_of_finalize (hT : F.NoTrailingSides) (d : RR)
    (hc : F.startAt n b Q (MultiRelay.recList d.1.1.record)
      (MultiRelay.recList d.1.1.record).length =
      d.1.1.time) :
    sideAddsPerm F b Q d = d := by
  rw [sideAddsPerm_apply]
  obtain ⟨⟨⟨inn, rec, store, side, t⟩, rq, rs⟩, pr⟩ := d
  simp only at hc ⊢
  rcases hcur : F.curRel n b Q rec t with _ | ⟨j, r, sub⟩
  · rfl
  · simp only
    split_ifs with hj
    · have hsub : sub = F.len := by
        obtain ⟨hj', -, hs, -, -⟩ := F.curRel_eq_some hcur
        have hb := curRel_rel F b Q hcur
        have h0 : 0 < (MultiRelay.recList rec).length := by
          by_contra h0
          unfold MultiRelay.curRel at hcur
          simp only [h0, ↓reduceIte] at hcur
          cases hcur
        have hL : (MultiRelay.recList rec).length = j + 1 := by omega
        rw [hL, F.startAt_succ, hb] at hc
        change _ + F.len = _ at hc
        omega
      subst hsub
      rw [F.addsVec_len hT, Function.update_eq_self]
    · rfl

omit [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req]
  [Fintype Resp] [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] [Fintype Ys]
  [DecidableEq Ys] in
/-- **The side additions commute with the reply of a finished relayed request**, without
trailing side reads: both keep the record and the clock, and where the reply is written the
additions are the identity. -/
theorem finalizePerm_sideAddsPerm (hT : F.NoTrailingSides) (d : RR) :
    finalizePerm F b Q (sideAddsPerm F b Q d) = sideAddsPerm F b Q (finalizePerm F b Q d) := by
  change finalizeFun F b Q (sideAddsPerm F b Q d) = sideAddsPerm F b Q (finalizeFun F b Q d)
  by_cases hc : F.startAt n b Q (MultiRelay.recList d.1.1.record)
      (MultiRelay.recList d.1.1.record).length = d.1.1.time
  · rw [sideAddsPerm_of_finalize F b Q hT d hc]
    have hf : (finalizeFun F b Q d).1.1.record = d.1.1.record ∧
        (finalizeFun F b Q d).1.1.time = d.1.1.time := by
      unfold finalizeFun
      simp only [hc, ↓reduceIte]
      split <;> exact ⟨rfl, rfl⟩
    rw [sideAddsPerm_of_finalize F b Q hT _ (by rw [hf.1, hf.2]; exact hc)]
  · have ha : (sideAddsPerm F b Q d).1.1.record = d.1.1.record ∧
        (sideAddsPerm F b Q d).1.1.time = d.1.1.time := by
      rw [sideAddsPerm_apply]
      exact ⟨rfl, rfl⟩
    have h1 : finalizeFun F b Q d = d := by
      unfold finalizeFun
      simp only [hc, ↓reduceIte]
    have h2 : finalizeFun F b Q (sideAddsPerm F b Q d) = sideAddsPerm F b Q d := by
      unfold finalizeFun
      simp only [ha.1, ha.2, hc, ↓reduceIte]
    rw [h1, h2]

omit [DecidableEq W] [DecidableEq X] [DecidableEq Y] [DecidableEq Req] [DecidableEq Resp]
  [DecidableEq Req'] [DecidableEq Resp'] [Inhabited X] [Inhabited Req'] [AddGroup Y] [AddGroup Ys]
  [DecidableEq Ys] in
/-- **A permutation that keeps the distinguisher's registers, and acts on the rest by a map that
keeps the record and the clock, commutes with the distinguisher's step at the start of a
slot.** -/
theorem ctrlStep_comm (π : Equiv.Perm RR) (f : RS → RS)
    (hf : ∀ e, SP (π e) = ((SP e).1, f (SP e).2)) (hrec : ∀ l, (f l).1 = l.1)
    (htime : ∀ l, (f l).2.2.2.1 = l.2.2.2.1) :
    (D.ctrlStep F b Q).trans (permOp π) = (permOp π).trans (D.ctrlStep F b Q) := by
  have hinj : ∀ i l₁ l₂, f l₁ = f l₂ → l₁ = l₂ := fun i l₁ l₂ h => by
    have h1 := hf ((SP).symm (i, l₁))
    have h2 := hf ((SP).symm (i, l₂))
    rw [Equiv.apply_symm_apply] at h1 h2
    have : π ((SP).symm (i, l₁)) = π ((SP).symm (i, l₂)) := (SP).injective (by rw [h1, h2, h])
    have := congrArg (fun e => (SP e).2) (π.injective this)
    simpa using this
  have hsymm : ∀ e, SP (π.symm e) = ((SP e).1, (SP (π.symm e)).2) ∧
      f (SP (π.symm e)).2 = (SP e).2 := fun e => by
    have h := hf (π.symm e)
    rw [Equiv.apply_symm_apply] at h
    exact ⟨Prod.ext (congrArg Prod.fst h).symm rfl, (congrArg Prod.snd h).symm⟩
  refine LinearIsometryEquiv.ext fun v => ?_
  ext d
  change (D.ctrlStep F b Q v) (π.symm d) = (D.ctrlStep F b Q (permOp π v)) d
  simp only [ctrlStep, LinearIsometryEquiv.trans_apply]
  change (controlled _ (relabel (SP) v)) ((SP) (π.symm d)) =
    (controlled _ (relabel (SP) (permOp π v))) ((SP) d)
  obtain ⟨hs1, hs2⟩ := hsymm d
  rw [hs1]
  have key : ∀ i' l, f ((SP) (π.symm d)).2 = l →
      (SP).symm (i', ((SP) (π.symm d)).2) = π.symm ((SP).symm (i', l)) := by
    intro i' l hl
    apply (SP).injective
    rw [Equiv.apply_symm_apply]
    obtain ⟨h3, h4⟩ := hsymm ((SP).symm (i', l))
    rw [Equiv.apply_symm_apply] at h3 h4
    rw [h3]
    refine Prod.ext rfl (hinj i' _ _ ?_)
    rw [h4, hl]
  have hU : ∀ l₁ l₂ : RS, l₁.1 = l₂.1 → l₁.2.2.2.1 = l₂.2.2.2.1 →
      (if F.startAt n b Q (MultiRelay.recList l₁.1) (MultiRelay.recList l₁.1).length =
          (l₁.2.2.2.1 : ℕ) then D.stepAt (MultiRelay.recList l₁.1).length
        else LinearIsometryEquiv.refl ℂ _) =
      (if F.startAt n b Q (MultiRelay.recList l₂.1) (MultiRelay.recList l₂.1).length =
          (l₂.2.2.2.1 : ℕ) then D.stepAt (MultiRelay.recList l₂.1).length
        else LinearIsometryEquiv.refl ℂ _) := fun l₁ l₂ h1 h2 => by rw [h1, h2]
  generalize hp : (SP) d = p at hs2 ⊢
  obtain ⟨i, l⟩ := p
  simp only at hs2 ⊢
  rw [controlled_apply, controlled_apply]
  have hl1 : ((SP) (π.symm d)).2.1 = l.1 := by rw [← hrec, hs2]
  have hl2 : ((SP) (π.symm d)).2.2.2.2.1 = l.2.2.2.1 := by rw [← htime, hs2]
  rw [hU _ l hl1 hl2]
  have hv : (WithLp.toLp 2 fun i' => relabel (SP) v (i', ((SP) (π.symm d)).2)) =
      (WithLp.toLp 2 fun i' => relabel (SP) (permOp π v) (i', l) :
        QState (DReg W n X Y Req Resp)) := by
    congr 1
    funext i'
    simp only [relabel_apply, permOp_apply]
    rw [key i' l hs2]
  rw [hv]

omit [DecidableEq W] [DecidableEq Y] [DecidableEq Resp'] [DecidableEq Ys] in
/-- **The side additions commute with the distinguisher's step at the start of a slot**: they
write only the side store, which its control does not read. -/
theorem ctrlStep_sideAddsPerm :
    (D.ctrlStep F b Q).trans (permOp (sideAddsPerm F b Q)) =
      (permOp (sideAddsPerm F b Q)).trans (D.ctrlStep F b Q) :=
  D.ctrlStep_comm F b Q _ (sideRest F b Q) (relaySplit_sideAddsPerm F b Q) (fun _ => rfl)
    (fun _ => rfl)

omit [Fintype Ys] [DecidableEq Ys] in
/-- **The rest of a step does not read the side function**: the tear-down, the clock, the reply,
the record and the set-up of the relay with another side function are the relay's. -/
theorem perms_withSide (s : Xs → Ys) :
    (teardownPerm (F.withSide s) b Q : Equiv.Perm RR) = teardownPerm F b Q ∧
      (tickPerm (F.withSide s) : Equiv.Perm RR) = tickPerm F ∧
      (finalizePerm (F.withSide s) b Q : Equiv.Perm RR) = finalizePerm F b Q ∧
      (recordPerm (F.withSide s) b Q D.kind : Equiv.Perm RR) = recordPerm F b Q D.kind ∧
      (setupPerm (F.withSide s) b Q : Equiv.Perm RR) = setupPerm F b Q := by
  refine ⟨Equiv.ext fun d => ?_, rfl, Equiv.ext fun d => ?_, rfl, Equiv.ext fun d => ?_⟩
  · change teardownFun (F.withSide s) b Q d = teardownFun F b Q d
    unfold teardownFun
    rw [MultiRelay.actAt_withSide]
  · change finalizeFun (F.withSide s) b Q d = finalizeFun F b Q d
    unfold finalizeFun
    rw [MultiRelay.lastReply_withSide]
    rfl
  · change setupFun (F.withSide s) b Q d = setupFun F b Q d
    unfold setupFun
    rw [MultiRelay.actAt_withSide]

omit [DecidableEq W] [DecidableEq X] [DecidableEq Y] [DecidableEq Req] [DecidableEq Resp]
  [DecidableEq Req'] [DecidableEq Resp'] [Inhabited X] [Inhabited Req'] [AddGroup Y] [AddGroup Ys]
  [DecidableEq Ys] in
/-- **The distinguisher's step does not read the side function.** -/
theorem ctrlStep_withSide (s : Xs → Ys) :
    (D.ctrlStep (F.withSide s) b Q : QState RR ≃ₗᵢ[ℂ] QState RR) = D.ctrlStep F b Q :=
  rfl

omit [DecidableEq Ys] in
/-- **A step `k > 0` of the relayed distinguisher** (`relay`): the tear-down, the clock, the side
additions and the reply, then the distinguisher's step, the record and the set-up. -/
theorem relay_step_of_ne_zero (k : Fin (relaySlots n m F + 1)) (hk : (k : ℕ) ≠ 0) :
    (D.relay F b Q).step k =
      (permOp ((((teardownPerm F b Q).trans (tickPerm F)).trans (sideAddsPerm F b Q)).trans
        (finalizePerm F b Q))).trans ((D.ctrlStep F b Q).trans
          ((permOp (recordPerm F b Q D.kind)).trans (permOp (setupPerm F b Q)))) := by
  simp only [relay, hk, ↓reduceIte]

/-- **A step `k > 0` of the relayed distinguisher at the zero side function**: the step without the
side additions. -/
theorem relay_step_withSide_zero (k : Fin (relaySlots n m F + 1)) (hk : (k : ℕ) ≠ 0) :
    (D.relay (F.withSide 0) b Q).step k =
      (permOp (((teardownPerm F b Q).trans (tickPerm F)).trans (finalizePerm F b Q))).trans
        ((D.ctrlStep F b Q).trans
          ((permOp (recordPerm F b Q D.kind)).trans (permOp (setupPerm F b Q)))) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := perms_withSide D F b Q 0
  have h0 : (sideAddsPerm (F.withSide 0) b Q : Equiv.Perm RR) = Equiv.refl _ :=
    sideAddsPerm_withSide_zero (W := W) (n := n) (m := m) F b Q
  rw [D.relay_step_of_ne_zero (F.withSide 0) b Q k hk, h0, h1, h2, h3, h4, h5,
    D.ctrlStep_withSide F b Q 0, Equiv.trans_refl]

/-- **The relayed step is the step at the zero side function followed by the conjugated side
additions** (module docstring): for a relay without trailing side reads, at every step `k > 0`
the side additions, which occur mid-step, move after the step by conjugation with its record and
set-up. -/
theorem relay_step_eq_withSide_zero (hT : F.NoTrailingSides) (k : Fin (relaySlots n m F + 1))
    (hk : (k : ℕ) ≠ 0) :
    (D.relay F b Q).step k =
      ((D.relay (F.withSide 0) b Q).step k).trans
      (permOp (((recordPerm F b Q D.kind).trans (setupPerm F b Q)).permCongr
        (sideAddsPerm F b Q))) := by
  have hpt : ∀ σ τ : Equiv.Perm RR, permOp (σ.trans τ) = (permOp σ).trans (permOp τ) :=
    fun _ _ => LinearIsometryEquiv.ext fun _ => rfl
  have hfin : (sideAddsPerm F b Q : Equiv.Perm RR).trans (finalizePerm F b Q) =
      (finalizePerm F b Q).trans (sideAddsPerm F b Q) :=
    Equiv.ext fun d => by
      rw [Equiv.trans_apply, Equiv.trans_apply]
      exact finalizePerm_sideAddsPerm (W := W) (n := n) (m := m) F b Q hT d
  have hC : (sideAddsPerm F b Q : Equiv.Perm RR).trans
      ((recordPerm F b Q D.kind).trans (setupPerm F b Q)) =
      ((recordPerm F b Q D.kind).trans (setupPerm F b Q)).trans
        (((recordPerm F b Q D.kind).trans (setupPerm F b Q)).permCongr (sideAddsPerm F b Q)) :=
    Equiv.ext fun d => by simp
  have e1 := D.ctrlStep_sideAddsPerm F b Q
  have key : (D.relay F b Q).step k =
      ((permOp (((teardownPerm F b Q).trans (tickPerm F)).trans (finalizePerm F b Q))).trans
        ((D.ctrlStep F b Q).trans
          ((permOp (recordPerm F b Q D.kind)).trans (permOp (setupPerm F b Q))))).trans
      (permOp (((recordPerm F b Q D.kind).trans (setupPerm F b Q)).permCongr
        (sideAddsPerm F b Q))) := by
    rw [D.relay_step_of_ne_zero F b Q k hk]
    refine LinearIsometryEquiv.ext fun v => ?_
    have hA : permOp ((((teardownPerm F b Q).trans (tickPerm F)).trans
        (sideAddsPerm F b Q)).trans (finalizePerm F b Q)) v =
        permOp (sideAddsPerm F b Q) (permOp (((teardownPerm F b Q).trans (tickPerm F)).trans
          (finalizePerm F b Q)) v) := by
      rw [Equiv.trans_assoc _ (sideAddsPerm F b Q), hfin, ← Equiv.trans_assoc]
      rfl
    have hc : ∀ w, D.ctrlStep F b Q (permOp (sideAddsPerm F b Q) w) =
        permOp (sideAddsPerm F b Q) (D.ctrlStep F b Q w) := fun w =>
      (congrArg (fun T : QState RR ≃ₗᵢ[ℂ] QState RR => T w) e1).symm
    simp only [LinearIsometryEquiv.trans_apply]
    rw [hA, hc]
    ext d
    simp only [permOp_apply]
    have hd : (((recordPerm F b Q D.kind).trans (setupPerm F b Q)).permCongr
        (sideAddsPerm F b Q)).symm d = ((recordPerm F b Q D.kind).trans (setupPerm F b Q))
          ((sideAddsPerm F b Q).symm
            (((recordPerm F b Q D.kind).trans (setupPerm F b Q)).symm d)) :=
      rfl
    rw [hd]
    simp only [Equiv.symm_trans_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [key, D.relay_step_withSide_zero F b Q k hk]

end Distinguisher

end GordieHowe.Quantum
