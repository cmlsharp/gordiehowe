-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.MultiRelaySideFactor
public import GordieHowe.Model.Quantum.Pure.MultiRelaySideStore

@[expose] public section

/-!
# The relayed step as the side additions before the side-free step

A step `k > 0` of the relayed distinguisher applies the side additions mid-step, after the
tear-down and the clock (`Pre`). Conjugated by `Pre`, they come before the step at the zero side
function (`relay_step_eq_pre_withSide_zero`). The conjugated additions write only the side store
(`preAdds_apply`): the side additions write the entries of the block in progress from its side
reads made before them on, and the tear-down's action reads only the entries below. So they keep
every other register and the kind (`preAdds_keeps`, `kind_preAdds`).

- `MultiRelay.actAt_update_side`: the action of a sub-slot reads the block's side vector only below
  the side reads made.
- `Distinguisher.withSideReg`, `Distinguisher.teardownFun_withSideReg`, `Distinguisher.prePerm`,
  `Distinguisher.prePerm_withSide`,
  `Distinguisher.preAdds`, `Distinguisher.actAt_sideAfter`, `Distinguisher.preAdds_apply`,
  `Distinguisher.actAt_teardownFun_store`, `Distinguisher.actAt_preAdds`,
  `Distinguisher.preAdds_keeps`, `Distinguisher.kind_preAdds`,
  `Distinguisher.relay_step_eq_pre_withSide_zero`.
-/

namespace GordieHowe.Quantum

namespace MultiRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)
  [Inhabited X] [Zero Y] [AddGroup Ys] [Inhabited Req']

omit [Inhabited Req'] in
/-- **The action of a sub-slot reads the block's side vector only below the side reads made.** -/
theorem actAt_update_side (n b Q : ℕ) {m S : ℕ} (rec : Fin m → Option (Option Req))
    (store : Fin S → Option Resp' × (X × Y)) (side : Fin m → Fin F.qS → Ys) {t j sub : ℕ}
    (hcb : F.curBlk n b Q rec t = some (j, sub)) (hj : j < m) (v' : Fin F.qS → Ys)
    (hag : ∀ r, (recList rec).getD j none = some r →
      ∀ k < (F.stAt (F.vecSa (side ⟨j, hj⟩)) r
        (fun k => storeAt store (F.startAt n b Q (recList rec) j + k)) sub).ns,
        ∀ x, F.vecSa v' k x = F.vecSa (side ⟨j, hj⟩) k x) :
    F.actAt n b Q rec store (Function.update side ⟨j, hj⟩ v') t =
      F.actAt n b Q rec store side t := by
  unfold actAt
  rw [hcb]
  simp only
  have hv : F.vecAt (Function.update side ⟨j, hj⟩ v') j = v' := by
    simp [vecAt, hj]
  have hv0 : F.vecAt side j = side ⟨j, hj⟩ := by
    simp [vecAt, hj]
  rw [hv, hv0]
  split
  · rfl
  · rename_i r _ hr
    rw [F.stAt_congr_sa (hag r hr) r _ sub le_rfl]
  · rfl

end MultiRelay

namespace Distinguisher

variable {W X Y Req Resp Req' Resp' Xs Ys : Type} [DecidableEq X] [DecidableEq Req]
  [DecidableEq Resp] [DecidableEq Req'] [Inhabited X] [Inhabited Req'] [AddGroup Y] [AddGroup Ys]
  {n m : ℕ} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (b Q : ℕ)

local notation "RR" => RelayReg W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)

/-- The relayed registers with the side store `s`. -/
def withSideReg (z : RR) (s : Fin m → Fin F.qS → Ys) : RR :=
  ((⟨z.1.1.inner, z.1.1.record, z.1.1.store, s, z.1.1.time⟩, z.1.2.1, z.1.2.2), z.2)

omit [DecidableEq X] [DecidableEq Req] [DecidableEq Resp] in
/-- **The tear-down commutes with a change of the side store that keeps its action.** -/
theorem teardownFun_withSideReg (z : RR) (s : Fin m → Fin F.qS → Ys)
    (h : F.actAt n b Q z.1.1.record z.1.1.store s z.1.1.time =
      F.actAt n b Q z.1.1.record z.1.1.store z.1.1.side z.1.1.time) :
    teardownFun F b Q (withSideReg F z s) = withSideReg F (teardownFun F b Q z) s := by
  obtain ⟨⟨⟨inn, rec, store, side, t⟩, rq, rs⟩, pr⟩ := z
  simp only [withSideReg] at h ⊢
  unfold teardownFun
  simp only
  rw [h]
  rcases F.actAt n b Q rec store side t with i | x | r'
  · rfl
  · simp only
    split_ifs <;> rfl
  · simp only
    split_ifs <;> rfl

/-- The tear-down and the clock, before the side additions of a step. -/
def prePerm : Equiv.Perm RR :=
  (teardownPerm F b Q).trans (tickPerm F)

/-- **The tear-down and the clock do not read the side function.** -/
theorem prePerm_withSide (sf : Xs → Ys) :
    (prePerm (F.withSide sf) b Q : Equiv.Perm RR) = prePerm F b Q := by
  refine Equiv.ext fun d => ?_
  change tickPerm (F.withSide sf) (teardownFun (F.withSide sf) b Q d) =
    tickPerm F (teardownFun F b Q d)
  unfold teardownFun
  rw [MultiRelay.actAt_withSide]
  rfl

/-- **The side additions conjugated before the step.** -/
def preAdds : Equiv.Perm RR :=
  (prePerm F b Q).symm.permCongr (sideAddsPerm F b Q)

/-- **The side additions at the next clock keep the action at the clock**: they write the block in
progress from the side reads made before them on, which the action does not read. -/
theorem actAt_sideAfter (rec : Fin m → Option (Option Req))
    (store : Fin (relaySlots n m F) → Option Resp' × (X × Y)) (side : Fin m → Fin F.qS → Ys)
    (t : Fin (relaySlots n m F + 1)) :
    F.actAt n b Q rec store (sideAfter F b Q rec store side (finRotate _ t)) t =
      F.actAt n b Q rec store side t := by
  unfold sideAfter
  rcases hc : F.curRel n b Q rec (finRotate _ t) with _ | ⟨j, r, sub⟩
  · rfl
  · simp only
    split_ifs with hj
    · obtain ⟨hj', hr, hs, h1, h2⟩ := F.curRel_eq_some hc
      have hb := curRel_rel F b Q hc
      have h0 : 0 < (MultiRelay.recList rec).length := by
        by_contra h0
        unfold MultiRelay.curRel at hc
        simp only [h0, ↓reduceIte] at hc
        cases hc
      have hne : t ≠ Fin.last _ := by
        intro he
        rw [he, finRotate_last] at h1
        simp at h1
      have ht : ((finRotate _ t : Fin _) : ℕ) = t + 1 := by
        rw [coe_finRotate_of_ne_last hne]
      rw [ht] at h1 h2 hs
      have hlen : F.blkLen n (MultiRelay.blkAt b Q (MultiRelay.recList rec) j) = F.len := by
        rw [hb]
        rfl
      have hcb : F.curBlk n b Q rec t = some (j, sub - 1) := by
        unfold MultiRelay.curBlk
        rw [← hj', hlen, if_pos ⟨h0, by omega, by omega⟩]
        congr 2
        omega
      refine F.actAt_update_side n b Q rec store side hcb hj _ fun r' hr' k hk x => ?_
      rw [hr] at hr'
      cases hr'
      have hN : (F.stAt (F.vecSa (side ⟨j, hj⟩)) r
          (fun k => MultiRelay.storeAt store (F.startAt n b Q (MultiRelay.recList rec) j + k))
          (sub - 1)).ns = (F.preSt (F.vecSa (side ⟨j, hj⟩)) r
          (fun k => MultiRelay.storeAt store (F.startAt n b Q (MultiRelay.recList rec) j + k))
          sub).ns := by
        obtain ⟨s', rfl⟩ : ∃ s', sub = s' + 1 := ⟨sub - 1, by omega⟩
        simp only [Nat.add_sub_cancel, MultiRelay.preSt, F.ns_next]
      rw [hN] at hk
      unfold MultiRelay.vecSa
      split_ifs with hq
      · exact F.addsVec_agree r _ sub (side ⟨j, hj⟩) ⟨k, hq⟩ hk
      · rfl
    · rfl

/-- **The side additions conjugated before the step write only the side store**: the side store
after the side additions at the registers after the tear-down and the clock. -/
theorem preAdds_apply (z : RR) :
    preAdds F b Q z = withSideReg F z (sideAfter F b Q z.1.1.record
      (teardownFun F b Q z).1.1.store z.1.1.side (finRotate _ z.1.1.time)) := by
  have hw : (teardownFun F b Q z).1.1.record = z.1.1.record ∧
      (teardownFun F b Q z).1.1.side = z.1.1.side ∧
        (teardownFun F b Q z).1.1.time = z.1.1.time := by
    unfold teardownFun
    split
    · exact ⟨rfl, rfl, rfl⟩
    · split_ifs <;> exact ⟨rfl, rfl, rfl⟩
    · split_ifs <;> exact ⟨rfl, rfl, rfl⟩
  set w := teardownFun F b Q z with hwdef
  set s' := sideAfter F b Q w.1.1.record w.1.1.store w.1.1.side (finRotate _ w.1.1.time)
  have e2 : sideAddsPerm F b Q (tickPerm F w) = tickPerm F (withSideReg F w s') := by
    rw [sideAddsPerm_apply]
    rfl
  have e5 : teardownFun F b Q (withSideReg F w s') = withSideReg F (teardownFun F b Q w) s' :=
    teardownFun_withSideReg F b Q w s' (actAt_sideAfter F b Q _ _ _ _)
  change teardownFun F b Q ((tickPerm F).symm (sideAddsPerm F b Q (tickPerm F w))) = _
  rw [e2, Equiv.symm_apply_apply, e5, hwdef, teardownFun_teardownFun]
  obtain ⟨h1, h2, h3⟩ := hw
  have h1' : (teardownFun F b Q z).1.1.record = z.1.1.record := h1
  have h2' : (teardownFun F b Q z).1.1.side = z.1.1.side := h2
  have h3' : (teardownFun F b Q z).1.1.time = z.1.1.time := h3
  simp only [s', hwdef, h1', h2', h3']

omit [DecidableEq X] [DecidableEq Req] [DecidableEq Resp] in
/-- The tear-down changes the stored answers at most at the clock. -/
theorem actAt_teardownFun_store (z : RR) (side : Fin m → Fin F.qS → Ys) :
    F.actAt n b Q z.1.1.record (teardownFun F b Q z).1.1.store side z.1.1.time =
      F.actAt n b Q z.1.1.record z.1.1.store side z.1.1.time := by
  unfold teardownFun
  split
  · rfl
  · split_ifs with h
    · exact F.actAt_update_store _ _ _ h _
    · rfl
  · split_ifs with h
    · exact F.actAt_update_store _ _ _ h _
    · rfl

/-- **The side additions conjugated before the step keep the action at the clock**, so the
relayed distinguisher's kind. -/
theorem actAt_preAdds (z : RR) :
    F.actAt n b Q (preAdds F b Q z).1.1.record (preAdds F b Q z).1.1.store
        (preAdds F b Q z).1.1.side (preAdds F b Q z).1.1.time =
      F.actAt n b Q z.1.1.record z.1.1.store z.1.1.side z.1.1.time := by
  rw [preAdds_apply]
  change F.actAt n b Q z.1.1.record z.1.1.store (sideAfter F b Q z.1.1.record
    (teardownFun F b Q z).1.1.store z.1.1.side (finRotate _ z.1.1.time)) z.1.1.time = _
  rw [← actAt_teardownFun_store F b Q z, actAt_sideAfter, actAt_teardownFun_store]

/-- **The side additions conjugated before the step keep every register but the side store.** -/
theorem preAdds_keeps (z : RR) :
    (preAdds F b Q z).1.1.inner = z.1.1.inner ∧ (preAdds F b Q z).1.1.record = z.1.1.record ∧
      (preAdds F b Q z).1.1.store = z.1.1.store ∧ (preAdds F b Q z).1.1.time = z.1.1.time ∧
      (preAdds F b Q z).1.2 = z.1.2 ∧ (preAdds F b Q z).2 = z.2 := by
  rw [preAdds_apply]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

variable [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req]
  [Fintype Resp] [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] [Fintype Ys] [DecidableEq Ys]
  (D : Distinguisher W X Y Req Resp n m)

omit [DecidableEq Ys] in
/-- **The side additions conjugated before the step keep the relayed distinguisher's kind.** -/
theorem kind_preAdds (z : RR) :
    (D.relay F b Q).kind (preAdds F b Q z).1.1 = (D.relay F b Q).kind z.1.1 := by
  change (F.actAt n b Q _ _ _ _).isAsk = (F.actAt n b Q _ _ _ _).isAsk
  rw [actAt_preAdds]

/-- **The relayed step is the side additions conjugated before the step, then the step at the zero
side function** (module docstring), at every step `k > 0`. -/
theorem relay_step_eq_pre_withSide_zero (k : Fin (relaySlots n m F + 1)) (hk : (k : ℕ) ≠ 0) :
    (D.relay F b Q).step k =
      (permOp (preAdds F b Q)).trans ((D.relay (F.withSide 0) b Q).step k) := by
  have hpt : ∀ σ τ : Equiv.Perm RR, permOp (σ.trans τ) = (permOp σ).trans (permOp τ) :=
    fun _ _ => LinearIsometryEquiv.ext fun _ => rfl
  have hgen : ∀ P A f : Equiv.Perm RR,
      (P.trans A).trans f = (P.symm.permCongr A).trans (P.trans f) :=
    fun P A f => Equiv.ext fun d => by simp
  have he : (((teardownPerm F b Q).trans (tickPerm F)).trans (sideAddsPerm F b Q)).trans
      (finalizePerm F b Q) = (preAdds F b Q).trans
        (((teardownPerm F b Q).trans (tickPerm F)).trans (finalizePerm F b Q)) :=
    hgen _ _ _
  have key : (D.relay F b Q).step k = (permOp (preAdds F b Q)).trans
      ((permOp (((teardownPerm F b Q).trans (tickPerm F)).trans (finalizePerm F b Q))).trans
        ((D.ctrlStep F b Q).trans
          ((permOp (recordPerm F b Q D.kind)).trans (permOp (setupPerm F b Q))))) := by
    rw [D.relay_step_of_ne_zero F b Q k hk, he, hpt]
    exact LinearIsometryEquiv.ext fun _ => rfl
  rw [key, D.relay_step_withSide_zero F b Q k hk]

end Distinguisher

end GordieHowe.Quantum
