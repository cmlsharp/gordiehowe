-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.RelayBlockEntry
public import GordieHowe.Model.Quantum.Pure.MultiRelaySideStore

@[expose] public section

/-!
# The relayed distinguisher with other programs, along a permutation of its registers

For a relay `F` and other programs `p'` whose resolved forms move the main requests and results
of some requests (`MultiRelay.ProgSwap`, `GordieHowe/Model/Quantum/Pure/MultiRelayResolve.lean`),
the steps of the relayed distinguisher with `p'` are those with `F`'s along a permutation of the
registers that moves the main request register by the current slot's permutation
(`MultiRelay.curSw`), the side store from the one read from the record with `F`'s programs to the
one with `p'`'s, and the distinguisher's workspace, request and response registers by a
permutation `πin es` read from the record `es`:

- `Distinguisher.gateAt`, `Distinguisher.sideSw`, `Distinguisher.restSw`: the side stores read
  from the record with `F`'s and with `p'`'s programs (`MultiRelay.consSide`) exchanged at the
  slots whose requests satisfy `P` when they satisfy `J`, on the side store and on the rest of the
  registers; `sideSw_apply`, `sideSw_sideSw`, `gateAt_of`, `of_gateAt`, `sideSw_consSide`,
  `sideSw_eq_consSide_iff`, `sideSw_congr_store`, `sideSw_update_fillAt`.
- `Distinguisher.relSwT`, `Distinguisher.relSw`: the permutation, on the workspace, main request
  and main response registers and on all the registers; `relSw_inner`, `relSw_record`,
  `relSw_store`, `relSw_side`, `relSw_time`, `relSw_req`, `relSw_resp`, `relSw_pair`;
  `Distinguisher.curSw_default`: the current slot's permutation keeps the blank main request.
- `Distinguisher.RespSw`: `πin` moves the response register by the last slot's permutation
  (`MultiRelay.lastSwO`), keeps the request register, and moves the workspace without reading the
  response.
- `Distinguisher.actAt_congr_side`, `Distinguisher.isAsk_actAt_sideSw`: the action of a sub-slot
  reads the side store at the current block only, and `sideSw` keeps its kind for programs of the
  same shape.
- `Distinguisher.actAt_relSw`, `Distinguisher.teardownFun_relSw`,
  `Distinguisher.sideAddsTick_relSw`, `Distinguisher.finalizeFun_relSw`,
  `Distinguisher.setupFun_relSw`, `Distinguisher.recordFun_relSw`: each part of a step with `p'`
  along `relSw` is the part with `F`, on a side store read from the record, when every started
  request satisfying `J` satisfies `P`, `sw` keeps the blank and the idle main requests, the main
  request register is blank where the clock moves and the record is read, and `πin` moves the
  response register by the last slot's permutation and keeps the kind and the request register.
  The clock and the side additions go together: between them the side store lags the clock.
- `Distinguisher.sideAddsPerm_rest`: the side additions keep the other registers.
- `Distinguisher.side_teardownFun`, `Distinguisher.side_preFun`: the tear-down, and the tear-down,
  clock, side additions and reply, keep a side store read from the record.
- `Distinguisher.relSw_eq_innerMap`, `Distinguisher.preFun_parts`, `Distinguisher.preFun_relSw`,
  `Distinguisher.setupFun_req_default`, `Distinguisher.setupFun_record`,
  `Distinguisher.setupFun_store_time`, `Distinguisher.recordSetup_relSw`: the tear-down, clock and
  reply, and the record and set-up undone, along `relSw`, as `innerMap` of `πin` of the record and
  `restSw`.
- **`Distinguisher.unitaryMat_relay_step_relSw`**: a step's entries with `p'` along `relSw` are
  those with `F`, given the controlled step along `πin` (`hctrl`).
-/

open Matrix

set_option linter.unusedSectionVars false

namespace GordieHowe.Quantum

namespace Distinguisher

open MultiRelay

variable {W X Y Req Resp Req' Resp' Xs Ys : Type} [Fintype W] [DecidableEq W] [Fintype X]
  [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Inhabited X] [Inhabited Req'] [AddGroup Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] {n m : ℕ}
  (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)
  (p' : Req → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') (Option Resp)) (b Q : ℕ)
  (J : Req → Bool) (P : Req → Prop) [DecidablePred P] (sw : Equiv.Perm Req')
  (πin : List (Option Req) → Equiv.Perm (W × Req × Option Resp))

local notation "RR" => RelayReg W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)

local notation "RRest" => RelayRest X Y Req Req' Resp' m (relaySlots n m F) (Fin F.qS → Ys)

/-- **The slots whose side vectors move**: a slot with a request satisfying `P` when it satisfies
`J`, or with no request. -/
def gateAt (e : Option Req) : Bool :=
  match e with
  | none => true
  | some r => !J r || decide (P r)

/-- **The side stores read from the record with `F`'s and with `p'`'s programs, exchanged** at the
slots of `gateAt`. -/
def sideSw (rec : Fin m → Option (Option Req))
    (store : Fin (relaySlots n m F) → Option Resp' × (X × Y)) (t : ℕ) :
    Equiv.Perm (Fin m → Fin F.qS → Ys) :=
  Equiv.piCongrRight fun i => if gateAt J P ((MultiRelay.recList rec).getD i none) then
    Equiv.swap (F.consSide n b Q rec store t i) ((F.withProg p').consSide n b Q rec store t i)
  else Equiv.refl _

theorem sideSw_apply (rec : Fin m → Option (Option Req))
    (store : Fin (relaySlots n m F) → Option Resp' × (X × Y)) (t : ℕ)
    (v : Fin m → Fin F.qS → Ys) (i : Fin m) :
    sideSw F p' b Q J P rec store t v i =
      if gateAt J P ((MultiRelay.recList rec).getD i none) then
        Equiv.swap (F.consSide n b Q rec store t i) ((F.withProg p').consSide n b Q rec store t i)
          (v i)
      else v i := by
  change (if gateAt J P ((MultiRelay.recList rec).getD i none) then
    Equiv.swap (F.consSide n b Q rec store t i) ((F.withProg p').consSide n b Q rec store t i)
    else Equiv.refl _) (v i) = _
  split_ifs <;> rfl

theorem sideSw_sideSw (rec : Fin m → Option (Option Req))
    (store : Fin (relaySlots n m F) → Option Resp' × (X × Y)) (t : ℕ)
    (v : Fin m → Fin F.qS → Ys) :
    sideSw F p' b Q J P rec store t (sideSw F p' b Q J P rec store t v) = v := by
  funext i
  rw [sideSw_apply, sideSw_apply]
  split_ifs
  · exact Equiv.swap_apply_self _ _ _
  · rfl

/-- **`sideSw` on the rest of the registers**, read from their record, stored answers and clock. -/
def restSw : Equiv.Perm RRest where
  toFun r := (r.1, r.2.1, sideSw F p' b Q J P r.1 r.2.1 r.2.2.2.1 r.2.2.1, r.2.2.2)
  invFun r := (r.1, r.2.1, sideSw F p' b Q J P r.1 r.2.1 r.2.2.2.1 r.2.2.1, r.2.2.2)
  left_inv r := by simp [sideSw_sideSw]
  right_inv r := by simp [sideSw_sideSw]

/-- **`relSw` on the workspace, main request and main response registers**: the distinguisher's
registers by `πin` of the record, the side store by `sideSw`, the main request by the current
slot's permutation. -/
def relSwT : Equiv.Perm (RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F) (Fin F.qS
    → Ys) ×
    Req' × Option Resp') where
  toFun x := ((⟨(πin (MultiRelay.recList x.1.record) x.1.inner.1, x.1.inner.2),
      x.1.record, x.1.store, sideSw F p' b Q J P x.1.record x.1.store x.1.time x.1.side, x.1.time⟩,
      F.curSw J sw n b Q x.1.record x.1.time x.2.1, x.2.2))
  invFun x := ((⟨((πin (MultiRelay.recList x.1.record)).symm x.1.inner.1, x.1.inner.2),
      x.1.record, x.1.store, sideSw F p' b Q J P x.1.record x.1.store x.1.time x.1.side, x.1.time⟩,
      (F.curSw J sw n b Q x.1.record x.1.time).symm x.2.1, x.2.2))
  left_inv x := by
    obtain ⟨⟨⟨w, p⟩, rec, store, side, t⟩, q, a⟩ := x
    simp [sideSw_sideSw]
  right_inv x := by
    obtain ⟨⟨⟨w, p⟩, rec, store, side, t⟩, q, a⟩ := x
    simp [sideSw_sideSw]

/-- **The permutation of the relayed registers**: the distinguisher's workspace, request and
response registers by `πin` of the record, the side store by `sideSw`, the main request register
by the current slot's permutation (`relSwT`); the query pair kept. -/
def relSw : Equiv.Perm RR :=
  (relSwT F p' b Q J P sw πin).prodCongr (Equiv.refl _)

variable {F p' b Q J P sw πin}

theorem relSw_inner (x : RR) : (relSw F p' b Q J P sw πin x).1.1.inner =
    (πin (MultiRelay.recList x.1.1.record) x.1.1.inner.1, x.1.1.inner.2) :=
  rfl

theorem relSw_record (x : RR) : (relSw F p' b Q J P sw πin x).1.1.record = x.1.1.record :=
  rfl

theorem relSw_store (x : RR) : (relSw F p' b Q J P sw πin x).1.1.store = x.1.1.store :=
  rfl

theorem relSw_side (x : RR) : (relSw F p' b Q J P sw πin x).1.1.side =
    sideSw F p' b Q J P x.1.1.record x.1.1.store x.1.1.time x.1.1.side :=
  rfl

theorem relSw_time (x : RR) : (relSw F p' b Q J P sw πin x).1.1.time = x.1.1.time :=
  rfl

theorem relSw_req (x : RR) :
    (relSw F p' b Q J P sw πin x).1.2.1 = F.curSw J sw n b Q x.1.1.record x.1.1.time x.1.2.1 :=
  rfl

theorem relSw_resp (x : RR) : (relSw F p' b Q J P sw πin x).1.2.2 = x.1.2.2 :=
  rfl

theorem relSw_pair (x : RR) : (relSw F p' b Q J P sw πin x).2 = x.2 :=
  rfl

omit [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req]
  [Fintype Resp] [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] [DecidableEq Req]
  [DecidableEq Resp] in
theorem gateAt_of {e : Option Req} (h : ∀ r, e = some r → J r = true → P r) :
    gateAt J P e = true := by
  rcases e with _ | r
  · rfl
  · simp only [gateAt, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq]
    by_cases hJ : J r = true
    · exact Or.inr (h r rfl hJ)
    · exact Or.inl (by simpa using hJ)

omit [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req]
  [Fintype Resp] [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] [DecidableEq Req]
  [DecidableEq Resp] in
theorem of_gateAt {r : Req} (h : gateAt J P (some r) = true) (hJ : J r = true) : P r := by
  simpa [gateAt, hJ] using h

/-- `sideSw` maps the side store read with `F`'s programs to the one with `p'`'s, on a record
whose started requests satisfying `J` satisfy `P`. -/
theorem sideSw_consSide {rec : Fin m → Option (Option Req)}
    (hrec : ∀ j r, (MultiRelay.recList rec).getD j none = some r → J r = true → P r)
    (store : Fin (relaySlots n m F) → Option Resp' × (X × Y)) (t : ℕ) :
    sideSw F p' b Q J P rec store t (F.consSide n b Q rec store t) =
      (F.withProg p').consSide n b Q rec store t := by
  funext i
  rw [sideSw_apply]
  simp only [gateAt_of (J := J) (P := P) fun r he => hrec i r he, ↓reduceIte]
  exact Equiv.swap_apply_left _ _

/-- **`sideSw` moves a side store to the one read from the record with `p'`'s programs exactly
from the one with `F`'s**, on a record whose started requests satisfying `J` satisfy `P`. -/
theorem sideSw_eq_consSide_iff {rec : Fin m → Option (Option Req)}
    (hrec : ∀ j r, (MultiRelay.recList rec).getD j none = some r → J r = true → P r)
    (store : Fin (relaySlots n m F) → Option Resp' × (X × Y)) (t : ℕ)
    (v : Fin m → Fin F.qS → Ys) :
    sideSw F p' b Q J P rec store t v = (F.withProg p').consSide n b Q rec store t ↔
      v = F.consSide n b Q rec store t := by
  constructor
  · intro e
    rw [← sideSw_sideSw (F := F) (p' := p') (b := b) (Q := Q) (J := J) (P := P) rec store t v, e,
      ← sideSw_consSide hrec store t, sideSw_sideSw]
  · intro e
    rw [e]
    exact sideSw_consSide hrec store t

/-- `sideSw` does not read the stored answers from the clock on. -/
theorem sideSw_congr_store (rec : Fin m → Option (Option Req))
    {store store' : Fin (relaySlots n m F) → Option Resp' × (X × Y)} {t : ℕ}
    (h : ∀ u < t, MultiRelay.storeAt store u = MultiRelay.storeAt store' u) :
    sideSw F p' b Q J P rec store t = sideSw F p' b Q J P rec store' t := by
  unfold sideSw
  rw [F.consSide_congr_store n b Q rec h, (F.withProg p').consSide_congr_store n b Q rec h]

/-- `sideSw` does not read the entry of the slot starting at the clock. -/
theorem sideSw_update_fillAt {rec : Fin m → Option (Option Req)}
    (store : Fin (relaySlots n m F) → Option Resp' × (X × Y)) {t : ℕ} {i : Fin m}
    (hf : F.fillAt n b Q rec t = some i) (v : Option (Option Req)) :
    sideSw F p' b Q J P (Function.update rec i v) store t = sideSw F p' b Q J P rec store t := by
  have hf' := F.fillAt_update hf v
  refine Equiv.ext fun s => funext fun k => ?_
  rw [sideSw_apply, sideSw_apply]
  by_cases hk : i ≤ k
  · rw [F.consSide_fillAt n b Q store hf' hk,
      (F.withProg p').consSide_fillAt n b Q store (i := i) hf' hk,
      F.consSide_fillAt n b Q store hf hk,
      (F.withProg p').consSide_fillAt n b Q store (i := i) hf hk]
    have hz : ∀ x : Fin F.qS → Ys, Equiv.swap (0 : Fin F.qS → Ys) 0 x = x := fun x => by simp
    split_ifs <;> first | rfl | exact hz _ | exact (hz _).symm
  · have hki : (k : ℕ) < i := by
      have := not_le.1 hk
      exact this
    have hg : (MultiRelay.recList (Function.update rec i v)).getD k none =
        (MultiRelay.recList rec).getD k none := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, ← List.getElem?_take_of_lt hki,
        F.recList_take_update_fillAt hf v, List.getElem?_take_of_lt hki]
    rw [hg, F.consSide_update_fillAt n b Q store hf v,
      (F.withProg p').consSide_update_fillAt n b Q store (i := i) hf v]

variable {swO : Equiv.Perm Resp}

/-- The current slot's permutation keeps the blank main request. -/
theorem curSw_default (hdef : sw default = default) {m' : ℕ}
    (rec : Fin m' → Option (Option Req)) (t : ℕ) : F.curSw J sw n b Q rec t default = default := by
  unfold MultiRelay.curSw
  rcases F.curBlk n b Q rec t with _ | ⟨j, sub⟩
  · rfl
  · simp only
    rcases MultiRelay.blkAt b Q (MultiRelay.recList rec) j with _ | _ | _ <;>
      rcases (MultiRelay.recList rec).getD j none with _ | r <;> try rfl
    simp only [MultiRelay.swAt]
    split_ifs
    · exact hdef
    · rfl

/-- **The action of a sub-slot with other programs on a side store read from the record**, the
side store moved by `sideSw`: `F`'s with its main request moved by the current slot's
permutation. -/
theorem actAt_relSw (h : F.ProgSwap p' J P sw swO) (hidle : sw F.idle = F.idle)
    {rec : Fin m → Option (Option Req)}
    (hrec : ∀ j r, (MultiRelay.recList rec).getD j none = some r → J r = true → P r)
    (store : Fin (relaySlots n m F) → Option Resp' × (X × Y)) (t : ℕ) :
    (F.withProg p').actAt n b Q rec store
        (sideSw F p' b Q J P rec store t (F.consSide n b Q rec store t)) t =
      (F.actAt n b Q rec store (F.consSide n b Q rec store t) t).mapAsk
        (F.curSw J sw n b Q rec t) := by
  rw [sideSw_consSide hrec]
  refine MultiRelay.actAt_withProg h hidle store _ _ t (fun j _ r _ he => hrec j r he)
    fun j sub r hc hb he => ⟨?_, ?_⟩
  · exact F.stAt_consSide_curBlk n b Q store t hc hb he
  · exact (F.withProg p').stAt_consSide_curBlk n b Q store t hc hb he

omit [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req]
  [Fintype Resp] [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] [DecidableEq Req]
  [DecidableEq Resp] [Fintype Ys] [DecidableEq Ys] in
/-- **The action of a sub-slot reads the side store at the current block only.** -/
theorem actAt_congr_side {rec : Fin m → Option (Option Req)}
    (store : Fin (relaySlots n m F) → Option Resp' × (X × Y)) {s s' : Fin m → Fin F.qS → Ys}
    {t : ℕ} (h : ∀ j sub, F.curBlk n b Q rec t = some (j, sub) → F.vecAt s j = F.vecAt s' j) :
    F.actAt n b Q rec store s t = F.actAt n b Q rec store s' t := by
  unfold MultiRelay.actAt
  rcases hc : F.curBlk n b Q rec t with _ | ⟨j, sub⟩
  · rfl
  · simp only
    rw [h j sub hc]

/-- **`sideSw` keeps the kind of a sub-slot** for programs `p'` of the same shape as `F`'s whose
resolved forms move the main requests on `P`. -/
theorem isAsk_actAt_sideSw (hS : F.SameShape p') (h : F.ProgSwap p' J P sw swO)
    (hidle : sw F.idle = F.idle) (rec : Fin m → Option (Option Req))
    (store : Fin (relaySlots n m F) → Option Resp' × (X × Y)) (side : Fin m → Fin F.qS → Ys)
    (t : ℕ) :
    (F.actAt n b Q rec store (sideSw F p' b Q J P rec store t side) t).isAsk =
      (F.actAt n b Q rec store side t).isAsk := by
  rcases hc : F.curBlk n b Q rec t with _ | ⟨j, sub⟩
  · rw [actAt_congr_side (b := b) (Q := Q) store (s' := side) fun j sub h => by
      rw [hc] at h
      cases h]
  · by_cases hjm : j < m
    swap
    · rw [actAt_congr_side (b := b) (Q := Q) store (s' := side) fun j' sub' h' => by
        rw [hc] at h'
        cases h'
        simp [MultiRelay.vecAt, hjm]]
    have hv : ∀ v : Fin m → Fin F.qS → Ys, F.vecAt v j = v ⟨j, hjm⟩ := fun v => by
      simp [MultiRelay.vecAt, hjm]
    have hcj : ∀ j' sub', F.curBlk n b Q rec t = some (j', sub') → j' = j := fun j' sub' h' => by
      rw [hc] at h'
      cases h'
      rfl
    -- off the gate, or off the two side stores, `sideSw` keeps the current slot's vector
    have hkeep : sideSw F p' b Q J P rec store t side ⟨j, hjm⟩ = side ⟨j, hjm⟩ →
        (F.actAt n b Q rec store (sideSw F p' b Q J P rec store t side) t).isAsk =
          (F.actAt n b Q rec store side t).isAsk := fun e => by
      rw [actAt_congr_side (b := b) (Q := Q) store (s' := side) fun j' sub' h' => by
        rw [hcj j' sub' h', hv, hv, e]]
    rw [sideSw_apply] at hkeep
    split_ifs at hkeep with hg
    swap
    · exact hkeep rfl
    have hrec : ∀ j' sub' r, F.curBlk n b Q rec t = some (j', sub') →
        (MultiRelay.recList rec).getD j' none = some r → J r = true → P r :=
      fun j' sub' r h' he hJ => by
        rw [hcj j' sub' h'] at he
        rw [he] at hg
        exact of_gateAt hg hJ
    by_cases h1 : side ⟨j, hjm⟩ = F.consSide n b Q rec store t ⟨j, hjm⟩
    · -- the side store read with `F`'s programs at the current slot
      have e1 : sideSw F p' b Q J P rec store t side ⟨j, hjm⟩ =
          (F.withProg p').consSide n b Q rec store t ⟨j, hjm⟩ := by
        rw [sideSw_apply]
        simp only [hg, ↓reduceIte]
        rw [h1]
        exact Equiv.swap_apply_left _ _
      have hA := MultiRelay.actAt_withProg h hidle store side (sideSw F p' b Q J P rec store t side)
        t hrec fun j' sub' r h' hb he => by
          obtain rfl := hcj j' sub' h'
          refine ⟨?_, ?_⟩
          · rw [show F.vecAt side j' = F.vecAt (F.consSide n b Q rec store t) j' by
              rw [hv, hv, h1]]
            exact F.stAt_consSide_curBlk n b Q store t h' hb he
          · rw [show F.vecAt (sideSw F p' b Q J P rec store t side) j' =
              F.vecAt ((F.withProg p').consSide n b Q rec store t) j' by
                simp only [MultiRelay.vecAt, hjm, ↓reduceDIte]
                exact e1]
            exact (F.withProg p').stAt_consSide_curBlk n b Q store t h' hb he
      rw [← MultiRelay.isAsk_actAt_shape hS, hA, SubAct.isAsk_mapAsk]
    · by_cases h2 : side ⟨j, hjm⟩ = (F.withProg p').consSide n b Q rec store t ⟨j, hjm⟩
      · -- the side store read with `p'`'s programs at the current slot
        have e1 : sideSw F p' b Q J P rec store t side ⟨j, hjm⟩ =
            F.consSide n b Q rec store t ⟨j, hjm⟩ := by
          rw [sideSw_apply]
          simp only [hg, ↓reduceIte]
          rw [h2]
          exact Equiv.swap_apply_right _ _
        have hA := MultiRelay.actAt_withProg h hidle store (sideSw F p' b Q J P rec store t side)
          side t hrec fun j' sub' r h' hb he => by
            obtain rfl := hcj j' sub' h'
            refine ⟨?_, ?_⟩
            · rw [show F.vecAt (sideSw F p' b Q J P rec store t side) j' =
                F.vecAt (F.consSide n b Q rec store t) j' by rw [hv, hv, e1]]
              exact F.stAt_consSide_curBlk n b Q store t h' hb he
            · rw [show F.vecAt side j' =
                F.vecAt ((F.withProg p').consSide n b Q rec store t) j' by
                  simp only [MultiRelay.vecAt, hjm, ↓reduceDIte]
                  exact h2]
              exact (F.withProg p').stAt_consSide_curBlk n b Q store t h' hb he
        rw [← SubAct.isAsk_mapAsk (F.curSw J sw n b Q rec t), ← hA,
          MultiRelay.isAsk_actAt_shape hS]
      · exact hkeep (Equiv.swap_apply_of_ne_of_ne h1 h2)

/-- **The tear-down with other programs along `relSw`**, on a side store read from the record. -/
theorem teardownFun_relSw (h : F.ProgSwap p' J P sw swO) (hidle : sw F.idle = F.idle)
    (hdef : sw default = default) (x : RR)
    (hrec : ∀ j r, (MultiRelay.recList x.1.1.record).getD j none = some r → J r = true → P r)
    (hs : x.1.1.side = F.consSide n b Q x.1.1.record x.1.1.store x.1.1.time) :
    teardownFun (F.withProg p') b Q (relSw F p' b Q J P sw πin x) =
      relSw F p' b Q J P sw πin (teardownFun F b Q x) := by
  obtain ⟨⟨⟨⟨w, p⟩, rec, store, side, t⟩, q, a⟩, pr⟩ := x
  change side = F.consSide n b Q rec store t at hs
  subst hs
  have hc := curSw_default (F := F) (b := b) (Q := Q) (n := n) (J := J) hdef rec t
  have hA := actAt_relSw (n := n) (b := b) (Q := Q) h hidle hrec store t
  have hU : ∀ (ht : (t : ℕ) < relaySlots n m F) (v : Option Resp' × (X × Y)),
      sideSw F p' b Q J P rec (Function.update store ⟨t, ht⟩ v) t =
        sideSw F p' b Q J P rec store t :=
    fun ht v => sideSw_congr_store rec fun u hu => by
      unfold MultiRelay.storeAt
      split_ifs with h'
      · rw [Function.update_of_ne (fun e => by
          have := congrArg Fin.val e
          simp only at this
          omega)]
      · rfl
  unfold teardownFun
  simp only [relSw_record, relSw_store, relSw_side, relSw_time]
  change (match (F.withProg p').actAt n b Q rec store
      (sideSw F p' b Q J P rec store t (F.consSide n b Q rec store t)) t with
    | .pair i => _ | .query _ => _ | .ask r' => _) = _
  rw [hA]
  rcases F.actAt n b Q rec store (F.consSide n b Q rec store t) t with i | x | r'
  · rfl
  · simp only [SubAct.mapAsk]
    by_cases ht : (t : ℕ) < relaySlots n m F
    · have ht' : (t : ℕ) < relaySlots n m (F.withProg p') := ht
      simp only [ht, ht', ↓reduceDIte]
      refine Prod.ext (Prod.ext (RelayW.ext ?_ ?_ ?_ ?_ ?_) ?_) ?_ <;>
        simp only [relSw_inner, relSw_record, relSw_store, relSw_side, relSw_time, relSw_req,
          relSw_resp, relSw_pair]
      all_goals first | exact (congrFun (congrArg DFunLike.coe (hU ht _)) _).symm | rfl
    · have ht' : ¬ (t : ℕ) < relaySlots n m (F.withProg p') := ht
      simp only [ht, ht', ↓reduceDIte]
      rfl
  · simp only [SubAct.mapAsk]
    have hsw : Equiv.swap default (F.curSw J sw n b Q rec t r') (F.curSw J sw n b Q rec t q) =
        F.curSw J sw n b Q rec t (Equiv.swap default r' q) := by
      conv_lhs => rw [← hc, Equiv.swap_apply_apply]
      simp [Equiv.Perm.mul_apply]
    by_cases ht : (t : ℕ) < relaySlots n m F
    · have ht' : (t : ℕ) < relaySlots n m (F.withProg p') := ht
      simp only [ht, ht', ↓reduceDIte]
      refine Prod.ext (Prod.ext (RelayW.ext ?_ ?_ ?_ ?_ ?_) (Prod.ext ?_ ?_)) ?_ <;>
        simp only [relSw_inner, relSw_record, relSw_store, relSw_side, relSw_time, relSw_req,
          relSw_resp, relSw_pair]
      all_goals first | exact hsw | exact (congrFun (congrArg DFunLike.coe (hU ht _)) _).symm | rfl
    · have ht' : ¬ (t : ℕ) < relaySlots n m (F.withProg p') := ht
      simp only [ht, ht', ↓reduceDIte]
      exact Prod.ext (Prod.ext rfl (Prod.ext hsw rfl)) rfl

omit [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req]
  [Fintype Resp] [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] [Fintype Ys]
  [DecidableEq Ys] in
/-- **The tear-down keeps a side store read from the record.** -/
theorem side_teardownFun (x : RR)
    (hs : x.1.1.side = F.consSide n b Q x.1.1.record x.1.1.store x.1.1.time) :
    (teardownFun F b Q x).1.1.side = F.consSide n b Q (teardownFun F b Q x).1.1.record
      (teardownFun F b Q x).1.1.store (teardownFun F b Q x).1.1.time := by
  obtain ⟨h1, h2, h3⟩ := teardownFun_record_time F b Q x
  rw [h1, h2, h3, hs]
  exact F.consSide_congr_store n b Q _ fun u hu =>
    (teardownFun_storeAt F b Q x (by omega)).symm

omit [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req]
  [Fintype Resp] [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] [Fintype Ys]
  [DecidableEq Ys] in
/-- The side additions keep the distinguisher's registers, the main response register and the
query pair. -/
theorem sideAddsPerm_rest (d : RR) : (sideAddsPerm F b Q d).1.1.inner = d.1.1.inner ∧
    (sideAddsPerm F b Q d).1.2.2 = d.1.2.2 ∧ (sideAddsPerm F b Q d).2 = d.2 := by
  rw [sideAddsPerm_apply]
  exact ⟨rfl, rfl, rfl⟩

/-- **The clock and the side additions with other programs along `relSw`**, on a blank main
request register and a side store read from the record at a clock `t < S`. -/
theorem sideAddsTick_relSw (hdef : sw default = default) (y : RR) (hq : y.1.2.1 = default)
    (hP : ∀ j r, (MultiRelay.recList y.1.1.record).getD j none = some r → J r = true → P r)
    {es : List (Option Req)} (hrec : RecAt (n := n) F b Q y.1.1.record es y.1.1.time)
    (ht : (y.1.1.time : ℕ) < relaySlots n m F)
    (hs : y.1.1.side = F.consSide n b Q y.1.1.record y.1.1.store y.1.1.time) :
    sideAddsPerm (F.withProg p') b Q (tickPerm (F.withProg p') (relSw F p' b Q J P sw πin y)) =
      relSw F p' b Q J P sw πin (sideAddsPerm F b Q (tickPerm F y)) := by
  have hsL := side_sideAddsPerm_tickPerm (F.withProg p') b Q (relSw F p' b Q J P sw πin y) hrec ht
    (by rw [relSw_side, hs, sideSw_consSide hP]; rfl)
  have hsR := side_sideAddsPerm_tickPerm F b Q y hrec ht hs
  have hpL := sideAddsPerm_parts (F.withProg p') b Q (tickPerm (F.withProg p')
    (relSw F p' b Q J P sw πin y))
  have hpR := sideAddsPerm_parts F b Q (tickPerm F y)
  have hiL' := sideAddsPerm_rest (F := F.withProg p') (b := b) (Q := Q)
    (tickPerm (F.withProg p') (relSw F p' b Q J P sw πin y))
  have hiR := sideAddsPerm_rest (F := F) (b := b) (Q := Q) (tickPerm F y)
  have htk : ((tickPerm F y).1.1.time : ℕ) = y.1.1.time + 1 := by
    change (finRotate _ y.1.1.time : ℕ) = _
    rw [coe_finRotate_of_ne_last (fun h => by
      have := congrArg Fin.val h
      simp only [Fin.val_last] at this
      omega)]
  refine Prod.ext (Prod.ext (RelayW.ext ?_ ?_ ?_ ?_ ?_) (Prod.ext ?_ ?_)) ?_
  · rw [hiL'.1, relSw_inner, hiR.1, hpR.1]
    rfl
  · rw [hpL.1, relSw_record, hpR.1]
    rfl
  · rw [hpL.2.1, relSw_store, hpR.2.1]
    rfl
  · rw [hsL, relSw_side, hsR, hpR.1, hpR.2.1, hpR.2.2.1, htk]
    exact (sideSw_consSide hP _ _).symm
  · rw [hpL.2.2.1, relSw_time, hpR.2.2.1]
    rfl
  · rw [hpL.2.2.2, relSw_req, hpR.2.2.2, hpR.1, hpR.2.2.1]
    change F.curSw J sw n b Q y.1.1.record y.1.1.time y.1.2.1 =
      F.curSw J sw n b Q y.1.1.record (tickPerm F y).1.1.time y.1.2.1
    rw [hq, curSw_default hdef, curSw_default hdef]
  · rw [hiL'.2.1, relSw_resp, hiR.2.1]
    rfl
  · rw [hiL'.2.2, relSw_pair, hiR.2.2]
    rfl

/-- **`πin` moves the response register by the last slot's permutation** and keeps the request
register; its move of the workspace does not read the response. -/
def RespSw (b' Q' : ℕ) (J' : Req → Bool) (swO : Equiv.Perm Resp)
    (π : List (Option Req) → Equiv.Perm (W × Req × Option Resp)) : Prop :=
  ∀ {m' : ℕ} (rec : Fin m' → Option (Option Req)) w q a,
    π (MultiRelay.recList rec) (w, q, a) =
      ((π (MultiRelay.recList rec) (w, q, none)).1, q,
        Option.map (MultiRelay.lastSwO J' swO b' Q' rec) a)

/-- **The reply of a finished slot with other programs along `relSw`**, on a side store read from
the record. -/
theorem finalizeFun_relSw (h : F.ProgSwap p' J P sw swO) (hπ : RespSw b Q J swO πin) (x : RR)
    (hrec : ∀ j r, (MultiRelay.recList x.1.1.record).getD j none = some r → J r = true → P r)
    (hside : x.1.1.side = F.consSide n b Q x.1.1.record x.1.1.store x.1.1.time) :
    finalizeFun (F.withProg p') b Q (relSw F p' b Q J P sw πin x) =
      relSw F p' b Q J P sw πin (finalizeFun F b Q x) := by
  obtain ⟨⟨⟨⟨⟨w, q₀, a₀⟩, p⟩, rec, store, side, t⟩, q, a⟩, pr⟩ := x
  change side = F.consSide n b Q rec store t at hside
  subst hside
  have hrec' : ∀ j r, (MultiRelay.recList rec).getD j none = some r → J r = true → P r := hrec
  unfold finalizeFun
  by_cases hs : F.startAt n b Q (MultiRelay.recList rec) (MultiRelay.recList rec).length = (t : ℕ)
  · have hs' : (F.withProg p').startAt n b Q (MultiRelay.recList rec)
        (MultiRelay.recList rec).length = (t : ℕ) := hs
    have hL := MultiRelay.lastReply_withProg (n := n) (b := b) (Q := Q) h hrec' store
      (F.consSide n b Q rec store t)
      (sideSw F p' b Q J P rec store t (F.consSide n b Q rec store t)) fun r hb he => by
        rw [sideSw_consSide hrec']
        exact ⟨F.stAt_consSide_last n b Q store hs hb he,
          (F.withProg p').stAt_consSide_last n b Q store hs' hb he⟩
    simp only [relSw_record, relSw_store, relSw_side, relSw_time, hs, hs', ↓reduceIte]
    erw [hL]
    rcases F.lastReply n b Q rec store (F.consSide n b Q rec store t) with _ | o
    · rfl
    · simp only [Option.map_some]
      refine Prod.ext (Prod.ext ?_ rfl) rfl
      refine RelayW.ext ?_ rfl rfl rfl rfl
      change (((πin (MultiRelay.recList rec) (w, q₀, a₀)).1, (πin (MultiRelay.recList rec)
          (w, q₀, a₀)).2.1, Equiv.swap none (Option.map (MultiRelay.lastSwO J swO b Q rec) o)
          (πin (MultiRelay.recList rec) (w, q₀, a₀)).2.2), p) =
        (πin (MultiRelay.recList rec) (w, q₀, Equiv.swap none o a₀), p)
      rw [hπ rec w q₀ a₀, hπ rec w q₀ (Equiv.swap none o a₀)]
      refine Prod.ext (Prod.ext rfl (Prod.ext rfl ?_)) rfl
      change Equiv.swap ((Equiv.optionCongr (MultiRelay.lastSwO J swO b Q rec)) none)
          ((Equiv.optionCongr (MultiRelay.lastSwO J swO b Q rec)) o)
          ((Equiv.optionCongr (MultiRelay.lastSwO J swO b Q rec)) a₀) =
        (Equiv.optionCongr (MultiRelay.lastSwO J swO b Q rec)) (Equiv.swap none o a₀)
      rw [Equiv.swap_apply_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
        Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  · have hs' : ¬ (F.withProg p').startAt n b Q (MultiRelay.recList rec)
        (MultiRelay.recList rec).length = (t : ℕ) := hs
    simp only [relSw_record, relSw_time, hs, hs', ↓reduceIte]
    rfl

/-- **The set-up with other programs along `relSw`**, on a side store read from the record. -/
theorem setupFun_relSw (h : F.ProgSwap p' J P sw swO) (hidle : sw F.idle = F.idle)
    (hdef : sw default = default) (x : RR)
    (hrec : ∀ j r, (MultiRelay.recList x.1.1.record).getD j none = some r → J r = true → P r)
    (hs : x.1.1.side = F.consSide n b Q x.1.1.record x.1.1.store x.1.1.time) :
    setupFun (F.withProg p') b Q (relSw F p' b Q J P sw πin x) =
      relSw F p' b Q J P sw πin (setupFun F b Q x) := by
  obtain ⟨⟨⟨⟨w, p⟩, rec, store, side, t⟩, q, a⟩, pr⟩ := x
  change side = F.consSide n b Q rec store t at hs
  subst hs
  have hc := curSw_default (F := F) (b := b) (Q := Q) (n := n) (J := J) hdef rec t
  have hrec' : ∀ j r, (MultiRelay.recList rec).getD j none = some r → J r = true → P r := hrec
  have hA := actAt_relSw (n := n) (b := b) (Q := Q) h hidle hrec' store t
  unfold setupFun
  simp only [relSw_record, relSw_store, relSw_side, relSw_time]
  change (match (F.withProg p').actAt n b Q rec store
      (sideSw F p' b Q J P rec store t (F.consSide n b Q rec store t)) t with
    | .pair i => _ | .query _ => _ | .ask r' => _) = _
  rw [hA]
  rcases F.actAt n b Q rec store (F.consSide n b Q rec store t) t with i | x | r'
  · rfl
  · rfl
  · simp only [SubAct.mapAsk]
    refine Prod.ext (Prod.ext rfl (Prod.ext ?_ rfl)) rfl
    change Equiv.swap default (F.curSw J sw n b Q rec t r') (F.curSw J sw n b Q rec t q) =
      F.curSw J sw n b Q rec t (Equiv.swap default r' q)
    conv_lhs => rw [← hc, Equiv.swap_apply_apply]
    simp [Equiv.Perm.mul_apply]

/-- **The record along `relSw`**, on a blank main request register, for `πin` keeping the kind
and the request register: the record with the distinguisher's registers moved by `πin` of the
record before and the rest by `restSw`. -/
theorem recordFun_relSw (kind : W → Bool) (hdef : sw default = default)
    (hk : ∀ es w q a, kind (πin es (w, q, a)).1 = kind w)
    (hrq : ∀ es w q a, (πin es (w, q, a)).2.1 = q) (x : RR) (hq : x.1.2.1 = default) :
    recordFun (F.withProg p') b Q kind (relSw F p' b Q J P sw πin x) =
      innerMap F ((πin (MultiRelay.recList x.1.1.record)).prodCongr (Equiv.refl _))
        (restSw F p' b Q J P) (recordFun F b Q kind x) := by
  obtain ⟨⟨⟨⟨⟨w, q₀, a₀⟩, p⟩, rec, store, side, t⟩, q, a⟩, pr⟩ := x
  change q = default at hq
  subst hq
  have hc := curSw_default (F := F) (b := b) (Q := Q) (n := n) (J := J) hdef rec t
  have he : entryOf kind (πin (MultiRelay.recList rec) (w, q₀, a₀), p) =
      entryOf kind ((w, q₀, a₀), p) := by
    simp only [entryOf, hk, hrq]
  unfold recordFun
  change (match F.fillAt n b Q rec t with
    | some i => _ | none => _) = innerMap F _ _ (match F.fillAt n b Q rec t with
    | some i => _ | none => _)
  rcases hf : F.fillAt n b Q rec t with _ | i
  · change (((RelayW.mk (πin (MultiRelay.recList rec) (w, q₀, a₀), p) rec store
      (sideSw F p' b Q J P rec store t side) t :
      RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F) (Fin F.qS → Ys)),
      F.curSw J sw n b Q rec t default, a), pr) = _
    rw [hc]
    rfl
  · change (((RelayW.mk (πin (MultiRelay.recList rec) (w, q₀, a₀), p) (Function.update rec i
      (Equiv.swap none (some (entryOf kind (πin (MultiRelay.recList rec) (w, q₀, a₀), p)))
        (rec i))) store (sideSw F p' b Q J P rec store t side) t :
        RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F) (Fin F.qS → Ys)),
      F.curSw J sw n b Q rec t default, a), pr) = _
    rw [hc, he, ← sideSw_update_fillAt store hf]
    rfl

/-- **The relayed registers along `relSw` on a blank main request register** are those along
`innerMap` of `πin` of the record and `restSw`. -/
theorem relSw_eq_innerMap (hdef : sw default = default) (x : RR) (hq : x.1.2.1 = default) :
    relSw F p' b Q J P sw πin x =
      innerMap F ((πin (MultiRelay.recList x.1.1.record)).prodCongr (Equiv.refl _))
        (restSw F p' b Q J P) x := by
  obtain ⟨⟨⟨⟨w, p⟩, rec, store, side, t⟩, q, a⟩, pr⟩ := x
  change q = default at hq
  subst hq
  change (((RelayW.mk (πin (MultiRelay.recList rec) w, p) rec store
      (sideSw F p' b Q J P rec store t side) t :
      RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F) (Fin F.qS → Ys)),
      F.curSw J sw n b Q rec t default, a), pr) = _
  rw [curSw_default hdef]
  rfl

/-- The tear-down blanks a main request register holding the action's main request; the clock
and the reply keep it blank and keep the record. -/
theorem preFun_parts (k : ℕ) (hk : k ≠ 0) (c : RR)
    (hc : c.1.2.1 = askOf (F.actAt n b Q c.1.1.record c.1.1.store c.1.1.side c.1.1.time)) :
    (preFun F b Q k c).1.2.1 = default ∧ (preFun F b Q k c).1.1.record = c.1.1.record := by
  unfold preFun
  simp only [hk, ↓reduceIte]
  obtain ⟨hf1, -, -, hf4⟩ := finalizeFun_parts F b Q
    (sideAddsPerm F b Q (tickPerm F (teardownFun F b Q c)))
  obtain ⟨ha1, -, -, ha4⟩ := sideAddsPerm_parts F b Q (tickPerm F (teardownFun F b Q c))
  exact ⟨hf4.trans (ha4.trans (teardownFun_req F b Q c hc)),
    hf1.trans (ha1.trans (teardownFun_record_time F b Q c).1)⟩

/-- **The tear-down, the clock, the side additions and the reply keep a side store read from the
record**, from a clock `t < S`. -/
theorem side_preFun (k : ℕ) (hk : k ≠ 0) (c : RR) {es : List (Option Req)}
    (hrec : RecAt (n := n) F b Q c.1.1.record es c.1.1.time)
    (ht : (c.1.1.time : ℕ) < relaySlots n m F)
    (hs : c.1.1.side = F.consSide n b Q c.1.1.record c.1.1.store c.1.1.time) :
    (preFun F b Q k c).1.1.side = F.consSide n b Q (preFun F b Q k c).1.1.record
      (preFun F b Q k c).1.1.store (preFun F b Q k c).1.1.time := by
  unfold preFun
  simp only [hk, ↓reduceIte]
  obtain ⟨h1, -, h3⟩ := teardownFun_record_time F b Q c
  have hs1 := side_teardownFun (F := F) (b := b) (Q := Q) c hs
  obtain ⟨hf1, hf2, hf3, -⟩ := finalizeFun_parts F b Q
    (sideAddsPerm F b Q (tickPerm F (teardownFun F b Q c)))
  obtain ⟨ha1, ha2, ha3, -⟩ := sideAddsPerm_parts F b Q (tickPerm F (teardownFun F b Q c))
  have hr : RecAt (n := n) F b Q (teardownFun F b Q c).1.1.record es
      (teardownFun F b Q c).1.1.time := by
    rw [h1, h3]
    exact hrec
  have hS := side_sideAddsPerm_tickPerm F b Q (teardownFun F b Q c) hr (by rw [h3]; exact ht) hs1
  rw [finalizeFun_side, hS, hf1, hf2, hf3, ha1, ha2, ha3]
  congr 1
  change _ = (finRotate _ (teardownFun F b Q c).1.1.time : ℕ)
  rw [coe_finRotate_of_ne_last (fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_last] at this
    rw [h3] at this
    omega)]

/-- **The tear-down, the clock, the side additions and the reply with other programs along
`relSw`**: `innerMap` of `πin` of the record and `restSw`, on a column whose main request register
holds the action's main request and whose side store is read from the record at a clock
`t < S`. -/
theorem preFun_relSw (h : F.ProgSwap p' J P sw swO) (hidle : sw F.idle = F.idle)
    (hdef : sw default = default) (hπ : RespSw b Q J swO πin) (k : ℕ) (c : RR)
    (hrec : ∀ j r, (MultiRelay.recList c.1.1.record).getD j none = some r → J r = true → P r)
    (hc : k ≠ 0 → c.1.2.1 = askOf (F.actAt n b Q c.1.1.record c.1.1.store c.1.1.side c.1.1.time) ∧
      c.1.1.side = F.consSide n b Q c.1.1.record c.1.1.store c.1.1.time ∧
      (∃ es, RecAt (n := n) F b Q c.1.1.record es c.1.1.time) ∧
      (c.1.1.time : ℕ) < relaySlots n m F)
    (hc0 : k = 0 → c.1.2.1 = default) :
    preFun (F.withProg p') b Q k (relSw F p' b Q J P sw πin c) =
      innerMap F ((πin (MultiRelay.recList c.1.1.record)).prodCongr (Equiv.refl _))
        (restSw F p' b Q J P) (preFun F b Q k c) := by
  by_cases hk : k = 0
  · subst hk
    exact relSw_eq_innerMap hdef c (hc0 rfl)
  · obtain ⟨hq0, hs, ⟨es, hR⟩, ht⟩ := hc hk
    obtain ⟨hq, hr⟩ := preFun_parts k hk c hq0
    have htd := teardownFun_record_time F b Q c
    have hq1 := teardownFun_req F b Q c hq0
    have hs1 := side_teardownFun (F := F) (b := b) (Q := Q) c hs
    unfold preFun
    simp only [hk, ↓reduceIte]
    rw [teardownFun_relSw h hidle hdef c hrec hs]
    rw [sideAddsTick_relSw hdef _ hq1 (by rw [htd.1]; exact hrec) (es := es)
      (by rw [htd.1, htd.2.2]; exact hR)
      (by rw [htd.2.2]; exact ht) hs1]
    have hrecY : ∀ j r, (MultiRelay.recList (sideAddsPerm F b Q (tickPerm F (teardownFun F b Q
        c))).1.1.record).getD j none = some r → J r = true → P r := by
      rw [(sideAddsPerm_parts F b Q _).1]
      change ∀ j r, (MultiRelay.recList (teardownFun F b Q c).1.1.record).getD j none = some r →
        J r = true → P r
      rw [htd.1]
      exact hrec
    have hsY := side_preFun (F := F) (b := b) (Q := Q) k hk c hR ht hs
    unfold preFun at hsY
    simp only [hk, ↓reduceIte, finalizeFun_side, (finalizeFun_parts F b Q _).1,
      (finalizeFun_parts F b Q _).2.1, (finalizeFun_parts F b Q _).2.2.1] at hsY
    rw [finalizeFun_relSw h hπ _ hrecY hsY]
    have h' := relSw_eq_innerMap (F := F) (p' := p') (b := b) (Q := Q) (J := J) (P := P)
      (πin := πin) hdef
      (finalizeFun F b Q (sideAddsPerm F b Q (tickPerm F (teardownFun F b Q c)))) (by
        have := hq
        unfold preFun at this
        simpa only [hk, ↓reduceIte] using this)
    rw [h']
    congr 3
    have := hr
    unfold preFun at this
    simp only [hk, ↓reduceIte] at this
    rw [this]

/-- The set-up undone blanks a main request register holding the action's main request. -/
theorem setupFun_req_default (a : RR)
    (ha : a.1.2.1 = askOf (F.actAt n b Q a.1.1.record a.1.1.store a.1.1.side a.1.1.time)) :
    (setupFun F b Q a).1.2.1 = default := by
  unfold setupFun
  rcases hA : F.actAt n b Q a.1.1.record a.1.1.store a.1.1.side a.1.1.time with i | x | r'
  · rw [hA] at ha
    exact ha
  · rw [hA] at ha
    exact ha
  · rw [hA] at ha
    change Equiv.swap default r' a.1.2.1 = default
    rw [ha]
    exact Equiv.swap_apply_right _ _

/-- The set-up keeps the record. -/
theorem setupFun_record (a : RR) : (setupFun F b Q a).1.1.record = a.1.1.record := by
  unfold setupFun
  rcases F.actAt n b Q a.1.1.record a.1.1.store a.1.1.side a.1.1.time with i | x | r' <;> rfl

/-- The set-up keeps the stored answers and the clock. -/
theorem setupFun_store_time (a : RR) :
    (setupFun F b Q a).1.1.store = a.1.1.store ∧ (setupFun F b Q a).1.1.time = a.1.1.time := by
  unfold setupFun
  rcases F.actAt n b Q a.1.1.record a.1.1.store a.1.1.side a.1.1.time with i | x | r' <;>
    exact ⟨rfl, rfl⟩

/-- **The record and the set-up keep the side store read from the record.** -/
theorem side_setupFun_recordFun (kind : W → Bool) (z : RR)
    (hs : z.1.1.side = F.consSide n b Q z.1.1.record z.1.1.store z.1.1.time) :
    (setupFun F b Q (recordFun F b Q kind z)).1.1.side =
      F.consSide n b Q (setupFun F b Q (recordFun F b Q kind z)).1.1.record
        (setupFun F b Q (recordFun F b Q kind z)).1.1.store
        (setupFun F b Q (recordFun F b Q kind z)).1.1.time := by
  obtain ⟨e1, e2⟩ := setupFun_store_time (F := F) (b := b) (Q := Q) (recordFun F b Q kind z)
  have r12 : (recordFun F b Q kind z).1.1.store = z.1.1.store ∧
      (recordFun F b Q kind z).1.1.time = z.1.1.time := by
    unfold recordFun
    rcases F.fillAt n b Q z.1.1.record z.1.1.time <;> exact ⟨rfl, rfl⟩
  rw [setupFun_side, recordFun_side, setupFun_record, e1, e2, r12.1, r12.2, consSide_recordFun, hs]

/-- **Registers with the same rest have the side store read from the record together.** -/
theorem side_consSide_of_rest {z c : RR} (h : rest F z = rest F c)
    (hs : c.1.1.side = F.consSide n b Q c.1.1.record c.1.1.store c.1.1.time) :
    z.1.1.side = F.consSide n b Q z.1.1.record z.1.1.store z.1.1.time := by
  have h1 : z.1.1.record = c.1.1.record := congrArg (fun r => r.1) h
  have h2 : z.1.1.store = c.1.1.store := congrArg (fun r => r.2.1) h
  have h3 : z.1.1.side = c.1.1.side := congrArg (fun r => r.2.2.1) h
  have h4 : z.1.1.time = c.1.1.time := congrArg (fun r => r.2.2.2.1) h
  rw [h1, h2, h3, h4]
  exact hs

/-- **The record and set-up undone with other programs along `relSw`**: `innerMap` of `πin` of
the row's record and `restSw`, on a row whose main request register holds the action's main
request and whose side store is read from the record. -/
theorem recordSetup_relSw (h : F.ProgSwap p' J P sw swO) (hidle : sw F.idle = F.idle)
    (hdef : sw default = default) (kind : W → Bool)
    (hk : ∀ es w q a, kind (πin es (w, q, a)).1 = kind w)
    (hrq : ∀ es w q a, (πin es (w, q, a)).2.1 = q) (a : RR)
    (hrec : ∀ j r, (MultiRelay.recList a.1.1.record).getD j none = some r → J r = true → P r)
    (ha : a.1.2.1 = askOf (F.actAt n b Q a.1.1.record a.1.1.store a.1.1.side a.1.1.time))
    (hs : a.1.1.side = F.consSide n b Q a.1.1.record a.1.1.store a.1.1.time) :
    recordFun (F.withProg p') b Q kind (setupFun (F.withProg p') b Q
        (relSw F p' b Q J P sw πin a)) =
      innerMap F ((πin (MultiRelay.recList a.1.1.record)).prodCongr (Equiv.refl _))
        (restSw F p' b Q J P) (recordFun F b Q kind (setupFun F b Q a)) := by
  rw [setupFun_relSw h hidle hdef _ hrec hs]
  have := recordFun_relSw (p' := p') (F := F) (b := b) (Q := Q) (J := J) (P := P) kind hdef hk hrq _
    (setupFun_req_default _ ha)
  rw [setupFun_record] at this
  exact this

variable (D : Distinguisher W X Y Req Resp n m)

/-- **A step of the relayed distinguisher with other programs along `relSw`**: its entry at the
moved rows and columns is the entry with `F`'s programs, when the rows' and the columns' records
have their started requests satisfying `J` in `P`, their main request registers hold their
actions' main requests (the columns before step `0` a blank one), their side stores are read from
their records (the columns' at a clock `t < S`), and the
distinguisher's step at the controls agrees along `πin` of the rows' and the columns' records
(`hctrl`). -/
theorem unitaryMat_relay_step_relSw (h : F.ProgSwap p' J P sw swO) (hidle : sw F.idle = F.idle)
    (hdef : sw default = default) (hπ : RespSw b Q J swO πin)
    (hk : ∀ es w q a, D.kind (πin es (w, q, a)).1 = D.kind w)
    (hrq : ∀ es w q a, (πin es (w, q, a)).2.1 = q) (k : Fin (relaySlots n m F + 1)) (a c : RR)
    (hrecA : ∀ j r, (MultiRelay.recList a.1.1.record).getD j none = some r → J r = true → P r)
    (hrecC : ∀ j r, (MultiRelay.recList c.1.1.record).getD j none = some r → J r = true → P r)
    (ha : a.1.2.1 = askOf (F.actAt n b Q a.1.1.record a.1.1.store a.1.1.side a.1.1.time))
    (hsa : a.1.1.side = F.consSide n b Q a.1.1.record a.1.1.store a.1.1.time)
    (hc : (k : ℕ) ≠ 0 → c.1.2.1 = askOf (F.actAt n b Q c.1.1.record c.1.1.store c.1.1.side
        c.1.1.time) ∧ c.1.1.side = F.consSide n b Q c.1.1.record c.1.1.store c.1.1.time ∧
      (∃ es, RecAt (n := n) F b Q c.1.1.record es c.1.1.time) ∧
      (c.1.1.time : ℕ) < relaySlots n m F)
    (hc0 : (k : ℕ) = 0 → c.1.2.1 = default)
    (hctrl : rest F (recordFun F b Q D.kind (setupFun F b Q a)) =
        rest F (preFun F b Q k c) →
      unitaryMat (D.ctrlU F b Q (rest F (preFun F b Q k c)))
        (((πin (MultiRelay.recList a.1.1.record)).prodCongr (Equiv.refl _))
          (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)
            (recordFun F b Q D.kind (setupFun F b Q a))).1)
        (((πin (MultiRelay.recList c.1.1.record)).prodCongr (Equiv.refl _))
          (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys) (preFun F b Q
              k c)).1) =
      unitaryMat (D.ctrlU F b Q (rest F (preFun F b Q k c)))
        (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)
          (recordFun F b Q D.kind (setupFun F b Q a))).1
        (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys) (preFun F b Q k
            c)).1) :
    unitaryMat ((D.relay (F.withProg p') b Q).step k) (relSw F p' b Q J P sw πin a)
      (relSw F p' b Q J P sw πin c) = unitaryMat ((D.relay F b Q).step k) a c := by
  refine (D.unitaryMat_relay_step (F.withProg p') b Q k _ _).trans ?_
  rw [recordSetup_relSw h hidle hdef D.kind hk hrq a hrecA ha hsa,
    preFun_relSw h hidle hdef hπ k c hrecC hc hc0, D.unitaryMat_relay_step F b Q k a c]
  change unitaryMat (D.ctrlStep F b Q) _ _ = _
  rw [D.unitaryMat_ctrlStep_innerMap F b Q, D.unitaryMat_ctrlStep F b Q]
  split_ifs with hr
  · exact hctrl hr
  · rfl

end Distinguisher

end GordieHowe.Quantum
