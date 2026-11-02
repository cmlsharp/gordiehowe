-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.RelayBlockSwap
public import GordieHowe.Model.QROM.DensityRunBlock

@[expose] public section

/-!
# The well-formed registers of the relayed distinguisher

For a test `J` of the requests and sets `Gin es` of the
distinguisher's workspace, request and response registers read from the list `es` of its started
slots' entries:

- `MultiRelay.countReq`, `MultiRelay.JTagged`, `MultiRelay.firstJ`: the requests among the entries,
  the entries with at most one request satisfying `J`, and the first request satisfying `J`.
  `MultiRelay.eq_of_firstJ`, `MultiRelay.not_J_of_firstJ_none`: in a tagged list, every request
  satisfying `J` is the first one.
- `Distinguisher.GoodAt`, `Distinguisher.Good₀`: the relay's bookkeeping after the set-up of
  sub-slot `k` (`Distinguisher.Booked`), a tagged record, and the distinguisher's registers in
  `Gin` of the record; before step `0`, the blank registers.
- `Distinguisher.recordFun_record_ofList`, `Distinguisher.recordFun_inner`,
  `Distinguisher.recordFun_rest`, `Distinguisher.preFun_record_inner`,
  `Distinguisher.ofList_inj`, `Distinguisher.jTagged_append`: the parts of a step on a record of a
  list.
- `Distinguisher.InnerSupp`: the sets `Gin` closed under response changes after a request slot,
  containing the initial support, and carried by the distinguisher's steps with tagged entries.
- `Distinguisher.preFun_resp`, `Distinguisher.preFun_inner_mem`: the reply writes the response
  register only after a request slot, so the distinguisher's registers stay in `Gin`.
- **`Distinguisher.relay_step_good`**, `Distinguisher.relay_step_good_rec`: the steps keep the
  well-formed registers, the row's started slots being the column's with possibly one more starting
  at the step, and its answers stored before the column's clock the column's.
-/

set_option linter.unusedSectionVars false

namespace GordieHowe.Quantum

open GordieHowe.QROM (prevSeq)

namespace MultiRelay

variable {Req : Type} (J : Req → Bool)

/-- **The number of requests** among the entries. -/
def countReq (es : List (Option Req)) : ℕ :=
  es.countP Option.isSome

/-- **Tagged entries**: at most one entry is a request satisfying `J`. -/
def JTagged (es : List (Option Req)) : Prop :=
  ∀ (i i' : ℕ) (r r' : Req), es[i]? = some (some r) → es[i']? = some (some r') → J r = true →
    J r' = true → i = i'

variable {J} in
/-- **In a tagged list the requests satisfying `J` are all equal.** -/
theorem JTagged.eq {es : List (Option Req)} (h : JTagged J es) {i i' : ℕ} {r r' : Req}
    (hi : es[i]? = some (some r)) (hi' : es[i']? = some (some r')) (hr : J r = true)
    (hr' : J r' = true) : r = r' := by
  have := h i i' r r' hi hi' hr hr'
  subst this
  rw [hi] at hi'
  exact Option.some.inj (Option.some.inj hi')

/-- **The first request satisfying `J`** among the entries. -/
def firstJ (es : List (Option Req)) : Option Req :=
  (es.find? fun e => e.any J).bind id

variable {J}

/-- **In a tagged list every request satisfying `J` is the first one.** -/
theorem eq_of_firstJ {es : List (Option Req)} (hes : JTagged J es) {r₀ : Req}
    (h0 : firstJ J es = some r₀) {i : ℕ} {r : Req} (hi : es[i]? = some (some r))
    (hr : J r = true) : r = r₀ := by
  unfold firstJ at h0
  rcases hf : es.find? (fun e => e.any J) with _ | e
  · rw [hf] at h0
    exact absurd h0 (by simp)
  rw [hf] at h0
  obtain ⟨-, i₀, hi₀, he, -⟩ := List.find?_eq_some_iff_getElem.1 hf
  have he' : e = some r₀ := by simpa using h0
  subst he'
  have hi₀' : es[i₀]? = some (some r₀) := by rw [List.getElem?_eq_getElem hi₀, he]
  have hJ₀ : J r₀ = true := by
    have := List.find?_some hf
    simpa using this
  exact hes.eq hi hi₀' hr hJ₀

/-- **A list whose first request satisfying `J` is absent has none.** -/
theorem not_J_of_firstJ_none {es : List (Option Req)} (h0 : firstJ J es = none) {i : ℕ} {r : Req}
    (hi : es[i]? = some (some r)) : J r = false := by
  unfold firstJ at h0
  have hf : es.find? (fun e => e.any J) = none := by
    rcases hf : es.find? (fun e => e.any J) with _ | e
    · exact hf
    · rw [hf] at h0
      have := List.find?_some hf
      rcases e with _ | e
      · simp at this
      · simp at h0
  have hmem : some r ∈ es := List.mem_of_getElem? hi
  have := List.find?_eq_none.1 hf _ hmem
  simpa using this

end MultiRelay

namespace Distinguisher

variable {W X Y Req Resp Req' Resp' Xs Ys : Type} [Fintype W] [DecidableEq W] [Fintype X]
  [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Inhabited X] [Inhabited Req'] [AddGroup Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] {n m : ℕ}
  (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (b Q : ℕ) (J : Req → Bool)
  (Gin : List (Option Req) → Set (W × Req × Option Resp))

local notation "RR" => RelayReg W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)

local notation "RT" => RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F) (Fin F.qS →
    Ys) ×
  Req' × Option Resp'

/-- **The well-formed registers after step `k`**: the clock at `k`, the record a tagged list `es`
of slots started by `k`, the main request register holding the action's main request, the side
store read from the record (`MultiRelay.consSide`), and the distinguisher's workspace, request and
response registers in `Gin es`, or else every slot started and the distinguisher's last step
already applied (its block starting by `k`). -/
def GoodAt (k : ℕ) : Set RT :=
  {x | ∃ es, (x.1.time : ℕ) = k ∧ RecAt (n := n) F b Q x.1.record es k ∧
    x.2.1 = askOf (F.actAt n b Q x.1.record x.1.store x.1.side x.1.time) ∧
    x.1.side = F.consSide n b Q x.1.record x.1.store x.1.time ∧
    MultiRelay.JTagged J es ∧
    (x.1.inner.1 ∈ Gin es ∨ (es.length = m ∧ F.startAt n b Q es m ≤ k))}

/-- **The well-formed registers before step `0`**: the clock at `0`, a blank record, main request
register and side store, and the distinguisher's registers in `Gin []`. -/
def Good₀ : Set RT :=
  {x | (x.1.time : ℕ) = 0 ∧ x.1.record = (fun _ => none) ∧ x.2.1 = default ∧
    x.1.inner.1 ∈ Gin [] ∧ x.1.side = 0}

/-- **The label of the relayed registers**: the first started request satisfying `J`. -/
def jLabel (w : RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F) (Fin F.qS → Ys)) :
    Option Req :=
  MultiRelay.firstJ J (MultiRelay.recList w.record)

variable {F b Q}

/-- The record of the starting slot keeps the distinguisher's registers. -/
theorem recordFun_inner (kind : W → Bool) (d : RR) :
    (recordFun F b Q kind d).1.1.inner = d.1.1.inner := by
  unfold recordFun
  rcases F.fillAt n b Q d.1.1.record d.1.1.time <;> rfl

/-- The record of the starting slot keeps the stored answers, the clock, the main request and
response registers and the query pair. -/
theorem recordFun_rest (kind : W → Bool) (d : RR) :
    (recordFun F b Q kind d).1.1.store = d.1.1.store ∧
      (recordFun F b Q kind d).1.1.time = d.1.1.time ∧
      (recordFun F b Q kind d).1.2 = d.1.2 ∧ (recordFun F b Q kind d).2 = d.2 := by
  unfold recordFun
  rcases F.fillAt n b Q d.1.1.record d.1.1.time <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- **The record of the starting slot on the record of a list**: the list with the entry of the
distinguisher's registers appended when the next slot starts at the clock, else the list. -/
theorem recordFun_record_ofList (hn : 0 < n) (kind : W → Bool) (d : RR) {es : List (Option Req)}
    (hl : es.length ≤ m) (hr : d.1.1.record = fun i : Fin m => es[(i : ℕ)]?)
    (hs : ∀ i < es.length, F.startAt n b Q es i < d.1.1.time) :
    (recordFun F b Q kind d).1.1.record = fun i : Fin m =>
      (if F.startAt n b Q es es.length = d.1.1.time ∧ es.length < m then
        es ++ [entryOf kind d.1.1.inner] else es)[(i : ℕ)]? := by
  split_ifs with hf
  · have hfill := F.fillAt_ofList_eq_some n b Q hn hf.2 hf.1
    simp only [recordFun, hr, hfill]
    funext i
    by_cases hi : (i : ℕ) = es.length
    · have : i = ⟨es.length, hf.2⟩ := Fin.ext hi
      subst this
      simp
    · rw [Function.update_of_ne (fun e => hi (by rw [e]))]
      rcases Nat.lt_or_gt_of_ne hi with h | h
      · rw [List.getElem?_append_left h]
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
  · have hnone : F.fillAt n b Q (fun i : Fin m => es[(i : ℕ)]?) d.1.1.time = none := by
      refine F.fillAt_ofList_eq_none n b Q hl fun i hi him he => ?_
      rcases Nat.lt_or_eq_of_le hi with h | h
      · exact absurd he (Nat.ne_of_lt (hs i h))
      · exact hf ⟨h ▸ he, h ▸ him⟩
    simp only [recordFun, hr, hnone]

/-- The tear-down, the clock and the reply keep the record and the distinguisher's workspace and
request register, and advance the clock. -/
theorem preFun_record_inner (k : ℕ) (c : RR) :
    (preFun F b Q k c).1.1.record = c.1.1.record ∧
      (preFun F b Q k c).1.1.inner.1.1 = c.1.1.inner.1.1 ∧
      (preFun F b Q k c).1.1.inner.1.2.1 = c.1.1.inner.1.2.1 ∧
      (k ≠ 0 → (c.1.1.time : ℕ) < relaySlots n m F →
        ((preFun F b Q k c).1.1.time : ℕ) = c.1.1.time + 1) ∧
      (k = 0 → (preFun F b Q k c) = c) := by
  unfold preFun
  by_cases hk : k = 0
  · subst hk
    simp
  · simp only [hk, ↓reduceIte]
    have ht := teardownFun_record_time F b Q c
    have hti : (teardownFun F b Q c).1.1.inner.1 = c.1.1.inner.1 := by
      unfold teardownFun
      rcases F.actAt n b Q c.1.1.record c.1.1.store c.1.1.side c.1.1.time with i | x | r'
      · rfl
      · dsimp only
        split_ifs <;> rfl
      · dsimp only
        split_ifs <;> rfl
    have hfi : ∀ d : RR, (finalizeFun F b Q d).1.1.inner.1.1 = d.1.1.inner.1.1 ∧
        (finalizeFun F b Q d).1.1.inner.1.2.1 = d.1.1.inner.1.2.1 := fun d => by
      unfold finalizeFun
      split_ifs
      · rcases F.lastReply n b Q d.1.1.record d.1.1.store d.1.1.side <;> exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    obtain ⟨hf1, -, hf3, -⟩ := finalizeFun_parts F b Q
      (sideAddsPerm F b Q (tickPerm F (teardownFun F b Q c)))
    obtain ⟨ha1, -, ha3, -⟩ := sideAddsPerm_parts F b Q (tickPerm F (teardownFun F b Q c))
    have hai : (sideAddsPerm F b Q (tickPerm F (teardownFun F b Q c))).1.1.inner =
        (teardownFun F b Q c).1.1.inner := by
      rw [sideAddsPerm_apply]
      rfl
    have hw1 : (sideAddsPerm F b Q (tickPerm F (teardownFun F b Q c))).1.1.inner.1.1 =
        c.1.1.inner.1.1 := by
      rw [hai]
      exact congrArg (fun p => p.1) hti
    have hw2 : (sideAddsPerm F b Q (tickPerm F (teardownFun F b Q c))).1.1.inner.1.2.1 =
        c.1.1.inner.1.2.1 := by
      rw [hai]
      exact congrArg (fun p => p.2.1) hti
    refine ⟨hf1.trans (ha1.trans ht.1), (hfi _).1.trans hw1, (hfi _).2.trans hw2, fun _ hlt => ?_,
      fun h => h.elim⟩
    rw [hf3, ha3]
    change (finRotate _ (teardownFun F b Q c).1.1.time : ℕ) = _
    rw [ht.2.2, coe_finRotate_of_ne_last (fun h => by
      have := congrArg Fin.val h
      simp only [Fin.val_last] at this
      omega)]

/-- **The distinguisher's registers within the well-formed sets**: the sets `Gin` are closed under
changes of the response register after a request slot (the only slots whose reply the relay
writes), contain the initial state's support, and each step of the
distinguisher numbered by the started slots, while a slot is left to start, maps `Gin es` into
`Gin` of the list with the slot's entry, whose request, if it satisfies `J`, follows no started
request satisfying `J`. The last step is not constrained: after it the relay applies the
identity. -/
structure InnerSupp (D : Distinguisher W X Y Req Resp n m) : Prop where
  /-- Closed under changes of the response register after a request slot. -/
  resp : ∀ es w q a a', (w, q, a) ∈ Gin es → (∃ r, es.getLast? = some (some r)) →
    (w, q, a') ∈ Gin es
  /-- The initial state's support. -/
  init : ∀ d, D.init d ≠ 0 → d.1 ∈ Gin []
  /-- The steps. -/
  step : ∀ es (y x : DReg W n X Y Req Resp), es.length < m → x.1 ∈ Gin es →
    unitaryMat (D.stepAt es.length) y x ≠ 0 →
      y.1 ∈ Gin (es ++ [entryOf D.kind y]) ∧
        ∀ r, entryOf D.kind y = some r → J r = true →
          ∀ (i : ℕ) (r' : Req), es[i]? = some (some r') → J r' = false

omit [Fintype W] [DecidableEq W] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited X] [Inhabited Req']
  [AddGroup Y] in
theorem ofList_inj {es es' : List (Option Req)} (hl : es.length ≤ m) (hl' : es'.length ≤ m)
    (h : (fun i : Fin m => es[(i : ℕ)]?) = fun i : Fin m => es'[(i : ℕ)]?) : es = es' := by
  rw [← MultiRelay.recList_getElem? es hl, ← MultiRelay.recList_getElem? es' hl', h]

/-- A tagged list with an entry tagged at its end is tagged. -/
theorem jTagged_append {es : List (Option Req)} (h : MultiRelay.JTagged J es) {e : Option Req}
    (he : ∀ r, e = some r → J r = true →
      ∀ (i : ℕ) (r' : Req), es[i]? = some (some r') → J r' = false) :
    MultiRelay.JTagged J (es ++ [e]) := fun i i' r r' hi hi' hr hr' => by
  have hcase : ∀ {i : ℕ} {r : Req}, (es ++ [e])[i]? = some (some r) →
      es[i]? = some (some r) ∨ (i = es.length ∧ e = some r) := fun {i r} hi => by
    by_cases hil : i < es.length
    · rw [List.getElem?_append_left hil] at hi
      exact Or.inl hi
    · have hi' : i = es.length := by
        by_contra hne
        rw [List.getElem?_eq_none (by simp; omega)] at hi
        exact absurd hi (by simp)
      subst hi'
      rw [List.getElem?_append_right le_rfl, Nat.sub_self] at hi
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      exact Or.inr ⟨rfl, hi⟩
  rcases hcase hi with h1 | ⟨hi1, h1⟩ <;> rcases hcase hi' with h2 | ⟨hi2, h2⟩
  · exact h i i' r r' h1 h2 hr hr'
  · exact absurd hr (by rw [he r' h2 hr' i r h1]; simp)
  · exact absurd hr' (by rw [he r h1 hr i' r' h2]; simp)
  · exact hi1.trans hi2.symm

/-- **The reply writes the response register only after a request slot**: the tear-down, the
clock, the side additions and the reply keep the response register, or the last started slot is
a request. -/
theorem preFun_resp (k : ℕ) (c : RR) :
    (preFun F b Q k c).1.1.inner.1.2.2 = c.1.1.inner.1.2.2 ∨
      ∃ r, (MultiRelay.recList c.1.1.record).getLast? = some (some r) := by
  unfold preFun
  split_ifs with hk
  · exact Or.inl rfl
  set d := sideAddsPerm F b Q (tickPerm F (teardownFun F b Q c)) with hd
  have hdi : d.1.1.inner = (teardownFun F b Q c).1.1.inner := by
    rw [hd, sideAddsPerm_apply]
    rfl
  have hti : (teardownFun F b Q c).1.1.inner.1 = c.1.1.inner.1 := by
    unfold teardownFun
    rcases F.actAt n b Q c.1.1.record c.1.1.store c.1.1.side c.1.1.time with i | x | r'
    · rfl
    · dsimp only
      split_ifs <;> rfl
    · dsimp only
      split_ifs <;> rfl
  have hdr : d.1.1.record = c.1.1.record :=
    ((sideAddsPerm_parts F b Q _).1).trans (teardownFun_record_time F b Q c).1
  unfold finalizeFun
  split_ifs
  · rcases hL : F.lastReply n b Q d.1.1.record d.1.1.store d.1.1.side with _ | o
    · left
      change d.1.1.inner.1.2.2 = _
      rw [hdi, hti]
    · right
      rw [← hdr]
      unfold MultiRelay.lastReply at hL
      split_ifs at hL with hpos
      · rcases hb : MultiRelay.blkAt b Q (MultiRelay.recList d.1.1.record)
            ((MultiRelay.recList d.1.1.record).length - 1) with _ | _ | _ <;>
          rcases he : (MultiRelay.recList d.1.1.record).getD
            ((MultiRelay.recList d.1.1.record).length - 1) none with _ | r <;>
          simp only [hb, he] at hL <;> try cases hL
        refine ⟨r, ?_⟩
        rw [List.getLast?_eq_getElem?]
        rw [List.getD_eq_getElem?_getD] at he
        rcases h : (MultiRelay.recList d.1.1.record)[(MultiRelay.recList d.1.1.record).length - 1]?
          with _ | e
        · rw [h] at he
          cases he
        · rw [h] at he
          simp only [Option.getD_some] at he
          rw [he]
  · left
    change d.1.1.inner.1.2.2 = _
    rw [hdi, hti]

/-- **The distinguisher's registers before a step stay in `Gin`** after the tear-down, the clock,
the side additions and the reply. -/
theorem preFun_inner_mem {D : Distinguisher W X Y Req Resp n m} (hI : InnerSupp J Gin D)
    (k : ℕ) (c : RR) {es : List (Option Req)} (hrc : MultiRelay.recList c.1.1.record = es)
    (hin : c.1.1.inner.1 ∈ Gin es) : (preFun F b Q k c).1.1.inner.1 ∈ Gin es := by
  obtain ⟨-, hxw, hxq, -, -⟩ := preFun_record_inner (F := F) (b := b) (Q := Q) k c
  rcases preFun_resp (F := F) (b := b) (Q := Q) k c with h | h
  · have e : (preFun F b Q k c).1.1.inner.1 = c.1.1.inner.1 :=
      Prod.ext hxw (Prod.ext hxq h)
    rw [e]
    exact hin
  · have h1 := hI.resp es c.1.1.inner.1.1 c.1.1.inner.1.2.1 c.1.1.inner.1.2.2
      (preFun F b Q k c).1.1.inner.1.2.2 hin (hrc ▸ h)
    rw [← hxw, ← hxq] at h1
    exact h1

variable (D : Distinguisher W X Y Req Resp n m)

/-- **The steps of the relayed distinguisher keep the well-formed registers**: a nonzero entry of
step `k` at a column well formed before it has a row well formed after it, whose started slots are
the column's, possibly with one more starting at `k`, and whose answers stored before `k - 1` are
the column's. -/
theorem relay_step_good_rec (hn : 0 < n) (hI : InnerSupp J Gin D) (k : Fin (relaySlots n m F + 1))
    (a c : RR) (hc : c.1 ∈ prevSeq (fun k => GoodAt F b Q J Gin k) (Good₀ F Gin) k)
    (hne : unitaryMat ((D.relay F b Q).step k) a c ≠ 0) : a.1 ∈ GoodAt F b Q J Gin k ∧
      ∃ es, MultiRelay.recList c.1.1.record = es ∧ (MultiRelay.recList a.1.1.record = es ∨
        ∃ e, MultiRelay.recList a.1.1.record = es ++ [e] ∧ F.startAt n b Q es es.length = k) ∧
      ∀ u < (k : ℕ) - 1, MultiRelay.storeAt a.1.1.store u = MultiRelay.storeAt c.1.1.store u := by
  rw [D.unitaryMat_relay_step F b Q k a c, D.unitaryMat_ctrlStep F b Q] at hne
  set z := recordFun F b Q D.kind (setupFun F b Q a) with hz
  set x := preFun F b Q k c with hx
  have hza : setupFun F b Q (recordFun F b Q D.kind z) = a := by
    rw [hz, recordFun_recordFun, setupFun_setupFun]
  split_ifs at hne with hrest
  swap
  · exact absurd rfl hne
  obtain ⟨hxr, hxw, hxq, hxt, hx0⟩ := preFun_record_inner (F := F) (b := b) (Q := Q) k c
  have hzr : z.1.1.record = c.1.1.record := (congrArg (fun r => r.1) hrest).trans hxr
  have hzt : z.1.1.time = x.1.1.time := congrArg (fun r => r.2.2.2.1) hrest
  -- the bookkeeping of the row, with some list `es'`
  have hbk : ∃ es es', es.length ≤ m ∧ c.1.1.record = (fun i : Fin m => es[(i : ℕ)]?) ∧
      MultiRelay.JTagged J es ∧
      (c.1.1.inner.1 ∈ Gin es ∨ (es.length = m ∧ F.startAt n b Q es m < z.1.1.time)) ∧
      (∀ i < es.length, F.startAt n b Q es i < z.1.1.time) ∧
      Booked F b Q k es' a ∧
      ∀ u < (k : ℕ) - 1, MultiRelay.storeAt a.1.1.store u = MultiRelay.storeAt c.1.1.store u := by
    by_cases hk0 : (k : ℕ) = 0
    · simp only [prevSeq, hk0, ↓reduceIte] at hc
      obtain ⟨ht0, hr0, hq0, hin, -⟩ := hc
      obtain ⟨es', hbk⟩ := booked_zero F b Q hn D.kind (q := c) (z := z) ht0 hr0 hq0
        (hrest.trans (by rw [hx, hx0 hk0]))
      rw [hza] at hbk
      refine ⟨[], es', Nat.zero_le _, by rw [hr0]; funext i; simp,
        fun i i' r r' hi => by simp at hi,
        Or.inl hin, fun i hi => absurd hi (Nat.not_lt_zero _), ?_, fun u hu => by omega⟩
      rw [show (k : ℕ) = 0 from hk0]
      exact hbk
    · simp only [prevSeq, hk0, ↓reduceIte] at hc
      obtain ⟨es, ht, hrec, hq, -, hJ, hin⟩ := hc
      have hkS : (k : ℕ) - 1 < relaySlots n m F := by
        have := k.isLt
        omega
      obtain ⟨es', -, hbk, hsto, -⟩ := booked_succ F b Q hn D.kind hkS ⟨ht, hrec, hq⟩
        (hrest.trans (by rw [hx]; unfold preFun; simp only [hk0, ↓reduceIte]))
      rw [hza, show (k : ℕ) - 1 + 1 = k by omega] at hbk
      rw [hza] at hsto
      have hzk : (z.1.1.time : ℕ) = (k : ℕ) - 1 + 1 := by
        rw [hzt, hxt hk0 (by rw [ht]; exact hkS), ht]
      refine ⟨es, es', hrec.1, hrec.2.1, hJ, hin.imp_right fun h => ⟨h.1, by rw [hzk]; omega⟩,
        fun i hi => ?_, hbk, hsto⟩
      rw [hzk]
      exact Nat.lt_succ_of_le (hrec.2.2 i hi)
  obtain ⟨es, es', hl, hrc, hJ, hin, hs, ⟨hta, hreca, hqa⟩, hsto⟩ := hbk
  have hzk : (z.1.1.time : ℕ) = k := by
    rw [← hta]
    conv_rhs => rw [← hza]
    exact congrArg Fin.val ((setupFun_store_time (F := F) (b := b) (Q := Q) _).2.trans
      (recordFun_rest (F := F) (b := b) (Q := Q) D.kind z).2.1).symm
  have hzrec : z.1.1.record = fun i : Fin m => es[(i : ℕ)]? := hzr.trans hrc
  have hrecz := recordFun_record_ofList hn D.kind z hl hzrec hs
  have harec : a.1.1.record = (recordFun F b Q D.kind z).1.1.record := by
    conv_lhs => rw [← hza]
    exact setupFun_record _
  have hain : a.1.1.inner.1 = z.1.1.inner.1 := by
    rw [← hza, setupFun_inner_fst, recordFun_inner]
  have hxin : c.1.1.inner.1 ∈ Gin es → x.1.1.inner.1 ∈ Gin es := fun hin =>
    preFun_inner_mem J Gin hI k c (by rw [hrc, MultiRelay.recList_getElem? es hl]) hin
  have hxl : MultiRelay.recList x.1.1.record = es := by
    rw [hxr, hrc, MultiRelay.recList_getElem? es hl]
  -- the list of the row
  have hes' : es' = if F.startAt n b Q es es.length = z.1.1.time ∧ es.length < m then
      es ++ [entryOf D.kind z.1.1.inner] else es := by
    refine ofList_inj hreca.1 ?_ (hreca.2.1.symm.trans (harec.trans hrecz))
    split_ifs with hf
    · simp only [List.length_append, List.length_singleton]
      omega
    · exact hl
  have hal : MultiRelay.recList a.1.1.record = es' := by
    rw [hreca.2.1, MultiRelay.recList_getElem? es' hreca.1]
  -- the side store of the column after the tear-down, the clock and the reply is read from its
  -- record
  have hxs : x.1.1.side = F.consSide n b Q x.1.1.record x.1.1.store x.1.1.time := by
    by_cases hk0 : (k : ℕ) = 0
    · simp only [prevSeq, hk0, ↓reduceIte] at hc
      obtain ⟨-, hr0, -, -, hs0⟩ := hc
      rw [hx, hx0 hk0, hs0, hr0, F.consSide_blank]
    · simp only [prevSeq, hk0, ↓reduceIte] at hc
      obtain ⟨esc, htc, hrecc, -, hsc, -, -⟩ := hc
      have hkS : (k : ℕ) - 1 < relaySlots n m F := by
        have := k.isLt
        omega
      exact side_preFun (F := F) (b := b) (Q := Q) k hk0 c (by rw [htc]; exact hrecc)
        (by rw [htc]; exact hkS) hsc
  have has : a.1.1.side = F.consSide n b Q a.1.1.record a.1.1.store a.1.1.time := by
    obtain ⟨e1, e2⟩ := setupFun_store_time (F := F) (b := b) (Q := Q)
      (recordFun F b Q D.kind z)
    obtain ⟨r1, r2, -, -⟩ := recordFun_rest (F := F) (b := b) (Q := Q) D.kind z
    have hzs : z.1.1.side = x.1.1.side := congrArg (fun r => r.2.2.1) hrest
    have hzst : z.1.1.store = x.1.1.store := congrArg (fun r => r.2.1) hrest
    rw [harec]
    conv_lhs => rw [← hza]
    conv_rhs => rw [← hza]
    rw [setupFun_side, recordFun_side, e1, e2, r1, r2, consSide_recordFun, hzs, hxs, hzst, hzt,
      hzr, hxr]
  refine ⟨⟨es', hta, hreca, hqa, has, ?_⟩, es, by rw [hrc, MultiRelay.recList_getElem? es hl], ?_,
    hsto⟩
  swap
  · rw [hal]
    split_ifs at hes' with hf
    · exact Or.inr ⟨_, hes', hf.1.trans hzk⟩
    · exact Or.inl hes'
  change MultiRelay.JTagged J es' ∧
    (a.1.1.inner.1 ∈ Gin es' ∨ (es'.length = m ∧ F.startAt n b Q es' m ≤ (k : ℕ)))
  rw [hain, hes']
  unfold ctrlU at hne
  change unitaryMat (if F.startAt n b Q (MultiRelay.recList x.1.1.record)
      (MultiRelay.recList x.1.1.record).length = (x.1.1.time : ℕ) then
        D.stepAt (MultiRelay.recList x.1.1.record).length else LinearIsometryEquiv.refl ℂ _)
      z.1.1.inner x.1.1.inner ≠ 0 at hne
  rw [hxl, ← hzt] at hne
  by_cases hf : F.startAt n b Q es es.length = (z.1.1.time : ℕ)
  · simp only [hf, ↓reduceIte] at hne
    -- the column is before the distinguisher's step of the started slots
    have hcin : c.1.1.inner.1 ∈ Gin es := by
      rcases hin with h | ⟨hm, hlt⟩
      · exact h
      · have : F.startAt n b Q es m = F.startAt n b Q es es.length := congrArg _ hm.symm
        omega
    by_cases hm : es.length < m
    · have hst := hI.step es z.1.1.inner x.1.1.inner hm (hxin hcin) hne
      simp only [hf, hm, and_self, ↓reduceIte]
      exact ⟨jTagged_append J hJ hst.2, Or.inl hst.1⟩
    · simp only [hf, hm, and_false, ↓reduceIte]
      have hm' : es.length = m := by omega
      refine ⟨hJ, Or.inr ⟨hm', ?_⟩⟩
      have : F.startAt n b Q es es.length = F.startAt n b Q es m := congrArg _ hm'
      omega
  · simp only [hf, ↓reduceIte, unitaryMat_refl] at hne
    have hzx : z.1.1.inner = x.1.1.inner := by
      by_contra hne'
      exact hne (Matrix.one_apply_ne hne')
    simp only [hf, false_and, ↓reduceIte]
    rw [hzx]
    refine ⟨hJ, ?_⟩
    rcases hin with h | ⟨hm, hlt⟩
    · exact Or.inl (hxin h)
    · exact Or.inr ⟨hm, by omega⟩

/-- **The steps of the relayed distinguisher keep the well-formed registers.** -/
theorem relay_step_good (hn : 0 < n) (hI : InnerSupp J Gin D) (k : Fin (relaySlots n m F + 1))
    (a c : RR) (hc : c.1 ∈ prevSeq (fun k => GoodAt F b Q J Gin k) (Good₀ F Gin) k)
    (hne : unitaryMat ((D.relay F b Q).step k) a c ≠ 0) : a.1 ∈ GoodAt F b Q J Gin k :=
  (relay_step_good_rec J Gin D hn hI k a c hc hne).1

end Distinguisher

end GordieHowe.Quantum
