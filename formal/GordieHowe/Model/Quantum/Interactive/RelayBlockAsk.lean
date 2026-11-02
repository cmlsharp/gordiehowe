-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.RelayBlockAdv
public import GordieHowe.Model.Quantum.Interactive.AbsorbTabBlock
public import GordieHowe.Model.Quantum.Interactive.AbortBlock
public import GordieHowe.Model.Quantum.Interactive.BlockRel

@[expose] public section

/-!
# The sub-slot of the main request of the relayed request satisfying a test

For a relay `F` and a test `J` of the requests, the sub-slot at which the started request
satisfying `J` asks its main request, read from the record and the stored answers up to the
clock, and the well-formed registers of the relayed distinguisher along it:

- `MultiRelay.askIn`, `MultiRelay.askJ`, `MultiRelay.askSlot`: sub-slot `t` asks a main request in
  the block of slot `i`, in the block of a request satisfying `J`; the first such sub-slot up to
  the clock. `askIn_iff`, `askJ_iff`, `askSlot_le`, `askSlot_nil`, `askSlot_succ`,
  `askSlot_zero`, `askSlot_congr`, `askSlot_of_first`.
- `MultiRelay.askIn_append`, `MultiRelay.askIn_store_congr`, `MultiRelay.askIn_of_lt`,
  `MultiRelay.askSlot_step`: the slot
  survives starting a further slot and changing the stored answers from the clock on.
- `MultiRelay.askIn_unique`: with one main request per relayed request, a block asks at one
  sub-slot at most.
- `MultiRelay.consistent_stAt`, `MultiRelay.act_stAt_off`: the states read with the side function
  are consistent with it, so off `J` the main requests asked are fixed by a permutation `sw` fixing
  the resolved programs' (`MultiRelay.OffTagFixed`) and the padding request.
- `MultiRelay.curSw_eq_or`, `Distinguisher.relSwW`, `Distinguisher.relSwT_apply`: the current
  slot's permutation is `sw` or the identity; `relSwT` on the workspace.
- `Distinguisher.goodAt_sw_or`: on the well-formed registers, the main request register is fixed by
  `sw`, or the current slot's permutation is `sw` and the clock is the slot of `askSlot`.
- `Distinguisher.jSlotStep_relay`: the slot changes only at its step (`AdaptiveIAlg.JSlotStep`).
- `AdaptiveIAlg.JSlotStep.toTP`, `AdaptiveIAlg.JSlotStep.restrictAt`: through the aborting
  completion and at a base part; `AdaptiveIAlg.jSlotStep_relayAdv`: for the relayed adversary.
-/

set_option linter.unusedSectionVars false

namespace GordieHowe.Quantum

open GordieHowe.QROM (prevSeq)

namespace MultiRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)
  [Inhabited X] [Zero Y] [Zero Ys] (n b Q : ℕ) (J : Req → Bool)

/-- **Sub-slot `t` asks a main request in the block of slot `i`**: slot `i` is a relayed request
`r` whose block contains `t`, and `r`'s program asks a main request at `t` on the answers stored
in the block before `t`, its side reads answered by the side function. -/
def askIn (es : List (Option Req)) {S : ℕ} (store : Fin S → Option Resp' × (X × Y)) (i t : ℕ) :
    Bool :=
  match blkAt b Q es i, es.getD i none with
  | .rel, some r => decide (F.startAt n b Q es i ≤ t ∧ t < F.startAt n b Q es i + F.len) &&
      (F.act r (F.stAt F.sideSa r (fun k => storeAt store (F.startAt n b Q es i + k))
        (t - F.startAt n b Q es i))).isRight
  | _, _ => false

/-- **Sub-slot `t` asks a main request in the block of a started request satisfying `J`.** -/
def askJ (es : List (Option Req)) {S : ℕ} (store : Fin S → Option Resp' × (X × Y)) (t : ℕ) :
    Bool :=
  (List.range es.length).any fun i => (es.getD i none).any J && F.askIn n b Q es store i t

/-- **The sub-slot of the main request of the started request satisfying `J`**: the first
sub-slot up to the clock `time` of `askJ`. -/
def askSlot (es : List (Option Req)) {S : ℕ} (store : Fin S → Option Resp' × (X × Y))
    (time : ℕ) : Option ℕ :=
  (List.range (time + 1)).find? (F.askJ n b Q J es store)

variable {F n b Q J} {S : ℕ}

theorem askIn_iff {es : List (Option Req)} {store : Fin S → Option Resp' × (X × Y)} {i t : ℕ} :
    F.askIn n b Q es store i t = true ↔ ∃ r, blkAt b Q es i = .rel ∧ es.getD i none = some r ∧
      F.startAt n b Q es i ≤ t ∧ t < F.startAt n b Q es i + F.len ∧
      (F.act r (F.stAt F.sideSa r (fun k => storeAt store (F.startAt n b Q es i + k))
        (t - F.startAt n b Q es i))).isRight = true := by
  unfold askIn
  rcases hb : blkAt b Q es i with _ | _ | _ <;> rcases he : es.getD i none with _ | r <;>
    simp [and_assoc]

theorem askJ_iff {es : List (Option Req)} {store : Fin S → Option Resp' × (X × Y)} {t : ℕ} :
    F.askJ n b Q J es store t = true ↔ ∃ i < es.length, ∃ r, es.getD i none = some r ∧
      J r = true ∧ F.askIn n b Q es store i t = true := by
  unfold askJ
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true]
  constructor
  · rintro ⟨i, hi, hJ, ha⟩
    rcases he : es.getD i none with _ | r
    · rw [he] at hJ
      cases hJ
    · rw [he] at hJ
      exact ⟨i, hi, r, he, hJ, ha⟩
  · rintro ⟨i, hi, r, he, hJ, ha⟩
    exact ⟨i, hi, by rw [he]; exact hJ, ha⟩

theorem askSlot_le {es : List (Option Req)} {store : Fin S → Option Resp' × (X × Y)}
    {time t : ℕ} (h : F.askSlot n b Q J es store time = some t) : t ≤ time := by
  have := List.mem_of_find?_eq_some h
  rw [List.mem_range] at this
  omega

theorem askSlot_nil (store : Fin S → Option Resp' × (X × Y)) (time : ℕ) :
    F.askSlot n b Q J [] store time = none :=
  List.find?_eq_none.2 fun t _ => by simp [askJ]

theorem askSlot_succ (es : List (Option Req)) (store : Fin S → Option Resp' × (X × Y))
    (k : ℕ) : F.askSlot n b Q J es store (k + 1) =
      (F.askSlot n b Q J es store k).or
        (if F.askJ n b Q J es store (k + 1) then some (k + 1) else none) := by
  unfold askSlot
  rw [List.range_succ, List.find?_append, List.find?_singleton]

theorem askSlot_zero (es : List (Option Req)) (store : Fin S → Option Resp' × (X × Y)) :
    F.askSlot n b Q J es store 0 = if F.askJ n b Q J es store 0 then some 0 else none := by
  unfold askSlot
  rw [show List.range (0 + 1) = [0] from rfl, List.find?_singleton]

theorem askSlot_congr {es es' : List (Option Req)} {S' : ℕ}
    {store : Fin S → Option Resp' × (X × Y)} {store' : Fin S' → Option Resp' × (X × Y)} :
    ∀ {time : ℕ}, (∀ t ≤ time, F.askJ n b Q J es' store' t = F.askJ n b Q J es store t) →
      F.askSlot n b Q J es' store' time = F.askSlot n b Q J es store time
  | 0, h => by rw [askSlot_zero, askSlot_zero, h 0 le_rfl]
  | k + 1, h => by
    rw [askSlot_succ, askSlot_succ, h (k + 1) le_rfl,
      askSlot_congr fun t ht => h t (Nat.le_succ_of_le ht)]

/-- **The slot is the clock** when the clock asks and no earlier sub-slot does. -/
theorem askSlot_of_first {es : List (Option Req)} {store : Fin S → Option Resp' × (X × Y)}
    {time : ℕ} (h : F.askJ n b Q J es store time = true)
    (hlt : ∀ t < time, F.askJ n b Q J es store t = false) :
    F.askSlot n b Q J es store time = some time := by
  unfold askSlot
  rw [List.range_succ, List.find?_append, List.find?_singleton, h]
  rw [List.find?_eq_none.2 fun t ht => by
    rw [List.mem_range] at ht
    simp [hlt t ht]]
  rfl

/-- **An ask in a started block survives starting a further slot.** -/
theorem askIn_append {es : List (Option Req)} (e : Option Req)
    (store : Fin S → Option Resp' × (X × Y)) {i : ℕ} (hi : i < es.length) (t : ℕ) :
    F.askIn n b Q (es ++ [e]) store i t = F.askIn n b Q es store i t := by
  unfold askIn
  rw [blkAt_append_of_lt b Q e hi, F.startAt_append_of_le n b Q e hi.le,
    List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]

/-- **An ask at `t` reads the stored answers before `t` only.** -/
theorem askIn_store_congr {es : List (Option Req)} {S' : ℕ}
    {store : Fin S → Option Resp' × (X × Y)} {store' : Fin S' → Option Resp' × (X × Y)}
    {i t : ℕ} (hs : ∀ u < t, storeAt store' u = storeAt store u) :
    F.askIn n b Q es store' i t = F.askIn n b Q es store i t := by
  unfold askIn
  rcases hb : blkAt b Q es i with _ | _ | _ <;> rcases he : es.getD i none with _ | r <;>
    simp only
  by_cases ht : F.startAt n b Q es i ≤ t ∧ t < F.startAt n b Q es i + F.len
  · rw [F.stAt_congr _ r fun k hk => hs (F.startAt n b Q es i + k) (by omega)]
  · simp [ht]

theorem askIn_of_lt {es : List (Option Req)} {store : Fin S → Option Resp' × (X × Y)} {i t : ℕ}
    (ht : t < F.startAt n b Q es i) : F.askIn n b Q es store i t = false := by
  rcases h : F.askIn n b Q es store i t
  · rfl
  · obtain ⟨r, -, -, h1, -⟩ := askIn_iff.1 h
    omega

/-- **The slot across a step**: from the clock `k` to `k + 1`, with the started slots kept or one
more starting at `k + 1` and the answers stored before `k` kept, the slot is kept, or set to
`k + 1` from none. -/
theorem askSlot_step {es es' : List (Option Req)} {S' : ℕ}
    {store : Fin S → Option Resp' × (X × Y)} {store' : Fin S' → Option Resp' × (X × Y)} {k : ℕ}
    (hes : es' = es ∨ ∃ e, es' = es ++ [e] ∧ F.startAt n b Q es es.length = k + 1)
    (hs : ∀ u < k, storeAt store' u = storeAt store u) :
    F.askSlot n b Q J es' store' (k + 1) = F.askSlot n b Q J es store k ∨
      (F.askSlot n b Q J es store k = none ∧
        F.askSlot n b Q J es' store' (k + 1) = some (k + 1)) := by
  have hJ : ∀ t ≤ k, F.askJ n b Q J es' store' t = F.askJ n b Q J es store t := by
    intro t ht
    have hst : ∀ i, F.askIn n b Q es store' i t = F.askIn n b Q es store i t := fun i =>
      askIn_store_congr fun u hu => hs u (by omega)
    rcases hes with rfl | ⟨e, rfl, he⟩
    · unfold askJ
      simp only [hst]
    · refine Bool.eq_iff_iff.2 ⟨fun h => ?_, fun h => ?_⟩
      · obtain ⟨i, hi, r, hr, hJr, ha⟩ := askJ_iff.1 h
        rw [List.length_append, List.length_singleton] at hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi,
            ← List.getD_eq_getElem?_getD] at hr
          rw [askIn_append e _ hi, hst] at ha
          exact askJ_iff.2 ⟨i, hi, r, hr, hJr, ha⟩
        · rw [askIn_of_lt (by rw [F.startAt_append_of_le n b Q e le_rfl, he]; omega)] at ha
          cases ha
      · obtain ⟨i, hi, r, hr, hJr, ha⟩ := askJ_iff.1 h
        refine askJ_iff.2 ⟨i, by simp; omega, r, ?_, hJr, ?_⟩
        · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi,
            ← List.getD_eq_getElem?_getD]
          exact hr
        · rw [askIn_append e _ hi, hst]
          exact ha
  have hk : F.askSlot n b Q J es' store' k = F.askSlot n b Q J es store k := askSlot_congr hJ
  rw [askSlot_succ, hk]
  rcases F.askSlot n b Q J es store k with _ | t
  · by_cases ha : F.askJ n b Q J es' store' (k + 1) = true
    · exact Or.inr ⟨rfl, by simp [ha]⟩
    · exact Or.inl (by simp [ha])
  · exact Or.inl rfl

/-- **With one main request per relayed request, a block asks at one sub-slot at most.** -/
theorem askIn_unique (hK : F.K = 1) {es : List (Option Req)}
    {store : Fin S → Option Resp' × (X × Y)} {i t t' : ℕ} (h : F.askIn n b Q es store i t = true)
    (h' : F.askIn n b Q es store i t' = true) : t = t' := by
  obtain ⟨r, -, hr, h1, -, ha⟩ := askIn_iff.1 h
  obtain ⟨r', -, hr', h1', -, ha'⟩ := askIn_iff.1 h'
  rw [hr] at hr'
  cases hr'
  by_contra hne
  have hsub : t - F.startAt n b Q es i ≠ t' - F.startAt n b Q es i := by omega
  have hc := F.card_isRight_le F.sideSa r
    (fun k => storeAt store (F.startAt n b Q es i + k))
    (max (t - F.startAt n b Q es i) (t' - F.startAt n b Q es i) + 1)
  have h2 : ({t - F.startAt n b Q es i, t' - F.startAt n b Q es i} : Finset ℕ) ⊆
      (Finset.range (max (t - F.startAt n b Q es i) (t' - F.startAt n b Q es i) + 1)).filter
        fun s => (F.act r (F.stAt F.sideSa r
          (fun k => storeAt store (F.startAt n b Q es i + k)) s)).isRight := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl <;> simp only [Finset.mem_filter, Finset.mem_range] <;>
      refine ⟨by omega, ?_⟩
    · exact ha
    · exact ha'
  have := Finset.card_le_card h2
  rw [Finset.card_pair hsub] at this
  rw [hK] at hc
  omega

/-- **The states read with the side function are consistent with it.** -/
theorem consistent_stAt (r : Req) (g : ℕ → Option Resp' × (X × Y)) :
    ∀ i, OracleProg.Consistent F.side (F.prog r) (F.stAt F.sideSa r g i).ans
  | 0 => OracleProg.Consistent.nil _ _
  | i + 1 => by
    have hnext : OracleProg.Consistent F.side (F.prog r)
        (F.next r (F.stAt F.sideSa r g i) (g i)).ans := by
      have hc := consistent_stAt r g i
      unfold next
      rcases hp : F.progAct r (F.stAt F.sideSa r g i) with _ | ((x | x) | r')
      · split_ifs <;> exact hc
      · obtain ⟨-, ha⟩ := F.progAct_plain hp
        exact OracleProg.Consistent.append_plain hc ha (fun x' e => by cases e) rfl
      · split_ifs <;> exact hc
      · obtain ⟨-, ha⟩ := F.progAct_plain hp
        exact OracleProg.Consistent.append_plain hc ha (fun x' e => by cases e) rfl
    change OracleProg.Consistent F.side (F.prog r) ((F.sideStep F.sideSa r)^[F.qS] _).ans
    generalize F.next r (F.stAt F.sideSa r g i) (g i) = st at hnext
    induction F.qS generalizing st with
    | zero => exact hnext
    | succ j ih =>
      rw [Function.iterate_succ_apply]
      refine ih _ ?_
      unfold sideStep
      rcases hp : F.progAct r st with _ | ((x | x) | r')
      · exact hnext
      · exact hnext
      · obtain ⟨-, ha⟩ := F.progAct_plain hp
        exact OracleProg.Consistent.append_side hnext ha
      · exact hnext

/-- **Off `J` the main requests asked are fixed by `sw`**, when `sw` fixes the resolved
programs' off `J` and the padding request. -/
theorem act_stAt_off {sw : Equiv.Perm Req'} (hoff : F.OffTagFixed J sw)
    (hidle : sw F.idle = F.idle) {r : Req} (hr : J r = false) (g : ℕ → Option Resp' × (X × Y))
    (i : ℕ) {r' : Req'} (h : F.act r (F.stAt F.sideSa r g i) = .inr r') : sw r' = r' := by
  unfold act at h
  rcases hp : F.progAct r (F.stAt F.sideSa r g i) with _ | ((x | x) | r'') <;>
    simp only [hp] at h
  · split_ifs at h
    · cases h
      exact hidle
  · cases h
  · split_ifs at h
    cases h
    exact hidle
  · cases h
    obtain ⟨-, ha⟩ := F.progAct_plain hp
    obtain ⟨k, hk⟩ := OracleProg.rest_of_after ha
    have hres := OracleProg.after_resolve F.side (F.prog r) _ (F.consistent_stAt r g i)
    rw [hk] at hres
    have hq := hoff r hr (OracleProg.plainList (F.stAt F.sideSa r g i).ans)
    rw [hres] at hq
    simpa [OracleProg.resolve, OracleProg.after] using hq

omit [Inhabited X] [Zero Y] [Zero Ys] in
/-- **The current slot's permutation is `sw` or the identity.** -/
theorem curSw_eq_or (sw : Equiv.Perm Req') {m : ℕ} (rec : Fin m → Option (Option Req)) (t : ℕ) :
    F.curSw J sw n b Q rec t = sw ∨ F.curSw J sw n b Q rec t = Equiv.refl _ := by
  unfold curSw swAt
  rcases F.curBlk n b Q rec t with _ | ⟨j, sub⟩
  · exact Or.inr rfl
  · simp only
    rcases blkAt b Q (recList rec) j with _ | _ | _ <;>
      rcases (recList rec).getD j none with _ | r <;> simp only
    all_goals first | (cases J r <;> simp) | simp

end MultiRelay

namespace Distinguisher

section SwapW

variable {W X Y Req Resp Req' Resp' Xs Ys : Type} [Fintype W] [DecidableEq W] [Fintype X]
  [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Inhabited X] [Inhabited Req'] [AddGroup Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] {n m : ℕ}
  (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)
  (p' : Req → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') (Option Resp)) (b Q : ℕ)
  (J : Req → Bool) (P : Req → Prop) [DecidablePred P] (sw : Equiv.Perm Req')
  (πin : List (Option Req) → Equiv.Perm (W × Req × Option Resp))

/-- **`relSwT` on the workspace**: the distinguisher's registers by `πin` of the record, the side
store by `sideSw`. -/
def relSwW : Equiv.Perm
    (RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F) (Fin F.qS → Ys)) where
  toFun w := ⟨(πin (MultiRelay.recList w.record) w.inner.1, w.inner.2), w.record, w.store,
    sideSw F p' b Q J P w.record w.store w.time w.side, w.time⟩
  invFun w := ⟨((πin (MultiRelay.recList w.record)).symm w.inner.1, w.inner.2), w.record,
    w.store, sideSw F p' b Q J P w.record w.store w.time w.side, w.time⟩
  left_inv w := by
    obtain ⟨⟨w, p⟩, rec, store, side, t⟩ := w
    simp [sideSw_sideSw]
  right_inv w := by
    obtain ⟨⟨w, p⟩, rec, store, side, t⟩ := w
    simp [sideSw_sideSw]

/-- **`relSwT` splits** as `relSwW` on the workspace and the current slot's permutation on the
main request register. -/
theorem relSwT_apply (x : RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F)
    (Fin F.qS → Ys) × Req' × Option Resp') :
    relSwT F p' b Q J P sw πin x =
      (relSwW F p' b Q J P πin x.1, F.curSw J sw n b Q x.1.record x.1.time x.2.1, x.2.2) :=
  rfl

end SwapW


variable {W X Y Req Resp Req' Resp' Xs Ys : Type} [Fintype W] [DecidableEq W] [Fintype X]
  [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Inhabited X] [Inhabited Req'] [AddGroup Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] {n m : ℕ}
  {F : MultiRelay X Y Req Resp Req' Resp' Xs Ys} {b Q : ℕ} {J : Req → Bool}
  {Gin : List (Option Req) → Set (W × Req × Option Resp)}

/-- **On the well-formed registers the main request register is fixed by `sw`, or the current
slot's permutation is `sw` and the clock is the slot of `askSlot`**, for one main request per
relayed request and `sw` fixing the resolved programs' main requests off `J`, the padding and
the blank request. -/
theorem goodAt_sw_or (hK : F.K = 1) {sw : Equiv.Perm Req'} (hoff : F.OffTagFixed J sw)
    (hidle : sw F.idle = F.idle) (hdef : sw default = default) {k : ℕ}
    {x : RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F) (Fin F.qS → Ys) ×
      Req' × Option Resp'} (hx : x ∈ GoodAt F b Q J Gin k) :
    sw x.2.1 = x.2.1 ∨ (F.curSw J sw n b Q x.1.record x.1.time = sw ∧
      F.askSlot n b Q J (MultiRelay.recList x.1.record) x.1.store x.1.time = some x.1.time) := by
  obtain ⟨es, -, hrec, hq, hs, hJ, -⟩ := hx
  have hrl : MultiRelay.recList x.1.record = es := by
    rw [hrec.2.1]
    exact MultiRelay.recList_getElem? es hrec.1
  rw [hq, hs]
  unfold MultiRelay.actAt MultiRelay.curSw
  rcases hc : F.curBlk n b Q x.1.record x.1.time with _ | ⟨j, sub⟩
  · exact Or.inl hidle
  obtain ⟨-, hst, hsub⟩ := F.curBlk_eq_some hc
  simp only
  rcases hbk : MultiRelay.blkAt b Q (MultiRelay.recList x.1.record) j with _ | _ | _ <;>
    rcases he : (MultiRelay.recList x.1.record).getD j none with _ | r <;> simp only
  · split_ifs
    · exact Or.inl hdef
    · exact Or.inl hidle
  · split_ifs
    · exact Or.inl hdef
    · exact Or.inl hidle
  · exact Or.inl hidle
  · exact Or.inl hidle
  · exact Or.inl hidle
  rw [F.stAt_consSide_curBlk n b Q x.1.store x.1.time hc hbk he]
  rcases ha : F.act r (F.stAt F.sideSa r (fun k => MultiRelay.storeAt x.1.store
      (F.startAt n b Q (MultiRelay.recList x.1.record) j + k)) sub) with (y | y) | r'
  · exact Or.inl hdef
  · exact Or.inl hdef
  by_cases hJr : J r = true
  swap
  · exact Or.inl (F.act_stAt_off hoff hidle (by simpa using hJr) _ sub ha)
  refine Or.inr ⟨by simp [MultiRelay.swAt, hJr], ?_⟩
  have hlen : F.blkLen n .rel = F.len := rfl
  rw [hbk, hlen] at hsub
  have hjl : j < (MultiRelay.recList x.1.record).length := by
    by_contra hj
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at he
    cases he
  have hin : F.askIn n b Q (MultiRelay.recList x.1.record) x.1.store j x.1.time = true := by
    refine MultiRelay.askIn_iff.2 ⟨r, hbk, he, by omega, by omega, ?_⟩
    rw [show (x.1.time : ℕ) - F.startAt n b Q (MultiRelay.recList x.1.record) j = sub by omega,
      ha]
    rfl
  refine MultiRelay.askSlot_of_first (MultiRelay.askJ_iff.2 ⟨j, hjl, r, he, hJr, hin⟩)
    fun t ht => ?_
  by_contra hne
  obtain ⟨i, -, r₂, he₂, hJ₂, hin₂⟩ := MultiRelay.askJ_iff.1 (by simpa using hne)
  have hij : i = j := by
    rw [hrl] at he he₂
    rw [List.getD_eq_getElem?_getD] at he he₂
    refine hJ i j r₂ r ?_ ?_ hJ₂ hJr
    · rcases h : es[i]? with _ | e
      · rw [h] at he₂
        cases he₂
      · rw [h] at he₂
        simp only [Option.getD_some] at he₂
        rw [he₂]
    · rcases h : es[j]? with _ | e
      · rw [h] at he
        cases he
      · rw [h] at he
        simp only [Option.getD_some] at he
        rw [he]
  subst hij
  have := MultiRelay.askIn_unique hK hin₂ hin
  omega

variable (J Gin) (D : Distinguisher W X Y Req Resp n m)

/-- **The slot of `askSlot` changes only at its step** on the well-formed registers of the relayed
distinguisher. -/
theorem jSlotStep_relay (hn : 0 < n) (hI : InnerSupp J Gin D) (q : ℕ) {O : Type}
    (out : RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F) (Fin F.qS → Ys) → O) :
    ((D.relay F b Q).toAdaptive Nat.one_pos q out).JSlotStep (fun k => GoodAt F b Q J Gin k)
      (Good₀ F Gin)
      (fun w => F.askSlot n b Q J (MultiRelay.recList w.record) w.store w.time) := by
  intro k i a c hc hne
  rw [Distinguisher.toAdaptive_op] at hne
  change unitaryMat ((D.relay F b Q).stepAt k) a c ≠ 0 at hne
  erw [stepAt_of_lt _ k k.isLt] at hne
  obtain ⟨hga, es, hes, hrec, hsto⟩ := relay_step_good_rec J Gin D hn hI ⟨k, k.isLt⟩ a c hc hne
  obtain ⟨esa, hta, -⟩ := hga
  simp only at hta hsto hrec
  change F.askSlot n b Q J _ a.1.1.store a.1.1.time = F.askSlot n b Q J _ c.1.1.store c.1.1.time ∨
    (F.askSlot n b Q J _ c.1.1.store c.1.1.time = none ∧
      F.askSlot n b Q J _ a.1.1.store a.1.1.time = some (k : ℕ))
  by_cases hk0 : (k : ℕ) = 0
  · simp only [prevSeq, hk0, ↓reduceIte] at hc
    have hnil : es = [] := by
      rw [← hes, hc.2.1]
      unfold MultiRelay.recList
      rcases m with _ | m
      · rfl
      · simp [List.finRange_succ]
    have hc0 : F.askSlot n b Q J (MultiRelay.recList c.1.1.record) c.1.1.store c.1.1.time =
        none := by
      rw [hes, hnil]
      exact MultiRelay.askSlot_nil _ _
    rw [hc0]
    rcases h : F.askSlot n b Q J (MultiRelay.recList a.1.1.record) a.1.1.store a.1.1.time with
      _ | t
    · exact Or.inl rfl
    · have := MultiRelay.askSlot_le h
      exact Or.inr ⟨rfl, by rw [hk0]; congr; omega⟩
  · simp only [prevSeq, hk0, ↓reduceIte] at hc
    obtain ⟨-, htc, -⟩ := hc
    have hta' : (a.1.1.time : ℕ) = ((k : ℕ) - 1) + 1 := by rw [hta]; omega
    rw [hta', htc, hes]
    have := MultiRelay.askSlot_step (F := F) (n := n) (b := b) (Q := Q) (J := J)
      (store := c.1.1.store) (store' := a.1.1.store) (k := (k : ℕ) - 1)
      (by
        rcases hrec with h | ⟨e, h, h'⟩
        · exact Or.inl h
        · exact Or.inr ⟨e, h, by rw [h']; omega⟩)
      hsto
    rw [show (k : ℕ) - 1 + 1 = k by omega] at this ⊢
    exact this

end Distinguisher

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shA : AlgShape X Y Req Resp} {A : AdaptiveIAlg shA O} {G : ℕ → Set (A.W × Req × Option Resp)}
  {G₀ : Set (A.W × Req × Option Resp)} {J : A.W → Option ℕ}

/-- **The slot changes only at its step through the aborting completion**, for trace-preserving
`A`. -/
theorem JSlotStep.toTP (hA : A.TracePreserving) (h : A.JSlotStep G G₀ J) :
    A.abortAlg.JSlotStep (fun n => A.cntSet (G n)) (A.cntSet G₀) (fun w => J w.1) := by
  intro k i a b hb hne
  erw [prevSeq_cntSet] at hb
  rw [abortAlg_step_op] at hne
  obtain ⟨r', hr⟩ := A.tpOp_ne_zero hA (k := k) (i := i) (y := a) (x := b) hne
  exact h k r' (A.cntSplit a).1 (A.cntSplit b).1 hb hr

/-- **The slot changes only at its step at a base part.** -/
theorem JSlotStep.restrictAt {Y₁ Y₂ : Type} [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂]
    [DecidableEq Y₂] [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] (sp : Y ≃+ Y₁ × Y₂) (H₁ : X → Y₁)
    (h : A.JSlotStep G G₀ J) :
    (A.restrictAt sp H₁).JSlotStep (fun n => A.restrictSet sp H₁ (G n)) (A.restrictSet sp H₁ G₀)
      (fun w => J w.1) := by
  intro k i a b hb hne
  rw [prevSeq_restrictSet] at hb
  exact h k i (splitReg sp A.W A.width X Req Resp
    ((basePerm H₁ (A.stepOn k) A.width Req Resp).symm a)) (splitReg sp A.W A.width X Req Resp b)
    hb hne


section RelayAdv

open Classical Distinguisher

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) [AddGroup Y]
  {Req' Resp' O' Xs Ys : Type} [Fintype Req'] [DecidableEq Req'] [Fintype Resp']
  [DecidableEq Resp'] [Inhabited X] [Inhabited Req'] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
  {F : MultiRelay X Y Req Resp Req' Resp' Xs Ys} (Q : ℕ) {J : Req → Bool}
  {Gin : List (Option Req) → Set (((A.toTPKindAlg true).unitOut.DW × Bool) × Req × Option Resp)}

/-- **The slot of `askSlot` changes only at its step in the relayed adversary** of `A`
(`Distinguisher.jSlotStep_relay`, through the aborting completion). -/
theorem jSlotStep_relayAdv (hn : 0 < (A.toTPKindAlg true).unitOut.width)
    (hI : InnerSupp J Gin A.pureD) (out' : A.RelayWS F → O') :
    (A.relayAdv F Q out').JSlotStep
      (fun k => ((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').cntSet
        (GoodAt F (A.budget + A.post) Q J Gin k))
      (((A.relayD F Q).toAdaptive Nat.one_pos (A.relayBudget F Q) out').cntSet (Good₀ F Gin))
      (fun w => F.askSlot (A.toTPKindAlg true).unitOut.width (A.budget + A.post) Q J
        (MultiRelay.recList w.1.record) w.1.store w.1.time) := by
  simp only [AdaptiveIAlg.relayAdv_eq]
  rw [A.relayD_eq F Q]
  exact (jSlotStep_relay (F := F) (b := A.budget + A.post) (Q := Q) J Gin A.pureD hn hI
    (A.relayBudget F Q) out').toTP (toAdaptive_tracePreserving _ _ _ _)

end RelayAdv

end AdaptiveIAlg

end GordieHowe.Quantum
