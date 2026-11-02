-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.MultiRelayRun

@[expose] public section

/-!
# The main requests of the relay's schedule

For the relay of `GordieHowe/Model/Quantum/Pure/MultiRelay.lean`, the sub-slots at which a relayed
request asks a main request, read from a list of started slots' entries and the stored answers,
and their number: at most `K` per relayed request, and at most `Q` relayed requests, so at most
`K · Q` sub-slots ask a main request that the idle request is not.

- `MultiRelay.AsksAt F n b Q es store t r'`: sub-slot `t` lies in the block of a started slot `i`
  that is a relayed request `r`, whose program asks `r'` there on the answers stored in the block
  before `t`.
- `MultiRelay.AsksAt.append`, `MultiRelay.AsksAt.store_congr`: it survives starting a further slot
  and changing the stored answers from `t` on.
- `MultiRelay.asksAt_of_actAt`: the action `actAt` of a sub-slot asking a request other than the
  idle one is such an ask.
- `MultiRelay.na_next`, `MultiRelay.card_isRight_le`: a relayed request asks a main request at most
  `K` times.
- `MultiRelay.card_rel_le`: at most `Q` started slots are relayed requests.
- `MultiRelay.card_asksAt_le` (**the count**): the sub-slots at which a relayed request asks a main
  request satisfying `p` are at most `K · Q`.

The bookkeeping of the relayed distinguisher (`Distinguisher.relay`) across a step, outside the
distinguisher's registers:

- `Distinguisher.askOf`, `Distinguisher.RecAt`, `Distinguisher.Booked`: the main request a
  sub-slot's set-up writes; the record as the list of the slots started by a time; the clock, the
  record and the main request register after the set-up of a sub-slot.
- `Distinguisher.teardownFun_record_time`, `Distinguisher.teardownFun_storeAt`,
  `Distinguisher.teardownFun_req`, `Distinguisher.finalizeFun_parts`,
  `Distinguisher.setupFun_parts`, `Distinguisher.recordFun_recAt`: the pieces of a step.
- `Distinguisher.booked_succ`, `Distinguisher.booked_zero`: the bookkeeping across a step.
- `Distinguisher.rest`, `Distinguisher.ctrlStep_supp`, `Distinguisher.relay_step_supp`: the entry
  form of a step, the distinguisher's own step read only through the rest of the registers it
  keeps.
-/

open Finset

namespace GordieHowe.Quantum

namespace MultiRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)
  [Inhabited X] [Zero Y] [Zero Ys] (n b Q : ℕ)

/-- **Sub-slot `t` of a relayed request asks `r'`**, for the entries `es` of the started slots,
the stored answers `store` and the side store `side`: `t` lies in the block of a started slot `i`
that is a relayed request `r` (`blkAt … = .rel`), and the program's action at `t` on the answers
stored in the block before `t`, its side reads answered from the slot's side vector, is the main
request `r'`. -/
def AsksAt (es : List (Option Req)) {m S : ℕ} (store : Fin S → Option Resp' × (X × Y))
    (side : Fin m → Fin F.qS → Ys) (t : ℕ) (r' : Req') : Prop :=
  ∃ i r, i < es.length ∧ es.getD i none = some r ∧ blkAt b Q es i = .rel ∧
    F.startAt n b Q es i ≤ t ∧ t < F.startAt n b Q es i + F.len ∧
    F.act r (F.stAt (F.vecSa (F.vecAt side i)) r
      (fun k => storeAt store (F.startAt n b Q es i + k)) (t - F.startAt n b Q es i)) = .inr r'

variable {F n b Q}

/-- **An ask survives starting a further slot.** -/
theorem AsksAt.append {es : List (Option Req)} {m S : ℕ}
    {store : Fin S → Option Resp' × (X × Y)} {side : Fin m → Fin F.qS → Ys} {t : ℕ} {r' : Req'}
    (h : F.AsksAt n b Q es store side t r')
    (e : Option Req) : F.AsksAt n b Q (es ++ [e]) store side t r' := by
  obtain ⟨i, r, hi, hr, hb, h1, h2, ha⟩ := h
  have hs : F.startAt n b Q (es ++ [e]) i = F.startAt n b Q es i :=
    F.startAt_append_of_le n b Q e hi.le
  refine ⟨i, r, by simp; omega, ?_, ?_, hs ▸ h1, hs ▸ h2, hs ▸ ha⟩
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]
    exact hr
  · rw [blkAt_append_of_lt b Q e hi]
    exact hb

/-- **An ask at `t` survives changing the stored answers from `t` on.** -/
theorem AsksAt.store_congr {es : List (Option Req)} {m S : ℕ}
    {store store' : Fin S → Option Resp' × (X × Y)} {side : Fin m → Fin F.qS → Ys} {t : ℕ}
    {r' : Req'} (h : F.AsksAt n b Q es store side t r')
    (hs : ∀ u < t, storeAt store' u = storeAt store u) :
    F.AsksAt n b Q es store' side t r' := by
  obtain ⟨i, r, hi, hr, hb, h1, h2, ha⟩ := h
  refine ⟨i, r, hi, hr, hb, h1, h2, ?_⟩
  rw [F.stAt_congr _ r fun k hk => hs (F.startAt n b Q es i + k) (by omega)]
  exact ha

/-- **The action of a sub-slot asking a request other than the idle one is an ask of a relayed
request** of the started slots. -/
theorem asksAt_of_actAt {m S : ℕ} {rec : Fin m → Option (Option Req)}
    {store : Fin S → Option Resp' × (X × Y)} {side : Fin m → Fin F.qS → Ys} {t : ℕ} {r' : Req'}
    (h : F.actAt n b Q rec store side t = .ask r') (hne : r' ≠ F.idle) :
    F.AsksAt n b Q (recList rec) store side t r' := by
  unfold actAt at h
  rcases hc : F.curBlk n b Q rec t with _ | ⟨j, sub⟩
  · rw [hc] at h
    exact absurd (SubAct.ask.inj h).symm hne
  rw [hc] at h
  obtain ⟨-, hst, hsub⟩ := F.curBlk_eq_some hc
  simp only at h
  rcases hbk : blkAt b Q (recList rec) j with _ | _ | _ <;>
    rcases he : (recList rec).getD j none with _ | r <;> simp only [hbk, he] at h
  · split_ifs at h
    exact absurd (SubAct.ask.inj h).symm hne
  · split_ifs at h
    exact absurd (SubAct.ask.inj h).symm hne
  · exact absurd (SubAct.ask.inj h).symm hne
  · exact absurd (SubAct.ask.inj h).symm hne
  · exact absurd (SubAct.ask.inj h).symm hne
  · have hj : j < (recList rec).length := by
      by_contra hj
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at he
      exact absurd he (by simp)
    have hlen : F.blkLen n .rel = F.len := rfl
    rw [hbk, hlen] at hsub
    refine ⟨j, r, hj, he, hbk, by omega, by omega, ?_⟩
    rw [show t - F.startAt n b Q (recList rec) j = sub by omega]
    rcases ha : F.act r (F.stAt (F.vecSa (F.vecAt side j)) r (fun k => storeAt store
      (F.startAt n b Q (recList rec) j + k)) sub) with (x | x) | r''
    · rw [ha] at h
      exact absurd h (by simp)
    · rw [ha] at h
      exact absurd h (by simp)
    · rw [ha] at h
      rw [SubAct.ask.inj h]

omit [Zero Y] [Zero Ys] in
/-- **A sub-slot adds a main request exactly when its action is one.** -/
theorem na_next (r : Req) (st : RelaySt Y Resp' Ys) (a : Option Resp' × (X × Y)) :
    (F.next r st a).na = st.na + if (F.act r st).isRight then 1 else 0 := by
  unfold next act
  rcases hp : F.progAct r st with _ | ((x | x) | r')
  · simp only
    split_ifs with h1 h2 h2 <;> simp_all
  · simp
  · simp only
    split_ifs <;> simp_all
  · simp

omit [Zero Y] [Zero Ys] in
/-- **A relayed request asks a main request at most `K` times** in its first `L` sub-slots, on any
stored answers. -/
theorem card_isRight_le (sa : ℕ → Xs → Ys) (r : Req) (g : ℕ → Option Resp' × (X × Y)) (L : ℕ) :
    ((range L).filter fun s => (F.act r (F.stAt sa r g s)).isRight).card ≤ F.K := by
  have key : ∀ L, ((range L).filter fun s => (F.act r (F.stAt sa r g s)).isRight).card =
      (F.stAt sa r g L).na := by
    intro L
    induction L with
    | zero => rfl
    | succ L ih =>
      rw [range_add_one, filter_insert, stAt, F.na_close, na_next]
      split_ifs with h
      · rw [card_insert_of_notMem (by simp), ih]
      · rw [ih, add_zero]
  have hle : ∀ L, (F.stAt sa r g L).na ≤ F.K := by
    intro L
    induction L with
    | zero => exact Nat.zero_le _
    | succ L ih =>
      rw [stAt, F.na_close]
      exact F.na_next_le r _ _ ih
  rw [key]
  exact hle L

omit [Inhabited X] [Zero Y] [Zero Ys] in
/-- **At most `Q` started slots are relayed requests**: a relayed request is numbered below `Q` by
the requests before it. -/
theorem card_rel_le (es : List (Option Req)) :
    ((range es.length).filter fun i => blkAt b Q es i = .rel).card ≤ Q := by
  classical
  have hrel : ∀ i, blkAt b Q es i = .rel →
      (es.getD i none).isSome ∧ (es.take i).countP Option.isSome < Q := by
    intro i h
    unfold blkAt at h
    rcases he : es.getD i none with _ | r
    · rw [he] at h
      simp only [blk] at h
      split_ifs at h
    · rw [he] at h
      simp only [blk] at h
      split_ifs at h with h'
      exact ⟨rfl, h'⟩
  refine (card_le_card_of_injOn (fun i => (es.take i).countP Option.isSome) (fun i hi => ?_)
    (fun i hi i' hi' he => ?_)).trans (card_range Q).le
  · simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hi
    exact mem_range.2 (hrel i hi.2).2
  · simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hi hi'
    have hsome : ∀ j, j < es.length → (es.getD j none).isSome →
        ∀ j', j < j' → (es.take j).countP Option.isSome < (es.take j').countP Option.isSome := by
      intro j hj hs j' hjj'
      have hsplit : es.take j' = es.take j ++ (es.drop j).take (j' - j) := by
        rw [← List.take_add, Nat.add_sub_cancel' hjj'.le]
      obtain ⟨d, hdj⟩ : ∃ d, j' - j = d + 1 := ⟨j' - j - 1, by omega⟩
      have hd : (es.drop j).take (j' - j) = es[j] :: (es.drop (j + 1)).take d := by
        rw [List.drop_eq_getElem_cons hj, hdj, List.take_succ_cons]
      have hsj : es[j].isSome := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] at hs
        simpa using hs
      rw [hsplit, hd, List.countP_append, List.countP_cons_of_pos hsj]
      omega
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact absurd he (Nat.ne_of_lt (hsome i hi.1 (hrel i hi.2).1 i' h))
    · exact absurd he.symm (Nat.ne_of_lt (hsome i' hi'.1 (hrel i' hi'.2).1 i h))

open Classical in
/-- **The count** (module docstring): the sub-slots at which a relayed request of the started
slots `es` asks a main request satisfying `p` are at most `K · Q`. -/
theorem card_asksAt_le (es : List (Option Req)) {m S : ℕ}
    (store : Fin S → Option Resp' × (X × Y)) (side : Fin m → Fin F.qS → Ys) (p : Req' → Bool) :
    (univ.filter fun t : Fin S => ∃ r', F.AsksAt n b Q es store side t r' ∧ p r' = true).card ≤
      F.K * Q := by
  classical
  set g : ℕ → ℕ → Option Resp' × (X × Y) := fun i k => storeAt store (F.startAt n b Q es i + k)
  set gs : ℕ → ℕ → Xs → Ys := fun i => F.vecSa (F.vecAt side i)
  set W : Finset (ℕ × ℕ) := ((range es.length).filter fun i => blkAt b Q es i = .rel).biUnion
    fun i => ((range F.len).filter fun s =>
      ((es.getD i none).elim false fun r => (F.act r (F.stAt (gs i) r (g i) s)).isRight)
      ).map ⟨fun s => (i, s), fun _ _ h => (Prod.mk.inj h).2⟩
  have hW : W.card ≤ F.K * Q := by
    refine (card_biUnion_le).trans ?_
    calc _ ≤ ∑ _i ∈ (range es.length).filter (fun i => blkAt b Q es i = .rel), F.K :=
          sum_le_sum fun i _ => by
            rw [card_map]
            rcases es.getD i none with _ | r
            · simp
            · exact F.card_isRight_le _ r _ _
      _ = ((range es.length).filter fun i => blkAt b Q es i = .rel).card * F.K := by
          rw [sum_const, smul_eq_mul]
      _ ≤ Q * F.K := Nat.mul_le_mul_right _ (card_rel_le es)
      _ = F.K * Q := Nat.mul_comm _ _
  refine le_trans ?_ hW
  set P : ℕ → ℕ → Prop := fun t i => i < es.length ∧ blkAt b Q es i = .rel ∧
    F.startAt n b Q es i ≤ t ∧ t - F.startAt n b Q es i < F.len ∧
    ((es.getD i none).elim false fun r =>
      (F.act r (F.stAt (gs i) r (g i) (t - F.startAt n b Q es i))).isRight) = true with hP
  have hch : ∀ t : Fin S, (∃ r', F.AsksAt n b Q es store side t r' ∧ p r' = true) →
      ∃ i, P t i := by
    rintro t ⟨r', ⟨i, r, hi, hr, hb, h1, h2, ha⟩, -⟩
    refine ⟨i, hi, hb, h1, by omega, ?_⟩
    rw [hr]
    change (F.act r (F.stAt (F.vecSa (F.vecAt side i)) r
      (fun k => storeAt store (F.startAt n b Q es i + k)) _)).isRight = true
    rw [ha]
    rfl
  set f : Fin S → ℕ × ℕ := fun t => if h : ∃ i, P t i then
    (Classical.choose h, (t : ℕ) - F.startAt n b Q es (Classical.choose h)) else (0, 0) with hf
  refine card_le_card_of_injOn f (fun t ht => ?_) (fun t ht t' ht' he => ?_)
  · have hx := hch t (mem_filter.1 ht).2
    have hs := Classical.choose_spec hx
    obtain ⟨hi, hb, -, hl, ha⟩ := hs
    simp only [hf, dif_pos hx]
    refine mem_biUnion.2 ⟨_, mem_filter.2 ⟨mem_range.2 hi, hb⟩, mem_map.2 ⟨_, ?_, rfl⟩⟩
    exact mem_filter.2 ⟨mem_range.2 hl, ha⟩
  · have hx := hch t (mem_filter.1 ht).2
    have hx' := hch t' (mem_filter.1 ht').2
    have h1 := (Classical.choose_spec hx).2.2.1
    have h1' := (Classical.choose_spec hx').2.2.1
    simp only [hf, dif_pos hx, dif_pos hx'] at he
    obtain ⟨he1, he2⟩ := Prod.mk.inj he
    rw [he1] at he2 h1
    exact Fin.ext (by omega)

end MultiRelay

namespace MultiRelay

section Mono

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)
  [Inhabited X]

/-- **The side reads made only grow along the sub-slots.** -/
theorem ns_stAt_mono (sa : ℕ → Xs → Ys) (r : Req) (g : ℕ → Option Resp' × (X × Y)) {i i' : ℕ}
    (h : i ≤ i') : (F.stAt sa r g i).ns ≤ (F.stAt sa r g i').ns := by
  induction i', h using Nat.le_induction with
  | base => exact le_rfl
  | succ i' _ ih =>
    refine ih.trans ?_
    have := F.ns_le_iterate_sideStep sa r F.qS (F.next r (F.stAt sa r g i') (g i'))
    rw [F.ns_next] at this
    exact this

/-- **The relayed request at the clock after a sub-slot**, unfolded: the last started slot, its
request, and the sub-slots of its block done. -/
theorem curRel_eq_some {n b Q m : ℕ} {rec : Fin m → Option (Option Req)} {t j : ℕ} {r : Req}
    {sub : ℕ} (h : F.curRel n b Q rec t = some (j, r, sub)) :
    j = (recList rec).length - 1 ∧ (recList rec).getD j none = some r ∧
      sub = t - F.startAt n b Q (recList rec) j ∧ F.startAt n b Q (recList rec) j < t ∧
      t ≤ F.startAt n b Q (recList rec) j + F.len := by
  unfold curRel at h
  by_cases h0 : 0 < (recList rec).length
  · rw [if_pos h0] at h
    split at h
    · rename_i r₁ hb he
      by_cases h1 : F.startAt n b Q (recList rec) ((recList rec).length - 1) < t ∧
          t ≤ F.startAt n b Q (recList rec) ((recList rec).length - 1) + F.len
      · rw [if_pos h1] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, he, rfl, h1.1, h1.2⟩
      · rw [if_neg h1] at h
        cases h
    · cases h
  · rw [if_neg h0] at h
    cases h

variable [AddGroup Ys]

/-- **The side additions keep the entries below the side reads before them.** -/
theorem addsVec_agree (r : Req) (g : ℕ → Option Resp' × (X × Y)) (sub : ℕ) (v : Fin F.qS → Ys)
    (k : Fin F.qS) (hk : (k : ℕ) < (F.preSt (F.vecSa v) r g sub).ns) :
    F.addsVec r g sub v k = v k := by
  set N := (F.preSt (F.vecSa v) r g sub).ns
  have key : ∀ (L : List ℕ) (v' : Fin F.qS → Ys), (∀ k' : Fin F.qS, (k' : ℕ) < N → v' k' = v k') →
      ∀ k' : Fin F.qS, (k' : ℕ) < N →
        L.foldl (fun v i => F.addVec r g sub i true v) v' k' = v k' := by
    intro L
    induction L with
    | nil => intro v' hv' k' hk'; exact hv' k' hk'
    | cons i L ih =>
      intro v' hv'
      refine ih _ fun k' hk' => ?_
      have hpre : F.preSt (F.vecSa v') r g sub = F.preSt (F.vecSa v) r g sub :=
        F.preSt_congr_sa (N := N) (fun j hj x => by
          unfold vecSa
          split_ifs with hjq
          · exact hv' ⟨j, hjq⟩ hj
          · rfl) r g sub le_rfl
      show F.addVec r g sub i true v' k' = v k'
      unfold addVec
      rcases hp : F.progAct r (F.pendSt (F.vecSa v') r g sub i) with _ | ((x | x) | r')
      · exact hv' k' hk'
      · exact hv' k' hk'
      · simp only
        by_cases hq : (F.pendSt (F.vecSa v') r g sub i).ns < F.qS
        · have hge : N ≤ (F.pendSt (F.vecSa v') r g sub i).ns := by
            unfold pendSt
            rw [hpre]
            exact F.ns_le_iterate_sideStep _ r i _
          rw [dif_pos hq, Function.update_of_ne (fun e => by
            have := congrArg Fin.val e
            simp only at this
            omega)]
          exact hv' k' hk'
        · rw [dif_neg hq]
          exact hv' k' hk'
      · exact hv' k' hk'
  exact key _ v (fun _ _ => rfl) k hk

end Mono

end MultiRelay

/-! ### The relay's bookkeeping across a step -/

namespace Distinguisher

variable {W X Y Req Resp Req' Resp' Xs Ys : Type} [DecidableEq X] [DecidableEq Req']
  [DecidableEq Req] [DecidableEq Resp] [Inhabited X] [Inhabited Req'] [AddGroup Y] [AddGroup Ys]
  {n m : ℕ} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (b Q : ℕ)

local notation "RR" => RelayReg W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)

/-- **The main request a sub-slot's action leaves in the main request register** after its set-up:
`r'` for the main request `r'`, the blank `default` otherwise. -/
def askOf : SubAct X Req' n → Req'
  | .ask r' => r'
  | _ => default

/-- **The record is the list `es` of the started slots' entries, each started by `t`.** -/
def RecAt (rec : Fin m → Option (Option Req)) (es : List (Option Req)) (t : ℕ) : Prop :=
  es.length ≤ m ∧ rec = (fun i : Fin m => es[(i : ℕ)]?) ∧ ∀ i < es.length, F.startAt n b Q es i ≤ t

/-- **The relay's bookkeeping after the set-up of sub-slot `t`**: the clock at `t`, the record the
list `es` of slots started by `t`, and the main request register holding the main request of
sub-slot `t`'s action (`askOf`). -/
def Booked (t : ℕ) (es : List (Option Req)) (d : RR) : Prop :=
  (d.1.1.time : ℕ) = t ∧ RecAt (n := n) F b Q d.1.1.record es t ∧
    d.1.2.1 = askOf (F.actAt n b Q d.1.1.record d.1.1.store d.1.1.side d.1.1.time)

omit [DecidableEq X] [DecidableEq Req] [DecidableEq Resp] in
/-- The tear-down keeps the record, the side store and the clock. -/
theorem teardownFun_record_time (d : RR) :
    (teardownFun F b Q d).1.1.record = d.1.1.record ∧
      (teardownFun F b Q d).1.1.side = d.1.1.side ∧
      (teardownFun F b Q d).1.1.time = d.1.1.time := by
  unfold teardownFun
  rcases F.actAt n b Q d.1.1.record d.1.1.store d.1.1.side d.1.1.time with i | x | r'
  · exact ⟨rfl, rfl, rfl⟩
  · dsimp only
    split_ifs <;> exact ⟨rfl, rfl, rfl⟩
  · dsimp only
    split_ifs <;> exact ⟨rfl, rfl, rfl⟩

omit [DecidableEq X] [DecidableEq Req] [DecidableEq Resp] in
/-- The tear-down changes the stored answers at the clock only. -/
theorem teardownFun_storeAt (d : RR) {u : ℕ} (hu : u ≠ d.1.1.time) :
    MultiRelay.storeAt (teardownFun F b Q d).1.1.store u = MultiRelay.storeAt d.1.1.store u := by
  have key : ∀ (h : (d.1.1.time : ℕ) < relaySlots n m F) (v : Option Resp' × (X × Y)),
      MultiRelay.storeAt (Function.update d.1.1.store ⟨d.1.1.time, h⟩ v) u =
        MultiRelay.storeAt d.1.1.store u := by
    intro h v
    unfold MultiRelay.storeAt
    split_ifs with h'
    · rw [Function.update_of_ne (fun e => hu (by simpa [Fin.ext_iff] using congrArg Fin.val e))]
    · rfl
  unfold teardownFun
  rcases F.actAt n b Q d.1.1.record d.1.1.store d.1.1.side d.1.1.time with i | x | r'
  · rfl
  · dsimp only
    split_ifs with h
    · exact key h _
    · rfl
  · dsimp only
    split_ifs with h
    · exact key h _
    · rfl

omit [DecidableEq X] [DecidableEq Req'] [DecidableEq Req] [Inhabited Req'] in
/-- The reply of a finished relayed request keeps the side store. -/
theorem finalizeFun_side (d : RR) : (finalizeFun F b Q d).1.1.side = d.1.1.side := by
  unfold finalizeFun
  split_ifs
  · rcases F.lastReply n b Q d.1.1.record d.1.1.store d.1.1.side with _ | o <;> rfl
  · rfl

omit [DecidableEq X] [DecidableEq Req] [DecidableEq Resp] in
/-- **The tear-down blanks the main request register** that the set-up filled. -/
theorem teardownFun_req (d : RR)
    (h : d.1.2.1 = askOf (F.actAt n b Q d.1.1.record d.1.1.store d.1.1.side d.1.1.time)) :
    (teardownFun F b Q d).1.2.1 = default := by
  unfold teardownFun
  rcases hA : F.actAt n b Q d.1.1.record d.1.1.store d.1.1.side d.1.1.time with i | x | r'
  · rw [hA] at h
    exact h
  · rw [hA] at h
    dsimp only
    split_ifs <;> exact h
  · rw [hA] at h
    dsimp only
    split_ifs
    · change Equiv.swap default r' d.1.2.1 = default
      rw [h]
      exact Equiv.swap_apply_right _ _
    · change Equiv.swap default r' d.1.2.1 = default
      rw [h]
      exact Equiv.swap_apply_right _ _

omit [DecidableEq X] [DecidableEq Req'] [DecidableEq Req] [Inhabited Req'] in
/-- The reply of a finished relayed request keeps the record, the stored answers, the clock and the
main request register. -/
theorem finalizeFun_parts (d : RR) :
    (finalizeFun F b Q d).1.1.record = d.1.1.record ∧
      (finalizeFun F b Q d).1.1.store = d.1.1.store ∧
      (finalizeFun F b Q d).1.1.time = d.1.1.time ∧ (finalizeFun F b Q d).1.2.1 = d.1.2.1 := by
  unfold finalizeFun
  split_ifs
  · rcases F.lastReply n b Q d.1.1.record d.1.1.store d.1.1.side with _ | o
    · exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

omit [DecidableEq Req] [DecidableEq Resp] in
/-- **The set-up keeps the record, the stored answers and the clock, and fills the blank main
request register with the main request of the sub-slot's action.** -/
theorem setupFun_parts (d : RR) (h : d.1.2.1 = default) :
    (setupFun F b Q d).1.1.record = d.1.1.record ∧ (setupFun F b Q d).1.1.store = d.1.1.store ∧
      (setupFun F b Q d).1.1.time = d.1.1.time ∧
      (setupFun F b Q d).1.2.1 =
        askOf (F.actAt n b Q d.1.1.record d.1.1.store d.1.1.side d.1.1.time) := by
  unfold setupFun
  rcases hA : F.actAt n b Q d.1.1.record d.1.1.store d.1.1.side d.1.1.time with i | x | r'
  · exact ⟨rfl, rfl, rfl, h⟩
  · exact ⟨rfl, rfl, rfl, h⟩
  · refine ⟨rfl, rfl, rfl, ?_⟩
    change Equiv.swap default r' d.1.2.1 = r'
    rw [h]
    exact Equiv.swap_apply_left _ _

omit [DecidableEq Req] [DecidableEq Resp] in
/-- The set-up keeps the side store. -/
theorem setupFun_side (d : RR) : (setupFun F b Q d).1.1.side = d.1.1.side := by
  unfold setupFun
  split <;> rfl

omit [DecidableEq X] [DecidableEq Req'] [DecidableEq Resp] [Inhabited X] [Inhabited Req']
  [AddGroup Y] in
/-- The record keeps the side store. -/
theorem recordFun_side (kind : W → Bool) (d : RR) :
    (recordFun F b Q kind d).1.1.side = d.1.1.side := by
  unfold recordFun
  split <;> rfl

omit [DecidableEq X] [DecidableEq Req'] [DecidableEq Resp] [Inhabited X] [Inhabited Req']
  [AddGroup Y] in
/-- **The record of the starting slot**: on a record of the slots started before the clock `t`
(each started before `t`), the record afterwards is that list or the list with one more entry, each
of its slots started by `t`; the stored answers, the clock and the main request register are
kept. -/
theorem recordFun_recAt (hn : 0 < n) (kind : W → Bool) (d : RR) {es : List (Option Req)}
    (hl : es.length ≤ m) (hr : d.1.1.record = fun i : Fin m => es[(i : ℕ)]?)
    (hs : ∀ i < es.length, F.startAt n b Q es i < d.1.1.time) :
    ∃ es', (es' = es ∨ ∃ e, es' = es ++ [e]) ∧
      RecAt (n := n) F b Q (recordFun F b Q kind d).1.1.record es' d.1.1.time ∧
      (recordFun F b Q kind d).1.1.store = d.1.1.store ∧
      (recordFun F b Q kind d).1.1.time = d.1.1.time ∧
      (recordFun F b Q kind d).1.2.1 = d.1.2.1 := by
  by_cases hf : F.startAt n b Q es es.length = d.1.1.time ∧ es.length < m
  · have hfill := F.fillAt_ofList_eq_some n b Q hn hf.2 hf.1
    refine ⟨es ++ [entryOf kind d.1.1.inner], Or.inr ⟨_, rfl⟩, ⟨by simp; omega, ?_, fun i hi => ?_⟩,
      ?_, ?_, ?_⟩
    · simp only [recordFun, hr, hfill]
      funext i
      by_cases hi : (i : ℕ) = es.length
      · have : i = ⟨es.length, hf.2⟩ := Fin.ext hi
        subst this
        simp
      · rw [Function.update_of_ne (fun e => hi (by rw [e]))]
        rcases Nat.lt_or_gt_of_ne hi with h | h
        · rw [List.getElem?_append_left h]
        · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
    · simp only [List.length_append, List.length_singleton] at hi
      rw [F.startAt_append_of_le n b Q _ (by omega)]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact (hs i h).le
      · rw [h, hf.1]
    · simp only [recordFun, hr, hfill]
    · simp only [recordFun, hr, hfill]
    · simp only [recordFun, hr, hfill]
  · have hnone : F.fillAt n b Q (fun i : Fin m => es[(i : ℕ)]?) d.1.1.time = none := by
      refine F.fillAt_ofList_eq_none n b Q hl fun i hi him he => ?_
      rcases Nat.lt_or_eq_of_le hi with h | h
      · exact absurd he (Nat.ne_of_lt (hs i h))
      · exact hf ⟨h ▸ he, h ▸ him⟩
    have hd : recordFun F b Q kind d = d := by
      simp only [recordFun, hr, hnone]
    rw [hd]
    exact ⟨es, Or.inl rfl, ⟨hl, hr, fun i hi => (hs i hi).le⟩, rfl, rfl, rfl⟩

/-- **The side additions keep the bookkeeping outside the side store**: the record, the stored
answers, the clock and the main request register. -/
theorem sideAddsPerm_parts (d : RR) :
    (sideAddsPerm F b Q d).1.1.record = d.1.1.record ∧
      (sideAddsPerm F b Q d).1.1.store = d.1.1.store ∧
      (sideAddsPerm F b Q d).1.1.time = d.1.1.time ∧
      (sideAddsPerm F b Q d).1.2.1 = d.1.2.1 := by
  rw [sideAddsPerm, foldl_sideAddPerm_apply, Equiv.refl_apply, foldl_sideAddFun]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **The side additions change a slot's side vector only at or past the side reads before
them**: off the relayed request at the clock, the side vectors are kept. -/
theorem sideAddsPerm_side (d : RR) (i : Fin m) (k : Fin F.qS)
    (h : ∀ r sub, F.curRel n b Q d.1.1.record d.1.1.time = some ((i : ℕ), r, sub) →
      (k : ℕ) < (F.preSt (F.vecSa (d.1.1.side i)) r (fun k' => MultiRelay.storeAt d.1.1.store
        (F.startAt n b Q (MultiRelay.recList d.1.1.record) i + k')) sub).ns) :
    (sideAddsPerm F b Q d).1.1.side i k = d.1.1.side i k := by
  rw [sideAddsPerm, foldl_sideAddPerm_apply, Equiv.refl_apply, foldl_sideAddFun]
  rcases hc : F.curRel n b Q d.1.1.record d.1.1.time with _ | ⟨j, r, sub⟩
  · rfl
  · by_cases hj : j < m
    · simp only [hj, ↓reduceDIte]
      by_cases hij : i = ⟨j, hj⟩
      · subst hij
        rw [Function.update_self]
        exact F.addsVec_agree r _ sub _ k (h r sub hc)
      · rw [Function.update_of_ne hij]
    · simp only [hj, ↓reduceDIte]

/-- The rest of the relay's registers: the record, the stored answers, the side store, the clock,
the main request and response registers and the query pair. -/
abbrev rest (d : RR) : RelayRest X Y Req Req' Resp' m (relaySlots n m F) (Fin F.qS → Ys) :=
  (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys) d).2

/-- **The bookkeeping across step `t + 1`** (module docstring): from the bookkeeping after the
set-up of sub-slot `t < S` with the started slots `es`, a state agreeing outside the
distinguisher's registers with the tear-down, the clock, the side additions and the reply (`z`),
recorded and set up, has the bookkeeping after the set-up of sub-slot `t + 1` with `es` or `es`
and one more entry; the stored answers before `t` are kept, and so is every ask of the started
slots at a sub-slot up to `t`. -/
theorem booked_succ (hn : 0 < n) (kind : W → Bool) {t : ℕ} (ht : t < relaySlots n m F)
    {es : List (Option Req)} {q z : RR} (hq : Booked F b Q t es q)
    (hz : rest F z = rest F (finalizeFun F b Q (sideAddsPerm F b Q
      (tickPerm F (teardownFun F b Q q))))) :
    ∃ es', (es' = es ∨ ∃ e, es' = es ++ [e]) ∧
      Booked F b Q (t + 1) es' (setupFun F b Q (recordFun F b Q kind z)) ∧
      (∀ u < t, MultiRelay.storeAt (setupFun F b Q (recordFun F b Q kind z)).1.1.store u =
        MultiRelay.storeAt q.1.1.store u) ∧
      ∀ u ≤ t, ∀ r', F.AsksAt n b Q es q.1.1.store q.1.1.side u r' →
        F.AsksAt n b Q es (setupFun F b Q (recordFun F b Q kind z)).1.1.store
          (setupFun F b Q (recordFun F b Q kind z)).1.1.side u r' := by
  obtain ⟨hqt, ⟨hl, hr, hs⟩, hreq⟩ := hq
  obtain ⟨hrt1, hrtS, hrt2⟩ := teardownFun_record_time F b Q q
  set y := sideAddsPerm F b Q (tickPerm F (teardownFun F b Q q)) with hy
  obtain ⟨ha1, ha2, ha3, ha4⟩ := sideAddsPerm_parts F b Q (tickPerm F (teardownFun F b Q q))
  obtain ⟨hf1, hf2, hf3, hf4⟩ := finalizeFun_parts F b Q y
  have hz1 : z.1.1.record = q.1.1.record := by
    rw [show z.1.1.record = (rest F z).1 from rfl, hz]
    exact hf1.trans (ha1.trans hrt1)
  have hz2 : z.1.1.store = (teardownFun F b Q q).1.1.store := by
    rw [show z.1.1.store = (rest F z).2.1 from rfl, hz]
    exact hf2.trans ha2
  have hyt : (y.1.1.time : ℕ) = t + 1 := by
    rw [ha3]
    change (finRotate _ (teardownFun F b Q q).1.1.time : ℕ) = t + 1
    rw [hrt2, coe_finRotate_of_ne_last (fun h => by
      have := congrArg Fin.val h
      simp only [Fin.val_last] at this
      omega), hqt]
  have hz3 : (z.1.1.time : ℕ) = t + 1 := by
    rw [show z.1.1.time = (rest F z).2.2.2.1 from rfl, hz]
    change ((finalizeFun F b Q y).1.1.time : ℕ) = t + 1
    rw [hf3, hyt]
  have hz4 : z.1.2.1 = default := by
    rw [show z.1.2.1 = (rest F z).2.2.2.2.1 from rfl, hz]
    exact hf4.trans (ha4.trans (teardownFun_req F b Q q hreq))
  have hz5 : z.1.1.side = y.1.1.side := by
    rw [show z.1.1.side = (rest F z).2.2.1 from rfl, hz]
    exact finalizeFun_side F b Q _
  obtain ⟨es', hes', hrec, hst, htm, hrq⟩ := recordFun_recAt F b Q hn kind z hl (hz1.trans hr)
    fun i hi => by rw [hz3]; exact Nat.lt_succ_of_le (hqt ▸ hs i hi)
  obtain ⟨hs1, hs2, hs3, hs4⟩ := setupFun_parts F b Q (recordFun F b Q kind z) (hrq.trans hz4)
  have hB : Booked F b Q (t + 1) es' (setupFun F b Q (recordFun F b Q kind z)) := by
    refine ⟨by rw [hs3, htm, hz3], ?_, by rw [hs4, hs1, hs2, setupFun_side, hs3]⟩
    rw [hs1]
    exact hz3 ▸ htm ▸ hrec
  have hstore : ∀ u < t + 1, u ≠ t → MultiRelay.storeAt
      (setupFun F b Q (recordFun F b Q kind z)).1.1.store u = MultiRelay.storeAt q.1.1.store u :=
    fun u _ hu => by
      rw [hs2, hst, hz2]
      exact teardownFun_storeAt F b Q q (by rw [hqt]; exact hu)
  refine ⟨es', hes', hB, fun u hu => hstore u (by omega) (by omega), fun u hu r' hA => ?_⟩
  -- the ask: the stored answers before `u` and the side reads before it are kept
  have hside : (setupFun F b Q (recordFun F b Q kind z)).1.1.side = y.1.1.side := by
    rw [setupFun_side, recordFun_side, hz5]
  obtain ⟨i, r, hi, hgi, hb, h1, h2, ha⟩ := hA
  refine ⟨i, r, hi, hgi, hb, h1, h2, ?_⟩
  have hu' : u - F.startAt n b Q es i < F.len := by omega
  -- the side vector of slot `i` is kept below the side reads up to `u`
  have him : i < m := lt_of_lt_of_le hi hl
  have hvec : ∀ k : Fin F.qS, (k : ℕ) < (F.stAt (F.vecSa (F.vecAt q.1.1.side i)) r
      (fun k' => MultiRelay.storeAt q.1.1.store (F.startAt n b Q es i + k'))
      (u - F.startAt n b Q es i)).ns →
      y.1.1.side ⟨i, him⟩ k = q.1.1.side ⟨i, him⟩ k := by
    intro k hk
    have hyside : (tickPerm F (teardownFun F b Q q)).1.1.side = q.1.1.side := hrtS
    rw [← hyside]
    refine sideAddsPerm_side F b Q _ ⟨i, him⟩ k fun r₀ sub hc => ?_
    -- the relayed request at the clock is slot `i`'s
    have hc' : F.curRel n b Q q.1.1.record (t + 1) = some (i, r₀, sub) := by
      have h0 : ((tickPerm F (teardownFun F b Q q)).1.1.time : ℕ) = t + 1 := by
        rw [← ha3]; exact hyt
      rw [show (tickPerm F (teardownFun F b Q q)).1.1.record = q.1.1.record from hrt1,
        h0] at hc
      exact hc
    have hrl : MultiRelay.recList q.1.1.record = es := by
      rw [hr]
      exact MultiRelay.recList_getElem? es hl
    obtain ⟨-, he, hsub, -, -⟩ := F.curRel_eq_some hc'
    rw [hrl] at he hsub
    have hrr : r₀ = r := by
      rw [he] at hgi
      exact Option.some.inj hgi
    subst hrr
    have hrl' : MultiRelay.recList (tickPerm F (teardownFun F b Q q)).1.1.record = es := by
      rw [show (tickPerm F (teardownFun F b Q q)).1.1.record = q.1.1.record from hrt1, hrl]
    rw [hrl', hsub]
    -- the side reads up to `u` are at most those before the additions
    have hvq : F.vecAt q.1.1.side i = q.1.1.side ⟨i, him⟩ := by
      simp [MultiRelay.vecAt, him]
    rw [hvq] at hk
    have hstk : F.stAt (F.vecSa (q.1.1.side ⟨i, him⟩)) r₀
        (fun k' => MultiRelay.storeAt q.1.1.store (F.startAt n b Q es i + k'))
        (u - F.startAt n b Q es i) =
        F.stAt (F.vecSa (q.1.1.side ⟨i, him⟩)) r₀
        (fun k' => MultiRelay.storeAt (tickPerm F (teardownFun F b Q q)).1.1.store
          (F.startAt n b Q es i + k')) (u - F.startAt n b Q es i) := by
      refine F.stAt_congr _ r₀ fun k' hk' => ?_
      change _ = MultiRelay.storeAt (teardownFun F b Q q).1.1.store _
      rw [teardownFun_storeAt F b Q q (by rw [hqt]; omega)]
    have hmono := F.ns_stAt_mono (F.vecSa (q.1.1.side ⟨i, him⟩)) r₀
      (fun k' => MultiRelay.storeAt (tickPerm F (teardownFun F b Q q)).1.1.store
        (F.startAt n b Q es i + k')) (show u - F.startAt n b Q es i ≤ t - F.startAt n b Q es i
        by omega)
    have hpre : (F.preSt (F.vecSa (q.1.1.side ⟨i, him⟩)) r₀
        (fun k' => MultiRelay.storeAt (tickPerm F (teardownFun F b Q q)).1.1.store
          (F.startAt n b Q es i + k')) (t + 1 - F.startAt n b Q es i)).ns =
        (F.stAt (F.vecSa (q.1.1.side ⟨i, him⟩)) r₀
        (fun k' => MultiRelay.storeAt (tickPerm F (teardownFun F b Q q)).1.1.store
          (F.startAt n b Q es i + k')) (t - F.startAt n b Q es i)).ns := by
      rw [show t + 1 - F.startAt n b Q es i = (t - F.startAt n b Q es i) + 1 by omega]
      exact F.ns_next _ _ _
    have hside0 : (tickPerm F (teardownFun F b Q q)).1.1.side = q.1.1.side := hrtS
    rw [hside0]
    simp only [Fin.val_mk]
    rw [hpre]
    rw [hstk] at hk
    omega
  -- the stored answers of the block before `u` are kept
  rw [F.stAt_congr _ r (g' := fun k' => MultiRelay.storeAt q.1.1.store (F.startAt n b Q es i + k'))
    fun k' hk' => hstore _ (by omega) (by omega)]
  -- the side answers read up to `u` are kept
  rw [F.stAt_congr_sa (sa := F.vecSa (F.vecAt q.1.1.side i))
    (N := (F.stAt (F.vecSa (F.vecAt q.1.1.side i)) r
      (fun k' => MultiRelay.storeAt q.1.1.store (F.startAt n b Q es i + k'))
      (u - F.startAt n b Q es i)).ns) (fun k hk x => ?_) r _ _ le_rfl]
  · exact ha
  · unfold MultiRelay.vecSa
    split_ifs with hkq
    · simp only [MultiRelay.vecAt, him, ↓reduceDIte, hside]
      exact hvec ⟨k, hkq⟩ hk
    · rfl

omit [DecidableEq Resp] in
/-- **The bookkeeping across step `0`**: from a blank record at the clock `0` with a blank main
request register, a state agreeing outside the distinguisher's registers, recorded and set up, has
the bookkeeping after the set-up of sub-slot `0`. -/
theorem booked_zero (hn : 0 < n) (kind : W → Bool) {q z : RR} (hqt : (q.1.1.time : ℕ) = 0)
    (hqr : q.1.1.record = fun _ => none) (hqq : q.1.2.1 = default) (hz : rest F z = rest F q) :
    ∃ es', Booked F b Q 0 es' (setupFun F b Q (recordFun F b Q kind z)) := by
  have hz1 : z.1.1.record = fun i : Fin m => ([] : List (Option Req))[(i : ℕ)]? := by
    rw [show z.1.1.record = (rest F z).1 from rfl, hz]
    exact hqr
  have hz3 : (z.1.1.time : ℕ) = 0 := by
    rw [show z.1.1.time = (rest F z).2.2.2.1 from rfl, hz]
    exact hqt
  have hz4 : z.1.2.1 = default := by
    rw [show z.1.2.1 = (rest F z).2.2.2.2.1 from rfl, hz]
    exact hqq
  obtain ⟨es', -, hrec, -, htm, hrq⟩ := recordFun_recAt F b Q hn kind z (Nat.zero_le _) hz1
    fun i hi => absurd hi (Nat.not_lt_zero _)
  obtain ⟨hs1, hs2, hs3, hs4⟩ := setupFun_parts F b Q (recordFun F b Q kind z) (hrq.trans hz4)
  refine ⟨es', by rw [hs3, htm, hz3], ?_, by rw [hs4, hs1, hs2, setupFun_side, hs3]⟩
  rw [hs1]
  exact hz3 ▸ htm ▸ hrec

variable [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req]
  [Fintype Resp] [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] [Fintype Ys] [DecidableEq Ys]

omit [Inhabited X] [Inhabited Req'] [AddGroup Y] [DecidableEq X] [DecidableEq Req']
  [DecidableEq Req] [DecidableEq Resp] [DecidableEq W] [DecidableEq Y] [DecidableEq Resp'] in
/-- **The control of the distinguisher's step keeps the rest of the registers**: the step at the
start of a slot applied to a vector supported on one basis state is supported on the registers with
the same rest. -/
theorem ctrlStep_supp (D : Distinguisher W X Y Req Resp n m) {q : RR} {v : QState RR}
    (hv : Supported {q} v) : Supported {p | rest F p = rest F q} (D.ctrlStep F b Q v) := by
  intro p hp
  change (relabel (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F)
    (Fin F.qS → Ys))).symm (controlled _ (relabel (relaySplit W X Y Req Resp Req' Resp' n m
      (relaySlots n m F) (Fin F.qS → Ys)) v)) p = 0
  rw [relabel_symm, relabel_apply, Equiv.symm_symm]
  change controlled _ _ ((relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F)
    (Fin F.qS → Ys) p).1, (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F)
      (Fin F.qS → Ys) p).2) = 0
  rw [controlled_apply]
  have h0 : (WithLp.toLp 2 fun i' => relabel (relaySplit W X Y Req Resp Req' Resp' n m
      (relaySlots n m F) (Fin F.qS → Ys)) v
        (i', (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)
          p).2) : QState (DReg W n X Y Req Resp)) = 0 := by
    ext i'
    rw [relabel_apply]
    refine hv _ fun he => hp ?_
    have := congrArg (fun d => (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F)
      (Fin F.qS → Ys) d).2) he
    simp only [Equiv.apply_symm_apply] at this
    exact this
  rw [h0, map_zero]
  rfl

/-- **The supports of a step of the relayed distinguisher** (the entry form): on a vector supported
on the basis state `q`, the step is supported on the states set up and recorded from a state `z`
that agrees outside the distinguisher's registers with `q` (step `0`) or with the tear-down, the
clock, the side additions and the reply of `q` (the later steps). -/
theorem relay_step_supp (D : Distinguisher W X Y Req Resp n m)
    (k : Fin (relaySlots n m F + 1)) {q : RR} {v : QState RR} (hv : Supported {q} v) :
    Supported {p | ∃ z, p = setupFun F b Q (recordFun F b Q D.kind z) ∧
      rest F z = rest F (if (k : ℕ) = 0 then q
        else finalizeFun F b Q (sideAddsPerm F b Q (tickPerm F (teardownFun F b Q q))))}
      ((D.relay F b Q).step k v) := by
  set q' : RR := if (k : ℕ) = 0 then q
    else finalizeFun F b Q (sideAddsPerm F b Q (tickPerm F (teardownFun F b Q q))) with hq'
  have h1 : Supported {q'} ((if (k : ℕ) = 0 then LinearIsometryEquiv.refl ℂ (QState RR) else
      permOp ((((teardownPerm F b Q).trans (tickPerm F)).trans (sideAddsPerm F b Q)).trans
        (finalizePerm F b Q))) v) := by
    split_ifs with hk
    · simp only [hq', hk, if_true]
      exact hv
    · refine hv.permOp fun r hr => ?_
      rw [Set.mem_singleton_iff.1 hr]
      simp only [hq', hk, if_false, Set.mem_singleton_iff]
      rfl
  have h2 := ctrlStep_supp F b Q D h1
  change Supported _ ((permOp (setupPerm F b Q)) ((permOp (recordPerm F b Q D.kind))
    (D.ctrlStep F b Q ((if (k : ℕ) = 0 then LinearIsometryEquiv.refl ℂ (QState RR) else
      permOp ((((teardownPerm F b Q).trans (tickPerm F)).trans (sideAddsPerm F b Q)).trans
        (finalizePerm F b Q))) v))))
  refine (h2.permOp (π := recordPerm F b Q D.kind) fun r hr => (Set.mem_image_of_mem _ hr)).permOp
    fun r hr => ?_
  obtain ⟨z, hz, rfl⟩ := hr
  refine ⟨z, rfl, hz⟩

end Distinguisher

end GordieHowe.Quantum
