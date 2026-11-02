-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.MultiRelayResolve
public import GordieHowe.Model.Quantum.Pure.MultiRelayCount

@[expose] public section

/-!
# The side store of the relayed distinguisher read from its record

On the relayed distinguisher's reachable registers the side store is a function of the record,
the stored answers and the clock (`MultiRelay.consSide`): the side vector of each started relayed
request is that of its program run with the side function, on its stored answers, for the
sub-slots of its block done by the clock.

- `MultiRelay.consSide`: the side store read from the record, the stored answers and the clock.
- `MultiRelay.consSide_blank`: the blank record's is blank.
- `MultiRelay.consSide_congr_store`: the stored answers from the clock on are not read.
- `MultiRelay.recList_length_le`, `MultiRelay.lt_of_getD_eq_some`: the started slots fit the
  record.
- `MultiRelay.stAt_vecSa_consSide`: the states of a started relayed request, its side reads answered
  from it, are those with the side reads answered by the side function.
- `MultiRelay.stAt_consSide_curBlk`, `MultiRelay.stAt_consSide_last`: the same at the current
  block, and at the last block when it ended at the clock.
- `MultiRelay.sideVec_init`: the state before the first sub-slot has a blank side vector.
- `MultiRelay.consSide_congr_take`, `MultiRelay.recList_take_of_isSome`, `MultiRelay.fillAt_take`,
  `MultiRelay.recList_take_update_fillAt`, `MultiRelay.consSide_update_fillAt`: records alike below
  a slot whose block starts at the clock or later give the same side store; so does any entry of
  the slot starting at the clock.
- `MultiRelay.consSide_eq_zero_of_le`, `MultiRelay.consSide_fillAt`: the slots from the block
  starting at the clock on have blank side vectors.
- `MultiRelay.consSide_withProg_of_eq`: programs equal at a slot's request give its side vector.
- `Distinguisher.consSide_of_lt`: a slot below the last started one keeps its side vector.
- `Distinguisher.curRel_rel`: the slot of the relayed block in progress is a relayed request.
- `Distinguisher.sideAfter_consSide`: the side additions at the next clock rebuild the side store.
- `Distinguisher.consSide_recordFun`: the record of the starting slot keeps it.
- `Distinguisher.side_sideAddsPerm_tickPerm`: the clock and the side additions rebuild it.
-/

set_option linter.unusedSectionVars false

namespace GordieHowe.Quantum

namespace MultiRelay

open OracleProg

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)
  [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req']

/-- **The side store read from the record, the stored answers and the clock**: at a started
relayed request `r` of slot `i`, the side vector of the program of `r` run with the side function
on the stored answers of its block for the sub-slots of the block done by `t`; `0` elsewhere. -/
def consSide (n b Q : ℕ) {m S : ℕ} (rec : Fin m → Option (Option Req))
    (store : Fin S → Option Resp' × (X × Y)) (t : ℕ) : Fin m → Fin F.qS → Ys :=
  fun i => match blkAt b Q (recList rec) i, (recList rec).getD i none with
    | .rel, some r => F.sideVec (F.stAt F.sideSa r
        (fun k => storeAt store (F.startAt n b Q (recList rec) i + k))
        (min (t - F.startAt n b Q (recList rec) i) F.len))
    | _, _ => 0

theorem consSide_apply_rel (n b Q : ℕ) {m S : ℕ} {rec : Fin m → Option (Option Req)}
    (store : Fin S → Option Resp' × (X × Y)) (t : ℕ) {i : Fin m} {r : Req}
    (hb : blkAt b Q (recList rec) i = .rel) (he : (recList rec).getD i none = some r) :
    F.consSide n b Q rec store t i = F.sideVec (F.stAt F.sideSa r
        (fun k => storeAt store (F.startAt n b Q (recList rec) i + k))
        (min (t - F.startAt n b Q (recList rec) i) F.len)) := by
  simp only [consSide, hb, he]

theorem consSide_apply_of_not (n b Q : ℕ) {m S : ℕ} {rec : Fin m → Option (Option Req)}
    (store : Fin S → Option Resp' × (X × Y)) (t : ℕ) {i : Fin m}
    (h : ∀ r, blkAt b Q (recList rec) i = .rel → (recList rec).getD i none ≠ some r) :
    F.consSide n b Q rec store t i = 0 := by
  unfold consSide
  rcases hb : blkAt b Q (recList rec) i with _ | _ | _ <;>
    rcases he : (recList rec).getD i none with _ | r <;> simp only
  exact absurd he (h r hb)

/-- **The blank record's side store is blank.** -/
theorem consSide_blank (n b Q : ℕ) {m S : ℕ} (store : Fin S → Option Resp' × (X × Y)) (t : ℕ) :
    F.consSide n b Q (fun _ : Fin m => none) store t = 0 := by
  funext i
  refine F.consSide_apply_of_not n b Q store t fun r _ he => ?_
  have hl : recList (fun _ : Fin m => (none : Option (Option Req))) = [] := by
    simp only [recList]
    cases List.finRange m <;> simp [List.takeWhile]
  rw [hl] at he
  simp at he

/-- **The stored answers from the clock on are not read.** -/
theorem consSide_congr_store (n b Q : ℕ) {m S : ℕ} (rec : Fin m → Option (Option Req))
    {store store' : Fin S → Option Resp' × (X × Y)} {t : ℕ}
    (h : ∀ u < t, storeAt store u = storeAt store' u) :
    F.consSide n b Q rec store t = F.consSide n b Q rec store' t := by
  funext i
  unfold consSide
  rcases blkAt b Q (recList rec) i with _ | _ | _ <;>
    rcases (recList rec).getD i none with _ | r <;> simp only
  congr 1
  exact F.stAt_congr _ r fun k hk => h _ (by omega)

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem recList_length_le {m : ℕ} (rec : Fin m → Option (Option Req)) :
    (recList rec).length ≤ m := by
  unfold recList
  simpa using (List.takeWhile_sublist (fun i : Fin m => (rec i).isSome)
    (l := List.finRange m)).length_le

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem lt_of_getD_eq_some {m : ℕ} {rec : Fin m → Option (Option Req)} {j : ℕ} {r : Req}
    (he : (recList rec).getD j none = some r) : j < m := by
  have := recList_length_le rec
  by_contra h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at he
  simp at he

/-- **The states of a started relayed request, its side reads answered from the side store read
from the record**, are those with the side reads answered by the side function, up to the
sub-slots of its block done by the clock. -/
theorem stAt_vecSa_consSide (n b Q : ℕ) {m S : ℕ} {rec : Fin m → Option (Option Req)}
    (store : Fin S → Option Resp' × (X × Y)) (t : ℕ) {i : ℕ} (hi : i < m) {r : Req}
    (hb : blkAt b Q (recList rec) i = .rel) (he : (recList rec).getD i none = some r) {u : ℕ}
    (hu : u ≤ min (t - F.startAt n b Q (recList rec) i) F.len) :
    F.stAt (F.vecSa (F.vecAt (F.consSide n b Q rec store t) i)) r
        (fun k => storeAt store (F.startAt n b Q (recList rec) i + k)) u =
      F.stAt F.sideSa r (fun k => storeAt store (F.startAt n b Q (recList rec) i + k)) u := by
  have hv : F.vecAt (F.consSide n b Q rec store t) i = F.sideVec (F.stAt F.sideSa r
      (fun k => storeAt store (F.startAt n b Q (recList rec) i + k))
      (min (t - F.startAt n b Q (recList rec) i) F.len)) := by
    simp only [vecAt, hi, ↓reduceDIte]
    exact F.consSide_apply_rel n b Q store t (i := ⟨i, hi⟩) hb he
  rw [hv]
  refine F.stAt_vecSa r _ u ?_
  exact (F.vecAgrees_sideVec _).of_prefix (F.sideInv_stAt _ r _ u) (F.stAt_ans_le _ r _ hu)
    (F.ns_stAt_le _ r _ hu)

/-- **The states of the current block's relayed request read from the side store read from the
record** are those with the side function. -/
theorem stAt_consSide_curBlk (n b Q : ℕ) {m S : ℕ} {rec : Fin m → Option (Option Req)}
    (store : Fin S → Option Resp' × (X × Y)) (t : ℕ) {j sub : ℕ} {r : Req}
    (hc : F.curBlk n b Q rec t = some (j, sub)) (hb : blkAt b Q (recList rec) j = .rel)
    (he : (recList rec).getD j none = some r) :
    F.stAt (F.vecSa (F.vecAt (F.consSide n b Q rec store t) j)) r
        (fun k => storeAt store (F.startAt n b Q (recList rec) j + k)) sub =
      F.stAt F.sideSa r (fun k => storeAt store (F.startAt n b Q (recList rec) j + k)) sub := by
  obtain ⟨-, h1, h2⟩ := F.curBlk_eq_some hc
  rw [hb] at h2
  simp only [blkLen] at h2
  exact F.stAt_vecSa_consSide n b Q store t (lt_of_getD_eq_some he) hb he (by omega)

/-- **The states of the last started relayed request, its block ended at the clock, read from the
side store read from the record** are those with the side function. -/
theorem stAt_consSide_last (n b Q : ℕ) {m S : ℕ} {rec : Fin m → Option (Option Req)}
    (store : Fin S → Option Resp' × (X × Y)) {t : ℕ}
    (ht : F.startAt n b Q (recList rec) (recList rec).length = t) {r : Req}
    (hb : blkAt b Q (recList rec) ((recList rec).length - 1) = .rel)
    (he : (recList rec).getD ((recList rec).length - 1) none = some r) :
    F.stAt (F.vecSa (F.vecAt (F.consSide n b Q rec store t) ((recList rec).length - 1))) r
        (fun k => storeAt store (F.startAt n b Q (recList rec) ((recList rec).length - 1) + k))
        F.len =
      F.stAt F.sideSa r (fun k => storeAt store
        (F.startAt n b Q (recList rec) ((recList rec).length - 1) + k)) F.len := by
  have hpos : 0 < (recList rec).length := by
    by_contra h0
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at he
    simp at he
  have hs := F.startAt_succ n b Q (recList rec) ((recList rec).length - 1)
  rw [hb, Nat.sub_add_cancel hpos, ht] at hs
  simp only [blkLen] at hs
  exact F.stAt_vecSa_consSide n b Q store t (lt_of_getD_eq_some he) hb he (by omega)

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
theorem sideVec_init : F.sideVec (RelaySt.init : RelaySt Y Resp' Ys) = 0 := by
  funext k
  rfl

/-- **Records alike below slot `i`, whose block starts at the clock or later**, give the same side
store. -/
theorem consSide_congr_take (n b Q : ℕ) {m S : ℕ} {rec rec' : Fin m → Option (Option Req)}
    (store : Fin S → Option Resp' × (X × Y)) {t i : ℕ}
    (hte : (recList rec).take i = (recList rec').take i)
    (hi : t ≤ F.startAt n b Q (recList rec) i) :
    F.consSide n b Q rec store t = F.consSide n b Q rec' store t := by
  have hi' : t ≤ F.startAt n b Q (recList rec') i := by
    rwa [← F.startAt_congr n b Q hte]
  funext j
  by_cases hj : (j : ℕ) < i
  · have ht : (recList rec).take j = (recList rec').take j := by
      have := congrArg (List.take j) hte
      simpa [List.take_take, Nat.min_eq_left hj.le] using this
    have hg : (recList rec).getD j none = (recList rec').getD j none := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, ← List.getElem?_take_of_lt hj,
        hte, List.getElem?_take_of_lt hj]
    have hbk : blkAt b Q (recList rec) j = blkAt b Q (recList rec') j := by
      simp only [blkAt, ht, hg]
    have hst : F.startAt n b Q (recList rec) j = F.startAt n b Q (recList rec') j :=
      F.startAt_congr n b Q ht
    unfold consSide
    rw [hbk, hg, hst]
  · -- the slots from `i` on have not run a sub-slot
    have hz : ∀ rec₀ : Fin m → Option (Option Req), t ≤ F.startAt n b Q (recList rec₀) i →
        F.consSide n b Q rec₀ store t j = 0 := fun rec₀ h₀ => by
      have hm := F.startAt_mono n b Q (recList rec₀) (show i ≤ j by omega)
      unfold consSide
      rcases blkAt b Q (recList rec₀) j with _ | _ | _ <;>
        rcases (recList rec₀).getD j none with _ | r <;> simp only
      rw [show min (t - F.startAt n b Q (recList rec₀) j) F.len = 0 by omega]
      exact F.sideVec_init
    rw [hz rec hi, hz rec' hi']

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem recList_take_of_isSome {m : ℕ} {rec : Fin m → Option (Option Req)} {i : Fin m}
    (h : ∀ i' : Fin m, i' < i → (rec i').isSome) : (recList rec).take i = recPrefix rec i := by
  unfold recList recPrefix
  rw [← List.map_take]
  congr 1
  conv_lhs => rw [← List.take_append_drop i (List.finRange m)]
  rw [List.takeWhile_append_of_pos]
  · rw [List.take_append, List.take_of_length_le (by simp)]
    simp
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    simp only [List.length_take, List.length_finRange] at hk
    refine h _ ?_
    simp only [List.getElem_take, List.getElem_finRange]
    exact Fin.mk_lt_mk.2 (by simp; omega)

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **The started slots below the slot starting at the clock**, and its block's start. -/
theorem fillAt_take {n b Q m : ℕ} {rec : Fin m → Option (Option Req)} {t : ℕ} {i : Fin m}
    (hf : F.fillAt n b Q rec t = some i) :
    (recList rec).take i = recPrefix rec i ∧ F.startAt n b Q (recList rec) i = t := by
  have hp := List.find?_some hf
  simp only [decide_eq_true_eq] at hp
  obtain ⟨hlt, hst⟩ := hp
  have h1 := recList_take_of_isSome hlt
  refine ⟨h1, ?_⟩
  rw [F.startAt_congr n b Q (es' := recPrefix rec i) (by
    rw [h1, List.take_of_length_le (by simp [recPrefix])]), hst]

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **The entry of the slot starting at the clock does not move the started slots below it.** -/
theorem recList_take_update_fillAt {n b Q m : ℕ} {rec : Fin m → Option (Option Req)} {t : ℕ}
    {i : Fin m} (hf : F.fillAt n b Q rec t = some i) (v : Option (Option Req)) :
    (recList (Function.update rec i v)).take i = (recList rec).take i := by
  rw [(F.fillAt_take (F.fillAt_update hf v)).1, (F.fillAt_take hf).1]
  unfold recPrefix
  refine List.map_congr_left fun j hj => ?_
  have hj' : j < i := by
    obtain ⟨k, hk, hkj⟩ := List.mem_iff_getElem.1 hj
    simp only [List.length_take, List.length_finRange] at hk
    rw [← hkj]
    simp only [List.getElem_take, List.getElem_finRange]
    exact Fin.mk_lt_mk.2 (by simp; omega)
  rw [Function.update_of_ne (ne_of_lt hj')]

/-- **The slots from the block starting at the clock on have blank side vectors.** -/
theorem consSide_eq_zero_of_le (n b Q : ℕ) {m S : ℕ} {rec : Fin m → Option (Option Req)}
    (store : Fin S → Option Resp' × (X × Y)) {t : ℕ} {j : Fin m}
    (h : t ≤ F.startAt n b Q (recList rec) j) : F.consSide n b Q rec store t j = 0 := by
  unfold consSide
  rcases blkAt b Q (recList rec) j with _ | _ | _ <;>
    rcases (recList rec).getD j none with _ | r <;> simp only
  rw [show min (t - F.startAt n b Q (recList rec) j) F.len = 0 by omega]
  exact F.sideVec_init

/-- **The slots from the slot starting at the clock on have blank side vectors.** -/
theorem consSide_fillAt (n b Q : ℕ) {m S : ℕ} {rec : Fin m → Option (Option Req)}
    (store : Fin S → Option Resp' × (X × Y)) {t : ℕ} {i : Fin m}
    (hf : F.fillAt n b Q rec t = some i) {k : Fin m} (hk : i ≤ k) :
    F.consSide n b Q rec store t k = 0 := by
  refine F.consSide_eq_zero_of_le n b Q store ?_
  rw [← (F.fillAt_take hf).2]
  exact F.startAt_mono n b Q _ hk

/-- **The slot starting at the clock does not move the side store** whatever its entry. -/
theorem consSide_update_fillAt (n b Q : ℕ) {m S : ℕ} {rec : Fin m → Option (Option Req)}
    (store : Fin S → Option Resp' × (X × Y)) {t : ℕ} {i : Fin m}
    (hf : F.fillAt n b Q rec t = some i) (v : Option (Option Req)) :
    F.consSide n b Q (Function.update rec i v) store t = F.consSide n b Q rec store t := by
  refine F.consSide_congr_take n b Q store (i := i) (F.recList_take_update_fillAt hf v) ?_
  rw [(F.fillAt_take (F.fillAt_update hf v)).2]

variable {F} {p' : Req → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') (Option Resp)}

/-- **A slot whose request has the same program has the same side vector.** -/
theorem consSide_withProg_of_eq (n b Q : ℕ) {m S : ℕ} (rec : Fin m → Option (Option Req))
    (store : Fin S → Option Resp' × (X × Y)) (t : ℕ) (i : Fin m)
    (h : ∀ r, (recList rec).getD i none = some r → p' r = F.prog r) :
    (F.withProg p').consSide n b Q rec store t i = F.consSide n b Q rec store t i := by
  unfold consSide
  rcases blkAt b Q (recList rec) i with _ | _ | _ <;>
    rcases he : (recList rec).getD i none with _ | r
  all_goals first
    | rfl
    | (simp only; rw [startAt_withProg, stAt_of_eq (h _ he)]; rfl)

end MultiRelay

/-! ### The side store across a step -/

namespace Distinguisher

open MultiRelay

variable {W X Y Req Resp Req' Resp' Xs Ys : Type} [Fintype W] [DecidableEq W] [Fintype X]
  [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Inhabited X] [Inhabited Req'] [AddGroup Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] {n m : ℕ}
  (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (b Q : ℕ)

/-- **A finished relayed block's side vector stays**: at a slot below the last started one, the
side store read at later clocks is the same. -/
theorem consSide_of_lt {rec : Fin m → Option (Option Req)} {es : List (Option Req)} {t : ℕ}
    (hrec : RecAt (n := n) F b Q rec es t) (store : Fin (relaySlots n m F) → Option Resp' × (X × Y))
    {t' : ℕ} (htt : t ≤ t') (i : Fin m) (hi : (i : ℕ) + 1 < es.length) :
    F.consSide n b Q rec store t' i = F.consSide n b Q rec store t i := by
  have hl : recList rec = es := by rw [hrec.2.1]; exact recList_getElem? es hrec.1
  unfold consSide
  rcases hb : blkAt b Q (recList rec) i with _ | _ | _ <;>
    rcases he : (recList rec).getD i none with _ | r <;> simp only
  have h1 := hrec.2.2 (i + 1) hi
  have h2 := F.startAt_succ n b Q es i
  rw [← hl, hb] at h2
  simp only [blkLen] at h2
  rw [hl]
  rw [hl] at h2
  rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]

omit [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req]
  [Fintype Resp] [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] [Fintype Ys]
  [DecidableEq Ys] in
theorem curRel_rel {rec : Fin m → Option (Option Req)} {t j : ℕ} {r : Req} {sub : ℕ}
    (h : F.curRel n b Q rec t = some (j, r, sub)) : blkAt b Q (recList rec) j = .rel := by
  obtain ⟨hj, -, -⟩ := F.curRel_eq_some h
  subst hj
  revert h
  unfold curRel
  rcases blkAt b Q (recList rec) ((recList rec).length - 1) with _ | _ | _ <;>
    rcases (recList rec).getD ((recList rec).length - 1) none with _ | r' <;> simp

/-- **The side additions after the clock rebuild the side store read from the record**: on the
side store read at clock `t`, the side additions at clock `t + 1` give the one read at `t + 1`. -/
theorem sideAfter_consSide {rec : Fin m → Option (Option Req)} {es : List (Option Req)} {t : ℕ}
    (hrec : RecAt (n := n) F b Q rec es t)
    (store : Fin (relaySlots n m F) → Option Resp' × (X × Y)) :
    sideAfter F b Q rec store (F.consSide n b Q rec store t) (t + 1) =
      F.consSide n b Q rec store (t + 1) := by
  have hl : recList rec = es := by rw [hrec.2.1]; exact recList_getElem? es hrec.1
  funext i
  -- the slots below the last started one, and those not started
  have hother : ∀ i : Fin m, (i : ℕ) ≠ es.length - 1 →
      F.consSide n b Q rec store t i = F.consSide n b Q rec store (t + 1) i := by
    intro i hi
    by_cases hlt : (i : ℕ) + 1 < es.length
    · exact (consSide_of_lt F b Q hrec store (Nat.le_succ t) i hlt).symm
    · have hge : es.length ≤ i := by omega
      have hn : ∀ t', F.consSide n b Q rec store t' i = 0 := fun t' =>
        F.consSide_apply_of_not n b Q store t' fun r _ he => by
          rw [hl] at he
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at he
      rw [hn, hn]
  unfold sideAfter
  rcases hc : F.curRel n b Q rec (t + 1) with _ | ⟨j, r, sub⟩
  · -- no relayed block in progress
    dsimp only
    by_cases hi : (i : ℕ) = es.length - 1
    · by_cases hrel : ∃ r, blkAt b Q (recList rec) i = .rel ∧ (recList rec).getD i none = some r
      · obtain ⟨r, hb, he⟩ := hrel
        rw [F.consSide_apply_rel n b Q store t hb he,
          F.consSide_apply_rel n b Q store (t + 1) hb he]
        have hpos : 0 < (recList rec).length := by
          by_contra h0
          have : recList rec = [] := List.eq_nil_of_length_eq_zero (by omega)
          rw [this] at he
          simp at he
        have hi' : (i : ℕ) = (recList rec).length - 1 := by rw [hl]; exact hi
        have hst : F.startAt n b Q (recList rec) i ≤ t := by
          rw [hl]
          exact hrec.2.2 i (by rw [hl] at hpos; omega)
        unfold curRel at hc
        simp only [hpos, ↓reduceIte] at hc
        rw [← hi', hb, he] at hc
        simp only at hc
        split_ifs at hc with h1
        push Not at h1
        have h2 := h1 (by omega)
        rw [Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
      · push Not at hrel
        rw [F.consSide_apply_of_not n b Q store t fun r hb he => hrel r hb he,
          F.consSide_apply_of_not n b Q store (t + 1) fun r hb he => hrel r hb he]
    · exact hother i hi
  · obtain ⟨hj, he, hsub, hlo, hhi⟩ := F.curRel_eq_some hc
    have hb := curRel_rel F b Q hc
    have hjm : j < m := by
      have := hrec.1
      have hpos : 0 < (recList rec).length := by
        by_contra h0
        have : recList rec = [] := List.eq_nil_of_length_eq_zero (by omega)
        rw [this] at he
        simp at he
      rw [hj, hl]
      rw [hl] at hpos
      omega
    simp only [hjm, ↓reduceDIte]
    by_cases hij : i = ⟨j, hjm⟩
    · subst hij
      rw [Function.update_self, F.consSide_apply_rel n b Q store t (i := ⟨j, hjm⟩) hb he,
        F.consSide_apply_rel n b Q store (t + 1) (i := ⟨j, hjm⟩) hb he]
      have hs1 : min (t - F.startAt n b Q (recList rec) j) F.len = sub - 1 := by
        rw [Nat.min_eq_left (by omega)]
        omega
      have hs2 : min (t + 1 - F.startAt n b Q (recList rec) j) F.len = sub - 1 + 1 := by
        rw [Nat.min_eq_left (by omega)]
        omega
      change F.addsVec r _ sub (F.sideVec (F.stAt F.sideSa r _
          (min (t - F.startAt n b Q (recList rec) j) F.len))) =
        F.sideVec (F.stAt F.sideSa r _ (min (t + 1 - F.startAt n b Q (recList rec) j) F.len))
      rw [hs1, hs2, show sub = sub - 1 + 1 by omega]
      exact F.addsVec_stAt r _ (sub - 1)
    · rw [Function.update_of_ne hij]
      refine hother i fun e => hij (Fin.ext ?_)
      show (i : ℕ) = j
      rw [hl] at hj
      omega

/-- **The record of the starting slot keeps the side store read from the record.** -/
theorem consSide_recordFun (kind : W → Bool)
    (d : RelayReg W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)) :
    F.consSide n b Q (recordFun F b Q kind d).1.1.record d.1.1.store d.1.1.time =
      F.consSide n b Q d.1.1.record d.1.1.store d.1.1.time := by
  unfold recordFun
  rcases hf : F.fillAt n b Q d.1.1.record d.1.1.time with _ | i
  · rfl
  · exact F.consSide_update_fillAt n b Q d.1.1.store hf _

/-- **The clock and the side additions rebuild the side store read from the record**: on registers
whose side store is read from the record at the clock `t < S`, the side store after the clock and
the side additions is read at `t + 1`. -/
theorem side_sideAddsPerm_tickPerm
    (y : RelayReg W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys))
    {es : List (Option Req)} (hrec : RecAt (n := n) F b Q y.1.1.record es y.1.1.time)
    (ht : (y.1.1.time : ℕ) < relaySlots n m F)
    (hs : y.1.1.side = F.consSide n b Q y.1.1.record y.1.1.store y.1.1.time) :
    (sideAddsPerm F b Q (tickPerm F y)).1.1.side =
      F.consSide n b Q y.1.1.record y.1.1.store (y.1.1.time + 1) := by
  have htk : ((tickPerm F y).1.1.time : ℕ) = y.1.1.time + 1 := by
    change (finRotate _ y.1.1.time : ℕ) = _
    rw [coe_finRotate_of_ne_last (fun h => by
      have := congrArg Fin.val h
      simp only [Fin.val_last] at this
      omega)]
  rw [sideAddsPerm_apply]
  change sideAfter F b Q y.1.1.record y.1.1.store y.1.1.side (tickPerm F y).1.1.time = _
  rw [htk, hs]
  exact sideAfter_consSide F b Q hrec y.1.1.store

end Distinguisher

end GordieHowe.Quantum
