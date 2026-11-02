-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.MultiRelayOrigin

@[expose] public section

/-!
# The number of the relay's main requests of a kind

The counting form of `GordieHowe/Model/Quantum/Pure/MultiRelayOrigin.lean`: for a test `p` on main
requests that the idle request fails and a test `q` on relayed requests holding of every request
whose program can make a main request satisfying `p` (`MultiRelay.CanAsk`), the main requests
satisfying `p` in the logs of the final placement of a basis state `g` are at most `K` times the
requests satisfying `q` among the first `Q` requests in `g`'s logs.

- `MultiRelay.countP_runEntries_le`: a relayed request makes at most `K` such main requests, and
  none when it fails `q`.
- `MultiRelay.countP_sched_le`, `MultiRelay.countP_tailEntries`, `MultiRelay.countP_subEntriesL_le`:
  the count for a schedule, its trailing idle sub-slots and its padded prefix.
- `Distinguisher.countP_place_le`: **the count in the logs of the final placement.**
-/

namespace GordieHowe.Quantum

namespace MultiRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)
  [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] (n b Q : ℕ) (ansM : List Req' → Req' → Option
      Resp')
  (H : X → Y) {p : Req' → Bool} {q : Req → Bool}

/-- **A relayed request makes at most `K` main requests satisfying `p`, and none when it fails
`q`**, when the idle request fails `p` (`hpi`) and every request whose program can make a main
request satisfying `p` satisfies `q` (`hq`). -/
theorem countP_runEntries_le (hpi : p F.idle = false)
    (hq : ∀ r r', F.CanAsk r r' → p r' = true → q r = true) (r : Req) (rs : List Req') :
    ((F.runEntries ansM H r rs).filterMap Prod.fst).countP p ≤ if q r then F.K else 0 := by
  by_cases hqr : q r = true
  · simp only [hqr, ↓reduceIte]
    exact List.countP_le_length.trans (F.length_filterMap_runEntries ansM H r rs).le
  · have hqf : q r = false := by simpa using hqr
    simp only [hqf, Bool.false_eq_true, ↓reduceIte, Nat.le_zero, List.countP_eq_zero]
    intro r' hr' hp
    rcases F.origin_runEntries ansM H r rs hr' with h | h
    · rw [h, hpi] at hp
      exact Bool.false_ne_true hp
    · exact hqr (hq r r' h hp)

omit [Inhabited Req'] in
/-- **The idle entry makes no main request satisfying `p`.** -/
theorem countP_idleEntry (hpi : p F.idle = false)
    (out : List (Option Req' × (Option Resp' × (X × Y)))) :
    ([F.idleEntry ansM out].filterMap Prod.fst).countP p = 0 := by
  simp [idleEntry, hpi]

/-- **The main requests of a schedule satisfying `p`** are at most `K` times the requests
satisfying `q` among the first `Q` requests of the entries. -/
theorem countP_sched_le (hpi : p F.idle = false)
    (hq : ∀ r r', F.CanAsk r r' → p r' = true → q r = true) (es : List (Option Req)) :
    ((F.sched n b Q ansM H es).out.filterMap Prod.fst).countP p ≤
      F.K * ((es.filterMap id).take Q).countP q := by
  induction es using List.reverseRecOn with
  | nil => simp [sched]
  | append_singleton es e ih =>
    rw [F.sched_append, F.schedStep_out, List.filterMap_append, List.countP_append,
      List.filterMap_append, List.take_append, List.countP_append, Nat.mul_add]
    refine Nat.add_le_add ih ?_
    rcases e with _ | r
    · simp only [blockOf]
      split_ifs
      · simp
      · rw [F.countP_idleEntry ansM hpi]
        exact Nat.zero_le _
    · simp only [blockOf]
      split_ifs with hrb
      · have hlen : (es.filterMap id).length < Q := by
          rw [length_filterMap_id]
          rw [(F.sched_qb_rb n b Q ansM H es).2] at hrb
          exact hrb
        have htake : ([some r].filterMap id).take (Q - (es.filterMap id).length) = [r] := by
          rw [List.take_of_length_le (by
            change 1 ≤ Q - (List.filterMap id es).length
            omega)]
          rfl
        rw [htake]
        refine (F.countP_runEntries_le ansM H hpi hq r _).trans ?_
        by_cases hqr : q r = true
        · simp [hqr]
        · simp [hqr]
      · rw [F.countP_idleEntry ansM hpi]
        exact Nat.zero_le _

omit [Inhabited Req'] in
/-- **Trailing sub-slots add no main request satisfying `p`.** -/
theorem countP_tailEntries (hpi : p F.idle = false)
    (out : List (Option Req' × (Option Resp' × (X × Y)))) :
    ∀ k, ((F.tailEntries ansM out k).filterMap Prod.fst).countP p =
      (out.filterMap Prod.fst).countP p
  | 0 => rfl
  | k + 1 => by
    rw [tailEntries, List.filterMap_append, List.countP_append, countP_tailEntries hpi out k,
      F.countP_idleEntry ansM hpi, Nat.add_zero]

/-- **The main requests satisfying `p` of the sub-slots before sub-slot `s`** are at most `K`
times the requests satisfying `q` among the first `Q` requests of the entries. -/
theorem countP_subEntriesL_le (hpi : p F.idle = false)
    (hq : ∀ r r', F.CanAsk r r' → p r' = true → q r = true) (s : ℕ) (es : List (Option Req)) :
    ((F.subEntriesL n b Q ansM H s es).filterMap Prod.fst).countP p ≤
      F.K * ((es.filterMap id).take Q).countP q := by
  calc ((F.subEntriesL n b Q ansM H s es).filterMap Prod.fst).countP p
      ≤ ((F.tailEntries ansM (F.sched n b Q ansM H es).out s).filterMap Prod.fst).countP p :=
        ((List.take_sublist _ _).filterMap Prod.fst).countP_le
    _ = ((F.sched n b Q ansM H es).out.filterMap Prod.fst).countP p :=
        F.countP_tailEntries ansM hpi _ s
    _ ≤ F.K * ((es.filterMap id).take Q).countP q := F.countP_sched_le n b Q ansM H hpi hq es

end MultiRelay

namespace Distinguisher

variable {W X Y Req Resp Req' Resp' Xs Ys : Type} [Fintype W] [DecidableEq W] [Fintype X]
  [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Inhabited X] [Inhabited Req'] [AddGroup Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] {n m : ℕ}
  (D : Distinguisher W X Y Req Resp n m) (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (b Q : ℕ)
      (ansM : List Req' → Req' → Option Resp')
  (H : X → Y) {p : Req' → Bool} {q : Req → Bool}

omit [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] in
/-- **The main requests satisfying `p` in the logs of the final placement** of a basis state `g`
are at most `K` times the requests satisfying `q` among the first `Q` requests in `g`'s logs, when
the idle request fails `p` and every request whose program can make a main request satisfying `p`
satisfies `q`. -/
theorem countP_place_le (hpi : p F.idle = false)
    (hq : ∀ r r', F.CanAsk r r' → p r' = true → q r = true) (g : GameReg W n X Y Req Resp m) :
    (requests (splitLogs (D.place F b Q ansM H (relaySlots n m F) m g)).2).countP p ≤
      F.K * ((requests (splitLogs g).2).take Q).countP q := by
  have hl : (splitLogs (D.place F b Q ansM H (relaySlots n m F) m g)).2 =
      fun t : Fin (relaySlots n m F) =>
        ((D.subEntries F b Q ansM H (relaySlots n m F) m g.1).getD t blankEntry).1 := by
    simp only [place, Equiv.apply_symm_apply]
  rw [hl, requests, requestsBefore_ofList _ _ rfl _ le_rfl]
  refine le_trans (((List.take_sublist _ _).filterMap Prod.fst).countP_le) ?_
  rw [subEntries, D.stEntries_self]
  rw [requests, requestsBefore_eq_logEntries _ m le_rfl]
  exact F.countP_subEntriesL_le n b Q ansM H hpi hq _ _

end Distinguisher

end GordieHowe.Quantum
