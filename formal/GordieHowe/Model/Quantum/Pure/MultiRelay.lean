-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.PostSlots
public import GordieHowe.Model.Quantum.O2H.Budget
public import GordieHowe.Model.NARG.OracleProg

@[expose] public section

/-!
# Relaying each request as several requests to a main environment

A distinguisher `D` of the pure game (`n` query pairs, `m` slots) plays against an environment
whose reply to each request is computed by a classical program that makes requests to a main
environment and queries to the oracle. The relayed distinguisher `D.relay F b Q` plays the pure
game against the main environment itself, with one query pair per slot.

- `OracleProg.after ans`: a program's state after the answers `ans` (its result, or its next
  query).
- `MultiRelay X Y Req Resp Req' Resp'`: the program `prog r` answering the request `r`; its
  queries are `X ⊕ Req'` (an oracle query or a main request) and its answers `Y ⊕ Option Resp'`;
  `K > 0` main requests and `qR` oracle queries per relayed request, `len = K + qR` sub-slots; the
  padding request `idle`.
- One relayed request, sub-slot by sub-slot (`progAct`, `act`, `next`, `stAt`, `reply`): the
  program's action while it keeps its budgets, padding after it returns (the idle request until
  `K` main requests were made, then a query of `default`), the program's result if it returned
  within its budgets, else `none`. Against main replies `ansM` (`runAux`, `runEntries`,
  `runReply`): the entries (main request, stored answer) of its `len` sub-slots, and its reply.
- The schedule (`Blk`, `blk`, `blkLen`, `blkAt`, `startAt`, `sched`, `tailEntries`, `mainReqs`):
  slot `i` of `D` becomes `n` single-query sub-slots if it queries within the budget `b`, the
  `len` sub-slots of its relayed request if it is a request numbered below `Q`, and one idle
  request otherwise; sub-slots after the last slot are idle requests. `mainReqs Q ansM H rs`: the
  main requests of relaying the requests `rs`.
- `RelayW`: the relayed distinguisher's workspace: `D`'s registers, the record of `D`'s slots, the
  stored answers of the sub-slots and the clock. `Distinguisher.relaySlots n m F = m · max n len`;
  `Distinguisher.relaySlotsS`, `relaySlots_eq_relaySlotsS`: the same from the relay's numbers.
- `Distinguisher.relay D F b Q` (the relayed distinguisher): each step tears down the previous
  sub-slot and ticks the clock, finalizes a completed slot (the relayed reply written into `D`'s
  response register), applies `D`'s step at the start of a slot (`ctrlStep`), records the slot's
  entry and sets up the next sub-slot (`teardownPerm`, `tickPerm`, `finalizePerm`, `recordPerm`,
  `setupPerm`). Its kind is read from the record, the stored answers and the
  clock. The theorems are in `GordieHowe/Model/Quantum/Pure/MultiRelayRun.lean`.
- The side answers a state reads (`sideStep_congr_sa`, `stAt_congr_sa`, `preSt_congr_sa`,
  `pendSt_congr_sa`): only those below its side reads. `NsAgree`, `nsAgree_sideStep`,
  `nsAgree_iterate_sideStep`, `nsAgree_next`, `nsAgree_stAt`, `nsAgree_pendSt`: side answers alike
  below `K` give states alike until `K` side reads; `ns_le_qS_sideStep`,
  `ns_le_qS_iterate_sideStep`, `ns_le_qS_pendSt`: at most `qS` side reads;
  `pendSt_ns_eq_qS_congr`: making all `qS` side reads does not read the last side answer.
-/

open Finset
open scoped BigOperators

namespace GordieHowe

namespace OracleProg

variable {A B R : Type*}

/-- **The state of a program after the answers `ans`**: `inl r` if it has returned `r`, `inr a` if
its next query is `a`. Answers after its return are ignored. -/
def after : OracleProg A B R → List B → R ⊕ A
  | pure r, _ => .inl r
  | query a _, [] => .inr a
  | query _ k, b :: bs => (k b).after bs

@[simp] theorem after_pure (r : R) (ans : List B) : (pure r : OracleProg A B R).after ans = .inl r :=
  rfl

@[simp] theorem after_query_nil (a : A) (k : B → OracleProg A B R) :
    (query a k).after [] = .inr a :=
  rfl

@[simp] theorem after_query_cons (a : A) (k : B → OracleProg A B R) (b : B) (bs : List B) :
    (query a k).after (b :: bs) = (k b).after bs :=
  rfl

/-- **The state of a translated program** after translated answers: the original state, its next
query translated, when the translation of answers inverts `φ`. -/
theorem after_translate {A' B' : Type*} (ι : A → A') (g : A → B' → B) (φ : B → B')
    (hg : ∀ a b, g a (φ b) = b) :
    ∀ (p : OracleProg A B R) (ans : List B),
      (p.translate ι g).after (ans.map φ) = Sum.map id ι (p.after ans)
  | pure _, _ => rfl
  | query _ _, [] => rfl
  | query a k, b :: bs => by
    simp only [translate, List.map_cons, after_query_cons, hg]
    exact after_translate ι g φ hg (k b) bs

/-- **A program that begins with a side read**: its first query is `inl (inr x)`, read from its
shape alone. -/
def startsSide {X Xs Req' B R : Type} : OracleProg ((X ⊕ Xs) ⊕ Req') B R → Bool
  | query (.inl (.inr _)) _ => true
  | _ => false

section Side

variable {X Xs Y Ys Req' Resp' R : Type}

/-- An answer of a side-read-free program as an answer of a program with side reads. -/
def liftAnsS : Y ⊕ Option Resp' → (Y ⊕ Ys) ⊕ Option Resp'
  | .inl y => .inl (.inl y)
  | .inr a => .inr a

/-- **`p` with its side reads answered by `s`**, classically: a side read at `x` is replaced by
`s x`; the oracle reads and the main requests are kept. -/
def elimSide (s : Xs → Ys) :
    OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R →
      OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R
  | .pure r => .pure r
  | .query (.inl (.inl x)) k => .query (.inl x) fun b => elimSide s (k (liftAnsS b))
  | .query (.inl (.inr x)) k => elimSide s (k (.inl (.inr (s x))))
  | .query (.inr r') k => .query (.inr r') fun b => elimSide s (k (liftAnsS b))

end Side

end OracleProg

namespace Quantum

/-- **A relay of requests to a main environment**: request `r` is answered by the classical
program `prog r`, whose queries are oracle queries `inl (inl x)` (answered `inl (inl (H x))`),
side reads `inl (inr x)` (answered `inl (inr (side x))`, classically, with no oracle query) and
main requests `inr r'` (answered `inr a`, the main environment's reply). Each relayed request
occupies `len = K + qR` sub-slots, each an oracle query or a main request, exactly `K` of them
main requests (`MultiRelay.length_runAux`, `MultiRelay.length_filterMap_runEntries`): the
program's own queries and main requests, then padding by the idle main request `idle` and by
queries of `default`. Its side reads, at most `qS`, are made after the sub-slots, and before the
first sub-slot a program that begins with a side read gets a pad sub-slot, a query of the fixed
point `default`, at most `qP` of them. A program that asks for more than `K` main requests, `qR`
queries, `qS` side reads or `qP` pad sub-slots is cut off. -/
structure MultiRelay (X Y Req Resp Req' Resp' : Type) (Xs : Type := Empty) (Ys : Type := Unit)
    where
  /-- The program answering a request: oracle queries `inl (inl x)`, side reads `inl (inr x)`
  and main requests `inr r'`. -/
  prog : Req → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') (Option Resp)
  /-- The main requests of one relayed request. -/
  K : ℕ
  K_pos : 0 < K
  /-- The oracle queries of one relayed request. -/
  qR : ℕ
  /-- The padding request. -/
  idle : Req'
  /-- The side function answering the side reads. -/
  side : Xs → Ys := by exact fun x => nomatch x
  /-- The side reads of one relayed request. -/
  qS : ℕ := 0
  /-- The pad sub-slots of one relayed request: a query of the fixed point `default` before a
  program that begins with a side read, since every step of the dilated distinguisher ends in a
  query. -/
  qP : ℕ := 0
  /-- At most one pad sub-slot. -/
  qP_le_one : qP ≤ 1 := by decide
  /-- Pad sub-slots only for a relay with side reads. -/
  qP_spec : qP = 0 ∨ Nonempty Xs := by exact Or.inl rfl

namespace MultiRelay

/-- The answer to a side-read-free program from an answer to a relay program. -/
def plainAns {Y Ys Resp' : Type} : (Y ⊕ Ys) ⊕ Option Resp' → Y ⊕ Option Resp'
  | .inl (.inl y) => .inl y
  | .inl (.inr _) => .inr none
  | .inr a => .inr a

/-- **A program over oracle queries and main requests as a program with side reads**: the same
queries, no side reads. -/
def plainOf {X Y Req' Resp' Xs Ys R : Type} (p : OracleProg (X ⊕ Req') (Y ⊕ Option Resp') R) :
    OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') R :=
  p.translate (Sum.map Sum.inl id) fun _ b => plainAns b

/-- **The side-read-free relay program** of a program over oracle queries and main requests: the
same queries, no side reads. -/
def plainProg {X Y Req Resp Req' Resp' Xs Ys : Type}
    (p : Req → OracleProg (X ⊕ Req') (Y ⊕ Option Resp') (Option Resp)) :
    Req → OracleProg ((X ⊕ Xs) ⊕ Req') ((Y ⊕ Ys) ⊕ Option Resp') (Option Resp) :=
  fun r => plainOf (p r)

end MultiRelay

/-- **The state of a relayed request**: the answers fed to the program, the main requests, oracle
queries, side reads and pad sub-slots made, and whether the program is still within its
budgets. -/
@[ext]
structure RelaySt (Y Resp' : Type) (Ys : Type := Unit) where
  /-- The answers fed to the program. -/
  ans : List ((Y ⊕ Ys) ⊕ Option Resp')
  /-- The main requests made. -/
  na : ℕ
  /-- The oracle queries made. -/
  nq : ℕ
  /-- The side reads made. -/
  ns : ℕ
  /-- The pad sub-slots made. -/
  np : ℕ
  /-- Whether the program is within its budgets. -/
  live : Bool

namespace RelaySt

/-- The state before the first sub-slot. -/
def init {Y Resp' Ys : Type} : RelaySt Y Resp' Ys := ⟨[], 0, 0, 0, 0, true⟩

end RelaySt

namespace MultiRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)

/-- **A relay without side reads has no pad sub-slots.** -/
theorem qP_eq_zero [IsEmpty Xs] : F.qP = 0 :=
  F.qP_spec.resolve_right fun ⟨x⟩ => isEmptyElim x

/-- The sub-slots of one relayed request (reducible, so that `relaySlots` and `relaySlotsS` of the
counts are one term after reducible unfolding). -/
abbrev len : ℕ := F.K + F.qR + F.qP

/-- A relayed request occupies at least one sub-slot. -/
theorem len_pos : 0 < F.len := Nat.add_pos_left (Nat.add_pos_left F.K_pos _) _

/-- **The program's action at a state**, within its budgets: a query `inl (inl x)`, a side read
`inl (inr x)` or a main request `inr r'`; `none` if it has returned, has left its budgets, or asks
for more than they allow. -/
def progAct (r : Req) (st : RelaySt Y Resp' Ys) : Option ((X ⊕ Xs) ⊕ Req') :=
  if st.live then
    match (F.prog r).after st.ans with
    | .inl _ => none
    | .inr (.inl (.inl x)) => if st.nq < F.qR then some (.inl (.inl x)) else none
    | .inr (.inl (.inr x)) => if st.ns < F.qS then some (.inl (.inr x)) else none
    | .inr (.inr r') => if st.na < F.K then some (.inr r') else none
  else none

/-- **One side read** answered by `sa`: at a side read of `x`, its answer `sa ns x` (`ns` the side
reads made before it) fed to the program; the state unchanged at any other action. -/
def sideStep (sa : ℕ → Xs → Ys) (r : Req) (st : RelaySt Y Resp' Ys) : RelaySt Y Resp' Ys :=
  match F.progAct r st with
  | some (.inl (.inr x)) =>
    ⟨st.ans ++ [.inl (.inr (sa st.ns x))], st.na, st.nq, st.ns + 1, st.np, st.live⟩
  | _ => st

/-- **The side reads the program makes next**, answered by `sa`: `qS` side steps, which make
every side read up to its next oracle query or main request (`progAct_close_ne_side`). -/
def close (sa : ℕ → Xs → Ys) (r : Req) (st : RelaySt Y Resp' Ys) : RelaySt Y Resp' Ys :=
  (F.sideStep sa r)^[F.qS] st

variable [Inhabited X]

/-- **The action of a sub-slot**: the program's (a side read only within the pad budget, the pad
sub-slot), else padding (the idle request while fewer than `K` main requests were made, else a
query of `default`). -/
def act (r : Req) (st : RelaySt Y Resp' Ys) : (X ⊕ Xs) ⊕ Req' :=
  match F.progAct r st with
  | some (.inl (.inr x)) =>
    if st.np < F.qP then .inl (.inr x)
    else if st.na < F.K then .inr F.idle else .inl (.inl default)
  | some a => a
  | none => if st.na < F.K then .inr F.idle else .inl (.inl default)

/-- **The state after a sub-slot** whose stored answer is `a` (the main reply and the query
pair): the program's answer appended for its own query or main request; at a side read, which
occurs only before the first sub-slot (`progAct_close_ne_side`), the sub-slot is a pad (a query
of `default`) within the pad budget, else padding that leaves the budgets; a padding action
counts as a main request or a query, and leaves the budgets when the program had not
returned. -/
def next (r : Req) (st : RelaySt Y Resp' Ys) (a : Option Resp' × (X × Y)) : RelaySt Y Resp' Ys :=
  match F.progAct r st with
  | some (.inl (.inl _)) => ⟨st.ans ++ [.inl (.inl a.2.2)], st.na, st.nq + 1, st.ns, st.np, st.live⟩
  | some (.inl (.inr _)) =>
    if st.np < F.qP then ⟨st.ans, st.na, st.nq, st.ns, st.np + 1, st.live⟩
    else if st.na < F.K then ⟨st.ans, st.na + 1, st.nq, st.ns, st.np, false⟩
    else ⟨st.ans, st.na, st.nq + 1, st.ns, st.np, false⟩
  | some (.inr _) => ⟨st.ans ++ [.inr a.1], st.na + 1, st.nq, st.ns, st.np, st.live⟩
  | none =>
    if st.na < F.K then
      ⟨st.ans, st.na + 1, st.nq, st.ns, st.np, st.live && ((F.prog r).after st.ans).isLeft⟩
    else ⟨st.ans, st.na, st.nq + 1, st.ns, st.np, st.live && ((F.prog r).after st.ans).isLeft⟩

/-- **The state after the stored answers** `g 0, …, g (i - 1)`, the side reads answered by `sa`:
the initial state, then each sub-slot followed by the side reads after it. -/
def stAt (sa : ℕ → Xs → Ys) (r : Req) (g : ℕ → Option Resp' × (X × Y)) : ℕ → RelaySt Y Resp' Ys
  | 0 => .init
  | i + 1 => F.close sa r (F.next r (stAt sa r g i) (g i))

/-- **The state before the side reads after sub-slot `i - 1`.** -/
def preSt (sa : ℕ → Xs → Ys) (r : Req) (g : ℕ → Option Resp' × (X × Y)) : ℕ → RelaySt Y Resp' Ys
  | 0 => .init
  | i + 1 => F.next r (F.stAt sa r g i) (g i)

/-- **The reply of a relayed request** at its final state: the program's result if it returned
within its budgets, else `none`. -/
def reply (r : Req) (st : RelaySt Y Resp' Ys) : Option Resp :=
  if st.live then ((F.prog r).after st.ans).elim id fun _ => none else none

omit [Inhabited X] in
/-- The program queries only within its query budget. -/
theorem nq_lt_of_progAct (r : Req) (st : RelaySt Y Resp' Ys) {x : X}
    (h : F.progAct r st = some (.inl (.inl x))) : st.nq < F.qR := by
  unfold progAct at h
  by_cases hl : st.live
  · rcases hq : (F.prog r).after st.ans with _ | ((x' | x') | r') <;>
      simp only [hl, hq, ↓reduceIte] at h
    · simp at h
    · by_cases h2 : st.nq < F.qR
      · exact h2
      · simp [h2] at h
    · split_ifs at h <;> simp at h
    · split_ifs at h <;> simp at h
  · simp [hl] at h

omit [Inhabited X] in
/-- The program reads the side function only within its side-read budget. -/
theorem ns_lt_of_progAct (r : Req) (st : RelaySt Y Resp' Ys) {x : Xs}
    (h : F.progAct r st = some (.inl (.inr x))) : st.ns < F.qS := by
  unfold progAct at h
  by_cases hl : st.live
  · rcases hq : (F.prog r).after st.ans with _ | ((x' | x') | r') <;>
      simp only [hl, hq, ↓reduceIte] at h
    · simp at h
    · split_ifs at h <;> simp at h
    · by_cases h2 : st.ns < F.qS
      · exact h2
      · simp [h2] at h
    · split_ifs at h <;> simp at h
  · simp [hl] at h

omit [Inhabited X] in
/-- The program makes main requests only within its budget. -/
theorem na_lt_of_progAct (r : Req) (st : RelaySt Y Resp' Ys) {r' : Req'}
    (h : F.progAct r st = some (.inr r')) : st.na < F.K := by
  unfold progAct at h
  by_cases hl : st.live
  · rcases hq : (F.prog r).after st.ans with _ | ((x' | x') | r'') <;>
      simp only [hl, hq, ↓reduceIte] at h
    · simp at h
    · split_ifs at h <;> simp at h
    · split_ifs at h <;> simp at h
    · by_cases h2 : st.na < F.K
      · exact h2
      · simp [h2] at h
  · simp [hl] at h

omit [Inhabited X] in
/-- A side step at any action but a side read keeps the state. -/
theorem sideStep_of_not (sa : ℕ → Xs → Ys) (r : Req) (st : RelaySt Y Resp' Ys)
    (h : ∀ x, F.progAct r st ≠ some (.inl (.inr x))) : F.sideStep sa r st = st := by
  unfold sideStep
  rcases hp : F.progAct r st with _ | ((x | x) | r')
  · rfl
  · rfl
  · exact absurd hp (h x)
  · rfl

omit [Inhabited X] in
/-- A side step keeps the main requests, the queries and the pad sub-slots. -/
theorem counts_sideStep (sa : ℕ → Xs → Ys) (r : Req) (st : RelaySt Y Resp' Ys) :
    (F.sideStep sa r st).na = st.na ∧ (F.sideStep sa r st).nq = st.nq ∧
      (F.sideStep sa r st).np = st.np := by
  unfold sideStep
  rcases F.progAct r st with _ | ((x | x) | r') <;> exact ⟨rfl, rfl, rfl⟩

omit [Inhabited X] in
/-- Side steps keep the main requests, the queries and the pad sub-slots. -/
theorem counts_iterate_sideStep (sa : ℕ → Xs → Ys) (r : Req) :
    ∀ (j : ℕ) (st : RelaySt Y Resp' Ys),
      ((F.sideStep sa r)^[j] st).na = st.na ∧ ((F.sideStep sa r)^[j] st).nq = st.nq ∧
        ((F.sideStep sa r)^[j] st).np = st.np
  | 0, _ => ⟨rfl, rfl, rfl⟩
  | j + 1, st => by
    rw [Function.iterate_succ_apply]
    obtain ⟨h1, h2, h3⟩ := counts_iterate_sideStep sa r j (F.sideStep sa r st)
    obtain ⟨h4, h5, h6⟩ := F.counts_sideStep sa r st
    exact ⟨h1.trans h4, h2.trans h5, h3.trans h6⟩

omit [Inhabited X] in
/-- The side reads keep the main requests made. -/
theorem na_close (sa : ℕ → Xs → Ys) (r : Req) (st : RelaySt Y Resp' Ys) :
    (F.close sa r st).na = st.na :=
  (F.counts_iterate_sideStep sa r _ st).1

omit [Inhabited X] in
/-- The side reads keep the queries made. -/
theorem nq_close (sa : ℕ → Xs → Ys) (r : Req) (st : RelaySt Y Resp' Ys) :
    (F.close sa r st).nq = st.nq :=
  (F.counts_iterate_sideStep sa r _ st).2.1

omit [Inhabited X] in
/-- The side reads keep the pad sub-slots made. -/
theorem np_close (sa : ℕ → Xs → Ys) (r : Req) (st : RelaySt Y Resp' Ys) :
    (F.close sa r st).np = st.np :=
  (F.counts_iterate_sideStep sa r _ st).2.2

omit [Inhabited X] in
/-- After `j` side steps, the program either makes no side read or has made `j` more. -/
theorem iterate_sideStep_side (sa : ℕ → Xs → Ys) (r : Req) :
    ∀ (j : ℕ) (st : RelaySt Y Resp' Ys) (x : Xs),
      F.progAct r ((F.sideStep sa r)^[j] st) = some (.inl (.inr x)) →
        st.ns + j ≤ ((F.sideStep sa r)^[j] st).ns
  | 0, st, _, _ => le_rfl
  | j + 1, st, x, h => by
    rw [Function.iterate_succ_apply] at h ⊢
    by_cases hs : ∃ x', F.progAct r st = some (.inl (.inr x'))
    · obtain ⟨x', hx'⟩ := hs
      have ih := iterate_sideStep_side sa r j (F.sideStep sa r st) x h
      have hns : (F.sideStep sa r st).ns = st.ns + 1 := by
        unfold sideStep
        rw [hx']
      omega
    · push_neg at hs
      rw [F.sideStep_of_not sa r st hs] at h ⊢
      have hfix : ∀ k, (F.sideStep sa r)^[k] st = st := fun k =>
        Function.iterate_fixed (F.sideStep_of_not sa r st hs) k
      rw [hfix] at h
      exact absurd h (hs x)

omit [Inhabited X] in
/-- **After the side reads, the program's action is not a side read.** -/
theorem progAct_close_ne_side (sa : ℕ → Xs → Ys) (r : Req) (st : RelaySt Y Resp' Ys) (x : Xs) :
    F.progAct r (F.close sa r st) ≠ some (.inl (.inr x)) := fun h => by
  have h1 := F.iterate_sideStep_side sa r F.qS st x h
  have h2 := F.ns_lt_of_progAct r _ h
  unfold close at h2
  omega

omit [Inhabited X] in
/-- A main request, a query or a pad sub-slot is counted by each sub-slot. -/
theorem counts_next (r : Req) (st : RelaySt Y Resp' Ys) (a : Option Resp' × (X × Y)) :
    (F.next r st a).na + (F.next r st a).nq + (F.next r st a).np =
      st.na + st.nq + st.np + 1 := by
  unfold next
  rcases F.progAct r st with _ | ((_ | _) | _)
  · split_ifs <;> simp <;> omega
  · simp; omega
  · split_ifs <;> simp <;> omega
  · simp; omega

omit [Inhabited X] in
/-- **The sub-slots done**: the main requests, queries and pad sub-slots made. -/
theorem counts_stAt (sa : ℕ → Xs → Ys) (r : Req) (g : ℕ → Option Resp' × (X × Y)) :
    ∀ i, (F.stAt sa r g i).na + (F.stAt sa r g i).nq + (F.stAt sa r g i).np = i
  | 0 => rfl
  | i + 1 => by
    simp only [stAt]
    rw [F.na_close, F.nq_close, F.np_close, counts_next, counts_stAt sa r g i]

omit [Inhabited X] in
/-- A sub-slot keeps the main requests made at most `K`. -/
theorem na_next_le (r : Req) (st : RelaySt Y Resp' Ys) (a : Option Resp' × (X × Y))
    (h : st.na ≤ F.K) : (F.next r st a).na ≤ F.K := by
  unfold next
  rcases hp : F.progAct r st with _ | ((_ | _) | _)
  · split_ifs with h1 <;> simp <;> omega
  · simpa using h
  · split_ifs with h1 h2 <;> simp <;> omega
  · have := F.na_lt_of_progAct r st hp
    simp only
    omega

/-- Before the last sub-slot (`na + nq + np < len`), a query is made only while fewer than
`qR + qP` queries were made. -/
theorem nq_lt_of_act_inl (r : Req) (st : RelaySt Y Resp' Ys) {x : X}
    (hst : st.na + st.nq + st.np < F.len) (h : F.act r st = .inl (.inl x)) :
    st.nq < F.qR + F.qP := by
  unfold act at h
  unfold len at hst
  rcases hp : F.progAct r st with _ | ((x' | x') | r')
  · rw [hp] at h
    simp only at h
    split_ifs at h with h1 <;> first | omega | cases h
  · have := F.nq_lt_of_progAct r st hp
    omega
  · rw [hp] at h
    simp only at h
    split_ifs at h with h1 h2 <;> first | omega | cases h
  · rw [hp] at h
    simp at h

/-! ### The relayed request against a main environment -/

variable [Zero Y] [Zero Ys] [Inhabited Req']

/-- **The side reads answered by the side function.** -/
def sideSa : ℕ → Xs → Ys := fun _ x => F.side x

/-- **The relayed request `r` against main replies**: after the main requests `rs`, with
`ansM rs' r'` the main reply to `r'` after the main requests `rs'` and `H` the oracle, the state
(after the side reads, answered by the side function) and the entries (main request, stored
answer) of the first `i` sub-slots. A main request `r'` is stored as its reply with the blank
pair; a query of `x` as no reply with the pair `(x, H x)`; a pad sub-slot as the query of
`default`. -/
def runAux (ansM : List Req' → Req' → Option Resp') (H : X → Y) (r : Req) (rs : List Req') :
    ℕ → RelaySt Y Resp' Ys × List (Option Req' × (Option Resp' × (X × Y)))
  | 0 => (.init, [])
  | i + 1 =>
    let p := runAux ansM H r rs i
    let e : Option Req' × (Option Resp' × (X × Y)) := match F.act r p.1 with
      | .inl (.inl x) => (none, (none, (x, H x)))
      | .inl (.inr _) => (none, (none, (default, H default)))
      | .inr r' => (some r', (ansM (rs ++ p.2.filterMap Prod.fst) r', (default, 0)))
    (F.close F.sideSa r (F.next r p.1 e.2), p.2 ++ [e])

/-- The entries of the sub-slots of a relayed request. -/
def runEntries (ansM : List Req' → Req' → Option Resp') (H : X → Y) (r : Req) (rs : List Req') :
    List (Option Req' × (Option Resp' × (X × Y))) :=
  (F.runAux ansM H r rs F.len).2

/-- **The reply of a relayed request** against main replies. -/
def runReply (ansM : List Req' → Req' → Option Resp') (H : X → Y) (r : Req) (rs : List Req') :
    Option Resp :=
  F.reply r (F.runAux ansM H r rs F.len).1

omit [Zero Y] [Zero Ys] in
/-- **The side answers fed to a program**, in order. -/
def sideVals (ans : List ((Y ⊕ Ys) ⊕ Option Resp')) : List Ys :=
  ans.filterMap fun a => match a with
    | .inl (.inr y) => some y
    | _ => none

/-- **The side vector of a state**: its `k`-th side answer at `k`, `0` past them. -/
def sideVec (st : RelaySt Y Resp' Ys) : Fin F.qS → Ys :=
  fun k => (sideVals st.ans).getD k 0

/-- **The side vector of a relayed request**: its side answers in order. -/
def runSide (ansM : List Req' → Req' → Option Resp') (H : X → Y) (r : Req) (rs : List Req') :
    Fin F.qS → Ys :=
  F.sideVec (F.runAux ansM H r rs F.len).1

omit [Inhabited Req'] in
/-- **The run of the program of `r` for `i` sub-slots has `i` entries.** -/
theorem length_runAux (ansM : List Req' → Req' → Option Resp') (H : X → Y) (r : Req)
    (rs : List Req') : ∀ i, (F.runAux ansM H r rs i).2.length = i
  | 0 => rfl
  | i + 1 => by simp [runAux, length_runAux ansM H r rs i]

/-! ### The schedule of a run -/

/-- **The kind of a block**: the sub-slots that one slot of the relayed distinguisher becomes. -/
inductive Blk
  /-- A query slot within the budget: one sub-slot per query pair. -/
  | qry
  /-- A query slot over the budget, or a request after the `Q`-th: one idle request. -/
  | idle
  /-- A relayed request. -/
  | rel
deriving DecidableEq

/-- The block of a slot with entry `e` (`none` for a query, `some r` for a request), after `qb`
query slots and `rb` requests: a query within the budget `b`, a request numbered below `Q`, or
idle. -/
def blk (b Q qb rb : ℕ) {Req : Type} : Option Req → Blk
  | none => if qb < b then .qry else .idle
  | some _ => if rb < Q then .rel else .idle

/-- The number of sub-slots of a block, with `n` query pairs. -/
def blkLen (n : ℕ) : Blk → ℕ
  | .qry => n
  | .idle => 1
  | .rel => F.len

/-- The block of entry `i` of the entry list `es`. -/
def blkAt (b Q : ℕ) (es : List (Option Req)) (i : ℕ) : Blk :=
  blk b Q ((es.take i).countP Option.isNone) ((es.take i).countP Option.isSome) (es.getD i none)

/-- **The first sub-slot of block `i`**: the sub-slots of the blocks before it. -/
def startAt (n b Q : ℕ) (es : List (Option Req)) (i : ℕ) : ℕ :=
  ∑ i' ∈ range i, F.blkLen n (blkAt b Q es i')

/-- **The state of the schedule** after some blocks: the query slots and requests so far, the
entries (main request, stored answer) of the sub-slots so far, and the side vectors of the
blocks so far. -/
structure SchedSt (X Y Req' Resp' : Type) (V : Type := Unit) where
  /-- The query slots. -/
  qb : ℕ
  /-- The requests. -/
  rb : ℕ
  /-- The entries of the sub-slots. -/
  out : List (Option Req' × (Option Resp' × (X × Y)))
  /-- The side vectors of the blocks. -/
  side : List V

/-- The entry of an idle sub-slot after the entries `out`: the idle request and its reply. -/
def idleEntry (ansM : List Req' → Req' → Option Resp')
    (out : List (Option Req' × (Option Resp' × (X × Y)))) : Option Req' × (Option Resp' × (X × Y)) :=
  (some F.idle, (ansM (out.filterMap Prod.fst) F.idle, (default, 0)))

/-- **One block of the schedule**: a query block adds `n` blank entries, an idle block one idle
request, a relayed request its sub-slots. -/
def schedStep (n b Q : ℕ) (ansM : List Req' → Req' → Option Resp') (H : X → Y)
    (st : SchedSt X Y Req' Resp' (Fin F.qS → Ys)) (e : Option Req) :
    SchedSt X Y Req' Resp' (Fin F.qS → Ys) :=
  match e with
  | none =>
    if st.qb < b then ⟨st.qb + 1, st.rb, st.out ++ List.replicate n (none, (none, (default, 0))),
      st.side ++ [0]⟩
    else ⟨st.qb + 1, st.rb, st.out ++ [F.idleEntry ansM st.out], st.side ++ [0]⟩
  | some r =>
    if st.rb < Q then ⟨st.qb, st.rb + 1, st.out ++ F.runEntries ansM H r (st.out.filterMap
        Prod.fst),
      st.side ++ [F.runSide ansM H r (st.out.filterMap Prod.fst)]⟩
    else ⟨st.qb, st.rb + 1, st.out ++ [F.idleEntry ansM st.out], st.side ++ [0]⟩

/-- **The schedule of the entry list `es`**. -/
def sched (n b Q : ℕ) (ansM : List Req' → Req' → Option Resp') (H : X → Y)
    (es : List (Option Req)) : SchedSt X Y Req' Resp' (Fin F.qS → Ys) :=
  es.foldl (F.schedStep n b Q ansM H) ⟨0, 0, [], []⟩

/-- **The entries `out` followed by `k` trailing idle sub-slots.** -/
def tailEntries (ansM : List Req' → Req' → Option Resp')
    (out : List (Option Req' × (Option Resp' × (X × Y)))) :
    ℕ → List (Option Req' × (Option Resp' × (X × Y)))
  | 0 => out
  | k + 1 => tailEntries ansM out k ++ [F.idleEntry ansM (tailEntries ansM out k)]

/-- The block of entries a slot with entry `e` adds to the schedule state `st`. -/
def blockOf (n b Q : ℕ) (ansM : List Req' → Req' → Option Resp') (H : X → Y)
    (st : SchedSt X Y Req' Resp' (Fin F.qS → Ys)) (e : Option Req) :
    List (Option Req' × (Option Resp' × (X × Y))) :=
  match e with
  | none => if st.qb < b then List.replicate n (none, (none, (default, 0))) else [F.idleEntry ansM st.out]
  | some r => if st.rb < Q then F.runEntries ansM H r (st.out.filterMap Prod.fst)
    else [F.idleEntry ansM st.out]

/-- The side vector a slot with entry `e` adds to the schedule state `st`: the relayed request's,
`0` for any other block. -/
def sideOf (b Q : ℕ) (ansM : List Req' → Req' → Option Resp') (H : X → Y)
    (st : SchedSt X Y Req' Resp' (Fin F.qS → Ys)) (e : Option Req) : Fin F.qS → Ys :=
  match e with
  | none => 0
  | some r => if st.rb < Q then F.runSide ansM H r (st.out.filterMap Prod.fst) else 0

/-- **The main requests after relaying the requests `rs`**: request number `c` adds the main
requests of its relay while `c < Q`, the idle request after. -/
def mainReqs (Q : ℕ) (ansM : List Req' → Req' → Option Resp') (H : X → Y) (rs : List Req) :
    List Req' :=
  (rs.foldl (fun (p : List Req' × ℕ) r =>
    (if p.2 < Q then p.1 ++ (F.runEntries ansM H r p.1).filterMap Prod.fst else p.1 ++ [F.idle],
      p.2 + 1)) ([], 0)).1

/-! ### Reading the record of the relayed distinguisher -/

/-- **The started slots of a record**, in order: the entries of its leading filled slots. -/
def recList {Req : Type} {m : ℕ} (rec : Fin m → Option (Option Req)) : List (Option Req) :=
  ((List.finRange m).takeWhile fun i => (rec i).isSome).map fun i => (rec i).getD none

/-- The entries of the slots below `i` of a record. -/
def recPrefix {Req : Type} {m : ℕ} (rec : Fin m → Option (Option Req)) (i : ℕ) :
    List (Option Req) :=
  ((List.finRange m).take i).map fun i' => (rec i').getD none

/-- The side vector of slot `j`, `0` past the side store. -/
def vecAt {m : ℕ} (side : Fin m → Fin F.qS → Ys) (j : ℕ) : Fin F.qS → Ys :=
  if h : j < m then side ⟨j, h⟩ else 0

/-- **The side reads answered from a side vector**: the `k`-th side read by its `k`-th entry,
`0` past them. -/
def vecSa (v : Fin F.qS → Ys) : ℕ → Xs → Ys :=
  fun k _ => if h : k < F.qS then v ⟨k, h⟩ else 0

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
/-- **The side reads answered from a side vector do not read the side point.** -/
theorem vecSa_point (v : Fin F.qS → Ys) : ∀ k x x', F.vecSa v k x = F.vecSa v k x' :=
  fun _ _ _ => rfl

/-- The stored answer of sub-slot `t`, blank past the store. -/
def storeAt {S : ℕ} (store : Fin S → Option Resp' × (X × Y)) (t : ℕ) : Option Resp' × (X × Y) :=
  if h : t < S then store ⟨t, h⟩ else (none, (default, 0))

/-- **The current block** of a record at sub-slot `t`: the last started slot `j` and the
sub-slot `t - startAt j` within its block, if `t` lies in that block. -/
def curBlk (n b Q : ℕ) {m : ℕ} (rec : Fin m → Option (Option Req)) (t : ℕ) : Option (ℕ × ℕ) :=
  if 0 < (recList rec).length ∧
      F.startAt n b Q (recList rec) ((recList rec).length - 1) ≤ t ∧
      t < F.startAt n b Q (recList rec) ((recList rec).length - 1) +
        F.blkLen n (blkAt b Q (recList rec) ((recList rec).length - 1)) then
    some ((recList rec).length - 1, t - F.startAt n b Q (recList rec) ((recList rec).length - 1))
  else none

end MultiRelay

/-- **The action of a sub-slot** of the relayed distinguisher: a query of the distinguisher's
query pair `i`, a relay query of `x`, a side read of `x`, or the main request `r'`. -/
inductive SubAct (X Req' : Type) (n : ℕ)
  /-- A query of the distinguisher's query pair `i`. -/
  | pair (i : Fin n)
  /-- A query of `x` by the relay. -/
  | query (x : X)
  /-- The main request `r'`. -/
  | ask (r' : Req')

namespace MultiRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)
  [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req']

/-- **The action at sub-slot `t`** given the record, the stored answers and the side store: in a
query block, the query of the pair numbered by the sub-slot; in a relayed request, the relay's
action on the answers stored in the block so far, its side reads answered from the block's side
vector; otherwise the idle request. -/
def actAt (n b Q : ℕ) {m S : ℕ} (rec : Fin m → Option (Option Req))
    (store : Fin S → Option Resp' × (X × Y)) (side : Fin m → Fin F.qS → Ys) (t : ℕ) :
    SubAct X Req' n :=
  match F.curBlk n b Q rec t with
  | none => .ask F.idle
  | some (j, sub) =>
    match blkAt b Q (recList rec) j, (recList rec).getD j none with
    | .qry, _ => if h : sub < n then .pair ⟨sub, h⟩ else .ask F.idle
    | .rel, some r =>
      match F.act r (F.stAt (F.vecSa (F.vecAt side j)) r
          (fun k => storeAt store (F.startAt n b Q (recList rec) j + k)) sub) with
      | .inl (.inl x) => .query x
      | .inl (.inr _) => .query default
      | .inr r' => .ask r'
    | _, _ => .ask F.idle

/-- Whether a sub-slot asks a main request. -/
def _root_.GordieHowe.Quantum.SubAct.isAsk {n : ℕ} : SubAct X Req' n → Bool
  | .ask _ => true
  | _ => false

/-- The distinguisher's query pair a sub-slot queries, if any. -/
def _root_.GordieHowe.Quantum.SubAct.pairIdx {n : ℕ} : SubAct X Req' n → Option (Fin n)
  | .pair i => some i
  | _ => none

/-- **The reply of the last started slot**, when it is a relayed request: the relay's reply on its
stored answers. -/
def lastReply (n b Q : ℕ) {m S : ℕ} (rec : Fin m → Option (Option Req))
    (store : Fin S → Option Resp' × (X × Y)) (side : Fin m → Fin F.qS → Ys) :
    Option (Option Resp) :=
  if 0 < (recList rec).length then
    match blkAt b Q (recList rec) ((recList rec).length - 1),
      (recList rec).getD ((recList rec).length - 1) none with
    | .rel, some r => some (F.reply r (F.stAt (F.vecSa (F.vecAt side ((recList rec).length - 1)))
        r (fun k => storeAt store (F.startAt n b Q (recList rec) ((recList rec).length - 1) + k))
        F.len))
    | _, _ => none
  else none

/-! ### The side answers a state reads -/

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- A side step makes at least the side reads made. -/
theorem ns_le_sideStep (sa : ℕ → Xs → Ys) (r : Req) (st : RelaySt Y Resp' Ys) :
    st.ns ≤ (F.sideStep sa r st).ns := by
  unfold sideStep
  rcases F.progAct r st with _ | ((x | x) | r') <;> simp

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem ns_le_iterate_sideStep (sa : ℕ → Xs → Ys) (r : Req) :
    ∀ (j : ℕ) (st : RelaySt Y Resp' Ys), st.ns ≤ ((F.sideStep sa r)^[j] st).ns
  | 0, _ => le_rfl
  | j + 1, st => by
    rw [Function.iterate_succ_apply]
    exact (F.ns_le_sideStep sa r st).trans (ns_le_iterate_sideStep sa r j _)

omit [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- A sub-slot keeps the side reads made. -/
theorem ns_next (r : Req) (st : RelaySt Y Resp' Ys) (a : Option Resp' × (X × Y)) :
    (F.next r st a).ns = st.ns := by
  unfold next
  rcases F.progAct r st with _ | ((_ | _) | _)
  · split_ifs <;> rfl
  · rfl
  · split_ifs <;> rfl
  · rfl

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **A side step reads the side answers only below the side reads it makes.** -/
theorem sideStep_congr_sa {sa sa' : ℕ → Xs → Ys} {N : ℕ} (h : ∀ k < N, ∀ x, sa' k x = sa k x)
    (r : Req) (st : RelaySt Y Resp' Ys) (hN : (F.sideStep sa r st).ns ≤ N) :
    F.sideStep sa' r st = F.sideStep sa r st := by
  unfold sideStep at hN ⊢
  rcases hp : F.progAct r st with _ | ((x | x) | r')
  · rfl
  · rfl
  · simp only [hp] at hN ⊢
    rw [h st.ns (by omega) x]
  · rfl

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem iterate_sideStep_congr_sa {sa sa' : ℕ → Xs → Ys} {N : ℕ}
    (h : ∀ k < N, ∀ x, sa' k x = sa k x) (r : Req) :
    ∀ (j : ℕ) (st : RelaySt Y Resp' Ys), ((F.sideStep sa r)^[j] st).ns ≤ N →
      (F.sideStep sa' r)^[j] st = (F.sideStep sa r)^[j] st
  | 0, _, _ => rfl
  | j + 1, st, hN => by
    rw [Function.iterate_succ_apply] at hN ⊢
    rw [Function.iterate_succ_apply]
    have h1 : (F.sideStep sa r st).ns ≤ N :=
      (F.ns_le_iterate_sideStep sa r j _).trans hN
    rw [F.sideStep_congr_sa h r st h1]
    exact iterate_sideStep_congr_sa h r j _ hN

omit [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **The state after `i` sub-slots reads the side answers only below its side reads.** -/
theorem stAt_congr_sa {sa sa' : ℕ → Xs → Ys} {N : ℕ} (h : ∀ k < N, ∀ x, sa' k x = sa k x)
    (r : Req) (g : ℕ → Option Resp' × (X × Y)) :
    ∀ i, (F.stAt sa r g i).ns ≤ N → F.stAt sa' r g i = F.stAt sa r g i
  | 0, _ => rfl
  | i + 1, hN => by
    simp only [stAt] at hN ⊢
    have h1 : (F.stAt sa r g i).ns ≤ N := by
      have := F.ns_le_iterate_sideStep sa r F.qS (F.next r (F.stAt sa r g i) (g i))
      rw [F.ns_next] at this
      exact this.trans hN
    rw [stAt_congr_sa h r g i h1]
    exact F.iterate_sideStep_congr_sa h r _ _ hN

omit [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- The state before the side reads after sub-slot `i - 1` reads the side answers only below its
side reads. -/
theorem preSt_congr_sa {sa sa' : ℕ → Xs → Ys} {N : ℕ} (h : ∀ k < N, ∀ x, sa' k x = sa k x)
    (r : Req) (g : ℕ → Option Resp' × (X × Y)) :
    ∀ i, (F.preSt sa r g i).ns ≤ N → F.preSt sa' r g i = F.preSt sa r g i
  | 0, _ => rfl
  | i + 1, hN => by
    simp only [preSt] at hN ⊢
    rw [F.ns_next] at hN
    rw [F.stAt_congr_sa h r g i hN]

/-- **The state after sub-slot `sub - 1` and `i` of the side reads after it.** -/
def pendSt (sa : ℕ → Xs → Ys) (r : Req) (g : ℕ → Option Resp' × (X × Y)) (sub i : ℕ) :
    RelaySt Y Resp' Ys :=
  (F.sideStep sa r)^[i] (F.preSt sa r g sub)

omit [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem pendSt_congr_sa {sa sa' : ℕ → Xs → Ys} {N : ℕ} (h : ∀ k < N, ∀ x, sa' k x = sa k x)
    (r : Req) (g : ℕ → Option Resp' × (X × Y)) (sub i : ℕ) (hN : (F.pendSt sa r g sub i).ns ≤ N) :
    F.pendSt sa' r g sub i = F.pendSt sa r g sub i := by
  unfold pendSt at hN ⊢
  have h1 : (F.preSt sa r g sub).ns ≤ N :=
    (F.ns_le_iterate_sideStep sa r i _).trans hN
  rw [F.preSt_congr_sa h r g sub h1]
  exact F.iterate_sideStep_congr_sa h r i _ hN

/-- **Two states alike until `K` side reads**: equal, or both past `K` side reads. -/
def NsAgree (K : ℕ) (st st' : RelaySt Y Resp' Ys) : Prop :=
  st = st' ∨ (K < st.ns ∧ K < st'.ns)

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem nsAgree_sideStep {sa sa' : ℕ → Xs → Ys} {K : ℕ} (h : ∀ k < K, ∀ x, sa' k x = sa k x)
    (r : Req) {st st' : RelaySt Y Resp' Ys} (hst : NsAgree K st st') :
    NsAgree K (F.sideStep sa r st) (F.sideStep sa' r st') := by
  rcases hst with rfl | ⟨h1, h2⟩
  · unfold sideStep
    rcases hp : F.progAct r st with _ | ((x | x) | r')
    · exact Or.inl rfl
    · exact Or.inl rfl
    · simp only
      by_cases hK : st.ns < K
      · rw [h st.ns hK x]
        exact Or.inl rfl
      · exact Or.inr ⟨by simp only; omega, by simp only; omega⟩
    · exact Or.inl rfl
  · exact Or.inr ⟨lt_of_lt_of_le h1 (F.ns_le_sideStep sa r st),
      lt_of_lt_of_le h2 (F.ns_le_sideStep sa' r st')⟩

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem nsAgree_iterate_sideStep {sa sa' : ℕ → Xs → Ys} {K : ℕ}
    (h : ∀ k < K, ∀ x, sa' k x = sa k x) (r : Req) :
    ∀ (j : ℕ) {st st' : RelaySt Y Resp' Ys}, NsAgree K st st' →
      NsAgree K ((F.sideStep sa r)^[j] st) ((F.sideStep sa' r)^[j] st')
  | 0, _, _, hst => hst
  | j + 1, _, _, hst => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact nsAgree_iterate_sideStep h r j (F.nsAgree_sideStep h r hst)

omit [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem nsAgree_next {K : ℕ} (r : Req) {st st' : RelaySt Y Resp' Ys} (a : Option Resp' × (X × Y))
    (hst : NsAgree K st st') : NsAgree K (F.next r st a) (F.next r st' a) := by
  rcases hst with rfl | ⟨h1, h2⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨by rw [F.ns_next]; exact h1, by rw [F.ns_next]; exact h2⟩

omit [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem nsAgree_stAt {sa sa' : ℕ → Xs → Ys} {K : ℕ} (h : ∀ k < K, ∀ x, sa' k x = sa k x)
    (r : Req) (g : ℕ → Option Resp' × (X × Y)) :
    ∀ i, NsAgree K (F.stAt sa r g i) (F.stAt sa' r g i)
  | 0 => Or.inl rfl
  | i + 1 => F.nsAgree_iterate_sideStep h r F.qS (F.nsAgree_next r (g i) (nsAgree_stAt h r g i))

omit [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem nsAgree_pendSt {sa sa' : ℕ → Xs → Ys} {K : ℕ} (h : ∀ k < K, ∀ x, sa' k x = sa k x)
    (r : Req) (g : ℕ → Option Resp' × (X × Y)) (sub i : ℕ) :
    NsAgree K (F.pendSt sa r g sub i) (F.pendSt sa' r g sub i) := by
  unfold pendSt
  refine F.nsAgree_iterate_sideStep h r i ?_
  cases sub with
  | zero => exact Or.inl rfl
  | succ j => exact F.nsAgree_next r (g j) (F.nsAgree_stAt h r g j)

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem ns_le_qS_sideStep (sa : ℕ → Xs → Ys) (r : Req) {st : RelaySt Y Resp' Ys}
    (h : st.ns ≤ F.qS) : (F.sideStep sa r st).ns ≤ F.qS := by
  unfold sideStep
  rcases hp : F.progAct r st with _ | ((x | x) | r')
  · exact h
  · exact h
  · have := F.ns_lt_of_progAct r st hp
    simp only
    omega
  · exact h

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem ns_le_qS_iterate_sideStep (sa : ℕ → Xs → Ys) (r : Req) :
    ∀ (j : ℕ) {st : RelaySt Y Resp' Ys}, st.ns ≤ F.qS → ((F.sideStep sa r)^[j] st).ns ≤ F.qS
  | 0, _, h => h
  | j + 1, _, h => by
    rw [Function.iterate_succ_apply]
    exact ns_le_qS_iterate_sideStep sa r j (F.ns_le_qS_sideStep sa r h)

omit [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **At most `qS` side reads** are made. -/
theorem ns_le_qS_pendSt (sa : ℕ → Xs → Ys) (r : Req) (g : ℕ → Option Resp' × (X × Y))
    (sub i : ℕ) : (F.pendSt sa r g sub i).ns ≤ F.qS := by
  have hst : ∀ j, (F.stAt sa r g j).ns ≤ F.qS := by
    intro j
    induction j with
    | zero => exact Nat.zero_le _
    | succ j ih =>
      exact F.ns_le_qS_iterate_sideStep sa r F.qS (by rw [F.ns_next]; exact ih)
  unfold pendSt
  refine F.ns_le_qS_iterate_sideStep sa r i ?_
  cases sub with
  | zero => exact Nat.zero_le _
  | succ j => rw [preSt, F.ns_next]; exact hst j

omit [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **All `qS` side reads made does not read the last side answer**: side answers alike below
`qS - 1` make all `qS` side reads too. -/
theorem pendSt_ns_eq_qS_congr {sa sa' : ℕ → Xs → Ys} (h : ∀ k < F.qS - 1, ∀ x, sa' k x = sa k x)
    (r : Req) (g : ℕ → Option Resp' × (X × Y)) (sub i : ℕ) (hq : (F.pendSt sa r g sub i).ns = F.qS) :
    (F.pendSt sa' r g sub i).ns = F.qS := by
  have hle := F.ns_le_qS_pendSt sa' r g sub i
  rcases F.nsAgree_pendSt h r g sub i with he | ⟨-, h2⟩
  · rw [← he]
    exact hq
  · omega

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
/-- **A side vector changed at entry `k`** answers the other side reads alike. -/
theorem vecSa_update_of_ne (v : Fin F.qS → Ys) {k : ℕ} (hk : k < F.qS) (y : Ys) {k' : ℕ}
    (hne : k' ≠ k) (x : Xs) :
    F.vecSa (Function.update v ⟨k, hk⟩ y) k' x = F.vecSa v k' x := by
  unfold vecSa
  split_ifs with h
  · exact Function.update_of_ne (fun e => hne (by simpa using congrArg Fin.val e)) _ _
  · rfl

/-- **The relayed request at the clock after a sub-slot**: the last started slot `j`, when it is
a relayed request `r` whose block has `sub` of its sub-slots done, `1 ≤ sub ≤ len`. -/
def curRel (n b Q : ℕ) {m : ℕ} (rec : Fin m → Option (Option Req)) (t : ℕ) :
    Option (ℕ × Req × ℕ) :=
  if 0 < (recList rec).length then
    match blkAt b Q (recList rec) ((recList rec).length - 1),
      (recList rec).getD ((recList rec).length - 1) none with
    | .rel, some r =>
      if F.startAt n b Q (recList rec) ((recList rec).length - 1) < t ∧
          t ≤ F.startAt n b Q (recList rec) ((recList rec).length - 1) + F.len then
        some ((recList rec).length - 1, r,
          t - F.startAt n b Q (recList rec) ((recList rec).length - 1))
      else none
    | _, _ => none
  else none

/-- **The slot to start at sub-slot `t`**: the slot `i` whose earlier slots have started and whose
block starts at `t`. -/
def fillAt (n b Q : ℕ) {m : ℕ} (rec : Fin m → Option (Option Req)) (t : ℕ) : Option (Fin m) :=
  (List.finRange m).find? fun i =>
    decide ((∀ i' : Fin m, i' < i → (rec i').isSome) ∧ F.startAt n b Q (recPrefix rec i) i = t)

end MultiRelay

/-! ### The relayed distinguisher -/

/-- **The workspace of the relayed distinguisher**: the registers `inner` of the distinguisher, the
record `record` of its slots (`none` before a slot starts, then `some` of its entry: `none` for a
query, `some r` for the request `r`), the stored answers of the sub-slots, the side store (one
entry per slot, the side vector of a relayed request), and the number of sub-slots done. -/
@[ext]
structure RelayW (Inner Req Resp' X Y : Type) (m S : ℕ) (Ys : Type := Unit) where
  /-- The distinguisher's registers. -/
  inner : Inner
  /-- The record of the distinguisher's slots. -/
  record : Fin m → Option (Option Req)
  /-- The stored answers of the sub-slots. -/
  store : Fin S → Option Resp' × (X × Y)
  /-- The side store: one entry per slot. -/
  side : Fin m → Ys
  /-- The sub-slots done. -/
  time : Fin (S + 1)

namespace RelayW

/-- The workspace as its parts. -/
def equivProd (Inner Req Resp' X Y : Type) (m S : ℕ) (Ys : Type) :
    RelayW Inner Req Resp' X Y m S Ys ≃
      Inner × (Fin m → Option (Option Req)) × (Fin S → Option Resp' × (X × Y)) ×
        (Fin m → Ys) × Fin (S + 1) where
  toFun w := (w.inner, w.record, w.store, w.side, w.time)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {Inner Req Resp' X Y Ys : Type} {m S : ℕ}

instance [Fintype Inner] [Fintype Req] [Fintype Resp'] [Fintype X] [Fintype Y] [Fintype Ys] :
    Fintype (RelayW Inner Req Resp' X Y m S Ys) :=
  Fintype.ofEquiv _ (equivProd Inner Req Resp' X Y m S Ys).symm

instance [DecidableEq Inner] [DecidableEq Req] [DecidableEq Resp'] [DecidableEq X] [DecidableEq Y]
    [DecidableEq Ys] : DecidableEq (RelayW Inner Req Resp' X Y m S Ys) :=
  haveI : DecidableEq (Fin m → Option (Option Req)) := inferInstance
  haveI : DecidableEq (Fin S → Option Resp' × (X × Y)) := inferInstance
  haveI : DecidableEq (Fin m → Ys) := inferInstance
  Equiv.decidableEq (equivProd Inner Req Resp' X Y m S Ys)

end RelayW

/-- **The registers of the relayed distinguisher**: its workspace (`RelayW`), a main request
register, a main response register and one query pair. -/
abbrev RelayReg (W X Y Req Resp Req' Resp' : Type) (n m S : ℕ) (Ys : Type := Unit) : Type :=
  DReg (RelayW (DReg W n X Y Req Resp) Req Resp' X Y m S Ys) 1 X Y Req' Resp'

/-- The registers of the relayed distinguisher beside the distinguisher's. -/
abbrev RelayRest (X Y Req Req' Resp' : Type) (m S : ℕ) (Ys : Type := Unit) : Type :=
  (Fin m → Option (Option Req)) × (Fin S → Option Resp' × (X × Y)) × (Fin m → Ys) ×
    Fin (S + 1) × Req' × Option Resp' × (Fin 1 → X × Y)

instance {X Y Req Req' Resp' Ys : Type} {m S : ℕ} [DecidableEq X] [DecidableEq Y] [DecidableEq Req]
    [DecidableEq Req'] [DecidableEq Resp'] [DecidableEq Ys] :
    DecidableEq (RelayRest X Y Req Req' Resp' m S Ys) :=
  @instDecidableEqProd _ _ inferInstance (@instDecidableEqProd _ _ inferInstance
    (@instDecidableEqProd _ _ inferInstance (@instDecidableEqProd _ _ inferInstance
      (@instDecidableEqProd _ _ inferInstance (@instDecidableEqProd _ _ inferInstance
        inferInstance)))))

/-- The registers of the relayed distinguisher as the distinguisher's and the rest. -/
def relaySplit (W X Y Req Resp Req' Resp' : Type) (n m S : ℕ) (Ys : Type := Unit) :
    RelayReg W X Y Req Resp Req' Resp' n m S Ys ≃
      DReg W n X Y Req Resp × RelayRest X Y Req Req' Resp' m S Ys where
  toFun d := (d.1.1.inner, d.1.1.record, d.1.1.store, d.1.1.side, d.1.1.time, d.1.2.1, d.1.2.2,
    d.2)
  invFun p := ((⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1⟩, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1),
    p.2.2.2.2.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

namespace Distinguisher

variable {W X Y Req Resp Req' Resp' Xs Ys : Type} [Fintype W] [DecidableEq W] [Fintype X]
  [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Inhabited X] [Inhabited Req'] [AddGroup Y] [Zero Ys] {n m : ℕ}
  (D : Distinguisher W X Y Req Resp n m) (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (b Q : ℕ)

/-- **The number of slots of the relayed distinguisher**: `m * max n F.len`, which bounds the
sub-slots of the blocks of `m` slots (`MultiRelay.startAt_le`). -/
abbrev relaySlots (n m : ℕ) (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) : ℕ := m * max n F.len

/-- **The number of slots of the relayed distinguisher from the relay's numbers**: `relaySlots`
at `K` main requests, `qR` oracle queries and `qP` pad sub-slots per relayed request. The shape
of `Distinguisher.relay` is its workspace `RelayW` at these slots and `Fin qS → Ys`. -/
@[reducible] def relaySlotsS (n m K qR qP : ℕ) : ℕ := m * max n (K + qR + qP)

theorem relaySlots_eq_relaySlotsS (n m : ℕ) (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) :
    relaySlots n m F = relaySlotsS n m F.K F.qR F.qP :=
  rfl

local notation "RR" => RelayReg W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)

/-- **The set-up of a sub-slot**, before it: a query of the distinguisher's pair `i` exchanges
that pair with the query pair; a relay query of `x` writes `x` into the blank query input; a
main request writes `r'` into the blank main request register. -/
def setupFun (d : RR) : RR :=
  match F.actAt n b Q d.1.1.record d.1.1.store d.1.1.side d.1.1.time with
  | .pair i => ((⟨(d.1.1.inner.1, Function.update d.1.1.inner.2 i (d.2 0)), d.1.1.record, d.1.1.store,
      d.1.1.side, d.1.1.time⟩, d.1.2.1, d.1.2.2), fun _ => d.1.1.inner.2 i)
  | .query x => ((d.1.1, d.1.2.1, d.1.2.2), fun _ => (Equiv.swap default x (d.2 0).1, (d.2 0).2))
  | .ask r' => ((d.1.1, Equiv.swap default r' d.1.2.1, d.1.2.2), d.2)

theorem fin1_funext {α : Type} {f g : Fin 1 → α} (h : f 0 = g 0) : f = g :=
  funext fun i => by rw [Subsingleton.elim i 0]; exact h

theorem setupFun_setupFun (d : RR) : setupFun F b Q (setupFun F b Q d) = d := by
  obtain ⟨⟨⟨⟨inn, ps⟩, rec, store, side, t⟩, rq, rs⟩, pr⟩ := d
  unfold setupFun
  rcases h : F.actAt n b Q rec store side t with i | x | r'
  · simp only [h]
    refine Prod.ext (Prod.ext ?_ rfl) (fin1_funext (by simp))
    simp
  · simp only [h]
    refine Prod.ext rfl (fin1_funext ?_)
    simp
  · simp only [h]
    simp

/-- The set-up keeps the distinguisher's workspace, request and response registers. -/
theorem setupFun_inner_fst (d : RR) : (setupFun F b Q d).1.1.inner.1 = d.1.1.inner.1 := by
  unfold setupFun
  split <;> rfl

/-- The set-up as a permutation. -/
def setupPerm : Equiv.Perm RR :=
  Function.Involutive.toPerm (setupFun F b Q) (setupFun_setupFun F b Q)

/-- **The tear-down of a sub-slot**, after it: a query of the distinguisher's pair `i` exchanges
the pairs back; a relay query stores the query pair (queried) and leaves the blank pair; a main
request stores the main reply, leaves the blank response register and clears the main request
register. -/
def teardownFun (d : RR) : RR :=
  match F.actAt n b Q d.1.1.record d.1.1.store d.1.1.side d.1.1.time with
  | .pair i => ((⟨(d.1.1.inner.1, Function.update d.1.1.inner.2 i (d.2 0)), d.1.1.record,
      d.1.1.store, d.1.1.side, d.1.1.time⟩, d.1.2.1, d.1.2.2), fun _ => d.1.1.inner.2 i)
  | .query _ =>
    if h : (d.1.1.time : ℕ) < relaySlots n m F then
      ((⟨d.1.1.inner, d.1.1.record, Function.update d.1.1.store ⟨d.1.1.time, h⟩
          ((d.1.1.store ⟨d.1.1.time, h⟩).1, d.2 0), d.1.1.side, d.1.1.time⟩, d.1.2.1, d.1.2.2),
        fun _ => (d.1.1.store ⟨d.1.1.time, h⟩).2)
    else d
  | .ask r' =>
    if h : (d.1.1.time : ℕ) < relaySlots n m F then
      ((⟨d.1.1.inner, d.1.1.record, Function.update d.1.1.store ⟨d.1.1.time, h⟩
          (d.1.2.2, (d.1.1.store ⟨d.1.1.time, h⟩).2), d.1.1.side, d.1.1.time⟩,
        Equiv.swap default r' d.1.2.1, (d.1.1.store ⟨d.1.1.time, h⟩).1), d.2)
    else ((d.1.1, Equiv.swap default r' d.1.2.1, d.1.2.2), d.2)

end Distinguisher

namespace MultiRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)
  [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req']

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- The state of a relayed request after `i` sub-slots reads only the first `i` stored answers. -/
theorem stAt_congr (sa : ℕ → Xs → Ys) (r : Req) {g g' : ℕ → Option Resp' × (X × Y)} :
    ∀ {i : ℕ}, (∀ k < i, g k = g' k) → F.stAt sa r g i = F.stAt sa r g' i
  | 0, _ => rfl
  | i + 1, h => by
    rw [stAt, stAt, stAt_congr sa r fun k hk => h k (by omega), h i (by omega)]

omit [Inhabited X] [Zero Ys] [Inhabited Req'] in
/-- The current block, when there is one, contains the sub-slot. -/
theorem curBlk_eq_some {n b Q m : ℕ} {rec : Fin m → Option (Option Req)} {t j sub : ℕ}
    (h : F.curBlk n b Q rec t = some (j, sub)) :
    j = (recList rec).length - 1 ∧ F.startAt n b Q (recList rec) j + sub = t ∧
      sub < F.blkLen n (blkAt b Q (recList rec) j) := by
  unfold curBlk at h
  split_ifs at h with hc
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by omega, by omega⟩

/-- **The action of sub-slot `t` reads only the answers stored before `t`.** -/
theorem actAt_update_store {n b Q m S : ℕ} (rec : Fin m → Option (Option Req))
    (store : Fin S → Option Resp' × (X × Y)) (side : Fin m → Fin F.qS → Ys) {t : ℕ} (ht : t < S)
    (v : Option Resp' × (X × Y)) :
    F.actAt n b Q rec (Function.update store ⟨t, ht⟩ v) side t =
      F.actAt n b Q rec store side t := by
  unfold actAt
  rcases hc : F.curBlk n b Q rec t with _ | ⟨j, sub⟩
  · rfl
  · obtain ⟨-, hs, -⟩ := F.curBlk_eq_some hc
    simp only
    have hst : ∀ r, F.stAt (F.vecSa (F.vecAt side j)) r
        (fun k => storeAt (Function.update store ⟨t, ht⟩ v) (F.startAt n b Q (recList rec) j + k))
          sub =
        F.stAt (F.vecSa (F.vecAt side j)) r
          (fun k => storeAt store (F.startAt n b Q (recList rec) j + k)) sub := by
      intro r
      refine F.stAt_congr _ r fun k hk => ?_
      unfold storeAt
      split_ifs with h1
      · rw [Function.update_of_ne (fun e => by simp [Fin.ext_iff] at e; omega)]
      · rfl
    simp only [hst]

end MultiRelay

namespace Distinguisher

variable {W X Y Req Resp Req' Resp' Xs Ys : Type} [DecidableEq X] [DecidableEq Req']
  [DecidableEq Req] [DecidableEq Resp] [Inhabited X] [Inhabited Req'] [AddGroup Y] [Zero Ys]
  {n m : ℕ} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (b Q : ℕ)

local notation "RR" => RelayReg W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)

theorem teardownFun_teardownFun (d : RR) : teardownFun F b Q (teardownFun F b Q d) = d := by
  obtain ⟨⟨⟨⟨inn, ps⟩, rec, store, side, t⟩, rq, rs⟩, pr⟩ := d
  unfold teardownFun
  rcases h : F.actAt n b Q rec store side t with i | x | r'
  · simp only [h]
    refine Prod.ext (Prod.ext ?_ rfl) (fin1_funext (by simp))
    simp
  · simp only [h]
    split_ifs with ht
    · simp only [F.actAt_update_store rec store side ht, h, ht, ↓reduceDIte]
      refine Prod.ext (Prod.ext ?_ rfl) (fin1_funext (by simp))
      simp
    · simp [h, ht]
  · simp only [h]
    split_ifs with ht
    · simp only [F.actAt_update_store rec store side ht, h, ht, ↓reduceDIte]
      simp
    · simp [h, ht]

/-- The tear-down as a permutation. -/
def teardownPerm : Equiv.Perm RR :=
  Function.Involutive.toPerm (teardownFun F b Q) (teardownFun_teardownFun F b Q)

/-- **The clock**: one more sub-slot done. -/
def tickPerm : Equiv.Perm RR where
  toFun d := ((⟨d.1.1.inner, d.1.1.record, d.1.1.store, d.1.1.side, finRotate _ d.1.1.time⟩,
    d.1.2.1, d.1.2.2), d.2)
  invFun d := ((⟨d.1.1.inner, d.1.1.record, d.1.1.store, d.1.1.side,
    (finRotate _).symm d.1.1.time⟩, d.1.2.1, d.1.2.2), d.2)
  left_inv d := by simp
  right_inv d := by simp

/-- **The reply of a finished relayed request**: when the blocks of the started slots end at the
clock and the last started slot is a relayed request, its reply is written into the
distinguisher's response register (exchanged with the blank `none`). -/
def finalizeFun (d : RR) : RR :=
  if F.startAt n b Q (MultiRelay.recList d.1.1.record) (MultiRelay.recList d.1.1.record).length =
      d.1.1.time then
    match F.lastReply n b Q d.1.1.record d.1.1.store d.1.1.side with
    | some o => ((⟨((d.1.1.inner.1.1, d.1.1.inner.1.2.1, Equiv.swap none o d.1.1.inner.1.2.2),
        d.1.1.inner.2), d.1.1.record, d.1.1.store, d.1.1.side, d.1.1.time⟩, d.1.2.1, d.1.2.2), d.2)
    | none => d
  else d

theorem finalizeFun_finalizeFun (d : RR) : finalizeFun F b Q (finalizeFun F b Q d) = d := by
  obtain ⟨⟨⟨⟨⟨w, rq0, rs0⟩, ps⟩, rec, store, side, t⟩, rq, rs⟩, pr⟩ := d
  by_cases h : F.startAt n b Q (MultiRelay.recList rec) (MultiRelay.recList rec).length = (t : ℕ)
  · rcases ho : F.lastReply n b Q rec store side with _ | o
    · simp only [finalizeFun, h, ho, ite_true]
    · simp only [finalizeFun, h, ho, ite_true]
      simp
  · simp only [finalizeFun, h, ite_false]

/-- The reply as a permutation. -/
def finalizePerm : Equiv.Perm RR :=
  Function.Involutive.toPerm (finalizeFun F b Q) (finalizeFun_finalizeFun F b Q)

/-- The entry of the distinguisher's registers: the request if the kind is a request, else
`none` (the log a slot receives). -/
def entryOf (kind : W → Bool) (d : DReg W n X Y Req Resp) : Option Req :=
  if kind d.1.1 then some d.1.2.1 else none

/-- **The record of a starting slot**: when slot `i` starts at the clock, its entry is written
into the record (exchanged with the blank `none`). -/
def recordFun (kind : W → Bool) (d : RR) : RR :=
  match F.fillAt n b Q d.1.1.record d.1.1.time with
  | some i => ((⟨d.1.1.inner, Function.update d.1.1.record i
      (Equiv.swap none (some (entryOf kind d.1.1.inner)) (d.1.1.record i)), d.1.1.store,
      d.1.1.side, d.1.1.time⟩, d.1.2.1, d.1.2.2), d.2)
  | none => d

end Distinguisher

theorem List.find?_finRange_congr {m : ℕ} {p p' : Fin m → Bool} {i : Fin m}
    (h : (List.finRange m).find? p = some i) (hp : ∀ i' ≤ i, p' i' = p i') :
    (List.finRange m).find? p' = some i := by
  rw [List.find?_eq_some_iff_append] at h ⊢
  obtain ⟨hpi, as, bs, heq, has⟩ := h
  refine ⟨by rw [hp i le_rfl]; exact hpi, as, bs, heq, fun a ha => ?_⟩
  have hpw := (List.sortedLT_finRange m).pairwise
  rw [heq, List.pairwise_append] at hpw
  have hlt : a < i := hpw.2.2 a ha i List.mem_cons_self
  rw [hp a hlt.le]
  exact has a ha

namespace MultiRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)

/-- **Filling the starting slot keeps it the starting slot.** -/
theorem fillAt_update {n b Q m : ℕ} {rec : Fin m → Option (Option Req)} {t : ℕ} {i : Fin m}
    (h : F.fillAt n b Q rec t = some i) (v : Option (Option Req)) :
    F.fillAt n b Q (Function.update rec i v) t = some i := by
  unfold fillAt at h ⊢
  refine List.find?_finRange_congr h fun i' hi' => ?_
  have hpre : recPrefix (Function.update rec i v) i' = recPrefix rec i' := by
    unfold recPrefix
    refine List.map_congr_left fun j hj => ?_
    have hj' : (j : ℕ) < i' := by
      obtain ⟨k, hk, hkj⟩ := List.mem_iff_getElem.1 hj
      simp only [List.length_take, List.length_finRange] at hk
      rw [← hkj]
      simp only [List.getElem_take, List.getElem_finRange, Fin.val_cast]
      omega
    rw [Function.update_of_ne (fun e => by subst e; exact absurd hi' (not_le.2 hj'))]
  simp only [hpre]
  congr 2
  refine propext ⟨fun h' i'' hi'' => ?_, fun h' i'' hi'' => ?_⟩
  · have := h' i'' hi''
    rwa [Function.update_of_ne (fun e => by subst e; exact absurd hi' (not_le.2 hi''))] at this
  · rw [Function.update_of_ne (fun e => by subst e; exact absurd hi' (not_le.2 hi''))]
    exact h' i'' hi''

end MultiRelay

namespace MultiRelay

section AddVec

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)
  [Inhabited X] [AddGroup Ys]

/-- **The `i`-th side addition after sub-slot `sub - 1`, on a side vector**: when the program,
after sub-slot `sub - 1` and `i` of the side reads after it (`pendSt`, its side reads answered
from the vector and its stored answers by `g`), makes a side read of `x` as its `ns`-th, the side
function's value `F.side x` added to (`sgn`) or subtracted from entry `ns`; the vector unchanged
otherwise. -/
def addVec (r : Req) (g : ℕ → Option Resp' × (X × Y)) (sub i : ℕ) (sgn : Bool)
    (v : Fin F.qS → Ys) : Fin F.qS → Ys :=
  match F.progAct r (F.pendSt (F.vecSa v) r g sub i) with
  | some (.inl (.inr x)) =>
    if hk : (F.pendSt (F.vecSa v) r g sub i).ns < F.qS then
      Function.update v ⟨_, hk⟩ (v ⟨_, hk⟩ + (if sgn then F.side x else -F.side x))
    else v
  | _ => v

/-- **Subtracting a side addition undoes it.** -/
theorem addVec_addVec (r : Req) (g : ℕ → Option Resp' × (X × Y)) (sub i : ℕ) (sgn : Bool)
    (v : Fin F.qS → Ys) : F.addVec r g sub i (!sgn) (F.addVec r g sub i sgn v) = v := by
  set P := F.pendSt (F.vecSa v) r g sub i with hP
  rcases hp : F.progAct r P with _ | ((x | x) | r')
  · simp only [addVec, ← hP, hp]
  · simp only [addVec, ← hP, hp]
  · by_cases hk : P.ns < F.qS
    · have hst : ∀ y : Ys, F.pendSt (F.vecSa (Function.update v ⟨P.ns, hk⟩ y)) r g sub i = P :=
        fun y => F.pendSt_congr_sa (N := P.ns)
          (fun k hk' x' => F.vecSa_update_of_ne _ hk _ (Nat.ne_of_lt hk') x') r _ sub i le_rfl
      simp only [addVec, ← hP, hp, hk, ↓reduceDIte, hst, Function.update_self]
      cases sgn <;> simp [Function.update_idem, Function.update_eq_self]
    · simp only [addVec, ← hP, hp, hk, ↓reduceDIte]
  · simp only [addVec, ← hP, hp]

end AddVec

end MultiRelay

namespace Distinguisher

variable {W X Y Req Resp Req' Resp' Xs Ys : Type} [DecidableEq X] [DecidableEq Req']
  [DecidableEq Req] [DecidableEq Resp] [Inhabited X] [Inhabited Req'] [AddGroup Y] [AddGroup Ys]
  {n m : ℕ} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (b Q : ℕ)

local notation "RR" => RelayReg W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)

theorem recordFun_recordFun (kind : W → Bool) (d : RR) :
    recordFun F b Q kind (recordFun F b Q kind d) = d := by
  obtain ⟨⟨⟨inn, rec, store, side, t⟩, rq, rs⟩, pr⟩ := d
  rcases h : F.fillAt n b Q rec t with _ | i
  · simp only [recordFun, h]
  · simp only [recordFun, h, F.fillAt_update h]
    simp

/-- The record as a permutation. -/
def recordPerm (kind : W → Bool) : Equiv.Perm RR :=
  Function.Involutive.toPerm (recordFun F b Q kind) (recordFun_recordFun F b Q kind)

/-- **The `i`-th side addition after a sub-slot**: when the last started slot `j` is a relayed
request `r` with `sub ≥ 1` of its sub-slots done, the slot's side vector after its `i`-th side
addition (`MultiRelay.addVec`); the identity elsewhere. The point and the entry are read from the
record, the stored answers, the clock and the entries below the entry, which the addition
keeps. -/
def sideAddFun (i : ℕ) (sgn : Bool) (d : RR) : RR :=
  match F.curRel n b Q d.1.1.record d.1.1.time with
  | some (j, r, sub) =>
    if hj : j < m then
      ((⟨d.1.1.inner, d.1.1.record, d.1.1.store, Function.update d.1.1.side ⟨j, hj⟩
          (F.addVec r (fun k => MultiRelay.storeAt d.1.1.store
            (F.startAt n b Q (MultiRelay.recList d.1.1.record) j + k)) sub i sgn
            (d.1.1.side ⟨j, hj⟩)), d.1.1.time⟩, d.1.2.1, d.1.2.2), d.2)
    else d
  | none => d

theorem sideAddFun_sideAddFun (i : ℕ) (sgn : Bool) (d : RR) :
    sideAddFun F b Q i (!sgn) (sideAddFun F b Q i sgn d) = d := by
  obtain ⟨⟨⟨inn, rec, store, side, t⟩, rq, rs⟩, pr⟩ := d
  rcases hc : F.curRel n b Q rec t with _ | ⟨j, r, sub⟩
  · simp only [sideAddFun, hc]
  · by_cases hj : j < m
    · simp only [sideAddFun, hc, hj, ↓reduceDIte, Function.update_self, F.addVec_addVec,
        Function.update_idem, Function.update_eq_self]
    · simp only [sideAddFun, hc, hj, ↓reduceDIte]

/-- **The `i`-th side addition** as a permutation (`sideAddFun`). -/
def sideAddPerm (i : ℕ) : Equiv.Perm RR where
  toFun := sideAddFun F b Q i true
  invFun := sideAddFun F b Q i false
  left_inv d := sideAddFun_sideAddFun F b Q i true d
  right_inv d := sideAddFun_sideAddFun F b Q i false d

/-- **The side additions after a sub-slot**: the `qS` side additions in order, which write the
side function's values at the side reads the program makes after the sub-slot into the slot's side
vector. -/
def sideAddsPerm : Equiv.Perm RR :=
  (List.range F.qS).foldl (fun P i => P.trans (sideAddPerm F b Q i)) (Equiv.refl _)

/-- The relayed distinguisher's registers at the start: the distinguisher's registers `d`, a blank
record, blank stored answers, a blank side store, the clock at `0`, blank main request and
response registers and the blank query pair. -/
def relayInit (d : DReg W n X Y Req Resp) : RR :=
  ((⟨d, fun _ => none, fun _ => (none, (default, 0)), fun _ => 0, 0⟩, default, none),
    fun _ => (default, 0))

theorem relayInit_injective : Function.Injective (relayInit (W := W) (Req := Req) (Resp := Resp)
    (n := n) (m := m) F) :=
  fun _ _ h => congrArg (fun x => x.1.1.inner) h

variable [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req]
  [Fintype Resp] [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] [Fintype Ys] [DecidableEq Ys]
  (D : Distinguisher W X Y Req Resp n m)

/-- **The distinguisher's step at the start of a slot**: on the registers whose started slots'
blocks end at the clock, the distinguisher's step numbered by the started slots, applied to its
registers; the identity elsewhere. -/
noncomputable def ctrlStep : QState RR ≃ₗᵢ[ℂ] QState RR :=
  (relabel (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys))).trans
    ((controlled fun rest : RelayRest X Y Req Req' Resp' m (relaySlots n m F) (Fin F.qS → Ys) =>
      if F.startAt n b Q (MultiRelay.recList rest.1) (MultiRelay.recList rest.1).length =
          (rest.2.2.2.1 : ℕ) then D.stepAt (MultiRelay.recList rest.1).length
      else LinearIsometryEquiv.refl ℂ _).trans
      (relabel (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F)
        (Fin F.qS → Ys))).symm)

/-- **The relayed distinguisher** (module docstring): the distinguisher `D` run inside the
workspace, each of its slots relayed as a block of sub-slots against a main environment through
`F`, with the query budget `b` and the request bound `Q` enforced. Its step `k` is, for `k > 0`,
the tear-down of sub-slot `k - 1`, the clock, the side additions after that sub-slot
(`sideAddsPerm`, which write the side function's values at the side reads the program makes next
into the side store) and the reply of a finished relayed request, then the distinguisher's step at
the start of a slot, the record of the starting slot and the set-up of sub-slot `k`. It accepts
when `D` accepts on its registers.

Running time: that of `D`, and for each of its slots a block of `relaySlots n m F` sub-slots,
each a step of a relay program of `F` (at most `F.K` main requests, `F.qR` oracle queries, `F.qS`
side reads and `F.qP` pad sub-slots per relayed request, each side read one evaluation of
`F.side`), with the classical records of the relayed requests and the budget and request
counters; polynomial when `D`, the relay programs and the side function are. This running time is
argued here, not proved in Lean. -/
noncomputable def relay : Distinguisher (RelayW (DReg W n X Y Req Resp) Req Resp' X Y m
    (relaySlots n m F) (Fin F.qS → Ys)) X Y Req' Resp' 1 (relaySlots n m F) where
  kind w := (F.actAt n b Q w.record w.store w.side w.time).isAsk
  init := embV (relayInit F) D.init
  norm_init := by rw [norm_embV (relayInit_injective F), D.norm_init]
  step k := (if (k : ℕ) = 0 then LinearIsometryEquiv.refl ℂ _ else
      permOp ((((teardownPerm F b Q).trans (tickPerm F)).trans (sideAddsPerm F b Q)).trans
        (finalizePerm F b Q))).trans
    ((D.ctrlStep F b Q).trans ((permOp (recordPerm F b Q D.kind)).trans
      (permOp (setupPerm F b Q))))
  accept := {d | d.1.1.inner ∈ D.accept}

end Distinguisher

end Quantum

end GordieHowe
