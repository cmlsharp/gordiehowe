-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.Game

@[expose] public section

/-!
# Query budgets of distinguishers

A distinguisher of `GordieHowe/Model/Quantum/Pure/Game.lean` decides at each slot, from its kind register, whether
the slot is a request or a query (Unruh 2017, ePrint 2017/398, p. 10: an oracle algorithm is a
Turing machine that chooses at run time which oracle it calls). A **query
budget** (`Distinguisher.Budget`) charges each branch only for the slots at which it queries: on
every branch at most `q` slots are query slots. It is given by a family of sets of workspaces
`inv k c`, the workspaces possible before slot `k` on a branch that queried at `c` of the slots
before `k`, kept by the steps, such that a branch that has used `q` query slots requests at every
later slot (`Budget.cap`).

- `queriesBefore lg k`: the number of query slots below slot `k` on the logs `lg` (a query slot
  leaves its log blank).

The zero-knowledge games charge a budget of `q` query slots as `n * q` queries
(`GordieHowe.QROM.ZeroKnowledgeAfterAdaptive`); the O2H step that uses it is
`Distinguisher.advantage_acceptProbOn_made_le_of_fresh_secret_budget`
(`GordieHowe/Model/Quantum/O2H/Budget.lean`).
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

section Logs

variable {Req : Type*} {m : ℕ}

/-- Whether slot `i` was a query slot on the logs `lg`: its log is blank. After the slot, a
request slot has a filled log (`Env.requestPerm`). -/
def queriedAt (lg : LogReg Req m) (i : ℕ) : Bool :=
  if h : i < m then (lg ⟨i, h⟩).isNone else false

/-- **The number of query slots below slot `k`** on the logs `lg`. -/
def queriesBefore (lg : LogReg Req m) (k : ℕ) : ℕ :=
  ((range k).filter fun i => queriedAt lg i).card

theorem queriesBefore_zero (lg : LogReg Req m) : queriesBefore lg 0 = 0 := by
  simp [queriesBefore]

theorem queriesBefore_succ (lg : LogReg Req m) (k : ℕ) :
    queriesBefore lg (k + 1) = queriesBefore lg k + if queriedAt lg k then 1 else 0 := by
  unfold queriesBefore
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun hk => by simp at hk)]
  · rfl

/-- The count below slot `k` reads only the logs below `k`. -/
theorem queriesBefore_congr {lg lg' : LogReg Req m} {k : ℕ}
    (h : ∀ i : Fin m, (i : ℕ) < k → lg i = lg' i) : queriesBefore lg k = queriesBefore lg' k := by
  unfold queriesBefore
  congr 1
  refine filter_congr fun i hi => ?_
  have hik : i < k := mem_range.1 hi
  unfold queriedAt
  split_ifs with him
  · rw [h ⟨i, him⟩ hik]
  · rfl

/-- No slot from slot `m` on is a query slot. -/
theorem queriedAt_of_le (lg : LogReg Req m) {i : ℕ} (h : m ≤ i) : queriedAt lg i = false := by
  simp [queriedAt, not_lt.2 h]

/-- The count does not grow after the last slot. -/
theorem queriesBefore_succ_of_le (lg : LogReg Req m) {k : ℕ} (h : m ≤ k) :
    queriesBefore lg (k + 1) = queriesBefore lg k := by
  rw [queriesBefore_succ, queriedAt_of_le lg h]
  rfl

/-- Changing the log of slot `k` does not change whether another slot was a query slot. -/
theorem queriedAt_update_of_ne [DecidableEq Req] (lg : LogReg Req m) {i : ℕ} {k : Fin m}
    (h : i ≠ k) (x : Option Req) : queriedAt (Function.update lg k x) i = queriedAt lg i := by
  unfold queriedAt
  split_ifs with hi
  · rw [Function.update_of_ne (Fin.ne_of_val_ne h)]
  · rfl

end Logs

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} (D : Distinguisher W X Y Req A n m)

/-- **A query budget of `q` slots**: a family `inv k c` of sets of workspaces, the workspaces
possible after step `k`, before slot `k`, on a branch that made queries at `c` of the slots before
`k`. It holds after the first step (`init`), is kept by every later step before the last slot, where
a branch whose slot `k` was a query (`kind = false`) has used one more query slot (`step`), and a
branch that queries at slot `k` has used fewer than `q` query slots before it (`cap`). So every
branch queries at no more than `q` slots, whatever the environment
(`Distinguisher.Budget.stepCount_gameAlg`, `GordieHowe/Model/Quantum/O2H/Budget.lean`), while the slots at which
it queries are chosen at run time (Unruh 2017, ePrint 2017/398, p. 10, oracle algorithms). -/
structure Budget (q : ℕ) where
  /-- The workspaces possible before slot `k` after `c` query slots. -/
  inv : ℕ → ℕ → Set W
  init : 0 < m → Supported {r : DReg W n X Y Req A | r.workspace ∈ inv 0 0} (D.step 0 D.init)
  step : ∀ (k : ℕ) (hk : k + 1 < m) (c : ℕ) (b : Bool) (v : QState (DReg W n X Y Req A)),
    Supported {r : DReg W n X Y Req A | r.workspace ∈ inv k c ∧ D.kind r.workspace = b} v →
    Supported {r : DReg W n X Y Req A | r.workspace ∈ inv (k + 1) (if b then c else c + 1)}
      (D.step ⟨k + 1, by omega⟩ v)
  cap : ∀ k < m, ∀ c w, w ∈ inv k c → D.kind w = false → c < q

variable {D}

end Distinguisher

end GordieHowe.Quantum
