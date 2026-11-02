-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.Budget

@[expose] public section

/-!
# The slot schedule of a simulating distinguisher

For step counts `nb : Fin (t + 1) → ℕ`, the slots of `t + 1` blocks: block `k` is a request slot
followed by `nb k` query slots. Block `k` starts at slot `slotStart nb k = k + slotQ nb k`, where
`slotQ nb k` counts the query slots of the blocks before `k`; there are `slotTotal nb` slots in all.
The logs of `t + 1` request points spread over the slots put log `k` at the request slot of block
`k` (`spreadAt`).

- `nbAt`, `nbAt_fin`, `slotQ`, `slotStart`, `slotTotal`, `slotQ_one`, `slotQ_zero`,
  `slotStart_zero`,
  `slotStart_succ`, `slotStart_lt_succ`, `slotStart_le_of_le`, `slotStart_lt_of_lt`,
  `slotStart_add_lt`, `slotStart_add_lt_total`, `slotStart_lt_total`: the block starts.
- `slotBlock`, `slotBlock_le`, `slotBlock_eq`, `slotStart_slotBlock_le`, `lt_slotStart_slotBlock`:
  the block of a slot.
- `spreadAt`, `spreadAt_start`, `spreadAt_query`, `spreadAt_eq_none`, `spreadAt_injective`,
  `spreadAt_update`, `requestsBefore_spreadAt`: the logs spread over the slots.
- `slotQBefore`, `slotQBefore_succ`, `slotQ_mono`, `slotQBefore_block`, `slotQBefore_le`: the query
  slots below a slot.
-/

open Finset

namespace GordieHowe.Quantum

namespace CoSimSchedule

variable {t : ℕ} (nb : Fin (t + 1) → ℕ)

/-- The query slots of block `k`, and none past the last block. -/
def nbAt (k : ℕ) : ℕ := if h : k < t + 1 then nb ⟨k, h⟩ else 0

/-- **The query slots of the blocks before `k`.** -/
def slotQ : ℕ → ℕ
  | 0 => 0
  | k + 1 => slotQ k + nbAt nb k

/-- **The first slot of block `k`**: its request slot. -/
def slotStart (k : ℕ) : ℕ := k + slotQ nb k

/-- **The number of slots.** -/
abbrev slotTotal : ℕ := slotStart nb (t + 1)

theorem nbAt_fin (k : Fin (t + 1)) : nbAt nb k = nb k := by
  simp only [nbAt, k.2, ↓reduceDIte]

theorem slotStart_zero : slotStart nb 0 = 0 := rfl

theorem slotStart_succ (k : ℕ) : slotStart nb (k + 1) = slotStart nb k + 1 + nbAt nb k := by
  simp only [slotStart, slotQ]
  omega

theorem slotStart_lt_succ (k : ℕ) : slotStart nb k < slotStart nb (k + 1) := by
  rw [slotStart_succ]
  omega

theorem slotStart_le_of_le {k k' : ℕ} (h : k ≤ k') : slotStart nb k ≤ slotStart nb k' := by
  induction k', h using Nat.le_induction with
  | base => exact le_rfl
  | succ k' _ ih => exact ih.trans (slotStart_lt_succ nb k').le

theorem slotStart_lt_of_lt {k k' : ℕ} (h : k < k') : slotStart nb k < slotStart nb k' :=
  (slotStart_lt_succ nb k).trans_le (slotStart_le_of_le nb h)

/-- The last slot of block `k` is before the next block. -/
theorem slotStart_add_lt {k o : ℕ} (ho : o ≤ nbAt nb k) :
    slotStart nb k + o < slotStart nb (k + 1) := by
  rw [slotStart_succ]
  omega

/-- The slots of block `k ≤ t` are slots. -/
theorem slotStart_add_lt_total {k : ℕ} (hk : k ≤ t) {o : ℕ} (ho : o ≤ nbAt nb k) :
    slotStart nb k + o < slotTotal nb :=
  (slotStart_add_lt nb ho).trans_le (slotStart_le_of_le nb (by omega))

/-- The start of block `k ≤ t` is a slot. -/
theorem slotStart_lt_total {k : ℕ} (hk : k ≤ t) : slotStart nb k < slotTotal nb :=
  slotStart_lt_of_lt nb (by omega)

/-- **One query slot per block**: `k` query slots before block `k ≤ t + 1`. -/
theorem slotQ_one : ∀ k ≤ t + 1, slotQ (t := t) (fun _ => 1) k = k
  | 0, _ => rfl
  | k + 1, hk => by
    simp only [slotQ, slotQ_one k (by omega), nbAt, show k < t + 1 by omega, ↓reduceDIte]

/-- **No query slots**: none before any block. -/
theorem slotQ_zero : ∀ k, slotQ (t := t) (fun _ => 0) k = 0
  | 0 => rfl
  | k + 1 => by
    simp only [slotQ, slotQ_zero k, nbAt]
    split <;> rfl

/-! ### The block of a slot -/

/-- **The block of slot `j`**: the last block starting at or before `j`. -/
def slotBlock (j : ℕ) : ℕ := Nat.findGreatest (fun k => slotStart nb k ≤ j) t

theorem slotBlock_le (j : ℕ) : slotBlock nb j ≤ t := Nat.findGreatest_le t

theorem slotStart_slotBlock_le (j : ℕ) : slotStart nb (slotBlock nb j) ≤ j :=
  Nat.findGreatest_spec (P := fun k => slotStart nb k ≤ j) (Nat.zero_le t)
    (by rw [slotStart_zero]; exact Nat.zero_le j)

/-- A slot is before the start of the block after its block. -/
theorem lt_slotStart_slotBlock {j : ℕ} (hj : j < slotTotal nb) :
    j < slotStart nb (slotBlock nb j + 1) := by
  by_contra h
  push Not at h
  by_cases hb : slotBlock nb j + 1 ≤ t
  · exact Nat.findGreatest_is_greatest (P := fun k => slotStart nb k ≤ j) (Nat.lt_succ_self _)
      hb h
  · have : slotBlock nb j = t := by have := slotBlock_le nb j; omega
    rw [this] at h
    exact absurd hj (not_lt.2 h)

/-- **The block of a slot of block `k`** is `k`. -/
theorem slotBlock_eq {k : ℕ} (hk : k ≤ t) {o : ℕ} (ho : o ≤ nbAt nb k) :
    slotBlock nb (slotStart nb k + o) = k := by
  refine (Nat.findGreatest_eq_iff).2 ⟨hk, fun _ => by omega, fun n hkn hn h => ?_⟩
  have h1 := slotStart_add_lt nb ho
  have h2 := slotStart_le_of_le nb (show k + 1 ≤ n by omega)
  exact absurd h (by omega)

/-! ### The logs spread over the slots -/

variable {Req : Type*}

/-- **The logs spread over the slots**: log `k` at the request slot of block `k`, the query slots
blank. -/
def spreadAt (lg : LogReg Req (t + 1)) : LogReg Req (slotTotal nb) :=
  fun j => if slotStart nb (slotBlock nb j) = j then
    lg ⟨slotBlock nb j, Nat.lt_succ_of_le (slotBlock_le nb j)⟩ else none

theorem spreadAt_start (lg : LogReg Req (t + 1)) (k : Fin (t + 1)) :
    spreadAt nb lg ⟨slotStart nb k, slotStart_lt_total nb (Nat.le_of_lt_succ k.2)⟩ = lg k := by
  have hb : slotBlock nb (slotStart nb k) = k := by
    simpa using slotBlock_eq nb (Nat.le_of_lt_succ k.2) (o := 0) (Nat.zero_le _)
  simp only [spreadAt, hb, ↓reduceIte]

theorem spreadAt_query (lg : LogReg Req (t + 1)) (k : Fin (t + 1)) {i : ℕ} (hi : i < nb k) :
    spreadAt nb lg ⟨slotStart nb k + 1 + i, by
      have := slotStart_add_lt_total nb (Nat.le_of_lt_succ k.2) (o := 1 + i)
        (by rw [nbAt_fin]; omega)
      omega⟩ = none := by
  have hb : slotBlock nb (slotStart nb k + (1 + i)) = k :=
    slotBlock_eq nb (Nat.le_of_lt_succ k.2) (by rw [nbAt_fin]; omega)
  have hb' : slotBlock nb (slotStart nb k + 1 + i) = k := by
    rw [show slotStart nb k + 1 + i = slotStart nb k + (1 + i) by omega, hb]
  simp only [spreadAt, hb', show slotStart nb k ≠ slotStart nb k + 1 + i by omega, ↓reduceIte]

/-- A slot other than the block starts carries a blank spread log. -/
theorem spreadAt_eq_none (lg : LogReg Req (t + 1)) (j : Fin (slotTotal nb))
    (hj : ∀ k : Fin (t + 1), (j : ℕ) ≠ slotStart nb k) : spreadAt nb lg j = none := by
  have h : slotStart nb (slotBlock nb j) ≠ j :=
    fun h => hj ⟨slotBlock nb j, Nat.lt_succ_of_le (slotBlock_le nb j)⟩ h.symm
  simp only [spreadAt, h, ↓reduceIte]

theorem spreadAt_injective : Function.Injective (spreadAt (Req := Req) nb) := by
  intro lg lg' h
  funext k
  have := congrFun h ⟨slotStart nb k, slotStart_lt_total nb (Nat.le_of_lt_succ k.2)⟩
  rwa [spreadAt_start, spreadAt_start] at this

theorem spreadAt_update [DecidableEq Req] (lg : LogReg Req (t + 1)) (k : Fin (t + 1))
    (r : Option Req) :
    spreadAt nb (Function.update lg k r) = Function.update (spreadAt nb lg)
      ⟨slotStart nb k, slotStart_lt_total nb (Nat.le_of_lt_succ k.2)⟩ r := by
  funext j
  by_cases hj : (j : ℕ) = slotStart nb k
  · have hj' : j = ⟨slotStart nb k, slotStart_lt_total nb (Nat.le_of_lt_succ k.2)⟩ :=
      Fin.ext hj
    rw [hj', Function.update_self, spreadAt_start, Function.update_self]
  · rw [Function.update_of_ne (fun h => hj (congrArg Fin.val h))]
    simp only [spreadAt]
    split_ifs with h2
    · rw [Function.update_of_ne]
      intro h
      apply hj
      rw [← h2]
      exact congrArg (slotStart nb) (congrArg Fin.val h)
    · rfl

/-- **The requests of the spread logs before block `k`** are those of the logs before `k`. -/
theorem requestsBefore_spreadAt (lg : LogReg Req (t + 1)) :
    ∀ k ≤ t + 1, requestsBefore (spreadAt nb lg) (slotStart nb k) = requestsBefore lg k
  | 0, _ => rfl
  | k + 1, hk => by
    -- the query slots of block `k` add nothing
    have hq : ∀ o ≤ nbAt nb k, requestsBefore (spreadAt nb lg) (slotStart nb k + 1 + o) =
        requestsBefore (spreadAt nb lg) (slotStart nb k + 1) := by
      intro o ho
      induction o with
      | zero => rfl
      | succ o ih =>
        rw [← Nat.add_assoc, requestsBefore_succ_of_lt _ (by
          have := slotStart_add_lt_total nb (k := k) (by omega) ho
          omega), ih (by omega)]
        have hk' : k < t + 1 := by omega
        have : spreadAt nb lg ⟨slotStart nb k + 1 + o, by
            have := slotStart_add_lt_total nb (k := k) (by omega) ho
            omega⟩ = none :=
          spreadAt_query nb lg ⟨k, hk'⟩ (by rw [← nbAt_fin nb ⟨k, hk'⟩]; simp only; omega)
        rw [this]
        simp
    have hk' : k < t + 1 := by omega
    rw [slotStart_succ, show slotStart nb k + 1 + nbAt nb k =
      slotStart nb k + 1 + nbAt nb k from rfl, hq _ le_rfl,
      requestsBefore_succ_of_lt _ (slotStart_lt_total nb (k := k) (by omega)),
      requestsBefore_spreadAt lg k (by omega), requestsBefore_succ_of_lt _ hk']
    have := spreadAt_start nb lg ⟨k, hk'⟩
    simp only at this
    rw [this]

/-! ### The query slots below a slot -/

/-- **The query slots below slot `j`**: the slots below `j` other than the block starts. -/
def slotQBefore (j : ℕ) : ℕ :=
  ((range j).filter fun i => slotStart nb (slotBlock nb i) ≠ i).card

theorem slotQBefore_succ (j : ℕ) : slotQBefore nb (j + 1) =
    slotQBefore nb j + if slotStart nb (slotBlock nb j) ≠ j then 1 else 0 := by
  unfold slotQBefore
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun hj => by simp at hj)]
  · rfl

theorem slotQ_mono {k k' : ℕ} (h : k ≤ k') : slotQ nb k ≤ slotQ nb k' := by
  induction k', h using Nat.le_induction with
  | base => exact le_rfl
  | succ k' _ ih => exact ih.trans (by simp only [slotQ]; omega)

/-- **The query slots below the slots of block `k`**: those of the blocks before `k`, and the
`o` first ones of block `k` below slot `slotStart nb k + 1 + o`. -/
theorem slotQBefore_block : ∀ k ≤ t + 1, slotQBefore nb (slotStart nb k) = slotQ nb k ∧
      (k ≤ t → ∀ o ≤ nbAt nb k, slotQBefore nb (slotStart nb k + 1 + o) = slotQ nb k + o)
  | 0, _ => by
    refine ⟨rfl, fun hk o ho => ?_⟩
    induction o with
    | zero =>
      rw [Nat.add_zero, slotQBefore_succ]
      have hb : slotBlock nb (slotStart nb 0) = 0 := by
        simpa using slotBlock_eq nb (k := 0) (Nat.zero_le t) (o := 0) (Nat.zero_le _)
      simp only [hb, ne_eq, not_true_eq_false, ↓reduceIte]
      rfl
    | succ o ih =>
      rw [← Nat.add_assoc, slotQBefore_succ, ih (by omega)]
      have hb : slotBlock nb (slotStart nb 0 + 1 + o) = 0 := by
        rw [show slotStart nb 0 + 1 + o = slotStart nb 0 + (1 + o) by omega]
        exact slotBlock_eq nb (Nat.zero_le t) (by omega)
      simp only [hb, ne_eq, show slotStart nb 0 ≠ slotStart nb 0 + 1 + o by omega,
        not_false_eq_true, ↓reduceIte]
      omega
  | k + 1, hk => by
    obtain ⟨_, hb⟩ := slotQBefore_block k (by omega)
    have h1 : slotQBefore nb (slotStart nb (k + 1)) = slotQ nb (k + 1) := by
      rw [slotStart_succ, hb (by omega) _ le_rfl]
      rfl
    refine ⟨h1, fun hk' o ho => ?_⟩
    induction o with
    | zero =>
      rw [Nat.add_zero, slotQBefore_succ, h1]
      have hb' : slotBlock nb (slotStart nb (k + 1)) = k + 1 := by
        simpa using slotBlock_eq nb hk' (o := 0) (Nat.zero_le _)
      simp only [hb', ne_eq, not_true_eq_false, ↓reduceIte]
    | succ o ih =>
      rw [← Nat.add_assoc, slotQBefore_succ, ih (by omega)]
      have hb' : slotBlock nb (slotStart nb (k + 1) + 1 + o) = k + 1 := by
        rw [show slotStart nb (k + 1) + 1 + o = slotStart nb (k + 1) + (1 + o) by omega]
        exact slotBlock_eq nb hk' (by omega)
      simp only [hb', ne_eq, show slotStart nb (k + 1) ≠ slotStart nb (k + 1) + 1 + o by omega,
        not_false_eq_true, ↓reduceIte]
      omega

/-- **At most `slotQ nb (t + 1)` query slots below a slot**, and fewer below a query slot. -/
theorem slotQBefore_le {j : ℕ} (hj : j < slotTotal nb) :
    slotQBefore nb j ≤ slotQ nb (t + 1) ∧
      (slotStart nb (slotBlock nb j) ≠ j → slotQBefore nb j < slotQ nb (t + 1)) := by
  have hk := slotBlock_le nb j
  have h1 := slotStart_slotBlock_le nb j
  have h2 := lt_slotStart_slotBlock nb hj
  have hm := slotQ_mono nb (show slotBlock nb j + 1 ≤ t + 1 by omega)
  have hq : slotQ nb (slotBlock nb j + 1) = slotQ nb (slotBlock nb j) + nbAt nb (slotBlock nb j) :=
    rfl
  rw [slotStart_succ] at h2
  obtain ⟨hs, hb⟩ := slotQBefore_block nb (slotBlock nb j) (by omega)
  by_cases he : slotStart nb (slotBlock nb j) = j
  · exact ⟨by rw [← he, hs]; omega, fun h => absurd he h⟩
  · have ho := hb hk (j - slotStart nb (slotBlock nb j) - 1) (by omega)
    rw [show slotStart nb (slotBlock nb j) + 1 + (j - slotStart nb (slotBlock nb j) - 1) = j by
      omega] at ho
    rw [ho]
    exact ⟨by omega, fun _ => by omega⟩

end CoSimSchedule

end GordieHowe.Quantum
