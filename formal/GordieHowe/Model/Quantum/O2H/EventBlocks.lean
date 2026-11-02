-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.O2H.Game

@[expose] public section

/-!
# The slot of a request: event blocks of the logs

A branch of the pure game (`GordieHowe/Model/Quantum/Pure/Game.lean`) that made request number `e`
made it at one slot `k`, after the logs before `k`, with one request `req`. `evLogs e b` are the
final logs of the block `b = (k, lg, req)`: they agree with `lg` before slot `k` and hold `req` at
slot `k`, where `lg` holds `e` requests and is blank from slot `k` on.

- `evLogs_disjoint`: distinct blocks have disjoint final logs.
- `exists_mem_evLogs`: the logs that made request `e` lie in some block, and
  `notMem_evLogs_of_notMem_madeLogs`: the others in none.
- `prob_eq_add_sum_evLogs`: a measurement splits into the part on the logs that did not make
  request `e` and the parts on the blocks.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

variable {Req : Type*} {m : ℕ}

/-- **The final logs of an event block** `b = (k, lg, req)` for request number `e`: logs that
agree with `lg` before slot `k` and hold `req` at slot `k`, for a block whose logs `lg` hold `e`
requests and are blank from slot `k` on (otherwise none). -/
def evLogs (e : ℕ) (b : Fin m × LogReg Req m × Req) : Set (LogReg Req m) :=
  {lg' | (∀ k' : Fin m, k' < b.1 → lg' k' = b.2.1 k') ∧ lg' b.1 = some b.2.2 ∧
    (requests b.2.1).length = e ∧ ∀ k' : Fin m, b.1 ≤ k' → b.2.1 k' = none}

/-- The number of requests before slot `k` grows by at most one per slot. -/
theorem length_requestsBefore_succ_le (lg : LogReg Req m) (k : ℕ) :
    (requestsBefore lg (k + 1)).length ≤ (requestsBefore lg k).length + 1 := by
  rw [requestsBefore]
  split_ifs
  · cases lg _ <;> simp
  · simp

/-- The number of requests before slot `k` is monotone in `k`. -/
theorem length_requestsBefore_mono (lg : LogReg Req m) {a b : ℕ} (hab : a ≤ b) :
    (requestsBefore lg a).length ≤ (requestsBefore lg b).length := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b _ ih =>
    rw [requestsBefore, List.length_append]
    omega

/-- Logs in the event block `(k, lg, req)` hold `e` requests before slot `k`. -/
theorem length_requestsBefore_of_mem_evLogs {e : ℕ} {b : Fin m × LogReg Req m × Req}
    {lg' : LogReg Req m} (h : lg' ∈ evLogs e b) : (requestsBefore lg' b.1).length = e := by
  obtain ⟨h1, -, h3, h4⟩ := h
  rw [requestsBefore_congr fun k' hk' => h1 k' hk', ← requests_eq_requestsBefore h4, h3]

/-- Logs in the event block `(k, lg, req)` hold `e + 1` requests before slot `k + 1`. -/
theorem length_requestsBefore_succ_of_mem_evLogs {e : ℕ} {b : Fin m × LogReg Req m × Req}
    {lg' : LogReg Req m} (h : lg' ∈ evLogs e b) :
    (requestsBefore lg' (b.1 + 1)).length = e + 1 := by
  rw [requestsBefore_succ_of_lt lg' b.1.2, List.length_append,
    length_requestsBefore_of_mem_evLogs h]
  simp [h.2.1]

/-- The requests of logs in the event block `(k, lg, req)` start with those of `lg`, then `req`. -/
theorem requests_of_mem_evLogs {e : ℕ} {b : Fin m × LogReg Req m × Req} {lg' : LogReg Req m}
    (h : lg' ∈ evLogs e b) : ∃ rs', requests lg' = requests b.2.1 ++ b.2.2 :: rs' := by
  obtain ⟨h1, h2, -, h4⟩ := h
  have hpre := requestsBefore_prefix lg' (show (b.1 : ℕ) + 1 ≤ m from b.1.2)
  rw [requestsBefore_succ_of_lt lg' b.1.2, Fin.eta, h2,
    requestsBefore_congr fun k' hk' => h1 k' hk', ← requests_eq_requestsBefore h4] at hpre
  obtain ⟨rs', hrs'⟩ := hpre
  exact ⟨rs', by rw [requests, ← hrs']; simp⟩

/-- Logs in an event block for request `e` made request `e`. -/
theorem mem_madeLogs_of_mem_evLogs {e : ℕ} {b : Fin m × LogReg Req m × Req} {lg' : LogReg Req m}
    (h : lg' ∈ evLogs e b) : lg' ∈ madeLogs e := by
  have h1 := length_requestsBefore_succ_of_mem_evLogs h
  have h2 := length_requestsBefore_mono lg' (show (b.1 : ℕ) + 1 ≤ m from b.1.2)
  simp only [madeLogs, Set.mem_ofPred_eq, requests]
  omega

/-- Logs that did not make request `e` are in no event block. -/
theorem notMem_evLogs_of_notMem_madeLogs {e : ℕ} {lg' : LogReg Req m} (h : lg' ∉ madeLogs e)
    (b : Fin m × LogReg Req m × Req) : lg' ∉ evLogs e b :=
  fun h' => h (mem_madeLogs_of_mem_evLogs h')

/-- **Distinct event blocks have disjoint final logs.** -/
theorem evLogs_disjoint {e : ℕ} {b b' : Fin m × LogReg Req m × Req} (hb : b ≠ b') :
    Disjoint (evLogs e b) (evLogs e b') := by
  obtain ⟨k, lg, req⟩ := b
  obtain ⟨k₀, lg₀, req₀⟩ := b'
  rw [Set.disjoint_left]
  intro lg' h h'
  have a := length_requestsBefore_of_mem_evLogs h
  have a' := length_requestsBefore_of_mem_evLogs h'
  have c := length_requestsBefore_succ_of_mem_evLogs h
  have c' := length_requestsBefore_succ_of_mem_evLogs h'
  dsimp only at a a' c c'
  have hk : k = k₀ := by
    rcases lt_trichotomy k k₀ with hlt | heq | hlt
    · have := length_requestsBefore_mono lg' (show (k : ℕ) + 1 ≤ k₀ from hlt)
      omega
    · exact heq
    · have := length_requestsBefore_mono lg' (show (k₀ : ℕ) + 1 ≤ k from hlt)
      omega
  subst hk
  obtain ⟨h1, h2, -, h4⟩ := h
  obtain ⟨h1', h2', -, h4'⟩ := h'
  dsimp only at h1 h2 h4 h1' h2' h4'
  refine hb (Prod.ext rfl (Prod.ext ?_ ?_))
  · funext j
    rcases lt_or_ge j k with hj | hj
    · exact (h1 j hj).symm.trans (h1' j hj)
    · exact (h4 j hj).trans (h4' j hj).symm
  · exact Option.some_injective _ (h2.symm.trans h2')

/-- **The logs that made request `e` lie in an event block.** -/
theorem exists_mem_evLogs {e : ℕ} {lg' : LogReg Req m} (h : lg' ∈ madeLogs e) :
    ∃ b, lg' ∈ evLogs e b := by
  simp only [madeLogs, Set.mem_ofPred_eq, requests] at h
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0
      simp [requestsBefore] at h
    · exact h0
  have hex : ∃ j, e < (requestsBefore lg' (j + 1)).length := ⟨m - 1, by rwa [Nat.sub_add_cancel hm]⟩
  classical
  set k := Nat.find hex with hkdef
  have hP : e < (requestsBefore lg' (k + 1)).length := Nat.find_spec hex
  have hkm : k < m := by
    have := Nat.find_min' hex (show e < (requestsBefore lg' (m - 1 + 1)).length by
      rwa [Nat.sub_add_cancel hm])
    omega
  have hle : (requestsBefore lg' k).length ≤ e := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0]
      simp [requestsBefore]
    · have := Nat.find_min hex (show k - 1 < k by omega)
      rw [Nat.sub_add_cancel h0] at this
      omega
  have hsucc := length_requestsBefore_succ_le lg' k
  have heq : (requestsBefore lg' k).length = e := by omega
  rw [requestsBefore_succ_of_lt lg' hkm, List.length_append] at hP
  obtain ⟨req, hreq⟩ : ∃ req, lg' ⟨k, hkm⟩ = some req := by
    cases hc : lg' ⟨k, hkm⟩ with
    | none => rw [hc] at hP; simp at hP; omega
    | some req => exact ⟨req, rfl⟩
  refine ⟨(⟨k, hkm⟩, fun j => if (j : ℕ) < k then lg' j else none, req), fun j hj => ?_, hreq, ?_,
    fun j hj => ?_⟩
  · simp only [Fin.lt_def] at hj
    simp [hj]
  · dsimp only
    rw [requests_eq_requestsBefore (k := k) fun j hj => by simp [not_lt.2 hj],
      requestsBefore_congr (lg' := lg') fun j hj => by simp [hj], heq]
  · simp only [Fin.le_def] at hj
    simp [not_lt.2 hj]

variable {W X Y A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] {n : ℕ}

/-- **A measurement splits by the slot of request `e`**: into the part on the logs that did not
make request `e` and the parts on the event blocks. -/
theorem prob_eq_add_sum_evLogs (e : ℕ) (C : Set (GameReg W n X Y Req A m))
    (v : QState (GameReg W n X Y Req A m)) :
    prob C v = prob (C ∩ logsIn (madeLogs e)ᶜ) v + ∑ b, prob (C ∩ logsIn (evLogs e b)) v := by
  classical
  have hspec : ∀ lg : LogReg Req m, lg ∈ madeLogs e → ∃ b, lg ∈ evLogs e b :=
    fun _ h => exists_mem_evLogs h
  let g : GameReg W n X Y Req A m → Option (Fin m × LogReg Req m × Req) := fun r =>
    if h : (splitLogs r).2 ∈ madeLogs e then some (Classical.choose (hspec _ h)) else none
  rw [prob_eq_sum_fiber C g v, Fintype.sum_option]
  congr 1
  · congr 1
    ext r
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, mem_logsIn,
      Set.mem_compl_iff, g]
    split_ifs with h <;> simp [h]
  · refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    ext r
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, mem_logsIn, g]
    refine and_congr_right fun _ => ?_
    split_ifs with h
    · have hc := Classical.choose_spec (hspec _ h)
      constructor
      · intro hb
        rw [← Option.some_injective _ hb]
        exact hc
      · intro hb
        by_contra hne
        exact Set.disjoint_left.1 (evLogs_disjoint (e := e) fun hc => hne (congrArg some hc)) hc hb
    · simp only [false_iff]
      exact notMem_evLogs_of_notMem_madeLogs h b

end GordieHowe.Quantum
