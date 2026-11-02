-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.O2H.HiddenSide

@[expose] public section

/-!
# The hybrid argument for two games whose slots differ, with a per-branch count

Ambainis, Hamburg and Unruh (CRYPTO 2019, ePrint 2018/904; AHU19), Lemma 8, pp. 26–27, bound the
distance of the final states of two runs whose oracle steps differ by the sum, over the steps, of
the weight of the state before the step on the basis states where the steps differ;
`OracleAlg.StepCount.norm_final_sub_le` (`GordieHowe/Model/Quantum/O2H/Budget.lean`) refines the
sum by a per-branch count of the steps. Here the two runs are the pure games
(`GordieHowe/Model/Quantum/Pure/Game.lean`) of one distinguisher against two environments `E` and
`E'`, and the differing steps are the slots: at slot `k` the slot permutations of `E` and `E'` may
differ, on the reachable basis states of a set `B k`, at a request as well as at a query.

`norm_run_sub_le_of_count`: if the slot permutations agree outside `B k`, both map the basis
states of `B k` into the basis states whose logs lie in `Lc k` (a set of logs read up to slot `k`,
`ReadsUpTo`), and every final basis state of an invariant family `G` has logs in at most `q'` of
the sets `Lc k`, then `‖run E − run E'‖ ≤ 2 √q' √(∑_k ‖mask (B k) (stage E k)‖²)`.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

/-- The mask of `T` of a vector supported in `S` is supported in `S ∩ T`. -/
theorem Supported.mask_inter {ι : Type*} [Fintype ι] {S : Set ι} {v : QState ι}
    (h : Supported S v) (T : Set ι) : Supported (S ∩ T) (mask T v) := fun r hr => by
  by_cases hT : r ∈ T
  · rw [mask_apply_of_mem _ hT, h r fun hS => hr ⟨hS, hT⟩]
  · exact mask_apply_of_notMem _ hT

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} (D : Distinguisher W X Y Req A n m) [DecidableEq Req] [DecidableEq A] [AddGroup Y]
  {Ω Ω' : Type*} {Q : ℕ} {St St' : Type _} [OracleState St X Y] [OracleState St' X Y]

open Classical in
/-- **AHU19 Lemma 8 for two games whose slots differ, with a per-branch count.** For two
environments `E` at `ω` and `E'` at `ω'`: the slot permutations agree outside `B k` on the
reachable basis states before slot `k` (`hB`); both map the reachable basis states of `B k` into
the basis states whose logs lie in `Lc k` (`hBC`), a set of logs read up to slot `k` (`hLc`); a
family `G` of sets holds the states of the run of `E` before each slot (`hGv`) and is carried by the
slots and steps of both games (`hGE`, `hGE'`); and every basis state of `G m` has logs in at most
`q'` of the sets `Lc k` (`hcount`). Then the final states are within
`2 √q' √(∑_k ‖mask (B k) (stage E ω k)‖²)`. -/
theorem norm_run_sub_le_of_count (E : Env Ω Req A X Y Q St) (E' : Env Ω Req A X Y Q St') {ω : Ω}
    (ω' : Ω)
    (B : ℕ → Set (GameReg W n X Y Req A m)) (Lc : ℕ → Set (LogReg Req m))
    (G : ℕ → Set (GameReg W n X Y Req A m)) (q' : ℕ)
    (hB : ∀ k < m, ∀ r ∈ logsIn (reachableLogs k), r ∉ B k →
      D.eventPerm E ω k r = D.eventPerm E' ω' k r)
    (hBC : ∀ k < m, ∀ r ∈ logsIn (reachableLogs k), r ∈ B k →
      D.eventPerm E ω k r ∈ logsIn (Lc k) ∧ D.eventPerm E' ω' k r ∈ logsIn (Lc k))
    (hLc : ∀ k, ReadsUpTo (Lc k) k)
    (hGv : ∀ k ≤ m, Supported (G k) (D.stage E ω k))
    (hGE : ∀ k < m, ∀ v, Supported (G k) v →
      Supported (G (k + 1)) (D.liftedStep (k + 1) (permOp (D.eventPerm E ω k) v)))
    (hGE' : ∀ k < m, ∀ v, Supported (G k) v →
      Supported (G (k + 1)) (D.liftedStep (k + 1) (permOp (D.eventPerm E' ω' k) v)))
    (hcount : ∀ r ∈ G m, ((range m).filter fun k => (splitLogs r).2 ∈ Lc k).card ≤ q') :
    ‖D.run E ω - D.run E' ω'‖ ≤
      2 * √q' * √(∑ k ∈ range m, ‖mask (B k) (D.stage E ω k)‖ ^ 2) := by
  have hreach : ∀ k ≤ m, ∃ w : ℕ → QState (GameReg W n X Y Req A m),
      D.stage E ω k - D.stage E' ω' k = ∑ i ∈ range k, w i ∧
      ∀ i < k, ‖w i‖ ≤ 2 * ‖mask (B i) (D.stage E ω i)‖ ∧
        Supported (logsIn (Lc i) ∩ G k) (w i) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨fun _ => 0, by simp [stage], fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨w, hw, hwb⟩ := ih (by omega)
      set s := D.stage E ω k with hs
      set π := D.eventPerm E ω k
      set π' := D.eventPerm E' ω' k
      set δ := permOp π s - permOp π' s with hδdef
      refine ⟨fun i => if i < k then D.liftedStep (k + 1) (permOp π' (w i))
        else D.liftedStep (k + 1) δ, ?_, ?_⟩
      · have e1 : D.stage E ω (k + 1) - D.stage E' ω' (k + 1) =
            D.liftedStep (k + 1) (permOp π' (D.stage E ω k - D.stage E' ω' k)) +
              D.liftedStep (k + 1) δ := by
          rw [stage_succ, stage_succ, ← map_add, ← map_sub]
          congr 1
          rw [hδdef, map_sub]
          abel
        rw [e1, hw, map_sum, map_sum, sum_range_succ]
        simp only [lt_irrefl, ↓reduceIte]
        congr 1
        exact sum_congr rfl fun i hi => by simp only [mem_range.1 hi, ↓reduceIte]
      · intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hik | rfl
        · simp only [hik, ↓reduceIte]
          obtain ⟨hn, hsu⟩ := hwb i hik
          refine ⟨by rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]; exact hn, ?_⟩
          have h1 := (hsu.mono Set.inter_subset_left).permOp (π := π') fun r hr =>
            (D.mem_logsIn_eventPerm_iff E' ω' (hLc i) hik r).2 hr
          have h2 := hGE' k (by omega) _ (hsu.mono Set.inter_subset_right)
          exact (h1.logControlled _).inter h2
        · simp only [lt_irrefl, ↓reduceIte]
          have hsR := D.stage_supported E ω i
          have hc : Supported (logsIn (reachableLogs i) ∩ (B i)ᶜ) (mask (B i)ᶜ s) :=
            hsR.mask_inter _
          have hδ : δ = permOp π (mask (B i) s) - permOp π' (mask (B i) s) := by
            rw [hδdef]
            conv_lhs => rw [← mask_add_mask_compl (B i) s]
            rw [map_add, map_add, hc.permOp_eq fun r hr => hB i (by omega) r hr.1 hr.2]
            abel
          refine ⟨?_, ?_⟩
          · rw [LinearIsometryEquiv.norm_map, hδ, two_mul]
            refine (norm_sub_le _ _).trans ?_
            rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
          · have hm : Supported (logsIn (reachableLogs i) ∩ B i) (mask (B i) s) :=
              hsR.mask_inter _
            have hd : Supported (logsIn (Lc i)) δ := by
              rw [hδ]
              exact (hm.permOp fun r hr => (hBC i (by omega) r hr.1 hr.2).1).sub
                (hm.permOp fun r hr => (hBC i (by omega) r hr.1 hr.2).2)
            have hG : Supported (G (i + 1)) (D.liftedStep (i + 1) δ) := by
              rw [hδdef, map_sub]
              exact (hGE i (by omega) s (hGv i (by omega))).sub
                (hGE' i (by omega) s (hGv i (by omega)))
            exact (hd.logControlled _).inter hG
  obtain ⟨w, hw, hwb⟩ := hreach m le_rfl
  have hsum : 0 ≤ ∑ k ∈ range m, ‖mask (B k) (D.stage E ω k)‖ ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt hsum, run, run, hw]
  refine (norm_sum_sq_le_of_count (range m) q' w (fun i => logsIn (Lc i)) (G m)
    (fun i hi => (hwb i (mem_range.1 hi)).2) hcount).trans ?_
  calc (q' : ℝ) * ∑ i ∈ range m, ‖w i‖ ^ 2
      ≤ q' * ∑ i ∈ range m, (2 * ‖mask (B i) (D.stage E ω i)‖) ^ 2 := by
        gcongr with i hi
        exact (hwb i (mem_range.1 hi)).1
    _ = 2 ^ 2 * q' * ∑ k ∈ range m, ‖mask (B k) (D.stage E ω k)‖ ^ 2 := by
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun i _ => ?_
        ring

end Distinguisher

end GordieHowe.Quantum
