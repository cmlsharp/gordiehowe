-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.O2H.Budget
public import GordieHowe.Model.Quantum.Pure.RequestBudget

@[expose] public section

/-!
# O2H at one request with a request budget

`Distinguisher.advantage_acceptProbOn_made_le_of_fresh_secret_budget` (`GordieHowe/Model/Quantum/O2H/Budget.lean`)
bounds the O2H step at request `j` by `2 q √(n ε)` for a distinguisher that queries at no more
than `q` slots on every branch. This file proves the same bound for a distinguisher with a request
budget of `q` slots (`Distinguisher.RequestBudget`): every branch queries at no more than `q`
slots before each of its requests, and any number of times after its last one.

**The argument** (our statement). The oracles of the two environments differ only on branches
that have not made request `j`. Call such a branch at slot `k` *dead* if it has queried at more
than `q` of the slots up to `k`: by the request budget it never requests again, so it never makes
request `j` and is not measured by the game restricted to `madeLogs j`. Run the game of `E'` with
the oracle of `E` on the dead branches (`Mid`): the oracles of the two runs differ only on dead
branches, which stay dead, so the parts of the final states off the dead branches agree
(`OracleAlg.mask_compl_stageVar_eq_stage`), and so do the restricted acceptance probabilities.
The runs with the oracle of `E` and with `Mid` differ only on live branches that have not made
request `j`, and a live branch is charged only for its at most `q` query slots up to the count
`q` (`queriedWithin`). AHU19 Lemma 8 with a per-branch count
(`OracleAlg.StepCount.norm_final_sub_finalVar_le`, the oracle of the second run changing from
step to step) and the averaging of `O2HSetting.o2h_fresh_secret_of_count` give `2 q √(n ε)`.

- `Distinguisher.advantage_acceptProbOn_made_le_of_fresh_secret_requestBudget`: the bound.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

/-! ### Runs whose oracle changes from step to step -/

namespace OracleAlg

variable {Z ι : Type*} [Fintype ι] {d : ℕ} (A : OracleAlg Z ι d)

/-- The run of `A` on input `z` with oracle `permOp (π k)` at oracle step `k`. -/
noncomputable def stageVar (π : ℕ → Equiv.Perm ι) (z : Z) : ℕ → QState ι :=
  hybrid (A.stepAt z) (fun k => permOp (π k)) (A.init z)

/-- The final state of the run with oracle `permOp (π k)` at step `k`. -/
noncomputable def finalVar (π : ℕ → Equiv.Perm ι) (z : Z) : QState ι :=
  A.stageVar π z d

/-- The probability that `A` outputs `1` on input `z` with oracle `permOp (π k)` at step `k`. -/
noncomputable def acceptProbVar (π : ℕ → Equiv.Perm ι) (z : Z) : ℝ :=
  prob (A.accept z) (A.finalVar π z)

theorem stageVar_zero (π : ℕ → Equiv.Perm ι) (z : Z) :
    A.stageVar π z 0 = A.stepAt z 0 (A.init z) :=
  rfl

theorem stageVar_succ (π : ℕ → Equiv.Perm ι) (z : Z) (k : ℕ) :
    A.stageVar π z (k + 1) = A.stepAt z (k + 1) (permOp (π k) (A.stageVar π z k)) :=
  rfl

@[simp]
theorem norm_stageVar (π : ℕ → Equiv.Perm ι) (z : Z) (k : ℕ) : ‖A.stageVar π z k‖ = 1 := by
  rw [stageVar, norm_hybrid, A.norm_init]

/-- The acceptance probabilities of a run and of a run with a changing oracle differ by at most
the distance of their final states. -/
theorem abs_acceptProb_sub_acceptProbVar_le (π : Equiv.Perm ι) (π' : ℕ → Equiv.Perm ι) (z : Z) :
    |A.acceptProb π z - A.acceptProbVar π' z| ≤ ‖A.final π z - A.finalVar π' z‖ :=
  abs_prob_sub_le _ (A.norm_final π z) (A.norm_stageVar π' z d)

/-- A basis permutation that keeps `S` commutes with the mask of the complement of `S`. -/
theorem mask_compl_permOp {S : Set ι} {π : Equiv.Perm ι} (h : ∀ r, π r ∈ S ↔ r ∈ S)
    (v : QState ι) : mask Sᶜ (permOp π v) = permOp π (mask Sᶜ v) := by
  ext i
  have hi : π.symm i ∈ S ↔ i ∈ S := by
    have := h (π.symm i)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  by_cases hS : i ∈ S
  · rw [mask_apply_of_notMem _ (by simpa using hS), permOp_apply,
      mask_apply_of_notMem _ (by simpa using hi.2 hS)]
  · rw [mask_apply_of_mem _ hS, permOp_apply, permOp_apply,
      mask_apply_of_mem _ (by simpa using fun h => hS (hi.1 h))]

/-- **Changes on dead branches are invisible off them.** Let the runs with oracles `π` and
`π' k` stay in `G k`, let the oracles agree outside sets `X k` that they keep, and let a step keep
a vector on `G k ∩ X k` inside `X (k + 1)`. Then the two runs have the same part outside `X k`. -/
theorem mask_compl_stageVar_eq_stage {z : Z} {G C X : ℕ → Set ι} {q : ℕ}
    (h : A.StepCount z G C q) {π : Equiv.Perm ι} {π' : ℕ → Equiv.Perm ι}
    (hπ : Respects π G C) (hπ' : ∀ k, Respects (π' k) G C)
    (hπX : ∀ k < d, ∀ r, π r ∈ X k ↔ r ∈ X k) (hπ'X : ∀ k < d, ∀ r, π' k r ∈ X k ↔ r ∈ X k)
    (hagree : ∀ k < d, ∀ r ∉ X k, π' k r = π r)
    (hX : ∀ k < d, ∀ v, Supported (G k ∩ X k) v → Supported (X (k + 1)) (A.stepAt z (k + 1) v)) :
    ∀ k ≤ d, Supported (G k) (A.stageVar π' z k) ∧
      mask (X k)ᶜ (A.stageVar π' z k) = mask (X k)ᶜ (A.stage π z k) := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨h.init, rfl⟩
  | succ k ih =>
    intro hk
    obtain ⟨hG', hm⟩ := ih (by omega)
    have hG := h.stage_supported hπ k (by omega)
    have hcut : ∀ v, Supported (G k) v → mask (X (k + 1))ᶜ (A.stepAt z (k + 1) v) =
        mask (X (k + 1))ᶜ (A.stepAt z (k + 1) (mask (X k)ᶜ v)) := by
      intro v hv
      have hvX : Supported (G k ∩ X k) (mask (X k) v) := fun r hr => by
        by_cases hrX : r ∈ X k
        · rw [mask_apply_of_mem _ hrX]
          exact hv r fun hrG => hr ⟨hrG, hrX⟩
        · exact mask_apply_of_notMem _ hrX
      have h0 : mask (X (k + 1))ᶜ (A.stepAt z (k + 1) (mask (X k) v)) = 0 := by
        ext r
        by_cases hr : r ∈ X (k + 1)
        · rw [mask_apply_of_notMem _ (by simpa using hr)]
          rfl
        · rw [mask_apply_of_mem _ (show r ∈ (X (k + 1))ᶜ from hr), hX k (by omega) _ hvX r hr]
          rfl
      conv_lhs => rw [← mask_add_mask_compl (X k) v]
      rw [map_add, map_add, h0, zero_add]
    refine ⟨h.stepG k (by omega) _ (hG'.permOp ((hπ' k).mapsTo k)), ?_⟩
    rw [stageVar_succ, stage_succ, hcut _ (hG'.permOp ((hπ' k).mapsTo k)),
      hcut _ (hG.permOp (hπ.mapsTo k)), mask_compl_permOp (hπ'X k (by omega)),
      mask_compl_permOp (hπX k (by omega)), hm, permOp_mask_compl (hagree k (by omega))]

namespace StepCount

variable {A} {z : Z} {G C : ℕ → Set ι} {q : ℕ}

/-- The run with oracles that respect `G` stays in `G`. -/
theorem stageVar_supported (h : A.StepCount z G C q) {π : ℕ → Equiv.Perm ι}
    (hπ : ∀ k, Respects (π k) G C) : ∀ k ≤ d, Supported (G k) (A.stageVar π z k)
  | 0, _ => h.init
  | k + 1, hk => h.stepG k (by omega) _
      ((h.stageVar_supported hπ k (by omega)).permOp ((hπ k).mapsTo k))

/-- **The hybrid as a sum, with a changing second oracle.** As
`StepCount.exists_stage_sub_eq_sum`, with the oracle `π' k` of the second run and the set
`B k` outside which it agrees with `π` depending on the step. -/
theorem exists_stage_sub_stageVar_eq_sum (h : A.StepCount z G C q) {π : Equiv.Perm ι}
    {π' : ℕ → Equiv.Perm ι} (hπ : Respects π G C) (hπ' : ∀ k, Respects (π' k) G C)
    {B : ℕ → Set ι} (hB : ∀ k, ∀ r ∉ B k, π r = π' k r)
    (hBC : ∀ k < d, ∀ r ∈ B k, r ∈ G k → r ∈ C k) :
    ∀ k ≤ d, ∃ w : ℕ → QState ι, A.stage π z k - A.stageVar π' z k = ∑ i ∈ range k, w i ∧
      ∀ i < k, ‖w i‖ ≤ 2 * ‖mask (B i) (A.stage π z i)‖ ∧ Supported (C i ∩ G k) (w i) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨fun _ => 0, by simp [stage_zero, stageVar_zero], fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨w, hw, hwb⟩ := ih (by omega)
    set s := A.stage π z k
    set δ := permOp π s - permOp (π' k) s with hδdef
    refine ⟨fun i => if i < k then A.stepAt z (k + 1) (permOp (π' k) (w i))
      else A.stepAt z (k + 1) δ, ?_, ?_⟩
    · have e1 : A.stage π z (k + 1) - A.stageVar π' z (k + 1) =
          A.stepAt z (k + 1) (permOp (π' k) (A.stage π z k - A.stageVar π' z k)) +
            A.stepAt z (k + 1) δ := by
        rw [stage_succ, stageVar_succ, ← map_add, ← map_sub]
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
        obtain ⟨hn, hs⟩ := hwb i hik
        refine ⟨by rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]; exact hn, ?_⟩
        have h1 := (hs.mono Set.inter_subset_left).permOp (π := π' k) fun r hr =>
          ((hπ' k).mem_iff i r).2 hr
        have h2 := (hs.mono Set.inter_subset_right).permOp ((hπ' k).mapsTo k)
        exact (h.stepC i k hik.le (by omega) _ h1).inter (h.stepG k (by omega) _ h2)
      · simp only [lt_irrefl, ↓reduceIte]
        refine ⟨by rw [LinearIsometryEquiv.norm_map]; exact norm_permOp_sub_le (hB i) s, ?_⟩
        have hδ : δ = permOp π (mask (B i) s) - permOp (π' i) (mask (B i) s) := by
          rw [hδdef]
          conv_lhs => rw [← mask_add_mask_compl (B i) s]
          rw [map_add, map_add, permOp_mask_compl (hB i)]
          abel
        have hsG := h.stage_supported hπ i (by omega)
        have hm : Supported (C i ∩ G i) (mask (B i) s) := fun r hr => by
          by_cases hrB : r ∈ B i
          · rw [mask_apply_of_mem _ hrB]
            by_cases hrG : r ∈ G i
            · exact absurd ⟨hBC i (by omega) r hrB hrG, hrG⟩ hr
            · exact hsG r hrG
          · exact mask_apply_of_notMem _ hrB
        have hpres : ∀ ρ : Equiv.Perm ι, Respects ρ G C →
            Supported (C i ∩ G i) (permOp ρ (mask (B i) s)) := fun ρ hρ =>
          hm.permOp fun r hr => ⟨(hρ.mem_iff i r).2 hr.1, hρ.mapsTo i r hr.2⟩
        have hd : Supported (C i ∩ G i) δ := by
          rw [hδ]
          exact (hpres π hπ).sub (hpres (π' i) (hπ' i))
        exact (h.stepC i i le_rfl (by omega) _ (hd.mono Set.inter_subset_left)).inter
          (h.stepG i (by omega) _ (hd.mono Set.inter_subset_right))

/-- **AHU19 Lemma 8 with a per-branch count and a changing second oracle**: as
`StepCount.norm_final_sub_le`, with the oracle `π' k` and the set `B k` depending on the step. -/
theorem norm_final_sub_finalVar_le (h : A.StepCount z G C q) {π : Equiv.Perm ι}
    {π' : ℕ → Equiv.Perm ι} (hπ : Respects π G C) (hπ' : ∀ k, Respects (π' k) G C)
    {B : ℕ → Set ι} (hB : ∀ k, ∀ r ∉ B k, π r = π' k r)
    (hBC : ∀ k < d, ∀ r ∈ B k, r ∈ G k → r ∈ C k) :
    ‖A.final π z - A.finalVar π' z‖ ≤ 2 * √q * √(∑ i : Fin d, prob (B i) (A.pre π z i)) := by
  obtain ⟨w, hw, hwb⟩ := h.exists_stage_sub_stageVar_eq_sum hπ hπ' hB hBC d le_rfl
  have hsum : 0 ≤ ∑ i : Fin d, prob (B i) (A.pre π z i) := sum_nonneg fun _ _ => prob_nonneg _ _
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt hsum, final, finalVar, hw]
  refine (norm_sum_sq_le_of_count (range d) q w C (G d) (fun i hi => (hwb i (mem_range.1 hi)).2)
    h.count).trans ?_
  calc (q : ℝ) * ∑ i ∈ range d, ‖w i‖ ^ 2
      ≤ q * ∑ i ∈ range d, (2 * ‖mask (B i) (A.stage π z i)‖) ^ 2 := by
        gcongr with i hi
        exact (hwb i (mem_range.1 hi)).1
    _ = 2 ^ 2 * q * ∑ i : Fin d, prob (B i) (A.pre π z i) := by
        rw [sum_range (fun i => (2 * ‖mask (B i) (A.stage π z i)‖) ^ 2), mul_sum, mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [prob, pre]
        ring

end StepCount

end OracleAlg

/-! ### Query slots up to the count `q` -/

section Logs

variable {Req : Type*} {m : ℕ}

/-- The count of query slots does not decrease. -/
theorem queriesBefore_mono (lg : LogReg Req m) {k k' : ℕ} (h : k ≤ k') :
    queriesBefore lg k ≤ queriesBefore lg k' :=
  card_le_card fun i hi => by
    simp only [mem_filter, mem_range] at hi ⊢
    exact ⟨by omega, hi.2⟩

/-- **The slot `i` is a query slot within the count `q`** on the logs `lg`: it is a query slot
and the branch has queried at no more than `q` slots up to and including it. -/
def queriedWithin (q : ℕ) (lg : LogReg Req m) (i : ℕ) : Prop :=
  queriedAt lg i = true ∧ queriesBefore lg (i + 1) ≤ q

instance (q : ℕ) (lg : LogReg Req m) : DecidablePred (queriedWithin q lg) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- At most `q` slots below `K` are query slots within the count `q`, and no more than the query
slots below `K`. -/
theorem card_queriedWithin_le (q : ℕ) (lg : LogReg Req m) (K : ℕ) :
    ((range K).filter fun i => queriedWithin q lg i).card ≤ q ∧
      ((range K).filter fun i => queriedWithin q lg i).card ≤ queriesBefore lg K := by
  classical
  induction K with
  | zero => simp
  | succ K ih =>
    rw [range_add_one, filter_insert, queriesBefore_succ]
    by_cases hK : queriedWithin q lg K
    · rw [if_pos hK, card_insert_of_notMem (by simp), if_pos hK.1]
      have := hK.2
      rw [queriesBefore_succ, if_pos hK.1] at this
      omega
    · rw [if_neg hK]
      split_ifs <;> omega

end Logs

/-! ### The request budget along the game -/

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} {D : Distinguisher W X Y Req A n m} {q : ℕ}

namespace RequestBudget

/-- **A request budget holds before oracle step `k` of the game**, on a content `s` of the work
register: its logs after slot `k` are blank, and for `k < m` its log of slot `k` records the kind of
the slot and its workspace is in `inv k` at its number of query slots before `k`. -/
structure Holds (rb : D.RequestBudget q) (k : ℕ) (s : W × Req × Option A × LogReg Req m) :
    Prop where
  blank : ∀ k' : Fin m, k < k' → s.2.2.2 k' = none
  logged : k < m → queriedAt s.2.2.2 k = !D.kind s.1
  mem : k < m → s.1 ∈ rb.inv k (queriesBefore s.2.2.2 k)

/-- **A request budget holds after the step before slot `k`**: the logs from slot `k` on are blank
and the workspace is in `inv k` at the number of query slots before `k`. -/
structure HoldsBefore (rb : D.RequestBudget q) (k : ℕ) (s : W × Req × Option A × LogReg Req m) :
    Prop where
  blank : ∀ k' : Fin m, k ≤ k' → s.2.2.2 k' = none
  mem : s.1 ∈ rb.inv k (queriesBefore s.2.2.2 k)

variable (rb : D.RequestBudget q)

/-- After the last slot the request budget holds. -/
theorem holds_of_le {k : ℕ} (hk : m ≤ k) (s : W × Req × Option A × LogReg Req m) :
    rb.Holds k s where
  blank k' hk' := absurd k'.2 (by omega)
  logged h := absurd h (by omega)
  mem h := absurd h (by omega)

variable [DecidableEq Req] [DecidableEq A] {Ω : Type*} {Q : ℕ}

/-- **The request of slot `k` keeps the request budget**: it logs the slot's kind. -/
theorem holds_requestPerm (E : Env Ω Req A X Y Q) (ω : Ω) {k : ℕ} (hk : k < m)
    {r : GameReg W n X Y Req A m} (hr : rb.HoldsBefore k r.1) :
    rb.Holds k (E.requestPerm D.kind ω ⟨k, hk⟩ r).1 := by
  have hws : (E.requestPerm D.kind ω ⟨k, hk⟩ r).1.1 = r.1.1 := E.workspace_requestPerm D.kind ω _ r
  have h0 : r.1.2.2.2 ⟨k, hk⟩ = none := hr.blank ⟨k, hk⟩ le_rfl
  have hlg := Budget.logs_requestPerm_of_blank (D := D) E ω hk h0
  have hlt : ∀ i : Fin m, (i : ℕ) < k →
      (E.requestPerm D.kind ω ⟨k, hk⟩ r).1.2.2.2 i = r.1.2.2.2 i := by
    intro i hi
    rw [hlg]
    split_ifs
    · exact Function.update_of_ne (Fin.ne_of_val_ne (by simp; omega)) _ _
    · rfl
  have hqb := queriesBefore_congr hlt
  have hqa : queriedAt (E.requestPerm D.kind ω ⟨k, hk⟩ r).1.2.2.2 k = !D.kind r.1.1 := by
    simp only [queriedAt, hk, ↓reduceDIte]
    rw [hlg]
    cases hkind : D.kind r.1.1 <;> simp [h0]
  refine ⟨?_, fun _ => by rw [hqa, hws], fun _ => by rw [hws, hqb]; exact hr.mem⟩
  intro k' hk'
  rw [hlg]
  split_ifs
  · rw [Function.update_of_ne (Fin.ne_of_val_ne (by simp; omega))]
    exact hr.blank k' hk'.le
  · exact hr.blank k' hk'.le

omit [DecidableEq Req] [DecidableEq A] in
/-- **The step before slot `k + 1` keeps the request budget** (`RequestBudget.step`), slice by
slice of the logs. -/
theorem holdsBefore_liftedStep (k : ℕ) (hk : k + 1 < m) {v : QState (GameReg W n X Y Req A m)}
    (hv : Supported {r | rb.Holds k r.1} v) :
    Supported {r | rb.HoldsBefore (k + 1) r.1} (D.liftedStep (k + 1) v) := by
  classical
  set S' : LogReg Req m → Set (DReg W n X Y Req A) := fun lg =>
    {d | (∀ k' : Fin m, k < k' → lg k' = none) ∧
      d.workspace ∈ rb.inv (k + 1) (queriesBefore lg (k + 1))}
  have key := supported_logControlled_of_slices (fun _ => D.stepAt (k + 1)) v (S := S')
    fun lg => by
      by_cases hlg : ∀ k' : Fin m, k < k' → lg k' = none
      · have hslice : Supported {d : DReg W n X Y Req A |
            d.workspace ∈ rb.inv k (queriesBefore lg k) ∧ D.kind d.workspace = !queriedAt lg k}
            (WithLp.toLp 2 fun d => v (splitLogs.symm (d, lg))) := by
          intro d hd
          show v (splitLogs.symm (d, lg)) = 0
          refine hv _ fun hH => hd ⟨hH.mem (by omega), ?_⟩
          have := hH.logged (by omega)
          change queriedAt lg k = !D.kind d.workspace at this
          rw [this, Bool.not_not]
        have hstep := rb.step k hk _ _ _ hslice
        simp only [stepAt, show k + 1 < m + 1 by omega, ↓reduceDIte]
        refine hstep.mono fun d hd => ⟨hlg, ?_⟩
        have hd' : d.workspace ∈ rb.inv (k + 1)
            (if !queriedAt lg k then queriesBefore lg k else queriesBefore lg k + 1) := hd
        rw [queriesBefore_succ]
        cases h : queriedAt lg k <;> simpa [h] using hd'
      · have h0 : (WithLp.toLp 2 fun d => v (splitLogs.symm (d, lg)) :
            QState (DReg W n X Y Req A)) = 0 := by
          ext d
          exact hv _ fun hH => hlg hH.blank
        rw [h0, map_zero]
        intro _ _
        rfl
  refine key.mono fun r hr => ?_
  obtain ⟨h2, h3⟩ := hr
  exact ⟨fun k' hk' => h2 k' (by omega), h3⟩

omit [DecidableEq A] in
/-- The first step keeps the request budget (`RequestBudget.init`). -/
theorem holdsBefore_liftedStep_zero (hm : 0 < m) :
    Supported {r : GameReg W n X Y Req A m | rb.HoldsBefore 0 r.1}
      (D.liftedStep 0 D.gameInit) := by
  classical
  have key := supported_logControlled_of_slices (fun _ => D.stepAt 0) D.gameInit
    (S := fun lg => {d | (lg = fun _ => none) ∧ d.workspace ∈ rb.inv 0 0}) fun lg => by
      by_cases hlg : lg = fun _ => none
      · have hslice : (WithLp.toLp 2 fun d => D.gameInit (splitLogs.symm (d, lg)) :
            QState (DReg W n X Y Req A)) = D.init := by
          ext d
          simp [gameInit, hlg]
        have h0 : D.stepAt 0 = D.step 0 := by simp [stepAt]
        rw [hslice, h0]
        exact (rb.init hm).mono fun d hd => ⟨hlg, hd⟩
      · have hslice : (WithLp.toLp 2 fun d => D.gameInit (splitLogs.symm (d, lg)) :
            QState (DReg W n X Y Req A)) = 0 := by
          ext d
          simp [gameInit, hlg]
        rw [hslice, map_zero]
        intro _ _
        rfl
  refine key.mono fun r hr => ?_
  obtain ⟨hlg, hmem⟩ := hr
  have hlg' : r.1.2.2.2 = fun _ => none := hlg
  have hq0 : queriesBefore r.1.2.2.2 0 = 0 := queriesBefore_zero _
  exact ⟨fun k' _ => by rw [hlg'], by rw [hq0]; exact hmem⟩

variable (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))

/-- The steps of the game after slot `i` keep every set of logs determined by the kinds of the
slots up to `i`. -/
theorem supported_gameStep_logs_le (E : Env Ω Req A X Y Q) (ω : Ω) {k i : ℕ} (hik : i < k)
    {L : Set (LogReg Req m)}
    (hL : ∀ lg lg' : LogReg Req m, (∀ i' ≤ i, queriedAt lg i' = queriedAt lg' i') →
      (lg ∈ L ↔ lg' ∈ L)) {v : QState (GameReg W n X Y Req A m)} (hv : Supported (logsIn L) v) :
    Supported (logsIn L) (D.gameStep E post ω k v) := by
  have h1 := hv.logControlled (fun _ => D.stepAt k)
  unfold gameStep
  split_ifs with hk
  · rw [LinearIsometryEquiv.trans_apply]
    refine h1.permOp fun r hr => ?_
    simp only [mem_logsIn] at hr ⊢
    exact (hL _ _ fun i' hi' =>
      Budget.queriedAt_requestPerm_of_ne (D := D) E ω hk r (by omega)).2 hr
  · rw [LinearIsometryEquiv.trans_apply]
    exact h1.logControlled _

omit [Fintype Req] [DecidableEq Req] in
/-- The query slots within the count `q` up to slot `i` depend only on the kinds of those
slots. -/
theorem queriedWithin_congr {lg lg' : LogReg Req m} {i : ℕ}
    (h : ∀ i' ≤ i, queriedAt lg i' = queriedAt lg' i') :
    queriedWithin q lg i ↔ queriedWithin q lg' i := by
  have hqb : queriesBefore lg (i + 1) = queriesBefore lg' (i + 1) := by
    unfold queriesBefore
    congr 1
    exact filter_congr fun i' hi' => by rw [h i' (by simp at hi'; omega)]
  unfold queriedWithin
  rw [h i le_rfl, hqb]

/-- **The game counts the query slots within the count `q`** (`OracleAlg.StepCount`): before
oracle step `k` the request budget holds, the branches that queried at slot `i` within the count
are kept by the later steps, and no branch has more than `q` such slots. -/
theorem stepCount_gameAlg (E : Env Ω Req A X Y Q) (L : Set (LogReg Req m)) (ω : Ω) :
    (D.gameAlg E post L).StepCount ω (fun k => {r | r.1 ∈ {s | rb.Holds k s}})
      (fun i => {r | r.1 ∈ {s : W × Req × Option A × LogReg Req m |
        queriedWithin q s.2.2.2 i}}) q where
  init := by
    rw [Budget.gameAlg_stepAt post E L ω (by omega)]
    by_cases hm : 0 < m
    · simp only [gameStep, hm, ↓reduceDIte, LinearIsometryEquiv.trans_apply]
      exact (rb.holdsBefore_liftedStep_zero hm).permOp fun r hr =>
        rb.holds_requestPerm E ω hm hr
    · intro r hr
      exact absurd (rb.holds_of_le (by omega) _) hr
  stepG k hk v hv := by
    rw [Budget.gameAlg_stepAt post E L ω (by omega)]
    by_cases hk1 : k + 1 < m
    · simp only [gameStep, hk1, ↓reduceDIte, LinearIsometryEquiv.trans_apply]
      exact (rb.holdsBefore_liftedStep k hk1 hv).permOp fun r hr =>
        rb.holds_requestPerm E ω hk1 hr
    · intro r hr
      exact absurd (rb.holds_of_le (by omega) _) hr
  stepC i k hik hk v hv := by
    rw [Budget.gameAlg_stepAt post E L ω (by omega)]
    exact supported_gameStep_logs_le post E ω (k := k + 1) (i := i)
      (L := {lg | queriedWithin q lg i}) (by omega)
      (fun lg lg' h => queriedWithin_congr h) hv
  stepCc i k hik hk v hv := by
    rw [Budget.gameAlg_stepAt post E L ω (by omega)]
    exact supported_gameStep_logs_le post E ω (k := k + 1) (i := i)
      (L := {lg | queriedWithin q lg i}ᶜ) (by omega)
      (fun lg lg' h => by simp only [Set.mem_compl_iff, Set.mem_setOf_eq,
        queriedWithin_congr h]) hv
  count r _ := by
    convert (card_queriedWithin_le q r.1.2.2.2 m).1 using 3
    exact Iff.rfl

/-- **The dead branches at oracle step `k`**, for request `j` and the halted workspaces `H`: the
branches that have queried at more than `q` of the slots up to `k` and have either not made request
`j` or halted. Under a request budget a dead branch that has not halted never requests again, and
the distinguisher does not accept on a halted one. -/
def deadSet (H : Set W) (q j k : ℕ) : Set (W × Req × Option A × LogReg Req m) :=
  {s | q < queriesBefore s.2.2.2 (k + 1) ∧ ((requests s.2.2.2).length ≤ j ∨ s.1 ∈ H)}

/-- The request of slot `k` keeps the number of query slots up to `k`... before `k`. -/
theorem queriesBefore_requestPerm (E : Env Ω Req A X Y Q) (ω : Ω) {k : ℕ} (hk : k < m)
    (r : GameReg W n X Y Req A m) :
    queriesBefore (E.requestPerm D.kind ω ⟨k, hk⟩ r).1.2.2.2 k = queriesBefore r.1.2.2.2 k := by
  unfold queriesBefore
  congr 1
  exact filter_congr fun i hi =>
    by rw [Budget.queriedAt_requestPerm_of_ne (D := D) E ω hk r (by simp at hi; omega)]

omit [DecidableEq Req] [DecidableEq A] in
/-- Two vectors supported in `S` add to a vector supported in `S`. -/
theorem supported_add {ι : Type*} [Fintype ι] {S : Set ι} {u v : QState ι}
    (hu : Supported S u) (hv : Supported S v) : Supported S (u + v) := fun r hr => by
  rw [PiLp.add_apply, hu r hr, hv r hr, add_zero]

omit [DecidableEq Req] [DecidableEq A] in
/-- **The halted part of a dead state, and the rest**: on the dead branches before oracle step `k`,
the halted part lies on the halted workspaces where the budget holds, and the other part on the
branches that queried at more than `q` slots up to `k` and have not made request `j`. -/
theorem split_dead {j k : ℕ} {v : QState (GameReg W n X Y Req A m)}
    (hv : Supported ({r | r.1 ∈ {s | rb.Holds k s}} ∩ {r | r.1 ∈ deadSet rb.halted q j k}) v) :
    Supported ({r | rb.Holds k r.1} ∩ {r | r.workspace ∈ rb.halted})
        (mask {r : GameReg W n X Y Req A m | r.workspace ∈ rb.halted} v) ∧
      Supported (logsIn {lg : LogReg Req m | q < queriesBefore lg (k + 1)})
        (mask {r : GameReg W n X Y Req A m | r.workspace ∈ rb.halted} v) ∧
      Supported ({r | r.1 ∈ {s | rb.Holds k s}} ∩ logsIn {lg : LogReg Req m |
          q < queriesBefore lg (k + 1) ∧ (requests lg).length ≤ j})
        (mask {r : GameReg W n X Y Req A m | r.workspace ∈ rb.halted}ᶜ v) := by
  set Hs : Set (GameReg W n X Y Req A m) := {r | r.workspace ∈ rb.halted}
  refine ⟨fun r hr => ?_, fun r hr => ?_, fun r hr => ?_⟩
  · by_cases hH : r ∈ Hs
    · rw [mask_apply_of_mem _ hH]
      exact hv r fun h => hr ⟨h.1, hH⟩
    · exact mask_apply_of_notMem _ hH
  · by_cases hH : r ∈ Hs
    · rw [mask_apply_of_mem _ hH]
      exact hv r fun h => hr h.2.1
    · exact mask_apply_of_notMem _ hH
  · by_cases hH : r ∈ Hs
    · exact mask_apply_of_notMem _ (by simpa using hH)
    · rw [mask_apply_of_mem _ (show r ∈ Hsᶜ from hH)]
      refine hv r fun h => hr ⟨h.1, h.2.1, ?_⟩
      rcases h.2.2 with h' | h'
      · exact h'
      · exact absurd h' hH

omit [DecidableEq Req] [DecidableEq A] in
/-- **The step after slot `k` keeps the halted branches** (`RequestBudget.halted_step`), slice by
slice of the logs: on a halted branch where the budget holds before oracle step `k`, the step
lands in `inv (k + 1)` at the number of query slots before `k`, still halted. -/
theorem supported_halted_liftedStep_le (k : ℕ) (hk : k + 1 < m + 1) (hkm : k < m)
    {v : QState (GameReg W n X Y Req A m)}
    (hv : Supported ({r | rb.Holds k r.1} ∩ {r | r.workspace ∈ rb.halted}) v) :
    Supported {r : GameReg W n X Y Req A m |
        (splitLogs r).1.workspace ∈ rb.inv (k + 1) (queriesBefore (splitLogs r).2 k) ∧
          r.workspace ∈ rb.halted} (D.liftedStep (k + 1) v) := by
  have key := supported_logControlled_of_slices (fun _ => D.stepAt (k + 1)) v
    (S := fun lg => {d | d.workspace ∈ rb.inv (k + 1) (queriesBefore lg k) ∧
      d.workspace ∈ rb.halted}) fun lg => by
      have hslice : Supported {d : DReg W n X Y Req A |
          d.workspace ∈ rb.inv k (queriesBefore lg k) ∧ d.workspace ∈ rb.halted}
          (WithLp.toLp 2 fun d => v (splitLogs.symm (d, lg))) := by
        intro d hd
        show v (splitLogs.symm (d, lg)) = 0
        exact hv _ fun h => hd ⟨h.1.mem hkm, h.2⟩
      simp only [stepAt, hk, ↓reduceDIte]
      exact rb.halted_step k hk _ _ hslice
  exact key.mono fun r hr => hr

omit [DecidableEq Req] [DecidableEq A] in
/-- The step after slot `k` keeps the halted branches, before the last slot. -/
theorem supported_halted_liftedStep (k : ℕ) (hk1 : k + 1 < m) {v : QState (GameReg W n X Y Req A m)}
    (hv : Supported ({r | rb.Holds k r.1} ∩ {r | r.workspace ∈ rb.halted}) v) :
    Supported {r : GameReg W n X Y Req A m | r.workspace ∈ rb.halted} (D.liftedStep (k + 1) v) :=
  (rb.supported_halted_liftedStep_le k (by omega) (by omega) hv).mono fun r hr => hr.2

/-- **Dead branches stay dead** under the steps of the game before the last slot: a dead branch
that has not halted has used more than `q` query slots, so by the request budget it does not
request at the next slot; a halted branch stays halted (`RequestBudget.halted_step`). -/
theorem supported_deadSet_gameStep [AddGroup Y] (E : Env Ω Req A X Y Q) (L : Set (LogReg Req m))
    (ω : Ω) (j : ℕ) {k : ℕ} (hk1 : k + 1 < m) (v : QState (GameReg W n X Y Req A m))
    (hv : Supported ({r | r.1 ∈ {s | rb.Holds k s}} ∩ {r | r.1 ∈ deadSet rb.halted q j k}) v) :
    Supported {r : GameReg W n X Y Req A m | r.1 ∈ deadSet rb.halted q j (k + 1)}
      ((D.gameAlg E post L).stepAt ω (k + 1) v) := by
  classical
  rw [Budget.gameAlg_stepAt post E L ω (by omega)]
  simp only [gameStep, hk1, ↓reduceDIte, LinearIsometryEquiv.trans_apply]
  set Hs : Set (GameReg W n X Y Req A m) := {r | r.workspace ∈ rb.halted}
  set Lc : Set (LogReg Req m) := {lg | q < queriesBefore lg (k + 1)}
  have hgrow : ∀ lg : LogReg Req m, q < queriesBefore lg (k + 1) →
      q < queriesBefore lg (k + 1 + 1) := fun lg h =>
    h.trans_le (queriesBefore_mono lg (by omega))
  obtain ⟨h1H, h1L, h2⟩ := split_dead rb hv
  rw [(mask_add_mask_compl Hs v).symm, map_add, map_add]
  refine supported_add ?_ ?_
  · have hA := (rb.supported_halted_liftedStep k hk1 h1H).inter
      (h1L.logControlled (fun _ => D.stepAt (k + 1)))
    refine hA.permOp fun r hr => ⟨?_, Or.inr ?_⟩
    · change q < queriesBefore (E.requestPerm D.kind ω ⟨k + 1, hk1⟩ r).1.2.2.2 (k + 1 + 1)
      refine hgrow _ ?_
      rw [queriesBefore_requestPerm E ω hk1]
      exact hr.2
    · change (E.requestPerm D.kind ω ⟨k + 1, hk1⟩ r).1.1 ∈ rb.halted
      rw [E.workspace_requestPerm]
      exact hr.1
  · have hH := rb.holdsBefore_liftedStep k hk1 (h2.mono fun r hr => hr.1)
    have hL := (h2.mono fun r hr => hr.2).logControlled (fun _ => D.stepAt (k + 1))
    refine (hH.inter hL).permOp fun r hr => ?_
    obtain ⟨hHr, hd, hlen⟩ := hr
    by_cases hhalt : r.workspace ∈ rb.halted
    · refine ⟨?_, Or.inr ?_⟩
      · change q < queriesBefore (E.requestPerm D.kind ω ⟨k + 1, hk1⟩ r).1.2.2.2 (k + 1 + 1)
        refine hgrow _ ?_
        rw [queriesBefore_requestPerm E ω hk1]
        exact hd
      · change (E.requestPerm D.kind ω ⟨k + 1, hk1⟩ r).1.1 ∈ rb.halted
        rw [E.workspace_requestPerm]
        exact hhalt
    · have hkind : D.kind r.workspace = false := by
        by_contra hne
        rw [Bool.not_eq_false] at hne
        have := rb.capReq (k + 1) hk1 _ r.1.1 hHr.mem hne hhalt
        change q < queriesBefore r.1.2.2.2 (k + 1) at hd
        omega
      rw [D.requestPerm_of_query E ω hk1 hkind]
      exact ⟨hgrow _ hd, Or.inl hlen⟩

/-- **Dead branches do not accept**: after the last slot, the step and the final unitary send the
dead branches off the accepting branches that made request `j`. A dead branch that has not halted
has not made request `j`, and the final unitary rejects a halted one (`hpost`). -/
theorem supported_notAccept_gameStep [AddGroup Y] (hpost : rb.PostRejectsHalted post)
    (E : Env Ω Req A X Y Q) (ω : Ω) (j : ℕ) {k : ℕ} (hk : k < m) (hk1 : ¬ k + 1 < m)
    (v : QState (GameReg W n X Y Req A m))
    (hv : Supported ({r | r.1 ∈ {s | rb.Holds k s}} ∩ {r | r.1 ∈ deadSet rb.halted q j k}) v) :
    Supported (D.gameAccept ∩ logsIn (madeLogs j))ᶜ
      ((D.gameAlg E post (madeLogs j)).stepAt ω (k + 1) v) := by
  classical
  rw [Budget.gameAlg_stepAt post E _ ω (by omega)]
  simp only [gameStep, hk1, ↓reduceDIte, LinearIsometryEquiv.trans_apply]
  set Hs : Set (GameReg W n X Y Req A m) := {r | r.workspace ∈ rb.halted}
  have hkm : k + 1 = m := by omega
  obtain ⟨h1H, -, h2⟩ := split_dead rb hv
  rw [(mask_add_mask_compl Hs v).symm, map_add, map_add]
  refine supported_add ?_ ?_
  · have hA := rb.supported_halted_liftedStep_le k (by omega) hk h1H
    intro r hr
    have hr : r ∈ D.gameAccept ∩ logsIn (madeLogs j) := by simpa using hr
    rw [postOp, logControlled_apply]
    refine hpost _ (queriesBefore (splitLogs r).2 k) _ (fun d hd => ?_) _ hr.1
    exact hA _ fun h => hd (hkm ▸ h)
  · have hL : Supported (logsIn {lg : LogReg Req m | (requests lg).length ≤ j}) (mask Hsᶜ v) :=
      h2.mono fun r hr => hr.2.2
    refine ((hL.logControlled _).logControlled _).mono fun r hr hacc => ?_
    have hmade : j < (requests (splitLogs r).2).length := hacc.2
    have : (requests (splitLogs r).2).length ≤ j := hr
    omega

end RequestBudget

variable [DecidableEq Req] [DecidableEq A] [AddGroup Y] {Q : ℕ} {V R : Type*} [Fintype V]
  [Fintype R] (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))

/-- **O2H at request `j` for a fresh secret, with a request budget.** The hypotheses on `E` and
`E'` are those of `advantage_acceptProbOn_made_le_of_fresh_secret_budget`; the distinguisher has
a request budget of `q` slots (`Distinguisher.RequestBudget`): every branch queries at no more
than `q` slots before each of its requests, chosen at run time, and at any number after its last
request. The games against `E` and `E'`, restricted to the branches that make request `j`, are
distinguished with advantage at most `2 q √(n ε)`. -/
theorem advantage_acceptProbOn_made_le_of_fresh_secret_requestBudget (rb : D.RequestBudget q)
    (hpost : rb.PostRejectsHalted post)
    (E E' : Env (V × R) Req A X Y Q) {μV : PMF V} {ν : PMF R} {T : R → Set X} {ε : ℝ} (j : ℕ)
    (hμ : ∀ v σ, E.μ (v, σ) = μV v * ν σ) (hμ' : E'.μ = E.μ)
    (hans : ∀ ω rs req, E.answerAfter ω rs req = E'.answerAfter ω rs req)
    (hafter : ∀ ω rs, j < rs.length → E.oracleIn ω rs = E'.oracleIn ω rs)
    (hbefore : ∀ ω rs, rs.length ≤ j → ∀ x ∉ T ω.2, E.oracleIn ω rs x = E'.oracleIn ω rs x)
    (hfreshOracle : ∀ v σ σ' rs, rs.length ≤ j → E.oracleIn (v, σ) rs = E.oracleIn (v, σ') rs)
    (hfreshAnswer : ∀ v σ σ' rs req, rs.length < j →
      E.answerAfter (v, σ) rs req = E.answerAfter (v, σ') rs req)
    (hε : ∀ x, (ν.toOuterMeasure {σ | x ∈ T σ}).toReal ≤ ε) :
    GordieHowe.advantage (D.acceptProbOn E post (madeLogs j)) (D.acceptProbOn E' post (madeLogs j)) ≤
      2 * q * √(n * ε) := by
  classical
  set Alg := D.gameAlg E post (madeLogs j)
  set G : ℕ → Set (GameReg W n X Y Req A m) := fun k => {r | r.1 ∈ {s | rb.Holds k s}}
  set C : ℕ → Set (GameReg W n X Y Req A m) := fun i =>
    {r | r.1 ∈ {s : W × Req × Option A × LogReg Req m | queriedWithin q s.2.2.2 i}}
  set Dd : ℕ → Set (W × Req × Option A × LogReg Req m) := fun k => RequestBudget.deadSet rb.halted q j k
  set πH : V × R → Equiv.Perm (GameReg W n X Y Req A m) := fun ω =>
    queryPermOf (E.oracleFn D.kind ω)
  set πG : V × R → Equiv.Perm (GameReg W n X Y Req A m) := fun ω =>
    queryPermOf (E'.oracleFn D.kind ω)
  set πM : V × R → ℕ → Equiv.Perm (GameReg W n X Y Req A m) := fun ω k =>
    queryPermOf fun s => if s ∈ Dd k then E.oracleFn D.kind ω s else E'.oracleFn D.kind ω s
  set M : ℕ → Set (W × Req × Option A × LogReg Req m) := fun k => {s | s ∈ D.openSet j ∧ s ∉ Dd k}
  set B : V × R → ℕ → Set (GameReg W n X Y Req A m) := fun ω k =>
    queriedOf fun s => if s ∈ M k then T ω.2 else ∅
  have hcount : ∀ ω, Alg.StepCount ω G C q := fun ω => rb.stepCount_gameAlg post E _ ω
  have hresp : ∀ F : W × Req × Option A × LogReg Req m → X → Y,
      OracleAlg.Respects (queryPermOf (n := n) F) G C := fun F =>
    respects_queryPermOf F _ _
  have hans' : ∀ ω (lg : LogReg Req m) k, E.answer ω lg k = E'.answer ω lg k := fun ω lg k => by
    simp only [Env.answer, funext (hans ω (requestsBefore lg k))]
  -- the run against `E'` and the run with `Mid` accept equally
  have hmid : ∀ ω, Alg.acceptProb (πG ω) ω = Alg.acceptProbVar (πM ω) ω := by
    intro ω
    set Xg : ℕ → Set (GameReg W n X Y Req A m) := fun k =>
      if k < m then {r | r.1 ∈ Dd k} else (D.gameAccept ∩ logsIn (madeLogs j))ᶜ
    have hXlt : ∀ k < m, Xg k = {r | r.1 ∈ Dd k} := fun k hk => by simp only [Xg, if_pos hk]
    have hX := Alg.mask_compl_stageVar_eq_stage (X := Xg) (hcount ω)
      (π := πG ω) (π' := πM ω)
      (hresp _) (fun k => hresp _) (fun k hk r => by rw [hXlt k hk]; exact Iff.rfl)
      (fun k hk r => by rw [hXlt k hk]; exact Iff.rfl)
      (fun k hk r hr => by
        rw [hXlt k hk] at hr
        have hr' : r.1 ∉ Dd k := hr
        simp only [πM, πG, queryPermOf_apply, if_neg hr'])
      (fun k hk v hv => by
        rw [hXlt k hk] at hv
        by_cases hk1 : k + 1 < m
        · rw [hXlt (k + 1) hk1]
          exact rb.supported_deadSet_gameStep post E _ ω j hk1 v hv
        · have hXm : Xg (k + 1) = (D.gameAccept ∩ logsIn (madeLogs j))ᶜ := by
            simp only [Xg, if_neg hk1]
          rw [hXm]
          exact rb.supported_notAccept_gameStep post hpost E ω j hk hk1 v hv) m le_rfl
    have hXm : Xg m = (D.gameAccept ∩ logsIn (madeLogs j))ᶜ := by simp only [Xg, lt_irrefl, if_false]
    have hset : Alg.accept ω = Alg.accept ω ∩ (Xg m)ᶜ := by
      rw [hXm, compl_compl]
      exact (Set.inter_self _).symm
    rw [OracleAlg.acceptProb, OracleAlg.acceptProbVar, OracleAlg.final, OracleAlg.finalVar, hset,
      prob_inter_eq_prob_mask, prob_inter_eq_prob_mask, hX.2]
  -- the per-tape bound
  set g : V × R → ℝ := fun ω => ∑ i : Fin m, prob (B ω i) (Alg.pre (πH ω) ω i) with hg
  have hstep : ∀ ω, |Alg.acceptProb (πH ω) ω - Alg.acceptProbVar (πM ω) ω| ≤
      2 * √q * √(g ω) := by
    intro ω
    refine (Alg.abs_acceptProb_sub_acceptProbVar_le _ _ _).trans ?_
    refine (hcount ω).norm_final_sub_finalVar_le (hresp _) (fun k => hresp _) (B := B ω)
      (fun k => queryPermOf_eq_of_notMem_queriedOf fun s x hx => ?_) ?_
    · by_cases hd : s ∈ Dd k
      · simp only [hd, ↓reduceIte]
      · simp only [hd, ↓reduceIte]
        refine (D.oracleFn_agree E E' (hafter ω) (hbefore ω) s x fun hxT => hx ?_).symm
        by_cases ho : s ∈ D.openSet j
        · have hM : s ∈ M k := ⟨ho, hd⟩
          simp only [ho, ↓reduceIte] at hxT
          simpa [hM] using hxT
        · simp [ho] at hxT
    · intro k hk r hr hrG
      obtain ⟨i, hi⟩ := hr
      have hM : r.1 ∈ M k := by
        by_contra hM
        simp [hM] at hi
      obtain ⟨⟨hkind, hlen⟩, hnd⟩ := hM
      have hlog := hrG.logged hk
      refine ⟨by rw [hlog, hkind]; rfl, ?_⟩
      by_contra hq
      exact hnd ⟨not_le.1 hq, Or.inl hlen⟩
  -- the probabilities as averages over the tape
  have hpL : ∑ ω, (E.μ ω).toReal * Alg.acceptProb (πH ω) ω =
      D.acceptProbOn E post (madeLogs j) :=
    sum_congr rfl fun ω _ => by rw [D.acceptProb_gameAlg_self E post _ ω]
  have hpR : ∑ ω, (E.μ ω).toReal * Alg.acceptProbVar (πM ω) ω =
      D.acceptProbOn E' post (madeLogs j) := by
    change _ = ∑ ω, (E'.μ ω).toReal * _
    rw [hμ']
    exact sum_congr rfl fun ω _ => by
      rw [← hmid ω, D.acceptProb_gameAlg E post E' _ ω (hans' ω) fun lg hlg =>
        hafter ω _ (by simpa [madeLogs] using hlg)]
  have hw : ∀ ω, 0 ≤ (E.μ ω).toReal := fun _ => ENNReal.toReal_nonneg
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => sum_nonneg fun _ _ => prob_nonneg _ _
  have hadv : GordieHowe.advantage (D.acceptProbOn E post (madeLogs j))
      (D.acceptProbOn E' post (madeLogs j)) ≤ 2 * √q * √(∑ ω, (E.μ ω).toReal * g ω) := by
    rw [← hpL, ← hpR, GordieHowe.advantage, ← sum_sub_distrib]
    calc |∑ ω, ((E.μ ω).toReal * Alg.acceptProb (πH ω) ω -
            (E.μ ω).toReal * Alg.acceptProbVar (πM ω) ω)|
        ≤ ∑ ω, (E.μ ω).toReal * (2 * √q * √(g ω)) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun ω _ => ?_)
          rw [← mul_sub, abs_mul, abs_of_nonneg (hw ω)]
          exact mul_le_mul_of_nonneg_left (hstep ω) (hw ω)
      _ = 2 * √q * ∑ ω, (E.μ ω).toReal * √(g ω) := by
          rw [mul_sum]
          exact sum_congr rfl fun ω _ => by ring
      _ ≤ 2 * √q * √(∑ ω, (E.μ ω).toReal * g ω) := by
          gcongr
          exact Real.sum_mul_sqrt_le_sqrt_sum_mul hw E.μ.sum_toReal hg0
  refine hadv.trans ?_
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · have hB0 : ∀ ω k, B ω k = ∅ := fun ω k => by
      ext r
      simp only [B, queriedOf, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      exact fun i => isEmptyElim (r.2 i).1
    have hg00 : ∀ ω, g ω = 0 := fun ω => by
      simp only [hg, hB0]
      refine sum_eq_zero fun i _ => ?_
      have hm : mask (∅ : Set (GameReg W n X Y Req A m)) (Alg.pre (πH ω) ω i) = 0 := by
        ext r
        simp
      rw [prob, hm, norm_zero, zero_pow two_ne_zero]
    simp only [hg00, mul_zero, sum_const_zero, Real.sqrt_zero]
    positivity
  have hε0 : 0 ≤ ε := ENNReal.toReal_nonneg.trans (hε x₀)
  -- the average of `g` is at most `n ε q`
  set Mr : ℕ → Set (GameReg W n X Y Req A m) := fun k => {r | r.1 ∈ M k}
  set Opn : Set (GameReg W n X Y Req A m) := {r | r.1 ∈ D.openSet j}
  have hq : ∀ v σ k (ψ : QState (GameReg W n X Y Req A m)),
      prob (B (v, σ) k) ψ = prob (queried (T σ)) (mask (Mr k) ψ) := by
    intro v σ k ψ
    have hset : B (v, σ) k = queried (T σ) ∩ Mr k := by
      ext r
      by_cases hr : r.1 ∈ M k
      · simp [B, queriedOf, queried, Mr, hr]
      · simp [B, queriedOf, queried, Mr, hr]
    rw [hset, prob_inter_eq_prob_mask]
  have hMO : ∀ k (ψ : QState (GameReg W n X Y Req A m)), mask (Mr k) ψ = mask (Mr k) (mask Opn ψ) :=
    fun k ψ => by
      ext r
      by_cases h : r ∈ Mr k
      · rw [mask_apply_of_mem _ h, mask_apply_of_mem _ h, mask_apply_of_mem _ (show r ∈ Opn from h.1)]
      · rw [mask_apply_of_notMem _ h, mask_apply_of_notMem _ h]
  have htuple : ∀ t : Fin n → X, (ν.toOuterMeasure {σ | ∃ i, t i ∈ T σ}).toReal ≤ n * ε := by
    intro t
    rw [Set.ofPred_exists]
    refine (ν.toReal_toOuterMeasure_iUnion_le _).trans ?_
    calc ∑ i, (ν.toOuterMeasure {σ | t i ∈ T σ}).toReal ≤ ∑ _i : Fin n, ε :=
          sum_le_sum fun i _ => hε (t i)
      _ = n * ε := by simp
  obtain ⟨σ₀, -⟩ := ν.support_nonempty
  have inner : ∀ v, ∑ σ, (ν σ).toReal * g (v, σ) ≤ n * ε * q := by
    intro v
    set ψ : Fin m → QState (GameReg W n X Y Req A m) := fun i => Alg.pre (πH (v, σ₀)) (v, σ₀) i
    calc ∑ σ, (ν σ).toReal * g (v, σ)
        = ∑ i : Fin m, ∑ σ, (ν σ).toReal * prob (queried (T σ)) (mask (Mr i) (ψ i)) := by
          simp only [hg, mul_sum]
          rw [sum_comm]
          refine sum_congr rfl fun i _ => sum_congr rfl fun σ _ => ?_
          rw [hq, hMO, hMO i (ψ i)]
          congr 3
          exact D.mask_pre_eq post E _ (hfreshAnswer v σ σ₀) (hfreshOracle v σ σ₀) i
      _ ≤ ∑ i : Fin m, n * ε * prob (Mr i) (ψ i) := by
          refine sum_le_sum fun i _ => ?_
          refine (sum_mul_prob_queried_le_mul_norm_sq ν T _ htuple).trans_eq ?_
          rw [prob]
      _ ≤ ∑ i : Fin m, n * ε * prob (C i) (ψ i) := by
          refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hsupp := (hcount (v, σ₀)).stage_supported (π := πH (v, σ₀)) (hresp _) i i.2.le
          refine hsupp.prob_le_of_inter_subset fun r hr hrG => ?_
          obtain ⟨⟨hkind, hlen⟩, hnd⟩ := hr
          have hlog := hrG.logged i.2
          refine ⟨by rw [hlog, hkind]; rfl, ?_⟩
          by_contra hqc
          exact hnd (show r.1 ∈ RequestBudget.deadSet rb.halted q j i from
            ⟨not_le.1 hqc, Or.inl hlen⟩)
      _ ≤ n * ε * q := by
          rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left ((hcount (v, σ₀)).sum_prob_pre_le (hresp _))
            (by positivity)
  have havg : ∑ ω, (E.μ ω).toReal * g ω ≤ n * ε * q := by
    rw [Fintype.sum_prod_type]
    simp_rw [hμ, ENNReal.toReal_mul, mul_assoc, ← mul_sum]
    calc ∑ v, (μV v).toReal * ∑ σ, (ν σ).toReal * g (v, σ) ≤ ∑ v, (μV v).toReal * (n * ε * q) :=
          sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (inner v) ENNReal.toReal_nonneg
      _ = n * ε * q := by rw [← sum_mul, μV.sum_toReal, one_mul]
      _ = n * (ε * q) := by ring
  calc 2 * √q * √(∑ ω, (E.μ ω).toReal * g ω) ≤ 2 * √q * √(n * ε * q) := by
        gcongr
    _ = 2 * q * √(n * ε) := by
        rw [Real.sqrt_mul (by positivity) q, mul_comm (√(n * ε)) (√q), ← mul_assoc,
          mul_assoc 2 (√q) (√q), Real.mul_self_sqrt (Nat.cast_nonneg _)]

end Distinguisher

end GordieHowe.Quantum
