-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.Budget
public import GordieHowe.Model.Quantum.O2H.Game

@[expose] public section

/-!
# O2H with a per-branch count of the oracle steps

AHU19 Theorem 3 (`O2HSetting.o2h`) charges every oracle step of an algorithm. When the algorithm
decides at run time, branch by branch, at which steps it queries the oracle (a distinguisher with a
query budget, `Distinguisher.Budget`), the bound should charge each branch only for the steps at
which it queries. This file proves that bound when the branches record which steps were queries in
a register that later steps do not change (the log registers of a game).

**The argument** (our statement; the hybrid is AHU19 Lemma 8, pp. 26–27). Write the difference of
the final states of the runs with oracles `π` and `π'` as a sum over the oracle steps `i` of
`w i`, the change at step `i` carried to the end by the run with `π'`
(`OracleAlg.StepCount.exists_stage_sub_eq_sum`); `‖w i‖ ≤ 2 ‖mask B vᵢ‖` for the state `vᵢ` before
step `i`. The vector `w i` lies on the basis states `C i` that queried at step `i`, and every
basis state reachable at the end lies in at most `q` of the sets `C i`, so Cauchy–Schwarz
basis state by basis state gives `‖∑ w i‖² ≤ q ∑ ‖w i‖²` (`norm_sum_sq_le_of_count`). Hence
`‖final − final'‖ ≤ 2 √q √(∑ i, Pr[B before step i])`. For a fresh secret, `Pr[B before step i]`
averages to at most `n ε Pr[C i before step i]`, and these sum to at most `q`
(`OracleAlg.StepCount.sum_prob_pre_le`), so the advantage is at most `2 q √(n ε)`: the bound of
`O2HSetting.o2h_fresh_secret` with `q` steps, where now each branch makes at most `q` queries but
the steps at which it does are chosen at run time.

- `O2HSetting.o2h_fresh_secret_of_count`: that bound.
- `Distinguisher.advantage_acceptProbOn_made_le_of_fresh_secret_budget`: the O2H step at one
  request of a game (`GordieHowe/Model/Quantum/O2H/Game.lean`) for a distinguisher with a budget of `q` query
  slots, `2 q √(n ε)`.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

/-! ### Supports and masks -/

section Supports

variable {ι : Type*} [Fintype ι]

theorem Supported.mono {S T : Set ι} {v : QState ι} (h : Supported S v) (hST : S ⊆ T) :
    Supported T v :=
  fun r hr => h r fun h' => hr (hST h')

theorem Supported.inter {S T : Set ι} {v : QState ι} (hS : Supported S v) (hT : Supported T v) :
    Supported (S ∩ T) v := fun r hr => by
  by_cases h : r ∈ S
  · exact hT r fun h' => hr ⟨h, h'⟩
  · exact hS r h

theorem Supported.sub {S : Set ι} {u v : QState ι} (hu : Supported S u) (hv : Supported S v) :
    Supported S (u - v) := fun r hr => by
  rw [PiLp.sub_apply, hu r hr, hv r hr, sub_zero]

theorem Supported.mask_eq_self {S : Set ι} {v : QState ι} (h : Supported S v) : mask S v = v := by
  ext r
  by_cases hr : r ∈ S
  · rw [mask_apply_of_mem _ hr]
  · rw [mask_apply_of_notMem _ hr, h r hr]

theorem Supported.mask_eq_zero {S T : Set ι} {v : QState ι} (h : Supported S v)
    (hST : ∀ r ∈ T, r ∉ S) : mask T v = 0 := by
  ext r
  by_cases hr : r ∈ T
  · rw [mask_apply_of_mem _ hr, h r (hST r hr)]
    rfl
  · rw [mask_apply_of_notMem _ hr]
    rfl

theorem supported_mask (S : Set ι) (v : QState ι) : Supported S (mask S v) :=
  fun _ hr => mask_apply_of_notMem _ hr

/-- **A map that keeps the supports `S` and `Sᶜ` commutes with the mask of `S`.** -/
theorem mask_comm_of_supported {S : Set ι} (f : QState ι ≃ₗᵢ[ℂ] QState ι)
    (hS : ∀ v, Supported S v → Supported S (f v)) (hSc : ∀ v, Supported Sᶜ v → Supported Sᶜ (f v))
    (v : QState ι) : mask S (f v) = f (mask S v) := by
  have hv : f v = f (mask S v) + f (mask Sᶜ v) := by rw [← map_add, mask_add_mask_compl]
  rw [hv, map_add, (hS _ (supported_mask S v)).mask_eq_self,
    (hSc _ (supported_mask Sᶜ v)).mask_eq_zero fun r hr hr' => hr' hr, add_zero]

/-- The probability of `S` in a vector supported in `G` is at most that of `T` when
`S ∩ G ⊆ T`. -/
theorem Supported.prob_le_of_inter_subset {S T G : Set ι} {v : QState ι} (h : Supported G v)
    (hST : ∀ r ∈ S, r ∈ G → r ∈ T) : prob S v ≤ prob T v := by
  classical
  rw [prob, prob, norm_mask_sq, norm_mask_sq]
  calc ∑ r with r ∈ S, ‖v r‖ ^ 2 = ∑ r with r ∈ S ∧ r ∈ G, ‖v r‖ ^ 2 := by
        refine (sum_subset (fun r hr => by simp only [mem_filter] at hr ⊢; exact ⟨hr.1, hr.2.1⟩)
          fun r hr hr' => ?_).symm
        simp only [mem_filter, mem_univ, true_and, not_and] at hr hr'
        rw [h r (hr' hr), norm_zero, zero_pow two_ne_zero]
    _ ≤ ∑ r with r ∈ T, ‖v r‖ ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (fun r hr => by
          simp only [mem_filter, mem_univ, true_and] at hr ⊢
          exact hST r hr.1 hr.2) fun _ _ _ => sq_nonneg _

open Classical in
/-- **Cauchy–Schwarz over the steps of each basis state.** If each `w i` is supported in
`C i ∩ G`, and every basis state of `G` lies in at most `q` of the sets `C i` for `i ∈ s`, then
`‖∑ i ∈ s, w i‖² ≤ q ∑ i ∈ s, ‖w i‖²`. -/
theorem norm_sum_sq_le_of_count {κ : Type*} (s : Finset κ) (q : ℕ) (w : κ → QState ι)
    (C : κ → Set ι) (G : Set ι) (hw : ∀ i ∈ s, Supported (C i ∩ G) (w i))
    (hG : ∀ r ∈ G, (s.filter fun i => r ∈ C i).card ≤ q) :
    ‖∑ i ∈ s, w i‖ ^ 2 ≤ q * ∑ i ∈ s, ‖w i‖ ^ 2 := by
  classical
  simp_rw [EuclideanSpace.norm_sq_eq]
  rw [sum_comm, mul_sum]
  refine sum_le_sum fun r _ => ?_
  have happ : (∑ i ∈ s, w i) r = ∑ i ∈ s, w i r := by
    simp [WithLp.ofLp_sum, Finset.sum_apply]
  rw [happ]
  by_cases hr : r ∈ G
  · have hF : ∑ i ∈ s, w i r = ∑ i ∈ s.filter (fun i => r ∈ C i), w i r := by
      refine (sum_subset (filter_subset _ _) fun i hi hi' => ?_).symm
      simp only [mem_filter, not_and] at hi'
      exact hw i hi r fun h => hi' hi h.1
    rw [hF]
    calc ‖∑ i ∈ s.filter (fun i => r ∈ C i), w i r‖ ^ 2
        ≤ (∑ i ∈ s.filter (fun i => r ∈ C i), ‖w i r‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (s.filter fun i => r ∈ C i).card * ∑ i ∈ s.filter (fun i => r ∈ C i), ‖w i r‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ q * ∑ i ∈ s, ‖w i r‖ ^ 2 := by
          gcongr
          · exact_mod_cast hG r hr
          · exact filter_subset _ _
  · have h0 : ∀ i ∈ s, w i r = 0 := fun i hi => hw i hi r fun h => hr h.2
    rw [sum_eq_zero h0, norm_zero, zero_pow two_ne_zero]
    positivity

end Supports

/-! ### Oracle algorithms whose branches record their oracle steps -/

namespace OracleAlg

variable {Z ι : Type*} [Fintype ι] {d : ℕ} (A : OracleAlg Z ι d)

/-- **A permutation that respects the sets `G k` and `C i`**: it maps each `G k` into itself and
keeps each `C i` and its complement. Oracle permutations act on the query registers only, so they
respect sets of the other registers (`respects_queryPermOf`). -/
structure Respects (π : Equiv.Perm ι) (G C : ℕ → Set ι) : Prop where
  mapsTo : ∀ k, ∀ r ∈ G k, π r ∈ G k
  mem_iff : ∀ i r, π r ∈ C i ↔ r ∈ C i

open Classical in
/-- **The oracle steps of each branch are counted**: along the run of `A` on input `z`, the states
before oracle step `k` are supported in `G k` (`init`, `stepG`), the steps after oracle step `i`
keep the set `C i` of the basis states that queried at step `i` and its complement (`stepC`,
`stepCc`), and every basis state of `G d`, the final states, lies in at most `q` of the sets `C i`
(`count`). -/
structure StepCount (z : Z) (G C : ℕ → Set ι) (q : ℕ) : Prop where
  init : Supported (G 0) (A.stepAt z 0 (A.init z))
  stepG : ∀ k < d, ∀ v, Supported (G k) v → Supported (G (k + 1)) (A.stepAt z (k + 1) v)
  stepC : ∀ i k, i ≤ k → k < d → ∀ v, Supported (C i) v → Supported (C i) (A.stepAt z (k + 1) v)
  stepCc : ∀ i k, i ≤ k → k < d → ∀ v, Supported (C i)ᶜ v →
    Supported (C i)ᶜ (A.stepAt z (k + 1) v)
  count : ∀ r ∈ G d, ((range d).filter fun i => r ∈ C i).card ≤ q

theorem stage_succ (π : Equiv.Perm ι) (z : Z) (k : ℕ) :
    A.stage π z (k + 1) = A.stepAt z (k + 1) (permOp π (A.stage π z k)) :=
  rfl

theorem stage_zero (π : Equiv.Perm ι) (z : Z) : A.stage π z 0 = A.stepAt z 0 (A.init z) :=
  rfl

namespace StepCount

variable {A} {z : Z} {G C : ℕ → Set ι} {q : ℕ}

/-- The run with a permutation that respects `G` stays in `G`. -/
theorem stage_supported (h : A.StepCount z G C q) {π : Equiv.Perm ι} (hπ : Respects π G C) :
    ∀ k ≤ d, Supported (G k) (A.stage π z k)
  | 0, _ => h.init
  | k + 1, hk => h.stepG k (by omega) _ ((h.stage_supported hπ k (by omega)).permOp (hπ.mapsTo k))

/-- **The hybrid as a sum.** The states of the runs with `π` and `π'` after `k` oracle steps
differ by `∑ i < k, w i`, where `w i` is the change at step `i`, `(π - π') vᵢ` for the state
`vᵢ` before step `i` of the run with `π`, carried to step `k` by the run with `π'`: so
`‖w i‖ ≤ 2 ‖mask B vᵢ‖`, and `w i` is supported in `C i ∩ G k` when the basis states of `B`
before step `i` lie in `C i`. -/
theorem exists_stage_sub_eq_sum (h : A.StepCount z G C q) {π π' : Equiv.Perm ι}
    (hπ : Respects π G C) (hπ' : Respects π' G C) {B : Set ι} (hB : ∀ r ∉ B, π r = π' r)
    (hBC : ∀ k < d, ∀ r ∈ B, r ∈ G k → r ∈ C k) :
    ∀ k ≤ d, ∃ w : ℕ → QState ι, A.stage π z k - A.stage π' z k = ∑ i ∈ range k, w i ∧
      ∀ i < k, ‖w i‖ ≤ 2 * ‖mask B (A.stage π z i)‖ ∧ Supported (C i ∩ G k) (w i) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨fun _ => 0, by simp [stage_zero], fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨w, hw, hwb⟩ := ih (by omega)
    set s := A.stage π z k
    set δ := permOp π s - permOp π' s with hδdef
    refine ⟨fun i => if i < k then A.stepAt z (k + 1) (permOp π' (w i))
      else A.stepAt z (k + 1) δ, ?_, ?_⟩
    · have e1 : A.stage π z (k + 1) - A.stage π' z (k + 1) =
          A.stepAt z (k + 1) (permOp π' (A.stage π z k - A.stage π' z k)) +
            A.stepAt z (k + 1) δ := by
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
        obtain ⟨hn, hs⟩ := hwb i hik
        refine ⟨by rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]; exact hn, ?_⟩
        have h1 := (hs.mono Set.inter_subset_left).permOp (π := π') fun r hr =>
          (hπ'.mem_iff i r).2 hr
        have h2 := (hs.mono Set.inter_subset_right).permOp (hπ'.mapsTo k)
        exact (h.stepC i k hik.le (by omega) _ h1).inter (h.stepG k (by omega) _ h2)
      · simp only [lt_irrefl, ↓reduceIte]
        refine ⟨by rw [LinearIsometryEquiv.norm_map]; exact norm_permOp_sub_le hB s, ?_⟩
        have hδ : δ = permOp π (mask B s) - permOp π' (mask B s) := by
          rw [hδdef]
          conv_lhs => rw [← mask_add_mask_compl B s]
          rw [map_add, map_add, permOp_mask_compl hB]
          abel
        have hsG := h.stage_supported hπ i (by omega)
        have hm : Supported (C i ∩ G i) (mask B s) := fun r hr => by
          by_cases hrB : r ∈ B
          · rw [mask_apply_of_mem _ hrB]
            by_cases hrG : r ∈ G i
            · exact absurd ⟨hBC i (by omega) r hrB hrG, hrG⟩ hr
            · exact hsG r hrG
          · exact mask_apply_of_notMem _ hrB
        have hpres : ∀ ρ : Equiv.Perm ι, Respects ρ G C →
            Supported (C i ∩ G i) (permOp ρ (mask B s)) := fun ρ hρ =>
          hm.permOp fun r hr => ⟨(hρ.mem_iff i r).2 hr.1, hρ.mapsTo i r hr.2⟩
        have hd : Supported (C i ∩ G i) δ := by
          rw [hδ]
          exact (hpres π hπ).sub (hpres π' hπ')
        exact (h.stepC i i le_rfl (by omega) _ (hd.mono Set.inter_subset_left)).inter
          (h.stepG i (by omega) _ (hd.mono Set.inter_subset_right))

/-- **AHU19 Lemma 8 with a per-branch count**: if the permutations `π` and `π'` agree outside
`B`, both respect `G` and `C`, and the basis states of `B` before step `k` lie in `C k`, then the
final states are within `2 √q √(∑ i, Pr[B before step i])`. -/
theorem norm_final_sub_le (h : A.StepCount z G C q) {π π' : Equiv.Perm ι}
    (hπ : Respects π G C) (hπ' : Respects π' G C) {B : Set ι} (hB : ∀ r ∉ B, π r = π' r)
    (hBC : ∀ k < d, ∀ r ∈ B, r ∈ G k → r ∈ C k) :
    ‖A.final π z - A.final π' z‖ ≤ 2 * √q * √(∑ i : Fin d, prob B (A.pre π z i)) := by
  obtain ⟨w, hw, hwb⟩ := h.exists_stage_sub_eq_sum hπ hπ' hB hBC d le_rfl
  have hsum : 0 ≤ ∑ i : Fin d, prob B (A.pre π z i) := sum_nonneg fun _ _ => prob_nonneg _ _
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt hsum, final, final, hw]
  refine (norm_sum_sq_le_of_count (range d) q w C (G d) (fun i hi => (hwb i (mem_range.1 hi)).2)
    h.count).trans ?_
  calc (q : ℝ) * ∑ i ∈ range d, ‖w i‖ ^ 2
      ≤ q * ∑ i ∈ range d, (2 * ‖mask B (A.stage π z i)‖) ^ 2 := by
        gcongr with i hi
        exact (hwb i (mem_range.1 hi)).1
    _ = 2 ^ 2 * q * ∑ i : Fin d, prob B (A.pre π z i) := by
        rw [sum_range (fun i => (2 * ‖mask B (A.stage π z i)‖) ^ 2), mul_sum, mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [prob, pre]
        ring

/-- **The steps at which the branches query number at most `q` on average**: the probabilities
of `C i` before step `i` sum to at most `q`. The part of the state on `C i` is carried unchanged in
norm to the end, where each basis state lies in at most `q` of the sets `C i`. -/
theorem sum_prob_pre_le (h : A.StepCount z G C q) {π : Equiv.Perm ι} (hπ : Respects π G C) :
    ∑ i : Fin d, prob (C i) (A.pre π z i) ≤ q := by
  classical
  have hcomm : ∀ i k, i ≤ k → k < d → ∀ v, mask (C i) (A.stepAt z (k + 1) (permOp π v)) =
      A.stepAt z (k + 1) (permOp π (mask (C i) v)) := by
    intro i k hik hk v
    rw [mask_comm_of_supported (A.stepAt z (k + 1)) (h.stepC i k hik hk) (h.stepCc i k hik hk),
      mask_comm_of_supported (permOp π) (fun v hv => hv.permOp fun r hr => (hπ.mem_iff i r).2 hr)
        (fun v hv => hv.permOp fun r hr hr' => hr ((hπ.mem_iff i r).1 hr'))]
  have hnorm : ∀ i k, i ≤ k → k ≤ d → prob (C i) (A.stage π z k) = prob (C i) (A.stage π z i) := by
    intro i k hik hkd
    induction k, hik using Nat.le_induction with
    | base => rfl
    | succ k hik ih =>
      rw [stage_succ, prob, hcomm i k hik (by omega), LinearIsometryEquiv.norm_map,
        LinearIsometryEquiv.norm_map, ← prob, ih (by omega)]
  have hfin := h.stage_supported hπ d le_rfl
  have hpt : ∀ r, ∑ i ∈ range d, (if r ∈ C i then ‖A.final π z r‖ ^ 2 else 0) ≤
      ‖A.final π z r‖ ^ 2 * q := by
    intro r
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
    by_cases hr : r ∈ G d
    · gcongr
      exact_mod_cast h.count r hr
    · rw [show A.final π z r = 0 from hfin r hr, norm_zero, zero_pow two_ne_zero, zero_mul,
        zero_mul]
  calc ∑ i : Fin d, prob (C i) (A.pre π z i)
      = ∑ i ∈ range d, prob (C i) (A.final π z) := by
        rw [sum_range (fun i => prob (C i) (A.final π z))]
        exact sum_congr rfl fun i _ => (hnorm i d i.2.le le_rfl).symm
    _ = ∑ r, ∑ i ∈ range d, (if r ∈ C i then ‖A.final π z r‖ ^ 2 else 0) := by
        rw [sum_comm]
        refine sum_congr rfl fun i _ => ?_
        rw [prob, norm_mask_sq, sum_filter]
    _ ≤ ∑ r, ‖A.final π z r‖ ^ 2 * q := sum_le_sum fun r _ => hpt r
    _ = q := by
        rw [← sum_mul, ← EuclideanSpace.norm_sq_eq, A.norm_final, one_pow, one_mul]

end StepCount

end OracleAlg

/-! ### O2H for a fresh secret with a per-branch count -/

section FreshCount

variable {W X Y : Type*} [Fintype W] [Fintype X] [Fintype Y] {n : ℕ}

omit [Fintype W] [Fintype X] [Fintype Y] in
/-- An oracle permutation respects sets of the work register. -/
theorem respects_queryPermOf [AddGroup Y] (F : W → X → Y) (G C : ℕ → Set W) :
    OracleAlg.Respects (queryPermOf (n := n) F) (fun k => {r | r.1 ∈ G k})
      (fun i => {r | r.1 ∈ C i}) where
  mapsTo _ r hr := by simpa using hr
  mem_iff _ r := by simp

variable {R : Type*} [Fintype R]

/-- Averaging the probability of `queried (T σ)` in `ψ` over `σ ← ν` gives at most `ε ‖ψ‖²` if
every tuple of query inputs meets `T σ` with probability at most `ε`. -/
theorem sum_mul_prob_queried_le_mul_norm_sq (ν : PMF R) (T : R → Set X)
    (ψ : QState (QueryReg W n X Y)) {ε : ℝ}
    (hε : ∀ t : Fin n → X, (ν.toOuterMeasure {σ | ∃ j, t j ∈ T σ}).toReal ≤ ε) :
    ∑ σ, (ν σ).toReal * prob (queried (T σ)) ψ ≤ ε * ‖ψ‖ ^ 2 := by
  rw [sum_mul_prob_queried_eq]
  calc ∑ t, prob (queryInputs ⁻¹' {t}) ψ * (ν.toOuterMeasure {σ | ∃ j, t j ∈ T σ}).toReal
      ≤ ∑ t, prob (queryInputs ⁻¹' {t}) ψ * ε :=
        sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hε t) (prob_nonneg _ _)
    _ = ε * ‖ψ‖ ^ 2 := by rw [← sum_mul, sum_prob_fiber, mul_comm]

namespace O2HSetting

section General

variable {Ω Z : Type*} [Fintype Ω] [AddGroup Y] {d : ℕ} (s : O2HSetting Ω Z W X Y)
  (A : OracleAlg Z (QueryReg W n X Y) d)

/-- **AHU19 Theorem 3 with a per-branch count of the oracle steps** (our statement; AHU19
pp. 11–12, with `OracleAlg.StepCount.norm_final_sub_le` in place of Lemma 8). If along every run
the branches record their oracle steps (`StepCount` with sets `G k` and `C i` of the work
register, at most `q` steps per branch), and a basis state on which the oracles may differ
before step `k` lies in `C k`, then
`|P_left − P_right| ≤ 2 √q √(𝔼 ω, ∑ i, Pr[queried S before step i])`. -/
theorem o2h_of_count (G C : ℕ → Set W) (q : ℕ)
    (hcount : ∀ ω, A.StepCount (s.z ω) (fun k => {r | r.1 ∈ G k}) (fun i => {r | r.1 ∈ C i}) q)
    (hSC : ∀ ω, ∀ k < d, ∀ w ∈ G k, ∀ x ∈ s.S ω w, w ∈ C k) :
    GordieHowe.advantage (s.pLeft A) (s.pRight A) ≤ 2 * √q * √(∑ ω, (s.μ ω).toReal *
      ∑ i : Fin d, prob (queriedOf (s.S ω)) (A.pre (queryPermOf (s.H ω)) (s.z ω) i)) := by
  set g : Ω → ℝ := fun ω => ∑ i : Fin d,
    prob (queriedOf (s.S ω)) (A.pre (queryPermOf (s.H ω)) (s.z ω) i)
  have hw : ∀ ω, 0 ≤ (s.μ ω).toReal := fun _ => ENNReal.toReal_nonneg
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => sum_nonneg fun _ _ => prob_nonneg _ _
  have hstep : ∀ ω, |A.acceptProb (queryPermOf (s.H ω)) (s.z ω) -
      A.acceptProb (queryPermOf (s.G ω)) (s.z ω)| ≤ 2 * √q * √(g ω) := fun ω =>
    (A.abs_acceptProb_sub_le _ _ _).trans ((hcount ω).norm_final_sub_le
      (respects_queryPermOf _ G C) (respects_queryPermOf _ G C)
      (queryPermOf_eq_of_notMem_queriedOf fun w x hx => (s.agree ω w x hx).symm)
      fun k hk r hr hrG => by
        obtain ⟨j, hj⟩ := hr
        exact hSC ω k hk r.1 hrG _ hj)
  rw [GordieHowe.advantage, pLeft, pRight, ← sum_sub_distrib]
  calc |∑ ω, ((s.μ ω).toReal * A.acceptProb (queryPermOf (s.H ω)) (s.z ω) -
          (s.μ ω).toReal * A.acceptProb (queryPermOf (s.G ω)) (s.z ω))|
      ≤ ∑ ω, (s.μ ω).toReal * (2 * √q * √(g ω)) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun ω _ => ?_)
        rw [← mul_sub, abs_mul, abs_of_nonneg (hw ω)]
        exact mul_le_mul_of_nonneg_left (hstep ω) (hw ω)
    _ = 2 * √q * ∑ ω, (s.μ ω).toReal * √(g ω) := by
        rw [mul_sum]
        exact sum_congr rfl fun ω _ => by ring
    _ ≤ 2 * √q * √(∑ ω, (s.μ ω).toReal * g ω) := by
        gcongr
        exact Real.sum_mul_sqrt_le_sqrt_sum_mul hw s.μ.sum_toReal hg0

end General

variable {Z V : Type*} [Fintype V] [AddGroup Y] {d : ℕ}
  (s : O2HSetting (V × R) Z W X Y) (A : OracleAlg Z (QueryReg W n X Y) d)

/-- **O2H for a fresh secret, with a per-branch count of the oracle steps** (our statement; AHU19
Theorem 3, pp. 11–12, through `o2h_of_count`). Let the outcome be `(v, σ)` with `μ (v, σ) = μV v * ν σ`, let the oracles differ on `T σ` for
the contents `w ∈ M` of the work register and nowhere else, and let the part on `M` of the states
before the oracle steps not depend on `σ`; suppose that along every run the branches record their oracle steps (`StepCount` with sets
`G k` and `C i` of the work register) and that a basis state of `M` before step `k` lies in `C k`.
If every input lies in `T σ` with probability at most `ε`, then
`|P_left − P_right| ≤ 2 q √(n ε)`: each branch is charged for the at most `q` oracle steps at
which it lies in `M`, wherever they fall. -/
theorem o2h_fresh_secret_of_count {μV : PMF V} {ν : PMF R} {T : R → Set X} {ε : ℝ} (M : Set W)
    (G C : ℕ → Set W) (q : ℕ) (hμ : ∀ v σ, s.μ (v, σ) = μV v * ν σ)
    (hS : ∀ v σ w, w ∈ M → s.S (v, σ) w = T σ) (hS' : ∀ v σ w, w ∉ M → s.S (v, σ) w = ∅)
    (hpre : ∀ v σ σ' i, mask {r : QueryReg W n X Y | r.1 ∈ M}
      (A.pre (queryPermOf (s.H (v, σ))) (s.z (v, σ)) i) =
        mask {r : QueryReg W n X Y | r.1 ∈ M} (A.pre (queryPermOf (s.H (v, σ'))) (s.z (v, σ')) i))
    (hcount : ∀ ω, A.StepCount (s.z ω) (fun k => {r | r.1 ∈ G k}) (fun i => {r | r.1 ∈ C i}) q)
    (hMC : ∀ k < d, ∀ w ∈ M, w ∈ G k → w ∈ C k)
    (hε0 : 0 ≤ ε) (hε : ∀ x, (ν.toOuterMeasure {σ | x ∈ T σ}).toReal ≤ ε) :
    GordieHowe.advantage (s.pLeft A) (s.pRight A) ≤ 2 * q * √(n * ε) := by
  classical
  set g : V × R → ℝ := fun ω => ∑ i : Fin d,
    prob (queriedOf (s.S ω)) (A.pre (queryPermOf (s.H ω)) (s.z ω) i) with hg
  have hSC : ∀ ω, ∀ k < d, ∀ w ∈ G k, ∀ x ∈ s.S ω w, w ∈ C k := by
    intro ω k hk w hwG x hx
    have hwM : w ∈ M := by
      by_contra hM
      rw [hS' ω.1 ω.2 _ hM] at hx
      exact hx
    exact hMC k hk w hwM hwG
  -- the average of `g` is at most `n ε q`
  set Mr : Set (QueryReg W n X Y) := {r | r.1 ∈ M}
  have hq : ∀ v σ (ψ : QState (QueryReg W n X Y)),
      prob (queriedOf (s.S (v, σ))) ψ = prob (queried (T σ)) (mask Mr ψ) := by
    intro v σ ψ
    have hset : queriedOf (n := n) (Y := Y) (s.S (v, σ)) = queried (T σ) ∩ Mr := by
      ext r
      by_cases hr : r.1 ∈ M
      · simp [queriedOf, queried, Mr, hS v σ _ hr, hr]
      · simp [queriedOf, queried, Mr, hS' v σ _ hr, hr]
    rw [hset, prob_inter_eq_prob_mask]
  have htuple : ∀ t : Fin n → X, (ν.toOuterMeasure {σ | ∃ j, t j ∈ T σ}).toReal ≤ n * ε := by
    intro t
    rw [Set.ofPred_exists]
    refine (ν.toReal_toOuterMeasure_iUnion_le _).trans ?_
    calc ∑ j, (ν.toOuterMeasure {σ | t j ∈ T σ}).toReal ≤ ∑ _j : Fin n, ε :=
          sum_le_sum fun j _ => hε (t j)
      _ = n * ε := by simp
  obtain ⟨σ₀, -⟩ := ν.support_nonempty
  have inner : ∀ v, ∑ σ, (ν σ).toReal * g (v, σ) ≤ n * ε * q := by
    intro v
    set ψ : Fin d → QState (QueryReg W n X Y) := fun i =>
      A.pre (queryPermOf (s.H (v, σ₀))) (s.z (v, σ₀)) i
    calc ∑ σ, (ν σ).toReal * g (v, σ)
        = ∑ i : Fin d, ∑ σ, (ν σ).toReal * prob (queried (T σ)) (mask Mr (ψ i)) := by
          simp only [hg, mul_sum]
          rw [sum_comm]
          refine sum_congr rfl fun i _ => sum_congr rfl fun σ _ => ?_
          rw [hq, hpre v σ σ₀]
      _ ≤ ∑ i : Fin d, n * ε * prob Mr (ψ i) := by
          refine sum_le_sum fun i _ => ?_
          refine (sum_mul_prob_queried_le_mul_norm_sq ν T _ htuple).trans_eq ?_
          rw [prob]
      _ ≤ ∑ i : Fin d, n * ε * prob {r : QueryReg W n X Y | r.1 ∈ C i} (ψ i) := by
          refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hsupp := (hcount (v, σ₀)).stage_supported
            (π := queryPermOf (s.H (v, σ₀))) (respects_queryPermOf _ G C) i i.2.le
          exact hsupp.prob_le_of_inter_subset fun r hr hrG => hMC i i.2 r.1 hr hrG
      _ ≤ n * ε * q := by
          rw [← mul_sum]
          exact mul_le_mul_of_nonneg_left
            ((hcount (v, σ₀)).sum_prob_pre_le (respects_queryPermOf _ G C)) (by positivity)
  have havg : ∑ ω, (s.μ ω).toReal * g ω ≤ n * ε * q := by
    rw [Fintype.sum_prod_type]
    simp_rw [hμ, ENNReal.toReal_mul, mul_assoc, ← mul_sum]
    calc ∑ v, (μV v).toReal * ∑ σ, (ν σ).toReal * g (v, σ) ≤ ∑ v, (μV v).toReal * (n * ε * q) :=
          sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (inner v) ENNReal.toReal_nonneg
      _ = n * ε * q := by rw [← sum_mul, μV.sum_toReal, one_mul]
      _ = n * (ε * q) := by ring
  refine (s.o2h_of_count A G C q hcount hSC).trans ?_
  calc 2 * √q * √(∑ ω, (s.μ ω).toReal * g ω) ≤ 2 * √q * √(n * ε * q) := by
        gcongr
    _ = 2 * q * √(n * ε) := by
        rw [Real.sqrt_mul (by positivity) q, mul_comm (√(n * ε)) (√q), ← mul_assoc,
          mul_assoc 2 (√q) (√q), Real.mul_self_sqrt (Nat.cast_nonneg _)]

end O2HSetting

end FreshCount

/-! ### A query budget along the game -/

section Slices

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ}

/-- A log-controlled unitary is supported, on the basis states with logs `lg`, where its unitary
for `lg` sends the slice of the vector at `lg`. -/
theorem supported_logControlled_of_slices
    (U : LogReg Req m → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (v : QState (GameReg W n X Y Req A m)) {S : LogReg Req m → Set (DReg W n X Y Req A)}
    (h : ∀ lg, Supported (S lg) (U lg (WithLp.toLp 2 fun d => v (splitLogs.symm (d, lg))))) :
    Supported {r | (splitLogs r).1 ∈ S (splitLogs r).2} (logControlled U v) :=
  fun r hr => by
    rw [logControlled_apply]
    exact h _ _ hr

end Slices

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} {D : Distinguisher W X Y Req A n m} {q : ℕ}

namespace Budget

/-- **A budget holds before oracle step `k` of the game**, on a content `s` of the work register of
the game (workspace, request, response and logs): the branch has queried at no more than `q` of the
slots up to `k` (`count`), its logs after slot `k` are blank (`blank`), and for `k < m` its log of
slot `k` records the kind of the slot (`logged`) and its workspace is in `inv k` at its number of
query slots before `k` (`mem`). -/
structure Holds (bud : D.Budget q) (k : ℕ) (s : W × Req × Option A × LogReg Req m) : Prop where
  count : queriesBefore s.2.2.2 (k + 1) ≤ q
  blank : ∀ k' : Fin m, k < k' → s.2.2.2 k' = none
  logged : k < m → queriedAt s.2.2.2 k = !D.kind s.1
  mem : k < m → s.1 ∈ bud.inv k (queriesBefore s.2.2.2 k)

/-- **A budget holds after the step before slot `k`**, before the request of slot `k`: at most `q`
query slots before `k`, the logs from slot `k` on blank, and the workspace in `inv k` at the number
of query slots before `k`. -/
structure HoldsBefore (bud : D.Budget q) (k : ℕ) (s : W × Req × Option A × LogReg Req m) :
    Prop where
  count : queriesBefore s.2.2.2 k ≤ q
  blank : ∀ k' : Fin m, k ≤ k' → s.2.2.2 k' = none
  mem : s.1 ∈ bud.inv k (queriesBefore s.2.2.2 k)

variable (bud : D.Budget q)

/-- After the last slot, the budget holds when the branch queried at no more than `q` slots. -/
theorem holds_of_le {k : ℕ} (hk : m ≤ k) {s : W × Req × Option A × LogReg Req m}
    (h : queriesBefore s.2.2.2 k ≤ q) : bud.Holds k s where
  count := by rwa [queriesBefore_succ_of_le _ hk]
  blank k' hk' := absurd k'.2 (by omega)
  logged h := absurd h (by omega)
  mem h := absurd h (by omega)

variable [DecidableEq Req] [DecidableEq A] {Ω : Type*} {Q : ℕ}

/-- The logs after the request of slot `k`, on a state whose log `k` is blank. -/
theorem logs_requestPerm_of_blank (E : Env Ω Req A X Y Q) (ω : Ω) {k : ℕ} (hk : k < m)
    {r : GameReg W n X Y Req A m} (h0 : r.1.2.2.2 ⟨k, hk⟩ = none) :
    (E.requestPerm D.kind ω ⟨k, hk⟩ r).1.2.2.2 =
      if D.kind r.1.1 then Function.update r.1.2.2.2 ⟨k, hk⟩ (some r.1.2.1) else r.1.2.2.2 := by
  have h := E.logs_requestPerm D.kind ω ⟨k, hk⟩ r
  change (E.requestPerm D.kind ω ⟨k, hk⟩ r).1.2.2.2 = if D.kind r.1.1 then
    Function.update r.1.2.2.2 ⟨k, hk⟩ (Equiv.swap none (some r.1.2.1) (r.1.2.2.2 ⟨k, hk⟩))
      else r.1.2.2.2 at h
  rw [h0, Equiv.swap_apply_left] at h
  exact h

/-- The request of slot `k` does not change whether another slot was a query slot. -/
theorem queriedAt_requestPerm_of_ne (E : Env Ω Req A X Y Q) (ω : Ω) {k : ℕ} (hk : k < m)
    (r : GameReg W n X Y Req A m) {i : ℕ} (hi : i ≠ k) :
    queriedAt (E.requestPerm D.kind ω ⟨k, hk⟩ r).1.2.2.2 i = queriedAt r.1.2.2.2 i := by
  have h := E.logs_requestPerm D.kind ω ⟨k, hk⟩ r
  change (E.requestPerm D.kind ω ⟨k, hk⟩ r).1.2.2.2 = if D.kind r.1.1 then
    Function.update r.1.2.2.2 ⟨k, hk⟩ (Equiv.swap none (some r.1.2.1) (r.1.2.2.2 ⟨k, hk⟩))
      else r.1.2.2.2 at h
  rw [h]
  split_ifs
  · exact queriedAt_update_of_ne _ hi _
  · rfl

/-- **The request of slot `k` keeps the budget**: from a state where the budget holds after the
step before slot `k`, the request logs the slot's kind, and a query at slot `k` is within the
budget (`Budget.cap`). -/
theorem holds_requestPerm (E : Env Ω Req A X Y Q) (ω : Ω) {k : ℕ} (hk : k < m)
    {r : GameReg W n X Y Req A m} (hr : bud.HoldsBefore k r.1) :
    bud.Holds k (E.requestPerm D.kind ω ⟨k, hk⟩ r).1 := by
  have hws : (E.requestPerm D.kind ω ⟨k, hk⟩ r).1.1 = r.1.1 := E.workspace_requestPerm D.kind ω _ r
  have h0 : r.1.2.2.2 ⟨k, hk⟩ = none := hr.blank ⟨k, hk⟩ le_rfl
  have hlg := logs_requestPerm_of_blank (D := D) E ω hk h0
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
  refine ⟨?_, ?_, fun _ => by rw [hqa, hws], fun _ => by rw [hws, hqb]; exact hr.mem⟩
  · rw [queriesBefore_succ, hqb, hqa]
    cases hkind : D.kind r.1.1
    · have := bud.cap k hk _ r.1.1 hr.mem hkind
      simp only [Bool.not_false, ↓reduceIte]
      omega
    · simpa using hr.count
  · intro k' hk'
    rw [hlg]
    split_ifs
    · rw [Function.update_of_ne (Fin.ne_of_val_ne (by simp; omega))]
      exact hr.blank k' hk'.le
    · exact hr.blank k' hk'.le

omit [DecidableEq Req] [DecidableEq A] in
/-- **The step before slot `k + 1` keeps the budget** (`Budget.step`), slice by slice of the
logs: the kind of slot `k` is read from its log. -/
theorem holdsBefore_liftedStep (k : ℕ) (hk : k + 1 < m) {v : QState (GameReg W n X Y Req A m)}
    (hv : Supported {r | bud.Holds k r.1} v) :
    Supported {r | bud.HoldsBefore (k + 1) r.1} (D.liftedStep (k + 1) v) := by
  classical
  set S' : LogReg Req m → Set (DReg W n X Y Req A) := fun lg =>
    {d | queriesBefore lg (k + 1) ≤ q ∧ (∀ k' : Fin m, k < k' → lg k' = none) ∧
      d.workspace ∈ bud.inv (k + 1) (queriesBefore lg (k + 1))}
  have key := supported_logControlled_of_slices (fun _ => D.stepAt (k + 1)) v (S := S')
    fun lg => by
      by_cases hlg : queriesBefore lg (k + 1) ≤ q ∧ ∀ k' : Fin m, k < k' → lg k' = none
      · have hslice : Supported {d : DReg W n X Y Req A |
            d.workspace ∈ bud.inv k (queriesBefore lg k) ∧ D.kind d.workspace = !queriedAt lg k}
            (WithLp.toLp 2 fun d => v (splitLogs.symm (d, lg))) := by
          intro d hd
          show v (splitLogs.symm (d, lg)) = 0
          refine hv _ fun hH => hd ⟨hH.mem (by omega), ?_⟩
          have := hH.logged (by omega)
          change queriedAt lg k = !D.kind d.workspace at this
          rw [this, Bool.not_not]
        have hstep := bud.step k hk _ _ _ hslice
        simp only [stepAt, show k + 1 < m + 1 by omega, ↓reduceDIte]
        refine hstep.mono fun d hd => ⟨hlg.1, hlg.2, ?_⟩
        have hd' : d.workspace ∈ bud.inv (k + 1)
            (if !queriedAt lg k then queriesBefore lg k else queriesBefore lg k + 1) := hd
        rw [queriesBefore_succ]
        cases h : queriedAt lg k <;> simpa [h] using hd'
      · have h0 : (WithLp.toLp 2 fun d => v (splitLogs.symm (d, lg)) :
            QState (DReg W n X Y Req A)) = 0 := by
          ext d
          exact hv _ fun hH => hlg ⟨hH.count, hH.blank⟩
        rw [h0, map_zero]
        intro _ _
        rfl
  refine key.mono fun r hr => ?_
  obtain ⟨h1, h2, h3⟩ := hr
  exact ⟨h1, fun k' hk' => h2 k' (by omega), h3⟩

omit [DecidableEq A] in
/-- The first step keeps the budget (`Budget.init`). -/
theorem holdsBefore_liftedStep_zero (hm : 0 < m) :
    Supported {r : GameReg W n X Y Req A m | bud.HoldsBefore 0 r.1} (D.liftedStep 0 D.gameInit) := by
  classical
  have key := supported_logControlled_of_slices (fun _ => D.stepAt 0) D.gameInit
    (S := fun lg => {d | (lg = fun _ => none) ∧ d.workspace ∈ bud.inv 0 0}) fun lg => by
      by_cases hlg : lg = fun _ => none
      · have hslice : (WithLp.toLp 2 fun d => D.gameInit (splitLogs.symm (d, lg)) :
            QState (DReg W n X Y Req A)) = D.init := by
          ext d
          simp [gameInit, hlg]
        have h0 : D.stepAt 0 = D.step 0 := by simp [stepAt]
        rw [hslice, h0]
        exact (bud.init hm).mono fun d hd => ⟨hlg, hd⟩
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
  exact ⟨by rw [hq0]; exact Nat.zero_le _, fun k' _ => by rw [hlg'], by rw [hq0]; exact hmem⟩

variable (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))

/-- The steps of the game as an oracle algorithm. -/
theorem gameAlg_stepAt (E : Env Ω Req A X Y Q) (L : Set (LogReg Req m)) (ω : Ω) {k : ℕ}
    (hk : k < m + 1) : (D.gameAlg E post L).stepAt ω k = D.gameStep E post ω k := by
  rw [OracleAlg.stepAt_of_lt _ hk]
  rfl

/-- The steps of the game keep the logs of the earlier slots. -/
theorem supported_gameStep_logs (E : Env Ω Req A X Y Q) (ω : Ω) {k i : ℕ} (hik : i < k)
    {L : Set (LogReg Req m)} (hL : ∀ lg lg' : LogReg Req m, queriedAt lg i = queriedAt lg' i →
      (lg ∈ L ↔ lg' ∈ L)) {v : QState (GameReg W n X Y Req A m)} (hv : Supported (logsIn L) v) :
    Supported (logsIn L) (D.gameStep E post ω k v) := by
  have h1 := hv.logControlled (fun _ => D.stepAt k)
  unfold gameStep
  split_ifs with hk
  · rw [LinearIsometryEquiv.trans_apply]
    refine h1.permOp fun r hr => ?_
    simp only [mem_logsIn] at hr ⊢
    exact (hL _ _ (queriedAt_requestPerm_of_ne (D := D) E ω hk r (by omega))).2 hr
  · rw [LinearIsometryEquiv.trans_apply]
    exact h1.logControlled _

/-- **The game counts the query slots of each branch** (`OracleAlg.StepCount`): before oracle
step `k` the budget holds (`Budget.Holds`), the set of the branches that queried at slot `i` is
kept by the later steps, and at the end every branch queried at no more than `q` slots. -/
theorem stepCount_gameAlg (E : Env Ω Req A X Y Q) (L : Set (LogReg Req m)) (ω : Ω) :
    (D.gameAlg E post L).StepCount ω (fun k => {r | r.1 ∈ {s | bud.Holds k s}})
      (fun i => {r | r.1 ∈ {s : W × Req × Option A × LogReg Req m | queriedAt s.2.2.2 i = true}})
      q where
  init := by
    rw [gameAlg_stepAt post E L ω (by omega)]
    by_cases hm : 0 < m
    · simp only [gameStep, hm, ↓reduceDIte, LinearIsometryEquiv.trans_apply]
      exact (bud.holdsBefore_liftedStep_zero hm).permOp fun r hr =>
        bud.holds_requestPerm E ω hm hr
    · intro r hr
      exact absurd (bud.holds_of_le (by omega) (by rw [queriesBefore_zero]; exact Nat.zero_le _)) hr
  stepG k hk v hv := by
    rw [gameAlg_stepAt post E L ω (by omega)]
    by_cases hk1 : k + 1 < m
    · simp only [gameStep, hk1, ↓reduceDIte, LinearIsometryEquiv.trans_apply]
      exact (bud.holdsBefore_liftedStep k hk1 hv).permOp fun r hr =>
        bud.holds_requestPerm E ω hk1 hr
    · simp only [gameStep, hk1, ↓reduceDIte, LinearIsometryEquiv.trans_apply]
      have hv' : Supported (logsIn {lg : LogReg Req m | queriesBefore lg (k + 1) ≤ q}) v :=
        hv.mono fun r hr => hr.count
      refine ((hv'.logControlled _).logControlled _).mono fun r hr => ?_
      exact bud.holds_of_le (by omega) hr
  stepC i k hik hk v hv := by
    rw [gameAlg_stepAt post E L ω (by omega)]
    exact supported_gameStep_logs post E ω (k := k + 1) (i := i) (L := {lg | queriedAt lg i = true}) (by omega)
      (fun lg lg' h => by simp [h]) hv
  stepCc i k hik hk v hv := by
    rw [gameAlg_stepAt post E L ω (by omega)]
    exact supported_gameStep_logs post E ω (k := k + 1) (i := i) (L := {lg | queriedAt lg i = true}ᶜ) (by omega)
      (fun lg lg' h => by simp [h]) hv
  count r hr := by
    have hc : queriesBefore r.1.2.2.2 m ≤ q := by
      have := hr.count
      rwa [queriesBefore_succ_of_le _ le_rfl] at this
    refine le_of_eq_of_le ?_ hc
    unfold queriesBefore
    congr 1
    ext i
    simp

end Budget

variable [DecidableEq Req] [DecidableEq A] [AddGroup Y] {Q : ℕ} {V R : Type*} [Fintype V]
  [Fintype R] (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))

/-- **O2H at request `j` for a fresh secret, with a query budget.** For two environments `E` and
`E'` with the same tape law and the same answers (`hμ'`, `hans`), whose oracles agree after more
than `j` requests (`hafter`) and, after at most `j` requests, outside a set `T σ` of inputs
determined by a component `σ` of the tape (`hbefore`) drawn independently (`hμ`) and not read by
`E` before request `j` (`hfreshOracle`, `hfreshAnswer`), with `Pr_σ[x ∈ T σ] ≤ ε` (`hε`), the games
against `E` and `E'`, restricted to the branches that make request `j`, are distinguished with
advantage at most `2 q √(n ε)` for a distinguisher with a budget of `q` query slots
(`Distinguisher.Budget`): every branch queries at no more than `q` slots, chosen at run time.
The proof is `O2HSetting.o2h_fresh_secret_of_count` for `gameAlg`, whose branches record their
query slots in the logs (`Budget.stepCount_gameAlg`). -/
theorem advantage_acceptProbOn_made_le_of_fresh_secret_budget (bud : D.Budget q)
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
  let s : O2HSetting (V × R) (V × R) (W × Req × Option A × LogReg Req m) X Y :=
    { μ := E.μ
      S := fun ω w => if w ∈ D.openSet j then T ω.2 else ∅
      G := fun ω => E'.oracleFn D.kind ω
      H := fun ω => E.oracleFn D.kind ω
      z := id
      agree := fun ω w x hx => D.oracleFn_agree E E' (hafter ω) (hbefore ω) w x hx }
  have hans' : ∀ ω (lg : LogReg Req m) k, E.answer ω lg k = E'.answer ω lg k := fun ω lg k => by
    simp only [Env.answer, funext (hans ω (requestsBefore lg k))]
  have hpL : s.pLeft (D.gameAlg E post (madeLogs j)) = D.acceptProbOn E post (madeLogs j) :=
    sum_congr rfl fun ω _ => by rw [← D.acceptProb_gameAlg_self E post _ ω]; rfl
  have hpR : s.pRight (D.gameAlg E post (madeLogs j)) = D.acceptProbOn E' post (madeLogs j) := by
    change ∑ ω, (E.μ ω).toReal * _ = ∑ ω, (E'.μ ω).toReal * _
    rw [hμ']
    exact sum_congr rfl fun ω _ => by
      rw [← D.acceptProb_gameAlg E post E' _ ω (hans' ω) fun lg hlg =>
        hafter ω _ (by simpa [madeLogs] using hlg)]
      rfl
  have hcount := fun ω => bud.stepCount_gameAlg post E (madeLogs j) ω
  have hMC : ∀ k < m, ∀ w ∈ D.openSet j, w ∈ {s | bud.Holds k s} →
      w ∈ {s : W × Req × Option A × LogReg Req m | queriedAt s.2.2.2 k = true} :=
    fun k hk w hw hH => by
      have h := hH.logged hk
      rw [hw.1] at h
      exact h
  rw [← hpL, ← hpR]
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · refine (s.o2h_of_count _ _ _ q hcount fun ω k hk w hw x hx => isEmptyElim x).trans ?_
    have hq : ∀ ω, queriedOf (n := n) (Y := Y) (s.S ω) = ∅ := fun ω => by
      ext r
      simp only [queriedOf, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      exact fun i => isEmptyElim (r.2 i).1
    have h0 : ∀ v : QState (GameReg W n X Y Req A m), prob ∅ v = 0 := fun v => by
      have hm : mask (∅ : Set (GameReg W n X Y Req A m)) v = 0 := by
        ext i
        simp
      rw [prob, hm, norm_zero, zero_pow two_ne_zero]
    simp only [hq, h0, sum_const_zero, mul_zero, Real.sqrt_zero]
    positivity
  have hε0 : 0 ≤ ε := ENNReal.toReal_nonneg.trans (hε x₀)
  exact s.o2h_fresh_secret_of_count _ (D.openSet j) _ _ q hμ (fun v σ w hw => by simp [s, hw])
    (fun v σ w hw => by simp [s, hw])
    (fun v σ σ' i => D.mask_pre_eq post E _ (hfreshAnswer v σ σ') (hfreshOracle v σ σ') i)
    hcount hMC hε0 hε

end Distinguisher

end GordieHowe.Quantum
