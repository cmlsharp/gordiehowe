-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.O2H.Budget

@[expose] public section

/-!
# The hybrid with a per-branch count for padded queries

`OracleAlg.StepCount` (`GordieHowe/Model/Quantum/O2H/Budget.lean`) asks the steps after oracle step `i` to keep
the set `C i` of the basis states that queried at step `i`, and its complement, on every vector.
The per-branch count of a compiled algorithm (`GordieHowe.QROM.QueryCount`) gives this only on the
vectors supported in the supports `G k` of the run, and at a step the branches outside `C k` do
not leave the query untouched: they query a clean ancilla whose answer register is in the uniform
superposition, which every oracle fixes. This file proves the hybrid of AHU19 Lemma 8 with a
per-branch count in that form.

- `OracleAlg.StepCountOn`: `StepCount` with the steps required to keep `C i` and its complement only
  on vectors supported in `G k`.
- `OracleAlg.StepCountOn.norm_final_sub_le`: if the permutations `π` and `π'` agree outside `B`
  and both act alike on the part of the run of `π` outside `C k` before step `k` (`hpad`: the
  padded branches), then `‖final π − final π'‖ ≤ 2 √q √(∑ i, ‖mask B (mask (C i) vᵢ)‖²)` for the
  states `vᵢ` of the run of `π` before step `i`.
- `OracleAlg.StepCountOn.sum_prob_pre_le`: the weights `‖mask (C i) vᵢ‖²` sum to at most `q`.

**The argument** (our statement; the hybrid is AHU19 Lemma 8, pp. 26–27, as in
`StepCount.exists_stage_sub_eq_sum`). At step `k` the change is `(π − π') vₖ`; by `hpad` it is
`(π − π') (mask (C k) vₖ)`, and since `π` and `π'` agree outside `B` it is
`(π − π') (mask B (mask (C k) vₖ))`, of norm at most `2 ‖mask B (mask (C k) vₖ)‖` and supported
in `C k ∩ G k`. The later steps keep that support, so Cauchy–Schwarz basis state by basis state
(`norm_sum_sq_le_of_count`) bounds the norm of the sum.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

namespace OracleAlg

variable {Z ι : Type*} [Fintype ι] {d : ℕ} (A : OracleAlg Z ι d)

open Classical in
/-- **The oracle steps of each branch are counted on the run's supports**: as `StepCount`, with the
steps after oracle step `i` required to keep `C i` and its complement only on vectors supported in
the support `G k` of the run before step `k`. -/
structure StepCountOn (z : Z) (G C : ℕ → Set ι) (q : ℕ) : Prop where
  init : Supported (G 0) (A.stepAt z 0 (A.init z))
  stepG : ∀ k < d, ∀ v, Supported (G k) v → Supported (G (k + 1)) (A.stepAt z (k + 1) v)
  stepC : ∀ i k, i ≤ k → k < d → ∀ v, Supported (C i ∩ G k) v →
    Supported (C i) (A.stepAt z (k + 1) v)
  stepCc : ∀ i k, i ≤ k → k < d → ∀ v, Supported ((C i)ᶜ ∩ G k) v →
    Supported (C i)ᶜ (A.stepAt z (k + 1) v)
  count : ∀ r ∈ G d, ((range d).filter fun i => r ∈ C i).card ≤ q

namespace StepCountOn

variable {A} {z : Z} {G C : ℕ → Set ι} {q : ℕ}

/-- The run with a permutation that respects `G` stays in `G`. -/
theorem stage_supported (h : A.StepCountOn z G C q) {π : Equiv.Perm ι} (hπ : Respects π G C) :
    ∀ k ≤ d, Supported (G k) (A.stage π z k)
  | 0, _ => h.init
  | k + 1, hk => h.stepG k (by omega) _ ((h.stage_supported hπ k (by omega)).permOp (hπ.mapsTo k))

/-- **The hybrid as a sum, for padded queries.** The states of the runs with `π` and `π'` after
`k` oracle steps differ by `∑ i < k, w i`, where `w i` is the change at step `i` carried to step
`k` by the run with `π'`: `‖w i‖ ≤ 2 ‖mask B (mask (C i) vᵢ)‖` for the state `vᵢ` before step `i`
of the run with `π`, and `w i` is supported in `C i ∩ G k`. -/
theorem exists_stage_sub_eq_sum (h : A.StepCountOn z G C q) {π π' : Equiv.Perm ι}
    (hπ : Respects π G C) (hπ' : Respects π' G C) {B : Set ι} (hB : ∀ r ∉ B, π r = π' r)
    (hpad : ∀ k < d, permOp π (mask (C k)ᶜ (A.stage π z k)) =
      permOp π' (mask (C k)ᶜ (A.stage π z k))) :
    ∀ k ≤ d, ∃ w : ℕ → QState ι, A.stage π z k - A.stage π' z k = ∑ i ∈ range k, w i ∧
      ∀ i < k, ‖w i‖ ≤ 2 * ‖mask B (mask (C i) (A.stage π z i))‖ ∧
        Supported (C i ∩ G k) (w i) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨fun _ => 0, by simp [stage_zero], fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨w, hw, hwb⟩ := ih (by omega)
    set s := A.stage π z k
    set u := mask B (mask (C k) s)
    set δ := permOp π u - permOp π' u with hδdef
    have hp : permOp π (mask (C k)ᶜ s) = permOp π' (mask (C k)ᶜ s) := hpad k (by omega)
    have hδ : permOp π s - permOp π' s = δ := by
      rw [hδdef]
      conv_lhs => rw [← mask_add_mask_compl (C k) s, ← mask_add_mask_compl B (mask (C k) s)]
      rw [map_add, map_add, map_add, map_add, hp, permOp_mask_compl hB (mask (C k) s)]
      abel
    refine ⟨fun i => if i < k then A.stepAt z (k + 1) (permOp π' (w i))
      else A.stepAt z (k + 1) δ, ?_, ?_⟩
    · have e1 : A.stage π z (k + 1) - A.stage π' z (k + 1) =
          A.stepAt z (k + 1) (permOp π' (A.stage π z k - A.stage π' z k)) +
            A.stepAt z (k + 1) δ := by
        have e0 : permOp π (A.stage π z k) - permOp π' (A.stage π' z k) =
            permOp π' (A.stage π z k - A.stage π' z k) + δ := by
          rw [← hδ, map_sub]
          abel
        rw [stage_succ, stage_succ, ← map_sub, e0, map_add]
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
        exact (h.stepC i k hik.le (by omega) _ (h1.inter h2)).inter
          (h.stepG k (by omega) _ h2)
      · simp only [lt_irrefl, ↓reduceIte]
        refine ⟨?_, ?_⟩
        · rw [LinearIsometryEquiv.norm_map, two_mul]
          refine (norm_sub_le _ _).trans ?_
          rw [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]
        · have hsG := h.stage_supported hπ i (by omega)
          have hm : Supported (C i ∩ G i) u := fun r hr => by
            by_cases hrB : r ∈ B
            · rw [mask_apply_of_mem _ hrB]
              by_cases hrC : r ∈ C i
              · rw [mask_apply_of_mem _ hrC]
                exact hsG r fun hrG => hr ⟨hrC, hrG⟩
              · exact mask_apply_of_notMem _ hrC
            · exact mask_apply_of_notMem _ hrB
          have hpres : ∀ ρ : Equiv.Perm ι, Respects ρ G C →
              Supported (C i ∩ G i) (permOp ρ u) := fun ρ hρ =>
            hm.permOp fun r hr => ⟨(hρ.mem_iff i r).2 hr.1, hρ.mapsTo i r hr.2⟩
          have hd : Supported (C i ∩ G i) δ := (hpres π hπ).sub (hpres π' hπ')
          exact (h.stepC i i le_rfl (by omega) _ hd).inter
            (h.stepG i (by omega) _ (hd.mono Set.inter_subset_right))

/-- **AHU19 Lemma 8 with a per-branch count, for padded queries**: if `π` and `π'` agree outside
`B`, both respect `G` and `C`, and act alike on the part of the run of `π` outside `C k` before
step `k` (`hpad`), then the final states are within
`2 √q √(∑ i, ‖mask B (mask (C i) vᵢ)‖²)`. -/
theorem norm_final_sub_le (h : A.StepCountOn z G C q) {π π' : Equiv.Perm ι}
    (hπ : Respects π G C) (hπ' : Respects π' G C) {B : Set ι} (hB : ∀ r ∉ B, π r = π' r)
    (hpad : ∀ k < d, permOp π (mask (C k)ᶜ (A.stage π z k)) =
      permOp π' (mask (C k)ᶜ (A.stage π z k))) :
    ‖A.final π z - A.final π' z‖ ≤
      2 * √q * √(∑ i : Fin d, prob B (mask (C i) (A.pre π z i))) := by
  obtain ⟨w, hw, hwb⟩ := h.exists_stage_sub_eq_sum hπ hπ' hB hpad d le_rfl
  have hsum : 0 ≤ ∑ i : Fin d, prob B (mask (C i) (A.pre π z i)) :=
    sum_nonneg fun _ _ => prob_nonneg _ _
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt hsum, final, final, hw]
  refine (norm_sum_sq_le_of_count (range d) q w C (G d) (fun i hi => (hwb i (mem_range.1 hi)).2)
    h.count).trans ?_
  calc (q : ℝ) * ∑ i ∈ range d, ‖w i‖ ^ 2
      ≤ q * ∑ i ∈ range d, (2 * ‖mask B (mask (C i) (A.stage π z i))‖) ^ 2 := by
        gcongr with i hi
        exact (hwb i (mem_range.1 hi)).1
    _ = 2 ^ 2 * q * ∑ i : Fin d, prob B (mask (C i) (A.pre π z i)) := by
        rw [sum_range (fun i => (2 * ‖mask B (mask (C i) (A.stage π z i))‖) ^ 2), mul_sum,
          mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [prob, pre]
        ring

/-- **The steps at which the branches query number at most `q` on average**, for padded
queries: the probabilities of `C i` before step `i` sum to at most `q`. -/
theorem sum_prob_pre_le (h : A.StepCountOn z G C q) {π : Equiv.Perm ι} (hπ : Respects π G C) :
    ∑ i : Fin d, prob (C i) (A.pre π z i) ≤ q := by
  classical
  have hcomm : ∀ i k, i ≤ k → k < d → ∀ v, Supported (G k) v →
      mask (C i) (A.stepAt z (k + 1) (permOp π v)) = A.stepAt z (k + 1) (permOp π (mask (C i) v)) := by
    intro i k hik hk v hv
    have hu : Supported (G k) (permOp π v) := hv.permOp (hπ.mapsTo k)
    have hmC : mask (C i) (permOp π v) = permOp π (mask (C i) v) := mask_comm_of_supported
      (permOp π) (fun v hv => hv.permOp fun r hr => (hπ.mem_iff i r).2 hr)
      (fun v hv => hv.permOp fun r hr hr' => hr ((hπ.mem_iff i r).1 hr')) v
    have h1 : Supported (C i) (A.stepAt z (k + 1) (mask (C i) (permOp π v))) :=
      h.stepC i k hik hk _ ((supported_mask _ _).inter fun r hr => by
        by_cases hrC : r ∈ C i
        · rw [mask_apply_of_mem _ hrC]
          exact hu r hr
        · exact mask_apply_of_notMem _ hrC)
    have h2 : Supported (C i)ᶜ (A.stepAt z (k + 1) (mask (C i)ᶜ (permOp π v))) :=
      h.stepCc i k hik hk _ ((supported_mask _ _).inter fun r hr => by
        by_cases hrC : r ∈ (C i)ᶜ
        · rw [mask_apply_of_mem _ hrC]
          exact hu r hr
        · exact mask_apply_of_notMem _ hrC)
    have hsplit : A.stepAt z (k + 1) (permOp π v) = A.stepAt z (k + 1) (mask (C i) (permOp π v)) +
        A.stepAt z (k + 1) (mask (C i)ᶜ (permOp π v)) := by
      rw [← map_add, mask_add_mask_compl]
    rw [hsplit, map_add, h1.mask_eq_self, h2.mask_eq_zero fun r hr hr' => hr' hr, add_zero, hmC]
  have hnorm : ∀ i k, i ≤ k → k ≤ d → prob (C i) (A.stage π z k) = prob (C i) (A.stage π z i) := by
    intro i k hik hkd
    induction k, hik using Nat.le_induction with
    | base => rfl
    | succ k hik ih =>
      rw [stage_succ, prob, hcomm i k hik (by omega) _ (h.stage_supported hπ k (by omega)),
        LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, ← prob, ih (by omega)]
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

end StepCountOn

end OracleAlg

end GordieHowe.Quantum
