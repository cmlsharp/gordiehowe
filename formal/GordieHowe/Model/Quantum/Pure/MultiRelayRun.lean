-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.MultiRelay
public import GordieHowe.Model.Quantum.Interactive.Pure

@[expose] public section

/-!
# The run of the relayed distinguisher

The run of the relayed distinguisher `D.relay F b Q` (`GordieHowe/Model/Quantum/Pure/MultiRelay.lean`)
against a main environment `E'` at the tape `ω'`, compared with the run of `D` against an outer
environment `E` at the tape `ω`, under three hypotheses: the oracle in force of both environments is
`H` at all logs (`hO`, `hO'`), and `E` answers each request numbered below `Q` by the relay's reply
`F.runReply` against the main replies after the main requests of the requests before it (`hR`).
`D` has a budget of `b` query slots (`D.Budget b`) and `0 < n`.

- `pushV f v`: a vector pushed along a map; `prob_pushV` for maps injective on its support.
- `Distinguisher.place F b Q ansM H s j g`: the placement of a basis state `g` of `D`'s game at
  stage `j` and sub-slot `s` in the relayed game: `D`'s registers, the record of its entries, the
  stored answers and main requests of the schedule.
- `Distinguisher.relay_stage`: after each step the relayed state is the set-up of the pieces of
  `D`'s run placed by `place`. `Distinguisher.run_relay`: the relayed run is the set-up of `D`'s
  run pushed along the final placement, which is injective (`place_last_injective`).
- `Distinguisher.prob_final_relay`: every event of the relayed final state has the probability, in
  `D`'s final state, of its preimage under the placement and the set-up.
- `Distinguisher.relay_stage_count`: after every step, every branch of the relayed run has made at
  most `n · b + Q · qR` query slots, and fewer before a query slot.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

/-- The query slots below `s` of logs read from a list of entries of length at least `s`. -/
theorem queriesBefore_ofList {Req' B : Type} {S : ℕ} (l : List (Option Req' × B)) (dflt : Option Req' × B)
    (hd : dflt.1 = none) : ∀ s ≤ S, s ≤ l.length →
      queriesBefore (fun t : Fin S => (l.getD t dflt).1) s =
        (l.take s).countP fun e => e.1.isNone
  | 0, _, _ => by simp [queriesBefore_zero]
  | s + 1, hs, hl => by
    rw [queriesBefore_succ, queriesBefore_ofList l dflt hd s (by omega) (by omega), List.take_succ,
      List.getElem?_eq_getElem (show s < l.length by omega), List.countP_append]
    simp only [queriedAt, show s < S by omega, ↓reduceDIte, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (show s < l.length by omega), Option.getD_some, Option.toList_some,
      List.countP_singleton]

/-! ### Vectors pushed forward along a map -/

section Push

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- **The vector `v` pushed forward along `f`**: the amplitude of `k` is the sum of the amplitudes
of its preimages. -/
noncomputable def pushV (f : ι → κ) (v : QState ι) : QState κ :=
  WithLp.toLp 2 fun k => ∑ i ∈ univ.filter (fun i => f i = k), v i

theorem pushV_apply (f : ι → κ) (v : QState ι) (k : κ) :
    pushV f v k = ∑ i ∈ univ.filter (fun i => f i = k), v i :=
  rfl

theorem pushV_add (f : ι → κ) (u v : QState ι) : pushV f (u + v) = pushV f u + pushV f v := by
  ext k
  simp [pushV_apply, Finset.sum_add_distrib]

theorem pushV_zero (f : ι → κ) : pushV f (0 : QState ι) = 0 := by
  ext k
  simp [pushV_apply]

theorem pushV_sum {α : Type*} (f : ι → κ) (s : Finset α) (v : α → QState ι) :
    pushV f (∑ a ∈ s, v a) = ∑ a ∈ s, pushV f (v a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pushV_zero]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, pushV_add, ih]

/-- Two maps that agree on a support push a vector supported there to the same vector. -/
theorem pushV_congr {S : Set ι} {v : QState ι} (hv : Supported S v) {f f' : ι → κ}
    (h : ∀ i ∈ S, f i = f' i) : pushV f v = pushV f' v := by
  classical
  ext k
  simp only [pushV_apply]
  rw [← sum_filter_add_sum_filter_not _ (· ∈ S), ← sum_filter_add_sum_filter_not
    (univ.filter fun i => f' i = k) (· ∈ S)]
  have h0 : ∀ (t : Finset ι), ∑ i ∈ t.filter (· ∉ S), v i = 0 := fun t =>
    sum_eq_zero fun i hi => hv i (mem_filter.1 hi).2
  rw [h0, h0, filter_filter, filter_filter]
  congr 1
  refine sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun ⟨h1, h2⟩ => ⟨(h i h2) ▸ h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(h i h2).symm ▸ h1, h2⟩⟩

/-- **A basis permutation intertwined with the map on a support**: if `π' (f i) = f' (π i)` for
the basis states `i` of a support of `v`, pushing `v` along `f` and then permuting by `π'` is
permuting by `π` and pushing along `f'`. -/
theorem permOp_pushV {S : Set ι} {v : QState ι} (hv : Supported S v) {f f' : ι → κ}
    {π : Equiv.Perm ι} {π' : Equiv.Perm κ} (h : ∀ i ∈ S, π' (f i) = f' (π i)) :
    permOp π' (pushV f v) = pushV f' (permOp π v) := by
  classical
  have hv' : Supported (π '' S) (permOp π v) := hv.permOp fun i hi => ⟨i, hi, rfl⟩
  have hf : ∀ i ∈ π '' S, f' i = π' (f (π.symm i)) := by
    rintro _ ⟨i, hi, rfl⟩
    rw [Equiv.symm_apply_apply, h i hi]
  rw [pushV_congr hv' hf]
  ext k
  simp only [permOp_apply, pushV_apply]
  refine Finset.sum_equiv π (fun i => ?_) (fun i _ => ?_)
  · simp only [mem_filter, mem_univ, true_and, Equiv.symm_apply_apply]
    exact Equiv.eq_symm_apply π'
  · simp [permOp_apply]

/-- **The probability of a pushed vector** along a map injective on a support is the probability
of the preimage. -/
theorem prob_pushV {S : Set ι} {v : QState ι} (hv : Supported S v) {f : ι → κ}
    (hinj : Set.InjOn f S) (T : Set κ) : prob T (pushV f v) = prob (f ⁻¹' T) v := by
  classical
  simp only [prob, norm_mask_sq, pushV_apply]
  have hfib : ∀ k, ‖∑ i ∈ univ.filter (fun i => f i = k), v i‖ ^ 2 =
      ∑ i ∈ univ.filter (fun i => f i = k), ‖v i‖ ^ 2 := by
    intro k
    rw [← sum_filter_of_ne (p := (· ∈ S)) (fun i _ hi => by
        by_contra h
        exact hi (hv i h)),
      ← sum_filter_of_ne (p := (· ∈ S)) (s := univ.filter fun i => f i = k)
        (f := fun i => ‖v i‖ ^ 2) (fun i _ hi => by
        by_contra h
        exact hi (by rw [hv i h, norm_zero, sq, mul_zero]))]
    have hcard : ((univ.filter fun i => f i = k).filter (· ∈ S)).card ≤ 1 := by
      refine card_le_one.2 fun i hi j hj => ?_
      simp only [mem_filter, mem_univ, true_and] at hi hj
      exact hinj hi.2 hj.2 (hi.1.trans hj.1.symm)
    rcases Finset.eq_empty_or_nonempty ((univ.filter fun i => f i = k).filter (· ∈ S)) with
      h | ⟨i, hi⟩
    · rw [h]
      simp
    · rw [Finset.eq_singleton_iff_unique_mem.2 ⟨hi, fun j hj => card_le_one.1 hcard j hj i hi⟩]
      simp
  rw [sum_filter, sum_filter]
  simp only [hfib, ← sum_filter]
  rw [show (univ.filter fun x => x ∈ f ⁻¹' T) = univ.filter fun x => f x ∈ T from rfl,
    ← sum_fiberwise_of_maps_to (s := univ.filter fun x => f x ∈ T) (t := univ.filter (· ∈ T))
      (g := f) (fun x hx => by simpa using hx)]
  refine sum_congr rfl fun a ha => sum_congr ?_ fun _ _ => rfl
  ext x
  simp only [mem_filter, mem_univ, true_and] at ha ⊢
  exact ⟨fun h => ⟨h ▸ ha, h⟩, fun h => h.2⟩

theorem mask_inter' (A B : Set ι) (v : QState ι) : mask A (mask B v) = mask (A ∩ B) v := by
  classical
  ext i
  by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;> simp [hA, hB]

theorem mask_permOp_of_inv {A : Set ι} {π : Equiv.Perm ι} (h : ∀ i, π i ∈ A ↔ i ∈ A)
    (v : QState ι) : mask A (permOp π v) = permOp π (mask A v) := by
  classical
  ext i
  have h' : π.symm i ∈ A ↔ i ∈ A := by rw [← h (π.symm i), Equiv.apply_symm_apply]
  by_cases hi : i ∈ A
  · rw [mask_apply_of_mem _ hi, permOp_apply, permOp_apply, mask_apply_of_mem _ (h'.2 hi)]
  · rw [mask_apply_of_notMem _ hi, permOp_apply, mask_apply_of_notMem _ (fun hh => hi (h'.1 hh))]

theorem mask_of_empty {A : Set ι} (h : ∀ i, i ∉ A) (v : QState ι) : mask A v = 0 := by
  ext i
  rw [mask_apply_of_notMem _ (h i)]
  rfl

theorem mask_union_of_disjoint {A B : Set ι} (h : ∀ i, i ∈ A → i ∉ B) (v : QState ι) :
    mask (A ∪ B) v = mask A v + mask B v := by
  classical
  ext i
  by_cases hA : i ∈ A
  · simp [hA, h i hA]
  · by_cases hB : i ∈ B <;> simp [hA, hB]

theorem permOp_refl' (v : QState ι) : permOp (Equiv.refl ι) v = v := by
  ext i
  rfl

/-- **A mask after a permutation** is the permutation after a mask, on a support where the
permutation maps the second set onto the first. -/
theorem mask_permOp_of_supported {B A A' : Set ι} {v : QState ι} (hv : Supported B v)
    {π : Equiv.Perm ι} (h : ∀ i ∈ B, π i ∈ A ↔ i ∈ A') :
    mask A (permOp π v) = permOp π (mask A' v) := by
  classical
  ext i
  simp only [permOp_apply]
  by_cases hB : π.symm i ∈ B
  · have h' := h _ hB
    rw [Equiv.apply_symm_apply] at h'
    by_cases hi : i ∈ A
    · rw [mask_apply_of_mem _ hi, permOp_apply, mask_apply_of_mem _ (h'.1 hi)]
    · rw [mask_apply_of_notMem _ hi, mask_apply_of_notMem _ (fun hh => hi (h'.2 hh))]
  · have h0 := hv _ hB
    by_cases hi : i ∈ A
    · rw [mask_apply_of_mem _ hi, permOp_apply, h0]
      by_cases hA' : π.symm i ∈ A'
      · rw [mask_apply_of_mem _ hA', h0]
      · rw [mask_apply_of_notMem _ hA']
    · rw [mask_apply_of_notMem _ hi]
      by_cases hA' : π.symm i ∈ A'
      · rw [mask_apply_of_mem _ hA', h0]
      · rw [mask_apply_of_notMem _ hA']

/-- Permutations that agree on a set they keep, together with its complement, permute a mask on
that set alike. -/
theorem mask_permOp_congr {A : Set ι} {π π' : Equiv.Perm ι} (hA : ∀ i, π i ∈ A ↔ i ∈ A)
    (h : ∀ i ∈ A, π i = π' i) (v : QState ι) : mask A (permOp π v) = mask A (permOp π' v) := by
  classical
  ext i
  by_cases hi : i ∈ A
  · rw [mask_apply_of_mem _ hi, mask_apply_of_mem _ hi]
    simp only [permOp_apply]
    have hs : π.symm i ∈ A := by rw [← hA, Equiv.apply_symm_apply]; exact hi
    have h1 : π' (π.symm i) = i := by rw [← h _ hs, Equiv.apply_symm_apply]
    rw [(Equiv.eq_symm_apply π').2 h1]
  · rw [mask_apply_of_notMem _ hi, mask_apply_of_notMem _ hi]

/-- The Born probability of a set after a basis permutation is that of its preimage. -/
theorem prob_permOp' (π : Equiv.Perm ι) (S : Set ι) (v : QState ι) :
    prob S (permOp π v) = prob (π ⁻¹' S) v := by
  classical
  rw [prob, prob, norm_mask_sq, norm_mask_sq, Finset.sum_filter, Finset.sum_filter]
  rw [← Equiv.sum_comp π]
  simp

theorem Supported.sum {α : Type*} {S : Set ι} (s : Finset α) {v : α → QState ι}
    (h : ∀ a ∈ s, Supported S (v a)) : Supported S (∑ a ∈ s, v a) := by
  intro i hi
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  exact Finset.sum_eq_zero fun a ha => h a ha i hi

theorem Supported.pushV {T : Set ι} {S : Set κ} {v : QState ι} (hv : Supported T v) {f : ι → κ}
    (h : ∀ i ∈ T, f i ∈ S) : Supported S (Quantum.pushV f v) := by
  intro k hk
  rw [pushV_apply]
  refine Finset.sum_eq_zero fun i hi => hv i fun hT => hk ?_
  rw [← (Finset.mem_filter.1 hi).2]
  exact h i hT

end Push

namespace MultiRelay

theorem getD_append_of_lt {α : Type*} (l l' : List α) (d : α) {k : ℕ} (h : k < l.length) :
    (l ++ l').getD k d = l.getD k d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_of_le {α : Type*} (l l' : List α) (d : α) {k : ℕ} (h : l.length ≤ k) :
    (l ++ l').getD k d = l'.getD (k - l.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_of_length_le {α : Type*} (l : List α) (d : α) {k : ℕ} (h : l.length ≤ k) :
    l.getD k d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

end MultiRelay

namespace MultiRelay

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)
  [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] (n b Q : ℕ)
  (ansM : List Req' → Req' → Option Resp') (H : X → Y)

/-! ### The relayed request -/

omit [Inhabited Req'] in
theorem runAux_succ_snd (r : Req) (rs : List Req') (i : ℕ) :
    ∃ e, (F.runAux ansM H r rs (i + 1)).2 = (F.runAux ansM H r rs i).2 ++ [e] :=
  ⟨_, rfl⟩

/-- The entries of the first `i` sub-slots are a prefix of those of the first `j ≥ i`. -/
theorem take_runAux {r : Req} {rs : List Req'} {i j : ℕ} (hij : i ≤ j) :
    (F.runAux ansM H r rs j).2.take i = (F.runAux ansM H r rs i).2 := by
  induction j, hij using Nat.le_induction with
  | base => simp [F.length_runAux]
  | succ j hij ih =>
    obtain ⟨e, he⟩ := F.runAux_succ_snd ansM H r rs j
    rw [he, List.take_append_of_le_length (by rw [F.length_runAux]; exact hij), ih]

/-! ### The side answers along a run -/

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem sideVals_append (l l' : List ((Y ⊕ Ys) ⊕ Option Resp')) :
    sideVals (l ++ l') = sideVals l ++ sideVals l' :=
  List.filterMap_append

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **A state whose side answers are its side reads**: as many side answers fed as side reads
made. -/
def SideInv (st : RelaySt Y Resp' Ys) : Prop := (sideVals st.ans).length = st.ns

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem sideStep_ans (sa : ℕ → Xs → Ys) (r : Req) (st : RelaySt Y Resp' Ys) :
    ∃ l, (F.sideStep sa r st).ans = st.ans ++ l := by
  unfold sideStep
  rcases F.progAct r st with _ | ((x | x) | r')
  · exact ⟨[], by simp⟩
  · exact ⟨[], by simp⟩
  · exact ⟨_, rfl⟩
  · exact ⟨[], by simp⟩

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem sideInv_sideStep (sa : ℕ → Xs → Ys) (r : Req) {st : RelaySt Y Resp' Ys}
    (h : SideInv st) : SideInv (F.sideStep sa r st) := by
  unfold sideStep
  rcases F.progAct r st with _ | ((x | x) | r')
  · exact h
  · exact h
  · show (sideVals (st.ans ++ [_])).length = st.ns + 1
    rw [sideVals_append, List.length_append, h]
    rfl
  · exact h

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem iterate_sideStep_ans (sa : ℕ → Xs → Ys) (r : Req) :
    ∀ (j : ℕ) (st : RelaySt Y Resp' Ys), ∃ l, ((F.sideStep sa r)^[j] st).ans = st.ans ++ l
  | 0, _ => ⟨[], by simp⟩
  | j + 1, st => by
    rw [Function.iterate_succ_apply]
    obtain ⟨l₁, h₁⟩ := F.sideStep_ans sa r st
    obtain ⟨l₂, h₂⟩ := iterate_sideStep_ans sa r j (F.sideStep sa r st)
    exact ⟨l₁ ++ l₂, by rw [h₂, h₁, List.append_assoc]⟩

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem sideInv_iterate_sideStep (sa : ℕ → Xs → Ys) (r : Req) :
    ∀ (j : ℕ) {st : RelaySt Y Resp' Ys}, SideInv st → SideInv ((F.sideStep sa r)^[j] st)
  | 0, _, h => h
  | j + 1, st, h => by
    rw [Function.iterate_succ_apply]
    exact sideInv_iterate_sideStep sa r j (F.sideInv_sideStep sa r h)

omit [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem next_ans (r : Req) (st : RelaySt Y Resp' Ys) (a : Option Resp' × (X × Y)) :
    ∃ l, (F.next r st a).ans = st.ans ++ l ∧ sideVals l = [] := by
  unfold next
  rcases F.progAct r st with _ | ((x | x) | r')
  · split_ifs <;> exact ⟨[], by simp, rfl⟩
  · exact ⟨_, rfl, rfl⟩
  · split_ifs <;> exact ⟨[], by simp, rfl⟩
  · exact ⟨_, rfl, rfl⟩

omit [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem sideInv_next (r : Req) {st : RelaySt Y Resp' Ys} (a : Option Resp' × (X × Y))
    (h : SideInv st) : SideInv (F.next r st a) := by
  obtain ⟨l, hl, hs⟩ := F.next_ans r st a
  unfold SideInv
  rw [hl, sideVals_append, hs, List.append_nil, F.ns_next]
  exact h

theorem sideInv_runAux (ansM : List Req' → Req' → Option Resp') (H : X → Y) (r : Req)
    (rs : List Req') : ∀ i, SideInv (F.runAux ansM H r rs i).1
  | 0 => rfl
  | i + 1 => F.sideInv_iterate_sideStep _ r _ (F.sideInv_next r _ (sideInv_runAux ansM H r rs i))

omit [Zero Y] [Inhabited Req'] in
theorem close_next_ans (sa : ℕ → Xs → Ys) (r : Req) (st : RelaySt Y Resp' Ys)
    (a : Option Resp' × (X × Y)) : ∃ l, (F.close sa r (F.next r st a)).ans = st.ans ++ l := by
  obtain ⟨l₁, h₁, -⟩ := F.next_ans r st a
  obtain ⟨l₂, h₂⟩ := F.iterate_sideStep_ans sa r F.qS (F.next r st a)
  exact ⟨l₁ ++ l₂, by unfold close; rw [h₂, h₁, List.append_assoc]⟩

theorem runAux_ans_succ (ansM : List Req' → Req' → Option Resp') (H : X → Y) (r : Req)
    (rs : List Req') (i : ℕ) :
    ∃ l, (F.runAux ansM H r rs (i + 1)).1.ans = (F.runAux ansM H r rs i).1.ans ++ l :=
  F.close_next_ans _ r _ _

theorem runAux_ans_le (ansM : List Req' → Req' → Option Resp') (H : X → Y) (r : Req)
    (rs : List Req') {i j : ℕ} (hij : i ≤ j) :
    ∃ l, (F.runAux ansM H r rs j).1.ans = (F.runAux ansM H r rs i).1.ans ++ l := by
  induction j, hij using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ j _ ih =>
    obtain ⟨l₁, h₁⟩ := ih
    obtain ⟨l₂, h₂⟩ := F.runAux_ans_succ ansM H r rs j
    exact ⟨l₁ ++ l₂, by rw [h₂, h₁, List.append_assoc]⟩

theorem ns_runAux_le (ansM : List Req' → Req' → Option Resp') (H : X → Y) (r : Req)
    (rs : List Req') {i j : ℕ} (hij : i ≤ j) :
    (F.runAux ansM H r rs i).1.ns ≤ (F.runAux ansM H r rs j).1.ns := by
  obtain ⟨l, hl⟩ := F.runAux_ans_le ansM H r rs hij
  have h1 := F.sideInv_runAux ansM H r rs i
  have h2 := F.sideInv_runAux ansM H r rs j
  unfold SideInv at h1 h2
  rw [hl, sideVals_append, List.length_append] at h2
  omega

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
/-- **A side vector agreeing with a state**: its entries below the side reads made are the side
answers fed. -/
def VecAgrees (V : Fin F.qS → Ys) (st : RelaySt Y Resp' Ys) : Prop :=
  ∀ k (hk : k < F.qS), k < st.ns → V ⟨k, hk⟩ = (sideVals st.ans).getD k 0

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
theorem vecAgrees_sideVec (st : RelaySt Y Resp' Ys) : F.VecAgrees (F.sideVec st) st :=
  fun _ _ _ => rfl

omit [Inhabited X] [Zero Y] [Inhabited Req'] in
variable {F} in
/-- A side vector agreeing with a later state agrees with an earlier one. -/
theorem VecAgrees.of_prefix {V : Fin F.qS → Ys} {st st' : RelaySt Y Resp' Ys}
    (h : F.VecAgrees V st') (hst : SideInv st) (hp : ∃ l, st'.ans = st.ans ++ l)
    (hns : st.ns ≤ st'.ns) : F.VecAgrees V st := fun k hk hks => by
  obtain ⟨l, hl⟩ := hp
  have hlt : k < (sideVals st.ans).length := by
    unfold SideInv at hst
    omega
  rw [h k hk (by omega), hl, sideVals_append, getD_append_of_lt _ _ _ hlt]

omit [Inhabited X] [Inhabited Req'] in
/-- **A side step answered from an agreeing side vector** is the side step answered by the side
function. -/
theorem sideStep_vecSa {V : Fin F.qS → Ys} (r : Req) {st : RelaySt Y Resp' Ys}
    (hinv : SideInv st) (h : F.VecAgrees V (F.sideStep F.sideSa r st)) :
    F.sideStep (F.vecSa V) r st = F.sideStep F.sideSa r st := by
  unfold sideStep at h ⊢
  rcases hp : F.progAct r st with _ | ((x | x) | r')
  · rfl
  · rfl
  · simp only [hp] at h
    have hlt := F.ns_lt_of_progAct r st hp
    have hk := h st.ns hlt (by simp)
    simp only [sideVals_append] at hk
    unfold SideInv at hinv
    rw [getD_append_of_le _ _ _ (by omega), hinv, Nat.sub_self] at hk
    simp only [vecSa, hlt, ↓reduceDIte, hk]
    rfl
  · rfl

omit [Inhabited X] [Inhabited Req'] in
theorem iterate_sideStep_vecSa {V : Fin F.qS → Ys} (r : Req) :
    ∀ (j : ℕ) {st : RelaySt Y Resp' Ys}, SideInv st →
      F.VecAgrees V ((F.sideStep F.sideSa r)^[j] st) →
        (F.sideStep (F.vecSa V) r)^[j] st = (F.sideStep F.sideSa r)^[j] st
  | 0, _, _, _ => rfl
  | j + 1, st, hinv, h => by
    rw [Function.iterate_succ_apply] at h ⊢
    rw [Function.iterate_succ_apply]
    have h1 : F.VecAgrees V (F.sideStep F.sideSa r st) :=
      h.of_prefix (F.sideInv_sideStep _ r hinv) (F.iterate_sideStep_ans _ r j _)
        (F.ns_le_iterate_sideStep _ r j _)
    rw [F.sideStep_vecSa r hinv h1]
    exact iterate_sideStep_vecSa r j (F.sideInv_sideStep _ r hinv) h

omit [Inhabited X] [Inhabited Req'] in
theorem close_vecSa {V : Fin F.qS → Ys} (r : Req) {st : RelaySt Y Resp' Ys} (hinv : SideInv st)
    (h : F.VecAgrees V (F.close F.sideSa r st)) :
    F.close (F.vecSa V) r st = F.close F.sideSa r st :=
  F.iterate_sideStep_vecSa r F.qS hinv h

/-- **The state on a prefix of a run, its side reads answered from an agreeing side vector**, is
the run's state. -/
theorem stAt_vecSa_runAux (r : Req) (rs : List Req') {V : Fin F.qS → Ys}
    {g : ℕ → Option Resp' × (X × Y)} :
    ∀ i, (∀ k < i, g k = ((F.runAux ansM H r rs i).2.getD k (none, (none, (default, 0)))).2) →
      F.VecAgrees V (F.runAux ansM H r rs i).1 →
        F.stAt (F.vecSa V) r g i = (F.runAux ansM H r rs i).1
  | 0, _, _ => rfl
  | i + 1, hg, hV => by
    have hgi : ∀ k < i, g k = ((F.runAux ansM H r rs i).2.getD k (none, (none, (default, 0)))).2 :=
      fun k hk => by
        rw [hg k (by omega)]
        simp only [runAux, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left (by rw [F.length_runAux]; exact hk)]
    have hV' : F.VecAgrees V (F.runAux ansM H r rs i).1 :=
      hV.of_prefix (F.sideInv_runAux ansM H r rs i) (F.runAux_ans_succ ansM H r rs i)
        (F.ns_runAux_le ansM H r rs (Nat.le_succ i))
    have ih := stAt_vecSa_runAux r rs i hgi hV'
    have hgl : g i = ((F.runAux ansM H r rs (i + 1)).2.getD i (none, (none, (default, 0)))).2 :=
      hg i (by omega)
    simp only [runAux, List.getD_eq_getElem?_getD] at hgl
    rw [List.getElem?_append_right (by rw [F.length_runAux]), F.length_runAux, Nat.sub_self] at hgl
    simp only [List.getElem?_cons_zero, Option.getD_some] at hgl
    rw [stAt, ih, hgl]
    exact F.close_vecSa r (F.sideInv_next r _ (F.sideInv_runAux ansM H r rs i)) hV

/-- **The state after the first `i` sub-slots is the state on their stored answers**, the side
reads answered from the side vector of any later state. -/
theorem stAt_runAux (r : Req) (rs : List Req') {i j : ℕ} (hij : i ≤ j) :
    F.stAt (F.vecSa (F.sideVec (F.runAux ansM H r rs j).1)) r
      (fun k => ((F.runAux ansM H r rs j).2.getD k (none, (none, (default, 0)))).2) i =
      (F.runAux ansM H r rs i).1 := by
  refine F.stAt_vecSa_runAux ansM H r rs i (fun k hk => ?_) ?_
  · rw [← F.take_runAux ansM H hij, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt hk]
  · exact (F.vecAgrees_sideVec _).of_prefix (F.sideInv_runAux ansM H r rs i)
      (F.runAux_ans_le ansM H r rs hij) (F.ns_runAux_le ansM H r rs hij)

/-! ### The schedule -/

theorem sched_append (es : List (Option Req)) (e : Option Req) :
    F.sched n b Q ansM H (es ++ [e]) = F.schedStep n b Q ansM H (F.sched n b Q ansM H es) e := by
  simp [sched, List.foldl_append]

theorem schedStep_out (st : SchedSt X Y Req' Resp' (Fin F.qS → Ys)) (e : Option Req) :
    (F.schedStep n b Q ansM H st e).out = st.out ++ F.blockOf n b Q ansM H st e := by
  rcases e with _ | r <;> simp only [schedStep, blockOf] <;> split_ifs <;> rfl

theorem schedStep_side (st : SchedSt X Y Req' Resp' (Fin F.qS → Ys)) (e : Option Req) :
    (F.schedStep n b Q ansM H st e).side = st.side ++ [F.sideOf b Q ansM H st e] := by
  rcases e with _ | r <;> simp only [schedStep, sideOf] <;> split_ifs <;> rfl

/-- **The schedule has one side vector per slot.** -/
theorem length_sched_side (es : List (Option Req)) :
    (F.sched n b Q ansM H es).side.length = es.length := by
  induction es using List.reverseRecOn with
  | nil => rfl
  | append_singleton es e ih =>
    rw [sched_append, schedStep_side, List.length_append, List.length_append, ih]
    rfl

theorem sched_qb_rb (es : List (Option Req)) :
    (F.sched n b Q ansM H es).qb = es.countP Option.isNone ∧
      (F.sched n b Q ansM H es).rb = es.countP Option.isSome := by
  induction es using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl⟩
  | append_singleton es e ih =>
    rw [sched_append]
    rcases e with _ | r <;> simp only [schedStep] <;> split_ifs <;> simp [List.countP_append, ih.1, ih.2]

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem blkAt_append_of_lt {es : List (Option Req)} (e : Option Req) {i : ℕ} (hi : i < es.length) :
    blkAt b Q (es ++ [e]) i = blkAt b Q es i := by
  simp only [blkAt, List.take_append_of_le_length hi.le, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hi]

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem blkAt_append_length (es : List (Option Req)) (e : Option Req) :
    blkAt b Q (es ++ [e]) es.length =
      blk b Q (es.countP Option.isNone) (es.countP Option.isSome) e := by
  simp [blkAt, List.take_append_of_le_length le_rfl]

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem startAt_append_of_le {es : List (Option Req)} (e : Option Req) {i : ℕ}
    (hi : i ≤ es.length) : F.startAt n b Q (es ++ [e]) i = F.startAt n b Q es i := by
  unfold startAt
  refine Finset.sum_congr rfl fun i' hi' => ?_
  rw [blkAt_append_of_lt b Q e (by simp at hi'; omega)]

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem startAt_succ (es : List (Option Req)) (i : ℕ) :
    F.startAt n b Q es (i + 1) = F.startAt n b Q es i + F.blkLen n (blkAt b Q es i) :=
  Finset.sum_range_succ _ _

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem blkLen_pos (hn : 0 < n) (k : Blk) : 0 < F.blkLen n k := by
  cases k
  · exact hn
  · exact Nat.one_pos
  · exact F.len_pos

theorem length_blockOf (st : SchedSt X Y Req' Resp' (Fin F.qS → Ys)) (e : Option Req) :
    (F.blockOf n b Q ansM H st e).length = F.blkLen n (blk b Q st.qb st.rb e) := by
  rcases e with _ | r <;> simp only [blockOf, blk] <;> split_ifs <;>
    simp [blkLen, runEntries, F.length_runAux]

/-- **The schedule has `startAt` sub-slots.** -/
theorem length_sched (es : List (Option Req)) :
    (F.sched n b Q ansM H es).out.length = F.startAt n b Q es es.length := by
  induction es using List.reverseRecOn with
  | nil => rfl
  | append_singleton es e ih =>
    rw [sched_append, schedStep_out, List.length_append, ih, length_blockOf,
      (F.sched_qb_rb n b Q ansM H es).1, (F.sched_qb_rb n b Q ansM H es).2, List.length_append,
      List.length_singleton, startAt_succ, startAt_append_of_le F n b Q e le_rfl,
      blkAt_append_length]

/-! ### Trailing idle sub-slots -/

theorem length_tailEntries (out : List (Option Req' × (Option Resp' × (X × Y)))) :
    ∀ k, (F.tailEntries ansM out k).length = out.length + k
  | 0 => rfl
  | k + 1 => by simp [tailEntries, length_tailEntries out k, Nat.add_assoc]

theorem take_tailEntries (out : List (Option Req' × (Option Resp' × (X × Y)))) {i k : ℕ}
    (hik : i ≤ k) : (F.tailEntries ansM out k).take (out.length + i) = F.tailEntries ansM out i := by
  induction k, hik using Nat.le_induction with
  | base => rw [List.take_of_length_le (by rw [length_tailEntries])]
  | succ k hik ih =>
    rw [tailEntries, List.take_append_of_le_length (by rw [length_tailEntries]; omega), ih]

theorem take_tailEntries_of_le (out : List (Option Req' × (Option Resp' × (X × Y)))) (k : ℕ)
    {t : ℕ} (ht : t ≤ out.length) : (F.tailEntries ansM out k).take t = out.take t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [tailEntries, List.take_append_of_le_length (by rw [length_tailEntries]; omega), ih]

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- The first sub-slot of block `i` reads only the entries below `i`. -/
theorem startAt_congr {es es' : List (Option Req)} {i : ℕ} (h : es.take i = es'.take i) :
    F.startAt n b Q es i = F.startAt n b Q es' i := by
  unfold startAt
  refine Finset.sum_congr rfl fun i' hi' => ?_
  have hi'' : i' < i := Finset.mem_range.1 hi'
  have ht : es.take i' = es'.take i' := by
    have := congrArg (List.take i') h
    simpa [List.take_take, Nat.min_eq_left hi''.le] using this
  have hg : es.getD i' none = es'.getD i' none := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, ← List.getElem?_take_of_lt hi'',
      h, List.getElem?_take_of_lt hi'']
  simp only [blkAt, ht, hg]

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **Each block has at least one sub-slot**, so block `i` starts at sub-slot `i` or later. -/
theorem le_startAt (hn : 0 < n) (es : List (Option Req)) : ∀ i, i ≤ F.startAt n b Q es i
  | 0 => Nat.zero_le _
  | i + 1 => by
    rw [startAt_succ]
    have := F.blkLen_pos n hn (blkAt b Q es i)
    have := le_startAt hn es i
    omega

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem startAt_mono (es : List (Option Req)) {i j : ℕ} (hij : i ≤ j) :
    F.startAt n b Q es i ≤ F.startAt n b Q es j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih => rw [startAt_succ]; omega

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem startAt_lt_of_lt (hn : 0 < n) (es : List (Option Req)) {i j : ℕ} (hij : i < j) :
    F.startAt n b Q es i < F.startAt n b Q es j := by
  have h1 := F.startAt_mono n b Q es (Nat.succ_le_of_lt hij)
  rw [startAt_succ] at h1
  have := F.blkLen_pos n hn (blkAt b Q es i)
  omega

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **The first `i` blocks fit in `i * max n F.len` sub-slots.** -/
theorem startAt_le (es : List (Option Req)) : ∀ i, F.startAt n b Q es i ≤ i * max n F.len
  | 0 => Nat.zero_le _
  | i + 1 => by
    rw [startAt_succ, Nat.succ_mul]
    have h1 := startAt_le es i
    have h2 : F.blkLen n (blkAt b Q es i) ≤ max n F.len := by
      cases blkAt b Q es i
      · exact le_max_left _ _
      · exact le_trans F.len_pos (le_max_right _ _)
      · exact le_max_right _ _
    omega

theorem getElem?_tailEntries_of_lt (out : List (Option Req' × (Option Resp' × (X × Y)))) (k : ℕ)
    {t : ℕ} (ht : t < out.length) : (F.tailEntries ansM out k)[t]? = out[t]? := by
  rw [← List.getElem?_take_of_lt (Nat.lt_succ_self t),
    F.take_tailEntries_of_le ansM out k (Nat.succ_le_of_lt ht),
    List.getElem?_take_of_lt (Nat.lt_succ_self t)]

/-- **A trailing idle sub-slot** stores the idle request with its reply after the entries before
it. -/
theorem getElem?_tailEntries_of_le (out : List (Option Req' × (Option Resp' × (X × Y)))) :
    ∀ (k : ℕ) {t : ℕ}, out.length ≤ t → t < out.length + k →
      (F.tailEntries ansM out k)[t]? = some (F.idleEntry ansM ((F.tailEntries ansM out k).take t))
  | 0, t, h1, h2 => absurd h2 (by omega)
  | k + 1, t, h1, h2 => by
    have hlen := F.length_tailEntries ansM out k
    rcases Nat.lt_or_ge t (out.length + k) with h | h
    · rw [tailEntries, List.getElem?_append_left (by omega),
        getElem?_tailEntries_of_le out k h1 h, List.take_append_of_le_length (by omega)]
    · have ht : t = (F.tailEntries ansM out k).length := by omega
      rw [tailEntries, List.getElem?_append_right (by omega), ht, Nat.sub_self,
        List.take_append_of_le_length le_rfl, List.take_length]
      rfl

theorem take_succ_tailEntries (out : List (Option Req' × (Option Resp' × (X × Y)))) (s : ℕ) :
    (F.tailEntries ansM out (s + 1)).take (s + 1) =
      (F.tailEntries ansM out s).take s ++ [((F.tailEntries ansM out (s + 1))[s]?).getD
        (none, (none, (default, 0)))] := by
  have hl : s < (F.tailEntries ansM out (s + 1)).length := by
    rw [length_tailEntries]; omega
  rw [List.take_succ, List.getElem?_eq_getElem hl]
  simp only [Option.toList_some, Option.getD_some]
  congr 1
  rw [tailEntries, List.take_append_of_le_length (by rw [length_tailEntries]; omega)]

/-- **The entries of the sub-slots before sub-slot `s`** of the entry list `es`: its schedule,
then idle sub-slots, cut at `s`. -/
def subEntriesL (s : ℕ) (es : List (Option Req)) : List (Option Req' × (Option Resp' × (X × Y))) :=
  (F.tailEntries ansM (F.sched n b Q ansM H es).out s).take s

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem length_filterMap_id (es : List (Option Req)) :
    (es.filterMap id).length = es.countP Option.isSome := by
  induction es with
  | nil => rfl
  | cons e es ih => rcases e with _ | r <;> simpa using ih

/-- **No query slot over the budget**: every query entry comes after fewer than `b` query
entries. -/
def NoIdleQ (b : ℕ) (es : List (Option Req)) : Prop :=
  ∀ i < es.length, es.getD i none = none → (es.take i).countP Option.isNone < b

theorem mainReqs_append (rs : List Req) (r : Req) :
    F.mainReqs Q ansM H (rs ++ [r]) =
      if rs.length < Q then F.mainReqs Q ansM H rs ++
        (F.runEntries ansM H r (F.mainReqs Q ansM H rs)).filterMap Prod.fst
      else F.mainReqs Q ansM H rs ++ [F.idle] := by
  have hc : ∀ rs : List Req, (rs.foldl (fun (p : List Req' × ℕ) r =>
      (if p.2 < Q then p.1 ++ (F.runEntries ansM H r p.1).filterMap Prod.fst else p.1 ++ [F.idle],
        p.2 + 1)) ([], 0)).2 = rs.length := by
    intro rs
    induction rs using List.reverseRecOn with
    | nil => rfl
    | append_singleton rs r ih => simp [List.foldl_append, ih]
  unfold mainReqs
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, hc]

/-- **The main requests of the schedule are those of its requests** when no query slot is over
the budget. -/
theorem filterMap_sched (es : List (Option Req)) (hes : NoIdleQ b es) :
    (F.sched n b Q ansM H es).out.filterMap Prod.fst = F.mainReqs Q ansM H (es.filterMap id) := by
  induction es using List.reverseRecOn with
  | nil => rfl
  | append_singleton es e ih =>
    have hes' : NoIdleQ b es := fun i hi h => by
      have := hes i (by simp; omega) (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
        rwa [List.getD_eq_getElem?_getD] at h)
      rwa [List.take_append_of_le_length hi.le] at this
    rw [F.sched_append, F.schedStep_out, List.filterMap_append, ih hes']
    have hqb := (F.sched_qb_rb n b Q ansM H es).1
    have hrb := (F.sched_qb_rb n b Q ansM H es).2
    rcases e with _ | r
    · have hlt : (F.sched n b Q ansM H es).qb < b := by
        rw [hqb]
        have := hes es.length (by simp) (by simp)
        rwa [List.take_append_of_le_length le_rfl, List.take_length] at this
      simp [blockOf, hlt, List.filterMap_replicate]
    · have hlen : (es.filterMap id).length = es.countP Option.isSome := length_filterMap_id es
      rw [List.filterMap_append, show ([some r] : List (Option Req)).filterMap id = [r] from rfl,
        F.mainReqs_append, hlen]
      simp only [blockOf, hrb, ← ih hes']
      split_ifs
      · rfl
      · simp [idleEntry, ih hes']

/-! ### Counting the query sub-slots -/

/-- The query sub-slots among entries: those without a main request. -/
def noneCount (l : List (Option Req' × (Option Resp' × (X × Y)))) : ℕ :=
  l.countP fun e => e.1.isNone

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem noneCount_append (l l' : List (Option Req' × (Option Resp' × (X × Y)))) :
    noneCount (l ++ l') = noneCount l + noneCount l' :=
  List.countP_append

omit [Inhabited Req'] in
/-- **The query sub-slots of a relayed request are the queries and pad sub-slots of its
state.** -/
theorem noneCount_runAux (r : Req) (rs : List Req') :
    ∀ i, noneCount (F.runAux ansM H r rs i).2 =
      (F.runAux ansM H r rs i).1.nq + (F.runAux ansM H r rs i).1.np
  | 0 => rfl
  | i + 1 => by
    simp only [runAux]
    rw [noneCount_append, noneCount_runAux r rs i, F.nq_close, F.np_close]
    unfold act next
    rcases hp : F.progAct r (F.runAux ansM H r rs i).1 with _ | ((x | x) | r')
    · simp only
      split_ifs <;> simp [noneCount] <;> omega
    · simp [noneCount]
      omega
    · simp only
      split_ifs <;> simp [noneCount] <;> omega
    · simp [noneCount]

omit [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- A relayed request makes at most `K` main requests. -/
theorem na_stAt_le (sa : ℕ → Xs → Ys) (r : Req) (g : ℕ → Option Resp' × (X × Y)) :
    ∀ i, (F.stAt sa r g i).na ≤ F.K
  | 0 => Nat.zero_le _
  | i + 1 => by
    simp only [stAt]
    rw [F.na_close]
    exact F.na_next_le r _ _ (na_stAt_le sa r g i)

omit [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **A sub-slot keeps the query budget**: at most `qR` queries and `qP` pad sub-slots, or `K`
main requests. -/
theorem next_budget (r : Req) (st : RelaySt Y Resp' Ys) (a : Option Resp' × (X × Y))
    (hK : st.na ≤ F.K) (h : (st.nq ≤ F.qR ∧ st.np ≤ F.qP) ∨ st.na = F.K) :
    ((F.next r st a).nq ≤ F.qR ∧ (F.next r st a).np ≤ F.qP) ∨ (F.next r st a).na = F.K := by
  unfold next
  rcases hp : F.progAct r st with _ | ((x | x) | r')
  · simp only
    split_ifs with h1 <;> simp only <;> omega
  · have := F.nq_lt_of_progAct r st hp
    simp only
    omega
  · simp only
    split_ifs with h1 h2 <;> simp only <;> omega
  · have := F.na_lt_of_progAct r st hp
    simp only
    omega

omit [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **The query budget of a relayed request**: at most `qR` queries and `qP` pad sub-slots while
the program runs, and `K` main requests once it pads with queries. -/
theorem stAt_budget (sa : ℕ → Xs → Ys) (r : Req) (g : ℕ → Option Resp' × (X × Y)) :
    ∀ i, ((F.stAt sa r g i).nq ≤ F.qR ∧ (F.stAt sa r g i).np ≤ F.qP) ∨
      (F.stAt sa r g i).na = F.K
  | 0 => .inl ⟨Nat.zero_le _, Nat.zero_le _⟩
  | i + 1 => by
    simp only [stAt]
    rw [F.na_close, F.nq_close, F.np_close]
    exact F.next_budget r _ _ (F.na_stAt_le sa r g i) (stAt_budget sa r g i)

omit [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **At most `qR + qP` query sub-slots per relayed request**: its queries and pad sub-slots. -/
theorem nq_stAt_le (sa : ℕ → Xs → Ys) (r : Req) (g : ℕ → Option Resp' × (X × Y)) :
    ∀ i ≤ F.len, (F.stAt sa r g i).nq + (F.stAt sa r g i).np ≤ F.qR + F.qP := by
  intro i hi
  have hs := F.counts_stAt sa r g i
  rcases F.stAt_budget sa r g i with h | h
  · omega
  · unfold len at hi
    omega

omit [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **Fewer than `qR + qP` query sub-slots before a query sub-slot** of a relayed request. -/
theorem nq_add_np_lt_of_act (sa : ℕ → Xs → Ys) (r : Req) (g : ℕ → Option Resp' × (X × Y))
    {i : ℕ} (hi : i < F.len) (h : (F.act r (F.stAt sa r g i)).isLeft) :
    (F.stAt sa r g i).nq + (F.stAt sa r g i).np < F.qR + F.qP := by
  have hs := F.counts_stAt sa r g i
  have hK := F.na_stAt_le sa r g i
  have hb := F.stAt_budget sa r g i
  unfold len at hi
  unfold act at h
  rcases hp : F.progAct r (F.stAt sa r g i) with _ | ((x | x) | r')
  · rw [hp] at h
    simp only at h
    split_ifs at h with h1 <;> (try simp at h) <;> omega
  · have := F.nq_lt_of_progAct r _ hp
    omega
  · rw [hp] at h
    simp only at h
    split_ifs at h with h1 h2 <;> (try simp at h) <;> omega
  · rw [hp] at h
    simp at h

theorem nq_runAux_le (r : Req) (rs : List Req') {i : ℕ} (hi : i ≤ F.len) :
    (F.runAux ansM H r rs i).1.nq + (F.runAux ansM H r rs i).1.np ≤ F.qR + F.qP := by
  have h := F.stAt_runAux ansM H r rs (le_refl i)
  rw [← h]
  exact F.nq_stAt_le _ r _ i hi

/-- **The query sub-slots of a schedule** are at most `n` per query slot within the budget and
`qR + qP` per relayed request. -/
theorem noneCount_sched_le (es : List (Option Req)) :
    noneCount (F.sched n b Q ansM H es).out ≤
      n * min (es.countP Option.isNone) b + (F.qR + F.qP) * min (es.countP Option.isSome) Q := by
  induction es using List.reverseRecOn with
  | nil => simp [sched, noneCount]
  | append_singleton es e ih =>
    rw [F.sched_append, F.schedStep_out, noneCount_append]
    have hqb := (F.sched_qb_rb n b Q ansM H es).1
    have hrb := (F.sched_qb_rb n b Q ansM H es).2
    rcases e with _ | r
    · simp only [List.countP_append, List.countP_singleton, Option.isNone_none, ↓reduceIte,
        Option.isSome_none, Bool.false_eq_true, add_zero]
      simp only [blockOf, hqb]
      split_ifs with h
      · have : noneCount (List.replicate n ((none, (none, (default, 0))) :
            Option Req' × (Option Resp' × (X × Y)))) = n := by
          simp [noneCount, List.countP_replicate]
        rw [this, show min (es.countP Option.isNone + 1) b = min (es.countP Option.isNone) b + 1 by
          omega]
        nlinarith
      · have : noneCount [F.idleEntry ansM (F.sched n b Q ansM H es).out] = 0 := by
          simp [noneCount, idleEntry]
        rw [this, show min (es.countP Option.isNone + 1) b = min (es.countP Option.isNone) b by
          omega]
        omega
    · simp only [List.countP_append, List.countP_singleton, Option.isNone_some, Bool.false_eq_true,
        ↓reduceIte, Option.isSome_some, add_zero]
      simp only [blockOf, hrb]
      split_ifs with h
      · have h1 : noneCount (F.runEntries ansM H r ((F.sched n b Q ansM H es).out.filterMap
            Prod.fst)) ≤ F.qR + F.qP := by
          rw [runEntries, F.noneCount_runAux]
          exact F.nq_runAux_le ansM H r _ le_rfl
        rw [show min (es.countP Option.isSome + 1) Q = min (es.countP Option.isSome) Q + 1 by omega]
        nlinarith
      · have : noneCount [F.idleEntry ansM (F.sched n b Q ansM H es).out] = 0 := by
          simp [noneCount, idleEntry]
        rw [this, show min (es.countP Option.isSome + 1) Q = min (es.countP Option.isSome) Q by
          omega]
        omega

omit [Inhabited Req'] in
theorem noneCount_tailEntries (out : List (Option Req' × (Option Resp' × (X × Y)))) :
    ∀ k, noneCount (F.tailEntries ansM out k) = noneCount out
  | 0 => rfl
  | k + 1 => by
    rw [tailEntries, noneCount_append, noneCount_tailEntries out k]
    simp [noneCount, idleEntry]

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem noneCount_take_le (l : List (Option Req' × (Option Resp' × (X × Y)))) (k : ℕ) :
    noneCount (l.take k) ≤ noneCount l :=
  (List.take_sublist _ _).countP_le

/-! ### Records read off an entry list -/

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **The record of an entry list** lists its entries. -/
theorem recList_getElem? {m : ℕ} (es : List (Option Req)) (hes : es.length ≤ m) :
    recList (fun i : Fin m => es[(i : ℕ)]?) = es := by
  unfold recList
  have hw : (List.finRange m).takeWhile (fun i : Fin m => (es[(i : ℕ)]?).isSome) =
      (List.finRange m).take es.length := by
    rw [← List.take_append_drop es.length (List.finRange m), List.takeWhile_append_of_pos]
    · rw [List.take_append_drop]
      rcases Nat.lt_or_ge es.length m with h | h
      · rw [List.drop_eq_getElem_cons (by simpa using h), List.takeWhile_cons_of_neg]
        · simp [List.take_append_drop]
        · simp
      · rw [List.drop_eq_nil_of_le (by simpa using h)]
        simp
    · intro i hi
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hi
      simp only [List.length_take, List.length_finRange] at hk
      simp only [List.getElem_take, List.getElem_finRange, Fin.val_cast]
      simp only [Option.isSome_iff_exists]
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  rw [hw]
  refine List.ext_getElem (by simp; omega) fun k h1 h2 => ?_
  simp [List.getElem_take, List.getElem_finRange, List.getElem?_eq_getElem h2]

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
theorem recPrefix_ofList {m : ℕ} {es : List (Option Req)} (hes : es.length ≤ m) {i : ℕ}
    (hi : i ≤ es.length) : recPrefix (fun i' : Fin m => es[(i' : ℕ)]?) i = es.take i := by
  unfold recPrefix
  refine List.ext_getElem (by simp; omega) fun k h1 h2 => ?_
  simp only [List.length_map, List.length_take, List.length_finRange] at h1
  simp [List.getElem_take, List.getElem_finRange, List.getElem?_eq_getElem (show k < es.length by omega)]

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **No slot starts at sub-slot `t`** of a record listing `es` if no block of `es` starts
there. -/
theorem fillAt_ofList_eq_none {m : ℕ} {es : List (Option Req)} (hes : es.length ≤ m) {t : ℕ}
    (h : ∀ i ≤ es.length, i < m → F.startAt n b Q es i ≠ t) :
    F.fillAt n b Q (fun i : Fin m => es[(i : ℕ)]?) t = none := by
  unfold fillAt
  rw [List.find?_eq_none]
  intro i _
  simp only [decide_eq_true_eq, not_and]
  intro hfill
  by_cases hi : (i : ℕ) ≤ es.length
  · rw [recPrefix_ofList hes hi, F.startAt_congr n b Q (es' := es) (by
      rw [List.take_take, Nat.min_self])]
    exact h i hi i.2
  · have := hfill ⟨es.length, by omega⟩ (by simp [Fin.lt_def]; omega)
    simp at this

omit [Inhabited X] [Zero Y] [Zero Ys] [Inhabited Req'] in
/-- **The next slot starts at sub-slot `t`** of a record listing `es` if the blocks of `es` end
at `t`. -/
theorem fillAt_ofList_eq_some (hn : 0 < n) {m : ℕ} {es : List (Option Req)} (hes : es.length < m)
    {t : ℕ} (ht : F.startAt n b Q es es.length = t) :
    F.fillAt n b Q (fun i : Fin m => es[(i : ℕ)]?) t = some ⟨es.length, hes⟩ := by
  unfold fillAt
  rw [List.find?_eq_some_iff_append]
  refine ⟨?_, (List.finRange m).take es.length, (List.finRange m).drop (es.length + 1), ?_, ?_⟩
  · simp only [decide_eq_true_eq]
    refine ⟨fun i' hi' => ?_, ?_⟩
    · simp [Fin.lt_def] at hi'
      simp [List.getElem?_eq_getElem hi']
    · rw [recPrefix_ofList hes.le le_rfl, List.take_length, ht]
  · conv_lhs => rw [← List.take_append_drop es.length (List.finRange m)]
    rw [List.drop_eq_getElem_cons (by simpa using hes)]
    simp
  · intro i hi
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hi
    simp only [List.length_take, List.length_finRange] at hk
    simp only [List.getElem_take, List.getElem_finRange, Fin.cast_mk, decide_eq_true_eq,
      Bool.not_eq_true', decide_eq_false_iff_not, not_and]
    intro _
    rw [recPrefix_ofList hes.le (by omega), F.startAt_congr n b Q (es' := es) (by
      rw [List.take_take, Nat.min_self])]
    have := F.startAt_lt_of_lt n b Q hn es (show k < es.length by omega)
    omega

/-- **The sub-slots before the end of the blocks of `es`** are the schedule of `es`, whatever
entry follows. -/
theorem subEntriesL_append (es : List (Option Req)) (e : Option Req) {t : ℕ}
    (ht : (F.sched n b Q ansM H es).out.length = t) :
    F.subEntriesL n b Q ansM H t (es ++ [e]) = (F.sched n b Q ansM H es).out ∧
      F.subEntriesL n b Q ansM H t es = (F.sched n b Q ansM H es).out := by
  unfold subEntriesL
  constructor
  · rw [F.take_tailEntries_of_le ansM _ t (by rw [F.sched_append, F.schedStep_out]; simp; omega),
      F.sched_append, F.schedStep_out, List.take_append, List.take_of_length_le ht.le]
    simp [ht]
  · rw [F.take_tailEntries_of_le ansM _ t ht.ge, List.take_of_length_le ht.le]

end MultiRelay

namespace MultiRelay

section Adds

variable {X Y Req Resp Req' Resp' Xs Ys : Type} (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys)
  [Inhabited X] [Zero Y] [AddGroup Ys] [Inhabited Req'] (ansM : List Req' → Req' → Option Resp')
  (H : X → Y)

/-- **The side additions after sub-slot `sub - 1`, on a side vector**: the `qS` additions of
`addVec` in order. -/
def addsVec (r : Req) (g : ℕ → Option Resp' × (X × Y)) (sub : ℕ) (v : Fin F.qS → Ys) :
    Fin F.qS → Ys :=
  (List.range F.qS).foldl (fun v i => F.addVec r g sub i true v) v

omit [Zero Y] [Inhabited Req'] in
theorem addsVec_eq (r : Req) (g : ℕ → Option Resp' × (X × Y)) (sub : ℕ) (v : Fin F.qS → Ys) :
    F.addsVec r g sub v = (List.range F.qS).foldl (fun v i => F.addVec r g sub i true v) v :=
  rfl

/-- The state after a sub-slot, before its side reads, from its stored answer. -/
theorem runAux_succ_fst (r : Req) (rs : List Req') (i : ℕ) :
    (F.runAux ansM H r rs (i + 1)).1 = F.close F.sideSa r (F.next r (F.runAux ansM H r rs i).1
      ((F.runAux ansM H r rs (i + 1)).2.getD i (none, (none, (default, 0)))).2) := by
  simp only [runAux, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by rw [F.length_runAux]), F.length_runAux, Nat.sub_self]
  rfl

omit [Zero Y] [Inhabited Req'] in
/-- **One side step adds the side answer to the side vector.** -/
theorem sideVec_sideStep (r : Req) {st : RelaySt Y Resp' Ys} (hinv : SideInv st) {x : Xs}
    (hp : F.progAct r st = some (.inl (.inr x))) (hk : st.ns < F.qS) :
    F.sideVec (F.sideStep F.sideSa r st) = Function.update (F.sideVec st) ⟨_, hk⟩ (F.side x) := by
  unfold SideInv at hinv
  have hs : F.sideStep F.sideSa r st =
      ⟨st.ans ++ [.inl (.inr (F.side x))], st.na, st.nq, st.ns + 1, st.np, st.live⟩ := by
    simp only [sideStep, hp]
    rfl
  rw [hs]
  funext k
  simp only [sideVec, sideVals_append]
  by_cases hk' : k = ⟨_, hk⟩
  · subst hk'
    rw [Function.update_self, getD_append_of_le _ _ _ (show _ ≤ st.ns by omega), hinv,
      Nat.sub_self]
    rfl
  · rw [Function.update_of_ne hk']
    show _ = (sideVals st.ans).getD k 0
    have hne : (k : ℕ) ≠ st.ns := fun e => hk' (Fin.ext e)
    rcases Nat.lt_or_ge (k : ℕ) st.ns with h | h
    · rw [getD_append_of_lt _ _ _ (by omega)]
    · have h1 : (sideVals [(.inl (.inr (F.side x)) : (Y ⊕ Ys) ⊕ Option Resp')]).length = 1 := rfl
      rw [getD_append_of_le _ _ _ (by omega), getD_of_length_le _ _ (by omega),
        getD_of_length_le _ _ (by omega)]

/-- **The side additions after a sub-slot rebuild the side vector** of the run after the sub-slot
and its side reads, from that before them, the stored answers being the run's. -/
theorem addsVec_runAux (r : Req) (rs : List Req') {s₀ J : ℕ} (hJ : s₀ + 1 ≤ J)
    {g : ℕ → Option Resp' × (X × Y)}
    (hg : ∀ k < s₀ + 1, g k = ((F.runAux ansM H r rs J).2.getD k (none, (none, (default, 0)))).2) :
    F.addsVec r g (s₀ + 1) (F.sideVec (F.runAux ansM H r rs s₀).1) =
      F.sideVec (F.runAux ansM H r rs (s₀ + 1)).1 := by
  -- the stored answers of the run after the sub-slot
  have hg' : ∀ k < s₀ + 1,
      g k = ((F.runAux ansM H r rs (s₀ + 1)).2.getD k (none, (none, (default, 0)))).2 :=
    fun k hk => by
      rw [hg k hk, ← F.take_runAux ansM H hJ, List.getD_eq_getElem?_getD,
        List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]
  set u₀ := F.next r (F.runAux ansM H r rs s₀).1 (g s₀) with hu₀
  have hinv₀ : SideInv u₀ := F.sideInv_next r _ (F.sideInv_runAux ansM H r rs s₀)
  have hend : (F.runAux ansM H r rs (s₀ + 1)).1 = (F.sideStep F.sideSa r)^[F.qS] u₀ := by
    rw [F.runAux_succ_fst, ← hg' s₀ (by omega)]
    rfl
  -- the vector after `i` additions is the side vector after `i` side steps
  have key : ∀ i ≤ F.qS, (List.range i).foldl (fun v i => F.addVec r g (s₀ + 1) i true v)
      (F.sideVec (F.runAux ansM H r rs s₀).1) = F.sideVec ((F.sideStep F.sideSa r)^[i] u₀) := by
    intro i
    induction i with
    | zero =>
      intro _
      have ⟨l, hl, hs⟩ := F.next_ans r (F.runAux ansM H r rs s₀).1 (g s₀)
      funext k
      simp only [List.range_zero, List.foldl_nil, Function.iterate_zero, id, sideVec, hu₀, hl,
        sideVals_append, hs, List.append_nil]
    | succ i ih =>
      intro hi
      rw [List.range_succ, List.foldl_append, ih (by omega)]
      simp only [List.foldl_cons, List.foldl_nil]
      set u := (F.sideStep F.sideSa r)^[i] u₀ with hu
      have hinv : SideInv u := F.sideInv_iterate_sideStep _ r i hinv₀
      -- the pending state read from the vector is `u`
      have hpre : F.preSt (F.vecSa (F.sideVec u)) r g (s₀ + 1) = u₀ := by
        simp only [preSt]
        obtain ⟨l, hl⟩ := F.iterate_sideStep_ans F.sideSa r i u₀
        obtain ⟨l', hl', -⟩ := F.next_ans r (F.runAux ansM H r rs s₀).1 (g s₀)
        rw [F.stAt_vecSa_runAux ansM H r rs s₀ (fun k hk => by
          rw [hg' k (by omega), ← F.take_runAux ansM H (Nat.le_succ s₀),
            List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_take_of_lt hk])]
        refine (F.vecAgrees_sideVec u).of_prefix (F.sideInv_runAux ansM H r rs s₀)
          ⟨l' ++ l, by rw [hu, hl, hu₀, hl', List.append_assoc]⟩ ?_
        have := F.ns_le_iterate_sideStep F.sideSa r i u₀
        rw [hu₀, F.ns_next] at this
        exact this
      have hpend : F.pendSt (F.vecSa (F.sideVec u)) r g (s₀ + 1) i = u := by
        unfold pendSt
        rw [hpre]
        exact F.iterate_sideStep_vecSa r i hinv₀ (F.vecAgrees_sideVec u)
      rw [Function.iterate_succ_apply']
      unfold addVec
      rw [hpend]
      rcases hp : F.progAct r u with _ | ((x | x) | r')
      · exact (congrArg F.sideVec (F.sideStep_of_not F.sideSa r u fun x h => by
          rw [hp] at h; cases h)).symm
      · exact (congrArg F.sideVec (F.sideStep_of_not F.sideSa r u fun x h => by
          rw [hp] at h; cases h)).symm
      · have hk := F.ns_lt_of_progAct r u hp
        simp only [hk, ↓reduceDIte, ↓reduceIte]
        rw [F.sideVec_sideStep r hinv hp hk]
        congr 1
        have : F.sideVec u ⟨_, hk⟩ = 0 := by
          have h1 : (sideVals u.ans).length = u.ns := hinv
          show (sideVals u.ans).getD u.ns 0 = 0
          exact getD_of_length_le _ _ (by omega)
        rw [this, zero_add]
      · exact (congrArg F.sideVec (F.sideStep_of_not F.sideSa r u fun x h => by
          rw [hp] at h; cases h)).symm
  rw [addsVec_eq, key F.qS le_rfl, hend]

end Adds

end MultiRelay

namespace Distinguisher

variable {W X Y Req Resp Req' Resp' Xs Ys : Type} [Fintype W] [DecidableEq W] [Fintype X]
  [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Inhabited X] [Inhabited Req'] [AddGroup Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] {n m : ℕ}
  (D : Distinguisher W X Y Req Resp n m) (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (b Q : ℕ)
      (ansM : List Req' → Req' → Option Resp')
  (H : X → Y)

/-! ### The placement of the distinguisher's run -/

/-- The entries of the slots below `j`, read from the logs. -/
def logEntries (j : ℕ) (lg : LogReg Req m) : List (Option Req) :=
  ((List.finRange m).take j).map lg

/-- **The entries of a game basis state at stage `j`** (given by the part `c` beside the query
pairs): its logs below `j` and, for `j < m`, the entry of its registers at slot `j` (its request
if it requests, else `none`). -/
def stEntries (j : ℕ) (c : W × Req × Option Resp × LogReg Req m) : List (Option Req) :=
  logEntries j c.2.2.2 ++ if j < m then [if D.kind c.1 then some c.2.1 else none] else []

/-- The blank entry of a sub-slot: no main request, no reply, the blank pair. -/
def blankEntry : Option Req' × (Option Resp' × (X × Y)) := (none, (none, (default, 0)))

/-- **The entries of the sub-slots before sub-slot `s`** at stage `j`. -/
def subEntries (s j : ℕ) (c : W × Req × Option Resp × LogReg Req m) :
    List (Option Req' × (Option Resp' × (X × Y))) :=
  F.subEntriesL n b Q ansM H s (D.stEntries j c)


/-- **The side vector of block `j` after sub-slot `s`**: for a relayed request, the side answers
of its run after the block's sub-slots before `s`; `0` otherwise. -/
def partSide (s j : ℕ) (c : W × Req × Option Resp × LogReg Req m) : Fin F.qS → Ys :=
  if j < m then
    match MultiRelay.blkAt b Q (D.stEntries j c) j, (D.stEntries j c).getD j none with
    | .rel, some r => F.sideVec (F.runAux ansM H r
        ((F.sched n b Q ansM H ((D.stEntries j c).take j)).out.filterMap Prod.fst)
        (s - F.startAt n b Q (D.stEntries j c) j)).1
    | _, _ => 0
  else 0

/-- **The side store at stage `j` and sub-slot `s`**: the side vectors of the slots below `j`, then
that of block `j`. -/
def subSides (s j : ℕ) (c : W × Req × Option Resp × LogReg Req m) : List (Fin F.qS → Ys) :=
  (F.sched n b Q ansM H ((D.stEntries j c).take j)).side ++ [D.partSide F b Q ansM H s j c]

/-- **The placement** of a game basis state `g` of `D` at stage `j` in the game registers of the
relayed distinguisher at sub-slot `s`, before the set-up of sub-slot `s`: the distinguisher's
registers, the record of the entries, the stored answers, the side store and the main logs of the
sub-slots before `s`, the clock at `s` (capped at `relaySlots n m F`), the blank main registers
and query pair. -/
def place (s j : ℕ) (g : GameReg W n X Y Req Resp m) :
    GameReg (RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F) (Fin F.qS → Ys)) 1
      X Y Req' Resp' (relaySlots n m F) :=
  splitLogs.symm (((⟨(splitLogs g).1, fun i => (D.stEntries j g.1)[(i : ℕ)]?,
      fun t => ((D.subEntries F b Q ansM H s j g.1).getD t blankEntry).2,
      fun i => (D.subSides F b Q ansM H s j g.1).getD i 0,
      ⟨min s (relaySlots n m F), Nat.lt_succ_of_le (min_le_right _ _)⟩⟩, default, none),
      fun _ => (default, 0)),
    fun t => ((D.subEntries F b Q ansM H s j g.1).getD t blankEntry).1)

/-- The first sub-slot of the block of slot `j`. -/
def blkStart (j : ℕ) (c : W × Req × Option Resp × LogReg Req m) : ℕ :=
  F.startAt n b Q (D.stEntries j c) j

/-- The block of slot `j`. -/
def blkKind (j : ℕ) (c : W × Req × Option Resp × LogReg Req m) : MultiRelay.Blk :=
  MultiRelay.blkAt b Q (D.stEntries j c) j

/-- **The basis states at stage `j` whose block contains sub-slot `s`**; for `j = m`, those whose
blocks all end by `s`. -/
def inBlock (s j : ℕ) : Set (GameReg W n X Y Req Resp m) :=
  {g | D.blkStart F b Q j g.1 ≤ s ∧ (j < m → s < D.blkStart F b Q j g.1 + F.blkLen n (D.blkKind b Q j g.1))}

/-- **The queries made so far in a query block**: at stage `j < m`, on a query block, the pairs
numbered below the sub-slot `s - blkStart` are queried to `H`. -/
def partQ (s j : ℕ) : Equiv.Perm (GameReg W n X Y Req Resp m) :=
  Equiv.prodShear (Equiv.refl _) fun c => Equiv.piCongrRight fun i =>
    Equiv.prodShear (Equiv.refl X) fun x => Equiv.addRight
      (if j < m ∧ D.blkKind b Q j c = .qry ∧ (i : ℕ) + D.blkStart F b Q j c < s then H x else 0)

omit [Fintype W] [DecidableEq W] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype
    Req]
  [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req'] [DecidableEq Req']
  [Fintype Resp'] [DecidableEq Resp'] [Inhabited X] [Inhabited Req'] [AddGroup Y] in
theorem length_logEntries {j : ℕ} (hj : j ≤ m) (lg : LogReg Req m) :
    (logEntries j lg).length = j := by
  simp [logEntries, hj]

theorem length_stEntries {j : ℕ} (hj : j ≤ m) (c : W × Req × Option Resp × LogReg Req m) :
    (D.stEntries j c).length = if j < m then j + 1 else j := by
  unfold stEntries
  split_ifs <;> simp [length_logEntries hj]

theorem take_stEntries {j : ℕ} (hj : j ≤ m) (c : W × Req × Option Resp × LogReg Req m) :
    (D.stEntries j c).take j = logEntries j c.2.2.2 := by
  unfold stEntries
  rw [List.take_append_of_le_length (by rw [length_logEntries hj]),
    List.take_of_length_le (by rw [length_logEntries hj])]

theorem stEntries_of_lt {j : ℕ} (hj : j < m) (c : W × Req × Option Resp × LogReg Req m) :
    D.stEntries j c = logEntries j c.2.2.2 ++ [if D.kind c.1 then some c.2.1 else none] := by
  simp [stEntries, hj]

theorem stEntries_self (c : W × Req × Option Resp × LogReg Req m) :
    D.stEntries m c = logEntries m c.2.2.2 := by
  simp [stEntries]

/-- **The scheduled action of sub-slot `s`** at stage `j`: in a query block, the query of the pair
numbered by the sub-slot; in a relayed request, the relay's action after the sub-slots so far; in
an idle block or after the last block, the idle request. -/
def schedAct (s j : ℕ) (c : W × Req × Option Resp × LogReg Req m) : SubAct X Req' n :=
  if j < m then
    match D.blkKind b Q j c, (D.stEntries j c).getD j none with
    | .qry, _ => if h : s - D.blkStart F b Q j c < n then .pair ⟨_, h⟩ else .ask F.idle
    | .rel, some r =>
      match F.act r (F.runAux ansM H r ((F.sched n b Q ansM H ((D.stEntries j c).take j)).out.filterMap
          Prod.fst) (s - D.blkStart F b Q j c)).1 with
      | .inl (.inl x) => .query x
      | .inl (.inr _) => .query default
      | .inr r' => .ask r'
    | _, _ => .ask F.idle
  else .ask F.idle

/-- The entry a sub-slot with the action `a` stores after the entries `pre`: blank for a query of
the distinguisher's pair; the queried pair for a relay query; the main reply for a main
request. -/
def entryOfAct (pre : List (Option Req' × (Option Resp' × (X × Y)))) :
    SubAct X Req' n → Option Req' × (Option Resp' × (X × Y))
  | .pair _ => blankEntry
  | .query x => (none, (none, (x, H x)))
  | .ask r' => (some r', (ansM (pre.filterMap Prod.fst) r', (default, 0)))

/-- **The schedule at stage `j < m`** is the schedule of the slots below `j` and the block of
slot `j`. -/
theorem sched_stEntries {j : ℕ} (hj : j < m) (c : W × Req × Option Resp × LogReg Req m) :
    (F.sched n b Q ansM H (D.stEntries j c)).out =
      (F.sched n b Q ansM H ((D.stEntries j c).take j)).out ++
        F.blockOf n b Q ansM H (F.sched n b Q ansM H ((D.stEntries j c).take j))
          ((D.stEntries j c).getD j none) := by
  have hl := length_logEntries hj.le c.2.2.2
  rw [D.stEntries_of_lt hj, List.take_append_of_le_length hl.ge, List.take_of_length_le hl.le,
    List.getD_eq_getElem?_getD, List.getElem?_append_right hl.le, hl, Nat.sub_self]
  simp only [List.getElem?_cons_zero, Option.getD_some]
  rw [F.sched_append, F.schedStep_out]

/-- **The side store of the schedule at stage `j < m`** is that of the slots below `j` and the
side vector of slot `j`. -/
theorem sched_stEntries_side {j : ℕ} (hj : j < m) (c : W × Req × Option Resp × LogReg Req m) :
    (F.sched n b Q ansM H (D.stEntries j c)).side =
      (F.sched n b Q ansM H ((D.stEntries j c).take j)).side ++
        [F.sideOf b Q ansM H (F.sched n b Q ansM H ((D.stEntries j c).take j))
          ((D.stEntries j c).getD j none)] := by
  have hl := length_logEntries hj.le c.2.2.2
  rw [D.stEntries_of_lt hj, List.take_append_of_le_length hl.ge, List.take_of_length_le hl.le,
    List.getD_eq_getElem?_getD, List.getElem?_append_right hl.le, hl, Nat.sub_self]
  simp only [List.getElem?_cons_zero, Option.getD_some]
  rw [F.sched_append, F.schedStep_side]

/-- The schedule of the slots below `j` ends at the first sub-slot of block `j`. -/
theorem length_sched_take {j : ℕ} (hj : j ≤ m) (c : W × Req × Option Resp × LogReg Req m) :
    (F.sched n b Q ansM H ((D.stEntries j c).take j)).out.length = D.blkStart F b Q j c := by
  rw [F.length_sched, blkStart]
  have hl : ((D.stEntries j c).take j).length = j := by
    rw [D.take_stEntries hj, length_logEntries hj]
  rw [hl]
  exact F.startAt_congr n b Q (by rw [List.take_take, Nat.min_self])

/-- The block of slot `j < m` read from the counts of the schedule before it. -/
theorem blkKind_eq {j : ℕ} (hj : j < m) (c : W × Req × Option Resp × LogReg Req m) :
    D.blkKind b Q j c = MultiRelay.blk b Q (F.sched n b Q ansM H ((D.stEntries j c).take j)).qb
      (F.sched n b Q ansM H ((D.stEntries j c).take j)).rb ((D.stEntries j c).getD j none) := by
  rw [(F.sched_qb_rb n b Q ansM H _).1, (F.sched_qb_rb n b Q ansM H _).2]
  rfl

/-- The schedule at stage `j` has its blocks up to block `j`. -/
theorem length_sched_stEntries {j : ℕ} (hj : j < m) (c : W × Req × Option Resp × LogReg Req m) :
    (F.sched n b Q ansM H (D.stEntries j c)).out.length =
      D.blkStart F b Q j c + F.blkLen n (D.blkKind b Q j c) := by
  rw [D.sched_stEntries F b Q ansM H hj, List.length_append, D.length_sched_take F b Q ansM H hj.le,
    F.length_blockOf, D.blkKind_eq F b Q ansM H hj]

/-- **The side store at the end of block `j`** is the schedule's at stage `j`. -/
theorem subSides_end {s j : ℕ} (hj : j < m) (c : W × Req × Option Resp × LogReg Req m)
    (hend : s = D.blkStart F b Q j c + F.blkLen n (D.blkKind b Q j c)) :
    D.subSides F b Q ansM H s j c = (F.sched n b Q ansM H (D.stEntries j c)).side := by
  rw [D.sched_stEntries_side F b Q ansM H hj c]
  unfold subSides
  congr 2
  have hblk := D.blkKind_eq F b Q ansM H hj c
  unfold partSide
  simp only [hj, ↓reduceIte]
  have hk' : MultiRelay.blkAt b Q (D.stEntries j c) j = D.blkKind b Q j c := rfl
  rw [hk']
  rcases he : (D.stEntries j c).getD j none with _ | r
  · rw [he] at hblk
    rcases D.blkKind b Q j c with _ | _ | _ <;>
      first | rfl | (simp [MultiRelay.blk] at hblk; split_ifs at hblk)
  · rw [he] at hblk
    simp only [MultiRelay.sideOf]
    by_cases hrb : (F.sched n b Q ansM H ((D.stEntries j c).take j)).rb < Q
    · have hk : D.blkKind b Q j c = .rel := by simp [hblk, MultiRelay.blk, hrb]
      rw [hk] at hend ⊢
      simp only [hrb, ↓reduceIte, MultiRelay.runSide, MultiRelay.blkLen] at hend ⊢
      have : s - F.startAt n b Q (D.stEntries j c) j = F.len := by
        unfold blkStart at hend
        omega
      rw [this]
    · have hk : D.blkKind b Q j c = .idle := by simp [hblk, MultiRelay.blk, hrb]
      rw [hk]
      simp [hrb]

/-- **The side store at the start of block `j`** is the schedule's of the slots below `j`. -/
theorem subSides_start {s j : ℕ} (hj : j ≤ m) (c : W × Req × Option Resp × LogReg Req m)
    (hs : D.blkStart F b Q j c = s) :
    (fun i : Fin m => (D.subSides F b Q ansM H s j c).getD i 0) =
      fun i : Fin m => (F.sched n b Q ansM H (logEntries j c.2.2.2)).side.getD i 0 := by
  have hpart : D.partSide F b Q ansM H s j c = 0 := by
    unfold partSide
    split_ifs with hjm
    · split
      · rename_i r _ _
        have h0 : s - F.startAt n b Q (D.stEntries j c) j = 0 := by
          unfold blkStart at hs
          omega
        rw [h0]
        funext k
        rfl
      · rfl
    · rfl
  funext i
  unfold subSides
  rw [hpart, D.take_stEntries hj]
  have hl : (F.sched n b Q ansM H (logEntries j c.2.2.2)).side.length = j := by
    rw [F.length_sched_side, length_logEntries hj]
  rcases Nat.lt_or_ge (i : ℕ) j with h | h
  · rw [MultiRelay.getD_append_of_lt _ _ _ (by omega)]
  · rw [MultiRelay.getD_append_of_le _ _ _ (by omega),
      MultiRelay.getD_of_length_le (F.sched n b Q ansM H (logEntries j c.2.2.2)).side 0
        (by omega)]
    rw [hl]
    rcases Nat.eq_zero_or_pos ((i : ℕ) - j) with h' | h'
    · rw [h']
      rfl
    · exact MultiRelay.getD_of_length_le _ _ (by simp; omega)

/-- **The record of a placement lists the entries.** -/
theorem recList_place {j : ℕ} (hj : j ≤ m) (c : W × Req × Option Resp × LogReg Req m) :
    MultiRelay.recList (fun i : Fin m => (D.stEntries j c)[(i : ℕ)]?) = D.stEntries j c :=
  MultiRelay.recList_getElem? _ (by rw [D.length_stEntries hj]; split_ifs <;> omega)

/-- **The side vector of block `j` in a placement** is the block's partial side vector. -/
theorem vecAt_place {s j : ℕ} (hj : j < m) (c : W × Req × Option Resp × LogReg Req m) :
    F.vecAt (fun i : Fin m => (D.subSides F b Q ansM H s j c).getD i 0) j =
      D.partSide F b Q ansM H s j c := by
  have hl : (F.sched n b Q ansM H ((D.stEntries j c).take j)).side.length = j := by
    rw [F.length_sched_side, D.take_stEntries hj.le, length_logEntries hj.le]
  simp only [MultiRelay.vecAt, hj, ↓reduceDIte, subSides]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_of_eq hl), hl, Nat.sub_self]
  rfl

/-- **The relay's state read from the stored answers and the side store of a placement** at
sub-slot `s'` after `k` sub-slots of a relayed request is the relay's own state after `k`
sub-slots. -/
theorem stAt_place_store {s' j k : ℕ} (hj : j < m) (c : W × Req × Option Resp × LogReg Req m)
    {r : Req} (hk : D.blkKind b Q j c = .rel) (he : (D.stEntries j c).getD j none = some r)
    (hs' : s' ≤ D.blkStart F b Q j c + F.len) (hks : D.blkStart F b Q j c + k ≤ s') :
    F.stAt (F.vecSa (F.vecAt (fun i : Fin m => (D.subSides F b Q ansM H s' j c).getD i 0) j)) r
      (fun k' => MultiRelay.storeAt (fun t : Fin (relaySlots n m F) =>
        ((D.subEntries F b Q ansM H s' j c).getD t blankEntry).2) (D.blkStart F b Q j c + k')) k =
      (F.runAux ansM H r ((F.sched n b Q ansM H ((D.stEntries j c).take j)).out.filterMap
        Prod.fst) k).1 := by
  have hblk := D.blkKind_eq F b Q ansM H hj c
  rw [hk, he] at hblk
  have hrb : (F.sched n b Q ansM H ((D.stEntries j c).take j)).rb < Q := by
    by_contra hc
    simp [MultiRelay.blk, hc] at hblk
  have hout := D.sched_stEntries F b Q ansM H hj c
  rw [he] at hout
  simp only [MultiRelay.blockOf, hrb, ↓reduceIte] at hout
  have hlen := D.length_sched_take F b Q ansM H hj.le c
  have hS : D.blkStart F b Q j c + F.len ≤ relaySlots n m F := by
    have := F.startAt_le n b Q (D.stEntries j c) (j + 1)
    rw [F.startAt_succ] at this
    unfold blkStart
    have h2 : (j + 1) * max n F.len ≤ m * max n F.len := Nat.mul_le_mul_right _ (by omega)
    have h3 : MultiRelay.blkAt b Q (D.stEntries j c) j = .rel := hk
    rw [h3] at this
    exact le_trans this h2
  have hpart : D.partSide F b Q ansM H s' j c = F.sideVec (F.runAux ansM H r
      ((F.sched n b Q ansM H ((D.stEntries j c).take j)).out.filterMap Prod.fst)
      (s' - D.blkStart F b Q j c)).1 := by
    have hk' : MultiRelay.blkAt b Q (D.stEntries j c) j = .rel := hk
    simp only [partSide, hj, ↓reduceIte, hk', he]
    rfl
  rw [D.vecAt_place F b Q ansM H hj c, hpart]
  set rs := (F.sched n b Q ansM H ((D.stEntries j c).take j)).out.filterMap Prod.fst
  refine F.stAt_vecSa_runAux ansM H r rs k (fun k' hk' => ?_) ?_
  · unfold MultiRelay.storeAt
    rw [dif_pos (by omega)]
    simp only [subEntries, MultiRelay.subEntriesL, List.getD_eq_getElem?_getD]
    have hlo : D.blkStart F b Q j c + k' < (F.sched n b Q ansM H (D.stEntries j c)).out.length := by
      rw [hout, List.length_append, hlen]
      simp [MultiRelay.runEntries, F.length_runAux]
      omega
    rw [List.getElem?_take_of_lt (by omega), F.getElem?_tailEntries_of_lt ansM _ s' hlo, hout,
      List.getElem?_append_right (by omega), hlen, Nat.add_sub_cancel_left,
      MultiRelay.runEntries, ← F.take_runAux ansM H (show k ≤ F.len by omega),
      List.getElem?_take_of_lt hk']
    rfl
  · exact (F.vecAgrees_sideVec _).of_prefix (F.sideInv_runAux ansM H r rs k)
      (F.runAux_ans_le ansM H r rs (show k ≤ s' - D.blkStart F b Q j c by omega))
      (F.ns_runAux_le ansM H r rs (show k ≤ s' - D.blkStart F b Q j c by omega))

/-- **The action at sub-slot `s` of a placement is the scheduled action.** -/
theorem actAt_place {s j : ℕ} (hj : j ≤ m) (hs : s ≤ relaySlots n m F)
    (c : W × Req × Option Resp × LogReg Req m) (h0 : D.blkStart F b Q j c ≤ s)
    (h1 : j < m → s < D.blkStart F b Q j c + F.blkLen n (D.blkKind b Q j c)) :
    F.actAt n b Q (fun i : Fin m => (D.stEntries j c)[(i : ℕ)]?)
      (fun t : Fin (relaySlots n m F) => ((D.subEntries F b Q ansM H s j c).getD t blankEntry).2)
      (fun i : Fin m => (D.subSides F b Q ansM H s j c).getD i 0)
      s = D.schedAct F b Q ansM H s j c := by
  have hrec := D.recList_place hj c
  unfold MultiRelay.actAt MultiRelay.curBlk schedAct
  rw [hrec, D.length_stEntries hj]
  by_cases hjm : j < m
  · have h1' := h1 hjm
    simp only [hjm, ↓reduceIte, Nat.add_sub_cancel]
    rw [ite_cond_eq_true _ _ (eq_true ⟨Nat.succ_pos _, h0, h1'⟩)]
    simp only
    change (match D.blkKind b Q j c, (D.stEntries j c).getD j none with
      | .qry, _ => if h : s - D.blkStart F b Q j c < n then SubAct.pair ⟨_, h⟩ else .ask F.idle
      | .rel, some r => match F.act r (F.stAt (F.vecSa (F.vecAt
          (fun i : Fin m => (D.subSides F b Q ansM H s j c).getD i 0) j)) r
          (fun k => MultiRelay.storeAt
          (fun t : Fin (relaySlots n m F) => ((D.subEntries F b Q ansM H s j c).getD t blankEntry).2)
          (D.blkStart F b Q j c + k)) (s - D.blkStart F b Q j c)) with
        | .inl (.inl x) => .query x
        | .inl (.inr _) => .query default
        | .inr r' => .ask r'
      | _, _ => .ask F.idle) = _
    rcases hk : D.blkKind b Q j c with _ | _ | _ <;>
      rcases he : (D.stEntries j c).getD j none with _ | r <;> simp only
    -- the relayed request: the stored answers are those of the relay
    have hL : F.blkLen n MultiRelay.Blk.rel = F.len := rfl
    rw [hk, hL] at h1'
    rw [D.stAt_place_store F b Q ansM H hjm c hk he (by omega) (by omega)]
  · simp only [hjm, ↓reduceIte]
    have hm : j = m := by omega
    subst hm
    rw [if_neg]
    rintro ⟨hpos, -, hlt⟩
    have h2 := F.startAt_succ n b Q (D.stEntries j c) (j - 1)
    rw [Nat.sub_add_cancel hpos] at h2
    rw [← h2] at hlt
    exact absurd h0 (not_le.2 hlt)

/-- **Sub-slot `s` appends the entry of its scheduled action** to the entries before it. -/
theorem subEntries_succ {s j : ℕ} (hj : j ≤ m) (c : W × Req × Option Resp × LogReg Req m)
    (h0 : D.blkStart F b Q j c ≤ s)
    (h1 : j < m → s < D.blkStart F b Q j c + F.blkLen n (D.blkKind b Q j c)) :
    D.subEntries F b Q ansM H (s + 1) j c = D.subEntries F b Q ansM H s j c ++
      [entryOfAct ansM H (D.subEntries F b Q ansM H s j c) (D.schedAct F b Q ansM H s j c)] := by
  set out := (F.sched n b Q ansM H (D.stEntries j c)).out with hout_def
  unfold subEntries MultiRelay.subEntriesL
  rw [← hout_def, F.take_succ_tailEntries ansM out s]
  congr 2
  rcases Nat.lt_or_ge s out.length with hso | hso
  · -- inside the schedule: block `j`, with `j < m`
    have hjm : j < m := by
      by_contra hjm
      have hm : j = m := by omega
      subst hm
      have hl := F.length_sched n b Q ansM H (D.stEntries j c)
      rw [D.length_stEntries hj, if_neg (lt_irrefl _)] at hl
      have : out.length = D.blkStart F b Q j c := hl
      omega
    have hout := D.sched_stEntries F b Q ansM H hjm c
    have hlen := D.length_sched_take F b Q ansM H hj c
    have hpre : (F.tailEntries ansM out s).take s =
        (F.sched n b Q ansM H ((D.stEntries j c).take j)).out ++
          (F.blockOf n b Q ansM H (F.sched n b Q ansM H ((D.stEntries j c).take j))
            ((D.stEntries j c).getD j none)).take (s - D.blkStart F b Q j c) := by
      rw [F.take_tailEntries_of_le ansM out s hso.le, hout_def, hout,
        List.take_append, List.take_of_length_le (by rw [hlen]; omega), hlen]
    rw [hpre, F.getElem?_tailEntries_of_lt ansM out _ hso, hout_def, hout,
      List.getElem?_append_right (by omega), hlen]
    have hblk := D.blkKind_eq F b Q ansM H hjm c
    have h1' := h1 hjm
    unfold schedAct
    simp only [hjm, ↓reduceIte]
    set st := F.sched n b Q ansM H ((D.stEntries j c).take j) with hst_def
    rcases hk : D.blkKind b Q j c with _ | _ | _ <;> rw [hk] at hblk h1' <;>
      rcases he : (D.stEntries j c).getD j none with _ | r <;> (try rw [he] at hblk)
    · -- a query block within the budget
      have hq : st.qb < b := by
        by_contra hc
        simp [MultiRelay.blk, hc] at hblk
      have hsub : s - D.blkStart F b Q j c < n := by
        simp only [MultiRelay.blkLen] at h1'
        omega
      simp only [MultiRelay.blockOf, hq, ↓reduceIte, hsub, ↓reduceDIte]
      rw [List.getElem?_replicate_of_lt hsub]
      rfl
    · simp [MultiRelay.blk] at hblk
      split_ifs at hblk
    · -- an idle query block
      have hq : ¬ st.qb < b := by
        intro hc
        simp [MultiRelay.blk, hc] at hblk
      have hsub : s - D.blkStart F b Q j c = 0 := by
        simp only [MultiRelay.blkLen] at h1'
        omega
      simp only [MultiRelay.blockOf, hq, ↓reduceIte, hsub, List.take_zero, List.append_nil]
      rfl
    · -- an idle request (after the `Q`-th)
      have hq : ¬ st.rb < Q := by
        intro hc
        simp [MultiRelay.blk, hc] at hblk
      have hsub : s - D.blkStart F b Q j c = 0 := by
        simp only [MultiRelay.blkLen] at h1'
        omega
      simp only [MultiRelay.blockOf, hq, ↓reduceIte, hsub, List.take_zero, List.append_nil]
      rfl
    · simp [MultiRelay.blk] at hblk
      split_ifs at hblk
    · -- a relayed request
      have hq : st.rb < Q := by
        by_contra hc
        simp [MultiRelay.blk, hc] at hblk
      have hsub : s - D.blkStart F b Q j c < F.len := by
        simp only [MultiRelay.blkLen] at h1'
        omega
      simp only [MultiRelay.blockOf, hq, ↓reduceIte, MultiRelay.runEntries]
      set k := s - D.blkStart F b Q j c
      rw [F.take_runAux ansM H hsub.le, ← List.getElem?_take_of_lt (Nat.lt_succ_self k),
        F.take_runAux ansM H (Nat.succ_le_of_lt hsub), MultiRelay.runAux]
      simp only
      rw [List.getElem?_append_right (by rw [F.length_runAux]), F.length_runAux, Nat.sub_self]
      simp only [List.getElem?_cons_zero, Option.getD_some]
      rcases F.act r (F.runAux ansM H r (st.out.filterMap Prod.fst) k).1 with (x | x) | r'
      · rfl
      · rfl
      · simp [entryOfAct, List.filterMap_append]
  · -- after the schedule: trailing idle sub-slots, at stage `m`
    have hjm : ¬ j < m := by
      intro hjm
      have h2 : out.length = D.blkStart F b Q j c + F.blkLen n (D.blkKind b Q j c) :=
        D.length_sched_stEntries F b Q ansM H hjm c
      have := h1 hjm
      omega
    rw [F.getElem?_tailEntries_of_le ansM out (s + 1) hso (by omega)]
    simp only [Option.getD_some, schedAct, hjm, ↓reduceIte]
    rw [MultiRelay.tailEntries, List.take_append_of_le_length
      (by rw [F.length_tailEntries]; omega)]
    rfl

/-! ### One sub-slot -/

/-- **The pair query of a sub-slot**: on the basis states whose scheduled action at sub-slot `s`
queries the distinguisher's pair `i`, that pair is queried to `H`. -/
def qstep (s j : ℕ) : Equiv.Perm (GameReg W n X Y Req Resp m) :=
  Equiv.prodShear (Equiv.refl _) fun c => Equiv.piCongrRight fun i =>
    Equiv.prodShear (Equiv.refl X) fun x => Equiv.addRight
      (if (D.schedAct F b Q ansM H s j c).pairIdx = some i then H x else 0)

end Distinguisher

/-- **A permutation of the distinguisher's registers on the game registers**, the identity on the
logs. -/
def liftL {W X Y Req A : Type} {n m : ℕ} (π : Equiv.Perm (DReg W n X Y Req A)) :
    Equiv.Perm (GameReg W n X Y Req A m) :=
  (splitLogs (W := W) (n := n) (X := X) (Y := Y) (Req := Req) (A := A) (m := m)).symm.permCongr
    (π.prodCongr (Equiv.refl _))

theorem liftL_apply {W X Y Req A : Type} {n m : ℕ} (π : Equiv.Perm (DReg W n X Y Req A))
    (r : GameReg W n X Y Req A m) :
    liftL π r = splitLogs.symm (π (splitLogs r).1, (splitLogs r).2) :=
  rfl

theorem liftL_trans {W X Y Req A : Type} {n m : ℕ} (π π' : Equiv.Perm (DReg W n X Y Req A)) :
    liftL (m := m) (π.trans π') = (liftL π).trans (liftL π') :=
  Equiv.ext fun _ => rfl

/-- **A log-controlled basis permutation that does not read the logs** is the lifted
permutation. -/
theorem logControlled_permOp {W X Y Req A : Type} [Fintype W] [Fintype X] [Fintype Y]
    [Fintype Req] [Fintype A] {n m : ℕ} (π : Equiv.Perm (DReg W n X Y Req A))
    (v : QState (GameReg W n X Y Req A m)) :
    logControlled (fun _ => permOp π) v = permOp (liftL π) v := by
  ext r
  rw [logControlled_apply, permOp_apply, permOp_apply]
  rfl

/-- **The requests before sub-slot `s`** of logs read from a list of entries. -/
theorem requestsBefore_ofList {Req' B : Type} {S : ℕ} (l : List (Option Req' × B)) (dflt : Option Req' × B)
    (hd : dflt.1 = none) : ∀ s ≤ S, requestsBefore (fun t : Fin S => (l.getD t dflt).1) s =
      (l.take s).filterMap Prod.fst
  | 0, _ => rfl
  | s + 1, hs => by
    rw [requestsBefore_succ_of_lt _ (by omega), requestsBefore_ofList l dflt hd s (by omega)]
    rcases Nat.lt_or_ge s l.length with h | h
    · rw [List.take_succ, List.getElem?_eq_getElem h, List.filterMap_append]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some,
        Option.toList_some, List.filterMap_cons, List.filterMap_nil]
      cases l[s].1 <;> rfl
    · simp [List.take_of_length_le h, List.take_of_length_le (show l.length ≤ s + 1 by omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_none h, hd]

namespace Distinguisher

variable {W X Y Req Resp Req' Resp' Xs Ys : Type} [Fintype W] [DecidableEq W] [Fintype X]
  [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Inhabited X] [Inhabited Req'] [AddGroup Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] {n m : ℕ}
  (D : Distinguisher W X Y Req Resp n m) (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (b Q : ℕ)
      (H : X → Y)
  {Ω' St' : Type} {Q' : ℕ} [OracleState St' X Y] (E' : Env Ω' Req' Resp' X Y Q' St') (ω' : Ω')

/-- **A game basis state of the relayed distinguisher from its parts**: the distinguisher's
registers `d`, the record, the stored answers, the clock, the main request and response registers,
the query pair and the main logs. -/
def mkR (d : DReg W n X Y Req Resp) (rec : Fin m → Option (Option Req))
    (store : Fin (relaySlots n m F) → Option Resp' × (X × Y))
    (side : Fin m → Fin F.qS → Ys) (t : Fin (relaySlots n m F + 1))
    (rq' : Req') (rs' : Option Resp') (pr : X × Y) (lg' : LogReg Req' (relaySlots n m F)) :
    GameReg (RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F) (Fin F.qS → Ys)) 1 X
        Y Req' Resp'
      (relaySlots n m F) :=
  splitLogs.symm (((⟨d, rec, store, side, t⟩, rq', rs'), fun _ => pr), lg')

variable {F} in
theorem liftL_setup_pair {d : DReg W n X Y Req Resp} {rec : Fin m → Option (Option Req)}
    {store : Fin (relaySlots n m F) → Option Resp' × (X × Y)}
    {side : Fin m → Fin F.qS → Ys} {t : Fin (relaySlots n m F + 1)}
    {i : Fin n} (h : F.actAt n b Q rec store side t = .pair i) (rq' : Req') (rs' : Option Resp')
    (pr : X × Y) (lg' : LogReg Req' (relaySlots n m F)) :
    liftL (setupPerm F b Q) (mkR F d rec store side t rq' rs' pr lg') =
      mkR F (d.1, Function.update d.2 i pr) rec store side t rq' rs' (d.2 i) lg' := by
  simp only [mkR, liftL_apply, Equiv.apply_symm_apply]
  change splitLogs.symm (setupFun F b Q _, lg') = _
  simp only [setupFun, h]

variable {F} in
theorem liftL_setup_query {d : DReg W n X Y Req Resp} {rec : Fin m → Option (Option Req)}
    {store : Fin (relaySlots n m F) → Option Resp' × (X × Y)}
    {side : Fin m → Fin F.qS → Ys} {t : Fin (relaySlots n m F + 1)}
    {x : X} (h : F.actAt n b Q rec store side t = .query x) (rq' : Req') (rs' : Option Resp')
    (pr : X × Y) (lg' : LogReg Req' (relaySlots n m F)) :
    liftL (setupPerm F b Q) (mkR F d rec store side t rq' rs' pr lg') =
      mkR F d rec store side t rq' rs' (Equiv.swap default x pr.1, pr.2) lg' := by
  simp only [mkR, liftL_apply, Equiv.apply_symm_apply]
  change splitLogs.symm (setupFun F b Q _, lg') = _
  simp only [setupFun, h]

variable {F} in
theorem liftL_setup_ask {d : DReg W n X Y Req Resp} {rec : Fin m → Option (Option Req)}
    {store : Fin (relaySlots n m F) → Option Resp' × (X × Y)}
    {side : Fin m → Fin F.qS → Ys} {t : Fin (relaySlots n m F + 1)}
    {r' : Req'} (h : F.actAt n b Q rec store side t = .ask r') (rq' : Req') (rs' : Option Resp')
    (pr : X × Y) (lg' : LogReg Req' (relaySlots n m F)) :
    liftL (setupPerm F b Q) (mkR F d rec store side t rq' rs' pr lg') =
      mkR F d rec store side t (Equiv.swap default r' rq') rs' pr lg' := by
  simp only [mkR, liftL_apply, Equiv.apply_symm_apply]
  change splitLogs.symm (setupFun F b Q _, lg') = _
  simp only [setupFun, h]

variable {F} in
theorem liftL_teardown_pair {d : DReg W n X Y Req Resp} {rec : Fin m → Option (Option Req)}
    {store : Fin (relaySlots n m F) → Option Resp' × (X × Y)}
    {side : Fin m → Fin F.qS → Ys} {t : Fin (relaySlots n m F + 1)}
    {i : Fin n} (h : F.actAt n b Q rec store side t = .pair i) (rq' : Req') (rs' : Option Resp')
    (pr : X × Y) (lg' : LogReg Req' (relaySlots n m F)) :
    liftL (teardownPerm F b Q) (mkR F d rec store side t rq' rs' pr lg') =
      mkR F (d.1, Function.update d.2 i pr) rec store side t rq' rs' (d.2 i) lg' := by
  simp only [mkR, liftL_apply, Equiv.apply_symm_apply]
  change splitLogs.symm (teardownFun F b Q _, lg') = _
  simp only [teardownFun, h]

variable {F} in
theorem liftL_teardown_query {d : DReg W n X Y Req Resp} {rec : Fin m → Option (Option Req)}
    {store : Fin (relaySlots n m F) → Option Resp' × (X × Y)}
    {side : Fin m → Fin F.qS → Ys} {t : Fin (relaySlots n m F + 1)}
    {x : X} (h : F.actAt n b Q rec store side t = .query x) (ht : (t : ℕ) < relaySlots n m F)
    (rq' : Req') (rs' : Option Resp') (pr : X × Y) (lg' : LogReg Req' (relaySlots n m F)) :
    liftL (teardownPerm F b Q) (mkR F d rec store side t rq' rs' pr lg') =
      mkR F d rec (Function.update store ⟨t, ht⟩ ((store ⟨t, ht⟩).1, pr)) side t rq' rs'
        (store ⟨t, ht⟩).2 lg' := by
  simp only [mkR, liftL_apply, Equiv.apply_symm_apply]
  change splitLogs.symm (teardownFun F b Q _, lg') = _
  simp only [teardownFun, h, ht, ↓reduceDIte]

variable {F} in
theorem liftL_teardown_ask {d : DReg W n X Y Req Resp} {rec : Fin m → Option (Option Req)}
    {store : Fin (relaySlots n m F) → Option Resp' × (X × Y)}
    {side : Fin m → Fin F.qS → Ys} {t : Fin (relaySlots n m F + 1)}
    {r' : Req'} (h : F.actAt n b Q rec store side t = .ask r') (ht : (t : ℕ) < relaySlots n m F)
    (rq' : Req') (rs' : Option Resp') (pr : X × Y) (lg' : LogReg Req' (relaySlots n m F)) :
    liftL (teardownPerm F b Q) (mkR F d rec store side t rq' rs' pr lg') =
      mkR F d rec (Function.update store ⟨t, ht⟩ (rs', (store ⟨t, ht⟩).2)) side t
        (Equiv.swap default r' rq') (store ⟨t, ht⟩).1 pr lg' := by
  simp only [mkR, liftL_apply, Equiv.apply_symm_apply]
  change splitLogs.symm (teardownFun F b Q _, lg') = _
  simp only [teardownFun, h, ht, ↓reduceDIte]

theorem liftL_tick (d : DReg W n X Y Req Resp) (rec : Fin m → Option (Option Req))
    (store : Fin (relaySlots n m F) → Option Resp' × (X × Y))
    (side : Fin m → Fin F.qS → Ys) (t : Fin (relaySlots n m F + 1))
    (rq' : Req') (rs' : Option Resp') (pr : X × Y) (lg' : LogReg Req' (relaySlots n m F)) :
    liftL (tickPerm F) (mkR F d rec store side t rq' rs' pr lg') =
      mkR F d rec store side (finRotate _ t) rq' rs' pr lg' :=
  rfl

/-- **The side vector of the current block after the side additions**: the block's vector with the
additions of `addsVec` when the last started slot is a relayed request after a sub-slot of its
block; the side store unchanged otherwise. -/
def sideAfter (rec : Fin m → Option (Option Req))
    (store : Fin (relaySlots n m F) → Option Resp' × (X × Y)) (side : Fin m → Fin F.qS → Ys)
    (t : ℕ) : Fin m → Fin F.qS → Ys :=
  match F.curRel n b Q rec t with
  | some (j, r, sub) =>
    if hj : j < m then
      Function.update side ⟨j, hj⟩ (F.addsVec r (fun k => MultiRelay.storeAt store
        (F.startAt n b Q (MultiRelay.recList rec) j + k)) sub (side ⟨j, hj⟩))
    else side
  | none => side

omit [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req]
  [Fintype Resp] [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] [Fintype Ys]
  [DecidableEq Ys] in
/-- **Composed side additions apply in order.** -/
theorem foldl_sideAddPerm_apply (L : List ℕ) :
    ∀ (P : Equiv.Perm (RelayReg W X Y Req Resp Req' Resp' n m (relaySlots n m F)
      (Fin F.qS → Ys))) (d : RelayReg W X Y Req Resp Req' Resp' n m (relaySlots n m F)
      (Fin F.qS → Ys)), (L.foldl (fun P i => P.trans (sideAddPerm F b Q i)) P) d =
      L.foldl (fun x i => sideAddFun F b Q i true x) (P d) := by
  induction L with
  | nil => intro P d; rfl
  | cons i L ih =>
    intro P d
    rw [List.foldl_cons, ih]
    rfl

omit [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req]
  [Fintype Resp] [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] [Fintype Ys]
  [DecidableEq Ys] in
theorem foldl_sideAddFun (L : List ℕ) :
    ∀ d : RelayReg W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys), L.foldl (fun x
        i => sideAddFun F b Q i true x) d =
      ((⟨d.1.1.inner, d.1.1.record, d.1.1.store,
        match F.curRel n b Q d.1.1.record d.1.1.time with
        | some (j, r, sub) =>
          if hj : j < m then
            Function.update d.1.1.side ⟨j, hj⟩ (L.foldl (fun v i => F.addVec r
              (fun k => MultiRelay.storeAt d.1.1.store
                (F.startAt n b Q (MultiRelay.recList d.1.1.record) j + k)) sub i true v)
              (d.1.1.side ⟨j, hj⟩))
          else d.1.1.side
        | none => d.1.1.side, d.1.1.time⟩, d.1.2.1, d.1.2.2), d.2) := by
  induction L with
  | nil =>
    intro d
    obtain ⟨⟨⟨inn, rec, store, side, t⟩, rq, rs⟩, pr⟩ := d
    simp only [List.foldl_nil]
    split
    · split_ifs <;> simp
    · rfl
  | cons i L ih =>
    intro d
    obtain ⟨⟨⟨inn, rec, store, side, t⟩, rq, rs⟩, pr⟩ := d
    rw [List.foldl_cons, ih]
    rcases hc : F.curRel n b Q rec t with _ | ⟨j, r, sub⟩
    · simp only [sideAddFun, hc]
    · by_cases hj : j < m
      · simp only [sideAddFun, hc, hj, ↓reduceDIte, List.foldl_cons, Function.update_self,
          Function.update_idem]
      · simp only [sideAddFun, hc, hj, ↓reduceDIte]

omit [Fintype W] [DecidableEq W] [Fintype X] [Fintype Y] [DecidableEq Y] [Fintype Req]
  [Fintype Resp] [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] [Fintype Ys]
  [DecidableEq Ys] in
/-- **The side additions** on the relayed registers: the current block's side vector after its
additions (`addsVec`), everything else kept. -/
theorem sideAddsPerm_apply (d : RelayReg W X Y Req Resp Req' Resp' n m (relaySlots n m F)
    (Fin F.qS → Ys)) :
    sideAddsPerm F b Q d = ((⟨d.1.1.inner, d.1.1.record, d.1.1.store,
        match F.curRel n b Q d.1.1.record d.1.1.time with
        | some (j, r, sub) =>
          if hj : j < m then
            Function.update d.1.1.side ⟨j, hj⟩ (F.addsVec r
              (fun k => MultiRelay.storeAt d.1.1.store
                (F.startAt n b Q (MultiRelay.recList d.1.1.record) j + k)) sub
              (d.1.1.side ⟨j, hj⟩))
          else d.1.1.side
        | none => d.1.1.side, d.1.1.time⟩, d.1.2.1, d.1.2.2), d.2) := by
  rw [sideAddsPerm, foldl_sideAddPerm_apply, Equiv.refl_apply, foldl_sideAddFun]
  rfl

/-- **The side additions** write the current block's side vector after them (`sideAfter`). -/
theorem liftL_sideAdds (d : DReg W n X Y Req Resp) (rec : Fin m → Option (Option Req))
    (store : Fin (relaySlots n m F) → Option Resp' × (X × Y))
    (side : Fin m → Fin F.qS → Ys) (t : Fin (relaySlots n m F + 1))
    (rq' : Req') (rs' : Option Resp') (pr : X × Y) (lg' : LogReg Req' (relaySlots n m F)) :
    liftL (sideAddsPerm F b Q) (mkR F d rec store side t rq' rs' pr lg') =
      mkR F d rec store (sideAfter F b Q rec store side t) t rq' rs' pr lg' := by
  simp only [mkR, liftL_apply, Equiv.apply_symm_apply]
  change splitLogs.symm ((sideAddsPerm F b Q) _, lg') = _
  rw [sideAddsPerm, foldl_sideAddPerm_apply, Equiv.refl_apply, foldl_sideAddFun]
  rfl

/-- The kind of the relayed distinguisher reads the action of the sub-slot at the clock. -/
theorem relay_kind (w : RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F) (Fin F.qS
    → Ys)) :
    (D.relay F b Q).kind w = (F.actAt n b Q w.record w.store w.side w.time).isAsk :=
  rfl

/-- **A sub-slot of the main environment on a query branch**: the query pair is queried to the
oracle in force. -/
theorem eventPerm_relay_query {d : DReg W n X Y Req Resp} {rec : Fin m → Option (Option Req)}
    {store : Fin (relaySlots n m F) → Option Resp' × (X × Y)}
    {side : Fin m → Fin F.qS → Ys} {t : Fin (relaySlots n m F + 1)}
    (h : (F.actAt n b Q rec store side t).isAsk = false) {s : ℕ} (hs : s < relaySlots n m F)
    (rq' : Req') (rs' : Option Resp') (pr : X × Y) (lg' : LogReg Req' (relaySlots n m F)) :
    (D.relay F b Q).eventPerm E' ω' s (mkR F d rec store side t rq' rs' pr lg') =
      mkR F d rec store side t rq' rs' (pr.1, pr.2 + E'.oracle ω' lg' pr.1) lg' := by
  simp only [eventPerm, hs, ↓reduceDIte, Equiv.trans_apply, Env.requestPerm, Env.oraclePerm, mkR]
  simp [Equiv.prodCongr_apply, copyPerm_apply, respondPerm_apply, relay_kind, h, splitLogs]

/-- **A sub-slot of the main environment on a request branch**: the main request is logged and
answered. -/
theorem eventPerm_relay_ask {d : DReg W n X Y Req Resp} {rec : Fin m → Option (Option Req)}
    {store : Fin (relaySlots n m F) → Option Resp' × (X × Y)}
    {side : Fin m → Fin F.qS → Ys} {t : Fin (relaySlots n m F + 1)}
    (h : (F.actAt n b Q rec store side t).isAsk = true) {s : ℕ} (hs : s < relaySlots n m F)
    (rq' : Req') (rs' : Option Resp') (pr : X × Y) (lg' : LogReg Req' (relaySlots n m F)) :
    (D.relay F b Q).eventPerm E' ω' s (mkR F d rec store side t rq' rs' pr lg') =
      mkR F d rec store side t rq'
        (Equiv.swap none (E'.answer ω' (Function.update lg' ⟨s, hs⟩
          (Equiv.swap none (some rq') (lg' ⟨s, hs⟩))) ⟨s, hs⟩) rs') (pr.1, pr.2 + 0)
        (Function.update lg' ⟨s, hs⟩ (Equiv.swap none (some rq') (lg' ⟨s, hs⟩))) := by
  simp only [eventPerm, hs, ↓reduceDIte, Equiv.trans_apply, Env.requestPerm, Env.oraclePerm, mkR]
  simp [Equiv.prodCongr_apply, copyPerm_apply, respondPerm_apply, relay_kind, h, splitLogs]

theorem length_subEntries (ansM : List Req' → Req' → Option Resp') (s j : ℕ)
    (c : W × Req × Option Resp × LogReg Req m) : (D.subEntries F b Q ansM H s j c).length = s := by
  simp [subEntries, MultiRelay.subEntriesL, F.length_tailEntries]

theorem place_eq_mkR (ansM : List Req' → Req' → Option Resp') (s j : ℕ)
    (g : GameReg W n X Y Req Resp m) :
    D.place F b Q ansM H s j g = mkR F (splitLogs g).1 (fun i => (D.stEntries j g.1)[(i : ℕ)]?)
      (fun t => ((D.subEntries F b Q ansM H s j g.1).getD t blankEntry).2)
      (fun i => (D.subSides F b Q ansM H s j g.1).getD i 0)
      ⟨min s (relaySlots n m F), Nat.lt_succ_of_le (min_le_right _ _)⟩ default none (default, 0)
      (fun t => ((D.subEntries F b Q ansM H s j g.1).getD t blankEntry).1) :=
  rfl

omit [Fintype W] [DecidableEq W] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype
    Req]
  [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req'] [DecidableEq Req']
  [Fintype Resp'] [DecidableEq Resp'] [Inhabited X] [Inhabited Req'] [AddGroup Y] in
theorem getD_append_singleton {α : Type} {L : List α} {s : ℕ} (hL : L.length = s) (e d : α) (t : ℕ) :
    (L ++ [e]).getD t d = if t = s then e else L.getD t d := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with ht
  · subst ht
    rw [← hL, List.getElem?_append_right le_rfl, Nat.sub_self]
    rfl
  · rcases Nat.lt_or_ge t s with h | h
    · rw [List.getElem?_append_left (by omega)]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem mkR_congr {d d' : DReg W n X Y Req Resp} {rec rec' : Fin m → Option (Option Req)}
    {store store' : Fin (relaySlots n m F) → Option Resp' × (X × Y)}
    {side side' : Fin m → Fin F.qS → Ys}
    {t t' : Fin (relaySlots n m F + 1)} {rq rq' : Req'} {rs rs' : Option Resp'} {pr pr' : X × Y}
    {lg lg' : LogReg Req' (relaySlots n m F)} (hd : d = d') (hrec : rec = rec')
    (hst : store = store') (hsd : side = side') (ht : t = t') (hrq : rq = rq') (hrs : rs = rs')
    (hpr : pr = pr') (hlg : lg = lg') :
    mkR F d rec store side t rq rs pr lg = mkR F d' rec' store' side' t' rq' rs' pr' lg' := by
  subst hd hrec hst hsd ht hrq hrs hpr hlg
  rfl

variable {F} in
theorem liftL_finalize_of_ne {d : DReg W n X Y Req Resp} {rec : Fin m → Option (Option Req)}
    {store : Fin (relaySlots n m F) → Option Resp' × (X × Y)}
    {side : Fin m → Fin F.qS → Ys} {t : Fin (relaySlots n m F + 1)}
    (h : F.startAt n b Q (MultiRelay.recList rec) (MultiRelay.recList rec).length ≠ t)
    (rq' : Req') (rs' : Option Resp') (pr : X × Y) (lg' : LogReg Req' (relaySlots n m F)) :
    liftL (finalizePerm F b Q) (mkR F d rec store side t rq' rs' pr lg') =
      mkR F d rec store side t rq' rs' pr lg' := by
  simp only [mkR, liftL_apply, Equiv.apply_symm_apply]
  change splitLogs.symm (finalizeFun F b Q _, lg') = _
  simp only [finalizeFun, h, ↓reduceIte]

variable {F} in
theorem liftL_finalize_of_none {d : DReg W n X Y Req Resp} {rec : Fin m → Option (Option Req)}
    {store : Fin (relaySlots n m F) → Option Resp' × (X × Y)}
    {side : Fin m → Fin F.qS → Ys} {t : Fin (relaySlots n m F + 1)}
    (ho : F.lastReply n b Q rec store side = none)
    (rq' : Req') (rs' : Option Resp') (pr : X × Y) (lg' : LogReg Req' (relaySlots n m F)) :
    liftL (finalizePerm F b Q) (mkR F d rec store side t rq' rs' pr lg') =
      mkR F d rec store side t rq' rs' pr lg' := by
  simp only [mkR, liftL_apply, Equiv.apply_symm_apply]
  change splitLogs.symm (finalizeFun F b Q _, lg') = _
  simp only [finalizeFun, ho]
  split_ifs <;> rfl

variable {F} in
theorem liftL_finalize_of_some {d : DReg W n X Y Req Resp} {rec : Fin m → Option (Option Req)}
    {store : Fin (relaySlots n m F) → Option Resp' × (X × Y)}
    {side : Fin m → Fin F.qS → Ys} {t : Fin (relaySlots n m F + 1)}
    (h : F.startAt n b Q (MultiRelay.recList rec) (MultiRelay.recList rec).length = t)
    {o : Option Resp} (ho : F.lastReply n b Q rec store side = some o)
    (rq' : Req') (rs' : Option Resp') (pr : X × Y) (lg' : LogReg Req' (relaySlots n m F)) :
    liftL (finalizePerm F b Q) (mkR F d rec store side t rq' rs' pr lg') =
      mkR F ((d.1.1, d.1.2.1, Equiv.swap none o d.1.2.2), d.2) rec store side t rq' rs' pr lg' := by
  simp only [mkR, liftL_apply, Equiv.apply_symm_apply]
  change splitLogs.symm (finalizeFun F b Q _, lg') = _
  simp only [finalizeFun, h, ho, ↓reduceIte]

variable {F} in
theorem liftL_record_of_none (kind : W → Bool) {d : DReg W n X Y Req Resp}
    {rec : Fin m → Option (Option Req)} {store : Fin (relaySlots n m F) → Option Resp' × (X × Y)}
    {side : Fin m → Fin F.qS → Ys} {t : Fin (relaySlots n m F + 1)} (h : F.fillAt n
        b Q rec t = none)
    (rq' : Req') (rs' : Option Resp') (pr : X × Y) (lg' : LogReg Req' (relaySlots n m F)) :
    liftL (recordPerm F b Q kind) (mkR F d rec store side t rq' rs' pr lg') =
      mkR F d rec store side t rq' rs' pr lg' := by
  simp only [mkR, liftL_apply, Equiv.apply_symm_apply]
  change splitLogs.symm (recordFun F b Q kind _, lg') = _
  simp only [recordFun, h]

variable {F} in
theorem liftL_record_of_some (kind : W → Bool) {d : DReg W n X Y Req Resp}
    {rec : Fin m → Option (Option Req)} {store : Fin (relaySlots n m F) → Option Resp' × (X × Y)}
    {side : Fin m → Fin F.qS → Ys} {t : Fin (relaySlots n m F + 1)} {i : Fin m} (h :
        F.fillAt n b Q rec t = some i)
    (rq' : Req') (rs' : Option Resp') (pr : X × Y) (lg' : LogReg Req' (relaySlots n m F)) :
    liftL (recordPerm F b Q kind) (mkR F d rec store side t rq' rs' pr lg') =
      mkR F d (Function.update rec i (Equiv.swap none (some (entryOf kind d)) (rec i))) store side t
      rq'
        rs' pr lg' := by
  simp only [mkR, liftL_apply, Equiv.apply_symm_apply]
  change splitLogs.symm (recordFun F b Q kind _, lg') = _
  simp only [recordFun, h]

/-! ### The distinguisher's step on pushed vectors -/

/-- Whether the distinguisher's step applies on the rest of the relayed registers: the blocks of
the started slots end at the clock. -/
def ctrlCond (rest : RelayRest X Y Req Req' Resp' m (relaySlots n m F) (Fin F.qS → Ys)) : Prop :=
  F.startAt n b Q (MultiRelay.recList rest.1) (MultiRelay.recList rest.1).length = (rest.2.2.2.1 :
      ℕ)

/-- **The distinguisher's step is the identity where it does not apply**: on vectors pushed along
`f` from a support on whose images the step does not apply. -/
theorem logControlled_ctrlStep_pushV_of_not {S : Set (GameReg W n X Y Req Resp m)}
    {v : QState (GameReg W n X Y Req Resp m)} (hv : Supported S v)
    {f : GameReg W n X Y Req Resp m → GameReg (RelayW (DReg W n X Y Req Resp) Req Resp' X Y m
      (relaySlots n m F) (Fin F.qS → Ys)) 1 X Y Req' Resp' (relaySlots n m F)}
    (hf : ∀ g ∈ S, ¬ ctrlCond F b Q (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F)
        (Fin F.qS → Ys)
      (splitLogs (f g)).1).2) :
    logControlled (fun _ => D.ctrlStep F b Q) (pushV f v) = pushV f v := by
  classical
  have h0 : ∀ r', ctrlCond F b Q (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin
      F.qS → Ys)
      (splitLogs r').1).2 → pushV f v r' = 0 := by
    intro r' hr'
    rw [pushV_apply]
    refine Finset.sum_eq_zero fun g hg => ?_
    have hfg : f g = r' := (Finset.mem_filter.1 hg).2
    by_cases hgS : g ∈ S
    · exact absurd (hfg ▸ hr') (hf g hgS)
    · exact hv g hgS
  ext r'
  rw [logControlled_apply]
  simp only [ctrlStep, LinearIsometryEquiv.trans_apply]
  set split := relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)
  rw [relabel_symm, relabel_apply, Equiv.symm_symm, controlled_apply]
  by_cases hc : ctrlCond F b Q (split (splitLogs r').1).2
  · have hz : (WithLp.toLp 2 fun i => relabel split (WithLp.toLp 2 fun d =>
        pushV f v (splitLogs.symm (d, (splitLogs r').2))) (i, (split (splitLogs r').1).2) :
        QState (DReg W n X Y Req Resp)) = 0 := by
      ext i
      simp only [relabel_apply, WithLp.ofLp_toLp]
      refine h0 _ ?_
      simp only [Equiv.apply_symm_apply]
      exact hc
    rw [hz, map_zero, h0 r' hc]
    rfl
  · have hc' : ¬ (F.startAt n b Q (MultiRelay.recList (split (splitLogs r').1).2.1)
        (MultiRelay.recList (split (splitLogs r').1).2.1).length =
          ((split (splitLogs r').1).2.2.2.2.1 : ℕ)) := hc
    rw [if_neg hc']
    simp only [LinearIsometryEquiv.coe_refl, id, relabel_apply, Equiv.symm_apply_apply, Prod.mk.eta]

/-- **A placement that keeps the distinguisher's registers and reads the rest from the logs.** -/
def placeOfLogs (ρ : LogReg Req m → RelayRest X Y Req Req' Resp' m (relaySlots n m F) (Fin F.qS →
    Ys))
    (lam : LogReg Req m → LogReg Req' (relaySlots n m F)) (g : GameReg W n X Y Req Resp m) :
    GameReg (RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F) (Fin F.qS → Ys)) 1 X
        Y Req' Resp'
      (relaySlots n m F) :=
  splitLogs.symm ((relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)).symm
    ((splitLogs g).1, ρ (splitLogs g).2), lam (splitLogs g).2)

theorem pushV_placeOfLogs_apply
    (ρ : LogReg Req m → RelayRest X Y Req Req' Resp' m (relaySlots n m F) (Fin F.qS → Ys))
    (lam : LogReg Req m → LogReg Req' (relaySlots n m F)) (w : QState (GameReg W n X Y Req Resp m))
    (i : DReg W n X Y Req Resp) (rest : RelayRest X Y Req Req' Resp' m (relaySlots n m F) (Fin F.qS
        → Ys))
    (lg' : LogReg Req' (relaySlots n m F)) :
    pushV (placeOfLogs F ρ lam) w (splitLogs.symm ((relaySplit W X Y Req Resp Req' Resp' n m
      (relaySlots n m F) (Fin F.qS → Ys)).symm (i, rest), lg')) =
      ∑ lg ∈ univ.filter (fun lg => ρ lg = rest ∧ lam lg = lg'), w (splitLogs.symm (i, lg)) := by
  classical
  rw [pushV_apply]
  refine Finset.sum_bij' (fun g _ => (splitLogs g).2) (fun lg _ => splitLogs.symm (i, lg))
    ?_ ?_ ?_ ?_ ?_
  · intro g hg
    have h := (Finset.mem_filter.1 hg).2
    unfold placeOfLogs at h
    have h' := congrArg splitLogs h
    simp only [Equiv.apply_symm_apply, Prod.mk.injEq] at h'
    have h'' := congrArg (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS →
        Ys)) h'.1
    simp only [Equiv.apply_symm_apply, Prod.mk.injEq] at h''
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h''.2, h'.2⟩
  · intro lg hlg
    have h := (Finset.mem_filter.1 hlg).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    simp only [placeOfLogs, Equiv.apply_symm_apply, h.1, h.2]
  · intro g hg
    have h := (Finset.mem_filter.1 hg).2
    unfold placeOfLogs at h
    have h' := congrArg splitLogs h
    simp only [Equiv.apply_symm_apply, Prod.mk.injEq] at h'
    have h'' := congrArg (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS →
        Ys)) h'.1
    simp only [Equiv.apply_symm_apply, Prod.mk.injEq] at h''
    rw [← h''.1, Prod.mk.eta, Equiv.symm_apply_apply]
  · intro lg _
    simp
  · intro g hg
    have h := (Finset.mem_filter.1 hg).2
    unfold placeOfLogs at h
    have h' := congrArg splitLogs h
    simp only [Equiv.apply_symm_apply, Prod.mk.injEq] at h'
    have h'' := congrArg (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS →
        Ys)) h'.1
    simp only [Equiv.apply_symm_apply, Prod.mk.injEq] at h''
    rw [← h''.1, Prod.mk.eta, Equiv.symm_apply_apply]

/-- **The distinguisher's step where it applies**: on vectors supported on logs in `L`, pushed
along a placement that keeps the distinguisher's registers and reads the rest from the logs, if
at every log in `L` the step applies with `k` started slots, the controlled step is the
distinguisher's step `k`. -/
theorem logControlled_ctrlStep_pushV {L : Set (LogReg Req m)}
    {v : QState (GameReg W n X Y Req Resp m)} (hv : Supported (logsIn L) v) {k : ℕ}
    (ρ : LogReg Req m → RelayRest X Y Req Req' Resp' m (relaySlots n m F) (Fin F.qS → Ys))
    (lam : LogReg Req m → LogReg Req' (relaySlots n m F))
    (hρ : ∀ lg ∈ L, ctrlCond F b Q (ρ lg) ∧ (MultiRelay.recList (ρ lg).1).length = k) :
    logControlled (fun _ => D.ctrlStep F b Q) (pushV (placeOfLogs F ρ lam) v) =
      pushV (placeOfLogs F ρ lam) (D.liftedStep k v) := by
  classical
  set split := relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)
  ext r'
  obtain ⟨d', lg', rfl⟩ : ∃ d' lg', r' = splitLogs.symm (d', lg') :=
    ⟨(splitLogs r').1, (splitLogs r').2, by simp⟩
  obtain ⟨i, rest, rfl⟩ : ∃ i rest, d' = split.symm (i, rest) := ⟨(split d').1, (split d').2, by simp⟩
  rw [logControlled_apply]
  simp only [Equiv.apply_symm_apply, ctrlStep, LinearIsometryEquiv.trans_apply, relabel_symm,
    relabel_apply, Equiv.symm_symm]
  rw [Equiv.apply_symm_apply, controlled_apply]
  have hvec : (WithLp.toLp 2 fun i' => (relabel split (WithLp.toLp 2 fun d =>
      pushV (placeOfLogs F ρ lam) v (splitLogs.symm (d, lg')))) (i', rest) :
        QState (DReg W n X Y Req Resp)) =
      ∑ lg ∈ univ.filter (fun lg => ρ lg = rest ∧ lam lg = lg'),
        WithLp.toLp 2 fun i' => v (splitLogs.symm (i', lg)) := by
    ext i'
    simp only [relabel_apply, WithLp.ofLp_toLp]
    rw [pushV_placeOfLogs_apply, WithLp.ofLp_sum, Finset.sum_apply]
  rw [hvec, pushV_placeOfLogs_apply]
  simp only [Distinguisher.liftedStep, logControlled_apply, Equiv.apply_symm_apply]
  by_cases hex : ∃ lg ∈ univ.filter (fun lg => ρ lg = rest ∧ lam lg = lg'), lg ∈ L
  · obtain ⟨lg0, hlg0, hL0⟩ := hex
    have h0 := (Finset.mem_filter.1 hlg0).2
    obtain ⟨hc, hk⟩ := hρ lg0 hL0
    rw [h0.1] at hc hk
    have hc' : F.startAt n b Q (MultiRelay.recList rest.1) (MultiRelay.recList rest.1).length =
        (rest.2.2.2.1 : ℕ) := hc
    rw [if_pos hc', hk, map_sum, WithLp.ofLp_sum, Finset.sum_apply]
  · simp only [not_exists, not_and] at hex
    have hz : ∀ lg ∈ univ.filter (fun lg => ρ lg = rest ∧ lam lg = lg'),
        (WithLp.toLp 2 fun i' => v (splitLogs.symm (i', lg)) : QState (DReg W n X Y Req Resp)) = 0 :=
      fun lg hlg => hv.slice_eq_zero (hex lg hlg)
    rw [Finset.sum_eq_zero hz, map_zero]
    refine (Finset.sum_eq_zero fun lg hlg => ?_).symm
    rw [hz lg hlg, map_zero]
    rfl

/-- **The placement after a sub-slot's tear-down and clock, before its side additions**: as the
placement at sub-slot `s + 1`, with the side store of sub-slot `s`. -/
def prePlace (ansM : List Req' → Req' → Option Resp') (s j : ℕ)
    (g : GameReg W n X Y Req Resp m) :
    GameReg (RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F) (Fin F.qS → Ys)) 1
      X Y Req' Resp' (relaySlots n m F) :=
  mkR F (splitLogs g).1 (fun i => (D.stEntries j g.1)[(i : ℕ)]?)
    (fun t => ((D.subEntries F b Q ansM H (s + 1) j g.1).getD t blankEntry).2)
    (fun i => (D.subSides F b Q ansM H s j g.1).getD i 0)
    ⟨min (s + 1) (relaySlots n m F), Nat.lt_succ_of_le (min_le_right _ _)⟩ default none (default, 0)
    (fun t => ((D.subEntries F b Q ansM H (s + 1) j g.1).getD t blankEntry).1)

/-- **One sub-slot of the relayed distinguisher on a placement, before its side additions**: the
set-up, the main environment's slot, the tear-down and the clock take the placement at sub-slot
`s` to `prePlace` at `s` of the basis state with the scheduled pair query made. -/
theorem oneSub_pre (hO' : ∀ lg' : LogReg Req' (relaySlots n m F), E'.oracle ω' lg' = H)
    {s j : ℕ} (hj : j ≤ m) (hs : s < relaySlots n m F) (g : GameReg W n X Y Req Resp m)
    (h0 : D.blkStart F b Q j g.1 ≤ s)
    (h1 : j < m → s < D.blkStart F b Q j g.1 + F.blkLen n (D.blkKind b Q j g.1)) :
    liftL (tickPerm F) (liftL (teardownPerm F b Q) ((D.relay F b Q).eventPerm E' ω' s
      (liftL (setupPerm F b Q) (D.place F b Q (E'.answerAfter ω') H s j g)))) =
    D.prePlace F b Q H (E'.answerAfter ω') s j (D.qstep F b Q (E'.answerAfter ω') H s j g) := by
  have htime : min s (relaySlots n m F) = s := min_eq_left hs.le
  have hact := D.actAt_place F b Q (E'.answerAfter ω') H hj hs.le g.1 h0 h1
  have hsub := D.subEntries_succ F b Q (E'.answerAfter ω') H hj g.1 h0 h1
  obtain ⟨⟨w, rq, rs, lg⟩, ps⟩ := g
  simp only at h0 h1 hact hsub
  have hact' : ∀ a, D.schedAct F b Q (E'.answerAfter ω') H s j (w, rq, rs, lg) = a →
      F.actAt n b Q (fun i : Fin m => (D.stEntries j (w, rq, rs, lg))[(i : ℕ)]?)
        (fun t : Fin (relaySlots n m F) =>
          ((D.subEntries F b Q (E'.answerAfter ω') H s j (w, rq, rs, lg)).getD t blankEntry).2)
        (fun i : Fin m => (D.subSides F b Q (E'.answerAfter ω') H s j (w, rq, rs, lg)).getD i 0)
        (min s (relaySlots n m F)) = a := fun a ha => by rw [htime, hact, ha]
  set L := D.subEntries F b Q (E'.answerAfter ω') H s j (w, rq, rs, lg) with hL_def
  have hL : L.length = s := D.length_subEntries F b Q H _ s j _
  have hLs : L.getD s blankEntry = blankEntry := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl
  have ht : ((⟨min s (relaySlots n m F), Nat.lt_succ_of_le (min_le_right _ _)⟩ :
      Fin (relaySlots n m F + 1)) : ℕ) < relaySlots n m F := by simp only; omega
  have htick : finRotate (relaySlots n m F + 1)
      ⟨min s (relaySlots n m F), Nat.lt_succ_of_le (min_le_right _ _)⟩ =
      ⟨min (s + 1) (relaySlots n m F), Nat.lt_succ_of_le (min_le_right _ _)⟩ := by
    ext
    rw [coe_finRotate_of_ne_last (by simp [Fin.ext_iff]; omega)]
    simp only
    omega
  rw [D.place_eq_mkR, prePlace]
  have hq : (D.qstep F b Q (E'.answerAfter ω') H s j ((w, rq, rs, lg), ps)).1 = (w, rq, rs, lg) := rfl
  rw [hq]
  have hlogL : ∀ e : Option Req' × (Option Resp' × (X × Y)), e.1 = none →
      (fun t : Fin (relaySlots n m F) => ((L ++ [e]).getD t blankEntry).1) =
        fun t : Fin (relaySlots n m F) => (L.getD t blankEntry).1 := fun e he => funext fun t => by
    rw [getD_append_singleton hL]
    split_ifs with hts
    · rw [hts, hLs, he]
      rfl
    · rfl
  have hps0 : ∀ a : SubAct X Req' n, a.pairIdx = none →
      D.schedAct F b Q (E'.answerAfter ω') H s j (w, rq, rs, lg) = a →
      (splitLogs (D.qstep F b Q (E'.answerAfter ω') H s j ((w, rq, rs, lg), ps))).1 =
        (splitLogs ((w, rq, rs, lg), ps)).1 := fun a hp ha =>
    Prod.ext rfl (funext fun i' => by simp [splitLogs, qstep, ha, hp])
  rcases ha : D.schedAct F b Q (E'.answerAfter ω') H s j (w, rq, rs, lg) with i | x | r'
  · -- a query of the distinguisher's pair `i`
    have h2 := hact' _ ha
    rw [liftL_setup_pair b Q h2, D.eventPerm_relay_query F b Q E' ω' (by rw [h2]; rfl) hs,
      liftL_teardown_pair b Q h2, liftL_tick, htick, hO', hsub, ha]
    simp only [entryOfAct]
    refine mkR_congr F ?_ rfl ?_ rfl rfl rfl rfl (by simp) (hlogL blankEntry rfl).symm
    · refine Prod.ext rfl (funext fun i' => ?_)
      simp only [splitLogs, Equiv.coe_fn_mk, qstep, Equiv.prodShear_apply, Equiv.coe_refl, id,
        Equiv.piCongrRight_apply, Equiv.coe_addRight, ha, SubAct.pairIdx, Option.some.injEq]
      by_cases hi : i' = i
      · subst hi
        simp
      · simp [Function.update_of_ne hi, Ne.symm hi]
    · funext t
      rw [getD_append_singleton hL]
      split_ifs with hts
      · rw [hts, hLs]
      · rfl
  · -- a query of the relay
    have h2 := hact' _ ha
    rw [liftL_setup_query b Q h2, D.eventPerm_relay_query F b Q E' ω' (by rw [h2]; rfl) hs,
      liftL_teardown_query b Q h2 ht, liftL_tick, htick, hO', hsub, ha, hps0 _ rfl ha]
    simp only [entryOfAct, Equiv.swap_apply_left]
    have hst0 : (L.getD (min s (relaySlots n m F)) blankEntry) = blankEntry := by rw [htime, hLs]
    refine mkR_congr F rfl rfl ?_ rfl rfl rfl rfl (by simp only [hst0]; rfl)
      (hlogL (none, (none, (x, H x))) rfl).symm
    funext t
    rw [getD_append_singleton hL]
    split_ifs with hts
    · have : t = ⟨min s (relaySlots n m F), ht⟩ := Fin.ext (by simp only; omega)
      rw [this, Function.update_self, hst0]
      simp [blankEntry]
    · rw [Function.update_of_ne (fun e => hts (by rw [e]; simp only; omega))]
  · -- a main request
    have h2 := hact' _ ha
    rw [liftL_setup_ask b Q h2, D.eventPerm_relay_ask F b Q E' ω' (by rw [h2]; rfl) hs,
      liftL_teardown_ask b Q h2 ht, liftL_tick, htick, hsub, ha, hps0 _ rfl ha]
    simp only [entryOfAct, Equiv.swap_apply_left, Equiv.swap_apply_right]
    have hst0 : (L.getD (min s (relaySlots n m F)) blankEntry) = blankEntry := by rw [htime, hLs]
    have hlog0 : (L.getD s blankEntry).1 = none := by rw [hLs]; rfl
    have hans : E'.answer ω' (Function.update (fun t : Fin (relaySlots n m F) =>
        (L.getD t blankEntry).1) ⟨s, hs⟩ (Equiv.swap none (some r')
          ((L.getD s blankEntry).1))) ⟨s, hs⟩ = E'.answerAfter ω' (L.filterMap Prod.fst) r' := by
      rw [hlog0, Equiv.swap_apply_left]
      simp only [Env.answer, Function.update_self, Option.elim_some]
      congr 1
      rw [requestsBefore_congr (lg' := fun t : Fin (relaySlots n m F) => (L.getD t blankEntry).1)
        fun k hk => Function.update_of_ne (fun e => by simp [Fin.ext_iff] at e; omega) _ _,
        requestsBefore_ofList L blankEntry rfl s hs.le, List.take_of_length_le hL.le]
    refine mkR_congr F rfl rfl ?_ rfl rfl rfl (by simp only [hst0]; rfl) (by simp) ?_
    · funext t
      rw [getD_append_singleton hL]
      split_ifs with hts
      · have : t = ⟨min s (relaySlots n m F), ht⟩ := Fin.ext (by simp only; omega)
        rw [this, Function.update_self, hst0]
        refine Prod.ext ?_ rfl
        exact hans
      · rw [Function.update_of_ne (fun e => hts (by rw [e]; simp only; omega))]
    · funext t
      rw [getD_append_singleton hL]
      split_ifs with hts
      · have : t = ⟨s, hs⟩ := Fin.ext hts
        rw [this, Function.update_self, hlog0, Equiv.swap_apply_left]
      · rw [Function.update_of_ne (fun e => hts (by rw [e]))]

/-- **The relayed request at the clock after sub-slot `s` of a placement**: block `j`'s, with
`s + 1 - blkStart` of its sub-slots done, when it is a relayed request. -/
theorem curRel_place {s j : ℕ} (hj : j ≤ m) (c : W × Req × Option Resp × LogReg Req m)
    (h0 : D.blkStart F b Q j c ≤ s)
    (h1 : j < m → s < D.blkStart F b Q j c + F.blkLen n (D.blkKind b Q j c)) :
    F.curRel n b Q (fun i : Fin m => (D.stEntries j c)[(i : ℕ)]?) (s + 1) =
      if j < m then
        match D.blkKind b Q j c, (D.stEntries j c).getD j none with
        | .rel, some r => some (j, r, s + 1 - D.blkStart F b Q j c)
        | _, _ => none
      else none := by
  have hrec := D.recList_place hj c
  unfold MultiRelay.curRel
  rw [hrec, D.length_stEntries hj]
  by_cases hjm : j < m
  · have h1' := h1 hjm
    simp only [hjm, ↓reduceIte, Nat.succ_pos, Nat.add_sub_cancel]
    change (match D.blkKind b Q j c, (D.stEntries j c).getD j none with
      | .rel, some r => if D.blkStart F b Q j c < s + 1 ∧ s + 1 ≤ D.blkStart F b Q j c + F.len
          then some (j, r, s + 1 - D.blkStart F b Q j c) else none
      | _, _ => none) = _
    rcases hk : D.blkKind b Q j c with _ | _ | _ <;>
      rcases he : (D.stEntries j c).getD j none with _ | r <;> simp only
    rw [hk] at h1'
    rw [if_pos ⟨by omega, by simp only [MultiRelay.blkLen] at h1'; omega⟩]
  · simp only [hjm, ↓reduceIte]
    have hm : j = m := by omega
    subst hm
    by_cases hpos : 0 < j
    · simp only [hpos, ↓reduceIte]
      have h2 := F.startAt_succ n b Q (D.stEntries j c) (j - 1)
      rw [Nat.sub_add_cancel hpos] at h2
      have h0' : F.startAt n b Q (D.stEntries j c) j ≤ s := h0
      rcases hb : MultiRelay.blkAt b Q (D.stEntries j c) (j - 1) with _ | _ | _ <;>
        rcases (D.stEntries j c).getD (j - 1) none with _ | r <;> simp only
      rw [if_neg]
      rintro ⟨-, hle⟩
      rw [h2, hb] at h0'
      simp only [MultiRelay.blkLen] at h0'
      omega
    · simp [hpos]

/-- **The side additions after sub-slot `s` of a placement** write the side vector of block `j`
after the sub-slot: `prePlace`'s side store becomes the placement's at `s + 1`. -/
theorem sideAfter_place (ansM : List Req' → Req' → Option Resp') {s j : ℕ} (hj : j ≤ m)
    (hs : s < relaySlots n m F) (c : W × Req × Option Resp × LogReg Req m)
    (h0 : D.blkStart F b Q j c ≤ s)
    (h1 : j < m → s < D.blkStart F b Q j c + F.blkLen n (D.blkKind b Q j c)) :
    sideAfter F b Q (fun i : Fin m => (D.stEntries j c)[(i : ℕ)]?)
      (fun t : Fin (relaySlots n m F) =>
        ((D.subEntries F b Q ansM H (s + 1) j c).getD t blankEntry).2)
      (fun i : Fin m => (D.subSides F b Q ansM H s j c).getD i 0) (s + 1) =
      fun i : Fin m => (D.subSides F b Q ansM H (s + 1) j c).getD i 0 := by
  have hcur := D.curRel_place F b Q hj c h0 h1
  have hpre : ∀ s', (D.subSides F b Q ansM H s' j c) =
      (F.sched n b Q ansM H ((D.stEntries j c).take j)).side ++ [D.partSide F b Q ansM H s' j c] :=
    fun _ => rfl
  -- the side stores at `s` and `s + 1` differ at most at block `j`
  have hother : ∀ i : Fin m, (i : ℕ) ≠ j →
      (D.subSides F b Q ansM H s j c).getD i 0 = (D.subSides F b Q ansM H (s + 1) j c).getD i 0 :=
    fun i hi => by
      rw [hpre, hpre]
      rcases Nat.lt_or_ge (i : ℕ) (F.sched n b Q ansM H ((D.stEntries j c).take j)).side.length
        with h | h
      · rw [MultiRelay.getD_append_of_lt _ _ _ h, MultiRelay.getD_append_of_lt _ _ _ h]
      · rw [MultiRelay.getD_append_of_le _ _ _ h, MultiRelay.getD_append_of_le _ _ _ h]
        have hl : (F.sched n b Q ansM H ((D.stEntries j c).take j)).side.length = j := by
          rw [F.length_sched_side, D.take_stEntries hj, length_logEntries hj]
        rw [MultiRelay.getD_of_length_le _ _ (by simp; omega),
          MultiRelay.getD_of_length_le _ _ (by simp; omega)]
  unfold sideAfter
  rw [hcur]
  by_cases hjm : j < m
  · have hl : (F.sched n b Q ansM H ((D.stEntries j c).take j)).side.length = j := by
      rw [F.length_sched_side, D.take_stEntries hj, length_logEntries hj]
    have hat : ∀ s', (D.subSides F b Q ansM H s' j c).getD j 0 = D.partSide F b Q ansM H s' j c :=
      fun s' => by
        rw [hpre, MultiRelay.getD_append_of_le _ _ _ (le_of_eq hl), hl, Nat.sub_self]
        rfl
    simp only [hjm, ↓reduceIte]
    rcases hk : D.blkKind b Q j c with _ | _ | _ <;>
      rcases he : (D.stEntries j c).getD j none with _ | r <;> simp only
    all_goals try
      (funext i
       by_cases hi : (i : ℕ) = j
       · have : i = ⟨j, hjm⟩ := Fin.ext hi
         subst this
         simp only [hat, partSide, hjm, ↓reduceIte]
         have hk' : MultiRelay.blkAt b Q (D.stEntries j c) j = D.blkKind b Q j c := rfl
         rw [hk', hk, he]
       · exact hother i hi)
    -- the relayed request
    simp only [hjm, ↓reduceDIte]
    funext i
    by_cases hi : (i : ℕ) = j
    · have hi' : i = ⟨j, hjm⟩ := Fin.ext hi
      subst hi'
      rw [Function.update_self, hat, hat]
      have hk' : MultiRelay.blkAt b Q (D.stEntries j c) j = .rel := hk
      simp only [partSide, hjm, ↓reduceIte, hk', he]
      have hrec := D.recList_place hj c
      have e1 : F.startAt n b Q (D.stEntries j c) j = D.blkStart F b Q j c := rfl
      have hstart : F.startAt n b Q (MultiRelay.recList (fun i : Fin m =>
          (D.stEntries j c)[(i : ℕ)]?)) j = D.blkStart F b Q j c := by rw [hrec]; rfl
      rw [e1, hstart]
      have hL : s - D.blkStart F b Q j c + 1 ≤ F.len := by
        have := h1 hjm
        rw [hk] at this
        simp only [MultiRelay.blkLen] at this
        omega
      have hsub : s + 1 - D.blkStart F b Q j c = s - D.blkStart F b Q j c + 1 := by omega
      rw [hsub]
      refine F.addsVec_runAux ansM H r _ hL fun k hk2 => ?_
      -- the stored answers of the block are those of the relayed request
      have hblk := D.blkKind_eq F b Q ansM H hjm c
      rw [hk, he] at hblk
      have hrb : (F.sched n b Q ansM H ((D.stEntries j c).take j)).rb < Q := by
        by_contra hc
        simp [MultiRelay.blk, hc] at hblk
      have hout := D.sched_stEntries F b Q ansM H hjm c
      rw [he] at hout
      simp only [MultiRelay.blockOf, hrb, ↓reduceIte] at hout
      have hlen := D.length_sched_take F b Q ansM H hj c
      have hS : D.blkStart F b Q j c + F.len ≤ relaySlots n m F := by
        have := F.startAt_le n b Q (D.stEntries j c) (j + 1)
        rw [F.startAt_succ] at this
        unfold blkStart
        have h2 : (j + 1) * max n F.len ≤ m * max n F.len := Nat.mul_le_mul_right _ (by omega)
        have h3 : MultiRelay.blkAt b Q (D.stEntries j c) j = .rel := hk
        rw [h3] at this
        exact le_trans this h2
      unfold MultiRelay.storeAt
      rw [dif_pos (by omega)]
      simp only [subEntries, MultiRelay.subEntriesL, List.getD_eq_getElem?_getD]
      have hlo : D.blkStart F b Q j c + k < (F.sched n b Q ansM H (D.stEntries j c)).out.length :=
          by
        rw [hout, List.length_append, hlen]
        simp [MultiRelay.runEntries, F.length_runAux]
        omega
      rw [List.getElem?_take_of_lt (by omega),
        F.getElem?_tailEntries_of_lt ansM _ (s + 1) hlo, hout,
        List.getElem?_append_right (by omega), hlen, Nat.add_sub_cancel_left]
      rfl
    · rw [Function.update_of_ne (fun e => hi (by rw [e])), hother i hi]
  · simp only [hjm, ↓reduceIte]
    funext i
    have hi : (i : ℕ) ≠ j := by omega
    exact hother i hi

/-- **One sub-slot of the relayed distinguisher on a placement**: the set-up, the main
environment's slot, the tear-down, the clock and the side additions take the placement at
sub-slot `s` to the placement at `s + 1` of the basis state with the scheduled pair query
made. -/
theorem oneSub (hO' : ∀ lg' : LogReg Req' (relaySlots n m F), E'.oracle ω' lg' = H)
    {s j : ℕ} (hj : j ≤ m) (hs : s < relaySlots n m F) (g : GameReg W n X Y Req Resp m)
    (h0 : D.blkStart F b Q j g.1 ≤ s)
    (h1 : j < m → s < D.blkStart F b Q j g.1 + F.blkLen n (D.blkKind b Q j g.1)) :
    liftL (sideAddsPerm F b Q) (liftL (tickPerm F) (liftL (teardownPerm F b Q)
      ((D.relay F b Q).eventPerm E' ω' s
        (liftL (setupPerm F b Q) (D.place F b Q (E'.answerAfter ω') H s j g))))) =
    D.place F b Q (E'.answerAfter ω') H (s + 1) j (D.qstep F b Q (E'.answerAfter ω') H s j g) := by
  rw [D.oneSub_pre F b Q H E' ω' hO' hj hs g h0 h1, prePlace, liftL_sideAdds, D.place_eq_mkR]
  have hq : (D.qstep F b Q (E'.answerAfter ω') H s j g).1 = g.1 := rfl
  have htime : (⟨min (s + 1) (relaySlots n m F), Nat.lt_succ_of_le (min_le_right _ _)⟩ :
      Fin (relaySlots n m F + 1)) = ⟨s + 1, by omega⟩ := Fin.ext (min_eq_left (by omega))
  refine mkR_congr F rfl rfl rfl ?_ rfl rfl rfl rfl rfl
  rw [hq, htime]
  exact D.sideAfter_place F b Q H (E'.answerAfter ω') hj hs g.1 h0 h1

/-! ### The boundaries of blocks -/

/-- The blocks of the entries at stage `j` end at sub-slot `startAt` of their number. -/
theorem startAt_stEntries_length {j : ℕ} (hj : j ≤ m) (c : W × Req × Option Resp × LogReg Req m) :
    F.startAt n b Q (D.stEntries j c) (D.stEntries j c).length =
      if j < m then D.blkStart F b Q j c + F.blkLen n (D.blkKind b Q j c) else D.blkStart F b Q j c := by
  rw [D.length_stEntries hj]
  split_ifs
  · rw [F.startAt_succ]
    rfl
  · rfl

/-- **Inside a block, no reply is written, no step applies and no slot starts** at the next
sub-slot. -/
theorem boundary_cont (hn : 0 < n) (ansM : List Req' → Req' → Option Resp') {s j : ℕ} (hj : j ≤ m)
    (hs : s + 1 ≤ relaySlots n m F) (g : GameReg W n X Y Req Resp m)
    (h0 : D.blkStart F b Q j g.1 ≤ s)
    (h1 : j < m → s + 1 < D.blkStart F b Q j g.1 + F.blkLen n (D.blkKind b Q j g.1)) :
    ¬ ctrlCond F b Q (relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)
        (splitLogs (D.place F b Q ansM H (s + 1) j g)).1).2 ∧
      liftL (finalizePerm F b Q) (D.place F b Q ansM H (s + 1) j g) = D.place F b Q ansM H (s + 1) j g ∧
      liftL (recordPerm F b Q D.kind) (D.place F b Q ansM H (s + 1) j g) =
        D.place F b Q ansM H (s + 1) j g := by
  have hrec := D.recList_place hj g.1
  have htime : min (s + 1) (relaySlots n m F) = s + 1 := min_eq_left hs
  have hne : F.startAt n b Q (MultiRelay.recList (fun i : Fin m => (D.stEntries j g.1)[(i : ℕ)]?))
      (MultiRelay.recList (fun i : Fin m => (D.stEntries j g.1)[(i : ℕ)]?)).length ≠ s + 1 := by
    rw [hrec, D.startAt_stEntries_length F b Q hj]
    split_ifs with hjm
    · have := h1 hjm
      omega
    · omega
  refine ⟨fun h => hne ?_, ?_, ?_⟩
  · have h' : F.startAt n b Q (MultiRelay.recList (fun i : Fin m => (D.stEntries j g.1)[(i : ℕ)]?))
        (MultiRelay.recList (fun i : Fin m => (D.stEntries j g.1)[(i : ℕ)]?)).length =
          min (s + 1) (relaySlots n m F) := h
    rwa [htime] at h'
  · rw [D.place_eq_mkR, liftL_finalize_of_ne b Q (by simpa [htime] using hne)]
  · rw [D.place_eq_mkR, liftL_record_of_none b Q D.kind]
    refine F.fillAt_ofList_eq_none n b Q (by rw [D.length_stEntries hj]; split_ifs <;> omega) ?_
    intro i hi him
    simp only [htime]
    rw [D.length_stEntries hj] at hi
    split_ifs at hi with hjm
    · rcases Nat.lt_or_ge i (j + 1) with h | h
      · have := F.startAt_mono n b Q (D.stEntries j g.1) (show i ≤ j by omega)
        unfold blkStart at h0
        omega
      · have hij : i = j + 1 := by omega
        subst hij
        have := h1 hjm
        rw [F.startAt_succ]
        unfold blkStart blkKind at this
        omega
    · have := F.startAt_mono n b Q (D.stEntries j g.1) hi
      unfold blkStart at h0
      omega

omit [Fintype W] [DecidableEq W] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype
    Req]
  [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req'] [DecidableEq Req']
  [Fintype Resp'] [DecidableEq Resp'] [Inhabited X] [Inhabited Req'] [AddGroup Y] in
theorem logEntries_succ {j : ℕ} (hj : j < m) (lg : LogReg Req m) :
    logEntries (j + 1) lg = logEntries j lg ++ [lg ⟨j, hj⟩] := by
  simp [logEntries, List.take_succ, List.getElem?_eq_getElem (show j < (List.finRange m).length by simpa)]

omit [Fintype W] [DecidableEq W] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype
    Req]
  [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req'] [DecidableEq Req']
  [Fintype Resp'] [DecidableEq Resp'] [Inhabited X] [Inhabited Req'] [AddGroup Y] in
theorem requestsBefore_eq_logEntries (lg : LogReg Req m) :
    ∀ j ≤ m, requestsBefore lg j = (logEntries j lg).filterMap id
  | 0, _ => by simp [logEntries]; rfl
  | j + 1, hj => by
    rw [requestsBefore_succ_of_lt _ (by omega), requestsBefore_eq_logEntries lg j (by omega),
      logEntries_succ (by omega), List.filterMap_append]
    cases lg ⟨j, by omega⟩ <;> rfl

/-- The rest of the relayed registers read from the logs below `j`, at sub-slot `s`. -/
def logRest (ansM : List Req' → Req' → Option Resp') (s j : ℕ) (lg : LogReg Req m) :
    RelayRest X Y Req Req' Resp' m (relaySlots n m F) (Fin F.qS → Ys) :=
  (fun i : Fin m => (logEntries j lg)[(i : ℕ)]?,
    fun t => ((F.subEntriesL n b Q ansM H s (logEntries j lg)).getD t blankEntry).2,
    fun i => (F.sched n b Q ansM H (logEntries j lg)).side.getD i 0,
    ⟨min s (relaySlots n m F), Nat.lt_succ_of_le (min_le_right _ _)⟩, default, none,
    fun _ => (default, 0))

/-- The main logs read from the logs below `j`, at sub-slot `s`. -/
def logLog (ansM : List Req' → Req' → Option Resp') (s j : ℕ) (lg : LogReg Req m) :
    LogReg Req' (relaySlots n m F) :=
  fun t => ((F.subEntriesL n b Q ansM H s (logEntries j lg)).getD t blankEntry).1

/-- **The placement between the end of a block and the start of the next slot**: the
distinguisher's registers, and the rest read from the logs below `j`. -/
def placeMid (ansM : List Req' → Req' → Option Resp') (s j : ℕ) :
    GameReg W n X Y Req Resp m →
      GameReg (RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F) (Fin F.qS → Ys)) 1
          X Y Req'
          Resp'
        (relaySlots n m F) :=
  placeOfLogs F (logRest F b Q H ansM s j) (logLog F b Q H ansM s j)

theorem placeMid_eq_mkR (ansM : List Req' → Req' → Option Resp') (s j : ℕ)
    (g : GameReg W n X Y Req Resp m) :
    placeMid F b Q H ansM s j g = mkR F (splitLogs g).1
      (fun i => (logEntries j (splitLogs g).2)[(i : ℕ)]?)
      (fun t => ((F.subEntriesL n b Q ansM H s (logEntries j (splitLogs g).2)).getD t blankEntry).2)
      (fun i => (F.sched n b Q ansM H (logEntries j (splitLogs g).2)).side.getD i 0)
      ⟨min s (relaySlots n m F), Nat.lt_succ_of_le (min_le_right _ _)⟩ default none (default, 0)
      (fun t => ((F.subEntriesL n b Q ansM H s (logEntries j (splitLogs g).2)).getD t blankEntry).1) :=
  rfl

variable {Ω St : Type} [OracleState St X Y] (E : Env Ω Req Resp X Y Q St) (ω : Ω)

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype Resp] [Fintype Req']
  [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req'] [AddGroup Y] in
theorem logEntries_update_of_le {j : ℕ} (lg : LogReg Req m) (k : Fin m) (hk : j ≤ k)
    (v : Option Req) : logEntries j (Function.update lg k v) = logEntries j lg := by
  unfold logEntries
  refine List.map_congr_left fun i hi => Function.update_of_ne (fun e => ?_) _ _
  subst e
  obtain ⟨l, hl, hli⟩ := List.mem_iff_getElem.1 hi
  simp only [List.length_take, List.length_finRange] at hl
  rw [← hli] at hk
  simp at hk
  omega

/-- **The reply at the end of a block**: under the relay hypothesis `hR`, writing the reply into
the placement at the end of block `j` gives the placement between blocks (`placeMid`, stage
`j + 1`) of the basis state after the request of slot `j`. -/
theorem finalize_place_end (ansM : List Req' → Req' → Option Resp')
    (hR : ∀ (rs : List Req) (r : Req), rs.length < Q →
      E.answerAfter ω rs r = F.runReply ansM H r (F.mainReqs Q ansM H rs))
    {s j : ℕ} (hj : j < m) (hs : s + 1 ≤ relaySlots n m F) (g : GameReg W n X Y Req Resp m)
    (hblank : (splitLogs g).2 ⟨j, hj⟩ = none)
    (hend : s + 1 = D.blkStart F b Q j g.1 + F.blkLen n (D.blkKind b Q j g.1))
    (hbud : MultiRelay.NoIdleQ b (D.stEntries j g.1)) :
    liftL (finalizePerm F b Q) (D.place F b Q ansM H (s + 1) j g) =
      placeMid F b Q H ansM (s + 1) (j + 1) (E.requestPerm D.kind ω ⟨j, hj⟩ g) := by
  obtain ⟨⟨w, rq, rs, lg⟩, ps⟩ := g
  simp only at hblank hend hbud
  change lg ⟨j, hj⟩ = none at hblank
  have hes := D.stEntries_of_lt hj (w, rq, rs, lg)
  simp only at hes
  have htime : min (s + 1) (relaySlots n m F) = s + 1 := min_eq_left hs
  have hcond : F.startAt n b Q (MultiRelay.recList (fun i : Fin m =>
      (D.stEntries j (w, rq, rs, lg))[(i : ℕ)]?)) (MultiRelay.recList (fun i : Fin m =>
      (D.stEntries j (w, rq, rs, lg))[(i : ℕ)]?)).length =
      ((⟨min (s + 1) (relaySlots n m F), Nat.lt_succ_of_le (min_le_right _ _)⟩ :
        Fin (relaySlots n m F + 1)) : ℕ) := by
    rw [D.recList_place hj.le, D.startAt_stEntries_length F b Q hj.le, if_pos hj]
    simp only [htime]
    omega
  have hrec : D.stEntries j (w, rq, rs, lg) = logEntries (j + 1)
      (splitLogs (E.requestPerm D.kind ω ⟨j, hj⟩ ((w, rq, rs, lg), ps))).2 := by
    rw [logEntries_succ hj, hes]
    by_cases hk : D.kind w
    · have hlg : (splitLogs (E.requestPerm D.kind ω ⟨j, hj⟩ ((w, rq, rs, lg), ps))).2 =
          Function.update lg ⟨j, hj⟩ (some rq) := by
        rw [E.logs_requestPerm D.kind ω ⟨j, hj⟩]
        simp [hk, hblank, splitLogs, GameReg.workspace, GameReg.request]
      rw [hlg, logEntries_update_of_le lg ⟨j, hj⟩ (by simp), Function.update_self]
      simp [hk]
    · have hlg : (splitLogs (E.requestPerm D.kind ω ⟨j, hj⟩ ((w, rq, rs, lg), ps))).2 = lg := by
        rw [E.logs_requestPerm D.kind ω ⟨j, hj⟩]
        simp [hk, splitLogs, GameReg.workspace]
      rw [hlg, hblank]
      simp [hk]
  have hsideEnd : (fun i : Fin m => (D.subSides F b Q ansM H (s + 1) j (w, rq, rs, lg)).getD i 0) =
      fun i : Fin m => (F.sched n b Q ansM H (D.stEntries j (w, rq, rs, lg))).side.getD i 0 := by
    rw [D.subSides_end F b Q ansM H hj _ hend]
  rw [D.place_eq_mkR, placeMid_eq_mkR, ← hrec]
  dsimp only [subEntries]
  set es := D.stEntries j (w, rq, rs, lg) with hes_def
  have hlen : (MultiRelay.recList (fun i : Fin m => es[(i : ℕ)]?)).length = j + 1 := by
    rw [D.recList_place hj.le, D.length_stEntries hj.le, if_pos hj]
  have htake : es.take j = logEntries j lg := D.take_stEntries hj.le _
  have hbud' : MultiRelay.NoIdleQ b (es.take j) := fun i hi h => by
    have hij : i < j := by
      rw [htake, length_logEntries hj.le] at hi
      exact hi
    have hi' : i < es.length := lt_of_lt_of_le hi (by simp)
    have h' : es.getD i none = none := by
      rw [List.getD_eq_getElem?_getD, ← List.getElem?_take_of_lt hij]
      rwa [List.getD_eq_getElem?_getD] at h
    have := hbud i hi' h'
    rwa [List.take_take, Nat.min_eq_left hij.le]
  have hqbrb := D.blkKind_eq F b Q ansM H hj (w, rq, rs, lg)
  have hqb := (F.sched_qb_rb n b Q ansM H (es.take j)).1
  have hrb := (F.sched_qb_rb n b Q ansM H (es.take j)).2
  have hgetj : es.getD j none = if D.kind w then some rq else none := by
    rw [hes, List.getD_eq_getElem?_getD, List.getElem?_append_right (by
      rw [length_logEntries hj.le]), length_logEntries hj.le, Nat.sub_self]
    rfl
  have hlast_unf : F.lastReply n b Q (fun i : Fin m => es[(i : ℕ)]?)
      (fun t : Fin (relaySlots n m F) =>
        ((F.subEntriesL n b Q ansM H (s + 1) es).getD t blankEntry).2)
      (fun i : Fin m => (D.subSides F b Q ansM H (s + 1) j (w, rq, rs, lg)).getD i 0) =
      match D.blkKind b Q j (w, rq, rs, lg), es.getD j none with
      | .rel, some r => some (F.reply r (F.stAt (F.vecSa (F.vecAt
          (fun i : Fin m => (D.subSides F b Q ansM H (s + 1) j (w, rq, rs, lg)).getD i 0) j)) r
          (fun k => MultiRelay.storeAt (fun t : Fin (relaySlots n m F) =>
            ((F.subEntriesL n b Q ansM H (s + 1) es).getD t blankEntry).2)
          (D.blkStart F b Q j (w, rq, rs, lg) + k)) F.len))
      | _, _ => none := by
    unfold MultiRelay.lastReply
    rw [D.recList_place hj.le, ← hes_def]
    have hl : es.length = j + 1 := by rw [hes_def, D.length_stEntries hj.le, if_pos hj]
    simp only [hl, Nat.succ_pos, ↓reduceIte, Nat.add_sub_cancel]
    rfl
  by_cases hk : D.kind w
  · have hans : E.answer ω (Function.update lg ⟨j, hj⟩ (some rq)) ⟨j, hj⟩ =
        E.answerAfter ω (requestsBefore lg j) rq := by
      simp only [Env.answer, Function.update_self, Option.elim_some]
      congr 1
      exact requestsBefore_congr fun k hk' =>
        Function.update_of_ne (fun e => by simp [Fin.ext_iff] at e; omega) _ _
    have hreq : (splitLogs (E.requestPerm D.kind ω ⟨j, hj⟩ ((w, rq, rs, lg), ps))).1 =
        ((w, rq, Equiv.swap none (E.answerAfter ω (requestsBefore lg j) rq) rs), ps) := by
      rw [← hans]
      simp [Env.requestPerm, copyPerm_apply, respondPerm_apply, hk, hblank, splitLogs]
    rw [hreq]
    simp only [hk, ↓reduceIte] at hgetj
    have hrs0 : (requestsBefore lg j).length = (F.sched n b Q ansM H (es.take j)).rb := by
      rw [hrb, htake, requestsBefore_eq_logEntries lg j hj.le, MultiRelay.length_filterMap_id]
    by_cases hQ : (requestsBefore lg j).length < Q
    · have hkind : D.blkKind b Q j (w, rq, rs, lg) = .rel := by
        rw [hqbrb, ← hes_def, hgetj]
        simp [MultiRelay.blk, ← hrs0, hQ]
      have hmain : (F.sched n b Q ansM H (es.take j)).out.filterMap Prod.fst =
          F.mainReqs Q ansM H (requestsBefore lg j) := by
        rw [F.filterMap_sched n b Q ansM H _ hbud', htake, requestsBefore_eq_logEntries lg j hj.le]
      have hst := D.stAt_place_store F b Q ansM H (s' := s + 1) (k := F.len) hj (w, rq, rs, lg)
        hkind (by rw [← hes_def]; exact hgetj) (by
          have h := hend
          rw [hkind] at h
          exact h.le) (by
          have h := hend
          rw [hkind] at h
          exact h.ge)
      have hlast : F.lastReply n b Q (fun i : Fin m => es[(i : ℕ)]?)
          (fun t : Fin (relaySlots n m F) =>
            ((F.subEntriesL n b Q ansM H (s + 1) es).getD t blankEntry).2)
          (fun i : Fin m => (D.subSides F b Q ansM H (s + 1) j (w, rq, rs, lg)).getD i 0) =
          some (E.answerAfter ω (requestsBefore lg j) rq) := by
        rw [hlast_unf, hkind, hgetj]
        simp only
        have hst' : F.stAt (F.vecSa (F.vecAt
            (fun i : Fin m => (D.subSides F b Q ansM H (s + 1) j (w, rq, rs, lg)).getD i 0) j))
            rq (fun k => MultiRelay.storeAt (fun t : Fin (relaySlots n m F) =>
            ((F.subEntriesL n b Q ansM H (s + 1) es).getD t blankEntry).2)
            (D.blkStart F b Q j (w, rq, rs, lg) + k)) F.len =
            (F.runAux ansM H rq ((F.sched n b Q ansM H (es.take j)).out.filterMap
              Prod.fst) F.len).1 := hst
        rw [hst', hmain, hR _ _ hQ]
        rfl
      rw [liftL_finalize_of_some b Q hcond hlast]
      exact mkR_congr F rfl rfl rfl hsideEnd rfl rfl rfl rfl rfl
    · have hkind : D.blkKind b Q j (w, rq, rs, lg) = .idle := by
        rw [hqbrb, ← hes_def, hgetj]
        simp [MultiRelay.blk, ← hrs0, hQ]
      have hlast : F.lastReply n b Q (fun i : Fin m => es[(i : ℕ)]?)
          (fun t : Fin (relaySlots n m F) =>
            ((F.subEntriesL n b Q ansM H (s + 1) es).getD t blankEntry).2)
          (fun i : Fin m => (D.subSides F b Q ansM H (s + 1) j (w, rq, rs, lg)).getD i 0) = none :=
              by
        rw [hlast_unf, hkind]
      have hnone : E.answerAfter ω (requestsBefore lg j) rq = none := by
        unfold Env.answerAfter
        rw [dif_neg hQ]
      rw [liftL_finalize_of_none b Q hlast, hnone, Equiv.swap_self]
      exact mkR_congr F rfl rfl rfl hsideEnd rfl rfl rfl rfl rfl
  · have hreq : (splitLogs (E.requestPerm D.kind ω ⟨j, hj⟩ ((w, rq, rs, lg), ps))).1 =
        ((w, rq, rs), ps) := by
      simp [Env.requestPerm, copyPerm_apply, respondPerm_apply, hk, splitLogs]
    rw [hreq]
    simp only [hk, Bool.false_eq_true, ↓reduceIte] at hgetj
    have hkind : D.blkKind b Q j (w, rq, rs, lg) = .qry := by
      have hb := hbud j (by rw [hes_def, D.length_stEntries hj.le, if_pos hj]; omega) hgetj
      rw [hqbrb, ← hes_def, hgetj]
      simp [MultiRelay.blk, hqb, hb]
    have hlast : F.lastReply n b Q (fun i : Fin m => es[(i : ℕ)]?)
        (fun t : Fin (relaySlots n m F) =>
          ((F.subEntriesL n b Q ansM H (s + 1) es).getD t blankEntry).2)
        (fun i : Fin m => (D.subSides F b Q ansM H (s + 1) j (w, rq, rs, lg)).getD i 0) = none := by
      rw [hlast_unf, hkind]
    rw [liftL_finalize_of_none b Q hlast]
    exact mkR_congr F rfl rfl rfl hsideEnd rfl rfl rfl rfl rfl

/-- **The step applies between blocks**: at sub-slot `s` the step numbered `j` applies on the
placement between blocks when the blocks of the logs below `j` end at `s`. -/
theorem ctrlCond_placeMid (ansM : List Req' → Req' → Option Resp') {s j : ℕ} (hj : j ≤ m)
    (hs : s ≤ relaySlots n m F) (lg : LogReg Req m)
    (hstart : F.startAt n b Q (logEntries j lg) j = s) :
    ctrlCond (n := n) F b Q (logRest (n := n) F b Q H ansM s j lg) ∧
      (MultiRelay.recList (logRest (n := n) F b Q H ansM s j lg).1).length = j := by
  have hl := length_logEntries hj lg
  have hrec : MultiRelay.recList (logRest (n := n) F b Q H ansM s j lg).1 = logEntries j lg :=
    MultiRelay.recList_getElem? _ (by omega)
  refine ⟨?_, by rw [hrec, hl]⟩
  unfold ctrlCond
  rw [hrec, hl, hstart]
  simp [logRest, min_eq_left hs]

/-- **The record of the starting slot completes the placement**: between blocks, recording the
entry of slot `j` (when `j < m`) gives the placement at stage `j`. -/
theorem record_placeMid (hn : 0 < n) (ansM : List Req' → Req' → Option Resp') {s j : ℕ}
    (hj : j ≤ m) (hs : s ≤ relaySlots n m F) (g : GameReg W n X Y Req Resp m)
    (hstart : F.startAt n b Q (logEntries j (splitLogs g).2) j = s) :
    liftL (recordPerm F b Q D.kind) (placeMid F b Q H ansM s j g) = D.place F b Q ansM H s j g := by
  obtain ⟨⟨w, rq, rs, lg⟩, ps⟩ := g
  change F.startAt n b Q (logEntries j lg) j = s at hstart
  have hl := length_logEntries hj lg
  have hout : (F.sched n b Q ansM H (logEntries j lg)).out.length = s := by
    rw [F.length_sched, hl, hstart]
  have hbs : D.blkStart F b Q j (w, rq, rs, lg) = s := by
    unfold blkStart
    rw [F.startAt_congr n b Q (es' := logEntries j lg)
      (by rw [D.take_stEntries hj, List.take_of_length_le (by rw [hl])]), hstart]
  rw [placeMid_eq_mkR, D.place_eq_mkR, D.subSides_start F b Q ansM H hj _ hbs]
  dsimp only [subEntries]
  change liftL (recordPerm F b Q D.kind) (mkR F ((w, rq, rs), ps) (fun i => (logEntries j lg)[(i : ℕ)]?)
    (fun t => ((F.subEntriesL n b Q ansM H s (logEntries j lg)).getD t blankEntry).2)
    (fun i => (F.sched n b Q ansM H (logEntries j lg)).side.getD i 0)
    ⟨min s (relaySlots n m F), Nat.lt_succ_of_le (min_le_right _ _)⟩ default none (default, 0)
    (fun t => ((F.subEntriesL n b Q ansM H s (logEntries j lg)).getD t blankEntry).1)) =
    mkR F ((w, rq, rs), ps) (fun i => (D.stEntries j (w, rq, rs, lg))[(i : ℕ)]?)
      (fun t => ((F.subEntriesL n b Q ansM H s (D.stEntries j (w, rq, rs, lg))).getD t blankEntry).2)
      (fun i => (F.sched n b Q ansM H (logEntries j lg)).side.getD i 0)
      ⟨min s (relaySlots n m F), Nat.lt_succ_of_le (min_le_right _ _)⟩ default none (default, 0)
      (fun t => ((F.subEntriesL n b Q ansM H s (D.stEntries j (w, rq, rs, lg))).getD t blankEntry).1)
  by_cases hjm : j < m
  · have hes := D.stEntries_of_lt hjm (w, rq, rs, lg)
    simp only at hes
    have hfill : F.fillAt n b Q (fun i : Fin m => (logEntries j lg)[(i : ℕ)]?)
        (min s (relaySlots n m F)) = some ⟨j, hjm⟩ := by
      rw [F.fillAt_ofList_eq_some n b Q hn (es := logEntries j lg)
        (t := min s (relaySlots n m F)) (by rwa [hl]) (by rw [hl, min_eq_left hs]; exact hstart)]
      simp [hl]
    rw [liftL_record_of_some b Q D.kind (i := ⟨j, hjm⟩) hfill]
    have hsub := F.subEntriesL_append n b Q ansM H (logEntries j lg)
      (if D.kind w then some rq else none) hout
    rw [hes, hsub.1, hsub.2]
    refine mkR_congr F rfl ?_ rfl rfl rfl rfl rfl rfl rfl
    funext i
    by_cases hi : (i : ℕ) = j
    · have : i = ⟨j, hjm⟩ := Fin.ext hi
      subst this
      rw [Function.update_self, List.getElem?_eq_none (by omega), Equiv.swap_apply_left,
        List.getElem?_append_right (by omega)]
      simp [hl, entryOf]
    · rw [Function.update_of_ne (fun e => hi (by rw [e]))]
      rcases Nat.lt_or_ge (i : ℕ) j with h | h
      · rw [List.getElem?_append_left (by omega)]
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
  · have hm : j = m := by omega
    rw [liftL_record_of_none b Q D.kind (F.fillAt_ofList_eq_none n b Q (es := logEntries j lg)
      (by omega) fun i hi him => by
        have := F.startAt_lt_of_lt n b Q hn (logEntries j lg) (show i < j by omega)
        show _ ≠ min s (relaySlots n m F)
        rw [min_eq_left hs]
        omega)]
    subst hm
    rw [D.stEntries_self]

/-! ### The distinguisher's side -/

theorem partQ_apply (s j : ℕ) (c : W × Req × Option Resp × LogReg Req m) (ps : Fin n → X × Y) :
    D.partQ F b Q H s j (c, ps) = (c, fun i => ((ps i).1, (ps i).2 +
      if j < m ∧ D.blkKind b Q j c = .qry ∧ (i : ℕ) + D.blkStart F b Q j c < s then H (ps i).1
      else 0)) :=
  rfl

theorem qstep_apply (ansM : List Req' → Req' → Option Resp') (s j : ℕ)
    (c : W × Req × Option Resp × LogReg Req m) (ps : Fin n → X × Y) :
    D.qstep F b Q ansM H s j (c, ps) = (c, fun i => ((ps i).1, (ps i).2 +
      if (D.schedAct F b Q ansM H s j c).pairIdx = some i then H (ps i).1 else 0)) :=
  rfl

/-- The scheduled action queries a pair only in a query block, the pair numbered by the
sub-slot. -/
theorem schedAct_pairIdx (ansM : List Req' → Req' → Option Resp') (s j : ℕ)
    (c : W × Req × Option Resp × LogReg Req m) (i : Fin n) :
    (D.schedAct F b Q ansM H s j c).pairIdx = some i ↔
      j < m ∧ D.blkKind b Q j c = .qry ∧ (i : ℕ) = s - D.blkStart F b Q j c := by
  unfold schedAct
  by_cases hj : j < m
  · simp only [hj, ↓reduceIte, true_and]
    rcases hk : D.blkKind b Q j c with _ | _ | _ <;>
      rcases he : (D.stEntries j c).getD j none with _ | r <;> simp only
    · split_ifs with h
      · simp [SubAct.pairIdx, Fin.ext_iff, eq_comm]
      · simp only [SubAct.pairIdx, reduceCtorEq, false_iff]
        omega
    · split_ifs with h
      · simp [SubAct.pairIdx, Fin.ext_iff, eq_comm]
      · simp only [SubAct.pairIdx, reduceCtorEq, false_iff]
        omega
    · simp [SubAct.pairIdx]
    · simp [SubAct.pairIdx]
    · simp [SubAct.pairIdx]
    · split <;> simp [SubAct.pairIdx]
  · simp [hj, SubAct.pairIdx]

/-- **The partial queries advance by the scheduled pair query.** -/
theorem partQ_succ (ansM : List Req' → Req' → Option Resp') {s j : ℕ}
    (c : W × Req × Option Resp × LogReg Req m) (ps : Fin n → X × Y)
    (h0 : D.blkStart F b Q j c ≤ s) :
    D.partQ F b Q H (s + 1) j (c, ps) =
      D.qstep F b Q ansM H s j (D.partQ F b Q H s j (c, ps)) := by
  rw [partQ_apply, partQ_apply, qstep_apply]
  refine Prod.ext rfl (funext fun i => Prod.ext rfl ?_)
  simp only [D.schedAct_pairIdx]
  by_cases hq : j < m ∧ D.blkKind b Q j c = .qry
  · simp only [hq, true_and]
    by_cases h1 : (i : ℕ) + D.blkStart F b Q j c < s
    · have h2 : ¬ (i : ℕ) = s - D.blkStart F b Q j c := by omega
      simp [h1, h2, show (i : ℕ) + D.blkStart F b Q j c < s + 1 by omega]
    · by_cases h2 : (i : ℕ) = s - D.blkStart F b Q j c
      · simp [h1, h2, show s - D.blkStart F b Q j c + D.blkStart F b Q j c < s + 1 by omega,
          show ¬ (s - D.blkStart F b Q j c + D.blkStart F b Q j c < s) by omega]
      · simp [h1, h2, show ¬ ((i : ℕ) + D.blkStart F b Q j c < s + 1) by omega]
  · simp [hq, not_and_or.mp hq]
    rcases not_and_or.mp hq with h | h <;> simp [h]

/-- **At the start of a block no pair has been queried.** -/
theorem partQ_start {s j : ℕ} (c : W × Req × Option Resp × LogReg Req m) (ps : Fin n → X × Y)
    (h0 : s ≤ D.blkStart F b Q j c) : D.partQ F b Q H s j (c, ps) = (c, ps) := by
  rw [partQ_apply]
  refine Prod.ext rfl (funext fun i => Prod.ext rfl ?_)
  simp [show ¬ ((i : ℕ) + D.blkStart F b Q j c < s) by omega]

theorem requestPerm_of_not_kind {k : Fin m} {g : GameReg W n X Y Req Resp m}
    (h : D.kind g.1.1 = false) : E.requestPerm D.kind ω k g = g := by
  obtain ⟨⟨w, rq, rs, lg⟩, ps⟩ := g
  simp only at h
  simp [Env.requestPerm, copyPerm_apply, respondPerm_apply, h]

theorem oraclePerm_apply' (g : GameReg W n X Y Req Resp m) :
    E.oraclePerm D.kind ω g = (g.1, fun i => ((g.2 i).1, (g.2 i).2 +
      if D.kind g.1.1 then 0 else E.oracle ω g.1.2.2.2 (g.2 i).1)) := by
  simp only [Env.oraclePerm, queryPermOf_apply]
  refine Prod.ext rfl (funext fun i => Prod.ext rfl ?_)
  split_ifs <;> rfl

/-- **The slot of `D` at the end of a block** is the scheduled pair query after the partial
queries (a query block), then the request of the slot. -/
theorem eventPerm_end (hO : ∀ lg : LogReg Req m, E.oracle ω lg = H)
    (ansM : List Req' → Req' → Option Resp') {s j : ℕ} (hj : j < m)
    (g : GameReg W n X Y Req Resp m) (h0 : D.blkStart F b Q j g.1 ≤ s)
    (hend : s + 1 = D.blkStart F b Q j g.1 + F.blkLen n (D.blkKind b Q j g.1))
    (hbud : MultiRelay.NoIdleQ b (D.stEntries j g.1)) :
    D.eventPerm E ω j g =
      E.requestPerm D.kind ω ⟨j, hj⟩ (D.qstep F b Q ansM H s j (D.partQ F b Q H s j g)) := by
  obtain ⟨c, ps⟩ := g
  obtain ⟨w, rq, rs, lg⟩ := c
  simp only at h0 hend hbud
  have hes := D.stEntries_of_lt hj (w, rq, rs, lg)
  simp only at hes
  have hgetj : (D.stEntries j (w, rq, rs, lg)).getD j none = if D.kind w then some rq else none := by
    rw [hes, List.getD_eq_getElem?_getD, List.getElem?_append_right (by
      rw [length_logEntries hj.le]), length_logEntries hj.le, Nat.sub_self]
    rfl
  have hqbrb := D.blkKind_eq F b Q ansM H hj (w, rq, rs, lg)
  rw [D.partQ_apply, D.qstep_apply]
  simp only [eventPerm, hj, ↓reduceDIte, Equiv.trans_apply]
  by_cases hk : D.kind w
  · have hnq : D.blkKind b Q j (w, rq, rs, lg) ≠ .qry := by
      rw [hqbrb, hgetj]
      simp only [hk, ↓reduceIte, MultiRelay.blk]
      split_ifs <;> simp
    have hpair : ∀ i : Fin n, ¬ (D.schedAct F b Q ansM H s j (w, rq, rs, lg)).pairIdx = some i :=
      fun i h => hnq ((D.schedAct_pairIdx F b Q H ansM s j _ i).1 h).2.1
    simp only [hnq, false_and, and_false, ↓reduceIte, hpair, add_zero]
    rw [oraclePerm_apply']
    have hw := E.workspace_requestPerm D.kind ω ⟨j, hj⟩ ((w, rq, rs, lg), ps)
    have hp : (E.requestPerm D.kind ω ⟨j, hj⟩ ((w, rq, rs, lg), ps)).2 = ps := rfl
    rw [hw, hp]
    simp only [hk, ↓reduceIte, add_zero]
    rfl
  · have hq : D.blkKind b Q j (w, rq, rs, lg) = .qry := by
      have hb := hbud j (by rw [D.length_stEntries hj.le, if_pos hj]; omega) (by
        rw [hgetj]; simp [hk])
      rw [hqbrb, hgetj]
      simp only [hk, Bool.false_eq_true, ↓reduceIte, MultiRelay.blk]
      rw [if_pos (by rwa [(F.sched_qb_rb n b Q ansM H _).1])]
    have hk' : D.kind w = false := by simpa using hk
    rw [hq] at hend
    simp only [MultiRelay.blkLen] at hend
    simp only [hq, hj, true_and, D.schedAct_pairIdx]
    rw [D.requestPerm_of_not_kind Q E ω (g := ((w, rq, rs, lg), ps)) hk',
      D.requestPerm_of_not_kind Q E ω hk', oraclePerm_apply']
    simp only [hk', Bool.false_eq_true, ↓reduceIte, hO]
    refine Prod.ext rfl (funext fun i => Prod.ext rfl ?_)
    have hi := i.2
    by_cases h1 : (i : ℕ) + D.blkStart F b Q j (w, rq, rs, lg) < s
    · simp [h1, show ¬ ((i : ℕ) = s - D.blkStart F b Q j (w, rq, rs, lg)) by omega]
    · simp [h1, show (i : ℕ) = s - D.blkStart F b Q j (w, rq, rs, lg) by omega,
        show ¬ (s - D.blkStart F b Q j (w, rq, rs, lg) + D.blkStart F b Q j (w, rq, rs, lg) < s)
          by omega]

/-! ### The budget of the distinguisher -/

omit [Fintype W] [DecidableEq W] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype
    Req]
  [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req'] [DecidableEq Req']
  [Fintype Resp'] [DecidableEq Resp'] [Inhabited X] [Inhabited Req'] [AddGroup Y] in
theorem queriesBefore_eq_countP (lg : LogReg Req m) :
    ∀ j ≤ m, queriesBefore lg j = (logEntries j lg).countP Option.isNone
  | 0, _ => by simp [queriesBefore_zero, logEntries]
  | j + 1, hj => by
    rw [queriesBefore_succ, queriesBefore_eq_countP lg j (by omega), logEntries_succ (by omega),
      List.countP_append]
    simp only [queriedAt, show j < m by omega, ↓reduceDIte]
    cases lg ⟨j, by omega⟩ <;> rfl

/-- **The request of slot `k` keeps the budget** (`Budget.holds_requestPerm` for any
environment state). -/
theorem holds_requestPerm' (bud : D.Budget b) {k : ℕ} (hk : k < m) {r : GameReg W n X Y Req Resp m}
    (hr : bud.HoldsBefore k r.1) : bud.Holds k (E.requestPerm D.kind ω ⟨k, hk⟩ r).1 := by
  have hws : (E.requestPerm D.kind ω ⟨k, hk⟩ r).1.1 = r.1.1 := E.workspace_requestPerm D.kind ω _ r
  have h0 : r.1.2.2.2 ⟨k, hk⟩ = none := hr.blank ⟨k, hk⟩ le_rfl
  have hlg : (E.requestPerm D.kind ω ⟨k, hk⟩ r).1.2.2.2 =
      if D.kind r.1.1 then Function.update r.1.2.2.2 ⟨k, hk⟩ (some r.1.2.1) else r.1.2.2.2 := by
    have h := E.logs_requestPerm D.kind ω ⟨k, hk⟩ r
    change (E.requestPerm D.kind ω ⟨k, hk⟩ r).1.2.2.2 = if D.kind r.1.1 then
      Function.update r.1.2.2.2 ⟨k, hk⟩ (Equiv.swap none (some r.1.2.1) (r.1.2.2.2 ⟨k, hk⟩))
        else r.1.2.2.2 at h
    rw [h0, Equiv.swap_apply_left] at h
    exact h
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

/-- **The stages before the last slot respect the budget.** -/
theorem stage_supported_holdsBefore (bud : D.Budget b) :
    ∀ j, j < m → Supported {r : GameReg W n X Y Req Resp m | bud.HoldsBefore j r.1} (D.stage E ω j)
  | 0, hm => bud.holdsBefore_liftedStep_zero hm
  | j + 1, hj => by
    rw [D.stage_succ]
    refine bud.holdsBefore_liftedStep j hj
      ((stage_supported_holdsBefore bud j (by omega)).permOp fun r hr => ?_)
    simp only [eventPerm, show j < m by omega, ↓reduceDIte, Equiv.trans_apply, Set.mem_setOf_eq]
    exact holds_requestPerm' D b Q E ω bud (by omega) hr

/-- **The last stage respects the budget**: at most `b` query slots. -/
theorem stage_supported_last (bud : D.Budget b) :
    Supported {r : GameReg W n X Y Req Resp m | queriesBefore r.1.2.2.2 m ≤ b} (D.stage E ω m) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have h := (D.gameInit_supported).logControlled (fun _ => D.stepAt 0)
    refine h.mono fun r hr => ?_
    simp [queriesBefore_zero]
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [D.stage_succ]
    have h1 := (D.stage_supported_holdsBefore b Q E ω bud k (by omega)).permOp
      (π := D.eventPerm E ω k) (B' := {r | bud.Holds k r.1}) fun r hr => by
        simp only [eventPerm, show k < k + 1 by omega, ↓reduceDIte, Equiv.trans_apply,
          Set.mem_setOf_eq]
        exact holds_requestPerm' D b Q E ω bud (by omega) hr
    have h2 : Supported (logsIn {lg : LogReg Req (k + 1) | queriesBefore lg (k + 1) ≤ b})
        (permOp (D.eventPerm E ω k) (D.stage E ω k)) := h1.mono fun r hr => hr.count
    exact (h2.logControlled _).mono fun r hr => hr

omit [Fintype W] [DecidableEq W] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype
    Req]
  [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req'] [DecidableEq Req']
  [Fintype Resp'] [DecidableEq Resp'] [Inhabited X] [Inhabited Req'] [AddGroup Y] in
theorem take_logEntries {i j : ℕ} (hij : i ≤ j) (lg : LogReg Req m) :
    (logEntries j lg).take i = logEntries i lg := by
  simp [logEntries, List.take_take, ← List.map_take, Nat.min_eq_left hij]

omit [Fintype W] [DecidableEq W] [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype
    Req]
  [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req'] [DecidableEq Req']
  [Fintype Resp'] [DecidableEq Resp'] [Inhabited X] [Inhabited Req'] [AddGroup Y] in
/-- A query entry below `j` comes after fewer query entries than the logs below `j` hold. -/
theorem countP_lt_of_none {i j : ℕ} (hij : i < j) (hj : j ≤ m) (lg : LogReg Req m)
    (h : lg ⟨i, by omega⟩ = none) :
    (logEntries i lg).countP Option.isNone < (logEntries j lg).countP Option.isNone := by
  have h1 : (logEntries (i + 1) lg).countP Option.isNone =
      (logEntries i lg).countP Option.isNone + 1 := by
    rw [logEntries_succ (by omega), List.countP_append, h]
    rfl
  have h2 : (logEntries (i + 1) lg).countP Option.isNone ≤ (logEntries j lg).countP Option.isNone := by
    rw [← take_logEntries (show i + 1 ≤ j by omega)]
    exact List.Sublist.countP_le (List.take_sublist _ _)
  omega

theorem noIdleQ_of_count {j : ℕ} (hj : j ≤ m) (c : W × Req × Option Resp × LogReg Req m)
    (hc : queriesBefore c.2.2.2 j ≤ b)
    (hlast : j < m → D.kind c.1 = false → queriesBefore c.2.2.2 j < b) :
    MultiRelay.NoIdleQ b (D.stEntries j c) := by
  intro i hi hnone
  rw [queriesBefore_eq_countP _ j hj] at hc hlast
  rw [D.length_stEntries hj] at hi
  rcases Nat.lt_or_ge i j with hij | hij
  · have htk : (D.stEntries j c).take i = logEntries i c.2.2.2 := by
      have := congrArg (List.take i) (D.take_stEntries hj c)
      rw [List.take_take, Nat.min_eq_left hij.le] at this
      rw [this, take_logEntries hij.le]
    rw [htk]
    have hlE : (logEntries j c.2.2.2)[i]? = some (c.2.2.2 ⟨i, by omega⟩) := by
      unfold logEntries
      rw [List.getElem?_map, List.getElem?_take_of_lt hij,
        List.getElem?_eq_getElem (by simp; omega)]
      simp
    have hg : c.2.2.2 ⟨i, by omega⟩ = none := by
      rw [List.getD_eq_getElem?_getD, ← List.getElem?_take_of_lt hij, D.take_stEntries hj, hlE]
        at hnone
      exact hnone
    have := countP_lt_of_none hij hj c.2.2.2 hg
    omega
  · split_ifs at hi with hjm
    · have hij' : i = j := by omega
      subst hij'
      rw [D.take_stEntries hj]
      have hk : D.kind c.1 = false := by
        rw [D.stEntries_of_lt hjm, List.getD_eq_getElem?_getD, List.getElem?_append_right
          (by rw [length_logEntries hj]), length_logEntries hj, Nat.sub_self] at hnone
        simp only [List.getElem?_cons_zero, Option.getD_some] at hnone
        cases hkk : D.kind c.1
        · rfl
        · simp [hkk] at hnone
      exact hlast hjm hk
    · omega

theorem noIdleQ_of_holdsBefore (bud : D.Budget b) {j : ℕ} (hj : j < m)
    (r : GameReg W n X Y Req Resp m) (h : bud.HoldsBefore j r.1) :
    MultiRelay.NoIdleQ b (D.stEntries j r.1) :=
  D.noIdleQ_of_count b hj.le r.1 h.count fun _ hk => bud.cap j hj _ r.1.1 h.mem hk

/-! ### The run of the relayed distinguisher -/

/-- The basis states at stage `j` within the budget whose logs from slot `j` on are blank. -/
def Good (j : ℕ) : Set (GameReg W n X Y Req Resp m) :=
  {g | MultiRelay.NoIdleQ b (D.stEntries j g.1) ∧ ∀ k : Fin m, j ≤ (k : ℕ) → g.1.2.2.2 k = none}

/-- **The stages are within the budget, with blank later logs.** -/
theorem stage_supported_good (bud : D.Budget b) {j : ℕ} (hj : j ≤ m) :
    Supported (D.Good b j) (D.stage E ω j) := by
  rcases Nat.lt_or_ge j m with hjm | hjm
  · refine (D.stage_supported_holdsBefore b Q E ω bud j hjm).mono fun r hr =>
      ⟨D.noIdleQ_of_holdsBefore b bud hjm r hr, fun k hk => hr.blank k hk⟩
  · have hm : j = m := by omega
    subst hm
    refine (D.stage_supported_last b Q E ω bud).mono fun r hr =>
      ⟨D.noIdleQ_of_count b le_rfl r.1 hr (fun h => absurd h (lt_irrefl _)), fun k hk =>
        absurd k.2 (by omega)⟩

/-- **The part of the stage at sub-slot `s`**: the basis states of stage `j` whose block contains
`s`, with the partial queries of their block made. -/
noncomputable def piece (s j : ℕ) : QState (GameReg W n X Y Req Resp m) :=
  mask (D.inBlock F b Q s j) (permOp (D.partQ F b Q H s j) (D.stage E ω j))

theorem piece_supported (bud : D.Budget b) {s j : ℕ} (hj : j ≤ m) :
    Supported (D.inBlock F b Q s j ∩ D.Good b j) (D.piece F b Q H E ω s j) := by
  intro g hg
  unfold piece
  by_cases h1 : g ∈ D.inBlock F b Q s j
  · rw [mask_apply_of_mem _ h1, permOp_apply]
    refine D.stage_supported_good b Q E ω bud hj _ fun h => hg ⟨h1, ?_⟩
    obtain ⟨c, ps⟩ := g
    exact h
  · rw [mask_apply_of_notMem _ h1]

/-- **The logs below `j + 1` after the request of slot `j`** list the entries at stage `j`. -/
theorem logEntries_requestPerm {j : ℕ} (hj : j < m) (g : GameReg W n X Y Req Resp m)
    (hblank : g.1.2.2.2 ⟨j, hj⟩ = none) :
    logEntries (j + 1) (E.requestPerm D.kind ω ⟨j, hj⟩ g).1.2.2.2 = D.stEntries j g.1 := by
  obtain ⟨⟨w, rq, rs, lg⟩, ps⟩ := g
  change lg ⟨j, hj⟩ = none at hblank
  rw [logEntries_succ hj, D.stEntries_of_lt hj]
  have hlg := E.logs_requestPerm D.kind ω ⟨j, hj⟩ ((w, rq, rs, lg), ps)
  change (E.requestPerm D.kind ω ⟨j, hj⟩ ((w, rq, rs, lg), ps)).1.2.2.2 = _ at hlg
  rw [hlg]
  by_cases hk : D.kind w
  · simp only [GameReg.workspace, GameReg.request, splitLogs, Equiv.coe_fn_mk, hk, ↓reduceIte,
      hblank, Equiv.swap_apply_left]
    rw [logEntries_update_of_le lg ⟨j, hj⟩ (by simp), Function.update_self]
  · simp only [GameReg.workspace, splitLogs, Equiv.coe_fn_mk, hk, Bool.false_eq_true, ↓reduceIte,
      hblank]

theorem logEntries_eventPerm {j : ℕ} (hj : j < m) (g : GameReg W n X Y Req Resp m)
    (hblank : g.1.2.2.2 ⟨j, hj⟩ = none) :
    logEntries (j + 1) (D.eventPerm E ω j g).1.2.2.2 = D.stEntries j g.1 := by
  simp only [eventPerm, hj, ↓reduceDIte, Equiv.trans_apply]
  exact D.logEntries_requestPerm Q E ω hj g hblank

/-- The basis states at stage `j < m` whose block ends at sub-slot `s`. -/
def endSet (s j : ℕ) : Set (GameReg W n X Y Req Resp m) :=
  {g | j < m ∧ s + 1 = D.blkStart F b Q j g.1 + F.blkLen n (D.blkKind b Q j g.1)}

/-- The basis states at stage `j` whose block starts at sub-slot `t`. -/
def startSet (t j : ℕ) : Set (GameReg W n X Y Req Resp m) :=
  {g | D.blkStart F b Q j g.1 = t}

/-- **One sub-slot on a placed vector.** -/
theorem stepA (hO' : ∀ lg' : LogReg Req' (relaySlots n m F), E'.oracle ω' lg' = H)
    {s j : ℕ} (hj : j ≤ m) (hs : s < relaySlots n m F) {v : QState (GameReg W n X Y Req Resp m)}
    (hv : Supported (D.inBlock F b Q s j) v) :
    permOp (liftL (sideAddsPerm F b Q)) (permOp (liftL (tickPerm F))
      (permOp (liftL (teardownPerm F b Q))
      (permOp ((D.relay F b Q).eventPerm E' ω' s) (permOp (liftL (setupPerm F b Q))
        (pushV (D.place F b Q (E'.answerAfter ω') H s j) v))))) =
      pushV (D.place F b Q (E'.answerAfter ω') H (s + 1) j)
        (permOp (D.qstep F b Q (E'.answerAfter ω') H s j) v) := by
  rw [← permOp_trans, ← permOp_trans, ← permOp_trans, ← permOp_trans]
  exact permOp_pushV hv fun g hg => D.oneSub F b Q H E' ω' hO' hj hs g hg.1 hg.2

/-- **Inside a block** the reply, the step and the record leave a placed vector unchanged. -/
theorem stepCont (hn : 0 < n) (ansM : List Req' → Req' → Option Resp') {s j : ℕ} (hj : j ≤ m)
    (hs : s + 1 ≤ relaySlots n m F) {u : QState (GameReg W n X Y Req Resp m)}
    (hu : Supported (D.inBlock F b Q s j ∩ (D.endSet F b Q s j)ᶜ) u) :
    permOp (liftL (recordPerm F b Q D.kind)) (logControlled (fun _ => D.ctrlStep F b Q)
      (permOp (liftL (finalizePerm F b Q)) (pushV (D.place F b Q ansM H (s + 1) j) u))) =
      pushV (D.place F b Q ansM H (s + 1) j) u := by
  have hb : ∀ g ∈ D.inBlock F b Q s j ∩ (D.endSet F b Q s j)ᶜ, _ := fun g hg =>
    D.boundary_cont F b Q H hn ansM hj hs g hg.1.1 fun hjm => by
      have h1 := hg.1.2 hjm
      have h2 : ¬ (j < m ∧ _) := hg.2
      have h3 : ¬ s + 1 = D.blkStart F b Q j g.1 + F.blkLen n (D.blkKind b Q j g.1) :=
        fun h => h2 ⟨hjm, h⟩
      omega
  rw [permOp_pushV hu (π := Equiv.refl _) (f' := D.place F b Q ansM H (s + 1) j)
      fun g hg => (hb g hg).2.1, permOp_refl',
    D.logControlled_ctrlStep_pushV_of_not F b Q hu fun g hg => (hb g hg).1,
    permOp_pushV hu (π := Equiv.refl _) (f' := D.place F b Q ansM H (s + 1) j)
      fun g hg => (hb g hg).2.2, permOp_refl']

/-- The first sub-slot of block `j + 1` read from the logs below `j + 1`. -/
theorem blkStart_succ_eq {j : ℕ} (hj : j + 1 ≤ m) (c : W × Req × Option Resp × LogReg Req m) :
    D.blkStart F b Q (j + 1) c = F.startAt n b Q (logEntries (j + 1) c.2.2.2) (j + 1) :=
  F.startAt_congr n b Q (by rw [D.take_stEntries hj, take_logEntries le_rfl])

/-- **The end of a block on a placed vector**: the reply, the distinguisher's next step and the
record of the next slot turn the placement at stage `j` into the placement at stage `j + 1`, and
the distinguisher's side makes its slot `j` and its step `j + 1`. -/
theorem stepEnd (hn : 0 < n) (hO : ∀ lg : LogReg Req m, E.oracle ω lg = H)
    (hR : ∀ (rs : List Req) (r : Req), rs.length < Q →
      E.answerAfter ω rs r = F.runReply (E'.answerAfter ω') H r (F.mainReqs Q (E'.answerAfter ω') H rs))
    {s j : ℕ} (hj : j < m) (hs : s + 1 ≤ relaySlots n m F) {v : QState (GameReg W n X Y Req Resp m)}
    (hv : Supported (D.endSet F b Q s j ∩ D.Good b j) v) :
    permOp (liftL (recordPerm F b Q D.kind)) (logControlled (fun _ => D.ctrlStep F b Q)
      (permOp (liftL (finalizePerm F b Q)) (pushV (D.place F b Q (E'.answerAfter ω') H (s + 1) j)
        (permOp (D.qstep F b Q (E'.answerAfter ω') H s j) (permOp (D.partQ F b Q H s j) v))))) =
      pushV (D.place F b Q (E'.answerAfter ω') H (s + 1) (j + 1))
        (D.liftedStep (j + 1) (permOp (D.eventPerm E ω j) v)) := by
  set ansM := E'.answerAfter ω'
  set S := D.endSet F b Q s j ∩ D.Good b j
  have hinv : ∀ (π : Equiv.Perm (GameReg W n X Y Req Resp m)), (∀ g, (π g).1 = g.1) →
      ∀ g ∈ S, π g ∈ S := fun π hπ g hg => by
    have h1 : (π g).1 = g.1 := hπ g
    simp only [S, endSet, Good, Set.mem_inter_iff, Set.mem_setOf_eq] at hg ⊢
    rw [h1]
    exact hg
  have hu : Supported S (permOp (D.qstep F b Q ansM H s j) (permOp (D.partQ F b Q H s j) v)) :=
    (hv.permOp (hinv _ fun g => rfl)).permOp (hinv _ fun g => rfl)
  have hstep1 := permOp_pushV hu (π := E.requestPerm D.kind ω ⟨j, hj⟩)
    (π' := liftL (finalizePerm F b Q)) (f := D.place F b Q ansM H (s + 1) j)
    (f' := placeMid F b Q H ansM (s + 1) (j + 1)) fun g hg =>
      D.finalize_place_end F b Q H E ω ansM hR hj hs g (hg.2.2 ⟨j, hj⟩ le_rfl) hg.1.2 hg.2.1
  rw [hstep1, ← permOp_trans, ← permOp_trans]
  have hev : permOp ((D.partQ F b Q H s j).trans ((D.qstep F b Q ansM H s j).trans
      (E.requestPerm D.kind ω ⟨j, hj⟩))) v = permOp (D.eventPerm E ω j) v :=
    hv.permOp_eq fun g hg => (D.eventPerm_end F b Q H E ω hO ansM hj g (by
      have := hg.1.2
      have := F.blkLen_pos n hn (D.blkKind b Q j g.1)
      omega) hg.1.2 hg.2.1).symm
  rw [hev]
  set L : Set (LogReg Req m) :=
    {lg | F.startAt n b Q (logEntries (j + 1) lg) (j + 1) = s + 1}
  have hL : Supported (logsIn L) (permOp (D.eventPerm E ω j) v) := hv.permOp fun g hg => by
    show F.startAt n b Q (logEntries (j + 1) (D.eventPerm E ω j g).1.2.2.2) (j + 1) = s + 1
    rw [D.logEntries_eventPerm Q E ω hj g (hg.2.2 ⟨j, hj⟩ le_rfl), F.startAt_succ, hg.1.2]
    rfl
  have hctrl := D.logControlled_ctrlStep_pushV F b Q hL (k := j + 1)
    (logRest F b Q H ansM (s + 1) (j + 1)) (logLog F b Q H ansM (s + 1) (j + 1))
    fun lg hlg => ctrlCond_placeMid (n := n) F b Q H ansM (by omega) hs lg hlg
  unfold placeMid
  rw [hctrl]
  have hL' : Supported (logsIn L) (D.liftedStep (j + 1) (permOp (D.eventPerm E ω j) v)) :=
    hL.logControlled _
  rw [permOp_pushV hL' (π := Equiv.refl _)
    (f := placeOfLogs F (logRest F b Q H ansM (s + 1) (j + 1)) (logLog F b Q H ansM (s + 1) (j + 1)))
    (f' := D.place F b Q ansM H (s + 1) (j + 1))
    fun g hg => D.record_placeMid F b Q H hn ansM (by omega) hs g hg, permOp_refl']

/-- **The start of a block at stage `j + 1`** comes from the end of a block at stage `j`. -/
theorem mask_startSet_stage (bud : D.Budget b) {s j : ℕ} (hj : j < m) :
    mask (D.startSet F b Q (s + 1) (j + 1)) (D.stage E ω (j + 1)) =
      D.liftedStep (j + 1) (permOp (D.eventPerm E ω j) (mask (D.endSet F b Q s j)
        (D.stage E ω j))) := by
  set L : Set (LogReg Req m) :=
    {lg | F.startAt n b Q (logEntries (j + 1) lg) (j + 1) = s + 1}
  have hset : D.startSet F b Q (s + 1) (j + 1) = logsIn L := by
    ext g
    simp only [startSet, Set.mem_setOf_eq, mem_logsIn, L,
      D.blkStart_succ_eq F b Q (j := j) (by omega)]
    rfl
  rw [D.stage_succ, hset]
  unfold Distinguisher.liftedStep
  rw [mask_logControlled]
  congr 1
  refine mask_permOp_of_supported (D.stage_supported_good b Q E ω bud hj.le) fun g hg => ?_
  simp only [mem_logsIn, L, Set.mem_setOf_eq, endSet]
  change F.startAt n b Q (logEntries (j + 1) (D.eventPerm E ω j g).1.2.2.2) (j + 1) = s + 1 ↔ _
  rw [D.logEntries_eventPerm Q E ω hj g (hg.2 ⟨j, hj⟩ le_rfl), F.startAt_succ]
  exact ⟨fun h => ⟨hj, h.symm⟩, fun h => h.2.symm⟩

/-- **The part at the next sub-slot**: the continuing part with the scheduled pair query made, and
the basis states whose block starts at the next sub-slot. -/
theorem piece_succ (hn : 0 < n) (ansM : List Req' → Req' → Option Resp') {s j : ℕ} :
    D.piece F b Q H E ω (s + 1) j =
      permOp (D.qstep F b Q ansM H s j) (mask (D.endSet F b Q s j)ᶜ (D.piece F b Q H E ω s j)) +
        mask (D.startSet F b Q (s + 1) j) (D.stage E ω j) := by
  unfold piece
  set w := D.stage E ω j
  have hU : D.inBlock F b Q (s + 1) j =
      (D.inBlock F b Q s j ∩ (D.endSet F b Q s j)ᶜ) ∪ D.startSet F b Q (s + 1) j := by
    ext g
    have hl := F.blkLen_pos n hn (D.blkKind b Q j g.1)
    simp only [inBlock, endSet, startSet, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
      Set.mem_setOf_eq, not_and]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h : D.blkStart F b Q j g.1 = s + 1
      · exact Or.inr h
      · refine Or.inl ⟨⟨by omega, fun hjm => by have := h2 hjm; omega⟩, fun hjm => by
          have := h2 hjm; omega⟩
    · rintro (⟨⟨h1, h2⟩, h3⟩ | h)
      · exact ⟨by omega, fun hjm => by have := h2 hjm; have := h3 hjm; omega⟩
      · exact ⟨by omega, fun _ => by omega⟩
  rw [hU, mask_union_of_disjoint (fun g h1 h2 => by
    have := h1.1.1
    simp only [startSet, Set.mem_setOf_eq] at h2
    omega)]
  congr 1
  · rw [mask_inter', Set.inter_comm (D.inBlock F b Q s j),
      ← mask_permOp_of_inv (π := D.qstep F b Q ansM H s j) (fun g => Iff.rfl), ← permOp_trans]
    exact mask_permOp_congr (fun g => Iff.rfl) (fun g hg => by
      obtain ⟨c, ps⟩ := g
      exact D.partQ_succ F b Q H ansM c ps hg.2.1) w
  · rw [mask_permOp_congr (π' := Equiv.refl _) (fun g => Iff.rfl) (fun g hg => by
      obtain ⟨c, ps⟩ := g
      exact D.partQ_start F b Q H c ps (le_of_eq hg.symm)) w, permOp_refl']

theorem logControlled_const_trans {W' : Type} [Fintype W'] {n' m' : ℕ} {Req'' A : Type}
    [Fintype Req''] [Fintype A]
    (U V : QState (DReg W' n' X Y Req'' A) ≃ₗᵢ[ℂ] QState (DReg W' n' X Y Req'' A))
    (v : QState (GameReg W' n' X Y Req'' A m')) :
    logControlled (fun _ => U.trans V) v = logControlled (fun _ => V) (logControlled (fun _ => U) v) :=
  logControlled_trans (fun _ => V) (fun _ => U) v

/-- **The first step of the relayed distinguisher**: the distinguisher's first step, the record of
slot `0` and the set-up of sub-slot `0`. -/
theorem relay_liftedStep_zero (v : QState (GameReg (RelayW (DReg W n X Y Req Resp) Req Resp' X Y m
    (relaySlots n m F) (Fin F.qS → Ys)) 1 X Y Req' Resp' (relaySlots n m F))) :
    (D.relay F b Q).liftedStep 0 v = permOp (liftL (setupPerm F b Q))
      (permOp (liftL (recordPerm F b Q D.kind)) (logControlled (fun _ => D.ctrlStep F b Q) v)) := by
  unfold Distinguisher.liftedStep Distinguisher.stepAt
  rw [dif_pos (Nat.succ_pos _)]
  simp only [relay, Nat.cast_zero, ↓reduceIte]
  rw [logControlled_const_trans, logControlled_const_trans, logControlled_const_trans,
    logControlled_permOp, logControlled_permOp, logControlled_refl]

/-- **A later step of the relayed distinguisher**: the tear-down, the clock, the side additions,
the reply, the distinguisher's step, the record and the set-up. -/
theorem relay_liftedStep_succ {k : ℕ} (hk : k + 1 ≤ relaySlots n m F)
    (v : QState (GameReg (RelayW (DReg W n X Y Req Resp) Req Resp' X Y m
    (relaySlots n m F) (Fin F.qS → Ys)) 1 X Y Req' Resp' (relaySlots n m F))) :
    (D.relay F b Q).liftedStep (k + 1) v = permOp (liftL (setupPerm F b Q))
      (permOp (liftL (recordPerm F b Q D.kind)) (logControlled (fun _ => D.ctrlStep F b Q)
        (permOp (liftL (finalizePerm F b Q)) (permOp (liftL (sideAddsPerm F b Q))
          (permOp (liftL (tickPerm F)) (permOp (liftL (teardownPerm F b Q)) v)))))) := by
  unfold Distinguisher.liftedStep Distinguisher.stepAt
  rw [dif_pos (by omega)]
  simp only [relay, Nat.add_one_ne_zero, ↓reduceIte]
  rw [logControlled_const_trans, logControlled_const_trans, logControlled_const_trans,
    logControlled_permOp, logControlled_permOp, logControlled_permOp, liftL_trans, liftL_trans,
    liftL_trans, permOp_trans, permOp_trans, permOp_trans]

/-- The rest of the relayed registers at the start. -/
def restInit : RelayRest X Y Req Req' Resp' m (relaySlots n m F) (Fin F.qS → Ys) :=
  (fun _ => none, fun _ => (none, (default, 0)), fun _ => 0, 0, default, none,
    fun _ => (default, 0))

theorem logRest_zero (ansM : List Req' → Req' → Option Resp') (lg : LogReg Req m) :
    logRest F b Q H ansM 0 0 lg = restInit (n := n) F := by
  simp only [logRest, restInit, logEntries, List.take_zero, List.map_nil,
    MultiRelay.subEntriesL, List.getElem?_nil, Prod.mk.injEq, true_and]
  refine ⟨funext fun t => by simp [blankEntry], funext fun t => by simp [MultiRelay.sched],
    Fin.ext (by simp), trivial⟩

theorem logLog_zero (ansM : List Req' → Req' → Option Resp') (lg : LogReg Req m) :
    logLog (n := n) F b Q H ansM 0 0 lg = fun _ => none := by
  funext t
  simp [logLog, logEntries, MultiRelay.subEntriesL, blankEntry]

theorem gameInit_apply' {W' : Type} [Fintype W'] {n' m' : ℕ} {Req'' A : Type} [Fintype Req'']
    [Fintype A] [DecidableEq Req''] [DecidableEq A] (D' : Distinguisher W' X Y Req'' A n' m')
    (d : DReg W' n' X Y Req'' A) (lg : LogReg Req'' m') :
    D'.gameInit (splitLogs.symm (d, lg)) = if lg = (fun _ => none) then D'.init d else 0 := by
  simp [gameInit]

/-- **The initial state of the relayed distinguisher** is the distinguisher's initial state
pushed along the placement at the start. -/
theorem gameInit_relay (ansM : List Req' → Req' → Option Resp') :
    (D.relay F b Q).gameInit = pushV (placeMid F b Q H ansM 0 0) D.gameInit := by
  classical
  set split := relaySplit W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys)
  ext r'
  obtain ⟨d', lg', rfl⟩ : ∃ d' lg', r' = splitLogs.symm (d', lg') :=
    ⟨(splitLogs r').1, (splitLogs r').2, by simp⟩
  obtain ⟨i, rest, rfl⟩ : ∃ i rest, d' = split.symm (i, rest) := ⟨(split d').1, (split d').2, by simp⟩
  unfold placeMid
  rw [pushV_placeOfLogs_apply, gameInit_apply']
  simp only [logRest_zero, logLog_zero, gameInit_apply']
  have hinit : ∀ d, relayInit F d = split.symm (d, restInit (n := n) F) := fun d => rfl
  by_cases hc : restInit (n := n) F = rest ∧ (fun _ => none) = lg'
  · obtain ⟨rfl, rfl⟩ := hc
    rw [if_pos rfl]
    simp only [and_self, Finset.sum_ite_eq']
    rw [show (D.relay F b Q).init = embV (relayInit F) D.init from rfl, ← hinit,
      embV_apply_self (relayInit_injective F)]
    simp
  · have hz : univ.filter (fun lg : LogReg Req m => restInit (n := n) F = rest ∧
        (fun _ => none) = lg') = ∅ := Finset.filter_eq_empty_iff.2 fun _ _ h => hc h
    rw [hz, Finset.sum_empty]
    by_cases hl : (fun _ => none) = lg'
    · have hr : restInit (n := n) F ≠ rest := fun h => hc ⟨h, hl⟩
      rw [if_pos hl.symm, show (D.relay F b Q).init = embV (relayInit F) D.init from rfl]
      refine embV_apply_of_notMem _ ?_
      rintro ⟨d, hd⟩
      rw [hinit] at hd
      exact hr (congrArg Prod.snd (split.symm.injective hd))
    · rw [if_neg (fun h => hl h.symm)]

theorem piece_eq_stage {s j : ℕ} (hin : ∀ g : GameReg W n X Y Req Resp m, g ∈ D.inBlock F b Q s j)
    (hp : ∀ c ps, D.partQ F b Q H s j (c, ps) = (c, ps)) :
    D.piece F b Q H E ω s j = D.stage E ω j := by
  unfold piece
  rw [(show Supported (D.inBlock F b Q s j) (permOp (D.partQ F b Q H s j) (D.stage E ω j)) from
    fun g hg => absurd (hin g) hg).mask_eq_self]
  rw [(show Supported Set.univ (D.stage E ω j) from fun _ h => absurd trivial h).permOp_eq
    (π' := Equiv.refl _) fun g _ => by obtain ⟨c, ps⟩ := g; exact hp c ps, permOp_refl']

theorem piece_eq_zero {s j : ℕ} (hin : ∀ g : GameReg W n X Y Req Resp m, g ∉ D.inBlock F b Q s j) :
    D.piece F b Q H E ω s j = 0 :=
  mask_of_empty hin _

/-- **The relayed distinguisher at its start**. -/
theorem relay_stage_zero (hn : 0 < n) (ansM : List Req' → Req' → Option Resp') :
    (D.relay F b Q).stage E' ω' 0 = permOp (liftL (setupPerm F b Q))
      (∑ j ∈ range (m + 1), pushV (D.place F b Q ansM H 0 j) (D.piece F b Q H E ω 0 j)) := by
  change (D.relay F b Q).liftedStep 0 (D.relay F b Q).gameInit = _
  rw [D.relay_liftedStep_zero, D.gameInit_relay F b Q H ansM]
  unfold placeMid
  rw [D.logControlled_ctrlStep_pushV F b Q (L := Set.univ) (fun _ h => absurd trivial h) (k := 0)
    (logRest F b Q H ansM 0 0) (logLog F b Q H ansM 0 0)
    fun lg _ => ctrlCond_placeMid (n := n) F b Q H ansM (Nat.zero_le _) (Nat.zero_le _) lg rfl]
  rw [permOp_pushV (S := Set.univ) (fun _ h => absurd trivial h) (π := Equiv.refl _)
    (f := placeOfLogs F (logRest F b Q H ansM 0 0) (logLog F b Q H ansM 0 0))
    (f' := D.place F b Q ansM H 0 0)
    fun g _ => D.record_placeMid F b Q H hn ansM (Nat.zero_le _) (Nat.zero_le _) g rfl, permOp_refl']
  congr 1
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun j _ => by
    rw [D.piece_eq_zero F b Q H E ω fun g hg => by
      have := F.le_startAt n b Q hn (D.stEntries (j + 1) g.1) (j + 1)
      have := hg.1
      unfold blkStart at this
      omega, pushV_zero], zero_add]
  rw [D.piece_eq_stage F b Q H E ω (fun g => ⟨Nat.zero_le _, fun _ => by
      have := F.blkLen_pos n hn (D.blkKind b Q 0 g.1)
      simp [blkStart, MultiRelay.startAt]
      omega⟩)
    fun c ps => D.partQ_start F b Q H c ps (Nat.zero_le _)]
  rfl

/-- **The pieces at the last sub-slot** sum to the last stage of `D` pushed along the final
placement. -/
theorem sum_pieces_last (ansM : List Req' → Req' → Option Resp') :
    ∑ j ∈ range (m + 1), pushV (D.place F b Q ansM H (relaySlots n m F) j)
        (D.piece F b Q H E ω (relaySlots n m F) j) =
      pushV (D.place F b Q ansM H (relaySlots n m F) m) (D.stage E ω m) := by
  rw [Finset.sum_range_succ, Finset.sum_eq_zero fun j hj => by
    have hjm : j < m := Finset.mem_range.1 hj
    rw [D.piece_eq_zero F b Q H E ω fun g hg => by
      have h1 := hg.2 hjm
      have h2 := F.startAt_le n b Q (D.stEntries j g.1) (j + 1)
      rw [F.startAt_succ] at h2
      have h3 : (j + 1) * max n F.len ≤ m * max n F.len := Nat.mul_le_mul_right _ hjm
      unfold blkStart blkKind at h1
      unfold relaySlots at h1
      omega, pushV_zero], zero_add]
  rw [D.piece_eq_stage F b Q H E ω (fun g => ⟨by
      have := F.startAt_le n b Q (D.stEntries m g.1) m
      exact this, fun h => absurd h (lt_irrefl _)⟩)
    fun c ps => by
      rw [D.partQ_apply]
      refine Prod.ext rfl (funext fun i => Prod.ext rfl ?_)
      simp]

/-- **The run of the relayed distinguisher, sub-slot by sub-slot**: after step `s` its state is
the set-up of the parts of the stages of `D` pushed along the placements at `s`. -/
theorem relay_stage (hn : 0 < n) (bud : D.Budget b)
    (hO : ∀ lg : LogReg Req m, E.oracle ω lg = H)
    (hO' : ∀ lg' : LogReg Req' (relaySlots n m F), E'.oracle ω' lg' = H)
    (hR : ∀ (rs : List Req) (r : Req), rs.length < Q →
      E.answerAfter ω rs r = F.runReply (E'.answerAfter ω') H r (F.mainReqs Q (E'.answerAfter ω') H rs)) :
    ∀ s ≤ relaySlots n m F, (D.relay F b Q).stage E' ω' s = permOp (liftL (setupPerm F b Q))
      (∑ j ∈ range (m + 1), pushV (D.place F b Q (E'.answerAfter ω') H s j)
        (D.piece F b Q H E ω s j)) := by
  set ansM := E'.answerAfter ω'
  intro s hs
  induction s with
  | zero => exact D.relay_stage_zero F b Q H E' ω' E ω hn ansM
  | succ s ih =>
    rw [Distinguisher.stage_succ, ih (by omega), D.relay_liftedStep_succ F b Q hs]
    congr 1
    simp only [map_sum]
    -- each part, sub-slot `s`
    have hpart : ∀ j ∈ range (m + 1),
        permOp (liftL (recordPerm F b Q D.kind)) (logControlled (fun _ => D.ctrlStep F b Q)
          (permOp (liftL (finalizePerm F b Q)) (permOp (liftL (sideAddsPerm F b Q))
            (permOp (liftL (tickPerm F))
            (permOp (liftL (teardownPerm F b Q)) (permOp ((D.relay F b Q).eventPerm E' ω' s)
              (permOp (liftL (setupPerm F b Q)) (pushV (D.place F b Q ansM H s j)
                (D.piece F b Q H E ω s j))))))))) =
          pushV (D.place F b Q ansM H (s + 1) j) (permOp (D.qstep F b Q ansM H s j)
            (mask (D.endSet F b Q s j)ᶜ (D.piece F b Q H E ω s j))) +
          (if j < m then pushV (D.place F b Q ansM H (s + 1) (j + 1))
            (mask (D.startSet F b Q (s + 1) (j + 1)) (D.stage E ω (j + 1))) else 0) := by
      intro j hj
      have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have hsup := D.piece_supported F b Q H E ω bud (s := s) hjm
      rw [D.stepA F b Q H E' ω' hO' hjm (by omega) (hsup.mono Set.inter_subset_left)]
      conv_lhs => rw [← mask_add_mask_compl (D.endSet F b Q s j)ᶜ (D.piece F b Q H E ω s j),
        compl_compl]
      rw [map_add, pushV_add, map_add, map_add, map_add]
      congr 1
      · refine D.stepCont F b Q H hn ansM hjm hs ?_
        have hsup' : Supported (D.inBlock F b Q s j ∩ (D.endSet F b Q s j)ᶜ)
            (mask (D.endSet F b Q s j)ᶜ (D.piece F b Q H E ω s j)) := fun g hg => by
          by_cases hE : g ∈ (D.endSet F b Q s j)ᶜ
          · rw [mask_apply_of_mem _ hE]
            exact hsup g fun h => hg ⟨h.1, hE⟩
          · rw [mask_apply_of_notMem _ hE]
        exact hsup'.permOp fun r hr => hr
      · split_ifs with hjm'
        · have hmask : mask (D.endSet F b Q s j) (D.piece F b Q H E ω s j) =
              permOp (D.partQ F b Q H s j) (mask (D.endSet F b Q s j) (D.stage E ω j)) := by
            unfold piece
            rw [mask_inter', show D.endSet F b Q s j ∩ D.inBlock F b Q s j = D.endSet F b Q s j by
              ext g
              constructor
              · exact fun h => h.1
              · intro h
                refine ⟨h, ?_, fun _ => ?_⟩
                · have := h.2
                  have := F.blkLen_pos n hn (D.blkKind b Q j g.1)
                  omega
                · have := h.2
                  omega,
              mask_permOp_of_inv (fun g => Iff.rfl)]
          rw [hmask, D.stepEnd F b Q H E' ω' E ω hn hO hR hjm' hs (fun g hg => by
              by_cases h1 : g ∈ D.endSet F b Q s j
              · rw [mask_apply_of_mem _ h1]
                exact D.stage_supported_good b Q E ω bud hjm g fun h2 => hg ⟨h1, h2⟩
              · rw [mask_apply_of_notMem _ h1]),
            D.mask_startSet_stage F b Q E ω bud hjm']
        · have hempty : ∀ g : GameReg W n X Y Req Resp m, g ∉ D.endSet F b Q s j :=
            fun g hg => hjm' hg.1
          rw [mask_of_empty hempty, map_zero, pushV_zero, map_zero, map_zero, map_zero]
    rw [Finset.sum_congr rfl hpart, Finset.sum_add_distrib]
    simp only [D.piece_succ F b Q H E ω hn ansM, pushV_add, Finset.sum_add_distrib]
    congr 1
    conv_lhs => rw [Finset.sum_range_succ, if_neg (lt_irrefl m), add_zero]
    conv_rhs => rw [Finset.sum_range_succ']
    have h0 : mask (D.startSet F b Q (s + 1) 0) (D.stage E ω 0) = 0 :=
      mask_of_empty (fun g hg => by
        simp only [startSet, blkStart, MultiRelay.startAt, Finset.range_zero, Finset.sum_empty,
          Set.mem_setOf_eq] at hg
        omega) _
    rw [h0, pushV_zero, add_zero]
    exact Finset.sum_congr rfl fun j hj => by rw [if_pos (Finset.mem_range.1 hj)]

/-- **The run of the relayed distinguisher** (module docstring): its final state against the main
environment is the set-up of the final state of `D` against the outer environment, pushed along
the final placement. -/
theorem run_relay (hn : 0 < n) (bud : D.Budget b)
    (hO : ∀ lg : LogReg Req m, E.oracle ω lg = H)
    (hO' : ∀ lg' : LogReg Req' (relaySlots n m F), E'.oracle ω' lg' = H)
    (hR : ∀ (rs : List Req) (r : Req), rs.length < Q →
      E.answerAfter ω rs r = F.runReply (E'.answerAfter ω') H r (F.mainReqs Q (E'.answerAfter ω') H rs)) :
    (D.relay F b Q).run E' ω' = permOp (liftL (setupPerm F b Q))
      (pushV (D.place F b Q (E'.answerAfter ω') H (relaySlots n m F) m) (D.run E ω)) := by
  unfold Distinguisher.run
  rw [D.relay_stage F b Q H E' ω' E ω hn bud hO hO' hR _ le_rfl, D.sum_pieces_last]

/-- The final placement keeps the distinguisher's registers and records all its logs, so it is
injective. -/
theorem place_last_injective (ansM : List Req' → Req' → Option Resp') :
    Function.Injective (D.place F b Q ansM H (relaySlots n m F) m) := by
  intro g g' h
  have h1 := congrArg (fun r => (splitLogs r).1.1.1.inner) h
  have h2 := congrArg (fun r => (splitLogs r).1.1.1.record) h
  simp only [place, Equiv.apply_symm_apply] at h1 h2
  have hlen : ∀ c : W × Req × Option Resp × LogReg Req m, (D.stEntries m c).length ≤ m :=
    fun c => by rw [D.length_stEntries le_rfl]; simp
  have hl : logEntries m g.1.2.2.2 = logEntries m g'.1.2.2.2 := by
    rw [← D.stEntries_self, ← D.stEntries_self,
      ← MultiRelay.recList_getElem? (D.stEntries m g.1) (hlen _),
      ← MultiRelay.recList_getElem? (D.stEntries m g'.1) (hlen _), h2]
  have hlg : g.1.2.2.2 = g'.1.2.2.2 := by
    funext k
    have := congrArg (fun l => l[(k : ℕ)]?) hl
    simp only [logEntries, List.getElem?_map, List.getElem?_take_of_lt k.2,
      List.getElem?_eq_getElem (show (k : ℕ) < (List.finRange m).length by simp)] at this
    simpa using this
  rw [← splitLogs.symm_apply_apply g, ← splitLogs.symm_apply_apply g']
  congr 1
  exact Prod.ext h1 hlg

/-- **Events of the relayed distinguisher's run** have the probability, against the outer
environment, of their preimage under the final placement and the set-up. -/
theorem prob_final_relay (hn : 0 < n) (bud : D.Budget b)
    (hO : ∀ lg : LogReg Req m, E.oracle ω lg = H)
    (hO' : ∀ lg' : LogReg Req' (relaySlots n m F), E'.oracle ω' lg' = H)
    (hR : ∀ (rs : List Req) (r : Req), rs.length < Q →
      E.answerAfter ω rs r = F.runReply (E'.answerAfter ω') H r (F.mainReqs Q (E'.answerAfter ω') H rs))
    (S : Set (GameReg (RelayW (DReg W n X Y Req Resp) Req Resp' X Y m (relaySlots n m F) (Fin F.qS →
        Ys)) 1 X Y
        Req'
      Resp' (relaySlots n m F))) :
    prob S ((D.relay F b Q).final E' noPost ω') =
      prob ((fun g => liftL (setupPerm F b Q) (D.place F b Q (E'.answerAfter ω') H
        (relaySlots n m F) m g)) ⁻¹' S) (D.final E noPost ω) := by
  simp only [final, noPost, logControlled_refl]
  rw [D.run_relay F b Q H E' ω' E ω hn bud hO hO' hR, prob_permOp' (liftL (setupPerm F b Q)),
    prob_pushV (S := Set.univ) (fun _ h => absurd trivial h)
      (fun g _ g' _ h => D.place_last_injective F b Q H _ h)]
  congr 1

/-! ### The query budget of the relayed run -/

/-- **At most `n b + Q qR + Q qP` query sub-slots before any sub-slot.** -/
theorem noneCount_subEntries_le (ansM : List Req' → Req' → Option Resp') (s j : ℕ)
    (c : W × Req × Option Resp × LogReg Req m) :
    MultiRelay.noneCount (D.subEntries F b Q ansM H s j c) ≤ n * b + Q * F.qR + Q * F.qP := by
  unfold subEntries MultiRelay.subEntriesL
  refine (MultiRelay.noneCount_take_le _ _).trans ?_
  rw [F.noneCount_tailEntries]
  refine (F.noneCount_sched_le n b Q ansM H _).trans ?_
  have h1 : n * min ((D.stEntries j c).countP Option.isNone) b ≤ n * b :=
    Nat.mul_le_mul_left _ (min_le_right _ _)
  have h2 : (F.qR + F.qP) * min ((D.stEntries j c).countP Option.isSome) Q ≤
      (F.qR + F.qP) * Q := Nat.mul_le_mul_left _ (min_le_right _ _)
  have h3 : (F.qR + F.qP) * Q = Q * F.qR + Q * F.qP := by ring
  omega

/-- **Fewer than `n b + Q qR + Q qP` query sub-slots before a query sub-slot.** -/
theorem noneCount_subEntries_lt (ansM : List Req' → Req' → Option Resp') {s j : ℕ}
    (c : W × Req × Option Resp × LogReg Req m) (h0 : D.blkStart F b Q j c ≤ s)
    (h1 : j < m → s < D.blkStart F b Q j c + F.blkLen n (D.blkKind b Q j c))
    (hq : (D.schedAct F b Q ansM H s j c).isAsk = false) :
    MultiRelay.noneCount (D.subEntries F b Q ansM H s j c) < n * b + Q * F.qR + Q * F.qP := by
  have hjm : j < m := by
    by_contra hjm
    simp [schedAct, hjm, SubAct.isAsk] at hq
  have hj := hjm.le
  have h1' := h1 hjm
  have hout := D.sched_stEntries F b Q ansM H hjm c
  have hlen := D.length_sched_take F b Q ansM H hj c
  set st := F.sched n b Q ansM H ((D.stEntries j c).take j) with hst_def
  have hso : s < (F.sched n b Q ansM H (D.stEntries j c)).out.length := by
    rw [D.length_sched_stEntries F b Q ansM H hjm]
    exact h1'
  have hpre : D.subEntries F b Q ansM H s j c = st.out ++
      (F.blockOf n b Q ansM H st ((D.stEntries j c).getD j none)).take
        (s - D.blkStart F b Q j c) := by
    unfold subEntries MultiRelay.subEntriesL
    rw [F.take_tailEntries_of_le ansM _ s hso.le, hout, List.take_append,
      List.take_of_length_le (by rw [hlen]; omega), hlen]
  rw [hpre, MultiRelay.noneCount_append]
  have hst := F.noneCount_sched_le n b Q ansM H ((D.stEntries j c).take j)
  have hqb := (F.sched_qb_rb n b Q ansM H ((D.stEntries j c).take j)).1
  have hrb := (F.sched_qb_rb n b Q ansM H ((D.stEntries j c).take j)).2
  rw [← hst_def] at hst hqb hrb
  have hblk := D.blkKind_eq F b Q ansM H hjm c
  rw [← hst_def] at hblk
  unfold schedAct at hq
  simp only [hjm, ↓reduceIte] at hq
  rcases hk : D.blkKind b Q j c with _ | _ | _ <;> rw [hk] at hq hblk h1' <;>
    rcases he : (D.stEntries j c).getD j none with _ | r <;> rw [he] at hq hblk
  · -- a query block: the pairs below the sub-slot
    have hqb' : st.qb < b := by
      by_contra hc
      simp [MultiRelay.blk, hc] at hblk
    simp only [MultiRelay.blkLen] at h1'
    simp only [MultiRelay.blockOf, hqb', ↓reduceIte, List.take_replicate]
    have : MultiRelay.noneCount (List.replicate (min (s - D.blkStart F b Q j c) n)
        ((none, (none, (default, 0))) : Option Req' × (Option Resp' × (X × Y)))) =
        min (s - D.blkStart F b Q j c) n := by
      simp [MultiRelay.noneCount, List.countP_replicate]
    rw [this]
    have h3 : n * min ((D.stEntries j c).take j |>.countP Option.isNone) b ≤ n * (b - 1) :=
      Nat.mul_le_mul_left _ (by rw [← hqb]; omega)
    have h4 : (F.qR + F.qP) * min ((D.stEntries j c).take j |>.countP Option.isSome) Q ≤
        (F.qR + F.qP) * Q := Nat.mul_le_mul_left _ (min_le_right _ _)
    have h4' : (F.qR + F.qP) * Q = Q * F.qR + Q * F.qP := by ring
    have h5 : n * (b - 1) + n = n * b := by
      have : 0 < b := by omega
      rw [← Nat.mul_succ]
      congr 1
      omega
    omega
  · simp [MultiRelay.blk] at hblk
    split_ifs at hblk
  · simp [SubAct.isAsk] at hq
  · simp [SubAct.isAsk] at hq
  · simp [MultiRelay.blk] at hblk
    split_ifs at hblk
  · -- a relayed request: its queries so far
    have hrb' : st.rb < Q := by
      by_contra hc
      simp [MultiRelay.blk, hc] at hblk
    simp only [MultiRelay.blkLen] at h1'
    simp only [MultiRelay.blockOf, hrb', ↓reduceIte, MultiRelay.runEntries]
    set k := s - D.blkStart F b Q j c
    rw [F.take_runAux ansM H (show k ≤ F.len by omega), F.noneCount_runAux]
    have hact : (F.act r (F.runAux ansM H r (st.out.filterMap Prod.fst) k).1).isLeft := by
      rcases ha : F.act r (F.runAux ansM H r (st.out.filterMap Prod.fst) k).1 with x | r'
      · rfl
      · exfalso
        revert hq
        simp only [k] at ha ⊢
        rw [ha]
        simp [SubAct.isAsk]
    have hnq := F.nq_add_np_lt_of_act
      (F.vecSa (F.sideVec (F.runAux ansM H r (st.out.filterMap Prod.fst) F.len).1)) r
      (fun k' => ((F.runAux ansM H r (st.out.filterMap Prod.fst)
      F.len).2.getD k' (none, (none, (default, 0)))).2)
      (i := k) (by omega) (by rw [F.stAt_runAux ansM H r _ (show k ≤ F.len by omega)]; exact hact)
    rw [F.stAt_runAux ansM H r _ (show k ≤ F.len by omega)] at hnq
    have h3 : n * min ((D.stEntries j c).take j |>.countP Option.isNone) b ≤ n * b :=
      Nat.mul_le_mul_left _ (min_le_right _ _)
    have h4 : (F.qR + F.qP) * min ((D.stEntries j c).take j |>.countP Option.isSome) Q ≤
        (F.qR + F.qP) * (Q - 1) := Nat.mul_le_mul_left _ (by rw [← hrb]; omega)
    have h5 : (F.qR + F.qP) * (Q - 1) + (F.qR + F.qP) = Q * F.qR + Q * F.qP := by
      have : 0 < Q := by omega
      obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    omega

theorem relay_kind_setup (r : GameReg (RelayW (DReg W n X Y Req Resp) Req Resp' X Y m
    (relaySlots n m F) (Fin F.qS → Ys)) 1 X Y Req' Resp' (relaySlots n m F)) :
    (D.relay F b Q).kind (liftL (setupPerm F b Q) r).1.1 = (D.relay F b Q).kind r.1.1 := by
  have hw : ∀ d : RelayReg W X Y Req Resp Req' Resp' n m (relaySlots n m F) (Fin F.qS → Ys),
      (setupFun F b Q d).1.1.record = d.1.1.record ∧ (setupFun F b Q d).1.1.store = d.1.1.store ∧
        (setupFun F b Q d).1.1.side = d.1.1.side ∧ (setupFun F b Q d).1.1.time = d.1.1.time :=
    fun d => by
      unfold setupFun
      split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  simp only [relay_kind, liftL_apply, setupPerm]
  change (F.actAt n b Q (setupFun F b Q _).1.1.record (setupFun F b Q _).1.1.store
    (setupFun F b Q _).1.1.side (setupFun F b Q _).1.1.time).isAsk = _
  rw [(hw _).1, (hw _).2.1, (hw _).2.2.1, (hw _).2.2.2]
  rfl

/-- **The relayed run within the budget** `n b + Q qR + Q qP`: after step `s`, every branch has
made at most that many query slots, and fewer before a query slot. -/
theorem relay_stage_count (hn : 0 < n) (bud : D.Budget b)
    (hO : ∀ lg : LogReg Req m, E.oracle ω lg = H)
    (hO' : ∀ lg' : LogReg Req' (relaySlots n m F), E'.oracle ω' lg' = H)
    (hR : ∀ (rs : List Req) (r : Req), rs.length < Q →
      E.answerAfter ω rs r = F.runReply (E'.answerAfter ω') H r (F.mainReqs Q (E'.answerAfter ω') H rs))
    (s : ℕ) (hs : s ≤ relaySlots n m F) :
    Supported {r' | queriesBefore (splitLogs r').2 s ≤ n * b + Q * F.qR + Q * F.qP ∧
      ((D.relay F b Q).kind r'.1.1 = false → queriesBefore (splitLogs r').2 s < n * b + Q * F.qR + Q
          * F.qP)}
      ((D.relay F b Q).stage E' ω' s) := by
  rw [D.relay_stage F b Q H E' ω' E ω hn bud hO hO' hR s hs]
  refine Supported.permOp (B := {r' | queriesBefore (splitLogs r').2 s ≤ n * b + Q * F.qR + Q * F.qP
      ∧
      ((D.relay F b Q).kind r'.1.1 = false → queriesBefore (splitLogs r').2 s < n * b + Q * F.qR + Q
          * F.qP)})
    ?_ fun r hr => ?_
  · refine Supported.sum _ fun j hj => ?_
    have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    refine (D.piece_supported F b Q H E ω bud (s := s) hjm).pushV fun g hg => ?_
    have hL := D.length_subEntries F b Q H (E'.answerAfter ω') s j g.1
    have hq : queriesBefore (splitLogs (D.place F b Q (E'.answerAfter ω') H s j g)).2 s =
        MultiRelay.noneCount (D.subEntries F b Q (E'.answerAfter ω') H s j g.1) := by
      change queriesBefore (fun t : Fin (relaySlots n m F) =>
        ((D.subEntries F b Q (E'.answerAfter ω') H s j g.1).getD t blankEntry).1) s = _
      rw [queriesBefore_ofList _ blankEntry rfl s hs hL.ge, List.take_of_length_le hL.le]
      rfl
    have hk : (D.relay F b Q).kind (D.place F b Q (E'.answerAfter ω') H s j g).1.1 =
        (D.schedAct F b Q (E'.answerAfter ω') H s j g.1).isAsk := by
      rw [relay_kind]
      change (F.actAt n b Q (fun i : Fin m => (D.stEntries j g.1)[(i : ℕ)]?)
        (fun t : Fin (relaySlots n m F) =>
          ((D.subEntries F b Q (E'.answerAfter ω') H s j g.1).getD t blankEntry).2)
        (fun i : Fin m => (D.subSides F b Q (E'.answerAfter ω') H s j g.1).getD i 0)
        (min s (relaySlots n m F))).isAsk = _
      rw [min_eq_left hs, D.actAt_place F b Q (E'.answerAfter ω') H hjm hs g.1 hg.1.1 hg.1.2]
    refine ⟨by rw [hq]; exact D.noneCount_subEntries_le F b Q H _ s j g.1, fun hkf => ?_⟩
    rw [hq]
    rw [hk] at hkf
    exact D.noneCount_subEntries_lt F b Q H _ g.1 hg.1.1 hg.1.2 hkf
  · refine ⟨hr.1, fun hkf => hr.2 ?_⟩
    rwa [D.relay_kind_setup F b Q] at hkf

end Distinguisher

end GordieHowe.Quantum
