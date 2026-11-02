-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.PMFTV
public import GordieHowe.Foundations.ToMathlib.PMFUnion

@[expose] public section

/-!
# The points of rejected attempts, given the reply

`N` attempts run in sequence with independent coins `u a ← p a` (`u ← pi p`): attempt `a` runs
when every earlier attempt rejected (`Runs`), outputs `att a (u a)` (`none` for a rejection), and
has a point `pt a (u a)`. The reply is the output of the first attempt that keeps, or `none`
(`firstKept`, the shape of `firstSome_eq_map_pi` in
`GordieHowe/Foundations/ToMathlib/PMFRejection.lean`). The points of the attempts that ran and
rejected (`rejectedPoints`) are hidden, but correlated with the reply through which attempt was
kept.

- `sum_toReal_pi_mul_eq_sum_update`: redrawing one coordinate of independent coordinates keeps
  their law; `toReal_pi_inter_eq_mul`: a coordinate is independent of an event that ignores it.
- `replyWithout att a`: the reply as if attempt `a` rejected, a function of the other attempts'
  coins (`replyWithout_update`); when attempt `a` rejects, the reply equals it
  (`firstKept_eq_replyWithout`).
- `toReal_pt_rejected_reply_le`: `Pr[pt a (u a) = x ∧ a runs ∧ a rejects ∧ reply = r] ≤
  Pr[pt a (u a) = x] · Pr[replyWithout att a u = r]`.
- `toReal_pt_eq_replyWithout_le`: the point of an attempt is a guess from the reply as if it
  rejected with probability at most `δ`.
- `notKeptPoints`, `firstKept_eq_replyWithout_of_notKept`, `toReal_guess_mem_notKeptPoints_le`,
  `sum_sup'_toReal_notKeptPoints_le`: the same bounds for the points of every attempt that was not
  kept (rejected, or not run because an earlier attempt kept): the reply is the reply as if that
  attempt rejected.
- `toReal_guess_mem_rejectedPoints_le`: for `δ` bounding the probability of each point of each
  attempt, every guess `g (reply)` is a rejected point with probability at most `N δ`, with no
  lower bound on the probability of keeping; `sum_sup'_toReal_rejectedPoints_le`: the same as
  `∑ r, max_x Pr[x ∈ rejectedPoints ∧ reply = r] ≤ N δ`.
- `toReal_pt_eq_of_update_le`, `toReal_guess_mem_of_alternatives`: the point of an attempt is a
  guess ignoring its coins with probability at most `δ`; a guess from any reply is a hidden point
  with probability at most `|ι| K δ` when, at each hidden point, the reply is one of `K`
  alternatives ignoring the coins of that point's attempt (attempts indexed by a finite type `ι`).
- `toReal_uniform_le_of_overwrite`: a bound for every value of the rest of a uniform law, over
  uniform coordinates written into it, is a bound over the uniform law.
- `callOutcome`, `loopOut`, `KeptAt`, `loopOut_of_keptAt`, `exists_loopOut_mem_range_of_not_keptAt`:
  `k` calls of `T` attempts with a keep test per call; varying the mask of an attempt not kept,
  the reply takes at most two values, the same for every mask;
  `exists_keptAt_of_loopOut_eq_some`: an output is the output of a kept attempt;
  `toReal_guess_mem_loopPoints_le`: a guess from the reply is the point of an attempt not kept with
  probability at most `k T 2 δ`.

About Mathlib objects and `PMF.pi` (`GordieHowe/Foundations/ToMathlib/PMFTV.lean`) only.
-/

open Finset
open scoped BigOperators

namespace PMF

/-! ### Redrawing one coordinate of a product -/

section Resample

variable {ι U : Type*} [Fintype ι] [DecidableEq ι] [Fintype U]

/-- **Redrawing one coordinate of independent coordinates keeps their law**: averaging `f` over
`u ← pi p` is averaging, over `u ← pi p` and `a ← p c`, the value of `f` at `u` with
coordinate `c` replaced by `a`. -/
theorem sum_toReal_pi_mul_eq_sum_update (p : ι → PMF U) (c : ι) (f : (ι → U) → ℝ) :
    ∑ u, (pi p u).toReal * f u =
      ∑ u, (pi p u).toReal * ∑ a, (p c a).toReal * f (Function.update u c a) := by
  have hprod : ∀ u a, (pi p u).toReal * (p c a).toReal =
      (pi p (Function.update u c a)).toReal * (p c (u c)).toReal := by
    intro u a
    have h2 : ∏ i ∈ {c}ᶜ, (p i (Function.update u c a i)).toReal = ∏ i ∈ {c}ᶜ, (p i (u i)).toReal :=
      prod_congr rfl fun i hi => by rw [Function.update_of_ne (by simpa using hi)]
    rw [toReal_pi_apply, toReal_pi_apply, Fintype.prod_eq_mul_prod_compl c,
      Fintype.prod_eq_mul_prod_compl c (fun i => (p i (Function.update u c a i)).toReal),
      Function.update_self, h2]
    ring
  let e : (ι → U) × U ≃ (ι → U) × U :=
    { toFun := fun q => (Function.update q.1 c q.2, q.1 c)
      invFun := fun q => (Function.update q.1 c q.2, q.1 c)
      left_inv := fun q => by ext <;> simp
      right_inv := fun q => by ext <;> simp }
  calc ∑ u, (pi p u).toReal * f u
      = ∑ q : (ι → U) × U, (pi p q.1).toReal * ((p c q.2).toReal * f q.1) := by
        rw [Fintype.sum_prod_type]
        refine sum_congr rfl fun u _ => ?_
        dsimp only
        rw [← mul_sum, ← sum_mul, sum_toReal, one_mul]
    _ = ∑ q : (ι → U) × U, (pi p (e q).1).toReal * ((p c (e q).2).toReal * f (e q).1) :=
        (e.sum_comp (fun q => (pi p q.1).toReal * ((p c q.2).toReal * f q.1))).symm
    _ = ∑ u, (pi p u).toReal * ∑ a, (p c a).toReal * f (Function.update u c a) := by
        rw [Fintype.sum_prod_type]
        refine sum_congr rfl fun u _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun a _ => ?_
        simp only [e, Equiv.coe_fn_mk]
        rw [← mul_assoc, ← hprod, mul_assoc]

/-- **A coordinate is independent of an event that ignores it.** -/
theorem toReal_pi_inter_eq_mul (p : ι → PMF U) (c : ι) (F : Set U) (G : Set (ι → U))
    (hG : ∀ u a, Function.update u c a ∈ G ↔ u ∈ G) :
    ((pi p).toOuterMeasure {u | u c ∈ F ∧ u ∈ G}).toReal =
      ((p c).toOuterMeasure F).toReal * ((pi p).toOuterMeasure G).toReal := by
  classical
  rw [toReal_toOuterMeasure_apply, toReal_toOuterMeasure_apply, toReal_toOuterMeasure_apply]
  have h := sum_toReal_pi_mul_eq_sum_update p c
    (fun u => if u c ∈ F ∧ u ∈ G then (1 : ℝ) else 0)
  calc ∑ u, (if u ∈ {u | u c ∈ F ∧ u ∈ G} then (pi p u).toReal else 0)
      = ∑ u, (pi p u).toReal * (if u c ∈ F ∧ u ∈ G then (1 : ℝ) else 0) :=
        sum_congr rfl fun u _ => by
          simp only [Set.mem_ofPred_eq]
          split_ifs <;> simp
    _ = ∑ u, (pi p u).toReal * ∑ a, (p c a).toReal *
          (if Function.update u c a c ∈ F ∧ Function.update u c a ∈ G then (1 : ℝ) else 0) := h
    _ = ∑ u, (if u ∈ G then (pi p u).toReal else 0) *
          ∑ a, (if a ∈ F then (p c a).toReal else 0) := by
        refine sum_congr rfl fun u _ => ?_
        simp only [Function.update_self, hG]
        by_cases hu : u ∈ G
        · simp only [hu, and_true, ↓reduceIte]
          congr 1
          exact sum_congr rfl fun a _ => by split_ifs <;> simp
        · simp [hu]
    _ = (∑ a, if a ∈ F then (p c a).toReal else 0) *
          ∑ u, (if u ∈ G then (pi p u).toReal else 0) := by
        rw [← sum_mul, mul_comm]

end Resample

/-! ### Sequential attempts -/

section Attempts

variable {U β X : Type*} {N : ℕ}

/-- **The reply of `N` sequential attempts**: attempt `a` with coins `u a` outputs
`att a (u a)`, `none` for a rejection; the reply is the output of the first attempt that keeps,
or `none` if all reject. -/
def firstKept (att : Fin N → U → Option β) (u : Fin N → U) : Option β :=
  (List.finRange N).findSome? fun a => att a (u a)

/-- **Attempt `a` runs**: every earlier attempt rejected. -/
def Runs (att : Fin N → U → Option β) (u : Fin N → U) (a : Fin N) : Prop :=
  ∀ b < a, att b (u b) = none

/-- **The points of the rejected attempts**: the points `pt a (u a)` of the attempts that ran
and rejected. -/
def rejectedPoints (att : Fin N → U → Option β) (pt : Fin N → U → X) (u : Fin N → U) : Set X :=
  {x | ∃ a, Runs att u a ∧ att a (u a) = none ∧ pt a (u a) = x}

/-- **The reply as if attempt `a` rejected**: the first kept output among the other attempts,
a function of the coins of the other attempts (`replyWithout_update`). -/
def replyWithout (att : Fin N → U → Option β) (a : Fin N) (u : Fin N → U) : Option β :=
  firstKept (fun b => if b = a then fun _ => none else att b) u

/-- The reply as if attempt `a` rejected does not read the coins of attempt `a`. -/
theorem replyWithout_update (att : Fin N → U → Option β) (a : Fin N) (u : Fin N → U) (y : U) :
    replyWithout att a (Function.update u a y) = replyWithout att a u := by
  unfold replyWithout firstKept
  congr 1
  funext b
  by_cases hb : b = a
  · simp [hb]
  · simp [hb]

/-- **When attempt `a` rejects, the reply is the reply as if it rejected.** In particular this
holds when attempt `a` runs and rejects. -/
theorem firstKept_eq_replyWithout (att : Fin N → U → Option β) {a : Fin N} {u : Fin N → U}
    (h : att a (u a) = none) : firstKept att u = replyWithout att a u := by
  unfold replyWithout firstKept
  congr 1
  funext b
  by_cases hb : b = a
  · subst hb
    simp [h]
  · simp [hb]

/-- `findSome?` agrees for two functions that agree on the list's elements. -/
theorem findSome?_congr_mem {α γ : Type*} {l : List α} {f g : α → Option γ}
    (h : ∀ x ∈ l, f x = g x) : l.findSome? f = l.findSome? g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.findSome?_cons, h x List.mem_cons_self,
      ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- The first `a` indices of `finRange N` are those below `a`. -/
theorem mem_take_finRange {a : ℕ} {x : Fin N} : x ∈ (List.finRange N).take a ↔ (x : ℕ) < a := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [List.getElem_finRange, Fin.val_cast]
    exact lt_of_lt_of_le hi (min_le_left _ _)
  · intro hx
    exact ⟨x, lt_min hx (by simp), by simp⟩

/-- **When attempt `a` does not run, the reply is the reply as if it rejected**: an earlier attempt
kept, and the two families agree below `a`. -/
theorem firstKept_eq_replyWithout_of_not_runs (att : Fin N → U → Option β) {a : Fin N}
    {u : Fin N → U} (h : ¬ Runs att u a) : firstKept att u = replyWithout att a u := by
  unfold Runs at h
  push Not at h
  obtain ⟨b, hb, hsome⟩ := h
  unfold replyWithout firstKept
  rw [← List.take_append_drop (a : ℕ) (List.finRange N), List.findSome?_append,
    List.findSome?_append]
  have hcongr : ((List.finRange N).take a).findSome? (fun c => att c (u c)) =
      ((List.finRange N).take a).findSome?
        (fun c => (if c = a then fun _ => none else att c) (u c)) :=
    findSome?_congr_mem fun x hx => by
      rw [ite_eq_right_of_eq_false _ _ (eq_false (Fin.ne_of_lt (mem_take_finRange.1 hx)))]
  have hb' : b ∈ (List.finRange N).take a := mem_take_finRange.2 hb
  have hsome' : (((List.finRange N).take a).findSome? fun c => att c (u c)).isSome :=
    List.findSome?_isSome_iff.2 ⟨b, hb', Option.isSome_iff_ne_none.2 hsome⟩
  rw [← hcongr]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hsome'
  rw [hv]
  rfl

/-- **The points of the attempts not kept**: the attempts that rejected or did not run. -/
def notKeptPoints (att : Fin N → U → Option β) (pt : Fin N → U → X) (u : Fin N → U) : Set X :=
  {x | ∃ a, (¬ Runs att u a ∨ att a (u a) = none) ∧ pt a (u a) = x}

/-- **When attempt `a` was not kept, the reply is the reply as if it rejected.** -/
theorem firstKept_eq_replyWithout_of_notKept (att : Fin N → U → Option β) {a : Fin N}
    {u : Fin N → U} (h : ¬ Runs att u a ∨ att a (u a) = none) :
    firstKept att u = replyWithout att a u := by
  rcases h with h | h
  · exact firstKept_eq_replyWithout_of_not_runs att h
  · exact firstKept_eq_replyWithout att h

variable [Fintype U] (p : Fin N → PMF U) (att : Fin N → U → Option β) (pt : Fin N → U → X)

/-- Events of independent coordinates have finite probability. -/
theorem toOuterMeasure_pi_ne_top (t : Set (Fin N → U)) : (pi p).toOuterMeasure t ≠ ⊤ := by
  rw [toOuterMeasure_apply]
  exact (pi p).tsum_coe_indicator_ne_top t

/-- **The point of a rejected attempt and the reply** (a product bound): that attempt `a`
runs, rejects with point `x`, and the reply is `r`, has probability at most
`Pr[pt a (u a) = x] · Pr[replyWithout att a u = r]`. -/
theorem toReal_pt_rejected_reply_le (a : Fin N) (x : X) (r : Option β) :
    ((pi p).toOuterMeasure {u | pt a (u a) = x ∧ Runs att u a ∧ att a (u a) = none ∧
      firstKept att u = r}).toReal ≤
      ((p a).toOuterMeasure {y | pt a y = x}).toReal *
        ((pi p).toOuterMeasure {u | replyWithout att a u = r}).toReal := by
  classical
  rw [← toReal_pi_inter_eq_mul p a {y | pt a y = x} {u | replyWithout att a u = r}
    fun u y => by simp [replyWithout_update]]
  refine ENNReal.toReal_mono (toOuterMeasure_pi_ne_top p _) (MeasureTheory.measure_mono ?_)
  rintro u ⟨h1, -, h3, h4⟩
  exact ⟨h1, by rw [Set.mem_ofPred_eq, ← firstKept_eq_replyWithout att h3]; exact h4⟩

/-- **A guess from the reply is a rejected point with probability at most `N δ`**, for `δ`
bounding the probability of each point of each attempt. -/
theorem toReal_guess_mem_rejectedPoints_le {δ : ℝ}
    (hδ : ∀ a x, ((p a).toOuterMeasure {y | pt a y = x}).toReal ≤ δ) (g : Option β → X) :
    ((pi p).toOuterMeasure {u | g (firstKept att u) ∈ rejectedPoints att pt u}).toReal ≤
      N * δ := by
  classical
  have hsub : {u | g (firstKept att u) ∈ rejectedPoints att pt u} ⊆
      ⋃ a, {u | pt a (u a) = g (replyWithout att a u)} := by
    rintro u ⟨a, -, h2, h3⟩
    refine Set.mem_iUnion.2 ⟨a, ?_⟩
    rw [Set.mem_ofPred_eq, h3, firstKept_eq_replyWithout att h2]
  have hEa : ∀ a, ((pi p).toOuterMeasure {u | pt a (u a) = g (replyWithout att a u)}).toReal ≤
      δ := by
    intro a
    rw [toReal_toOuterMeasure_apply]
    have h := sum_toReal_pi_mul_eq_sum_update p a
      (fun u => if pt a (u a) = g (replyWithout att a u) then (1 : ℝ) else 0)
    calc ∑ u, (if u ∈ {u | pt a (u a) = g (replyWithout att a u)} then (pi p u).toReal else 0)
        = ∑ u, (pi p u).toReal * (if pt a (u a) = g (replyWithout att a u) then (1 : ℝ) else 0) :=
          sum_congr rfl fun u _ => by
            simp only [Set.mem_ofPred_eq]
            split_ifs <;> simp
      _ = ∑ u, (pi p u).toReal *
          ((p a).toOuterMeasure {y | pt a y = g (replyWithout att a u)}).toReal := by
          rw [h]
          refine sum_congr rfl fun u _ => ?_
          rw [toReal_toOuterMeasure_apply]
          congr 1
          refine sum_congr rfl fun y _ => ?_
          simp only [Function.update_self, replyWithout_update, Set.mem_ofPred_eq]
          split_ifs <;> simp
      _ ≤ ∑ u, (pi p u).toReal * δ :=
          sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hδ a _) ENNReal.toReal_nonneg
      _ = δ := by rw [← sum_mul, sum_toReal, one_mul]
  calc ((pi p).toOuterMeasure {u | g (firstKept att u) ∈ rejectedPoints att pt u}).toReal
      ≤ ((pi p).toOuterMeasure (⋃ a, {u | pt a (u a) = g (replyWithout att a u)})).toReal :=
        ENNReal.toReal_mono (toOuterMeasure_pi_ne_top p _) (MeasureTheory.measure_mono hsub)
    _ ≤ ∑ a, ((pi p).toOuterMeasure {u | pt a (u a) = g (replyWithout att a u)}).toReal :=
        toReal_toOuterMeasure_iUnion_le _ _
    _ ≤ ∑ _a : Fin N, δ := sum_le_sum fun a _ => hEa a
    _ = N * δ := by simp

/-- **The rejected points, summed over the replies of their best guess** (the form
`∑ r, max_x Pr[x ∈ S ∧ reply = r] ≤ N δ`, `S` the rejected points). -/
theorem sum_sup'_toReal_rejectedPoints_le [Fintype β] [Fintype X] [Nonempty X] {δ : ℝ}
    (hδ : ∀ a x, ((p a).toOuterMeasure {y | pt a y = x}).toReal ≤ δ) :
    ∑ r : Option β, univ.sup' univ_nonempty (fun x => ((pi p).toOuterMeasure
      {u | x ∈ rejectedPoints att pt u ∧ firstKept att u = r}).toReal) ≤ N * δ := by
  classical
  choose g hg using fun r : Option β => exists_max_image univ (fun x => ((pi p).toOuterMeasure
    {u | x ∈ rejectedPoints att pt u ∧ firstKept att u = r}).toReal) univ_nonempty
  calc ∑ r : Option β, univ.sup' univ_nonempty (fun x => ((pi p).toOuterMeasure
        {u | x ∈ rejectedPoints att pt u ∧ firstKept att u = r}).toReal)
      ≤ ∑ r : Option β, ((pi p).toOuterMeasure
        {u | g r ∈ rejectedPoints att pt u ∧ firstKept att u = r}).toReal :=
        sum_le_sum fun r _ => Finset.sup'_le _ _ fun x _ => (hg r).2 x (mem_univ x)
    _ = ((pi p).toOuterMeasure {u | g (firstKept att u) ∈ rejectedPoints att pt u}).toReal := by
        simp only [toReal_toOuterMeasure_apply, Set.mem_ofPred_eq]
        rw [sum_comm]
        refine sum_congr rfl fun u _ => ?_
        rw [sum_eq_single (firstKept att u)]
        · simp
        · intro r _ hr
          simp [Ne.symm hr]
        · simp
    _ ≤ N * δ := toReal_guess_mem_rejectedPoints_le p att pt hδ g

/-- **The point of an attempt is a guess from the reply as if it rejected** with probability at
most `δ`: that reply does not read the attempt's coins (`replyWithout_update`). -/
theorem toReal_pt_eq_replyWithout_le {δ : ℝ}
    (hδ : ∀ a x, ((p a).toOuterMeasure {y | pt a y = x}).toReal ≤ δ) (g : Option β → X)
    (a : Fin N) :
    ((pi p).toOuterMeasure {u | pt a (u a) = g (replyWithout att a u)}).toReal ≤ δ := by
  classical
  rw [toReal_toOuterMeasure_apply]
  have h := sum_toReal_pi_mul_eq_sum_update p a
    (fun u => if pt a (u a) = g (replyWithout att a u) then (1 : ℝ) else 0)
  calc ∑ u, (if u ∈ {u | pt a (u a) = g (replyWithout att a u)} then (pi p u).toReal else 0)
      = ∑ u, (pi p u).toReal * (if pt a (u a) = g (replyWithout att a u) then (1 : ℝ) else 0) :=
        sum_congr rfl fun u _ => by
          simp only [Set.mem_ofPred_eq]
          split_ifs <;> simp
    _ = ∑ u, (pi p u).toReal *
          ((p a).toOuterMeasure {y | pt a y = g (replyWithout att a u)}).toReal := by
        rw [h]
        refine sum_congr rfl fun u _ => ?_
        rw [toReal_toOuterMeasure_apply]
        congr 1
        refine sum_congr rfl fun y _ => ?_
        simp only [Function.update_self, replyWithout_update, Set.mem_ofPred_eq]
        split_ifs <;> simp
    _ ≤ ∑ u, (pi p u).toReal * δ :=
        sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hδ a _) ENNReal.toReal_nonneg
    _ = δ := by rw [← sum_mul, sum_toReal, one_mul]

/-- **A guess from the reply is the point of an attempt not kept with probability at most `N δ`**,
for `δ` bounding the probability of each point of each attempt. -/
theorem toReal_guess_mem_notKeptPoints_le {δ : ℝ}
    (hδ : ∀ a x, ((p a).toOuterMeasure {y | pt a y = x}).toReal ≤ δ) (g : Option β → X) :
    ((pi p).toOuterMeasure {u | g (firstKept att u) ∈ notKeptPoints att pt u}).toReal ≤
      N * δ := by
  classical
  have hsub : {u | g (firstKept att u) ∈ notKeptPoints att pt u} ⊆
      ⋃ a, {u | pt a (u a) = g (replyWithout att a u)} := by
    rintro u ⟨a, h2, h3⟩
    refine Set.mem_iUnion.2 ⟨a, ?_⟩
    rw [Set.mem_ofPred_eq, h3, firstKept_eq_replyWithout_of_notKept att h2]
  refine (ENNReal.toReal_mono (toOuterMeasure_pi_ne_top p _)
    (MeasureTheory.measure_mono hsub)).trans ?_
  -- the union bound and the per-attempt bound, as in `toReal_guess_mem_rejectedPoints_le`
  refine (toReal_toOuterMeasure_iUnion_le _ _).trans ?_
  calc ∑ a, ((pi p).toOuterMeasure {u | pt a (u a) = g (replyWithout att a u)}).toReal
      ≤ ∑ _a : Fin N, δ := sum_le_sum fun a _ => toReal_pt_eq_replyWithout_le p att pt hδ g a
    _ = N * δ := by simp

/-- **The points of the attempts not kept, summed over the replies of their best guess.** -/
theorem sum_sup'_toReal_notKeptPoints_le [Fintype β] [Fintype X] [Nonempty X] {δ : ℝ}
    (hδ : ∀ a x, ((p a).toOuterMeasure {y | pt a y = x}).toReal ≤ δ) :
    ∑ r : Option β, univ.sup' univ_nonempty (fun x => ((pi p).toOuterMeasure
      {u | x ∈ notKeptPoints att pt u ∧ firstKept att u = r}).toReal) ≤ N * δ := by
  classical
  choose g hg using fun r : Option β => exists_max_image univ (fun x => ((pi p).toOuterMeasure
    {u | x ∈ notKeptPoints att pt u ∧ firstKept att u = r}).toReal) univ_nonempty
  calc ∑ r : Option β, univ.sup' univ_nonempty (fun x => ((pi p).toOuterMeasure
        {u | x ∈ notKeptPoints att pt u ∧ firstKept att u = r}).toReal)
      ≤ ∑ r : Option β, ((pi p).toOuterMeasure
        {u | g r ∈ notKeptPoints att pt u ∧ firstKept att u = r}).toReal :=
        sum_le_sum fun r _ => Finset.sup'_le _ _ fun x _ => (hg r).2 x (mem_univ x)
    _ = ((pi p).toOuterMeasure {u | g (firstKept att u) ∈ notKeptPoints att pt u}).toReal := by
        simp only [toReal_toOuterMeasure_apply, Set.mem_ofPred_eq]
        rw [sum_comm]
        refine sum_congr rfl fun u _ => ?_
        rw [sum_eq_single (firstKept att u)]
        · simp
        · intro r _ hr
          simp [Ne.symm hr]
        · simp
    _ ≤ N * δ := toReal_guess_mem_notKeptPoints_le p att pt hδ g

end Attempts

/-! ### Guesses from alternatives that ignore an attempt's coins -/

section Alternatives

variable {ι U X : Type*} [Fintype ι] [DecidableEq ι] [Fintype U] (p : ι → PMF U)
  (pt : ι → U → X)

/-- **The point of an attempt is a guess that ignores the attempt's coins** with probability at
most `δ`. -/
theorem toReal_pt_eq_of_update_le {δ : ℝ}
    (hδ : ∀ a x, ((p a).toOuterMeasure {y | pt a y = x}).toReal ≤ δ) (a : ι)
    (f : (ι → U) → X) (hf : ∀ u y, f (Function.update u a y) = f u) :
    ((pi p).toOuterMeasure {u | pt a (u a) = f u}).toReal ≤ δ := by
  classical
  rw [toReal_toOuterMeasure_apply]
  have h := sum_toReal_pi_mul_eq_sum_update p a
    (fun u => if pt a (u a) = f u then (1 : ℝ) else 0)
  calc ∑ u, (if u ∈ {u | pt a (u a) = f u} then (pi p u).toReal else 0)
      = ∑ u, (pi p u).toReal * (if pt a (u a) = f u then (1 : ℝ) else 0) :=
        sum_congr rfl fun u _ => by
          simp only [Set.mem_ofPred_eq]
          split_ifs <;> simp
    _ = ∑ u, (pi p u).toReal * ((p a).toOuterMeasure {y | pt a y = f u}).toReal := by
        rw [h]
        refine sum_congr rfl fun u _ => ?_
        rw [toReal_toOuterMeasure_apply]
        congr 1
        refine sum_congr rfl fun y _ => ?_
        simp only [Function.update_self, hf, Set.mem_ofPred_eq]
        split_ifs <;> simp
    _ ≤ ∑ u, (pi p u).toReal * δ :=
        sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hδ a _) ENNReal.toReal_nonneg
    _ = δ := by rw [← sum_mul, sum_toReal, one_mul]

/-- **A guess from the reply is a hidden point with probability at most `|ι| K δ`** when every
hidden point is the point of an attempt at which the reply is one of `K` alternatives that ignore
that attempt's coins, for `δ` bounding the probability of each point of each attempt. -/
theorem toReal_guess_mem_of_alternatives {β' : Type*} {K : ℕ} {δ : ℝ}
    (hδ : ∀ a x, ((p a).toOuterMeasure {y | pt a y = x}).toReal ≤ δ)
    (reply : (ι → U) → β') (alt : ι → Fin K → (ι → U) → β')
    (halt : ∀ a i u y, alt a i (Function.update u a y) = alt a i u)
    (hidden : (ι → U) → Set X)
    (hhid : ∀ u x, x ∈ hidden u → ∃ a i, pt a (u a) = x ∧ reply u = alt a i u) (g : β' → X) :
    ((pi p).toOuterMeasure {u | g (reply u) ∈ hidden u}).toReal ≤
      Fintype.card ι * K * δ := by
  classical
  have hsub : {u | g (reply u) ∈ hidden u} ⊆
      ⋃ ai : ι × Fin K, {u | pt ai.1 (u ai.1) = g (alt ai.1 ai.2 u)} := by
    intro u hu
    obtain ⟨a, i, h1, h2⟩ := hhid u _ hu
    refine Set.mem_iUnion.2 ⟨(a, i), ?_⟩
    rw [Set.mem_ofPred_eq, h1, h2]
  refine (ENNReal.toReal_mono (((pi p).toOuterMeasure_apply_le_one _).trans_lt
    ENNReal.one_lt_top).ne (MeasureTheory.measure_mono hsub)).trans ?_
  refine (toReal_toOuterMeasure_iUnion_le _ _).trans ?_
  calc ∑ ai : ι × Fin K,
        ((pi p).toOuterMeasure {u | pt ai.1 (u ai.1) = g (alt ai.1 ai.2 u)}).toReal
      ≤ ∑ _ai : ι × Fin K, δ := sum_le_sum fun ai _ =>
        toReal_pt_eq_of_update_le p pt hδ ai.1 _ fun u y => by rw [halt]
    _ = Fintype.card ι * K * δ := by simp [mul_assoc]

/-- The probability of an event under a uniform law: its size over the size of the space. -/
theorem toReal_uniformOfFintype_toOuterMeasure {α : Type*} [Fintype α] [Nonempty α] (s : Set α)
    [DecidablePred (· ∈ s)] :
    ((uniformOfFintype α).toOuterMeasure s).toReal =
      (Fintype.card α : ℝ)⁻¹ * ∑ a, if a ∈ s then (1 : ℝ) else 0 := by
  rw [toReal_toOuterMeasure_apply, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  split_ifs <;> simp

/-- **A bound under redrawing coordinates of a uniform law**: `Φ v ω` overwrites part of `ω` by
`v`, and `r` reads it back (`r (Φ v ω) = v`, `Φ (r ω) (Φ v ω) = ω`). If for every `ω` the event
holds at `Φ v ω` with probability at most `ε` over a uniform `v`, it holds with probability at
most `ε` over a uniform `ω`. -/
theorem toReal_uniform_le_of_overwrite {Ω V : Type*} [Fintype Ω] [Nonempty Ω] [Fintype V]
    [Nonempty V] (Φ : V → Ω → Ω) (r : Ω → V) (h1 : ∀ v ω, r (Φ v ω) = v)
    (h2 : ∀ v ω, Φ (r ω) (Φ v ω) = ω) (E : Set Ω) {ε : ℝ}
    (h : ∀ ω, ((uniformOfFintype V).toOuterMeasure {v | Φ v ω ∈ E}).toReal ≤ ε) :
    ((uniformOfFintype Ω).toOuterMeasure E).toReal ≤ ε := by
  classical
  let e : V × Ω ≃ V × Ω :=
    { toFun := fun q => (r q.2, Φ q.1 q.2)
      invFun := fun q => (r q.2, Φ q.1 q.2)
      left_inv := fun q => by simp only [h1, h2]
      right_inv := fun q => by simp only [h1, h2] }
  set F : Ω → ℝ := fun ω => if ω ∈ E then 1 else 0 with hF
  have hsum : ∑ ω, ∑ v, F (Φ v ω) = Fintype.card V * ∑ ω, F ω := by
    calc ∑ ω, ∑ v, F (Φ v ω)
        = ∑ q : V × Ω, F (e q).2 := by
          rw [Fintype.sum_prod_type, sum_comm]
          rfl
      _ = ∑ q : V × Ω, F q.2 := e.sum_comp (fun q => F q.2)
      _ = Fintype.card V * ∑ ω, F ω := by
          rw [Fintype.sum_prod_type]
          dsimp only
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hV : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hΩ : (0 : ℝ) ≤ (Fintype.card Ω : ℝ)⁻¹ := by positivity
  calc ((uniformOfFintype Ω).toOuterMeasure E).toReal
      = ∑ ω, (Fintype.card Ω : ℝ)⁻¹ *
          ((uniformOfFintype V).toOuterMeasure {v | Φ v ω ∈ E}).toReal := by
        simp only [toReal_uniformOfFintype_toOuterMeasure, Set.mem_ofPred_eq]
        change _ * ∑ ω, F ω = ∑ ω, _ * (_ * ∑ v, F (Φ v ω))
        rw [← mul_sum, ← mul_sum, hsum, ← mul_assoc, ← mul_assoc,
          mul_assoc _ _ (Fintype.card V : ℝ), inv_mul_cancel₀ hV, mul_one]
    _ ≤ ∑ _ω : Ω, (Fintype.card Ω : ℝ)⁻¹ * ε :=
        sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) hΩ
    _ = ε := by
        rw [sum_const, card_univ, nsmul_eq_mul, ← mul_assoc,
          mul_inv_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_mul]

end Alternatives

/-! ### Calls of sequential attempts with a keep test -/

section Calls

variable {M β : Type*} {k T : ℕ}

/-- **When attempt `a` runs and outputs, the reply is its output.** -/
theorem firstKept_eq_of_runs {U : Type*} {N : ℕ} (att : Fin N → U → Option β) {a : Fin N}
    {u : Fin N → U} {v : β} (hr : Runs att u a) (hs : att a (u a) = some v) :
    firstKept att u = some v := by
  unfold firstKept
  rw [← List.take_append_drop (a : ℕ) (List.finRange N), List.findSome?_append]
  have h1 : ((List.finRange N).take a).findSome? (fun c => att c (u c)) = none :=
    List.findSome?_eq_none_iff.2 fun x hx => hr x (mem_take_finRange.1 hx)
  rw [h1, Option.none_or, List.drop_eq_getElem_cons (by simp), List.findSome?_cons]
  simp [hs]

/-- `find?` agrees for two predicates that agree on the list's elements. -/
theorem find?_congr_mem {α : Type*} {l : List α} {p q : α → Bool}
    (h : ∀ x ∈ l, p x = q x) : l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.find?_cons, h x List.mem_cons_self,
      ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- **The first index of `finRange T` passing `p`** is `t₀` when `t₀` passes and no earlier index
does. -/
theorem find?_finRange_eq_some {p : Fin T → Bool} {t₀ : Fin T} (h : ∀ t < t₀, p t = false)
    (ht : p t₀ = true) : (List.finRange T).find? p = some t₀ := by
  rw [← List.take_append_drop (t₀ : ℕ) (List.finRange T), List.find?_append]
  have h1 : ((List.finRange T).take t₀).find? p = none :=
    List.find?_eq_none.2 fun x hx => by simp [h x (mem_take_finRange.1 hx)]
  rw [h1, Option.none_or, List.drop_eq_getElem_cons (by simp), List.find?_cons]
  simp [ht]

/-- **The output of one call of `T` attempts**: the first attempt `t` whose mask `ys t` passes
`acc`, output as `out (ys t)` when its keep test `ok (ys t)` holds; `none` when no attempt passes
or the keep test fails. -/
def callOutcome (acc ok : M → Bool) (out : M → β) (ys : Fin T → M) : Option β :=
  match (List.finRange T).find? (fun t => acc (ys t)) with
  | none => none
  | some t => if ok (ys t) then some (out (ys t)) else none

/-- **The output of `k` calls**: the output of the first call that outputs (`firstKept`), call `c`
with the tests `acc c`, `ok c` and the output `out c` on its masks `ys c`. -/
def loopOut (acc ok : Fin k → M → Bool) (out : Fin k → M → β) (ys : Fin k → Fin T → M) :
    Option β :=
  firstKept (fun c => callOutcome (acc c) (ok c) (out c)) ys

/-- **Attempt `t₀` of call `c₀` is kept**: the call runs (every earlier call output nothing), every
earlier attempt of the call fails `acc`, and the attempt passes `acc` and its keep test. -/
def KeptAt (acc ok : Fin k → M → Bool) (out : Fin k → M → β) (ys : Fin k → Fin T → M)
    (c₀ : Fin k) (t₀ : Fin T) : Prop :=
  Runs (fun c => callOutcome (acc c) (ok c) (out c)) ys c₀ ∧
    (∀ t < t₀, acc c₀ (ys c₀ t) = false) ∧ acc c₀ (ys c₀ t₀) = true ∧ ok c₀ (ys c₀ t₀) = true

/-- The masks `ys` with the mask of attempt `t₀` of call `c₀` replaced by `y`. -/
def updAt (ys : Fin k → Fin T → M) (c₀ : Fin k) (t₀ : Fin T) (y : M) : Fin k → Fin T → M :=
  Function.update ys c₀ (Function.update (ys c₀) t₀ y)

@[simp] theorem updAt_self (ys : Fin k → Fin T → M) (c₀ : Fin k) (t₀ : Fin T) (y : M) :
    updAt ys c₀ t₀ y c₀ t₀ = y := by
  simp [updAt]

theorem updAt_of_ne {ys : Fin k → Fin T → M} {c₀ : Fin k} {t₀ t : Fin T} (y : M) (h : t ≠ t₀) :
    updAt ys c₀ t₀ y c₀ t = ys c₀ t := by
  simp [updAt, h]

theorem updAt_of_ne_call {ys : Fin k → Fin T → M} {c₀ c : Fin k} (t₀ : Fin T) (y : M)
    (h : c ≠ c₀) : updAt ys c₀ t₀ y c = ys c := by
  simp [updAt, h]

theorem updAt_eq_update (ys : Fin k → Fin T → M) (c₀ : Fin k) (t₀ : Fin T) (y : M) :
    updAt ys c₀ t₀ y = Function.update ys c₀ (updAt ys c₀ t₀ y c₀) := by
  funext c
  by_cases hc : c = c₀
  · subst hc
    simp
  · simp [updAt, hc]

variable (acc ok : Fin k → M → Bool) (out : Fin k → M → β)

/-- **A kept attempt's output is the reply.** -/
theorem loopOut_of_keptAt {ys : Fin k → Fin T → M} {c₀ : Fin k} {t₀ : Fin T}
    (h : KeptAt acc ok out ys c₀ t₀) : loopOut acc ok out ys = some (out c₀ (ys c₀ t₀)) := by
  obtain ⟨hr, hlt, hacc, hok⟩ := h
  refine firstKept_eq_of_runs _ hr ?_
  unfold callOutcome
  rw [find?_finRange_eq_some (p := fun t => acc c₀ (ys c₀ t)) hlt hacc]
  simp [hok]

/-- **The first index of `finRange T` passing `p` has no earlier index passing `p`.** -/
theorem find?_finRange_eq_some_lt {p : Fin T → Bool} {t₀ : Fin T}
    (h : (List.finRange T).find? p = some t₀) : ∀ t < t₀, p t = false := by
  classical
  intro t ht
  by_contra hpt
  have hpt' : p t = true := by simpa using hpt
  set F := univ.filter fun t => p t = true with hFdef
  have hF : F.Nonempty := ⟨t, mem_filter.2 ⟨mem_univ _, hpt'⟩⟩
  have hmin : ∀ t' < F.min' hF, p t' = false := fun t' ht' => by
    by_contra hne
    exact absurd (F.min'_le t' (mem_filter.2 ⟨mem_univ _, by simpa using hne⟩)) (not_le.2 ht')
  have h1 := find?_finRange_eq_some hmin (mem_filter.1 (F.min'_mem hF)).2
  rw [h] at h1
  have hle : F.min' hF ≤ t := F.min'_le t (mem_filter.2 ⟨mem_univ _, hpt'⟩)
  rw [← Option.some_injective _ h1] at hle
  exact absurd ht (not_lt.2 hle)

/-- **An output of the calls is the output of a kept attempt.** -/
theorem exists_keptAt_of_loopOut_eq_some {ys : Fin k → Fin T → M} {v : β}
    (h : loopOut acc ok out ys = some v) :
    ∃ c₀ t₀, KeptAt acc ok out ys c₀ t₀ ∧ v = out c₀ (ys c₀ t₀) := by
  classical
  set att := fun c => callOutcome (acc c) (ok c) (out c) with hatt
  have hex : ∃ c, att c (ys c) ≠ none := by
    by_contra hne
    push Not at hne
    have h0 : loopOut acc ok out ys = none := List.findSome?_eq_none_iff.2 fun c _ => hne c
    rw [h0] at h
    exact absurd h (by simp)
  set F := univ.filter fun c => att c (ys c) ≠ none with hFdef
  have hF : F.Nonempty := ⟨_, mem_filter.2 ⟨mem_univ _, hex.choose_spec⟩⟩
  have hc₀ : att (F.min' hF) (ys (F.min' hF)) ≠ none := (mem_filter.1 (F.min'_mem hF)).2
  have hmin : Runs att ys (F.min' hF) := fun b hb => by
    by_contra hne
    exact absurd (F.min'_le b (mem_filter.2 ⟨mem_univ _, hne⟩)) (not_le.2 hb)
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hc₀
  have hv : v = w := Option.some_injective _ (h.symm.trans (firstKept_eq_of_runs att hmin hw))
  subst hv
  have hw' : callOutcome (acc (F.min' hF)) (ok (F.min' hF)) (out (F.min' hF)) (ys (F.min' hF)) =
      some v := hw
  unfold callOutcome at hw'
  rcases hf : (List.finRange T).find? (fun t => acc (F.min' hF) (ys (F.min' hF) t)) with _ | t₀
  · rw [hf] at hw'
    exact absurd hw' (by simp)
  · rw [hf] at hw'
    dsimp only at hw'
    split_ifs at hw' with hok
    have hacc : acc (F.min' hF) (ys (F.min' hF) t₀) = true := by simpa using List.find?_some hf
    exact ⟨F.min' hF, t₀, ⟨hmin, find?_finRange_eq_some_lt hf, hacc, hok⟩,
      (Option.some_injective _ hw').symm⟩

/-- Call `c₀` runs for the masks with one of its attempts replaced iff it runs for the masks. -/
theorem runs_updAt_iff (ys : Fin k → Fin T → M) (c₀ : Fin k) (t₀ : Fin T) (y : M) :
    Runs (fun c => callOutcome (acc c) (ok c) (out c)) (updAt ys c₀ t₀ y) c₀ ↔
      Runs (fun c => callOutcome (acc c) (ok c) (out c)) ys c₀ := by
  unfold Runs
  refine forall_congr' fun b => imp_congr_right fun hb => ?_
  rw [updAt_of_ne_call t₀ y (Fin.ne_of_lt hb)]

/-- **The reply ignores a failed or unreached attempt**: for two masks `y`, `y'` of attempt `t₀`
of call `c₀` at which the attempt is not reached or fails `acc`, the replies agree. -/
theorem loopOut_updAt_eq_of_fail (ys : Fin k → Fin T → M) (c₀ : Fin k) (t₀ : Fin T) {y y' : M}
    (hy : ¬ (Runs (fun c => callOutcome (acc c) (ok c) (out c)) ys c₀ ∧
        ∀ t < t₀, acc c₀ (ys c₀ t) = false) ∨ acc c₀ y = false)
    (hy' : ¬ (Runs (fun c => callOutcome (acc c) (ok c) (out c)) ys c₀ ∧
        ∀ t < t₀, acc c₀ (ys c₀ t) = false) ∨ acc c₀ y' = false) :
    loopOut acc ok out (updAt ys c₀ t₀ y) = loopOut acc ok out (updAt ys c₀ t₀ y') := by
  classical
  set att := fun c => callOutcome (acc c) (ok c) (out c) with hatt
  -- the replies agree when the outputs of call `c₀` agree
  have hcall : callOutcome (acc c₀) (ok c₀) (out c₀) (updAt ys c₀ t₀ y c₀) =
      callOutcome (acc c₀) (ok c₀) (out c₀) (updAt ys c₀ t₀ y' c₀) →
      loopOut acc ok out (updAt ys c₀ t₀ y) = loopOut acc ok out (updAt ys c₀ t₀ y') := by
    intro h
    unfold loopOut firstKept
    congr 1
    funext c
    by_cases hc : c = c₀
    · subst hc
      exact h
    · rw [updAt_of_ne_call t₀ y hc, updAt_of_ne_call t₀ y' hc]
  -- the call's output from the first passing attempt, when it is not `t₀`
  have hout : ∀ (t₁ : Fin T), t₁ ≠ t₀ →
      (List.finRange T).find? (fun t => acc c₀ (updAt ys c₀ t₀ y c₀ t)) = some t₁ →
      (List.finRange T).find? (fun t => acc c₀ (updAt ys c₀ t₀ y' c₀ t)) = some t₁ →
      callOutcome (acc c₀) (ok c₀) (out c₀) (updAt ys c₀ t₀ y c₀) =
        callOutcome (acc c₀) (ok c₀) (out c₀) (updAt ys c₀ t₀ y' c₀) := by
    intro t₁ hne h1 h2
    unfold callOutcome
    rw [h1, h2]
    simp only [updAt_of_ne y hne, updAt_of_ne y' hne]
  by_cases hR : Runs att ys c₀ ∧ ∀ t < t₀, acc c₀ (ys c₀ t) = false
  · -- the attempt is reached and fails at both masks: the predicates agree
    have hf : acc c₀ y = false := hy.resolve_left (not_not.2 hR)
    have hf' : acc c₀ y' = false := hy'.resolve_left (not_not.2 hR)
    have hp : (fun t => acc c₀ (updAt ys c₀ t₀ y c₀ t)) =
        fun t => acc c₀ (updAt ys c₀ t₀ y' c₀ t) := by
      funext t
      by_cases ht : t = t₀
      · subst ht
        simp [hf, hf']
      · rw [updAt_of_ne y ht, updAt_of_ne y' ht]
    apply hcall
    rcases hres : (List.finRange T).find? (fun t => acc c₀ (updAt ys c₀ t₀ y c₀ t)) with _ | t₁
    · unfold callOutcome
      rw [hres, ← hp, hres]
    · have ht₁ := List.find?_some hres
      have hne : t₁ ≠ t₀ := by
        rintro rfl
        simp [hf] at ht₁
      exact hout t₁ hne hres (hp ▸ hres)
  · rcases not_and_or.1 hR with hrun | hearly
    · -- the call does not run: the reply as if it rejected
      have h1 : ¬ Runs att (updAt ys c₀ t₀ y) c₀ := by
        rw [hatt, runs_updAt_iff]
        exact hrun
      have h2 : ¬ Runs att (updAt ys c₀ t₀ y') c₀ := by
        rw [hatt, runs_updAt_iff]
        exact hrun
      unfold loopOut
      rw [← hatt, firstKept_eq_replyWithout_of_not_runs att h1,
        firstKept_eq_replyWithout_of_not_runs att h2, updAt_eq_update ys c₀ t₀ y,
        updAt_eq_update ys c₀ t₀ y', replyWithout_update, replyWithout_update]
    · -- an earlier attempt of the call passes: the call stops before `t₀`
      push Not at hearly
      obtain ⟨t₂, ht₂, hacc₂⟩ := hearly
      have hacc₂' : acc c₀ (ys c₀ t₂) = true := by simpa using hacc₂
      apply hcall
      have htake : ∀ y'' : M, ((List.finRange T).take t₀).find?
          (fun t => acc c₀ (updAt ys c₀ t₀ y'' c₀ t)) =
          ((List.finRange T).take t₀).find? (fun t => acc c₀ (ys c₀ t)) := fun y'' =>
        find?_congr_mem fun x hx => by
          rw [updAt_of_ne y'' (Fin.ne_of_lt (mem_take_finRange.1 hx))]
      have hsome : (((List.finRange T).take t₀).find? (fun t => acc c₀ (ys c₀ t))).isSome :=
        List.find?_isSome.2 ⟨t₂, mem_take_finRange.2 ht₂, hacc₂'⟩
      obtain ⟨t₁, ht₁⟩ := Option.isSome_iff_exists.1 hsome
      have hlt : (t₁ : ℕ) < t₀ := mem_take_finRange.1 (List.mem_of_find?_eq_some ht₁)
      have hfull : ∀ y'' : M,
          (List.finRange T).find? (fun t => acc c₀ (updAt ys c₀ t₀ y'' c₀ t)) = some t₁ :=
        fun y'' => by
          rw [← List.take_append_drop (t₀ : ℕ) (List.finRange T), List.find?_append, htake, ht₁]
          rfl
      exact hout t₁ (Fin.ne_of_lt hlt) (hfull y) (hfull y')

/-- **The reply ignores an attempt whose call it ends without output**: for two masks `y`, `y'`
of attempt `t₀` of call `c₀` at which the attempt is reached, passes `acc` and fails its keep
test, the replies agree. -/
theorem loopOut_updAt_eq_of_drop (ys : Fin k → Fin T → M) (c₀ : Fin k) (t₀ : Fin T) {y y' : M}
    (hR : ∀ t < t₀, acc c₀ (ys c₀ t) = false)
    (hy : acc c₀ y = true ∧ ok c₀ y = false) (hy' : acc c₀ y' = true ∧ ok c₀ y' = false) :
    loopOut acc ok out (updAt ys c₀ t₀ y) = loopOut acc ok out (updAt ys c₀ t₀ y') := by
  set att := fun c => callOutcome (acc c) (ok c) (out c) with hatt
  have hnone : ∀ y'' : M, acc c₀ y'' = true → ok c₀ y'' = false →
      att c₀ (updAt ys c₀ t₀ y'' c₀) = none := fun y'' ha hk => by
    change callOutcome (acc c₀) (ok c₀) (out c₀) (updAt ys c₀ t₀ y'' c₀) = none
    unfold callOutcome
    rw [find?_finRange_eq_some (p := fun t => acc c₀ (updAt ys c₀ t₀ y'' c₀ t))
      (fun t ht => by rw [updAt_of_ne y'' (Fin.ne_of_lt ht)]; exact hR t ht) (by simpa using ha)]
    simp [hk]
  unfold loopOut
  rw [← hatt, firstKept_eq_replyWithout att (hnone y hy.1 hy.2),
    firstKept_eq_replyWithout att (hnone y' hy'.1 hy'.2), updAt_eq_update ys c₀ t₀ y,
    updAt_eq_update ys c₀ t₀ y', replyWithout_update, replyWithout_update]

/-- **The reply at a mask of an attempt not kept is one of two values** that do not depend on that
mask: the reply when the attempt fails or is not reached, and the reply when it ends its call
without output. -/
theorem exists_loopOut_mem_range_of_not_keptAt (ys : Fin k → Fin T → M) (c₀ : Fin k)
    (t₀ : Fin T) : ∃ v : Fin 2 → Option β, ∀ y,
      ¬ KeptAt acc ok out (updAt ys c₀ t₀ y) c₀ t₀ →
        loopOut acc ok out (updAt ys c₀ t₀ y) ∈ Set.range v := by
  classical
  set R : Prop := Runs (fun c => callOutcome (acc c) (ok c) (out c)) ys c₀ ∧
    ∀ t < t₀, acc c₀ (ys c₀ t) = false with hRdef
  let A : M → Prop := fun y => ¬ R ∨ acc c₀ y = false
  let B : M → Prop := fun y => R ∧ acc c₀ y = true ∧ ok c₀ y = false
  let v : Fin 2 → Option β := fun i =>
    if i = 0 then (if h : ∃ y, A y then loopOut acc ok out (updAt ys c₀ t₀ h.choose) else none)
    else (if h : ∃ y, B y then loopOut acc ok out (updAt ys c₀ t₀ h.choose) else none)
  refine ⟨v, fun y hy => ?_⟩
  have hAB : A y ∨ B y := by
    by_cases hR : R
    · by_cases ha : acc c₀ y = true
      · right
        refine ⟨hR, ha, ?_⟩
        by_contra hk
        apply hy
        refine ⟨(runs_updAt_iff acc ok out ys c₀ t₀ y).2 hR.1, fun t ht => ?_, by simpa using ha,
          by simpa using hk⟩
        rw [updAt_of_ne y (Fin.ne_of_lt ht)]
        exact hR.2 t ht
      · left
        exact Or.inr (by simpa using ha)
    · exact Or.inl (Or.inl hR)
  rcases hAB with hA | hB
  · have h : ∃ y, A y := ⟨y, hA⟩
    refine ⟨0, ?_⟩
    simp only [v, ↓reduceIte, h, ↓reduceDIte]
    exact loopOut_updAt_eq_of_fail acc ok out ys c₀ t₀ h.choose_spec hA
  · have h : ∃ y, B y := ⟨y, hB⟩
    refine ⟨1, ?_⟩
    simp only [v, one_ne_zero, ↓reduceIte, h, ↓reduceDIte]
    exact loopOut_updAt_eq_of_drop acc ok out ys c₀ t₀ hB.1.2
      ⟨h.choose_spec.2.1, h.choose_spec.2.2⟩ ⟨hB.2.1, hB.2.2⟩

/-- **A guess from the calls' reply is the point of an attempt not kept with probability at most
`k T 2 δ`**: the masks `mask (v (c, t))` of the `k T` attempts are decoded from independent coins
`v (c, t) ← q`, the point of an attempt with mask `y` is `ptM y` (probability at most `δ` for
each point), the reply is `rep` of the calls' output, and the kept points `keepF` of the reply
hold the point of a kept attempt, unless `rep` is constant. -/
theorem toReal_guess_mem_loopPoints_le {Y X γ : Type*} [Fintype Y] [Nonempty Y] [DecidableEq X]
    (q : PMF Y) (mask : Y → M) (ptM : M → X) (rep : Option β → γ) (keepF : γ → Finset X)
    {δ : ℝ} (hδ : ∀ x, (q.toOuterMeasure {y | ptM (mask y) = x}).toReal ≤ δ)
    (hk : (∀ L L', rep L = rep L') ∨ ∀ (ys : Fin k → Fin T → M) c t, KeptAt acc ok out ys c t →
      ptM (ys c t) ∈ keepF (rep (loopOut acc ok out ys)))
    (g : γ → X) :
    ((pi fun _ : Fin k × Fin T => q).toOuterMeasure {v | g (rep (loopOut acc ok out
      fun c t => mask (v (c, t)))) ∈ (univ.image fun a => ptM (mask (v a))) \
        keepF (rep (loopOut acc ok out fun c t => mask (v (c, t))))}).toReal ≤
      k * T * 2 * δ := by
  classical
  let ysOf : (Fin k × Fin T → Y) → Fin k → Fin T → M := fun v c t => mask (v (c, t))
  let y₀ : Y := Classical.arbitrary Y
  have hex := fun (a : Fin k × Fin T) (ys : Fin k → Fin T → M) =>
    exists_loopOut_mem_range_of_not_keptAt acc ok out ys a.1 a.2
  let w : Fin k × Fin T → (Fin k → Fin T → M) → Fin 2 → Option β := fun a ys => (hex a ys).choose
  have hupd : ∀ (v : Fin k × Fin T → Y) (c₀ : Fin k) (t₀ : Fin T),
      ysOf v = updAt (ysOf (Function.update v (c₀, t₀) y₀)) c₀ t₀ (mask (v (c₀, t₀))) := by
    intro v c₀ t₀
    funext c t
    by_cases hc : c = c₀
    · subst hc
      by_cases ht : t = t₀
      · subst ht
        simp [updAt, ysOf]
      · have hne : (c, t) ≠ (c, t₀) := fun h => ht (Prod.mk.inj h).2
        simp [updAt, ysOf, ht]
    · have hne : (c, t) ≠ (c₀, t₀) := fun h => hc (Prod.mk.inj h).1
      simp [updAt, ysOf, hc]
  have hmain := toReal_guess_mem_of_alternatives (fun _ : Fin k × Fin T => q)
    (fun _ y => ptM (mask y)) (fun _ x => hδ x) (fun v => rep (loopOut acc ok out (ysOf v)))
    (fun a i v => rep (w a (ysOf (Function.update v a y₀)) i))
    (fun a i v y => by simp only [Function.update_idem])
    (fun v => ↑((univ.image fun a => ptM (mask (v a))) \
      keepF (rep (loopOut acc ok out (ysOf v)))))
    (fun v x hx => by
      rw [Finset.mem_coe, Finset.mem_sdiff, Finset.mem_image] at hx
      obtain ⟨⟨⟨c₀, t₀⟩, -, hax⟩, hxk⟩ := hx
      refine ⟨(c₀, t₀), ?_⟩
      rcases hk with hc | hk
      · exact ⟨0, hax, hc _ _⟩
      · have hnk : ¬ KeptAt acc ok out
            (updAt (ysOf (Function.update v (c₀, t₀) y₀)) c₀ t₀ (mask (v (c₀, t₀)))) c₀ t₀ := by
          rw [← hupd]
          intro hK
          exact hxk (by rw [← hax]; exact hk _ _ _ hK)
        obtain ⟨i, hi⟩ := (hex (c₀, t₀) (ysOf (Function.update v (c₀, t₀) y₀))).choose_spec
          (mask (v (c₀, t₀))) hnk
        refine ⟨i, hax, ?_⟩
        rw [hupd v c₀ t₀]
        exact congrArg rep hi.symm) g
  simpa [Fintype.card_prod, Fintype.card_fin] using hmain

end Calls

end PMF
