-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.List.Range

@[expose] public section

/-!
# `forIn` over a list in `Id`, and arrays filled by a loop

Candidate for upstreaming next to core's `List.forIn_pure_yield_eq_foldl`, which
requires the body to continue on every state. Here the body only has to continue
on the states the loop actually visits, which is what a loop with early `return`
branches needs when those branches are never taken.
-/

universe u v

/-- A `forIn` loop over a list in `Id` is the left fold of `g` when, at every
position `n`, the body continues (`ForInStep.yield`) with `g` applied to the state
reached after the first `n` elements. -/
theorem List.forIn_id_eq_foldl_of_yield {α : Type u} {β : Type v} (l : List α) (init : β)
    (f : α → β → Id (ForInStep β)) (g : β → α → β)
    (h : ∀ (n : ℕ) (hn : n < l.length),
      f l[n] ((l.take n).foldl g init) = ForInStep.yield (g ((l.take n).foldl g init) l[n])) :
    forIn l init f = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons a t ih =>
    have h0 : f a init = ForInStep.yield (g init a) := by
      have := h 0 (by simp)
      rwa [List.getElem_cons_zero, List.take_zero, List.foldl_nil] at this
    rw [List.forIn_cons, h0, List.foldl_cons]
    exact ih (g init a) fun n hn => by
      have := h (n + 1) (by simpa using hn)
      rwa [List.getElem_cons_succ, List.take_succ_cons, List.foldl_cons] at this

/-- A `forIn` loop over a list in `Id` whose body always continues with `g` is the left
fold of `g`. -/
theorem List.forIn_id_eq_foldl {α : Type u} {β : Type v} (l : List α) (init : β)
    (f : α → β → Id (ForInStep β)) (g : β → α → β)
    (h : ∀ a b, f a b = ForInStep.yield (g b a)) :
    forIn l init f = l.foldl g init :=
  List.forIn_id_eq_foldl_of_yield l init f g fun _ _ => h _ _

/-- Setting the indices of `l` to `true` in a Boolean array, one after another, reads back
at an in-bounds index `x` as the old value or membership of `x` in `l`. -/
theorem Array.getD_foldl_set!_true (l : List ℕ) (init : Array Bool) {x : ℕ} (hx : x < init.size) :
    (l.foldl (fun a j => a.set! j true) init).getD x false = (init.getD x false || decide (x ∈ l)) := by
  induction l generalizing init with
  | nil => simp
  | cons j l ih =>
    rw [List.foldl_cons, ih _ (by rw [Array.size_set!]; exact hx)]
    rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds]
    by_cases hjx : j = x
    · subst hjx; simp [hx]
    · simp [hjx, Ne.symm hjx]

/-- Binding in `Id` applies the continuation. -/
theorem Id.bind_eq_apply {α β : Type u} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl

/-- A prefix of `List.range' s n` (step one) is `List.range' s t`. -/
theorem List.take_range'_of_le {s n t : ℕ} (ht : t ≤ n) : (List.range' s n).take t = List.range' s t := by
  rw [show n = t + (n - t) by omega, ← List.range'_append_1, List.take_left']
  simp
