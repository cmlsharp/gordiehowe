-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Range

@[expose] public section

/-!
# Small combinators for `Check` composition

`Check.and` is the verdict-and-needle monoid every gadget builds its checks
from. These facts about it (right identity, associativity, and how
acceptance and needle membership pass through it) are used wherever a gadget
assembles many checks by folding, as `GordieHowe.Falcon512.NativeNorm.run` does.
-/

namespace GordieHowe.Check

variable {K : Type*}

@[simp] theorem and_pass (a : Check K) : a.and Check.pass = a := by
  cases a
  simp [Check.and, Check.pass]

theorem and_assoc (a b c : Check K) : (a.and b).and c = a.and (b.and c) := by
  cases a
  cases b
  cases c
  simp [Check.and, Bool.and_assoc, List.append_assoc]

/-- If a conjoined check accepts, its left component accepts. -/
theorem ok_of_and_left {a b : Check K} (h : (a.and b).ok = true) : a.ok = true :=
  (Bool.and_eq_true_iff.mp h).1

/-- If a conjoined check accepts, its right component accepts. -/
theorem ok_of_and_right {a b : Check K} (h : (a.and b).ok = true) : b.ok = true :=
  (Bool.and_eq_true_iff.mp h).2

theorem needles_subset_and_left (a b : Check K) : ∀ x ∈ a.needles, x ∈ (a.and b).needles := by
  intro x hx
  simp only [Check.and_needles, List.mem_append]
  exact Or.inl hx

theorem needles_subset_and_right (a b : Check K) : ∀ x ∈ b.needles, x ∈ (a.and b).needles := by
  intro x hx
  simp only [Check.and_needles, List.mem_append]
  exact Or.inr hx

/-- The needles of a `Check.all` built from `(List.finRange n).map f` count as the sum of
each element's own needle count, whatever that count depends on. Upstream candidate: this
is really a `List`/`Check.all` fact, not specific to any gadget. -/
theorem check_all_needles_length {n : ℕ} (f : Fin n → Check K)
    (g : Fin n → ℕ) (hf : ∀ i, (f i).needles.length = g i) :
    (Check.all ((List.finRange n).map f)).needles.length = ((List.finRange n).map g).sum := by
  rw [Check.all_needles, List.length_flatMap, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact hf i

section InTable

variable [Field K] [DecidableEq K]

omit [DecidableEq K] in
/-- If a conjoined check's needles all lie in the table, so do its left component's. -/
theorem and_inTable_left {T : ℕ} {a b : Check K}
    (h : Range.InTable T (a.and b).needles) : Range.InTable T a.needles :=
  fun v hv => h v (Check.needles_subset_and_left a b v hv)

omit [DecidableEq K] in
/-- If a conjoined check's needles all lie in the table, so do its right component's. -/
theorem and_inTable_right {T : ℕ} {a b : Check K}
    (h : Range.InTable T (a.and b).needles) : Range.InTable T b.needles :=
  fun v hv => h v (Check.needles_subset_and_right a b v hv)

omit [DecidableEq K] in
/-- The lookup requests of a conjunction are in the table when both parts' are. -/
theorem and_inTable {T : ℕ} {a b : Check K} (ha : Range.InTable T a.needles)
    (hb : Range.InTable T b.needles) : Range.InTable T (a.and b).needles := by
  intro x hx
  rw [Check.and_needles, List.mem_append] at hx
  exact hx.elim (ha x) (hb x)

end InTable

end GordieHowe.Check
