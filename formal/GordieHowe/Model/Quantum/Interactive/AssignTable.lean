-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.Basic

@[expose] public section

/-!
# Assignment tables

An assignment list (Unruh 2017, ePrint 2017/398, section 2, p. 7) reprograms an oracle; only its
last assignment to each input matters (`reprogram_apply_eq_lastAssign`,
`GordieHowe/Model/Quantum/Core/Reprogram.lean`). An adversary that patches its own queries holds
the assignments in force as a finite table `X → Option Y`, the last assignment to each input.

- `reprogT T H`: the oracle `H` with the inputs of the table `T` answered by `T`.
  `reprogram_eq_reprogT`: reprogramming by a list is reprogramming by its table `lastAssign`;
  `reprogT_apply_of_none`: off the table it is `H`.
- `overT T₁ T₂`: the table `T₁` with the entries of `T₂` taking precedence.
  **Order semantics**: `lastAssign_append` (the table of `a ++ b` is that of `a` overridden by
  that of `b`), `reprogT_overT` (reprogramming by an overridden table is reprogramming twice, the
  later table last), `reprogram_append_eq_reprogT` (the oracle reprogrammed by a concatenation is
  read through the overridden table), `foldT`, `lastAssign_flatten` (the table of a concatenation
  of lists, in order).
-/

namespace GordieHowe.Quantum

section Table

variable {X Y : Type*} [DecidableEq X]

/-- **The oracle `H` read through the table `T`**: an input with an entry gets the entry. -/
def reprogT (T : X → Option Y) (H : X → Y) : X → Y :=
  fun x => (T x).getD (H x)

omit [DecidableEq X] in
theorem reprogT_apply (T : X → Option Y) (H : X → Y) (x : X) : reprogT T H x = (T x).getD (H x) :=
  rfl

omit [DecidableEq X] in
/-- **Off the table, the oracle read through the table is the oracle.** -/
theorem reprogT_apply_of_none {T : X → Option Y} (H : X → Y) {x : X} (h : T x = none) :
    reprogT T H x = H x := by
  simp [reprogT, h]

omit [DecidableEq X] in
/-- The empty table changes nothing. -/
@[simp]
theorem reprogT_none (H : X → Y) : reprogT (fun _ => none) H = H :=
  rfl

/-- **Reprogramming by a list is reading through its table** of last assignments. -/
theorem reprogram_eq_reprogT (H : X → Y) (ass : List (Assignment X Y)) :
    H.reprogram ass = reprogT (lastAssign ass) H :=
  funext fun x => reprogram_apply_eq_lastAssign H ass x

/-- **The table `T₁` overridden by `T₂`**: the entry of `T₂` where it has one, else that of
`T₁`. -/
def overT (T₁ T₂ : X → Option Y) : X → Option Y :=
  fun x => (T₂ x).or (T₁ x)

omit [DecidableEq X] in
@[simp]
theorem overT_none_left (T : X → Option Y) : overT (fun _ => none) T = T :=
  funext fun x => by cases h : T x <;> simp [overT, h]

omit [DecidableEq X] in
@[simp]
theorem overT_none_right (T : X → Option Y) : overT T (fun _ => none) = T :=
  funext fun _ => rfl

omit [DecidableEq X] in
theorem overT_assoc (T₁ T₂ T₃ : X → Option Y) : overT (overT T₁ T₂) T₃ = overT T₁ (overT T₂ T₃) :=
  funext fun x => by
    simp only [overT]
    cases T₃ x <;> cases T₂ x <;> rfl

/-- **Order semantics of assignment lists**: the last assignment in `a ++ b` is the last one in
`b`, else the last one in `a`. -/
theorem lastAssign_append (a b : List (Assignment X Y)) :
    lastAssign (a ++ b) = overT (lastAssign a) (lastAssign b) := by
  induction b using List.reverseRecOn with
  | nil => rw [List.append_nil]; exact (overT_none_right _).symm
  | append_singleton l c ih =>
    funext x
    rw [← List.append_assoc]
    rw [lastAssign_append_singleton, congrFun ih x]
    simp only [overT]
    rw [lastAssign_append_singleton]
    by_cases h : c.input = x <;> simp [h]

omit [DecidableEq X] in
/-- **Reading through an overridden table is reading through the two tables**, the later one
last. -/
theorem reprogT_overT (T₁ T₂ : X → Option Y) (H : X → Y) :
    reprogT (overT T₁ T₂) H = reprogT T₂ (reprogT T₁ H) :=
  funext fun x => by cases h : T₂ x <;> simp [reprogT, overT, h]

/-- **The oracle reprogrammed by a concatenation** is `H` read through the table of the first
list overridden by that of the second. -/
theorem reprogram_append_eq_reprogT (H : X → Y) (a b : List (Assignment X Y)) :
    H.reprogram (a ++ b) = reprogT (overT (lastAssign a) (lastAssign b)) H := by
  rw [reprogram_eq_reprogT, lastAssign_append]

/-- **The tables of a list of tables, overridden in order.** -/
def foldT (l : List (X → Option Y)) : X → Option Y :=
  l.foldl overT fun _ => none

omit [DecidableEq X] in
@[simp]
theorem foldT_nil : foldT ([] : List (X → Option Y)) = fun _ => none :=
  rfl

omit [DecidableEq X] in
theorem foldT_append_singleton (l : List (X → Option Y)) (T : X → Option Y) :
    foldT (l ++ [T]) = overT (foldT l) T := by
  simp [foldT, List.foldl_append]

/-- **The table of a concatenation of assignment lists** is the tables of the lists overridden in
order. -/
theorem lastAssign_flatten (l : List (List (Assignment X Y))) :
    lastAssign l.flatten = foldT (l.map lastAssign) := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.flatten_append, List.flatten_singleton, lastAssign_append, ih, List.map_append,
      List.map_singleton, foldT_append_singleton]

end Table

end GordieHowe.Quantum
