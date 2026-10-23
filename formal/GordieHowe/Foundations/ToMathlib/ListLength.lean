-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-!
# Counting lists of bounded length

Candidates for upstreaming, next to Mathlib's `List.finite_length_le`
(`Mathlib/Data/Set/Finite/List.lean`).
-/

namespace List

/-- **There are `|α|^n` lists of length `n`** over a finite type `α`. -/
theorem ncard_length_eq (α : Type*) [Fintype α] (n : ℕ) :
    {l : List α | l.length = n}.ncard = Fintype.card α ^ n := by
  rw [← Nat.card_coe_set_eq]
  change Nat.card (List.Vector α n) = _
  rw [Nat.card_eq_fintype_card, card_vector]

/-- **Fewer than `2^(n+1)` bit strings have length at most `n`.** -/
theorem ncard_length_le_bool (n : ℕ) : {l : List Bool | l.length ≤ n}.ncard < 2 ^ (n + 1) := by
  induction n with
  | zero =>
    have h : {l : List Bool | l.length ≤ 0} = {[]} := by
      ext l
      simp
    rw [h, Set.ncard_singleton]
    decide
  | succ n ih =>
    have h : {l : List Bool | l.length ≤ n + 1} =
        {l | l.length ≤ n} ∪ {l | l.length = n + 1} := by
      ext l
      simp [Nat.le_succ_iff]
    have hu := Set.ncard_union_le {l : List Bool | l.length ≤ n} {l | l.length = n + 1}
    rw [ncard_length_eq, Fintype.card_bool] at hu
    rw [h, pow_succ 2 (n + 1)]
    omega

end List
