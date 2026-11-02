-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.Fintype.Sigma

@[expose] public section

/-!
# Counting lists of bounded length

Candidates for upstreaming, next to Mathlib's `List.finite_length_le`
(`Mathlib/Data/Set/Finite/List.lean`).

- `List.equivSigmaLengthLe`, `List.fintypeLengthLe`: the lists of length at most `n` as the
  vectors of each length `k ≤ n`, and the finite type they form, with compiled code and no
  decision of equality on the entries (`List.finite_length_le` gives only `Finite`).
-/

namespace List

/-- **The lists of length at most `n` are the vectors of each length `k ≤ n`.** -/
def equivSigmaLengthLe (α : Type*) (n : ℕ) :
    {l : List α // l.length ≤ n} ≃ Σ k : Fin (n + 1), List.Vector α k where
  toFun l := ⟨⟨l.1.length, Nat.lt_succ_of_le l.2⟩, ⟨l.1, rfl⟩⟩
  invFun v := ⟨v.2.1, v.2.2.trans_le (Nat.le_of_lt_succ v.1.2)⟩
  left_inv _ := rfl
  right_inv v := by
    obtain ⟨k, l, hl⟩ := v
    exact Sigma.ext (Fin.ext hl) ((Subtype.heq_iff_coe_eq fun _ => by dsimp only; rw [hl]).2 rfl)

/-- **The lists of length at most `n` over a finite type form a finite type**, enumerated through
the vectors of each length (`equivSigmaLengthLe`), with compiled code. -/
abbrev fintypeLengthLe (α : Type*) [Fintype α] (n : ℕ) : Fintype {l : List α // l.length ≤ n} :=
  Fintype.ofEquiv _ (equivSigmaLengthLe α n).symm

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
