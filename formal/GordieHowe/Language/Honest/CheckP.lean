-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Honest.CheckValues

@[expose] public section

/-!
# GordieHowe: checks over two aligned lists

`allIdx2` checks a predicate at every index of two lists read together, the second padded with a
default, and `allIdx2_sound` gives the predicate at every index of the first.
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## One pass over two lists -/

/-- **A check of each element of `l` with the element of `m` at its position** (`d` past `m`'s
end), the positions from `i`. -/
def allIdx2 {α β : Type} (p : ℕ → α → β → Bool) (d : β) : List α → List β → ℕ → Bool
  | [], _, _ => true
  | x :: xs, m, i => p i x (m.headD d) && allIdx2 p d xs m.tail (i + 1)

theorem allIdx2_sound {α β : Type} [Inhabited α] (p : ℕ → α → β → Bool) (d : β) :
    ∀ (l : List α) (m : List β) (i : ℕ), allIdx2 p d l m i = true →
      ∀ j < l.length, p (i + j) (l.getD j default) (m.getD j d) = true
  | [], _, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | x :: xs, m, i, h, j, hj => by
    unfold allIdx2 at h
    simp only [Bool.and_eq_true] at h
    cases j with
    | zero =>
      cases m <;> simpa using h.1
    | succ j =>
      have := allIdx2_sound p d xs m.tail (i + 1) h.2 j (by simpa using hj)
      rw [show i + (j + 1) = i + 1 + j by omega]
      cases m <;> simpa using this

variable (ir : RealizedProgram) (primeNodes : ℕ → List String)

/-! ## The committed-digits `mod_q`s -/

variable (L : ℕ → ℕ → Option Ivl)

end GordieHowe.RealizedProgram
