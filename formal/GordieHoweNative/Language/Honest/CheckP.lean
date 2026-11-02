-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Honest.CheckValues

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Honest.CheckP`

The definitions of `GordieHowe.Language.Honest.CheckP` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Honest/CheckP.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- **A check of each element of `l` with the element of `m` at its position** (`d` past `m`'s
end), the positions from `i` (`allIdx2_nil`, `allIdx2_cons`), by the recursor: each step matches
on `m` and on the position, so the kernel keeps them evaluated. Compiled code runs `allIdx2C`
(`allIdx2_csimp`). -/
noncomputable def allIdx2 {α β : Type} (p : ℕ → α → β → Bool) (d : β) (l : List α) (m : List β)
    (i : ℕ) : Bool :=
  @List.rec α (fun _ => List β → ℕ → Bool) (fun _ _ => true)
    (fun x _ ih m i => @List.casesOn β (fun _ => Bool) m
      (p i x d && @Nat.casesOn (fun _ => Bool) i (ih [] 1) fun k => ih [] (k + 2))
      fun y ys => p i x y && @Nat.casesOn (fun _ => Bool) i (ih ys 1) fun k => ih ys (k + 2)) l m i

theorem allIdx2_cons {α β : Type} (p : ℕ → α → β → Bool) (d : β) (x : α) (xs : List α)
    (m : List β) (i : ℕ) :
    allIdx2 p d (x :: xs) m i = (p i x (m.headD d) && allIdx2 p d xs m.tail (i + 1)) := by
  cases m <;> cases i <;> rfl

/-- **`allIdx2`, by structural recursion**: the code compiled for it. -/
def allIdx2C {α β : Type} (p : ℕ → α → β → Bool) (d : β) : List α → List β → ℕ → Bool
  | [], _, _ => true
  | x :: xs, m, i => p i x (m.headD d) && allIdx2C p d xs m.tail (i + 1)

@[csimp] theorem allIdx2_csimp : @allIdx2 = @allIdx2C := by
  funext α β p d l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    funext m i
    rw [allIdx2_cons, allIdx2C, ih]

end GordieHowe.RealizedProgram
