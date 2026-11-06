-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Check

/-!
# Bounded decisions through Boolean checks

The check's Boolean pass avoids nested decision-proof recursion for large bounds.
-/

public section

namespace GordieHowe.RealizedProgram

/-- **A decidable predicate holds below a bound**, checked by a Boolean pass over the range.
Unlike a nested bounded-quantifier decision, the kernel evaluates no chain of proof constructors. -/
@[expose] def allLtB (n : Nat) (p : Nat → Prop) [DecidablePred p] : Bool :=
  (List.range n).all (fun i => decide (p i))

/-- **The Boolean range check states the bounded universal proposition.** -/
theorem allLtB_iff (n : Nat) (p : Nat → Prop) [DecidablePred p] :
    allLtB n p = true ↔ ∀ i < n, p i := by
  simp only [allLtB, List.all_eq_true, decide_eq_true_eq, List.mem_range]

/-- **A bounded universal decision through its Boolean range check**, so large certificate
bounds do not require a deeper kernel recursion limit. -/
@[expose] def decidableAllLt (n : Nat) (p : Nat → Prop) [DecidablePred p] : Decidable (∀ i < n, p i) :=
  decidable_of_iff (allLtB n p = true) (allLtB_iff n p)

end GordieHowe.RealizedProgram
