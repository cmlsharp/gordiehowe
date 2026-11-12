-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.Anonymity

@[expose] public section

/-!
# Refusal rules that answer differently

- `ite_some_ne_ite_some_iff`: two refusal rules `p` and `p ∧ q` answer differently exactly when
  `p` holds and `q` fails.
-/

namespace GordieHowe.Ring

open IOP GordieHowe.SPBCS GordieHowe.QROM
open scoped NNReal ENNReal BigOperators

variable {N : ℕ} {RMsg : Type}


/-! The instances of the restricted signer's types: those of `S`; its refusal rule is decided by
`S`'s and classically on `Ok`. -/


/-- Two refusal rules `p` and `p ∧ q` answer differently exactly when `p` holds and `q` fails. -/
theorem ite_some_ne_ite_some_iff {α : Type*} (p q : Prop) {_ : Decidable p}
    {_ : Decidable (p ∧ q)} (x : α) : ((if p then some x else none) ≠ (if p ∧ q then some x else none)) ↔ (p ∧ ¬ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]


end GordieHowe.Ring
