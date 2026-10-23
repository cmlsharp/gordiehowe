-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Range
public import GordieHowe.Foundations.Algebra.IntLift

@[expose] public section

/-!
# The ML-DSA hint weight

```
gadget HintWeight(hsum, needles):
    append ω − hsum to needles
```

`hsum` is the sum of the `K·N` hint wires, accumulated by the UseHint loop and never committed. The
native arm pushes `ω − hsum` into the shared range table `[0, 512)`, the emulated arm into
`[0, 4096)`; the C++ `hint_weight` (`lib/gordiehowe/examples/mldsa/mldsa_gadgets.h`) requests the
same complement needle. Booleanity of the hints is asserted by the UseHint gadget (`assert_is_bit`
natively, `b·(b − 1) = 0` emulated), so soundness takes it as a hypothesis supplied by the UseHint
gadget.

Soundness: with Boolean hints the sum is the hint weight `c ≤ K·N`. If `c > ω`, the needle is
`χ + ω − c ≥ χ + ω − K·N`, outside the table when `K·N + T < χ`.
-/

namespace GordieHowe.MLDSA44.HintWeight

variable {K : Type*} [Field K] [DecidableEq K]

/-- Boolean hint wires sum to the hint weight. -/
theorem sum_eq_card {m : ℕ} {h : Fin m → K} (hbool : ∀ i, h i = 0 ∨ h i = 1) :
    ∑ i, h i = ((Finset.univ.filter fun i => h i = 1).card : K) := by
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases hbool i with h0 | h1 <;> simp [*]

end GordieHowe.MLDSA44.HintWeight
