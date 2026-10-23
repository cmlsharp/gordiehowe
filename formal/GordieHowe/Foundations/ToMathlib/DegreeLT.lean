-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section

/-!
# Natural-degree form of membership in `degreeLT`

Candidate for upstreaming next to `Polynomial.mem_degreeLT`.
-/

namespace Polynomial

variable {R : Type*} [Semiring R] {n : ℕ}

/-- For `0 < n`, a polynomial lies in `degreeLT R n` exactly when its natural degree is below
`n` (the zero polynomial has natural degree `0`). -/
theorem mem_degreeLT_iff_natDegree_lt (hn : 0 < n) {p : R[X]} :
    p ∈ degreeLT R n ↔ p.natDegree < n := by
  by_cases hp : p = 0
  · simp [hp, hn]
  · rw [mem_degreeLT, natDegree_lt_iff_degree_lt hp]

/-- An element of `degreeLT R n`, for `0 < n`, has natural degree below `n`. -/
theorem natDegree_lt_of_mem_degreeLT (hn : 0 < n) (p : degreeLT R n) :
    (p : R[X]).natDegree < n :=
  (mem_degreeLT_iff_natDegree_lt hn).mp p.2

end Polynomial
