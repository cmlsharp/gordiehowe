-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Lowering
public import GordieHowe.Foundations.Algebra.IntLift
public import GordieHowe.Foundations.Algebra.ReconstructSum

@[expose] public section

/-!
# The modular equality: integers in an interval

`assert_mod(lhs, rhs, m)` declares `lhs ≡ rhs (mod m)` over the integers
(`lib/gordiehowe/compiler/mod.h`). The lowering reads the integer interval of the two sides from
interval propagation before the range planner runs (Bit values, range requests, constants, operators
with a row sum) and picks a form from `m`, the characteristic `p` and that interval.

This file holds the integer facts that the plan's realizations of a modular equality read
(`GordieHowe/Language/Realizations/RealizeMod.lean`, `GordieHowe/Language/Realizations/RealizeCommitted.lean`,
`GordieHowe/Language/Realizations/RealizeGrouped.lean`). `IntIn lo hi z v` states that the field value `v` is the
cast of the integer `z ∈ [lo, hi]`. `IntIn.sub_eq_natCast` lifts a shifted equation `v - c = n` in
the field, with `n < M`, to the integers when `hi - c < p` and `M - 1 + (c - lo) < p`. Every form
but the field equality gives `v - m qlo = m q` in the field with `q` the cast of a natural below a
bound; with `c = m qlo` the lift makes the integer of `v` a multiple of `m`. Here
`qlo = ⌈lo / m⌉` is the quotient's lower end (`mod.h`, `quotient_shape`).
-/

namespace GordieHowe
open RealizedProgram.ProofSystem.PhaseLayout Range
open scoped NNReal

/-! ### Integers in an interval -/

/-- **`v` is the cast of the integer `z` of `[lo, hi]`.** -/
structure IntIn {F : Type*} [Ring F] (lo hi z : ℤ) (v : F) : Prop where
  lo_le : lo ≤ z
  le_hi : z ≤ hi
  cast_eq : (z : F) = v

namespace IntIn

variable {F : Type*} [Field F]

variable {p : ℕ} [CharP F p]

/-- **A shifted equation lifts to the integers**: `v - c = n` in the field, with `v` the cast of
`z ∈ [lo, hi]` and `n < M`, holds over the integers when `hi - c < p` and `M - 1 + (c - lo) < p`
(the difference `z - c - n` then lies in `(-p, p)`). -/
theorem sub_eq_natCast {lo hi z c : ℤ} {n M : ℕ} {v : F} (hz : IntIn lo hi z v)
    (hhi : hi - c < p) (hlo : (M : ℤ) - 1 + (c - lo) < p) (hn : n < M)
    (h : v - (c : F) = n) : z - c = n := by
  have h0 : ((z - c - n : ℤ) : F) = 0 := by
    push_cast
    rw [hz.cast_eq, h]
    ring
  have hdvd : (p : ℤ) ∣ z - c - n := (CharP.intCast_eq_zero_iff F p _).mp h0
  have h1 := hz.lo_le
  have h2 := hz.le_hi
  have hn' : (n : ℤ) < M := by exact_mod_cast hn
  have : z - c - n = 0 :=
    Int.eq_zero_of_abs_lt_dvd hdvd (abs_lt.mpr ⟨by omega, by omega⟩)
  omega

end IntIn

end GordieHowe
