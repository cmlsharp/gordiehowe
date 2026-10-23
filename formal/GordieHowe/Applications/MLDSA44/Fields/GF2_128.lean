-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Fields.GF2_128Dual
public import GordieHowe.Foundations.Fields.Counter
public import GordieHowe.Language.Realizations.MemoryShuffle
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

@[expose] public section

/-!
# The ML-DSA-44 H field data of `GF(2¹²⁸)`

The field data the ML-DSA-44 H circuit takes as `field` arguments, at the
constants of `lib/gf2k/gf2_128.h` (class `GF2_128`, `subfield_log_bits = 4`):

* `gf2_128SelectionField128`: the selection field data of `gf2_128SelectionField` (the
  subfield `GF(2¹⁶)`, `X = x`, `e i = g ^ i`, `g` the subfield generator) at the
  selection degree `128`, the length of the candidate stream `out[8..136)`.
* `gf2_128Theta`: `θ = as_counter(21845)`, the constant of the memory shuffle's ternary
  cells (`ml_dsa_hash_circuit.h:453`, `const auto theta = lc_.f_.as_counter(21845).e`;
  GordieHowe's `lib/gordiehowe/examples/mldsa/sample_in_ball.h`). `as_counter(a)` multiplies
  `counter_beta(i) = g ^ (2 ^ i)` over the set bits `i` of `a`
  (`gf2_128.h:335-346`, with `counter_beta_` built at lines 154-157 by repeated squaring
  of `g = kg_`), so it is `g ^ a`. With `g` of order `65535 = 3 · 21845`
  (`orderOf_gf2_128SubfieldGen`), `θ = g ^ 21845` has order `3`, and
  `θ ^ 2 + θ + 1 = 0`.
-/

namespace GordieHowe

/-- The selection field data at the ML-DSA-44 selection degree `128`. -/
def gf2_128SelectionField128 : SelectionField GF2_128 128 :=
  gf2_128SelectionField.ofLE (by decide)

/-- `θ = as_counter(21845) = g ^ 21845` has order `3`. -/
theorem orderOf_gf2_128SubfieldGen_pow_21845 : orderOf (gf2_128SubfieldGen ^ 21845) = 3 := by
  rw [orderOf_pow_of_dvd (by norm_num) (by rw [orderOf_gf2_128SubfieldGen]; norm_num),
    orderOf_gf2_128SubfieldGen]

/-- The memory shuffle's ternary constant `θ = as_counter(21845)`
(`ml_dsa_hash_circuit.h:442`). -/
def gf2_128Theta : MemoryShuffle.Theta GF2_128 where
  θ := gf2_128SubfieldGen ^ 21845
  θ_sq := by
    have h := (IsPrimitiveRoot.orderOf (gf2_128SubfieldGen ^ 21845)).geom_sum_eq_zero
      (by rw [orderOf_gf2_128SubfieldGen_pow_21845]; norm_num)
    rw [orderOf_gf2_128SubfieldGen_pow_21845, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, pow_zero, pow_one] at h
    rw [← h]
    ring

/-- `θ` is the C++ `as_counter(21845)` over the counter basis `g ^ (2 ^ i)`. -/
theorem gf2_128Theta_eq_asCounter : gf2_128Theta.θ = asCounter gf2_128SubfieldGen 16 21845 :=
  (asCounter_eq_pow _ (by norm_num)).symm

/-- `θ` lies in the selection subfield. -/
theorem gf2_128Theta_mem : gf2_128Theta.θ ∈ gf2_128SelectionField128.E :=
  gf2_128Subfield.pow_mem gf2_128SubfieldGen_mem _

end GordieHowe
