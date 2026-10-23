-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Fields.GF2_256Dual
public import GordieHowe.Foundations.Fields.Counter
public import GordieHowe.Language.Realizations.MemoryShuffle
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

@[expose] public section

/-!
# The ML-DSA-44 H field data of `GF(2²⁵⁶)`

The `GF(2²⁵⁶)` analogue of `GordieHowe/Applications/MLDSA44/Fields/GF2_128.lean`, at the constants of `lib/gf2k/gf2_256.h`
(class `GF2_256<>`, `subfield_log_bits = 4`, commit `f21acd4`):

* `gf2_256SelectionField128`: `gf2_256SelectionField` (the subfield `GF(2¹⁶)`, `X = x`,
  `e i = g ^ i`, `g` the subfield generator) at the selection degree `128`.
* `gf2_256Theta`: `θ = as_counter(21845)` (`ml_dsa_hash_circuit.h:453`;
  `lib/gordiehowe/examples/mldsa/sample_in_ball.h`). `as_counter(a)` multiplies
  `1 + (counter_beta(i) + 1) · bit_i` over `i < 16` (`gf2_256.h:316-327`), with
  `counter_beta_[i] = g ^ (2 ^ i)` (lines 146-150), so it is `g ^ a` (`asCounter_eq_pow`). With `g`
  of order `65535 = 3 · 21845`, `θ = g ^ 21845` has order `3`, and `θ ^ 2 + θ + 1 = 0`.
-/

namespace GordieHowe

/-- The selection field data at the ML-DSA-44 selection degree `128`. -/
def gf2_256SelectionField128 : SelectionField GF2_256 128 :=
  gf2_256SelectionField.ofLE (by decide)

/-- `θ = as_counter(21845) = g ^ 21845` has order `3`. -/
theorem orderOf_gf2_256SubfieldGen_pow_21845 : orderOf (gf2_256SubfieldGen ^ 21845) = 3 := by
  rw [orderOf_pow_of_dvd (by norm_num) (by rw [orderOf_gf2_256SubfieldGen]; norm_num),
    orderOf_gf2_256SubfieldGen]

/-- The memory shuffle's ternary constant `θ = as_counter(21845)`
(`ml_dsa_hash_circuit.h:442`). -/
def gf2_256Theta : MemoryShuffle.Theta GF2_256 where
  θ := gf2_256SubfieldGen ^ 21845
  θ_sq := by
    have h := (IsPrimitiveRoot.orderOf (gf2_256SubfieldGen ^ 21845)).geom_sum_eq_zero
      (by rw [orderOf_gf2_256SubfieldGen_pow_21845]; norm_num)
    rw [orderOf_gf2_256SubfieldGen_pow_21845, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one, pow_zero, pow_one] at h
    rw [← h]
    ring

/-- `θ` is the C++ `as_counter(21845)` over the counter basis `g ^ (2 ^ i)`. -/
theorem gf2_256Theta_eq_asCounter : gf2_256Theta.θ = asCounter gf2_256SubfieldGen 16 21845 :=
  (asCounter_eq_pow _ (by norm_num)).symm

/-- `θ` lies in the selection subfield. -/
theorem gf2_256Theta_mem : gf2_256Theta.θ ∈ gf2_256SelectionField128.E :=
  gf2_256Subfield.pow_mem gf2_256SubfieldGen_mem _

end GordieHowe
