-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Gadgets.EmulatedNorm

@[expose] public section

/-!
# The ML-DSA infinity norm

`‖z‖_∞ < bound` with `bound = γ₁ − β`, as a two-sided limb range check of the shifted
coefficient `z + (bound − 1) ∈ [0, 2·bound − 2]`:

```
gadget InfinityNorm(z, needles):
    InfinityNormShifted(z + (bound−1), needles)
gadget InfinityNormShifted(shifted, needles):
    RangeTwoSided(shifted, 2·bound − 1, ·, ·, needles)
```

The C++ `infinity_norm` (`lib/gordiehowe/examples/mldsa/mldsa_gadgets.h`) requests the same
range, `z + (bound − 1)` below `2·bound − 1`.

Native arm: per coefficient, `value = z + (bound − 1)` and the two-sided range check
`range_check_two_sided(value, 2·bound − 1, 512, 2, lo, hi)`
(`lib/schemes/ml_dsa/ml_dsa_logup.h`): `value = Σ_l lo[l]·512^l`,
`(2·bound − 2) − value = Σ_l hi[l]·512^l`, needles `lo[0], hi[0], lo[1], hi[1]`. At ML-DSA-44,
`2·(512² − 1) < q`, so no extra top-limb needles are needed; the case `2·(B^k − 1) ≥ q` (the
ML-DSA-65 native case) is not modelled.

Emulated arm (base `B1 = 4096`, `Ln = 2` limbs): the shifted value is the reconstruction of its own
low limbs and the two-sided range check is applied to it; its first equation holds by definition.

Coefficients are indexed `c = i·N + j` for `i < L`, `j < N`.

This file states the honest-limb fact for these range checks (`radix_spec`): the base-`B`
limbs of a natural below `B^k` reconstruct it and lie in the table.
-/

namespace GordieHowe.MLDSA44.InfinityNorm

variable {K : Type*} [Field K] [DecidableEq K]

omit [DecidableEq K] in
/-- The honest limbs of a natural below `B^k` reconstruct it and lie in the table. -/
theorem radix_spec {B k a : ℕ} (ha : a < B ^ k) :
    Range.reconstruct (K := K) B (List.ofFn fun l : Fin k => ((a / B ^ (l : ℕ) % B : ℕ) : K)) =
        (a : K) ∧
      ∀ v ∈ List.ofFn (fun l : Fin k => ((a / B ^ (l : ℕ) % B : ℕ) : K)), Range.IsNatBelow B v := by
  refine ⟨Falcon512.EmulatedNorm.reconstruct_radixDigits ha, fun v hv => ?_⟩
  obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hv
  exact Falcon512.EmulatedNorm.radixDigit_isNatBelow ha l

end GordieHowe.MLDSA44.InfinityNorm
