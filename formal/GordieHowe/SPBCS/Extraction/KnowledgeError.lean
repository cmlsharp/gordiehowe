-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.Lifting
public import GordieHowe.Model.QROM.Oracle

@[expose] public section

/-!
# The knowledge errors of a compiled argument

The error formulas of the knowledge bounds of a compiled verifier, at digests of `k` bytes, `c`
digests per `transcript` input and round errors at most `κ`:

- `knowledgeError k e kq t c cP κ`: in the QROM (CMS19 Theorem 8.6 (2)), the oracle-simulation
  term `2√(kq/|Out|)` for `kq` verifier queries and the instability term
  `6t²(κ + (max 2 c + cP + 1)t/2^(8k))` at `t` queries in all, with `cP` extra digests per input
  (the digest seeding of joined branches' final digests);
- `knowledgeErrorROM k t c cP κ`: in the classical random-oracle model,
  `t (κ + (max 2 c + cP + 1) t / 2^(8k))`;
- `knowledgeErrorFullPast k e kq t c κ`: the QROM error without extra digests, `max 2 c + 1` in
  place of `max 2 c + cP + 1`.

The spBCS compiler (`GordieHowe.SPBCS`, `GordieHowe/SPBCS/Knowledge.lean`) states its bounds with the first
two; the full-past compiler (`GordieHowe.SPBCS.FullPast`, `GordieHowe/SPBCS/FullPast/Online.lean`) with the third.
-/

namespace GordieHowe.SPBCS
open GordieHowe.QROM
open scoped ENNReal NNReal

/-- **The knowledge error of the full-past compiler** (`FullPast`) in the QROM: the
oracle-simulation term `2√(kq/|Out|)` and the instability term `6t²(κ + (max 2 c + 1)t/2^(8k))`.
-/
noncomputable def knowledgeErrorFullPast (k e kq t c : ℕ) (κ : ℝ≥0) : ℝ≥0∞ :=
  2 * esqrt (kq / Fintype.card (Out k e)) +
    6 * (t : ℝ≥0∞) ^ 2 * ((κ : ℝ≥0∞) + (((max 2 c + 1) * t : ℕ) : ℝ≥0∞) / 2 ^ (8 * k))

/-! ### With extra digests per input -/

/-- **The knowledge error** of the QROM knowledge bound: the knowledge error
`knowledgeErrorFullPast` with the extra digests `cP` of the digest seeding added to the digests
of one input. -/
noncomputable def knowledgeError (k e kq t c cP : ℕ) (κ : ℝ≥0) : ℝ≥0∞ :=
  2 * esqrt (kq / Fintype.card (Out k e)) +
    6 * (t : ℝ≥0∞) ^ 2 * ((κ : ℝ≥0∞) + (((max 2 c + cP + 1) * t : ℕ) : ℝ≥0∞) / 2 ^ (8 * k))

/-- **The classical knowledge error**: `t (κ + (max 2 c + cP + 1) t /
2^(8k))`, the extra digests `cP` of the digest seeding added to the digests of one input. -/
noncomputable def knowledgeErrorROM (k t c cP : ℕ) (κ : ℝ≥0) : ℝ≥0∞ :=
  t * ((κ : ℝ≥0∞) + (((max 2 c + cP + 1) * t : ℕ) : ℝ≥0∞) / 2 ^ (8 * k))

theorem knowledgeErrorROM_mono_error {k t c cP : ℕ} {κ κ' : ℝ≥0} (h : κ ≤ κ') :
    knowledgeErrorROM k t c cP κ ≤ knowledgeErrorROM k t c cP κ' := by
  unfold knowledgeErrorROM
  gcongr

end GordieHowe.SPBCS
