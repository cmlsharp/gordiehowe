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
- `knowledgeErrorROMTyped k t kq T κ S`: the classical error with the round errors and the
  collisions charged by entry class, `t κ + S + κ + (t + kq)(max 2 T + 1)(t + kq) / 2^(8k)` for
  `S` the sum of the round errors and `T` the number of Merkle trees; at most
  `knowledgeErrorROM k (t + kq) c cP κ` when `S + κ ≤ kq κ` and `max 2 T ≤ max 2 c + cP`
  (`knowledgeErrorROMTyped_le`).

The spBCS compiler (`GordieHowe.SPBCS`, `GordieHowe/SPBCS/Knowledge.lean`) states its bounds with
them.
-/

namespace GordieHowe.SPBCS
open GordieHowe.QROM
open scoped ENNReal NNReal

/-- **The knowledge error** of the QROM knowledge bound: the oracle-simulation term
`2√(kq/|Out|)` and the instability term `6t²(κ + (max 2 c + cP + 1)t/2^(8k))`, with the extra
digests `cP` of the digest seeding added to the digests of one input. -/
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

/-- **The classical knowledge error with the round errors charged by entry class**: `t · κ`
for the algorithm's steps, the sum `S` of the round errors and one `κ` for the verifier's steps,
and at each of the `t + kq` steps the collision bound `(max 2 T + 1)(t + kq) / 2^(8k)` of a
composite with `T` Merkle trees: `t κ + S + κ + (t + kq)(max 2 T + 1)(t + kq) / 2^(8k)`. -/
noncomputable def knowledgeErrorROMTyped (k t kq T : ℕ) (κ S : ℝ≥0) : ℝ≥0∞ :=
  t * (κ : ℝ≥0∞) + S + κ +
    (t + kq : ℕ) * ((((max 2 T + 1) * (t + kq) : ℕ) : ℝ≥0∞) / 2 ^ (8 * k))

/-- **The typed error is monotone** in the tree count, the largest round error and the sum. -/
theorem knowledgeErrorROMTyped_mono {k t kq T T' : ℕ} {κ κ' S S' : ℝ≥0} (hT : T ≤ T')
    (hκ : κ ≤ κ') (hS : S ≤ S') :
    knowledgeErrorROMTyped k t kq T κ S ≤ knowledgeErrorROMTyped k t kq T' κ' S' := by
  unfold knowledgeErrorROMTyped
  have h1 : ((κ : ℝ≥0∞)) ≤ κ' := by exact_mod_cast hκ
  have h2 : ((S : ℝ≥0∞)) ≤ S' := by exact_mod_cast hS
  have h3 : max 2 T ≤ max 2 T' := max_le_max le_rfl hT
  gcongr

/-- **The typed error is monotone in the adversary's queries.** -/
theorem knowledgeErrorROMTyped_mono_queries {k t t' kq T : ℕ} {κ S : ℝ≥0} (ht : t ≤ t') :
    knowledgeErrorROMTyped k t kq T κ S ≤ knowledgeErrorROMTyped k t' kq T κ S := by
  unfold knowledgeErrorROMTyped
  gcongr

/-- **The typed error is finite.** -/
theorem knowledgeErrorROMTyped_ne_top (k t kq T : ℕ) (κ S : ℝ≥0) :
    knowledgeErrorROMTyped k t kq T κ S ≠ ⊤ := by
  unfold knowledgeErrorROMTyped
  finiteness

/-- **The typed error as a real number.** -/
theorem knowledgeErrorROMTyped_toReal (k t kq T : ℕ) (κ S : ℝ≥0) :
    (knowledgeErrorROMTyped k t kq T κ S).toReal =
      t * (κ : ℝ) + S + κ +
        (t + kq : ℕ) * ((((max 2 T + 1) * (t + kq) : ℕ) : ℝ) / 2 ^ (8 * k)) := by
  unfold knowledgeErrorROMTyped
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_add (by finiteness)
      (by finiteness), ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_add,
    ENNReal.toReal_natCast]

/-- **The typed error is at most `(t + kq)(κ + D (t + kq) / 2^(8k))`** when the round errors and
one more are at most `kq` largest (`hS`) and `max 2 T + 1 ≤ D` (`hD`). -/
theorem knowledgeErrorROMTyped_le_mul (k t kq T D : ℕ) {κ S : ℝ≥0} (hS : S + κ ≤ kq * κ)
    (hD : max 2 T + 1 ≤ D) :
    knowledgeErrorROMTyped k t kq T κ S ≤
      ((t + kq : ℕ) : ℝ≥0∞) * ((κ : ℝ≥0∞) + ((D * (t + kq) : ℕ) : ℝ≥0∞) / 2 ^ (8 * k)) := by
  rw [knowledgeErrorROMTyped, mul_add ((t + kq : ℕ) : ℝ≥0∞)]
  refine add_le_add ?_ ?_
  · have : ((S + κ : ℝ≥0) : ℝ≥0∞) ≤ (kq * κ : ℝ≥0) := by exact_mod_cast hS
    push_cast at this ⊢
    calc (t : ℝ≥0∞) * κ + S + κ = t * κ + (S + κ) := by ring
      _ ≤ t * κ + kq * κ := by gcongr
      _ = (t + kq) * κ := by ring
  · gcongr

/-- **The typed error is at most the uniform one** when the round errors and one more are at
most `kq` largest (`hS`) and `max 2 T ≤ max 2 c + cP` (`hT`). -/
theorem knowledgeErrorROMTyped_le (k t kq T c cP : ℕ) {κ S : ℝ≥0} (hS : S + κ ≤ kq * κ)
    (hT : max 2 T ≤ max 2 c + cP) :
    knowledgeErrorROMTyped k t kq T κ S ≤ knowledgeErrorROM k (t + kq) c cP κ :=
  knowledgeErrorROMTyped_le_mul k t kq T _ hS (by omega)

end GordieHowe.SPBCS
