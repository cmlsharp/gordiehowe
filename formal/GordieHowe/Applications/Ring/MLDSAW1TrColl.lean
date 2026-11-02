-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1
public import GordieHowe.Foundations.Probability.Advantage
public import GordieHowe.Foundations.ToMathlib.PMFBadSet

@[expose] public section

/-!
# Collisions of the public-key hash among honest keys

The message representative of the ML-DSA ring publishing `w₁` is read at the point
`(tr, bm)` with `tr = H(pkEncode(ρ, t₁), 64)` the public-key hash (FIPS 204 Algorithm 6, line 6;
`pubTr`). The hash `H` is computed by the primitives, not read from the random oracle, and the
published key also carries `t₀`, which `tr` does not hash. So two honest users with distinct
published keys can share their message-representative points exactly when their `tr` agree.

- `trCollAt prims n`: the probability, over `n` uniform key seeds, that two users have distinct
  published keys with the same public-key hash.
- `tsum_le_add_trCollAt`: an average over the key seeds of a `[0, 1]`-valued quantity is at most
  its average over the seeds without a collision plus `trCollAt`.
- `eq_of_pubTr_eq`: without a collision, equal public-key hashes mean equal published keys.

Remark (not a theorem here): `tr` is 64 bytes of SHAKE256 output, `pkEncode` is injective, and
SHAKE256 has 256-bit collision strength (FIPS 202, Appendix A.1, Table 4); for keys whose
`(ρ, t₁)` differ, a collision of `tr` is a SHAKE256 collision. Keys with equal `(ρ, t₁)` and
different `t₀` also collide, and their probability over the seeds is not bounded here.
-/

open scoped ENNReal

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.IOP

variable {p : Params} (prims : Primitives p) [NTTRingOps]

/-- **The public-key-hash collision probability of `n` honest keys**: over `n` uniform key
seeds, the probability that two users `i ≠ j` have distinct published keys
(`keyGen`, `(ρ, t₁, t₀)`) with the same public-key hash `pubTr` (FIPS 204 Algorithm 6). -/
noncomputable def trCollAt (n : ℕ) : ℝ≥0∞ :=
  Pr[seeds ~ PMF.uniformOfFintype (Fin n → Bytes 32) :
    ∃ i j, i ≠ j ∧
      pubTr prims (keyGen prims (seeds i)).1 = pubTr prims (keyGen prims (seeds j)).1 ∧
      (keyGen prims (seeds i)).1 ≠ (keyGen prims (seeds j)).1]

/-- `trCollAt` is a probability. -/
theorem trCollAt_le_one (n : ℕ) : trCollAt prims n ≤ 1 := by
  unfold trCollAt
  exact PMF.toOuterMeasure_apply_le_one _ _

/-- **One user has no collision**: `trCollAt prims 1 = 0`. -/
theorem trCollAt_one : trCollAt prims 1 = 0 := by
  unfold trCollAt
  have h : {seeds : Fin 1 → Bytes 32 | ∃ i j, i ≠ j ∧
      pubTr prims (keyGen prims (seeds i)).1 = pubTr prims (keyGen prims (seeds j)).1 ∧
      (keyGen prims (seeds i)).1 ≠ (keyGen prims (seeds j)).1} = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun _ ⟨i, j, hij, _⟩ => hij (Subsingleton.elim i j)
  rw [h, MeasureTheory.measure_empty]

/-- **Splitting off the collisions of the public-key hash**: the average over `n` uniform key seeds
of a `[0, 1]`-valued quantity `f` is at most its average over the seeds without a collision plus
`trCollAt prims n` (`PMF.tsum_mul_le_add_toOuterMeasure`). -/
theorem tsum_le_add_trCollAt (n : ℕ) (f : (Fin n → Bytes 32) → ℝ≥0∞) (hf : ∀ seeds, f seeds ≤ 1) :
    ∑' seeds, PMF.uniformOfFintype (Fin n → Bytes 32) seeds * f seeds ≤
      ∑' seeds, PMF.uniformOfFintype (Fin n → Bytes 32) seeds *
        {seeds | ∃ i j, i ≠ j ∧
            pubTr prims (keyGen prims (seeds i)).1 = pubTr prims (keyGen prims (seeds j)).1 ∧
            (keyGen prims (seeds i)).1 ≠ (keyGen prims (seeds j)).1}ᶜ.indicator f seeds +
        trCollAt prims n := by
  exact PMF.tsum_mul_le_add_toOuterMeasure _ f hf _

/-- **Without a collision, equal public-key hashes mean equal published keys.** -/
theorem eq_of_pubTr_eq {n : ℕ} {seeds : Fin n → Bytes 32}
    (h : ¬ ∃ i j, i ≠ j ∧
      pubTr prims (keyGen prims (seeds i)).1 = pubTr prims (keyGen prims (seeds j)).1 ∧
      (keyGen prims (seeds i)).1 ≠ (keyGen prims (seeds j)).1)
    {i j : Fin n} (hij : pubTr prims (keyGen prims (seeds i)).1 =
      pubTr prims (keyGen prims (seeds j)).1) :
    (keyGen prims (seeds i)).1 = (keyGen prims (seeds j)).1 := by
  by_cases hne : i = j
  · rw [hne]
  · by_contra hk
    exact h ⟨i, j, hne, hij, hk⟩

end GordieHowe.Ring.MLDSAW1
