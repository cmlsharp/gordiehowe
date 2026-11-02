-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Spec.Rounding
import all LatticeCrypto.MLDSA.Concrete.Rounding
import LatticeCrypto.MLDSA.Concrete.LawBounds

@[expose] public section

/-!
# Counting behind ML-DSA's rejection checks

Exact counts behind the rejection checks of FIPS 204 Algorithm 7 (ML-DSA.Sign_internal), for
general rounding parameters `γ₂` with `2γ₂ ∣ q - 1` and `M = (q - 1)/(2γ₂)` buckets. The counts
go through the representation `x = 2γ₂ · r1 + r0` of `decomposeCoeff_of_repr`; nothing enumerates
`Coeff`.

* `bucket_r0_card`: for every bucket `r1 < M` and every shift `|a| ≤ β`, exactly `2(γ₂ - β) - 1`
  residues `x` have `HighBits(x) = r1` and `|LowBits(x - a)| < γ₂ - β` (the r0-check, line 23, on
  one coordinate with `a = (cs₂)_i`). Decompose's merged bucket `0` has the same count.
  At ML-DSA-44 (`γ₂ = 95232`, `β = 78`) this is `190307`.
* `highBits_sub_eq_of_lowBits`: on that set `HighBits(x - a) = HighBits(x)`.
* `bucket_hint_card`: on that set the hint `MakeHint(-ct₀, w - cs₂ + ct₀)` (line 26) fires for
  `|b| - β` residues if `b < 0` and `r1 ≠ 0`, and `|b| - β - 1` otherwise (truncated at `0`),
  where `b = (ct₀)_i`.
* `box_shift_card`, `zCheck_vec_card`: for `‖v‖∞ ≤ β < γ₁`, the masks `y` of ExpandMask's range
  with `‖y + v‖∞ < γ₁ - β` (the z-check, line 23, with `v = cs₁`) number `2(γ₁ - β) - 1` per
  coefficient and `(2(γ₁ - β) - 1)^(256 l)` per vector, by the bijection `y ↦ y + v`.
* `norm_challenge_mul_le`: a challenge with at most `τ` nonzero coefficients, each `±1`, times
  `s` with `‖s‖∞ ≤ η` has `‖c · s‖∞ ≤ τη = β`, so the shifts above are in range.

* `SigningParams`, `SigningParams.of_isApproved`: the side conditions of these lemmas hold at
  every approved parameter set (`mldsa44`, `mldsa65`, `mldsa87`), and the `_of_approved`
  corollaries state the counts there.
* `norm_challenge_mul_t0_le`, `ct0_check_passes`: `‖t₀‖∞ ≤ 2^(d-1)` gives `‖c · t₀‖∞ ≤ τ · 2^(d-1)`,
  so the ct₀-check (line 28) always passes when `τ · 2^(d-1) < γ₂`. This holds at ML-DSA-65 and
  ML-DSA-87 and fails at ML-DSA-44 (`ct0_floor_mldsa44_fails`).

The statements are generic in `γ₁, γ₂, β, τ, η`; `q` is the vendored `modulus`, shared by every
ML-DSA parameter set.

So the z-check and r0-check pass the same number of masks for every challenge and in every
`HighBits` bucket: their acceptance is independent of `c` and of `w₁`. The hint count is not: it
depends on `ct₀`, and through the sign of `ct₀` on whether the bucket is `0`.
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA44

/-! ### Points of a `HighBits` bucket -/

/-- The residue `2γ₂ · r1 + s` of `Coeff`: the point at offset `s` of the `HighBits` bucket `r1`
(FIPS 204 Algorithm 36 writes `r ≡ r1 · 2γ₂ + r0`). -/
def bucketPoint (γ₂ r1 : ℕ) (s : ℤ) : Coeff :=
  ((((2 * γ₂ * r1 : ℕ) : ℤ) + s : ℤ) : Coeff)

/-- `decomposeCoeff` of a bucket point in the representation range. -/
theorem decomposeCoeff_bucketPoint {γ₂ : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1)
    {r1 : ℕ} {s : ℤ} (hr1 : r1 < (modulus - 1) / (2 * γ₂))
    (hs : (-(γ₂ : ℤ) < s ∧ s ≤ γ₂) ∨ (r1 = 0 ∧ s = -(γ₂ : ℤ))) :
    decomposeCoeff (bucketPoint γ₂ r1 s) γ₂ = (r1, s) :=
  decomposeCoeff_of_repr hγ hdvd hr1 hs

/-- Every residue is the bucket point of its own `Decompose` output. -/
theorem eq_bucketPoint {γ₂ : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1) (x : Coeff) :
    x = bucketPoint γ₂ (highBitsCoeff x γ₂) (lowBitsCoeff x γ₂) := by
  have hrep := (decomposeCoeff_repr hγ hdvd x).val_eq
  have hx : (((x.val : ℤ)) : Coeff) = x := by simp
  unfold bucketPoint highBitsCoeff lowBitsCoeff
  generalize decomposeCoeff x γ₂ = d at hrep ⊢
  rcases hrep with h | h
  · rw [← hx, h]; push_cast; ring
  · rw [← hx, h]; push_cast; simp

/-- Adding an integer to a bucket point moves its offset. -/
theorem bucketPoint_add (γ₂ r1 : ℕ) (s a : ℤ) :
    bucketPoint γ₂ r1 s + (a : Coeff) = bucketPoint γ₂ r1 (s + a) := by
  unfold bucketPoint; push_cast; ring

/-- Two bucket points agree when their integer representatives differ by a multiple of `q`. -/
theorem bucketPoint_eq_of_eq {γ₂ r1 r1' : ℕ} {s s' k : ℤ}
    (h : 2 * (γ₂ : ℤ) * r1 + s = 2 * γ₂ * r1' + s' + k * modulus) :
    bucketPoint γ₂ r1 s = bucketPoint γ₂ r1' s' := by
  unfold bucketPoint
  have : (((2 * γ₂ * r1 : ℕ) : ℤ) + s : ℤ) = ((2 * γ₂ * r1' : ℕ) : ℤ) + s' + k * modulus := by
    push_cast; linarith
  rw [this]; push_cast; simp

/-- **Decompose under a small shift.** If `|LowBits(y) + a| < γ₂`, then `y + a` has the same
`HighBits` as `y` and low part `LowBits(y) + a`. -/
theorem decomposeCoeff_add_of_abs_lt {γ₂ : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1)
    (y : Coeff) {a : ℤ} (h : |lowBitsCoeff y γ₂ + a| < γ₂) :
    decomposeCoeff (y + (a : Coeff)) γ₂ = (highBitsCoeff y γ₂, lowBitsCoeff y γ₂ + a) := by
  rw [eq_bucketPoint hγ hdvd y, bucketPoint_add]
  rw [← eq_bucketPoint hγ hdvd y]
  rw [abs_lt] at h
  exact decomposeCoeff_bucketPoint hγ hdvd (decomposeCoeff_repr hγ hdvd y).high_lt
    (Or.inl ⟨by linarith, by linarith⟩)

/-- **HighBits is unchanged by the shift on the r0-check set.** If `|a| ≤ β` and
`|LowBits(x - a)| < γ₂ - β`, then `HighBits(x - a) = HighBits(x)`. -/
theorem highBits_sub_eq_of_lowBits {γ₂ β : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1)
    (x : Coeff) {a : ℤ} (ha : |a| ≤ β) (hlow : |lowBitsCoeff (x - (a : Coeff)) γ₂| < γ₂ - β) :
    highBitsCoeff (x - (a : Coeff)) γ₂ = highBitsCoeff x γ₂ := by
  have h : |lowBitsCoeff (x - (a : Coeff)) γ₂ + a| < γ₂ := by
    rw [abs_lt] at *; rw [abs_le] at ha; constructor <;> linarith
  have := decomposeCoeff_add_of_abs_lt hγ hdvd (x - (a : Coeff)) h
  rw [sub_add_cancel] at this
  rw [show highBitsCoeff x γ₂ = (decomposeCoeff x γ₂).1 from rfl, this]

/-- `HighBits` and `LowBits` of a bucket point in the representation range. -/
theorem highBits_bucketPoint {γ₂ : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1)
    {r1 : ℕ} {s : ℤ} (hr1 : r1 < (modulus - 1) / (2 * γ₂)) (hs : |s| < γ₂) :
    highBitsCoeff (bucketPoint γ₂ r1 s) γ₂ = r1 ∧ lowBitsCoeff (bucketPoint γ₂ r1 s) γ₂ = s := by
  rw [abs_lt] at hs
  have := decomposeCoeff_bucketPoint hγ hdvd hr1 (s := s) (Or.inl ⟨hs.1, hs.2.le⟩)
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

/-- **`HighBits` near a bucket.** For `-2γ₂ < t < 2γ₂`, the point `2γ₂ · r1 + t` stays in bucket
`r1` exactly when `t ∈ (-γ₂, γ₂]`, or `r1 = 0` and `t = -γ₂` (Decompose's merged bucket `0`).
Needs at least two buckets, `2γ₂ < q - 1`; otherwise every residue is in bucket `0`. -/
theorem highBits_bucketPoint_eq_iff {γ₂ : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1)
    (hM : 2 * γ₂ < modulus - 1) {r1 : ℕ} (hr1 : r1 < (modulus - 1) / (2 * γ₂)) {t : ℤ}
    (ht : -(2 * γ₂ : ℤ) < t ∧ t < 2 * γ₂) :
    highBitsCoeff (bucketPoint γ₂ r1 t) γ₂ = r1 ↔
      (-(γ₂ : ℤ) < t ∧ t ≤ γ₂) ∨ (r1 = 0 ∧ t = -(γ₂ : ℤ)) := by
  obtain ⟨M, hMq⟩ := hdvd
  have hq1 : 1 ≤ modulus := by decide
  have hMdef : (modulus - 1) / (2 * γ₂) = M := by
    rw [hMq, Nat.mul_div_cancel_left _ (by omega)]
  have hdvd : 2 * γ₂ ∣ modulus - 1 := ⟨M, hMq⟩
  rw [hMdef] at hr1
  have hM2 : 2 ≤ M := by
    by_contra h
    have : M ≤ 1 := by omega
    have := Nat.mul_le_mul_left (2 * γ₂) this
    omega
  have hqZ : (modulus : ℤ) = 2 * γ₂ * M + 1 := by
    have : modulus = 2 * γ₂ * M + 1 := by omega
    rw [this]; push_cast; ring
  have hlt : ∀ r, r < M → r < (modulus - 1) / (2 * γ₂) := fun r h => hMdef ▸ h
  have hb : ∀ {r : ℕ} {s : ℤ}, r < M → ((-(γ₂ : ℤ) < s ∧ s ≤ γ₂) ∨ (r = 0 ∧ s = -(γ₂ : ℤ))) →
      highBitsCoeff (bucketPoint γ₂ r s) γ₂ = r := fun hr hs =>
    congrArg Prod.fst (decomposeCoeff_bucketPoint hγ hdvd (hlt _ hr) hs)
  constructor
  · intro h
    by_contra hn
    rcases lt_or_ge (γ₂ : ℤ) t with htop | hbot
    · rcases Nat.lt_or_ge (r1 + 1) M with hnext | hlast
      · rw [bucketPoint_eq_of_eq (r1' := r1 + 1) (s' := t - 2 * γ₂) (k := 0) (by push_cast; ring),
          hb hnext (Or.inl ⟨by linarith, by linarith⟩)] at h
        omega
      · have hr1M : r1 + 1 = M := by omega
        rw [bucketPoint_eq_of_eq (r1' := 0) (s' := t - 2 * γ₂ - 1) (k := 1)
            (by rw [hqZ, ← hr1M]; push_cast; ring)] at h
        rw [hb (by omega) (by
          rcases eq_or_lt_of_le (show -(γ₂ : ℤ) ≤ t - 2 * γ₂ - 1 by linarith) with he | he
          · exact Or.inr ⟨rfl, he.symm⟩
          · exact Or.inl ⟨he, by linarith⟩)] at h
        omega
    · rcases Nat.eq_zero_or_pos r1 with hr0 | hrpos
      · subst hr0
        have htl : t < -(γ₂ : ℤ) := by
          by_contra hc
          rcases eq_or_lt_of_le (not_lt.mp hc) with he | he
          · exact hn (Or.inr ⟨rfl, he.symm⟩)
          · exact hn (Or.inl ⟨he, hbot⟩)
        obtain ⟨M', rfl⟩ : ∃ M', M = M' + 2 := ⟨M - 2, by omega⟩
        rw [bucketPoint_eq_of_eq (r1' := M' + 1) (s' := t + 2 * γ₂ + 1) (k := -1)
            (by rw [hqZ]; push_cast; ring),
          hb (by omega) (Or.inl ⟨by linarith, by linarith⟩)] at h
        omega
      · obtain ⟨r', rfl⟩ : ∃ r', r1 = r' + 1 := ⟨r1 - 1, by omega⟩
        have htl : t ≤ -(γ₂ : ℤ) := by
          by_contra hc; exact hn (Or.inl ⟨by linarith, hbot⟩)
        rw [bucketPoint_eq_of_eq (r1' := r') (s' := t + 2 * γ₂) (k := 0) (by push_cast; ring),
          hb (by omega) (Or.inl ⟨by linarith, by linarith⟩)] at h
        omega
  · exact hb hr1

/-! ### The r0-check set of one bucket -/

/-- The residues `x` in `HighBits` bucket `r1` that pass the r0-check of FIPS 204 Algorithm 7
line 23, `‖LowBits(w - cs₂)‖∞ < γ₂ - β`, on one coordinate, with `x = w_i` and `a = (cs₂)_i`. -/
def rejectionBucket (γ₂ β r1 : ℕ) (a : ℤ) : Finset Coeff :=
  Finset.univ.filter fun x =>
    highBitsCoeff x γ₂ = r1 ∧ |lowBitsCoeff (x - (a : Coeff)) γ₂| < (γ₂ : ℤ) - β

/-- The r0-check set of a bucket is the image of the offsets `|s| < γ₂ - β` under
`s ↦ 2γ₂ · r1 + s + a`. -/
theorem rejectionBucket_eq_image {γ₂ β : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1)
    {r1 : ℕ} (hr1 : r1 < (modulus - 1) / (2 * γ₂)) {a : ℤ} (ha : |a| ≤ β) :
    rejectionBucket γ₂ β r1 a =
      (Finset.Ioo (-((γ₂ : ℤ) - β)) ((γ₂ : ℤ) - β)).image
        fun s => bucketPoint γ₂ r1 (s + a) := by
  rw [abs_le] at ha
  ext x
  simp only [rejectionBucket, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_Ioo]
  constructor
  · rintro ⟨hx1, hx2⟩
    have hhigh := highBits_sub_eq_of_lowBits (β := β) hγ hdvd x (abs_le.mpr ha) hx2
    refine ⟨lowBitsCoeff (x - (a : Coeff)) γ₂, abs_lt.mp hx2, ?_⟩
    rw [← bucketPoint_add, ← hx1, ← hhigh, ← eq_bucketPoint hγ hdvd, sub_add_cancel]
  · rintro ⟨s, hs, rfl⟩
    have hsub : bucketPoint γ₂ r1 (s + a) - (a : Coeff) = bucketPoint γ₂ r1 s := by
      rw [sub_eq_add_neg, ← Int.cast_neg, bucketPoint_add]; ring_nf
    rw [hsub, (highBits_bucketPoint hγ hdvd hr1 (s := s) (abs_lt.mpr ⟨by linarith, by linarith⟩)).2,
      (highBits_bucketPoint hγ hdvd hr1 (s := s + a)
        (abs_lt.mpr ⟨by linarith, by linarith⟩)).1]
    exact ⟨rfl, abs_lt.mpr ⟨by linarith, by linarith⟩⟩

/-- The offset map `s ↦ 2γ₂ · r1 + s + a` is injective on `|s| < γ₂`. -/
theorem bucketPoint_add_injOn {γ₂ : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1)
    {r1 : ℕ} (hr1 : r1 < (modulus - 1) / (2 * γ₂)) (a : ℤ) {L : ℤ} (hL : L ≤ γ₂) :
    Set.InjOn (fun s => bucketPoint γ₂ r1 (s + a)) (Finset.Ioo (-L) L : Set ℤ) := by
  intro s hs s' hs' h
  simp only [Finset.coe_Ioo, Set.mem_Ioo] at hs hs'
  have key : ∀ u : ℤ, -L < u ∧ u < L → lowBitsCoeff (bucketPoint γ₂ r1 (u + a) - (a : Coeff)) γ₂ = u := by
    intro u hu
    rw [sub_eq_add_neg, ← Int.cast_neg, bucketPoint_add, add_neg_cancel_right]
    exact (highBits_bucketPoint hγ hdvd hr1 (abs_lt.mpr ⟨by linarith, by linarith⟩)).2
  rw [← key s hs, ← key s' hs']
  exact congrArg (fun y => lowBitsCoeff (y - (a : Coeff)) γ₂) h

/-- **The r0-check keeps the same number of residues in every bucket, for every shift.** For
`r1 < (q - 1)/(2γ₂)` and `|a| ≤ β`, exactly `2(γ₂ - β) - 1` residues `x` have
`HighBits(x) = r1` and `|LowBits(x - a)| < γ₂ - β`. -/
theorem bucket_r0_card {γ₂ β : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1)
    {r1 : ℕ} (hr1 : r1 < (modulus - 1) / (2 * γ₂)) {a : ℤ} (ha : |a| ≤ β) :
    (rejectionBucket γ₂ β r1 a).card = 2 * (γ₂ - β) - 1 := by
  rw [rejectionBucket_eq_image hγ hdvd hr1 ha,
    Finset.card_image_of_injOn (bucketPoint_add_injOn hγ hdvd hr1 a (by omega)), Int.card_Ioo]
  omega

/-! ### The hint on the r0-check set -/

/-- On a bucket point, the FIPS 204 hint `MakeHint(-b, x - a + b)` fires exactly when adding `b` to
the unshifted offset leaves the bucket. -/
theorem makeHintCoeff_bucketPoint {γ₂ : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1)
    {r1 : ℕ} (hr1 : r1 < (modulus - 1) / (2 * γ₂)) {s : ℤ} (hs : |s| < γ₂) (a b : ℤ) :
    makeHintCoeff (-(b : Coeff)) (bucketPoint γ₂ r1 (s + a) - (a : Coeff) + (b : Coeff)) γ₂ =
      decide (highBitsCoeff (bucketPoint γ₂ r1 (s + b)) γ₂ ≠ r1) := by
  have e1 : bucketPoint γ₂ r1 (s + a) - (a : Coeff) + (b : Coeff) = bucketPoint γ₂ r1 (s + b) := by
    unfold bucketPoint; push_cast; ring
  have e2 : bucketPoint γ₂ r1 (s + b) + -(b : Coeff) = bucketPoint γ₂ r1 s := by
    unfold bucketPoint; push_cast; ring
  rw [e1]
  unfold makeHintCoeff
  rw [e2, (highBits_bucketPoint hγ hdvd hr1 hs).1]

/-- **The hint count of a bucket.** Among the `2(γ₂ - β) - 1` residues of `rejectionBucket`, the
FIPS 204 hint `h = MakeHint(-ct₀, w - cs₂ + ct₀)` (Algorithm 7 line 26) fires, on one coordinate
with `x = w_i`, `a = (cs₂)_i`, `b = (ct₀)_i`, for exactly `|b| - β` residues when `b < 0` and
`r1 ≠ 0`, and `|b| - β - 1` otherwise (truncated at `0`). The count depends on `b` and, for
negative `b`, on whether `r1` is Decompose's merged bucket `0`; it does not depend on `a`.
Needs at least two buckets, `2γ₂ < q - 1`. -/
theorem bucket_hint_card {γ₂ β : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1)
    (hM : 2 * γ₂ < modulus - 1) {r1 : ℕ} (hr1 : r1 < (modulus - 1) / (2 * γ₂)) {a : ℤ}
    (ha : |a| ≤ β) {b : ℤ} (hb : |b| < γ₂) :
    ((rejectionBucket γ₂ β r1 a).filter fun x =>
        makeHintCoeff (-(b : Coeff)) (x - (a : Coeff) + (b : Coeff)) γ₂ = true).card =
      (if b < 0 ∧ r1 ≠ 0 then -b - β else |b| - β - 1).toNat := by
  rw [rejectionBucket_eq_image hγ hdvd hr1 ha, Finset.filter_image,
    Finset.card_image_of_injOn ((bucketPoint_add_injOn hγ hdvd hr1 a (L := (γ₂ : ℤ) - β)
      (by omega)).mono (by simp only [Finset.coe_filter]; exact fun x hx => hx.1))]
  have hb' := abs_lt.mp hb
  have hfilter :
      (Finset.Ioo (-((γ₂ : ℤ) - β)) ((γ₂ : ℤ) - β)).filter
        (fun s => makeHintCoeff (-(b : Coeff))
          (bucketPoint γ₂ r1 (s + a) - (a : Coeff) + (b : Coeff)) γ₂ = true) =
      (Finset.Ioo (-((γ₂ : ℤ) - β)) ((γ₂ : ℤ) - β)).filter
        (fun s => ¬ ((-(γ₂ : ℤ) < s + b ∧ s + b ≤ γ₂) ∨ (r1 = 0 ∧ s + b = -(γ₂ : ℤ)))) := by
    refine Finset.filter_congr fun s hs => ?_
    rw [Finset.mem_Ioo] at hs
    rw [makeHintCoeff_bucketPoint hγ hdvd hr1 (abs_lt.mpr ⟨by omega, by omega⟩),
      decide_eq_true_iff, ne_eq,
      highBits_bucketPoint_eq_iff hγ hdvd hM hr1 ⟨by omega, by omega⟩]
  refine Eq.trans (by convert congrArg Finset.card hfilter) ?_
  rcases le_or_gt 0 b with hb0 | hb0
  · rw [show (Finset.Ioo (-((γ₂ : ℤ) - β)) ((γ₂ : ℤ) - β)).filter
          (fun s => ¬ ((-(γ₂ : ℤ) < s + b ∧ s + b ≤ γ₂) ∨ (r1 = 0 ∧ s + b = -(γ₂ : ℤ)))) =
        Finset.Icc ((γ₂ : ℤ) - b + 1) ((γ₂ : ℤ) - β - 1) by
          ext s; simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_Icc]; omega,
      Int.card_Icc, abs_of_nonneg hb0]
    split_ifs <;> omega
  · rw [abs_of_neg hb0]
    by_cases hr0 : r1 = 0
    · rw [show (Finset.Ioo (-((γ₂ : ℤ) - β)) ((γ₂ : ℤ) - β)).filter
            (fun s => ¬ ((-(γ₂ : ℤ) < s + b ∧ s + b ≤ γ₂) ∨ (r1 = 0 ∧ s + b = -(γ₂ : ℤ)))) =
          Finset.Icc ((β : ℤ) - γ₂ + 1) (-(γ₂ : ℤ) - b - 1) by
            ext s; simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_Icc]; omega,
        Int.card_Icc]
      split_ifs <;> omega
    · rw [show (Finset.Ioo (-((γ₂ : ℤ) - β)) ((γ₂ : ℤ) - β)).filter
            (fun s => ¬ ((-(γ₂ : ℤ) < s + b ∧ s + b ≤ γ₂) ∨ (r1 = 0 ∧ s + b = -(γ₂ : ℤ)))) =
          Finset.Icc ((β : ℤ) - γ₂ + 1) (-(γ₂ : ℤ) - b) by
            ext s; simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_Icc]; omega,
        Int.card_Icc]
      split_ifs <;> omega

/-! ### The z-check: shifting the mask box -/

/-- **The z-check box, over the integers.** For `|v| ≤ β`, the shift `y ↦ y + v` maps the
masks `y ∈ (-γ₁, γ₁]` (FIPS 204 Algorithm 34, ExpandMask) with `|y + v| < γ₁ - β` bijectively
onto `{z : |z| < γ₁ - β}`. -/
theorem box_shift_bijOn_int {γ₁ β : ℕ} {v : ℤ} (hv : |v| ≤ β) :
    Set.BijOn (fun y => y + v)
      (((Finset.Ioc (-(γ₁ : ℤ)) γ₁).filter fun y => |y + v| < (γ₁ : ℤ) - β : Finset ℤ) : Set ℤ)
      (Finset.Ioo (-((γ₁ : ℤ) - β)) ((γ₁ : ℤ) - β) : Set ℤ) := by
  rw [abs_le] at hv
  refine ⟨fun y hy => ?_, fun y _ y' _ h => add_right_cancel h, fun z hz => ?_⟩
  · simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_ofPred_eq, abs_lt] at hy
    simp only [Finset.coe_Ioo, Set.mem_Ioo]
    omega
  · simp only [Finset.coe_Ioo, Set.mem_Ioo] at hz
    refine ⟨z - v, ?_, by simp⟩
    simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_ofPred_eq, abs_lt, sub_add_cancel]
    omega

/-- The integer z-check box has `2(γ₁ - β) - 1` elements, for every shift `|v| ≤ β` (both sides are `0` when `γ₁ ≤ β`). -/
theorem box_shift_card_int {γ₁ β : ℕ} {v : ℤ} (hv : |v| ≤ β) :
    ((Finset.Ioc (-(γ₁ : ℤ)) γ₁).filter fun y => |y + v| < (γ₁ : ℤ) - β).card =
      2 * (γ₁ - β) - 1 := by
  have himg : ((Finset.Ioc (-(γ₁ : ℤ)) γ₁).filter fun y => |y + v| < (γ₁ : ℤ) - β).image
      (fun y => y + v) = Finset.Ioo (-((γ₁ : ℤ) - β)) ((γ₁ : ℤ) - β) :=
    Finset.coe_injective (by rw [Finset.coe_image]; exact (box_shift_bijOn_int hv).image_eq)
  rw [← Finset.card_image_of_injOn (box_shift_bijOn_int hv).injOn, himg, Int.card_Ioo]
  omega

/-- The z-check set of one coefficient of `Coeff`: masks with centered representative in
`(-γ₁, γ₁]` whose shift by `v` has centered absolute value below `γ₁ - β`. -/
def zCheckCoeffSet (γ₁ β : ℕ) (v : ℤ) : Finset Coeff :=
  Finset.univ.filter fun y =>
    (-(γ₁ : ℤ) < LatticeCrypto.centeredRepr y ∧ LatticeCrypto.centeredRepr y ≤ γ₁) ∧
      |LatticeCrypto.centeredRepr (y + (v : Coeff))| < (γ₁ : ℤ) - β

/-- **The z-check box of one coefficient.** For `|v| ≤ β` and `2(γ₁ + β) < q`, exactly
`2(γ₁ - β) - 1` coefficients `y` have centered value in `(-γ₁, γ₁]` and
`|centered(y + v)| < γ₁ - β`. -/
theorem box_shift_card {γ₁ β : ℕ} (hq : 2 * (γ₁ + β) < modulus) {v : ℤ}
    (hv : |v| ≤ β) : (zCheckCoeffSet γ₁ β v).card = 2 * (γ₁ - β) - 1 := by
  rw [← box_shift_card_int hv]
  have hv' := abs_le.mp hv
  have hcr : ∀ z : ℤ, |z| ≤ γ₁ + β → LatticeCrypto.centeredRepr ((z : Coeff)) = z := fun z hz =>
    LatticeCrypto.centeredRepr_intCast_eq_of_natAbs_le z (b := γ₁ + β)
      (by rw [abs_le] at hz; omega) hq
  symm
  refine Finset.card_bij (fun y _ => ((y : ℤ) : Coeff)) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_Ioc, abs_lt] at hy
    simp only [zCheckCoeffSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← Int.cast_add, hcr y (abs_le.mpr ⟨by omega, by omega⟩),
      hcr (y + v) (abs_le.mpr ⟨by omega, by omega⟩), abs_lt]
    omega
  · intro y hy y' hy' h
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hy hy'
    have := congrArg LatticeCrypto.centeredRepr h
    rwa [hcr y (abs_le.mpr ⟨by omega, by omega⟩), hcr y' (abs_le.mpr ⟨by omega, by omega⟩)] at this
  · intro x hx
    simp only [zCheckCoeffSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    refine ⟨LatticeCrypto.centeredRepr x, ?_, (LatticeCrypto.centeredRepr_intCast x).symm⟩
    have hxv : LatticeCrypto.centeredRepr (x + (v : Coeff)) = LatticeCrypto.centeredRepr x + v := by
      conv_lhs => rw [LatticeCrypto.centeredRepr_intCast x, ← Int.cast_add]
      exact hcr _ (abs_le.mpr ⟨by omega, by omega⟩)
    rw [hxv] at hx
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨hx.1, hx.2⟩

/-- Vectors whose entries satisfy independent constraints are counted coordinatewise. -/
theorem natCard_vector_forall {α : Type*} {n : ℕ} (P : Fin n → α → Prop) :
    Nat.card {y : Vector α n // ∀ i, P i (y.get i)} = ∏ i, Nat.card {a // P i a} := by
  rw [← Nat.card_pi]
  exact Nat.card_congr
    { toFun := fun y i => ⟨y.1.get i, y.2 i⟩
      invFun := fun f => ⟨Vector.ofFn fun i => (f i).1, fun i => by
        rw [Vector.get_ofFn]; exact (f i).2⟩
      left_inv := fun y => Subtype.ext (Vector.ext fun i hi => by simp [Vector.get])
      right_inv := fun f => funext fun i => Subtype.ext (by simp) }

/-- The centered infinity norm of a polynomial vector is below `c > 0` exactly when every
coefficient's centered absolute value is. -/
theorem polyVecNorm_lt_iff {k : ℕ} (w : RqVec k) {c : ℕ} (hc : 0 < c) :
    polyVecNorm w < c ↔
      ∀ j i, (LatticeCrypto.centeredRepr ((w.get j).get i)).natAbs < c := by
  rw [show polyVecNorm w < c ↔ polyVecNorm w ≤ c - 1 by omega, polyVecNorm,
    LatticeCrypto.PolyVec.cInfNorm_le_iff]
  refine forall_congr' fun j => ?_
  rw [← polyNorm, polyNorm_eq_cInfNorm, LatticeCrypto.cInfNorm_le_iff]
  exact forall_congr' fun i => by omega

/-- **The z-check box of a mask vector.** For `|v| ≤ β < γ₁` coefficientwise (`‖v‖∞ ≤ β`, as for
`v = cs₁`) and `2(γ₁ + β) < q`, the masks `y ∈ R_q^l` with every centered coefficient in
`(-γ₁, γ₁]` (FIPS 204 Algorithm 34) and `‖y + v‖∞ < γ₁ - β` (Algorithm 7 line 23) number exactly
`(2(γ₁ - β) - 1)^(256 l)`, whatever `v` is. -/
theorem zCheck_vec_card {γ₁ β l : ℕ} (hβ : β < γ₁) (hq : 2 * (γ₁ + β) < modulus) (v : RqVec l)
    (hv : polyVecNorm v ≤ β) :
    Nat.card {y : RqVec l //
        (∀ j i, -(γ₁ : ℤ) < LatticeCrypto.centeredRepr ((y.get j).get i) ∧
          LatticeCrypto.centeredRepr ((y.get j).get i) ≤ γ₁) ∧
        polyVecNorm (y + v) < γ₁ - β} =
      (2 * (γ₁ - β) - 1) ^ (ringDegree * l) := by
  have hvc : ∀ j i, |LatticeCrypto.centeredRepr ((v.get j).get i)| ≤ β := by
    intro j i
    have h1 := (LatticeCrypto.PolyVec.cInfNorm_le_iff _).mp hv j
    rw [← polyNorm, polyNorm_eq_cInfNorm, LatticeCrypto.cInfNorm_le_iff] at h1
    have := h1 i
    rw [abs_le]; omega
  have hiff : ∀ y : RqVec l,
      ((∀ j i, -(γ₁ : ℤ) < LatticeCrypto.centeredRepr ((y.get j).get i) ∧
          LatticeCrypto.centeredRepr ((y.get j).get i) ≤ γ₁) ∧
        polyVecNorm (y + v) < γ₁ - β) ↔
      ∀ j, (fun (j : Fin l) (p : Rq) => ∀ i, p.get i ∈
        zCheckCoeffSet γ₁ β (LatticeCrypto.centeredRepr ((v.get j).get i))) j (y.get j) := by
    intro y
    rw [polyVecNorm_lt_iff _ (by omega)]
    simp only [zCheckCoeffSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hadd : ∀ j i, ((y + v).get j).get i =
        (y.get j).get i + (((LatticeCrypto.centeredRepr ((v.get j).get i) : ℤ)) : Coeff) := by
      intro j i
      rw [← LatticeCrypto.centeredRepr_intCast]
      have h1 : (y + v).get j = y.get j + v.get j := by
        simp only [Vector.get_eq_getElem, Vector.getElem_add]
      rw [h1]
      exact LatticeCrypto.vectorRing_add_get (y.get j) (v.get j) i
    simp only [hadd]
    constructor
    · rintro ⟨h1, h2⟩ j i
      refine ⟨h1 j i, ?_⟩
      have := h2 j i
      rw [← LatticeCrypto.centeredRepr_intCast] at this ⊢
      rw [abs_lt]; omega
    · intro h
      refine ⟨fun j i => (h j i).1, fun j i => ?_⟩
      have := (h j i).2
      rw [← LatticeCrypto.centeredRepr_intCast] at this ⊢
      rw [abs_lt] at this; omega
  refine (Nat.card_congr (Equiv.subtypeEquivRight hiff)).trans ?_
  refine (natCard_vector_forall (α := Rq) (n := l) (fun (j : Fin l) (p : Rq) => ∀ i, p.get i ∈
    zCheckCoeffSet γ₁ β (LatticeCrypto.centeredRepr ((v.get j).get i)))).trans ?_
  have hinner : ∀ j : Fin l, Nat.card {p : Rq // ∀ i, p.get i ∈
      zCheckCoeffSet γ₁ β (LatticeCrypto.centeredRepr ((v.get j).get i))} =
      (2 * (γ₁ - β) - 1) ^ ringDegree := by
    intro j
    have := natCard_vector_forall (α := Coeff) (n := ringDegree)
      (fun i a => a ∈ zCheckCoeffSet γ₁ β (LatticeCrypto.centeredRepr ((v.get j).get i)))
    refine this.trans ?_
    simp only [Nat.card_eq_fintype_card, Fintype.card_coe, box_shift_card hq (hvc j _),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [hinner, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

/-! ### The challenge product bound -/

/-- A challenge-shaped polynomial (at most `τ` nonzero coefficients, each of centered absolute
value at most `1`, as `SampleInBall`, FIPS 204 Algorithm 29, produces) has `ℓ₁` norm at most `τ`. -/
theorem l1Norm_le_of_weight {τ : ℕ} (c : Rq) (hc1 : polyNorm c ≤ 1)
    (hcw : (Finset.univ.filter fun i : Fin ringDegree => c.get i ≠ 0).card ≤ τ) :
    LatticeCrypto.l1Norm c ≤ τ := by
  rw [LatticeCrypto.l1Norm_eq_sum]
  refine le_trans ?_ hcw
  rw [Finset.card_filter]
  refine Finset.sum_le_sum fun i _ => ?_
  have hle := LatticeCrypto.coeff_le_cInfNorm c i
  rw [← polyNorm_eq_cInfNorm] at hle
  split_ifs with h
  · omega
  · rw [not_not] at h
    rw [h]
    simp [LatticeCrypto.centeredRepr]

/-- **`‖c · s‖∞ ≤ τ · η`.** For a challenge-shaped `c` (at most `τ` nonzero coefficients, each
`±1`) and `‖s‖∞ ≤ η`, the negacyclic product satisfies `‖c · s‖∞ ≤ τη`, which is `β` in ML-DSA
(FIPS 204 Table 1). Built on the vendored `LatticeCrypto.cInfNorm_mul_le`. -/
theorem norm_challenge_mul_le {τ η : ℕ} (c s : Rq) (hc1 : polyNorm c ≤ 1)
    (hcw : (Finset.univ.filter fun i : Fin ringDegree => c.get i ≠ 0).card ≤ τ)
    (hs : polyNorm s ≤ η) : polyNorm (c * s) ≤ τ * η := by
  rw [polyNorm_eq_cInfNorm] at hs ⊢
  exact (LatticeCrypto.cInfNorm_mul_le c s).trans
    (Nat.mul_le_mul (l1Norm_le_of_weight c hc1 hcw) hs)

/-- The vector form of `norm_challenge_mul_le`: `‖c · s‖∞ ≤ τη` for `s : R_q^k`, multiplied
componentwise. -/
theorem norm_challenge_mul_vec_le {τ η k : ℕ} (c : Rq) (s : RqVec k) (hc1 : polyNorm c ≤ 1)
    (hcw : (Finset.univ.filter fun i : Fin ringDegree => c.get i ≠ 0).card ≤ τ)
    (hs : polyVecNorm s ≤ η) : polyVecNorm (s.map (c * ·)) ≤ τ * η := by
  rw [polyVecNorm, LatticeCrypto.PolyVec.cInfNorm_le_iff] at hs ⊢
  intro j
  rw [Vector.get_map]
  exact norm_challenge_mul_le c _ hc1 hcw (hs j)

/-- The challenge bound for the transform-domain product `coeffScalarVecMul c s` that the
vendored `MLDSA.Primitives.Laws.sampleInBall_smul_bound` refers to, given the transform laws. -/
theorem norm_challenge_coeffScalarVecMul_le {τ η k : ℕ} (ops : NTTRingOps) [NTTRingLaws ops]
    (c : Rq) (s : RqVec k) (hc1 : polyNorm c ≤ 1)
    (hcw : (Finset.univ.filter fun i : Fin ringDegree => c.get i ≠ 0).card ≤ τ)
    (hs : polyVecNorm s ≤ η) : polyVecNorm (ops.coeffScalarVecMul c s) ≤ τ * η := by
  rw [polyVecNorm, LatticeCrypto.PolyVec.cInfNorm_le_iff] at hs ⊢
  intro j
  rw [LatticeCrypto.TransformOps.coeffScalarVecMul_get]
  exact norm_challenge_mul_le c _ hc1 hcw (hs j)

/-! ### The ct₀-check floor -/

/-- `‖c · t₀‖∞ ≤ τ · 2^(d-1)` for a challenge-shaped `c` and `‖t₀‖∞ ≤ 2^(d-1)`, `d = 13`
(Power2Round's low part, FIPS 204 Algorithm 35). -/
theorem norm_challenge_mul_t0_le {τ : ℕ} (c t0 : Rq) (hc1 : polyNorm c ≤ 1)
    (hcw : (Finset.univ.filter fun i : Fin ringDegree => c.get i ≠ 0).card ≤ τ)
    (ht0 : polyNorm t0 ≤ 2 ^ (droppedBits - 1)) :
    polyNorm (c * t0) ≤ τ * 2 ^ (droppedBits - 1) :=
  norm_challenge_mul_le c t0 hc1 hcw ht0

/-- **The ct₀-check always passes when `τ · 2^(d-1) < γ₂`.** Under the hypotheses of
`norm_challenge_mul_t0_le`, `‖c · t₀‖∞ < γ₂` (FIPS 204 Algorithm 7 line 28). -/
theorem ct0_check_passes {τ γ₂ : ℕ} (hfloor : τ * 2 ^ (droppedBits - 1) < γ₂) (c t0 : Rq)
    (hc1 : polyNorm c ≤ 1)
    (hcw : (Finset.univ.filter fun i : Fin ringDegree => c.get i ≠ 0).card ≤ τ)
    (ht0 : polyNorm t0 ≤ 2 ^ (droppedBits - 1)) : polyNorm (c * t0) < γ₂ :=
  lt_of_le_of_lt (norm_challenge_mul_t0_le c t0 hc1 hcw ht0) hfloor

/-- At ML-DSA-65, `τ · 2^(d-1) = 49 · 4096 = 200704 < 261888 = γ₂`. -/
theorem ct0_floor_mldsa65 : mldsa65.tau * 2 ^ (droppedBits - 1) < mldsa65.gamma2 := by
  simp only [mldsa65, ParameterSet.params, droppedBits, modulus]; decide

/-- At ML-DSA-87, `τ · 2^(d-1) = 60 · 4096 = 245760 < 261888 = γ₂`. -/
theorem ct0_floor_mldsa87 : mldsa87.tau * 2 ^ (droppedBits - 1) < mldsa87.gamma2 := by
  simp only [mldsa87, ParameterSet.params, droppedBits, modulus]; decide

/-- At ML-DSA-44 the floor fails: `τ · 2^(d-1) = 39 · 4096 = 159744 ≥ 95232 = γ₂`, so
`ct0_check_passes` does not apply and the ct₀-check can reject. -/
theorem ct0_floor_mldsa44_fails : ¬ mldsa44.tau * 2 ^ (droppedBits - 1) < mldsa44.gamma2 := by
  simp only [mldsa44, ParameterSet.params, droppedBits, modulus]; decide

/-! ### Instantiation at the approved parameter sets -/

/-- The side conditions of this file's lemmas for a parameter record `p`: `γ₂ > 0`, `2γ₂ ∣ q - 1`,
at least two `HighBits` buckets, `β < γ₂`, `β < γ₁`, and `2(γ₁ + β) < q`. (`β = τη` holds by the
definition `Params.beta`.) -/
structure SigningParams (p : Params) : Prop where
  gamma2_pos : 0 < p.gamma2
  gamma2_dvd : 2 * p.gamma2 ∣ modulus - 1
  two_buckets : 2 * p.gamma2 < modulus - 1
  beta_lt_gamma2 : p.beta < p.gamma2
  beta_lt_gamma1 : p.beta < p.gamma1
  gamma1_beta_lt : 2 * (p.gamma1 + p.beta) < modulus

/-- Every approved parameter set (FIPS 204 Table 1) satisfies `SigningParams`. -/
theorem SigningParams.of_isApproved {p : Params} (hp : p.isApproved) : SigningParams p := by
  rcases hp with rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- `bucket_r0_card` at an approved parameter set. -/
theorem bucket_r0_card_of_approved {p : Params} (hp : p.isApproved) {r1 : ℕ}
    (hr1 : r1 < (modulus - 1) / (2 * p.gamma2)) {a : ℤ} (ha : |a| ≤ p.beta) :
    (rejectionBucket p.gamma2 p.beta r1 a).card = 2 * (p.gamma2 - p.beta) - 1 :=
  have h := SigningParams.of_isApproved hp
  bucket_r0_card h.gamma2_pos h.gamma2_dvd hr1 ha

/-- `bucket_hint_card` at an approved parameter set. -/
theorem bucket_hint_card_of_approved {p : Params} (hp : p.isApproved) {r1 : ℕ}
    (hr1 : r1 < (modulus - 1) / (2 * p.gamma2)) {a : ℤ} (ha : |a| ≤ p.beta) {b : ℤ}
    (hb : |b| < p.gamma2) :
    ((rejectionBucket p.gamma2 p.beta r1 a).filter fun x =>
        makeHintCoeff (-(b : Coeff)) (x - (a : Coeff) + (b : Coeff)) p.gamma2 = true).card =
      (if b < 0 ∧ r1 ≠ 0 then -b - p.beta else |b| - p.beta - 1).toNat :=
  have h := SigningParams.of_isApproved hp
  bucket_hint_card h.gamma2_pos h.gamma2_dvd h.two_buckets hr1 ha hb

/-- `zCheck_vec_card` at an approved parameter set, for `v : R_q^l` with `‖v‖∞ ≤ β`. -/
theorem zCheck_vec_card_of_approved {p : Params} (hp : p.isApproved) (v : RqVec p.l)
    (hv : polyVecNorm v ≤ p.beta) :
    Nat.card {y : RqVec p.l //
        (∀ j i, -(p.gamma1 : ℤ) < LatticeCrypto.centeredRepr ((y.get j).get i) ∧
          LatticeCrypto.centeredRepr ((y.get j).get i) ≤ p.gamma1) ∧
        polyVecNorm (y + v) < p.gamma1 - p.beta} =
      (2 * (p.gamma1 - p.beta) - 1) ^ (ringDegree * p.l) :=
  have h := SigningParams.of_isApproved hp
  zCheck_vec_card h.beta_lt_gamma1 h.gamma1_beta_lt v hv

/-- `norm_challenge_mul_vec_le` at a parameter record: `‖c · s‖∞ ≤ β = τη`. -/
theorem norm_challenge_mul_vec_le_beta (p : Params) {k : ℕ} (c : Rq) (s : RqVec k)
    (hc1 : polyNorm c ≤ 1)
    (hcw : (Finset.univ.filter fun i : Fin ringDegree => c.get i ≠ 0).card ≤ p.tau)
    (hs : polyVecNorm s ≤ p.eta) : polyVecNorm (s.map (c * ·)) ≤ p.beta :=
  norm_challenge_mul_vec_le c s hc1 hcw hs

end GordieHowe.MLDSA
