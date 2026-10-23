-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Range
public import GordieHowe.Foundations.Algebra.IntLift
public import GordieHowe.Applications.Spec.Centered
public import GordieHowe.Applications.Falcon512.Spec.Basic

@[expose] public section

/-!
# `NormBoundEmulated`: Falcon's `ℓ₂` norm over `𝔽_p`

```
gadget NormBoundEmulated(s₁, s₂, a_digits, sum_limbs, β², needles):
    total := 0
    for i, v in (s₁ ‖ s₂):
        a := Σ_l a_digits[i][l]·B^l
        append a_digits[i] to needles
        assert (a−v)·(a−(q−v)) == 0
        total := total + a·a
    RangeTwoSided(total, β²+1, sum_limbs.lo, sum_limbs.hi, needles)
```

`𝔽_p` is far larger than `β²`, so the sum of squares is formed directly.  The
magnitude `a` of each coefficient is committed in base-`B` digits, all
needled, and pinned to the coefficient by `(a − v)(a − (q − v)) = 0`, which
pins `v` to `{a, q − a}`. The total norm bound forces `a < q`,
so `v` lies in `[0, q]`; the endpoint `v = q` represents zero. Taking either representative
can only increase the norm above its centered value, so the accepted bound
implies the specification's.
-/

namespace GordieHowe.Falcon512.EmulatedNorm

variable {F : Type*} [Field F] [DecidableEq F]

/-- Natural representatives extracted from the magnitude constraints. The endpoint
`q` is allowed, and is reduced modulo `q` in the norm. -/
structure Lifted (q βSq : ℕ) {m : ℕ} (v : Fin m → F) (vals : Fin m → ℕ) : Prop where
  bounded : ∀ i, vals i ≤ q
  cast_eq : ∀ i, (vals i : F) = v i
  norm : ∑ i, (LatticeCrypto.centeredRepr (vals i : ZMod q)).natAbs ^ 2 ≤ βSq

omit [DecidableEq F] in
/-- A natural magnitude satisfying the core's two-root equation bounds the
centered representative of the corresponding residue. -/
theorem centered_le_of_centering {p q nv a : ℕ} [CharP F p] [NeZero q]
    (hqp : q < p) (hnv : nv ≤ q) (ha : a ≤ q)
    (h : ((a : F) - (nv : F)) * ((a : F) - (q - (nv : F))) = 0) :
    (LatticeCrypto.centeredRepr (nv : ZMod q)).natAbs ≤ a := by
  rcases mul_eq_zero.mp h with hfirst | hsecond
  · have hcast : (a : F) = (nv : F) := sub_eq_zero.mp hfirst
    have hanv : a = nv :=
      IntLift.natCast_inj_of_lt (K := F) (ha.trans_lt hqp) (hnv.trans_lt hqp) hcast
    subst nv
    exact Centered.natAbs_centeredRepr_natCast_le q a
  · have hcast : (a : F) = (q : F) - (nv : F) := sub_eq_zero.mp hsecond
    have hsubCast : ((q - nv : ℕ) : F) = (q : F) - (nv : F) := Nat.cast_sub hnv
    have haSub : a = q - nv :=
      IntLift.natCast_inj_of_lt (K := F) (ha.trans_lt hqp)
        ((Nat.sub_le q nv).trans_lt hqp) (hcast.trans hsubCast.symm)
    rw [show (nv : ZMod q) = -(a : ZMod q) by
      simp [haSub, Nat.cast_sub hnv]]
    rw [LatticeCrypto.centeredRepr_natAbs_neg]
    exact Centered.natAbs_centeredRepr_natCast_le q a

omit [DecidableEq F] in
/-- A magnitude that is a natural at most `q` pins its coefficient: the two-root equation leaves
`v = mag` or `v = q - mag`, both naturals at most `q`. -/
theorem isNatBelow_of_centering {q : ℕ} {v mag : F}
    (hmag : Range.IsNatBelow (q + 1) mag) (h : (mag - v) * (mag - (q - v)) = 0) :
    Range.IsNatBelow (q + 1) v := by
  obtain ⟨a, ha, rfl⟩ := hmag
  rcases mul_eq_zero.mp h with hfirst | hsecond
  · exact ⟨a, ha, sub_eq_zero.mp hfirst⟩
  · refine ⟨q - a, by omega, ?_⟩
    rw [Nat.cast_sub (by omega)]
    linear_combination -hsecond

/-- **The norm from a bounded sum of squares.** Magnitudes that are naturals below `M`, each pinned
to its coefficient by `(mag − v)(mag − (q − v)) = 0`, whose sum of squares is a natural at most
`βSq`, give natural coefficients at most `q` whose centered norm is at most `βSq`. The sum of
squares is lifted to the naturals before `βSq < q²` bounds each magnitude. `hβq`, `hβp` and `hsq`
are parameter conditions. -/
theorem lifted_of_sumSq {p : ℕ} [CharP F p] {q M βSq : ℕ} {m : ℕ} {v mag : Fin m → F}
    (hβq : βSq < q ^ 2) (hβp : βSq < p) (hsq : m * (M - 1) ^ 2 < p)
    (hmagBound : ∀ i, Range.IsNatBelow M (mag i))
    (hcoeff : ∀ i, (mag i - v i) * (mag i - (q - v i)) = 0)
    (htotal : Range.IsNatBelow (βSq + 1) (∑ i, mag i * mag i)) :
    ∃ vals : Fin m → ℕ, Lifted q βSq v vals := by
  choose mags hmags_lt hmags_cast using hmagBound
  obtain ⟨totalNat, htotalLt, htotalCast⟩ := htotal
  have hsumSqBound : ∑ i, mags i ^ 2 ≤ m * (M - 1) ^ 2 := by
    calc
      ∑ i, mags i ^ 2 ≤ ∑ _i : Fin m, (M - 1) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact Nat.pow_le_pow_left (Nat.le_sub_one_of_lt (hmags_lt i)) 2
      _ = m * (M - 1) ^ 2 := by simp [Finset.sum_const]
  have hsumSqLt : ∑ i, mags i ^ 2 < p := hsumSqBound.trans_lt hsq
  have htotalNatLt : totalNat < p := by omega
  have hsumSqCast : ((∑ i, mags i ^ 2 : ℕ) : F) = ∑ i, mag i * mag i := by
    simp [Nat.cast_sum, hmags_cast, pow_two]
  have hsumSqEq : ∑ i, mags i ^ 2 = totalNat := by
    apply IntLift.natCast_inj_of_lt (K := F) hsumSqLt htotalNatLt
    exact hsumSqCast.trans htotalCast.symm
  have hmags_le_q : ∀ i, mags i ≤ q := by
    intro i
    have hi : mags i ^ 2 ≤ ∑ j, mags j ^ 2 :=
      Finset.single_le_sum (f := fun j => mags j ^ 2)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hsqle : mags i ^ 2 ≤ βSq := by omega
    by_contra h
    have hqm : q < mags i := Nat.lt_of_not_ge h
    have hpows : q ^ 2 < mags i ^ 2 := Nat.pow_lt_pow_left hqm (by decide)
    omega
  let vals : Fin m → ℕ := fun i => if (mags i : F) = v i then mags i else q - mags i
  refine ⟨vals, ?_, ?_, ?_⟩
  · intro i
    simp only [vals]
    split
    · exact hmags_le_q i
    · exact Nat.sub_le q (mags i)
  · intro i
    by_cases hi : (mags i : F) = v i
    · simp [vals, hi]
    · have hsecond : (mags i : F) = (q : F) - v i := by
        rcases mul_eq_zero.mp (hcoeff i) with hfirst | hsecond
        · exact False.elim (hi (hmags_cast i |>.trans (sub_eq_zero.mp hfirst)))
        · exact hmags_cast i |>.trans (sub_eq_zero.mp hsecond)
      simp only [vals, hi, ite_false, Nat.cast_sub (hmags_le_q i)]
      rw [hsecond]
      ring
  · calc
      ∑ i, (LatticeCrypto.centeredRepr (vals i : ZMod q)).natAbs ^ 2
          ≤ ∑ i, mags i ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            apply Nat.pow_le_pow_left
            by_cases hi : (mags i : F) = v i
            · simpa [vals, hi] using Centered.natAbs_centeredRepr_natCast_le q (mags i)
            · rw [show (vals i : ZMod q) = -(mags i : ZMod q) by
                  simp [vals, hi, Nat.cast_sub (hmags_le_q i)]]
              rw [LatticeCrypto.centeredRepr_natAbs_neg]
              exact Centered.natAbs_centeredRepr_natCast_le q (mags i)
      _ = totalNat := hsumSqEq
      _ ≤ βSq := by omega

/-- Honest magnitude advice is the absolute value of the centered residue. -/
-- spec-side
def honestMagnitude {q : ℕ} (x : ZMod q) : F :=
  ((LatticeCrypto.centeredRepr x).natAbs : F)

/-- The honest centered magnitude is either the ordinary representative or
its distance from the modulus. -/
theorem honestMagnitude_eq_val_or {q : ℕ} [NeZero q] (x : ZMod q) :
    (LatticeCrypto.centeredRepr x).natAbs = x.val ∨
      (LatticeCrypto.centeredRepr x).natAbs = q - x.val := by
  by_cases hx : (x.val : ℤ) ≤ (q : ℤ) / 2
  · left
    rw [LatticeCrypto.centeredRepr_of_le hx]
    exact Int.natAbs_natCast x.val
  · right
    rw [LatticeCrypto.centeredRepr_of_gt (lt_of_not_ge hx)]
    have hxval : x.val < q := ZMod.val_lt x
    omega

omit [DecidableEq F] in
/-- **The honest centered magnitude satisfies the centering equation**
`(mag − v)(mag − (q − v)) = 0` at the canonical representative `v` (`honestMagnitude_eq_val_or`). -/
theorem honestMagnitude_centering {q : ℕ} [NeZero q] (x : ZMod q) :
    (honestMagnitude (F := F) x - (x.val : F)) * (honestMagnitude x - ((q : F) - (x.val : F))) =
      0 := by
  unfold honestMagnitude
  rcases honestMagnitude_eq_val_or x with hval | hsub
  · rw [hval]
    simp
  · rw [hsub, Nat.cast_sub (ZMod.val_lt x).le]
    simp

omit [DecidableEq F] in
/-- The fixed-width little-endian radix digits reconstruct a natural below
their represented range. This proof also covers the degenerate bases `0` and
`1`, whose hypotheses force the represented value to be zero. -/
theorem reconstruct_radixDigits {a B k : ℕ} (ha : a < B ^ k) :
    Range.reconstruct (K := F) B
      (List.ofFn fun l : Fin k => ((a / B ^ (l : ℕ) % B : ℕ) : F)) = (a : F) := by
  induction k generalizing a with
  | zero =>
      have ha0 : a = 0 := by simpa using ha
      subst a
      simp [Range.reconstruct]
  | succ k ih =>
      have hB : 0 < B := by
        by_contra h
        have hB0 : B = 0 := Nat.eq_zero_of_not_pos h
        subst B
        simp at ha
      rw [List.ofFn_succ, Range.reconstruct_cons]
      have hdiv : a / B < B ^ k := by
        rw [Nat.div_lt_iff_lt_mul hB]
        simpa [pow_succ, Nat.mul_comm] using ha
      have htail :
          (fun i : Fin k => ((a / B ^ ((Fin.succ i : Fin (k + 1)) : ℕ) % B : ℕ) : F)) =
            (fun i : Fin k => (((a / B) / B ^ (i : ℕ) % B : ℕ) : F)) := by
        funext i
        congr 2
        rw [show ((Fin.succ i : Fin (k + 1)) : ℕ) = (i : ℕ) + 1 by rfl, pow_succ,
          Nat.mul_comm (B ^ (i : ℕ)) B, ← Nat.div_div_eq_div_mul]
      rw [htail, ih hdiv]
      simp only [Fin.val_zero, pow_zero, Nat.div_one]
      simpa using congrArg (fun n : ℕ => (n : F)) (Nat.mod_add_div a B)

omit [DecidableEq F] in
/-- Every digit of a fitting fixed-width radix expansion belongs to the
base-sized lookup table. -/
theorem radixDigit_isNatBelow {a B k : ℕ} (ha : a < B ^ k) (l : Fin k) :
    Range.IsNatBelow B ((a / B ^ (l : ℕ) % B : ℕ) : F) := by
  have hk : 0 < k := Nat.zero_lt_of_lt l.isLt
  have hB : 0 < B := by
    by_contra h
    have hB0 : B = 0 := Nat.eq_zero_of_not_pos h
    subst B
    simp [zero_pow hk.ne'] at ha
  exact ⟨a / B ^ (l : ℕ) % B, Nat.mod_lt _ hB, rfl⟩

end GordieHowe.Falcon512.EmulatedNorm
