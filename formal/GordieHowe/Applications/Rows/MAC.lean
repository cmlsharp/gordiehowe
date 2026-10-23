-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Rows.Basic
public import GordieHowe.Foundations.Algebra.Conv
public import GordieHowe.Language.Realizations.Range
public import GordieHowe.Foundations.Algebra.IntLift

@[expose] public section

/-!
# The MAC linear rows

```
procedure MACLinearRows(r, s̃):
    s := bits(P_mac) + Σ_c Conv(r[c]) · bits(X[c])    // symbolic expressions
    LinearConstraint(P_s + s == s̃)                     // w linear equations
```

The witness these rows read is the pad `P_s`, the bits of `P_mac`, and the
bits of the shared-witness chunks, `w` bits each (the flagship's
`macChunkBits = 128`).  It is a product of function types, so its
module structure is Mathlib's, and the rows are built from `LinearMap.proj`
and sums.

`Conv(r[c])` is the verifier's computation from the transcript value `K_mac`;
the rows take the ladder's bits as input and the composition theorem
substitutes them.

The masked hash-field MAC `maskedMAC` is the pack of the integer accumulator
`accumulatorNat` (`maskedMAC_eq_pack_accumulatorNat`); its bits are the
accumulator's parities (`unpack_maskedMAC`), and a tag whose bits are those
parities is the masked MAC (`maskedMAC_eq_of_unpack`).
-/

namespace GordieHowe.MACRows

open Conv (convMax)

variable {F : Type*} [Field F]

/-- The witness the MAC rows read: `P_s`, the bits of `P_mac`, and `k` chunks of
`w` bit wires. -/
abbrev Wit (F : Type*) (w k : ℕ) := (Fin w → F) × (Fin w → F) × (Fin k → Fin w → F)

variable {w k : ℕ} {T : Finset ℕ}

def pmac : Wit F w k →ₗ[F] (Fin w → F) := (LinearMap.fst F _ _).comp (LinearMap.snd F _ _)
def x : Wit F w k →ₗ[F] (Fin k → Fin w → F) := (LinearMap.snd F _ _).comp (LinearMap.snd F _ _)

/-- Semantic masked MAC of the shared bits, read from the arithmetic field
into the hash field. This is an extractor, not a circuit operation. -/
def maskedMAC {K : Type*} [Field K] [DecidableEq F]
    (B : MACBasis w K) (Kmac : K) (W : Wit F w k) : K :=
  MAC.sharedWitnessMAC
    (fun c => MAC.pack B (fun b => if x W c b = 1 then 1 else 0))
    (MAC.ladder k Kmac)
    + MAC.pack B (fun b => if pmac W b = 1 then 1 else 0)

section Accumulator

variable {K : Type*} [Field K] [DecidableEq F]

/-- The honest integer accumulator `bits(P_mac) + Σ_c Conv(K_mac^(c+1)) · bits(X[c])` of the
rows' witness, each bit wire read as the natural `0` or `1`. The honest prover computes it
after `K_mac` and reveals `s̃ = P_s + accumulatorNat`. -/
-- spec-side
def accumulatorNat (T : Finset ℕ) (B : MACBasis w K) (Kmac : K) (W : Wit F w k) (m : Fin w) : ℕ :=
  (if pmac W m = 1 then 1 else 0) + ∑ c : Fin k,
    Conv.applyConv T (Conv.bitsNat B (Kmac ^ ((c : ℕ) + 1))) (fun b => if x W c b = 1 then 1 else 0) m

/-- **The semantic masked MAC is the pack of the accumulator**, cast into the hash field.
`CharP K 2` is a fact about the field. -/
theorem maskedMAC_eq_pack_accumulatorNat [CharP K 2] (B : Conv.ConvBasis w T K) (Kmac : K)
    (W : Wit F w k) :
    maskedMAC B.toMACBasis Kmac W =
      MAC.pack B.toMACBasis (fun m => (accumulatorNat T B.toMACBasis Kmac W m : K)) := by
  have hchunk : ∀ c : Fin k,
      MAC.pack B.toMACBasis (fun m => (Conv.applyConv T
        (Conv.bitsNat B.toMACBasis (Kmac ^ ((c : ℕ) + 1)))
        (fun b => if x W c b = 1 then 1 else 0) m : K)) =
      Kmac ^ ((c : ℕ) + 1) * MAC.pack B.toMACBasis (fun b => if x W c b = 1 then 1 else 0) := by
    intro c
    have hpacked : Conv.bitsNat B.toMACBasis
        (MAC.pack B.toMACBasis (fun b => if x W c b = 1 then 1 else 0)) =
        fun b => if x W c b = 1 then 1 else 0 := by
      simpa only [decide_eq_true_eq] using
        Conv.bitsNat_pack B.toMACBasis (fun b => decide (x W c b = 1))
    have hc := Conv.pack_applyConv B (Kmac ^ ((c : ℕ) + 1))
      (MAC.pack B.toMACBasis (fun b => if x W c b = 1 then 1 else 0))
    rw [hpacked] at hc
    exact hc
  have hpad : MAC.pack B.toMACBasis (fun b => if pmac W b = 1 then 1 else 0) =
      MAC.pack B.toMACBasis (fun b => ((if pmac W b = 1 then 1 else 0 : ℕ) : K)) := by
    unfold MAC.pack
    exact Finset.sum_congr rfl fun m _ => by dsimp only; split <;> simp
  unfold maskedMAC MAC.sharedWitnessMAC MAC.ladder
  rw [Finset.sum_congr rfl fun c _ => by rw [mul_comm, ← hchunk c], hpad]
  unfold MAC.pack accumulatorNat
  simp only [Nat.cast_add, Nat.cast_sum, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm, add_comm]

/-- **The masked MAC's bits are the accumulator's parities.** `CharP K 2` is a fact about the
field. -/
theorem unpack_maskedMAC [CharP K 2] (B : Conv.ConvBasis w T K) (Kmac : K) (W : Wit F w k) :
    B.toMACBasis.unpack (maskedMAC B.toMACBasis Kmac W) =
      fun m => decide (accumulatorNat T B.toMACBasis Kmac W m % 2 = 1) := by
  have hcoeff : ∀ n : ℕ, (n : K) = if decide (n % 2 = 1) then 1 else 0 := by
    intro n
    rw [CharP.cast_eq_mod K 2]
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;> simp [hn]
  apply B.toMACBasis.pack_injective
  rw [B.toMACBasis.pack_unpack, maskedMAC_eq_pack_accumulatorNat]
  unfold MAC.pack
  exact Finset.sum_congr rfl fun m _ => by dsimp only; rw [hcoeff]; split <;> simp

/-- **The masked MAC from the accumulator's parities**: when every bit of `Mtilde` is the parity of
the integer accumulator of `W` (`accumulatorNat`), the masked MAC of `W` is `Mtilde`. No bound on
the accumulator is needed: the parities are of the naturals themselves. `CharP K 2` is a fact about
the field. -/
theorem maskedMAC_eq_of_unpack [CharP K 2] (B : Conv.ConvBasis w T K) {Kmac Mtilde : K}
    {W : Wit F w k}
    (h : ∀ m, (B.unpack Mtilde m ↔ accumulatorNat T B.toMACBasis Kmac W m % 2 = 1)) :
    maskedMAC B.toMACBasis Kmac W = Mtilde := by
  have hEq : B.toMACBasis.unpack (maskedMAC B.toMACBasis Kmac W) =
      B.toMACBasis.unpack Mtilde := by
    rw [unpack_maskedMAC]
    funext m
    have := h m
    cases hT : B.toMACBasis.unpack Mtilde m <;> simp_all
  rw [← B.toMACBasis.pack_unpack Mtilde, ← hEq, B.toMACBasis.pack_unpack]

end Accumulator

end GordieHowe.MACRows
