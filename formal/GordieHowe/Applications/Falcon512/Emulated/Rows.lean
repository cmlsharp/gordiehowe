-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Rows.Basic
public import GordieHowe.Language.Realizations.Range
public import GordieHowe.Language.Realizations.Bits
public import GordieHowe.Foundations.Algebra.IntLift
public import GordieHowe.Applications.Falcon512.Spec.Basic
public import LatticeCrypto.Ring.Kernel

@[expose] public section

/-!
# Falcon's emulated signature rows

```
procedure EmulatedSignatureRows(pk):
    Falcon:
        LinearConstraint(c − h*s₂ − s₁ + BIAS·1 == q·dq)
```

`*` is integer polynomial multiplication modulo `X^n + 1`, `h` has public
coefficients in `[0, q)` recovered from the key, `c` enters through its 16
committed bits per coefficient, `s₁` through its limbs, `dq` through its
quotient limbs, and `s₂` directly.  Every row is affine in the committed
wires because `h` is public, so each is a `Row` on the product witness.

What the rows establish, when both sides of each row stay below the characteristic: the residual is
an integer equation, `BIAS` is a multiple of `q`, and so `c ≡ s₁ + h·s₂ (mod q)` coefficientwise.
-/

namespace GordieHowe.Falcon512.Emulated.Rows

variable {F : Type*} [Field F]

variable {n L₁ Lq : ℕ}

/-- Weight of `s₂[j]` in coefficient `i` of the negacyclic product `h * s₂`:
`h[i − j]` for `j ≤ i`, `−h[n + i − j]` otherwise. -/
def convWeight (F : Type*) [Ring F] (h : Fin n → ℕ) (i j : Fin n) : F :=
  if hj : (j : ℕ) ≤ i then (h ⟨i - j, by omega⟩ : F) else -(h ⟨n + i - j, by omega⟩ : F)

/-- The single-sum convolution weights are the vendored double-sum negacyclic
convolution, over any commutative coefficient ring. -/
theorem sum_convWeight_eq_negacyclicConvCoeff {R : Type*} [CommRing R]
    (h : Fin n → ℕ) (g : Fin n → R) (i : Fin n) :
    ∑ j, convWeight R h i j * g j =
      LatticeCrypto.negacyclicConvCoeff (fun k => (h k : R)) g i := by
  rw [LatticeCrypto.negacyclicConvCoeff, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : (j : ℕ) ≤ i
  · let k₀ : Fin n := ⟨i - j, by omega⟩
    rw [Finset.sum_eq_single k₀]
    · have hmod : ((k₀ : ℕ) + j) % n = i := by
        have hn : 0 < n := by omega
        simp only [k₀]
        rw [Nat.sub_add_cancel hj, Nat.mod_eq_of_lt i.isLt]
      have hnowrap : (k₀ : ℕ) + j < n := by simp only [k₀]; omega
      have himod : (i : ℕ) % n = i := Nat.mod_eq_of_lt i.isLt
      simp [convWeight, hj, himod, k₀]
    · intro k _ hne
      have hnot : ((k : ℕ) + j) % n ≠ i := by
        intro hmod
        have hn : 0 < n := by omega
        have hsum : (k : ℕ) + j < 2 * n := by omega
        have hdiv : ((k : ℕ) + j) / n < 2 :=
          (Nat.div_lt_iff_lt_mul hn).2 (by omega)
        have hdecomp := Nat.mod_add_div ((k : ℕ) + j) n
        have hk : (k : ℕ) = i - j := by
          interval_cases hq : ((k : ℕ) + j) / n <;>
            simp [hmod] at hdecomp <;> omega
        apply hne
        apply Fin.ext
        exact hk
      simp [hnot]
    · simp

  · let k₀ : Fin n := ⟨n + i - j, by omega⟩
    rw [Finset.sum_eq_single k₀]
    · have hmod : ((k₀ : ℕ) + j) % n = i := by
        have hn : 0 < n := by omega
        have heq : (k₀ : ℕ) + j = n + i := by simp only [k₀]; omega
        rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt i.isLt]
      have hwrap : ¬ ((k₀ : ℕ) + j < n) := by simp only [k₀]; omega
      have himod : (i : ℕ) % n = i := Nat.mod_eq_of_lt i.isLt
      simp [convWeight, hj, hmod, hwrap, k₀]
    · intro k _ hne
      have hnot : ((k : ℕ) + j) % n ≠ i := by
        intro hmod
        have hn : 0 < n := by omega
        have hsum : (k : ℕ) + j < 2 * n := by omega
        have hdiv : ((k : ℕ) + j) / n < 2 :=
          (Nat.div_lt_iff_lt_mul hn).2 (by omega)
        have hdecomp := Nat.mod_add_div ((k : ℕ) + j) n
        have hk : (k : ℕ) = n + i - j := by
          interval_cases hq : ((k : ℕ) + j) / n <;>
            simp [hmod] at hdecomp <;> omega
        apply hne
        apply Fin.ext
        exact hk
      simp [hnot]
    · simp

/- Cast the integer convolution once, so row extraction and its reduction
   modulo `q` use the same coefficientwise lemma. -/
theorem intCast_negacyclicConvCoeff {R : Type*} [CommRing R]
    (h s : Fin n → ℕ) (i : Fin n) :
    ((LatticeCrypto.negacyclicConvCoeff (fun j => (h j : ℤ))
      (fun j => (s j : ℤ)) i : ℤ) : R) =
      LatticeCrypto.negacyclicConvCoeff (fun j => (h j : R))
        (fun j => (s j : R)) i := by
  rw [← (sum_convWeight_eq_negacyclicConvCoeff (R := ℤ) h
    (fun j => (s j : ℤ)) i)]
  rw [← (sum_convWeight_eq_negacyclicConvCoeff (R := R) h
    (fun j => (s j : R)) i)]
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Int.cast_mul, convWeight]
  split <;> simp

/-- The integer residual `c − h*s₂ − s₁` of row `i` on natural operands. -/
-- spec-side
def residual (h c s₁v s₂v : Fin n → ℕ) (i : Fin n) : ℤ :=
  c i - LatticeCrypto.negacyclicConvCoeff (fun j => (h j : ℤ)) (fun j => (s₂v j : ℤ)) i
    - s₁v i

/-- `c ≡ s₁ + h*s₂ (mod q)` coefficientwise. -/
def Congruent (q : ℕ) (h c s₁v s₂v : Fin n → ℕ) : Prop :=
  ∀ i, (c i : ZMod q) = (s₁v i : ZMod q) +
    LatticeCrypto.negacyclicConvCoeff (fun j => (h j : ZMod q))
      (fun j => (s₂v j : ZMod q)) i

/-- The quotient limb value the honest prover commits: the shifted residual
divided by `q`. -/
-- spec-side
def honestQuotient (q BIAS : ℕ) (h c s₁v s₂v : Fin n → ℕ) (i : Fin n) : ℕ :=
  (residual h c s₁v s₂v i + BIAS).toNat / q

/-- Absolute value bound on one coefficient of the negacyclic convolution
`h * s₂`, for public key coefficients below `q` and operands at most `q`. -/
theorem negacyclicConv_natAbs_le {q : ℕ} {h s₂v : Fin n → ℕ} (hh : ∀ k, h k < q)
    (hs₂v : ∀ k, s₂v k ≤ q) (i : Fin n) :
    (LatticeCrypto.negacyclicConvCoeff (fun j => (h j : ℤ))
      (fun j => (s₂v j : ℤ)) i).natAbs ≤ n * (q - 1) * q := by
  rw [← sum_convWeight_eq_negacyclicConvCoeff]
  calc
    (∑ j, convWeight ℤ h i j * (s₂v j : ℤ)).natAbs
        ≤ ∑ j, (convWeight ℤ h i j * (s₂v j : ℤ)).natAbs := by
          simpa using Int.natAbs_sum_le Finset.univ
            (fun j => convWeight ℤ h i j * (s₂v j : ℤ))
    _ ≤ ∑ _j : Fin n, (q - 1) * q := by
      apply Finset.sum_le_sum
      intro j _
      unfold convWeight
      split
      · simp only [Int.natAbs_mul, Int.natAbs_natCast]
        exact Nat.mul_le_mul (Nat.le_sub_one_of_lt (hh _)) (hs₂v j)
      · simp only [Int.natAbs_mul, Int.natAbs_neg, Int.natAbs_natCast]
        exact Nat.mul_le_mul (Nat.le_sub_one_of_lt (hh _)) (hs₂v j)
    _ = n * (q - 1) * q := by simp [Finset.sum_const, Nat.mul_assoc]

/-- **The negacyclic product of bounded natural operands** has absolute value at most `n · A · B`
when every coefficient of `h` is at most `A` and every coefficient of `s` at most `B`. -/
theorem negacyclicConv_natAbs_le_mul {A B : ℕ} {h s : Fin n → ℕ} (hh : ∀ k, h k ≤ A)
    (hs : ∀ k, s k ≤ B) (i : Fin n) :
    (LatticeCrypto.negacyclicConvCoeff (fun j => (h j : ℤ)) (fun j => (s j : ℤ)) i).natAbs ≤
      n * A * B := by
  rw [← sum_convWeight_eq_negacyclicConvCoeff]
  calc
    (∑ j, convWeight ℤ h i j * (s j : ℤ)).natAbs
        ≤ ∑ j, (convWeight ℤ h i j * (s j : ℤ)).natAbs := by
          simpa using Int.natAbs_sum_le Finset.univ (fun j => convWeight ℤ h i j * (s j : ℤ))
    _ ≤ ∑ _j : Fin n, A * B := by
      apply Finset.sum_le_sum
      intro j _
      unfold convWeight
      split
      · simp only [Int.natAbs_mul, Int.natAbs_natCast]
        exact Nat.mul_le_mul (hh _) (hs j)
      · simp only [Int.natAbs_mul, Int.natAbs_neg, Int.natAbs_natCast]
        exact Nat.mul_le_mul (hh _) (hs j)
    _ = n * A * B := by simp [Finset.sum_const, Nat.mul_assoc]

/-- An integer row identity holds modulo `q` once `q ∣ BIAS`. -/
theorem Congruent.of_integer_eq {q BIAS : ℕ} {h c s₁v s₂v dq : Fin n → ℕ}
    (hBIAS : q ∣ BIAS)
    (heq : ∀ i, residual h c s₁v s₂v i + BIAS = (q : ℤ) * dq i) :
    Congruent q h c s₁v s₂v := by
  intro i
  let conv : ℤ := LatticeCrypto.negacyclicConvCoeff (fun j => (h j : ℤ))
    (fun j => (s₂v j : ℤ)) i
  have hconvCastZMod : (conv : ZMod q) =
      LatticeCrypto.negacyclicConvCoeff (fun j => (h j : ZMod q))
        (fun j => (s₂v j : ZMod q)) i := by
    dsimp only [conv]
    exact intCast_negacyclicConvCoeff h s₂v i
  have hInt : (c i : ℤ) - conv - s₁v i + BIAS = (q : ℤ) * dq i := heq i
  have hBias : (BIAS : ZMod q) = 0 := by
    obtain ⟨k, hk⟩ := hBIAS
    rw [hk, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have hIntCast : (c i : ZMod q) - (conv : ZMod q) - (s₁v i : ZMod q) +
      (BIAS : ZMod q) = (q : ZMod q) * (dq i : ZMod q) := by
    have h := congrArg (fun z : ℤ => (z : ZMod q)) hInt
    simpa only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast] using h
  rw [hconvCastZMod] at hIntCast
  simp [hBias] at hIntCast
  linear_combination hIntCast

/-- **The congruence from a field row whose sides stay below the characteristic**: for natural
operands with `h, c < q`, `s₁, s₂ ≤ q` and quotients below `D`, a row
`c + BIAS − s₁ − q · dq = h * s₂` in a field of characteristic `p` exceeding every term's sum holds
on the integers, so `c ≡ s₁ + h * s₂ (mod q)` once `q ∣ BIAS`. -/
theorem Congruent.of_field {p : ℕ} [CharP F p] {q BIAS D : ℕ} {h c s₁v s₂v dq : Fin n → ℕ}
    (hh : ∀ k, h k < q) (hc : ∀ i, c i < q) (hs₁ : ∀ i, s₁v i ≤ q) (hs₂ : ∀ i, s₂v i ≤ q)
    (hdq : ∀ i, dq i < D) (hBIAS : q ∣ BIAS) (hp : q + BIAS + q + q * D + n * (q - 1) * q < p)
    (hf : ∀ i, (c i : F) + BIAS - s₁v i - q * dq i =
      LatticeCrypto.negacyclicConvCoeff (fun j => (h j : F)) (fun j => (s₂v j : F)) i) :
    Congruent q h c s₁v s₂v := by
  refine Congruent.of_integer_eq (dq := dq) hBIAS fun i => ?_
  set conv : ℤ := LatticeCrypto.negacyclicConvCoeff (fun j => (h j : ℤ)) (fun j => (s₂v j : ℤ)) i
    with hconv
  have hconvF : (conv : F) =
      LatticeCrypto.negacyclicConvCoeff (fun j => (h j : F)) (fun j => (s₂v j : F)) i :=
    intCast_negacyclicConvCoeff h s₂v i
  have hzero : (((c i : ℤ) + BIAS - s₁v i - q * dq i - conv : ℤ) : F) = 0 := by
    push_cast
    rw [hconvF, hf i, sub_self]
  rw [CharP.intCast_eq_zero_iff F p] at hzero
  have hcb := negacyclicConv_natAbs_le hh hs₂ i
  have hb := LatticeCrypto.neg_le_and_le_of_natAbs_le hcb
  have hqd : ((q * dq i : ℕ) : ℤ) ≤ ((q * D : ℕ) : ℤ) :=
    Int.ofNat_le.mpr (Nat.mul_le_mul_left q (hdq i).le)
  have hci : (c i : ℤ) ≤ q := by exact_mod_cast (hc i).le
  have hsi : (s₁v i : ℤ) ≤ q := by exact_mod_cast hs₁ i
  have hp' : ((q + BIAS + q + q * D + n * (q - 1) * q : ℕ) : ℤ) < p := by exact_mod_cast hp
  have e1 : ((q * dq i : ℕ) : ℤ) = (q : ℤ) * (dq i : ℤ) := by push_cast; ring
  have e2 : ((q + BIAS + q + q * D + n * (q - 1) * q : ℕ) : ℤ) =
      (q : ℤ) + BIAS + q + ((q * D : ℕ) : ℤ) + ((n * (q - 1) * q : ℕ) : ℤ) := by push_cast; ring
  have hc0 : (0 : ℤ) ≤ c i := Int.natCast_nonneg _
  have hs0 : (0 : ℤ) ≤ s₁v i := Int.natCast_nonneg _
  have hd0 : (0 : ℤ) ≤ ((q * dq i : ℕ) : ℤ) := Int.natCast_nonneg _
  have hB0 : (0 : ℤ) ≤ BIAS := Int.natCast_nonneg _
  have habs : |((c i : ℤ) + BIAS - s₁v i - q * dq i - conv)| < p := by
    rw [abs_lt, ← e1]
    rw [e2] at hp'
    constructor <;> linarith [hb.1, hb.2]
  have h0 := Int.eq_zero_of_abs_lt_dvd hzero habs
  unfold residual
  linear_combination h0

/-- **The shifted residual of congruent operands is `q` times the honest quotient** wherever it is
nonnegative (`hnonneg`) and `q ∣ BIAS`. -/
theorem residual_add_bias_eq_honestQuotient_of_nonneg {q BIAS : ℕ} {h c s₁v s₂v : Fin n → ℕ}
    (hBIAS : q ∣ BIAS) (hcongr : Congruent q h c s₁v s₂v) {i : Fin n}
    (hnonneg : 0 ≤ residual h c s₁v s₂v i + BIAS) :
    residual h c s₁v s₂v i + BIAS = (q : ℤ) * honestQuotient q BIAS h c s₁v s₂v i := by
  have hresZero : (residual h c s₁v s₂v i : ZMod q) = 0 := by
    unfold residual
    push_cast
    rw [intCast_negacyclicConvCoeff h s₂v i]
    have hc := hcongr i
    linear_combination hc
  have hqdvdres : (q : ℤ) ∣ residual h c s₁v s₂v i :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hresZero
  have hqdvdBIAS : (q : ℤ) ∣ (BIAS : ℤ) := Int.natCast_dvd_natCast.mpr hBIAS
  have hqdvdShift : (q : ℤ) ∣ (residual h c s₁v s₂v i + BIAS) := hqdvdres.add hqdvdBIAS
  have htoNat : ((residual h c s₁v s₂v i + BIAS).toNat : ℤ) =
      residual h c s₁v s₂v i + BIAS := Int.toNat_of_nonneg hnonneg
  have hqdvdToNat : q ∣ (residual h c s₁v s₂v i + BIAS).toNat := by
    have hz : (q : ℤ) ∣ ((residual h c s₁v s₂v i + BIAS).toNat : ℤ) := by
      rw [htoNat]; exact hqdvdShift
    exact_mod_cast hz
  have hgoal : ((residual h c s₁v s₂v i + BIAS).toNat : ℤ) =
      (q : ℤ) * (honestQuotient q BIAS h c s₁v s₂v i : ℤ) := by
    unfold honestQuotient
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hqdvdToNat]
  rw [← htoNat]
  exact hgoal

end GordieHowe.Falcon512.Emulated.Rows
