-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# The integer matrix `Conv(r)`

`Conv(r)` is the `w × w` matrix of nonnegative integers of the paper's `def:macconv`,
representing multiplication by `r` in a binary field
`GF(2^w) = GF(2)[X]/(φ)` given in the polynomial basis, for a reduction polynomial
`φ = X^w + Σ_{t ∈ T} X^t` with each tap `t ∈ T` below `w`. It multiplies the two bit polynomials
over the integers and replaces each monomial `X^k` of the product by the `0/1` coefficient vector
of `X^k mod φ` (over `GF(2)`), once:

```
procedure ApplyConv(r, x[0..w)) → Conv(r) · x:
    rb := bits(r)
    v[0..2w−1) := 0
    for i,j in 0..w−1:
        v[i+j] += x[i]·rb[j]
    out[0..w) := 0
    for k in 0..2w−2:
        for m in 0..w−1:
            out[m] += v[k] · bit_m(X^k mod φ)
    return out
```

The definition is over naturals and needs no field. `reduceBit w T k m` is the coefficient of
`X^m` in `X^k mod φ`, computed by multiplying by `X` and reducing `k` times on a bit mask
(`powModPacked`). Two facts about `Conv(r)` are Layer A lemmas. On bit vectors every entry is at
most `w` (`matrix_le_width`, the paper's bound `[0, ω]`) and every coordinate of `Conv(r) · x` is
at most `convMax w T`, the largest coordinate on the all-one inputs (`applyConv_le_convMax`, by
monotonicity). In characteristic two, evaluated at any `α` with `α^w = Σ_{t ∈ T} α^t`, the output
is the product of the evaluated inputs (`applyConv_eval`). The flagship shape is `w = 128` with the
taps `gf2_128Taps = {0, 1, 2, 7}` of `X¹²⁸ + X⁷ + X² + X + 1`, where
`convMax 128 gf2_128Taps = 504` (`convMax_gf2_128`); the width-256 shape has the taps
`gf2_256Taps = {0, 2, 5, 10}` of `X²⁵⁶ + X¹⁰ + X⁵ + X² + 1`, where `convMax 256 gf2_256Taps = 1017`
(`convMax_gf2_256`). Both match the C++ `MACConv` (`lib/gordiehowe/ops/operators.h`).
-/

namespace GordieHowe.Conv

/-- The taps of the `GF(2¹²⁸)` reduction polynomial `X¹²⁸ + X⁷ + X² + X + 1`. -/
def gf2_128Taps : Finset ℕ := {0, 1, 2, 7}

/-- The tap powers of `GF(2¹²⁸)` summed, written out. -/
theorem sum_gf2_128Taps {R : Type*} [CommSemiring R] (α : R) :
    ∑ t ∈ gf2_128Taps, α ^ t = α ^ 7 + α ^ 2 + α + 1 := by
  simp [gf2_128Taps]
  ring

section Lanes

/-! ### Packed vectors

A natural number `P` is read as a vector of `B`-bit digits, its lanes. With `B = 1` the lanes are
the bits of `P`; wider lanes let the kernel accumulate the integer row sums of `Conv(1…1)` in one
natural number (`convMax_eq_packed`). -/

/-- The lane of width `B` at position `j` of a natural number read as a vector of `B`-bit
digits: `⌊P / 2^(B·j)⌋ mod 2^B`. -/
def lane (B P j : ℕ) : ℕ := P / 2 ^ (B * j) % 2 ^ B

theorem lane_zero_right (B P : ℕ) : lane B P 0 = P % 2 ^ B := by
  simp [lane]

theorem lane_succ (B P j : ℕ) : lane B P (j + 1) = lane B (P / 2 ^ B) j := by
  unfold lane
  rw [Nat.div_div_eq_div_mul, ← pow_add]
  congr 3
  ring

theorem lane_zero_left (B j : ℕ) : lane B 0 j = 0 := by
  simp [lane]

theorem lane_lt (B P j : ℕ) : lane B P j < 2 ^ B :=
  Nat.mod_lt _ (pow_pos (by norm_num) _)

/-- Multiplying by `2^B` moves every lane up by one position. -/
theorem lane_mul_pow_zero (B P : ℕ) : lane B (P * 2 ^ B) 0 = 0 := by
  rw [lane_zero_right, Nat.mul_mod_left]

theorem lane_mul_pow_succ (B P j : ℕ) : lane B (P * 2 ^ B) (j + 1) = lane B P j := by
  rw [lane_succ, Nat.mul_div_cancel _ (pow_pos (by norm_num) _)]

/-- Exclusive or acts lane by lane. -/
theorem lane_xor (B P Q j : ℕ) : lane B (P ^^^ Q) j = lane B P j ^^^ lane B Q j := by
  simp only [lane, Nat.xor_div_two_pow, Nat.xor_mod_two_pow]

/-- Adding two packed vectors adds their lanes when no lane sum overflows. -/
theorem lane_add {B P Q : ℕ} (h : ∀ j, lane B P j + lane B Q j < 2 ^ B) (m : ℕ) :
    lane B (P + Q) m = lane B P m + lane B Q m := by
  induction m generalizing P Q with
  | zero =>
    have h0 := h 0
    rw [lane_zero_right, lane_zero_right] at h0
    rw [lane_zero_right, lane_zero_right, lane_zero_right, Nat.add_mod, Nat.mod_eq_of_lt h0]
  | succ m ih =>
    have h0 := h 0
    rw [lane_zero_right, lane_zero_right] at h0
    have hdiv : (P + Q) / 2 ^ B = P / 2 ^ B + Q / 2 ^ B := by
      rw [Nat.add_div (pow_pos (by norm_num) _), ite_eq_right (by omega), Nat.add_zero]
    rw [lane_succ, lane_succ, lane_succ, hdiv]
    exact ih fun j => by
      have := h (j + 1)
      rwa [lane_succ, lane_succ] at this

/-- Scaling a packed vector scales its lanes when no scaled lane overflows. -/
theorem lane_mul {B P : ℕ} (c : ℕ) (h : ∀ j, c * lane B P j < 2 ^ B) (m : ℕ) :
    lane B (c * P) m = c * lane B P m := by
  induction c generalizing m with
  | zero => simp [lane_zero_left]
  | succ c ih =>
    have ih' : ∀ m, lane B (c * P) m = c * lane B P m := fun m =>
      ih (fun j => lt_of_le_of_lt (Nat.mul_le_mul_right _ (Nat.le_succ c)) (h j)) m
    rw [Nat.succ_mul, lane_add (fun j => by rw [ih' j, ← Nat.succ_mul]; exact h j), ih',
      Nat.succ_mul]

/-- A finite sum of packed vectors sums their lanes when no lane sum overflows. -/
theorem lane_sum {ι : Type*} {B : ℕ} (s : Finset ι) (f : ι → ℕ)
    (h : ∀ j, ∑ i ∈ s, lane B (f i) j < 2 ^ B) (m : ℕ) :
    lane B (∑ i ∈ s, f i) m = ∑ i ∈ s, lane B (f i) m := by
  classical
  induction s using Finset.induction_on generalizing m with
  | empty => simp [lane_zero_left]
  | insert a s ha ih =>
    have hs : ∀ j, ∑ i ∈ s, lane B (f i) j < 2 ^ B := fun j => by
      have := h j
      rw [Finset.sum_insert ha] at this
      omega
    rw [Finset.sum_insert ha, Finset.sum_insert ha, lane_add (fun j => by
      rw [ih hs j]
      have := h j
      rwa [Finset.sum_insert ha] at this), ih hs]

/-- The power `2^(B·t)` has lane `t` equal to `1` and every other lane `0`. -/
theorem lane_two_pow {B : ℕ} (hB : 0 < B) (t j : ℕ) :
    lane B (2 ^ (B * t)) j = if j = t then 1 else 0 := by
  unfold lane
  rcases lt_trichotomy j t with hjt | rfl | hjt
  · rw [ite_eq_right (by omega), show B * t = B * (t - j - 1) + B + B * j by
      rw [← Nat.mul_add_one, ← Nat.mul_add]; congr 1; omega, pow_add, pow_add,
      Nat.mul_div_cancel _ (pow_pos (by norm_num) _), Nat.mul_mod_left]
  · rw [ite_eq_left rfl, Nat.div_self (pow_pos (by norm_num) _),
      Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
  · rw [ite_eq_right (by omega), Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by norm_num)
      (Nat.mul_lt_mul_of_pos_left hjt hB)), Nat.zero_mod]

/-- A sum of distinct powers `2^(B·t)`, `t ∈ U`, has lane `j` equal to `1` exactly for `j ∈ U`. -/
theorem lane_sum_two_pow {B : ℕ} (hB : 0 < B) (U : Finset ℕ) (j : ℕ) :
    lane B (∑ t ∈ U, 2 ^ (B * t)) j = if j ∈ U then 1 else 0 := by
  have hl : ∀ j, ∑ t ∈ U, lane B (2 ^ (B * t)) j = if j ∈ U then 1 else 0 := fun j => by
    simp only [lane_two_pow hB, Finset.sum_ite_eq]
  rw [lane_sum U _ (fun j => by
    rw [hl j]
    exact lt_of_le_of_lt (by split <;> omega) (Nat.one_lt_two_pow (by omega))), hl]

end Lanes

section Reduce

/-! ### The reduction `X^k mod φ`

`powModPacked B w Φ k` is `X^k mod φ` as a packed vector, coefficient `m` in lane `m`, for the
reduction polynomial packed as `Φ = phiPacked B w T`: start from `1` and `k` times multiply by `X`
(move every lane up by one) and, when lane `w` is set, add `φ` (exclusive or). With `B = 1` it is
the bit mask of `X^k mod φ`; every lane width `B ≥ 1` gives the same lanes
(`lane_powModPacked`). -/

/-- The reduction polynomial `X^w + Σ_{t ∈ T} X^t` packed with lanes of width `B`: lane `t` is
`1` for `t ∈ insert w T` (`lane_phiPacked`). -/
def phiPacked (B w : ℕ) (T : Finset ℕ) : ℕ := ∑ t ∈ insert w T, 2 ^ (B * t)

theorem lane_phiPacked {B : ℕ} (hB : 0 < B) (w : ℕ) (T : Finset ℕ) (j : ℕ) :
    lane B (phiPacked B w T) j = if j ∈ insert w T then 1 else 0 :=
  lane_sum_two_pow hB _ j

/-- Multiply a packed polynomial by `X` and reduce once by `φ` (packed as `Φ`) when the
coefficient of `X^w` is set. -/
def mulXPacked (B w Φ s : ℕ) : ℕ :=
  if lane B (s * 2 ^ B) w = 0 then s * 2 ^ B else (s * 2 ^ B) ^^^ Φ

/-- `X^k mod φ` as a packed vector (lanes of width `B`), for `φ` packed as `Φ`. -/
def powModPacked (B w Φ : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => mulXPacked B w Φ (powModPacked B w Φ k)

/-- **The coefficient of `X^m` in `X^k mod φ`**, `φ = X^w + Σ_{t ∈ T} X^t` over `GF(2)`: bit `m`
of the bit mask `powModPacked 1 w (phiPacked 1 w T) k`. -/
def reduceBit (w : ℕ) (T : Finset ℕ) (k m : ℕ) : ℕ :=
  lane 1 (powModPacked 1 w (phiPacked 1 w T) k) m

theorem reduceBit_le_one (w : ℕ) (T : Finset ℕ) (k m : ℕ) : reduceBit w T k m ≤ 1 :=
  Nat.le_of_lt_succ (lane_lt 1 _ m)

/-- Every lane width `B ≥ 1` computes the same coefficients of `X^k mod φ`. -/
theorem lane_powModPacked {B : ℕ} (hB : 0 < B) (w : ℕ) (T : Finset ℕ) (k m : ℕ) :
    lane B (powModPacked B w (phiPacked B w T) k) m = reduceBit w T k m := by
  unfold reduceBit
  induction k generalizing m with
  | zero =>
    simp only [powModPacked]
    have h1 := lane_two_pow hB 0 m
    have h2 := lane_two_pow Nat.one_pos 0 m
    simp only [Nat.mul_zero, pow_zero] at h1 h2
    rw [h1, h2]
  | succ k ih =>
    simp only [powModPacked, mulXPacked]
    have hs : ∀ j, lane B (powModPacked B w (phiPacked B w T) k * 2 ^ B) j =
        lane 1 (powModPacked 1 w (phiPacked 1 w T) k * 2 ^ 1) j := by
      intro j
      cases j with
      | zero => rw [lane_mul_pow_zero, lane_mul_pow_zero]
      | succ j => rw [lane_mul_pow_succ, lane_mul_pow_succ, ih]
    rw [hs w]
    split
    · exact hs m
    · rw [lane_xor, lane_xor, hs m, lane_phiPacked hB, lane_phiPacked Nat.one_pos]

/-- Below the degree, `X^k mod φ` is `X^k`. -/
theorem reduceBit_of_lt {w : ℕ} (T : Finset ℕ) {k : ℕ} (hk : k < w) (m : ℕ) :
    reduceBit w T k m = if m = k then 1 else 0 := by
  unfold reduceBit
  induction k generalizing m with
  | zero =>
    have h := lane_two_pow Nat.one_pos 0 m
    simp only [Nat.mul_zero, pow_zero] at h
    simp only [powModPacked]
    exact h
  | succ k ih =>
    simp only [powModPacked, mulXPacked]
    have hs : ∀ j, lane 1 (powModPacked 1 w (phiPacked 1 w T) k * 2 ^ 1) j =
        if j = k + 1 then 1 else 0 := by
      intro j
      cases j with
      | zero => rw [lane_mul_pow_zero]; simp
      | succ j => rw [lane_mul_pow_succ, ih (by omega)]; simp
    rw [hs w, ite_eq_right (show ¬ w = k + 1 by omega), ite_eq_left rfl]
    exact hs m

end Reduce

variable {w : ℕ}

/-- Coefficients of the product of two bit polynomials over `ℕ`, degree `< 2w − 1`. -/
def prodCoeffs (rb x : Fin w → ℕ) (m : ℕ) : ℕ :=
  ∑ i : Fin w, ∑ j : Fin w, if (i : ℕ) + j = m then x i * rb j else 0


/-- `ApplyConv`: the product coefficients, each monomial `X^k` replaced by the coefficients of
`X^k mod φ` (`reduceBit`). -/
def applyConv (T : Finset ℕ) (rb x : Fin w → ℕ) (m : Fin w) : ℕ :=
  ∑ k ∈ Finset.range (2 * w - 1), prodCoeffs rb x k * reduceBit w T k m

/-- The matrix, column `b` being the action on the unit vector `e_b`. -/
def matrix (T : Finset ℕ) (rb : Fin w → ℕ) : Matrix (Fin w) (Fin w) ℕ :=
  fun m b => applyConv T rb (Pi.single b 1) m

/-- Largest coordinate of `Conv(r) · bits(x)` over all bit vectors `r, x`: the largest coordinate on
the all-one inputs, the largest row sum of `Conv(1…1)`. -/
def convMax (w : ℕ) (T : Finset ℕ) : ℕ :=
  Finset.univ.sup fun m : Fin w => applyConv T (fun _ => 1) (fun _ => 1) m

/-- The product coefficients against a unit vector `e_b` are `rb` shifted by `b`. -/
theorem prodCoeffs_single (rb : Fin w → ℕ) (b : Fin w) (m : ℕ) :
    prodCoeffs rb (Pi.single b 1) m =
      ∑ j : Fin w, if (b : ℕ) + j = m then rb j else 0 := by
  classical
  unfold prodCoeffs
  rw [Finset.sum_eq_single b]
  · simp
  · intro i _ hi
    simp [hi]
  · simp

theorem prodCoeffs_eq_sum_single (rb x : Fin w → ℕ) (m : ℕ) :
    prodCoeffs rb x m =
      ∑ b : Fin w, prodCoeffs rb (Pi.single b 1) m * x b := by
  classical
  rw [prodCoeffs]
  apply Finset.sum_congr rfl
  intro b _
  rw [prodCoeffs_single, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  split <;> simp_all [Nat.mul_comm]

/-- The product coefficients of the all-one bit vectors: the number of ways to
write `m` as a sum of two indices below `w`. -/
theorem prodCoeffs_one (m : ℕ) :
    prodCoeffs (w := w) (fun _ => 1) (fun _ => 1) m = min (m + 1) (2 * w - 1 - m) := by
  classical
  have hinner : ∀ i : Fin w,
      (∑ j : Fin w, if (i : ℕ) + (j : ℕ) = m then 1 * 1 else 0) =
        if (i : ℕ) ≤ m ∧ m < (i : ℕ) + w then 1 else 0 := by
    intro i
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one,
      mul_one]
    by_cases hi : (i : ℕ) ≤ m ∧ m < (i : ℕ) + w
    · rw [ite_eq_left hi, Finset.card_eq_one]
      refine ⟨⟨m - i, by omega⟩, ?_⟩
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
      omega
    · rw [ite_eq_right hi, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _
      have := j.isLt
      omega
  unfold prodCoeffs
  simp_rw [hinner]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i ≤ m ∧ m < i + w then (1 : ℕ) else 0),
    Finset.sum_boole, Nat.cast_id]
  have hset : (Finset.range w).filter (fun i => i ≤ m ∧ m < i + w)
      = Finset.Icc (m + 1 - w) (min (w - 1) m) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, le_min_iff]
    omega
  rw [hset, Nat.card_Icc]
  omega


/-- `applyConv` is linear in `x`: the action of the matrix. -/
theorem applyConv_eq_mulVec (T : Finset ℕ) (rb x : Fin w → ℕ) :
    applyConv T rb x = (matrix T rb).mulVec x := by
  funext m
  change applyConv T rb x m = ∑ b, applyConv T rb (Pi.single b 1) m * x b
  simp only [applyConv, prodCoeffs_eq_sum_single rb x, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The sum of a row is `ApplyConv` on the all-one bit vector. -/
theorem matrix_rowSum_eq_applyConv (T : Finset ℕ) (rb : Fin w → ℕ) (m : Fin w) :
    ∑ b, matrix T rb m b = applyConv T rb (fun _ => 1) m := by
  rw [applyConv_eq_mulVec]
  simp [Matrix.mulVec, dotProduct]

theorem prodCoeffs_mono {rb rb' x x' : Fin w → ℕ}
    (hr : ∀ i, rb i ≤ rb' i) (hx : ∀ i, x i ≤ x' i) (m : ℕ) :
    prodCoeffs rb x m ≤ prodCoeffs rb' x' m := by
  unfold prodCoeffs
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  split
  · exact Nat.mul_le_mul (hx i) (hr j)
  · exact le_rfl


/-- `applyConv` is monotone in both inputs, coordinatewise. -/
theorem applyConv_mono (T : Finset ℕ) {rb rb' x x' : Fin w → ℕ}
    (hr : ∀ i, rb i ≤ rb' i) (hx : ∀ i, x i ≤ x' i) (m : Fin w) :
    applyConv T rb x m ≤ applyConv T rb' x' m :=
  Finset.sum_le_sum fun k _ => Nat.mul_le_mul_right _ (prodCoeffs_mono hr hx k)

/-- The coordinate bound: on bit vectors every coordinate is at most `convMax w T`, by monotonicity
from the all-one inputs. -/
theorem applyConv_le_convMax (T : Finset ℕ) {rb x : Fin w → ℕ} (hr : ∀ i, rb i ≤ 1)
    (hx : ∀ i, x i ≤ 1) (m : Fin w) : applyConv T rb x m ≤ convMax w T :=
  (applyConv_mono T hr hx m).trans
    (Finset.le_sup (f := fun m : Fin w => applyConv T (fun _ => 1) (fun _ => 1) m)
      (Finset.mem_univ m))

/-- A `Conv` matrix built from bits has row sum at most `convMax w T`. -/
theorem matrix_rowSum_le_convMax (T : Finset ℕ) {rb : Fin w → ℕ} (hr : ∀ i, rb i ≤ 1)
    (m : Fin w) : ∑ b, matrix T rb m b ≤ convMax w T := by
  rw [matrix_rowSum_eq_applyConv]
  exact applyConv_le_convMax T hr (fun _ => le_rfl) m

/-- An entry of `Conv(r)`: `Σ_j bits(r)_j · bit_m(X^(b+j) mod φ)`. -/
theorem matrix_apply (T : Finset ℕ) (rb : Fin w → ℕ) (m b : Fin w) :
    matrix T rb m b = ∑ j : Fin w, rb j * reduceBit w T (b + j) m := by
  simp only [matrix, applyConv, prodCoeffs_single, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq (Finset.range (2 * w - 1)) ((b : ℕ) + j),
    ite_eq_left (Finset.mem_range.mpr (by omega))]

/-- **Every entry of `Conv(r)` lies in `[0, w]`** (`def:macconv`, the paper's bound `[0, ω]`):
entry `(m, b)` is a sum over the `w` bits of `r` of coefficients `0` or `1`, for any reduction
polynomial. -/
theorem matrix_le_width (T : Finset ℕ) {rb : Fin w → ℕ} (hr : ∀ i, rb i ≤ 1) (m b : Fin w) :
    matrix T rb m b ≤ w := by
  rw [matrix_apply]
  calc ∑ j : Fin w, rb j * reduceBit w T (b + j) m ≤ ∑ _j : Fin w, 1 :=
        Finset.sum_le_sum fun j _ => by
          simpa using Nat.mul_le_mul (hr j) (reduceBit_le_one w T (b + j) m)
    _ = w := by simp

section Packed

/-! ### Packed evaluation of `convMax`

The concrete bounds `convMax_gf2_128` and `convMax_gf2_256` are kernel computations. The row
sums `Σ_k c_k · bit_m(X^k mod φ)` of `Conv(1…1)`, with `c_k` the product coefficients of the
all-one inputs, are accumulated lane by lane in one natural number with lanes of `B` bits
(`accPacked`): the kernel evaluates the `2w − 1` steps with its built-in natural number arithmetic.
No lane overflows when `(2w − 1) · w < 2^B`, and `convMax_eq_packed` transfers the result. -/

/-- The reduction polynomial packed from a list of taps: `Σ_{t ∈ w :: Tl} 2^(B·t)`. -/
def phiList (B w : ℕ) (Tl : List ℕ) : ℕ := ((w :: Tl).map fun t => 2 ^ (B * t)).sum

theorem phiList_eq {B w : ℕ} {T : Finset ℕ} {Tl : List ℕ} (hTl : (w :: Tl).Nodup)
    (hT : Tl.toFinset = T) : phiList B w Tl = phiPacked B w T := by
  rw [phiList, phiPacked, ← hT, ← List.toFinset_cons, List.sum_toFinset _ hTl]

/-- The product coefficient of `X^k` on the all-one inputs, `min (k + 1) (2w − 1 − k)`. -/
def onesCoeff (w k : ℕ) : ℕ := min (k + 1) (2 * w - 1 - k)

/-- The packed row sums of `Conv(1…1)`: the pair `(X^n mod φ, Σ_{k<n} c_k · (X^k mod φ))` after
`n = 2w − 1` steps, packed with lanes of width `B`, for `φ` packed as `Φ`. -/
def accPacked (B w Φ : ℕ) : ℕ × ℕ :=
  (List.range (2 * w - 1)).foldl
    (fun p k => (mulXPacked B w Φ p.1, p.2 + onesCoeff w k * p.1)) (1, 0)

theorem foldl_accPacked (B w Φ n : ℕ) :
    (List.range n).foldl (fun p k => (mulXPacked B w Φ p.1, p.2 + onesCoeff w k * p.1)) (1, 0) =
      (powModPacked B w Φ n, ∑ k ∈ Finset.range n, onesCoeff w k * powModPacked B w Φ k) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ]
    rfl

/-- **`convMax` from the packed row sums**: the largest of the low `w` lanes of `accPacked`, for
distinct taps and lanes wide enough, `(2w − 1) · w < 2^B`. -/
theorem convMax_eq_packed {B w : ℕ} {T : Finset ℕ} {Tl : List ℕ} (hB : 0 < B)
    (hw : (2 * w - 1) * w < 2 ^ B) (hTl : (w :: Tl).Nodup) (hT : Tl.toFinset = T) :
    convMax w T = Finset.univ.sup fun m : Fin w => lane B (accPacked B w (phiList B w Tl)).2 m := by
  rw [convMax]
  congr 1
  funext m
  have hc : ∀ k, onesCoeff w k ≤ w := fun k => by unfold onesCoeff; omega
  have hwB : w < 2 ^ B := by
    rcases Nat.eq_zero_or_pos w with h | h
    · rw [h]; exact pow_pos (by norm_num) _
    · exact lt_of_le_of_lt (Nat.le_mul_of_pos_left w (by omega)) hw
  have hcr : ∀ k j, onesCoeff w k * reduceBit w T k j ≤ w := fun k j => by
    simpa using Nat.mul_le_mul (hc k) (reduceBit_le_one w T k j)
  have hlane : ∀ k j, lane B (onesCoeff w k * powModPacked B w (phiPacked B w T) k) j =
      onesCoeff w k * reduceBit w T k j := fun k j => by
    rw [lane_mul _ (fun j => by
      rw [lane_powModPacked hB]
      exact lt_of_le_of_lt (hcr k j) hwB) j,
      lane_powModPacked hB]
  rw [accPacked, foldl_accPacked, phiList_eq hTl hT, lane_sum _ _ (fun j => by
    simp only [hlane]
    calc ∑ k ∈ Finset.range (2 * w - 1), onesCoeff w k * reduceBit w T k j
        ≤ ∑ _k ∈ Finset.range (2 * w - 1), w := Finset.sum_le_sum fun k _ => hcr k j
      _ < 2 ^ B := by simpa using hw)]
  simp only [hlane]
  simp only [applyConv, prodCoeffs_one, onesCoeff]

end Packed

/-- The `GF(2¹²⁸)` coordinate bound `504`, by kernel evaluation of the packed row sums of
`Conv(1…1)` (`convMax_eq_packed`). -/
theorem convMax_gf2_128 : convMax 128 gf2_128Taps = 504 := by
  rw [convMax_eq_packed (B := 32) (T := gf2_128Taps) (Tl := [0, 1, 2, 7]) (by norm_num) (by norm_num) (by decide) rfl]
  decide +kernel

/-- The taps of the `GF(2²⁵⁶)` reduction polynomial `X²⁵⁶ + X¹⁰ + X⁵ + X² + 1`
(`lib/gf2k/sysdep256.h:6`). -/
def gf2_256Taps : Finset ℕ := {0, 2, 5, 10}

/-- The tap powers of `GF(2²⁵⁶)` summed, written out. -/
theorem sum_gf2_256Taps {R : Type*} [CommSemiring R] (α : R) :
    ∑ t ∈ gf2_256Taps, α ^ t = α ^ 10 + α ^ 5 + α ^ 2 + 1 := by
  simp [gf2_256Taps]
  ring

/-- The `GF(2²⁵⁶)` coordinate bound `1017`, by kernel evaluation of the packed row sums of
`Conv(1…1)` (`convMax_eq_packed`). -/
theorem convMax_gf2_256 : convMax 256 gf2_256Taps = 1017 := by
  rw [convMax_eq_packed (B := 32) (T := gf2_256Taps) (Tl := [0, 2, 5, 10]) (by norm_num) (by norm_num) (by decide) rfl]
  decide +kernel

section Eval

variable {R : Type*} [CommSemiring R]

/-- Evaluating the product coefficients at `α` gives the product of the two
evaluated bit polynomials. -/
theorem prodCoeffs_eval (rb x : Fin w → ℕ) (α : R) :
    ∑ k ∈ Finset.range (2 * w - 1), (prodCoeffs rb x k : R) * α ^ k =
      (∑ j : Fin w, (rb j : R) * α ^ (j : ℕ)) * ∑ i : Fin w, (x i : R) * α ^ (i : ℕ) := by
  simp only [prodCoeffs, Nat.cast_sum, Nat.cast_ite, Nat.cast_mul, Nat.cast_zero,
    Finset.sum_mul, ite_mul, zero_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq (Finset.range (2 * w - 1)) ((i : ℕ) + j),
    ite_eq_left (Finset.mem_range.mpr (by omega)), pow_add]
  ring


/-- In characteristic two the exclusive or of two bits casts to their sum. -/
theorem cast_xor_of_le_one {R : Type*} [CommRing R] [CharP R 2] {a b : ℕ} (ha : a ≤ 1)
    (hb : b ≤ 1) : ((a ^^^ b : ℕ) : R) = a + b := by
  have h2 : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  interval_cases a <;> interval_cases b
  · simp
  · simp
  · simp
  · rw [show (1 ^^^ 1 : ℕ) = 0 from rfl, Nat.cast_zero, Nat.cast_one, one_add_one_eq_two, h2]

/-- **`X^k mod φ` evaluates to `α^k`** at any `α` with `α^w = Σ_{t ∈ T} α^t` in characteristic
two, the taps below `w`; its coefficients at and above `w` vanish. -/
theorem reduceBit_eval_aux {R : Type*} [CommRing R] [CharP R 2] {T : Finset ℕ}
    (hT : ∀ t ∈ T, t < w) (hw : 0 < w) {α : R} (hα : α ^ w = ∑ t ∈ T, α ^ t) (k : ℕ) :
    (∀ j, w ≤ j → reduceBit w T k j = 0) ∧
      ∑ m ∈ Finset.range w, (reduceBit w T k m : R) * α ^ m = α ^ k := by
  have h2 : (2 : R) = 0 := by exact_mod_cast CharP.cast_eq_zero R 2
  induction k with
  | zero =>
    refine ⟨fun j hj => by rw [reduceBit_of_lt T hw, ite_eq_right (by omega)], ?_⟩
    simp only [reduceBit_of_lt T hw, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_range, ite_eq_left hw, pow_zero]
  | succ k ih =>
    obtain ⟨ihz, ihe⟩ := ih
    unfold reduceBit at ihz ihe ⊢
    set S := powModPacked 1 w (phiPacked 1 w T) k
    set s := S * 2 ^ 1 with hsdef
    have hs0 : lane 1 s 0 = 0 := lane_mul_pow_zero 1 S
    have hss : ∀ j, lane 1 s (j + 1) = lane 1 S j := lane_mul_pow_succ 1 S
    have hsz : ∀ j, w + 1 ≤ j → lane 1 s j = 0 := fun j hj => by
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      rw [hss]
      exact ihz j' (by omega)
    have hse : ∑ m ∈ Finset.range (w + 1), (lane 1 s m : R) * α ^ m = α ^ (k + 1) := by
      rw [Finset.sum_range_succ', hs0]
      simp only [hss, Nat.cast_zero, zero_mul, add_zero, pow_succ]
      rw [← ihe, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => by ring
    have hstep : powModPacked 1 w (phiPacked 1 w T) (k + 1) = mulXPacked 1 w (phiPacked 1 w T) S :=
      rfl
    rw [hstep, mulXPacked, ← hsdef]
    split
    · rename_i hw0
      refine ⟨fun j hj => ?_, ?_⟩
      · rcases Nat.eq_or_lt_of_le hj with rfl | hj
        · exact hw0
        · exact hsz j hj
      · rw [← hse, Finset.sum_range_succ, hw0, Nat.cast_zero, zero_mul, add_zero]
    · rename_i hw1
      have hl1 : lane 1 s w = 1 := by
        have := lane_lt 1 s w
        omega
      have hx : ∀ j, lane 1 (s ^^^ phiPacked 1 w T) j =
          lane 1 s j ^^^ (if j ∈ insert w T then 1 else 0) := fun j => by
        rw [lane_xor, lane_phiPacked Nat.one_pos]
      have hwT : w ∉ T := fun h => by have := hT w h; omega
      have hzw : lane 1 (s ^^^ phiPacked 1 w T) w = 0 := by
        rw [hx, hl1, ite_eq_left (Finset.mem_insert_self w T)]
        rfl
      refine ⟨fun j hj => ?_, ?_⟩
      · rcases Nat.eq_or_lt_of_le hj with rfl | hj
        · exact hzw
        · rw [hx, hsz j hj, ite_eq_right (fun h => by
            rcases Finset.mem_insert.mp h with h | h
            · omega
            · have := hT j h; omega)]
          rfl
      · have hsum : ∑ m ∈ Finset.range (w + 1), (lane 1 (s ^^^ phiPacked 1 w T) m : R) * α ^ m =
            α ^ (k + 1) := by
          simp only [hx]
          rw [Finset.sum_congr rfl fun m _ => by
            rw [cast_xor_of_le_one (Nat.le_of_lt_succ (lane_lt 1 s m)) (by split <;> omega),
              add_mul]]
          rw [Finset.sum_add_distrib, hse]
          simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul, one_mul, zero_mul,
            Finset.sum_ite_mem]
          rw [Finset.inter_eq_right.mpr (fun t ht => by
              rcases Finset.mem_insert.mp ht with rfl | ht
              · exact Finset.mem_range.mpr (by omega)
              · exact Finset.mem_range.mpr (by have := hT t ht; omega)),
            Finset.sum_insert hwT, ← hα, ← two_mul, h2, zero_mul, add_zero]
        rw [← hsum, Finset.sum_range_succ, hzw, Nat.cast_zero, zero_mul, add_zero]

/-- **`X^k mod φ` evaluates to `α^k`** at any `α` with `α^w = Σ_{t ∈ T} α^t`, in characteristic
two, the taps below `w`. -/
theorem reduceBit_eval {R : Type*} [CommRing R] [CharP R 2] {T : Finset ℕ}
    (hT : ∀ t ∈ T, t < w) {α : R} (hα : α ^ w = ∑ t ∈ T, α ^ t) (k : ℕ) :
    ∑ m : Fin w, (reduceBit w T k m : R) * α ^ (m : ℕ) = α ^ k := by
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst hw
    have hT0 : T = ∅ := Finset.eq_empty_of_forall_notMem fun t ht => by have := hT t ht; omega
    rw [hT0, Finset.sum_empty, pow_zero] at hα
    have h : ∀ a : R, a = 0 := fun a => by rw [← mul_one a, hα, mul_zero]
    rw [h (α ^ k)]
    exact h _
  · rw [Fin.sum_univ_eq_sum_range (fun m => (reduceBit w T k m : R) * α ^ m) w]
    obtain ⟨-, h⟩ := reduceBit_eval_aux hT hw hα k
    exact h

/-- `applyConv` computes multiplication in `GF(2)[X]/(X^w + Σ_{t ∈ T} X^t)`: in characteristic
two, evaluated at any `α` with `α^w = Σ_{t ∈ T} α^t`, its output is the product of the evaluated
inputs.  The taps lie below `w` (`hT`). -/
theorem applyConv_eval {R : Type*} [CommRing R] [CharP R 2] {T : Finset ℕ}
    (hT : ∀ t ∈ T, t < w) {α : R} (hα : α ^ w = ∑ t ∈ T, α ^ t) (rb x : Fin w → ℕ) :
    ∑ m : Fin w, (applyConv T rb x m : R) * α ^ (m : ℕ) =
      (∑ j : Fin w, (rb j : R) * α ^ (j : ℕ)) * ∑ i : Fin w, (x i : R) * α ^ (i : ℕ) := by
  rw [← prodCoeffs_eval]
  simp only [applyConv, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← reduceBit_eval hT hα k, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => by ring

end Eval

end GordieHowe.Conv
