-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.NegacyclicSpectrum
public import GordieHowe.Foundations.Algebra.BitReverse
public import GordieHowe.Foundations.Algebra.ConvMatrix

@[expose] public section

/-!
# GordieHowe: the meanings of the plan's named operators and Logic builders

The named operators of the plan's program (`GordieHowe.RealizedProgram.NamedOp`, the C++ operators of
`lib/gordiehowe/ops/operators.h`) and its Logic builders (`GordieHowe.RealizedProgram.LogicOp`,
`lib/circuits/logic/logic.h`), as functions on vectors `ℕ → K` of a field `K` (coordinates past a
block's length are `0`). Where a specification of the operation exists in this development, the
meaning is that specification, and a lemma states that it agrees with the operator's defining
formula:

* the negacyclic convolution is the vendored `LatticeCrypto.negacyclicConvCoeff`
  (`negacyclic_apply`: `y_j = Σ_{i+k=j} h_i x_k − Σ_{i+k=j+n} h_i x_k`);
* the negacyclic transform in natural order is `DFT.negSpectrum` (`nttNatural_apply`:
  `y_m = Σ_i x_i ψ^((2m+1) i)`), in scheme order at the bit reversal `bitRevNat`
  (`nttScheme_apply`: `y_m = Σ_i x_i ψ^((2·br(m)+1) i)`);
* the inverse transform is a right inverse of the scheme-order transform at a primitive `2n`-th
  root of unity (`nttScheme_inverseNtt`);
* the MAC's carry-free convolution is `Conv.matrix` (`GordieHowe/Foundations/Algebra/ConvMatrix.lean`, the
  transcription of `ApplyConv` and of the C++ `mac_fold`), column `i` of chunk `c` being
  `fold(R_c · x^i)` (`macConv_natCast`: on naturals it is `Σ_c ApplyConv(r_c, x_c)`).

The others are new definitions, transcribing the operators' defining formulas: the transposed
transform, the acyclic convolution, the row products, the diagonals, the sums and the digit
recombination. The Logic builders transcribe `lt_reduce`, `eq_reduce` and the balanced AND and OR
trees (`land`, `lor`), with `lxor(a, b) = a + b − 2ab` (the odd-characteristic form, equal to
`a + b` in characteristic two), over any commutative ring, so the integer reading of `mod_q` uses
the same polynomials.
-/

namespace GordieHowe.RealizedProgram.Ops

open GordieHowe.DFT

/-! ## Vectors -/

section Vectors

variable {R : Type*} [Zero R]

/-- **A vector on `Fin n` as a vector on `ℕ`**, `0` past the end. -/
def ofFin {n : ℕ} (y : Fin n → R) (j : ℕ) : R := if h : j < n then y ⟨j, h⟩ else 0

/-- **The first `n` coordinates** of a vector on `ℕ`. -/
def toFin (n : ℕ) (x : ℕ → R) : Fin n → R := fun i => x i

@[simp] theorem ofFin_of_lt {n : ℕ} (y : Fin n → R) {j : ℕ} (h : j < n) : ofFin y j = y ⟨j, h⟩ :=
  dif_pos h

omit [Zero R] in
@[simp] theorem toFin_apply (n : ℕ) (x : ℕ → R) (i : Fin n) : toFin n x i = x i := rfl

end Vectors

variable {K : Type*} [Field K]

/-! ## Negacyclic convolution and transforms -/

/-- **The negacyclic convolution** of length `n`, `h · x` in `K[X]/(X^n + 1)`: the vendored
`LatticeCrypto.negacyclicConvCoeff` (`negacyclic_apply` is the operator's defining formula). -/
def negacyclic (n : ℕ) (h x : ℕ → K) : ℕ → K :=
  ofFin (LatticeCrypto.negacyclicConvCoeff (toFin n h) (toFin n x))

/-- **The negacyclic convolution is the operator's defining formula** (`negacyclicConv`):
`y_j = Σ_{i+k=j} h_i x_k − Σ_{i+k=j+n} h_i x_k`. -/
theorem negacyclic_apply (n : ℕ) (h x : ℕ → K) {j : ℕ} (hj : j < n) :
    negacyclic n h x j =
      (∑ i : Fin n, ∑ k : Fin n, if (i : ℕ) + k = j then h i * x k else 0) -
        ∑ i : Fin n, ∑ k : Fin n, if (i : ℕ) + k = j + n then h i * x k else 0 := by
  rw [negacyclic, ofFin_of_lt _ hj, LatticeCrypto.negacyclicConvCoeff, Fintype.sum_prod_type,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hi := i.isLt
  have hk := k.isLt
  simp only [toFin_apply]
  have hmod : ((i : ℕ) + k) % n = if (i : ℕ) + k < n then (i : ℕ) + k else (i : ℕ) + k - n := by
    split_ifs with hlt
    · exact Nat.mod_eq_of_lt hlt
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hmod]
  split_ifs <;> first | (exfalso; omega) | ring

/-- **The negacyclic transform in natural order**: `DFT.negSpectrum`, the evaluation at
`ψ^(2m+1)` (`nttNatural_apply`). -/
def nttNatural (n : ℕ) (ψ : K) (x : ℕ → K) : ℕ → K := ofFin (negSpectrum ψ (toFin n x))

/-- **The natural-order transform is the operator's defining formula** (`ntt n ψ natural`):
`y_m = Σ_i x_i ψ^((2m+1) i)`. -/
theorem nttNatural_apply (n : ℕ) (ψ : K) (x : ℕ → K) {m : ℕ} (hm : m < n) :
    nttNatural n ψ x m = ∑ i : Fin n, x i * ψ ^ ((2 * m + 1) * i) := by
  rw [nttNatural, ofFin_of_lt _ hm, negSpectrum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [toFin_apply, Nat.mul_comm]

/-- **The negacyclic transform in scheme order**: frequency `m` is the natural-order frequency
`br(m)`, `br` the bit reversal on `log₂ n` bits (`bitRevNat`; `GordieHowe/Foundations/Algebra/BitReverse.lean`, the
order of `host_ntt::NegacyclicPlan`). -/
def nttScheme (n : ℕ) (ψ : K) (x : ℕ → K) (m : ℕ) : K :=
  if m < n then nttNatural n ψ x (bitRevNat (Nat.log2 n) m) else 0

/-- **The scheme-order transform is the operator's defining formula** (`ntt n ψ scheme`), for
`n = 2^k`: `y_m = Σ_i x_i ψ^((2·br(m)+1) i)`. -/
theorem nttScheme_apply {k n : ℕ} (hn : n = 2 ^ k) (ψ : K) (x : ℕ → K) {m : ℕ} (hm : m < n) :
    nttScheme n ψ x m = ∑ i : Fin n, x i * ψ ^ ((2 * bitRevNat k m + 1) * i) := by
  subst hn
  rw [nttScheme, if_pos hm, Nat.log2_two_pow, nttNatural_apply _ _ _ (bitRevNat_lt k m)]

/-- **The inverse transform** (`inverseNtt n ψ`): `x_i = n⁻¹ Σ_m y_m ψ^(−(2·br(m)+1) i)`, the
inverse of the scheme-order transform at a primitive `2n`-th root `ψ` (`nttScheme_inverseNtt`). -/
def inverseNtt (n : ℕ) (ψ : K) (y : ℕ → K) (i : ℕ) : K :=
  if i < n then
    (n : K)⁻¹ * ∑ m : Fin n, y m * ψ⁻¹ ^ ((2 * bitRevNat (Nat.log2 n) m + 1) * i)
  else 0

/-- **The inverse transform inverts the scheme-order transform** (the defining formula of
`inverseNtt n ψ`: the inverse of `ntt n ψ scheme`), for `n = 2^k` invertible in `K` and `ψ` a
primitive `2n`-th root of unity. -/
theorem nttScheme_inverseNtt {k n : ℕ} (hn : n = 2 ^ k) {ψ : K} (hψ : IsPrimitiveRoot ψ (2 * n))
    (hn0 : (n : K) ≠ 0) (y : ℕ → K) {m : ℕ} (hm : m < n) :
    nttScheme n ψ (inverseNtt n ψ y) m = y m := by
  have hn0' : n ≠ 0 := fun h => hn0 (by rw [h, Nat.cast_zero])
  have hψ0 : ψ ≠ 0 := hψ.ne_zero (by omega)
  have hω : IsPrimitiveRoot (ψ ^ 2) n := IsPrimitiveRoot.sq_of_two_mul hψ hn0'
  have hlog : Nat.log2 n = k := by rw [hn, Nat.log2_two_pow]
  have hbr : ∀ j : ℕ, bitRevNat k j < n := fun j => hn ▸ bitRevNat_lt k j
  rw [nttScheme_apply hn ψ _ hm]
  -- Each term: `n⁻¹ Σ_{m'} y_{m'} ψ^(2 br(m) i) ψ^(−2 br(m') i)`, the `ψ^(±i)` cancelling.
  have hterm : ∀ i : Fin n, inverseNtt n ψ y i * ψ ^ ((2 * bitRevNat k m + 1) * i) =
      (n : K)⁻¹ * ∑ m' : Fin n, y m' *
        ((ψ ^ 2) ^ ((bitRevNat k m : ℕ) * i) * (ψ ^ 2)⁻¹ ^ ((i : ℕ) * bitRevNat k m')) := by
    intro i
    rw [inverseNtt, if_pos i.isLt, hlog, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun m' _ => ?_
    have hsplit : ∀ b : ℕ, ψ ^ ((2 * b + 1) * (i : ℕ)) = (ψ ^ 2) ^ (b * i) * ψ ^ (i : ℕ) :=
      fun b => by rw [← pow_mul, ← pow_add]; ring_nf
    have hsplit' : ∀ b : ℕ, ψ⁻¹ ^ ((2 * b + 1) * (i : ℕ)) =
        (ψ ^ 2)⁻¹ ^ ((i : ℕ) * b) * (ψ ^ (i : ℕ))⁻¹ := fun b => by
      simp only [inv_pow]
      rw [← mul_inv, ← pow_mul, ← pow_add]
      ring_nf
    rw [hsplit, hsplit']
    have hc : (ψ ^ (i : ℕ))⁻¹ * ψ ^ (i : ℕ) = 1 := inv_mul_cancel₀ (pow_ne_zero _ hψ0)
    calc y m' * ((ψ ^ 2)⁻¹ ^ ((i : ℕ) * bitRevNat k m') * (ψ ^ (i : ℕ))⁻¹) *
          ((ψ ^ 2) ^ (bitRevNat k m * (i : ℕ)) * ψ ^ (i : ℕ))
        = y m' * ((ψ ^ 2) ^ (bitRevNat k m * (i : ℕ)) *
            (ψ ^ 2)⁻¹ ^ ((i : ℕ) * bitRevNat k m')) * ((ψ ^ (i : ℕ))⁻¹ * ψ ^ (i : ℕ)) := by ring
      _ = _ := by rw [hc, mul_one]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum, Finset.sum_comm]
  -- Orthogonality at `ω = ψ²`, the bit reversal being injective below `n`.
  have horth : ∀ m' : Fin n, ∑ i : Fin n, y m' *
      ((ψ ^ 2) ^ ((bitRevNat k m : ℕ) * i) * (ψ ^ 2)⁻¹ ^ ((i : ℕ) * bitRevNat k m')) =
        if (m' : ℕ) = m then y m' * n else 0 := by
    intro m'
    rw [← Finset.mul_sum]
    have := sum_pow_mul_inv_pow_eq hω ⟨bitRevNat k m, hbr m⟩ ⟨bitRevNat k m', hbr m'⟩
    simp only at this
    rw [this]
    by_cases hmm : (m' : ℕ) = m
    · simp [hmm]
    · have hne : (⟨bitRevNat k m, hbr m⟩ : Fin n) ≠ ⟨bitRevNat k m', hbr m'⟩ := by
        intro h
        exact hmm (bitRevNat_injOn (hn ▸ m'.isLt) (hn ▸ hm) (Fin.mk.inj_iff.mp h).symm)
      simp [hne, hmm]
  rw [Finset.sum_congr rfl fun m' _ => horth m']
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hfilter : (Finset.univ.filter fun m' : Fin n => (m' : ℕ) = m) = {⟨m, hm⟩} := by
    ext m'
    simp [Fin.ext_iff]
  rw [hfilter, Finset.sum_singleton, ← mul_assoc, mul_comm _ (y m), mul_assoc,
    inv_mul_cancel₀ hn0, mul_one]

/-- **The scheme-order transform at frequency `m`** is the natural-order transform `negSpectrum` at
the bit reversal of `m`, for `n = 2^k`. -/
theorem nttScheme_eq_negSpectrum {k : ℕ} (ψ : K) (x : ℕ → K) (m : Fin (2 ^ k)) :
    nttScheme (2 ^ k) ψ x m = negSpectrum ψ (toFin (2 ^ k) x) (bitRev k m) := by
  rw [nttScheme, if_pos m.isLt, Nat.log2_two_pow,
    nttNatural, ofFin_of_lt _ (bitRevNat_lt k m)]
  rfl

/-- **The scheme-order transform is injective** on the first `n` coordinates, for `n = 2^k`
invertible in `K` and `ψ` a primitive `2n`-th root of unity (`negSpectrum_injective`, the bit
reversal a permutation). -/
theorem toFin_eq_of_nttScheme_eq {k n : ℕ} (hn : n = 2 ^ k) {ψ : K}
    (hψ : IsPrimitiveRoot ψ (2 * n)) (hn0 : (n : K) ≠ 0) {x y : ℕ → K}
    (h : ∀ m < n, nttScheme n ψ x m = nttScheme n ψ y m) : toFin n x = toFin n y := by
  subst hn
  apply negSpectrum_injective hψ hn0
  funext j
  have := h ((bitRev k).symm j) ((bitRev k).symm j).isLt
  rw [nttScheme_eq_negSpectrum ψ x ((bitRev k).symm j),
    nttScheme_eq_negSpectrum ψ y ((bitRev k).symm j), Equiv.apply_symm_apply] at this
  exact this

/-- **The inverse transform is a left inverse of the scheme-order transform** below `n`
(`nttScheme_inverseNtt` and the transform's injectivity, `toFin_eq_of_nttScheme_eq`). -/
theorem inverseNtt_nttScheme {k n : ℕ} (hn : n = 2 ^ k) {ψ : K} (hψ : IsPrimitiveRoot ψ (2 * n))
    (hn0 : (n : K) ≠ 0) (x : ℕ → K) {i : ℕ} (hi : i < n) :
    inverseNtt n ψ (nttScheme n ψ x) i = x i := by
  have h := toFin_eq_of_nttScheme_eq hn hψ hn0 (x := inverseNtt n ψ (nttScheme n ψ x)) (y := x)
    fun m hm => nttScheme_inverseNtt hn hψ hn0 _ hm
  exact congrFun h ⟨i, hi⟩

/-- **The inverse transform reads only its input's first `n` coordinates.** -/
theorem inverseNtt_congr {n : ℕ} {ψ : K} {x y : ℕ → K} (hxy : ∀ m < n, x m = y m) (i : ℕ) :
    inverseNtt n ψ x i = inverseNtt n ψ y i := by
  unfold inverseNtt
  split_ifs
  · congr 1
    exact Finset.sum_congr rfl fun m _ => by rw [hxy m m.isLt]
  · rfl

/-- **The inverse transform commutes with a field homomorphism.** -/
theorem map_inverseNtt {K' : Type*} [Field K'] (f : K →+* K') (n : ℕ) (ψ : K) (y : ℕ → K)
    (i : ℕ) : f (inverseNtt n ψ y i) = inverseNtt n (f ψ) (fun m => f (y m)) i := by
  unfold inverseNtt
  split_ifs
  · rw [map_mul, map_inv₀, map_natCast, map_sum]
    simp only [map_mul, map_pow, map_inv₀]
  · exact map_zero f

/-- **The transposed transform** (`nttTranspose n ψ`, the operator's defining formula):
`x_i = Σ_m ψ^((2m+1) i) y_m`, the transpose of the natural-order transform. -/
def nttTranspose (n : ℕ) (ψ : K) (y : ℕ → K) (i : ℕ) : K :=
  if i < n then ∑ m : Fin n, ψ ^ ((2 * (m : ℕ) + 1) * i) * y m else 0

/-! ## Products by public operands -/

/-- **The acyclic convolution** with `h` of length `lh` (`acyclicConv`, the operator's defining
formula): `y_i = Σ_{a+b=i} x_a h_b`, `[lx] → [lx + lh − 1]`. -/
def acyclic (lh lx : ℕ) (h x : ℕ → K) (i : ℕ) : K :=
  if i + 1 < lx + lh then
    ∑ a : Fin lx, ∑ b : Fin lh, if (a : ℕ) + b = i then x a * h b else 0
  else 0

/-- **The rows of a public matrix** (`rowDot M R W`, the operator's defining formula):
`y_r = Σ_c M[r][c] · x_c`, `M` row-major. -/
def rowDot (R W : ℕ) (M x : ℕ → K) (r : ℕ) : K :=
  if r < R then ∑ c : Fin W, M (r * W + c) * x c else 0

/-- **A diagonal** (`diagonal d`, `constDiagonal d`): `y_i = d_i x_i`. -/
def diagonal (n : ℕ) (d x : ℕ → K) (i : ℕ) : K := if i < n then d i * x i else 0

/-- **The sum of `w` coordinates** (`sum w`): `y_0 = Σ_{t<w} x_t`. -/
def sum (w : ℕ) (x : ℕ → K) (j : ℕ) : K := if j = 0 then ∑ t : Fin w, x t else 0

/-- **A number from its digits** (`fromDigits k base`): `y_0 = Σ_{l<k} base^l x_l`. -/
def fromDigits (k : ℕ) (base : K) (x : ℕ → K) (j : ℕ) : K :=
  if j = 0 then ∑ l : Fin k, base ^ (l : ℕ) * x l else 0

/-! ## The MAC's carry-free convolution -/

/-- **The MAC's carry-free convolution** (`macConv r w nch taps`):
`y_b = Σ_c Σ_i x[c·w + i] · Conv(r_c)[b][i]`, `Conv(r_c)` the integer matrix of multiplication by
`r_c` in the binary field of reduction polynomial `x^w + Σ_{d ∈ taps} x^d` (`Conv.matrix`: column
`i` is `fold(R_c · x^i)`, `R_c` the bits `rb c` of `r_c`, `fold` the C++ `mac_fold`), its entries
read in `K`. The reduction substitutes `x^w = Σ_{d ∈ taps} x^d`, with positive coefficients, as the
C++ (`mac_fold`, `lib/gordiehowe/ops/operators.h`) and `Conv.applyConv` do. -/
def macConv (w nch : ℕ) (taps : List ℕ) (rb : ℕ → Fin w → ℕ) (x : ℕ → K) (b : ℕ) : K :=
  if h : b < w then
    ∑ c : Fin nch, ∑ i : Fin w, (Conv.matrix taps.toFinset (rb c) ⟨b, h⟩ i : K) * x (c * w + i)
  else 0

/-- **The MAC's convolution on naturals is `ApplyConv`** (`Conv.applyConv`, the defining formula
`Σ_c fold(R_c · X_c)`): on inputs cast from naturals `xs`, output `b` is the cast of
`Σ_c ApplyConv(r_c, X_c)[b]`, `X_c` the `c`-th chunk of `w`. -/
theorem macConv_natCast (w nch : ℕ) (taps : List ℕ) (rb : ℕ → Fin w → ℕ) (xs : ℕ → ℕ) {b : ℕ}
    (hb : b < w) :
    macConv w nch taps rb (fun t => (xs t : K)) b =
      ((∑ c : Fin nch, Conv.applyConv taps.toFinset (rb c) (fun i => xs (c * w + i)) ⟨b, hb⟩ : ℕ) :
        K) := by
  rw [macConv, dif_pos hb]
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Conv.applyConv_eq_mulVec, Matrix.mulVec, dotProduct]
  push_cast
  rfl

/-! ## Logic builders -/

section Logic

variable {R : Type*} [CommRing R]

/-- **`lxor`** (`Logic::lxor`): `a + b − 2ab`, which is `a + b` in characteristic two. -/
def lxor (a b : R) : R := a + b - 2 * (a * b)

/-- **`lt_reduce`** on the bits `[i0, i0 + n)` of `a` and `b` (`Logic::lt_reduce`): the pair
`(eq, lt)`. Above one bit it splits at `i0 + n/2`, the low half first:
`eq = eq_hi · eq_lo`, `lt = lt_hi + eq_hi · lt_lo`; on one bit `eq = 1 − lxor(a, b)`,
`lt = (1 − a) · b`. An empty range gives `(1, 0)`. -/
def ltReduce (a b : ℕ → R) : ℕ → ℕ → R × R
  | 0, _ => (1, 0)
  | 1, i0 => (1 - lxor (a i0) (b i0), (1 - a i0) * b i0)
  | n + 2, i0 =>
    let lo := ltReduce a b ((n + 2) / 2) i0
    let hi := ltReduce a b (n + 2 - (n + 2) / 2) (i0 + (n + 2) / 2)
    (hi.1 * lo.1, hi.2 + hi.1 * lo.2)
termination_by n => n
decreasing_by all_goals omega

/-- **`eq_reduce`** on the bits `[i0, i0 + n)` (`Logic::eq_reduce`): `1` on an empty range,
`1 − lxor(a, b)` on one bit, the product of the halves above. -/
def eqReduce (a b : ℕ → R) : ℕ → ℕ → R
  | 0, _ => 1
  | 1, i0 => 1 - lxor (a i0) (b i0)
  | n + 2, i0 =>
    eqReduce a b ((n + 2) / 2) i0 * eqReduce a b (n + 2 - (n + 2) / 2) (i0 + (n + 2) / 2)
termination_by n => n
decreasing_by all_goals omega

/-- **The balanced AND tree** on `[i0, i0 + n)` (`Logic::land(i0, i1, f)`): `1` on an empty range,
the bit on one, the product of the halves above. -/
def andTree (a : ℕ → R) : ℕ → ℕ → R
  | 0, _ => 1
  | 1, i0 => a i0
  | n + 2, i0 => andTree a ((n + 2) / 2) i0 * andTree a (n + 2 - (n + 2) / 2) (i0 + (n + 2) / 2)
termination_by n => n
decreasing_by all_goals omega

/-- **`lor`** (`Logic::lor`): `1 − (1 − a)(1 − b)`. -/
def lor (a b : R) : R := 1 - (1 - a) * (1 - b)

/-- **The balanced OR tree** on `[i0, i0 + n)` (`Logic::lor(i0, i1, f)`): `0` on an empty range,
the bit on one, `lor` of the halves above. -/
def orTree (a : ℕ → R) : ℕ → ℕ → R
  | 0, _ => 0
  | 1, i0 => a i0
  | n + 2, i0 => lor (orTree a ((n + 2) / 2) i0) (orTree a (n + 2 - (n + 2) / 2) (i0 + (n + 2) / 2))
termination_by n => n
decreasing_by all_goals omega

/-- **`a < b` on words of `w` bits** (`Logic::lt`): `0` for `w = 0`, else `lt_reduce`'s `lt`. -/
def ltWord (w : ℕ) (a b : ℕ → R) : R := (ltReduce a b w 0).2

/-- **`a ≤ b` on words of `w` bits** (`Logic::leq`): `1 − lt(b, a)`. -/
def leqWord (w : ℕ) (a b : ℕ → R) : R := 1 - ltWord w b a

/-- **`a = b` on words of `w` bits** (`Logic::eq`): `eq_reduce`. -/
def eqWord (w : ℕ) (a b : ℕ → R) : R := eqReduce a b w 0

end Logic

end GordieHowe.RealizedProgram.Ops
