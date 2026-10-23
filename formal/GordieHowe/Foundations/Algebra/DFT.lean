-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.BigOperators.Fin
public import LatticeCrypto.Ring.Kernel

@[expose] public section

/-!
# Discrete Fourier transforms and convolution

The flagship verifier evaluates two families of extra linear rows with number theoretic transforms
over `Fp128`: the MAC accumulator rows with a length-256 cyclic transform, and the Falcon signature
rows with a length-512 negacyclic transform. The same identities are needed whether a transform runs
in the verifier or inside a circuit, so they are stated here once, over any commutative ring or
field:

* the convolution identity: the transform of a cyclic convolution is the
  pointwise product of transforms, and the inverse transform undoes the
  transform when the root is primitive and the length is invertible;
* the negacyclic product as a cyclic product of inputs twisted by `ψ` with
  `ψ ^ n = -1`;
* transposes: the transpose of cyclic multiplication by `v` is cyclic
  multiplication by the reversal of `v`, and the transpose of negacyclic
  multiplication by `h` is negacyclic multiplication by `negRev h`;
* zero-padded inputs whose supports are short enough do not wrap.

The C++ butterflies emit frequencies in bit-reversed order and the inverse
consumes that order. Pointwise products commute with any permutation of the
frequencies, so no statement here depends on the bit-reversal permutation.
-/

namespace GordieHowe.DFT

open scoped BigOperators

section CommRing

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The discrete Fourier transform with root `ω`: `dft ω a k = ∑ j, a j · ω ^ (j · k)`. -/
def dft (ω : R) (a : Fin n → R) (k : Fin n) : R :=
  ∑ j : Fin n, a j * ω ^ ((j : ℕ) * k)

/-- Cyclic convolution of length `n`, summed over input pairs as
`LatticeCrypto.negacyclicConvCoeff` is. -/
def cyclicConv (u v : Fin n → R) (k : Fin n) : R :=
  ∑ ij : Fin n × Fin n, if (ij.1.val + ij.2.val) % n = k.val then u ij.1 * v ij.2 else 0

/-- Coefficientwise multiplication by the powers of `ψ`. -/
def twist (ψ : R) (a : Fin n → R) (j : Fin n) : R := ψ ^ (j : ℕ) * a j

/-- The reversal `a ↦ v (-a mod n)`: the transpose of cyclic multiplication by
`v` is cyclic multiplication by `rev v`. -/
def rev (v : Fin n → R) (a : Fin n) : R :=
  v ⟨(n - a) % n, Nat.mod_lt _ (Fin.pos a)⟩

/-- `[h 0, -h (n-1), …, -h 1]`: the transpose of negacyclic multiplication by
`h` is negacyclic multiplication by `negRev h`. -/
def negRev (h : Fin n → R) (a : Fin n) : R :=
  if ha : (a : ℕ) = 0 then h a else -h ⟨n - a, by have := a.isLt; omega⟩

/-- `ω` is periodic with period `n` when `ω ^ n = 1`: reducing an exponent mod
`n` does not change the power. -/
theorem pow_mod_of_pow_eq_one {ω : R} {n : ℕ} (hω : ω ^ n = 1) (m : ℕ) :
    ω ^ (m % n) = ω ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m n, pow_add, pow_mul, hω, one_pow, one_mul]

/-- The pairs a cyclic sum ranges over, as `Fin n` addition rather than a
`Nat` congruence. -/
theorem add_eq_iff_val_mod_eq (i j c : Fin n) :
    i + j = c ↔ ((i : ℕ) + (j : ℕ)) % n = (c : ℕ) := by
  rw [Fin.ext_iff, Fin.val_add]

/-- `cyclicConv` sums over an unordered decomposition of the output index, so
swapping its arguments does not change it. -/
theorem cyclicConv_comm (u v : Fin n → R) (k : Fin n) :
    cyclicConv u v k = cyclicConv v u k := by
  simp only [cyclicConv, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Nat.add_comm (b : ℕ) (a : ℕ), mul_comm (u b) (v a)]

/-- `ω`'s period-`n` power splits over a sum reduced mod `n`, multiplied by a
further exponent: `ω ^ ((a + b) % n * k) = ω ^ (a * k) * ω ^ (b * k)`. -/
theorem pow_add_mod_mul {ω : R} (hω : ω ^ n = 1) (a b k : ℕ) :
    ω ^ ((a + b) % n * k) = ω ^ (a * k) * ω ^ (b * k) := by
  rw [pow_mul, pow_mod_of_pow_eq_one hω, pow_add, mul_pow, ← pow_mul, ← pow_mul]

/-- The transform of a cyclic convolution is the pointwise product of the
transforms, for any `ω` with `ω ^ n = 1`. -/
theorem dft_cyclicConv {ω : R} (hω : ω ^ n = 1) (u v : Fin n → R) :
    dft ω (cyclicConv u v) = dft ω u * dft ω v := by
  funext k
  simp only [Pi.mul_apply, dft, cyclicConv]
  rw [Finset.sum_mul_sum]
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [← add_eq_iff_val_mod_eq, Fintype.sum_ite_eq]
  rw [← Fintype.sum_prod_type']
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [Fin.val_add, pow_add_mod_mul hω]
  ring

/-- `cyclicConv` at a single output index, as a sum over one convolution
variable instead of over pairs. -/
theorem cyclicConv_eq_sum_sub (u v : Fin n → R) (k : Fin n) :
    cyclicConv u v k = ∑ a, u a * v (k - a) := by
  have : NeZero n := ⟨fun h => by subst h; exact k.elim0⟩
  have hidx : ∀ i j : Fin n, i + j = k ↔ j = k - i := fun i j => eq_sub_iff_add_eq'.symm
  simp only [cyclicConv, Fintype.sum_prod_type, ← add_eq_iff_val_mod_eq, hidx,
    Fintype.sum_ite_eq']

/-- `rev v a = v (-a)`: `rev` is negation of the index. -/
theorem rev_eq_neg (v : Fin n → R) (a : Fin n) : rev v a = v (-a) := by
  rw [Fin.neg_def]
  rfl

/-- The transpose of cyclic multiplication by `v`. -/
theorem sum_cyclicConv_mul (u v μ : Fin n → R) :
    ∑ k, cyclicConv u v k * μ k = ∑ i, u i * cyclicConv (rev v) μ i := by
  simp only [cyclicConv_eq_sum_sub, rev_eq_neg, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hn : n = 0
  · subst hn; exact a.elim0
  have : NeZero n := ⟨hn⟩
  let e : Fin n ≃ Fin n := ⟨fun k => a - k, fun k => a - k, sub_sub_cancel a, sub_sub_cancel a⟩
  exact Fintype.sum_equiv e (fun k => u a * v (k - a) * μ k)
    (fun b => u a * (v (-b) * μ (a - b)))
    (fun k => by show u a * v (k - a) * μ k = u a * (v (-(a - k)) * μ (a - (a - k)))
                 rw [neg_sub, sub_sub_cancel]; ring)

/-- `LatticeCrypto.negacyclicConvCoeff` at a single output index, as a sum over
one convolution variable, with the wrap sign written as a comparison against
the output index. -/
theorem negacyclicConvCoeff_eq_sum (f g : Fin n → R) (k : Fin n) :
    LatticeCrypto.negacyclicConvCoeff f g k =
      ∑ a : Fin n, if a ≤ k then f a * g (k - a) else -(f a * g (k - a)) := by
  have : NeZero n := ⟨fun h => by subst h; exact k.elim0⟩
  have hidx : ∀ i j : Fin n, i + j = k ↔ j = k - i := fun i j => eq_sub_iff_add_eq'.symm
  unfold LatticeCrypto.negacyclicConvCoeff
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [← add_eq_iff_val_mod_eq, hidx a, Fintype.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hak : a ≤ k
  · have hsub : (k - a).val = k.val - a.val := Fin.sub_val_of_le hak
    have hakv : a.val ≤ k.val := hak
    have hlt : a.val + (k - a).val < n := by rw [hsub]; have := k.isLt; omega
    simp [hak, hlt]
  · have hltk : k < a := not_le.mp hak
    have hsub : (k - a).val = n + k.val - a.val := Fin.coe_sub_iff_lt.mpr hltk
    have hnotlt : ¬ (a.val + (k - a).val < n) := by
      rw [hsub]
      have h1 := a.isLt
      have h2 := k.isLt
      omega
    simp [hak, hnotlt]

/-- `LatticeCrypto.negacyclicConvCoeff f` is linear in its second argument:
decomposed against the standard basis `Pi.single j 1`. -/
theorem negacyclicConvCoeff_eq_sum_mul_single (f g : Fin n → R) (k : Fin n) :
    LatticeCrypto.negacyclicConvCoeff f g k =
      ∑ j, g j * LatticeCrypto.negacyclicConvCoeff f (Pi.single j 1) k := by
  have hsingle : ∀ j : Fin n, LatticeCrypto.negacyclicConvCoeff f (Pi.single j 1) k =
      ∑ i : Fin n, if (i.val + j.val) % n = k.val then
        (if i.val + j.val < n then f i else -f i) else 0 := by
    intro j
    unfold LatticeCrypto.negacyclicConvCoeff
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_eq_single j fun j' hne => by simp [Pi.single_apply, Ne.symm hne]]
    simp [Pi.single_apply]
  simp only [hsingle]
  unfold LatticeCrypto.negacyclicConvCoeff
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hmod : (i.val + j.val) % n = k.val <;>
    by_cases hlt : i.val + j.val < n <;> simp [hmod, hlt, mul_comm]

/-- A ring homomorphism commutes with `LatticeCrypto.negacyclicConvCoeff`: applying it
to a coefficient of the negacyclic product of `a` and `b` gives the same coefficient
of the negacyclic product of `f ∘ a` and `f ∘ b`. -/
theorem negacyclicConvCoeff_map {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (a b : Fin n → R) (k : Fin n) :
    f (LatticeCrypto.negacyclicConvCoeff a b k) =
      LatticeCrypto.negacyclicConvCoeff (f ∘ a) (f ∘ b) k := by
  unfold LatticeCrypto.negacyclicConvCoeff
  rw [map_sum]
  refine Finset.sum_congr rfl fun ij _ => ?_
  by_cases h1 : (ij.1.val + ij.2.val) % n = k.val <;>
    by_cases h2 : ij.1.val + ij.2.val < n <;>
    simp [h1, h2, Function.comp_apply, map_mul, map_neg]

/-- The negacyclic product of a ternary combination `s − 2·g` with a scaled vector `a·t`
splits into the products of `s` and `g` with `t`: bilinearity of
`LatticeCrypto.negacyclicConvCoeff`. -/
theorem negacyclicConvCoeff_ternary (s g t : Fin n → R) (a : R) (k : Fin n) :
    LatticeCrypto.negacyclicConvCoeff (fun j => s j - 2 * g j) (fun j => a * t j) k =
      a * LatticeCrypto.negacyclicConvCoeff s t k -
        2 * a * LatticeCrypto.negacyclicConvCoeff g t k := by
  unfold LatticeCrypto.negacyclicConvCoeff
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ij _ => ?_
  split_ifs <;> ring

/-- The weights `negacyclicConvCoeff a (Pi.single j 1) k` applied to `g` sum to the
negacyclic product of `a` and `g`: `negacyclicConvCoeff_eq_sum_mul_single` with the
factors in the order a linear row writes them. -/
theorem sum_single_mul (a g : Fin n → R) (k : Fin n) :
    ∑ j, LatticeCrypto.negacyclicConvCoeff a (Pi.single j 1) k * g j =
      LatticeCrypto.negacyclicConvCoeff a g k := by
  rw [negacyclicConvCoeff_eq_sum_mul_single a g k]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- `negRev h a = h (-a)` at `a = 0`, and `-h (-a)` otherwise: the negacyclic
reversal is negation of the index with a sign flip away from `0`. -/
theorem negRev_eq (h : Fin n → R) (a : Fin n) :
    negRev h a = if (a : ℕ) = 0 then h (-a) else -h (-a) := by
  unfold negRev
  by_cases ha : (a : ℕ) = 0
  · rw [dif_pos ha, if_pos ha]
    congr 1
    apply Fin.ext
    rw [Fin.val_neg', ha]
    simp
  · rw [dif_neg ha, if_neg ha]
    congr 1
    congr 1
    apply Fin.ext
    rw [Fin.val_neg']
    have hpos : 0 < (a : ℕ) := Nat.pos_of_ne_zero ha
    have := a.isLt
    first
      | exact Nat.mod_eq_of_lt (by omega)
      | exact (Nat.mod_eq_of_lt (by omega)).symm

/-- `LatticeCrypto.negacyclicConvCoeff f g` weighted by `w` and summed, as a sum
over input pairs with the wrap sign made explicit and the output index in the
weight written as `Fin n` addition. -/
theorem negacyclicConvCoeff_mul_eq_sum_pairs (f g w : Fin n → R) :
    ∑ k, LatticeCrypto.negacyclicConvCoeff f g k * w k =
      ∑ ij : Fin n × Fin n,
        (if ij.1.val + ij.2.val < n then f ij.1 * g ij.2 else -(f ij.1 * g ij.2)) *
          w (ij.1 + ij.2) := by
  unfold LatticeCrypto.negacyclicConvCoeff
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [← add_eq_iff_val_mod_eq, Fintype.sum_ite_eq]

/-- The transpose of negacyclic multiplication by `h`. -/
theorem sum_negacyclicConvCoeff_mul (h s μ : Fin n → R) :
    ∑ k, LatticeCrypto.negacyclicConvCoeff h s k * μ k =
      ∑ j, s j * LatticeCrypto.negacyclicConvCoeff (negRev h) μ j := by
  by_cases hn : n = 0
  · subst hn
    simp
  have : NeZero n := ⟨hn⟩
  simp only [mul_comm (s _)]
  rw [negacyclicConvCoeff_mul_eq_sum_pairs h s μ,
    negacyclicConvCoeff_mul_eq_sum_pairs (negRev h) μ s]
  have hΦ : ∀ p : Fin n × Fin n, (-(-p.1), -p.1 + (p.1 + p.2)) = p := by
    intro p
    refine Prod.ext (neg_neg p.1) ?_
    rw [← add_assoc, neg_add_cancel, zero_add]
  let Φ : Fin n × Fin n ≃ Fin n × Fin n :=
    ⟨fun p => (-p.1, p.1 + p.2), fun p => (-p.1, p.1 + p.2), hΦ, hΦ⟩
  refine Fintype.sum_equiv Φ _ _ fun ij => ?_
  obtain ⟨i, j⟩ := ij
  show (if i.val + j.val < n then h i * s j else -(h i * s j)) * μ (i + j) =
    (if (-i).val + (i + j).val < n then negRev h (-i) * μ (i + j) else
      -(negRev h (-i) * μ (i + j))) * s (-i + (i + j))
  have hcancel : -i + (i + j) = j := by rw [← add_assoc, neg_add_cancel, zero_add]
  rw [hcancel]
  by_cases hi0 : i = 0
  · subst hi0
    have h1 : (-(0 : Fin n)) = 0 := neg_zero
    have h2 : (0 : Fin n) + j = j := zero_add j
    rw [h1, h2]
    have hlt1 : (0 : Fin n).val + j.val < n := by simpa using j.isLt
    have hlt2 : (0 : Fin n).val + j.val < n := hlt1
    rw [if_pos hlt1, if_pos hlt2]
    simp only [negRev_eq, neg_zero, Fin.val_zero]
    norm_num
    ring
  · have hnegi : (-i).val = n - i.val := by
      have := Fin.val_neg (n := n) i
      rw [if_neg hi0] at this
      exact this
    have hival0 : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
    have hine0 : ((-i : Fin n) : ℕ) ≠ 0 := by
      rw [hnegi]
      have := i.isLt
      omega
    rw [negRev_eq, if_neg hine0]
    by_cases hlt : i.val + j.val < n
    · have heqv : (i + j).val = i.val + j.val := Fin.val_add_eq_of_add_lt hlt
      have hnotlt : ¬ ((-i).val + (i + j).val < n) := by
        rw [hnegi, heqv]
        have := j.isLt
        omega
      rw [if_pos hlt, if_neg hnotlt, neg_neg]
      ring
    · have h1 := i.isLt
      have h2 := j.isLt
      have hge : n ≤ i.val + j.val := not_lt.mp hlt
      have hlt2n : i.val + j.val < 2 * n := by omega
      obtain ⟨r, hr⟩ : ∃ r, i.val + j.val = n + r := ⟨i.val + j.val - n, by omega⟩
      have hrlt : r < n := by omega
      have heqv : (i + j).val = r := by
        rw [Fin.val_add, hr, Nat.add_mod_left, Nat.mod_eq_of_lt hrlt]
      have hlt2 : (-i).val + (i + j).val < n := by rw [hnegi, heqv]; omega
      rw [if_neg hlt, if_pos hlt2, neg_neg]
      ring

/-- Inputs supported below `m` and `m'` with `m + m' ≤ n + 1` do not wrap: their
cyclic convolution is the ordinary product's coefficients. -/
theorem cyclicConv_eq_of_support {m m' : ℕ} {u v : Fin n → R}
    (hu : ∀ i : Fin n, m ≤ i → u i = 0) (hv : ∀ j : Fin n, m' ≤ j → v j = 0)
    (hmn : m + m' ≤ n + 1) (k : Fin n) :
    cyclicConv u v k =
      ∑ ij : Fin n × Fin n, if ij.1.val + ij.2.val = k.val then u ij.1 * v ij.2 else 0 := by
  unfold cyclicConv
  refine Finset.sum_congr rfl fun ij _ => ?_
  by_cases heq : ij.1.val + ij.2.val = k.val
  · have hmod : (ij.1.val + ij.2.val) % n = k.val := by rw [heq]; exact Nat.mod_eq_of_lt k.isLt
    rw [if_pos heq, if_pos hmod]
  · by_cases hmodeq : (ij.1.val + ij.2.val) % n = k.val
    · have hlt2n : ij.1.val + ij.2.val < 2 * n := by
        have h1 := ij.1.isLt
        have h2 := ij.2.isLt
        omega
      have hge : n ≤ ij.1.val + ij.2.val := by
        by_contra hlt
        push_neg at hlt
        exact heq ((Nat.mod_eq_of_lt hlt).symm.trans hmodeq)
      obtain ⟨r, hr⟩ : ∃ r, ij.1.val + ij.2.val = n + r := ⟨ij.1.val + ij.2.val - n, by omega⟩
      have hrlt : r < n := by omega
      have hrk : r = k.val := by
        have h := hmodeq
        rwa [hr, Nat.add_mod_left, Nat.mod_eq_of_lt hrlt] at h
      have hwrap : ij.1.val + ij.2.val = k.val + n := by omega
      have hnot : ¬ (ij.1.val < m ∧ ij.2.val < m') := by omega
      simp only [not_and_or, not_lt] at hnot
      rw [if_neg heq, if_pos hmodeq]
      rcases hnot with h1 | h2
      · simp [hu ij.1 h1]
      · simp [hv ij.2 h2]
    · rw [if_neg heq, if_neg hmodeq]

end CommRing

section Field

variable {F : Type*} [Field F] {n : ℕ}

/-- The inverse transform, `n⁻¹` times the transform with `ω⁻¹`. -/
def idft (ω : F) (b : Fin n → F) (k : Fin n) : F :=
  (n : F)⁻¹ * dft ω⁻¹ b k

/-- A finite geometric sum with ratio `ζ` vanishes when `ζ ^ n = 1` and `ζ ≠ 1`. -/
theorem sum_pow_range_eq_zero_of_ne_one {ζ : F} {n : ℕ} (h1 : ζ ^ n = 1) (h2 : ζ ≠ 1) :
    ∑ j ∈ Finset.range n, ζ ^ j = 0 := by
  have hmul : (∑ j ∈ Finset.range n, ζ ^ j) * (ζ - 1) = 0 := by rw [geom_sum_mul, h1, sub_self]
  rcases mul_eq_zero.mp hmul with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) h2

/-- Orthogonality of the powers of a primitive `n`-th root: the sum over `Fin n`
of `ω ^ (i * j) * ω⁻¹ ^ (j * l)` is `n` when `i = l` and `0` otherwise. -/
theorem sum_pow_mul_inv_pow_eq {ω : F} (hω : IsPrimitiveRoot ω n) (i l : Fin n) :
    ∑ j : Fin n, ω ^ ((i : ℕ) * j) * ω⁻¹ ^ ((j : ℕ) * l) = if i = l then (n : F) else 0 := by
  have hn : n ≠ 0 := fun h => by subst h; exact i.elim0
  have hω0 : ω ≠ 0 := by
    rintro rfl
    have h1 := hω.pow_eq_one
    rw [zero_pow hn] at h1
    exact zero_ne_one h1
  have hωinv : ω⁻¹ ^ n = 1 := by rw [inv_pow, hω.pow_eq_one, inv_one]
  have hterm : ∀ j : Fin n, ω ^ ((i : ℕ) * j) * ω⁻¹ ^ ((j : ℕ) * l) =
      (ω ^ (i : ℕ) * (ω ^ (l : ℕ))⁻¹) ^ (j : ℕ) := by
    intro j
    rw [mul_pow, ← inv_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (l : ℕ) (j : ℕ)]
  simp only [hterm]
  rw [Fin.sum_univ_eq_sum_range fun j => (ω ^ (i : ℕ) * (ω ^ (l : ℕ))⁻¹) ^ j]
  by_cases hil : i = l
  · subst hil
    have h1 : ω ^ (i : ℕ) * (ω ^ (i : ℕ))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hω0)
    simp [h1]
  · have hζn : (ω ^ (i : ℕ) * (ω ^ (l : ℕ))⁻¹) ^ n = 1 := by
      rw [mul_pow, ← inv_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (i : ℕ) n, Nat.mul_comm (l : ℕ) n,
        pow_mul, pow_mul, hω.pow_eq_one, hωinv, one_pow, one_pow, mul_one]
    have hζne : ω ^ (i : ℕ) * (ω ^ (l : ℕ))⁻¹ ≠ 1 := by
      intro hζ
      rw [← div_eq_mul_inv, div_eq_one_iff_eq (pow_ne_zero (l : ℕ) hω0)] at hζ
      exact hil (Fin.ext (hω.pow_inj i.isLt l.isLt hζ))
    simp [hil, sum_pow_range_eq_zero_of_ne_one hζn hζne]

/-- The inverse transform undoes the transform for a primitive `n`-th root
when `n` is invertible. -/
theorem idft_dft {ω : F} (hω : IsPrimitiveRoot ω n) (hn : (n : F) ≠ 0) (a : Fin n → F) :
    idft ω (dft ω a) = a := by
  funext l
  have step : ∀ i : Fin n, ∑ j : Fin n, a i * ω ^ ((i : ℕ) * j) * ω⁻¹ ^ ((j : ℕ) * l) =
      a i * ∑ j : Fin n, ω ^ ((i : ℕ) * j) * ω⁻¹ ^ ((j : ℕ) * l) := by
    intro i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  show (n : F)⁻¹ * dft ω⁻¹ (dft ω a) l = a l
  simp only [dft, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [step, sum_pow_mul_inv_pow_eq hω, mul_ite, mul_zero, Fintype.sum_ite_eq']
  rw [mul_comm (a l) (n : F), ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

/-- The convolution identity in the form the transform-based evaluators use. -/
theorem idft_dft_mul {ω : F} (hω : IsPrimitiveRoot ω n) (hn : (n : F) ≠ 0)
    (u v : Fin n → F) :
    idft ω (dft ω u * dft ω v) = cyclicConv u v := by
  rw [← dft_cyclicConv hω.pow_eq_one, idft_dft hω hn]

/-- The negacyclic product is the untwisted cyclic product of the twisted
inputs, for `ψ` with `ψ ^ n = -1`. -/
theorem negacyclicConvCoeff_eq_untwist {ψ : F} (hψ : ψ ^ n = -1) (u v : Fin n → F) :
    LatticeCrypto.negacyclicConvCoeff u v =
      fun k : Fin n => ψ⁻¹ ^ (k : ℕ) * cyclicConv (twist ψ u) (twist ψ v) k := by
  funext k
  have hn : n ≠ 0 := fun h => by subst h; exact k.elim0
  have hψ0 : ψ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hψ
    exact absurd hψ.symm (neg_ne_zero.mpr one_ne_zero)
  have hcancel : ψ⁻¹ ^ (k : ℕ) * ψ ^ (k : ℕ) = 1 := by
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hψ0)]
  have htwist : ∀ ij : Fin n × Fin n,
      twist ψ u ij.1 * twist ψ v ij.2 = ψ ^ ((ij.1 : ℕ) + (ij.2 : ℕ)) * (u ij.1 * v ij.2) := by
    intro ij
    unfold twist
    rw [pow_add]
    ring
  unfold LatticeCrypto.negacyclicConvCoeff cyclicConv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ij _ => ?_
  by_cases hcond : (ij.1.val + ij.2.val) % n = k.val
  · rw [if_pos hcond, if_pos hcond, htwist ij]
    by_cases hlt : ij.1.val + ij.2.val < n
    · have heq : ij.1.val + ij.2.val = k.val := (Nat.mod_eq_of_lt hlt).symm.trans hcond
      rw [if_pos hlt, heq, ← mul_assoc, hcancel, one_mul]
    · have hnlt : n ≤ ij.1.val + ij.2.val := by omega
      have hlt2n : ij.1.val + ij.2.val < 2 * n := by
        have h1 := ij.1.isLt
        have h2 := ij.2.isLt
        omega
      obtain ⟨r, hr⟩ : ∃ r, ij.1.val + ij.2.val = n + r := ⟨ij.1.val + ij.2.val - n, by omega⟩
      have hrlt : r < n := by omega
      have hrk : r = k.val := by rwa [hr, Nat.add_mod_left, Nat.mod_eq_of_lt hrlt] at hcond
      have hwrap : ij.1.val + ij.2.val = k.val + n := by omega
      rw [if_neg hlt, hwrap, pow_add, hψ,
        show ψ ^ (k : ℕ) * -1 * (u ij.1 * v ij.2) = -(u ij.1 * v ij.2 * ψ ^ (k : ℕ)) from by ring,
        show ψ⁻¹ ^ (k : ℕ) * -(u ij.1 * v ij.2 * ψ ^ (k : ℕ)) =
          -((ψ⁻¹ ^ (k : ℕ) * ψ ^ (k : ℕ)) * (u ij.1 * v ij.2)) from by ring,
        hcancel, one_mul]
  · rw [if_neg hcond, if_neg hcond, mul_zero]

end Field

end GordieHowe.DFT
