-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.MeanInequalities

@[expose] public section

/-!
# Complex matrices: traces, sums and positive semidefiniteness

Facts about Mathlib's matrices used by the mixed-state formalism (`GordieHowe/Model/Quantum/Core/Channel.lean`):

- `exists_eq_conjTranspose_mul_self`: a positive semidefinite matrix is `Bᴴ B`;
- `PosSemidef.re_trace_mul_nonneg`: `0 ≤ re (tr (A B))` for positive semidefinite `A`, `B`;
- `re_trace_eq_sum`, `trace_submatrix_equiv`: the trace as a sum of diagonal entries, and its
  invariance under conjugation by a permutation of the basis;
- `sum_kronecker`, `submatrix_sum`: Kronecker products and submatrices commute with finite sums.

A determinant bound of Hadamard type over `ℝ`:

- `Real.prod_le_mean_pow`: `∏ z ≤ (Σ z / n)^n` for nonnegative `z` (AM–GM);
- `det_sq_le_trace_div_pow`: `det M ^ 2 ≤ (tr (Mᵀ M) / n)^n`, by AM–GM on the eigenvalues of
  the positive semidefinite `Mᵀ M`;
- `det_sq_le_of_abs_le`: `det M ^ 2 ≤ (n B²)^n` when every entry is at most `B` in absolute
  value. This is Hadamard's inequality `|det M| ≤ ∏_j ‖M_j‖` evaluated at columns of norm at most
  `√n B`; the column-by-column form is not proved here.

Integer matrices and a prime `p`:

- `pow_card_dvd_det_of_dvd_rows`: if every entry of the rows in `J` is divisible by `c`, then
  `c ^ |J|` divides the determinant;
- `pow_dvd_det_of_rank_le`: if the reduction modulo `p` has rank at most `r`, then
  `p ^ (n - r)` divides the determinant (Gaussian elimination over `ZMod p`, lifted to `ℤ` by
  transvections of determinant one).

The statements are about Mathlib objects only and are candidates for upstreaming.
-/

open Finset
open scoped BigOperators ComplexOrder Kronecker MatrixOrder

namespace Matrix

variable {ι : Type*} [Fintype ι]

/-- A positive semidefinite matrix is `Bᴴ B` for some `B` (its square root). -/
theorem exists_eq_conjTranspose_mul_self [DecidableEq ι] {M : Matrix ι ι ℂ} (hM : M.PosSemidef) :
    ∃ B : Matrix ι ι ℂ, M = Bᴴ * B := by
  refine ⟨CFC.sqrt M, ?_⟩
  have hsa : (CFC.sqrt M)ᴴ = CFC.sqrt M := (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq
  rw [hsa, CFC.sqrt_mul_sqrt_self M hM.nonneg]

/-- The real part of the trace is the sum of the real parts of the diagonal. -/
theorem re_trace_eq_sum (ρ : Matrix ι ι ℂ) : ρ.trace.re = ∑ i, (ρ i i).re := by
  rw [Matrix.trace, Complex.re_sum]
  rfl

/-- Conjugating by a permutation of the basis preserves the trace. -/
theorem trace_submatrix_equiv {R : Type*} [AddCommMonoid R] (ρ : Matrix ι ι R) (e : ι ≃ ι) :
    (ρ.submatrix e e).trace = ρ.trace :=
  Equiv.sum_comp e fun i => ρ i i

/-- A positive semidefinite matrix has a trace with nonnegative real part. -/
theorem PosSemidef.re_trace_nonneg {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) : 0 ≤ ρ.trace.re :=
  (Complex.nonneg_iff.1 hρ.trace_nonneg).1

/-- The trace of a product of two positive semidefinite matrices has nonnegative real part. -/
theorem PosSemidef.re_trace_mul_nonneg [DecidableEq ι] {A B : Matrix ι ι ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  obtain ⟨C, rfl⟩ := exists_eq_conjTranspose_mul_self hA
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc]
  exact (hB.mul_mul_conjTranspose_same C).re_trace_nonneg

/-- The Kronecker product with a fixed right factor commutes with finite sums. -/
theorem sum_kronecker {α R l m n p : Type*} [CommSemiring R] (s : Finset α)
    (A : α → Matrix l m R) (B : Matrix n p R) :
    (∑ a ∈ s, A a) ⊗ₖ B = ∑ a ∈ s, A a ⊗ₖ B :=
  map_sum ({ toFun := fun M => M ⊗ₖ B
             map_zero' := zero_kronecker B
             map_add' := fun M N => add_kronecker M N B } : Matrix l m R →+ Matrix (l × n) (m × p) R)
    A s

/-- Taking a submatrix commutes with finite sums. -/
theorem submatrix_sum {α R l m n o : Type*} [AddCommMonoid R] (s : Finset α)
    (A : α → Matrix m n R) (e : l → m) (f : o → n) :
    (∑ a ∈ s, A a).submatrix e f = ∑ a ∈ s, (A a).submatrix e f :=
  map_sum ({ toFun := fun M => M.submatrix e f
             map_zero' := by simp
             map_add' := fun M N => rfl } : Matrix m n R →+ Matrix l o R) A s

/-! ### Determinants divisible by a prime power -/

section PrimePower

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If every entry of the rows in `J` is divisible by `c`, then `c ^ |J|` divides the
determinant. -/
theorem pow_card_dvd_det_of_dvd_rows {R : Type*} [CommRing R] (A : Matrix n n R) (J : Finset n)
    {c : R} (h : ∀ i ∈ J, ∀ j, c ∣ A i j) : c ^ J.card ∣ A.det := by
  have h' : ∀ i ∈ J, ∀ j, ∃ b, A i j = c * b := fun i hi j => h i hi j
  choose! B hB using h'
  let B' : Matrix n n R := of fun i j => if i ∈ J then B i j else A i j
  have hA : A = of fun i j => (if i ∈ J then c else 1) * B' i j := by
    ext i j
    by_cases hi : i ∈ J
    · simp only [of_apply, B', hi, ite_true]
      exact hB i hi j
    · simp only [of_apply, B', hi, ite_false, one_mul]
  rw [hA, det_mul_column, (Fintype.prod_ite_mem J fun _ => c).trans (Finset.prod_const c)]
  exact dvd_mul_right _ _

/-- **A matrix of rank at most `r` modulo a prime `p` has determinant divisible by
`p ^ (n - r)`.** Gaussian elimination over `ZMod p`
(`Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal`) lifts to `ℤ` through
transvections, which have determinant one; the lifted product is diagonal modulo `p` with at most
`r` nonzero diagonal entries, so at least `n - r` of its rows vanish modulo `p`. -/
theorem pow_dvd_det_of_rank_le {p : ℕ} [Fact p.Prime] (M : Matrix n n ℤ) {r : ℕ}
    (h : (M.map (Int.castRingHom (ZMod p))).rank ≤ r) :
    (p : ℤ) ^ (Fintype.card n - r) ∣ M.det := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set f := Int.castRingHom (ZMod p) with hf
  obtain ⟨L, L', D, hD⟩ :=
    Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal (M.map f)
  let lift : TransvectionStruct n (ZMod p) → TransvectionStruct n ℤ :=
    fun t => ⟨t.i, t.j, t.hij, ((t.c.val : ℕ) : ℤ)⟩
  have hlift : ∀ t, f.mapMatrix (lift t).toMatrix = t.toMatrix := by
    intro t
    have hc : f ((t.c.val : ℕ) : ℤ) = t.c := by
      simp only [hf, Int.coe_castRingHom, Int.cast_natCast, ZMod.natCast_zmod_val]
    change f.mapMatrix (1 + single t.i t.j ((t.c.val : ℕ) : ℤ)) = 1 + single t.i t.j t.c
    rw [map_add, map_one, RingHom.mapMatrix_apply, Matrix.map_single, hc]
  have hprod : ∀ L : List (TransvectionStruct n (ZMod p)),
      f.mapMatrix ((L.map lift).map TransvectionStruct.toMatrix).prod =
        (L.map TransvectionStruct.toMatrix).prod := by
    intro L
    induction L with
    | nil => simp
    | cons t L ih => simp only [List.map_cons, List.prod_cons, map_mul, hlift, ih]
  set A := ((L.map lift).map TransvectionStruct.toMatrix).prod * M *
    ((L'.map lift).map TransvectionStruct.toMatrix).prod with hAdef
  have hAdet : A.det = M.det := by
    rw [hAdef, det_mul, det_mul, TransvectionStruct.det_toMatrix_prod,
      TransvectionStruct.det_toMatrix_prod, one_mul, mul_one]
  have hAmap : f.mapMatrix A = diagonal D := by
    rw [hAdef, map_mul, map_mul, hprod, hprod]
    exact hD
  have hrank : (diagonal D).rank = (M.map f).rank := by
    rw [← hD, rank_mul_eq_left_of_isUnit_det _ _ (by simp),
      rank_mul_eq_right_of_isUnit_det _ _ (by simp)]
  have hcard : Fintype.card {i // D i ≠ 0} ≤ r := by
    rw [← rank_diagonal, hrank]
    exact h
  set J : Finset n := Finset.univ.filter fun i => D i = 0
  have hJ : Fintype.card n - r ≤ J.card := by
    have hsplit : J.card + (Finset.univ.filter fun i => D i ≠ 0).card = Fintype.card n := by
      rw [← Finset.card_univ]
      exact Finset.card_filter_add_card_filter_not _
    rw [Fintype.card_subtype] at hcard
    omega
  have hrows : ∀ i ∈ J, ∀ j, (p : ℤ) ∣ A i j := by
    intro i hi j
    have hij := congrFun (congrFun hAmap i) j
    rw [RingHom.mapMatrix_apply, map_apply, hf, Int.coe_castRingHom, diagonal_apply,
      (Finset.mem_filter.1 hi).2, ite_self] at hij
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hij
  rw [← hAdet]
  exact (pow_dvd_pow _ hJ).trans (pow_card_dvd_det_of_dvd_rows A J hrows)

end PrimePower

end Matrix

namespace Real

/-- **AM–GM**: `∏ z ≤ (Σ z / n)^n` for nonnegative `z` on a finite type of size `n`. -/
theorem prod_le_mean_pow {ι : Type*} [Fintype ι] {z : ι → ℝ} (hz : ∀ i, 0 ≤ z i) :
    ∏ i, z i ≤ ((∑ i, z i) / Fintype.card ι) ^ Fintype.card ι := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h := geom_mean_le_arith_mean_weighted (s := Finset.univ)
    (fun _ => ((Fintype.card ι : ℕ) : ℝ)⁻¹) z (fun _ _ => inv_nonneg.2 hn.le)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hn.ne'])
    (fun i _ => hz i)
  rw [← Finset.mul_sum, inv_mul_eq_div] at h
  calc ∏ i, z i = (∏ i, z i ^ ((Fintype.card ι : ℕ) : ℝ)⁻¹) ^ Fintype.card ι := by
        rw [← Finset.prod_pow]
        exact Finset.prod_congr rfl fun i _ =>
          (rpow_inv_natCast_pow (hz i) Fintype.card_ne_zero).symm
    _ ≤ _ := pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => rpow_nonneg (hz i) _) h _

end Real

namespace Matrix

/-! ### A Hadamard-type bound -/

section Hadamard

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The determinant squared is at most `(tr (Mᵀ M) / n)^n` (AM–GM on the eigenvalues of
`Mᵀ M`). -/
theorem det_sq_le_trace_div_pow (M : Matrix n n ℝ) :
    M.det ^ 2 ≤ ((Mᵀ * M).trace / Fintype.card n) ^ Fintype.card n := by
  have hA := posSemidef_conjTranspose_mul_self M
  have hdet : (Mᴴ * M).det = M.det ^ 2 := by
    rw [det_mul, det_conjTranspose, sq, star_trivial]
  have hMT : Mᴴ = Mᵀ := conjTranspose_eq_transpose_of_trivial M
  rw [← hdet, hA.isHermitian.det_eq_prod_eigenvalues, ← hMT,
    hA.isHermitian.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  exact Real.prod_le_mean_pow fun i => hA.eigenvalues_nonneg i

/-- **Hadamard-type bound**: `det M ^ 2 ≤ (n B²)^n` when every entry of `M` is at most `B` in
absolute value. -/
theorem det_sq_le_of_abs_le (M : Matrix n n ℝ) {B : ℝ} (hB : ∀ i j, |M i j| ≤ B) :
    M.det ^ 2 ≤ (Fintype.card n * B ^ 2) ^ Fintype.card n := by
  refine (det_sq_le_trace_div_pow M).trans (pow_le_pow_left₀ ?_ ?_ _)
  · have : 0 ≤ (Mᵀ * M).trace := by
      simp only [trace, diag, mul_apply, transpose_apply]
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _
    positivity
  · have htr : (Mᵀ * M).trace ≤ Fintype.card n * (Fintype.card n * B ^ 2) := by
      simp only [trace, diag, mul_apply, transpose_apply]
      calc ∑ i, ∑ j, M j i * M j i ≤ ∑ _i : n, ∑ _j : n, B ^ 2 := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            rw [← sq, ← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hB j i) 2
        _ = _ := by simp
    rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | hpos
    · rw [h0]
      simp
    · have hn : (0 : ℝ) < Fintype.card n := by exact_mod_cast hpos
      rw [div_le_iff₀ hn]
      linarith

end Hadamard

end Matrix
