-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.Matrix
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

@[expose] public section

/-!
# The determinant bound for words of small spectral support

Lemma 2 of "A shorter proof of the stated HighBits regularity claim" (10 September 2026,
Section 4): a nonzero integer word `v` of length `a = 2^e` whose reduction modulo a prime `q` is a
combination of at most `r` root words `(ρ^b)_b` with `ρ^a = -1` satisfies
`q^(a - r) ≤ a! · ‖v‖∞^a` (`pow_le_factorial_mul_pow_of_mem_span`). The note's form
`‖v‖∞ ≥ q^(1 - r/a) / a` follows from `a! ≤ a^a`. The Hadamard form
`q^(2(a - r)) ≤ a^a · ‖v‖∞^(2a)`, the note's `‖v‖∞ ≥ q^(1 - r/a) / √a`, is
`pow_two_mul_le_pow_mul_pow_of_mem_span` (from `Matrix.det_sq_le_of_abs_le`).

The proof goes through the matrix `negacyclicMatrix v` of multiplication by `v` modulo
`X^a + 1`, whose column `j` is the `j`-fold negacyclic shift of `v`:

- `det_negacyclicMatrix_ne_zero`: its determinant is nonzero, since `X^(2^e) + 1` is the
  cyclotomic polynomial of order `2^(e+1)`, irreducible over `ℚ`
  (`irreducible_X_pow_two_pow_add_one`), so multiplication by `v ≠ 0` in the field
  `ℚ[X]/(X^a + 1)` is injective;
- `rank_negacyclicMatrix_le`: over a field, if `v` lies in the span of the root words of `T`,
  every column does (each root word is an eigenvector of the shift), so the rank is at most `|T|`;
  with `Matrix.pow_dvd_det_of_rank_le` this gives `q^(a - r) ∣ det`;
- `abs_det_negacyclicMatrix_le`: the Leibniz bound `|det| ≤ a! · B^a` for entries bounded
  by `B` (`Matrix.det_le`).
-/

open Polynomial
open scoped Matrix

namespace GordieHowe.MLDSA.Regularity

variable {R : Type*} [CommRing R] {a : ℕ}

/-! ### The negacyclic shift and the multiplication matrix -/

/-- **The negacyclic shift**: the coefficients of `X · w` modulo `X^a + 1`, that is
`(-w_(a-1), w_0, …, w_(a-2))`. -/
def negacyclicShift (w : Fin a → R) (i : Fin a) : R :=
  if h : (i : ℕ) = 0 then -w ⟨a - 1, by have := i.isLt; omega⟩
  else w ⟨i - 1, by have := i.isLt; omega⟩

/-- The negacyclic shift is linear. -/
def negacyclicShiftₗ : (Fin a → R) →ₗ[R] (Fin a → R) where
  toFun := negacyclicShift
  map_add' w w' := by
    funext i
    simp only [negacyclicShift, Pi.add_apply]
    split_ifs <;> ring
  map_smul' c w := by
    funext i
    simp only [negacyclicShift, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- **The negacyclic multiplication matrix** of `v`: column `j` holds the coefficients of
`X^j · v` modulo `X^a + 1`, so `negacyclicMatrix v *ᵥ u` is the coefficient vector of `v · u`
in `R[X]/(X^a + 1)` (`toQuotient_mulVec`). -/
def negacyclicMatrix (v : Fin a → R) : Matrix (Fin a) (Fin a) R :=
  Matrix.of fun i j => (negacyclicShift^[(j : ℕ)] v) i

/-- The shift commutes with a ring homomorphism applied coefficientwise. -/
theorem negacyclicShift_map {S : Type*} [CommRing S] (f : R →+* S) (w : Fin a → R) :
    negacyclicShift (fun b => f (w b)) = fun b => f (negacyclicShift w b) := by
  funext i
  simp only [negacyclicShift]
  split_ifs <;> simp

/-- The iterated shift commutes with a ring homomorphism applied coefficientwise. -/
theorem negacyclicShift_iterate_map {S : Type*} [CommRing S] (f : R →+* S) (w : Fin a → R)
    (j : ℕ) :
    negacyclicShift^[j] (fun b => f (w b)) = fun b => f (negacyclicShift^[j] w b) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, negacyclicShift_map]

/-- The multiplication matrix commutes with a ring homomorphism applied coefficientwise. -/
theorem negacyclicMatrix_map {S : Type*} [CommRing S] (f : R →+* S) (v : Fin a → R) :
    negacyclicMatrix (fun b => f (v b)) = (negacyclicMatrix v).map f := by
  ext i j
  simp only [negacyclicMatrix, Matrix.of_apply, Matrix.map_apply, negacyclicShift_iterate_map]

/-! ### The entry bound and the Leibniz bound -/

/-- The shift preserves a coefficient bound. -/
theorem abs_negacyclicShift_le {w : Fin a → ℤ} {B : ℤ} (hw : ∀ b, |w b| ≤ B) (i : Fin a) :
    |negacyclicShift w i| ≤ B := by
  simp only [negacyclicShift]
  split_ifs
  · rw [abs_neg]
    exact hw _
  · exact hw _

/-- Every entry of the multiplication matrix is bounded by a coefficient bound of `v`. -/
theorem abs_negacyclicMatrix_le {v : Fin a → ℤ} {B : ℤ} (hv : ∀ b, |v b| ≤ B) (i j : Fin a) :
    |negacyclicMatrix v i j| ≤ B := by
  have h : ∀ k : ℕ, ∀ i, |(negacyclicShift^[k] v) i| ≤ B := by
    intro k
    induction k with
    | zero => exact hv
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact abs_negacyclicShift_le ih
  exact h j i

/-- **The Leibniz bound**: `|det| ≤ a! · B^a` for coefficients of `v` bounded by `B`. -/
theorem abs_det_negacyclicMatrix_le {v : Fin a → ℤ} {B : ℤ} (hv : ∀ b, |v b| ≤ B) :
    |(negacyclicMatrix v).det| ≤ a.factorial * B ^ a := by
  have h := Matrix.det_le (abv := AbsoluteValue.abs) (abs_negacyclicMatrix_le hv)
  simpa [nsmul_eq_mul] using h

/-! ### The rank modulo a prime -/

/-- A root word `(ρ^b)_b` with `ρ^a = -1` is an eigenvector of the shift, with eigenvalue
`ρ⁻¹`. -/
theorem negacyclicShift_powers {K : Type*} [Field K] {ρ : K} (hρ : ρ ^ a = -1) :
    negacyclicShift (fun b : Fin a => ρ ^ (b : ℕ)) = ρ⁻¹ • fun b : Fin a => ρ ^ (b : ℕ) := by
  funext i
  have ha : 0 < a := i.pos
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow ha.ne'] at hρ
    exact one_ne_zero (neg_eq_zero.1 hρ.symm)
  simp only [negacyclicShift, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · have hpow : ρ ^ (a - 1) * ρ = -1 := by
      rw [← pow_succ, Nat.sub_add_cancel ha]
      exact hρ
    rw [h, pow_zero, mul_one]
    exact eq_inv_of_mul_eq_one_left (by rw [neg_mul, hpow, neg_neg])
  · have hpow : ρ ^ (i : ℕ) = ρ ^ ((i : ℕ) - 1) * ρ := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero h)]
    rw [hpow, mul_comm (ρ ^ _) ρ, ← mul_assoc, inv_mul_cancel₀ hρ0, one_mul]

/-- **The rank bound.** Over a field, if `v` is a combination of the root words `(ρ^b)_b` for
`ρ ∈ T`, each with `ρ^a = -1`, then the multiplication matrix has rank at most `|T|`: every
column, an iterated shift of `v`, stays in the span of the root words. -/
theorem rank_negacyclicMatrix_le {K : Type*} [Field K] {v : Fin a → K} (T : Finset K)
    (hT : ∀ ρ ∈ T, ρ ^ a = -1)
    (hv : v ∈ Submodule.span K ((fun ρ : K => fun b : Fin a => ρ ^ (b : ℕ)) '' T)) :
    (negacyclicMatrix v).rank ≤ T.card := by
  classical
  set g : K → Fin a → K := fun ρ b => ρ ^ (b : ℕ) with hg
  set W := Submodule.span K (g '' T) with hWdef
  have hW : W ≤ W.comap negacyclicShiftₗ := by
    rw [hWdef, Submodule.span_le]
    rintro _ ⟨ρ, hρ, rfl⟩
    change negacyclicShift (g ρ) ∈ W
    rw [hg, negacyclicShift_powers (hT ρ hρ)]
    exact W.smul_mem _ (Submodule.subset_span ⟨ρ, hρ, rfl⟩)
  have hcol : ∀ j : ℕ, negacyclicShift^[j] v ∈ W := by
    intro j
    induction j with
    | zero => exact hv
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact hW ih
  rw [Matrix.rank_eq_finrank_span_cols]
  calc Module.finrank K (Submodule.span K (Set.range (negacyclicMatrix v)ᵀ))
      ≤ Module.finrank K W :=
        Submodule.finrank_mono (Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hcol j))
    _ ≤ (T.image g).card := by
        rw [hWdef, ← Finset.coe_image]
        exact finrank_span_finset_le_card _
    _ ≤ T.card := Finset.card_image_le

/-! ### Nonsingularity -/

/-- `X^(2^e) + 1` is irreducible over `ℚ`: it is the cyclotomic polynomial of order
`2^(e+1)`. -/
theorem irreducible_X_pow_two_pow_add_one (e : ℕ) : Irreducible ((X : ℚ[X]) ^ 2 ^ e + 1) := by
  have h := cyclotomic_prime_pow_eq_geom_sum (R := ℚ) Nat.prime_two (n := e)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at h
  rw [add_comm, ← h]
  exact cyclotomic.irreducible_rat (by positivity)

/-- The element `Σ_b w_b X^b` of `R[X]/(X^a + 1)`. -/
noncomputable def toQuotient (w : Fin a → R) : AdjoinRoot ((X : R[X]) ^ a + 1) :=
  AdjoinRoot.mk _ (∑ b : Fin a, C (w b) * X ^ (b : ℕ))

/-- `toQuotient` as a sum of powers of the root. -/
theorem toQuotient_eq_sum (w : Fin a → R) :
    toQuotient w = ∑ b : Fin a, AdjoinRoot.of _ (w b) * AdjoinRoot.root _ ^ (b : ℕ) := by
  simp only [toQuotient, map_sum, map_mul, map_pow]
  rfl

/-- The root of `X^a + 1` satisfies `root ^ a = -1`. -/
theorem root_pow_eq_neg_one : AdjoinRoot.root ((X : R[X]) ^ a + 1) ^ a = -1 := by
  have h := AdjoinRoot.mk_self (f := (X : R[X]) ^ a + 1)
  rw [map_add, map_pow, AdjoinRoot.mk_X, map_one] at h
  exact eq_neg_of_add_eq_zero_left h

/-- The shift is multiplication by the root. -/
theorem toQuotient_negacyclicShift (w : Fin a → R) :
    toQuotient (negacyclicShift w) = AdjoinRoot.root _ * toQuotient w := by
  cases a with
  | zero => simp [toQuotient]
  | succ n =>
    have h0 : negacyclicShift w 0 = -w (Fin.last n) := by
      simp only [negacyclicShift, Fin.val_zero]
      exact congrArg (fun x => -w x) (Fin.ext (by simp))
    have hs : ∀ i : Fin n, negacyclicShift w i.succ = w i.castSucc := by
      intro i
      simp only [negacyclicShift, Fin.val_succ, Nat.add_one_ne_zero, dite_false]
      exact congrArg w (Fin.ext (by simp))
    have hsum : ∀ i : Fin n,
        AdjoinRoot.root ((X : R[X]) ^ (n + 1) + 1) *
            (AdjoinRoot.of _ (w i.castSucc) * AdjoinRoot.root _ ^ (i.castSucc : ℕ)) =
          AdjoinRoot.of _ (w i.castSucc) * AdjoinRoot.root _ ^ (i.succ : ℕ) := by
      intro i
      simp only [Fin.val_succ, Fin.val_castSucc]
      ring
    rw [toQuotient_eq_sum, toQuotient_eq_sum, Finset.mul_sum, Fin.sum_univ_succ,
      Fin.sum_univ_castSucc, h0]
    simp only [hs, hsum, Fin.val_zero, pow_zero, mul_one, map_neg, Fin.val_last]
    linear_combination (-(AdjoinRoot.of ((X : R[X]) ^ (n + 1) + 1) (w (Fin.last n)))) *
      (root_pow_eq_neg_one (R := R) (a := n + 1))

/-- **Multiplication.** `negacyclicMatrix v *ᵥ u` represents the product `u · v` in
`R[X]/(X^a + 1)`. -/
theorem toQuotient_mulVec (v u : Fin a → R) :
    toQuotient (negacyclicMatrix v *ᵥ u) = toQuotient u * toQuotient v := by
  have hit : ∀ j : ℕ, toQuotient (negacyclicShift^[j] v) =
      AdjoinRoot.root _ ^ j * toQuotient v := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', toQuotient_negacyclicShift, ih]
      ring
  calc toQuotient (negacyclicMatrix v *ᵥ u)
      = ∑ j : Fin a, AdjoinRoot.of _ (u j) * toQuotient (negacyclicShift^[(j : ℕ)] v) := by
        simp only [toQuotient_eq_sum, Matrix.mulVec, dotProduct, negacyclicMatrix,
          Matrix.of_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ j : Fin a, AdjoinRoot.of _ (u j) * (AdjoinRoot.root _ ^ (j : ℕ) * toQuotient v) := by
        simp only [hit]
    _ = toQuotient u * toQuotient v := by
        rw [toQuotient_eq_sum (w := u), Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring

/-- Over a nontrivial ring, `toQuotient` has trivial kernel: a polynomial of degree `< a`
divisible by the monic `X^a + 1` is zero. -/
theorem eq_zero_of_toQuotient_eq_zero [Nontrivial R] (ha : 0 < a) {w : Fin a → R}
    (h : toQuotient w = 0) : w = 0 := by
  rw [toQuotient, AdjoinRoot.mk_eq_zero] at h
  have hmonic : ((X : R[X]) ^ a + 1).Monic := by
    simpa using monic_X_pow_add_C (1 : R) ha.ne'
  have hdeg : ((X : R[X]) ^ a + 1).degree = a := by
    simpa using degree_X_pow_add_C ha (1 : R)
  have hg : ∑ b : Fin a, C (w b) * X ^ (b : ℕ) = 0 := by
    by_contra hne
    exact hmonic.not_dvd_of_degree_lt hne (hdeg ▸ degree_sum_fin_lt w) h
  funext b
  have hb := congrArg (fun g => coeff g b) hg
  simpa [finsetSum_coeff, coeff_C_mul_X_pow, Fin.val_inj] using hb

/-- **The multiplication matrix of a nonzero word of length `2^e` is nonsingular.** -/
theorem det_negacyclicMatrix_ne_zero {e : ℕ} {v : Fin (2 ^ e) → ℤ} (hv : v ≠ 0) :
    (negacyclicMatrix v).det ≠ 0 := by
  have : Fact (Irreducible ((X : ℚ[X]) ^ 2 ^ e + 1)) := ⟨irreducible_X_pow_two_pow_add_one e⟩
  intro h0
  set w : Fin (2 ^ e) → ℚ := fun b => Int.castRingHom ℚ (v b) with hw
  have hdet : (negacyclicMatrix w).det = 0 := by
    have h := (Int.castRingHom ℚ).map_det (negacyclicMatrix v)
    rw [h0, map_zero, RingHom.mapMatrix_apply, ← negacyclicMatrix_map] at h
    exact h.symm
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hprod := toQuotient_mulVec w u
  rw [hu, show toQuotient (0 : Fin (2 ^ e) → ℚ) = 0 by simp [toQuotient]] at hprod
  rcases mul_eq_zero.1 hprod.symm with h | h
  · exact hu0 (eq_zero_of_toQuotient_eq_zero (by positivity) h)
  · refine hv (funext fun b => ?_)
    have hb := congrFun (eq_zero_of_toQuotient_eq_zero (by positivity) h) b
    simpa [hw] using hb

/-! ### Lemma 2 -/

/-- **Lemma 2 of the note (determinant bound), Leibniz form.** Let `q` be prime and `v` a
nonzero integer word of length `2^e` whose reduction modulo `q` is a combination of the root
words `(ρ^b)_b` for `ρ ∈ T`, each `ρ^(2^e) = -1`, with `|T| ≤ r`. If every coefficient of `v`
is at most `B` in absolute value, then `q^(2^e - r) ≤ (2^e)! · B^(2^e)`. -/
theorem pow_le_factorial_mul_pow_of_mem_span {q : ℕ} [Fact q.Prime] {e r : ℕ}
    {v : Fin (2 ^ e) → ℤ} (hv : v ≠ 0) (T : Finset (ZMod q)) (hT : ∀ ρ ∈ T, ρ ^ 2 ^ e = -1)
    (hTr : T.card ≤ r)
    (hspan : (fun b => (v b : ZMod q)) ∈
      Submodule.span (ZMod q) ((fun ρ : ZMod q => fun b : Fin (2 ^ e) => ρ ^ (b : ℕ)) '' T))
    {B : ℤ} (hB : ∀ b, |v b| ≤ B) :
    (q : ℤ) ^ (2 ^ e - r) ≤ (2 ^ e).factorial * B ^ 2 ^ e := by
  have hrank : ((negacyclicMatrix v).map (Int.castRingHom (ZMod q))).rank ≤ r := by
    rw [← negacyclicMatrix_map]
    exact (rank_negacyclicMatrix_le T hT (by simpa using hspan)).trans hTr
  have hdvd := Matrix.pow_dvd_det_of_rank_le (negacyclicMatrix v) hrank
  rw [Fintype.card_fin] at hdvd
  have hne := det_negacyclicMatrix_ne_zero hv
  exact (Int.le_of_dvd (abs_pos.2 hne) ((dvd_abs _ _).2 hdvd)).trans
    (abs_det_negacyclicMatrix_le hB)

/-- **Lemma 2 of the note, Hadamard form.** Under the hypotheses of
`pow_le_factorial_mul_pow_of_mem_span`, `q^(2(2^e - r)) ≤ (2^e)^(2^e) · B^(2 · 2^e)`, the
note's `‖v‖∞ ≥ q^(1 - r/a) / √a`. -/
theorem pow_two_mul_le_pow_mul_pow_of_mem_span {q : ℕ} [Fact q.Prime] {e r : ℕ}
    {v : Fin (2 ^ e) → ℤ} (hv : v ≠ 0) (T : Finset (ZMod q)) (hT : ∀ ρ ∈ T, ρ ^ 2 ^ e = -1)
    (hTr : T.card ≤ r)
    (hspan : (fun b => (v b : ZMod q)) ∈
      Submodule.span (ZMod q) ((fun ρ : ZMod q => fun b : Fin (2 ^ e) => ρ ^ (b : ℕ)) '' T))
    {B : ℤ} (hB : ∀ b, |v b| ≤ B) :
    (q : ℤ) ^ (2 * (2 ^ e - r)) ≤ (2 ^ e : ℤ) ^ 2 ^ e * B ^ (2 * 2 ^ e) := by
  have hrank : ((negacyclicMatrix v).map (Int.castRingHom (ZMod q))).rank ≤ r := by
    rw [← negacyclicMatrix_map]
    exact (rank_negacyclicMatrix_le T hT (by simpa using hspan)).trans hTr
  have hdvd := Matrix.pow_dvd_det_of_rank_le (negacyclicMatrix v) hrank
  rw [Fintype.card_fin] at hdvd
  have hne := det_negacyclicMatrix_ne_zero hv
  have h1 : (q : ℤ) ^ (2 ^ e - r) ≤ |(negacyclicMatrix v).det| :=
    Int.le_of_dvd (abs_pos.2 hne) ((dvd_abs _ _).2 hdvd)
  have h2 : (q : ℤ) ^ (2 * (2 ^ e - r)) ≤ (negacyclicMatrix v).det ^ 2 := by
    rw [mul_comm, pow_mul, ← sq_abs ((negacyclicMatrix v).det)]
    exact pow_le_pow_left₀ (by positivity) h1 2
  have h3 : (((negacyclicMatrix v).det : ℤ) : ℝ) ^ 2 ≤
      ((2 ^ e : ℕ) * (B : ℝ) ^ 2) ^ 2 ^ e := by
    have h := Matrix.det_sq_le_of_abs_le ((negacyclicMatrix v).map (Int.castRingHom ℝ))
      (B := (B : ℝ)) fun i j => by
        simpa using (show ((|negacyclicMatrix v i j| : ℤ) : ℝ) ≤ B by
          exact_mod_cast abs_negacyclicMatrix_le hB i j)
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Fintype.card_fin] at h
    simpa using h
  have h4 : (((negacyclicMatrix v).det : ℤ) : ℝ) ^ 2 ≤
      (((2 ^ e : ℤ) ^ 2 ^ e * B ^ (2 * 2 ^ e) : ℤ) : ℝ) := by
    refine h3.trans_eq ?_
    push_cast
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 (2 ^ e)]
  exact h2.trans (by exact_mod_cast h4)

end GordieHowe.MLDSA.Regularity
