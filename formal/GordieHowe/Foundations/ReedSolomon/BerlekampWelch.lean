-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.GaussianElimination
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.LinearAlgebra.Lagrange

@[expose] public section

/-!
# Executable Berlekamp–Welch decoding of one Reed–Solomon row

Received word `u` at distinct points `D` (`N` of them), degree bound `k`, error bound `e`, with
`2e + k ≤ N`. The decoder `decode` follows Berlekamp–Welch as presented by Gemmell and Sudan
("Highly resilient correctors for polynomials", Inform. Process. Lett. 43 (1992), 169–174),
on values only:

1. solve the linear system `Q(D_j) = u_j · E(D_j)` for a monic error locator `E` of degree `e`
   and `Q` of degree `< e + k` with `GaussianElimination.solve`;
2. evaluate `E` and `Q` at the points and take the first `k` positions with `E(D_j) ≠ 0`; there
   the message polynomial has value `Q(D_j) / E(D_j)`;
3. interpolate those `k` values: the coefficients are a solution of the `k × k` Vandermonde
   system, solved with `GaussianElimination.solve`;
4. count the positions at which the interpolant disagrees with `u`, and return its coefficients
   iff there are at most `e`.

No polynomial division and no Mathlib `Polynomial` operation occurs in the algorithm; the
polynomials `Qpoly`, `Epoly` and `ofCoeffs` are views used only in proofs.

Correctness (`decode_eq_some_iff`): `decode` returns `c` iff the polynomial with coefficients `c` is
within `e` errors of `u`. The mathematics (`exists_solution`, `Qpoly_eq_mul_Epoly`) states the
system through `Matrix.mulVec`. The vendored ArkLib Berlekamp–Welch files prove the same two facts
(`linsolve_always_some_berlekamp_welch`, `Q'_div_E'_eq_p`) but fix `F : Type`, which the
universe-polymorphic `GordieHowe.RSCode` cannot use.
-/

namespace GordieHowe.RSCode.BerlekampWelch

open Polynomial Matrix

variable {F : Type*} [Field F] {N k e : ℕ}

section Math

/-- The value at `z` of the polynomial with coefficients `c` (degree `< k`). -/
def evalCoeffs (c : Fin k → F) (z : F) : F :=
  ∑ i : Fin k, c i * z ^ (i : ℕ)

/-- The polynomial with coefficients `c`, a view of `c` used only in proofs. -/
noncomputable def ofCoeffs (c : Fin k → F) : F[X] :=
  ∑ i : Fin k, C (c i) * X ^ (i : ℕ)

/-- Coefficients of a sum of monomials indexed by `Fin n`. -/
theorem coeff_sum_fin {n : ℕ} (g : Fin n → F) (m : ℕ) :
    (∑ i : Fin n, C (g i) * X ^ (i : ℕ)).coeff m = if h : m < n then g ⟨m, h⟩ else 0 := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨m, h⟩]
    · simp
    · intro b _ hb
      rw [ite_eq_right]
      intro hm
      exact hb (Fin.ext hm.symm)
    · simp
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [ite_eq_right]
    intro hm
    exact h (hm ▸ i.isLt)

theorem coeff_ofCoeffs (c : Fin k → F) (i : Fin k) : (ofCoeffs c).coeff i = c i := by
  rw [ofCoeffs, coeff_sum_fin, dite_eq_left i.isLt]

theorem ofCoeffs_injective : Function.Injective (ofCoeffs (F := F) (k := k)) := by
  intro c c' h
  funext i
  rw [← coeff_ofCoeffs c i, h, coeff_ofCoeffs]

theorem eval_ofCoeffs (c : Fin k → F) (z : F) : (ofCoeffs c).eval z = evalCoeffs c z := by
  simp only [ofCoeffs, evalCoeffs, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]

theorem degree_ofCoeffs_lt (c : Fin k → F) : (ofCoeffs c).degree < k :=
  degree_sum_fin_lt _

theorem natDegree_ofCoeffs_lt (hk : 0 < k) (c : Fin k → F) : (ofCoeffs c).natDegree < k := by
  by_cases h : ofCoeffs c = 0
  · rw [h, natDegree_zero]
    exact hk
  · rw [natDegree_lt_iff_degree_lt h]
    exact degree_ofCoeffs_lt c

/-- A coefficient vector of length `k` gives a polynomial of natural degree at most `k − 1`
(including `k = 0`, where the polynomial is zero). -/
theorem natDegree_ofCoeffs_le (c : Fin k → F) : (ofCoeffs c).natDegree ≤ k - 1 := by
  by_cases h : ofCoeffs c = 0
  · rw [h, natDegree_zero]
    exact Nat.zero_le _
  · have := (natDegree_lt_iff_degree_lt h).mpr (degree_ofCoeffs_lt c)
    omega

/-- A polynomial of degree `< k` is `ofCoeffs` of its first `k` coefficients. -/
theorem ofCoeffs_coeff {f : F[X]} (hf : f.natDegree < k) :
    ofCoeffs (fun i : Fin k => f.coeff i) = f := by
  ext n
  rw [ofCoeffs, coeff_sum_fin]
  split_ifs with h
  · rfl
  · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-- The value of a polynomial of degree `< k` is `evalCoeffs` of its first `k` coefficients. -/
theorem evalCoeffs_coeff {f : F[X]} (hf : f.natDegree < k) (z : F) :
    evalCoeffs (fun i : Fin k => f.coeff i) z = f.eval z := by
  rw [← eval_ofCoeffs, ofCoeffs_coeff hf]

/-- The polynomial `Q` of an assignment of the unknowns: the first `e + k` unknowns are its
coefficients. -/
noncomputable def Qpoly (x : Fin (e + k + e) → F) : F[X] :=
  ∑ i : Fin (e + k), C (x (Fin.castAdd e i)) * X ^ (i : ℕ)

/-- The monic error locator `E` of an assignment of the unknowns: the last `e` unknowns are its
low coefficients. -/
noncomputable def Epoly (x : Fin (e + k + e) → F) : F[X] :=
  X ^ e + ∑ i : Fin e, C (x (Fin.natAdd (e + k) i)) * X ^ (i : ℕ)

/-- The value of `Qpoly x` at `z`, computed from the unknowns. -/
def qValue (x : Fin (e + k + e) → F) (z : F) : F :=
  ∑ i : Fin (e + k), x (Fin.castAdd e i) * z ^ (i : ℕ)

/-- The value of `Epoly x` at `z`, computed from the unknowns. -/
def eValue (x : Fin (e + k + e) → F) (z : F) : F :=
  z ^ e + ∑ i : Fin e, x (Fin.natAdd (e + k) i) * z ^ (i : ℕ)

theorem eval_Qpoly (x : Fin (e + k + e) → F) (z : F) : (Qpoly x).eval z = qValue x z := by
  simp only [Qpoly, qValue, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]

theorem eval_Epoly (x : Fin (e + k + e) → F) (z : F) : (Epoly x).eval z = eValue x z := by
  simp only [Epoly, eValue, eval_add, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]

theorem Epoly_monic (x : Fin (e + k + e) → F) : (Epoly x).Monic :=
  (monic_X_pow e).add_of_left ((degree_sum_fin_lt _).trans_eq (degree_X_pow e).symm)

theorem Epoly_natDegree (x : Fin (e + k + e) → F) : (Epoly x).natDegree = e := by
  rw [Epoly, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  exact (degree_sum_fin_lt _).trans_eq (degree_X_pow e).symm

/-- The coefficient matrix of the Berlekamp–Welch system: row `j` is
`(D_j^i for i < e + k, -(u_j D_j^i) for i < e)`. -/
def sysA (k e : ℕ) (D u : Fin N → F) : Fin N → Fin (e + k + e) → F := fun j =>
  Fin.append (fun i : Fin (e + k) => D j ^ (i : ℕ)) (fun i : Fin e => -(u j * D j ^ (i : ℕ)))

/-- The right-hand side of the Berlekamp–Welch system, `u_j D_j^e`. -/
def sysB (D u : Fin N → F) (e : ℕ) : Fin N → F := fun j => u j * D j ^ e

/-- The equations of the system are `Q(D_j) = u_j E(D_j)`. -/
theorem sys_iff (D u : Fin N → F) (x : Fin (e + k + e) → F) :
    sysA k e D u *ᵥ x = sysB D u e ↔
      ∀ j, (Qpoly x).eval (D j) = u j * (Epoly x).eval (D j) := by
  rw [funext_iff]
  refine forall_congr' fun j => ?_
  have hQ : (Qpoly x).eval (D j) = ∑ i : Fin (e + k), D j ^ (i : ℕ) * x (Fin.castAdd e i) := by
    simp only [Qpoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hE : (Epoly x).eval (D j) =
      D j ^ e + ∑ i : Fin e, D j ^ (i : ℕ) * x (Fin.natAdd (e + k) i) := by
    simp only [Epoly, eval_add, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hS : (sysA k e D u *ᵥ x) j = ∑ i : Fin (e + k), D j ^ (i : ℕ) * x (Fin.castAdd e i)
      - u j * ∑ i : Fin e, D j ^ (i : ℕ) * x (Fin.natAdd (e + k) i) := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Fin.sum_univ_add, Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    simp only [sysA, Fin.append_left, Fin.append_right]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hS, hQ, hE, sysB]
  constructor <;> intro h <;> linear_combination h

variable [DecidableEq F]

/-- The positions at which `u` disagrees with `f`. -/
def errs (D u : Fin N → F) (f : F[X]) : Finset (Fin N) :=
  Finset.univ.filter fun j => u j ≠ f.eval (D j)

@[simp] theorem mem_errs {D u : Fin N → F} {f : F[X]} {j : Fin N} :
    j ∈ errs D u f ↔ u j ≠ f.eval (D j) := by
  simp [errs]

/-- `f` has degree `< k` and disagrees with `u` in at most `e` positions. -/
structure Close (D u : Fin N → F) (k e : ℕ) (f : F[X]) : Prop where
  degree : f.natDegree < k
  errors : (errs D u f).card ≤ e

/-- **A close polynomial gives a solution of the system**: the error locator times
`X^(e - errors)`, and `Q = f E`. -/
theorem exists_solution {D u : Fin N → F} {f : F[X]}
    (hf : Close D u k e f) : ∃ x, sysA k e D u *ᵥ x = sysB D u e := by
  let E0 : F[X] := (∏ j ∈ errs D u f, (X - C (D j))) * X ^ (e - (errs D u f).card)
  have hmon : E0.Monic :=
    (monic_prod_of_monic _ _ fun j _ => monic_X_sub_C (D j)).mul (monic_X_pow _)
  have hdeg : E0.natDegree = e := by
    have h1 := hf.errors
    rw [Monic.natDegree_mul (monic_prod_of_monic _ _ fun j _ => monic_X_sub_C (D j))
      (monic_X_pow _), natDegree_prod_of_monic _ _ fun j _ => monic_X_sub_C (D j)]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one, natDegree_X_pow]
    omega
  let Q0 : F[X] := f * E0
  have hQd : Q0.natDegree < e + k := by
    show (f * E0).natDegree < e + k
    have := natDegree_mul_le (p := f) (q := E0)
    have := hf.degree
    omega
  let x : Fin (e + k + e) → F :=
    Fin.append (fun i : Fin (e + k) => Q0.coeff i) (fun i : Fin e => E0.coeff i)
  have hQx : Qpoly x = Q0 := by
    ext n
    rw [Qpoly, coeff_sum_fin]
    split_ifs with h
    · exact Fin.append_left _ _ ⟨n, h⟩
    · exact (coeff_eq_zero_of_natDegree_lt (by omega)).symm
  have hEx : Epoly x = E0 := by
    ext n
    rw [Epoly, coeff_add, coeff_sum_fin, coeff_X_pow]
    split_ifs with h1 h2 h2
    · omega
    · subst h1
      rw [← hdeg, hmon.coeff_natDegree]
      simp
    · rw [zero_add]
      exact Fin.append_right _ _ ⟨n, h2⟩
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      simp
  refine ⟨x, (sys_iff D u x).mpr fun j => ?_⟩
  rw [hQx, hEx, eval_mul]
  by_cases hj : j ∈ errs D u f
  · have : E0.eval (D j) = 0 := by
      simp only [E0, eval_mul]
      rw [eval_prod, Finset.prod_eq_zero hj (by simp), zero_mul]
    rw [this]
    simp
  · have : u j = f.eval (D j) := by
      by_contra h
      exact hj (mem_errs.mpr h)
    rw [this]

/-- **Every solution is divisible by the close polynomial's error locator**: `Q = f E`. -/
theorem Qpoly_eq_mul_Epoly {D u : Fin N → F} (hD : Function.Injective D) (hr : 2 * e + k ≤ N) {f : F[X]}
    (hf : Close D u k e f) {x : Fin (e + k + e) → F}
    (hx : sysA k e D u *ᵥ x = sysB D u e) : Qpoly x = f * Epoly x := by
  let A := Finset.univ \ errs D u f
  have hA : e + k ≤ A.card := by
    have hs := Finset.le_card_sdiff (errs D u f) (Finset.univ : Finset (Fin N))
    have := hf.errors
    simp only [Finset.card_univ, Fintype.card_fin] at hs
    dsimp [A]
    omega
  let S := A.image D
  have hS : S.card = A.card := Finset.card_image_of_injective _ hD
  apply eq_of_degree_sub_lt_of_eval_finset_eq S
  · have h1 : (Qpoly x).degree < (S.card : WithBot ℕ) :=
      (degree_sum_fin_lt _).trans_le (by exact_mod_cast (hS ▸ hA))
    have h2 : (f * Epoly x).degree < (S.card : WithBot ℕ) := by
      refine degree_le_natDegree.trans_lt ?_
      have := natDegree_mul_le (p := f) (q := Epoly x)
      have := hf.degree
      rw [Epoly_natDegree] at *
      exact_mod_cast (show (f * Epoly x).natDegree < S.card by omega)
    exact (degree_sub_le _ _).trans_lt (max_lt h1 h2)
  · intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    have hjB := (Finset.mem_sdiff.mp hj).2
    have hfj : u j = f.eval (D j) := by
      by_contra h
      exact hjB (mem_errs.mpr h)
    rw [(sys_iff D u x).mp hx j, eval_mul, hfj]

/-- A nonzero polynomial vanishes at no more of `N` distinct points than its degree. -/
theorem card_filter_eval_eq_zero_le {D : Fin N → F} (hD : Function.Injective D) {p : F[X]}
    (hp : p ≠ 0) : (Finset.univ.filter fun j => p.eval (D j) = 0).card ≤ p.natDegree := by
  rw [← Finset.card_image_of_injective _ hD]
  refine card_le_degree_of_subset_roots fun z hz => ?_
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (Finset.mem_val.mp hz)
  exact (mem_roots hp).mpr (Finset.mem_filter.mp hj).2

/-- Two polynomials of degree `< k` that agree at `k` distinct points are equal. -/
theorem eq_of_eval_eq_at {f g : F[X]} (hf : f.degree < k) (hg : g.degree < k)
    {z : Fin k → F} (hz : Function.Injective z) (h : ∀ i, f.eval (z i) = g.eval (z i)) :
    f = g := by
  have hS : (Finset.univ.image z).card = k := by
    rw [Finset.card_image_of_injective _ hz, Finset.card_univ, Fintype.card_fin]
  apply eq_of_degree_sub_lt_of_eval_finset_eq (Finset.univ.image z)
  · rw [hS]
    exact (degree_sub_le _ _).trans_lt (max_lt hf hg)
  · intro w hw
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
    exact h i

end Math

section Decoder

variable [DecidableEq F]

/-- The positions at which `u` disagrees with the polynomial with coefficients `c`. -/
def errorSet (D u : Fin N → F) (c : Fin k → F) : Finset (Fin N) :=
  Finset.univ.filter fun j => u j ≠ evalCoeffs c (D j)

theorem errorSet_eq_errs (D u : Fin N → F) (c : Fin k → F) :
    errorSet D u c = errs D u (ofCoeffs c) := by
  simp only [errorSet, errs, eval_ofCoeffs]

/-- The positions with `E(D_j) ≠ 0`, in increasing order. -/
def goodPositions (D : Fin N → F) (x : Fin (e + k + e) → F) : List (Fin N) :=
  (List.finRange N).filter fun j => decide (eValue x (D j) ≠ 0)

theorem goodPositions_nodup (D : Fin N → F) (x : Fin (e + k + e) → F) :
    (goodPositions (k := k) D x).Nodup :=
  (List.nodup_finRange N).filter _

theorem eValue_ne_zero_of_mem_goodPositions {D : Fin N → F} {x : Fin (e + k + e) → F}
    {j : Fin N} (h : j ∈ goodPositions D x) : eValue x (D j) ≠ 0 := by
  simpa [goodPositions] using h

theorem length_goodPositions (D : Fin N → F) (x : Fin (e + k + e) → F) :
    (goodPositions (k := k) D x).length =
      (Finset.univ.filter fun j => eValue x (D j) ≠ 0).card := by
  rw [← List.toFinset_card_of_nodup (goodPositions_nodup D x)]
  congr 1
  ext j
  simp [goodPositions]

/-- At least `N - e` positions have `E(D_j) ≠ 0`. -/
theorem le_length_goodPositions {D : Fin N → F} (hD : Function.Injective D)
    (x : Fin (e + k + e) → F) : N - e ≤ (goodPositions (k := k) D x).length := by
  rw [length_goodPositions]
  have hzero := card_filter_eval_eq_zero_le hD (Epoly_monic x).ne_zero
  rw [Epoly_natDegree] at hzero
  simp only [eval_Epoly] at hzero
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N))) (fun j => eValue x (D j) = 0)
  simp only [Finset.card_univ, Fintype.card_fin, ← ne_eq] at hsplit
  omega

/-- The Vandermonde matrix of the points `D (pts i)`: entry `(i, l)` is `D (pts i) ^ l`. -/
def vandermonde (D : Fin N → F) (pts : Fin k → Fin N) : Fin k → Fin k → F :=
  fun i l => D (pts i) ^ (l : ℕ)

omit [DecidableEq F] in
theorem vandermonde_mulVec (D : Fin N → F) (pts : Fin k → Fin N) (c : Fin k → F) (i : Fin k) :
    (vandermonde D pts *ᵥ c) i = evalCoeffs c (D (pts i)) := by
  simp only [Matrix.mulVec, dotProduct, vandermonde, evalCoeffs]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- **Berlekamp–Welch on values**: the coefficients of the polynomial of degree `< k` within `e`
errors of `u`, or `none` if there is none (`decode_eq_some_iff`, `decode_eq_none_iff`).

Running time: the Berlekamp–Welch system has `N` rows and `2e + k ≤ N` unknowns, `O(N · (2e + k))`
field operations to set up and `O(N · (2e + k)²)` to solve (`GaussianElimination.solveArr`). Evaluating `E`
and `Q` at the `N` points costs `O(N · (2e + k) · log N)`; the Vandermonde system is `k × k`,
`O(k² log k)` to set up and `O(k³)` to solve; the final count evaluates the interpolant at `N`
points, `O(N · k · log k)`. In total `O(N · (2e + k)²)` field operations, polynomial in `N`.
This running time is argued here, not proved in Lean. -/
def decode (D : Fin N → F) (k e : ℕ) (u : Fin N → F) : Option (Fin k → F) :=
  match GaussianElimination.solve (sysA k e D u) (sysB D u e) with
  | none => none
  | some x =>
    let good := (goodPositions (k := k) D x).toArray
    if h : k ≤ good.size then
      let pts : Fin k → Fin N := fun i => good[i]
      match GaussianElimination.solve (vandermonde D pts)
          (fun i => qValue x (D (pts i)) / eValue x (D (pts i))) with
      | none => none
      | some c => if (errorSet D u c).card ≤ e then some c else none
    else none

/-- Whatever `decode` returns is within `e` errors of `u`. -/
theorem card_errorSet_le_of_decode_eq_some {D u : Fin N → F} {c : Fin k → F}
    (h : decode D k e u = some c) : (errorSet D u c).card ≤ e := by
  unfold decode at h
  split at h
  · cases h
  · simp only at h
    split_ifs at h with hk
    split at h
    · cases h
    · split_ifs at h with he
      cases h
      exact he

/-- **Completeness**: a polynomial of degree `< k` within `e` errors of `u` is decoded. -/
theorem decode_of_close {D u : Fin N → F} (hD : Function.Injective D) (hr : 2 * e + k ≤ N)
    {f : F[X]} (hf : Close D u k e f) :
    decode D k e u = some (fun i : Fin k => f.coeff i) := by
  obtain ⟨x0, hx0⟩ := exists_solution hf
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (GaussianElimination.solve_isSome_of_mulVec_eq hx0)
  have hkey := Qpoly_eq_mul_Epoly hD hr hf (GaussianElimination.solve_eq_some hx)
  have hlen := le_length_goodPositions (k := k) hD x
  have hk : k ≤ (goodPositions (k := k) D x).toArray.size := by
    rw [List.size_toArray]
    omega
  let pts : Fin k → Fin N := fun i => (goodPositions (k := k) D x).toArray[i]
  have hpts : ∀ i, pts i = (goodPositions (k := k) D x)[i] := fun i => by
    simp [pts]
  have hmem : ∀ i, pts i ∈ goodPositions (k := k) D x := fun i => by
    rw [hpts]
    exact List.getElem_mem _
  have hinj : Function.Injective pts := by
    intro i i' h
    rw [hpts, hpts] at h
    exact Fin.ext ((goodPositions_nodup D x).getElem_inj_iff.mp h)
  have hval : ∀ i, qValue x (D (pts i)) / eValue x (D (pts i)) = f.eval (D (pts i)) := by
    intro i
    have hE := eValue_ne_zero_of_mem_goodPositions (hmem i)
    rw [← eval_Qpoly, hkey, eval_mul, eval_Epoly, mul_div_assoc, div_self hE, mul_one]
  have hcons : vandermonde D pts *ᵥ (fun l : Fin k => f.coeff l) =
      fun i => qValue x (D (pts i)) / eValue x (D (pts i)) := by
    funext i
    rw [vandermonde_mulVec, evalCoeffs_coeff hf.degree]
    exact (hval i).symm
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (GaussianElimination.solve_isSome_of_mulVec_eq hcons)
  have hceq : ofCoeffs c = f := by
    have hsol := GaussianElimination.solve_eq_some hc
    refine eq_of_eval_eq_at (degree_ofCoeffs_lt c)
      (degree_le_natDegree.trans_lt (by exact_mod_cast hf.degree))
      (z := fun i => D (pts i)) (hD.comp hinj) fun i => ?_
    rw [eval_ofCoeffs, ← vandermonde_mulVec, hsol]
    exact hval i
  have hcf : c = fun i : Fin k => f.coeff i := by
    rw [← hceq]
    funext i
    rw [coeff_ofCoeffs]
  have herr : (errorSet D u c).card ≤ e := by
    rw [errorSet_eq_errs, hceq]
    exact hf.errors
  unfold decode
  rw [hx]
  simp only [pts] at hc
  rw [hcf] at herr
  simp only [hk, ↓reduceDIte, hc, hcf, herr, ↓reduceIte]

/-- **Row decoding specification**: `decode` returns `c` iff the polynomial with coefficients `c`
is within `e` errors of `u`.

Hypotheses: `hD` (`param`: distinct points), `hr` (`param`: unique-decoding radius),
`hk` (`param`). -/
theorem decode_eq_some_iff {D u : Fin N → F} (hD : Function.Injective D) (hr : 2 * e + k ≤ N)
    (hk : 0 < k) {c : Fin k → F} :
    decode D k e u = some c ↔ (errorSet D u c).card ≤ e := by
  constructor
  · exact card_errorSet_le_of_decode_eq_some
  · intro h
    have hclose : Close D u k e (ofCoeffs c) :=
      ⟨natDegree_ofCoeffs_lt hk c, errorSet_eq_errs D u c ▸ h⟩
    rw [decode_of_close hD hr hclose]
    congr 1
    funext i
    exact coeff_ofCoeffs c i

/-- `decode` returns the coefficients of `f` iff `f` is close to `u`.

Hypotheses: `hD` (`param`), `hr` (`param`), `hk` (`param`). -/
theorem decode_eq_some_iff_close {D u : Fin N → F} (hD : Function.Injective D)
    (hr : 2 * e + k ≤ N) (hk : 0 < k) {c : Fin k → F} :
    decode D k e u = some c ↔ Close D u k e (ofCoeffs c) := by
  rw [decode_eq_some_iff hD hr hk, errorSet_eq_errs]
  exact ⟨fun h => ⟨natDegree_ofCoeffs_lt hk c, h⟩, fun h => h.errors⟩

/-- `decode` fails iff no polynomial of degree `< k` is within `e` errors of `u`.

Hypotheses: `hD` (`param`), `hr` (`param`), `hk` (`param`). -/
theorem decode_eq_none_iff {D u : Fin N → F} (hD : Function.Injective D) (hr : 2 * e + k ≤ N)
    (hk : 0 < k) : decode D k e u = none ↔ ¬ ∃ f, Close D u k e f := by
  constructor
  · rintro h ⟨f, hf⟩
    rw [decode_of_close hD hr hf] at h
    cases h
  · intro h
    cases hdec : decode D k e u with
    | none => rfl
    | some c => exact (h ⟨ofCoeffs c, (decode_eq_some_iff_close hD hr hk).mp hdec⟩).elim

end Decoder

end GordieHowe.RSCode.BerlekampWelch
