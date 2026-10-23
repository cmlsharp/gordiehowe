-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Ligero.Tableau

@[expose] public section

/-!
# Honest completeness for the prepared Ligero tableau

This file gives the algebraic completeness witness for the verifier interface
in `Ligero.Tableau`.  A tableau is fixed before the batching challenges: its
rows satisfy `Holds`, and its two mask polynomials satisfy the zero functionals
used by the C++ IDOT and IQUAD rows.  The masks may be chosen to be zero; the
point is existence and causal placement, not a zero-knowledge claim.

The encoded matrix evaluates the fixed row polynomials on the code domain.
Responses add the fixed masks to the challenge batches.  Consequently every
query accepts, while the response degrees and scalar checks are discharged
from the prepared equations.  Merkle commitments and transcript bytes are
outside this algebraic oracle interface.

The construction follows `lib/ligero/ligero_prover.h`: IDOT is constrained by the W-only sum, IQUAD
is zero on the W coordinates, and the response vectors are the corresponding row combinations. See
`Ligero.Tableau.Valid` and its three acceptance predicates for the verifier interface.
-/

namespace GordieHowe.Ligero.Completeness
open IOP

open Polynomial
open scoped Classical
section

variable {F : Type} [Field F] {N R nL nQ nrep : ℕ}
  {C : GordieHowe.RSCode F N}
  {P : Tableau.Parameters (R := R) (nQ := nQ) C}
  {L : Tableau.LinearSystem (nL := nL) C P}

variable {hrate : 2 * C.k - 1 ≤ N}

/-- A fixed tableau and fixed prechallenge masks that satisfy the verifier's
prepared equations, with `nrep` low-degree repetitions: the ILDT polynomial of each repetition
and the data polynomials, whose tableau `ILDT_0, data` (`rows`) satisfies the equations.
`dotMask_zero` is the C++ IDOT W-sum constraint and `quadMask_zero` is the C++ IQUAD W-zero
constraint. -/
structure HonestTableau (hrate : 2 * C.k - 1 ≤ N) (nrep : ℕ) [NeZero nrep] where
  /-- The ILDT polynomial of each repetition. -/
  ildt : Fin nrep → F[X]
  /-- The data polynomials. -/
  data : Fin R → F[X]
  ildt_degree : ∀ j, (ildt j).natDegree < C.k
  data_degree : ∀ i, (data i).natDegree < C.k
  holds : Tableau.Holds C P L (Fin.cons (ildt 0) data)
  dotMask : F[X]
  quadMask : F[X]
  dotMask_degree : dotMask.natDegree < (MaskedPolynomialTest.maskCode C hrate).k
  quadMask_degree : quadMask.natDegree < (MaskedPolynomialTest.maskCode C hrate).k
  dotMask_zero : Tableau.dotCheck C P dotMask = 0
  quadMask_zero : ∀ j, Tableau.quadCheck C P j quadMask = 0

/-- Canonical existence witness: zero IDOT and IQUAD masks satisfy the two
zero-knowledge row constraints, and every repetition uses the ILDT row `rows 0`.  Nonzero masks
can be supplied through `HonestTableau` when a separate hiding argument needs them. -/
noncomputable def HonestTableau.ofRows (hrate : 2 * C.k - 1 ≤ N) (nrep : ℕ) [NeZero nrep]
    (rows : Fin (R + 1) → F[X]) (rows_degree : ∀ row, (rows row).natDegree < C.k)
    (holds : Tableau.Holds C P L rows) :
    HonestTableau (C := C) (P := P) (L := L) hrate nrep where
  ildt _ := rows 0
  data := Fin.tail rows
  ildt_degree _ := rows_degree 0
  data_degree i := rows_degree i.succ
  holds := by rwa [Fin.cons_self_tail]
  dotMask := 0
  quadMask := 0
  dotMask_degree := by
    have hk := C.k_pos
    simpa [MaskedPolynomialTest.maskCode] using (show 0 < 2 * C.k - 1 by omega)
  quadMask_degree := by
    have hk := C.k_pos
    simpa [MaskedPolynomialTest.maskCode] using (show 0 < 2 * C.k - 1 by omega)
  dotMask_zero := by simp
  quadMask_zero := by intro j; simp [Tableau.quadCheck]

variable [NeZero nrep] (H : HonestTableau (C := C) (P := P) (L := L) hrate nrep)

/-- The polynomials of repetition `j`'s matrix: its ILDT polynomial, then the data
polynomials. -/
noncomputable def HonestTableau.ldtRows (j : Fin nrep) : Fin (R + 1) → F[X] :=
  Fin.cons (H.ildt j) H.data

/-- The tableau polynomials: repetition `0`'s (`ILDT_0`, then the data polynomials). -/
noncomputable def HonestTableau.rows : Fin (R + 1) → F[X] := H.ldtRows 0

theorem HonestTableau.ldtRows_degree (j : Fin nrep) (row : Fin (R + 1)) :
    (H.ldtRows j row).natDegree < C.k :=
  Fin.cases (H.ildt_degree j) H.data_degree row

theorem HonestTableau.rows_degree (row : Fin (R + 1)) : (H.rows row).natDegree < C.k :=
  H.ldtRows_degree 0 row

theorem HonestTableau.rows_holds : Tableau.Holds C P L H.rows := H.holds

/-- Evaluation of the fixed polynomials on the verifier domain: the encoded rows. -/
noncomputable def encode : Tableau.Rows F N R nrep :=
  ⟨fun j col => (H.ildt j).eval (C.D col), fun i col => (H.data i).eval (C.D col)⟩

theorem encode_ldtMatrix (j : Fin nrep) (row : Fin (R + 1)) (col : Fin N) :
    (encode H).ldtMatrix j row col = (H.ldtRows j row).eval (C.D col) :=
  Fin.cases rfl (fun _ => rfl) row

theorem encode_tableau (row : Fin (R + 1)) (col : Fin N) :
    (encode H).tableau row col = (H.rows row).eval (C.D col) :=
  encode_ldtMatrix H 0 row col

/-- The fixed IDOT and IQUAD masks, evaluated on the verifier domain. -/
def masks : Tableau.Aux F N :=
  (fun j => H.dotMask.eval (C.D j), fun j => H.quadMask.eval (C.D j))

/-- The projected row polynomial of repetition `j` used by the affine code test. -/
noncomputable def codeResponse (r : Tableau.Challenge F R nL nQ nrep) (j : Fin nrep) : F[X] :=
  AffineCodeTest.projectedPolynomial (H.ldtRows j) (r.1 j)

/-- The IDOT response after the linear batching challenge. -/
noncomputable def dotResponse (r : Tableau.Challenge F R nL nQ nrep) : F[X] :=
  H.dotMask + MaskedConstraintTest.batch
    (fun l => Tableau.dotPolynomials C P L H.rows l) r.2.1

/-- The IQUAD response after the quadratic batching challenge. -/
noncomputable def quadResponse (r : Tableau.Challenge F R nL nQ nrep) : F[X] :=
  H.quadMask + MaskedConstraintTest.batch
    (fun q => Tableau.quadPolynomials C P H.rows q) r.2.2

theorem encode_decode :
    RSCode.nearbyRows C (encode H).tableau = some H.rows := by
  apply RSCode.nearbyRows_eq_some_iff.mpr
  refine ⟨H.rows_degree, ?_⟩
  have he : (Finset.univ.filter (fun j : Fin N =>
      ∃ row, (encode H).tableau row j ≠ (H.rows row).eval (C.D j))) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro j _ hj
    obtain ⟨row, hrow⟩ := hj
    exact hrow (encode_tableau H row j)
  simpa only [RSCode.columnErrors, he, Finset.card_empty, Nat.zero_le]

theorem dotColumn_encode (l : Fin nL) (j : Fin N) :
    Tableau.dotColumn C P L (encode H).tableau l j =
      (Tableau.dotPolynomials C P L H.rows l).eval (C.D j) := by
  simp only [Tableau.dotColumn, Tableau.dotPolynomials,
    LigeroInterpolation.decodedDot, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, encode_tableau, LigeroInterpolation.eval_interpolate]

theorem quadColumn_encode (q : Fin nQ) (j : Fin N) :
    Tableau.quadColumn C P (encode H).tableau q j =
      (Tableau.quadPolynomials C P H.rows q).eval (C.D j) := by
  simp only [Tableau.quadColumn, Tableau.quadPolynomials, encode_tableau,
    Polynomial.eval_sub, Polynomial.eval_mul]

theorem add_degree_lt_mask (hrate : 2 * C.k - 1 ≤ N) (a b : F[X])
    (ha : a.natDegree < (MaskedPolynomialTest.maskCode C hrate).k)
    (hb : b.natDegree < (MaskedPolynomialTest.maskCode C hrate).k) :
    (a + b).natDegree < (MaskedPolynomialTest.maskCode C hrate).k := by
  exact (Polynomial.natDegree_add_le _ _).trans_lt (max_lt ha hb)

theorem dot_polynomial_degree (hrate : 2 * C.k - 1 ≤ N) (l : Fin nL) :
    (Tableau.dotPolynomials C P L H.rows l).natDegree <
      (MaskedPolynomialTest.maskCode C hrate).k := by
  simpa only [MaskedPolynomialTest.maskCode] using
    Tableau.dot_degree C P L H.rows H.rows_degree l

theorem quad_polynomial_degree (hrate : 2 * C.k - 1 ≤ N) (q : Fin nQ) :
    (Tableau.quadPolynomials C P H.rows q).natDegree <
      (MaskedPolynomialTest.maskCode C hrate).k := by
  simpa only [MaskedPolynomialTest.maskCode] using
    Tableau.quad_degree C P H.rows H.rows_degree q

theorem batch_degree_mask (hrate : 2 * C.k - 1 ≤ N)
    (g : Fin nL → F[X]) (hg : ∀ i, (g i).natDegree <
      (MaskedPolynomialTest.maskCode C hrate).k) (r : Fin nL → F) :
    (MaskedConstraintTest.batch g r).natDegree <
      (MaskedPolynomialTest.maskCode C hrate).k := by
  exact MaskedConstraintTest.batch_degree (MaskedPolynomialTest.maskCode C hrate)
    g hg r

theorem quad_batch_degree_mask (hrate : 2 * C.k - 1 ≤ N)
    (g : Fin nQ → F[X]) (hg : ∀ i, (g i).natDegree <
      (MaskedPolynomialTest.maskCode C hrate).k) (r : Fin nQ → F) :
    (MaskedConstraintTest.batch g r).natDegree <
      (MaskedPolynomialTest.maskCode C hrate).k := by
  exact MaskedConstraintTest.batch_degree (MaskedPolynomialTest.maskCode C hrate)
    g hg r

theorem codeResponse_degree (r : Tableau.Challenge F R nL nQ nrep) (j : Fin nrep) :
    (codeResponse H r j).natDegree < C.k :=
  AffineCodeTest.projectedPolynomial_degree (H.ldtRows_degree j) (r.1 j)

theorem dotResponse_degree (hrate : 2 * C.k - 1 ≤ N)
    (r : Tableau.Challenge F R nL nQ nrep) :
    (dotResponse H r).natDegree <
      (MaskedPolynomialTest.maskCode C hrate).k := by
  apply add_degree_lt_mask hrate H.dotMask
    (MaskedConstraintTest.batch (fun l => Tableau.dotPolynomials C P L H.rows l) r.2.1)
    H.dotMask_degree
    (batch_degree_mask hrate _ (fun l => dot_polynomial_degree H hrate l) r.2.1)

theorem quadResponse_degree (hrate : 2 * C.k - 1 ≤ N)
    (r : Tableau.Challenge F R nL nQ nrep) :
    (quadResponse H r).natDegree <
      (MaskedPolynomialTest.maskCode C hrate).k := by
  apply add_degree_lt_mask hrate H.quadMask
    (MaskedConstraintTest.batch (fun q => Tableau.quadPolynomials C P H.rows q) r.2.2)
    H.quadMask_degree
    (quad_batch_degree_mask hrate _ (fun q => quad_polynomial_degree H hrate q) r.2.2)

/-- The response formed after the verifier's algebraic challenge: the values of the three
response polynomials on the response nodes (`Tableau.Response.ofPolys`). Its degree bounds are
`codeResponse_degree`, `dotResponse_degree` and `quadResponse_degree`. -/
noncomputable def response (r : Tableau.Challenge F R nL nQ nrep) :
    Tableau.Response F C.k nrep :=
  Tableau.Response.ofPolys C (codeResponse H r) (dotResponse H r) (quadResponse H r)

@[simp] theorem response_code (r : Tableau.Challenge F R nL nQ nrep) (j : Fin nrep) :
    (response H r).code C j = codeResponse H r j :=
  Tableau.Response.code_ofPolys C (codeResponse_degree H r) _ _ j

@[simp] theorem response_dot (r : Tableau.Challenge F R nL nQ nrep) :
    (response H r).dot C = dotResponse H r :=
  Tableau.Response.dot_ofPolys C hrate _ (dotResponse_degree H hrate r) _

@[simp] theorem response_quad (r : Tableau.Challenge F R nL nQ nrep) :
    (response H r).quad C = quadResponse H r :=
  Tableau.Response.quad_ofPolys C hrate _ _ (quadResponse_degree H hrate r)

theorem valid (r : Tableau.Challenge F R nL nQ nrep) :
    Tableau.Valid C P L r (response H r) := by
  refine ⟨?_, ?_⟩
  · simp only [response_dot, dotResponse, LinearMap.map_add,
      MaskedConstraintTest.check_batch]
    rw [H.dotMask_zero]
    simp only [zero_add]
    calc
      ∑ i, r.2.1 i * Tableau.dotCheck C P
          (Tableau.dotPolynomials C P L H.rows i) =
          ∑ i, r.2.1 i * L.target i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [H.rows_holds.1 i]
      _ = _ := rfl
  · intro j
    simp only [response_quad, quadResponse,
      LinearMap.map_add, MaskedConstraintTest.check_batch]
    rw [H.quadMask_zero j]
    simp only [zero_add]
    simp only [H.rows_holds.2 j, mul_zero, Finset.sum_const_zero]

theorem codeAccept (r : Tableau.Challenge F R nL nQ nrep)
    {t : ℕ} (q : Tableau.Query N t) :
    Tableau.CodeAccept C (encode H) r.1
      (codeResponse H r) q := by
  intro j s
  simp only [codeResponse, AffineCodeTest.projection, encode_ldtMatrix,
    AffineCodeTest.eval_projectedPolynomial]

theorem dotAccept (r : Tableau.Challenge F R nL nQ nrep)
    {t : ℕ} (q : Tableau.Query N t) :
    Tableau.DotAccept C P L (encode H).tableau (masks H).1 r.2.1
      (dotResponse H r) q := by
  intro s
  simp only [Tableau.DotAccept, masks, dotResponse,
    MaskedConstraintTest.batch, Polynomial.eval_add,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  simp_rw [dotColumn_encode H]

theorem quadAccept (r : Tableau.Challenge F R nL nQ nrep)
    {t : ℕ} (q : Tableau.Query N t) :
    Tableau.QuadAccept C P (encode H).tableau (masks H).2 r.2.2
      (quadResponse H r) q := by
  intro s
  simp only [Tableau.QuadAccept, masks, quadResponse,
    MaskedConstraintTest.batch, Polynomial.eval_add,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  simp_rw [quadColumn_encode H]

theorem accept [DecidableEq F] (r : Tableau.Challenge F R nL nQ nrep)
    {t : ℕ} (q : Tableau.Query N t) :
    Tableau.accept C P L (encode H) (masks H) r
      (response H r) q = true := by
  rw [Tableau.accept_eq_true_iff, Tableau.AcceptProp, response_dot, response_quad]
  refine ⟨valid H r, ?_, dotAccept H r q, quadAccept H r q⟩
  simpa only [funext (response_code H r)] using codeAccept H r q

end
end GordieHowe.Ligero.Completeness
