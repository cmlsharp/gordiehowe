-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Ligero.AgreementThreshold

@[expose] public section

/-!
# Ligero at agreement threshold `A` with the mask test

Ligero at agreement threshold `A` (`GordieHowe.Ligero.AgreementThreshold`) whose two response masks are committed as
tested tableau rows (the paper's Appendix D.4, Mask pieces and the subfield test): for each mask
(IDOT, IQUAD) three rows `A`, `C`, `B` of the tableau, each a row of the code, and the verifier
evaluates the mask at column `j` as `A_j + x_j ^ (k − t) · C_j + x_j ^ k · B_j` (`recombine`,
`Pieces.value`). The piece rows are ordinary tableau rows: they enter the commit-phase low-degree
combination and are pinned with the witness rows.

* **the oracle message** is the encoded rows alone (`Tableau.Rows`: the `nrep` ILDT rows and the
  data rows), with their columns as leaves (`Tableau.Rows.column`);
* **the commit rounds** are the low-degree challenges and responses of the `nrep` repetitions
  (`GordieHowe.Ligero.AgreementThreshold.commitSpec`);
* **the extracted cells** are those of the prepared tableau
  (`GordieHowe.Ligero.AgreementThreshold.TableauSetup.extract`): on the common agreement set `D` of the low-degree
  test, if `|D| ≥ A`, every tableau row interpolated on the first `k` columns of `D`; zero
  otherwise;
* **the proof phase** is that of `GordieHowe.Ligero.AgreementThreshold` (`GordieHowe.Ligero.AgreementThreshold.proofSpec`); **the
  verdict** (`verdict`) is the tableau verifier `Ligero.Tableau.accept` with the masks recombined
  from the piece rows' entries in each queried column (`PieceRows.masks`).

**Soundness** (`sound`). The commit event is that every low-degree challenge is exceptional, of
density `(B / (|F| - 1)) ^ nrep` (`GordieHowe.Ligero.AgreementThreshold.Threshold.commitError`), as in
`GordieHowe.Ligero.AgreementThreshold`. Outside it, with `D` fixed by the commit phase before the query:

* if `|D| < A`, every accepted query lies in `D`, so at most `(A - 1).descFactorial t` queries
  are accepted;
* if `|D| ≥ A`, every row, including the six piece rows, agrees on all of `D` with the pinned row
  (`GordieHowe.Ligero.AgreementThreshold.Threshold.pinnedRows_agree`), so on `D` the recombined masks are the values of
  the pinned masks `M* = A* + X ^ (k − t) · C* + X ^ k · B*` (`PieceRows.masks_dot_eq_of_agree`),
  polynomials of degree `≤ 2k − 1` (`Pieces.natDegree_poly_lt`). If the rows hold on the extracted
  cells the claim holds. Otherwise the constraints fail on the pinned rows; outside the selected
  check's Schwartz–Zippel event at the pinned mask (`pinnedBad`, at most one `|F|`-th of the
  constraint challenges, `pinnedBad_count`), the selected masked response `q` differs from the true
  response `f(V) + M*`, both of degree `≤ 2k − 1`, and accepted queries lie in `D` and in the
  agreement set of those two polynomials, at most `2k − 1` columns (`selected_query_count_pinned`).

The column query costs `((A − 1).descFactorial t + (2k − 1).descFactorial t) / N.descFactorial t`
(`columnError`); the constraint challenge `1 / |F|` (`testError`).
-/

namespace GordieHowe.Ligero.MaskTest.Pieces
open IOP

open ProtocolSpec Polynomial
open Ligero.AgreementThreshold (commitSpec CommitRounds ldtChallenge ldtResponse proofSpec
  ConstraintChallenge MaskedResponse maskRound_dir queryIdx chQuery constraintOf maskedOf queryOf
  commonAgreement mem_commonAgreement_of_accept TableauSetup proofError proofError_le_of sum_proofError
  card_filter_le_of_lt card_le_fraction)
open scoped NNReal ENNReal

/-! ### The recombined mask -/

section Recombine

variable {F : Type} [Field F]

/-- **The recombined mask value** at the point `x` from the values `a`, `c`, `b` of the three
piece rows `A`, `C`, `B`: `a + x ^ (k − t) · c + x ^ k · b`. -/
def recombine (k t : ℕ) (x a c b : F) : F :=
  a + x ^ (k - t) * c + x ^ k * b

/-- **The recombined mask polynomial** `A + X ^ (k − t) · C + X ^ k · B` of three piece
polynomials. -/
noncomputable def recombinePoly (k t : ℕ) (a c b : F[X]) : F[X] :=
  a + Polynomial.X ^ (k - t) * c + Polynomial.X ^ k * b

/-- The recombined polynomial's value is the recombination of the pieces' values. -/
@[simp] theorem eval_recombinePoly (k t : ℕ) (a c b : F[X]) (x : F) :
    (recombinePoly k t a c b).eval x = recombine k t x (a.eval x) (c.eval x) (b.eval x) := by
  simp [recombinePoly, recombine]

/-- Three pieces of degree `< k` recombine to a polynomial of degree `≤ 2k − 1`. -/
theorem natDegree_recombinePoly_lt {k : ℕ} (t : ℕ) {a c b : F[X]} (ha : a.natDegree < k)
    (hc : c.natDegree < k) (hb : b.natDegree < k) :
    (recombinePoly k t a c b).natDegree < 2 * k := by
  have hC : (Polynomial.X ^ (k - t) * c).natDegree < 2 * k :=
    natDegree_mul_le.trans_lt (by rw [natDegree_X_pow]; omega)
  have hB : (Polynomial.X ^ k * b).natDegree < 2 * k :=
    natDegree_mul_le.trans_lt (by rw [natDegree_X_pow]; omega)
  exact (natDegree_add_le _ _).trans_lt
    (max_lt ((natDegree_add_le _ _).trans_lt (max_lt (by omega) hC)) hB)

/-- **The piece rows of one response mask**: the tableau rows of
the pieces `A`, `C`, `B`, each a row of the code; the mask is `A + X ^ (k − t) · C + X ^ k · B`
(`recombinePoly`). -/
structure Pieces (R : ℕ) where
  /-- The row of the piece `A`. -/
  rowA : Fin (R + 1)
  /-- The row of the piece `C`, shifted by `X ^ (k − t)`. -/
  rowC : Fin (R + 1)
  /-- The row of the piece `B`, shifted by `X ^ k`. -/
  rowB : Fin (R + 1)

namespace Pieces

variable {N R : ℕ} (pc : Pieces R)

/-- **The mask value at column `j`** of the tableau `U`: the recombination of the piece rows'
entries in column `j` at the column's point `C.D j`. -/
def value (C : GordieHowe.RSCode F N) (t : ℕ) (U : RSCode.Matrix F (R + 1) N) (j : Fin N) : F :=
  recombine C.k t (C.D j) (U pc.rowA j) (U pc.rowC j) (U pc.rowB j)

/-- **The mask polynomial of the rows `fs`**: the recombination of the piece rows' polynomials. -/
noncomputable def poly (k t : ℕ) (fs : Fin (R + 1) → F[X]) : F[X] :=
  recombinePoly k t (fs pc.rowA) (fs pc.rowC) (fs pc.rowB)

/-- The mask value at a column reads only that column. -/
theorem value_congr {C : GordieHowe.RSCode F N} {t : ℕ} {U U' : RSCode.Matrix F (R + 1) N}
    {j : Fin N} (h : ∀ row, U row j = U' row j) : pc.value C t U j = pc.value C t U' j := by
  simp only [value, h]

/-- **At a column where every row is the evaluation of its polynomial in `fs`**, the mask value is
the evaluation of the mask polynomial of `fs`. -/
theorem value_eq_eval {C : GordieHowe.RSCode F N} {t : ℕ} {U : RSCode.Matrix F (R + 1) N}
    {fs : Fin (R + 1) → F[X]} {j : Fin N} (h : ∀ row, U row j = (fs row).eval (C.D j)) :
    pc.value C t U j = (pc.poly C.k t fs).eval (C.D j) := by
  simp only [value, poly, eval_recombinePoly, h]

/-- Rows of degree `< k` give a mask polynomial of degree `≤ 2k − 1`. -/
theorem natDegree_poly_lt {k : ℕ} (t : ℕ) {fs : Fin (R + 1) → F[X]}
    (hfs : ∀ row, (fs row).natDegree < k) : (pc.poly k t fs).natDegree < 2 * k :=
  natDegree_recombinePoly_lt t (hfs _) (hfs _) (hfs _)

end Pieces

/-- **The piece rows of the two response masks**: three rows for the IDOT mask and three for the
IQUAD mask (`Pieces`). -/
structure PieceRows (R : ℕ) where
  /-- The piece rows of the IDOT mask (the linear test). -/
  dot : Pieces R
  /-- The piece rows of the IQUAD mask (the quadratic test). -/
  quad : Pieces R

/-- **The mask rows of two polynomials**: their values at the code's evaluation points. -/
noncomputable def evalMasks {N : ℕ} (C : GordieHowe.RSCode F N) (mDot mQuad : F[X]) :
    Tableau.Aux F N :=
  (fun j => mDot.eval (C.D j), fun j => mQuad.eval (C.D j))

namespace PieceRows

variable {N R : ℕ} (pr : PieceRows R)

/-- **The recombined masks of the tableau `U`**: at every column, the IDOT and IQUAD mask values
recombined from the piece rows' entries in that column (`Pieces.value`). -/
def masks (C : GordieHowe.RSCode F N) (t : ℕ) (U : RSCode.Matrix F (R + 1) N) : Tableau.Aux F N :=
  (pr.dot.value C t U, pr.quad.value C t U)

/-- **The mask polynomials' values for the rows `fs`** (`evalMasks` of `Pieces.poly`). -/
noncomputable def polyMasks (C : GordieHowe.RSCode F N) (t : ℕ) (fs : Fin (R + 1) → F[X]) :
    Tableau.Aux F N :=
  evalMasks C (pr.dot.poly C.k t fs) (pr.quad.poly C.k t fs)

/-- The recombined IDOT mask at a column reads only that column. -/
theorem masks_dot_congr {C : GordieHowe.RSCode F N} {t : ℕ} {U U' : RSCode.Matrix F (R + 1) N}
    {j : Fin N} (h : ∀ row, U row j = U' row j) :
    (pr.masks C t U).dot j = (pr.masks C t U').dot j :=
  pr.dot.value_congr h

/-- The recombined IQUAD mask at a column reads only that column. -/
theorem masks_quad_congr {C : GordieHowe.RSCode F N} {t : ℕ} {U U' : RSCode.Matrix F (R + 1) N}
    {j : Fin N} (h : ∀ row, U row j = U' row j) :
    (pr.masks C t U).quad j = (pr.masks C t U').quad j :=
  pr.quad.value_congr h

/-- At a column where the rows are the evaluations of `fs`, the recombined IDOT mask is the value
of the IDOT mask polynomial of `fs`. -/
theorem masks_dot_eq_of_agree {C : GordieHowe.RSCode F N} {t : ℕ} {U : RSCode.Matrix F (R + 1) N}
    {fs : Fin (R + 1) → F[X]} {j : Fin N} (h : ∀ row, U row j = (fs row).eval (C.D j)) :
    (pr.masks C t U).dot j = (pr.polyMasks C t fs).dot j :=
  pr.dot.value_eq_eval h

/-- At a column where the rows are the evaluations of `fs`, the recombined IQUAD mask is the value
of the IQUAD mask polynomial of `fs`. -/
theorem masks_quad_eq_of_agree {C : GordieHowe.RSCode F N} {t : ℕ} {U : RSCode.Matrix F (R + 1) N}
    {fs : Fin (R + 1) → F[X]} {j : Fin N} (h : ∀ row, U row j = (fs row).eval (C.D j)) :
    (pr.masks C t U).quad j = (pr.polyMasks C t fs).quad j :=
  pr.quad.value_eq_eval h

end PieceRows

end Recombine

/-! ### The selected test at pinned masks

The masked constraint test with the masks fixed polynomials (candidate lists of size one,
`MaskedConstraintList.FiniteList.pinned_query_count`): outside the affine cancellation event at a
mask `m`, a valid response `p` has `p − batch ≠ m`, so the column identity `m + batch = p` holds at
fewer points than the degree bound. -/

section PinnedTest

variable {F : Type} [Field F] {N n : ℕ}

variable {R nL nQ : ℕ} (C : GordieHowe.RSCode F N) (P : Tableau.Parameters (R := R) (nQ := nQ) C)
  (L : Tableau.LinearSystem (nL := nL) C P)

open Classical in
/-- **The selected check's event at the pinned masks** `mDot`, `mQuad` on the rows `fs`: the
cancellation event of the linear family at `mDot` when the linear checks fail on `fs`, else of
the quadratic family at `mQuad` (`UntestedMaskRow.constraintBad` with the one-candidate lists
`{mDot}`, `{mQuad}`). -/
def pinnedBad (fs : Fin (R + 1) → F[X]) (mDot mQuad : F[X]) (r : (Fin nL → F) × (Fin nQ → F)) :
    Prop :=
  if ¬ ∀ l, Tableau.dotCheck C P (Tableau.dotPolynomials C P L fs l) = L.target l then
    MaskedConstraintList.FiniteList.BadChallenge {mDot} (Tableau.dotCheck C P)
      (Tableau.dotPolynomials C P L fs) L.target r.1
  else MaskedConstraintList.FiniteList.FamilyBadChallenge {mQuad} (Tableau.quadCheck C P)
    (Tableau.quadPolynomials C P fs) (fun _ _ => 0) r.2

open Classical in
/-- **The exact count of the selected check's event at the pinned masks**: at most one `|F|`-th of
the constraint challenges, `|bad| · |F| ≤ |F| ^ (nL + nQ)`, for all rows `fs` and masks `mDot`,
`mQuad` (one affine event of the selected check, `AffineBatching.card_zeros_mul_card_le`). -/
theorem pinnedBad_count [Fintype F] (fs : Fin (R + 1) → F[X]) (mDot mQuad : F[X]) :
    (Finset.univ.filter (pinnedBad C P L fs mDot mQuad)).card * Fintype.card F ≤
      Fintype.card ((Fin nL → F) × (Fin nQ → F)) := by
  change (Finset.univ.filter fun r => pinnedBad C P L fs mDot mQuad r).card * _ ≤ _
  by_cases hd : ¬ ∀ l, Tableau.dotCheck C P (Tableau.dotPolynomials C P L fs l) = L.target l
  · simp only [pinnedBad, ite_eq_left hd]
    rw [UntestedMaskRow.count_left]
    have h := MaskedConstraintList.FiniteList.badChallenge_count {mDot} (Tableau.dotCheck C P)
      (Tableau.dotPolynomials C P L fs) L.target (not_forall.mp hd)
    rw [Finset.card_singleton, one_mul] at h
    rw [mul_assoc, mul_comm (Fintype.card (Fin nQ → F)), ← mul_assoc]
    simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] using
      Nat.mul_le_mul_right (Fintype.card (Fin nQ → F)) h
  · simp only [pinnedBad, ite_eq_right hd]
    rw [UntestedMaskRow.count_right]
    have h := MaskedConstraintList.FiniteList.family_badChallenge_count {mQuad}
      (Tableau.quadCheck C P) (Tableau.quadPolynomials C P fs) (fun _ _ => 0)
    rw [Finset.card_singleton, one_mul] at h
    rw [mul_assoc]
    simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] using
      Nat.mul_le_mul_left (Fintype.card (Fin nL → F)) h

open Classical in
/-- **The selected column count at the pinned masks**: for rows `fs` of degree `< k` on which the
constraints fail and mask polynomials of degree `≤ 2k − 1`, outside the selected event at the
masks (`pinnedBad`), a valid response passes the selected family's column identity with the
masks' values (`Tableau.selectedAccept` at `evalMasks`) on at most `(2k − 1).descFactorial t`
query tuples. -/
theorem selected_query_count_pinned (hrate : 2 * C.k - 1 ≤ N) (fs : Fin (R + 1) → F[X])
    (hfs : ∀ row, (fs row).natDegree < C.k) {mDot mQuad : F[X]} (hmDot : mDot.natDegree < 2 * C.k)
    (hmQuad : mQuad.natDegree < 2 * C.k) (hfalse : ¬ Tableau.Holds C P L fs)
    {nrep : ℕ} (r : Tableau.Challenge F R nL nQ nrep) (hbad : ¬ pinnedBad C P L fs mDot mQuad r.2)
    (p : Tableau.Response F C.k nrep) (hp : Tableau.Valid C P L r p) (t : ℕ) :
    (Finset.univ.filter
      (Tableau.selectedAccept C P L fs (evalMasks C mDot mQuad) r p (t := t))).card ≤
      (2 * C.k - 1).descFactorial t := by
  have hk := C.k_pos
  by_cases hd : ¬ ∀ l, Tableau.dotCheck C P (Tableau.dotPolynomials C P L fs l) = L.target l
  · have hb : ¬ MaskedConstraintList.FiniteList.BadChallenge {mDot} (Tableau.dotCheck C P)
        (Tableau.dotPolynomials C P L fs) L.target r.2.1 := by
      simpa only [pinnedBad, ite_eq_left hd] using hbad
    have h := MaskedConstraintList.FiniteList.pinned_query_count C.D_injective hmDot (Tableau.dotCheck C P)
      (fun i => (Tableau.dot_degree C P L fs hfs i).trans (by omega)) L.target hb
      ((Tableau.Response.natDegree_dot_lt C hrate p).trans (by omega)) hp.1 t
    change (Finset.univ.filter fun q => Tableau.selectedAccept C P L fs _ r p q).card ≤ _
    simp only [Tableau.selectedAccept, ite_eq_left hd]
    convert h using 1; rfl
  · have hqfalse : ¬ MaskedConstraintFamily.Claim (Tableau.quadCheck C P)
        (Tableau.quadPolynomials C P fs) (fun _ _ => 0) := fun hq => hfalse ⟨not_not.mp hd, hq⟩
    have hb : ¬ MaskedConstraintList.FiniteList.FamilyBadChallenge {mQuad} (Tableau.quadCheck C P)
        (Tableau.quadPolynomials C P fs) (fun _ _ => 0) r.2.2 := by
      simpa only [pinnedBad, ite_eq_right hd] using hbad
    have h := MaskedConstraintList.FiniteList.pinned_family_query_count C.D_injective hmQuad (Tableau.quadCheck C P)
      (fun i => (Tableau.quad_degree C P fs hfs i).trans (by omega)) _ hqfalse hb
      ((Tableau.Response.natDegree_quad_lt C hrate p).trans (by omega)) (by simpa using hp.2) t
    change (Finset.univ.filter fun q => Tableau.selectedAccept C P L fs _ r p q).card ≤ _
    simp only [Tableau.selectedAccept, ite_eq_right hd]
    convert h using 1; rfl

end PinnedTest

section

variable {F ι Q Lin : Type} [Field F] [Fintype F] [Fintype ι] [Fintype Q] [Fintype Lin]
  {N R nL nQ : ℕ} {C : GordieHowe.RSCode F N} {P : Tableau.Parameters (R := R) (nQ := nQ) C}
  {products : Routing.ProductLayout ι Q}

/-! ### The setup -/

/-- **The data of Ligero at agreement threshold `A` with the mask test**: the prepared tableau at
agreement threshold `A` (`Ligero.AgreementThreshold.TableauSetup`), `rate_le`: the rate condition
`2k − 1 ≤ N` that the response masks' code needs, and `pieces`: the six piece rows of the two
response masks (`PieceRows`); the shift of the piece `C` is `X ^ (k − t)`. -/
structure Setup (C : GordieHowe.RSCode F N) (P : Tableau.Parameters (R := R) (nQ := nQ) C)
    (products : Routing.ProductLayout ι Q) (Lin : Type) (nL : ℕ)
    extends TableauSetup C P products Lin nL where
  /-- The rate condition `2k − 1 ≤ N` of the response masks (a parameter condition). -/
  rate_le : 2 * C.k - 1 ≤ N
  pieces : PieceRows R

/-- **The code parameters of Ligero at agreement threshold `A` with the mask test**, parameter facts
about the code `C` at the numbers `A` (the agreement threshold) and `B` (the exceptional count of
the line certificate): `k ≤ A` and a line certificate at threshold `A` with at most `B`
exceptional challenges per line (`RSCode.LineCertificate`). These are
`Ligero.AgreementThreshold.Parameters` without the arbitrary-mask list hypotheses, which this system does
not use. A configuration proves them once per tableau, the line certificate from a weighted
Johnson certificate (`RSCode.lineCertificate_of_weightedJohnson`). -/
structure Parameters (C : GordieHowe.RSCode F N) (A B : ℕ) : Prop where
  k_le_A : C.k ≤ A
  line : RSCode.LineCertificate C A B

variable (S : Setup C P products Lin nL)

/-! ### The system -/

variable {Ctx : Type} (rows : Ctx → Lin → AffineForm F ι) [DecidableEq F]

/-- The input of the proof phase: the context, the encoded rows and the commit rounds. -/
abbrev Input (Ctx : Type) (F : Type) (N R k nrep : ℕ) : Type :=
  FieldProof.CommitProve.Input Ctx (Tableau.Rows F N R nrep) (CommitRounds F R k nrep)

/-- **The verdict**: the tableau verifier on the linear system of the context's rows, the
committed tableau with the masks recombined from its piece rows (`PieceRows.masks`), the
low-degree challenge and response of the commit rounds, and the constraint challenge, masked
responses and query of the proof phase. -/
def verdict (c : Input Ctx F N R C.k S.nrep)
    (tr : (proofSpec F N nL nQ C.k S.t).Transcript (Fin.last 3)) : Bool :=
  Tableau.accept C P (S.linearSystem (rows c.ctx)) c.com (S.pieces.masks C S.t c.com.tableau)
    (ldtChallenge c.rounds, constraintOf tr) (ldtResponse c.rounds, maskedOf tr) (queryOf tr)

/-- **Ligero at agreement threshold `A` with the mask test as a commit-and-prove system** for the
rows `rows` and the products `products` on the setup `S`: the encoded rows (`Tableau.Rows`) as the
oracle message, with their columns as leaves (`Tableau.Rows.column`); the low-degree challenge and response as the commit rounds
(`Ligero.AgreementThreshold.commitSpec`); the cells read from the rows pinned by the low-degree test as the
extracted cells (`Ligero.AgreementThreshold.TableauSetup.extract`); the constraint challenge, masked
responses and column query as the proof phase (`Ligero.AgreementThreshold.proofSpec`), with the tableau
verifier at the recombined masks as verdict (`verdict`). -/
def commitProve : FieldProof.CommitProve F ι products Ctx rows where
  Com := Tableau.Rows F N R S.nrep
  nLeaves := N
  Leaf := Tableau.Column F R S.nrep
  leaf := Tableau.Rows.column
  leaf_injective := Tableau.Rows.column_injective
  ofLeaves := Tableau.Rows.ofColumns
  leaf_ofLeaves := Tableau.Rows.column_ofColumns
  leafDefault := ⟨0, 0⟩
  nc := 2
  commitRounds := AgreementThreshold.commitSpec F R C.k S.nrep
  extract := S.extract
  n := 3
  spec := proofSpec F N nL nQ C.k S.t
  V := verdict S rows
  queries ch := Finset.univ.map (chQuery ch)
  reads c ch O O' r tr htr h := by
    have hq : queryOf tr = chQuery ch := htr (queryIdx F N nL nQ C.k S.t)
    have hl : ∀ s, O.column (queryOf tr s) = O'.column (queryOf tr s) := fun s => by
      rw [hq]
      exact h _ (Finset.mem_map_of_mem _ (Finset.mem_univ s))
    have hU : ∀ row s, O.tableau row (queryOf tr s) = O'.tableau row (queryOf tr s) :=
      fun row s => Tableau.Rows.ldtMatrix_congr (hl s) 0 row
    exact Tableau.accept_congr C P _ hl (fun s => S.pieces.masks_dot_congr fun row => hU row s)
      fun s => S.pieces.masks_quad_congr fun row => hU row s

/-- **The verifier queries `t` leaves** at every challenge vector: the `t` distinct queried
columns. -/
theorem card_queries (ch : (proofSpec F N nL nQ C.k S.t).Challenges) :
    ((commitProve S rows).queries ch).card = S.t := by
  simp [commitProve]

/-! ### Soundness -/

variable (F) in
/-- **The test error**: `1 / |F|` at the constraint challenge, the selected check's event at the
pinned masks (`pinnedBad_count`). -/
noncomputable def testError : ℝ≥0 := 1 / Fintype.card F

/-- **The column error**: `(A − 1).descFactorial t` accepted queries when the agreement set is
small, `(2k − 1).descFactorial t` from the pinned masks otherwise, over the `N.descFactorial t`
queries. -/
noncomputable def columnError : ℝ≥0 :=
  ((S.A - 1).descFactorial S.t + (2 * C.k - 1).descFactorial S.t : ℝ≥0) / N.descFactorial S.t

/-- **The errors of the proof phase**: `testError` at the constraint challenge and `columnError`
at the column query. -/
noncomputable def error : (proofSpec F N nL nQ C.k S.t).ChallengeIdx → ℝ≥0 :=
  proofError (testError F) (columnError S)

omit [Fintype ι] [Fintype Q] [Fintype Lin] [DecidableEq F] in
/-- Every round error of the proof phase is at most `δ` when the test and column errors are. -/
theorem error_le_of {δ : ℝ≥0} (htest : testError F ≤ δ) (hcol : columnError S ≤ δ)
    (i : (proofSpec F N nL nQ C.k S.t).ChallengeIdx) : error S i ≤ δ :=
  proofError_le_of htest hcol i

omit [Fintype ι] [Fintype Q] [Fintype Lin] [DecidableEq F] in
/-- The errors of the proof phase sum to the test and column errors. -/
theorem error_sum : ∑ i, error S i = testError F + columnError S :=
  sum_proofError _ _

/-- **The round errors of Ligero at agreement threshold `A` with the mask test** on a field `F`, at
block length `N`, agreement threshold `A`, exceptional count `B`, dimension `k` and `t` queried
columns: the commit error `(B / (|F| − 1)) ^ nrep` at `nrep` repetitions, the test error
`1 / |F|` and the column error `((A − 1).descFactorial t + (2k − 1).descFactorial t) / N.descFactorial t` (those of
`Ligero.AgreementThreshold.Threshold.commitError`, `testError` and `columnError` at a setup with these
numbers). -/
noncomputable def bounds (F : Type) [Fintype F] (N A B nrep k t : ℕ) :
    Ligero.AgreementThreshold.Bounds :=
  ⟨((B : ℝ≥0) / (Fintype.card F - 1)) ^ nrep, 1 / Fintype.card F,
    ((A - 1).descFactorial t + (2 * k - 1).descFactorial t : ℝ≥0) / N.descFactorial t⟩

/-- **With one repetition the commit error** is `B / (|F| − 1)`. -/
@[simp] theorem bounds_commit_one (F : Type) [Fintype F] (N A B k t : ℕ) :
    (bounds F N A B 1 k t).commit = (B : ℝ≥0) / (Fintype.card F - 1) :=
  pow_one _

/-- **The claim of the proof phase**: the low-degree challenge was exceptional (the commit phase
was bad, `Ligero.AgreementThreshold.Threshold.eventOccurs_iff`), or the rows hold on the extracted cells. -/
def Claim (c : Input Ctx F N R C.k S.nrep) : Prop :=
  S.Exceptional c.com c.rounds ∨ RowsHold (rows c.ctx) products (S.extract c.com c.rounds)

/-- **The bad constraint challenges**: the selected check's event (`pinnedBad`) on the pinned
rows at the pinned masks, the mask polynomials of the pinned piece rows (`Pieces.poly`). The mask
message `u` of the two-stage test is not read: the masks are
recombined from the tableau. -/
def Bad (c : Input Ctx F N R C.k S.nrep) (_u : Tableau.Aux F N) (rc : ConstraintChallenge F nL nQ) :
    Prop :=
  pinnedBad C P (S.linearSystem (rows c.ctx)) (S.pinnedRows c.com c.rounds)
    (S.pieces.dot.poly C.k S.t (S.pinnedRows c.com c.rounds))
    (S.pieces.quad.poly C.k S.t (S.pinnedRows c.com c.rounds)) rc

/-- The verdict of the two-stage test on the input, the constraint challenge, the masked
responses and the query, at the masks recombined from the tableau. The mask message `u` of the
two-stage test is not read. -/
def testAccept (c : Input Ctx F N R C.k S.nrep) (_u : Tableau.Aux F N)
    (rc : ConstraintChallenge F nL nQ) (p : MaskedResponse F C.k) (q : Tableau.Query N S.t) :
    Bool :=
  Tableau.accept C P (S.linearSystem (rows c.ctx)) c.com (S.pieces.masks C S.t c.com.tableau)
    (ldtChallenge c.rounds, rc) (ldtResponse c.rounds, p) q

omit [Fintype Lin] in
open Classical in
/-- The bad constraint challenges are at most a `testError` fraction. -/
theorem test_count (c : Input Ctx F N R C.k S.nrep) (u : Tableau.Aux F N) :
    ((Finset.univ.filter fun rc => Bad S rows c u rc).card : ℝ≥0) ≤
      testError F * Fintype.card (ConstraintChallenge F nL nQ) := by
  have h := pinnedBad_count C P (S.linearSystem (rows c.ctx)) (S.pinnedRows c.com c.rounds)
    (S.pieces.dot.poly C.k S.t (S.pinnedRows c.com c.rounds))
    (S.pieces.quad.poly C.k S.t (S.pinnedRows c.com c.rounds))
  unfold testError
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by exact_mod_cast Fintype.card_pos (α := F))]
  exact_mod_cast h

open Classical in
/-- **The column count**: when the claim is false and the constraint challenge is not bad, at
most `(A − 1).descFactorial t + (2k − 1).descFactorial t` queries are accepted, whatever the
masked responses. -/
theorem query_count_nat (c : Input Ctx F N R C.k S.nrep) (hc : ¬ Claim S rows c) (u : Tableau.Aux F N)
    (rc : ConstraintChallenge F nL nQ) (hbad : ¬ Bad S rows c u rc) (p : MaskedResponse F C.k) :
    (Finset.univ.filter fun q : Tableau.Query N S.t =>
      Tableau.AcceptProp C P (S.linearSystem (rows c.ctx)) c.com
        (S.pieces.masks C S.t c.com.tableau) (ldtChallenge c.rounds, rc) (ldtResponse c.rounds, p) q).card ≤
      (S.A - 1).descFactorial S.t + (2 * C.k - 1).descFactorial S.t := by
  set D := commonAgreement C c.com (ldtChallenge c.rounds) (ldtResponse c.rounds)
  set L := S.linearSystem (rows c.ctx)
  set fs := S.pinnedRows c.com c.rounds
  have hnot : ¬ S.Exceptional c.com c.rounds := fun h => hc (.inl h)
  by_cases hD : S.A ≤ D.card
  · refine le_trans ?_ (Nat.le_add_left _ _)
    by_cases hp : Tableau.Valid C P L (ldtChallenge c.rounds, rc) (ldtResponse c.rounds, p)
    · have hfalse : ¬ Tableau.Holds C P L fs := by
        intro hh
        apply hc
        right
        rw [TableauSetup.extract_eq]
        exact S.rowsHold_of_holds (rows c.ctx) hh
      have hfs := S.natDegree_pinnedRows_lt c.com c.rounds
      refine le_trans (Finset.card_le_card fun q hq => ?_)
        (selected_query_count_pinned C P L S.rate_le fs hfs
          (S.pieces.dot.natDegree_poly_lt S.t hfs) (S.pieces.quad.natDegree_poly_lt S.t hfs)
          hfalse (ldtChallenge c.rounds, rc) hbad _ hp S.t)
      have ha := (Finset.mem_filter.mp hq).2
      have hagree : ∀ s row, c.com.tableau row (q s) = (fs row).eval (C.D (q s)) := fun s row =>
        S.pinnedRows_agree hnot hD (mem_commonAgreement_of_accept ha s) row
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Tableau.selectedAccept_of_agree C P L c.com.tableau fs (S.pieces.polyMasks C S.t fs) _ _ q
          hagree (fun s => ?_) fun s => ?_⟩
      · have h := S.pieces.masks_dot_eq_of_agree (t := S.t) (hagree s)
        rw [Tableau.Aux.dot, Tableau.Aux.dot] at h
        rw [← h]
        exact ha.2.2.1 s
      · have h := S.pieces.masks_quad_eq_of_agree (t := S.t) (hagree s)
        rw [Tableau.Aux.quad, Tableau.Aux.quad] at h
        rw [← h]
        exact ha.2.2.2 s
    · have he : (Finset.univ.filter fun q : Tableau.Query N S.t =>
          Tableau.AcceptProp C P L c.com (S.pieces.masks C S.t c.com.tableau)
            (ldtChallenge c.rounds, rc) (ldtResponse c.rounds, p) q) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun q _ hq => hp hq.1
      rw [he]
      exact Nat.zero_le _
  · exact le_trans (card_filter_le_of_lt (not_le.mp hD) fun q hq => mem_commonAgreement_of_accept hq)
      (Nat.le_add_right _ _)

open Classical in
/-- The column count as a fraction: at most `columnError` of the queries are accepted. -/
theorem query_count (c : Input Ctx F N R C.k S.nrep) (hc : ¬ Claim S rows c) (u : Tableau.Aux F N)
    (rc : ConstraintChallenge F nL nQ) (hbad : ¬ Bad S rows c u rc) (p : MaskedResponse F C.k) :
    ((Finset.univ.filter fun q : Tableau.Query N S.t =>
      testAccept S rows c u rc p q = true).card : ℝ≥0) ≤
      columnError S * Fintype.card (Tableau.Query N S.t) := by
  have h := query_count_nat S rows c hc u rc hbad p
  rw [← Finset.filter_congr fun q _ => Tableau.accept_eq_true_iff ..] at h
  exact card_le_fraction S.t_le h

/-- **The two-stage test of the proof phase**, round-by-round sound relative to `Claim`: the
constraint challenge costs `testError` (`test_count`), the column query `columnError`
(`query_count`). -/
noncomputable def testProof :
    ClaimProof (TwoStageTest.spec (Tableau.Aux F N) (ConstraintChallenge F nL nQ)
      (MaskedResponse F C.k) (Tableau.Query N S.t)) (Input Ctx F N R C.k S.nrep)
      (TwoStageTest.error (testError F) (columnError S)) :=
  TwoStageTest.proof (Claim S rows) (Bad S rows) (testAccept S rows) (testError F) (columnError S)
    (fun c u _ => test_count S rows c u)
    (fun c u rc p hc hb => query_count S rows c hc u rc hb p)

/-- **Soundness of Ligero at agreement threshold `A` with the mask test** (the paper's Appendix D.5,
Security of Ligero with the mask test): the commit event is that every one of the `nrep` low-degree
challenges is exceptional (`Ligero.AgreementThreshold.Threshold.commitEvent`), of probability at most
`(B / (|F| − 1)) ^ nrep`; the proof phase is the two-stage test (`testProof`) with the masks
recombined from the tableau's piece rows (`ClaimProof.dropMsg`), round-by-round sound relative to
"the commit phase was bad or the rows hold on the extracted cells", with the errors `error`:
`1 / |F|` at the constraint challenge and
`((A − 1).descFactorial t + (2k − 1).descFactorial t) / N.descFactorial t` at the column query. -/
noncomputable def sound : (commitProve S rows).Sound (fun _ => S.commitError) (error S) where
  commitEvent := S.commitEvent id
  commitEvent_bound := S.commitEvent_bound id
  proof := ((testProof S rows).dropMsg (maskRound_dir F N nL nQ C.k S.t) id
    fun c => S.pieces.masks C S.t c.com.tableau).ofFintype _ _
  V_eq _ _ := rfl
  claim_iff _ := or_congr_left S.eventOccurs_iff.symm

end

end GordieHowe.Ligero.MaskTest.Pieces
