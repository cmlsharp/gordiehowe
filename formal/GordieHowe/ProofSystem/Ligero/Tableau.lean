-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Ligero.Interpolation
public import GordieHowe.ProofSystem.Ligero.MaskedConstraintFamily
public import GordieHowe.ProofSystem.Ligero.MaskedPolynomialTest
public import GordieHowe.ProofSystem.Ligero.AffineCodeTest
public import GordieHowe.ProofSystem.Ligero.TwoStageTest
public import GordieHowe.Foundations.ReedSolomon.Decoder
public import GordieHowe.Foundations.ToMathlib.DegreeLT

@[expose] public section

/-!
# Longfellow's prepared Ligero tableau

The low-degree test uses ILDT with fixed coefficient one. Linear checks use
public coefficient rows interpolated from zero privacy coordinates and witness
coefficients. Their response is checked by summing only the witness positions.
Quadratic triples share coefficients across all witness positions. IDOT and
IQUAD are arbitrary mask oracles, never assumed honestly generated.

Specification follows `ligero_verifier.h` and `LigeroCommon::layout_Aext`.
The oracle model omits Merkle authentication and byte-level transcript encoding.
-/

namespace GordieHowe.Ligero.Tableau
open IOP

open Polynomial
open scoped Classical NNReal
section

variable {F : Type} [Field F] {N R nL nQ : ℕ}

/-- Fixed message domain and witness-position subset. Rows include ILDT at zero;
private and routed product rows are addressed by the remaining row selectors. -/
structure Parameters (C : GordieHowe.RSCode F N) where
  /-- The message nodes: row position `j` holds the value of the row polynomial at `nodes j`. -/
  nodes : Fin C.k → F
  /-- The message nodes are distinct. -/
  nodes_injective : Function.Injective nodes
  /-- The witness positions of each row; the other positions hold the privacy coordinates. -/
  witness : Finset (Fin C.k)
  /-- The rows `(x, y, z)` of each quadratic triple `z = x · y`. -/
  products : Fin nQ → Fin 3 → Fin (R + 1)

/-- Public linear coefficients are zero outside the witness part of each row.
The first row is the ILDT mask and carries no linear-constraint coefficient. -/
structure LinearSystem (C : GordieHowe.RSCode F N) (P : Parameters (R := R) (nQ := nQ) C) where
  /-- The coefficient of equation `l` at position `j` of row `row`. -/
  coeff : Fin nL → Fin (R + 1) → Fin C.k → F
  /-- The right-hand side of equation `l`. -/
  target : Fin nL → F
  /-- The coefficients vanish outside the witness positions. -/
  privacy_zero : ∀ l row j, j ∉ P.witness → coeff l row j = 0
  /-- The coefficients vanish on the ILDT row. -/
  ildt_zero : ∀ l j, coeff l 0 j = 0

variable (C : GordieHowe.RSCode F N) (P : Parameters (R := R) (nQ := nQ) C)
    (L : LinearSystem (nL := nL) C P)

/-- Univariate polynomial for each public linear equation. -/
noncomputable def dotPolynomials (fs : Fin (R + 1) → F[X]) (l : Fin nL) : F[X] :=
  LigeroInterpolation.decodedDot P.nodes (L.coeff l) fs

/-- The implementation batches `z-x*y` for each fixed triple of rows. -/
noncomputable def quadPolynomials (fs : Fin (R + 1) → F[X]) (q : Fin nQ) : F[X] :=
  fs (P.products q 2) - fs (P.products q 0) * fs (P.products q 1)

/-- The linear check of a linear response polynomial: the sum of its values at the witness
nodes. -/
def dotCheck : F[X] →ₗ[F] F := LigeroInterpolation.sumEvaluationOn P.nodes P.witness

/-- All witness positions share the same quadratic coefficient vector. -/
noncomputable def quadCheck (j : Fin C.k) : F[X] →ₗ[F] F :=
  if j ∈ P.witness then
    { toFun := fun p => p.eval (P.nodes j)
      map_add' := fun _ _ => Polynomial.eval_add
      map_smul' := fun _ _ => by simp }
  else 0

/-- **The quadratic checks vanish** exactly when the polynomial vanishes at every witness node. -/
theorem quadCheck_eq_zero_iff (p : F[X]) :
    (∀ j, quadCheck C P j p = 0) ↔ ∀ j ∈ P.witness, p.eval (P.nodes j) = 0 := by
  refine ⟨fun h j hj => ?_, fun h j => ?_⟩
  · have := h j
    simp only [quadCheck, hj, if_true] at this
    exact this
  · by_cases hj : j ∈ P.witness
    · simp only [quadCheck, hj, if_true]
      exact h j hj
    · simp only [quadCheck, hj, if_false, LinearMap.zero_apply]

/-- **The row polynomials satisfy the system**: every linear equation's polynomial sums to its
target over the witness nodes, and every quadratic triple's polynomial vanishes at every witness
node. -/
def Holds (fs : Fin (R + 1) → F[X]) : Prop :=
  (∀ l, dotCheck C P (dotPolynomials C P L fs l) = L.target l) ∧
  MaskedConstraintFamily.Claim (quadCheck C P) (quadPolynomials C P fs) (fun _ _ => 0)

/-- Public dot source at an actual opened column, before adding the mask. -/
def dotColumn (U : RSCode.Matrix F (R + 1) N) (l : Fin nL) (j : Fin N) : F :=
  ∑ row, LigeroInterpolation.interpolateEval P.nodes (L.coeff l row) (C.D j) * U row j

/-- Quadratic source at an actual opened column, before adding the mask: `z − x · y` of the
triple's rows. -/
def quadColumn (U : RSCode.Matrix F (R + 1) N) (q : Fin nQ) (j : Fin N) : F :=
  U (P.products q 2) j - U (P.products q 0) j * U (P.products q 1) j
 

theorem dot_degree (fs : Fin (R + 1) → F[X])
    (hfs : ∀ row, (fs row).natDegree < C.k) (l : Fin nL) :
    (dotPolynomials C P L fs l).natDegree < 2 * C.k - 1 :=
  LigeroInterpolation.decodedDot_degree C.k_pos P.nodes_injective (L.coeff l) fs hfs

theorem quad_degree (fs : Fin (R + 1) → F[X])
    (hfs : ∀ row, (fs row).natDegree < C.k) (q : Fin nQ) :
    (quadPolynomials C P fs q).natDegree < 2 * C.k - 1 := by
  have ha := hfs (P.products q 0)
  have hb := hfs (P.products q 1)
  have hc := hfs (P.products q 2)
  have hk := C.k_pos
  apply (Polynomial.natDegree_sub_le _ _).trans_lt
  apply max_lt
  · omega
  · exact Polynomial.natDegree_mul_le.trans_lt (by omega)

/-- Interpolating the verifier's batched public coefficient row equals batching
its individual interpolants, including zero privacy entries. -/
theorem interpolate_batch (r : Fin nL → F) (row : Fin (R + 1)) :
    LigeroInterpolation.interpolate P.nodes (∑ l, r l • L.coeff l row) =
      ∑ l, Polynomial.C (r l) * LigeroInterpolation.interpolate P.nodes (L.coeff l row) := by
  simp only [map_sum, map_smul, Polynomial.smul_eq_C_mul]

/-- **A pair of mask rows**: the IDOT and IQUAD mask rows of length `N`. -/
abbrev Aux (F : Type) (N : ℕ) := (Fin N → F) × (Fin N → F)

/-- The IDOT mask row of a mask pair. -/
abbrev Aux.dot {F : Type} {N : ℕ} (u : Aux F N) : Fin N → F := u.1

/-- The IQUAD mask row of a mask pair. -/
abbrev Aux.quad {F : Type} {N : ℕ} (u : Aux F N) : Fin N → F := u.2

/-! ### The encoded rows with `nrep` low-degree repetitions

The low-degree test runs `nrep` independent repetitions in one commit round.
Repetition `j` has its own ILDT row `ILDT_j`, with coefficient one in repetition `j`'s
combination only. The encoded rows are the `nrep` ILDT rows and the `R` data rows (`Rows`).
Repetition `j` combines the matrix `ILDT_j, data rows` (`Rows.ldtMatrix`), which has the shape
of the single-repetition tableau, so the single-repetition lemmas apply to each repetition. The
constraint checks read repetition `0`'s matrix (`Rows.tableau`): row `0` is `ILDT_0`, which no
linear coefficient reads (`LinearSystem.ildt_zero`), and the data rows follow. In the C++ the
`nrep` ILDT rows are the tableau's first rows, followed by the other rows in their order. -/

/-- **The encoded rows of a tableau with `nrep` low-degree repetitions**: the ILDT row of each
repetition and the `R` data rows. -/
@[ext] structure Rows (F : Type) (N R nrep : ℕ) where
  /-- The ILDT row of each repetition. -/
  ildt : Fin nrep → Fin N → F
  /-- The data rows. -/
  data : RSCode.Matrix F R N

namespace Rows

variable {F : Type} {N R nrep : ℕ}

/-- **The matrix of repetition `j`**: its ILDT row `ILDT_j`, then the data rows. The low-degree
test of repetition `j` combines its rows (`AffineCodeTest.projection`). -/
def ldtMatrix (O : Rows F N R nrep) (j : Fin nrep) : RSCode.Matrix F (R + 1) N :=
  Fin.cons (O.ildt j) O.data

@[simp] theorem ldtMatrix_zero (O : Rows F N R nrep) (j : Fin nrep) :
    O.ldtMatrix j 0 = O.ildt j :=
  rfl

@[simp] theorem ldtMatrix_succ (O : Rows F N R nrep) (j : Fin nrep) (i : Fin R) :
    O.ldtMatrix j i.succ = O.data i :=
  rfl

/-- **The tableau the constraint checks read**: repetition `0`'s matrix, `ILDT_0` at row `0`
(read by no linear coefficient, `LinearSystem.ildt_zero`) and the data rows. -/
def tableau [NeZero nrep] (O : Rows F N R nrep) : RSCode.Matrix F (R + 1) N :=
  O.ldtMatrix 0

@[simp] theorem tableau_zero [NeZero nrep] (O : Rows F N R nrep) : O.tableau 0 = O.ildt 0 :=
  rfl

@[simp] theorem tableau_succ [NeZero nrep] (O : Rows F N R nrep) (i : Fin R) :
    O.tableau i.succ = O.data i :=
  rfl

/-- **The rows with one repetition are a tableau**: `ILDT_0` and the data rows as one matrix of
`R + 1` rows (`tableau`). -/
def equivMatrix : Rows F N R 1 ≃ RSCode.Matrix F (R + 1) N where
  toFun O := O.tableau
  invFun U := ⟨fun _ => U 0, Fin.tail U⟩
  left_inv O := by
    ext j
    · rw [Subsingleton.elim j 0]
      rfl
    · rfl
  right_inv U := Fin.cons_self_tail U

@[simp] theorem equivMatrix_apply (O : Rows F N R 1) : equivMatrix O = O.tableau :=
  rfl

end Rows

/-- **A column of the encoded rows**: the `nrep` ILDT entries and the `R` data entries. -/
@[ext] structure Column (F : Type) (R nrep : ℕ) where
  /-- The ILDT entries, one per repetition. -/
  ildt : Fin nrep → F
  /-- The data entries. -/
  data : Fin R → F

/-- **A column as one array**: the `nrep` ILDT entries, then the data entries (the C++ leaf
order of the encoded rows). -/
def Column.equivFin {F : Type} {R nrep : ℕ} : Column F R nrep ≃ (Fin (nrep + R) → F) where
  toFun c := Fin.append c.ildt c.data
  invFun v := ⟨fun j => v (Fin.castAdd R j), fun i => v (Fin.natAdd nrep i)⟩
  left_inv c := by
    ext j
    · exact Fin.append_left _ _ j
    · exact Fin.append_right _ _ j
  right_inv v := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Fin.append_left _ _ j
    · exact Fin.append_right _ _ j

/-- **The column of the encoded rows at `j`**: every row's entry at `j`. -/
def Rows.column {F : Type} {N R nrep : ℕ} (O : Rows F N R nrep) (j : Fin N) : Column F R nrep :=
  ⟨fun r => O.ildt r j, fun i => O.data i j⟩

theorem Rows.column_injective {F : Type} {N R nrep : ℕ} :
    Function.Injective (Rows.column (F := F) (N := N) (R := R) (nrep := nrep)) := by
  intro O O' h
  refine Rows.ext (funext fun r => funext fun j => ?_) (funext fun i => funext fun j => ?_)
  · exact congrFun (congrArg Column.ildt (congrFun h j)) r
  · exact congrFun (congrArg Column.data (congrFun h j)) i

/-- The encoded rows with the given columns. -/
def Rows.ofColumns {F : Type} {N R nrep : ℕ} (l : Fin N → Column F R nrep) : Rows F N R nrep :=
  ⟨fun r j => (l j).ildt r, fun i j => (l j).data i⟩

theorem Rows.column_ofColumns {F : Type} {N R nrep : ℕ} (l : Fin N → Column F R nrep) :
    Rows.column (Rows.ofColumns l) = l :=
  rfl

/-- **The entries of every repetition's matrix at a column are read off the column**: two encoded
rows with equal columns at `j` have equal matrices at `j`. -/
theorem Rows.ldtMatrix_congr {F : Type} {N R nrep : ℕ} {O O' : Rows F N R nrep} {j : Fin N}
    (h : O.column j = O'.column j) (r : Fin nrep) (row : Fin (R + 1)) :
    O.ldtMatrix r row j = O'.ldtMatrix r row j := by
  refine Fin.cases ?_ (fun i => ?_) row
  · exact congrFun (congrArg Column.ildt h) r
  · exact congrFun (congrArg Column.data h) i

/-- **The tableau column of a column**: `ILDT_0`'s entry, then the data entries (the column of
`Rows.tableau`, `Rows.column_tableau`). -/
def Column.tableau {F : Type} {R nrep : ℕ} [NeZero nrep] (c : Column F R nrep) : Fin (R + 1) → F :=
  Fin.cons (c.ildt 0) c.data

theorem Rows.column_tableau {F : Type} {N R nrep : ℕ} [NeZero nrep] (O : Rows F N R nrep)
    (j : Fin N) : (O.column j).tableau = fun row => O.tableau row j := by
  funext row
  exact Fin.cases rfl (fun _ => rfl) row

/-- **A Ligero commitment**: the encoded rows (`Rows`) and the IDOT and IQUAD mask rows. -/
@[ext] structure Commitment (F : Type) (N R nrep : ℕ) where
  /-- The encoded rows. -/
  rows : Rows F N R nrep
  /-- The IDOT and IQUAD mask rows. -/
  masks : Aux F N

/-- The tableau of a commitment that the constraint checks read (`Rows.tableau`). -/
abbrev Commitment.tableau {F : Type} {N R nrep : ℕ} [NeZero nrep] (O : Commitment F N R nrep) :
    RSCode.Matrix F (R + 1) N :=
  O.rows.tableau

/-- **A leaf of a commitment**: a column of the encoded rows and the two mask entries. -/
structure Leaf (F : Type) (R nrep : ℕ) where
  /-- The column of the encoded rows. -/
  column : Column F R nrep
  /-- The IDOT mask entry. -/
  dotMask : F
  /-- The IQUAD mask entry. -/
  quadMask : F

/-- A leaf as its column (one array, `Column.equivFin`) and its two mask entries, for its
codec. -/
def Leaf.equivProd {F : Type} {R nrep : ℕ} : Leaf F R nrep ≃ (Fin (nrep + R) → F) × (F × F) where
  toFun l := (Column.equivFin l.column, l.dotMask, l.quadMask)
  invFun x := ⟨Column.equivFin.symm x.1, x.2.1, x.2.2⟩
  left_inv l := by simp
  right_inv x := by simp

namespace Commitment

/-- The leaves of a commitment: column `j` of the encoded rows with the masks' entries at `j`. -/
def leaf {F : Type} {N R nrep : ℕ} (O : Commitment F N R nrep) (j : Fin N) : Leaf F R nrep :=
  ⟨O.rows.column j, O.masks.dot j, O.masks.quad j⟩

theorem leaf_injective {F : Type} {N R nrep : ℕ} :
    Function.Injective (leaf (F := F) (N := N) (R := R) (nrep := nrep)) := by
  intro O O' h
  refine Commitment.ext (Rows.column_injective (funext fun j => congrArg Leaf.column (congrFun h j)))
    (Prod.ext (funext fun j => ?_) (funext fun j => ?_))
  · exact congrArg Leaf.dotMask (congrFun h j)
  · exact congrArg Leaf.quadMask (congrFun h j)

/-- The commitment with the given leaves: the encoded rows and the masks read off the leaves. -/
def ofLeaves {F : Type} {N R nrep : ℕ} (l : Fin N → Leaf F R nrep) : Commitment F N R nrep :=
  ⟨Rows.ofColumns fun j => (l j).column, (fun j => (l j).dotMask, fun j => (l j).quadMask)⟩

theorem leaf_ofLeaves {F : Type} {N R nrep : ℕ} (l : Fin N → Leaf F R nrep) :
    leaf (ofLeaves l) = l :=
  rfl

end Commitment

/-- **The low-degree challenges**: for each of the `nrep` repetitions, the coefficients of the
`R` data rows (`ILDT_j` has coefficient one). Repetition-major, as the C++ draws them. -/
abbrev LdtChallenge (F : Type) (R nrep : ℕ) := Fin nrep → Fin R → F

/-- **The low-degree responses**: for each repetition, the values of a polynomial of degree `< k`
at the first `k` response nodes. Repetition-major, as the C++ writes them. -/
abbrev LdtResponse (F : Type) (k nrep : ℕ) := Fin nrep → Fin k → F

/-- **The low-degree responses as one array** of `nrep · k` elements, repetition-major: the
element `i` of repetition `j` at position `j · k + i` (`finProdFinEquiv`). The C++ writes them in
this order. -/
def LdtResponse.equivFin {F : Type} {k nrep : ℕ} : LdtResponse F k nrep ≃ (Fin (nrep * k) → F) :=
  (Equiv.curry (Fin nrep) (Fin k) F).symm.trans (Equiv.arrowCongr finProdFinEquiv (Equiv.refl F))

/-- **The challenge round**: the low-degree challenges (`LdtChallenge`), and the batching
coefficients of the linear equations and of the quadratic triples. -/
abbrev Challenge (F : Type) (R nL nQ nrep : ℕ) :=
  LdtChallenge F R nrep × ((Fin nL → F) × (Fin nQ → F))
/-- **The response round's message**: the low-degree responses (`LdtResponse`, each the values of
a polynomial at the first `k` response nodes) and the values of the linear and quadratic responses
at the first `2k − 1` (`responseNode`: the code's first evaluation points, which in the relative
layout are opened-column points). The C++ sends the same polynomials as their values at the
tableau positions `[0, block)` and `[0, dblock)` (`block = k`, `dblock = 2k − 1`): `y_ldt` for
each repetition, `y_dot` and `y_quad` without its `w` witness-position values (sizes
`lib/ligero/ligero_param.h` lines 335–344; `low_degree_proof`, `dot_proof`, `quadratic_proof`,
`ligero_prover.h` lines 431–494, called at lines 138, 157 and 165–166), and the verifier
re-interpolates them (`ligero_verifier.h` lines 195–206). The two responses correspond by
re-interpolation: `k` (or `2k − 1`) values at distinct points determine a polynomial of degree
below `k` (or `2k − 1`). The values determine the polynomials of the same degree bounds
(`Response.code`, `Response.dot`, `Response.quad`), so the degree bounds are enforced by the
format. The omitted `y_quad` values are those at the witness positions, where the verifier
requires the quadratic polynomial to vanish; the Lean checks the vanishing at the message nodes
(`Valid`, conjunct `quadCheck`). -/
abbrev Response (F : Type) (k nrep : ℕ) :=
  LdtResponse F k nrep × ((Fin (2 * k - 1) → F) × (Fin (2 * k - 1) → F))

/-- **The query round**: `t` distinct opened columns among the `N` columns of the tableau. -/
abbrev Query (N t : ℕ) := Fin t ↪ Fin N

/-- There are `t` distinct query columns among `N` exactly when `t ≤ N`; this is
the direction the protocols use. -/
theorem Query.nonempty_of_le {N t : ℕ} (h : t ≤ N) : Nonempty (Query N t) :=
  ⟨Fin.castLEEmb h⟩

/-- The query sets as a computable finite type: the injective maps `Fin t → Fin N`. Not an
instance; the protocols that run the queries supply it as their challenge type's
enumeration. -/
abbrev Query.fintype (N t : ℕ) : Fintype (Query N t) :=
  Fintype.ofEquiv _ (Equiv.subtypeInjectiveEquivEmbedding (Fin t) (Fin N))

/-- **The response nodes**: the `i`-th point `C.D i` of the code's evaluation domain, for the
first `m` points; zero beyond the domain. In the relative layout `C.D i` is the point of opened
column `i` (`code.D j = P.pt (dblock + j)`), not a C++ interpolation point; the responses
correspond to the C++ ones by re-interpolation (`Response`). -/
def responseNode (m : ℕ) (i : Fin m) : F := if h : (i : ℕ) < N then C.D ⟨i, h⟩ else 0

theorem responseNode_injective {m : ℕ} (hm : m ≤ N) : Function.Injective (responseNode C m) := by
  intro i j h
  simp only [responseNode, dif_pos (lt_of_lt_of_le i.isLt hm),
    dif_pos (lt_of_lt_of_le j.isLt hm)] at h
  exact Fin.ext (by simpa using congrArg Fin.val (C.D_injective h))

theorem k_le_N : C.k ≤ N := by have := C.radius; omega

variable {nrep : ℕ}

/-- The low-degree response polynomial of repetition `j`: the interpolant of its values on the
response nodes. -/
noncomputable def Response.code (p : Response F C.k nrep) (j : Fin nrep) : F[X] :=
  LigeroInterpolation.interpolate (responseNode C C.k) (p.1 j)

/-- The linear response polynomial. -/
noncomputable def Response.dot (p : Response F C.k nrep) : F[X] :=
  LigeroInterpolation.interpolate (responseNode C (2 * C.k - 1)) p.2.1

/-- The quadratic response polynomial. -/
noncomputable def Response.quad (p : Response F C.k nrep) : F[X] :=
  LigeroInterpolation.interpolate (responseNode C (2 * C.k - 1)) p.2.2

/-- The low-degree response of repetition `j` at `x`, by field operations. -/
def Response.codeEval (p : Response F C.k nrep) (j : Fin nrep) (x : F) : F :=
  LigeroInterpolation.interpolateEval (responseNode C C.k) (p.1 j) x

/-- The linear response's value at `x`, by field operations. -/
def Response.dotEval (p : Response F C.k nrep) (x : F) : F :=
  LigeroInterpolation.interpolateEval (responseNode C (2 * C.k - 1)) p.2.1 x

/-- The quadratic response's value at `x`, by field operations. -/
def Response.quadEval (p : Response F C.k nrep) (x : F) : F :=
  LigeroInterpolation.interpolateEval (responseNode C (2 * C.k - 1)) p.2.2 x

theorem Response.eval_code (p : Response F C.k nrep) (j : Fin nrep) (x : F) :
    (p.code C j).eval x = p.codeEval C j x :=
  LigeroInterpolation.eval_interpolate _ _ _

theorem Response.eval_dot (p : Response F C.k nrep) (x : F) :
    (p.dot C).eval x = p.dotEval C x :=
  LigeroInterpolation.eval_interpolate _ _ _

theorem Response.eval_quad (p : Response F C.k nrep) (x : F) :
    (p.quad C).eval x = p.quadEval C x :=
  LigeroInterpolation.eval_interpolate _ _ _

/-- Each low-degree response has degree below `k`. -/
theorem Response.natDegree_code_lt (p : Response F C.k nrep) (j : Fin nrep) :
    (p.code C j).natDegree < C.k :=
  LigeroInterpolation.interpolate_degree C.k_pos (responseNode_injective C (k_le_N C)) _

/-- The linear response has degree below `2k − 1`. -/
theorem Response.natDegree_dot_lt (hrate : 2 * C.k - 1 ≤ N) (p : Response F C.k nrep) :
    (p.dot C).natDegree < 2 * C.k - 1 :=
  LigeroInterpolation.interpolate_degree (by have := C.k_pos; omega)
    (responseNode_injective C (by omega)) _

/-- The quadratic response has degree below `2k − 1`. -/
theorem Response.natDegree_quad_lt (hrate : 2 * C.k - 1 ≤ N) (p : Response F C.k nrep) :
    (p.quad C).natDegree < 2 * C.k - 1 :=
  LigeroInterpolation.interpolate_degree (by have := C.k_pos; omega)
    (responseNode_injective C (by omega)) _

/-- **The response of polynomials**: their values on the response nodes, one low-degree response
`a j` per repetition. For polynomials within the degree bounds it is the inverse of
`Response.code`, `Response.dot`, `Response.quad` (`code_ofPolys`, `dot_ofPolys`,
`quad_ofPolys`). -/
def Response.ofPolys (a : Fin nrep → F[X]) (b c : F[X]) : Response F C.k nrep :=
  (fun j i => (a j).eval (responseNode C C.k i), fun i => b.eval (responseNode C (2 * C.k - 1) i),
    fun i => c.eval (responseNode C (2 * C.k - 1) i))

theorem Response.code_ofPolys {a : Fin nrep → F[X]} (ha : ∀ j, (a j).natDegree < C.k)
    (b c : F[X]) (j : Fin nrep) : (Response.ofPolys C a b c).code C j = a j := by
  symm
  exact Lagrange.eq_interpolate_of_eval_eq _ (responseNode_injective C (k_le_N C)).injOn
    (by rw [Finset.card_univ, Fintype.card_fin]; exact (degree_le_natDegree.trans_lt
      (by exact_mod_cast ha j))) (fun i _ => rfl)

theorem Response.dot_ofPolys (hrate : 2 * C.k - 1 ≤ N) (a : Fin nrep → F[X]) {b : F[X]}
    (hb : b.natDegree < 2 * C.k - 1) (c : F[X]) :
    (Response.ofPolys C a b c).dot C = b := by
  symm
  exact Lagrange.eq_interpolate_of_eval_eq _ (responseNode_injective C (by omega)).injOn
    (by rw [Finset.card_univ, Fintype.card_fin]; exact (degree_le_natDegree.trans_lt
      (by exact_mod_cast hb))) (fun i _ => rfl)

theorem Response.quad_ofPolys (hrate : 2 * C.k - 1 ≤ N) (a : Fin nrep → F[X]) (b : F[X]) {c : F[X]}
    (hc : c.natDegree < 2 * C.k - 1) :
    (Response.ofPolys C a b c).quad C = c := by
  symm
  exact Lagrange.eq_interpolate_of_eval_eq _ (responseNode_injective C (by omega)).injOn
    (by rw [Finset.card_univ, Fintype.card_fin]; exact (degree_le_natDegree.trans_lt
      (by exact_mod_cast hc))) (fun i _ => rfl)

/-- The response's algebraic checks: the linear response sums to the batched targets over the
witness positions, and the quadratic response vanishes at every witness node. Its degree bounds
are in its type (`Response`). -/
def Valid (r : Challenge F R nL nQ nrep) (p : Response F C.k nrep) : Prop :=
  dotCheck C P (p.dot C) = ∑ i, r.2.1 i * L.target i ∧
  ∀ j, quadCheck C P j (p.quad C) = 0

/-- **The low-degree checks at the opened columns**: in every repetition `j`, the combination of
repetition `j`'s matrix by `r j` (ILDT coefficient one) equals the low-degree response `p j`
there. -/
def CodeAccept (O : Rows F N R nrep) (r : LdtChallenge F R nrep) (p : Fin nrep → F[X])
    {t : ℕ} (q : Query N t) : Prop :=
  ∀ j s, AffineCodeTest.projection (O.ldtMatrix j) (r j) (q s) = (p j).eval (C.D (q s))

/-- The linear check at the opened columns: the IDOT mask plus the batched public dot source
equals the linear response there. -/
def DotAccept (U : RSCode.Matrix F (R + 1) N) (u : Fin N → F)
    (r : Fin nL → F) (p : F[X]) {t : ℕ} (q : Query N t) : Prop :=
  ∀ s, u (q s) + ∑ l, r l * dotColumn C P L U l (q s) = p.eval (C.D (q s))

/-- The quadratic check at the opened columns: the IQUAD mask plus the batched quadratic source
equals the quadratic response there. -/
def QuadAccept (U : RSCode.Matrix F (R + 1) N) (u : Fin N → F)
    (r : Fin nQ → F) (p : F[X]) {t : ℕ} (q : Query N t) : Prop :=
  ∀ s, u (q s) + ∑ l, r l * quadColumn C P U l (q s) = p.eval (C.D (q s))

/-- `Valid` by field operations: the witness-position sum of the linear response's values and
its values at the witness nodes of the quadratic response (`valid_iff_validDec`). -/
def ValidDec (r : Challenge F R nL nQ nrep) (p : Response F C.k nrep) : Prop :=
  ∑ j ∈ P.witness, p.dotEval C (P.nodes j) = ∑ i, r.2.1 i * L.target i ∧
  ∀ j, j ∈ P.witness → p.quadEval C (P.nodes j) = 0

theorem valid_iff_validDec (r : Challenge F R nL nQ nrep) (p : Response F C.k nrep) :
    Valid C P L r p ↔ ValidDec C P L r p := by
  unfold Valid ValidDec
  simp only [dotCheck, LigeroInterpolation.sumEvaluationOn_apply, Response.eval_dot]
  refine and_congr Iff.rfl (forall_congr' fun j => ?_)
  by_cases hj : j ∈ P.witness
  · simp [quadCheck, hj, Response.eval_quad]
  · simp [quadCheck, hj]

/-- **Acceptance of a response**, on the response polynomials: the algebraic checks, the
low-degree checks of every repetition, and the linear and quadratic column checks on the tableau
(`Rows.tableau`) at the queried columns. The verifier computes it on the response values
(`accept`, `accept_eq_true_iff`). -/
def AcceptProp [NeZero nrep] (O : Rows F N R nrep) (u : Aux F N)
    (r : Challenge F R nL nQ nrep) (p : Response F C.k nrep) {t : ℕ} (q : Query N t) : Prop :=
  Valid C P L r p ∧ CodeAccept C O r.1 (p.code C) q ∧
    DotAccept C P L O.tableau u.1 r.2.1 (p.dot C) q ∧ QuadAccept C P O.tableau u.2 r.2.2 (p.quad C) q

/-- **The tableau verifier**, computed on the response values: the response's algebraic checks
(`ValidDec`), the low-degree checks of every repetition and the linear and quadratic column
checks at the queried columns, each response evaluated at the column's point by field operations
(`Response.codeEval` and the like). It accepts exactly when the polynomial checks hold
(`accept_eq_true_iff`). -/
def accept [DecidableEq F] [NeZero nrep] (O : Rows F N R nrep) (u : Aux F N)
    (r : Challenge F R nL nQ nrep) (p : Response F C.k nrep) {t : ℕ} (q : Query N t) : Bool :=
  decide ((∑ j ∈ P.witness, p.dotEval C (P.nodes j) = ∑ i, r.2.1 i * L.target i ∧
      ∀ j, j ∈ P.witness → p.quadEval C (P.nodes j) = 0) ∧
    (∀ j s, AffineCodeTest.projection (O.ldtMatrix j) (r.1 j) (q s) =
      p.codeEval C j (C.D (q s))) ∧
    (∀ s, u.1 (q s) + ∑ l, r.2.1 l * dotColumn C P L O.tableau l (q s) =
      p.dotEval C (C.D (q s))) ∧
    (∀ s, u.2 (q s) + ∑ l, r.2.2 l * quadColumn C P O.tableau l (q s) =
      p.quadEval C (C.D (q s))))

theorem accept_eq_true_iff [DecidableEq F] [NeZero nrep] (O : Rows F N R nrep) (u : Aux F N)
    (r : Challenge F R nL nQ nrep) (p : Response F C.k nrep) {t : ℕ} (q : Query N t) :
    accept C P L O u r p q = true ↔ AcceptProp C P L O u r p q := by
  rw [accept, decide_eq_true_iff, AcceptProp, valid_iff_validDec]
  simp only [ValidDec, CodeAccept, DotAccept, QuadAccept, Response.eval_code, Response.eval_dot,
    Response.eval_quad]

/-- `accept` reads the encoded rows and the masks only at the queried columns. -/
theorem accept_congr [DecidableEq F] [NeZero nrep] {O O' : Rows F N R nrep} {u u' : Aux F N}
    {r : Challenge F R nL nQ nrep} {p : Response F C.k nrep} {t : ℕ} {q : Query N t}
    (hO : ∀ s, O.column (q s) = O'.column (q s)) (hdot : ∀ s, u.dot (q s) = u'.dot (q s))
    (hquad : ∀ s, u.quad (q s) = u'.quad (q s)) :
    accept C P L O u r p q = accept C P L O' u' r p q := by
  refine decide_eq_decide.mpr ?_
  simp only [Aux.dot, Aux.quad] at hdot hquad
  have hU : ∀ j row s, O.ldtMatrix j row (q s) = O'.ldtMatrix j row (q s) :=
    fun j row s => Rows.ldtMatrix_congr (hO s) j row
  simp only [AffineCodeTest.projection, dotColumn, quadColumn, Rows.tableau, hU, hdot, hquad]

/-! ### The selected test on given rows

The column checks read at queried columns where the rows of the tableau agree with given
polynomials `fs`. Ligero at agreement threshold `A` (`Ligero.AgreementThreshold`, `MaskTest.Pieces`) pins
the rows from the commit phase this way. -/

/-- The public dot source at a column where every row of `U` is the evaluation of its
polynomial in `fs`: the evaluation of the dot polynomial of `fs`. -/
theorem dotColumn_eq_of_agree (U : RSCode.Matrix F (R + 1) N) (fs : Fin (R + 1) → F[X])
    {j : Fin N} (h : ∀ row, U row j = (fs row).eval (C.D j)) (l : Fin nL) :
    dotColumn C P L U l j = (dotPolynomials C P L fs l).eval (C.D j) := by
  simp only [dotColumn, dotPolynomials, LigeroInterpolation.decodedDot,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, h, LigeroInterpolation.eval_interpolate]

/-- The quadratic source at a column where every row of `U` is the evaluation of its
polynomial in `fs`: the evaluation of the quadratic polynomial of `fs`. -/
theorem quadColumn_eq_of_agree (U : RSCode.Matrix F (R + 1) N) (fs : Fin (R + 1) → F[X])
    {j : Fin N} (h : ∀ row, U row j = (fs row).eval (C.D j)) (q : Fin nQ) :
    quadColumn C P U q j = (quadPolynomials C P fs q).eval (C.D j) := by
  simp only [quadColumn, quadPolynomials, Polynomial.eval_sub, Polynomial.eval_mul, h]

/-- **Decoded acceptance of the selected family on the rows `fs`**: the linear family's column
identity at every queried column when the linear checks fail on `fs`, else the quadratic
family's. -/
def selectedAccept (fs : Fin (R + 1) → F[X]) (u : Aux F N)
    (r : Challenge F R nL nQ nrep) (p : Response F C.k nrep) {t : ℕ} (q : Query N t) : Prop :=
  if ¬ ∀ l, dotCheck C P (dotPolynomials C P L fs l) = L.target l then
    ∀ s, u.1 (q s) + (MaskedConstraintTest.batch (dotPolynomials C P L fs) r.2.1).eval
      (C.D (q s)) = (p.dot C).eval (C.D (q s))
  else
    ∀ s, u.2 (q s) + (MaskedConstraintTest.batch (quadPolynomials C P fs) r.2.2).eval
      (C.D (q s)) = (p.quad C).eval (C.D (q s))

/-- At queried columns where the rows of `U` are the evaluations of `fs`, the linear and
quadratic column checks give the selected family's acceptance on `fs`. -/
theorem selectedAccept_of_agree (U : RSCode.Matrix F (R + 1) N) (fs : Fin (R + 1) → F[X])
    (u : Aux F N) (r : Challenge F R nL nQ nrep) (p : Response F C.k nrep) {t : ℕ}
    (q : Query N t) (hq : ∀ s row, U row (q s) = (fs row).eval (C.D (q s)))
    (hdot : DotAccept C P L U u.1 r.2.1 (p.dot C) q)
    (hquad : QuadAccept C P U u.2 r.2.2 (p.quad C) q) :
    selectedAccept C P L fs u r p q := by
  by_cases hd : ¬ ∀ l, dotCheck C P (dotPolynomials C P L fs l) = L.target l
  · simp only [selectedAccept, ite_eq_left hd]
    intro s
    simpa only [MaskedConstraintTest.batch, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C, dotColumn_eq_of_agree C P L U fs (hq s)] using
      hdot s
  · simp only [selectedAccept, ite_eq_right hd]
    intro s
    simpa only [MaskedConstraintTest.batch, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_C, quadColumn_eq_of_agree C P U fs (hq s)] using
      hquad s

end

end GordieHowe.Ligero.Tableau
