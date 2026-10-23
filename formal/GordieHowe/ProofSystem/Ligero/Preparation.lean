-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Ligero.Tableau
public import GordieHowe.ProofSystem.Ligero.UntestedMaskRow
public import GordieHowe.ProofSystem.Ligero.Routing
public import GordieHowe.Foundations.Algebra.AffineCoordinates
public import GordieHowe.Foundations.Algebra.AffineForm

@[expose] public section

/-!
# Preparing affine equations and fixed products in a Ligero tableau

Every source variable and multiplication copy has an explicit tableau slot.
Public linear rows are calculated from polynomial coefficients, including
routing coefficients, rather than supplied with a semantic correspondence
hypothesis. Fixed product-row checks then imply the original source products.
Unused product slots may impose extra conditions, so the main result is a
soundness implication, not an unsupported completeness equivalence.
-/

namespace GordieHowe.Ligero

/-- Locations of variables among the systematic message coordinates: the row and the message node
of each variable. Distinct message nodes define one interpolation block; several variables may
read the same row and column. -/
structure Readout (F : Type) (R : ℕ) (ι : Type) where
  /-- The number of message nodes. -/
  nMessage : ℕ
  /-- The message nodes. -/
  messagePoint : Fin nMessage → F
  /-- The message nodes are distinct. -/
  messagePoint_injective : Function.Injective messagePoint
  /-- The row of each variable. -/
  row : ι → Fin R
  /-- The message node of each variable. -/
  column : ι → Fin nMessage

/-- The systematic message node selected for a variable. -/
def Readout.point {F ι : Type} {R : ℕ} (A : Readout F R ι) (i : ι) : F :=
  A.messagePoint (A.column i)

end GordieHowe.Ligero

namespace GordieHowe.Ligero.Preparation
open IOP

open MvPolynomial
open scoped Classical

section

variable {F ι Q Lin : Type} [Field F] [Fintype ι] [Fintype Q] [Fintype Lin]
    {N R nL nQ : ℕ} {C : GordieHowe.RSCode F N}
    {P : Tableau.Parameters (R := R) (nQ := nQ) C}

/-- Fixed source and multiplication-copy locations. No source variable occupies
the ILDT mask row or a privacy column. Locations need not be injective. -/
structure Placement (C : GordieHowe.RSCode F N)
    (P : Tableau.Parameters (R := R) (nQ := nQ) C) (ι Q : Type) where
  /-- The row and column of each source variable. -/
  source : ι → Fin (R + 1) × Fin C.k
  /-- No source variable is on the ILDT row. -/
  source_nonzero : ∀ i, (source i).1 ≠ 0
  /-- Every source variable is at a witness position. -/
  source_witness : ∀ i, (source i).2 ∈ P.witness
  /-- The product group whose X, Y, Z rows hold the copies of each product. -/
  copyGroup : Q → Fin nQ
  /-- The column of each product's copies in its group's rows. -/
  copyCol : Q → Fin C.k
  /-- Every copy is at a witness position. -/
  copy_witness : ∀ q, copyCol q ∈ P.witness
  /-- No product row is the ILDT row. -/
  product_nonzero : ∀ q s, P.products (copyGroup q) s ≠ 0

namespace Placement

variable (A : Placement C P ι Q)

/-- The row and column of each prepared coordinate: a source variable's position, or a copy's
group row and column. -/
def location : Routing.Prepared ι Q → Fin (R + 1) × Fin C.k :=
  Sum.elim A.source (fun qs => (P.products (A.copyGroup qs.1) qs.2, A.copyCol qs.1))

omit [Fintype ι] [Fintype Q] in
theorem location_nonzero (i : Routing.Prepared ι Q) : (A.location i).1 ≠ 0 := by
  cases i with
  | inl i => exact A.source_nonzero i
  | inr qs => exact A.product_nonzero qs.1 qs.2

omit [Fintype ι] [Fintype Q] in
theorem location_witness (i : Routing.Prepared ι Q) : (A.location i).2 ∈ P.witness := by
  cases i with
  | inl i => exact A.source_witness i
  | inr qs => exact A.copy_witness qs.1

/-- The value of a prepared coordinate read from the row polynomials: its row's polynomial at its
column's message node. -/
def readout (fs : Fin (R + 1) → Polynomial F) (i : Routing.Prepared ι Q) : F :=
  (fs (A.location i).1).eval (P.nodes (A.location i).2)

/-- The value of a source variable read from the row polynomials. -/
def sourceReadout (fs : Fin (R + 1) → Polynomial F) (i : ι) : F :=
  (fs (A.source i).1).eval (P.nodes (A.source i).2)

/-- The source coordinates as the common systematic-message readout. -/
def messageReadout : Ligero.Readout F (R + 1) ι where
  nMessage := C.k
  messagePoint := P.nodes
  messagePoint_injective := P.nodes_injective
  row i := (A.source i).1
  column i := (A.source i).2

end Placement

variable (A : Placement C P ι Q) (products : Routing.ProductLayout ι Q)
    (linear : Lin → MvPolynomial ι F) (hlinear : ∀ l, (linear l).totalDegree ≤ 1)
    (index : Fin nL ≃ Routing.PreparedRow Lin Q)

/-- Original affine rows and linear copy-routing rows. -/
noncomputable def equation : Routing.PreparedRow Lin Q → MvPolynomial (Routing.Prepared ι Q) F
  | .linear l => rename Sum.inl (linear l)
  | .copy q s => Routing.routingPolynomial products q s

omit [Fintype ι] [Fintype Q] [Fintype Lin] in
include hlinear in
theorem equation_degree (e : Routing.PreparedRow Lin Q) :
    (equation products linear e).totalDegree ≤ 1 := by
  cases e with
  | linear l => exact (totalDegree_rename_le _ _).trans (hlinear l)
  | copy q s => exact Routing.routingPolynomial_degree products q s

/-- Accumulated coefficients vanish at slots occupied by no variable. -/
theorem coeffAt_zero_of_unoccupied {α Row Col : Type} [Fintype α] [DecidableEq Row]
    [DecidableEq Col]
    (loc : α → Row × Col) (coeff : α → F) (row : Row) (col : Col)
    (h : ∀ i, loc i ≠ (row, col)) : AffineCoordinates.coeffAt loc coeff row col = 0 := by
  simp [AffineCoordinates.coeffAt, h]

/-- Compute every public linear coefficient and target directly. -/
noncomputable def linearSystem : Tableau.LinearSystem (nL := nL) C P where
  coeff l := AffineCoordinates.coeffAt A.location
    (AffineCoordinates.weight (equation products linear (index l)))
  target l := -(equation products linear (index l)).constantCoeff
  privacy_zero l row j hj := coeffAt_zero_of_unoccupied A.location _ row j (by
    intro i heq
    have hcol := congrArg Prod.snd heq
    apply hj
    simpa only [hcol] using A.location_witness i)
  ildt_zero l j := coeffAt_zero_of_unoccupied A.location _ 0 j (by
    intro i heq
    exact A.location_nonzero i (congrArg Prod.fst heq))

/-- **The prepared rows as affine forms** on the prepared coordinates: an original row `l` on
the source coordinates, or the copy-routing row of operand `s` of product `q` (`+1` on the copy,
`-1` on its source). The forms of the polynomials `equation` (`equationForm_toMvPolynomial`). -/
def equationForm (rows : Lin → AffineForm F ι) :
    Routing.PreparedRow Lin Q → AffineForm F (Routing.Prepared ι Q)
  | .linear l => (rows l).rename Sum.inl
  | .copy q s => AffineForm.var (.inr (q, s)) - AffineForm.var (.inl (products.source q s))

omit [Fintype ι] [Fintype Q] [Fintype Lin] in
theorem equationForm_toMvPolynomial (rows : Lin → AffineForm F ι)
    (e : Routing.PreparedRow Lin Q) :
    (equationForm products rows e).toMvPolynomial =
      equation products (fun l => (rows l).toMvPolynomial) e := by
  cases e with
  | linear l => simp [equationForm, equation]
  | copy q s => simp [equationForm, equation, Routing.routingPolynomial]

/-- **The prepared linear system of rows given as affine forms**: each prepared row's
coefficients accumulated at the placement's slots (`AffineForm.coeffAt`) and its constant,
computed from the forms' terms. It is the polynomial system `linearSystem` of the forms'
polynomials (`formSystem_eq`). -/
def formSystem (rows : Lin → AffineForm F ι) : Tableau.LinearSystem (nL := nL) C P where
  coeff l := (equationForm products rows (index l)).coeffAt A.location
  target l := -(equationForm products rows (index l)).const
  privacy_zero l row j hj := by
    rw [AffineForm.coeffAt_eq, equationForm_toMvPolynomial]
    exact (linearSystem A products (fun l => (rows l).toMvPolynomial) index).privacy_zero l row j hj
  ildt_zero l j := by
    rw [AffineForm.coeffAt_eq, equationForm_toMvPolynomial]
    exact (linearSystem A products (fun l => (rows l).toMvPolynomial) index).ildt_zero l j

omit [Fintype Lin] in
theorem formSystem_eq (rows : Lin → AffineForm F ι) :
    formSystem A products index rows =
      linearSystem A products (fun l => (rows l).toMvPolynomial) index := by
  have hc : (formSystem A products index rows).coeff =
      (linearSystem A products (fun l => (rows l).toMvPolynomial) index).coeff := by
    funext l row col
    change (equationForm products rows (index l)).coeffAt A.location row col = _
    rw [AffineForm.coeffAt_eq, equationForm_toMvPolynomial]
    rfl
  have ht : (formSystem A products index rows).target =
      (linearSystem A products (fun l => (rows l).toMvPolynomial) index).target := by
    funext l
    change -(equationForm products rows (index l)).const = -(equation products _ (index l)).constantCoeff
    rw [← equationForm_toMvPolynomial, AffineForm.constantCoeff_toMvPolynomial]
  cases h : formSystem A products index rows
  cases h' : linearSystem A products (fun l => (rows l).toMvPolynomial) index
  rw [h, h'] at hc ht
  cases hc
  cases ht
  rfl

/-- Privacy-zero coefficient rows allow the W-only verifier functional to be
written as an all-message-node sum. -/
theorem dotCheck_eq_full_sum
    (L : Tableau.LinearSystem (nL := nL) C P)
    (fs : Fin (R + 1) → Polynomial F) (l : Fin nL) :
    Tableau.dotCheck C P (Tableau.dotPolynomials C P L fs l) =
      ∑ row, ∑ j, L.coeff l row j * (fs row).eval (P.nodes j) := by
  rw [Tableau.dotCheck, Tableau.dotPolynomials,
    LigeroInterpolation.sumEvaluationOn_decodedDot P.nodes_injective]
  apply Finset.sum_congr rfl
  intro row _
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  simp [L.privacy_zero l row j hj]

omit [Fintype Lin] in
include hlinear in
/-- The calculated tableau row is the affine polynomial minus its constant. -/
theorem equation_eval (fs : Fin (R + 1) → Polynomial F) (l : Fin nL) :
    eval (A.readout fs) (equation products linear (index l)) =
      (equation products linear (index l)).constantCoeff +
      Tableau.dotCheck C P
        (Tableau.dotPolynomials C P (linearSystem A products linear index) fs l) := by
  rw [dotCheck_eq_full_sum]
  exact AffineCoordinates.eval_at_locations _ (equation_degree products linear hlinear (index l))
    A.location (fun row j => (fs row).eval (P.nodes j))

omit [Fintype Lin] in
include hlinear in
theorem equation_zero_of_holds (fs : Fin (R + 1) → Polynomial F)
    (h : Tableau.Holds C P (linearSystem A products linear index) fs)
    (e : Routing.PreparedRow Lin Q) : eval (A.readout fs) (equation products linear e) = 0 := by
  have he := equation_eval A products linear hlinear index fs (index.symm e)
  rw [h.1] at he
  simpa [linearSystem] using he

omit [Fintype Lin] in
include hlinear in
/-- Every source affine equation follows from its computed tableau row. -/
theorem affine_of_holds (fs : Fin (R + 1) → Polynomial F)
    (h : Tableau.Holds C P (linearSystem A products linear index) fs) (l : Lin) :
    eval (A.sourceReadout fs) (linear l) = 0 := by
  change eval (fun i => (fs (A.source i).1).eval (P.nodes (A.source i).2)) (linear l) = 0
  simpa [equation, eval_rename, Placement.readout, Placement.sourceReadout,
    Placement.location, Function.comp_def] using
      equation_zero_of_holds A products linear hlinear index fs h (.linear l)

omit [Fintype Lin] in
include hlinear in
/-- Copy equalities are conclusions of the prepared linear equations. -/
theorem routing_of_holds (fs : Fin (R + 1) → Polynomial F)
    (h : Tableau.Holds C P (linearSystem A products linear index) fs) :
    Ligero.Routing products (A.readout fs) := by
  intro q s
  simpa [equation, sub_eq_zero] using
    equation_zero_of_holds A products linear hlinear index fs h (.copy q s)

omit [Fintype Lin] in
/-- The tableau's product check covers each prepared copy at its selected
witness column; unused columns are not needed for this implication. -/
theorem copyProducts_of_holds (fs : Fin (R + 1) → Polynomial F)
    (h : Tableau.Holds C P (linearSystem A products linear index) fs) :
    Routing.CopyProducts (A.readout fs) := by
  intro q
  have hq := h.2 (A.copyCol q) (A.copyGroup q)
  have heq : (fs (P.products (A.copyGroup q) 2)).eval (P.nodes (A.copyCol q)) -
      (fs (P.products (A.copyGroup q) 0)).eval (P.nodes (A.copyCol q)) *
        (fs (P.products (A.copyGroup q) 1)).eval (P.nodes (A.copyCol q)) = 0 := by
    simpa [Tableau.quadCheck, A.copy_witness q, Tableau.quadPolynomials] using hq
  exact (sub_eq_zero.mp heq).symm

include hlinear in
/-- Concrete preparation soundness: all original affine equations and fixed
source products hold on the selected witness coordinates. -/
theorem holds_source (fs : Fin (R + 1) → Polynomial F)
    (h : Tableau.Holds C P (linearSystem A products linear index) fs) :
    (Routing.sourceSystem products linear hlinear).Holds (A.sourceReadout fs) := by
  rw [Routing.sourceSystem_holds_iff]
  refine ⟨affine_of_holds A products linear hlinear index fs h, ?_⟩
  exact (Routing.copyProducts_iff_sourceProducts
    (routing_of_holds A products linear hlinear index fs h)).mp
      (copyProducts_of_holds A products linear index fs h)

end

end GordieHowe.Ligero.Preparation
