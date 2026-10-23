-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.Polynomial.OfFn
public import GordieHowe.Foundations.ReedSolomon.SubfieldInterpolation
public import GordieHowe.ProofSystem.Ligero.Completeness
public import GordieHowe.Model.IOP.HVZK

@[expose] public section

/-!
# Perfect honest-verifier zero-knowledge of one Ligero tableau

One prepared Longfellow tableau (`Ligero.Tableau`) is simulated exactly for every
fixed challenge and query set. The honest prover draws:
* the ILDT row's message values, uniform over `F`;
* each data row's privacy values, uniform over that row's blinding field
  (a subfield for subfield rows, `⊤` otherwise);
* the IDOT mask, uniform among polynomials of degree `< 2k − 1` whose
  witness-position sum is zero;
* the IQUAD mask, uniform among those that vanish at every witness node.

The verifier reads the three responses and, at each queried column, every row
entry and both mask entries (`view`). The simulator (`simulate`) samples the
data-row openings uniformly over their blinding fields and the three responses
uniformly over the sets the verifier accepts, then solves the three acceptance
equations for the ILDT, IDOT and IQUAD openings.

The argument follows AHIV17 Lemma 4.15 (ePrint 2022/1608, p. 26), with three
changes. Longfellow runs at `k = ℓ + t`, where the lemma asks `k > ℓ + t`: the
one-row lemma here needs only `t ≤` the number of privacy positions. The
responses are sampled from the accepted sets, where AHIV17 samples the
low-degree response from all of `F^n`. Subfield rows carry subfield blinding;
the three mask rows are full-field and absorb every full-field combination.

The honest prover reads only the blinding fields (`BlindingFields`); its completeness also needs the
parameter condition that no quadratic triple reads the ILDT row (`honest`). The hiding argument adds
parameter conditions and facts about the field in `HidingLayout`:
* every node and every code point lies in each row's blinding field;
* no code point is a witness node;
* at least one witness node exists (the linear response's offset uses it);
* no quadratic triple reads the ILDT row.

The honest input is a witness assignment whose cells lie in their rows'
blinding fields and satisfy the tableau's equations.
-/

namespace GordieHowe.Ligero.HVZK
open IOP

open Polynomial
open scoped Classical
section

variable {F : Type} [Field F] [Fintype F] {N R nL nQ : ℕ}
  {C : GordieHowe.RSCode F N}
  {P : Tableau.Parameters (R := R) (nQ := nQ) C}
  {L : Tableau.LinearSystem (nL := nL) C P}
  {hrate : 2 * C.k - 1 ≤ N}

/-- The privacy positions of a row: the message nodes outside the witness. -/
abbrev Privacy (P : Tableau.Parameters (R := R) (nQ := nQ) C) : Type :=
  {j : Fin C.k // j ∉ P.witness}

/-- The blinding field of each data row: the field its privacy values are drawn
from (a subfield for subfield rows, `⊤` otherwise). This is all the honest
prover reads of a layout (`Coins`, `Cells`, `honest`). -/
structure BlindingFields (C : GordieHowe.RSCode F N)
    (P : Tableau.Parameters (R := R) (nQ := nQ) C) where
  /-- The field a data row's privacy values are drawn from. -/
  field : Fin R → Subfield F
  /-- Membership in each row's blinding field is decidable (the simulator enumerates its
  openings in it). -/
  [decMem : ∀ row, DecidablePred (· ∈ field row)]

attribute [instance] BlindingFields.decMem

variable (C P) in
/-- **The hiding thresholds of a tableau**, parameter conditions on the code and the message nodes:
no code point is a witness node, and the witness part of a row is nonempty. -/
structure HidingParams : Prop where
  /-- No code point is a witness node. -/
  off_witness : ∀ i, ∀ j ∈ P.witness, C.D i ≠ P.nodes j
  /-- The witness part of a row is nonempty. -/
  witness_nonempty : P.witness.Nonempty

variable (C P) in
/-- The blinding fields and the layout facts the hiding argument uses. -/
structure HidingLayout extends BlindingFields C P, HidingParams C P where
  /-- Equality in the field is decidable (the simulator enumerates its mask coins). -/
  decEq : DecidableEq F
  /-- Every message node lies in every row's blinding field. -/
  nodes_mem : ∀ row j, P.nodes j ∈ field row
  /-- Every code point lies in every row's blinding field. -/
  points_mem : ∀ row i, C.D i ∈ field row
  /-- Quadratic triples read data rows only. -/
  products_ne_zero : ∀ q i, P.products q i ≠ 0

omit [Fintype F] in
/-- `Ligero.Tableau.Holds` reads the data rows only through their values at the
witness nodes, and never reads the ILDT row when no quadratic triple does:
the linear coefficients of row 0 are zero (`ildt_zero`). -/
theorem holds_iff_of_eval_witness (hprod : ∀ q i, P.products q i ≠ 0)
    {fs gs : Fin (R + 1) → F[X]}
    (h : ∀ (i : Fin R), ∀ j ∈ P.witness,
      (fs i.succ).eval (P.nodes j) = (gs i.succ).eval (P.nodes j)) :
    Tableau.Holds C P L fs ↔ Tableau.Holds C P L gs := by
  have hdot : ∀ l, Tableau.dotCheck C P (Tableau.dotPolynomials C P L fs l) =
      Tableau.dotCheck C P (Tableau.dotPolynomials C P L gs l) := by
    intro l
    simp only [Tableau.dotCheck, Tableau.dotPolynomials,
      LigeroInterpolation.sumEvaluationOn_decodedDot P.nodes_injective]
    refine Finset.sum_congr rfl fun row _ => Finset.sum_congr rfl fun j hj => ?_
    obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ row
    · simp [L.ildt_zero]
    · rw [h i j hj]
  have hquad : ∀ j q, Tableau.quadCheck C P j (Tableau.quadPolynomials C P fs q) =
      Tableau.quadCheck C P j (Tableau.quadPolynomials C P gs q) := by
    intro j q
    by_cases hj : j ∈ P.witness
    · have key : ∀ i, (fs (P.products q i)).eval (P.nodes j) =
          (gs (P.products q i)).eval (P.nodes j) := by
        intro i
        obtain ⟨m, hm⟩ := Fin.exists_succ_eq.mpr (hprod q i)
        rw [← hm, h m j hj]
      simp only [Tableau.quadCheck, hj, ↓reduceIte, LinearMap.coe_mk, AddHom.coe_mk,
        Tableau.quadPolynomials, eval_sub, eval_mul, key]
    · simp [Tableau.quadCheck, hj]
  unfold Tableau.Holds MaskedConstraintFamily.Claim
  simp only [hdot, hquad]

variable (Bf : BlindingFields C P)
variable {nrep : ℕ}

/-- The committed witness cells: a value for every witness cell, in its row's
blinding field. No equation is attached, since the cells are committed before
the linear system is known. -/
structure Cells where
  cell : Fin R → Fin C.k → F
  cell_mem : ∀ row, ∀ j ∈ P.witness, cell row j ∈ Bf.field row

variable {Bf} in
/-- The zero-privacy tableau of the cells `ω`: the ILDT row is zero, and each
data row interpolates its witness cells with zero at the privacy positions. -/
noncomputable def zeroRows (ω : Cells Bf) : Fin (R + 1) → F[X] :=
  Fin.cases 0 fun row => LigeroInterpolation.interpolate P.nodes fun j =>
    if j ∈ P.witness then ω.cell row j else 0

omit [Fintype F] in
@[simp] theorem zeroRows_zero (ω : Cells Bf) : zeroRows ω 0 = 0 := rfl

omit [Fintype F] in
@[simp] theorem zeroRows_succ (ω : Cells Bf) (row : Fin R) :
    zeroRows ω row.succ = LigeroInterpolation.interpolate P.nodes fun j =>
      if j ∈ P.witness then ω.cell row j else 0 := rfl

variable (L) in
/-- The honest input: committed cells such that the zero-privacy tableau
satisfies the equations of `L`. -/
structure Witness extends Cells Bf where
  holds : Tableau.Holds C P L (zeroRows ⟨cell, cell_mem⟩)

variable (C P hrate) in
/-- IDOT masks: degree `< 2k − 1` and witness-position sum zero. -/
def DotMasks : Type :=
  {p : F[X] // p.natDegree < (MaskedPolynomialTest.maskCode C hrate).k ∧
    Tableau.dotCheck C P p = 0}

variable (C P hrate) in
/-- IQUAD masks: degree `< 2k − 1` and zero at every witness node. -/
def QuadMasks : Type :=
  {p : F[X] // p.natDegree < (MaskedPolynomialTest.maskCode C hrate).k ∧
    ∀ j, Tableau.quadCheck C P j p = 0}

omit [Fintype F] in
/-- Polynomials of degree `< n` are determined by their first `n` coefficients. -/
theorem coeffs_injective {n : ℕ} {Q : F[X] → Prop} :
    Function.Injective fun p : {p : F[X] // p.natDegree < n ∧ Q p} =>
      fun i : Fin n => p.1.coeff i := by
  intro p p' h
  apply Subtype.ext
  ext m
  by_cases hm : m < n
  · exact congrFun h ⟨m, hm⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le p.2.1 (not_lt.mp hm)),
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le p'.2.1 (not_lt.mp hm))]

noncomputable instance : Fintype (DotMasks C P hrate) :=
  Fintype.ofInjective _ coeffs_injective
noncomputable instance : Fintype (QuadMasks C P hrate) :=
  Fintype.ofInjective _ coeffs_injective

section Enumeration

variable [DecidableEq F]

variable (F) in
/-- **The coefficient vectors of length `n` whose polynomials satisfy `Q`.** -/
def polyCandidates (n : ℕ) (Q : F[X] → Prop)
    [DecidablePred fun v : Fin n → F => Q (Polynomial.ofFn n v)] : Finset (Fin n → F) :=
  Finset.univ.filter fun v => Q (Polynomial.ofFn n v)

theorem mem_polyCandidates {n : ℕ} {Q : F[X] → Prop}
    [DecidablePred fun v : Fin n → F => Q (Polynomial.ofFn n v)] {v : Fin n → F} :
    v ∈ polyCandidates F n Q ↔ Q (Polynomial.ofFn n v) := by
  simp [polyCandidates]

/-- **The polynomials of degree `< n` with a property `Q`, enumerated** through their coefficient
vectors (`Polynomial.ofFn`, `polyCandidates`), when `Q` is decidable on the polynomials of the
coefficient vectors. -/
@[instance_reducible] def polyEnum {n : ℕ} (hn : 0 < n) (Q : F[X] → Prop)
    [DecidablePred fun v : Fin n → F => Q (Polynomial.ofFn n v)] :
    Fintype {p : F[X] // p.natDegree < n ∧ Q p} where
  elems := (polyCandidates F n Q).attach.map
    ⟨fun v : {v // v ∈ polyCandidates F n Q} =>
        ⟨Polynomial.ofFn n v.1, Polynomial.ofFn_natDegree_lt hn v.1, mem_polyCandidates.1 v.2⟩,
      fun _ _ h => Subtype.ext (Polynomial.injective_ofFn n (congrArg Subtype.val h :))⟩
  complete q := by
    have hq := Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt q.2.1
    have hv : Polynomial.toFn n q.1 ∈ polyCandidates F n Q :=
      mem_polyCandidates.2 (by rw [hq]; exact q.2.2)
    rw [Finset.mem_map]
    exact ⟨⟨_, hv⟩, Finset.mem_attach _ _, Subtype.ext hq⟩

/-- **The IDOT masks, enumerated** (`polyEnum`): the polynomials of the coefficient vectors whose
witness-position sum vanishes, with the decidable equality of `F`. -/
@[instance_reducible] def DotMasks.enum : Fintype (DotMasks C P hrate) :=
  polyEnum (MaskedPolynomialTest.maskCode C hrate).k_pos _

/-- **The IQUAD masks, enumerated** (`polyEnum`): the polynomials of the coefficient vectors that
vanish at every witness node (`Tableau.quadCheck_eq_zero_iff`), with the decidable equality of `F`. -/
@[instance_reducible] def QuadMasks.enum : Fintype (QuadMasks C P hrate) :=
  haveI : DecidablePred fun v : Fin (MaskedPolynomialTest.maskCode C hrate).k → F =>
      ∀ j, Tableau.quadCheck C P j (Polynomial.ofFn _ v) = 0 := fun v =>
    decidable_of_iff _ (Tableau.quadCheck_eq_zero_iff C P _).symm
  polyEnum (MaskedPolynomialTest.maskCode C hrate).k_pos _

end Enumeration

omit [Fintype F] in
/-- The zero polynomial is an IDOT mask. -/
instance : Nonempty (DotMasks C P hrate) :=
  ⟨⟨0, by simpa using (MaskedPolynomialTest.maskCode C hrate).k_pos, map_zero _⟩⟩

omit [Fintype F] in
/-- The zero polynomial is an IQUAD mask. -/
instance : Nonempty (QuadMasks C P hrate) :=
  ⟨⟨0, by simpa using (MaskedPolynomialTest.maskCode C hrate).k_pos, fun _ => map_zero _⟩⟩

variable (P hrate) in
/-- **The response coins**: the ILDT message values of each of the `nrep` repetitions and the IDOT
and IQUAD masks. For fixed privacy values they determine the responses, and the honest responses are
a translate of them (`responseShift`). -/
@[ext]
structure ResponseCoins (nrep : ℕ) where
  /-- The ILDT message values of each repetition. -/
  ildt : Fin nrep → Fin C.k → F
  /-- The IDOT mask. -/
  dotMask : DotMasks C P hrate
  /-- The IQUAD mask. -/
  quadMask : QuadMasks C P hrate

variable (P hrate nrep) in
/-- Response coins as their three parts. -/
def ResponseCoins.equivProd :
    ResponseCoins P hrate nrep ≃
      (Fin nrep → Fin C.k → F) × DotMasks C P hrate × QuadMasks C P hrate where
  toFun x := (x.ildt, x.dotMask, x.quadMask)
  invFun y := ⟨y.1, y.2.1, y.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : Fintype (ResponseCoins P hrate nrep) :=
  Fintype.ofEquiv _ (ResponseCoins.equivProd P hrate nrep).symm

variable (P hrate nrep) in
/-- **The response coins, enumerated** with the decidable equality of `F`: their three parts
(`DotMasks.enum`, `QuadMasks.enum`). -/
@[instance_reducible] def ResponseCoins.enum [DecidableEq F] : Fintype (ResponseCoins P hrate nrep) :=
  letI := DotMasks.enum (C := C) (P := P) (hrate := hrate)
  letI := QuadMasks.enum (C := C) (P := P) (hrate := hrate)
  Fintype.ofEquiv _ (ResponseCoins.equivProd P hrate nrep).symm

instance : Nonempty (ResponseCoins P hrate nrep) :=
  ⟨⟨0, Classical.arbitrary _, Classical.arbitrary _⟩⟩

variable (hrate) in
/-- **The honest prover's coins**: each data row's privacy values in its blinding field, and the
response coins. -/
@[ext]
structure Coins (nrep : ℕ) where
  /-- Each data row's privacy values. -/
  privacy : ∀ row : Fin R, Privacy P → Bf.field row
  /-- The response coins. -/
  response : ResponseCoins P hrate nrep

variable (hrate nrep) in
/-- The honest prover's coins as the privacy values and the response coins. -/
def Coins.equivProd :
    Coins hrate Bf nrep ≃ (∀ row : Fin R, Privacy P → Bf.field row) × ResponseCoins P hrate nrep where
  toFun c := (c.privacy, c.response)
  invFun y := ⟨y.1, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : Fintype (Coins hrate Bf nrep) := by
  classical
  exact Fintype.ofEquiv _ (Coins.equivProd hrate Bf nrep).symm

instance : Nonempty (Coins hrate Bf nrep) :=
  ⟨⟨fun _ _ => 0, Classical.arbitrary _⟩⟩

variable {Bf}

/-- A data row's message values: the witness cells and the privacy coins. -/
def rowValues (ω : Cells Bf) (ρ : ∀ row : Fin R, Privacy P → Bf.field row) (row : Fin R) :
    Fin C.k → F :=
  fun j => if h : j ∈ P.witness then ω.cell row j else ρ row ⟨j, h⟩

/-- The honest row polynomials of repetition `j`'s matrix: `ILDT_j` from its coins, data rows
from `rowValues`. -/
noncomputable def ldtRows (ω : Cells Bf) (c : Coins hrate Bf nrep) (j : Fin nrep) :
    Fin (R + 1) → F[X] :=
  Fin.cons (LigeroInterpolation.interpolate P.nodes (c.response.ildt j)) fun row =>
    LigeroInterpolation.interpolate P.nodes (rowValues ω c.privacy row)

variable [NeZero nrep]

/-- The honest tableau polynomials: repetition `0`'s (`ldtRows`). -/
noncomputable def rows (ω : Cells Bf) (c : Coins hrate Bf nrep) : Fin (R + 1) → F[X] :=
  ldtRows ω c 0

omit [Fintype F] in
@[simp] theorem rows_zero (ω : Cells Bf) (c : Coins hrate Bf nrep) :
    rows ω c 0 = LigeroInterpolation.interpolate P.nodes (c.response.ildt 0) := rfl

omit [Fintype F] in
@[simp] theorem rows_succ (ω : Cells Bf) (c : Coins hrate Bf nrep) (row : Fin R) :
    rows ω c row.succ = LigeroInterpolation.interpolate P.nodes (rowValues ω c.privacy row) := rfl

/-- The honest row polynomials' values at a point, by field operations (`eval_rows`). -/
def rowsEval (ω : Cells Bf) (c : Coins hrate Bf nrep) (row : Fin (R + 1)) (x : F) : F :=
  Fin.cases (LigeroInterpolation.interpolateEval P.nodes (c.response.ildt 0) x) (fun row =>
    LigeroInterpolation.interpolateEval P.nodes (rowValues ω c.privacy row) x) row

omit [Fintype F] in
theorem eval_rows (ω : Cells Bf) (c : Coins hrate Bf nrep) (row : Fin (R + 1)) (x : F) :
    (rows ω c row).eval x = rowsEval ω c row x := by
  obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ row
  · simp [rowsEval, LigeroInterpolation.eval_interpolate]
  · simp [rowsEval, LigeroInterpolation.eval_interpolate]

omit [Fintype F] in
theorem rowValues_of_mem (ω : Cells Bf) (ρ : ∀ row : Fin R, Privacy P → Bf.field row)
    (row : Fin R) {j : Fin C.k} (hj : j ∈ P.witness) : rowValues ω ρ row j = ω.cell row j := by
  simp [rowValues, hj]

omit [Fintype F] in
theorem rows_degree (ω : Cells Bf) (c : Coins hrate Bf nrep) (row : Fin (R + 1)) :
    (rows ω c row).natDegree < C.k := by
  obtain rfl | ⟨i, rfl⟩ := Fin.eq_zero_or_eq_succ row
  · exact LigeroInterpolation.interpolate_degree C.k_pos P.nodes_injective _
  · exact LigeroInterpolation.interpolate_degree C.k_pos P.nodes_injective _

omit [Fintype F] in
/-- Every message value of an honest data row lies in the row's blinding field: the
witness cells by `cell_mem`, the privacy values by construction. -/
theorem rowValues_mem (ω : Cells Bf) (ρ : ∀ row : Fin R, Privacy P → Bf.field row)
    (row : Fin R) (j : Fin C.k) : rowValues ω ρ row j ∈ Bf.field row := by
  unfold rowValues
  split_ifs with h
  · exact ω.cell_mem row j h
  · exact (ρ row ⟨j, h⟩).2

omit [Fintype F] in
/-- An honest data row whose blinding field lies in a subfield `E` containing the
message nodes evaluates into `E` at every point of `E`. -/
theorem rows_succ_eval_mem (ω : Cells Bf) (c : Coins hrate Bf nrep) {E : Subfield F}
    {row : Fin R} (hrow : Bf.field row ≤ E) (hnodes : ∀ j, P.nodes j ∈ E) {x : F}
    (hx : x ∈ E) : (rows ω c row.succ).eval x ∈ E := by
  rw [rows_succ]
  exact SubfieldInterpolation.eval_mem E P.nodes P.nodes_injective hnodes _
    (fun j => hrow (rowValues_mem ω c.privacy row j)) hx

omit [Fintype F] in
/-- The honest rows satisfy the equations: they agree with the zero-privacy
tableau of `ω.holds` at every witness node. `hprod`: a parameter
condition, no quadratic triple reads the ILDT row, whose honest values are random. -/
theorem rows_holds (hprod : ∀ q i, P.products q i ≠ 0) (ω : Witness L Bf) (c : Coins hrate Bf nrep) :
    Tableau.Holds C P L (rows ω.toCells c) := by
  refine (holds_iff_of_eval_witness hprod ?_).mp ω.holds
  intro i j hj
  simp only [zeroRows_succ, rows_succ, LigeroInterpolation.interpolate_eval P.nodes_injective,
    rowValues_of_mem ω.toCells c.privacy i hj, hj, ↓reduceIte]

/-- The honest tableau for the coins `c`. Its rows satisfy the equations
because the equations read only witness positions and no quadratic triple
reads the ILDT row (`hprod`, a parameter condition). -/
noncomputable def honest (hprod : ∀ q i, P.products q i ≠ 0) (ω : Witness L Bf) (c : Coins hrate Bf nrep) :
    Completeness.HonestTableau (C := C) (P := P) (L := L) hrate nrep where
  ildt j := LigeroInterpolation.interpolate P.nodes (c.response.ildt j)
  data i := LigeroInterpolation.interpolate P.nodes (rowValues ω.toCells c.privacy i)
  ildt_degree _ := LigeroInterpolation.interpolate_degree C.k_pos P.nodes_injective _
  data_degree _ := LigeroInterpolation.interpolate_degree C.k_pos P.nodes_injective _
  holds := rows_holds hprod ω c
  dotMask := c.response.dotMask.1
  quadMask := c.response.quadMask.1
  dotMask_degree := c.response.dotMask.2.1
  quadMask_degree := c.response.quadMask.2.1
  dotMask_zero := c.response.dotMask.2.2
  quadMask_zero := c.response.quadMask.2.2

variable (hprod : ∀ q i, P.products q i ≠ 0)

omit [Fintype F] in
/-- The honest tableau is accepted for every coin value, challenge and query set. -/
theorem honest_accept (ω : Witness L Bf) (c : Coins hrate Bf nrep)
    (r : Tableau.Challenge F R nL nQ nrep) {t : ℕ} (q : Tableau.Query N t) :
    Tableau.accept C P L (Completeness.encode (honest hprod ω c))
      (Completeness.masks (honest hprod ω c)) r
        (Completeness.response (honest hprod ω c) r) q = true :=
  Completeness.accept (honest hprod ω c) r q

omit [Fintype F] in
/-- The rows read only the ILDT and privacy coins. -/
theorem rows_congr (ω : Cells Bf) (ρ : ∀ row : Fin R, Privacy P → Bf.field row)
    {x x' : ResponseCoins P hrate nrep} (hl : x.ildt = x'.ildt) :
    rows ω ⟨ρ, x⟩ = rows ω ⟨ρ, x'⟩ := by
  unfold rows ldtRows
  rw [hl]

omit [Fintype F] in
/-- The honest low-degree response interpolates the ILDT values plus the
challenge combination of the data rows' values. -/
theorem codeResponse_honest (ω : Witness L Bf) (c : Coins hrate Bf nrep)
    (r : Tableau.Challenge F R nL nQ nrep) (j : Fin nrep) :
    Completeness.codeResponse (honest hprod ω c) r j =
      LigeroInterpolation.interpolate P.nodes
        (c.response.ildt j + ∑ i, r.1 j i • rowValues ω.toCells c.privacy i) := by
  change AffineCodeTest.projectedPolynomial (ldtRows ω.toCells c j) (r.1 j) = _
  simp only [AffineCodeTest.projectedPolynomial, ldtRows, Fin.cons_zero, Fin.cons_succ, map_add,
    map_sum, map_smul]

omit [Fintype F] in
theorem dotResponse_honest (ω : Witness L Bf) (c : Coins hrate Bf nrep)
    (r : Tableau.Challenge F R nL nQ nrep) :
    Completeness.dotResponse (honest hprod ω c) r = c.response.dotMask.1 + MaskedConstraintTest.batch
      (fun l => Tableau.dotPolynomials C P L (rows ω.toCells c) l) r.2.1 := rfl

omit [Fintype F] in
theorem quadResponse_honest (ω : Witness L Bf) (c : Coins hrate Bf nrep)
    (r : Tableau.Challenge F R nL nQ nrep) :
    Completeness.quadResponse (honest hprod ω c) r = c.response.quadMask.1 + MaskedConstraintTest.batch
      (fun q => Tableau.quadPolynomials C P (rows ω.toCells c) q) r.2.2 := rfl

/-- The committed matrix and the IDOT and IQUAD masks for coins `c`. They read
the cells only, so they are fixed before the linear system is known. -/
def commitOf (ω : Cells Bf) (c : Coins hrate Bf nrep) : Tableau.Commitment F N R nrep :=
  ⟨⟨fun j col => LigeroInterpolation.interpolateEval P.nodes (c.response.ildt j) (C.D col),
      fun i col => LigeroInterpolation.interpolateEval P.nodes (rowValues ω c.privacy i) (C.D col)⟩,
    (fun j => c.response.dotMask.1.eval (C.D j), fun j => c.response.quadMask.1.eval (C.D j))⟩

omit [Fintype F] [NeZero nrep] in
/-- Repetition `j`'s committed matrix is the evaluation of its honest rows. -/
theorem commitOf_ldtMatrix (ω : Cells Bf) (c : Coins hrate Bf nrep) (j : Fin nrep) :
    (commitOf ω c).rows.ldtMatrix j = fun row col => (ldtRows ω c j row).eval (C.D col) := by
  funext row col
  refine Fin.cases ?_ (fun i => ?_) row
  · simp [commitOf, ldtRows, LigeroInterpolation.eval_interpolate]
  · simp [commitOf, ldtRows, LigeroInterpolation.eval_interpolate]

omit [Fintype F] in
theorem commitOf_tableau (ω : Cells Bf) (c : Coins hrate Bf nrep) :
    (commitOf ω c).tableau = fun row j => (rows ω c row).eval (C.D j) :=
  commitOf_ldtMatrix ω c 0

omit [Fintype F] in
theorem commitOf_eq (ω : Witness L Bf) (c : Coins hrate Bf nrep) :
    commitOf ω.toCells c =
      ⟨Completeness.encode (honest hprod ω c), Completeness.masks (honest hprod ω c)⟩ := by
  refine Tableau.Commitment.ext (Tableau.Rows.ext ?_ ?_) rfl
  · funext j col
    exact (LigeroInterpolation.eval_interpolate _ _ _).symm
  · funext i col
    exact (LigeroInterpolation.eval_interpolate _ _ _).symm

omit [Fintype F] in
open Classical in
/-- The committed matrix of honest cells decodes to the honest rows, for every coin value. -/
theorem commitOf_decode (ω : Cells Bf) (c : Coins hrate Bf nrep) :
    RSCode.nearbyRows C (commitOf ω c).tableau = some (rows ω c) := by
  apply RSCode.nearbyRows_eq_some_iff.mpr
  refine ⟨rows_degree ω c, ?_⟩
  have hz : RSCode.columnErrors C (commitOf ω c).tableau (rows ω c) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro j _ hj
    obtain ⟨row, hrow⟩ := hj
    exact hrow (by rw [commitOf_tableau])
  rw [hz, Finset.card_empty]
  exact Nat.zero_le _

variable (L) in
/-- The three responses for coins `c` and challenge `r`, as their values on the response nodes,
by field operations: the low-degree response interpolates the ILDT values plus the challenge
combination of the data rows' values (`codeResponse_honest`), the linear and quadratic responses
add the masks to the batched row combinations. They read `L` only through the batching of the
linear polynomials by `r.2.1`; equal to `Completeness.response` (`responseOf_eq`). -/
def responseOf (ω : Cells Bf) (c : Coins hrate Bf nrep) (r : Tableau.Challenge F R nL nQ nrep) :
    Tableau.Response F C.k nrep :=
  (fun j i => LigeroInterpolation.interpolateEval P.nodes
      (c.response.ildt j + ∑ l, r.1 j l • rowValues ω c.privacy l) (Tableau.responseNode C C.k i),
    fun i => c.response.dotMask.1.eval (Tableau.responseNode C (2 * C.k - 1) i) +
      ∑ l, r.2.1 l * ∑ row, LigeroInterpolation.interpolateEval P.nodes (L.coeff l row)
        (Tableau.responseNode C (2 * C.k - 1) i) *
          rowsEval ω c row (Tableau.responseNode C (2 * C.k - 1) i),
    fun i => c.response.quadMask.1.eval (Tableau.responseNode C (2 * C.k - 1) i) +
      ∑ q, r.2.2 q * (rowsEval ω c (P.products q 2) (Tableau.responseNode C (2 * C.k - 1) i) -
        rowsEval ω c (P.products q 0) (Tableau.responseNode C (2 * C.k - 1) i) *
          rowsEval ω c (P.products q 1) (Tableau.responseNode C (2 * C.k - 1) i)))

omit [Fintype F] in
theorem responseOf_eq (ω : Witness L Bf) (c : Coins hrate Bf nrep)
    (r : Tableau.Challenge F R nL nQ nrep) :
    responseOf L ω.toCells c r = Completeness.response (honest hprod ω c) r := by
  refine Prod.ext (funext fun j => funext fun i => ?_)
    (Prod.ext (funext fun i => ?_) (funext fun i => ?_))
  · change _ = (Completeness.codeResponse (honest hprod ω c) r j).eval _
    rw [codeResponse_honest, LigeroInterpolation.eval_interpolate]
    rfl
  · change _ = (Completeness.dotResponse (honest hprod ω c) r).eval _
    simp only [dotResponse_honest, MaskedConstraintTest.batch, Tableau.dotPolynomials,
      LigeroInterpolation.decodedDot, eval_add, eval_finsetSum, eval_mul, eval_C,
      LigeroInterpolation.eval_interpolate, eval_rows]
    rfl
  · change _ = (Completeness.quadResponse (honest hprod ω c) r).eval _
    simp only [quadResponse_honest, MaskedConstraintTest.batch, Tableau.quadPolynomials,
      eval_add, eval_finsetSum, eval_mul, eval_sub, eval_C, eval_rows]
    rfl

/-- What the verifier reads of one tableau at `t` queried columns: the responses, and at each
queried column every entry of the encoded rows (`Tableau.Column`: the `nrep` ILDT entries and the
data entries) and both mask entries. -/
abbrev View (F : Type) [Field F] (R k t nrep : ℕ) : Type :=
  Tableau.Response F k nrep × (Fin t → Tableau.Column F R nrep × F × F)

omit [NeZero nrep] in
/-- The verifier's view of encoded rows, masks, response and query set. -/
def view {k t : ℕ} (O : Tableau.Rows F N R nrep) (u : Tableau.Aux F N)
    (p : Tableau.Response F k nrep) (q : Tableau.Query N t) : View F R k t nrep :=
  (p, fun s => (O.column (q s), u.1 (q s), u.2 (q s)))

/-- The honest view for the coins `c`: the view of the commitment and the
response. -/
def honestView (ω : Witness L Bf) (r : Tableau.Challenge F R nL nQ nrep) {t : ℕ}
    (q : Tableau.Query N t) (c : Coins hrate Bf nrep) : View F R C.k t nrep :=
  view (commitOf ω.toCells c).rows (commitOf ω.toCells c).masks (responseOf L ω.toCells c r) q

omit [Fintype F] in
/-- The honest view is the view of the honest tableau. -/
theorem honestView_eq (ω : Witness L Bf) (r : Tableau.Challenge F R nL nQ nrep) {t : ℕ}
    (q : Tableau.Query N t) (c : Coins hrate Bf nrep) :
    honestView ω r q c =
      view (Completeness.encode (honest hprod ω c))
        (Completeness.masks (honest hprod ω c))
        (Completeness.response (honest hprod ω c) r) q := by
  rw [honestView, commitOf_eq hprod, responseOf_eq hprod]

variable {Hd : HidingLayout C P}

/-! ## The simulator -/

/-- The linear column source at a point, from one column of row values.
`Ligero.Tableau.dotColumn` is this at the column's entries (`dotColumn_eq_dotAt`). -/
def dotAt (col : Fin (R + 1) → F) (l : Fin nL) (x : F) : F :=
  ∑ row, LigeroInterpolation.interpolateEval P.nodes (L.coeff l row) x * col row

/-- The quadratic column source from one column of row values. -/
def quadAt (col : Fin (R + 1) → F) (q : Fin nQ) : F :=
  col (P.products q 2) - col (P.products q 0) * col (P.products q 1)

omit [Fintype F] in
theorem dotColumn_eq_dotAt (U : RSCode.Matrix F (R + 1) N) (l : Fin nL) (j : Fin N) :
    Tableau.dotColumn C P L U l j = dotAt (L := L) (fun row => U row j) l (C.D j) := rfl

omit [Fintype F] in
theorem quadColumn_eq_quadAt (U : RSCode.Matrix F (R + 1) N) (q : Fin nQ) (j : Fin N) :
    Tableau.quadColumn C P U q j = quadAt (P := P) (fun row => U row j) q := rfl

variable (Hd) in
/-- A fixed public polynomial of degree `< k` whose witness-position sum is one:
the interpolant of the indicator of the least witness node. -/
noncomputable def unitDot : F[X] :=
  LigeroInterpolation.interpolate P.nodes (Pi.single (P.witness.min' Hd.witness_nonempty) 1)

omit [Fintype F] in
theorem dotCheck_unitDot : Tableau.dotCheck C P (unitDot Hd) = 1 := by
  simp only [Tableau.dotCheck, LigeroInterpolation.sumEvaluationOn_apply, unitDot,
    LigeroInterpolation.interpolate_eval P.nodes_injective, Finset.sum_pi_single',
    P.witness.min'_mem Hd.witness_nonempty, ↓reduceIte]

omit [Fintype F] in
theorem unitDot_degree : (unitDot Hd).natDegree < C.k :=
  LigeroInterpolation.interpolate_degree C.k_pos P.nodes_injective _

variable (Hd) in
/-- `unitDot`'s value at a point, by field operations. -/
def unitDotEval (x : F) : F :=
  LigeroInterpolation.interpolateEval P.nodes (Pi.single (P.witness.min' Hd.witness_nonempty) 1) x

omit [Fintype F] in
theorem eval_unitDot (x : F) : (unitDot Hd).eval x = unitDotEval Hd x :=
  LigeroInterpolation.eval_interpolate _ _ _

variable (Hd hrate) in
/-- **The simulator's coins**: each data row's openings in its blinding field, and response
coins: the low-degree response's message values, and the linear and quadratic responses as
translates of the IDOT and IQUAD mask sets. -/
@[ext]
structure SimCoins (t nrep : ℕ) where
  /-- Each data row's openings at the queried columns. -/
  openings : ∀ row : Fin R, Fin t → Hd.field row
  /-- The response coins. -/
  response : ResponseCoins P hrate nrep

variable (Hd hrate) in
/-- The simulator's coins as the openings and the response coins. -/
def SimCoins.equivProd (t nrep : ℕ) :
    SimCoins hrate Hd t nrep ≃ (∀ row : Fin R, Fin t → Hd.field row) × ResponseCoins P hrate nrep where
  toFun s := (s.openings, s.response)
  invFun y := ⟨y.1, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The simulator's coins are enumerated through the blinding fields' decidable membership and the
decidable equality of `F` of the hiding layout (`ResponseCoins.enum`). -/
instance (t : ℕ) : Fintype (SimCoins hrate Hd t nrep) :=
  letI := Hd.decEq
  letI := ResponseCoins.enum P hrate nrep
  Fintype.ofEquiv _ (SimCoins.equivProd hrate Hd t nrep).symm

instance (t : ℕ) : Nonempty (SimCoins hrate Hd t nrep) :=
  ⟨⟨fun _ _ => 0, Classical.arbitrary _⟩⟩

omit [NeZero nrep] in
variable (L Hd hrate) in
/-- The simulator's responses from its message values and mask-set samples, as their values on
the response nodes, by field operations: the interpolant of each repetition's ILDT values, the
IDOT mask plus the batched target times `unitDot`, and the IQUAD mask. Equal to the values of
those polynomials (`simResponse_eq`). -/
def simResponse (r : Tableau.Challenge F R nL nQ nrep) (x : ResponseCoins P hrate nrep) :
    Tableau.Response F C.k nrep :=
  (fun j i => LigeroInterpolation.interpolateEval P.nodes (x.ildt j)
      (Tableau.responseNode C C.k i),
    fun i => x.dotMask.1.eval (Tableau.responseNode C (2 * C.k - 1) i) +
      (∑ l, r.2.1 l * L.target l) * unitDotEval Hd (Tableau.responseNode C (2 * C.k - 1) i),
    fun i => x.quadMask.1.eval (Tableau.responseNode C (2 * C.k - 1) i))

omit [Fintype F] [NeZero nrep] in
theorem simResponse_eq (r : Tableau.Challenge F R nL nQ nrep) (x : ResponseCoins P hrate nrep) :
    simResponse L hrate Hd r x = Tableau.Response.ofPolys C
      (fun j => LigeroInterpolation.interpolate P.nodes (x.ildt j))
      (x.dotMask.1 + Polynomial.C (∑ l, r.2.1 l * L.target l) * unitDot Hd) x.quadMask.1 := by
  refine Prod.ext (funext fun j => funext fun i => ?_) (Prod.ext (funext fun i => ?_) rfl)
  · simp only [simResponse, Tableau.Response.ofPolys, LigeroInterpolation.eval_interpolate]
  · simp only [simResponse, Tableau.Response.ofPolys, eval_add, eval_mul, eval_C, eval_unitDot]

variable (L Hd hrate) in
/-- **The simulator.** It reads the public linear system, the challenge and the
query set. The responses are sampled from the sets the verifier accepts; the
ILDT, IDOT and IQUAD openings are the solutions of the three acceptance
equations at each queried column.

Running time: sampling the coins is uniform sampling from `F`, from a subfield, and from the two
mask sets; each mask set is the solution space of linear equations over `F` in `2k − 1`
coefficients, so a basis is found by Gaussian elimination in `O(k³)` field operations and a uniform
element is a uniform combination of the basis. The output is one Lagrange interpolation over `k`
nodes (`O(k²)`), `t` evaluations of degree `< 2k − 1` polynomials, and for each queried column
`O(R)` operations for the ILDT opening, `O(nL · (R + 1) · k)` for the linear source (each
coefficient interpolant is evaluated once) and `O(nQ)` for the quadratic source. The total is
polynomial in `k`, `R`, `nL`, `nQ` and `t`. This running time is argued here, not proved in Lean. -/
def simulate (r : Tableau.Challenge F R nL nQ nrep) {t : ℕ} (q : Tableau.Query N t)
    (s : SimCoins hrate Hd t nrep) : View F R C.k t nrep :=
  let p := simResponse L hrate Hd r s.response
  let data : Fin R → Fin t → F := fun row j => s.openings row j
  let col : Fin t → Tableau.Column F R nrep := fun j =>
    ⟨fun m => p.codeEval C m (C.D (q j)) - ∑ i, r.1 m i * data i j, fun i => data i j⟩
  (p, fun j =>
    (col j,
      p.dotEval C (C.D (q j)) - ∑ l, r.2.1 l * dotAt (L := L) (col j).tableau l (C.D (q j)),
      p.quadEval C (C.D (q j)) - ∑ l, r.2.2 l * quadAt (P := P) (col j).tableau l))

/-! ## One row: the privacy values to the openings -/

section OneRow

/-- The openings at the points `y` of the interpolant of a row that is zero on
the witness positions `W` and carries the values `σ` elsewhere. Every value,
node and point lies in `E`, so the openings do too (`SubfieldInterpolation.eval_mem`). -/
noncomputable def privacyOpening {k t : ℕ} (E : Subfield F) {nodes : Fin k → F}
    (hinj : Function.Injective nodes) (hnodes : ∀ j, nodes j ∈ E) (W : Finset (Fin k))
    {y : Fin t → F} (hy : ∀ s, y s ∈ E) : ({j // j ∉ W} → E) →+ (Fin t → E) where
  toFun σ s := ⟨(LigeroInterpolation.interpolate nodes
      (fun j => if h : j ∈ W then 0 else (σ ⟨j, h⟩ : F))).eval (y s),
    SubfieldInterpolation.eval_mem E nodes hinj hnodes _
      (fun j => by split_ifs; exacts [E.zero_mem, (σ _).2]) (hy s)⟩
  map_zero' := by
    funext s
    apply Subtype.ext
    simp [← Pi.zero_def]
  map_add' σ σ' := by
    funext s
    apply Subtype.ext
    simp only [Pi.add_apply, Subfield.coe_add]
    rw [← eval_add, ← LigeroInterpolation.interpolate_add]
    congr 2
    funext j
    by_cases h : j ∈ W <;> simp [h]

variable {k t : ℕ} (E : Subfield F) {nodes : Fin k → F} (hinj : Function.Injective nodes)
  (hnodes : ∀ j, nodes j ∈ E) (W : Finset (Fin k)) {y : Fin t → F} (hy : ∀ s, y s ∈ E)

omit [Fintype F] in
theorem privacyOpening_apply (σ : {j // j ∉ W} → E) (s : Fin t) :
    (privacyOpening E hinj hnodes W hy σ s : F) = (LigeroInterpolation.interpolate nodes
      (fun j => if h : j ∈ W then 0 else (σ ⟨j, h⟩ : F))).eval (y s) := rfl

omit [Fintype F] in
/-- **One-row surjectivity**. When the points `y` are distinct, avoid the witness nodes, and number
at most the privacy positions, every vector of openings in `E` is reached. The Lagrange interpolant
of zero on the witness nodes and the target openings at `y` has degree `< k` and coefficients in
`E`; its values at the privacy nodes are the preimage. -/
theorem privacyOpening_surjective (hyinj : Function.Injective y)
    (hoff : ∀ s, ∀ j ∈ W, y s ≠ nodes j) (ht : W.card + t ≤ k) :
    Function.Surjective (privacyOpening E hinj hnodes W hy) := by
  intro τ
  let v : {j // j ∈ W} ⊕ Fin t → F := Sum.elim (fun j => nodes j.1) y
  let vals : {j // j ∈ W} ⊕ Fin t → F := Sum.elim 0 fun s => (τ s : F)
  have hv : Function.Injective v := by
    rintro (a | a) (b | b) hab
    · exact congrArg Sum.inl (Subtype.ext (hinj hab))
    · exact absurd hab.symm (hoff b a.1 a.2)
    · exact absurd hab (hoff a b.1 b.2)
    · exact congrArg Sum.inr (hyinj hab)
  let p : F[X] := Lagrange.interpolate Finset.univ v vals
  have hcard : (Finset.univ : Finset ({j // j ∈ W} ⊕ Fin t)).card = W.card + t := by
    simp
  have hnode : ∀ i, p.eval (v i) = vals i := fun i =>
    Lagrange.eval_interpolate_at_node vals hv.injOn (Finset.mem_univ i)
  have hdeg : p.degree < (W.card + t : ℕ) := by
    rw [← hcard]
    exact Lagrange.degree_interpolate_lt vals hv.injOn
  have hcoeff : ∀ n, p.coeff n ∈ E := by
    have hS : (Finset.univ.image v).card = W.card + t := by
      rw [Finset.card_image_of_injective _ hv, hcard]
    rcases eq_or_ne p 0 with h0 | h0
    · intro n
      rw [h0, coeff_zero]
      exact E.zero_mem
    refine Polynomial.coeff_mem_of_eval_mem E (S := Finset.univ.image v) ?_ ?_ ?_
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      rcases i with i | i
      exacts [hnodes _, hy _]
    · rw [hS]
      exact (natDegree_lt_iff_degree_lt h0).mpr hdeg
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      rw [hnode]
      rcases i with i | i
      exacts [E.zero_mem, (τ i).2]
  have hpE : ∀ x ∈ E, p.eval x ∈ E := fun x hx =>
    Polynomial.eval_mem_of_coeff_mem E hcoeff hx
  refine ⟨fun j => ⟨p.eval (nodes j.1), hpE _ (hnodes _)⟩, ?_⟩
  have hvals : (fun j => if h : j ∈ W then 0 else
      ((⟨p.eval (nodes j), hpE _ (hnodes _)⟩ : E) : F)) = fun j => p.eval (nodes j) := by
    funext j
    by_cases h : j ∈ W
    · simp only [h, ↓reduceDIte]
      exact (hnode (Sum.inl ⟨j, h⟩)).symm
    · simp only [h, ↓reduceDIte]
  have hint : LigeroInterpolation.interpolate nodes (fun j => p.eval (nodes j)) = p := by
    refine (Lagrange.eq_interpolate hinj.injOn ?_).symm
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_lt_of_le hdeg (by exact_mod_cast ht)
  funext s
  apply Subtype.ext
  rw [privacyOpening_apply]
  simp only [hvals, hint]
  exact hnode (Sum.inr s)

end OneRow

/-! ## The honest view as a public function of the openings and responses -/

variable (L) in
/-- The view rebuilt from the data-row openings and the three responses: the
ILDT, IDOT and IQUAD openings are the solutions of the three acceptance
equations. The simulator is this map on its sampled values (`simulate_eq`),
and so is the honest view (`view_honest`). -/
def publicView (r : Tableau.Challenge F R nL nQ nrep) {t : ℕ} (q : Tableau.Query N t)
    (data : Fin R → Fin t → F) (p : Tableau.Response F C.k nrep) : View F R C.k t nrep :=
  let col : Fin t → Tableau.Column F R nrep := fun j =>
    ⟨fun m => p.codeEval C m (C.D (q j)) - ∑ i, r.1 m i * data i j, fun i => data i j⟩
  (p, fun j =>
    (col j,
      p.dotEval C (C.D (q j)) - ∑ l, r.2.1 l * dotAt (L := L) (col j).tableau l (C.D (q j)),
      p.quadEval C (C.D (q j)) - ∑ l, r.2.2 l * quadAt (P := P) (col j).tableau l))

omit [Fintype F] in
/-- **The ILDT, IDOT and IQUAD openings are determined**. For every honest tableau, with any masks,
the view is the public map of the data-row openings and the responses. -/
theorem view_honest (H : Completeness.HonestTableau (C := C) (P := P) (L := L) hrate nrep)
    (r : Tableau.Challenge F R nL nQ nrep) {t : ℕ} (q : Tableau.Query N t) :
    view (Completeness.encode H) (Completeness.masks H)
        (Completeness.response H r) q =
      publicView L r q (fun i s => (H.data i).eval (C.D (q s)))
        (Completeness.response H r) := by
  have hcol : ∀ s, (⟨fun m => (Completeness.response H r).codeEval C m (C.D (q s)) -
      ∑ i, r.1 m i * (H.data i).eval (C.D (q s)),
        fun i => (H.data i).eval (C.D (q s))⟩ : Tableau.Column F R nrep) =
      (Completeness.encode H).column (q s) := by
    intro s
    refine Tableau.Column.ext (funext fun m => ?_) rfl
    simp [← Tableau.Response.eval_code, Completeness.response_code,
      Completeness.codeResponse, Completeness.HonestTableau.ldtRows, Completeness.encode,
      Tableau.Rows.column]
  refine Prod.ext rfl (funext fun s => ?_)
  simp only [publicView, hcol, Tableau.Rows.column_tableau]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · have h := Completeness.dotAccept H r q s
    simp only [dotColumn_eq_dotAt] at h
    rw [← Tableau.Response.eval_dot, Completeness.response_dot]
    exact (eq_sub_of_add_eq h).trans rfl
  · have h := Completeness.quadAccept H r q s
    simp only [quadColumn_eq_quadAt] at h
    rw [← Tableau.Response.eval_quad, Completeness.response_quad]
    exact (eq_sub_of_add_eq h).trans rfl

/-! ## The data-row openings are uniform -/

/-- The openings of data row `row` at the query set, for privacy values `σ`.
They lie in the row's blinding field (`SubfieldInterpolation.eval_mem`). -/
noncomputable def rowOpening (ω : Cells Hd.toBlindingFields) {t : ℕ} (q : Tableau.Query N t) (row : Fin R)
    (σ : Privacy P → Hd.field row) : Fin t → Hd.field row := fun s =>
  ⟨(LigeroInterpolation.interpolate P.nodes
      (fun j => if h : j ∈ P.witness then ω.cell row j else (σ ⟨j, h⟩ : F))).eval (C.D (q s)),
    SubfieldInterpolation.eval_mem _ P.nodes P.nodes_injective (Hd.nodes_mem row) _
      (fun j => by split_ifs with h; exacts [ω.cell_mem row j h, (σ _).2])
      (Hd.points_mem row (q s))⟩

omit [Fintype F] in
/-- A row's openings are the privacy openings plus the openings of its witness
part, which do not depend on `σ`. -/
theorem rowOpening_eq (ω : Cells Hd.toBlindingFields) {t : ℕ} (q : Tableau.Query N t)
    (row : Fin R) (σ : Privacy P → Hd.field row) :
    rowOpening ω q row σ = privacyOpening (Hd.field row) P.nodes_injective (Hd.nodes_mem row)
      P.witness (y := fun s => C.D (q s)) (fun s => Hd.points_mem row (q s)) σ +
        rowOpening ω q row 0 := by
  funext s
  apply Subtype.ext
  simp only [Pi.add_apply, Subfield.coe_add, privacyOpening_apply, rowOpening]
  rw [← eval_add, ← LigeroInterpolation.interpolate_add]
  congr 2
  funext j
  by_cases h : j ∈ P.witness <;> simp [h]

/-- **Data-row openings**. A row's openings are uniform over its blinding field, whatever the
witness. `ht`: a parameter condition. -/
theorem rowOpening_uniform (ω : Cells Hd.toBlindingFields) {t : ℕ} (q : Tableau.Query N t)
    (row : Fin R) (ht : t ≤ C.k - P.witness.card) : Uniform (rowOpening ω q row) := by
  have hcard : P.witness.card ≤ C.k := by simpa using P.witness.card_le_univ
  have h := Uniform.of_surjective _ (privacyOpening_surjective (Hd.field row)
    P.nodes_injective (Hd.nodes_mem row) P.witness (fun s => Hd.points_mem row (q s))
    (C.D_injective.comp q.injective) (fun s j hj => Hd.off_witness (q s) j hj) (by omega))
    (rowOpening ω q row 0)
  have he : rowOpening ω q row = fun σ => privacyOpening (Hd.field row) P.nodes_injective
      (Hd.nodes_mem row) P.witness (y := fun s => C.D (q s)) (fun s => Hd.points_mem row (q s))
        σ + rowOpening ω q row 0 :=
    funext (rowOpening_eq ω q row)
  rw [he]
  exact h

/-- The openings of every data row. -/
noncomputable def openings (ω : Cells Hd.toBlindingFields) {t : ℕ} (q : Tableau.Query N t)
    (ρ : ∀ row : Fin R, Privacy P → Hd.field row) : ∀ row : Fin R, Fin t → Hd.field row :=
  fun row => rowOpening ω q row (ρ row)

/-- The rows use disjoint privacy coins, so their openings are jointly uniform. -/
theorem openings_uniform (ω : Cells Hd.toBlindingFields) {t : ℕ} (q : Tableau.Query N t)
    (ht : t ≤ C.k - P.witness.card) : Uniform (openings ω q) :=
  IdentDistrib.pi (f := fun row => rowOpening ω q row) (g := fun _ => id)
    fun row => rowOpening_uniform ω q row ht

/-! ## The responses, for fixed privacy coins -/

omit [Fintype F] in
theorem simulate_eq (r : Tableau.Challenge F R nL nQ nrep) {t : ℕ}
    (q : Tableau.Query N t) (s : SimCoins hrate Hd t nrep) :
    simulate L hrate Hd r q s =
      publicView L r q (fun i j => s.openings i j) (simResponse L hrate Hd r s.response) := rfl

variable (Hd) in
omit [Fintype F] in
/-- The honest linear response, less the public offset, is an IDOT mask. -/
theorem dotResponse_sub_mem (H : Completeness.HonestTableau (C := C) (P := P) (L := L) hrate nrep)
    (r : Tableau.Challenge F R nL nQ nrep) :
    (Completeness.dotResponse H r -
        Polynomial.C (∑ l, r.2.1 l * L.target l) * unitDot Hd).natDegree <
        (MaskedPolynomialTest.maskCode C hrate).k ∧
      Tableau.dotCheck C P (Completeness.dotResponse H r -
        Polynomial.C (∑ l, r.2.1 l * L.target l) * unitDot Hd) = 0 := by
  have hv := Completeness.valid H r
  have hk : C.k ≤ (MaskedPolynomialTest.maskCode C hrate).k := by
    change C.k ≤ 2 * C.k - 1
    have := C.k_pos
    omega
  refine ⟨(natDegree_sub_le _ _).trans_lt (max_lt (Completeness.dotResponse_degree H hrate r)
    ((natDegree_C_mul_le _ _).trans_lt ((unitDot_degree (Hd := Hd)).trans_le hk))), ?_⟩
  have hd : Tableau.dotCheck C P (Completeness.dotResponse H r) =
      ∑ l, r.2.1 l * L.target l := by
    have := hv.1
    rwa [Completeness.response_dot] at this
  rw [map_sub, ← Polynomial.smul_eq_C_mul, map_smul, dotCheck_unitDot, hd, smul_eq_mul, mul_one,
    sub_self]

/-- For fixed privacy coins, the map from the response coins to the responses,
rewritten as the simulator's sample: a translation of each coin. -/
noncomputable def responseShift (ω : Witness L Hd.toBlindingFields) (r : Tableau.Challenge F R nL nQ nrep)
    (ρ : ∀ row : Fin R, Privacy P → Hd.field row) (x : ResponseCoins P hrate nrep) :
    ResponseCoins P hrate nrep :=
  ⟨x.ildt + fun j => ∑ i, r.1 j i • rowValues ω.toCells ρ i,
    ⟨_, dotResponse_sub_mem Hd (honest Hd.products_ne_zero ω ⟨ρ, x⟩) r⟩,
    ⟨Completeness.quadResponse (honest Hd.products_ne_zero ω ⟨ρ, x⟩) r,
      Completeness.quadResponse_degree (honest Hd.products_ne_zero ω ⟨ρ, x⟩) hrate r,
      fun j => by
        have := (Completeness.valid (honest Hd.products_ne_zero ω ⟨ρ, x⟩) r).2 j
        rwa [Completeness.response_quad] at this⟩⟩

omit [Fintype F] in
@[simp] theorem responseShift_ildt (ω : Witness L Hd.toBlindingFields)
    (r : Tableau.Challenge F R nL nQ nrep) (ρ : ∀ row : Fin R, Privacy P → Hd.field row)
    (x : ResponseCoins P hrate nrep) :
    (responseShift ω r ρ x).ildt = x.ildt + fun j => ∑ i, r.1 j i • rowValues ω.toCells ρ i :=
  rfl

omit [Fintype F] in
@[simp] theorem responseShift_dotMask (ω : Witness L Hd.toBlindingFields)
    (r : Tableau.Challenge F R nL nQ nrep) (ρ : ∀ row : Fin R, Privacy P → Hd.field row)
    (x : ResponseCoins P hrate nrep) :
    (responseShift ω r ρ x).dotMask.1 =
      Completeness.dotResponse (honest Hd.products_ne_zero ω ⟨ρ, x⟩) r -
      Polynomial.C (∑ l, r.2.1 l * L.target l) * unitDot Hd := rfl

omit [Fintype F] in
@[simp] theorem responseShift_quadMask (ω : Witness L Hd.toBlindingFields)
    (r : Tableau.Challenge F R nL nQ nrep) (ρ : ∀ row : Fin R, Privacy P → Hd.field row)
    (x : ResponseCoins P hrate nrep) :
    (responseShift ω r ρ x).quadMask.1 =
      Completeness.quadResponse (honest Hd.products_ne_zero ω ⟨ρ, x⟩) r := rfl

omit [Fintype F] in
theorem responseShift_injective (ω : Witness L Hd.toBlindingFields)
    (r : Tableau.Challenge F R nL nQ nrep)
    (ρ : ∀ row : Fin R, Privacy P → Hd.field row) :
    Function.Injective (responseShift (hrate := hrate) ω r ρ) := by
  intro x x' h
  have h1 := congrArg ResponseCoins.ildt h
  have h2 := congrArg (fun z => z.dotMask.1) h
  have h3 := congrArg (fun z => z.quadMask.1) h
  simp only [responseShift_ildt, add_left_inj] at h1
  simp only [responseShift_dotMask, dotResponse_honest, rows_congr ω.toCells ρ h1, sub_left_inj,
    add_left_inj] at h2
  simp only [responseShift_quadMask, quadResponse_honest, rows_congr ω.toCells ρ h1,
    add_left_inj] at h3
  exact ResponseCoins.ext h1 (Subtype.ext h2) (Subtype.ext h3)

/-- **The responses**. For fixed privacy coins, the three responses have the simulator's law. -/
theorem response_identDistrib (ω : Witness L Hd.toBlindingFields) (r : Tableau.Challenge F R nL nQ nrep)
    (ρ : ∀ row : Fin R, Privacy P → Hd.field row) :
    (fun x : ResponseCoins P hrate nrep =>
        Completeness.response (honest Hd.products_ne_zero ω ⟨ρ, x⟩) r) =ᵈ
      (simResponse L hrate Hd r) := by
  refine IdentDistrib.of_equiv (Equiv.ofBijective _
    (responseShift_injective (hrate := hrate) ω r ρ).bijective_of_finite) fun x => ?_
  change Completeness.response _ r = simResponse L hrate Hd r (responseShift ω r ρ x)
  have hc : Completeness.codeResponse (honest Hd.products_ne_zero ω ⟨ρ, x⟩) r =
      fun j => LigeroInterpolation.interpolate P.nodes ((responseShift ω r ρ x).ildt j) :=
    funext fun j => by
      rw [codeResponse_honest Hd.products_ne_zero ω ⟨ρ, x⟩ r j]
      rfl
  rw [simResponse_eq, Completeness.response, hc, responseShift_dotMask, responseShift_quadMask,
    sub_add_cancel]

/-- **Perfect honest-verifier zero-knowledge of one tableau.** For every honest
witness, challenge and query set of at most as many columns as there are
privacy positions, the honest view and the simulated view have the same
distribution. `ht`: a parameter condition, the hiding threshold `t ≤ r`. -/
theorem identDistrib (ω : Witness L Hd.toBlindingFields) (r : Tableau.Challenge F R nL nQ nrep) {t : ℕ}
    (q : Tableau.Query N t) (ht : t ≤ C.k - P.witness.card) :
    (honestView (hrate := hrate) ω r q) =ᵈ simulate L hrate Hd r q := by
  have hdep : (fun c : (∀ row : Fin R, Privacy P → Hd.field row) × ResponseCoins P hrate nrep =>
        (openings ω.toCells q c.1,
          Completeness.response (honest Hd.products_ne_zero ω ⟨c.1, c.2⟩) r)) =ᵈ
      (fun s : (∀ row : Fin R, Fin t → Hd.field row) × ResponseCoins P hrate nrep =>
        (s.1, simResponse L hrate Hd r s.2)) :=
    IdentDistrib.dependent (g₁ := id) (g₂ := fun _ => simResponse L hrate Hd r)
      (openings_uniform ω.toCells q ht) (fun ρ => response_identDistrib ω r ρ)
  let k := fun x : (∀ row : Fin R, Fin t → Hd.field row) × Tableau.Response F C.k nrep =>
    publicView L r q (fun i j => x.1 i j) x.2
  have h := ((hdep.comp k).comp_equiv (Coins.equivProd hrate Hd.toBlindingFields nrep)).trans
    (IdentDistrib.of_equiv (SimCoins.equivProd hrate Hd t nrep) fun _ => rfl).symm
  have h1 : honestView (hrate := hrate) ω r q = fun c =>
      k (openings ω.toCells q c.privacy, Completeness.response (honest Hd.products_ne_zero ω c) r) :=
    funext fun c => (honestView_eq Hd.products_ne_zero ω r q c).trans
      (view_honest (honest Hd.products_ne_zero ω c) r q)
  have h2 : simulate L hrate Hd r q = fun s => k (s.openings, simResponse L hrate Hd r s.response) :=
    funext fun s => simulate_eq r q s
  rw [h1, h2]
  exact h
end

end GordieHowe.Ligero.HVZK
