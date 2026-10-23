-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Ligero.MaskTest.Pieces
public import GordieHowe.ProofSystem.Ligero.MaskPieces

@[expose] public section

/-!
# The honest prover of Ligero at agreement threshold `A` with the mask test

The honest prover of `GordieHowe.Ligero.MaskTest.Pieces`, its completeness and
its hiding.

**The honest prover.** It draws the coins of the unsplit honest prover (`Ligero.HVZK.Coins`: the
ILDT values, the privacy values of each data row, the IDOT and IQUAD masks uniform in their honest
mask spaces) and, for each mask `M`, a uniform element of the kernel of the three-piece splitting
map (`Kernel`, `GordieHowe.Ligero.MaskPieces.kernel`). The pieces of `M` are the coefficient-block splitting
`(M mod X ^ k, 0, M div X ^ k)` (`blockSplit`) plus the kernel element (`honestPieces`): a uniform
splitting of `M`. The tableau rows (`ZK.honestRows`) are the unsplit honest rows with the six
piece rows replaced by the pieces (`PieceRows.fill`); the masks recombined from the piece rows are
the honest masks (`ZK.masks_honestCommit`).

**Completeness** (`honest`, field `complete`). The piece rows are separate from the data
(`PieceRows.Separate`: distinct, not row 0, not read by the linear system or a product group), so
the rows still satisfy the constraints and `Ligero.Completeness.accept` applies to the tableau with
the honest masks.

**Hiding** (`ZK.identDistrib`). The view is the public map `Ligero.HVZK.publicView` of the
data-row openings and the three responses (`Ligero.HVZK.view_honest`), where a piece row's
openings are those of its piece. At each queried column the opening of the piece `A` of a mask is
the mask's value (read off the masked response and the data columns) minus the recombination of
the openings of `C` and `B` (`ZK.simData`). So the view is a public function of the openings of the
other data rows, the three responses and the openings of the pieces `C` and `B`. Their joint law
does not depend on the witness:

* the data rows' openings are uniform (`Ligero.HVZK.openings_uniform`);
* for fixed privacy values, each repetition's low-degree response absorbs the piece rows through
  its own ILDT values (a translation of that repetition's ILDT coins, `ZK.ildtOffset`), and the three responses have the law of the
  unsplit simulator's (`Ligero.HVZK.response_identDistrib`);
* for each mask, the openings of `C` and `B` of a uniform splitting are uniform and independent of
  the mask (`honestOpenings_uniform`): the values of the pieces `C` and `B` of a kernel element
  cover every pair when `2t ≤ k` (`GordieHowe.Ligero.MaskPieces.kernelOpenings_surjective`, from the covering
  lemma `GordieHowe.Ligero.MaskPieces.exists_splitting_vanishing`).

The simulator (`ZK.simulate`) samples these quantities directly: the unsplit simulator's coins and
uniform openings of `C` and `B` for each mask.
-/

namespace GordieHowe.Ligero.MaskTest.Pieces
open IOP

open ProtocolSpec Polynomial
open Ligero.MaskPieces (threeShifts threeBounds)
open Ligero.AgreementThreshold (commitSpec ldtIdx proofSpec ConstraintChallenge chQuery ldtChallenge
  TableauSetup)

/-! ### The piece rows of a tableau -/

section Fill

variable {R : ℕ}

/-- **The rows of the pieces** `A`, `C`, `B` of one mask, in this order. -/
def Pieces.row (pc : Pieces R) : Fin 3 → Fin (R + 1) := ![pc.rowA, pc.rowC, pc.rowB]

namespace PieceRows

variable (pr : PieceRows R)

/-- **The six piece rows**: IDOT `A`, `C`, `B`, then IQUAD `A`, `C`, `B`. -/
def toList : List (Fin (R + 1)) :=
  [pr.dot.rowA, pr.dot.rowC, pr.dot.rowB, pr.quad.rowA, pr.quad.rowC, pr.quad.rowB]

/-- **The rows with the pieces placed**: at the piece rows the entries of `dot` and `quad` (in the
order `A`, `C`, `B`), at every other row the entry of `other`. Computable: it compares row
indices. -/
def fill {α : Type} (dot quad : Fin 3 → α) (other : Fin (R + 1) → α) (row : Fin (R + 1)) : α :=
  if row = pr.dot.rowA then dot 0 else if row = pr.dot.rowC then dot 1 else
  if row = pr.dot.rowB then dot 2 else if row = pr.quad.rowA then quad 0 else
  if row = pr.quad.rowC then quad 1 else if row = pr.quad.rowB then quad 2 else other row

variable {pr}

theorem fill_of_not_mem {α : Type} {dot quad : Fin 3 → α} {other : Fin (R + 1) → α}
    {row : Fin (R + 1)} (h : row ∉ pr.toList) : pr.fill dot quad other row = other row := by
  simp only [toList, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp [fill, h1, h2, h3, h4, h5, h6]

/-- The rows with the pieces placed read `other` only outside the piece rows. -/
theorem fill_congr {α : Type} {dot quad : Fin 3 → α} {other other' : Fin (R + 1) → α}
    {row : Fin (R + 1)} (h : row ∉ pr.toList → other row = other' row) :
    pr.fill dot quad other row = pr.fill dot quad other' row := by
  by_cases hm : row ∈ pr.toList
  · simp only [toList, List.mem_cons, List.not_mem_nil, or_false] at hm
    unfold fill
    rcases hm with h1 | h1 | h1 | h1 | h1 | h1 <;> simp [h1]
  · rw [fill_of_not_mem hm, fill_of_not_mem hm, h hm]

/-- A function applied to the rows with the pieces placed places the function's values. -/
theorem fill_map {α β : Type} (g : α → β) (dot quad : Fin 3 → α) (other : Fin (R + 1) → α)
    (row : Fin (R + 1)) :
    g (pr.fill dot quad other row) = pr.fill (g ∘ dot) (g ∘ quad) (g ∘ other) row := by
  unfold fill
  split_ifs <;> rfl

/-- A property of every entry holds for the rows with the pieces placed. -/
theorem fill_mem {α : Type} {p : α → Prop} {dot quad : Fin 3 → α} {other : Fin (R + 1) → α}
    (hd : ∀ m, p (dot m)) (hq : ∀ m, p (quad m)) (ho : ∀ row, p (other row))
    (row : Fin (R + 1)) : p (pr.fill dot quad other row) := by
  unfold fill
  split_ifs
  exacts [hd 0, hd 1, hd 2, hq 0, hq 1, hq 2, ho row]

/-- At an IDOT piece row, the rows with the pieces placed hold the IDOT entry. -/
theorem fill_dot {α : Type} (hn : pr.toList.Nodup) (dot quad : Fin 3 → α)
    (other : Fin (R + 1) → α) (m : Fin 3) : pr.fill dot quad other (pr.dot.row m) = dot m := by
  simp only [toList, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩, ⟨h10, h11, h12⟩, -⟩ := hn
  fin_cases m <;> simp [fill, Pieces.row, Ne.symm h1, Ne.symm h2, Ne.symm h6]

/-- At an IQUAD piece row, the rows with the pieces placed hold the IQUAD entry. -/
theorem fill_quad {α : Type} (hn : pr.toList.Nodup) (dot quad : Fin 3 → α)
    (other : Fin (R + 1) → α) (m : Fin 3) : pr.fill dot quad other (pr.quad.row m) = quad m := by
  simp only [toList, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
  obtain ⟨⟨h1, h2, h3, h4, h5⟩, ⟨h6, h7, h8, h9⟩, ⟨h10, h11, h12⟩, ⟨h13, h14⟩, h15, -⟩ := hn
  fin_cases m <;> simp [fill, Pieces.row, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h7,
    Ne.symm h8, Ne.symm h9, Ne.symm h10, Ne.symm h11, Ne.symm h12, Ne.symm h13, Ne.symm h14,
    Ne.symm h15]

end PieceRows

end Fill

/-! ### The piece rows are separate from the data -/

section Separate

variable {F : Type} [Field F] {N R nL nQ : ℕ} {C : GordieHowe.RSCode F N}
  {P : Tableau.Parameters (R := R) (nQ := nQ) C}

/-- **The piece rows are separate from the data** of the linear system `L` (parameter
conditions): the six rows are distinct, none is the ILDT row `0`, the linear system has zero
coefficients on them, and no product group reads one. -/
structure PieceRows.Separate (pr : PieceRows R) (L : Tableau.LinearSystem (nL := nL) C P) :
    Prop where
  nodup : pr.toList.Nodup
  zero_not_mem : (0 : Fin (R + 1)) ∉ pr.toList
  coeff_eq_zero : ∀ l, ∀ row ∈ pr.toList, L.coeff l row = 0
  products_not_mem : ∀ q i, P.products q i ∉ pr.toList

variable {pr : PieceRows R} {L : Tableau.LinearSystem (nL := nL) C P}

namespace PieceRows.Separate

variable (hs : pr.Separate L)
include hs

/-- The linear polynomials read neither row `0` nor the piece rows. -/
theorem dotPolynomials_congr {fs gs : Fin (R + 1) → F[X]}
    (h : ∀ row, row ≠ 0 → row ∉ pr.toList → fs row = gs row) (l : Fin nL) :
    Tableau.dotPolynomials C P L fs l = Tableau.dotPolynomials C P L gs l := by
  unfold Tableau.dotPolynomials LigeroInterpolation.decodedDot
  refine Finset.sum_congr rfl fun row _ => ?_
  by_cases h0 : row = 0
  · subst h0
    have hc : L.coeff l 0 = 0 := funext (L.ildt_zero l)
    simp [hc]
  by_cases hm : row ∈ pr.toList
  · simp [hs.coeff_eq_zero l row hm]
  · rw [h row h0 hm]

/-- The quadratic polynomials read neither row `0` nor the piece rows, when no product group reads
row `0`. -/
theorem quadPolynomials_congr (hprod : ∀ q i, P.products q i ≠ 0) {fs gs : Fin (R + 1) → F[X]}
    (h : ∀ row, row ≠ 0 → row ∉ pr.toList → fs row = gs row) (q : Fin nQ) :
    Tableau.quadPolynomials C P fs q = Tableau.quadPolynomials C P gs q := by
  have hr : ∀ i, fs (P.products q i) = gs (P.products q i) := fun i =>
    h _ (hprod q i) (hs.products_not_mem q i)
  simp only [Tableau.quadPolynomials, hr]

/-- The constraints read neither row `0` nor the piece rows, when no product group reads row
`0`. -/
theorem holds_congr (hprod : ∀ q i, P.products q i ≠ 0) {fs gs : Fin (R + 1) → F[X]}
    (h : ∀ row, row ≠ 0 → row ∉ pr.toList → fs row = gs row) :
    Tableau.Holds C P L fs ↔ Tableau.Holds C P L gs := by
  unfold Tableau.Holds MaskedConstraintFamily.Claim
  simp only [hs.dotPolynomials_congr h, hs.quadPolynomials_congr hprod h]

/-- The linear column sources read neither row `0` nor the piece rows. -/
theorem dotAt_congr {col col' : Fin (R + 1) → F}
    (h : ∀ row, row ≠ 0 → row ∉ pr.toList → col row = col' row) (l : Fin nL) (x : F) :
    HVZK.dotAt (L := L) col l x = HVZK.dotAt (L := L) col' l x := by
  unfold HVZK.dotAt
  refine Finset.sum_congr rfl fun row _ => ?_
  by_cases h0 : row = 0
  · subst h0
    have hc : L.coeff l 0 = 0 := funext (L.ildt_zero l)
    simp [hc, LigeroInterpolation.interpolateEval]
  by_cases hm : row ∈ pr.toList
  · simp [hs.coeff_eq_zero l row hm, LigeroInterpolation.interpolateEval]
  · rw [h row h0 hm]

/-- The quadratic column sources read neither row `0` nor the piece rows, when no product group
reads row `0`. -/
theorem quadAt_congr (hprod : ∀ q i, P.products q i ≠ 0) {col col' : Fin (R + 1) → F}
    (h : ∀ row, row ≠ 0 → row ∉ pr.toList → col row = col' row) (q : Fin nQ) :
    HVZK.quadAt (P := P) col q = HVZK.quadAt (P := P) col' q := by
  have hr : ∀ i, col (P.products q i) = col' (P.products q i) := fun i =>
    h _ (hprod q i) (hs.products_not_mem q i)
  simp only [HVZK.quadAt, hr]

end PieceRows.Separate

/-- The linear polynomials' values are the linear column sources of the rows' values. -/
theorem eval_dotPolynomials (L : Tableau.LinearSystem (nL := nL) C P)
    (fs : Fin (R + 1) → F[X]) (l : Fin nL) (x : F) :
    (Tableau.dotPolynomials C P L fs l).eval x =
      HVZK.dotAt (L := L) (fun row => (fs row).eval x) l x := by
  simp only [Tableau.dotPolynomials, LigeroInterpolation.decodedDot, eval_finsetSum, eval_mul,
    LigeroInterpolation.eval_interpolate, HVZK.dotAt]

/-- The quadratic polynomials' values are the quadratic column sources of the rows' values. -/
theorem eval_quadPolynomials (fs : Fin (R + 1) → F[X]) (q : Fin nQ) (x : F) :
    (Tableau.quadPolynomials C P fs q).eval x =
      HVZK.quadAt (P := P) (fun row => (fs row).eval x) q := by
  simp only [Tableau.quadPolynomials, eval_sub, eval_mul, HVZK.quadAt]

end Separate

/-! ### The honest splitting of a mask -/

section Splitting

variable {F : Type} [Field F]

/-- **The kernel coins** for `k` and `t`: the splittings of zero in the three-piece split
`A + X ^ (k − t) · C + X ^ k · B` (`MaskPieces.kernel`). The honest prover draws one uniformly
for each mask. -/
abbrev Kernel (F : Type) [Field F] (k t : ℕ) : Type :=
  MaskPieces.kernel F (threeShifts k t) (threeBounds k)

/-- **The coefficient-block splitting** of `M`: `(M mod X ^ k, 0, M div X ^ k)`. -/
noncomputable def blockSplit (k : ℕ) (M : F[X]) : Fin 3 → F[X] :=
  ![M %ₘ (Polynomial.X ^ k : F[X]), 0, M /ₘ (Polynomial.X ^ k : F[X])]

/-- The coefficient-block splitting of a polynomial of degree `< 2k − 1` is a three-piece
splitting. -/
theorem isSplitting_blockSplit (t : ℕ) {k : ℕ} {M : F[X]} (hM : M.natDegree < 2 * k - 1) :
    MaskPieces.IsSplitting (threeShifts k t) (threeBounds k) M (blockSplit k M) := by
  refine ⟨fun m => ?_, ?_⟩
  · fin_cases m
    · simpa [blockSplit, threeBounds] using degree_modByMonic_lt M (monic_X_pow (R := F) k)
    · simp [blockSplit, threeBounds]
    · show (M /ₘ (Polynomial.X ^ k : F[X])).degree < ((k - 1 : ℕ) : WithBot ℕ)
      by_cases h0 : M /ₘ (Polynomial.X ^ k : F[X]) = 0
      · simp [h0]
      · have hk : (Polynomial.X ^ k : F[X]).natDegree = k := natDegree_X_pow k
        have hd := natDegree_divByMonic M (monic_X_pow (R := F) k)
        rw [hk] at hd
        have hge : k ≤ M.natDegree := by
          by_contra hlt
          apply h0
          rw [divByMonic_eq_zero_iff (monic_X_pow (R := F) k), degree_X_pow]
          exact (degree_le_natDegree).trans_lt (by exact_mod_cast (not_le.mp hlt))
        rw [degree_eq_natDegree h0]
        exact_mod_cast (show (M /ₘ (Polynomial.X ^ k : F[X])).natDegree < k - 1 by omega)
  · rw [MaskPieces.split_three]
    simpa [blockSplit, add_comm] using modByMonic_add_div M (Polynomial.X ^ k : F[X])

/-- **The honest pieces** of the mask `M` with the kernel coin `κ`: the coefficient-block
splitting plus `κ`, a uniform splitting of `M` when `κ` is uniform. -/
noncomputable def honestPieces {k t : ℕ} (M : F[X]) (κ : Kernel F k t) : Fin 3 → F[X] :=
  blockSplit k M + (κ : Fin 3 → F[X])

theorem isSplitting_honestPieces {k t : ℕ} {M : F[X]} (hM : M.natDegree < 2 * k - 1)
    (κ : Kernel F k t) :
    MaskPieces.IsSplitting (threeShifts k t) (threeBounds k) M (honestPieces M κ) := by
  simpa [honestPieces] using (isSplitting_blockSplit t hM).add (MaskPieces.mem_kernel.mp κ.2)

/-- The honest pieces recombine to the mask. -/
theorem recombinePoly_honestPieces {k t : ℕ} {M : F[X]} (hM : M.natDegree < 2 * k - 1)
    (κ : Kernel F k t) :
    recombinePoly k t (honestPieces M κ 0) (honestPieces M κ 1) (honestPieces M κ 2) = M := by
  rw [recombinePoly, ← MaskPieces.split_three]
  exact (isSplitting_honestPieces hM κ).split_eq

/-- Every honest piece has degree `< k`. -/
theorem natDegree_honestPieces_lt {k t : ℕ} (hk : 0 < k) {M : F[X]} (hM : M.natDegree < 2 * k - 1)
    (κ : Kernel F k t) (m : Fin 3) : (honestPieces M κ m).natDegree < k := by
  have h := (isSplitting_honestPieces hM κ).degree_lt m
  have hb : threeBounds k m ≤ k := by fin_cases m <;> simp [threeBounds]
  by_cases h0 : honestPieces M κ m = 0
  · rw [h0, natDegree_zero]
    exact hk
  · rw [degree_eq_natDegree h0] at h
    exact lt_of_lt_of_le (by exact_mod_cast h) hb

/-- **The openings of the pieces `C` and `B`** of one mask at the `t` queried columns. -/
@[ext]
structure PieceOpenings (F : Type) (t : ℕ) where
  /-- The openings of the piece `C`. -/
  c : Fin t → F
  /-- The openings of the piece `B`. -/
  b : Fin t → F

/-- Piece openings as the pair of their value vectors. -/
def PieceOpenings.equivProd (F : Type) (t : ℕ) : PieceOpenings F t ≃ (Fin t → F) × (Fin t → F) where
  toFun o := (o.c, o.b)
  invFun y := ⟨y.1, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype F] [DecidableEq F] (t : ℕ) : Fintype (PieceOpenings F t) :=
  Fintype.ofEquiv _ (PieceOpenings.equivProd F t).symm

instance (t : ℕ) : Nonempty (PieceOpenings F t) := ⟨⟨0, 0⟩⟩

/-- **The honest openings of the pieces `C` and `B`** of the mask `M` with the kernel coin `κ` at
the points `x`. -/
noncomputable def honestOpenings {k t : ℕ} (x : Fin t → F) (M : F[X]) (κ : Kernel F k t) :
    PieceOpenings F t :=
  ⟨fun s => (honestPieces M κ 1).eval (x s), fun s => (honestPieces M κ 2).eval (x s)⟩

/-- **The honest openings of `C` and `B` are uniform**, whatever the mask: the kernel coin's
openings of `C` and `B` cover every pair (`MaskPieces.kernelOpenings_surjective`, for `2t ≤ k`
and distinct points), and the block splitting adds a fixed value. -/
theorem honestOpenings_uniform [Fintype F] [DecidableEq F] {k t : ℕ} (h : 2 * t ≤ k)
    {x : Fin t → F} (hx : Function.Injective x) (M : F[X]) :
    Uniform (honestOpenings (k := k) x M) := by
  let φ : Kernel F k t →+ (Fin t → F) × (Fin t → F) :=
    { toFun := fun κ => (fun j => (κ.1 1).eval (x j), fun j => (κ.1 2).eval (x j))
      map_zero' := by ext <;> simp
      map_add' := fun a b => by ext <;> simp }
  have hu := Uniform.of_surjective φ (MaskPieces.kernelOpenings_surjective h hx)
    (fun j => (blockSplit k M 1).eval (x j), fun j => (blockSplit k M 2).eval (x j))
  have he : honestOpenings (k := k) x M =
      (PieceOpenings.equivProd F t).symm ∘ fun κ => φ κ + (fun j => (blockSplit k M 1).eval (x j),
        fun j => (blockSplit k M 2).eval (x j)) := by
    funext κ
    ext s
    · simp [honestOpenings, honestPieces, φ, PieceOpenings.equivProd, add_comm]
    · simp [honestOpenings, honestPieces, φ, PieceOpenings.equivProd, add_comm]
  rw [he]
  exact (hu.comp _).trans (Uniform.of_equiv _)

end Splitting

/-! ### The honest tableau and its simulator -/

namespace ZK

section

variable {F : Type} [Field F] [Fintype F] {N R nL nQ : ℕ} {C : GordieHowe.RSCode F N}
  {P : Tableau.Parameters (R := R) (nQ := nQ) C} {L : Tableau.LinearSystem (nL := nL) C P}
  {hrate : 2 * C.k - 1 ≤ N} {nrep : ℕ}

variable (hrate) in
/-- **The honest prover's coins** with `t` queried columns: the coins of the unsplit honest prover
(`Ligero.HVZK.Coins`: the ILDT values, the privacy values, the IDOT and IQUAD masks) and a kernel
coin for each mask (`Kernel`). -/
@[ext]
structure Coins (Bf : HVZK.BlindingFields C P) (t nrep : ℕ) where
  /-- The coins of the unsplit honest prover. -/
  inner : HVZK.Coins hrate Bf nrep
  /-- The kernel coin splitting the IDOT mask. -/
  dotKernel : Kernel F C.k t
  /-- The kernel coin splitting the IQUAD mask. -/
  quadKernel : Kernel F C.k t

variable (hrate) in
/-- The honest coins as the privacy values, the response coins and the two kernel coins. -/
def Coins.equivProd (Bf : HVZK.BlindingFields C P) (t nrep : ℕ) :
    Coins hrate Bf t nrep ≃ (∀ row : Fin R, HVZK.Privacy P → Bf.field row) ×
      (HVZK.ResponseCoins P hrate nrep × (Kernel F C.k t × Kernel F C.k t)) where
  toFun c := (c.inner.privacy, c.inner.response, c.dotKernel, c.quadKernel)
  invFun y := ⟨⟨y.1, y.2.1⟩, y.2.2.1, y.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (Bf : HVZK.BlindingFields C P) (t : ℕ) : Fintype (Coins hrate Bf t nrep) := by
  classical
  exact Fintype.ofEquiv _ (Coins.equivProd hrate Bf t nrep).symm

instance (Bf : HVZK.BlindingFields C P) (t : ℕ) : Nonempty (Coins hrate Bf t nrep) :=
  ⟨⟨Classical.arbitrary _, 0, 0⟩⟩

variable {Bf : HVZK.BlindingFields C P} (pr : PieceRows R) {t : ℕ}

/-- The IDOT mask of the honest coins. -/
abbrev Coins.dotMask (c : Coins hrate Bf t nrep) : F[X] := c.inner.response.dotMask.1

/-- The IQUAD mask of the honest coins. -/
abbrev Coins.quadMask (c : Coins hrate Bf t nrep) : F[X] := c.inner.response.quadMask.1

omit [Fintype F] in
theorem Coins.natDegree_dotMask_lt (c : Coins hrate Bf t nrep) : c.dotMask.natDegree < 2 * C.k - 1 :=
  c.inner.response.dotMask.2.1

omit [Fintype F] in
theorem Coins.natDegree_quadMask_lt (c : Coins hrate Bf t nrep) :
    c.quadMask.natDegree < 2 * C.k - 1 :=
  c.inner.response.quadMask.2.1

variable [NeZero nrep]

/-- **The honest rows**: the pieces of the IDOT and IQUAD masks (`honestPieces`) at the piece rows,
the unsplit honest rows (`Ligero.HVZK.rows`) elsewhere. -/
noncomputable def honestRows (ω : HVZK.Cells Bf) (c : Coins hrate Bf t nrep) : Fin (R + 1) → F[X] :=
  pr.fill (honestPieces c.dotMask c.dotKernel)
    (honestPieces c.quadMask c.quadKernel) (HVZK.rows ω c.inner)

variable {pr}

omit [Fintype F] in
theorem honestRows_of_not_mem (ω : HVZK.Cells Bf) (c : Coins hrate Bf t nrep) {row : Fin (R + 1)}
    (h : row ∉ pr.toList) : honestRows pr ω c row = HVZK.rows ω c.inner row :=
  PieceRows.fill_of_not_mem h

omit [Fintype F] in
theorem honestRows_dot (hn : pr.toList.Nodup) (ω : HVZK.Cells Bf) (c : Coins hrate Bf t nrep)
    (m : Fin 3) :
    honestRows pr ω c (pr.dot.row m) = honestPieces c.dotMask c.dotKernel m :=
  PieceRows.fill_dot hn _ _ _ m

omit [Fintype F] in
theorem honestRows_quad (hn : pr.toList.Nodup) (ω : HVZK.Cells Bf) (c : Coins hrate Bf t nrep)
    (m : Fin 3) :
    honestRows pr ω c (pr.quad.row m) = honestPieces c.quadMask c.quadKernel m :=
  PieceRows.fill_quad hn _ _ _ m

omit [Fintype F] in
/-- The honest rows have degree `< k`. -/
theorem natDegree_honestRows_lt (ω : HVZK.Cells Bf) (c : Coins hrate Bf t nrep) (row : Fin (R + 1)) :
    (honestRows pr ω c row).natDegree < C.k :=
  PieceRows.fill_mem (p := fun f : F[X] => f.natDegree < C.k)
    (natDegree_honestPieces_lt C.k_pos c.natDegree_dotMask_lt _)
    (natDegree_honestPieces_lt C.k_pos c.natDegree_quadMask_lt _)
    (HVZK.rows_degree ω c.inner) row

omit [Fintype F] in
/-- The honest data rows read the privacy values, the masks and the kernel coins, not the ILDT
values. -/
theorem honestRows_succ_congr (ω : HVZK.Cells Bf) (ρ : ∀ row : Fin R, HVZK.Privacy P → Bf.field row)
    (v v' : Fin nrep → Fin C.k → F) (dm : HVZK.DotMasks C P hrate) (qm : HVZK.QuadMasks C P hrate)
    (κd κq : Kernel F C.k t) (i : Fin R) :
    honestRows pr ω (⟨⟨ρ, ⟨v, dm, qm⟩⟩, κd, κq⟩ : Coins hrate Bf t nrep) i.succ =
      honestRows pr ω (⟨⟨ρ, ⟨v', dm, qm⟩⟩, κd, κq⟩ : Coins hrate Bf t nrep) i.succ :=
  PieceRows.fill_congr fun _ => rfl

variable (pr) in
/-- **The honest rows of repetition `j`'s matrix**: the interpolant of `ILDT_j`'s values, then the
honest data rows (`honestRows`). -/
noncomputable def honestLdtRows (ω : HVZK.Cells Bf) (c : Coins hrate Bf t nrep) (j : Fin nrep) :
    Fin (R + 1) → F[X] :=
  Fin.cons (LigeroInterpolation.interpolate P.nodes (c.inner.response.ildt j))
    fun i => honestRows pr ω c i.succ

omit [Fintype F] in
/-- Repetition `0`'s honest rows are the honest rows, the piece rows not being row `0`. -/
theorem honestLdtRows_zero (hz : (0 : Fin (R + 1)) ∉ pr.toList) (ω : HVZK.Cells Bf)
    (c : Coins hrate Bf t nrep) : honestLdtRows pr ω c 0 = honestRows pr ω c := by
  funext row
  refine Fin.cases ?_ (fun _ => rfl) row
  rw [honestRows_of_not_mem ω c hz]
  rfl

omit [Fintype F] in
theorem natDegree_honestLdtRows_lt (ω : HVZK.Cells Bf) (c : Coins hrate Bf t nrep) (j : Fin nrep)
    (row : Fin (R + 1)) : (honestLdtRows pr ω c j row).natDegree < C.k :=
  Fin.cases (LigeroInterpolation.interpolate_degree C.k_pos P.nodes_injective _)
    (fun i => natDegree_honestRows_lt ω c i.succ) row

variable (pr) in
/-- **The honest commitment**: the honest ILDT rows and data rows at the code's evaluation
points. -/
noncomputable def honestCommit (ω : HVZK.Cells Bf) (c : Coins hrate Bf t nrep) :
    Tableau.Rows F N R nrep :=
  ⟨fun j col => (LigeroInterpolation.interpolate P.nodes (c.inner.response.ildt j)).eval (C.D col),
    fun i col => (honestRows pr ω c i.succ).eval (C.D col)⟩

omit [Fintype F] in
/-- The tableau of the honest commitment is the honest rows' values. -/
theorem honestCommit_tableau (hz : (0 : Fin (R + 1)) ∉ pr.toList) (ω : HVZK.Cells Bf)
    (c : Coins hrate Bf t nrep) :
    (honestCommit pr ω c).tableau = fun row col => (honestRows pr ω c row).eval (C.D col) := by
  funext row col
  rw [← honestLdtRows_zero hz]
  exact Fin.cases rfl (fun _ => rfl) row

variable (pr) in
/-- **The honest low-degree responses** to the challenges `r`: for each repetition `j`, the values
at the first `k` response nodes of `honestLdtRows j 0 + Σ r_{j,i} · honestLdtRows j (i + 1)`. They
read neither the linear system nor the constraint challenge. -/
noncomputable def honestLdtResponse (ω : HVZK.Cells Bf) (c : Coins hrate Bf t nrep)
    (r : Tableau.LdtChallenge F R nrep) : Tableau.LdtResponse F C.k nrep :=
  fun j i => (AffineCodeTest.projectedPolynomial (honestLdtRows pr ω c j) (r j)).eval
    (Tableau.responseNode C C.k i)

variable (L pr) in
/-- **The honest masked responses** to the challenge `r`: the values at the first `2k − 1` response
nodes of each mask plus the batched constraint polynomials of the honest rows. -/
noncomputable def honestMasked (ω : HVZK.Cells Bf) (c : Coins hrate Bf t nrep)
    (r : Tableau.Challenge F R nL nQ nrep) : Ligero.AgreementThreshold.MaskedResponse F C.k :=
  (fun i => (c.dotMask + MaskedConstraintTest.batch
      (fun l => Tableau.dotPolynomials C P L (honestLdtRows pr ω c 0) l) r.2.1).eval
        (Tableau.responseNode C (2 * C.k - 1) i),
    fun i => (c.quadMask + MaskedConstraintTest.batch
      (fun q => Tableau.quadPolynomials C P (honestLdtRows pr ω c 0) q) r.2.2).eval
        (Tableau.responseNode C (2 * C.k - 1) i))

/-- **The honest tableau** of the witness `ω` and the coins `c`: the honest rows, which satisfy the
constraints because the piece rows are separate from the data (`PieceRows.Separate`) and the
unsplit honest rows satisfy them (`Ligero.HVZK.rows_holds`); the unsplit honest masks. `hprod`: a
parameter condition, no product group reads row `0`. -/
noncomputable def honestTableau (hprod : ∀ q i, P.products q i ≠ 0) (hs : pr.Separate L)
    (ω : HVZK.Witness L Bf) (c : Coins hrate Bf t nrep) :
    Completeness.HonestTableau (C := C) (P := P) (L := L) hrate nrep where
  ildt j := LigeroInterpolation.interpolate P.nodes (c.inner.response.ildt j)
  data i := honestRows pr ω.toCells c i.succ
  ildt_degree _ := LigeroInterpolation.interpolate_degree C.k_pos P.nodes_injective _
  data_degree i := natDegree_honestRows_lt ω.toCells c i.succ
  holds := by
    change Tableau.Holds C P L (honestLdtRows pr ω.toCells c 0)
    rw [honestLdtRows_zero hs.zero_not_mem]
    exact (hs.holds_congr hprod fun _ _ hm => (honestRows_of_not_mem ω.toCells c hm).symm).mp
      (HVZK.rows_holds hprod ω c.inner)
  dotMask := c.dotMask
  quadMask := c.quadMask
  dotMask_degree := c.inner.response.dotMask.2.1
  quadMask_degree := c.inner.response.quadMask.2.1
  dotMask_zero := c.inner.response.dotMask.2.2
  quadMask_zero := c.inner.response.quadMask.2.2

variable (hprod : ∀ q i, P.products q i ≠ 0) (hs : pr.Separate L)

omit [Fintype F] in
/-- **The masks recombined from the honest piece rows are the honest masks.** -/
theorem masks_honestCommit (hn : pr.toList.Nodup) (hz : (0 : Fin (R + 1)) ∉ pr.toList)
    (ω : HVZK.Cells Bf) (c : Coins hrate Bf t nrep) :
    pr.masks C t (honestCommit pr ω c).tableau =
      evalMasks C c.dotMask c.quadMask := by
  rw [honestCommit_tableau hz]
  have hv : ∀ (pc : Pieces R) (M : F[X]) (κ : Kernel F C.k t),
      (∀ m, honestRows pr ω c (pc.row m) = honestPieces M κ m) →
      M.natDegree < 2 * C.k - 1 →
      pc.value C t (fun row col => (honestRows pr ω c row).eval (C.D col)) =
        fun j => M.eval (C.D j) := by
    intro pc M κ hrow hM
    funext j
    have h0 := hrow 0
    have h1 := hrow 1
    have h2 := hrow 2
    simp only [Pieces.row, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons] at h0 h1 h2
    rw [Pieces.value, h0, h1, h2, ← eval_recombinePoly,
      recombinePoly_honestPieces hM]
  exact Prod.ext (hv pr.dot _ _ (honestRows_dot hn ω c) c.natDegree_dotMask_lt)
    (hv pr.quad _ _ (honestRows_quad hn ω c) c.natDegree_quadMask_lt)

/-! #### The simulator -/

variable (hrate) in
/-- **The simulator's coins**: the unsplit simulator's coins (`Ligero.HVZK.SimCoins`: the data
rows' openings and the response coins) and the openings of the pieces `C` and `B` of each mask. -/
@[ext]
structure SimCoins (Hd : HVZK.HidingLayout C P) (t nrep : ℕ) where
  /-- The unsplit simulator's coins. -/
  inner : HVZK.SimCoins hrate Hd t nrep
  /-- The openings of the pieces `C` and `B` of the IDOT mask. -/
  dot : PieceOpenings F t
  /-- The openings of the pieces `C` and `B` of the IQUAD mask. -/
  quad : PieceOpenings F t

variable (hrate) in
/-- The simulator's coins as the openings, the response coins and the two piece openings. -/
def SimCoins.equivProd (Hd : HVZK.HidingLayout C P) (t nrep : ℕ) :
    SimCoins hrate Hd t nrep ≃ (∀ row : Fin R, Fin t → Hd.field row) ×
      (HVZK.ResponseCoins P hrate nrep × (PieceOpenings F t × PieceOpenings F t)) where
  toFun s := (s.inner.openings, s.inner.response, s.dot, s.quad)
  invFun y := ⟨⟨y.1, y.2.1⟩, y.2.2.1, y.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The simulator's coins are enumerated through the hiding layout's decidable membership and
equality (`HVZK.ResponseCoins.enum`). -/
instance (Hd : HVZK.HidingLayout C P) (t : ℕ) : Fintype (SimCoins hrate Hd t nrep) :=
  letI := Hd.decEq
  letI := HVZK.ResponseCoins.enum P hrate nrep
  Fintype.ofEquiv _ (SimCoins.equivProd hrate Hd t nrep).symm

instance (Hd : HVZK.HidingLayout C P) (t : ℕ) : Nonempty (SimCoins hrate Hd t nrep) :=
  ⟨⟨Classical.arbitrary _, ⟨0, 0⟩, ⟨0, 0⟩⟩⟩

/-- **The openings of the three pieces of one mask at the queried column `s`** with point `x`: the
openings of `C` and `B` from `o`, and the opening of `A` that recombines with them to the mask
value `mask`: `mask − x ^ (k − t) · C − x ^ k · B`. -/
def pieceColumn (k t : ℕ) (x mask : F) (o : PieceOpenings F t) (s : Fin t) : Fin 3 → F :=
  ![mask - x ^ (k - t) * o.c s - x ^ k * o.b s, o.c s, o.b s]

variable (L pr) in
/-- **The data-row openings with the pieces placed**: from the openings `o` of the data rows, the
response `p` and the openings `dot`, `quad` of the pieces `C` and `B`. At the column `s` with point
`x`, each mask's value is the masked response's value less the batched column sources of the other
data rows (which do not read the piece rows); the piece rows hold `pieceColumn` of these values,
every other data row its entry of `o`. Computable. -/
def simData (r : Tableau.Challenge F R nL nQ nrep) (q : Tableau.Query N t) (o : Fin R → Fin t → F)
    (p : Tableau.Response F C.k nrep) (dot quad : PieceOpenings F t) : Fin R → Fin t → F :=
  fun i s =>
    let x := C.D (q s)
    let col : Fin (R + 1) → F := Fin.cases 0 fun i => o i s
    pr.fill (pieceColumn C.k t x (p.dotEval C x - ∑ l, r.2.1 l * HVZK.dotAt (L := L) col l x) dot s)
      (pieceColumn C.k t x (p.quadEval C x - ∑ l, r.2.2 l * HVZK.quadAt (P := P) col l) quad s)
      col i.succ

variable (L hrate pr) in
/-- **The simulator** of one tableau with the mask test, on the linear system `L`, the challenge `r`
and the query `q`: the unsplit simulator's responses (`Ligero.HVZK.simResponse`), the data rows'
openings from its coins with the piece rows filled by `simData`, and the openings of the
remaining rows from the acceptance equations (`Ligero.HVZK.publicView`).

Running time: one run of `Ligero.HVZK.simResponse` (one Lagrange interpolation over `k` nodes and
`2k − 1` evaluations of each mask, its docstring); for each of the `t` queried columns, the mask
values (`O(nL · (R + 1) · k + nQ)` field operations for the column sources, as in
`Ligero.HVZK.simulate`), the three piece openings of each mask (`O(log k)` multiplications for the
powers of the point), and six row comparisons per row; then `Ligero.HVZK.publicView`, as in
`Ligero.HVZK.simulate`. Polynomial in `k`, `R`, `nL`, `nQ` and `t`.
This running time is argued here, not proved in Lean. -/
def simulate (Hd : HVZK.HidingLayout C P) (r : Tableau.Challenge F R nL nQ nrep)
    (q : Tableau.Query N t) (s : SimCoins hrate Hd t nrep) : HVZK.View F R C.k t nrep :=
  let p := HVZK.simResponse L hrate Hd r s.inner.response
  HVZK.publicView L r q (simData L pr r q (fun i j => s.inner.openings i j) p s.dot s.quad) p

/-! #### The honest view as a public function -/

/-- **The ILDT offset** of the coins `c` at the low-degree challenge `r`: the values at the
message nodes of `Σ r_i · (honestRows (i + 1) − HVZK.rows (i + 1))`, the change the piece rows make
to the low-degree response. The low-degree response of the split tableau is that of the unsplit
tableau with the ILDT values shifted by it (`codeResponse_honestRows`). -/
noncomputable def ildtOffset (ω : HVZK.Cells Bf) (r : Fin R → F) (c : Coins hrate Bf t nrep) :
    Fin C.k → F :=
  fun j => (∑ i, r i • (honestRows pr ω c i.succ - HVZK.rows ω c.inner i.succ)).eval (P.nodes j)

omit [Fintype F] in
theorem ildtOffset_congr (ω : HVZK.Cells Bf) (r : Fin R → F)
    (ρ : ∀ row : Fin R, HVZK.Privacy P → Bf.field row) (v v' : Fin nrep → Fin C.k → F)
    (dm : HVZK.DotMasks C P hrate) (qm : HVZK.QuadMasks C P hrate) (κd κq : Kernel F C.k t) :
    ildtOffset (pr := pr) ω r (⟨⟨ρ, ⟨v, dm, qm⟩⟩, κd, κq⟩ : Coins hrate Bf t nrep) =
      ildtOffset (pr := pr) ω r (⟨⟨ρ, ⟨v', dm, qm⟩⟩, κd, κq⟩ : Coins hrate Bf t nrep) := by
  funext j
  simp only [ildtOffset, honestRows_succ_congr ω ρ v v' dm qm κd κq, HVZK.rows_succ]

/-- **The coins with the ILDT values shifted by the ILDT offsets**: repetition `j`'s ILDT values
by the ILDT offset at its challenge `r j`. -/
noncomputable def shiftCoins (ω : HVZK.Cells Bf) (r : Tableau.LdtChallenge F R nrep)
    (c : Coins hrate Bf t nrep) : HVZK.Coins hrate Bf nrep :=
  ⟨c.inner.privacy, ⟨c.inner.response.ildt + fun j => ildtOffset (pr := pr) ω (r j) c,
    c.inner.response.dotMask, c.inner.response.quadMask⟩⟩

omit [Fintype F] in
/-- **The low-degree response polynomial of the split tableau** in repetition `j` is that of the
unsplit tableau at the shifted coins. -/
theorem codeResponse_honestRows (ω : HVZK.Cells Bf) (r : Tableau.LdtChallenge F R nrep)
    (c : Coins hrate Bf t nrep) (j : Fin nrep) :
    AffineCodeTest.projectedPolynomial (honestLdtRows pr ω c j) (r j) =
      AffineCodeTest.projectedPolynomial (HVZK.ldtRows ω (shiftCoins (pr := pr) ω r c) j)
        (r j) := by
  have hdeg : (∑ i, r j i • (honestRows pr ω c i.succ - HVZK.rows ω c.inner i.succ)).degree <
      C.k := by
    rw [← mem_degreeLT]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
    · exact mem_degreeLT.mpr (degree_le_natDegree.trans_lt
        (by exact_mod_cast natDegree_honestRows_lt ω c i.succ))
    · exact mem_degreeLT.mpr (degree_le_natDegree.trans_lt
        (by exact_mod_cast HVZK.rows_degree ω c.inner i.succ))
  have hint := LigeroInterpolation.interpolate_eval_nodes P.nodes_injective hdeg
  simp only [AffineCodeTest.projectedPolynomial, honestLdtRows, HVZK.ldtRows, Fin.cons_zero,
    Fin.cons_succ, shiftCoins, Pi.add_apply, map_add]
  change _ = _ + LigeroInterpolation.interpolate P.nodes (ildtOffset (pr := pr) ω (r j) c) + _
  rw [show LigeroInterpolation.interpolate P.nodes (ildtOffset (pr := pr) ω (r j) c) = _ from hint]
  simp only [HVZK.rows_succ, smul_sub, Finset.sum_sub_distrib]
  abel

omit [Fintype F] in
/-- **The response of the split tableau is the unsplit response at the shifted coins**: the
low-degree response by `codeResponse_honestRows`; the masked responses because the masks are the
same and the constraint polynomials read neither row `0` nor the piece rows. -/
theorem response_honestTableau_eq (ω : HVZK.Witness L Bf) (r : Tableau.Challenge F R nL nQ nrep)
    (c : Coins hrate Bf t nrep) :
    Completeness.response (honestTableau hprod hs ω c) r =
      Completeness.response (HVZK.honest hprod ω (shiftCoins (pr := pr) ω.toCells r.1 c)) r := by
  have hrow : ∀ row, row ≠ 0 → row ∉ pr.toList → honestLdtRows pr ω.toCells c 0 row =
      HVZK.rows ω.toCells (shiftCoins (pr := pr) ω.toCells r.1 c) row := by
    intro row h0 hm
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.mpr h0
    change honestRows pr ω.toCells c i.succ = _
    rw [honestRows_of_not_mem ω.toCells c hm, HVZK.rows_succ, HVZK.rows_succ]
    rfl
  have hcode : (fun j => AffineCodeTest.projectedPolynomial (honestLdtRows pr ω.toCells c j)
      (r.1 j)) = fun j => AffineCodeTest.projectedPolynomial
        (HVZK.ldtRows ω.toCells (shiftCoins (pr := pr) ω.toCells r.1 c) j) (r.1 j) :=
    funext (codeResponse_honestRows ω.toCells r.1 c)
  simp only [Completeness.response, Completeness.dotResponse, Completeness.quadResponse]
  change Tableau.Response.ofPolys C
      (fun j => AffineCodeTest.projectedPolynomial (honestLdtRows pr ω.toCells c j) (r.1 j))
      (c.dotMask + MaskedConstraintTest.batch
        (fun l => Tableau.dotPolynomials C P L (honestLdtRows pr ω.toCells c 0) l) r.2.1)
      (c.quadMask + MaskedConstraintTest.batch
        (fun q => Tableau.quadPolynomials C P (honestLdtRows pr ω.toCells c 0) q) r.2.2) =
    Tableau.Response.ofPolys C
      (fun j => AffineCodeTest.projectedPolynomial
        (HVZK.ldtRows ω.toCells (shiftCoins (pr := pr) ω.toCells r.1 c) j) (r.1 j))
      (c.dotMask + MaskedConstraintTest.batch (fun l => Tableau.dotPolynomials C P L
        (HVZK.rows ω.toCells (shiftCoins (pr := pr) ω.toCells r.1 c)) l) r.2.1)
      (c.quadMask + MaskedConstraintTest.batch (fun q => Tableau.quadPolynomials C P
        (HVZK.rows ω.toCells (shiftCoins (pr := pr) ω.toCells r.1 c)) q) r.2.2)
  rw [hcode]
  simp only [hs.dotPolynomials_congr hrow, hs.quadPolynomials_congr hprod hrow]

end

section View

variable {F : Type} [Field F] [Fintype F] {N R nL nQ : ℕ} {C : GordieHowe.RSCode F N}
  {P : Tableau.Parameters (R := R) (nQ := nQ) C} {L : Tableau.LinearSystem (nL := nL) C P}
  {hrate : 2 * C.k - 1 ≤ N} {Hd : HVZK.HidingLayout C P} {pr : PieceRows R} {t nrep : ℕ}
  [NeZero nrep]

variable (hs : pr.Separate L)

variable (hrate) in
/-- **The honest view** of one tableau with the mask test: the view of the honest tableau, its masks
and its response at the challenge `r` and the query `q`. -/
noncomputable def honestView (ω : HVZK.Witness L Hd.toBlindingFields)
    (r : Tableau.Challenge F R nL nQ nrep) (q : Tableau.Query N t)
    (c : Coins hrate Hd.toBlindingFields t nrep) : HVZK.View F R C.k t nrep :=
  HVZK.view (Completeness.encode (honestTableau Hd.products_ne_zero hs ω c))
    (Completeness.masks (honestTableau Hd.products_ne_zero hs ω c))
    (Completeness.response (honestTableau Hd.products_ne_zero hs ω c) r) q

omit [Fintype F] in
/-- **The honest view is the public map of the data rows' openings, the response and the honest
openings of the pieces `C` and `B`**: the data rows' openings at the piece rows are recovered by
`simData`. -/
theorem honestView_eq (ω : HVZK.Witness L Hd.toBlindingFields) (r : Tableau.Challenge F R nL nQ nrep)
    (q : Tableau.Query N t) (c : Coins hrate Hd.toBlindingFields t nrep) :
    honestView hrate hs ω r q c =
      HVZK.publicView L r q (simData L pr r q
          (fun i s => (HVZK.openings ω.toCells q c.inner.privacy i s : F))
          (Completeness.response (honestTableau Hd.products_ne_zero hs ω c) r)
          (honestOpenings (fun s => C.D (q s)) c.dotMask c.dotKernel)
          (honestOpenings (fun s => C.D (q s)) c.quadMask c.quadKernel))
        (Completeness.response (honestTableau Hd.products_ne_zero hs ω c) r) := by
  set H := honestTableau Hd.products_ne_zero hs ω c
  rw [honestView, HVZK.view_honest H r q]
  congr 1
  funext i s
  set x := C.D (q s)
  set col : Fin (R + 1) → F := Fin.cases 0 fun i =>
    (HVZK.openings ω.toCells q c.inner.privacy i s : F)
  have hcolH : ∀ row, row ≠ 0 → (HVZK.rows ω.toCells c.inner row).eval x = col row := by
    intro row h0
    obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr h0
    rfl
  have hcol : ∀ row, row ≠ 0 → row ∉ pr.toList → (H.rows row).eval x = col row := by
    intro row h0 hm
    obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr h0
    change (honestRows pr ω.toCells c i'.succ).eval x = col i'.succ
    rw [honestRows_of_not_mem ω.toCells c hm]
    exact hcolH _ h0
  have hmD : (Completeness.response H r).dotEval C x -
      ∑ l, r.2.1 l * HVZK.dotAt (L := L) col l x = c.dotMask.eval x := by
    rw [← Tableau.Response.eval_dot, Completeness.response_dot]
    simp only [Completeness.dotResponse, MaskedConstraintTest.batch, eval_add, eval_finsetSum,
      eval_mul, eval_C, eval_dotPolynomials, hs.dotAt_congr hcol]
    exact add_sub_cancel_right _ _
  have hmQ : (Completeness.response H r).quadEval C x -
      ∑ l, r.2.2 l * HVZK.quadAt (P := P) col l = c.quadMask.eval x := by
    rw [← Tableau.Response.eval_quad, Completeness.response_quad]
    simp only [Completeness.quadResponse, MaskedConstraintTest.batch, eval_add, eval_finsetSum,
      eval_mul, eval_C, eval_quadPolynomials, hs.quadAt_congr Hd.products_ne_zero hcol]
    exact add_sub_cancel_right _ _
  have hpiece : ∀ (M : F[X]) (κ : Kernel F C.k t), M.natDegree < 2 * C.k - 1 →
      (fun m => (honestPieces M κ m).eval x) = pieceColumn C.k t x (M.eval x)
        (honestOpenings (fun s => C.D (q s)) M κ) s := by
    intro M κ hM
    have hrec := congrArg (Polynomial.eval x) (recombinePoly_honestPieces (t := t) hM κ)
    rw [eval_recombinePoly, recombine] at hrec
    funext m
    fin_cases m
    · change (honestPieces M κ 0).eval x = M.eval x - x ^ (C.k - t) *
        (honestPieces M κ 1).eval x - x ^ C.k * (honestPieces M κ 2).eval x
      rw [← hrec]
      ring
    · rfl
    · rfl
  change (honestRows pr ω.toCells c i.succ).eval x = pr.fill
    (pieceColumn C.k t x ((Completeness.response H r).dotEval C x -
      ∑ l, r.2.1 l * HVZK.dotAt (L := L) col l x)
      (honestOpenings (fun s => C.D (q s)) c.dotMask c.dotKernel) s)
    (pieceColumn C.k t x ((Completeness.response H r).quadEval C x -
      ∑ l, r.2.2 l * HVZK.quadAt (P := P) col l)
      (honestOpenings (fun s => C.D (q s)) c.quadMask c.quadKernel) s)
    col i.succ
  rw [hmD, hmQ, honestRows, PieceRows.fill_map (fun f : F[X] => f.eval x),
    ← hpiece _ _ c.natDegree_dotMask_lt, ← hpiece _ _ c.natDegree_quadMask_lt]
  exact PieceRows.fill_congr fun _ => hcolH _ (Fin.succ_ne_zero i)

/-- **Perfect honest-verifier zero-knowledge of one tableau with the mask test**.
For every honest witness, challenge and query of `t` distinct
columns with `t` at most the number of privacy positions and `2t ≤ k`, the honest view
(`honestView`) and the simulated view (`simulate`) have the same distribution. `hs`, `ht`,
`ht2`: parameter conditions. -/
theorem identDistrib (ω : HVZK.Witness L Hd.toBlindingFields) (r : Tableau.Challenge F R nL nQ nrep)
    (q : Tableau.Query N t) (ht : t ≤ C.k - P.witness.card) (ht2 : 2 * t ≤ C.k) :
    honestView hrate hs ω r q =ᵈ simulate L hrate pr Hd r q := by
  classical
  set xq : Fin t → F := fun s => C.D (q s)
  have hxq : Function.Injective xq := C.D_injective.comp q.injective
  -- For fixed privacy values: the responses and the piece openings.
  have h2 : ∀ ρ : ∀ row : Fin R, HVZK.Privacy P → Hd.field row,
      (fun y : HVZK.ResponseCoins P hrate nrep × (Kernel F C.k t × Kernel F C.k t) =>
        (Completeness.response (honestTableau Hd.products_ne_zero hs ω
            (⟨⟨ρ, y.1⟩, y.2.1, y.2.2⟩ : Coins hrate Hd.toBlindingFields t nrep)) r,
          honestOpenings xq y.1.dotMask.1 y.2.1, honestOpenings xq y.1.quadMask.1 y.2.2)) =ᵈ
      (fun z : HVZK.ResponseCoins P hrate nrep × (PieceOpenings F t × PieceOpenings F t) =>
        (HVZK.simResponse L hrate Hd r z.1, z.2)) := by
    intro ρ
    let off := fun (y : HVZK.ResponseCoins P hrate nrep × (Kernel F C.k t × Kernel F C.k t)) =>
      fun j => ildtOffset (pr := pr) ω.toCells (r.1 j)
        (⟨⟨ρ, y.1⟩, y.2.1, y.2.2⟩ : Coins hrate Hd.toBlindingFields t nrep)
    have hoff : ∀ (y : HVZK.ResponseCoins P hrate nrep × (Kernel F C.k t × Kernel F C.k t))
        (v : Fin nrep → Fin C.k → F), off (⟨v, y.1.dotMask, y.1.quadMask⟩, y.2) = off y := by
      rintro ⟨⟨v₀, dm, qm⟩, κd, κq⟩ v
      exact funext fun j => ildtOffset_congr ω.toCells (r.1 j) ρ v v₀ dm qm κd κq
    let e : HVZK.ResponseCoins P hrate nrep × (Kernel F C.k t × Kernel F C.k t) ≃
        HVZK.ResponseCoins P hrate nrep × (Kernel F C.k t × Kernel F C.k t) :=
      { toFun := fun y => (⟨y.1.ildt + off y, y.1.dotMask, y.1.quadMask⟩, y.2)
        invFun := fun y => (⟨y.1.ildt - off y, y.1.dotMask, y.1.quadMask⟩, y.2)
        left_inv := fun y => by
          simp only [hoff]
          rw [add_sub_cancel_right]
        right_inv := fun y => by
          simp only [hoff]
          rw [sub_add_cancel] }
    refine (IdentDistrib.of_equiv e fun y => ?_).trans
      (IdentDistrib.dependent
        (f₁ := fun x => Completeness.response (HVZK.honest Hd.products_ne_zero ω ⟨ρ, x⟩) r)
        (g₁ := HVZK.simResponse L hrate Hd r)
        (f₂ := fun x (κ : Kernel F C.k t × Kernel F C.k t) =>
          (honestOpenings xq x.dotMask.1 κ.1, honestOpenings xq x.quadMask.1 κ.2))
        (g₂ := fun _ => id) (HVZK.response_identDistrib ω r ρ)
        fun x => IdentDistrib.prod (honestOpenings_uniform ht2 hxq x.dotMask.1)
          (honestOpenings_uniform ht2 hxq x.quadMask.1))
    exact congrArg (fun p => (p, _))
      (response_honestTableau_eq Hd.products_ne_zero hs ω r _)
  have hdep := IdentDistrib.dependent (f₁ := HVZK.openings ω.toCells q) (g₁ := id)
    (f₂ := fun ρ (y : HVZK.ResponseCoins P hrate nrep × (Kernel F C.k t × Kernel F C.k t)) =>
      (Completeness.response (honestTableau Hd.products_ne_zero hs ω
          (⟨⟨ρ, y.1⟩, y.2.1, y.2.2⟩ : Coins hrate Hd.toBlindingFields t nrep)) r,
        honestOpenings xq y.1.dotMask.1 y.2.1, honestOpenings xq y.1.quadMask.1 y.2.2))
    (g₂ := fun _ (z : HVZK.ResponseCoins P hrate nrep × (PieceOpenings F t × PieceOpenings F t)) =>
      (HVZK.simResponse L hrate Hd r z.1, z.2))
    (HVZK.openings_uniform ω.toCells q ht) h2
  let K := fun (w : (∀ row : Fin R, Fin t → Hd.field row) ×
      (Tableau.Response F C.k nrep × (PieceOpenings F t × PieceOpenings F t))) =>
    HVZK.publicView L r q (simData L pr r q (fun i s => (w.1 i s : F)) w.2.1 w.2.2.1 w.2.2.2)
      w.2.1
  have h := ((hdep.comp K).comp_equiv (Coins.equivProd hrate Hd.toBlindingFields t nrep)).trans
    (IdentDistrib.of_equiv (SimCoins.equivProd hrate Hd t nrep) fun _ => rfl).symm
  have h1 : honestView hrate hs ω r q = fun c => K (HVZK.openings ω.toCells q c.inner.privacy,
      Completeness.response (honestTableau Hd.products_ne_zero hs ω c) r,
      honestOpenings xq c.dotMask c.dotKernel,
      honestOpenings xq c.quadMask c.quadKernel) :=
    funext fun c => honestView_eq hs ω r q c
  rw [h1]
  exact h

end View

end ZK

/-! ### The honest prover of the system -/

section System

variable {F ι Q Lin : Type} [Field F] [Fintype F] [Fintype ι] [Fintype Q] [Fintype Lin]
  {N R nL nQ : ℕ} {C : GordieHowe.RSCode F N} {P : Tableau.Parameters (R := R) (nQ := nQ) C}
  {products : Routing.ProductLayout ι Q}

/-- **The piece rows are free in the placement** `A` (parameter conditions): the six rows are
distinct, none is the ILDT row `0`, no source variable is placed in one, and no product group
reads one. -/
structure PieceRows.Free (pr : PieceRows R) (A : Preparation.Placement C P ι Q) : Prop where
  nodup : pr.toList.Nodup
  zero_not_mem : (0 : Fin (R + 1)) ∉ pr.toList
  source_not_mem : ∀ i, (A.source i).1 ∉ pr.toList
  products_not_mem : ∀ g s, P.products g s ∉ pr.toList

omit [Fintype F] [Fintype Lin] in
/-- **Free piece rows are separate from the data** of every prepared linear system on the
placement: no prepared coordinate sits in a piece row, so the accumulated coefficients there are
zero. -/
theorem PieceRows.Free.separate {pr : PieceRows R} {A : Preparation.Placement C P ι Q}
    (hf : pr.Free A) {nL : ℕ} (index : Fin nL ≃ Routing.PreparedRow Lin Q)
    (rows : Lin → AffineForm F ι) :
    pr.Separate (Preparation.formSystem A products index rows) where
  nodup := hf.nodup
  zero_not_mem := hf.zero_not_mem
  coeff_eq_zero l row hrow := by
    funext j
    have hloc : ∀ z, A.location z ≠ (row, j) := by
      intro z hz
      have h1 := congrArg Prod.fst hz
      cases z with
      | inl i =>
        have h2 : (A.source i).1 = row := h1
        exact hf.source_not_mem i (h2 ▸ hrow)
      | inr qs =>
        have h2 : P.products (A.copyGroup qs.1) qs.2 = row := h1
        exact hf.products_not_mem _ _ (h2 ▸ hrow)
    simp [Preparation.formSystem, AffineForm.coeffAt, hloc]
  products_not_mem := hf.products_not_mem

variable (S : Setup C P products Lin nL)

/-- **The data of the honest prover** of Ligero at agreement threshold `A` with the mask test on
the setup `S`: that of the prepared tableau (`Ligero.AgreementThreshold.TableauSetup.Placement`: the hiding
layout and the allocation conditions of the placement), and the piece rows are free in the
placement (`PieceRows.Free`) (parameter conditions). Completeness needs only these. -/
structure Placement (S : Setup C P products Lin nL) extends
    toTableauPlacement : TableauSetup.Placement S.toTableauSetup where
  free : S.pieces.Free S.placement

/-- **The data of the honest prover** of Ligero at agreement threshold `A` with the mask test on the
setup `S`: that of the honest prover (`Placement`), the hiding threshold `t ≤` the number of
privacy positions (the paper's `nq ≤ k − ℓ`) and `2t ≤ k`,
the covering condition of the three-piece split (`MaskPieces.covers_three`, the paper's
`2nq ≤ k`) (parameter conditions). -/
structure Hiding (S : Setup C P products Lin nL) extends Placement S where
  t_le_privacy : S.t ≤ C.k - P.witness.card
  t_le_half : 2 * S.t ≤ C.k

namespace Placement

variable {Ctx : Type} (rows : Ctx → Lin → AffineForm F ι) [DecidableEq F]

variable {S} (Pl : Placement S)

/-- **The honest prover's coins**: the blinding coins and the uniform splittings. -/
abbrev Coins : Type := ZK.Coins S.rate_le Pl.layout.toBlindingFields S.t S.nrep

/-- **The honest oracle message**: the commitment of the honest rows (`ZK.honestCommit`: the
unsplit honest rows with the piece rows holding uniform splittings of the unsplit honest masks). -/
noncomputable def commit (x : ι → F) (c : Pl.Coins) : (commitProve S rows).Com :=
  ZK.honestCommit S.pieces (Pl.cells x) c

/-- **The honest commit rounds**: the low-degree challenge and the honest low-degree response
(`ZK.honestLdtResponse`). -/
noncomputable def commitRounds (x : ι → F) (c : Pl.Coins) :
    CausalTranscript (commitProve S rows).commitRounds :=
  Ligero.AgreementThreshold.honestCommitRounds (ZK.honestLdtResponse S.pieces (Pl.cells x) c)

/-- **The honest proof**: the honest masked responses (`ZK.honestMasked`) at the low-degree
challenge of the commit rounds and the constraint challenge. -/
noncomputable def prove (ctx : Ctx) (x : ι → F) (c : Pl.Coins) (r : (commitProve S rows).Rounds) :
    CausalTranscript (commitProve S rows).spec :=
  Ligero.AgreementThreshold.honestProof fun rc =>
    ZK.honestMasked (S.linearSystem (rows ctx)) S.pieces (Pl.cells x) c (ldtChallenge r, rc)

/-- **Completeness of the honest prover** (`Ligero.Completeness.accept` at the honest tableau
`ZK.honestTableau`, whose recombined masks are the honest masks, `ZK.masks_honestCommit`): on
admissible cells satisfying the rows, the verifier accepts at every coins and every challenge. No
query bound is needed. -/
theorem complete (ctx : Ctx) (x : ι → F)
    (hx : FieldProof.CommitProve.Admits Pl.Admissible (rows ctx) products x) (c : Pl.Coins)
    (chc : (commitProve S rows).commitRounds.Challenges)
    (ch : (commitProve S rows).spec.Challenges) :
    (commitProve S rows).V ⟨ctx, Pl.commit rows x c, (Pl.commitRounds rows x c).transcript chc⟩
      ((Pl.prove rows ctx x c ((Pl.commitRounds rows x c).transcript chc)).transcript ch) =
        true := by
  have hs := Pl.free.separate (products := products) S.index (rows ctx)
  set H := ZK.honestTableau Pl.layout.products_ne_zero hs
    (Pl.witness rows hx.admissible ctx hx.rowsHold) c
  have hacc := Completeness.accept H (chc (ldtIdx F R C.k S.nrep), Ligero.AgreementThreshold.chConstraint ch)
    (chQuery ch)
  have hm : Completeness.masks H = S.pieces.masks C S.t (Completeness.encode H).tableau :=
    (ZK.masks_honestCommit Pl.free.nodup Pl.free.zero_not_mem (Pl.cells x) c).symm
  rw [hm] at hacc
  exact hacc

end Placement

variable {S} (Hd : Hiding S) {Ctx : Type} (rows : Ctx → Lin → AffineForm F ι) [DecidableEq F]

variable (S) in
/-- **The view from a tableau view** at the low-degree challenge `r`, the constraint challenge
`rc` and the query `q`: the queried columns of the tableau view as leaves
(`Ligero.AgreementThreshold.viewLeaves`), the low-degree challenge and the low-degree response as the
commit rounds, the constraint challenge, the masked responses and the query as the proof-phase
transcript. -/
def viewOf (r : Tableau.LdtChallenge F R S.nrep) (rc : ConstraintChallenge F nL nQ)
    (q : Tableau.Query N S.t) (v : HVZK.View F R C.k S.t S.nrep) : (commitProve S rows).View :=
  ⟨Ligero.AgreementThreshold.viewLeaves Prod.fst q v, Ligero.AgreementThreshold.commitTranscript r v.1.1,
    Ligero.AgreementThreshold.proofTranscript rc v.1.2 q⟩

/-- **The simulator** of Ligero at agreement threshold `A` with the mask test: on the context `c`,
the low-degree challenge (in `chc`) and the proof-phase challenges, the tableau simulator of
the mask test `ZK.simulate` on the linear system of the context's rows at the low-degree and
constraint challenges and the query; its low-degree response goes into the commit rounds, its
masked responses into the proof-phase transcript and its queried columns into the leaves
(`viewOf`).

Running time: one run of `ZK.simulate` (polynomial in the tableau sizes, its docstring), the
verifier's computation of the prepared linear system from the rows (one pass over the placement
per row), and the assembly of the leaves, a search over the `t` queried columns for each of the
`N` positions. This running time is argued here, not proved in Lean. -/
def simulate (c : Ctx) (chc : (AgreementThreshold.commitSpec F R C.k S.nrep).Challenges)
    (ch : (proofSpec F N nL nQ C.k S.t).Challenges)
    (s : ZK.SimCoins S.rate_le Hd.layout S.t S.nrep) :
    (commitProve S rows).View :=
  viewOf S rows (chc (ldtIdx F R C.k S.nrep)) (Ligero.AgreementThreshold.chConstraint ch) (chQuery ch)
    (ZK.simulate (S.linearSystem (rows c)) S.rate_le S.pieces Hd.layout
      (chc (ldtIdx F R C.k S.nrep), Ligero.AgreementThreshold.chConstraint ch) (chQuery ch) s)

/-- **The simulator of Ligero at agreement threshold `A` with the mask test**: `simulate` at the
hiding data `Hd`, on its coins (`ZK.SimCoins`).

Running time: that of `simulate` (its docstring). This running time is argued here, not proved in
Lean. -/
def honestSim : (commitProve S rows).Sim where
  SimCoins := ZK.SimCoins S.rate_le Hd.layout S.t S.nrep
  sim c chc ch s := simulate Hd rows c chc ch s

/-- **The honest prover of Ligero at agreement threshold `A` with the mask test**: the honest prover of
the placement (`Placement.commit`, `Placement.commitRounds`, `Placement.prove`), complete by
`Placement.complete`; hiding is `ZK.identDistrib` at each fixed vector of admissible cells, with the
simulator `honestSim` (`simulate`), under the query bounds `t ≤ k − |witness|` and `2t ≤ k` of `Hd`. -/
noncomputable def honest : (commitProve S rows).Honest (honestSim Hd rows) where
  Coins := Hd.Coins
  commit := Hd.commit rows
  commitRounds := Hd.commitRounds rows
  prove := Hd.prove rows
  Admissible := Hd.Admissible
  complete := Hd.complete rows
  hides ctx x hx chc ch := by
    have hs := Hd.free.separate (products := products) S.index (rows ctx)
    have key := (ZK.identDistrib (hrate := S.rate_le) hs
      (Hd.witness rows hx.admissible ctx hx.rowsHold)
      (chc (ldtIdx F R C.k S.nrep), Ligero.AgreementThreshold.chConstraint ch) (chQuery ch) Hd.t_le_privacy
      Hd.t_le_half).comp
        (viewOf S rows (chc (ldtIdx F R C.k S.nrep)) (Ligero.AgreementThreshold.chConstraint ch) (chQuery ch))
    refine IdentDistrib.trans (IdentDistrib.of_equiv (Equiv.refl _) fun ρ => ?_) key
    exact congrArg (fun l => FieldProof.CommitProve.View.mk l _ _)
      (Ligero.AgreementThreshold.see_eq_viewLeaves (commitProve S rows).comView rfl _ _ _ fun _ => rfl)

end System

end GordieHowe.Ligero.MaskTest.Pieces
