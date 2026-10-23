-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Core.Model
public import GordieHowe.Foundations.ToMathlib.PMFOption

@[expose] public section

/-!
# Lemmas for constructions on the core

General facts used by the constructions on the core algorithms of `GordieHowe/Model/Quantum/Core/Model.lean`:
inverses of the oracle permutations, laws of computational-basis measurements, linearity of
Kraus maps, and block-diagonal matrices (`blk`, `KrausMap.blockSum`) for folding a family of
registers into one.
-/

open Finset Matrix
open scoped BigOperators ENNReal Kronecker ComplexOrder

namespace GordieHowe.Quantum

/-! ### Inverses of the oracle permutations -/

section Inverse

variable {W X Y : Type*} {n : ℕ} [AddGroup Y]

theorem queryPermOf_symm_apply (f : W → X → Y) (r : QueryReg W n X Y) :
    (queryPermOf f).symm r = (r.1, fun j => ((r.2 j).1, (r.2 j).2 - f r.1 (r.2 j).1)) := by
  rw [Equiv.symm_apply_eq]
  simp

theorem queryPerm_symm_apply (f : X → Y) (r : QueryReg W n X Y) :
    (queryPerm f).symm r = (r.1, fun j => ((r.2 j).1, (r.2 j).2 - f (r.2 j).1)) := by
  rw [← queryPermOf_const, queryPermOf_symm_apply]

end Inverse


section BasisLaw

variable {ι E O : Type*} [Fintype ι] [Fintype E] [DecidableEq E]

/-- Appending a register in a basis state and forgetting it does not change the
computational-basis law. -/
theorem basisLaw_kronecker_single_map {σ : Matrix (ι × E) (ι × E) ℂ} (ρ : Matrix ι ι ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace.re ≤ 1) (e : E) (hσ : σ = ρ ⊗ₖ Matrix.single e e 1)
    (h1 : σ.PosSemidef) (h2 : σ.trace.re ≤ 1) (g : ι → O) :
    (basisLaw σ h1 h2).map (Option.map fun p => g p.1) =
      (basisLaw ρ hρ htr).map (Option.map g) := by
  subst hσ
  refine PMF.ext_of_some fun o => ?_
  rw [PMF.map_apply, PMF.map_apply, tsum_fintype, tsum_fintype, Fintype.sum_option,
    Fintype.sum_option]
  simp only [Fintype.sum_prod_type, Option.map_some,
    Option.map_none, reduceCtorEq, if_false, zero_add, mul_ite, mul_one, mul_zero, Option.some.injEq]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · rw [Finset.sum_eq_single e (fun b _ hb => by simp [Matrix.single_apply, Ne.symm hb])
      (by simp)]
    simp [Matrix.single_apply]
  · exact Finset.sum_const_zero

/-- Conjugating by a basis permutation that preserves a function `g` of the outcome does not change
the law of `g`. -/
theorem basisLaw_submatrix_perm_map {σ : Matrix ι ι ℂ} (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef)
    (htr : ρ.trace.re ≤ 1) (π : Equiv.Perm ι) (hσ : σ = ρ.submatrix π.symm π.symm)
    (h1 : σ.PosSemidef) (h2 : σ.trace.re ≤ 1) (g : ι → O) (hg : ∀ i, g (π i) = g i) :
    (basisLaw σ h1 h2).map (Option.map g) = (basisLaw ρ hρ htr).map (Option.map g) := by
  subst hσ
  refine PMF.ext_of_some fun o => ?_
  rw [PMF.map_apply, PMF.map_apply, tsum_fintype, tsum_fintype, Fintype.sum_option,
    Fintype.sum_option]
  congr 1
  · simp
  · rw [← Equiv.sum_comp π]
    simp only [basisLaw_some, Option.map_some]
    exact Finset.sum_congr rfl fun x _ => by
      have := hg x
      simp only [submatrix_apply, Equiv.symm_apply_apply]
      split_ifs <;> simp_all

theorem map_basisLaw_apply_some [DecidableEq O] (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace.re ≤ 1)
    (g : ι → O) (o : O) :
    (basisLaw ρ hρ htr).map (Option.map g) (some o) =
      ∑ i, if some o = some (g i) then ENNReal.ofReal (ρ i i).re else 0 := by
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_option]
  simp only [Option.map_none, Option.map_some, reduceCtorEq, if_false, zero_add, basisLaw_some]
  exact Finset.sum_congr rfl fun i _ => by congr

end BasisLaw

/-! ### Kraus maps are linear -/

theorem KrausMap.apply_smul {R ι : Type*} [Fintype R] [Fintype ι] [DecidableEq ι]
    (K : KrausMap R ι ι) (c : ℂ) (ρ : Matrix ι ι ℂ) : K (c • ρ) = c • K ρ := by
  simp [KrausMap.apply, Finset.smul_sum]

/-! ### Block-diagonal states: folding a family into one register -/

section Block

variable {Aux : Type*} [Fintype Aux] [DecidableEq Aux] {Q : Aux → Type*} [∀ a, Fintype (Q a)]
  [∀ a, DecidableEq (Q a)] {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι ≃ Σ a, Q a)

/-- A block-diagonal matrix on `ι ≃ Σ a, Q a` with blocks `M a`. -/
def blk (M : ∀ a, Matrix (Q a) (Q a) ℂ) : Matrix ι ι ℂ :=
  (blockDiagonal' M).submatrix e e

theorem blk_mul (M N : ∀ a, Matrix (Q a) (Q a) ℂ) :
    blk e M * blk e N = blk e fun a => M a * N a := by
  rw [blk, blk, blk, submatrix_mul_equiv, blockDiagonal'_mul]

theorem blk_conjTranspose (M : ∀ a, Matrix (Q a) (Q a) ℂ) :
    (blk e M)ᴴ = blk e fun a => (M a)ᴴ := by
  rw [blk, blk, conjTranspose_submatrix, blockDiagonal'_conjTranspose]

theorem blk_add (M N : ∀ a, Matrix (Q a) (Q a) ℂ) :
    blk e M + blk e N = blk e fun a => M a + N a := by
  rw [blk, blk, blk, show (fun a => M a + N a) = M + N from rfl, blockDiagonal'_add]
  rfl

theorem blk_zero : blk e (fun _ => (0 : Matrix _ _ ℂ)) = (0 : Matrix ι ι ℂ) := by
  ext i j
  simp [blk, blockDiagonal'_apply]

theorem blk_sum {β : Type*} (s : Finset β) (M : β → ∀ a, Matrix (Q a) (Q a) ℂ) :
    ∑ i ∈ s, blk e (M i) = blk e fun a => ∑ i ∈ s, M i a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [blk_zero]
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, ih, blk_add]
    simp [Finset.sum_insert hx]

theorem blk_one : blk e (fun _ => 1) = 1 := by
  rw [blk, show (fun _ => (1 : Matrix _ _ ℂ)) = (1 : ∀ a, Matrix (Q a) (Q a) ℂ) from rfl,
    blockDiagonal'_one, submatrix_one_equiv]

theorem blk_sub (M N : ∀ a, Matrix (Q a) (Q a) ℂ) :
    blk e M - blk e N = blk e fun a => M a - N a := by
  rw [blk, blk, blk, show (fun a => M a - N a) = M - N from rfl, blockDiagonal'_sub]
  rfl

theorem blk_smul (c : ℂ) (M : ∀ a, Matrix (Q a) (Q a) ℂ) :
    c • blk e M = blk e fun a => c • M a := by
  rw [blk, blk, show (fun a => c • M a) = c • M from rfl, blockDiagonal'_smul]
  rfl

theorem blk_apply (M : ∀ a, Matrix (Q a) (Q a) ℂ) (a : Aux) (i j : Q a) :
    blk e M (e.symm ⟨a, i⟩) (e.symm ⟨a, j⟩) = M a i j := by
  simp [blk, blockDiagonal'_apply_eq]

/-- Block-diagonal with positive semidefinite blocks is positive semidefinite. -/
theorem posSemidef_blk {M : ∀ a, Matrix (Q a) (Q a) ℂ} (hM : ∀ a, (M a).PosSemidef) :
    (blk e M).PosSemidef := by
  choose C hC using fun a => exists_eq_conjTranspose_mul_self (hM a)
  have : blk e M = (blk e C)ᴴ * blk e C := by
    rw [blk_conjTranspose, blk_mul]
    exact congrArg _ (funext hC)
  rw [this]
  exact posSemidef_conjTranspose_mul_self _

theorem trace_blk (M : ∀ a, Matrix (Q a) (Q a) ℂ) : (blk e M).trace = ∑ a, (M a).trace := by
  rw [blk, Matrix.trace, ← e.symm.sum_comp, Fintype.sum_sigma]
  simp [Matrix.trace, blockDiagonal'_apply_eq]

/-- For the family that is `X` at block `a` and `0` elsewhere, the blockwise product of its
conjugate transpose with itself is `Xᴴ * X` at block `a` and `0` elsewhere. -/
theorem single_conjTranspose_mul_single (a : Aux) (X : Matrix (Q a) (Q a) ℂ) :
    (fun b => (Pi.single (M := fun b => Matrix (Q b) (Q b) ℂ) a X b)ᴴ *
      Pi.single (M := fun b => Matrix (Q b) (Q b) ℂ) a X b) =
      Pi.single (M := fun b => Matrix (Q b) (Q b) ℂ) a (Xᴴ * X) := by
  funext b
  by_cases h : b = a
  · subst h
    simp
  · simp [Pi.single_apply, h]

/-- For the family that is `X` at block `a` and `0` elsewhere, conjugating `σ` blockwise by it
gives `X * σ a * Xᴴ` at block `a` and `0` elsewhere. -/
theorem single_mul_mul_conjTranspose (a : Aux) (X : Matrix (Q a) (Q a) ℂ)
    (σ : ∀ a, Matrix (Q a) (Q a) ℂ) :
    (fun b => Pi.single (M := fun b => Matrix (Q b) (Q b) ℂ) a X b * σ b *
      (Pi.single (M := fun b => Matrix (Q b) (Q b) ℂ) a X b)ᴴ) =
      Pi.single (M := fun b => Matrix (Q b) (Q b) ℂ) a (X * σ a * Xᴴ) := by
  funext b
  by_cases h : b = a
  · subst h
    simp
  · simp [Pi.single_apply, h]

open scoped MatrixOrder in
/-- **A family of Kraus maps acting blockwise**: operator `(a, r)` is `op r` of the `a`-th Kraus
map on block `a`, zero elsewhere. -/
def KrausMap.blockSum {R : Aux → Type*} [∀ a, Fintype (R a)]
    (K : ∀ a, KrausMap (R a) (Q a) (Q a)) : KrausMap (Σ a, R a) ι ι where
  op p := blk e (Pi.single (M := fun b => Matrix (Q b) (Q b) ℂ) p.1 ((K p.1).op p.2))
  sum_le := by
    have h : ∑ p : Σ a, R a, (blk e (Pi.single (M := fun b => Matrix (Q b) (Q b) ℂ) p.1
        ((K p.1).op p.2)))ᴴ * blk e (Pi.single (M := fun b => Matrix (Q b) (Q b) ℂ) p.1
        ((K p.1).op p.2)) = blk e fun a => ∑ r, ((K a).op r)ᴴ * (K a).op r := by
      simp only [blk_conjTranspose, blk_mul, single_conjTranspose_mul_single]
      rw [Fintype.sum_sigma]
      simp only [blk_sum]
      congr 1
      funext b
      try simp only [Finset.sum_apply]
      rw [Finset.sum_eq_single b (fun a _ hab => by simp [Pi.single_apply, Ne.symm hab]) (by simp)]
      simp
    rw [h, Matrix.le_iff, ← blk_one e, blk_sub]
    exact posSemidef_blk e fun a => Matrix.le_iff.1 (K a).sum_le

theorem KrausMap.blockSum_apply {R : Aux → Type*} [∀ a, Fintype (R a)]
    (K : ∀ a, KrausMap (R a) (Q a) (Q a)) (σ : ∀ a, Matrix (Q a) (Q a) ℂ) :
    (KrausMap.blockSum e K) (blk e σ) = blk e fun a => (K a) (σ a) := by
  simp only [KrausMap.apply, KrausMap.blockSum, blk_conjTranspose, blk_mul,
    single_mul_mul_conjTranspose]
  rw [Fintype.sum_sigma]
  simp only [blk_sum]
  congr 1
  funext b
  try simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single b (fun a _ hab => by simp [Pi.single_apply, Ne.symm hab]) (by simp)]
  simp

end Block

namespace Alg

/-- The real masses of a distribution on a finite type sum to `1`. -/
theorem sum_toReal_pmf {Aux : Type} [Fintype Aux] (μ : PMF Aux) : ∑ a, (μ a).toReal = 1 := by
  have h := μ.tsum_coe
  rw [tsum_fintype] at h
  rw [← ENNReal.toReal_sum fun a _ => PMF.apply_ne_top μ a, h, ENNReal.toReal_one]

end Alg

end GordieHowe.Quantum
