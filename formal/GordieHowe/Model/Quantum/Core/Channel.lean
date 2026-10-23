-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Core.State
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import GordieHowe.Foundations.ToMathlib.Matrix
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

/-!
# Mixed states, Kraus maps and general measurements

The mixed-state formalism of finite-dimensional quantum mechanics, transcribed from Heidler and
Unruh, "Formalizing the One-Way to Hiding Theorem" (CPP 2025; cited as HU25), section 2.3,
p. 245. Each sentence is quoted with the Lean that transcribes it. Names follow Lean-QuantumInfo
(physlib, checked at 56e83a9; copied, not imported): `MState` for a mixed state.

- "A mixed state is described by a matrix [trace-class operator] ρ ∈ C^{n×n}, called a density
  operator. … The valid quantum states are exactly the positive operators of trace 1."
  `MState ι`: a positive semidefinite matrix `Matrix ι ι ℂ` (Mathlib's `Matrix.PosSemidef`) with
  trace `1`, over a finite computational basis `ι`.

- "Often, we may also consider density operators with trace ≤ 1, called subdensity operators.
  These correspond to subprobability distributions with total probability ≤ 1. (Useful for
  modeling programs that terminate with probability ≤ 1.)"
  A subdensity operator is a positive semidefinite matrix whose trace has real part at most `1`.
  Its computational-basis law (`basisLaw`) is a distribution on `Option ι`: the outcome `some i`
  has probability `re (ρ i i)`, and `none` carries the missing mass `1 - re (tr ρ)`, the
  probability of non-termination.

- "To represent a mixed state that is with probability 1 the pure state ψ (a vector) in this
  formalism, we define ρ := ψψ*. … A distribution of states ψ_i with corresponding
  probabilities p_i is described by ρ := ∑ p_i ψ_i ψ_i*."
  Classical randomness is a mixed state; the amplitude convention is `(ψψ*) i j = ψ i * conj (ψ j)`
  (`GordieHowe/Model/Quantum/Core/Dilation.lean`, `reduce`).

- "Applying a unitary U to a mixed state ρ results in UρU*."
  For a basis permutation `π` this is `MState.permute π`: `(UρU*) i j = ρ (π⁻¹ i) (π⁻¹ j)`.

- "The general form for such mixed probabilistic quantum operations is ρ ↦ ∑ E_i ρ E_i* for some
  E_i with ∑ E_i* E_i = I (or ≤ I if we allow subprobability distributions; we call this the
  normalization condition) … We call such maps "Kraus maps" (and the E_i Kraus operators)."
  `KrausMap R ι κ`: Kraus operators `op r : Matrix κ ι ℂ` indexed by a finite type `R` with
  `∑ r, (op r)ᴴ * op r ≤ 1` in the Loewner order (Mathlib's `MatrixOrder`);
  `KrausMap.apply` is `ρ ↦ ∑ r, op r * ρ * (op r)ᴴ`. It maps subdensity operators to subdensity
  operators (`KrausMap.posSemidef_apply`, `KrausMap.re_trace_apply_le`). `KrausChannel R ι κ` is the
  trace-preserving case `∑ r, (op r)ᴴ * op r = 1` (the Kraus form of Lean-QuantumInfo's
  `CPTPMap`), used by the dilation (`GordieHowe/Model/Quantum/Core/Dilation.lean`). HU25 also allow infinitely many
  operators; in finite dimension finitely many suffice.

- "Measuring with projector P gives "yes" with probability tr Pρ and "no" with tr(I − P)ρ."
  A general measurement is a Kraus family whose index is the outcome: outcome `r` has
  probability `tr (op r * ρ * (op r)ᴴ)` (`Quantum.KrausChannel.outcomeLaw`), the law of the POVM with effects
  `(op r)ᴴ * op r` (Lean-QuantumInfo `POVM`). For the projectors `op yes = P`, `op no = I − P`
  this is HU25's `tr Pρ` and `tr (I − P)ρ`, since `tr (PρP) = tr (P P ρ) = tr (Pρ)`. The
  computational-basis measurement is `Quantum.KrausChannel.basis`. Reading the outcome as a classical register
  that a later operation may consult is again a Kraus map (the operators `|r⟩ ⊗ op r`), so
  intermediate measurements are Kraus maps.

Everything here is about Mathlib objects only.
-/

open Finset Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

namespace GordieHowe.Quantum

/-! ### Mixed states -/

/-- **A mixed state** (HU25 section 2.3, p. 245, "the valid quantum states are exactly the
positive operators of trace 1"; Lean-QuantumInfo `MState`): a density matrix, that is, a positive
semidefinite matrix of trace `1`. -/
structure MState (ι : Type*) [Fintype ι] where
  /-- The matrix. -/
  mat : Matrix ι ι ℂ
  posSemidef : mat.PosSemidef
  trace_eq_one : mat.trace = 1

namespace MState

variable {ι : Type*} [Fintype ι]

@[ext]
theorem ext {ρ σ : MState ι} (h : ρ.mat = σ.mat) : ρ = σ := by
  cases ρ
  cases σ
  simp only at h
  subst h
  rfl

/-- A system with a density matrix has a nonempty computational basis: the trace over an empty
basis is `0`. -/
theorem nonempty (ρ : MState ι) : Nonempty ι := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := ρ.trace_eq_one
  rw [Matrix.trace, Finset.univ_eq_empty, Finset.sum_empty] at this
  exact zero_ne_one this

/-- **A unitary basis permutation applied to a density matrix** (HU25 p. 245, "UρU*"): for
`U = permOp π`, `(UρU*) i j = ρ (π⁻¹ i) (π⁻¹ j)`. -/
def permute (π : Equiv.Perm ι) (ρ : MState ι) : MState ι where
  mat := ρ.mat.submatrix π.symm π.symm
  posSemidef := ρ.posSemidef.submatrix _
  trace_eq_one := by
    rw [← ρ.trace_eq_one, Matrix.trace, Matrix.trace]
    exact Equiv.sum_comp π.symm fun i => ρ.mat i i

@[simp]
theorem permute_mat (π : Equiv.Perm ι) (ρ : MState ι) (i j : ι) :
    (ρ.permute π).mat i j = ρ.mat (π.symm i) (π.symm j) :=
  rfl

/-- The real diagonal entries of a density matrix are nonnegative. -/
theorem re_diag_nonneg (ρ : MState ι) (i : ι) : 0 ≤ (ρ.mat i i).re :=
  (Complex.nonneg_iff.1 (ρ.posSemidef.diag_nonneg (i := i))).1

/-- **The probability of an outcome in `B` when `ρ` is measured in the computational basis**
(HU25 p. 245, "tr Pρ", for the projector `P` onto the span of the basis states in `B`):
`∑ i ∈ B, ρ i i`. -/
noncomputable def probIn (B : Set ι) (ρ : MState ι) : ℝ :=
  ∑ i, B.indicator (fun i => (ρ.mat i i).re) i

theorem probIn_nonneg (B : Set ι) (ρ : MState ι) : 0 ≤ ρ.probIn B :=
  Finset.sum_nonneg fun i _ => Set.indicator_nonneg (fun i _ => ρ.re_diag_nonneg i) i

/-- **A mixed state with a register in a basis state appended**: `ρ ⊗ |e⟩⟨e|` on `ι × E`. -/
def tensorKet {E : Type*} [Fintype E] [DecidableEq E] (ρ : MState ι) (e : E) :
    MState (ι × E) where
  mat := ρ.mat ⊗ₖ Matrix.single e e 1
  posSemidef := by
    refine ρ.posSemidef.kronecker ?_
    have h : (Matrix.single e e (1 : ℂ)) = (Matrix.single e e (1 : ℂ))ᴴ * Matrix.single e e 1 := by
      rw [conjTranspose_single, star_one, single_mul_single_same, mul_one]
    rw [h]
    exact posSemidef_conjTranspose_mul_self _
  trace_eq_one := by
    rw [trace_kronecker, ρ.trace_eq_one, one_mul, trace_single_eq_same]

@[simp]
theorem tensorKet_mat {E : Type*} [Fintype E] [DecidableEq E] (ρ : MState ι) (e : E) :
    (ρ.tensorKet e).mat = ρ.mat ⊗ₖ Matrix.single e e 1 :=
  rfl

end MState

/-! ### Kraus families -/

/-- **A Kraus family** (HU25 section 2.3, p. 245, "ρ ↦ ∑ E_i ρ E_i* for some E_i with
∑ E_i* E_i = I … We call such maps "Kraus maps""): operators `op r : Matrix κ ι ℂ` indexed by a
finite type `R` with `∑ r, (op r)ᴴ * op r = 1`. As a channel it maps density matrices on `ι` to
density matrices on `κ` (`Quantum.KrausChannel.apply`); as a measurement its index is the outcome
(`Quantum.KrausChannel.outcomeLaw`). -/
structure KrausChannel (R ι κ : Type*) [Fintype R] [Fintype ι] [Fintype κ] [DecidableEq ι] where
  /-- The Kraus operators. -/
  op : R → Matrix κ ι ℂ
  sum_conjTranspose_mul : ∑ r, (op r)ᴴ * op r = 1

namespace KrausChannel

variable {R ι κ : Type*} [Fintype R] [Fintype ι] [Fintype κ] [DecidableEq ι] (K : KrausChannel R ι κ)

/-- **The channel of a Kraus family**: `ρ ↦ ∑ r, op r * ρ * (op r)ᴴ`. -/
def apply (ρ : Matrix ι ι ℂ) : Matrix κ κ ℂ :=
  ∑ r, K.op r * ρ * (K.op r)ᴴ

/-- A Kraus channel applied to a matrix: `K ρ` is `K.apply ρ`. -/
instance : CoeFun (KrausChannel R ι κ) (fun _ => Matrix ι ι ℂ → Matrix κ κ ℂ) := ⟨apply⟩

/-- A Kraus family preserves the trace. -/
theorem trace_apply (ρ : Matrix ι ι ℂ) : (K ρ).trace = ρ.trace := by
  rw [apply, Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (K.op _) ρ, ← Matrix.trace_sum, ← Finset.sum_mul,
    K.sum_conjTranspose_mul, Matrix.one_mul]

/-- A Kraus family maps positive semidefinite matrices to positive semidefinite matrices. -/
theorem posSemidef_apply {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) : (K ρ).PosSemidef :=
  Matrix.posSemidef_sum _ fun r _ => hρ.mul_mul_conjTranspose_same (K.op r)

/-- The channel of a Kraus family on density matrices. -/
def applyMState (ρ : MState ι) : MState κ where
  mat := K ρ.mat
  posSemidef := K.posSemidef_apply ρ.posSemidef
  trace_eq_one := by rw [K.trace_apply, ρ.trace_eq_one]

@[simp]
theorem applyMState_mat (ρ : MState ι) : (K.applyMState ρ).mat = K ρ.mat :=
  rfl

/-- A Kraus family on a nonempty basis has a nonempty index type. -/
theorem nonempty [Nonempty ι] (K : KrausChannel R ι κ) : Nonempty R := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := K.sum_conjTranspose_mul
  rw [Finset.univ_eq_empty, Finset.sum_empty] at this
  obtain ⟨i⟩ := ‹Nonempty ι›
  have h1 := congrFun (congrFun this i) i
  simp at h1

/-- The probability of outcome `r`: `re (tr (op r * ρ * (op r)ᴴ))`. -/
def outcomeProb (ρ : MState ι) (r : R) : ℝ :=
  (K.op r * ρ.mat * (K.op r)ᴴ).trace.re

theorem outcomeProb_nonneg (ρ : MState ι) (r : R) : 0 ≤ K.outcomeProb ρ r :=
  (Complex.nonneg_iff.1 (ρ.posSemidef.mul_mul_conjTranspose_same (K.op r)).trace_nonneg).1

theorem sum_outcomeProb (ρ : MState ι) : ∑ r, K.outcomeProb ρ r = 1 := by
  have h := K.trace_apply ρ.mat
  rw [ρ.trace_eq_one, apply, Matrix.trace_sum] at h
  simp only [outcomeProb, ← Complex.re_sum, h, Complex.one_re]

/-- **The outcome law of a measurement** (HU25 p. 245, "measuring with projector P gives "yes"
with probability tr Pρ", for general measurement operators): outcome `r` has probability
`tr (op r * ρ * (op r)ᴴ)`. -/
def outcomeLaw (ρ : MState ι) : PMF R :=
  PMF.ofFintype (fun r => ENNReal.ofReal (K.outcomeProb ρ r)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun r _ => K.outcomeProb_nonneg ρ r, K.sum_outcomeProb,
      ENNReal.ofReal_one])

@[simp]
theorem outcomeLaw_apply (ρ : MState ι) (r : R) :
    K.outcomeLaw ρ r = ENNReal.ofReal (K.outcomeProb ρ r) :=
  rfl

/-- **The computational-basis measurement**: the projectors `|i⟩⟨i|`, with outcome `i`. -/
def basis (ι : Type*) [Fintype ι] [DecidableEq ι] : KrausChannel ι ι ι where
  op i := Matrix.single i i 1
  sum_conjTranspose_mul := by
    simp only [conjTranspose_single, star_one, single_mul_single_same, mul_one]
    exact sum_single_one

/-- The computational-basis measurement gives outcome `i` with probability `re (ρ i i)`. -/
theorem outcomeProb_basis {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : MState ι) (i : ι) :
    (basis ι).outcomeProb ρ i = (ρ.mat i i).re := by
  rw [outcomeProb, basis, conjTranspose_single, star_one, Matrix.trace_mul_cycle,
    single_mul_single_same, mul_one, trace_single_mul]
  simp

end KrausChannel

/-! ### Subdensity operators -/

section Sub

variable {ι : Type*} [Fintype ι]

/-- **The computational-basis law of a subdensity operator** (HU25 section 2.3, p. 245:
"density operators with trace ≤ 1, called subdensity operators … correspond to subprobability
distributions with total probability ≤ 1"): outcome `some i` with probability `re (ρ i i)`, and
`none`, non-termination, with the missing mass `1 - re (tr ρ)`. -/
def basisLaw (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace.re ≤ 1) :
    PMF (Option ι) :=
  PMF.ofFintype (fun o => o.elim (ENNReal.ofReal (1 - ρ.trace.re)) fun i =>
    ENNReal.ofReal (ρ i i).re) (by
      have hdiag : ∀ i, 0 ≤ (ρ i i).re := fun i =>
        (Complex.nonneg_iff.1 (hρ.diag_nonneg (i := i))).1
      rw [Fintype.sum_option]
      simp only [Option.elim]
      rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => hdiag i, ← re_trace_eq_sum,
        ← ENNReal.ofReal_add (by linarith) hρ.re_trace_nonneg]
      simp)

@[simp]
theorem basisLaw_some (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace.re ≤ 1) (i : ι) :
    basisLaw ρ hρ htr (some i) = ENNReal.ofReal (ρ i i).re :=
  rfl

@[simp]
theorem basisLaw_none (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace.re ≤ 1) :
    basisLaw ρ hρ htr none = ENNReal.ofReal (1 - ρ.trace.re) :=
  rfl

/-- Conjugating by two basis permutations in turn is conjugating by their composite. -/
theorem submatrix_perm_submatrix_perm (ρ : Matrix ι ι ℂ) (σ τ : Equiv.Perm ι) :
    (ρ.submatrix σ.symm σ.symm).submatrix τ.symm τ.symm =
      ρ.submatrix (σ.trans τ).symm (σ.trans τ).symm :=
  rfl

/-- Conjugating `ρ ⊗ τ` by a basis permutation of the first factor. -/
theorem kronecker_submatrix_prodCongr {E : Type*} (ρ : Matrix ι ι ℂ) (τ : Matrix E E ℂ)
    (π : Equiv.Perm ι) :
    (ρ ⊗ₖ τ).submatrix (π.prodCongr (Equiv.refl E)).symm (π.prodCongr (Equiv.refl E)).symm =
      ρ.submatrix π.symm π.symm ⊗ₖ τ :=
  rfl

end Sub

/-! ### Kraus maps -/

/-- **A Kraus map** (HU25 section 2.3, p. 245, "ρ ↦ ∑ E_i ρ E_i* for some E_i with
∑ E_i* E_i = I (or ≤ I if we allow subprobability distributions; we call this the normalization
condition) … We call such maps "Kraus maps""): operators `op r : Matrix κ ι ℂ` indexed by a
finite type `R` with `∑ r, (op r)ᴴ * op r ≤ 1` in the Loewner order. It maps subdensity operators
on `ι` to subdensity operators on `κ`. -/
structure KrausMap (R ι κ : Type*) [Fintype R] [Fintype ι] [Fintype κ] [DecidableEq ι] where
  /-- The Kraus operators. -/
  op : R → Matrix κ ι ℂ
  sum_le : ∑ r, (op r)ᴴ * op r ≤ 1

namespace KrausMap

variable {R ι κ : Type*} [Fintype R] [Fintype ι] [Fintype κ] [DecidableEq ι]
  (K : KrausMap R ι κ)

/-- **The map of a Kraus map**: `ρ ↦ ∑ r, op r * ρ * (op r)ᴴ`. -/
def apply (ρ : Matrix ι ι ℂ) : Matrix κ κ ℂ :=
  ∑ r, K.op r * ρ * (K.op r)ᴴ

/-- A Kraus map applied to a matrix: `K ρ` is `K.apply ρ`. -/
instance : CoeFun (KrausMap R ι κ) (fun _ => Matrix ι ι ℂ → Matrix κ κ ℂ) := ⟨apply⟩

/-- A Kraus map maps positive semidefinite matrices to positive semidefinite matrices. -/
theorem posSemidef_apply {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) : (K ρ).PosSemidef :=
  Matrix.posSemidef_sum _ fun r _ => hρ.mul_mul_conjTranspose_same (K.op r)

theorem trace_apply (ρ : Matrix ι ι ℂ) :
    (K ρ).trace = ((∑ r, (K.op r)ᴴ * K.op r) * ρ).trace := by
  rw [apply, Matrix.trace_sum, Finset.sum_mul, Matrix.trace_sum]
  exact Finset.sum_congr rfl fun r _ => Matrix.trace_mul_cycle (K.op r) ρ _

/-- **A Kraus map does not increase the trace** of a positive semidefinite matrix. -/
theorem re_trace_apply_le {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) :
    (K ρ).trace.re ≤ ρ.trace.re := by
  have h := (Matrix.le_iff.1 K.sum_le).re_trace_mul_nonneg hρ
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re] at h
  rw [K.trace_apply]
  linarith

/-- **A trace-preserving Kraus map preserves the trace.** -/
theorem trace_apply_of_tp (h : ∑ r, (K.op r)ᴴ * K.op r = 1) (ρ : Matrix ι ι ℂ) :
    (K ρ).trace = ρ.trace := by
  rw [K.trace_apply, h, Matrix.one_mul]

end KrausMap

namespace KrausMap

/-! #### Constructions of Kraus maps -/

section Constructions

variable {R : Type*} [Fintype R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A basis permutation, a Kraus map, a basis permutation**: the Kraus map that applies the
basis permutation `σ`, then `K`, then the basis permutation `τ`. Its operators are
`(K.op r).submatrix τ.symm σ`, the matrices of `U_τ * K.op r * U_σ`. -/
def permConj (K : KrausMap R ι ι) (σ τ : Equiv.Perm ι) : KrausMap R ι ι where
  op r := (K.op r).submatrix τ.symm σ
  sum_le := by
    have h : ∑ r, ((K.op r).submatrix τ.symm σ)ᴴ * (K.op r).submatrix τ.symm σ =
        (∑ r, (K.op r)ᴴ * K.op r).submatrix σ σ := by
      rw [submatrix_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [conjTranspose_submatrix, submatrix_mul_equiv]
    rw [h, Matrix.le_iff]
    have h1 : (1 : Matrix ι ι ℂ) = (1 : Matrix ι ι ℂ).submatrix σ σ := (submatrix_one_equiv σ).symm
    rw [h1]
    exact (Matrix.le_iff.1 K.sum_le).submatrix σ

theorem permConj_apply (K : KrausMap R ι ι) (σ τ : Equiv.Perm ι) (ρ : Matrix ι ι ℂ) :
    (K.permConj σ τ) ρ = (K (ρ.submatrix σ.symm σ.symm)).submatrix τ.symm τ.symm := by
  rw [apply, apply, submatrix_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hρ : ρ = (ρ.submatrix σ.symm σ.symm).submatrix σ σ := by
    rw [submatrix_submatrix]
    simp
  simp only [permConj]
  conv_lhs => rw [hρ]
  rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]

/-- **A Kraus map on the first factor**: `K ⊗ 1` on `ι × A` (HU25 p. 245, "Applying a Kraus map
{E_i}_i to A corresponds to applying the Kraus map {E_i ⊗ I}_i to AB"). -/
def tensorId (K : KrausMap R ι ι) (A : Type*) [Fintype A] [DecidableEq A] :
    KrausMap R (ι × A) (ι × A) where
  op r := K.op r ⊗ₖ (1 : Matrix A A ℂ)
  sum_le := by
    have h : ∑ r, (K.op r ⊗ₖ (1 : Matrix A A ℂ))ᴴ * (K.op r ⊗ₖ (1 : Matrix A A ℂ)) =
        (∑ r, (K.op r)ᴴ * K.op r) ⊗ₖ (1 : Matrix A A ℂ) := by
      rw [sum_kronecker]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]
    rw [h, Matrix.le_iff]
    have h2 : (1 : Matrix (ι × A) (ι × A) ℂ) - (∑ r, (K.op r)ᴴ * K.op r) ⊗ₖ 1 =
        (1 - ∑ r, (K.op r)ᴴ * K.op r) ⊗ₖ (1 : Matrix A A ℂ) := by
      ext ⟨a, b⟩ ⟨c, d⟩
      simp only [Matrix.sub_apply, kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
      by_cases hac : a = c <;> by_cases hbd : b = d <;> simp [hac, hbd]
    rw [h2]
    exact (Matrix.le_iff.1 K.sum_le).kronecker PosSemidef.one

theorem tensorId_apply (K : KrausMap R ι ι) {A : Type*} [Fintype A] [DecidableEq A]
    (ρ : Matrix ι ι ℂ) (τ : Matrix A A ℂ) :
    (K.tensorId A) (ρ ⊗ₖ τ) = K ρ ⊗ₖ τ := by
  rw [apply, apply, sum_kronecker]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [tensorId]
  rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, ← mul_kronecker_mul,
    Matrix.one_mul, Matrix.mul_one]

/-- The identity as a Kraus map with one operator. -/
def identity (ι : Type*) [Fintype ι] [DecidableEq ι] : KrausMap Unit ι ι where
  op _ := 1
  sum_le := by simp

@[simp]
theorem id_apply (ρ : Matrix ι ι ℂ) : (KrausMap.identity ι) ρ = ρ := by
  simp [apply, KrausMap.identity]

/-- `K` with its index set enlarged by a zero operator at `none`. -/
def optionSome (K : KrausMap R ι ι) : KrausMap (Option R) ι ι where
  op o := o.elim 0 K.op
  sum_le := by simpa [Fintype.sum_option] using K.sum_le

@[simp]
theorem optionSome_apply (K : KrausMap R ι ι) (ρ : Matrix ι ι ℂ) :
    K.optionSome ρ = K ρ := by
  simp [apply, optionSome, Fintype.sum_option]

/-- A Kraus map with one operator, placed at `none` of the index set `Option R`, with zero
operators at `some r`. -/
def optionNone (K : KrausMap Unit ι ι) (R : Type*) [Fintype R] : KrausMap (Option R) ι ι where
  op o := o.elim (K.op ()) 0
  sum_le := by simpa [Fintype.sum_option] using K.sum_le

@[simp]
theorem optionNone_apply (K : KrausMap Unit ι ι) (ρ : Matrix ι ι ℂ) :
    (K.optionNone R) ρ = K ρ := by
  simp [apply, optionNone, Fintype.sum_option]

end Constructions

/-! #### Runs of Kraus maps alternating with a basis permutation -/

section Run

variable {R : Type*} [Fintype R] {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- The Kraus map `step k` indexed by `ℕ`, applied to a matrix; the identity after `step d`. -/
def stepAt (step : Fin (d + 1) → KrausMap R ι ι) (k : ℕ) (ρ : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  if h : k < d + 1 then (step ⟨k, h⟩) ρ else ρ

theorem stepAt_of_lt (step : Fin (d + 1) → KrausMap R ι ι) {k : ℕ} (h : k < d + 1)
    (ρ : Matrix ι ι ℂ) : stepAt step k ρ = (step ⟨k, h⟩) ρ :=
  dif_pos h

theorem posSemidef_stepAt (step : Fin (d + 1) → KrausMap R ι ι) (k : ℕ) {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) : (stepAt step k ρ).PosSemidef := by
  unfold stepAt
  split_ifs
  · exact posSemidef_apply _ hρ
  · exact hρ

theorem re_trace_stepAt_le (step : Fin (d + 1) → KrausMap R ι ι) (k : ℕ) {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) : (stepAt step k ρ).trace.re ≤ ρ.trace.re := by
  unfold stepAt
  split_ifs
  · exact re_trace_apply_le _ hρ
  · exact le_rfl

/-- **Kraus maps alternating with a basis permutation** (the shape of HU25 Definition 6.3,
p. 248): `run step π ρ₀ k` is `(step k ∘ E_π ∘ step (k - 1) ∘ ⋯ ∘ E_π ∘ step 0)(ρ₀)`, where
`E_π(ρ) = UρU*` for `U = permOp π` is `ρ.submatrix π.symm π.symm`. -/
def run (step : Fin (d + 1) → KrausMap R ι ι) (π : Equiv.Perm ι) (ρ₀ : Matrix ι ι ℂ) :
    ℕ → Matrix ι ι ℂ
  | 0 => stepAt step 0 ρ₀
  | k + 1 => stepAt step (k + 1) ((run step π ρ₀ k).submatrix π.symm π.symm)

theorem run_zero (step : Fin (d + 1) → KrausMap R ι ι) (π : Equiv.Perm ι) (ρ₀ : Matrix ι ι ℂ) :
    run step π ρ₀ 0 = stepAt step 0 ρ₀ :=
  rfl

theorem run_succ (step : Fin (d + 1) → KrausMap R ι ι) (π : Equiv.Perm ι) (ρ₀ : Matrix ι ι ℂ)
    (k : ℕ) : run step π ρ₀ (k + 1) = stepAt step (k + 1) ((run step π ρ₀ k).submatrix π.symm π.symm) :=
  rfl

theorem posSemidef_run (step : Fin (d + 1) → KrausMap R ι ι) (π : Equiv.Perm ι)
    {ρ₀ : Matrix ι ι ℂ} (hρ₀ : ρ₀.PosSemidef) (k : ℕ) : (run step π ρ₀ k).PosSemidef := by
  induction k with
  | zero => exact posSemidef_stepAt step 0 hρ₀
  | succ k ih => exact posSemidef_stepAt step (k + 1) (ih.submatrix _)

theorem re_trace_run_le (step : Fin (d + 1) → KrausMap R ι ι) (π : Equiv.Perm ι)
    {ρ₀ : Matrix ι ι ℂ} (hρ₀ : ρ₀.PosSemidef) (k : ℕ) :
    (run step π ρ₀ k).trace.re ≤ ρ₀.trace.re := by
  induction k with
  | zero => exact re_trace_stepAt_le step 0 hρ₀
  | succ k ih =>
    refine (re_trace_stepAt_le step (k + 1) ((posSemidef_run step π hρ₀ k).submatrix _)).trans ?_
    rwa [trace_submatrix_equiv]

/-- **Trace-preserving steps keep the trace at every stage.** -/
theorem trace_stepAt_of_tp {step : Fin (d + 1) → KrausMap R ι ι}
    (hs : ∀ k, ∑ r, ((step k).op r)ᴴ * (step k).op r = 1) (k : ℕ) (ρ : Matrix ι ι ℂ) :
    (stepAt step k ρ).trace = ρ.trace := by
  unfold stepAt
  split_ifs
  · exact trace_apply_of_tp _ (hs _) ρ
  · rfl

/-- **A run of trace-preserving steps keeps the trace.** -/
theorem trace_run_of_tp {step : Fin (d + 1) → KrausMap R ι ι}
    (hs : ∀ k, ∑ r, ((step k).op r)ᴴ * (step k).op r = 1) (π : Equiv.Perm ι)
    (ρ₀ : Matrix ι ι ℂ) (k : ℕ) : (run step π ρ₀ k).trace = ρ₀.trace := by
  induction k with
  | zero => exact trace_stepAt_of_tp hs 0 ρ₀
  | succ k ih => rw [run_succ, trace_stepAt_of_tp hs, trace_submatrix_equiv, ih]

end Run

end KrausMap

/-- A trace-preserving Kraus family is a Kraus map. -/
def KrausChannel.toKrausMap {R ι κ : Type*} [Fintype R] [Fintype ι] [Fintype κ] [DecidableEq ι]
    (K : KrausChannel R ι κ) : KrausMap R ι κ where
  op := K.op
  sum_le := K.sum_conjTranspose_mul.le

end GordieHowe.Quantum
