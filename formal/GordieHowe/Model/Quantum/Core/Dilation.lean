-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Core.Channel
public import GordieHowe.Model.Quantum.Core.Born
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

/-!
# Purification and Stinespring dilation in finite dimension

The facts that turn the mixed-state formalism of `GordieHowe/Model/Quantum/Core/Channel.lean` into the pure-state
formalism of `GordieHowe/Model/Quantum/Core/State.lean`, for a system with computational basis `ι` and an ancilla
register with basis `A`.

- `reduce ψ` is the reduced density matrix of a vector `ψ` on `ι × A` on the system `ι`, the
  partial trace of `ψψ*` over the ancilla: `reduce ψ i j = ∑ a, ψ (i, a) * conj (ψ (j, a))`. It is
  positive semidefinite with trace `‖ψ‖²` (`posSemidef_reduce`, `trace_reduce`). Measuring `ψ` in
  the computational basis and reading the system gives the computational-basis law of
  `reduce ψ` (`probIn_reduceMState`).
- **Purification** (`purify`, `reduce_purify`): every density matrix `ρ` on `ι` is `reduce ψ` for
  a unit vector `ψ` on `ι × ι`. With `ρ = Bᴴ B` (`B` the square root of `ρ`),
  `ψ (i, a) = conj (B a i)`.
- **Extension of an isometry to a unitary** (`extendUnitary`): on a finite-dimensional inner
  product space, a linear map that preserves the norm of every vector of a subspace `S` agrees
  on `S` with a unitary. This is Mathlib's `LinearIsometry.extend`.
- **Stinespring dilation** (`stinespring`, `reduce_stinespring`): for a Kraus family
  `K : KrausChannel R ι ι` and an ancilla `A ≃ R × C` with a register `R` in a fixed basis state `r₀`
  (a fresh register), the map `ψ ↦ ∑ r, (K r ⊗ |r⟩⟨r₀|) ψ` preserves norms on the vectors whose
  `R` register is `r₀` (`norm_krausAct`), so it agrees there with a unitary; the reduced state
  after it is `K.apply` of the reduced state before. The register `R` afterwards holds the Kraus
  index: measuring it gives outcome `r` with probability `tr (K r ρ (K r)ᴴ)`
  (`prob_krausAct_fiber`), the outcome law of `K` as a measurement. This is Naimark's dilation
  of a measurement, and with the outcome register never touched again it is the principle of
  deferred measurement. The rest `C` of the ancilla is not touched (`krausAct_eq_zero_of`).

Everything here is about Mathlib objects only.
-/

open Finset Matrix
open scoped BigOperators ComplexOrder MatrixOrder

namespace GordieHowe.Quantum

/-! ### Born laws of functions of the outcome -/

/-- The Born law of a function `g` of the computational-basis outcome gives the value `k` the
probability of the preimage of `k`. -/
theorem born_map_apply {ι κ : Type*} [Fintype ι] (v : QState ι) (hv : ‖v‖ = 1) (g : ι → κ)
    (k : κ) : (born v hv).map g k = ENNReal.ofReal (prob (g ⁻¹' {k}) v) := by
  classical
  rw [PMF.map_apply, tsum_fintype, prob, norm_mask_sq,
    ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : g i = k
  · simp [h, born, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]
  · simp [h, Ne.symm h]

/-- The Born probability of a set on a relabelled basis is that of its preimage. -/
theorem prob_relabel {ι κ : Type*} [Fintype ι] [Fintype κ] (σ : ι ≃ κ) (S : Set κ)
    (v : QState ι) : prob S (relabel σ v) = prob (σ ⁻¹' S) v := by
  classical
  rw [prob, prob, norm_mask_sq, norm_mask_sq, Finset.sum_filter, Finset.sum_filter]
  rw [← Equiv.sum_comp σ]
  simp

/-! ### Reduced density matrices -/

section Reduce

variable {ι A : Type*} [Fintype ι] [Fintype A]

/-- **The reduced density matrix on the system** of a vector `ψ` on `ι × A`: the partial trace of
`ψψ*` over `A`, `reduce ψ i j = ∑ a, ψ (i, a) * conj (ψ (j, a))`. -/
def reduce (ψ : QState (ι × A)) : Matrix ι ι ℂ :=
  Matrix.of fun i j => ∑ a, ψ (i, a) * star (ψ (j, a))

@[simp]
theorem reduce_apply (ψ : QState (ι × A)) (i j : ι) :
    reduce ψ i j = ∑ a, ψ (i, a) * star (ψ (j, a)) :=
  rfl

/-- The reduced density matrix is `Mᴴ M` for `M a i = conj (ψ (i, a))`. -/
theorem reduce_eq_conjTranspose_mul (ψ : QState (ι × A)) :
    reduce ψ = (Matrix.of fun (a : A) (i : ι) => star (ψ (i, a)))ᴴ *
      Matrix.of fun (a : A) (i : ι) => star (ψ (i, a)) := by
  ext i j
  simp [Matrix.mul_apply]

theorem posSemidef_reduce (ψ : QState (ι × A)) : (reduce ψ).PosSemidef := by
  rw [reduce_eq_conjTranspose_mul]
  exact posSemidef_conjTranspose_mul_self _

/-- The trace of the reduced density matrix is the squared norm. -/
theorem trace_reduce (ψ : QState (ι × A)) : (reduce ψ).trace = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag_apply, reduce_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

/-- Two vectors with reduced density matrices of equal trace have equal norms. -/
theorem norm_eq_norm_of_trace_reduce_eq {κ B : Type*} [Fintype κ] [Fintype B]
    {φ : QState (ι × A)} {ψ : QState (κ × B)} (h : (reduce φ).trace = (reduce ψ).trace) : ‖φ‖ = ‖ψ‖ := by
  rw [trace_reduce, trace_reduce, Complex.ofReal_inj] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- The reduced density matrix of a unit vector, as a density matrix. -/
def reduceMState (ψ : QState (ι × A)) (hψ : ‖ψ‖ = 1) : MState ι where
  mat := reduce ψ
  posSemidef := posSemidef_reduce ψ
  trace_eq_one := by rw [trace_reduce, hψ]; simp

@[simp]
theorem reduceMState_mat (ψ : QState (ι × A)) (hψ : ‖ψ‖ = 1) :
    (reduceMState ψ hψ).mat = reduce ψ :=
  rfl

/-- The diagonal of the reduced density matrix is the Born weight of the system's basis
states. -/
theorem re_reduce_apply_self (ψ : QState (ι × A)) (i : ι) :
    (reduce ψ i i).re = ∑ a, ‖ψ (i, a)‖ ^ 2 := by
  simp only [reduce_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]

/-- Measuring a vector in the computational basis and reading the system gives the
computational-basis law of its reduced density matrix. -/
theorem probIn_reduceMState (ψ : QState (ι × A)) (hψ : ‖ψ‖ = 1) (B : Set ι) :
    (reduceMState ψ hψ).probIn B = prob {p | p.1 ∈ B} ψ := by
  classical
  rw [MState.probIn, prob, norm_mask_sq, Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i ∈ B
  · simp only [Set.indicator, reduceMState_mat, Set.mem_ofPred_eq, h, ite_true,
      re_reduce_apply_self]
  · simp [h]

/-- A basis permutation of the system acts on the reduced density matrix by conjugation. -/
theorem reduce_permOp_prodCongr (π : Equiv.Perm ι) (ψ : QState (ι × A)) :
    reduce (permOp (π.prodCongr (Equiv.refl A)) ψ) = (reduce ψ).submatrix π.symm π.symm := by
  ext i j
  simp [Equiv.prodCongr_symm]

/-- The reduced density matrix of a unit vector after a basis permutation of the system is the
permuted reduced density matrix. -/
theorem reduceMState_permOp_prodCongr (π : Equiv.Perm ι) (ψ : QState (ι × A)) (hψ : ‖ψ‖ = 1) :
    reduceMState (permOp (π.prodCongr (Equiv.refl A)) ψ)
        (by rw [LinearIsometryEquiv.norm_map, hψ]) =
      (reduceMState ψ hψ).permute π :=
  MState.ext (reduce_permOp_prodCongr π ψ)

end Reduce

/-! ### Purification -/

section Purify

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A purification of a density matrix**: a vector on `ι × ι` whose reduced density matrix is
`ρ` (`reduce_purify`). With `ρ = Bᴴ B`, it is `ψ (i, a) = conj (B a i)`. -/
noncomputable def purify (ρ : MState ι) : QState (ι × ι) :=
  WithLp.toLp 2 fun p => star ((exists_eq_conjTranspose_mul_self ρ.posSemidef).choose p.2 p.1)

theorem reduce_purify (ρ : MState ι) : reduce (purify ρ) = ρ.mat := by
  have h := (exists_eq_conjTranspose_mul_self ρ.posSemidef).choose_spec
  conv_rhs => rw [h]
  ext i j
  simp [purify, Matrix.mul_apply]

theorem norm_purify (ρ : MState ι) : ‖purify ρ‖ = 1 := by
  have h := trace_reduce (purify ρ)
  rw [reduce_purify, ρ.trace_eq_one] at h
  have h2 : ‖purify ρ‖ ^ 2 = 1 := by exact_mod_cast h.symm
  rwa [pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero] at h2

end Purify

/-! ### Fresh registers -/

section Append

variable {ι P B : Type*} [Fintype ι] [Fintype P] [Fintype B] [DecidableEq B]

/-- The vector `ψ ⊗ |b⟩`: a register `B` in the basis state `b` appended to the ancilla. -/
def appendKet (ψ : QState (ι × P)) (b : B) : QState (ι × (P × B)) :=
  WithLp.toLp 2 fun p => ψ (p.1, p.2.1) * if p.2.2 = b then 1 else 0

@[simp]
theorem appendKet_apply (ψ : QState (ι × P)) (b : B) (p : ι × (P × B)) :
    appendKet ψ b p = ψ (p.1, p.2.1) * if p.2.2 = b then 1 else 0 :=
  rfl

/-- Appending a register in a basis state does not change the reduced density matrix. -/
theorem reduce_appendKet (ψ : QState (ι × P)) (b : B) : reduce (appendKet ψ b) = reduce ψ := by
  ext i j
  simp only [reduce_apply, appendKet_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single b (fun b' _ h => by simp [h]) (by simp)]
  simp

theorem norm_appendKet (ψ : QState (ι × P)) (b : B) : ‖appendKet ψ b‖ = ‖ψ‖ :=
  norm_eq_norm_of_trace_reduce_eq (by rw [reduce_appendKet])

end Append

/-! ### Extension of an isometry to a unitary -/

section Extend

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

/-- **A linear map that preserves norms on a subspace agrees there with a unitary**, in finite
dimension (Mathlib's `LinearIsometry.extend`, `extendUnitary_apply_of_mem`). -/
noncomputable def extendUnitary (S : Submodule ℂ V) (J : V →ₗ[ℂ] V)
    (hJ : ∀ v ∈ S, ‖J v‖ = ‖v‖) : V ≃ₗᵢ[ℂ] V :=
  (LinearIsometry.extend
    { toLinearMap := J ∘ₗ S.subtype
      norm_map' := fun v => hJ v v.2 }).toLinearIsometryEquiv rfl

theorem extendUnitary_apply_of_mem (S : Submodule ℂ V) (J : V →ₗ[ℂ] V)
    (hJ : ∀ v ∈ S, ‖J v‖ = ‖v‖) {v : V} (hv : v ∈ S) : extendUnitary S J hJ v = J v :=
  LinearIsometry.extend_apply _ ⟨v, hv⟩

end Extend

/-! ### Stinespring dilation of a Kraus family -/

section Stinespring

variable {R ι κ A C : Type*} [Fintype R] [Fintype ι] [Fintype κ] [Fintype A] [Fintype C]
  [DecidableEq ι] (e : A ≃ R × C) (r₀ : R)

/-- A vector whose register `R` (the first component of the ancilla split `e`) is in the basis
state `r₀`. -/
def Fresh (ψ : QState (ι × A)) : Prop :=
  ∀ i a, (e a).1 ≠ r₀ → ψ (i, a) = 0

/-- The vectors whose register `R` is in the basis state `r₀`. -/
def freshSubmodule : Submodule ℂ (QState (ι × A)) where
  carrier := {ψ | Fresh e r₀ ψ}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := fun {ψ φ} hψ hφ i a ha => by
    change ψ (i, a) + φ (i, a) = 0
    rw [hψ i a ha, hφ i a ha, add_zero]
  smul_mem' := fun c ψ hψ i a ha => by
    change c * ψ (i, a) = 0
    rw [hψ i a ha, mul_zero]

/-- **The Stinespring map of a Kraus family on a fresh register**: `ψ ↦ ∑ r, (K r ⊗ |r⟩⟨r₀|) ψ`,
`(krausAct K e r₀ ψ) (i, a) = ∑ j, K (e a).1 i j * ψ (j, a')` with `a'` the ancilla state `a` with
register `R` set to `r₀`. -/
def krausAct (K : KrausChannel R ι κ) : QState (ι × A) →ₗ[ℂ] QState (κ × A) where
  toFun ψ := WithLp.toLp 2 fun p => ∑ j, K.op (e p.2).1 p.1 j * ψ (j, e.symm (r₀, (e p.2).2))
  map_add' ψ φ := by
    ext p
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c ψ := by
    ext p
    simp [Finset.mul_sum, mul_left_comm]

variable {e r₀}

omit [Fintype C] in
theorem krausAct_apply (K : KrausChannel R ι κ) (ψ : QState (ι × A)) (k : κ) (a : A) :
    krausAct e r₀ K ψ (k, a) = ∑ j, K.op (e a).1 k j * ψ (j, e.symm (r₀, (e a).2)) :=
  rfl

omit [Fintype C] in
@[simp]
theorem krausAct_apply_symm (K : KrausChannel R ι κ) (ψ : QState (ι × A)) (k : κ) (r : R) (c : C) :
    krausAct e r₀ K ψ (k, e.symm (r, c)) = ∑ j, K.op r k j * ψ (j, e.symm (r₀, c)) := by
  simp [krausAct_apply]

/-- A sum over the ancilla is a sum over the register `R` and the rest `C`. -/
theorem sum_ancilla {M : Type*} [AddCommMonoid M] (e : A ≃ R × C) (f : A → M) : ∑ a, f a = ∑ r, ∑ c, f (e.symm (r, c)) := by
  rw [← Fintype.sum_prod_type']
  exact (Equiv.sum_comp e.symm f).symm

omit [DecidableEq ι] in
/-- The reduced density matrix of a fresh vector is a sum over the rest of the ancilla. -/
theorem reduce_apply_of_fresh {ψ : QState (ι × A)} (hψ : Fresh e r₀ ψ) (i j : ι) :
    reduce ψ i j = ∑ c, ψ (i, e.symm (r₀, c)) * star (ψ (j, e.symm (r₀, c))) := by
  rw [reduce_apply, sum_ancilla e]
  refine Finset.sum_eq_single r₀ (fun r _ hr => Finset.sum_eq_zero fun c _ => ?_) (by simp)
  rw [hψ i _ (by simpa using hr), zero_mul]

/-- **The fiber of the Kraus index `r`**: after the Stinespring map, the part of the state with
register `R` equal to `r` has reduced density matrix `K r ρ (K r)ᴴ`. -/
theorem sum_fiber_krausAct (K : KrausChannel R ι κ) {ψ : QState (ι × A)} (hψ : Fresh e r₀ ψ) (r : R)
    (k l : κ) :
    ∑ c, krausAct e r₀ K ψ (k, e.symm (r, c)) * star (krausAct e r₀ K ψ (l, e.symm (r, c))) =
      (K.op r * reduce ψ * (K.op r)ᴴ) k l := by
  simp only [krausAct_apply_symm, Matrix.mul_apply, reduce_apply_of_fresh hψ,
    Matrix.conjTranspose_apply, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j₁ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j₂ _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- **Stinespring dilation, reduced state**: the reduced density matrix after the Stinespring map
of a fresh vector is the channel `K.apply` of the reduced density matrix before it. -/
theorem reduce_krausAct (K : KrausChannel R ι κ) {ψ : QState (ι × A)} (hψ : Fresh e r₀ ψ) :
    reduce (krausAct e r₀ K ψ) = K (reduce ψ) := by
  ext k l
  rw [reduce_apply, sum_ancilla e]
  simp only [KrausChannel.apply, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun r _ => sum_fiber_krausAct K hψ r k l

/-- The Stinespring map preserves the norm of fresh vectors. -/
theorem norm_krausAct (K : KrausChannel R ι κ) {ψ : QState (ι × A)} (hψ : Fresh e r₀ ψ) :
    ‖krausAct e r₀ K ψ‖ = ‖ψ‖ :=
  norm_eq_norm_of_trace_reduce_eq (by rw [reduce_krausAct K hψ, K.trace_apply])

omit [Fintype C] in
/-- The Stinespring map does not touch the rest `C` of the ancilla: if `ψ` vanishes on the basis
states whose ancilla satisfies `P`, and `P` still holds after the register `R` is reset to `r₀`,
then the image vanishes there too. -/
theorem krausAct_eq_zero_of (K : KrausChannel R ι κ) {P : A → Prop} {ψ : QState (ι × A)}
    (hψ : ∀ i a, P a → ψ (i, a) = 0) (hP : ∀ a, P a → P (e.symm (r₀, (e a).2))) (k : κ) {a : A}
    (ha : P a) : krausAct e r₀ K ψ (k, a) = 0 := by
  rw [krausAct_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [hψ j _ (hP a ha), mul_zero]

/-- **Naimark dilation of a measurement**: after the Stinespring map of a fresh vector, measuring
the register `R` gives `r` with probability `tr (K r ρ (K r)ᴴ)` for the reduced density matrix
`ρ` before it. -/
theorem prob_krausAct_fiber (K : KrausChannel R ι κ) {ψ : QState (ι × A)} (hψ : Fresh e r₀ ψ) (r : R) :
    prob ((fun p : κ × A => (e p.2).1) ⁻¹' {r}) (krausAct e r₀ K ψ) =
      (K.op r * reduce ψ * (K.op r)ᴴ).trace.re := by
  classical
  rw [prob, norm_mask_sq, Finset.sum_filter, Fintype.sum_prod_type, Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.diag_apply, ← sum_fiber_krausAct K hψ r k k, Complex.re_sum, sum_ancilla e,
    Finset.sum_eq_single r (fun r' _ hr' => Finset.sum_eq_zero fun c _ => by simp [hr'])
      (by simp)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ite_eq_left (by simp), RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.ofReal_re]

variable (e r₀)

/-- **The Stinespring unitary of a Kraus family**: a unitary on `ι × A` that agrees with the
Stinespring map on fresh vectors (`stinespring_apply_of_fresh`). -/
noncomputable def stinespring (K : KrausChannel R ι ι) : QState (ι × A) ≃ₗᵢ[ℂ] QState (ι × A) :=
  extendUnitary (freshSubmodule e r₀) (krausAct e r₀ K) fun _ hψ => norm_krausAct K hψ

variable {e r₀}

theorem stinespring_apply_of_fresh (K : KrausChannel R ι ι) {ψ : QState (ι × A)} (hψ : Fresh e r₀ ψ) :
    stinespring e r₀ K ψ = krausAct e r₀ K ψ :=
  extendUnitary_apply_of_mem _ _ _ hψ

/-- **Stinespring dilation** (finite dimension): the reduced density matrix after the
Stinespring unitary of a fresh vector is the channel `K.apply` of the reduced density matrix
before it. -/
theorem reduce_stinespring (K : KrausChannel R ι ι) {ψ : QState (ι × A)} (hψ : Fresh e r₀ ψ) :
    reduce (stinespring e r₀ K ψ) = K (reduce ψ) := by
  rw [stinespring_apply_of_fresh K hψ, reduce_krausAct K hψ]

end Stinespring

end GordieHowe.Quantum
