-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.Compressed
public import GordieHowe.Model.Quantum.Core.MixedAlg
public import GordieHowe.Model.QROM.CoherentBridgeCore

@[expose] public section

/-!
# The compressed-oracle simulation of a dilated algorithm as a density-matrix run

`simState A` (`GordieHowe/Model/QROM/Compressed.lean`) runs a pure serial unitary algorithm `A` against the
compressed phase oracle. When `A` is the dilation of a general algorithm (its work register is
`V × Anc`, and on clean ancilla states its unitaries act on the reduced state as Kraus maps on
`QueryReg V 1 X Y`; `QueryAlg.Dilation`), tracing the ancilla out of the simulation gives a
density-matrix run on `QueryReg V 1 X Y × Slots`: each step applies the Kraus map tensored with
the identity on the database register, and each query conjugates by the matrix of the simulated
query `simQuery` on `SimRegister V` (`reduce_simStage_dilation`). The run (`densityRun`) takes only the
Kraus maps and the initial reduced state, so it does not depend on the dilation
(`densityRun_congr`: it depends on the Kraus maps only through their channels).

This generalizes `MixedAlg.dilRun_spec` (`GordieHowe/Model/Quantum/Core/MixedAlg.lean`), whose oracle is a
basis permutation of the system, to the compressed oracle, an operator on the system and the
database register that leaves the ancilla alone.

The general facts used: the cross matrix of two vectors (`cross`, the off-diagonal form of
`reduce`), operators that act as the identity on the ancilla (`liftKernel`), and the controlled
form of a step on the database register (`reduce_controlled`).
-/

open Finset Matrix
open scoped BigOperators Kronecker ComplexOrder

namespace GordieHowe.Quantum

/-! ### Cross matrices -/

section Cross

variable {ι A : Type*} [Fintype ι] [Fintype A]

/-- **The cross matrix of two vectors on `ι × A`**: the partial trace over `A` of `φχ*`,
`cross φ χ i j = ∑ a, φ (i, a) * conj (χ (j, a))`. `cross ψ ψ = reduce ψ`. -/
def cross (φ χ : QState (ι × A)) : Matrix ι ι ℂ :=
  Matrix.of fun i j => ∑ a, φ (i, a) * star (χ (j, a))

@[simp]
theorem cross_apply (φ χ : QState (ι × A)) (i j : ι) :
    cross φ χ i j = ∑ a, φ (i, a) * star (χ (j, a)) :=
  rfl

theorem cross_self (ψ : QState (ι × A)) : cross ψ ψ = reduce ψ :=
  rfl

end Cross

section CrossKraus

variable {R ι κ A C : Type*} [Fintype R] [Fintype ι] [Fintype κ] [Fintype A] [Fintype C]
  [DecidableEq ι] {e : A ≃ R × C} {r₀ : R}

omit [DecidableEq ι] in
/-- The cross matrix of two fresh vectors is a sum over the rest of the ancilla. -/
theorem cross_apply_of_fresh {φ χ : QState (ι × A)} (hφ : Fresh e r₀ φ) (i j : ι) :
    cross φ χ i j = ∑ c, φ (i, e.symm (r₀, c)) * star (χ (j, e.symm (r₀, c))) := by
  rw [cross_apply, sum_ancilla e]
  refine Finset.sum_eq_single r₀ (fun r _ hr => Finset.sum_eq_zero fun c _ => ?_) (by simp)
  rw [hφ i _ (by simpa using hr), zero_mul]

/-- **The Stinespring map acts on cross matrices as the channel**: for fresh `φ` and `χ`, the
cross matrix of their images is `K` applied to their cross matrix (the off-diagonal form of
`reduce_krausAct`). -/
theorem cross_krausAct (K : KrausChannel R ι κ) {φ χ : QState (ι × A)} (hφ : Fresh e r₀ φ) :
    cross (krausAct e r₀ K φ) (krausAct e r₀ K χ) = K (cross φ χ) := by
  ext k l
  rw [cross_apply, sum_ancilla e]
  simp only [KrausChannel.apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [krausAct_apply_symm, Matrix.mul_apply, cross_apply_of_fresh hφ,
    Matrix.conjTranspose_apply, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j₁ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j₂ _ => ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

end CrossKraus

/-! ### Operators that leave the ancilla alone -/

section Lift

variable {ι κ A : Type*} [Fintype ι] [Fintype κ] [Fintype A] [DecidableEq A]

/-- **A kernel on `ι` extended by the identity on `A`**: `L ⊗ 1`. -/
def liftKernel (L : ι → ι → ℂ) (p' p : ι × A) : ℂ :=
  if p'.2 = p.2 then L p'.1 p.1 else 0

theorem kernelOp_liftKernel_apply (L : ι → ι → ℂ) (ψ : QState (ι × A)) (i : ι) (a : A) :
    kernelOp (liftKernel L) ψ (i, a) = ∑ j, L i j * ψ (j, a) := by
  rw [kernelOp_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [liftKernel]

/-- The product of two lifted kernels is the lifted product. -/
theorem liftKernel_mul (L₁ L₂ : ι → ι → ℂ) (p' p : ι × A) :
    ∑ q, liftKernel L₁ p' q * liftKernel L₂ q p =
      liftKernel (A := A) (fun i j => ∑ k, L₁ i k * L₂ k j) p' p := by
  rw [Fintype.sum_prod_type]
  simp only [liftKernel]
  by_cases h : p'.2 = p.2
  · simp only [h, ↓reduceIte]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single p'.2 (fun a _ ha => by rw [h] at ha; simp [ha, Ne.symm ha]) (by simp)]
    simp [h]
  · simp only [h, ↓reduceIte]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun a _ => ?_
    by_cases ha : p'.2 = a
    · subst ha
      simp [h]
    · simp [ha]

/-- A lifted operator keeps a vector supported on a set of ancilla states. -/
theorem Supported.kernelOp_liftKernel {S : Set A} {ψ : QState (ι × A)}
    (hψ : Supported {p | p.2 ∈ S} ψ) (L : ι → ι → ℂ) :
    Supported {p | p.2 ∈ S} (Quantum.kernelOp (liftKernel L) ψ) := by
  rintro ⟨i, a⟩ ha
  rw [kernelOp_liftKernel_apply]
  exact Finset.sum_eq_zero fun j _ => by rw [hψ (j, a) ha, mul_zero]

/-- **A lifted operator conjugates the cross matrix**: for `L ⊗ 1`, the cross matrix of the
images is `L (cross φ χ) Lᴴ`. -/
theorem cross_kernelOp_liftKernel (L : ι → ι → ℂ) (φ χ : QState (ι × A)) :
    cross (kernelOp (liftKernel L) φ) (kernelOp (liftKernel L) χ) =
      Matrix.of L * cross φ χ * (Matrix.of L)ᴴ := by
  ext i i'
  simp only [cross_apply, kernelOp_liftKernel_apply, Matrix.mul_apply, Matrix.of_apply,
    Matrix.conjTranspose_apply, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j' _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

omit [Fintype κ] [DecidableEq A] in
/-- Relabelling the basis conjugates a kernel. -/
theorem relabel_kernelOp {ι' : Type*} [Fintype ι'] (σ : ι ≃ ι') (K : ι → ι → ℂ)
    (v : QState ι) :
    relabel σ (kernelOp K v) = kernelOp (fun i j => K (σ.symm i) (σ.symm j)) (relabel σ v) := by
  ext i
  simp only [relabel_apply, kernelOp_apply]
  exact (Equiv.sum_comp σ.symm _).symm

/-- A lifted kernel is the Kronecker product with the identity. -/
theorem of_liftKernel (L : ι → ι → ℂ) :
    Matrix.of (liftKernel (A := A) L) = Matrix.of L ⊗ₖ (1 : Matrix A A ℂ) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases h : a = b <;> simp [liftKernel, kroneckerMap_apply, Matrix.one_apply, h]

omit [Fintype κ] in
/-- **Conjugation by `L ⊗ 1`, blockwise**: the block at `(a, a')` of `(L ⊗ 1) X (L ⊗ 1)ᴴ` is
`L` conjugating the block of `X` at `(a, a')`. -/
theorem kronecker_one_conj_submatrix (L : Matrix ι ι ℂ) (X : Matrix (ι × A) (ι × A) ℂ)
    (a a' : A) :
    ((L ⊗ₖ (1 : Matrix A A ℂ)) * X * (L ⊗ₖ (1 : Matrix A A ℂ))ᴴ).submatrix (·, a) (·, a') =
      L * X.submatrix (·, a) (·, a') * Lᴴ := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [Finset.sum_eq_single a' (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp only [ite_true, star_one, mul_one, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

omit [Fintype κ] in
/-- **Products of kernels that are lifts after relabelling**: if `K₁` and `K₂` become `L₁ ⊗ 1`
and `L₂ ⊗ 1` after relabelling by `σ`, their product becomes `(L₁ L₂) ⊗ 1`. -/
theorem mulKernel_relabel_liftKernel {ι' : Type*} [Fintype ι'] (σ : ι' ≃ ι × A)
    {K₁ K₂ : ι' → ι' → ℂ} {L₁ L₂ : ι → ι → ℂ}
    (h₁ : ∀ p' p, K₁ (σ.symm p') (σ.symm p) = liftKernel L₁ p' p)
    (h₂ : ∀ p' p, K₂ (σ.symm p') (σ.symm p) = liftKernel L₂ p' p) (p' p : ι × A) :
    ∑ k, K₁ (σ.symm p') k * K₂ k (σ.symm p) =
      liftKernel (fun i j => ∑ k, L₁ i k * L₂ k j) p' p := by
  rw [← liftKernel_mul, ← Equiv.sum_comp σ.symm]
  exact Finset.sum_congr rfl fun q _ => by rw [h₁, h₂]

end Lift

/-! ### A step controlled by the database register -/

section Controlled

variable {ι κ A D : Type} [Fintype ι] [Fintype κ] [Fintype A] [Fintype D]

omit [Fintype ι] [Fintype κ] [Fintype A] [Fintype D] in
/-- The basis `ι × D` with `ι` split as system and ancilla, `ι ≃ κ × A`, regrouped as
`(κ × D) × A`. -/
def ctrlSplit (τ : ι ≃ κ × A) : ι × D ≃ (κ × D) × A where
  toFun p := (((τ p.1).1, p.2), (τ p.1).2)
  invFun q := (τ.symm (q.1.1, q.2), q.1.2)
  left_inv p := by simp
  right_inv q := by simp

omit [Fintype ι] [Fintype κ] [Fintype A] [Fintype D] in
@[simp]
theorem ctrlSplit_symm_apply (τ : ι ≃ κ × A) (q : (κ × D) × A) :
    (ctrlSplit τ).symm q = (τ.symm (q.1.1, q.2), q.1.2) :=
  rfl

omit [Fintype ι] [Fintype κ] [Fintype A] [Fintype D] in
@[simp]
theorem ctrlSplit_apply (τ : ι ≃ κ × A) (p : ι × D) :
    ctrlSplit τ p = (((τ p.1).1, p.2), (τ p.1).2) :=
  rfl

variable [DecidableEq κ] [DecidableEq D]

/-- **A Kraus map tensored with the identity, entrywise**: the block of `(K ⊗ 1) ρ` at
`(d, d')` is `K` applied to the block of `ρ` at `(d, d')`. -/
theorem _root_.GordieHowe.Quantum.KrausMap.tensorId_apply_submatrix {R : Type*} [Fintype R]
    (K : KrausMap R κ κ) (ρ : Matrix (κ × D) (κ × D) ℂ) (k k' : κ) (d d' : D) :
    (K.tensorId D) ρ (k, d) (k', d') = K (ρ.submatrix (·, d) (·, d')) k k' := by
  simp only [KrausMap.apply, KrausMap.tensorId, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply,
    Matrix.submatrix_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [Finset.sum_eq_single d' (fun e _ he => by simp [Ne.symm he]) (by simp)]
  simp only [ite_true, mul_one, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single d (fun e _ he => by simp [Ne.symm he]) (by simp)]
  simp

/-- The slice of a vector on `ι × D` at the database basis state `d`. -/
def slice (Ψ : QState (ι × D)) (d : D) : QState ι :=
  WithLp.toLp 2 fun i => Ψ (i, d)

omit [DecidableEq κ] [DecidableEq D] in
theorem controlled_slice (U : QState ι ≃ₗᵢ[ℂ] QState ι) (Ψ : QState (ι × D)) (d : D) :
    slice (controlled (fun _ => U) Ψ) d = U (slice Ψ d) :=
  rfl

/-- **A step controlled by the database register, on cross matrices**: if the unitary `U` on
`ι ≃ κ × A` acts on the cross matrices of vectors supported on the ancilla states `S` as the Kraus
map `K`, then applying `U` to every database slice acts on the cross matrices over the ancilla on
`κ × D` of vectors supported on `S` as `K ⊗ 1`. -/
theorem cross_controlled {R : Type*} [Fintype R] (τ : ι ≃ κ × A) (U : QState ι ≃ₗᵢ[ℂ] QState ι)
    (K : KrausMap R κ κ) {S : Set A}
    (hU : ∀ φ χ : QState (κ × A), Supported {p | p.2 ∈ S} φ → Supported {p | p.2 ∈ S} χ →
      cross (relabel τ (U (relabel τ.symm φ))) (relabel τ (U (relabel τ.symm χ))) =
        K (cross φ χ))
    {Ψ Φ : QState (ι × D)} (hΨ : Supported {p | p.2 ∈ S} (relabel (ctrlSplit τ) Ψ))
    (hΦ : Supported {p | p.2 ∈ S} (relabel (ctrlSplit τ) Φ)) :
    cross (relabel (ctrlSplit τ) (controlled (fun _ => U) Ψ))
        (relabel (ctrlSplit τ) (controlled (fun _ => U) Φ)) =
      (K.tensorId D) (cross (relabel (ctrlSplit τ) Ψ) (relabel (ctrlSplit τ) Φ)) := by
  have hsl : ∀ {Ψ : QState (ι × D)}, Supported {p | p.2 ∈ S} (relabel (ctrlSplit τ) Ψ) →
      ∀ d, Supported {p | p.2 ∈ S} (relabel τ (slice Ψ d)) := fun h d p hp =>
    h ((p.1, d), p.2) hp
  have hτ : ∀ (Ψ : QState (ι × D)) d, relabel τ.symm (relabel τ (slice Ψ d)) = slice Ψ d :=
    fun Ψ d => by
      ext i
      simp
  ext ⟨k, d⟩ ⟨k', d'⟩
  rw [KrausMap.tensorId_apply_submatrix]
  have hblk : (cross (relabel (ctrlSplit τ) Ψ) (relabel (ctrlSplit τ) Φ)).submatrix (·, d)
      (·, d') = cross (relabel τ (slice Ψ d)) (relabel τ (slice Φ d')) := by
    ext i j
    simp [slice]
  rw [hblk, ← hU _ _ (hsl hΨ d) (hsl hΦ d'), hτ, hτ]
  simp only [cross_apply, relabel_apply, ctrlSplit_symm_apply]
  rfl

/-- **A step controlled by the database register, reduced**: the case `Ψ = Φ` of
`cross_controlled`. -/
theorem reduce_controlled {R : Type*} [Fintype R] (τ : ι ≃ κ × A) (U : QState ι ≃ₗᵢ[ℂ] QState ι)
    (K : KrausMap R κ κ) {S : Set A}
    (hU : ∀ φ χ : QState (κ × A), Supported {p | p.2 ∈ S} φ → Supported {p | p.2 ∈ S} χ →
      cross (relabel τ (U (relabel τ.symm φ))) (relabel τ (U (relabel τ.symm χ))) =
        K (cross φ χ))
    {Ψ : QState (ι × D)} (hΨ : Supported {p | p.2 ∈ S} (relabel (ctrlSplit τ) Ψ)) :
    reduce (relabel (ctrlSplit τ) (controlled (fun _ => U) Ψ)) =
      (K.tensorId D) (reduce (relabel (ctrlSplit τ) Ψ)) :=
  cross_controlled τ U K hU hΨ hΨ

omit [DecidableEq κ] [DecidableEq D] in
/-- A step controlled by the database register keeps a vector supported on ancilla states if the
unitary does. -/
theorem Supported.controlled_ctrlSplit (τ : ι ≃ κ × A) (U : QState ι ≃ₗᵢ[ℂ] QState ι)
    {S S' : Set A}
    (hU : ∀ φ : QState (κ × A), Supported {p | p.2 ∈ S} φ →
      Supported {p | p.2 ∈ S'} (relabel τ (U (relabel τ.symm φ))))
    {Ψ : QState (ι × D)} (hΨ : Supported {p | p.2 ∈ S} (relabel (ctrlSplit τ) Ψ)) :
    Supported {p | p.2 ∈ S'} (relabel (ctrlSplit τ) (Quantum.controlled (fun _ => U) Ψ)) := by
  have hsl : ∀ d, Supported {p | p.2 ∈ S} (relabel τ (slice Ψ d)) := fun d p hp =>
    hΨ ((p.1, d), p.2) hp
  have hτ : ∀ d, relabel τ.symm (relabel τ (slice Ψ d)) = slice Ψ d := fun d => by
    ext i
    simp
  rintro ⟨⟨k, d⟩, a⟩ ha
  have := hU _ (hsl d) (k, a) ha
  rw [hτ] at this
  exact this

end Controlled

/-! ### Dilated query algorithms -/

namespace QueryAlg

variable {X Y O : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] {t : ℕ}

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
/-- The basis of the query registers with the work register split as `V × Anc`, regrouped with
the ancilla last. -/
def queryAncSplit {W V Anc : Type} (σ : W ≃ V × Anc) :
    QueryReg W 1 X Y ≃ QueryReg V 1 X Y × Anc where
  toFun r := (((σ r.1).1, r.2), (σ r.1).2)
  invFun p := (σ.symm (p.1.1, p.2), p.1.2)
  left_inv r := by simp
  right_inv p := by simp

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
@[simp]
theorem queryAncSplit_apply {W V Anc : Type} (σ : W ≃ V × Anc) (r : QueryReg W 1 X Y) :
    queryAncSplit σ r = (((σ r.1).1, r.2), (σ r.1).2) :=
  rfl

omit [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] in
@[simp]
theorem queryAncSplit_symm_apply {W V Anc : Type} (σ : W ≃ V × Anc)
    (p : QueryReg V 1 X Y × Anc) :
    (queryAncSplit (X := X) (Y := Y) σ).symm p = (σ.symm (p.1.1, p.2), p.1.2) :=
  rfl

/-- **A dilation of `A`**: the work register of `A` is `V × Anc`, and on vectors whose ancilla is
clean before step `k` (in `clean k`), step `k` of `A` gives a vector clean before step `k + 1`
and acts on cross matrices over the ancilla as the Kraus map `kraus k` on `QueryReg V 1 X Y`.
The initial state has reduced state `init` and a clean ancilla. The dilation of a general
algorithm (`MixedAlg.dilate`) is one, with `clean k` the ancilla states whose registers from step
`k` on are fresh. -/
structure Dilation (A : QueryAlg X Y t O) (V Anc R : Type) [Fintype V] [DecidableEq V]
    [Fintype Anc] [Fintype R] where
  /-- The split of the work register into the system and the ancilla. -/
  equiv : A.W ≃ V × Anc
  /-- The Kraus maps of the dilated algorithm. -/
  kraus : Fin (t + 1) → KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)
  /-- `clean k`: the ancilla states before step `k`. -/
  clean : ℕ → Set Anc
  /-- The initial reduced state. -/
  init : Matrix (QueryReg V 1 X Y) (QueryReg V 1 X Y) ℂ
  reduce_init : reduce (relabel (queryAncSplit equiv) A.init) = init
  supported_init : Supported {p | p.2 ∈ clean 0} (relabel (queryAncSplit equiv) A.init)
  supported_step : ∀ (k : Fin (t + 1)) (φ : QState (QueryReg V 1 X Y × Anc)),
    Supported {p | p.2 ∈ clean k} φ →
      Supported {p | p.2 ∈ clean (k + 1)}
        (relabel (queryAncSplit equiv) (A.step k (relabel (queryAncSplit equiv).symm φ)))
  cross_step : ∀ (k : Fin (t + 1)) (φ χ : QState (QueryReg V 1 X Y × Anc)),
    Supported {p | p.2 ∈ clean k} φ → Supported {p | p.2 ∈ clean k} χ →
      cross (relabel (queryAncSplit equiv) (A.step k (relabel (queryAncSplit equiv).symm φ)))
          (relabel (queryAncSplit equiv) (A.step k (relabel (queryAncSplit equiv).symm χ))) =
        kraus k (cross φ χ)

end QueryAlg

/-! ### Relabelling a Kraus family -/

namespace KrausChannel

variable {R ι κ : Type*} [Fintype R] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- **A Kraus family on a relabelled basis**: the operators conjugated by the relabelling
`e : ι ≃ κ`. -/
def relabel (K : KrausChannel R ι ι) (e : ι ≃ κ) : KrausChannel R κ κ where
  op r := (K.op r).submatrix e.symm e.symm
  sum_conjTranspose_mul := by
    simp only [conjTranspose_submatrix, submatrix_mul_equiv]
    rw [← submatrix_sum, K.sum_conjTranspose_mul, submatrix_one_equiv]

/-- The relabelled family acts on relabelled matrices as the family does. -/
theorem relabel_apply_submatrix (K : KrausChannel R ι ι) (e : ι ≃ κ) (ρ : Matrix ι ι ℂ) :
    K.relabel e (ρ.submatrix e.symm e.symm) = (K ρ).submatrix e.symm e.symm := by
  simp only [KrausChannel.apply, relabel, conjTranspose_submatrix, submatrix_mul_equiv,
    submatrix_sum]

/-- The relabelled family, entrywise. -/
theorem relabel_apply_apply (K : KrausChannel R ι ι) (e : ι ≃ κ) (X : Matrix κ κ ℂ) (i j : ι) :
    K.relabel e X (e i) (e j) = K (X.submatrix e e) i j := by
  have := congrFun (congrFun (K.relabel_apply_submatrix e (X.submatrix e e)) (e i)) (e j)
  simpa using this

end KrausChannel

theorem _root_.GordieHowe.Quantum.KrausChannel.toKrausMap_apply {R ι κ : Type*} [Fintype R] [Fintype ι]
    [Fintype κ] [DecidableEq ι] (K : KrausChannel R ι κ) (ρ : Matrix ι ι ℂ) :
    K.toKrausMap ρ = K ρ :=
  rfl

/-- Relabelling the system relabels the cross matrix. -/
theorem cross_relabel_prodCongr {ι κ A : Type*} [Fintype ι] [Fintype κ] [Fintype A] (e : ι ≃ κ)
    (φ χ : QState (ι × A)) :
    cross (relabel (e.prodCongr (Equiv.refl A)) φ) (relabel (e.prodCongr (Equiv.refl A)) χ) =
      (cross φ χ).submatrix e.symm e.symm := by
  ext i j
  simp [Equiv.prodCongr_symm]

/-! ### The dilation of a general algorithm is a dilation -/

namespace MixedAlg

variable {ι R M V X Y O : Type} [Fintype ι] [DecidableEq ι] [Fintype R]
  [Fintype M] [Nonempty R] [Nonempty M] [Fintype V] [DecidableEq V]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] {d : ℕ} (G : MixedAlg Unit ι d R M)

/-- The basis of the dilation of `G`, with the system `ι` identified with the query registers
`QueryReg V 1 X Y` by `e₀`, as the basis of the query registers of a work register
`W ≃ V × Anc ι d R M`. -/
def dilSplit {W : Type} (e₀ : ι ≃ QueryReg V 1 X Y) (σ : W ≃ V × Anc ι d R M) :
    ι × Anc ι d R M ≃ QueryReg W 1 X Y :=
  (e₀.prodCongr (Equiv.refl _)).trans (QueryAlg.queryAncSplit σ).symm

omit [DecidableEq ι] [Nonempty R]
  [Nonempty M] [DecidableEq V] [DecidableEq X] [DecidableEq Y] in
theorem queryAncSplit_dilSplit {W : Type} [Fintype W] (e₀ : ι ≃ QueryReg V 1 X Y)
    (σ : W ≃ V × Anc ι d R M) (ψ : QState (ι × Anc ι d R M)) :
    relabel (QueryAlg.queryAncSplit σ) (relabel (dilSplit e₀ σ) ψ) =
      relabel (e₀.prodCongr (Equiv.refl _)) ψ := by
  ext p
  simp [dilSplit, Equiv.prodCongr_symm]

/-- **`A` runs the dilation of `G`**: on the basis `dilSplit e₀ σ`, the initial state of `A` is
that of the dilation of `G` and each step of `A` is the corresponding unitary `dilStep`. -/
structure IsDilationOf (A : QueryAlg X Y d O) (e₀ : ι ≃ QueryReg V 1 X Y)
    (σ : A.W ≃ V × Anc ι d R M) : Prop where
  init_eq : A.init = relabel (dilSplit e₀ σ) (G.dilInit ())
  step_apply : ∀ k v,
    A.step k v = relabel (dilSplit e₀ σ) (G.dilStep () k (relabel (dilSplit e₀ σ).symm v))

variable {G}

omit [DecidableEq V] [DecidableEq X] [DecidableEq Y] in
theorem IsDilationOf.step_relabel {A : QueryAlg X Y d O} {e₀ : ι ≃ QueryReg V 1 X Y}
    {σ : A.W ≃ V × Anc ι d R M} (h : G.IsDilationOf A e₀ σ) (k : Fin (d + 1))
    (φ : QState (QueryReg V 1 X Y × Anc ι d R M)) :
    relabel (QueryAlg.queryAncSplit σ) (A.step k (relabel (QueryAlg.queryAncSplit σ).symm φ)) =
      relabel (e₀.prodCongr (Equiv.refl _))
        (G.dilStep () k (relabel (e₀.prodCongr (Equiv.refl _)).symm φ)) := by
  rw [h.step_apply, queryAncSplit_dilSplit]
  congr 2
  ext p
  simp [dilSplit, Equiv.prodCongr_symm]
  rfl

omit [DecidableEq ι] [DecidableEq V] [DecidableEq X]
  [DecidableEq Y] in
theorem cleanVec_relabel_symm {e₀ : ι ≃ QueryReg V 1 X Y} {n : ℕ}
    {φ : QState (QueryReg V 1 X Y × Anc ι d R M)}
    (hφ : Supported {p | p.2 ∈ {a | Clean n a}} φ) :
    CleanVec n (relabel (e₀.prodCongr (Equiv.refl (Anc ι d R M))).symm φ) := fun i a ha => by
  simpa [Equiv.prodCongr_symm] using hφ (e₀ i, a) ha

/-- **The dilation of `G` as a dilation of `A`**: the Kraus maps are those of `G` on the basis
`QueryReg V 1 X Y`, the clean ancilla states before step `k` are `Clean k`, and the initial
reduced state is `G.init ()`. -/
noncomputable def IsDilationOf.toDilation {A : QueryAlg X Y d O} {e₀ : ι ≃ QueryReg V 1 X Y}
    {σ : A.W ≃ V × Anc ι d R M} (h : G.IsDilationOf A e₀ σ) : A.Dilation V (Anc ι d R M) R where
  equiv := σ
  kraus k := ((G.step () k).relabel e₀).toKrausMap
  clean n := {a | Clean n a}
  init := (G.init ()).mat.submatrix e₀.symm e₀.symm
  reduce_init := by
    rw [h.init_eq, queryAncSplit_dilSplit, ← cross_self, cross_relabel_prodCongr, cross_self,
      reduce_dilInit]
  supported_init := fun p hp => by
    rw [h.init_eq, queryAncSplit_dilSplit, relabel_apply]
    exact G.cleanVec_dilInit () _ _ (by simpa [Equiv.prodCongr_symm] using hp)
  supported_step := fun k φ hφ p hp => by
    rw [h.step_relabel, relabel_apply]
    exact (G.dilStep_spec () (cleanVec_relabel_symm hφ)).1 _ _
      (by simpa [Equiv.prodCongr_symm] using hp)
  cross_step := fun k φ χ hφ hχ => by
    have hfφ := (cleanVec_relabel_symm (e₀ := e₀) hφ).fresh (k := k) le_rfl
    have hfχ := (cleanVec_relabel_symm (e₀ := e₀) hχ).fresh (k := k) le_rfl
    rw [h.step_relabel, h.step_relabel, cross_relabel_prodCongr]
    simp only [dilStep, k.isLt, dite_true, Fin.eta]
    rw [stinespring_apply_of_fresh _ hfφ, stinespring_apply_of_fresh _ hfχ, cross_krausAct _ hfφ,
      KrausChannel.toKrausMap_apply, ← KrausChannel.relabel_apply_submatrix,
      ← cross_relabel_prodCongr]
    congr 2 <;> ext p <;> simp [Equiv.prodCongr_symm, Prod.map]

end MixedAlg

/-! ### The coherent purification of a core algorithm -/

namespace Alg

variable {X Y O : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

/-- The query registers with the halting flag, `((v, q), b) ↦ ((v, b), q)`: the system of the
halting completion as the query registers of the work register `V × Bool`. -/
def haltSys (V : Type) : QueryReg V 1 X Y × Bool ≃ QueryReg (V × Bool) 1 X Y where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun r := ((r.1.1, r.2), r.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable (A : Alg X Y O)

/-- **The coherent pure algorithm of `A` runs the dilation of its halting completion.** -/
theorem isDilationOf_toQueryAlgCoh :
    haveI := A.init.nonempty
    A.halting.IsDilationOf A.toQueryAlgCoh (haltSys A.V) (Equiv.refl _) := by
  have := A.init.nonempty
  have hs : MixedAlg.dilSplit (haltSys (X := X) (Y := Y) A.V)
      (Equiv.refl ((A.V × Bool) × A.HaltAnc)) = haltRelabel A.V A.HaltAnc X Y :=
    Equiv.ext fun _ => rfl
  refine ⟨?_, fun k v => ?_⟩
  · rw [hs]
    rfl
  · rw [hs]
    rfl

/-- **The coherent pure algorithm of `A` as a dilation**: its Kraus maps are the halting
completions of the Kraus maps of `A`, its initial reduced state is `A.init` with the flag
`false`. -/
noncomputable def cohDilation :
    A.toQueryAlgCoh.Dilation (A.V × Bool) A.HaltAnc
      (A.R ⊕ Bool) :=
  haveI := A.init.nonempty
  (isDilationOf_toQueryAlgCoh A).toDilation

end Alg

/-! ### Trace preservation and the halting completion -/

namespace KrausMap

variable {R ι : Type*} [Fintype R] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- A matrix on `ι × Bool` that vanishes outside the flag-`false` block is that block tensored
with `|false⟩⟨false|`. -/
theorem eq_ffBlock_kronecker {Y : Matrix (ι × Bool) (ι × Bool) ℂ}
    (hY : ∀ i j b b', ¬ (b = false ∧ b' = false) → Y (i, b) (j, b') = 0) :
    Y = ffBlock Y ⊗ₖ Matrix.single false false (1 : ℂ) := by
  ext ⟨i, b⟩ ⟨j, b'⟩
  cases b <;> cases b' <;> simp [ffBlock, kroneckerMap_apply, hY]

/-- **The halting completion of a trace-preserving Kraus map never halts**: on a state with flag
`false` it applies the Kraus map and keeps the flag `false`. -/
theorem complete_apply_kronecker (K : KrausMap R ι ι) (hK : ∑ r, (K.op r)ᴴ * K.op r = 1)
    (Y : Matrix ι ι ℂ) :
    K.complete (Y ⊗ₖ Matrix.single false false (1 : ℂ)) =
      K Y ⊗ₖ Matrix.single false false (1 : ℂ) := by
  rw [KrausChannel.apply, Fintype.sum_sum_type, Fintype.sum_bool]
  simp only [complete, completeOp, conjTranspose_kronecker, conjTranspose_single, star_one,
    ← mul_kronecker_mul, haltOp_eq_zero hK, Matrix.zero_mul, zero_kronecker,
    Matrix.single_mul_single_same]
  rw [KrausMap.apply, sum_kronecker]
  simp [Matrix.single_mul_single_of_ne]

end KrausMap

/-- **A trace-preserving core algorithm**: every Kraus map satisfies `∑ r, (op r)ᴴ * op r = 1`
(the per-step condition of `AdaptiveIAlg.TracePreserving`). -/
def Alg.TracePreserving {X Y O : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (A : Alg X Y O) : Prop :=
  ∀ k, ∑ r, ((A.step k).op r)ᴴ * (A.step k).op r = 1

theorem Alg.tracePreserving_iff {X Y O : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    [DecidableEq Y] (A : Alg X Y O) :
    A.TracePreserving ↔ ∀ k, ∑ r, ((A.step k).op r)ᴴ * (A.step k).op r = 1 :=
  Iff.rfl

end GordieHowe.Quantum

namespace GordieHowe.QROM

open GordieHowe.Quantum

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {B : Type} (e : BitStr I J ≃ B)

/-! ### The kernels of the simulated query -/

section Kernels

variable (W : Type) [Fintype W] [DecidableEq W] (t : ℕ)

/-- The kernel of `hadamard`. -/
noncomputable def hadamardKernel (b' b : SimRegister W I J m t) : ℂ :=
  if b'.1.1 = b.1.1 ∧ qIn b'.1 = qIn b.1 ∧ b'.2 = b.2 then
    invSqrtCard I J * signOf ((qAns b'.1).dot (qAns b.1))
  else 0

/-- The kernel of `decOp`. -/
noncomputable def decKernel (b' b : SimRegister W I J m t) : ℂ :=
  if b'.1 = b.1 then
    (if IsDBState e b.2 then decX e t (qIn b.1) (slotsDB e b.2) else ket b.2) b'.2
  else 0

/-- The kernel of `phaseOp`. -/
noncomputable def phaseKernel (b' b : SimRegister W I J m t) : ℂ :=
  if b' = b then dbPhase e (qAns b.1) (qIn b.1) (slotsDB e b.2) else 0

/-- **The matrix of the simulated query** `simQuery = H ∘ Dec ∘ O0 ∘ Dec ∘ H`
(`simQuery_eq_kernelOp`). -/
noncomputable def simQueryKernel (b' b : SimRegister W I J m t) : ℂ :=
  ∑ c, hadamardKernel W t b' c * ∑ c₁, decKernel e W t c c₁ * ∑ c₂, phaseKernel e W t c₁ c₂ *
    ∑ c₃, decKernel e W t c₂ c₃ * hadamardKernel W t c₃ b

theorem hadamard_eq_kernelOp :
    hadamard W t = kernelOp (hadamardKernel (I := I) (J := J) (m := m) W t) :=
  rfl

theorem decOp_eq_kernelOp : decOp e W t = kernelOp (decKernel (m := m) e W t) :=
  rfl

theorem phaseOp_eq_kernelOp : phaseOp e W t = kernelOp (phaseKernel (m := m) e W t) :=
  rfl

theorem simQuery_eq_kernelOp (v : QState (SimRegister W I J m t)) :
    simQuery e W t v = kernelOp (simQueryKernel e W t) v := by
  simp only [simQuery, compressedOracle, ContinuousLinearMap.comp_apply, hadamard_eq_kernelOp,
    decOp_eq_kernelOp, phaseOp_eq_kernelOp, kernelOp_kernelOp]
  rfl

end Kernels

/-! ### The simulated query leaves the ancilla alone -/

section Lift

variable {V Anc W : Type} [Fintype V] [DecidableEq V] [Fintype Anc] [DecidableEq Anc]
  [Fintype W] [DecidableEq W] {t : ℕ}

/-- The basis of `Sim*` with the work register split as `V × Anc`, regrouped as the basis of
`Sim*` on `V` and the ancilla. -/
def simAncSplit (σ : W ≃ V × Anc) : SimRegister W I J m t ≃ SimRegister V I J m t × Anc :=
  ctrlSplit (QueryAlg.queryAncSplit σ)

omit [Fintype V] [Fintype Anc] [Fintype W] in
theorem hadamardKernel_simAncSplit (σ : W ≃ V × Anc) (p' p : SimRegister V I J m t × Anc) :
    hadamardKernel W t ((simAncSplit σ).symm p') ((simAncSplit σ).symm p) =
      liftKernel (hadamardKernel V t) p' p := by
  obtain ⟨⟨⟨v', q'⟩, s'⟩, a'⟩ := p'
  obtain ⟨⟨⟨v, q⟩, s⟩, a⟩ := p
  by_cases ha : a' = a
  · subst ha
    simp [simAncSplit, hadamardKernel, liftKernel]
  · simp [simAncSplit, hadamardKernel, liftKernel, ha]

omit [Fintype V] [Fintype Anc] [Fintype W] in
theorem decKernel_simAncSplit (σ : W ≃ V × Anc) (p' p : SimRegister V I J m t × Anc) :
    decKernel e W t ((simAncSplit σ).symm p') ((simAncSplit σ).symm p) =
      liftKernel (decKernel e V t) p' p := by
  obtain ⟨⟨⟨v', q'⟩, s'⟩, a'⟩ := p'
  obtain ⟨⟨⟨v, q⟩, s⟩, a⟩ := p
  by_cases ha : a' = a
  · subst ha
    simp only [simAncSplit, decKernel, liftKernel, ctrlSplit_symm_apply,
      QueryAlg.queryAncSplit_symm_apply, (Equiv.injective _).eq_iff,
      Prod.mk.injEq, and_true, ↓reduceIte]
    rfl
  · simp [simAncSplit, decKernel, liftKernel, ha]

omit [DecidableEq I] [DecidableEq J] [Fintype V] [Fintype Anc] [Fintype W] in
theorem phaseKernel_simAncSplit (σ : W ≃ V × Anc) (p' p : SimRegister V I J m t × Anc) :
    phaseKernel e W t ((simAncSplit σ).symm p') ((simAncSplit σ).symm p) =
      liftKernel (phaseKernel e V t) p' p := by
  obtain ⟨⟨⟨v', q'⟩, s'⟩, a'⟩ := p'
  obtain ⟨⟨⟨v, q⟩, s⟩, a⟩ := p
  by_cases ha : a' = a
  · subst ha
    simp [simAncSplit, phaseKernel, liftKernel]
  · simp [simAncSplit, phaseKernel, liftKernel, ha]

theorem simQueryKernel_simAncSplit (σ : W ≃ V × Anc) (p' p : SimRegister V I J m t × Anc) :
    simQueryKernel e W t ((simAncSplit σ).symm p') ((simAncSplit σ).symm p) =
      liftKernel (simQueryKernel e V t) p' p := by
  have h4 := mulKernel_relabel_liftKernel (simAncSplit σ) (decKernel_simAncSplit e σ)
    (hadamardKernel_simAncSplit (m := m) (t := t) σ)
  have h3 := mulKernel_relabel_liftKernel (simAncSplit σ) (phaseKernel_simAncSplit e σ)
    (K₂ := fun i j => ∑ k, decKernel e W t i k * hadamardKernel W t k j) h4
  have h2 := mulKernel_relabel_liftKernel (simAncSplit σ) (decKernel_simAncSplit e σ)
    (K₂ := fun i j => ∑ k, phaseKernel e W t i k *
      ∑ k', decKernel e W t k k' * hadamardKernel W t k' j) h3
  exact mulKernel_relabel_liftKernel (simAncSplit σ) (hadamardKernel_simAncSplit (m := m) σ)
    (K₂ := fun i j => ∑ k, decKernel e W t i k * ∑ k', phaseKernel e W t k k' *
      ∑ k'', decKernel e W t k' k'' * hadamardKernel W t k'' j) h2 p' p

/-- **The simulated query on `V × Anc` is the simulated query on `V` tensored with the identity on
the ancilla.** -/
theorem relabel_simQuery (σ : W ≃ V × Anc) (v : QState (SimRegister W I J m t)) :
    relabel (simAncSplit σ) (simQuery e W t v) =
      kernelOp (liftKernel (simQueryKernel e V t)) (relabel (simAncSplit σ) v) := by
  rw [simQuery_eq_kernelOp, relabel_kernelOp]
  refine congrArg (fun K => kernelOp K _) (funext fun p' => funext fun p => ?_)
  exact simQueryKernel_simAncSplit e σ p' p

end Lift

/-! ### The density-matrix run -/

section Run

variable {V R : Type} [Fintype V] [DecidableEq V] [Fintype R] {t : ℕ}

/-- **The density-matrix run of the compressed-oracle simulation** of a general algorithm with
Kraus maps `K` and initial state `ρ₀` on `QueryReg V 1 (Bits m) (BitStr I J)`: the initial state
with the empty database `|∅_t⟩`, then `K 0 ⊗ 1`, then for each of the `t` queries conjugation by
the matrix of the simulated query `simQuery` followed by the next Kraus map tensored with the
identity on the database register. -/
noncomputable def densityRun
    (K : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J)))
    (ρ₀ : Matrix (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J)) ℂ) :
    ℕ → Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ
  | 0 => KrausMap.stepAt (fun k => (K k).tensorId (Slots I J m t)) 0
      (ρ₀ ⊗ₖ Matrix.single (dbSlots e t (∅ : DB (Bits m) B)) (dbSlots e t (∅ : DB (Bits m) B)) 1)
  | k + 1 => KrausMap.stepAt (fun k => (K k).tensorId (Slots I J m t)) (k + 1)
      (Matrix.of (simQueryKernel e V t) * densityRun K ρ₀ k *
        (Matrix.of (simQueryKernel e V t))ᴴ)

/-- **The run depends on the Kraus maps only through their channels.** -/
theorem densityRun_congr {R' : Type} [Fintype R']
    {K : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J))}
    {K' : Fin (t + 1) → KrausMap R' (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J))}
    (hK : ∀ k ρ, K k ρ = K' k ρ)
    (ρ₀ : Matrix (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J)) ℂ)
    (k : ℕ) : densityRun e K ρ₀ k = densityRun e K' ρ₀ k := by
  have hT : ∀ (j : ℕ) (ρ : Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ),
      KrausMap.stepAt (fun k => (K k).tensorId (Slots I J m t)) j ρ =
        KrausMap.stepAt (fun k => (K' k).tensorId (Slots I J m t)) j ρ := by
    intro j ρ
    unfold KrausMap.stepAt
    split_ifs with h
    · ext ⟨a, d⟩ ⟨a', d'⟩
      rw [KrausMap.tensorId_apply_submatrix, KrausMap.tensorId_apply_submatrix, hK]
    · rfl
  induction k with
  | zero => exact hT 0 _
  | succ k ih =>
    simp only [densityRun]
    rw [ih, hT]

end Run

/-! ### The simulation of a dilated algorithm reduces to the density-matrix run -/

section Reduce

variable {V Anc R O : Type} [Fintype V] [DecidableEq V] [Fintype Anc]
  [Fintype R] {t : ℕ} {A : QueryAlg (Bits m) (BitStr I J) t O} (D : A.Dilation V Anc R)

theorem simStep_eq_controlled {k : ℕ} (hk : k < t + 1) :
    simStep A k = controlled fun _ => A.step ⟨k, hk⟩ := by
  rw [simStep, OracleAlg.stepAt_of_lt _ hk]
  rfl

theorem supported_simInit :
    Supported {p | p.2 ∈ D.clean 0} (relabel (simAncSplit D.equiv) (simInit e A)) := by
  rintro ⟨⟨k, s⟩, a⟩ ha
  have := D.supported_init (k, a) ha
  rw [relabel_apply] at this
  simp only [relabel_apply, simAncSplit, ctrlSplit_symm_apply, simInit]
  rw [this, zero_mul]

theorem reduce_simInit :
    reduce (relabel (simAncSplit D.equiv) (simInit e A)) =
      D.init ⊗ₖ Matrix.single (dbSlots e t (∅ : DB (Bits m) B)) (dbSlots e t (∅ : DB (Bits m) B)) 1 := by
  ext ⟨k, s⟩ ⟨k', s'⟩
  rw [← D.reduce_init]
  simp only [reduce_apply, relabel_apply, simAncSplit, ctrlSplit_symm_apply, simInit,
    kroneckerMap_apply, Matrix.single_apply, QueryAlg.queryAncSplit_symm_apply]
  by_cases hs : s = dbSlots e t (∅ : DB (Bits m) B) <;>
    by_cases hs' : s' = dbSlots e t (∅ : DB (Bits m) B) <;> simp [hs, hs', eq_comm]

/-- One step of the simulation: on a state whose ancilla is clean before step `k`, `simStep k`
gives a state clean before step `k + 1` and applies `kraus k ⊗ 1` to the reduced state. -/
theorem simStep_spec {k : ℕ} (hk : k < t + 1) {Ψ : QState (SimRegister A.W I J m t)}
    (hΨ : Supported {p | p.2 ∈ D.clean k} (relabel (simAncSplit D.equiv) Ψ)) :
    Supported {p | p.2 ∈ D.clean (k + 1)} (relabel (simAncSplit D.equiv) (simStep A k Ψ)) ∧
      reduce (relabel (simAncSplit D.equiv) (simStep A k Ψ)) =
        KrausMap.stepAt (fun k => (D.kraus k).tensorId (Slots I J m t)) k
          (reduce (relabel (simAncSplit D.equiv) Ψ)) := by
  rw [simStep_eq_controlled hk, KrausMap.stepAt_of_lt _ hk]
  exact ⟨Supported.controlled_ctrlSplit _ _ (D.supported_step ⟨k, hk⟩) hΨ,
    reduce_controlled _ _ _ (D.cross_step ⟨k, hk⟩) hΨ⟩

/-- The run of the simulation, with the cleanliness invariant. -/
theorem simStage_spec {k : ℕ} (hk : k ≤ t) :
    Supported {p | p.2 ∈ D.clean (k + 1)} (relabel (simAncSplit D.equiv) (simStage e A k)) ∧
      reduce (relabel (simAncSplit D.equiv) (simStage e A k)) = densityRun e D.kraus D.init k := by
  classical
  induction k with
  | zero =>
    obtain ⟨h1, h2⟩ := simStep_spec D (Nat.succ_pos t) (supported_simInit e D)
    refine ⟨h1, ?_⟩
    change reduce (relabel (simAncSplit D.equiv) (simStep A 0 (simInit e A))) = _
    rw [h2, reduce_simInit]
    rfl
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih (Nat.le_of_succ_le hk)
    have hq := relabel_simQuery e D.equiv (simStage e A k)
    obtain ⟨h1, h2⟩ := simStep_spec D (Nat.lt_succ_of_le hk)
      (Ψ := simQuery e A.W t (simStage e A k)) (by rw [hq]; exact ih1.kernelOp_liftKernel _)
    refine ⟨h1, ?_⟩
    change reduce (relabel (simAncSplit D.equiv)
      (simStep A (k + 1) (simQuery e A.W t (simStage e A k)))) = _
    rw [h2, hq, ← cross_self, cross_kernelOp_liftKernel, cross_self, ih2]
    rfl

/-- **Tracing the ancilla out of the simulation of a dilated algorithm gives the density-matrix
run**: after step `k ≤ t`, the reduced state of `simStage A k` on the registers `QueryReg V` and
the database is `densityRun e D.kraus D.init k`, which takes only the Kraus maps and the initial
reduced state of the dilation. -/
theorem reduce_simStage_dilation {k : ℕ} (hk : k ≤ t) :
    reduce (relabel (simAncSplit D.equiv) (simStage e A k)) = densityRun e D.kraus D.init k :=
  (simStage_spec e D hk).2

/-- **The final simulated state `|Sim*(A)⟩` of a dilated algorithm, with the ancilla traced out, is
the density-matrix run.** -/
theorem reduce_simState_dilation :
    reduce (relabel (simAncSplit D.equiv) (simState e A)) = densityRun e D.kraus D.init t :=
  reduce_simStage_dilation e D le_rfl

end Reduce

/-! ### The halting flag -/

end GordieHowe.QROM
