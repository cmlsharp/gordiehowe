-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.AdaptiveTest
public import GordieHowe.Model.Quantum.Interactive.AdaptiveTP

@[expose] public section

/-!
# Kraus maps and circuits acting alike on a larger register

A register `ι'` that splits as `ι × Z` along an equivalence `E` carries the matrices
`liftMat E ρ τ`, the matrix `ρ ⊗ τ` placed in `ι'`. A Kraus map `K'` on `ι'` **lifts** a Kraus map
`K` on `ι` along `E` (`KrausMap.Lifts`) when it acts on every `liftMat E ρ τ` as `K` on `ρ`, leaving
`τ` alone; a circuit with reprogrammed queries lifts another (`ReprogrammedCircuit.Lifted`) when it
has the same shape, its Kraus maps lift the other's and its reprogrammed queries read the same
assignment lists. Then the runs agree on lifted states (`ReprogrammedCircuit.Lifted.run`).

This is the tool that compares the composition of an adversary followed by a query-free test
(`AdaptiveIAlg.withTest`) with the composition of the adversary: before the junction, the first
acts on its registers as the second, with the copy register as the extra factor.
-/

open Finset Matrix
open scoped BigOperators Kronecker ENNReal NNReal ComplexOrder

namespace GordieHowe.Quantum

section Lift

variable {ι ι' κ κ' Z : Type*}

/-- **The matrix `ρ ⊗ τ` placed in a register `ι'` split as `ι × Z` by `E`.** -/
def liftMat (E : ι' ≃ ι × Z) (ρ : Matrix ι ι ℂ) (τ : Matrix Z Z ℂ) : Matrix ι' ι' ℂ :=
  (ρ ⊗ₖ τ).submatrix E E

theorem liftMat_apply (E : ι' ≃ ι × Z) (ρ : Matrix ι ι ℂ) (τ : Matrix Z Z ℂ) (x y : ι') :
    liftMat E ρ τ x y = ρ (E x).1 (E y).1 * τ (E x).2 (E y).2 :=
  rfl

theorem liftMat_add_left (E : ι' ≃ ι × Z) (ρ σ : Matrix ι ι ℂ) (τ : Matrix Z Z ℂ) :
    liftMat E (ρ + σ) τ = liftMat E ρ τ + liftMat E σ τ := by
  ext x y
  simp [liftMat_apply, add_mul]

/-- A basis permutation of `ι'` that acts as `π` on the `ι` factor moves lifted matrices as `π`
moves the `ι` factor. -/
theorem liftMat_submatrix (E : ι' ≃ ι × Z) {π' : Equiv.Perm ι'} {π : Equiv.Perm ι}
    (h : ∀ x, E (π'.symm x) = (π.symm (E x).1, (E x).2)) (ρ : Matrix ι ι ℂ) (τ : Matrix Z Z ℂ) :
    (liftMat E ρ τ).submatrix π'.symm π'.symm = liftMat E (ρ.submatrix π.symm π.symm) τ := by
  ext x y
  simp only [submatrix_apply, liftMat_apply, h]

/-- **The block of a matrix on `ι'` at the `Z`-coordinates `z`, `z'`**, a matrix on `ι`. -/
def blockAt (E : ι' ≃ ι × Z) (M : Matrix ι' ι' ℂ) (z z' : Z) : Matrix ι ι ℂ :=
  Matrix.of fun q q' => M (E.symm (q, z)) (E.symm (q', z'))

@[simp] theorem blockAt_apply (E : ι' ≃ ι × Z) (M : Matrix ι' ι' ℂ) (z z' : Z) (q q' : ι) :
    blockAt E M z z' q q' = M (E.symm (q, z)) (E.symm (q', z')) :=
  rfl

/-- **`ι' × A` split as `ι × (Z × A)`** along `E : ι' ≃ ι × Z`. -/
def rightProd (E : ι' ≃ ι × Z) (A : Type*) : ι' × A ≃ ι × (Z × A) where
  toFun p := ((E p.1).1, ((E p.1).2, p.2))
  invFun q := (E.symm (q.1, q.2.1), q.2.2)
  left_inv p := by simp
  right_inv q := by simp

variable [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype κ] [DecidableEq κ]
  [Fintype κ'] [DecidableEq κ']

/-- **`ι' × A` split as `(ι × A) × Z`** along `E : ι' ≃ ι × Z`. -/
def liftProd (E : ι' ≃ ι × Z) (A : Type*) : ι' × A ≃ (ι × A) × Z where
  toFun p := (((E p.1).1, p.2), (E p.1).2)
  invFun q := (E.symm (q.1.1, q.2), q.1.2)
  left_inv p := by simp
  right_inv q := by simp

namespace KrausMap

variable {R R' : Type*} [Fintype R] [Fintype R']

/-- **`K'` lifts `K` along `E`**: on every matrix `ρ ⊗ τ` placed in `ι'` by `E`, `K'` acts as `K`
on `ρ` and leaves `τ` alone. -/
def Lifts (E : ι' ≃ ι × Z) (K' : KrausMap R' ι' ι') (K : KrausMap R ι ι) : Prop :=
  ∀ ρ τ, K' (liftMat E ρ τ) = liftMat E (K ρ) τ

/-- **`K ⊗ 1` lifts `K`.** -/
theorem lifts_reindex_tensorId [Fintype Z] [DecidableEq Z] (E : ι' ≃ ι × Z) (K : KrausMap R ι ι) :
    ((K.tensorId Z).reindex E.symm).Lifts E K := fun ρ τ => by
  rw [reindex_apply]
  have h : (liftMat E ρ τ).submatrix E.symm E.symm = ρ ⊗ₖ τ := by
    ext a b
    simp [liftMat]
  rw [h, tensorId_apply]
  rfl

theorem Lifts.congr_left {E : ι' ≃ ι × Z} {K₁' : KrausMap R' ι' ι'} {R'' : Type*} [Fintype R'']
    {K₂' : KrausMap R'' ι' ι'} {K : KrausMap R ι ι} (h : K₁'.Lifts E K)
    (heq : ∀ ρ, K₂' ρ = K₁' ρ) : K₂'.Lifts E K := fun ρ τ => by
  rw [heq, h]

theorem Lifts.congr_right {E : ι' ≃ ι × Z} {K' : KrausMap R' ι' ι'} {K₁ : KrausMap R ι ι}
    {R'' : Type*} [Fintype R''] {K₂ : KrausMap R'' ι ι} (h : K'.Lifts E K₁)
    (heq : ∀ ρ, K₁ ρ = K₂ ρ) : K'.Lifts E K₂ := fun ρ τ => by
  rw [h, heq]

theorem Lifts.ite {E : ι' ≃ ι × Z} {c : Prop} [Decidable c] {K₁' K₂' : KrausMap R' ι' ι'}
    {K₁ K₂ : KrausMap R ι ι} (h₁ : c → K₁'.Lifts E K₁) (h₂ : ¬ c → K₂'.Lifts E K₂) :
    (if c then K₁' else K₂').Lifts E (if c then K₁ else K₂) := by
  by_cases hc : c
  · simp only [if_pos hc]
    exact h₁ hc
  · simp only [if_neg hc]
    exact h₂ hc

theorem Lifts.embedIdx {E : ι' ≃ ι × Z} {K' : KrausMap R' ι' ι'} {K : KrausMap R ι ι}
    {R'' : Type*} [Fintype R''] (h : K'.Lifts E K) (f : R' ↪ R'') : (K'.embedIdx f).Lifts E K :=
  h.congr_left fun ρ => embedIdx_apply K' f ρ

theorem Lifts.comp {E : ι' ≃ ι × Z} {R₁ R₂ R₁' R₂' : Type*} [Fintype R₁] [Fintype R₂]
    [Fintype R₁'] [Fintype R₂'] {K₁' : KrausMap R₁' ι' ι'} {K₂' : KrausMap R₂' ι' ι'}
    {K₁ : KrausMap R₁ ι ι} {K₂ : KrausMap R₂ ι ι} (h₂ : K₂'.Lifts E K₂) (h₁ : K₁'.Lifts E K₁) :
    (K₂'.comp K₁').Lifts E (K₂.comp K₁) := fun ρ τ => by
  rw [comp_apply, comp_apply, h₁, h₂]

/-- **Lifting is carried along basis equivalences**: if `K'` lifts `K` along `E`, then `K'` moved
by `e'` lifts `K` moved by `e` along any `E₂` with `E₂ (e' x) = (e (E x).1, (E x).2)`. -/
theorem Lifts.reindex {E : ι' ≃ ι × Z} {K' : KrausMap R' ι' ι'} {K : KrausMap R ι ι}
    (h : K'.Lifts E K) {e' : ι' ≃ κ'} {e : ι ≃ κ} {E₂ : κ' ≃ κ × Z}
    (hE : ∀ x, E₂ (e' x) = (e (E x).1, (E x).2)) : (K'.reindex e').Lifts E₂ (K.reindex e) :=
  fun ρ τ => by
    have hE' : ∀ y, E₂ y = (e (E (e'.symm y)).1, (E (e'.symm y)).2) := fun y => by
      rw [← hE, Equiv.apply_symm_apply]
    rw [reindex_apply, reindex_apply]
    have h1 : (liftMat E₂ ρ τ).submatrix e' e' = liftMat E (ρ.submatrix e e) τ := by
      ext x y
      simp only [submatrix_apply, liftMat_apply, hE]
    rw [h1, h]
    ext x y
    simp only [submatrix_apply, liftMat_apply, hE', Equiv.symm_apply_apply]

/-- **The entries of `K ⊗ 1` on any matrix**: the block at `(a, b)` is `K` of the block. -/
theorem tensorId_apply_apply {A : Type*} [Fintype A] [DecidableEq A] (K : KrausMap R ι ι)
    (ρ : Matrix (ι × A) (ι × A) ℂ) (i j : ι) (a b : A) :
    (K.tensorId A) ρ (i, a) (j, b) = K (fun k l => ρ (k, a) (l, b)) i j := by
  simp only [apply, tensorId, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, mul_ite, ite_mul,
    Finset.sum_ite_eq, conjTranspose_apply]
  simp only [apply_ite (starRingEnd ℂ), map_zero, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  rfl

/-- **Lifting is carried through `⊗ 1`**, along any `E₂` that places the extra factor `A` next to
`ι` (`E₂ (x, a) = (((E x).1, a), (E x).2)`). -/
theorem Lifts.tensorId {E : ι' ≃ ι × Z} {K' : KrausMap R' ι' ι'} {K : KrausMap R ι ι}
    (h : K'.Lifts E K) (A : Type*) [Fintype A] [DecidableEq A] {E₂ : ι' × A ≃ (ι × A) × Z}
    (hE : ∀ x a, E₂ (x, a) = (((E x).1, a), (E x).2)) :
    (K'.tensorId A).Lifts E₂ (K.tensorId A) := fun ρ τ => by
  ext ⟨x, a⟩ ⟨y, b⟩
  rw [tensorId_apply_apply, liftMat_apply, hE, hE]
  have h1 : (fun k l => liftMat E₂ ρ τ (k, a) (l, b)) =
      liftMat E (fun k l => ρ (k, a) (l, b)) τ := by
    ext k l
    simp only [liftMat_apply, hE]
    rfl
  rw [h1, h (fun k l => ρ (k, a) (l, b)) τ, liftMat_apply, tensorId_apply_apply]

/-- **`K` followed by the projection onto `p`**: the projector on both sides of `K ρ`. -/
theorem restrict_apply_apply (K : KrausMap R ι ι) (p : ι → Bool) (ρ : Matrix ι ι ℂ) (i j : ι) :
    (K.restrict p) ρ i j = (if p i then 1 else 0) * K ρ i j * (if p j then 1 else 0) := by
  simp only [apply, restrict, Matrix.sum_apply, Matrix.conjTranspose_mul,
    Matrix.diagonal_conjTranspose]
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Matrix.mul_assoc, Matrix.diagonal_mul]
  simp only [← Matrix.mul_assoc]
  by_cases hj : p j <;> simp [hj, mul_comm]

theorem Lifts.restrict {E : ι' ≃ ι × Z} {K' : KrausMap R' ι' ι'} {K : KrausMap R ι ι}
    (h : K'.Lifts E K) {p' : ι' → Bool} {p : ι → Bool} (hp : ∀ x, p' x = p (E x).1) :
    (K'.restrict p').Lifts E (K.restrict p) := fun ρ τ => by
  ext x y
  rw [restrict_apply_apply, h, liftMat_apply, liftMat_apply, restrict_apply_apply, hp, hp]
  ring

theorem Lifts.permConj {E : ι' ≃ ι × Z} {K' : KrausMap R' ι' ι'} {K : KrausMap R ι ι}
    (h : K'.Lifts E K) {σ' τ' : Equiv.Perm ι'} {σ τ : Equiv.Perm ι}
    (hσ : ∀ x, E (σ'.symm x) = (σ.symm (E x).1, (E x).2))
    (hτ : ∀ x, E (τ'.symm x) = (τ.symm (E x).1, (E x).2)) :
    (K'.permConj σ' τ').Lifts E (K.permConj σ τ) := fun ρ τ₀ => by
  rw [permConj_apply, permConj_apply, liftMat_submatrix E hσ, h, liftMat_submatrix E hτ]

/-- **A Kraus map is additive over finite sums.** -/
theorem apply_sum {α : Type*} (K : KrausMap R ι ι) (s : Finset α) (M : α → Matrix ι ι ℂ) :
    K (∑ a ∈ s, M a) = ∑ a ∈ s, K (M a) := by
  simp only [apply, Matrix.mul_sum, Matrix.sum_mul]
  exact Finset.sum_comm

/-- **The entries of a lifting map on any matrix**: the entry at `(x, y)` is `K` of the block of
`M` at the `Z`-coordinates of `x` and `y`. -/
theorem Lifts.apply_apply [Fintype Z] [DecidableEq Z] {E : ι' ≃ ι × Z} {K' : KrausMap R' ι' ι'} {K : KrausMap R ι ι}
    (h : K'.Lifts E K) (M : Matrix ι' ι' ℂ) (x y : ι') :
    K' M x y = K (blockAt E M (E x).2 (E y).2) (E x).1 (E y).1 := by
  have hM : M = ∑ z, ∑ z', liftMat E (blockAt E M z z') (Matrix.single z z' 1) := by
    ext a b
    simp only [Matrix.sum_apply, liftMat_apply, Matrix.single_apply, Quantum.blockAt_apply]
    rw [Finset.sum_eq_single (E a).2 (fun z _ hz => by simp [hz]) (by simp),
      Finset.sum_eq_single (E b).2 (fun z _ hz => by simp [hz]) (by simp)]
    simp
  have h' : ∀ ρ τ, K' (liftMat E ρ τ) = liftMat E (K ρ) τ := h
  conv_lhs => rw [hM]
  simp only [apply_sum, h', Matrix.sum_apply, liftMat_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single (E x).2 (fun z _ hz => by simp [hz]) (by simp),
    Finset.sum_eq_single (E y).2 (fun z _ hz => by simp [hz]) (by simp)]
  simp

/-- **Two maps lifting the same map along the same split agree on every matrix.** -/
theorem Lifts.apply_eq [Fintype Z] [DecidableEq Z] {E : ι' ≃ ι × Z} {R'' : Type*} [Fintype R''] {K₁' : KrausMap R' ι' ι'}
    {K₂' : KrausMap R'' ι' ι'} {K : KrausMap R ι ι} (h₁ : K₁'.Lifts E K) (h₂ : K₂'.Lifts E K)
    (M : Matrix ι' ι' ℂ) : K₁' M = K₂' M := by
  ext x y
  rw [h₁.apply_apply, h₂.apply_apply]

/-- **A lifting map tensored with an identity lifts the same map**, the extra factor joining
`Z`: along `E₂ (x, a) = ((E x).1, ((E x).2, a))`. -/
theorem Lifts.tensorId_right {E : ι' ≃ ι × Z} {K' : KrausMap R' ι' ι'} {K : KrausMap R ι ι}
    (h : K'.Lifts E K) (A : Type*) [Fintype A] [DecidableEq A] {E₂ : ι' × A ≃ ι × (Z × A)}
    (hE : ∀ x a, E₂ (x, a) = ((E x).1, ((E x).2, a))) : (K'.tensorId A).Lifts E₂ K :=
  fun ρ τ => by
    ext ⟨x, a⟩ ⟨y, b⟩
    rw [tensorId_apply_apply, liftMat_apply, hE, hE]
    have h1 : (fun k l => liftMat E₂ ρ τ (k, a) (l, b)) =
        liftMat E ρ (Matrix.of fun z z' => τ (z, a) (z', b)) := by
      ext k l
      simp only [liftMat_apply, hE]
      rfl
    have h' : ∀ ρ τ, K' (liftMat E ρ τ) = liftMat E (K ρ) τ := h
    rw [h1, h', liftMat_apply]
    rfl

/-- **Lifting is carried along a basis equivalence of the larger register.** -/
theorem Lifts.reindex_left {E : ι' ≃ ι × Z} {K' : KrausMap R' ι' ι'} {K : KrausMap R ι ι}
    (h : K'.Lifts E K) {e' : ι' ≃ κ'} {E₂ : κ' ≃ ι × Z} (hE : ∀ x, E₂ (e' x) = E x) :
    (K'.reindex e').Lifts E₂ K := fun ρ τ => by
  have hE' : ∀ y, E₂ y = E (e'.symm y) := fun y => by rw [← hE, Equiv.apply_symm_apply]
  have h' : ∀ ρ τ, K' (liftMat E ρ τ) = liftMat E (K ρ) τ := h
  rw [reindex_apply]
  have h1 : (liftMat E₂ ρ τ).submatrix e' e' = liftMat E ρ τ := by
    ext x y
    simp only [submatrix_apply, liftMat_apply, hE]
  rw [h1, h']
  ext x y
  simp only [submatrix_apply, liftMat_apply, hE']

theorem lifts_ofPerm (E : ι' ≃ ι × Z) {π' : Equiv.Perm ι'} {π : Equiv.Perm ι}
    (h : ∀ x, E (π'.symm x) = (π.symm (E x).1, (E x).2)) :
    (KrausMap.ofPerm π').Lifts E (KrausMap.ofPerm π) := fun ρ τ => by
  rw [ofPerm_apply, ofPerm_apply, liftMat_submatrix E h]

theorem lifts_measureFn (E : ι' ≃ ι × Z) {M : Type*} [Fintype M] [DecidableEq M] {f' : ι' → M}
    {f : ι → M} (h : ∀ x, f' x = f (E x).1) :
    (KrausMap.measureFn f').Lifts E (KrausMap.measureFn f) := fun ρ τ => by
  rw [measureFn_apply, measureFn_apply]
  ext x y
  simp only [dephase, liftMat_apply, h]
  split_ifs <;> simp

end KrausMap

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype κ] [DecidableEq κ]
  [Fintype κ'] [DecidableEq κ'] in
/-- A permutation's inverse acts as the inverse of its factor when the permutation does. -/
theorem perm_symm_lift (E : ι' ≃ ι × Z) {π' : Equiv.Perm ι'} {π : Equiv.Perm ι}
    (h : ∀ x, E (π' x) = (π (E x).1, (E x).2)) (x : ι') :
    E (π'.symm x) = (π.symm (E x).1, (E x).2) := by
  have := h (π'.symm x)
  rw [Equiv.apply_symm_apply] at this
  rw [this]
  simp

end Lift

/-! ### Lifted circuits with reprogrammed queries -/

namespace ReprogrammedCircuit

variable {V V' X Y Z : Type} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The query register over `V'` split along `E : V' ≃ V × Z`. -/
def liftEquiv (E : V' ≃ V × Z) : QueryReg V' 1 X Y ≃ QueryReg V 1 X Y × Z where
  toFun p := (((E p.1).1, p.2), (E p.1).2)
  invFun q := (E.symm (q.1.1, q.2), q.1.2)
  left_inv p := by simp
  right_inv q := by simp

/-- **A circuit lifting another along `E`**: the same shape, each Kraus map lifting the other's
(`KrausMap.Lifts`), and each reprogrammed query reading the other's assignment list on the `V`
factor. -/
def Lifted (E : V' ≃ V × Z) : ReprogrammedCircuit V' X Y → ReprogrammedCircuit V X Y → Prop
  | nil, nil => True
  | kraus K' c', kraus K c => K'.Lifts (liftEquiv E) K ∧ Lifted E c' c
  | rquery a' c', rquery a c => (∀ v, a' v = a (E v).1) ∧ Lifted E c' c
  | _, _ => False

theorem lifted_nil {E : V' ≃ V × Z} : Lifted E (.nil : ReprogrammedCircuit V' X Y) .nil :=
  trivial

theorem lifted_kraus {E : V' ≃ V × Z} {R R' : Type} [Fintype R] [Fintype R']
    {K' : KrausMap R' (QueryReg V' 1 X Y) (QueryReg V' 1 X Y)}
    {K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)} {c' : ReprogrammedCircuit V' X Y}
    {c : ReprogrammedCircuit V X Y} (hK : K'.Lifts (liftEquiv E) K) (hc : Lifted E c' c) :
    Lifted E (.kraus K' c') (.kraus K c) :=
  ⟨hK, hc⟩

theorem lifted_rquery {E : V' ≃ V × Z} {a' : V' → List (Assignment X Y)}
    {a : V → List (Assignment X Y)} {c' : ReprogrammedCircuit V' X Y}
    {c : ReprogrammedCircuit V X Y} (ha : ∀ v, a' v = a (E v).1) (hc : Lifted E c' c) :
    Lifted E (.rquery a' c') (.rquery a c) :=
  ⟨ha, hc⟩

theorem Lifted.append {E : V' ≃ V × Z} : ∀ {c' : ReprogrammedCircuit V' X Y}
    {c : ReprogrammedCircuit V X Y} {d' d}, Lifted E c' c → Lifted E d' d →
    Lifted E (c' ++ d') (c ++ d)
  | nil, nil, _, _, _, hd => hd
  | kraus _ c', kraus _ _, _, _, ⟨hK, hc⟩, hd => ⟨hK, Lifted.append (c' := c') hc hd⟩
  | rquery _ c', rquery _ _, _, _, ⟨ha, hc⟩, hd => ⟨ha, Lifted.append (c' := c') hc hd⟩
  | nil, kraus _ _, _, _, h, _ => h.elim
  | nil, rquery _ _, _, _, h, _ => h.elim
  | kraus _ _, nil, _, _, h, _ => h.elim
  | kraus _ _, rquery _ _, _, _, h, _ => h.elim
  | rquery _ _, nil, _, _, h, _ => h.elim
  | rquery _ _, kraus _ _, _, _, h, _ => h.elim

theorem Lifted.concat_map {E : V' ≃ V × Z} {α : Type*} {f' : α → ReprogrammedCircuit V' X Y}
    {f : α → ReprogrammedCircuit V X Y} (h : ∀ a, Lifted E (f' a) (f a)) :
    ∀ l : List α, Lifted E (concat (l.map f')) (concat (l.map f))
  | [] => trivial
  | a :: l => (h a).append (Lifted.concat_map h l)

variable [AddGroup Y]

/-- **Lifted circuits have lifted runs.** -/
theorem Lifted.run {E : V' ≃ V × Z} (H : X → Y) : ∀ {c' : ReprogrammedCircuit V' X Y}
    {c : ReprogrammedCircuit V X Y}, Lifted E c' c → ∀ ρ τ,
    c'.run H (liftMat (liftEquiv E) ρ τ) = liftMat (liftEquiv E) (c.run H ρ) τ
  | nil, nil, _, _, _ => rfl
  | kraus K' c', kraus K c, ⟨hK, hc⟩, ρ, τ => by
    rw [ReprogrammedCircuit.run, ReprogrammedCircuit.run, hK, hc.run H]
  | rquery a' c', rquery a c, ⟨ha, hc⟩, ρ, τ => by
    rw [ReprogrammedCircuit.run, ReprogrammedCircuit.run, liftMat_submatrix _
      (perm_symm_lift _ fun x => ?_), hc.run H]
    obtain ⟨v, qp⟩ := x
    simp [liftEquiv, ha]
  | nil, kraus _ _, h, _, _ => h.elim
  | nil, rquery _ _, h, _, _ => h.elim
  | kraus _ _, nil, h, _, _ => h.elim
  | kraus _ _, rquery _ _, h, _, _ => h.elim
  | rquery _ _, nil, h, _, _ => h.elim
  | rquery _ _, kraus _ _, h, _, _ => h.elim

end ReprogrammedCircuit

/-! ### Diagonal sums -/

section Diag

variable {ι ι' Z : Type*} [Fintype ι] [Fintype ι'] [Fintype Z]

/-- **A diagonal sum over a lifted state factors**, when the `Z` factor is a positive semidefinite
matrix of trace `1` with real diagonal: summing an event of the `ι` coordinate over the diagonal of
`ρ ⊗ τ` gives its sum over the diagonal of `ρ`. -/
theorem sum_liftMat_diag (E : ι' ≃ ι × Z) {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef)
    {τ : Matrix Z Z ℂ} (hτ : τ.PosSemidef) (htr : τ.trace = 1) (g : ι → ℝ≥0∞) :
    ∑ x, g (E x).1 * ENNReal.ofReal (liftMat E ρ τ x x).re = ∑ q, g q * ENNReal.ofReal (ρ q q).re := by
  rw [← E.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hρq : 0 ≤ (ρ q q).re := (Complex.nonneg_iff.1 (hρ.diag_nonneg (i := q))).1
  have hτr : ∀ z, (τ z z).im = 0 := fun z => (Complex.nonneg_iff.1 (hτ.diag_nonneg (i := z))).2.symm
  have hτz : ∀ z, 0 ≤ (τ z z).re := fun z => (Complex.nonneg_iff.1 (hτ.diag_nonneg (i := z))).1
  have h1 : ∀ z, (liftMat E ρ τ (E.symm (q, z)) (E.symm (q, z))).re = (ρ q q).re * (τ z z).re :=
    fun z => by simp [liftMat_apply, Complex.mul_re, hτr]
  simp only [Equiv.apply_symm_apply, h1, ENNReal.ofReal_mul hρq, ← Finset.mul_sum]
  rw [← ENNReal.ofReal_sum_of_nonneg fun z _ => hτz z]
  have h2 : ∑ z, (τ z z).re = 1 := by
    have := congrArg Complex.re htr
    rw [Matrix.trace, Complex.re_sum] at this
    simpa using this
  rw [h2, ENNReal.ofReal_one, mul_one]

end Diag

/-- **Positivity is kept by the run of a circuit with reprogrammed queries.** -/
theorem ReprogrammedCircuit.posSemidef_run {V X Y : Type} [Fintype V] [DecidableEq V] [Fintype X]
    [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddGroup Y] (H : X → Y)
    (c : ReprogrammedCircuit V X Y) {ρ : Matrix (QueryReg V 1 X Y) (QueryReg V 1 X Y) ℂ}
    (hρ : ρ.PosSemidef) : (c.run H ρ).PosSemidef := by
  induction c generalizing ρ with
  | nil => exact hρ
  | kraus K c ih => exact ih (K.posSemidef_apply hρ)
  | rquery a c ih => exact ih (hρ.submatrix _)

/-- **The part of a lifted matrix on a set read from the `ι` coordinate** is the lift of the part
of the matrix. -/
theorem cutTo_liftMat {ι ι' Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (E : ι' ≃ ι × Z) {S : Set ι'} {S' : Set ι} (hS : ∀ x, x ∈ S ↔ (E x).1 ∈ S')
    (ρ : Matrix ι ι ℂ) (τ : Matrix Z Z ℂ) :
    cutTo S (liftMat E ρ τ) = liftMat E (cutTo S' ρ) τ := by
  classical
  ext x y
  simp only [cutTo, liftMat_apply, hS]
  split_ifs <;> simp

/-- **The block of a part on a set read from the `ι` coordinate** is the part of the block. -/
theorem blockAt_cutTo {ι ι' Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (E : ι' ≃ ι × Z) {S : Set ι'} {S' : Set ι} (hS : ∀ x, x ∈ S ↔ (E x).1 ∈ S')
    (ρ : Matrix ι' ι' ℂ) (z z' : Z) :
    blockAt E (cutTo S ρ) z z' = cutTo S' (blockAt E ρ z z') := by
  classical
  ext q q'
  simp only [blockAt_apply, cutTo, hS, Equiv.apply_symm_apply]

/-- **The part of a positive semidefinite matrix on a set is positive semidefinite.** -/
theorem posSemidef_cutTo {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Set ι) {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) : (cutTo S ρ).PosSemidef := by
  rw [cutTo_eq]
  have := hρ.mul_mul_conjTranspose_same (projOn S)
  rwa [projOn_conjTranspose] at this

end GordieHowe.Quantum
