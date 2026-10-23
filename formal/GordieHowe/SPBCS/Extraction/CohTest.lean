-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.DensityRunExpand
public import GordieHowe.Model.Quantum.Interactive.TPRun
public import GordieHowe.Model.Quantum.Interactive.QueryFreeTest

@[expose] public section

/-!
# Test absorption at the coherent database extractor: the density-matrix machinery

The model-independent part of the implication to Unruh's Definition 14 for tests that make no oracle
queries (the paper's Section 6.1.2, Weak online simulation extractability): for a trace-preserving
adversary `A` and a query-free test `Π` of its residual state, the density-matrix run of the
coherent database extractor on the adversary followed by the test (`A^Π`) is, blockwise along the
copy register, the test applied to the run on `A` cut to the outputs (route 3′). Each compiler
states Unruh's Extract with the test at its own extractor from these lemmas: the spBCS
compiler (`GordieHowe/SPBCS/SimExtractUnruh.lean`).

## Route 3′

Tracing the ancilla of the purification out of the compressed-oracle simulation gives the
density-matrix run of the Kraus maps (`reduce_simStage_expandAdv_toQueryAlgCoh`,
`GordieHowe/Model/QROM/DensityRunExpand.lean`); for trace-preserving maps the halting flag stays `false`
(`densityRun_expandCoh_eq_liftMat`). Before the junction the maps of `A^Π`'s composition lift those
of `A`'s along the copy register (`AdaptiveIAlg.testFold`, an `Alg.TestFold`), so the run of `A^Π` is
the run of `A` with a blank copy (`densityRun_expKraus_liftMat`). At the junction the block of `A^Π`'s
state at copy value `c` is the test applied to `A`'s state cut to the outputs with representative `c`
(`blockAt_composeTP_last`). After it, the expansion's steps and the simulated queries act on the
registers the test leaves alone and read no register the test changes, so the block relation is
carried to the end of the run (`blockAt_densityRun_expKraus`); summing the blocks over the copy values
is summing over the outputs (`AdaptiveIAlg.sum_repIs`).
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.Quantum

section BlockConj

variable {ι ι' Z : Type*} [Fintype ι] [Fintype ι'] [Fintype Z] [DecidableEq Z]

/-- **Conjugation by a block-diagonal matrix, blockwise**: if `G'` is block diagonal along `E`
with block `G z` at `z`, the block at `(z, z')` of `G' M G'ᴴ` is `G z` times the block of `M`
times `(G z')ᴴ`. -/
theorem blockAt_conj (E : ι' ≃ ι × Z) {G' : Matrix ι' ι' ℂ} (G : Z → Matrix ι ι ℂ)
    (hG : ∀ x' z' x z, G' (E.symm (x', z')) (E.symm (x, z)) = if z' = z then G z x' x else 0)
    (M : Matrix ι' ι' ℂ) (z z' : Z) :
    blockAt E (G' * M * G'ᴴ) z z' = G z * blockAt E M z z' * (G z')ᴴ := by
  ext q q'
  simp only [blockAt_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← E.symm.sum_comp, Fintype.sum_prod_type]
  simp_rw [← E.symm.sum_comp (fun a => G' _ a * M a _), Fintype.sum_prod_type, hG]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, apply_ite star,
    star_zero, mul_ite, mul_zero]

omit [Fintype ι] [Fintype ι'] [Fintype Z] [DecidableEq Z] in
theorem blockAt_liftMat (E : ι' ≃ ι × Z) (ρ : Matrix ι ι ℂ) (τ : Matrix Z Z ℂ) (z z' : Z) :
    blockAt E (liftMat E ρ τ) z z' = τ z z' • ρ := by
  ext q q'
  simp [liftMat_apply, mul_comm]

/-- **A lifting map acts blockwise.** -/
theorem KrausMap.Lifts.blockAt_apply {R R' : Type*} [Fintype R] [Fintype R'] [DecidableEq ι]
    [DecidableEq ι'] {E : ι' ≃ ι × Z} {K' : KrausMap R' ι' ι'} {K : KrausMap R ι ι}
    (h : K'.Lifts E K) (M : Matrix ι' ι' ℂ) (z z' : Z) :
    blockAt E (K' M) z z' = K (blockAt E M z z') := by
  ext q q'
  rw [GordieHowe.Quantum.blockAt_apply, h.apply_apply]
  simp

omit [Fintype ι] [Fintype ι'] [Fintype Z] [DecidableEq Z] in
/-- **Matrices with the same blocks are equal.** -/
theorem blockAt_ext (E : ι' ≃ ι × Z) {M₁ M₂ : Matrix ι' ι' ℂ}
    (h : ∀ z z', blockAt E M₁ z z' = blockAt E M₂ z z') : M₁ = M₂ := by
  ext x y
  have := congrFun (congrFun (h (E x).2 (E y).2) (E x).1) (E y).1
  simpa using this

/-- **A block-diagonal conjugation of a lifted matrix** is the lift of the conjugation by the
common block. -/
theorem conj_liftMat (E : ι' ≃ ι × Z) {G' : Matrix ι' ι' ℂ} (G : Matrix ι ι ℂ)
    (hG : ∀ x' z' x z, G' (E.symm (x', z')) (E.symm (x, z)) = if z' = z then G x' x else 0)
    (M : Matrix ι ι ℂ) (τ : Matrix Z Z ℂ) :
    G' * liftMat E M τ * G'ᴴ = liftMat E (G * M * Gᴴ) τ := by
  refine blockAt_ext E fun z z' => ?_
  rw [blockAt_conj E (fun _ => G) hG, blockAt_liftMat, blockAt_liftMat, Matrix.mul_smul,
    Matrix.smul_mul]

omit [Fintype ι] [Fintype ι'] [Fintype Z] [DecidableEq Z] in
/-- **A basis permutation that keeps the `Z` coordinate, blockwise**: if `π'` acts at `z` as
`π z`, the block of the permuted matrix is the permuted block. -/
theorem blockAt_submatrix_perm (E : ι' ≃ ι × Z) {π' : Equiv.Perm ι'} (π : Z → Equiv.Perm ι)
    (h : ∀ x z, π'.symm (E.symm (x, z)) = E.symm ((π z).symm x, z)) (M : Matrix ι' ι' ℂ)
    (z z' : Z) :
    blockAt E (M.submatrix π'.symm π'.symm) z z' =
      (blockAt E M z z').submatrix (π z).symm (π z').symm := by
  ext q q'
  simp [h]

end BlockConj

namespace KrausMap

variable {R R' ι ι' Z : Type*} [Fintype R] [Fintype R'] [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι']

/-- **`K'` acts as `K` on the matrices `ρ ⊗ τ` at one `τ`** (the matrices with the `Z` factor in
the state `τ`). -/
def LiftsAt (E : ι' ≃ ι × Z) (τ : Matrix Z Z ℂ) (K' : KrausMap R' ι' ι') (K : KrausMap R ι ι) :
    Prop :=
  ∀ ρ, K' (liftMat E ρ τ) = liftMat E (K ρ) τ

theorem Lifts.liftsAt {E : ι' ≃ ι × Z} {K' : KrausMap R' ι' ι'} {K : KrausMap R ι ι}
    (h : K'.Lifts E K) (τ : Matrix Z Z ℂ) : K'.LiftsAt E τ K := fun ρ => h ρ τ

/-- **Lifting at one `τ` is carried through `⊗ 1`.** -/
theorem LiftsAt.tensorId {E : ι' ≃ ι × Z} {τ : Matrix Z Z ℂ} {K' : KrausMap R' ι' ι'}
    {K : KrausMap R ι ι} (h : K'.LiftsAt E τ K) (A : Type*) [Fintype A] [DecidableEq A]
    {E₂ : ι' × A ≃ (ι × A) × Z} (hE : ∀ x a, E₂ (x, a) = (((E x).1, a), (E x).2)) :
    (K'.tensorId A).LiftsAt E₂ τ (K.tensorId A) := fun ρ => by
  ext ⟨x, a⟩ ⟨y, b⟩
  rw [tensorId_apply_apply, liftMat_apply, hE, hE]
  have h1 : (fun k l => liftMat E₂ ρ τ (k, a) (l, b)) =
      liftMat E (fun k l => ρ (k, a) (l, b)) τ := by
    ext k l
    simp only [liftMat_apply, hE]
    rfl
  rw [h1, h (fun k l => ρ (k, a) (l, b)), liftMat_apply, tensorId_apply_apply]

end KrausMap

end GordieHowe.Quantum

namespace GordieHowe.QROM

open GordieHowe.Quantum

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {B : Type} (e : BitStr I J ≃ B)

section DensityLift

variable {V V' Z R R' : Type} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
  [Fintype Z] [DecidableEq Z] [Fintype R] [Fintype R'] {t : ℕ}

/-- **The simulated query of a lifted matrix** is the lift of the simulated query: CMS19's query
acts on the query register and the database, never on a factor of the work register. -/
theorem simQuery_conj_liftMat (σ : V' ≃ V × Z) (M : Matrix (SimRegister V I J m t)
    (SimRegister V I J m t) ℂ) (τ : Matrix Z Z ℂ) :
    Matrix.of (simQueryKernel e V' t) * liftMat (simAncSplit σ) M τ *
        (Matrix.of (simQueryKernel e V' t))ᴴ =
      liftMat (simAncSplit σ) (Matrix.of (simQueryKernel e V t) * M *
        (Matrix.of (simQueryKernel e V t))ᴴ) τ :=
  conj_liftMat (simAncSplit σ) _ (fun x' z' x z => by
    rw [Matrix.of_apply, simQueryKernel_simAncSplit e σ (x', z') (x, z)]
    rfl) M τ

/-- **The simulated query of a matrix, blockwise along a split of the work register.** -/
theorem blockAt_simQuery_conj (σ : V' ≃ V × Z) (M : Matrix (SimRegister V' I J m t)
    (SimRegister V' I J m t) ℂ) (z z' : Z) :
    blockAt (simAncSplit σ) (Matrix.of (simQueryKernel e V' t) * M *
        (Matrix.of (simQueryKernel e V' t))ᴴ) z z' =
      Matrix.of (simQueryKernel e V t) * blockAt (simAncSplit σ) M z z' *
        (Matrix.of (simQueryKernel e V t))ᴴ :=
  blockAt_conj (simAncSplit σ) (fun _ => Matrix.of (simQueryKernel e V t)) (fun x' z' x z => by
    rw [Matrix.of_apply, simQueryKernel_simAncSplit e σ (x', z') (x, z)]
    rfl) M z z'

omit [DecidableEq I] [DecidableEq J] [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
  [Fintype Z] [DecidableEq Z] in
/-- The initial matrix of the run, lifted. -/
theorem liftMat_kronecker_empty (σ : V' ≃ V × Z)
    (ρ₀ : Matrix (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J)) ℂ)
    (τ : Matrix Z Z ℂ) :
    liftMat (QueryAlg.queryAncSplit σ) ρ₀ τ ⊗ₖ
        Matrix.single (dbSlots e t (∅ : DB (Bits m) B)) (dbSlots e t (∅ : DB (Bits m) B)) 1 =
      liftMat (simAncSplit σ) (ρ₀ ⊗ₖ
        Matrix.single (dbSlots e t (∅ : DB (Bits m) B)) (dbSlots e t (∅ : DB (Bits m) B)) 1) τ := by
  ext ⟨x, a⟩ ⟨y, b⟩
  simp only [liftMat_apply, kroneckerMap_apply, simAncSplit, ctrlSplit_apply,
    QueryAlg.queryAncSplit_apply]
  ring

omit [Fintype Z] [DecidableEq Z] in
/-- **A step of the run on a lifted matrix**, when the Kraus map lifts at `τ`. -/
theorem stepAt_tensorId_liftMat (σ : V' ≃ V × Z) (τ : Matrix Z Z ℂ)
    (K : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J)))
    (K' : Fin (t + 1) → KrausMap R' (QueryReg V' 1 (Bits m) (BitStr I J))
      (QueryReg V' 1 (Bits m) (BitStr I J))) {j : ℕ}
    (hK : ∀ i : Fin (t + 1), (i : ℕ) = j → (K' i).LiftsAt (QueryAlg.queryAncSplit σ) τ (K i))
    (M : Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ) :
    KrausMap.stepAt (fun k => (K' k).tensorId (Slots I J m t)) j (liftMat (simAncSplit σ) M τ) =
      liftMat (simAncSplit σ) (KrausMap.stepAt (fun k => (K k).tensorId (Slots I J m t)) j M) τ := by
  unfold KrausMap.stepAt
  split_ifs with h
  · exact (hK ⟨j, h⟩ rfl).tensorId (Slots I J m t) (fun _ _ => rfl) M
  · rfl

/-- **The run of maps that lift the first `n` maps at `τ`**, from a lifted initial state, is the
lifted run, up to step `n - 1`. -/
theorem densityRun_liftMat (σ : V' ≃ V × Z) (τ : Matrix Z Z ℂ)
    (K : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J)))
    (K' : Fin (t + 1) → KrausMap R' (QueryReg V' 1 (Bits m) (BitStr I J))
      (QueryReg V' 1 (Bits m) (BitStr I J))) {n : ℕ}
    (hK : ∀ i : Fin (t + 1), (i : ℕ) < n → (K' i).LiftsAt (QueryAlg.queryAncSplit σ) τ (K i))
    (ρ₀ : Matrix (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J)) ℂ) :
    ∀ k < n, densityRun e K' (liftMat (QueryAlg.queryAncSplit σ) ρ₀ τ) k =
      liftMat (simAncSplit σ) (densityRun e K ρ₀ k) τ
  | 0, h0 => by
    simp only [densityRun]
    rw [liftMat_kronecker_empty]
    exact stepAt_tensorId_liftMat σ τ K K' (fun i hi => hK i (hi ▸ h0)) _
  | k + 1, hk => by
    simp only [densityRun]
    rw [densityRun_liftMat σ τ K K' hK ρ₀ k (by omega), simQuery_conj_liftMat]
    exact stepAt_tensorId_liftMat σ τ K K' (fun i hi => hK i (hi ▸ hk)) _

/-- **The block of the run after a junction** (route 3′, the step of test absorption): let the
maps `K'` lift `K` at `τ` before step `n`; at step `n`, the block at `(c, c)` of `K' n` on a lifted
matrix is `F` of `K n` on the matrix; and after it the steps and the simulated queries carry the
relation `blockAt M' c c = F M`. Then from step `n` on, the block at `(c, c)` of the run of `K'`
from a lifted initial state is `F` of the run of `K`. -/
theorem densityRun_blockAt (σ : V' ≃ V × Z) (τ : Matrix Z Z ℂ)
    (K : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J)))
    (K' : Fin (t + 1) → KrausMap R' (QueryReg V' 1 (Bits m) (BitStr I J))
      (QueryReg V' 1 (Bits m) (BitStr I J))) {n : ℕ}
    (hK : ∀ i : Fin (t + 1), (i : ℕ) < n → (K' i).LiftsAt (QueryAlg.queryAncSplit σ) τ (K i))
    (c : Z) (F : Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ →
      Matrix (SimRegister V I J m t) (SimRegister V I J m t) ℂ)
    (hjunc : ∀ M, blockAt (simAncSplit σ) (KrausMap.stepAt (fun k => (K' k).tensorId
        (Slots I J m t)) n (liftMat (simAncSplit σ) M τ)) c c =
      F (KrausMap.stepAt (fun k => (K k).tensorId (Slots I J m t)) n M))
    (hpost : ∀ j, n < j → ∀ M' M, blockAt (simAncSplit σ) M' c c = F M →
      blockAt (simAncSplit σ) (KrausMap.stepAt (fun k => (K' k).tensorId (Slots I J m t)) j M')
          c c =
        F (KrausMap.stepAt (fun k => (K k).tensorId (Slots I J m t)) j M))
    (hquery : ∀ M' M, blockAt (simAncSplit σ) M' c c = F M →
      blockAt (simAncSplit σ) (Matrix.of (simQueryKernel e V' t) * M' *
          (Matrix.of (simQueryKernel e V' t))ᴴ) c c =
        F (Matrix.of (simQueryKernel e V t) * M * (Matrix.of (simQueryKernel e V t))ᴴ))
    (ρ₀ : Matrix (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J)) ℂ)
    (k : ℕ) (hk : n ≤ k) :
    blockAt (simAncSplit σ) (densityRun e K' (liftMat (QueryAlg.queryAncSplit σ) ρ₀ τ) k) c c =
      F (densityRun e K ρ₀ k) := by
  induction k, hk using Nat.le_induction with
  | base =>
    cases n with
    | zero =>
      simp only [densityRun]
      rw [liftMat_kronecker_empty]
      exact hjunc _
    | succ n =>
      simp only [densityRun]
      rw [densityRun_liftMat e σ τ K K' (fun i hi => hK i (by omega)) ρ₀ n (by omega),
        simQuery_conj_liftMat]
      exact hjunc _
  | succ k hk ih =>
    simp only [densityRun]
    exact hpost (k + 1) (by omega) _ _ (hquery _ _ ih)

end DensityLift

end GordieHowe.QROM


namespace GordieHowe.Quantum

namespace KrausMap

variable {R R' ι : Type*} [Fintype R] [Fintype R'] [Fintype ι] [DecidableEq ι]

theorem sum_embedIdx (K : KrausMap R ι ι) (f : R ↪ R') :
    ∑ r', ((K.embedIdx f).op r')ᴴ * (K.embedIdx f).op r' = ∑ r, (K.op r)ᴴ * K.op r := by
  classical
  have hop : ∀ r, (K.embedIdx f).op (f r) = K.op r := fun r => by
    change (if h : ∃ r₀, f r₀ = f r then K.op h.choose else 0) = K.op r
    rw [dif_pos ⟨r, rfl⟩]
    congr 1
    exact f.injective (Exists.choose_spec (⟨r, rfl⟩ : ∃ r₀, f r₀ = f r))
  have hzero : ∀ r', r' ∉ univ.map f → (K.embedIdx f).op r' = 0 := fun r' hr' => by
    change (if h : ∃ r, f r = r' then K.op h.choose else 0) = 0
    rw [dif_neg fun ⟨r, hr⟩ => hr' (Finset.mem_map.2 ⟨r, Finset.mem_univ _, hr⟩)]
  rw [← Finset.sum_subset (Finset.subset_univ (univ.map f)) fun r' _ hr' => by
    rw [hzero r' hr']
    simp, Finset.sum_map]
  exact Finset.sum_congr rfl fun r _ => by rw [hop r]

theorem sum_tensorId (K : KrausMap R ι ι) (A : Type*) [Fintype A] [DecidableEq A] :
    ∑ r, ((K.tensorId A).op r)ᴴ * (K.tensorId A).op r =
      (∑ r, (K.op r)ᴴ * K.op r) ⊗ₖ (1 : Matrix A A ℂ) := by
  rw [sum_kronecker]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [tensorId]
  rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul]

theorem sum_reindex {κ : Type*} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (K : KrausMap R ι ι) :
    ∑ r, ((K.reindex e).op r)ᴴ * (K.reindex e).op r =
      (∑ r, (K.op r)ᴴ * K.op r).submatrix e.symm e.symm := by
  rw [submatrix_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [reindex]
  rw [conjTranspose_submatrix, submatrix_mul_equiv]

/-- **A trace-preserving map tensored with an identity and moved along a basis equivalence is
trace preserving.** -/
theorem sum_tensorId_reindex_eq_one (K : KrausMap R ι ι) (hK : ∑ r, (K.op r)ᴴ * K.op r = 1)
    {A κ : Type*} [Fintype A] [DecidableEq A] [Fintype κ] [DecidableEq κ] (e : ι × A ≃ κ) :
    ∑ r, (((K.tensorId A).reindex e).op r)ᴴ * ((K.tensorId A).reindex e).op r = 1 := by
  rw [sum_reindex, sum_tensorId, hK, one_kronecker_one, submatrix_one_equiv]

end KrausMap

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]

/-- **The trace-preserving form's step when the adversary's Kraus map does not halt**: the
adversary's map within the budget with the counter advanced, plus the map over the budget moved to
the ended value, at a slot; the adversary's map with the counter, after the slots. -/
theorem toTPKindAlg_step_apply (B : AdaptiveIAlg X Y Req Resp O) (k : StepIdx B.slots B.post)
    (h : (B.step k).haltOp = 0) (ρ : Matrix B.CReg B.CReg ℂ) :
    B.toTPKindAlg.step k ρ = if (k : ℕ) < B.slots then
        ((B.cntKraus k).restrict B.inBudget).permConj (Equiv.refl _) B.tpShift ρ +
          ((B.cntKraus k).restrict fun d => !B.inBudget d).permConj (Equiv.refl _) B.endSwap ρ
      else B.cntKraus k ρ := by
  change ∑ x, B.tpOp k x * ρ * (B.tpOp k x)ᴴ = _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have h3 : ∀ c : Fin (B.budget + 2), B.tpOp k (.inr (.inr c)) = 0 := fun c => by
    simp only [tpOp, h, zero_kronecker]
    rfl
  simp only [h3, Matrix.zero_mul, Finset.sum_const_zero, add_zero]
  split_ifs with hk
  · simp only [tpOp, hk, ite_true]
    rfl
  · simp only [tpOp, hk, ite_false, Matrix.zero_mul, Finset.sum_const_zero, add_zero]
    rfl

variable {A : AdaptiveIAlg X Y Req Resp O} (T : A.QFTest)

/-- The steps of `A^Π` before the junction are trace preserving when `A`'s are. -/
theorem withTest_step_tp (hA : A.TracePreserving) {k : StepIdx A.slots A.post}
    (hk : (k : ℕ) < A.slots + A.post) :
    ∑ r, (((A.withTest T.toQTest).step k).op r)ᴴ * ((A.withTest T.toQTest).step k).op r = 1 := by
  have hstep : (A.withTest T.toQTest).step k =
      (A.liftCopy (A.step k)).embedIdx (A.embA T.toQTest.R) := by
    show withTestStep T.toQTest k = _
    unfold withTestStep
    rw [dif_pos hk]
  have key : ∀ K : KrausMap (Option A.R × Option T.toQTest.R) (DReg (A.W × A.W) A.width X Y Req Resp)
      (DReg (A.W × A.W) A.width X Y Req Resp),
      K = (A.liftCopy (A.step k)).embedIdx (A.embA T.toQTest.R) → ∑ r, (K.op r)ᴴ * K.op r = 1 := by
    rintro K rfl
    rw [KrausMap.sum_embedIdx]
    exact KrausMap.sum_tensorId_reindex_eq_one _ (hA _) _
  exact key _ hstep

/-- **The trace-preserving form's maps before the junction lift `A`'s** along the copy register,
for a trace-preserving `A`. -/
theorem tpStep_lifts (hA : A.TracePreserving) {k : StepIdx A.slots A.post}
    (hk : (k : ℕ) < A.slots + A.post) :
    ((A.withTest T.toQTest).toTPKindAlg.step k).Lifts (cntCopy T) (A.toTPKindAlg.step k) := by
  have hstep : (A.withTest T.toQTest).step k =
      (A.liftCopy (A.step k)).embedIdx (A.embA T.toQTest.R) := by
    show withTestStep T.toQTest k = _
    unfold withTestStep
    rw [dif_pos hk]
  have hcopy : ((A.withTest T.toQTest).step k).Lifts A.copySplit (A.step k) := by
    rw [hstep]
    exact (KrausMap.lifts_reindex_tensorId A.copySplit (A.step k)).embedIdx _
  have hcnt : ((A.withTest T.toQTest).cntKraus k).Lifts (cntCopy T) (A.cntKraus k) :=
    (hcopy.tensorId (Fin (A.budget + 2)) (E₂ := liftProd A.copySplit _) fun _ _ => rfl).reindex
      fun _ => rfl
  have hσ : ∀ x, cntCopy T ((Equiv.refl (A.withTest T.toQTest).CReg).symm x) =
      ((Equiv.refl A.CReg).symm (cntCopy T x).1, (cntCopy T x).2) := fun _ => rfl
  have hshift : ∀ x, cntCopy T ((A.withTest T.toQTest).tpShift x) =
      (A.tpShift (cntCopy T x).1, (cntCopy T x).2) := fun x => by
    obtain ⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩ := x
    rfl
  have hend : ∀ x, cntCopy T ((A.withTest T.toQTest).endSwap x) =
      (A.endSwap (cntCopy T x).1, (cntCopy T x).2) := fun x => by
    obtain ⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩ := x
    rfl
  have hbud : ∀ x, (A.withTest T.toQTest).inBudget x = A.inBudget (cntCopy T x).1 := fun x => by
    obtain ⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩ := x
    rfl
  have h1 := (hcnt.restrict hbud).permConj hσ (perm_symm_lift _ hshift)
  have h2 := (hcnt.restrict (p' := fun d => !(A.withTest T.toQTest).inBudget d)
    (p := fun d => !A.inBudget d) fun x => congrArg (!·) (hbud x)).permConj hσ (perm_symm_lift _ hend)
  have hT := KrausMap.haltOp_eq_zero (withTest_step_tp T hA hk)
  have hA' := KrausMap.haltOp_eq_zero (hA k)
  intro ρ τ
  refine ((toTPKindAlg_step_apply (A.withTest T.toQTest) k hT _).trans ?_).trans
    (congrArg (liftMat (cntCopy T) · τ) (toTPKindAlg_step_apply A k hA' ρ)).symm
  by_cases hs : (k : ℕ) < A.slots
  · have hs' : (k : ℕ) < (A.withTest T.toQTest).slots := hs
    rw [if_pos hs', if_pos hs]
    exact (congrArg₂ (· + ·) (h1 ρ τ) (h2 ρ τ)).trans (liftMat_add_left (cntCopy T) _ _ τ).symm
  · have hs' : ¬ (k : ℕ) < (A.withTest T.toQTest).slots := hs
    rw [if_neg hs', if_neg hs]
    exact hcnt ρ τ

variable (C : Challenger X Y Req Resp)

open ReprogrammedCircuit (liftEquiv Lifted)

/-- **The trace-preserving form's maps before the junction, on the composed registers, lift
`A`'s.** -/
theorem lifts_tpAdvKraus (hA : A.TracePreserving) {k : StepIdx A.slots A.post}
    (hk : (k : ℕ) < A.slots + A.post) :
    ((A.withTest T.toQTest).toTPKindAlg.advKraus C k).Lifts (liftEquiv (cwCopy T C))
      (A.toTPKindAlg.advKraus C k) :=
  ((tpStep_lifts T hA hk).tensorId _ (E₂ := liftProd (cntCopy T) _) fun _ _ => rfl).reindex
    fun _ => rfl

theorem lifts_tpMeasReq [Nonempty X] [AddGroup Y] (j : Fin A.slots) :
    ((A.withTest T.toQTest).toTPKindAlg.measReq C j).Lifts (liftEquiv (cwCopy T C))
      (A.toTPKindAlg.measReq C j) := by
  refine KrausMap.Lifts.comp (KrausMap.lifts_ofPerm _ (perm_symm_lift _ fun x => ?_))
    (KrausMap.lifts_measureFn _ fun x => ?_)
  · obtain ⟨⟨⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩, u⟩, qr⟩ := x
    simp only [KindAlg.copyReq, Function.Involutive.coe_toPerm]
    split_ifs with h1 h2 h2 <;> first | rfl | exact absurd h1 h2 | exact absurd h2 h1
  · obtain ⟨⟨⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩, u⟩, qr⟩ := x
    rfl

theorem lifts_tpWriteReply [Nonempty X] [AddGroup Y] (j : Fin A.slots) :
    (KrausMap.ofPerm ((A.withTest T.toQTest).toTPKindAlg.writeReply C j)).Lifts
      (liftEquiv (cwCopy T C)) (KrausMap.ofPerm (A.toTPKindAlg.writeReply C j)) := by
  refine KrausMap.lifts_ofPerm _ (perm_symm_lift _ fun x => ?_)
  obtain ⟨⟨⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩, u⟩, qr⟩ := x
  show liftEquiv (cwCopy T C) (if (u.logs j).isSome then _ else _) =
    ((if (u.logs j).isSome then _ else _), _)
  by_cases hl : (u.logs j).isSome = true
  · rw [if_pos hl, if_pos hl]
    rfl
  · rw [if_neg hl, if_neg hl]

theorem lifted_tpAdvQueries [Nonempty X] [AddGroup Y]
    (ass : A.toTPKindAlg.CW C → List (Assignment X Y)) :
    Lifted (cwCopy T C)
      ((A.withTest T.toQTest).toTPKindAlg.advQueries C fun v => ass (cwCopy T C v).1)
      (A.toTPKindAlg.advQueries C ass) := by
  refine Lifted.concat_map (fun k => ReprogrammedCircuit.lifted_kraus ?_
    (ReprogrammedCircuit.lifted_rquery (fun v => rfl)
      (ReprogrammedCircuit.lifted_kraus ?_ (by exact ReprogrammedCircuit.lifted_nil)))) _
  all_goals
    refine KrausMap.lifts_ofPerm _ (perm_symm_lift _ fun x => ?_)
    obtain ⟨⟨⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩, u⟩, qr⟩ := x
    rfl

theorem lifted_tpChalQueries [Nonempty X] [AddGroup Y] (j : Fin A.slots) :
    Lifted (cwCopy T C) ((A.withTest T.toQTest).toTPKindAlg.chalQueries C j)
      (A.toTPKindAlg.chalQueries C j) := by
  unfold KindAlg.chalQueries
  refine Lifted.concat_map (fun i => ?_) _
  have hp : ∀ (π' : Equiv.Perm (QueryReg ((A.withTest T.toQTest).toTPKindAlg.CW C) 1 X Y))
      (π : Equiv.Perm (QueryReg (A.toTPKindAlg.CW C) 1 X Y)),
      (∀ x, liftEquiv (cwCopy T C) (π' x) = (π (liftEquiv (cwCopy T C) x).1,
        (liftEquiv (cwCopy T C) x).2)) →
      (KrausMap.ofPerm π').Lifts (liftEquiv (cwCopy T C)) (KrausMap.ofPerm π) :=
    fun _ _ h => KrausMap.lifts_ofPerm _ (perm_symm_lift _ h)
  refine ReprogrammedCircuit.lifted_kraus (hp _ _ fun x => ?_)
    (ReprogrammedCircuit.lifted_rquery (fun v => rfl)
      (ReprogrammedCircuit.lifted_kraus (hp _ _ fun x => ?_)
        (by exact ReprogrammedCircuit.lifted_nil)))
  all_goals
    obtain ⟨⟨⟨⟨⟨⟨w, c⟩, n⟩, rq, rs⟩, pr⟩, u⟩, qr⟩ := x
    rfl

theorem lifted_tpSlotCircBoth [Nonempty X] [AddGroup Y] (hA : A.TracePreserving)
    (j : Fin A.slots) :
    Lifted (cwCopy T C) ((A.withTest T.toQTest).toTPKindAlg.slotCircBoth C j)
      (A.toTPKindAlg.slotCircBoth C j) :=
  ReprogrammedCircuit.lifted_kraus (lifts_tpAdvKraus T C hA (k := slotStep j) (by simp; omega))
    (ReprogrammedCircuit.lifted_kraus (lifts_tpMeasReq T C j)
      ((lifted_tpChalQueries T C j).append (ReprogrammedCircuit.lifted_kraus
        (lifts_tpWriteReply T C j)
        (lifted_tpAdvQueries T C fun u => A.toTPKindAlg.advAss C j u.chal))))

theorem lifted_tpPostCirc [Nonempty X] [AddGroup Y] (hA : A.TracePreserving) (b : Fin A.post) :
    Lifted (cwCopy T C) ((A.withTest T.toQTest).toTPKindAlg.postCirc C b)
      (A.toTPKindAlg.postCirc C b) :=
  ReprogrammedCircuit.lifted_kraus (lifts_tpAdvKraus T C hA (k := postStep b) (by simp))
    (lifted_tpAdvQueries T C fun u => A.toTPKindAlg.postAss C u.chal)

/-- **Before the junction, the trace-preserving composition of `A^Π` lifts that of `A`**, with the
copy register as the extra factor. -/
theorem lifted_tpPreCirc [Nonempty X] [AddGroup Y] (hA : A.TracePreserving) :
    Lifted (cwCopy T C) (preCirc C (A.withTest T.toQTest).toTPKindAlg)
      (preCirc C A.toTPKindAlg) :=
  (Lifted.concat_map (fun j => lifted_tpSlotCircBoth T C hA j) _).append
    (Lifted.concat_map (fun b => lifted_tpPostCirc T C hA b) (List.finRange A.post))

end AdaptiveIAlg

end GordieHowe.Quantum

namespace GordieHowe.Quantum

namespace KrausMap

variable {R : Type*} [Fintype R] {ι ι' Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
  [DecidableEq ι']

theorem lifts_identity (E : ι' ≃ ι × Z) : (KrausMap.identity ι').Lifts E (KrausMap.identity ι) :=
  fun ρ τ => by rw [id_apply, id_apply]

end KrausMap

/-! ### Lifted circuits of the core and their query intervals -/

namespace Circuit

variable {ι ι' Z : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

/-- **A circuit of the core lifting another along `E`**: the same shape, each Kraus map lifting the
other's. -/
def Lifted (E : ι' ≃ ι × Z) : Circuit ι' → Circuit ι → Prop
  | nil, nil => True
  | kraus K' c', kraus K c => K'.Lifts E K ∧ Lifted E c' c
  | query c', query c => Lifted E c' c
  | _, _ => False

theorem Lifted.queries_eq {E : ι' ≃ ι × Z} : ∀ {c' : Circuit ι'} {c : Circuit ι},
    Lifted E c' c → c'.queries = c.queries
  | nil, nil, _ => rfl
  | kraus _ c', kraus _ c, ⟨_, h⟩ => Lifted.queries_eq (c' := c') (c := c) h
  | query c', query c, h => by
    simp only [queries]
    rw [Lifted.queries_eq (c' := c') (c := c) h]
  | nil, kraus _ _, h => h.elim
  | nil, query _, h => h.elim
  | kraus _ _, nil, h => h.elim
  | kraus _ _, query _, h => h.elim
  | query _, nil, h => h.elim
  | query _, kraus _ _, h => h.elim

theorem Lifted.head {E : ι' ≃ ι × Z} : ∀ {c' : Circuit ι'} {c : Circuit ι},
    Lifted E c' c → (Circuit.head c').K.Lifts E (Circuit.head c).K
  | nil, nil, _ => KrausMap.lifts_identity E
  | kraus _ c', kraus _ c, ⟨hK, h⟩ => (Lifted.head (c' := c') (c := c) h).comp hK
  | query _, query _, _ => KrausMap.lifts_identity E
  | nil, kraus _ _, h => h.elim
  | nil, query _, h => h.elim
  | kraus _ _, nil, h => h.elim
  | kraus _ _, query _, h => h.elim
  | query _, nil, h => h.elim
  | query _, kraus _ _, h => h.elim

theorem Lifted.tail {E : ι' ≃ ι × Z} : ∀ {c' : Circuit ι'} {c : Circuit ι},
    Lifted E c' c → Lifted E (Circuit.tail c') (Circuit.tail c)
  | nil, nil, _ => trivial
  | kraus _ c', kraus _ c, ⟨_, h⟩ => Lifted.tail (c' := c') (c := c) h
  | query _, query _, h => h
  | nil, kraus _ _, h => h.elim
  | nil, query _, h => h.elim
  | kraus _ _, nil, h => h.elim
  | kraus _ _, query _, h => h.elim
  | query _, nil, h => h.elim
  | query _, kraus _ _, h => h.elim

/-- **The query intervals of lifted circuits lift each other.** -/
theorem Lifted.seg {E : ι' ≃ ι × Z} {c' : Circuit ι'} {c : Circuit ι} (h : Lifted E c' c) :
    ∀ k, (Circuit.seg c' k).K.Lifts E (Circuit.seg c k).K
  | 0 => h.head
  | k + 1 => Lifted.seg h.tail k

theorem Lifted.append {E : ι' ≃ ι × Z} : ∀ {c' : Circuit ι'} {c : Circuit ι} {d' d},
    Lifted E c' c → Lifted E d' d → Lifted E (c' ++ d') (c ++ d)
  | nil, nil, _, _, _, hd => hd
  | kraus _ c', kraus _ c, _, _, ⟨hK, hc⟩, hd => ⟨hK, Lifted.append (c' := c') (c := c) hc hd⟩
  | query c', query c, _, _, hc, hd => Lifted.append (c' := c') (c := c) hc hd
  | nil, kraus _ _, _, _, h, _ => h.elim
  | nil, query _, _, _, h, _ => h.elim
  | kraus _ _, nil, _, _, h, _ => h.elim
  | kraus _ _, query _, _, _, h, _ => h.elim
  | query _, nil, _, _, h, _ => h.elim
  | query _, kraus _ _, _, _, h, _ => h.elim

/-- **The query intervals of a circuit followed by one Kraus map**: those of the circuit, the last
followed by the map. -/
theorem seg_append_kraus {R : Type} [Fintype R] (L : KrausMap R ι ι) :
    ∀ (c : Circuit ι) (k : ℕ), k ≤ c.queries → ∀ ρ : Matrix ι ι ℂ,
      (Circuit.seg (c ++ kraus L nil) k).K ρ =
        if k < c.queries then (Circuit.seg c k).K ρ else L ((Circuit.seg c k).K ρ)
  | nil, 0, _, ρ => by
    simp only [Circuit.seg, Circuit.head, nil_append, queries, lt_self_iff_false, ite_false]
    exact (KrausMap.comp_apply _ _ ρ).trans
      ((KrausMap.id_apply _).trans (congrArg L.apply (KrausMap.id_apply ρ)).symm)
  | nil, k + 1, hk, _ => by simp [queries] at hk
  | kraus K c, 0, hk, ρ => by
    have ih := seg_append_kraus L c 0 hk (K ρ)
    simp only [Circuit.seg] at ih
    simp only [Circuit.seg, Circuit.head, kraus_append, queries]
    refine (KrausMap.comp_apply _ _ ρ).trans (ih.trans ?_)
    by_cases h : 0 < c.queries
    · simp only [h, ite_true]
      exact (KrausMap.comp_apply _ _ _).symm
    · simp only [h, ite_false]
      exact congrArg L.apply (KrausMap.comp_apply _ _ _).symm
  | kraus K c, k + 1, hk, ρ => seg_append_kraus L c (k + 1) hk ρ
  | query c, 0, _, ρ => by
    simp only [Circuit.seg, Circuit.head, query_append, queries, Nat.zero_lt_succ, ite_true]
    rfl
  | query c, k + 1, hk, ρ => by
    have ih := seg_append_kraus L c k (by simp [queries] at hk; omega) ρ
    simp only [Circuit.seg, Circuit.tail, query_append, queries, Nat.add_lt_add_iff_right]
    exact ih

end Circuit

namespace ReprogrammedCircuit

variable {V V' X Y Z : Type} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddGroup Y]

/-- The work register with the reprogramming ancilla, split along `E : V' ≃ V × Z`. -/
def ancLift (E : V' ≃ V × Z) : V' × (X × Y × Bool) ≃ (V × (X × Y × Bool)) × Z where
  toFun p := (((E p.1).1, p.2), (E p.1).2)
  invFun q := (E.symm (q.1.1, q.2), q.1.2)
  left_inv p := by simp
  right_inv q := by simp

omit [AddGroup Y] in
theorem Lifted.queries_eq {E : V' ≃ V × Z} : ∀ {c' : ReprogrammedCircuit V' X Y}
    {c : ReprogrammedCircuit V X Y}, Lifted E c' c → c'.queries = c.queries
  | nil, nil, _ => rfl
  | kraus _ c', kraus _ c, ⟨_, h⟩ => Lifted.queries_eq (c' := c') (c := c) h
  | rquery _ c', rquery _ c, ⟨_, h⟩ => by
    simp only [queries]
    rw [Lifted.queries_eq (c' := c') (c := c) h]
  | nil, kraus _ _, h => h.elim
  | nil, rquery _ _, h => h.elim
  | kraus _ _, nil, h => h.elim
  | kraus _ _, rquery _ _, h => h.elim
  | rquery _ _, nil, h => h.elim
  | rquery _ _, kraus _ _, h => h.elim

omit [AddGroup Y] in
/-- A Kraus map lifting another lifts it with the reprogramming ancilla. -/
theorem lifts_liftAnc {E : V' ≃ V × Z} {R R' : Type} [Fintype R] [Fintype R']
    {K' : KrausMap R' (QueryReg V' 1 X Y) (QueryReg V' 1 X Y)}
    {K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)} (h : K'.Lifts (liftEquiv E) K) :
    K'.liftAnc.Lifts (liftEquiv (ancLift (X := X) (Y := Y) E)) K.liftAnc :=
  (h.tensorId (X × Y × Bool) (E₂ := liftProd (liftEquiv E) _) fun _ _ => rfl).reindex
    fun _ => rfl

omit [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V'] [Fintype X] [Fintype Y] [DecidableEq Y] [AddGroup Y] in
theorem reprogSwap_lift {E : V' ≃ V × Z} {a' : V' → List (Assignment X Y)}
    {a : V → List (Assignment X Y)} (ha : ∀ v, a' v = a (E v).1)
    (x : ReprogrammedQueryReg V' X Y) :
    liftEquiv (ancLift (X := X) (Y := Y) E) (reprogSwap a' x) =
      (reprogSwap a (liftEquiv (ancLift (X := X) (Y := Y) E) x).1,
        (liftEquiv (ancLift (X := X) (Y := Y) E) x).2) := by
  obtain ⟨⟨v, xa, ya, f⟩, q⟩ := x
  simp only [reprogSwap_apply, reprogCond, ha, liftEquiv, ancLift, Equiv.coe_fn_mk]
  split_ifs <;> rfl

omit [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V'] [Fintype X] [Fintype Y] [DecidableEq Y] in
theorem reprogAdd_lift {E : V' ≃ V × Z} {a' : V' → List (Assignment X Y)}
    {a : V → List (Assignment X Y)} (ha : ∀ v, a' v = a (E v).1)
    (x : ReprogrammedQueryReg V' X Y) :
    liftEquiv (ancLift (X := X) (Y := Y) E) (reprogAdd a' x) =
      (reprogAdd a (liftEquiv (ancLift (X := X) (Y := Y) E) x).1,
        (liftEquiv (ancLift (X := X) (Y := Y) E) x).2) := by
  obtain ⟨⟨v, xa, ya, f⟩, q⟩ := x
  simp only [reprogAdd, queryPermOf, ha]
  rfl

/-- **Lifted circuits compile to lifted circuits of the core.** -/
theorem Lifted.toCircuit {E : V' ≃ V × Z} : ∀ {c' : ReprogrammedCircuit V' X Y}
    {c : ReprogrammedCircuit V X Y}, Lifted E c' c →
    Circuit.Lifted (liftEquiv (ancLift (X := X) (Y := Y) E)) (ReprogrammedCircuit.toCircuit c')
      (ReprogrammedCircuit.toCircuit c)
  | nil, nil, _ => trivial
  | kraus _ c', kraus _ c, ⟨hK, h⟩ => ⟨lifts_liftAnc hK, Lifted.toCircuit (c' := c') (c := c) h⟩
  | rquery _ c', rquery _ c, ⟨ha, h⟩ =>
    ⟨KrausMap.lifts_ofPerm _ (perm_symm_lift _ (reprogSwap_lift ha)),
      (KrausMap.lifts_ofPerm _ (perm_symm_lift _ (reprogAdd_lift ha))).comp
        (KrausMap.lifts_ofPerm _ (perm_symm_lift _ (reprogSwap_lift ha))),
        Lifted.toCircuit (c' := c') (c := c) h⟩
  | nil, kraus _ _, h => h.elim
  | nil, rquery _ _, h => h.elim
  | kraus _ _, nil, h => h.elim
  | kraus _ _, rquery _ _, h => h.elim
  | rquery _ _, nil, h => h.elim
  | rquery _ _, kraus _ _, h => h.elim

end ReprogrammedCircuit

end GordieHowe.Quantum

namespace GordieHowe.Quantum

namespace KrausMap

variable {R R₁ R₂ ι : Type*} [Fintype R] [Fintype R₁] [Fintype R₂] [Fintype ι] [DecidableEq ι]

theorem sum_permConj (K : KrausMap R ι ι) (σ τ : Equiv.Perm ι) :
    ∑ r, ((K.permConj σ τ).op r)ᴴ * (K.permConj σ τ).op r =
      (∑ r, (K.op r)ᴴ * K.op r).submatrix σ σ := by
  rw [submatrix_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [permConj]
  rw [conjTranspose_submatrix, submatrix_mul_equiv]

theorem sum_comp_of_tp (K₂ : KrausMap R₂ ι ι) (K₁ : KrausMap R₁ ι ι)
    (h₂ : ∑ r, (K₂.op r)ᴴ * K₂.op r = 1) :
    ∑ r, ((K₂.comp K₁).op r)ᴴ * (K₂.comp K₁).op r = ∑ r, (K₁.op r)ᴴ * K₁.op r := by
  simp only [comp, Fintype.sum_prod_type, conjTranspose_mul]
  refine Finset.sum_congr rfl fun r₁ _ => ?_
  calc ∑ r₂, (K₁.op r₁)ᴴ * (K₂.op r₂)ᴴ * (K₂.op r₂ * K₁.op r₁)
      = (K₁.op r₁)ᴴ * (∑ r₂, (K₂.op r₂)ᴴ * K₂.op r₂) * K₁.op r₁ := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun r₂ _ => ?_
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h₂, Matrix.mul_one]

/-- Maps with the same action have the same action tensored with an identity and moved along a
basis equivalence. -/
theorem tensorId_reindex_congr {K₁ : KrausMap R₁ ι ι} {K₂ : KrausMap R₂ ι ι}
    (h : ∀ ρ, K₁ ρ = K₂ ρ) {A κ : Type*} [Fintype A] [DecidableEq A] [Fintype κ] [DecidableEq κ]
    (e : ι × A ≃ κ) (M : Matrix κ κ ℂ) :
    ((K₁.tensorId A).reindex e) M = ((K₂.tensorId A).reindex e) M := by
  rw [reindex_apply, reindex_apply]
  congr 1
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [tensorId_apply_apply, tensorId_apply_apply]
  exact congrFun (congrFun (h _) i) j

end KrausMap

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {A : AdaptiveIAlg X Y Req Resp O} (T : A.QFTest) (C : Challenger X Y Req Resp)

/-- **The junction is trace preserving** when `A`'s last map is. -/
theorem junction_tp (hA : A.TracePreserving) :
    ∑ r, ((junction T.toQTest).op r)ᴴ * (junction T.toQTest).op r = 1 := by
  have h2 := KrausMap.sum_tensorId_reindex_eq_one T.step.toKrausMap T.step.sum_conjTranspose_mul
    A.copySplit.symm
  have h1 : ∑ r, (((A.liftCopy (A.step lastStep)).permConj (Equiv.refl _) A.copyOut).op r)ᴴ *
      ((A.liftCopy (A.step lastStep)).permConj (Equiv.refl _) A.copyOut).op r = 1 := by
    rw [KrausMap.sum_permConj, liftCopy, KrausMap.sum_tensorId_reindex_eq_one _ (hA _) _,
      submatrix_one_equiv]
  exact (KrausMap.sum_comp_of_tp ((T.step.toKrausMap.tensorId A.W).reindex A.copySplit.symm) _
    h2).trans h1

theorem withTest_step_last_tp (hA : A.TracePreserving) :
    ∑ r, (((A.withTest T.toQTest).step lastStep).op r)ᴴ *
      ((A.withTest T.toQTest).step lastStep).op r = 1 := by
  have hstep : (A.withTest T.toQTest).step lastStep =
      (junction T.toQTest).embedIdx (A.embAT T.toQTest.R) := by
    show withTestStep T.toQTest lastStep = _
    unfold withTestStep
    rw [dif_neg (by simp [QFTest.toQTest])]
    exact if_pos (by simp [QFTest.toQTest])
  have key : ∀ K : KrausMap (Option A.R × Option T.toQTest.R) (DReg (A.W × A.W) A.width X Y Req Resp)
      (DReg (A.W × A.W) A.width X Y Req Resp),
      K = (junction T.toQTest).embedIdx (A.embAT T.toQTest.R) → ∑ r, (K.op r)ᴴ * K.op r = 1 := by
    rintro K rfl
    rw [KrausMap.sum_embedIdx]
    exact junction_tp T hA
  exact key _ hstep

/-- **After the slots, the trace-preserving form's map on the composed registers is the model's**,
when the adversary's map does not halt. -/
theorem tpAdvKraus_apply_of_not_lt (B : AdaptiveIAlg X Y Req Resp O) {k : StepIdx B.slots B.post}
    (hk : ¬ (k : ℕ) < B.slots) (h : (B.step k).haltOp = 0)
    (M : Matrix (QueryReg (B.toKindAlg.CW C) 1 X Y) (QueryReg (B.toKindAlg.CW C) 1 X Y) ℂ) :
    B.toTPKindAlg.advKraus C k M = B.toKindAlg.advKraus C k M :=
  KrausMap.tensorId_reindex_congr (fun ρ => by
    refine (toTPKindAlg_step_apply B k h ρ).trans ?_
    rw [if_neg hk]
    change B.cntKraus k ρ = (if (k : ℕ) < B.slots then ((B.cntKraus k).restrict
      B.inBudget).permConj (Equiv.refl _) B.cntShift else B.cntKraus k) ρ
    rw [if_neg hk]) _ M

theorem lastStep_not_lt (B : AdaptiveIAlg X Y Req Resp O) :
    ¬ ((lastStep : StepIdx B.slots B.post) : ℕ) < B.slots := by
  rw [Fin.val_mk]
  omega

/-- **The junction, blockwise**: on a state with a blank copy, the block of the junction at copy
value `c` is the test's channel applied to `A`'s last map's output cut to the basis states whose
output has the representative `c`. -/
theorem blockAt_junction (σ : Matrix (DReg A.W A.width X Y Req Resp)
      (DReg A.W A.width X Y Req Resp) ℂ) (c : A.W) :
    blockAt A.copySplit (junction T.toQTest
        (liftMat A.copySplit σ (Matrix.single A.copyBlank A.copyBlank 1))) c c =
      T.step (cutTo (repIs c) (A.step lastStep σ)) := by
  have hP : ((A.liftCopy (A.step lastStep)).permConj (Equiv.refl _) A.copyOut)
      (liftMat A.copySplit σ (Matrix.single A.copyBlank A.copyBlank 1)) =
      (liftMat A.copySplit (A.step lastStep σ) (Matrix.single A.copyBlank A.copyBlank 1)).submatrix
        A.copyOut.symm A.copyOut.symm := by
    rw [KrausMap.permConj_apply]
    simp only [Equiv.refl_symm, Equiv.coe_refl, Matrix.submatrix_id_id]
    rw [lifts_liftCopy (A.step lastStep) σ]
  rw [junction, KrausMap.comp_apply,
    (lifts_liftCopy (T.toQTest.step 0).toKrausMap).blockAt_apply, hP]
  have hb : blockAt A.copySplit
      ((liftMat A.copySplit (A.step lastStep σ) (Matrix.single A.copyBlank A.copyBlank 1)).submatrix
        A.copyOut.symm A.copyOut.symm) c c = cutTo (repIs c) (A.step lastStep σ) := by
    ext a b
    rw [GordieHowe.Quantum.blockAt_apply, Matrix.submatrix_apply, liftMat_apply, copySplit_copyOut_symm,
      copySplit_copyOut_symm]
    have hs : ∀ r x : A.W, A.copyBlank = Equiv.swap A.copyBlank r x ↔ x = r := fun r x => by
      rw [eq_comm, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
    simp only [cutTo, repIs, Set.mem_ofPred_eq, Matrix.single_apply, hs]
    by_cases ha : A.outRep a.workspace = c <;>
      by_cases hb : A.outRep b.workspace = c <;> simp_all [eq_comm]
  rw [hb]
  rfl

open ReprogrammedCircuit (liftEquiv) in
/-- The basis states of the composed registers whose output has the representative `c`. -/
def repIsC (c : A.W) : Set (QueryReg (A.toKindAlg.CW C) 1 X Y) :=
  {q | A.outRep q.1.adv.workspace.1 = c}

open ReprogrammedCircuit (liftEquiv) in
/-- **The junction on the composed registers, blockwise**: on a state with a blank copy, the block
at copy value `c` of the last map of the composition of `A^Π` is the test's channel on `A`'s
registers applied to `A`'s last map's output cut to `repIsC c`. -/
theorem blockAt_advKraus_last (M : Matrix (QueryReg (A.toKindAlg.CW C) 1 X Y)
      (QueryReg (A.toKindAlg.CW C) 1 X Y) ℂ) (c : A.W) :
    blockAt (liftEquiv (cwCopy T C)) ((A.withTest T.toQTest).toKindAlg.advKraus C lastStep
        (liftMat (liftEquiv (cwCopy T C)) M (Matrix.single A.copyBlank A.copyBlank 1))) c c =
      composedLift C A T.step.toKrausMap (cutTo (repIsC C c) (A.toKindAlg.advKraus C lastStep M)) := by
  ext x y
  rw [GordieHowe.Quantum.blockAt_apply]
  refine ((lifts_advKraus_last T C).apply_apply _ _ _).trans (Eq.trans ?_
    ((lifts_composedLift C A T.step.toKrausMap).apply_apply _ _ _).symm)
  rw [blockAt_cutTo (composedSplit C A) (S := repIsC C c) (S' := repIs c) (fun _ => Iff.rfl)]
  have h2 := (lifts_advKraus_last_self (A := A) C).blockAt_apply M (composedSplit C A x).2
    (composedSplit C A y).2
  have key := congrFun (congrFun (blockAt_junction T (blockAt (composedSplit C A) M
    (composedSplit C A x).2 (composedSplit C A y).2) c) (composedSplit C A x).1)
    (composedSplit C A y).1
  rw [GordieHowe.Quantum.blockAt_apply, ← blockAt_liftMat_cwCopy] at key
  exact key.trans (congrArg (fun N => T.step.toKrausMap (cutTo (repIs c) N)
    (composedSplit C A x).1 (composedSplit C A y).1) h2.symm)

end AdaptiveIAlg

end GordieHowe.Quantum

namespace GordieHowe.Quantum

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  (C : Challenger X Y Req Resp)

open ReprogrammedCircuit (liftEquiv Lifted ancLift)

/-- The query depth of a composition is the number of queries before its last map. -/
theorem depth_composeBothOut (B : KindAlg X Y Req Resp O) {O' : Type} (f : B.CW C → O') :
    (B.composeBothOut C f).depth = (preCirc C B).queries := by
  show (ReprogrammedCircuit.toCircuit (B.fullCircBoth C)).queries = _
  rw [ReprogrammedCircuit.queries_toCircuit, fullCircBoth_eq, ReprogrammedCircuit.queries_append]
  rfl

/-- **The Kraus maps of a composition**: the query intervals of the circuit before its last map,
the last followed by the last map. -/
theorem composeBothOut_step_apply (B : KindAlg X Y Req Resp O) {O' : Type} (f : B.CW C → O')
    (k : Fin ((B.composeBothOut C f).depth + 1))
    (ρ : Matrix (ReprogrammedQueryReg (B.CW C) X Y) (ReprogrammedQueryReg (B.CW C) X Y) ℂ) :
    (B.composeBothOut C f).step k ρ =
      if (k : ℕ) < (preCirc C B).queries then
        (Circuit.seg (ReprogrammedCircuit.toCircuit (preCirc C B)) k).K ρ
      else (B.advKraus C lastStep).liftAnc
        ((Circuit.seg (ReprogrammedCircuit.toCircuit (preCirc C B)) k).K ρ) := by
  have hk : (k : ℕ) ≤ (ReprogrammedCircuit.toCircuit (preCirc C B)).queries := by
    rw [ReprogrammedCircuit.queries_toCircuit, ← depth_composeBothOut C B f]
    exact Nat.le_of_lt_succ k.2
  refine (KrausMap.sigmaEmbed_apply _ k ρ).trans ?_
  have h := Circuit.seg_append_kraus (B.advKraus C lastStep).liftAnc
    (ReprogrammedCircuit.toCircuit (preCirc C B)) k hk ρ
  rw [ReprogrammedCircuit.queries_toCircuit] at h
  have he : ReprogrammedCircuit.toCircuit (B.fullCircBoth C) =
      ReprogrammedCircuit.toCircuit (preCirc C B) ++
        Circuit.kraus (B.advKraus C lastStep).liftAnc Circuit.nil := by
    rw [fullCircBoth_eq, ReprogrammedCircuit.toCircuit_append]
    rfl
  rw [← h]
  exact congrArg (fun c => (Circuit.seg c k).K ρ) he

variable {A : AdaptiveIAlg X Y Req Resp O} (T : A.QFTest)

theorem depth_composeTP_withTest (hA : A.TracePreserving) {O' O'' : Type}
    (f : (A.withTest T.toQTest).toTPKindAlg.CW C → O') (g : A.toTPKindAlg.CW C → O'') :
    ((A.withTest T.toQTest).toTPKindAlg.composeBothOut C f).depth =
      (A.toTPKindAlg.composeBothOut C g).depth := by
  rw [depth_composeBothOut, depth_composeBothOut, (lifted_tpPreCirc T C hA).queries_eq]

/-- **Before the junction, the Kraus maps of the trace-preserving composition of `A^Π` lift those
of `A`**, along the copy register. -/
theorem composeTP_step_lifts (hA : A.TracePreserving) {O' O'' : Type}
    (f : (A.withTest T.toQTest).toTPKindAlg.CW C → O') (g : A.toTPKindAlg.CW C → O'')
    (k : Fin (((A.withTest T.toQTest).toTPKindAlg.composeBothOut C f).depth + 1))
    (k' : Fin ((A.toTPKindAlg.composeBothOut C g).depth + 1)) (hkk : (k : ℕ) = k')
    (hk : (k' : ℕ) < (A.toTPKindAlg.composeBothOut C g).depth) :
    (((A.withTest T.toQTest).toTPKindAlg.composeBothOut C f).step k).Lifts
      (liftEquiv (ancLift (X := X) (Y := Y) (cwCopy T C)))
      ((A.toTPKindAlg.composeBothOut C g).step k') := by
  have hL := lifted_tpPreCirc T C hA
  have hq := hL.queries_eq
  have hd := depth_composeBothOut C A.toTPKindAlg g
  intro ρ τ
  rw [composeBothOut_step_apply, composeBothOut_step_apply, if_pos (by omega), if_pos (by omega)]
  rw [hkk]
  exact hL.toCircuit.seg k' ρ τ

omit [Nonempty X] [AddGroup Y] [Fintype X] [DecidableEq Y] in
theorem withAnc_liftMat {V V' Z : Type} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    (E : V' ≃ V × Z) (x₀ : X) (ρ : Matrix (QueryReg V 1 X Y) (QueryReg V 1 X Y) ℂ)
    (τ : Matrix Z Z ℂ) :
    withAnc x₀ (liftMat (liftEquiv E) ρ τ) =
      liftMat (liftEquiv (ancLift (X := X) (Y := Y) E)) (withAnc x₀ ρ) τ := by
  ext p q
  simp only [withAnc, liftMat_apply, liftEquiv, ancLift, Equiv.coe_fn_mk]
  ring

/-- **The initial state of the trace-preserving composition of `A^Π`** is that of `A` with the
blank copy register. -/
theorem init_composeTP_withTest [Nonempty Y] {O' O'' : Type}
    (f : (A.withTest T.toQTest).toTPKindAlg.CW C → O') (g : A.toTPKindAlg.CW C → O'') :
    ((A.withTest T.toQTest).toTPKindAlg.composeBothOut C f).init.mat =
      liftMat (liftEquiv (ancLift (X := X) (Y := Y) (cwCopy T C)))
        (A.toTPKindAlg.composeBothOut C g).init.mat (Matrix.single A.copyBlank A.copyBlank 1) := by
  show withAnc KindAlg.x₀ ((A.withTest T.toQTest).toTPKindAlg.initSys C).mat =
    liftMat _ (withAnc KindAlg.x₀ (A.toTPKindAlg.initSys C).mat) _
  rw [← withAnc_liftMat]
  congr 1
  exact initSys_withTest T C

omit [Nonempty X] [AddGroup Y] in
/-- A map lifted with the reprogramming ancilla acts on the blocks at the ancilla. -/
theorem liftAnc_apply_apply {V R : Type} [Fintype V] [DecidableEq V] [Fintype R]
    (K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y))
    (N : Matrix (ReprogrammedQueryReg V X Y) (ReprogrammedQueryReg V X Y) ℂ)
    (p q : ReprogrammedQueryReg V X Y) :
    K.liftAnc N p q = K (blockAt (ancSplit V X Y) N p.1.2 q.1.2) (ancSplit V X Y p).1
      (ancSplit V X Y q).1 := by
  exact (KrausMap.lifts_reindex_tensorId (ancSplit V X Y) K).apply_apply N p q

omit [Nonempty X] [AddGroup Y] in
theorem blockAt_ancSplit_liftAnc {V R : Type} [Fintype V] [DecidableEq V] [Fintype R]
    (K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y))
    (N : Matrix (ReprogrammedQueryReg V X Y) (ReprogrammedQueryReg V X Y) ℂ) (α β : X × Y × Bool) :
    blockAt (ancSplit V X Y) (K.liftAnc N) α β = K (blockAt (ancSplit V X Y) N α β) :=
  (KrausMap.lifts_reindex_tensorId (ancSplit V X Y) K).blockAt_apply N α β

/-- The basis states of the composed registers with the reprogramming ancilla whose output has the
representative `c`. -/
def repIsR (c : A.W) : Set (ReprogrammedQueryReg (A.toKindAlg.CW C) X Y) :=
  {p | A.outRep p.1.1.adv.workspace.1 = c}

omit [Nonempty X] [AddGroup Y] in
/-- **The junction of the trace-preserving composition**, blockwise, with the reprogramming
ancilla. -/
theorem blockAt_tpAdvKraus_last_liftAnc (hA : A.TracePreserving)
    (N : Matrix (ReprogrammedQueryReg (A.toKindAlg.CW C) X Y)
      (ReprogrammedQueryReg (A.toKindAlg.CW C) X Y) ℂ) (c : A.W) :
    blockAt (liftEquiv (ancLift (X := X) (Y := Y) (cwCopy T C)))
        (((A.withTest T.toQTest).toTPKindAlg.advKraus C lastStep).liftAnc
          (liftMat (liftEquiv (ancLift (X := X) (Y := Y) (cwCopy T C))) N
            (Matrix.single A.copyBlank A.copyBlank 1))) c c =
      testOnComposed T C (cutTo (repIsR C c) ((A.toTPKindAlg.advKraus C lastStep).liftAnc N)) := by
  have hT := KrausMap.haltOp_eq_zero (withTest_step_last_tp T hA)
  have hA' := KrausMap.haltOp_eq_zero (hA lastStep)
  ext p q
  rw [GordieHowe.Quantum.blockAt_apply, liftAnc_apply_apply, testOnComposed, liftAnc_apply_apply,
    blockAt_cutTo (ancSplit _ X Y) (S := repIsR C c) (S' := repIsC C c) (fun _ => Iff.rfl),
    blockAt_ancSplit_liftAnc]
  have h2 := congrArg (fun M => (composedLift C A T.step.toKrausMap) (cutTo (repIsC C c) M)
    (ancSplit _ X Y p).1 (ancSplit _ X Y q).1)
    (tpAdvKraus_apply_of_not_lt C A (lastStep_not_lt _) hA' (blockAt (ancSplit _ X Y) N p.1.2 q.1.2))
  refine (congrFun (congrFun (tpAdvKraus_apply_of_not_lt C (A.withTest T.toQTest)
    (lastStep_not_lt _) hT _) _) _).trans (Eq.trans ?_ h2.symm)
  have key := congrFun (congrFun (blockAt_advKraus_last T C
    (blockAt (ancSplit _ X Y) N p.1.2 q.1.2) c) (ancSplit _ X Y p).1) (ancSplit _ X Y q).1
  rw [GordieHowe.Quantum.blockAt_apply] at key
  exact key

/-- **The junction of the trace-preserving compositions, blockwise**: at the last step, the block
at copy value `c` of the map of the composition of `A^Π` on a state with a blank copy is the
test's channel applied to the last map of `A`'s composition, cut to the basis states whose output
has the representative `c`. -/
theorem blockAt_composeTP_last (hA : A.TracePreserving) {O' O'' : Type}
    (f : (A.withTest T.toQTest).toTPKindAlg.CW C → O') (g : A.toTPKindAlg.CW C → O'')
    (k : Fin (((A.withTest T.toQTest).toTPKindAlg.composeBothOut C f).depth + 1))
    (k' : Fin ((A.toTPKindAlg.composeBothOut C g).depth + 1)) (hkk : (k : ℕ) = k')
    (hk : (k' : ℕ) = (A.toTPKindAlg.composeBothOut C g).depth)
    (ρ : Matrix (ReprogrammedQueryReg (A.toKindAlg.CW C) X Y)
      (ReprogrammedQueryReg (A.toKindAlg.CW C) X Y) ℂ) (c : A.W) :
    blockAt (liftEquiv (ancLift (X := X) (Y := Y) (cwCopy T C)))
        (((A.withTest T.toQTest).toTPKindAlg.composeBothOut C f).step k
          (liftMat (liftEquiv (ancLift (X := X) (Y := Y) (cwCopy T C))) ρ
            (Matrix.single A.copyBlank A.copyBlank 1))) c c =
      testOnComposed T C (cutTo (repIsR C c) ((A.toTPKindAlg.composeBothOut C g).step k' ρ)) := by
  have hL := lifted_tpPreCirc T C hA
  have hq := hL.queries_eq
  have hd := depth_composeBothOut C A.toTPKindAlg g
  rw [composeBothOut_step_apply, composeBothOut_step_apply, if_neg (by omega), if_neg (by omega),
    hkk, hL.toCircuit.seg k' ρ]
  exact blockAt_tpAdvKraus_last_liftAnc C T hA _ c

end AdaptiveIAlg

end GordieHowe.Quantum

namespace GordieHowe.Quantum

namespace KrausMap

variable {R R' ι ι' κ κ' Z : Type*} [Fintype R] [Fintype R'] [Fintype ι] [DecidableEq ι]
  [Fintype ι'] [DecidableEq ι'] [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

theorem relabel_apply (K : KrausMap R ι ι) (e : ι ≃ κ) (M : Matrix κ κ ℂ) :
    K.relabel e M = (K (M.submatrix e e)).submatrix e.symm e.symm := by
  rw [← relabel_apply_submatrix]
  congr 1
  ext x y
  simp

/-- **Lifting is carried along relabellings.** -/
theorem Lifts.relabel {E : ι' ≃ ι × Z} {K' : KrausMap R' ι' ι'} {K : KrausMap R ι ι}
    (h : K'.Lifts E K) {e' : ι' ≃ κ'} {e : ι ≃ κ} {E₂ : κ' ≃ κ × Z}
    (hE : ∀ x, E₂ (e' x) = (e (E x).1, (E x).2)) : (K'.relabel e').Lifts E₂ (K.relabel e) :=
  fun ρ τ => by
    have hE' : ∀ y, E₂ y = (e (E (e'.symm y)).1, (E (e'.symm y)).2) := fun y => by
      rw [← hE, Equiv.apply_symm_apply]
    rw [relabel_apply, relabel_apply]
    have h1 : (liftMat E₂ ρ τ).submatrix e' e' = liftMat E (ρ.submatrix e e) τ := by
      ext x y
      simp only [submatrix_apply, liftMat_apply, hE]
    rw [h1, h]
    ext x y
    simp only [submatrix_apply, liftMat_apply, hE', Equiv.symm_apply_apply]

theorem Lifts.optionSome {E : ι' ≃ ι × Z} {K' : KrausMap R' ι' ι'} {K : KrausMap R ι ι}
    (h : K'.Lifts E K) : K'.optionSome.Lifts E K.optionSome := fun ρ τ => by
  rw [optionSome_apply, optionSome_apply, h]

/-- **Lifting is carried along a relabelling of the extra factor.** -/
theorem Lifts.mapZ {Z' : Type*} {E : ι' ≃ ι × Z} {K' : KrausMap R' ι' ι'} {K : KrausMap R ι ι}
    (h : K'.Lifts E K) (f : Z ≃ Z') {E' : ι' ≃ ι × Z'} (hE : ∀ x, E' x = ((E x).1, f (E x).2)) :
    K'.Lifts E' K := fun ρ τ => by
  have hl : ∀ σ : Matrix ι ι ℂ, liftMat E' σ τ = liftMat E σ (τ.submatrix f f) := fun σ => by
    ext x y
    simp only [liftMat_apply, hE, submatrix_apply]
  rw [hl, hl, h]

end KrausMap

end GordieHowe.Quantum

namespace GordieHowe.QROM

open GordieHowe.Quantum ExpandAdv

variable {X Y B C C' : Type} [Fintype X] [DecidableEq X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] (e' : Y ≃ B) (k : ℕ)

namespace ExpandAdv

omit [Inhabited X] [AddCommGroup Y] in
/-- **Lifting is carried to the expansion's registers.** -/
theorem Lifts.liftKraus {V V' Z R R' : Type} [Fintype V] [DecidableEq V] [Fintype V']
    [DecidableEq V'] [Fintype R] [Fintype R'] {σ : V' ≃ V × Z}
    {K' : KrausMap R' (QueryReg V' 1 X Y) (QueryReg V' 1 X Y)}
    {K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)}
    (h : K'.Lifts (QueryAlg.queryAncSplit σ) K) :
    (ExpandAdv.liftKraus k K').Lifts (QueryAlg.queryAncSplit (expAncSplit k σ)) (ExpandAdv.liftKraus k K) :=
  (h.tensorId ((X × Y) × (Fin k → Y)) (E₂ := liftProd (QueryAlg.queryAncSplit σ) _)
    fun _ _ => rfl).relabel fun _ => rfl

end ExpandAdv

end GordieHowe.QROM

namespace GordieHowe.Quantum

variable {X Y O O' : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

open ReprogrammedCircuit (liftEquiv)

/-- The query registers over `V ≃ D × RW` as the factor `D` and the query registers over `RW`. -/
def qdSplit {V D RW : Type} (ξ : V ≃ D × RW) : QueryReg V 1 X Y ≃ D × QueryReg RW 1 X Y where
  toFun p := ((ξ p.1).1, ((ξ p.1).2, p.2))
  invFun q := (ξ.symm (q.1, q.2.1), q.2.2)
  left_inv p := by simp
  right_inv q := by simp

/-- **Test absorption at the level of core algorithms** (route 3′ of the module docstring): `𝒜'` is
`𝒜` followed by a test, written on `𝒜`'s registers and a copy register `Z` (`split`), started blank.
Before the last step the maps of `𝒜'` lift those of `𝒜`; at the last step (the junction) the block
of `𝒜'` at copy value `c` is the test applied to `𝒜`'s last map cut to the basis states whose
`label` is `c`. The test acts on a factor `D` of `𝒜`'s work register (`workSplit`). -/
structure Alg.TestFold (𝒜 : Alg X Y O) (𝒜' : Alg X Y O') (Z D RW : Type) [Fintype Z]
    [DecidableEq Z] [Fintype D] [DecidableEq D] [Fintype RW] [DecidableEq RW] where
  /-- The registers of `𝒜'` as those of `𝒜` and the copy register. -/
  split : 𝒜'.V ≃ 𝒜.V × Z
  /-- The blank content of the copy register. -/
  blank : Z
  depth_eq : 𝒜'.depth = 𝒜.depth
  init_eq : 𝒜'.init.mat =
    liftMat (liftEquiv split) 𝒜.init.mat (Matrix.single blank blank 1)
  step_lifts : ∀ (k : Fin (𝒜'.depth + 1)) (k' : Fin (𝒜.depth + 1)), (k : ℕ) = k' →
    (k' : ℕ) < 𝒜.depth → (𝒜'.step k).Lifts (liftEquiv split) (𝒜.step k')
  /-- The copy value that the junction writes, read from `𝒜`'s work register. -/
  label : 𝒜.V → Z
  /-- The index type of the test's Kraus operators. -/
  TR : Type
  [instTR : Fintype TR]
  /-- The test, on the factor `D`. -/
  test : KrausMap TR D D
  /-- The test on `𝒜`'s query registers. -/
  testCore : KrausMap TR (QueryReg 𝒜.V 1 X Y) (QueryReg 𝒜.V 1 X Y)
  /-- `𝒜`'s work register as the factor the test acts on and the rest. -/
  workSplit : 𝒜.V ≃ D × RW
  testCore_lifts : testCore.Lifts (qdSplit workSplit) test
  junction : ∀ (k : Fin (𝒜'.depth + 1)) (k' : Fin (𝒜.depth + 1)), (k : ℕ) = k' →
    (k' : ℕ) = 𝒜.depth → ∀ ρ c,
      blockAt (liftEquiv split) (𝒜'.step k (liftMat (liftEquiv split) ρ
          (Matrix.single blank blank 1))) c c =
        testCore (cutTo {p | label p.1 = c} (𝒜.step k' ρ))

attribute [instance] Alg.TestFold.instTR

end GordieHowe.Quantum

namespace GordieHowe.Quantum

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] (C : Challenger X Y Req Resp) {A : AdaptiveIAlg X Y Req Resp O} (T : A.QFTest)

open ReprogrammedCircuit (liftEquiv ancLift)

/-- The rest of the composed work register with the reprogramming ancilla, beside the adversary's
registers: the query counter, the challenger's registers and the ancilla. -/
abbrev WorkRest (A : AdaptiveIAlg X Y Req Resp O) (C : Challenger X Y Req Resp) : Type :=
  (Fin (A.budget + 2) × ChallengerRegs X Y Req A.slots C.q C.Coins) × (X × Y × Bool)

instance (A : AdaptiveIAlg X Y Req Resp O) (C : Challenger X Y Req Resp) :
    DecidableEq (WorkRest A C) :=
  @instDecidableEqProd _ _ inferInstance inferInstance

instance (A : AdaptiveIAlg X Y Req Resp O) (C : Challenger X Y Req Resp) :
    DecidableEq (A.toKindAlg.CW C × (X × Y × Bool)) :=
  @instDecidableEqProd _ _ inferInstance inferInstance

/-- The composed work register with the reprogramming ancilla as the adversary's registers and the
rest. -/
def workSplitR : A.toKindAlg.CW C × (X × Y × Bool) ≃ DReg A.W A.width X Y Req Resp × WorkRest A C where
  toFun v := ((A.cntSplit v.1.adv).1, (((A.cntSplit v.1.adv).2, v.1.chal), v.2))
  invFun q := (⟨A.cntSplit.symm (q.1, q.2.1.1), q.2.1.2⟩, q.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The rest of the composed registers with the reprogramming ancilla, beside the adversary's
registers. -/
abbrev TestRest (A : AdaptiveIAlg X Y Req Resp O) (C : Challenger X Y Req Resp) : Type :=
  (Fin (A.budget + 2) × CRest X Y Req A.slots C.q C.Coins) × (X × Y × Bool)

/-- The composed registers with the reprogramming ancilla as the adversary's registers and the
rest. -/
def testSplitR : ReprogrammedQueryReg (A.toKindAlg.CW C) X Y ≃
    DReg A.W A.width X Y Req Resp × TestRest A C where
  toFun p := ((composedSplit C A (ancSplit _ X Y p).1).1,
    ((composedSplit C A (ancSplit _ X Y p).1).2, (ancSplit _ X Y p).2))
  invFun q := (ancSplit _ X Y).symm ((composedSplit C A).symm (q.1, q.2.1), q.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
theorem testOnComposed_lifts : (testOnComposed T C).Lifts (testSplitR C) T.step.toKrausMap :=
  ((lifts_composedLift C A T.step.toKrausMap).tensorId_right (X × Y × Bool)
    (E₂ := rightProd (composedSplit C A) _) fun _ _ => rfl).reindex_left fun _ => rfl

/-- The rest of the registers, regrouped. -/
def restEquiv : TestRest A C ≃ QueryReg (WorkRest A C) 1 X Y where
  toFun r := (((r.1.1, r.1.2.1), r.2), r.1.2.2)
  invFun q := ((q.1.1.1, (q.1.1.2, q.2)), q.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

omit [Nonempty X] [AddGroup Y] [Nonempty Y] in
theorem testOnComposed_lifts_qd :
    (testOnComposed T C).Lifts (qdSplit (workSplitR C)) T.step.toKrausMap :=
  (testOnComposed_lifts C T).mapZ (restEquiv C) fun _ => rfl

/-- **The trace-preserving compositions of `A` and of `A^Π` are related by test absorption**, for a
trace-preserving `A`. -/
noncomputable def testFold (hA : A.TracePreserving) :
    (A.toTPKindAlg.composeBothOut C id).TestFold
      ((A.withTest T.toQTest).toTPKindAlg.composeBothOut C id) A.W (DReg A.W A.width X Y Req Resp)
      (WorkRest A C) where
  split := ancLift (cwCopy T C)
  blank := A.copyBlank
  depth_eq := depth_composeTP_withTest C T hA id id
  init_eq := init_composeTP_withTest C T id id
  step_lifts k k' hkk hk := composeTP_step_lifts C T hA id id k k' hkk hk
  label v := A.outRep v.1.adv.workspace.1
  TR := T.R
  test := T.step.toKrausMap
  testCore := testOnComposed T C
  workSplit := workSplitR C
  testCore_lifts := testOnComposed_lifts_qd C T
  junction k k' hkk hk ρ c := blockAt_composeTP_last C T hA id id k k' hkk hk ρ c

end AdaptiveIAlg

end GordieHowe.Quantum

namespace GordieHowe.QROM

open GordieHowe.Quantum ExpandAdv

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {B Bt C C' : Type} (e : BitStr I J ≃ B) (e' : BitStr I J ≃ Bt)
  (E : Expansion (Bits m) Bt C) (E' : Expansion (Bits m) Bt C') (k : ℕ)

section ExpandLift

variable {V V' Z R R' : Type} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
  [Fintype Z] [DecidableEq Z] [Fintype R] [Fintype R'] {t : ℕ}

omit [DecidableEq I] [DecidableEq J] [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V'] [Fintype Z] [DecidableEq Z] in
/-- **The initial state of the expanded run, lifted.** -/
theorem expInit_liftMat (σ : V' ≃ V × Z)
    (ρ₀ : Matrix (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J)) ℂ)
    (τ : Matrix Z Z ℂ) :
    (liftMat (QueryAlg.queryAncSplit σ) ρ₀ τ ⊗ₖ
        Matrix.single (fresh (X := Bits m) (Y := BitStr I J) k) (fresh k) (1 : ℂ)).submatrix
        (registerSplit k V') (registerSplit k V') =
      liftMat (QueryAlg.queryAncSplit (expAncSplit k σ))
        ((ρ₀ ⊗ₖ Matrix.single (fresh (X := Bits m) (Y := BitStr I J) k) (fresh k) (1 : ℂ)).submatrix
          (registerSplit k V) (registerSplit k V)) τ := by
  ext x y
  simp only [submatrix_apply, kroneckerMap_apply, liftMat_apply, registerSplit, expAncSplit,
    QueryAlg.queryAncSplit_apply, Equiv.coe_fn_mk]
  ring

/-- **Route 3′ (a): before the junction, the expanded run of `A^Π` is the lift of `A`'s**: the
density-matrix runs of the expanded adversaries (`expKraus`) of two families whose maps before
step `t` lift each other along `σ`, from lifted initial states, are lifted up to step `t - 1`, with
the database factor (`simAncSplit`). -/
theorem densityRun_expKraus_liftMat (σ : V' ≃ V × Z) (τ : Matrix Z Z ℂ)
    (K : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J)))
    (K' : Fin (t + 1) → KrausMap R' (QueryReg V' 1 (Bits m) (BitStr I J))
      (QueryReg V' 1 (Bits m) (BitStr I J))) (o : V → C) (o' : V' → C')
    (hK : ∀ i : Fin (t + 1), (i : ℕ) < t → (K' i).Lifts (QueryAlg.queryAncSplit σ) (K i))
    (ρ₀ : Matrix (ExpBasis (X := Bits m) (Y := BitStr I J) k V)
      (ExpBasis (X := Bits m) (Y := BitStr I J) k V) ℂ) :
    ∀ n < t, densityRun e (expKraus e' E' k K' o')
        (liftMat (QueryAlg.queryAncSplit (expAncSplit k σ)) ρ₀ τ) n =
      liftMat (simAncSplit (expAncSplit k σ)) (densityRun e (expKraus e' E k K o) ρ₀ n) τ :=
  densityRun_liftMat e (expAncSplit k σ) τ _ _ (fun i hi => by
    have h1 : (i : ℕ) < t := hi
    unfold expKraus
    rw [dif_pos h1, dif_pos h1]
    exact ((ExpandAdv.Lifts.liftKraus k (hK ⟨i, by omega⟩ h1)).optionSome).liftsAt τ) ρ₀

end ExpandLift

end GordieHowe.QROM

namespace GordieHowe.Quantum

namespace KrausMap

variable {R R' R₂ R₂' ι ι' κ κ' Z : Type*} [Fintype R] [Fintype R'] [Fintype R₂] [Fintype R₂']
  [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype κ] [DecidableEq κ]
  [Fintype κ'] [DecidableEq κ']

theorem LiftsAt.relabel {E : ι' ≃ ι × Z} {τ : Matrix Z Z ℂ} {K' : KrausMap R' ι' ι'}
    {K : KrausMap R ι ι} (h : K'.LiftsAt E τ K) {e' : ι' ≃ κ'} {e : ι ≃ κ} {E₂ : κ' ≃ κ × Z}
    (hE : ∀ x, E₂ (e' x) = (e (E x).1, (E x).2)) : (K'.relabel e').LiftsAt E₂ τ (K.relabel e) :=
  fun ρ => by
    have hE' : ∀ y, E₂ y = (e (E (e'.symm y)).1, (E (e'.symm y)).2) := fun y => by
      rw [← hE, Equiv.apply_symm_apply]
    rw [relabel_apply, relabel_apply]
    have h1 : (liftMat E₂ ρ τ).submatrix e' e' = liftMat E (ρ.submatrix e e) τ := by
      ext x y
      simp only [submatrix_apply, liftMat_apply, hE]
    rw [h1, h]
    ext x y
    simp only [submatrix_apply, liftMat_apply, hE', Equiv.symm_apply_apply]

theorem LiftsAt.optionSome {E : ι' ≃ ι × Z} {τ : Matrix Z Z ℂ} {K' : KrausMap R' ι' ι'}
    {K : KrausMap R ι ι} (h : K'.LiftsAt E τ K) : K'.optionSome.LiftsAt E τ K.optionSome :=
  fun ρ => by rw [optionSome_apply, optionSome_apply, h]

theorem LiftsAt.optionNone {E : ι' ≃ ι × Z} {τ : Matrix Z Z ℂ} {K' : KrausMap Unit ι' ι'}
    {K : KrausMap Unit ι ι} (h : K'.LiftsAt E τ K) (R R' : Type*) [Fintype R] [Fintype R'] :
    (K'.optionNone R').LiftsAt E τ (K.optionNone R) :=
  fun ρ => by rw [optionNone_apply, optionNone_apply, h]

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] in
/-- **A basis permutation that keeps the `Z` coordinate and acts as `π` at `z`** carries the
matrices with the `Z` factor in the state `|z⟩⟨z|`. -/
theorem liftMat_single_submatrix [DecidableEq Z] (E : ι' ≃ ι × Z) (z : Z) {π' : Equiv.Perm ι'}
    {π : Equiv.Perm ι} (hz : ∀ x, (E (π'.symm x)).2 = (E x).2)
    (hπ : ∀ y, π'.symm (E.symm (y, z)) = E.symm (π.symm y, z)) (ρ : Matrix ι ι ℂ) :
    (liftMat E ρ (Matrix.single z z 1)).submatrix π'.symm π'.symm =
      liftMat E (ρ.submatrix π.symm π.symm) (Matrix.single z z 1) := by
  classical
  ext a b
  simp only [submatrix_apply, liftMat_apply, Matrix.single_apply, hz]
  by_cases ha : (E a).2 = z
  · by_cases hb : (E b).2 = z
    · have ea : a = E.symm ((E a).1, z) := by rw [← ha]; simp
      have eb : b = E.symm ((E b).1, z) := by rw [← hb]; simp
      rw [ea, eb, hπ, hπ]
      simp
    · rw [if_neg (fun h => hb h.2.symm), mul_zero, mul_zero]
  · rw [if_neg (fun h => ha h.1.symm), mul_zero, mul_zero]

theorem LiftsAt.permConj_single [DecidableEq Z] {E : ι' ≃ ι × Z} {z : Z} {K' : KrausMap R' ι' ι'}
    {K : KrausMap R ι ι} (h : K'.LiftsAt E (Matrix.single z z 1) K) {π' : Equiv.Perm ι'}
    {π : Equiv.Perm ι} (hz : ∀ x, (E (π'.symm x)).2 = (E x).2)
    (hπ : ∀ y, π'.symm (E.symm (y, z)) = E.symm (π.symm y, z)) :
    (K'.permConj 1 π').LiftsAt E (Matrix.single z z 1) (K.permConj 1 π) := fun ρ => by
  rw [permConj_apply, permConj_apply]
  simp only [Equiv.Perm.one_symm, Equiv.Perm.coe_one, Matrix.submatrix_id_id]
  rw [h, liftMat_single_submatrix E z hz hπ]

end KrausMap

end GordieHowe.Quantum

namespace GordieHowe.QROM

open GordieHowe.Quantum ExpandAdv

namespace ExpandAdv

variable {X Y B C : Type} [Fintype X] [DecidableEq X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] (e' : Y ≃ B) (E : Expansion X B C) (k : ℕ)

omit [Fintype X] [Fintype Y] [DecidableEq Y] in
/-- **The classical steps of the expansion read the output only at the work register.** -/
theorem expPerm_apply_congr {W : Type} {o o₂ : W → C} (j : ℕ)
    (b : ExpBasis (X := X) (Y := Y) k W) (h : o b.1.1 = o₂ b.1.1) :
    expPerm e' E k o j b = expPerm e' E k o₂ j b := by
  obtain ⟨⟨w, s, a⟩, q⟩ := b
  change o w = o₂ w at h
  cases j with
  | zero => simp [expPerm, stashPerm, movePerm, h]
  | succ j =>
    simp only [expPerm, Equiv.trans_apply]
    unfold recordPerm
    split_ifs <;> simp [movePerm, addAnsPerm, subAnsPerm, h]

omit [Inhabited X] [AddCommGroup Y] in
/-- **Lifting at one `τ` is carried to the expansion's registers.** -/
theorem LiftsAt.liftKraus {V V' Z R R' : Type} [Fintype V] [DecidableEq V] [Fintype V']
    [DecidableEq V'] [Fintype R] [Fintype R'] {σ : V' ≃ V × Z} {τ : Matrix Z Z ℂ}
    {K' : KrausMap R' (QueryReg V' 1 X Y) (QueryReg V' 1 X Y)}
    {K : KrausMap R (QueryReg V 1 X Y) (QueryReg V 1 X Y)}
    (h : K'.LiftsAt (QueryAlg.queryAncSplit σ) τ K) :
    (ExpandAdv.liftKraus k K').LiftsAt (QueryAlg.queryAncSplit (expAncSplit k σ)) τ (ExpandAdv.liftKraus k K) :=
  (h.tensorId ((X × Y) × (Fin k → Y)) (E₂ := liftProd (QueryAlg.queryAncSplit σ) _)
    fun _ _ => rfl).relabel fun _ => rfl

end ExpandAdv

theorem perm_symm_slice {ι ι' Z : Type*} (E : ι' ≃ ι × Z) (z : Z) {π' : Equiv.Perm ι'}
    {π : Equiv.Perm ι} (h : ∀ y, π' (E.symm (y, z)) = E.symm (π y, z)) (y : ι) :
    π'.symm (E.symm (y, z)) = E.symm (π.symm y, z) := by
  have := h (π.symm y)
  rw [Equiv.apply_symm_apply] at this
  rw [← this, Equiv.symm_apply_apply]

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {B Bt C : Type} (e : BitStr I J ≃ B) (e' : BitStr I J ≃ Bt)
  (E : Expansion (Bits m) Bt C) (k : ℕ)

/-- **The halting completion of a trace-preserving map acts at flag `false` as the map.** -/
theorem liftsAt_complete {V R : Type} [Fintype V] [DecidableEq V] [Fintype R]
    (K : KrausMap R (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J)))
    (hK : ∑ r, (K.op r)ᴴ * K.op r = 1) :
    ((K.complete.relabel (Alg.haltSys V)).toKrausMap).LiftsAt
      (QueryAlg.queryAncSplit (Equiv.refl (V × Bool))) (Matrix.single false false 1) K :=
  fun ρ => by
    show (K.complete.relabel (Alg.haltSys V)).toKrausMap
        ((ρ ⊗ₖ Matrix.single false false (1 : ℂ)).submatrix (Alg.haltSys V).symm
          (Alg.haltSys V).symm) =
      (K ρ ⊗ₖ Matrix.single false false (1 : ℂ)).submatrix (Alg.haltSys V).symm
        (Alg.haltSys V).symm
    rw [KrausChannel.toKrausMap_apply, KrausChannel.relabel_apply_submatrix,
      KrausMap.complete_apply_kronecker K hK]

variable {O : Type} (A : Alg (Bits m) (BitStr I J) O) (g : Option O → C)

/-- The expansion's classical steps on the coherent registers, at flag `false`, are those on the
core registers reading `A`'s output. -/
theorem expPerm_cohOut_slice (j : ℕ) (y : ExpBasis (X := Bits m) (Y := BitStr I J) k A.V) :
    expPerm e' E k (cohOut A g) j
        ((QueryAlg.queryAncSplit (expAncSplit k (Equiv.refl (A.V × Bool)))).symm (y, false)) =
      (QueryAlg.queryAncSplit (expAncSplit k (Equiv.refl (A.V × Bool)))).symm
        (expPerm e' E k (fun v => g (some (A.out v))) j y, false) := by
  rw [expPerm_apply_congr e' E k (o₂ := fun w => (fun v => g (some (A.out v)))
    ((Equiv.refl (A.V × Bool)) w).1) j _ rfl]
  rw [Equiv.eq_symm_apply]
  have := queryAncSplit_expPerm e' E k (Equiv.refl (A.V × Bool)) (fun v => g (some (A.out v))) j
    ((QueryAlg.queryAncSplit (expAncSplit k (Equiv.refl (A.V × Bool)))).symm (y, false))
  rw [Equiv.apply_symm_apply] at this
  exact this

/-- **The flag stays `false` in the expanded coherent run**: for a trace-preserving `A`, the
density-matrix run of the expanded coherent purification is the run of `A`'s own Kraus maps and the
expansion, with the halting flag `false`. -/
theorem densityRun_expandCoh_eq_liftMat (hA : A.TracePreserving) {n : ℕ} (hn : n ≤ A.depth + k) :
    densityRun e (expandCohDilation A g e' E k).kraus (expandCohDilation A g e' E k).init n =
      liftMat (simAncSplit (expAncSplit k (Equiv.refl (A.V × Bool))))
        (densityRun e (expKraus e' E k A.step fun v => g (some (A.out v)))
          ((A.init.mat ⊗ₖ Matrix.single (fresh (X := Bits m) (Y := BitStr I J) k) (fresh k)
            (1 : ℂ)).submatrix (registerSplit k A.V) (registerSplit k A.V)) n)
        (Matrix.single false false 1) := by
  have hinit : (expandCohDilation A g e' E k).init =
      liftMat (QueryAlg.queryAncSplit (expAncSplit k (Equiv.refl (A.V × Bool))))
        ((A.init.mat ⊗ₖ Matrix.single (fresh (X := Bits m) (Y := BitStr I J) k) (fresh k)
          (1 : ℂ)).submatrix (registerSplit k A.V) (registerSplit k A.V))
        (Matrix.single false false 1) := by
    rw [← expInit_liftMat]
    have hc : (A.cohDilation.mapOut g).init =
        liftMat (QueryAlg.queryAncSplit (Equiv.refl (A.V × Bool))) A.init.mat
          (Matrix.single false false 1) := by
      ext x y
      rfl
    rw [← hc]
    ext x y
    rfl
  rw [hinit]
  have hz : ∀ (j : ℕ) (x : ExpBasis (X := Bits m) (Y := BitStr I J) k (A.V × Bool)),
      (QueryAlg.queryAncSplit (expAncSplit k (Equiv.refl (A.V × Bool)))
        ((expPerm e' E k (cohOut A g) j).symm x)).2 =
      (QueryAlg.queryAncSplit (expAncSplit k (Equiv.refl (A.V × Bool))) x).2 := fun j x => by
    simp only [QueryAlg.queryAncSplit_apply, expAncSplit, Equiv.coe_fn_mk, Equiv.refl_apply,
      expPerm_symm_fst_fst]
  refine densityRun_liftMat e (expAncSplit k (Equiv.refl _)) _ _ _ (n := A.depth + k + 1)
    (fun i hi => ?_) _ n (by omega)
  show (expKraus e' E k (A.cohDilation.mapOut g).kraus (cohOut A g) i).LiftsAt _ _
    (expKraus e' E k A.step (fun v => g (some (A.out v))) i)
  unfold expKraus
  split_ifs with h1 h2
  · exact (ExpandAdv.LiftsAt.liftKraus k (liftsAt_complete _ (hA _))).optionSome
  · exact ((ExpandAdv.LiftsAt.liftKraus k (liftsAt_complete _ (hA _))).permConj_single
      (hz 0) (perm_symm_slice _ false (expPerm_cohOut_slice e' E k A g 0))).optionSome
  · exact (((KrausMap.lifts_identity _).liftsAt _).permConj_single (hz _)
      (perm_symm_slice _ false (expPerm_cohOut_slice e' E k A g _))).optionNone _ _

end GordieHowe.QROM

namespace GordieHowe.Quantum

section Commute

variable {ι ι' D Rr : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [Fintype D] [DecidableEq D] [Fintype Rr] [DecidableEq Rr]

omit [Fintype ι] [DecidableEq ι] in
/-- **The part on `S` of a permuted matrix**: if `π` keeps `S` and agrees with `πc` on `S`, cutting
to `S` after `π` is permuting by `πc` after cutting. -/
theorem cutTo_submatrix_perm {S : Set ι} {π πc : Equiv.Perm ι} (hS : ∀ x, π x ∈ S ↔ x ∈ S)
    (hc : ∀ x ∈ S, π x = πc x) (M : Matrix ι ι ℂ) :
    cutTo S (M.submatrix π.symm π.symm) = (cutTo S M).submatrix πc.symm πc.symm := by
  classical
  have h1 : ∀ y ∈ S, π.symm y = πc.symm y := fun y hy => by
    have hy' : π.symm y ∈ S := (hS _).1 (by simpa using hy)
    rw [Equiv.eq_symm_apply, ← hc _ hy', Equiv.apply_symm_apply]
  have h2 : ∀ y, y ∉ S → πc.symm y ∉ S := fun y hy hc' => by
    apply hy
    have := hc _ hc'
    rw [Equiv.apply_symm_apply] at this
    rw [← this]
    exact (hS _).2 hc'
  ext a b
  simp only [cutTo, submatrix_apply]
  by_cases ha : a ∈ S
  · by_cases hb : b ∈ S
    · rw [if_pos ⟨ha, hb⟩, if_pos ⟨by rw [← h1 a ha]; exact (hS _).1 (by simpa using ha),
        by rw [← h1 b hb]; exact (hS _).1 (by simpa using hb)⟩, h1 a ha, h1 b hb]
    · rw [if_neg (fun h => hb h.2), if_neg (fun h => h2 b hb h.2)]
  · rw [if_neg (fun h => ha h.1), if_neg (fun h => h2 a ha h.1)]

omit [DecidableEq ι] in
/-- **The part on `S` after a conjugation** that never connects a basis state in `S` with one
outside. -/
theorem cutTo_conj {S : Set ι} {G : Matrix ι ι ℂ}
    (hG : ∀ b' b, G b' b ≠ 0 → (b' ∈ S ↔ b ∈ S)) (M : Matrix ι ι ℂ) :
    cutTo S (G * M * Gᴴ) = G * cutTo S M * Gᴴ := by
  classical
  ext a b
  simp only [cutTo, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hz : ∀ x y, (G a x * M x y * star (G b y)) =
      if (a ∈ S ∧ b ∈ S) then G a x * (if x ∈ S ∧ y ∈ S then M x y else 0) * star (G b y)
      else if x ∈ S ∧ y ∈ S then 0 else G a x * M x y * star (G b y) := by
    intro x y
    by_cases hax : G a x = 0
    · simp [hax]
    by_cases hby : G b y = 0
    · simp [hby]
    have h1 := hG a x hax
    have h2 := hG b y hby
    by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp_all
  split_ifs with hab
  · simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
    rw [hz x y, if_pos hab]
  · symm
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun x _ => ?_
    split_ifs with hxy
    · by_cases hax : G a x = 0
      · simp [hax]
      by_cases hby : G b y = 0
      · simp [hby]
      exact absurd ⟨(hG a x hax).2 hxy.1, (hG b y hby).2 hxy.2⟩ hab
    · simp

variable {R R' : Type*} [Fintype R] [Fintype R']

/-- **A lifting map commutes with a basis permutation that keeps the `D` coordinate and moves the
rest of the basis state independently of it.** -/
theorem KrausMap.Lifts.submatrix_perm_comm {χ : ι' ≃ D × Rr} {K' : KrausMap R' ι' ι'}
    {K : KrausMap R D D} (h : K'.Lifts χ K) {π : Equiv.Perm ι'}
    (h1 : ∀ x, (χ (π.symm x)).1 = (χ x).1)
    (h2 : ∀ x x', (χ x).2 = (χ x').2 → (χ (π.symm x)).2 = (χ (π.symm x')).2)
    (X : Matrix ι' ι' ℂ) :
    K' (X.submatrix π.symm π.symm) = (K' X).submatrix π.symm π.symm := by
  have hb : ∀ x d, π.symm (χ.symm (d, (χ x).2)) = χ.symm (d, (χ (π.symm x)).2) := fun x d => by
    rw [Equiv.eq_symm_apply]
    refine Prod.ext ?_ ?_
    · rw [h1]
      simp
    · exact h2 _ _ (by simp)
  have hB : ∀ x y, blockAt χ (X.submatrix π.symm π.symm) (χ x).2 (χ y).2 =
      blockAt χ X (χ (π.symm x)).2 (χ (π.symm y)).2 := fun x y => by
    ext d d'
    simp only [GordieHowe.Quantum.blockAt_apply, submatrix_apply, hb]
  ext x y
  rw [h.apply_apply, submatrix_apply, h.apply_apply, h1, h1, hB]

/-- **A lifting map commutes with a conjugation that is the identity on the `D` coordinate.** -/
theorem KrausMap.Lifts.conj_comm {χ : ι' ≃ D × Rr} {K' : KrausMap R' ι' ι'}
    {K : KrausMap R D D} (h : K'.Lifts χ K) {G : Matrix ι' ι' ℂ} (g : Matrix Rr Rr ℂ)
    (hG : ∀ d' r' d r, G (χ.symm (d', r')) (χ.symm (d, r)) = if d' = d then g r' r else 0)
    (M : Matrix ι' ι' ℂ) :
    K' (G * M * Gᴴ) = G * K' M * Gᴴ := by
  have hK' : ∀ N, K' N = ((K.tensorId Rr) (N.submatrix χ.symm χ.symm)).submatrix χ χ := fun N => by
    rw [h.apply_eq (KrausMap.lifts_reindex_tensorId χ K) N, KrausMap.reindex_apply,
      Equiv.symm_symm]
  have hG' : G = ((1 : Matrix D D ℂ) ⊗ₖ g).submatrix χ χ := by
    ext a b
    have := hG (χ a).1 (χ a).2 (χ b).1 (χ b).2
    simp only [Equiv.symm_apply_apply, Prod.mk.eta] at this
    rw [this, submatrix_apply, kroneckerMap_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hc : ∀ (X : Matrix D D ℂ), (X ⊗ₖ (1 : Matrix Rr Rr ℂ)) * ((1 : Matrix D D ℂ) ⊗ₖ g) =
      ((1 : Matrix D D ℂ) ⊗ₖ g) * (X ⊗ₖ (1 : Matrix Rr Rr ℂ)) := fun X => by
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one]
  set N := M.submatrix χ.symm χ.symm
  set L := (1 : Matrix D D ℂ) ⊗ₖ g
  have hsub : ∀ (P Q U : Matrix (D × Rr) (D × Rr) ℂ),
      (P * Q * U).submatrix χ χ = P.submatrix χ χ * Q.submatrix χ χ * U.submatrix χ χ :=
    fun P Q U => by rw [submatrix_mul_equiv, submatrix_mul_equiv]
  have hMN : M = N.submatrix χ χ := by simp [N]
  rw [hK', hK', hG', conjTranspose_submatrix, hMN, ← hsub, ← hsub]
  simp only [submatrix_submatrix, submatrix_id_id, Equiv.self_comp_symm]
  congr 1
  simp only [KrausMap.apply, KrausMap.tensorId, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h1 := hc (K.op r)
  have h2 : Lᴴ * ((K.op r) ⊗ₖ (1 : Matrix Rr Rr ℂ))ᴴ =
      ((K.op r) ⊗ₖ (1 : Matrix Rr Rr ℂ))ᴴ * Lᴴ := by
    rw [← conjTranspose_mul, ← conjTranspose_mul, h1]
  calc K.op r ⊗ₖ 1 * (L * N * Lᴴ) * (K.op r ⊗ₖ 1)ᴴ
      = (K.op r ⊗ₖ 1 * L) * N * (Lᴴ * (K.op r ⊗ₖ 1)ᴴ) := by simp only [Matrix.mul_assoc]
    _ = (L * (K.op r ⊗ₖ 1)) * N * ((K.op r ⊗ₖ 1)ᴴ * Lᴴ) := by rw [h1, h2]
    _ = _ := by simp only [Matrix.mul_assoc]

end Commute

end GordieHowe.Quantum

namespace GordieHowe.QROM

open GordieHowe.Quantum ExpandAdv

namespace ExpandAdv

variable {X Y B C C₂ : Type} [Fintype X] [DecidableEq X] [Inhabited X] [Fintype Y]
  [DecidableEq Y] [AddCommGroup Y] (e' : Y ≃ B) (E : Expansion X B C) (k : ℕ)

omit [Fintype X] [Fintype Y] [DecidableEq Y] in
/-- **The classical steps of the expansion read the output only through the expansion's next
query**, at the work register. -/
theorem expPerm_congr_next {W : Type} {E₂ : Expansion X B C₂} {o : W → C} {o₂ : W → C₂} (j : ℕ)
    (b : ExpBasis (X := X) (Y := Y) k W) (h : E.next (o b.1.1) = E₂.next (o₂ b.1.1)) :
    expPerm e' E k o j b = expPerm e' E₂ k o₂ j b := by
  obtain ⟨⟨w, s, a⟩, q⟩ := b
  change E.next (o w) = E₂.next (o₂ w) at h
  cases j with
  | zero => simp [expPerm, stashPerm, movePerm, queryAt, prevQuery, h]
  | succ j =>
    simp only [expPerm, Equiv.trans_apply]
    unfold recordPerm
    split_ifs <;> simp [movePerm, addAnsPerm, subAnsPerm, queryAt, prevQuery, h]

omit [Fintype X] [Fintype Y] [DecidableEq Y] in
theorem expPerm_symm_congr_next {W : Type} {E₂ : Expansion X B C₂} {o : W → C} {o₂ : W → C₂}
    (j : ℕ) (b : ExpBasis (X := X) (Y := Y) k W) (h : E.next (o b.1.1) = E₂.next (o₂ b.1.1)) :
    (expPerm e' E k o j).symm b = (expPerm e' E₂ k o₂ j).symm b := by
  rw [Equiv.eq_symm_apply, ← expPerm_congr_next e' E k j _ (by
    rw [expPerm_symm_fst_fst]
    exact h), Equiv.apply_symm_apply]

omit [Fintype X] [Fintype Y] [DecidableEq Y] in
/-- **The classical steps of the expansion over a split work register**, at the block of the
second factor `z`: the steps that read the output at `z`. -/
theorem queryAncSplit_expPerm_at {W V Z : Type} (σ : W ≃ V × Z) (o : W → C) (j : ℕ)
    (b : ExpBasis (X := X) (Y := Y) k W) :
    QueryAlg.queryAncSplit (expAncSplit k σ) (expPerm e' E k o j b) =
      (expPerm e' E k (fun v => o (σ.symm (v, (QueryAlg.queryAncSplit (expAncSplit k σ) b).2))) j
        (QueryAlg.queryAncSplit (expAncSplit k σ) b).1,
        (QueryAlg.queryAncSplit (expAncSplit k σ) b).2) := by
  rw [expPerm_congr_next e' E k (E₂ := E) (o₂ := fun w => (fun v =>
    o (σ.symm (v, (QueryAlg.queryAncSplit (expAncSplit k σ) b).2))) (σ w).1) j b (by
      simp [expAncSplit])]
  have := queryAncSplit_expPerm e' E k σ
    (fun v => o (σ.symm (v, (QueryAlg.queryAncSplit (expAncSplit k σ) b).2))) j b
  exact this

end ExpandAdv

end GordieHowe.QROM

namespace GordieHowe.Quantum

namespace KrausMap

variable {R ι : Type*} [Fintype R] [Fintype ι] [DecidableEq ι] {A : Type*} [Fintype A]
  [DecidableEq A]

theorem tensorId_permConj_identity_apply (π : Equiv.Perm ι) (R' : Type*) [Fintype R']
    (M : Matrix (ι × A) (ι × A) ℂ) :
    ((((KrausMap.identity ι).permConj 1 π).optionNone R').tensorId A) M =
      M.submatrix (π.prodCongr (Equiv.refl A)).symm (π.prodCongr (Equiv.refl A)).symm := by
  have h : ∀ N : Matrix ι ι ℂ, (((KrausMap.identity ι).permConj 1 π).optionNone R') N =
      N.submatrix π.symm π.symm := fun N => by
    rw [optionNone_apply, permConj_apply]
    simp only [Equiv.Perm.one_symm, Equiv.Perm.coe_one, Matrix.submatrix_id_id, id_apply]
  ext ⟨x, a⟩ ⟨y, b⟩
  rw [tensorId_apply_apply]
  exact congrFun (congrFun (h _) x) y

theorem tensorId_permConj_optionSome_apply (L : KrausMap R ι ι) (π : Equiv.Perm ι)
    (M : Matrix (ι × A) (ι × A) ℂ) :
    (((L.permConj 1 π).optionSome).tensorId A) M =
      ((L.tensorId A) M).submatrix (π.prodCongr (Equiv.refl A)).symm
        (π.prodCongr (Equiv.refl A)).symm := by
  have h : ∀ N : Matrix ι ι ℂ, ((L.permConj 1 π).optionSome) N =
      (L N).submatrix π.symm π.symm := fun N => by
    rw [optionSome_apply, permConj_apply]
    simp only [Equiv.Perm.one_symm, Equiv.Perm.coe_one, Matrix.submatrix_id_id]
  ext ⟨x, a⟩ ⟨y, b⟩
  rw [tensorId_apply_apply]
  exact (congrFun (congrFun (h _) x) y).trans (tensorId_apply_apply L M _ _ a b).symm

end KrausMap

end GordieHowe.Quantum

namespace GordieHowe.Quantum

namespace KrausMap

variable {R R' R₂ ι ι' κ κ' Z : Type*} [Fintype R] [Fintype R'] [Fintype R₂] [Fintype ι]
  [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype κ] [DecidableEq κ] [Fintype κ']
  [DecidableEq κ']

/-- **A junction relation is carried through `⊗ 1`.** -/
theorem junction_tensorId {E : ι' ≃ ι × Z} {τ : Matrix Z Z ℂ} {c : Z} {K' : KrausMap R' ι' ι'}
    {K : KrausMap R ι ι} {G : KrausMap R₂ ι ι} {S : Set ι}
    (h : ∀ ρ, blockAt E (K' (liftMat E ρ τ)) c c = G (cutTo S (K ρ))) (A : Type*) [Fintype A]
    [DecidableEq A] {E₂ : ι' × A ≃ (ι × A) × Z} (hE : ∀ x a, E₂ (x, a) = (((E x).1, a), (E x).2))
    (M : Matrix (ι × A) (ι × A) ℂ) :
    blockAt E₂ ((K'.tensorId A) (liftMat E₂ M τ)) c c =
      (G.tensorId A) (cutTo {p | p.1 ∈ S} ((K.tensorId A) M)) := by
  classical
  have hE' : ∀ x a, E₂.symm ((x, a), c) = (E.symm (x, c), a) := fun x a => by
    rw [Equiv.symm_apply_eq, hE]
    simp
  ext ⟨x, a⟩ ⟨y, b⟩
  rw [GordieHowe.Quantum.blockAt_apply, hE', hE', tensorId_apply_apply, tensorId_apply_apply]
  have h1 : (fun k l => liftMat E₂ M τ (k, a) (l, b)) =
      liftMat E (fun k l => M (k, a) (l, b)) τ := by
    ext k l
    simp only [liftMat_apply, hE]
    rfl
  have h2 : (fun k l => cutTo {p : ι × A | p.1 ∈ S} ((K.tensorId A) M) (k, a) (l, b)) =
      cutTo S (K (fun k l => M (k, a) (l, b))) := by
    ext k l
    simp only [cutTo, Set.mem_ofPred_eq]
    rw [tensorId_apply_apply]
  rw [h1, h2]
  have := congrFun (congrFun (h (fun k l => M (k, a) (l, b))) x) y
  rw [GordieHowe.Quantum.blockAt_apply] at this
  exact this

/-- **A junction relation is carried along relabellings.** -/
theorem junction_relabel {E : ι' ≃ ι × Z} {τ : Matrix Z Z ℂ} {c : Z} {K' : KrausMap R' ι' ι'}
    {K : KrausMap R ι ι} {G : KrausMap R₂ ι ι} {S : Set ι}
    (h : ∀ ρ, blockAt E (K' (liftMat E ρ τ)) c c = G (cutTo S (K ρ))) {e' : ι' ≃ κ'}
    {e : ι ≃ κ} {E₂ : κ' ≃ κ × Z} (hE : ∀ x, E₂ (e' x) = (e (E x).1, (E x).2))
    (M : Matrix κ κ ℂ) :
    blockAt E₂ ((K'.relabel e') (liftMat E₂ M τ)) c c =
      (G.relabel e) (cutTo {p | e.symm p ∈ S} ((K.relabel e) M)) := by
  classical
  have hE' : ∀ y, E₂.symm (y, c) = e' (E.symm (e.symm y, c)) := fun y => by
    rw [Equiv.symm_apply_eq, hE]
    simp
  have h1 : (liftMat E₂ M τ).submatrix e' e' = liftMat E (M.submatrix e e) τ := by
    ext x y
    simp only [submatrix_apply, liftMat_apply, hE]
  have h2 : (cutTo {p | e.symm p ∈ S} ((K.relabel e) M)).submatrix e e =
      cutTo S (K (M.submatrix e e)) := by
    ext x y
    simp only [cutTo, submatrix_apply, Set.mem_ofPred_eq, Equiv.symm_apply_apply, relabel_apply]
  ext x y
  rw [GordieHowe.Quantum.blockAt_apply, relabel_apply, relabel_apply, h2, hE', hE', submatrix_apply,
    submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, h1]
  have := congrFun (congrFun (h (M.submatrix e e)) (e.symm x)) (e.symm y)
  rw [GordieHowe.Quantum.blockAt_apply] at this
  exact this

end KrausMap

end GordieHowe.Quantum

namespace GordieHowe.Quantum

theorem KrausMap.Lifts.relabel_left {R R' ι ι' κ' Z : Type*} [Fintype R] [Fintype R'] [Fintype ι]
    [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype κ'] [DecidableEq κ']
    {E : ι' ≃ ι × Z} {K' : KrausMap R' ι' ι'} {K : KrausMap R ι ι} (h : K'.Lifts E K)
    {e' : ι' ≃ κ'} {E₂ : κ' ≃ ι × Z} (hE : ∀ x, E₂ (e' x) = E x) : (K'.relabel e').Lifts E₂ K :=
  fun ρ τ => by
    have hE' : ∀ y, E₂ y = E (e'.symm y) := fun y => by rw [← hE, Equiv.apply_symm_apply]
    rw [relabel_apply]
    have h1 : (liftMat E₂ ρ τ).submatrix e' e' = liftMat E ρ τ := by
      ext x y
      simp only [submatrix_apply, liftMat_apply, hE]
    rw [h1, h]
    ext x y
    simp only [submatrix_apply, liftMat_apply, hE']

end GordieHowe.Quantum

namespace GordieHowe.QROM

open GordieHowe.Quantum ExpandAdv

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  (k : ℕ)

section TestSplit

variable {V D RW : Type}

/-- The expansion's registers over `V ≃ D × RW` as the factor `D` and the expansion's registers
over `RW`. -/
def expTestSplit (ξ : V ≃ D × RW) :
    ExpBasis (X := Bits m) (Y := BitStr I J) k V ≃ D × ExpBasis (X := Bits m) (Y := BitStr I J) k RW where
  toFun b := ((ξ b.1.1).1, (((ξ b.1.1).2, b.1.2), b.2))
  invFun r := ((ξ.symm (r.1, r.2.1.1), r.2.1.2), r.2.2)
  left_inv b := by simp
  right_inv r := by simp

/-- The simulated registers over `V ≃ D × RW` as the factor `D` and the rest. -/
def simTestSplit (ξ : V ≃ D × RW) (t : ℕ) :
    SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k V) I J m t ≃
      D × SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k RW) I J m t where
  toFun b := ((expTestSplit k ξ b.1).1, ((expTestSplit k ξ b.1).2, b.2))
  invFun r := ((expTestSplit k ξ).symm (r.1, r.2.1), r.2.2)
  left_inv b := by simp
  right_inv r := by simp

variable [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype RW] [DecidableEq RW]

omit [Fintype RW] [DecidableEq RW] in
/-- **The test on the simulated registers acts on the factor `D`.** -/
theorem lifts_testSim {TR : Type} [Fintype TR] {ξ : V ≃ D × RW} {T : KrausMap TR D D}
    {testCore : KrausMap TR (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J))}
    (h : testCore.Lifts (qdSplit ξ) T) (t : ℕ) :
    ((liftKraus k testCore).tensorId (Slots I J m t)).Lifts (simTestSplit k ξ t) T :=
  ((((h.tensorId_right ((Bits m × BitStr I J) × (Fin k → BitStr I J))
    (E₂ := rightProd (qdSplit ξ) _) fun _ _ => rfl).mapZ (registerSplit k RW).symm
      (E' := (rightProd (qdSplit ξ) _).trans
        (Equiv.prodCongr (Equiv.refl D) (registerSplit k RW).symm)) fun _ => rfl).relabel_left (E₂ := expTestSplit k ξ) fun _ => rfl).tensorId_right
        (Slots I J m t) (E₂ := simTestSplit k ξ t) fun _ _ => rfl)

end TestSplit

end GordieHowe.QROM

namespace GordieHowe.QROM

open GordieHowe.Quantum ExpandAdv

namespace ExpandAdv

variable {X Y B C : Type} [Fintype X] [DecidableEq X] [Inhabited X] [Fintype Y]
  [DecidableEq Y] [AddCommGroup Y] (e' : Y ≃ B) (E : Expansion X B C) (k : ℕ)

omit [Fintype X] [Fintype Y] [DecidableEq Y] in
/-- **The classical steps of the expansion move the registers other than the work register as a
function of the expansion's next query alone**: at two work registers with the same next query,
they act alike on the rest. -/
theorem expPerm_transport {W : Type} {o : W → C} (j : ℕ) {w w' : W}
    (h : E.next (o w) = E.next (o w')) (r : ((X × Y) × (Fin k → Y)) × (Fin 1 → X × Y)) :
    expPerm e' E k o j ((w', r.1), r.2) =
      ((w', (expPerm e' E k o j ((w, r.1), r.2)).1.2), (expPerm e' E k o j ((w, r.1), r.2)).2) := by
  obtain ⟨⟨s, a⟩, q⟩ := r
  cases j with
  | zero => simp [expPerm, stashPerm, movePerm, queryAt, prevQuery, h]
  | succ j =>
    simp only [expPerm, Equiv.trans_apply]
    unfold recordPerm
    split_ifs <;> simp [movePerm, addAnsPerm, subAnsPerm, queryAt, prevQuery, h]

omit [Fintype X] [Fintype Y] [DecidableEq Y] in
theorem expPerm_symm_transport {W : Type} {o : W → C} (j : ℕ) {w w' : W}
    (h : E.next (o w) = E.next (o w')) (r : ((X × Y) × (Fin k → Y)) × (Fin 1 → X × Y)) :
    (expPerm e' E k o j).symm ((w', r.1), r.2) =
      ((w', ((expPerm e' E k o j).symm ((w, r.1), r.2)).1.2),
        ((expPerm e' E k o j).symm ((w, r.1), r.2)).2) := by
  rw [Equiv.symm_apply_eq]
  set y := (expPerm e' E k o j).symm ((w, r.1), r.2) with hy
  have hw : y.1.1 = w := by rw [hy, expPerm_symm_fst_fst]
  have hP : expPerm e' E k o j y = ((w, r.1), r.2) := by rw [hy, Equiv.apply_symm_apply]
  have := expPerm_transport e' E k (o := o) j (w := y.1.1) (w' := w') (by rw [hw, h]) (y.1.2, y.2)
  rw [this]
  have hy' : ((y.1.1, y.1.2), y.2) = y := rfl
  rw [hy', hP]

end ExpandAdv

end GordieHowe.QROM

namespace GordieHowe.QROM

open GordieHowe.Quantum ExpandAdv

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {B Bt C C' : Type} (e : BitStr I J ≃ B) (e' : BitStr I J ≃ Bt)
  (E : Expansion (Bits m) Bt C) (E' : Expansion (Bits m) Bt C') (k : ℕ)

/-- **The simulated query never changes the work register.** -/
theorem simQueryKernel_work {W : Type} [Fintype W] [DecidableEq W] {t : ℕ}
    {b' b : SimRegister W I J m t} (h : simQueryKernel e W t b' b ≠ 0) : b'.1.1 = b.1.1 := by
  have key := simQueryKernel_simAncSplit e (Equiv.punitProd W).symm
    (simAncSplit (Equiv.punitProd W).symm b')
    (simAncSplit (Equiv.punitProd W).symm b)
  simp only [Equiv.symm_apply_apply] at key
  rw [key, liftKernel] at h
  by_contra hne
  apply h
  rw [if_neg]
  exact fun h' => hne h'

section ExpandBlock

variable {V V' Z D RW R R' TR : Type} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
  [Fintype Z] [DecidableEq Z] [Fintype D] [DecidableEq D] [Fintype RW] [DecidableEq RW]
  [Fintype R] [Fintype R'] [Fintype TR] {t : ℕ}

/-- The simulated basis states whose work register has label `c`. -/
def labelIs (label : V → Z) (c : Z) (t : ℕ) :
    Set (SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k V) I J m t) :=
  {b | label b.1.1.1 = c}

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V'] [Fintype Z] [DecidableEq Z] in
/-- **The expansion's steps on the registers of `A^Π`, at the block of copy value `c`.** -/
theorem blockAt_expPerm (σ : V' ≃ V × Z) (o' : V' → C') (j : ℕ)
    (M : Matrix (SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k V') I J m t)
      (SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k V') I J m t) ℂ) (c : Z) :
    blockAt (simAncSplit (expAncSplit k σ))
        (M.submatrix ((expPerm e' E' k o' j).prodCongr (Equiv.refl _)).symm
          ((expPerm e' E' k o' j).prodCongr (Equiv.refl _)).symm) c c =
      (blockAt (simAncSplit (expAncSplit k σ)) M c c).submatrix
        ((expPerm e' E' k (fun v => o' (σ.symm (v, c))) j).prodCongr (Equiv.refl _)).symm
        ((expPerm e' E' k (fun v => o' (σ.symm (v, c))) j).prodCongr (Equiv.refl _)).symm := by
  refine blockAt_submatrix_perm _
    (fun z => (expPerm e' E' k (fun v => o' (σ.symm (v, z))) j).prodCongr (Equiv.refl _))
    (fun x z => ?_) M c c
  have hf : ∀ y, expPerm e' E' k o' j ((QueryAlg.queryAncSplit (expAncSplit k σ)).symm (y, z)) =
      (QueryAlg.queryAncSplit (expAncSplit k σ)).symm
        (expPerm e' E' k (fun v => o' (σ.symm (v, z))) j y, z) := fun y => by
    rw [Equiv.eq_symm_apply, queryAncSplit_expPerm_at, Equiv.apply_symm_apply]
  have hs := perm_symm_slice _ z hf x.1
  obtain ⟨y, db⟩ := x
  simp only [simAncSplit, ctrlSplit_symm_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Prod.map, Equiv.refl_symm, Equiv.refl_apply]
  exact congrArg (·, db) hs

omit [Fintype V'] [DecidableEq V'] [Fintype Z] [DecidableEq Z] in
/-- **The test and the cut commute with the expansion's steps**: on the basis states with label
`c`, the steps of `A`'s expansion are those of `A^Π`'s at copy value `c`, which act on the rest of
the registers as a function of the rest alone. -/
theorem testCut_expPerm (σ : V' ≃ V × Z) (o : V → C) (o' : V' → C') (label : V → Z)
    (ξ : V ≃ D × RW) {T : KrausMap TR D D}
    {testCore : KrausMap TR (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J))}
    (htest : testCore.Lifts (qdSplit ξ) T)
    (hexpA : ∀ v c, label v = c → E.next (o v) = E'.next (o' (σ.symm (v, c))))
    (hexpD : ∀ c v v', (ξ v).2 = (ξ v').2 →
      E'.next (o' (σ.symm (v, c))) = E'.next (o' (σ.symm (v', c))))
    (j : ℕ) (c : Z)
    (M : Matrix (SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k V) I J m t)
      (SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k V) I J m t) ℂ) :
    ((liftKraus k testCore).tensorId (Slots I J m t)) (cutTo (labelIs k label c t)
        (M.submatrix ((expPerm e' E k o j).prodCongr (Equiv.refl _)).symm
          ((expPerm e' E k o j).prodCongr (Equiv.refl _)).symm)) =
      (((liftKraus k testCore).tensorId (Slots I J m t)) (cutTo (labelIs k label c t) M)).submatrix
        ((expPerm e' E' k (fun v => o' (σ.symm (v, c))) j).prodCongr (Equiv.refl _)).symm
        ((expPerm e' E' k (fun v => o' (σ.symm (v, c))) j).prodCongr (Equiv.refl _)).symm := by
  rw [cutTo_submatrix_perm
    (πc := (expPerm e' E' k (fun v => o' (σ.symm (v, c))) j).prodCongr (Equiv.refl _))
    (fun x => by simp [labelIs, expPerm_fst_fst]) (fun x hx => by
      obtain ⟨b, db⟩ := x
      simp only [Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]
      rw [expPerm_congr_next e' E k (E₂ := E') (o₂ := fun v => o' (σ.symm (v, c))) j b
        (hexpA _ _ hx)])]
  refine (lifts_testSim k htest t).submatrix_perm_comm (fun x => ?_) (fun x x' hx => ?_) _
  · obtain ⟨b, db⟩ := x
    simp [simTestSplit, expTestSplit, Equiv.prodCongr_symm, expPerm_symm_fst_fst]
  · obtain ⟨⟨⟨w, s, a⟩, q⟩, db⟩ := x
    obtain ⟨⟨⟨w', s', a'⟩, q'⟩, db'⟩ := x'
    have hw : (ξ w).2 = (ξ w').2 := congrArg (fun r => r.1.1.1) hx
    have hs : s = s' := congrArg (fun r => r.1.1.2.1) hx
    have ha : a = a' := congrArg (fun r => r.1.1.2.2) hx
    have hq : q = q' := congrArg (fun r => r.1.2) hx
    have hd : db = db' := congrArg (fun r => r.2) hx
    subst hs ha hq hd
    have ht := expPerm_symm_transport e' E' k (o := fun v => o' (σ.symm (v, c))) j
      (hexpD c w w' hw) ((s, a), q)
    simp only [Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map, Equiv.refl_symm,
      Equiv.refl_apply]
    rw [ht]
    have hw0 := expPerm_symm_fst_fst e' E' k (fun v => o' (σ.symm (v, c))) j ((w, s, a), q)
    simp only [simTestSplit, expTestSplit, Equiv.coe_fn_mk, hw0, hw]

omit [Fintype Z] [DecidableEq Z] in
/-- **The test and the cut commute with the simulated query.** -/
theorem testCut_simQuery (label : V → Z) (ξ : V ≃ D × RW) {T : KrausMap TR D D}
    {testCore : KrausMap TR (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J))}
    (htest : testCore.Lifts (qdSplit ξ) T) (c : Z)
    (M : Matrix (SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k V) I J m t)
      (SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k V) I J m t) ℂ) :
    ((liftKraus k testCore).tensorId (Slots I J m t)) (cutTo (labelIs k label c t)
        (Matrix.of (simQueryKernel e (ExpansionRegister (X := Bits m) (Y := BitStr I J) k V) t) * M *
          (Matrix.of (simQueryKernel e (ExpansionRegister (X := Bits m) (Y := BitStr I J) k V) t))ᴴ)) =
      Matrix.of (simQueryKernel e (ExpansionRegister (X := Bits m) (Y := BitStr I J) k V) t) *
        ((liftKraus k testCore).tensorId (Slots I J m t)) (cutTo (labelIs k label c t) M) *
        (Matrix.of (simQueryKernel e (ExpansionRegister (X := Bits m) (Y := BitStr I J) k V) t))ᴴ := by
  rw [cutTo_conj (fun b' b hb => by
    have := simQueryKernel_work e (W := ExpansionRegister (X := Bits m) (Y := BitStr I J) k V) hb
    simp only [labelIs, Set.mem_ofPred_eq, this])]
  refine (lifts_testSim k htest t).conj_comm
    (Matrix.of (simQueryKernel e (ExpansionRegister (X := Bits m) (Y := BitStr I J) k RW) t))
    (fun d' r' d r => ?_) _
  have hχ : ∀ (d : D) (r : SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k RW)
      I J m t), (simTestSplit k ξ t).symm (d, r) =
      (simAncSplit (expAncSplit k (ξ.trans (Equiv.prodComm D RW)))).symm (r, d) := fun d r => rfl
  rw [Matrix.of_apply, hχ, hχ, simQueryKernel_simAncSplit, liftKernel]
  rfl

omit [Fintype Z] in
/-- **The junction on the simulated registers**: the junction relation of the core maps, carried to
the expansion's registers and the database. -/
theorem blockAt_liftKraus_junction (σ : V' ≃ V × Z) (blank : Z)
    {Kl' : KrausMap R' (QueryReg V' 1 (Bits m) (BitStr I J)) (QueryReg V' 1 (Bits m) (BitStr I J))}
    {Kl : KrausMap R (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J))}
    {testCore : KrausMap TR (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J))}
    (label : V → Z) (c : Z)
    (hj : ∀ ρ, blockAt (QueryAlg.queryAncSplit σ) (Kl' (liftMat (QueryAlg.queryAncSplit σ) ρ
        (Matrix.single blank blank 1))) c c = testCore (cutTo {p | label p.1 = c} (Kl ρ)))
    (M : Matrix (SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k V) I J m t)
      (SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k V) I J m t) ℂ) :
    blockAt (simAncSplit (expAncSplit k σ)) (((liftKraus k Kl').tensorId (Slots I J m t))
        (liftMat (simAncSplit (expAncSplit k σ)) M (Matrix.single blank blank 1))) c c =
      ((liftKraus k testCore).tensorId (Slots I J m t))
        (cutTo (labelIs k label c t) (((liftKraus k Kl).tensorId (Slots I J m t)) M)) := by
  have h1 := KrausMap.junction_tensorId hj ((Bits m × BitStr I J) × (Fin k → BitStr I J))
    (E₂ := liftProd (QueryAlg.queryAncSplit σ) _) fun _ _ => rfl
  have h2 := KrausMap.junction_relabel h1 (e' := (registerSplit k V').symm)
    (e := (registerSplit k V).symm) (E₂ := QueryAlg.queryAncSplit (expAncSplit k σ)) fun _ => rfl
  exact KrausMap.junction_tensorId h2 (Slots I J m t) (E₂ := simAncSplit (expAncSplit k σ))
    (fun _ _ => rfl) M

/-- **Route 3′ (b): the expanded run of `A^Π` at copy value `c`**: for families whose maps before
step `t` lift each other, whose last maps satisfy the junction relation, and whose expansions read
the same next queries on the basis states of label `c` (`hexpA`) and read nothing of the factor the
test acts on (`hexpD`), the block at `(c, c)` of the final expanded density-matrix run of `K'`, from
a lifted initial state, is the test applied to the final run of `K` cut to label `c`. -/
theorem blockAt_densityRun_expKraus (σ : V' ≃ V × Z) (blank : Z)
    (K : Fin (t + 1) → KrausMap R (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J)))
    (K' : Fin (t + 1) → KrausMap R' (QueryReg V' 1 (Bits m) (BitStr I J))
      (QueryReg V' 1 (Bits m) (BitStr I J))) (o : V → C) (o' : V' → C') (label : V → Z)
    (ξ : V ≃ D × RW) {T : KrausMap TR D D}
    {testCore : KrausMap TR (QueryReg V 1 (Bits m) (BitStr I J)) (QueryReg V 1 (Bits m) (BitStr I J))}
    (htest : testCore.Lifts (qdSplit ξ) T)
    (hK : ∀ i : Fin (t + 1), (i : ℕ) < t → (K' i).Lifts (QueryAlg.queryAncSplit σ) (K i))
    (hjunc : ∀ ρ c, blockAt (QueryAlg.queryAncSplit σ) (K' (Fin.last t)
        (liftMat (QueryAlg.queryAncSplit σ) ρ (Matrix.single blank blank 1))) c c =
      testCore (cutTo {p | label p.1 = c} (K (Fin.last t) ρ)))
    (hexpA : ∀ v c, label v = c → E.next (o v) = E'.next (o' (σ.symm (v, c))))
    (hexpD : ∀ c v v', (ξ v).2 = (ξ v').2 →
      E'.next (o' (σ.symm (v, c))) = E'.next (o' (σ.symm (v', c))))
    (ρ₀ : Matrix (ExpBasis (X := Bits m) (Y := BitStr I J) k V)
      (ExpBasis (X := Bits m) (Y := BitStr I J) k V) ℂ) (c : Z) :
    blockAt (simAncSplit (expAncSplit k σ)) (densityRun e (expKraus e' E' k K' o')
        (liftMat (QueryAlg.queryAncSplit (expAncSplit k σ)) ρ₀ (Matrix.single blank blank 1))
        (t + k)) c c =
      ((liftKraus k testCore).tensorId (Slots I J m (t + k)))
        (cutTo (labelIs k label c (t + k)) (densityRun e (expKraus e' E k K o) ρ₀ (t + k))) := by
  have hperm : ∀ (j : ℕ) (M' : Matrix
      (SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k V') I J m (t + k))
      (SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k V') I J m (t + k)) ℂ)
      (N : Matrix (SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k V) I J m (t + k))
        (SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k V) I J m (t + k)) ℂ),
      blockAt (simAncSplit (expAncSplit k σ)) M' c c =
        ((liftKraus k testCore).tensorId (Slots I J m (t + k))) (cutTo (labelIs k label c (t + k)) N) →
      blockAt (simAncSplit (expAncSplit k σ))
          (M'.submatrix ((expPerm e' E' k o' j).prodCongr (Equiv.refl _)).symm
            ((expPerm e' E' k o' j).prodCongr (Equiv.refl _)).symm) c c =
        ((liftKraus k testCore).tensorId (Slots I J m (t + k))) (cutTo (labelIs k label c (t + k))
          (N.submatrix ((expPerm e' E k o j).prodCongr (Equiv.refl _)).symm
            ((expPerm e' E k o j).prodCongr (Equiv.refl _)).symm)) := fun j M' N h => by
    rw [blockAt_expPerm, h, testCut_expPerm e' E E' k σ o o' label ξ htest hexpA hexpD]
  refine densityRun_blockAt e (expAncSplit k σ) (Matrix.single blank blank 1)
    (expKraus e' E k K o) (expKraus e' E' k K' o') (n := t) (fun i hi => ?_) c
    (fun N => ((liftKraus k testCore).tensorId (Slots I J m (t + k)))
      (cutTo (labelIs k label c (t + k)) N)) (fun M => ?_)
    (fun j hj M' M h => ?_) (fun M' M h => ?_) ρ₀ (t + k) (by omega)
  · have h1 : (i : ℕ) < t := hi
    unfold expKraus
    rw [dif_pos h1, dif_pos h1]
    exact ((ExpandAdv.Lifts.liftKraus k (hK ⟨i, by omega⟩ h1)).optionSome).liftsAt _
  · rw [KrausMap.stepAt_of_lt _ (by omega), KrausMap.stepAt_of_lt _ (by omega)]
    have hu : ∀ {RR : Type} [Fintype RR] {VV : Type} [Fintype VV] [DecidableEq VV] {CC : Type}
        (EE : Expansion (Bits m) Bt CC) (KK : Fin (t + 1) → KrausMap RR (QueryReg VV 1 (Bits m)
          (BitStr I J)) (QueryReg VV 1 (Bits m) (BitStr I J))) (oo : VV → CC),
        expKraus e' EE k KK oo ⟨t, by omega⟩ =
          ((liftKraus k (KK (Fin.last t))).permConj 1 (expPerm e' EE k oo 0)).optionSome := by
      intros
      unfold expKraus
      rw [dif_neg (by simp), if_pos rfl]
    simp only [hu]
    rw [KrausMap.tensorId_permConj_optionSome_apply, KrausMap.tensorId_permConj_optionSome_apply]
    exact hperm 0 _ _ (blockAt_liftKraus_junction k σ blank label c (hjunc · c) M)
  · by_cases hj' : j < t + k + 1
    · rw [KrausMap.stepAt_of_lt _ hj', KrausMap.stepAt_of_lt _ hj']
      have hu : ∀ {RR : Type} [Fintype RR] {VV : Type} [Fintype VV] [DecidableEq VV] {CC : Type}
          (EE : Expansion (Bits m) Bt CC) (KK : Fin (t + 1) → KrausMap RR (QueryReg VV 1 (Bits m)
            (BitStr I J)) (QueryReg VV 1 (Bits m) (BitStr I J))) (oo : VV → CC),
          expKraus e' EE k KK oo ⟨j, hj'⟩ =
            ((KrausMap.identity _).permConj 1 (expPerm e' EE k oo (j - t))).optionNone RR := by
        intros
        unfold expKraus
        rw [dif_neg (by simp; omega), if_neg (by simp; omega)]
      simp only [hu]
      rw [KrausMap.tensorId_permConj_identity_apply, KrausMap.tensorId_permConj_identity_apply]
      exact hperm _ _ _ h
    · unfold KrausMap.stepAt
      rw [dif_neg hj', dif_neg hj']
      exact h
  · rw [blockAt_simQuery_conj, h, testCut_simQuery e k label ξ htest]

end ExpandBlock

end GordieHowe.QROM

namespace GordieHowe.Quantum

open scoped ENNReal ComplexOrder

section Diag

variable {ι ι' A : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype A]
  [DecidableEq A]

/-- **The density matrix of a vector**: `ψψ*`. -/
def pureMat (ψ : QState ι') : Matrix ι' ι' ℂ :=
  Matrix.of fun i j => ψ i * star (ψ j)

omit [DecidableEq ι'] in
theorem posSemidef_pureMat (ψ : QState ι') : (pureMat ψ).PosSemidef := by
  have h2 : pureMat ψ = reduce (relabel (Equiv.prodPUnit.{0} ι').symm ψ) := by
    ext i j
    simp [pureMat, reduce_apply, relabel_apply]
  rw [h2]
  exact posSemidef_reduce _

omit [DecidableEq A] [DecidableEq ι] [DecidableEq ι'] in
/-- **Tracing out a factor of a density matrix** gives the reduced state. -/
theorem sum_blockAt_pureMat (ζ : ι' ≃ ι × A) (ψ : QState ι') :
    ∑ a, blockAt ζ (pureMat ψ) a a = reduce (relabel ζ ψ) := by
  ext x y
  simp [pureMat, reduce_apply, relabel_apply, Matrix.sum_apply]

omit [Fintype ι'] [DecidableEq ι'] in
/-- The real diagonal entries of a positive semidefinite matrix are nonnegative. -/
theorem _root_.Matrix.PosSemidef.re_diag_nonneg {M : Matrix ι' ι' ℂ} (hM : M.PosSemidef) (i : ι') :
    0 ≤ (M i i).re :=
  (Complex.nonneg_iff.1 (hM.diag_nonneg (i := i))).1

omit [DecidableEq ι] [DecidableEq ι'] [DecidableEq A] in
/-- **Born weights summed over a factor**: the probability of an event of the other factor is read
from the reduced state. -/
theorem sum_born_eq_sum_reduce (ζ : ι' ≃ ι × A) (ψ : QState ι') (g : ι → ℝ≥0∞) :
    ∑ b, g (ζ b).1 * ‖ψ b‖ₑ ^ 2 = ∑ x, g x * ENNReal.ofReal (reduce (relabel ζ ψ) x x).re := by
  rw [← ζ.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [re_reduce_apply_self, ENNReal.ofReal_sum_of_nonneg fun a _ => by positivity, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Equiv.apply_symm_apply, relabel_apply]
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- **A diagonal sum through a lifting map, with the extra factor traced out.** -/
theorem sum_diag_lifts {R R' : Type*} [Fintype R] [Fintype R'] {ζ : ι' ≃ ι × A}
    {K' : KrausMap R' ι' ι'} {K : KrausMap R ι ι} (h : K'.Lifts ζ K) {N : Matrix ι' ι' ℂ}
    (hN : N.PosSemidef) (g : ι → ℝ≥0∞) :
    ∑ b, g (ζ b).1 * ENNReal.ofReal (K' N b b).re =
      ∑ x, g x * ENNReal.ofReal (K (∑ a, blockAt ζ N a a) x x).re := by
  rw [← ζ.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hb : ∀ a, (K (blockAt ζ N a a)).PosSemidef := fun a =>
    K.posSemidef_apply (hN.submatrix _)
  simp only [Equiv.apply_symm_apply, h.apply_apply]
  rw [KrausMap.apply_sum, Matrix.sum_apply, Complex.re_sum,
    ENNReal.ofReal_sum_of_nonneg fun a _ => (hb a).re_diag_nonneg x, Finset.mul_sum]

omit [DecidableEq ι] [DecidableEq ι'] in
/-- **The diagonal of a matrix with a factor in the state `|z⟩⟨z|`**, summed against a weight. -/
theorem sum_diag_liftMat_single (ζ : ι' ≃ ι × A) (M : Matrix ι ι ℂ) (z : A) (g : ι' → ℝ≥0∞) :
    ∑ b, g b * ENNReal.ofReal (liftMat ζ M (Matrix.single z z 1) b b).re =
      ∑ y, g (ζ.symm (y, z)) * ENNReal.ofReal (M y y).re := by
  rw [← ζ.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single z (fun a _ ha => by
    simp [liftMat_apply, Ne.symm ha]) (by simp)]
  simp [liftMat_apply]

omit [DecidableEq ι] [DecidableEq ι'] [DecidableEq A] in
/-- **A diagonal sum by blocks.** -/
theorem sum_diag_blockAt (ζ : ι' ≃ ι × A) (M : Matrix ι' ι' ℂ) (g : ι' → ℝ≥0∞) :
    ∑ b, g b * ENNReal.ofReal (M b b).re =
      ∑ a, ∑ y, g (ζ.symm (y, a)) * ENNReal.ofReal (blockAt ζ M a a y y).re := by
  rw [← ζ.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

end Diag

end GordieHowe.Quantum

namespace GordieHowe.Quantum

open scoped ENNReal ComplexOrder

section CutSum

variable {ι ι' Z A : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype A]
  [DecidableEq A]

omit [Fintype ι] [DecidableEq ι] in
theorem cutTo_eq_zero_of_forall_notMem {S : Set ι} (h : ∀ x, x ∉ S) (M : Matrix ι ι ℂ) :
    cutTo S M = 0 := by
  classical
  ext a b
  simp [cutTo, h a]

omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] in
/-- **Cutting a matrix with a factor in the state `|z⟩⟨z|`** to a set that agrees at `z` with a set
of the other factor. -/
theorem cutTo_liftMat_single [DecidableEq Z] (E : ι' ≃ ι × Z) (z : Z) {S : Set ι'} {S' : Set ι}
    (hS : ∀ y, E.symm (y, z) ∈ S ↔ y ∈ S') (ρ : Matrix ι ι ℂ) :
    cutTo S (liftMat E ρ (Matrix.single z z 1)) = liftMat E (cutTo S' ρ) (Matrix.single z z 1) := by
  classical
  ext a b
  simp only [cutTo, liftMat_apply, Matrix.single_apply]
  by_cases ha : (E a).2 = z
  · by_cases hb : (E b).2 = z
    · have ea : a = E.symm ((E a).1, z) := by rw [← ha]; simp
      have eb : b = E.symm ((E b).1, z) := by rw [← hb]; simp
      have hSa := hS (E a).1
      have hSb := hS (E b).1
      rw [← ea] at hSa
      rw [← eb] at hSb
      simp only [hSa, hSb, ha, hb, and_self, if_true]
      split_ifs <;> simp
    · simp [Ne.symm hb]
  · simp [Ne.symm ha]

end CutSum

end GordieHowe.Quantum

namespace GordieHowe.QROM

open GordieHowe.Quantum ExpandAdv
open scoped ENNReal ComplexOrder

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {B Bt C : Type} (e : BitStr I J ≃ B) (e' : BitStr I J ≃ Bt)
  (E : Expansion (Bits m) Bt C) (k : ℕ)

/-- Decidable equality on the simulated registers of an expansion, assembled from its factors. -/
instance instDecidableEqSimExp {W : Type} [DecidableEq W] {t : ℕ} :
    DecidableEq (SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k W) I J m t) :=
  have : DecidableEq (ExpBasis (X := Bits m) (Y := BitStr I J) k W) := inferInstance
  inferInstance

section FullTest

variable {V TR : Type} [Fintype V] [DecidableEq V] [Fintype TR]

/-- **A map of the core registers on the expansion's registers with the halting flag and the
database**, the identity on the flag, the stash, the answer slots and the database. -/
noncomputable def flagLift (K : KrausMap TR (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J))) (t : ℕ) :
    KrausMap TR (SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k (V × Bool)) I J m t)
      (SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k (V × Bool)) I J m t) :=
  (liftKraus k ((K.tensorId Bool).reindex
    (QueryAlg.queryAncSplit (X := Bits m) (Y := BitStr I J) (Equiv.refl (V × Bool))).symm)).tensorId
      (Slots I J m t)

theorem lifts_flagLift (K : KrausMap TR (QueryReg V 1 (Bits m) (BitStr I J))
      (QueryReg V 1 (Bits m) (BitStr I J))) (t : ℕ) :
    (flagLift k K t).Lifts (simAncSplit (expAncSplit k (Equiv.refl (V × Bool))))
      ((liftKraus k K).tensorId (Slots I J m t)) :=
  (ExpandAdv.Lifts.liftKraus k (KrausMap.lifts_reindex_tensorId _ K)).tensorId (Slots I J m t)
    (E₂ := simAncSplit (expAncSplit k (Equiv.refl (V × Bool)))) fun _ _ => rfl

end FullTest

end GordieHowe.QROM

namespace GordieHowe.QROM

open GordieHowe.Quantum ExpandAdv
open scoped ENNReal ComplexOrder

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {B Bt C : Type} (e : BitStr I J ≃ B) (e' : BitStr I J ≃ Bt)
  (E : Expansion (Bits m) Bt C) (k : ℕ)

section FullTestRun

variable {O TR : Type} [Fintype TR] (A : Alg (Bits m) (BitStr I J) O) (g : Option O → C)

/-- **The test on the registers of the coherent extractor's run**: a map of `A`'s query registers,
the identity on the halting flag, the expansion's registers, the database and the ancilla of the
purification. -/
noncomputable def testFull (testCore : KrausMap TR (QueryReg A.V 1 (Bits m) (BitStr I J))
      (QueryReg A.V 1 (Bits m) (BitStr I J))) :
    KrausMap TR (SimRegister (expandAdv e' E k (A.toQueryAlgCoh.mapOut g)).W I J m (A.depth + k))
      (SimRegister (expandAdv e' E k (A.toQueryAlgCoh.mapOut g)).W I J m (A.depth + k)) :=
  letI : DecidableEq A.HaltAnc := Classical.decEq _
  ((flagLift k testCore (A.depth + k)).tensorId A.HaltAnc).reindex
    (simAncSplit (expandCohDilation A g e' E k).equiv).symm

theorem lifts_testFull (testCore : KrausMap TR (QueryReg A.V 1 (Bits m) (BitStr I J))
      (QueryReg A.V 1 (Bits m) (BitStr I J))) :
    (testFull e' E k A g testCore).Lifts (simAncSplit (expandCohDilation A g e' E k).equiv)
      (flagLift k testCore (A.depth + k)) :=
  letI : DecidableEq A.HaltAnc := Classical.decEq _
  KrausMap.lifts_reindex_tensorId _ _

/-- **The test after the coherent extractor's run, read from the run of `A`'s Kraus maps**: for a
trace-preserving `A`, events of the outcome measured before the test and of the registers after
it have the probability computed from the density-matrix run of `A`'s maps and the expansion, with
the test acting on `A`'s registers. -/
theorem sum_testFull_eq (hA : A.TracePreserving)
    (testCore : KrausMap TR (QueryReg A.V 1 (Bits m) (BitStr I J))
      (QueryReg A.V 1 (Bits m) (BitStr I J))) {Oa : Type} (s : Finset Oa)
    (S : Oa → Set (SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k (A.V × Bool))
      I J m (A.depth + k)))
    (G : Oa → SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k (A.V × Bool))
      I J m (A.depth + k) → ℝ≥0∞) :
    ∑ o ∈ s, ∑ b, G o (simAncSplit (expandCohDilation A g e' E k).equiv b).1 *
        ENNReal.ofReal ((testFull e' E k A g testCore (cutTo
          {b | (simAncSplit (expandCohDilation A g e' E k).equiv b).1 ∈ S o}
          (pureMat (simState e (expandAdv e' E k (A.toQueryAlgCoh.mapOut g)))))) b b).re =
      ∑ o ∈ s, ∑ y, G o ((simAncSplit (expAncSplit k (Equiv.refl (A.V × Bool)))).symm (y, false)) *
        ENNReal.ofReal (((liftKraus k testCore).tensorId (Slots I J m (A.depth + k)))
          (cutTo {y | (simAncSplit (expAncSplit k (Equiv.refl (A.V × Bool)))).symm (y, false) ∈ S o}
            (densityRun e (expKraus e' E k A.step fun v => g (some (A.out v)))
              ((A.init.mat ⊗ₖ Matrix.single (fresh (X := Bits m) (Y := BitStr I J) k) (fresh k)
                (1 : ℂ)).submatrix (registerSplit k A.V) (registerSplit k A.V)) (A.depth + k)))
          y y).re := by
  let : DecidableEq A.HaltAnc := Classical.decEq _
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [sum_diag_lifts (lifts_testFull e' E k A g testCore)
    (posSemidef_cutTo _ (posSemidef_pureMat _))]
  have hb : ∑ a, blockAt (simAncSplit (expandCohDilation A g e' E k).equiv)
      (cutTo {b | (simAncSplit (expandCohDilation A g e' E k).equiv b).1 ∈ S o}
        (pureMat (simState e (expandAdv e' E k (A.toQueryAlgCoh.mapOut g))))) a a =
      cutTo (S o) (reduce (relabel (simAncSplit (expandCohDilation A g e' E k).equiv)
        (simState e (expandAdv e' E k (A.toQueryAlgCoh.mapOut g))))) := by
    rw [← sum_blockAt_pureMat, cutTo_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ext x y
    simp only [GordieHowe.Quantum.blockAt_apply, cutTo, Set.mem_ofPred_eq]
    split_ifs with h1 h2 <;> simp_all
  rw [hb, show simState e (expandAdv e' E k (A.toQueryAlgCoh.mapOut g)) =
      simStage e (expandAdv e' E k (A.toQueryAlgCoh.mapOut g)) (A.depth + k) from rfl,
    reduce_simStage_expandAdv_toQueryAlgCoh e A g e' E k le_rfl,
    densityRun_expandCoh_eq_liftMat e e' E k A g hA le_rfl,
    cutTo_liftMat_single _ false (fun _ => Iff.rfl), lifts_flagLift]
  exact sum_diag_liftMat_single _ _ false _

end FullTestRun

end GordieHowe.QROM

namespace GordieHowe.QROM

open GordieHowe.Quantum ExpandAdv
open scoped ENNReal ComplexOrder

theorem liftEquiv_eq_queryAncSplit {X Y W V Z : Type} (σ : W ≃ V × Z) :
    ReprogrammedCircuit.liftEquiv (X := X) (Y := Y) σ = QueryAlg.queryAncSplit σ :=
  Equiv.ext fun _ => rfl

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {B Bt C C' : Type} (e : BitStr I J ≃ B) (e' : BitStr I J ≃ Bt)
  (E : Expansion (Bits m) Bt C) (E' : Expansion (Bits m) Bt C') (k : ℕ)

section Fold

variable {O O' Z D RW : Type} [Fintype Z] [DecidableEq Z] [Fintype D] [DecidableEq D]
  [Fintype RW] [DecidableEq RW]

/-- **The final run of the expansion of `A^Π`, read blockwise** (route 3′ (b) at the level of core
algorithms): for core algorithms related by test absorption (`Alg.TestFold`) and expansions that
read the same next queries on the basis states of label `c` and nothing of the factor the test acts
on, the diagonal of the final expanded run of `𝒜'`, summed against an event of its work register and
the database, is the sum over copy values `c` of the diagonal of the test applied to the final
expanded run of `𝒜` cut to label `c`. -/
theorem sum_densityRun_testFold (𝒜 : Alg (Bits m) (BitStr I J) O)
    (𝒜' : Alg (Bits m) (BitStr I J) O') (F : 𝒜.TestFold 𝒜' Z D RW) (o : 𝒜.V → C)
    (o' : 𝒜'.V → C')
    (hexpA : ∀ v c, F.label v = c → E.next (o v) = E'.next (o' (F.split.symm (v, c))))
    (hexpD : ∀ c v v', (F.workSplit v).2 = (F.workSplit v').2 →
      E'.next (o' (F.split.symm (v, c))) = E'.next (o' (F.split.symm (v', c))))
    (h' : 𝒜'.V → DB (Bits m) B → ℝ≥0∞) :
    ∑ y', h' y'.1.1.1 (slotsDB e y'.2) * ENNReal.ofReal (densityRun e (expKraus e' E' k 𝒜'.step o')
        ((𝒜'.init.mat ⊗ₖ Matrix.single (fresh (X := Bits m) (Y := BitStr I J) k) (fresh k)
          (1 : ℂ)).submatrix (registerSplit k 𝒜'.V) (registerSplit k 𝒜'.V)) (𝒜'.depth + k)
        y' y').re =
      ∑ c, ∑ y, h' (F.split.symm (y.1.1.1, c)) (slotsDB e y.2) *
        ENNReal.ofReal (((liftKraus k F.testCore).tensorId (Slots I J m (𝒜.depth + k)))
          (cutTo (labelIs k F.label c (𝒜.depth + k)) (densityRun e (expKraus e' E k 𝒜.step o)
            ((𝒜.init.mat ⊗ₖ Matrix.single (fresh (X := Bits m) (Y := BitStr I J) k) (fresh k)
              (1 : ℂ)).submatrix (registerSplit k 𝒜.V) (registerSplit k 𝒜.V)) (𝒜.depth + k)))
          y y).re := by
  obtain ⟨V', d', R', init', step', out'⟩ := 𝒜'
  obtain ⟨split, blank, depth_eq, init_eq, step_lifts, label, TR, test, testCore, workSplit,
    testCore_lifts, junction⟩ := F
  change d' = 𝒜.depth at depth_eq
  subst depth_eq
  change init'.mat = _ at init_eq
  simp only at hexpA hexpD h' ⊢
  rw [sum_diag_blockAt (simAncSplit (expAncSplit k split)), init_eq,
    liftEquiv_eq_queryAncSplit, expInit_liftMat]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun y _ => ?_
  rw [blockAt_densityRun_expKraus e e' E E' k split blank 𝒜.step step' o o' label workSplit
    testCore_lifts (fun i hi => by
      have := step_lifts i i rfl hi
      rwa [liftEquiv_eq_queryAncSplit] at this)
    (fun ρ c => by
      have := junction (Fin.last _) (Fin.last _) rfl rfl ρ c
      rwa [liftEquiv_eq_queryAncSplit] at this) hexpA hexpD]
  rfl

end Fold

end GordieHowe.QROM

namespace GordieHowe.QROM

open GordieHowe.Quantum ExpandAdv
open scoped ENNReal ComplexOrder

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] {m : ℕ}
  {B C : Type} (e : BitStr I J ≃ B) (E : Expansion (Bits m) B C) (k : ℕ)

open Classical in
/-- **The extraction event of the coherent run, read from the run of the core maps**: for a
trace-preserving core algorithm, the probability that the measured output and database of the
coherent extractor's run satisfy `R` is the diagonal of the density-matrix run of its own Kraus
maps and the expansion, summed over the basis states satisfying `R`. -/
theorem simProb_expandCoh_eq {O : Type} (A : Alg (Bits m) (BitStr I J) O) (hA : A.TracePreserving)
    (g : Option O → C) (R : C → DB (Bits m) B → Prop) :
    simProb e (expandAdv e E k (A.toQueryAlgCoh.mapOut g)) R =
      ∑ y, (if R (g (some (A.out y.1.1.1))) (slotsDB e y.2) then 1 else 0) *
        ENNReal.ofReal (densityRun e (expKraus e E k A.step fun v => g (some (A.out v)))
          ((A.init.mat ⊗ₖ Matrix.single (fresh (X := Bits m) (Y := BitStr I J) k) (fresh k)
            (1 : ℂ)).submatrix (registerSplit k A.V) (registerSplit k A.V)) (A.depth + k) y y).re := by
  rw [simProb, simLaw, MeasureTheory.OuterMeasure.map_apply, bornWeight_apply_eq_sum]
  have h1 : ∀ b : SimRegister (expandAdv e E k (A.toQueryAlgCoh.mapOut g)).W I J m (A.depth + k),
      Set.indicator ((fun b : SimRegister (expandAdv e E k (A.toQueryAlgCoh.mapOut g)).W I J m
          (A.depth + k) => ((expandAdv e E k (A.toQueryAlgCoh.mapOut g)).out b.1.1,
            slotsDB e b.2)) ⁻¹' {p | R p.1.out p.2})
        (fun b => ‖simState e (expandAdv e E k (A.toQueryAlgCoh.mapOut g)) b‖ₑ ^ 2) b =
      (fun x : SimRegister (ExpansionRegister (X := Bits m) (Y := BitStr I J) k (A.V × Bool)) I J m
          (A.depth + k) => if R (cohOut A g x.1.1.1) (slotsDB e x.2) then (1 : ℝ≥0∞) else 0)
          (simAncSplit (expandCohDilation A g e E k).equiv b).1 *
        ‖simState e (expandAdv e E k (A.toQueryAlgCoh.mapOut g)) b‖ₑ ^ 2 := fun b => by
    simp only [Set.indicator, Set.mem_preimage, Set.mem_ofPred_eq]
    split_ifs with h2 h3 h3
    · rw [one_mul]
    · exact absurd h2 h3
    · exact absurd h3 h2
    · rw [zero_mul]
  simp_rw [h1]
  rw [sum_born_eq_sum_reduce (simAncSplit (expandCohDilation A g e E k).equiv) _
    (fun x => if R (cohOut A g x.1.1.1) (slotsDB e x.2) then (1 : ℝ≥0∞) else 0), show simState e (expandAdv e E k (A.toQueryAlgCoh.mapOut g)) =
      simStage e (expandAdv e E k (A.toQueryAlgCoh.mapOut g)) (A.depth + k) from rfl,
    reduce_simStage_expandAdv_toQueryAlgCoh e A g e E k le_rfl,
    densityRun_expandCoh_eq_liftMat e e E k A g hA le_rfl, sum_diag_liftMat_single]
  rfl

end GordieHowe.QROM

namespace GordieHowe.Quantum

namespace Circuit

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Every Kraus map of a circuit of the core is trace preserving.** -/
def AllTP : Circuit ι → Prop
  | nil => True
  | kraus K c => (∑ r, (K.op r)ᴴ * K.op r = 1) ∧ AllTP c
  | query c => AllTP c

theorem tp_identity : ∑ r, ((KrausMap.identity ι).op r)ᴴ * (KrausMap.identity ι).op r = 1 := by
  simp [KrausMap.identity]

theorem AllTP.head : ∀ {c : Circuit ι}, AllTP c →
    ∑ r, ((Circuit.head c).K.op r)ᴴ * (Circuit.head c).K.op r = 1
  | nil, _ => tp_identity
  | kraus _ c, ⟨hK, h⟩ => KrausMap.tp_comp (AllTP.head (c := c) h) hK
  | query _, _ => tp_identity

theorem AllTP.tail : ∀ {c : Circuit ι}, AllTP c → AllTP (Circuit.tail c)
  | nil, _ => trivial
  | kraus _ c, ⟨_, h⟩ => AllTP.tail (c := c) h
  | query _, h => h

theorem AllTP.seg {c : Circuit ι} (h : AllTP c) :
    ∀ k, ∑ r, ((Circuit.seg c k).K.op r)ᴴ * (Circuit.seg c k).K.op r = 1
  | 0 => h.head
  | k + 1 => AllTP.seg h.tail k

end Circuit

theorem KrausMap.tp_sigmaEmbed {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (F : Fin n → IndexedKrausMap ι) (k : Fin n)
    (h : ∑ r, ((F k).K.op r)ᴴ * (F k).K.op r = 1) :
    ∑ p, ((KrausMap.sigmaEmbed F k).op p)ᴴ * (KrausMap.sigmaEmbed F k).op p = 1 := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single k]
  · simpa [KrausMap.sigmaEmbed] using h
  · intro j _ hj
    simp [KrausMap.sigmaEmbed, hj]
  · simp

namespace ReprogrammedCircuit

variable {V X Y : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddGroup Y]

/-- **A circuit of trace-preserving maps compiles to one.** -/
theorem AllTP.toCircuit : ∀ {c : ReprogrammedCircuit V X Y}, AllTP c →
    Circuit.AllTP (ReprogrammedCircuit.toCircuit c)
  | nil, _ => trivial
  | kraus _ c, ⟨hK, h⟩ => ⟨KrausMap.tp_tensorId_reindex hK _, AllTP.toCircuit (c := c) h⟩
  | rquery _ c, h => ⟨KrausMap.tp_ofPerm _,
      KrausMap.tp_comp (KrausMap.tp_ofPerm _) (KrausMap.tp_ofPerm _), AllTP.toCircuit (c := c) h⟩

end ReprogrammedCircuit

/-- **The composition of a core algorithm with trace-preserving steps is trace preserving.** -/
theorem KindAlg.StepsTP.tracePreserving_composeBothOut {X Y Req Resp O : Type} [Fintype X]
    [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
    [DecidableEq Resp] [Nonempty X] [AddGroup Y] [Nonempty Y] {B : KindAlg X Y Req Resp O}
    (hB : B.StepsTP) (C : Challenger X Y Req Resp) {O' : Type} (f : B.CW C → O') :
    (B.composeBothOut C f).TracePreserving := fun k =>
  KrausMap.tp_sigmaEmbed _ k ((hB.allTP_fullCircBoth C).toCircuit.seg k)

end GordieHowe.Quantum
