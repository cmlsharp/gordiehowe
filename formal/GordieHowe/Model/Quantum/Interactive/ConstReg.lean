-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.Absorb

@[expose] public section

/-!
# An adversary with a constant classical register

An adversary `B` with a classical register `T` in its workspace, set to `t₀` at the start, whose
steps (`step'`) act on the block `t₀` as `B`'s steps (`Intertwines`): the mixed game of the
adversary with the register is `B`'s, placed at `t₀`.

- `Intertwines e M' M`: `M' * jmat e = jmat e * M`; closed under products, the identity,
  diagonals, submatrices along equivalences and `⊗ 1`.
- `KindAlg.mgRun_of_intertwine`: two kind algorithms whose initial states, Kraus maps and slot
  permutations are intertwined along an injective map, with the same logs, have mixed games placed
  along the map.
- `AdaptiveIAlg.withConst B T t₀ step'`: `B` with the register `T` at `t₀` and the steps `step'`;
  `AdaptiveIAlg.mgRun_withConst`: with `step' k` intertwined with `B.step k` along the placement at
  `t₀` (`insD`), its mixed game is `B`'s placed at `t₀` (`insG`);
  `AdaptiveIAlg.toOuterMeasure_outLaw_withConst`: the law of its composed registers against every
  challenger, with the register dropped (`forgetCW`), is `B`'s.
- `AdaptiveIAlg.withStep`, `AdaptiveIAlg.tpStepOf`: the steps of the trace-preserving form with
  replaced Kraus maps, at `B`'s registers (`toTPKindAlg_withStep_step`, `tpStepOf_step`,
  `tpStepOf_tp`).
- `AdaptiveIAlg.withStep B st`: `B` with the steps `st`. The shapes: `withConst_toShape`
  (`AlgShape.withConstS`), `withStep_toShape` (`B`'s).
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.Quantum

section Intertwine

variable {ι κ ι₀ κ₀ : Type*} [Fintype ι] [Fintype κ] [Fintype ι₀] [Fintype κ₀] [DecidableEq ι]
  [DecidableEq κ] [DecidableEq ι₀] [DecidableEq κ₀]

/-- **`M'` intertwined with `M` along `e`**: `M' * jmat e = jmat e * M`. -/
def Intertwines (e : κ → ι) (M' : Matrix ι ι ℂ) (M : Matrix κ κ ℂ) : Prop :=
  M' * jmat e = jmat e * M

omit [DecidableEq κ] in
theorem intertwines_iff {e : κ → ι} {M' : Matrix ι ι ℂ} {M : Matrix κ κ ℂ} :
    Intertwines e M' M ↔ ∀ i b, M' i (e b) = ∑ a, if e a = i then M a b else 0 := by
  have hl : ∀ i b, (M' * jmat e) i b = M' i (e b) := fun i b => by
    simp only [Matrix.mul_apply, jmat, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single (e b) (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
    simp
  have hr : ∀ i b, (jmat e * M) i b = ∑ a, if e a = i then M a b else 0 := fun i b => by
    simp only [Matrix.mul_apply, jmat, ite_mul, one_mul, zero_mul]
  unfold Intertwines
  constructor
  · intro h i b
    rw [← hl, ← hr, h]
  · intro h
    ext i b
    rw [hl, hr, h]

omit [DecidableEq κ] in
theorem Intertwines.mul {e : κ → ι} {A' B' : Matrix ι ι ℂ} {A B : Matrix κ κ ℂ}
    (hA : Intertwines e A' A) (hB : Intertwines e B' B) : Intertwines e (A' * B') (A * B) := by
  unfold Intertwines at *
  rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]

theorem Intertwines.one (e : κ → ι) : Intertwines e 1 1 := by
  simp [Intertwines]

theorem Intertwines.diagonal {e : κ → ι} {p' : ι → ℂ} {p : κ → ℂ} (h : ∀ a, p' (e a) = p a) :
    Intertwines e (Matrix.diagonal p') (Matrix.diagonal p) := by
  unfold Intertwines
  ext i b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [jmat]
  by_cases hb : e b = i
  · subst hb
    simp [h]
  · simp [hb]

omit [DecidableEq κ] [DecidableEq κ₀] in
/-- **Submatrices along equivalences**: with `f' (e a) = e₀ (f a)` and `g' (e a) = e₀ (g a)`. -/
theorem Intertwines.submatrix {e : κ → ι} {e₀ : κ₀ → ι₀} {M' : Matrix ι₀ ι₀ ℂ}
    {M : Matrix κ₀ κ₀ ℂ} (h : Intertwines e₀ M' M) (f g : κ ≃ κ₀) (f' g' : ι ≃ ι₀)
    (hf : ∀ a, f' (e a) = e₀ (f a)) (hg : ∀ a, g' (e a) = e₀ (g a)) :
    Intertwines e (M'.submatrix f' g') (M.submatrix f g) := by
  rw [intertwines_iff] at *
  intro i b
  simp only [submatrix_apply, hg, h]
  rw [← f.symm.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Equiv.apply_symm_apply]
  have : e₀ a = f' i ↔ e (f.symm a) = i := by
    rw [← f.apply_symm_apply a, ← hf, Equiv.apply_symm_apply, f'.apply_eq_iff_eq]
  exact if_congr this rfl rfl

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem jmat_prodMap (e : κ → ι) (L : Type*) [Fintype L] [DecidableEq L] :
    jmat (Prod.map e (_root_.id : L → L)) = jmat e ⊗ₖ (1 : Matrix L L ℂ) := by
  ext ⟨i, l⟩ ⟨a, l'⟩
  simp only [jmat, Prod.map, _root_.id, kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
  by_cases h1 : e a = i <;> by_cases h2 : l = l' <;> simp [h1, h2, eq_comm]

omit [DecidableEq κ] in
theorem Intertwines.kron_one {e : κ → ι} {M' : Matrix ι ι ℂ} {M : Matrix κ κ ℂ}
    (h : Intertwines e M' M) (L : Type*) [Fintype L] [DecidableEq L] :
    Intertwines (Prod.map e (_root_.id : L → L)) (M' ⊗ₖ (1 : Matrix L L ℂ))
      (M ⊗ₖ (1 : Matrix L L ℂ)) := by
  unfold Intertwines at *
  rw [jmat_prodMap, ← mul_kronecker_mul, ← mul_kronecker_mul, h, Matrix.one_mul]

/-- **Basis permutations intertwined along `e`**: with `π' (e a) = e (π a)`. -/
theorem Intertwines.ofPerm {e : κ → ι} {π' : Equiv.Perm ι} {π : Equiv.Perm κ}
    (h : ∀ a, π' (e a) = e (π a)) (r : Unit) :
    Intertwines e ((KrausMap.ofPerm π').op r) ((KrausMap.ofPerm π).op r) := by
  have hs : ∀ a, π'.symm (e a) = e (π.symm a) := fun a => by
    rw [Equiv.symm_apply_eq, h, Equiv.apply_symm_apply]
  exact (Intertwines.one e).submatrix π.symm (Equiv.refl _) π'.symm (Equiv.refl _) hs
    (fun _ => rfl)

/-- **`M ⊗ 1` is intertwined with `M` along `d ↦ (d, t)`.** -/
theorem Intertwines.kron_one_ket (M : Matrix κ κ ℂ) {L : Type*} [Fintype L] [DecidableEq L]
    (t : L) : Intertwines (fun d => (d, t)) (M ⊗ₖ (1 : Matrix L L ℂ)) M := by
  rw [intertwines_iff]
  rintro ⟨i, l⟩ b
  simp only [kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
  by_cases hl : t = l
  · subst hl
    simp
  · simp [hl, Ne.symm hl]

end Intertwine

/-- Dephasing depends only on which pairs of indices the function identifies. -/
theorem dephase_congr_of_iff {ι L L' : Type*} [DecidableEq L] [DecidableEq L'] {g : ι → L}
    {g' : ι → L'} (h : ∀ a b, g a = g b ↔ g' a = g' b) (σ : Matrix ι ι ℂ) :
    dephase g σ = dephase g' σ := by
  ext a b
  exact if_congr (h a b) rfl rfl

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {ksK ksK' : KindShape X Y Req Resp} {K : KindAlg ksK O} {K' : KindAlg ksK' O} [AddGroup Y] {Ω St : Type} {Q : ℕ} [OracleState St X Y]
  (E : Env Ω Req Resp X Y Q St) (ω : Ω) {e : K.G → K'.G}

theorem mgU_of_intertwine (hinit : K'.mgInitM.mat = embed e K.mgInitM.mat)
    (hgK : ∀ k σ, K'.gK k (embed e σ) = embed e (K.gK k σ))
    (hev : ∀ k a, K'.evPerm E ω k (e a) = e (K.evPerm E ω k a)) :
    ∀ k, K'.mgU E ω k = embed e (K.mgU E ω k)
  | 0 => hinit
  | k + 1 => by
    rw [mgU, mgU, mgU_of_intertwine hinit hgK hev k, hgK]
    exact submatrix_embed (S := Set.univ) (fun a _ => hev k a) (fun a b h => by simp at h)

/-- **Kind algorithms intertwined along a map have placed mixed games**: initial states (`hinit`),
Kraus maps (`hgK`) and slot permutations (`hev`) intertwined along `e`, the same number of steps
(`hn`) and logs identified alike (`hlog`). -/
theorem mgRun_of_intertwine (hn : K'.slots + K'.post = K.slots + K.post)
    (hinit : K'.mgInitM.mat = embed e K.mgInitM.mat)
    (hgK : ∀ k σ, K'.gK k (embed e σ) = embed e (K.gK k σ))
    (hev : ∀ k a, K'.evPerm E ω k (e a) = e (K.evPerm E ω k a))
    (hlog : ∀ a b, K'.logsBelow K'.slots (e a) = K'.logsBelow K'.slots (e b) ↔
      K.logsBelow K.slots a = K.logsBelow K.slots b) :
    K'.mgRun E ω true = embed e (K.mgRun E ω true) := by
  rw [mgRun_deph, mgRun_deph, mgRun_false_eq, mgRun_false_eq, hn,
    mgU_of_intertwine E ω hinit hgK hev, hgK, dephase_embed]
  congr 1
  exact dephase_congr_of_iff hlog _

end KindAlg

namespace AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shB : AlgShape X Y Req Resp} (B : AdaptiveIAlg shB O) (T : Type) [Fintype T] [DecidableEq T]

instance constW.instFintype : Fintype (B.W × T) := instFintypeProd _ _

instance constW.instDecidableEq : DecidableEq (B.W × T) := instDecidableEqProd

instance constW.instDecidableEqDReg : DecidableEq (DReg (B.W × T) B.width X Y Req Resp) :=
  DReg.instDecidableEq

/-- The registers of the adversary with a constant register as those of the adversary and the
register. -/
def constSplit : DReg (B.W × T) B.width X Y Req Resp ≃ DReg B.W B.width X Y Req Resp × T where
  toFun d := (((d.1.1.1, d.1.2), d.2), d.1.1.2)
  invFun p := (((p.1.1.1, p.2), p.1.1.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The adversary with a constant classical register** `T`, at `t₀` from the start, with the
steps `step'`; the kind and the output are read from `B`'s workspace. -/
def withConst (t₀ : T)
    (step' : StepIdx B.slots B.post →
      KrausMap B.R (DReg (B.W × T) B.width X Y Req Resp) (DReg (B.W × T) B.width X Y Req Resp)) :
    AdaptiveIAlg (shB.withConstS T) O where
  kind w := B.kind w.1
  init := MState.reindex (B.constSplit T).symm (B.init.tensorKet t₀)
  step := step'
  out w := B.out w.1

/-- **The adversary with its steps replaced** by `st`. -/
def withStep (st : StepIdx B.slots B.post →
      KrausMap B.R (DReg B.W B.width X Y Req Resp) (DReg B.W B.width X Y Req Resp)) :
    AdaptiveIAlg shB O where
  kind := B.kind
  init := B.init
  step := st
  out := B.out

section FieldLemmas

variable (t₀ : T) (step' : StepIdx B.slots B.post →
    KrausMap B.R (DReg (B.W × T) B.width X Y Req Resp) (DReg (B.W × T) B.width X Y Req Resp))
  (st : StepIdx B.slots B.post →
    KrausMap B.R (DReg B.W B.width X Y Req Resp) (DReg B.W B.width X Y Req Resp))

/-! #### The fields of `withConst` and `withStep`, as equations

Each field of a construction is stated through these, so that a proof about one field never
compares two constructions that differ in another field (the constant `t₀`, the steps). -/

theorem withConst_kind : (B.withConst T t₀ step').kind = fun w => B.kind w.1 := rfl

theorem withConst_init :
    (B.withConst T t₀ step').init = MState.reindex (B.constSplit T).symm (B.init.tensorKet t₀) :=
  rfl

theorem withConst_step : (B.withConst T t₀ step').step = step' := rfl

theorem withConst_out : (B.withConst T t₀ step').out = fun w => B.out w.1 := rfl

theorem withStep_kind : (B.withStep st).kind = B.kind := rfl

theorem withStep_init : (B.withStep st).init = B.init := rfl

theorem withStep_step : (B.withStep st).step = st := rfl

theorem withStep_out : (B.withStep st).out = B.out := rfl

end FieldLemmas

/-- **The steps of the trace-preserving form with the adversary's Kraus maps replaced by `st`**,
typed at the registers of `B`'s trace-preserving form, which read only `B`'s shape: comparing
them with `B`'s steps does not compare the two adversaries. -/
noncomputable def tpStepOf (freeze : Bool)
    (st : StepIdx B.slots B.post → KrausMap B.R (DReg B.W B.width X Y Req Resp)
      (DReg B.W B.width X Y Req Resp)) (k : StepIdx B.slots B.post) :
    KrausMap (B.R ⊕ (B.R ⊕ Fin (B.budget + 2))) B.CReg B.CReg :=
  ((B.withStep st).toTPKindAlg freeze).step k

theorem toTPKindAlg_withStep_step (freeze : Bool)
    (st : StepIdx B.slots B.post → KrausMap B.R (DReg B.W B.width X Y Req Resp)
      (DReg B.W B.width X Y Req Resp)) :
    ((B.withStep st).toTPKindAlg freeze).step = B.tpStepOf freeze st :=
  rfl

theorem tpStepOf_step (freeze : Bool) : B.tpStepOf freeze B.step = (B.toTPKindAlg freeze).step :=
  rfl

/-- **The steps with replaced Kraus maps are trace preserving.** -/
theorem tpStepOf_tp (freeze : Bool)
    (st : StepIdx B.slots B.post → KrausMap B.R (DReg B.W B.width X Y Req Resp)
      (DReg B.W B.width X Y Req Resp)) (k : StepIdx B.slots B.post) :
    ∑ r, ((B.tpStepOf freeze st k).op r)ᴴ * (B.tpStepOf freeze st k).op r = 1 :=
  (B.withStep st).toTPKindAlg_step_tp (freeze := freeze) k

/-- **The shape of the adversary with a constant register** (`AlgShape.withConstS`). -/
theorem withConst_toShape (t₀ : T)
    (step' : StepIdx B.slots B.post →
      KrausMap B.R (DReg (B.W × T) B.width X Y Req Resp) (DReg (B.W × T) B.width X Y Req Resp)) :
    (B.withConst T t₀ step').toShape = B.toShape.withConstS T :=
  rfl

/-- **The adversary with its steps replaced has its shape.** -/
theorem withStep_toShape (st : StepIdx B.slots B.post →
      KrausMap B.R (DReg B.W B.width X Y Req Resp) (DReg B.W B.width X Y Req Resp)) :
    (B.withStep st).toShape = B.toShape :=
  rfl

/-- The placement of the adversary's registers at the register value `t`. -/
def insD (t : T) (d : DReg B.W B.width X Y Req Resp) : DReg (B.W × T) B.width X Y Req Resp :=
  (B.constSplit T).symm (d, t)

variable {T} (t₀ : T)
  (step' : StepIdx B.slots B.post →
    KrausMap B.R (DReg (B.W × T) B.width X Y Req Resp) (DReg (B.W × T) B.width X Y Req Resp))

/-- The placement of the game registers at the register value `t`. -/
def insG (t : T) : B.toKindAlg.G → (B.withConst T t₀ step').toKindAlg.G :=
  fun g => (((AlgShape.CntW.mk (g.1.1.work, t) g.1.1.cnt : (B.withConst T t₀ step').CntW), g.1.2),
    g.2)

theorem insG_injective (t : T) : Function.Injective (B.insG t₀ step' t) := fun _ _ h =>
  congrArg (fun g : (B.withConst T t₀ step').toKindAlg.G =>
    (((AlgShape.CntW.mk g.1.1.work.1 g.1.1.cnt : B.CntW), g.1.2), g.2)) h

/-- The placement of the adversary's registers with its counter at the register value `t`. -/
def insC (t : T) : DReg B.CntW B.width X Y Req Resp →
    DReg (B.withConst T t₀ step').CntW (B.withConst T t₀ step').width X Y Req Resp :=
  fun d => (((AlgShape.CntW.mk (d.1.1.work, t) d.1.1.cnt : (B.withConst T t₀ step').CntW), d.1.2),
    d.2)

theorem cntShift_insC (t : T) (d : DReg B.CntW B.width X Y Req Resp) :
    (B.withConst T t₀ step').cntShift (B.insC t₀ step' t d) = B.insC t₀ step' t (B.cntShift d) := by
  obtain ⟨⟨wc_, rq, rs⟩, qs⟩ := d
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
  simp only [insC, cntShift_apply, AlgShape.CntW.work_mk, AlgShape.CntW.cnt_mk]
  rfl

theorem cntShift_symm_insC (t : T) (d : DReg B.CntW B.width X Y Req Resp) :
    (B.withConst T t₀ step').cntShift.symm (B.insC t₀ step' t d) =
      B.insC t₀ step' t (B.cntShift.symm d) := by
  rw [Equiv.symm_apply_eq, cntShift_insC, Equiv.apply_symm_apply]

/-- **The steps with the counter are intertwined** along the placement at `t₀`. -/
theorem toKindAlg_step_intertwines
    (hstep : ∀ k r, Intertwines (B.insD T t₀) ((step' k).op r) ((B.step k).op r))
    (k : StepIdx B.slots B.post) (r : B.R) :
    Intertwines (B.insC t₀ step' t₀) (((B.withConst T t₀ step').toKindAlg.step k).op r)
      ((B.toKindAlg.step k).op r) := by
  have hC : ∀ d, (B.withConst T t₀ step').cntSplit.symm.symm (B.insC t₀ step' t₀ d) =
      Prod.map (B.insD T t₀) _root_.id (B.cntSplit.symm.symm d) := fun _ => rfl
  have hK := ((hstep k r).kron_one (Fin (B.budget + 2))).submatrix
    B.cntSplit.symm.symm B.cntSplit.symm.symm (B.withConst T t₀ step').cntSplit.symm.symm
    (B.withConst T t₀ step').cntSplit.symm.symm hC hC
  rw [toKindAlg_step_eq, toKindAlg_step_eq]
  by_cases hk : (k : ℕ) < B.slots
  · simp only [hk, show (k : ℕ) < (B.withConst T t₀ step').slots from hk, ↓reduceIte]
    simp only [KrausMap.permConj, KrausMap.restrict, KrausMap.reindex, KrausMap.tensorId]
    exact (Intertwines.mul (Intertwines.diagonal fun _ => rfl) hK).submatrix
      B.cntShift.symm (Equiv.refl _) (B.withConst T t₀ step').cntShift.symm (Equiv.refl _)
      (cntShift_symm_insC B t₀ step' t₀) (fun _ => rfl)
  · simp only [hk, show ¬ (k : ℕ) < (B.withConst T t₀ step').slots from hk, ↓reduceIte]
    exact hK

theorem gK_insG (hstep : ∀ k r, Intertwines (B.insD T t₀) ((step' k).op r) ((B.step k).op r))
    (k : ℕ) (σ : Matrix B.toKindAlg.G B.toKindAlg.G ℂ) :
    (B.withConst T t₀ step').toKindAlg.gK k (embed (B.insG t₀ step' t₀) σ) =
      embed (B.insG t₀ step' t₀) (B.toKindAlg.gK k σ) := by
  unfold KindAlg.gK
  by_cases h : k < B.slots + B.post + 1
  · rw [dite_eq_left (show k < (B.withConst T t₀ step').toKindAlg.slots +
      (B.withConst T t₀ step').toKindAlg.post + 1 from h), dite_eq_left h]
    refine KrausMap.apply_embed_of_intertwine (fun r => ?_) σ
    have hL : ∀ g, (splitLogs.symm.symm (B.insG t₀ step' t₀ g) :
        DReg (B.withConst T t₀ step').CntW (B.withConst T t₀ step').width X Y Req Resp ×
          LogReg Req B.slots) =
        Prod.map (B.insC t₀ step' t₀) _root_.id (splitLogs.symm.symm g) := fun _ => rfl
    exact ((toKindAlg_step_intertwines B t₀ step' hstep _ r).kron_one _).submatrix
      splitLogs.symm.symm splitLogs.symm.symm splitLogs.symm.symm splitLogs.symm.symm hL hL
  · rw [dite_eq_right (show ¬ k < (B.withConst T t₀ step').toKindAlg.slots +
      (B.withConst T t₀ step').toKindAlg.post + 1 from h), dite_eq_right h]

theorem mgInitM_insG :
    (B.withConst T t₀ step').toKindAlg.mgInitM.mat =
      embed (B.insG t₀ step' t₀) B.toKindAlg.mgInitM.mat := by
  unfold KindAlg.mgInitM
  rw [MState.reindex_tensorKet_mat, MState.reindex_tensorKet_mat]
  erw [MState.reindex_tensorKet_mat, MState.reindex_tensorKet_mat, MState.reindex_tensorKet_mat]
  rw [embed_embed, embed_embed, embed_embed, embed_embed]
  rfl

variable [AddGroup Y] {Ω St : Type} {Q : ℕ} [OracleState St X Y] (E : Env Ω Req Resp X Y Q St)
  (ω : Ω)

theorem evPerm_insG (k : ℕ) (a : B.toKindAlg.G) :
    (B.withConst T t₀ step').toKindAlg.evPerm E ω k (B.insG t₀ step' t₀ a) =
      B.insG t₀ step' t₀ (B.toKindAlg.evPerm E ω k a) := by
  obtain ⟨⟨wc_, rq, rs, lg⟩, qs⟩ := a
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
  unfold KindAlg.evPerm
  by_cases hk : k < B.slots
  · rw [dite_eq_left (show k < (B.withConst T t₀ step').toKindAlg.slots from hk), dite_eq_left hk]
    simp only [Equiv.trans_apply, KindAlg.copyG, KindAlg.respG, Env.oraclePerm,
      Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, copyPerm_apply]
    by_cases hw : B.kind w <;>
      (simp [insG, withConst, toKindAlg, hw, respondPerm_apply, queryPermOf_apply]
       <;> erw [respondPerm_apply] <;> simp [hw] <;> erw [queryPermOf_apply] <;> simp [hw]
       <;> exact ⟨rfl, rfl⟩)
  · rw [dite_eq_right (show ¬ k < (B.withConst T t₀ step').toKindAlg.slots from hk), dite_eq_right hk]
    rfl

/-- **The mixed game of the adversary with a constant register is the adversary's, placed at
the register's value**, when its steps are intertwined with the adversary's along the placement
(`hstep`). -/
theorem mgRun_withConst
    (hstep : ∀ k r, Intertwines (B.insD T t₀) ((step' k).op r) ((B.step k).op r)) :
    (B.withConst T t₀ step').toKindAlg.mgRun E ω true =
      embed (B.insG t₀ step' t₀) (B.toKindAlg.mgRun E ω true) :=
  KindAlg.mgRun_of_intertwine E ω rfl (mgInitM_insG B t₀ step') (gK_insG B t₀ step' hstep)
    (evPerm_insG B t₀ step' E ω) fun _ _ => Iff.rfl

/-- The placement of the game registers of the adversary with replaced steps `st` at the register
value `t`. -/
def insGTo (st : StepIdx B.slots B.post →
      KrausMap B.R (DReg B.W B.width X Y Req Resp) (DReg B.W B.width X Y Req Resp)) (t : T) :
    (B.withStep st).toKindAlg.G → (B.withConst T t₀ step').toKindAlg.G :=
  fun g => (((AlgShape.CntW.mk (g.1.1.work, t) g.1.1.cnt : (B.withConst T t₀ step').CntW), g.1.2),
    g.2)

theorem insGTo_injective (st : StepIdx B.slots B.post →
      KrausMap B.R (DReg B.W B.width X Y Req Resp) (DReg B.W B.width X Y Req Resp)) (t : T) :
    Function.Injective (B.insGTo t₀ step' st t) := fun _ _ h =>
  congrArg (fun g : (B.withConst T t₀ step').toKindAlg.G =>
    (((AlgShape.CntW.mk g.1.1.work.1 g.1.1.cnt : (B.withStep st).CntW), g.1.2), g.2)) h

/-- **`mgRun_withConst` against the adversary with replaced steps** `st`. -/
theorem mgRun_withConst_withStep
    (st : StepIdx B.slots B.post →
      KrausMap B.R (DReg B.W B.width X Y Req Resp) (DReg B.W B.width X Y Req Resp))
    (hstep : ∀ k r, Intertwines (B.insD T t₀) ((step' k).op r) ((st k).op r)) :
    (B.withConst T t₀ step').toKindAlg.mgRun E ω true =
      embed (B.insGTo t₀ step' st t₀) ((B.withStep st).toKindAlg.mgRun E ω true) :=
  (B.withStep st).mgRun_withConst t₀ step' E ω hstep

section Law

variable [Nonempty X] [Nonempty Y] (C : Challenger X Y Req Resp)

/-- The composed registers with the constant register dropped. -/
def forgetCW (v : (B.withConst T t₀ step').toKindAlg.CW C) : B.toKindAlg.CW C :=
  ⟨((((v.adv.1.1.1.1, v.adv.1.1.2), v.adv.1.2), v.adv.2) : DReg B.CntW B.width
    X Y Req Resp), v.chal⟩

/-- **The law of the composed registers of the adversary with a constant register**, the register
dropped (`forgetCW`), is the adversary's, when its steps are intertwined with the adversary's
along the placement (`hstep`). -/
theorem toOuterMeasure_outLaw_withConst
    (hstep : ∀ k r, Intertwines (B.insD T t₀) ((step' k).op r) ((B.step k).op r)) (H : X → Y)
    (P : B.toKindAlg.CW C → Prop) :
    (((B.withConst T t₀ step').toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P (B.forgetCW t₀ step' C v)} =
      ((B.toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P v} := by
  classical
  have hite : ∀ (p : Prop) [Decidable p] (x : ℝ), (if p then x else 0) = (if p then 1 else 0) * x :=
    fun p _ x => by split_ifs <;> simp
  rw [KindAlg.toOuterMeasure_outLaw_composeBothOut_id,
    KindAlg.toOuterMeasure_outLaw_composeBothOut_id]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  rw [Finset.sum_congr rfl fun r' _ => hite _ _, Finset.sum_congr rfl fun r _ => hite _ _,
    mgRun_withConst B t₀ step' C.toPureEnv (H, c) hstep,
    embed_diag_of_injective (insG_injective B t₀ step' t₀)]
  rfl

/-- The composed registers with the constant register dropped, as those of the adversary with
replaced steps `st`. -/
def forgetCWTo (st : StepIdx B.slots B.post →
      KrausMap B.R (DReg B.W B.width X Y Req Resp) (DReg B.W B.width X Y Req Resp))
    (v : (B.withConst T t₀ step').toKindAlg.CW C) : (B.withStep st).toKindAlg.CW C :=
  ⟨((((v.adv.1.1.1.1, v.adv.1.1.2), v.adv.1.2), v.adv.2) : DReg B.CntW B.width
    X Y Req Resp), v.chal⟩

/-- **`toOuterMeasure_outLaw_withConst` against the adversary with replaced steps** `st`: the
adversary with a constant register and the steps `step'`, intertwined with `st` (`hstep`), has the
law of `B.withStep st`. -/
theorem toOuterMeasure_outLaw_withConst_withStep
    (st : StepIdx B.slots B.post →
      KrausMap B.R (DReg B.W B.width X Y Req Resp) (DReg B.W B.width X Y Req Resp))
    (hstep : ∀ k r, Intertwines (B.insD T t₀) ((step' k).op r) ((st k).op r)) (H : X → Y)
    (P : (B.withStep st).toKindAlg.CW C → Prop) :
    (((B.withConst T t₀ step').toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P (B.forgetCWTo t₀ step' C st v)} =
      (((B.withStep st).toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v} :=
  (B.withStep st).toOuterMeasure_outLaw_withConst t₀ step' C hstep H P

end Law

end AdaptiveIAlg

end GordieHowe.Quantum
