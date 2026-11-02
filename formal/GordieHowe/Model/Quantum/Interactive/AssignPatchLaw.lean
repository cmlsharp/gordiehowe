-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.AssignPatchSlot

@[expose] public section

/-!
# The mixed game of the patched adversary

The mixed game of `B.patchTag tab out'` against an environment `E` on the tape `ω` is the mixed game
of `B` against an environment `E₁` on the tape `ω₁`, with clean ancillas, placed (`patchPlace`),
when `E₁` is `E` read through the tables `T₁`:

- the reply of `E₁` to logs `lg` is the reply of `E` to the tagged logs `augLogs T₁ lg`
  (`hans`);
- the oracle in force of `E₁` at `lg` is that of `E` at the tagged logs, read through the table
  `T₁ (requests lg)` (`horc`);
- on `B`'s run against `E₁`, after each of `B`'s steps, the table `tab` of the workspace is `T₁` of
  the requests so far (`hinv`, `hinvPost`).

- `patchPend j σ`: the state at the start of step `j`, before the end of the reprogrammed
  queries of the previous slot (`patchAfter j`).
- `slot_patchTag`: one slot.
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.Quantum

theorem submatrix_submatrix_symm_self {ι : Type*} (π : Equiv.Perm ι) (X : Matrix ι ι ℂ) :
    (X.submatrix π π).submatrix π.symm π.symm = X := by
  ext a b
  simp

section EmbedTools

variable {ι κ A Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype A]
  [DecidableEq A] [Fintype Z] [DecidableEq Z]

/-- **Placing and then appending a factor** is placing the product. -/
theorem embed_kronecker (e : ι → κ) (X : Matrix ι ι ℂ) (M : Matrix A A ℂ) :
    embed e X ⊗ₖ M = embed (Prod.map e _root_.id) (X ⊗ₖ M) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [embed, kroneckerMap_apply, Fintype.sum_prod_type, Prod.map, _root_.id, Prod.mk.injEq,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single a (fun c _ hc => Finset.sum_eq_zero fun p' _ =>
    Finset.sum_eq_zero fun c' _ => by simp [hc]) (by simp)]
  refine Finset.sum_congr rfl fun p' _ => ?_
  rw [Finset.sum_eq_single b (fun c' _ hc' => by simp [hc']) (by simp)]
  by_cases h1 : e p = i <;> by_cases h2 : e p' = j <;> simp [h1, h2]

/-- **A factor in a basis state appended** is a placement. -/
theorem kronecker_kronecker_single (ρ : Matrix ι ι ℂ) (M : Matrix A A ℂ) (z : Z) :
    ρ ⊗ₖ (M ⊗ₖ Matrix.single z z 1) = embed (fun p : ι × A => (p.1, (p.2, z))) (ρ ⊗ₖ M) := by
  ext ⟨d, a, t⟩ ⟨d', a', t'⟩
  simp only [embed, kroneckerMap_apply, Fintype.sum_prod_type, Prod.mk.injEq, Matrix.single_apply]
  rw [Finset.sum_eq_single d (fun x _ hx => Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero
    fun x' _ => Finset.sum_eq_zero fun y' _ => by simp [hx]) (by simp)]
  rw [Finset.sum_eq_single a (fun y _ hy => Finset.sum_eq_zero fun x' _ => Finset.sum_eq_zero
    fun y' _ => by simp [hy]) (by simp)]
  rw [Finset.sum_eq_single d' (fun x' _ hx' => Finset.sum_eq_zero fun y' _ => by simp [hx'])
    (by simp)]
  rw [Finset.sum_eq_single a' (fun y' _ hy' => by simp [hy']) (by simp)]
  by_cases h1 : z = t <;> by_cases h2 : z = t' <;> simp [h1, h2, eq_comm]

end EmbedTools

namespace AdaptiveIAlg

variable {X Y Req Resp O O' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shB : AlgShape X Y Req Resp} (B : AdaptiveIAlg shB O) (tab : B.W → X → Option Y) (out' : B.W → O')
  [AddGroup Y] [Nonempty X] [Nonempty Y] (T₁ : List Req → X → Option Y)

theorem patchGamePerm_trans (π τ : Equiv.Perm B.PatchReg) :
    B.patchGamePerm tab out' (π.trans τ) =
      (B.patchGamePerm tab out' π).trans (B.patchGamePerm tab out' τ) :=
  Equiv.ext fun _ => rfl

/-- The exchanges with the ancillas on the query branches, on `B`'s game registers. -/
def liftS : Equiv.Perm (B.toKindAlg.G × AncReg X Y B.width) :=
  liftPairs fun v : B.BV => if !B.kind v.1.work then ancSwap (tab v.1.work) else Equiv.refl _

/-- The end of the reprogrammed queries on the query branches, on `B`'s game registers. -/
def liftF : Equiv.Perm (B.toKindAlg.G × AncReg X Y B.width) :=
  liftPairs fun v : B.BV => if !B.kind v.1.work then
    (ancSwap (tab v.1.work)).trans (ancAdd fun x => (tab v.1.work x).getD 0) else Equiv.refl _

/-- **The state at the start of step `j`**: `σ` with clean ancillas, placed, before the
permutation after slot `j - 1`. -/
noncomputable def patchPend (j : ℕ) (σ : Matrix B.toKindAlg.G B.toKindAlg.G ℂ) :
    Matrix (B.patchTag tab out').toKindAlg.G (B.patchTag tab out').toKindAlg.G ℂ :=
  (embed (B.patchPlace tab out' (fun _ _ => none) T₁) (σ ⊗ₖ ancMat KindAlg.x₀)).submatrix
    (B.patchGamePerm tab out' (B.patchAfter tab j)) (B.patchGamePerm tab out' (B.patchAfter tab j))

/-- **Step `k` on the state at its start** is `B`'s step `k` placed, before the permutation before
slot `k`. -/
theorem liftG_patchPend (k : StepIdx B.slots B.post) (σ : Matrix B.toKindAlg.G B.toKindAlg.G ℂ) :
    (B.patchTag tab out').toKindAlg.liftG k (B.patchPend tab out' T₁ k σ) =
      (embed (B.patchPlace tab out' (fun _ _ => none) T₁)
        ((B.toKindAlg.liftG k σ) ⊗ₖ ancMat KindAlg.x₀)).submatrix
        (B.patchGamePerm tab out' (B.patchBefore tab k)).symm
        (B.patchGamePerm tab out' (B.patchBefore tab k)).symm := by
  rw [patchTag_liftG_apply, patchPend, submatrix_submatrix_symm_self, patchGameStep_embed,
    KrausMap.tensorId_apply]

omit [Nonempty X] [Nonempty Y] in
theorem copyE_liftS (k : Fin B.slots) (x : B.toKindAlg.G × AncReg X Y B.width) :
    (B.toKindAlg.copyG k).prodCongr (Equiv.refl _) (B.liftS tab x) =
      B.liftS tab ((B.toKindAlg.copyG k).prodCongr (Equiv.refl _) x) := by
  obtain ⟨⟨⟨wc_, rq, rs, lg⟩, qs⟩, a⟩ := x
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
  by_cases hk : B.kind w = true
  · simp [liftS, liftPairs_apply, KindAlg.copyG, copyPerm_apply, toKindAlg, AlgShape.CntW.work_mk, AlgShape.CntW.cnt_mk, hk]
  · have hk' : B.kind w = false := by simpa using hk
    simp [liftS, liftPairs_apply, KindAlg.copyG, copyPerm_apply, toKindAlg, AlgShape.CntW.work_mk, AlgShape.CntW.cnt_mk, hk']

theorem respE_liftS {Ω₁ St₁ : Type} {Q₁ : ℕ} [OracleState St₁ X Y] (E₁ : Env Ω₁ Req Resp X Y Q₁ St₁)
    (ω₁ : Ω₁) (k : Fin B.slots) (x : B.toKindAlg.G × AncReg X Y B.width) :
    (B.toKindAlg.respG E₁ ω₁ k).prodCongr (Equiv.refl _) (B.liftS tab x) =
      B.liftS tab ((B.toKindAlg.respG E₁ ω₁ k).prodCongr (Equiv.refl _) x) := by
  obtain ⟨⟨⟨wc_, rq, rs, lg⟩, qs⟩, a⟩ := x
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
  by_cases hk : B.kind w = true
  · simp [liftS, liftPairs_apply, KindAlg.respG, respondPerm_apply, toKindAlg, AlgShape.CntW.work_mk, AlgShape.CntW.cnt_mk, hk]
  · have hk' : B.kind w = false := by simpa using hk
    simp [liftS, liftPairs_apply, KindAlg.respG, respondPerm_apply, toKindAlg, AlgShape.CntW.work_mk, AlgShape.CntW.cnt_mk, hk']

omit [AddGroup Y] [Nonempty X] [Nonempty Y] in
theorem copyG_mem_patchInv (k : Fin B.slots) {g : B.toKindAlg.G} (hg : g ∈ B.patchInv tab T₁ k) :
    B.toKindAlg.copyG k g ∈ B.patchInv tab T₁ k := by
  obtain ⟨⟨wc_, rq, rs, lg⟩, qs⟩ := g
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
  simp only [patchInv, Set.mem_setOf_eq, AlgShape.CntW.work_mk] at hg ⊢
  by_cases hk : B.kind w = true
  · simp only [KindAlg.copyG, Equiv.prodCongr_apply, Prod.map, copyPerm_apply, toKindAlg, AlgShape.CntW.work_mk, AlgShape.CntW.cnt_mk, hk,
      ite_true]
    rw [hg]
    exact congrArg T₁ (requestsBefore_congr fun k' hk' =>
      (Function.update_of_ne (fun e => by subst e; omega) _ _).symm)
  · simp only [KindAlg.copyG, Equiv.prodCongr_apply, Prod.map, copyPerm_apply, toKindAlg, AlgShape.CntW.work_mk, AlgShape.CntW.cnt_mk, hk]
    simpa using hg

omit [Nonempty X] [Nonempty Y] in
theorem respG_mem_patchInv {Ω₁ St₁ : Type} {Q₁ : ℕ} [OracleState St₁ X Y]
    (E₁ : Env Ω₁ Req Resp X Y Q₁ St₁) (ω₁ : Ω₁) (k : Fin B.slots) (j : ℕ) {g : B.toKindAlg.G}
    (hg : g ∈ B.patchInv tab T₁ j) : B.toKindAlg.respG E₁ ω₁ k g ∈ B.patchInv tab T₁ j := by
  obtain ⟨⟨wc_, rq, rs, lg⟩, qs⟩ := g
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
  simp only [patchInv, Set.mem_setOf_eq, AlgShape.CntW.work_mk] at hg ⊢
  by_cases hk : B.kind w = true
  · simpa [KindAlg.respG, respondPerm_apply, toKindAlg, AlgShape.CntW.work_mk, AlgShape.CntW.cnt_mk, hk] using hg
  · simpa [KindAlg.respG, respondPerm_apply, toKindAlg, AlgShape.CntW.work_mk, AlgShape.CntW.cnt_mk, hk] using hg

variable {Ω St : Type} {Q : ℕ} [OracleState St X Y] (E : Env Ω (Req × (X → Option Y)) Resp X Y Q St)
  (ω : Ω) {Ω₁ St₁ : Type} {Q₁ : ℕ} [OracleState St₁ X Y] (E₁ : Env Ω₁ Req Resp X Y Q₁ St₁)
  (ω₁ : Ω₁)

/-- The queries of a slot on the placed registers, as a lift. -/
def liftO : Equiv.Perm (B.toKindAlg.G × AncReg X Y B.width) :=
  liftPairs fun v : B.BV => ancAdd (if B.kind v.1.work then 0 else E.oracle ω (augLogs T₁ v.2.2.2))

/-- **The reprogrammed queries of a slot**: the exchanges, the queries, the end, on clean
ancillas, are the queries to `E`'s oracle at the tagged logs read through the workspace table, on
the query branches. -/
theorem kronecker_liftS_liftO_liftF (ρ : Matrix B.toKindAlg.G B.toKindAlg.G ℂ) :
    (((ρ ⊗ₖ ancMat KindAlg.x₀).submatrix (B.liftS tab).symm (B.liftS tab).symm).submatrix
      (B.liftO T₁ E ω).symm (B.liftO T₁ E ω).symm).submatrix (B.liftF tab).symm (B.liftF tab).symm =
      (ρ.submatrix (queryPermOf fun v : B.BV => if B.kind v.1.work then 0 else
          reprogT (tab v.1.work) (E.oracle ω (augLogs T₁ v.2.2.2))).symm
        (queryPermOf fun v : B.BV => if B.kind v.1.work then 0 else
          reprogT (tab v.1.work) (E.oracle ω (augLogs T₁ v.2.2.2))).symm) ⊗ₖ
        ancMat (n := B.width) KindAlg.x₀ := by
  rw [← submatrix_trans_symm, ← submatrix_trans_symm, liftS, liftO, liftF, liftPairs_trans,
    liftPairs_trans]
  refine kronecker_ancMat_submatrix_liftPairs _ _ _ (fun v p => ?_) (fun v p hf => ?_) ρ
  · by_cases hk : B.kind v.1.work = true
    · simp [hk, ancAdd_symm_apply]
    · have hk' : B.kind v.1.work = false := by simpa using hk
      simp only [hk', Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
      exact ⟨ancPerm_symm_anc_fst (tab v.1.work) _ p, ancPerm_symm_flag (tab v.1.work) _ p⟩
  · by_cases hk : B.kind v.1.work = true
    · simp [hk, ancAdd_symm_apply]
    · have hk' : B.kind v.1.work = false := by simpa using hk
      simp only [hk', Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
      exact ancPerm_symm_sys (tab v.1.work) _ p hf

/-- **One slot of the patched mixed game** is one slot of `B`'s mixed game against `E₁`, placed
(module docstring), on matrices whose logs from slot `k` on are blank and that are dephased in the
logs below `k`. -/
theorem slot_patchTag
    (hans : ∀ (lg : LogReg Req B.slots) k, E.answer ω (augLogs T₁ lg) k = E₁.answer ω₁ lg k)
    (horc : ∀ lg : LogReg Req B.slots,
      E₁.oracle ω₁ lg = reprogT (T₁ (requests lg)) (E.oracle ω (augLogs T₁ lg)))
    (k : Fin B.slots) {σ : Matrix B.toKindAlg.G B.toKindAlg.G ℂ}
    (hσ : SuppIn (B.toKindAlg.blankFrom k) σ) (hd : dephase (B.toKindAlg.logsBelow k) σ = σ)
    (hinv : SuppIn (B.patchInv tab T₁ k) (B.toKindAlg.liftG (slotStep k) σ)) :
    (Circuit.kraus ((B.patchTag tab out').toKindAlg.liftG (slotStep k))
        ((B.patchTag tab out').toKindAlg.eventCirc E ω k true)).run (Equiv.refl _)
        (B.patchPend tab out' T₁ k σ) =
      B.patchPend tab out' T₁ (k + 1) ((Circuit.kraus (B.toKindAlg.liftG (slotStep k))
        (B.toKindAlg.eventCirc E₁ ω₁ k true)).run (Equiv.refl _) σ) := by
  simp only [KindAlg.eventCirc, Circuit.run, ite_true, KrausMap.ofPerm_apply,
    KrausMap.measureFn_apply]
  rw [show B.patchPend tab out' T₁ (k : ℕ) σ =
    B.patchPend tab out' T₁ ((slotStep k : StepIdx B.slots B.post) : ℕ) σ from rfl,
    liftG_patchPend]
  set τ := B.toKindAlg.liftG (slotStep k) σ with hτdef
  have hτb : SuppIn (B.toKindAlg.blankFrom k) τ := KindAlg.SuppIn.liftG B.toKindAlg hσ _
  have hτd : dephase (B.toKindAlg.logsBelow k) τ = τ := by
    rw [hτdef, ← KrausMap.apply_dephase (B.toKindAlg.blockDiag_liftG_logsBelow _ _), hd]
  have hbefore : B.patchBefore tab ((slotStep k : StepIdx B.slots B.post) : ℕ) =
      (B.tagP tab B.kind).trans (B.swapP tab fun w => !B.kind w) := by
    simp [patchBefore, AlgShape.patchBefore, k.2]
  have hafter : B.patchAfter tab ((k : ℕ) + 1) =
      (B.tagP tab B.kind).trans (B.finishP tab fun w => !B.kind w) := by
    simp [patchAfter, AlgShape.patchAfter, k.2]
  set M := ancMat (Y := Y) (n := B.width) (KindAlg.x₀ : X)
  set copyE := (B.toKindAlg.copyG k).prodCongr (Equiv.refl (AncReg X Y B.width))
  set respE := (B.toKindAlg.respG E₁ ω₁ k).prodCongr (Equiv.refl (AncReg X Y B.width))
  -- the support of the state after `B`'s step, with the ancillas
  have hX1 : SuppIn (Prod.fst ⁻¹' B.toKindAlg.blankFrom k)
      ((τ ⊗ₖ M).submatrix (B.liftS tab).symm (B.liftS tab).symm) :=
    (hτb.kronecker_fst M).submatrix_perm fun a ha => ha
  have hX1d : dephase (B.toKindAlg.logsBelow k ∘ Prod.fst)
      (((τ ⊗ₖ M).submatrix (B.liftS tab).symm (B.liftS tab).symm).submatrix copyE.symm copyE.symm) =
      ((τ ⊗ₖ M).submatrix (B.liftS tab).symm (B.liftS tab).symm).submatrix copyE.symm
        copyE.symm := by
    rw [dephase_submatrix_of_comp (π := copyE) (fun a => B.toKindAlg.logsBelow_copyG k le_rfl a.1),
      dephase_submatrix_of_comp (π := B.liftS tab) (fun a => rfl), dephase_kronecker_fst, hτd]
  rw [hbefore, patchGamePerm_trans, submatrix_trans_symm,
    submatrix_embed_of_mem (S := Prod.fst ⁻¹' B.patchInv tab T₁ k)
      (fun x hx => B.gamePerm_tagP_place tab out' T₁ k hx) (hinv.kronecker_fst M),
    submatrix_embed (π' := B.liftS tab) (S := Set.univ)
      (fun x _ => B.gamePerm_swapP_place tab out' T₁ _ _ x) (fun a b h => by simp at h),
    submatrix_embed (π' := copyE) (S := Prod.fst ⁻¹' B.toKindAlg.blankFrom k)
      (fun x hx => B.copyG_place tab out' T₁ k hx) hX1,
    B.dephase_place tab out' T₁ k _ hX1d,
    submatrix_embed (π' := respE) (S := Set.univ)
      (fun x _ => B.respG_place tab out' T₁ E ω E₁ ω₁ k _ (fun _ _ _ _ _ => rfl) (hans · k) x)
      (fun a b h => by simp at h),
    submatrix_embed (π' := B.liftO T₁ E ω) (S := Set.univ)
      (fun x _ => B.oraclePerm_place tab out' T₁ E ω _ x) (fun a b h => by simp at h)]
  -- the supports after the copy and the reply
  have hρ₃ : SuppIn (B.toKindAlg.TSet k ∩ B.patchInv tab T₁ k)
      ((dephase (B.toKindAlg.logAt k) (τ.submatrix (B.toKindAlg.copyG k).symm
        (B.toKindAlg.copyG k).symm)).submatrix (B.toKindAlg.respG E₁ ω₁ k).symm
        (B.toKindAlg.respG E₁ ω₁ k).symm) := by
    refine SuppIn.inter ?_ ?_
    · exact ((hτb.submatrix_perm fun a ha =>
        B.toKindAlg.copyG_mem_TSet k ha).dephase _).submatrix_perm
        fun a ha => B.respG_mem_TSet' E₁ ω₁ k ha
    · exact ((hinv.submatrix_perm fun a ha =>
        B.copyG_mem_patchInv tab T₁ k ha).dephase _).submatrix_perm
        fun a ha => B.respG_mem_patchInv tab T₁ E₁ ω₁ k k ha
  have hZ : SuppIn (Prod.fst ⁻¹' B.patchInv tab T₁ k)
      (((dephase (B.toKindAlg.logAt k ∘ Prod.fst) (((τ ⊗ₖ M).submatrix (B.liftS tab).symm
        (B.liftS tab).symm).submatrix copyE.symm copyE.symm)).submatrix respE.symm
        respE.symm).submatrix (B.liftO T₁ E ω).symm (B.liftO T₁ E ω).symm) := by
    have h1 := (hinv.kronecker_fst M).submatrix_perm (π := B.liftS tab)
      (S' := Prod.fst ⁻¹' B.patchInv tab T₁ k) fun a ha => ha
    have h2 := h1.submatrix_perm (π := copyE) (S' := Prod.fst ⁻¹' B.patchInv tab T₁ k)
      fun a ha => B.copyG_mem_patchInv tab T₁ k ha
    have h3 := (h2.dephase (B.toKindAlg.logAt k ∘ Prod.fst)).submatrix_perm (π := respE)
      (S' := Prod.fst ⁻¹' B.patchInv tab T₁ k)
      fun a ha => B.respG_mem_patchInv tab T₁ E₁ ω₁ k k ha
    exact h3.submatrix_perm (π := B.liftO T₁ E ω) fun a ha => ha
  have key : (embed (B.patchPlace tab out' (B.tagT T₁ k) T₁)
      (((dephase (B.toKindAlg.logAt k ∘ Prod.fst) (((τ ⊗ₖ M).submatrix (B.liftS tab).symm
        (B.liftS tab).symm).submatrix copyE.symm copyE.symm)).submatrix respE.symm
        respE.symm).submatrix (B.liftO T₁ E ω).symm (B.liftO T₁ E ω).symm)).submatrix
        (B.patchGamePerm tab out' (B.patchAfter tab ((k : ℕ) + 1))).symm
        (B.patchGamePerm tab out' (B.patchAfter tab ((k : ℕ) + 1))).symm =
      embed (B.patchPlace tab out' (fun _ _ => none) T₁)
        ((((dephase (B.toKindAlg.logAt k) (τ.submatrix (B.toKindAlg.copyG k).symm
          (B.toKindAlg.copyG k).symm)).submatrix (B.toKindAlg.respG E₁ ω₁ k).symm
          (B.toKindAlg.respG E₁ ω₁ k).symm).submatrix (E₁.oraclePerm B.toKindAlg.kind ω₁).symm
          (E₁.oraclePerm B.toKindAlg.kind ω₁).symm) ⊗ₖ M) := by
    rw [hafter, patchGamePerm_trans, submatrix_trans_symm,
      submatrix_embed_of_mem (fun x hx => B.gamePerm_tagP_place_tagT tab out' T₁ k hx) hZ,
      submatrix_embed (π' := B.liftF tab) (S := Set.univ)
        (fun x _ => B.gamePerm_finishP_place tab out' T₁ _ _ x) (fun a b h => by simp at h)]
    congr 1
    rw [submatrix_comm_of_comm (π := B.liftS tab) (τ := copyE)
        (fun a => (B.copyE_liftS tab k a).symm),
      dephase_submatrix_of_comp (π := B.liftS tab) (fun a => rfl),
      submatrix_comm_of_comm (π := B.liftS tab) (τ := respE)
        (fun a => (B.respE_liftS tab E₁ ω₁ k a).symm),
      kronecker_submatrix_prodCongr, dephase_kronecker_fst, kronecker_submatrix_prodCongr,
      kronecker_liftS_liftO_liftF]
    congr 1
    refine submatrix_congr_of_suppIn hρ₃ fun g hg => ?_
    obtain ⟨⟨hlater, hlog⟩, hinvg⟩ := hg
    obtain ⟨⟨wc_, rq, rs, lg⟩, qs⟩ := g
    obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
    change LogReg Req B.slots at lg
    simp only [patchInv, Set.mem_setOf_eq, AlgShape.CntW.work_mk] at hinvg
    simp only [Env.oraclePerm, queryPermOf_apply, AlgShape.CntW.work_mk]
    refine Prod.ext rfl (funext fun i => ?_)
    by_cases hk : B.kind w = true
    · simp [toKindAlg_kind_mk, hk]
    · have hk' : B.kind w = false := by simpa using hk
      have hlk : lg k = none := by
        simpa [KindAlg.reqOutG, splitLogs, toKindAlg, AlgShape.CntW.work_mk, AlgShape.CntW.cnt_mk, hk'] using hlog
      have hreq : requests lg = requestsBefore lg k :=
        requests_eq_requestsBefore fun j hj => by
          rcases eq_or_lt_of_le hj with h | h
          · rw [← Fin.ext h]; exact hlk
          · exact hlater j h
      simp only [toKindAlg_kind_mk, AlgShape.CntW.work_mk, hk', Bool.false_eq_true, ite_false]
      rw [horc lg, hreq, ← hinvg]
      -- TODO(unbundle-M4): the `if` keeps the `Decidable` instance at `(mk w c).work`, so `simp [hk']`
      -- cannot rewrite its condition.
      exact congrArg (fun f : X → Y => ((qs i).1, (qs i).2 + f (qs i).1))
        (if_neg (show ¬ B.kind w = true from fun h => absurd (h.symm.trans hk') (by decide)))
  have e : ∀ (A' : Matrix (B.patchTag tab out').toKindAlg.G (B.patchTag tab out').toKindAlg.G ℂ)
      (π : Equiv.Perm (B.patchTag tab out').toKindAlg.G),
      A' = (A'.submatrix π.symm π.symm).submatrix π π := fun A' π => by
    ext a b
    simp
  rw [e (embed _ _) (B.patchGamePerm tab out' (B.patchAfter tab ((k : ℕ) + 1))), key]
  rfl

/-- **The initial state of the patched mixed game** is `B`'s with clean ancillas, placed. -/
theorem mgInit_patchTag :
    (B.patchTag tab out').toKindAlg.mgInit =
      embed (B.patchPlace tab out' (fun _ _ => none) T₁)
          (B.toKindAlg.mgInit ⊗ₖ ancMat KindAlg.x₀) := by
  have h1 : (B.patchTag tab out').toKindAlg.mgInit = embed
      (fun d => splitLogs.symm (d, fun _ => none))
      (embed (fun d => (B.patchTag tab out').cntSplit.symm (d, 0))
        (B.patchTag tab out').init.mat) := by
    rw [KindAlg.mgInit]
    exact (MState.reindex_tensorKet_mat _ _ _).trans
      (congrArg _ (MState.reindex_tensorKet_mat _ _ _))
  have h2 : B.toKindAlg.mgInit = embed (fun d => splitLogs.symm (d, fun _ => none))
      (embed (fun d => B.cntSplit.symm (d, 0)) B.init.mat) := by
    rw [KindAlg.mgInit]
    exact (MState.reindex_tensorKet_mat _ _ _).trans
      (congrArg _ (MState.reindex_tensorKet_mat _ _ _))
  have h3 : (B.patchTag tab out').init.mat = embed (B.patchSplitB.symm ∘
      fun p : DReg B.W B.width X Y Req Resp × AncReg X Y B.width => (p.1, (p.2, fun _ => none)))
      (B.init.mat ⊗ₖ ancMat KindAlg.x₀) := by
    rw [patchTag_init]
    change (B.init.mat ⊗ₖ
        (ancMat KindAlg.x₀ ⊗ₖ Matrix.single (fun _ => none) (fun _ => none) 1)).submatrix
      B.patchSplitB.symm.symm B.patchSplitB.symm.symm = _
    rw [kronecker_kronecker_single, Equiv.symm_symm, submatrix_embed_equiv]
  rw [h1, h2, h3, embed_kronecker, embed_kronecker, embed_embed, embed_embed, embed_embed,
    embed_embed]
  congr 1
/-- **One post batch of the patched mixed game** is a post batch of `B`'s mixed game against `E₁`,
placed. -/
theorem post_patchTag
    (horc : ∀ lg : LogReg Req B.slots,
      E₁.oracle ω₁ lg = reprogT (T₁ (requests lg)) (E.oracle ω (augLogs T₁ lg)))
    (b : Fin B.post) {σ : Matrix B.toKindAlg.G B.toKindAlg.G ℂ}
    (hinv : SuppIn (B.patchInv tab T₁ B.slots) (B.toKindAlg.liftG (postStep b) σ)) :
    (Circuit.kraus ((B.patchTag tab out').toKindAlg.liftG (postStep b))
        (.kraus (KrausMap.ofPerm ((B.patchTag tab out').toKindAlg.postG E ω)) .nil)).run
        (Equiv.refl _) (B.patchPend tab out' T₁ (B.slots + b) σ) =
      B.patchPend tab out' T₁ (B.slots + b + 1) ((Circuit.kraus (B.toKindAlg.liftG (postStep b))
        (.kraus (KrausMap.ofPerm (B.toKindAlg.postG E₁ ω₁)) .nil)).run (Equiv.refl _) σ) := by
  simp only [Circuit.run, KrausMap.ofPerm_apply]
  rw [show B.patchPend tab out' T₁ (B.slots + b) σ =
    B.patchPend tab out' T₁ ((postStep b : StepIdx B.slots B.post) : ℕ) σ from rfl,
    liftG_patchPend]
  set τ := B.toKindAlg.liftG (postStep b) σ
  set M := ancMat (Y := Y) (n := B.width) (KindAlg.x₀ : X)
  have hbefore : B.patchBefore tab ((postStep b : StepIdx B.slots B.post) : ℕ) =
      B.swapP tab fun _ => true := by
    simp [patchBefore, AlgShape.patchBefore]
  have hafter : B.patchAfter tab (B.slots + b + 1) = B.finishP tab fun _ => true := by
    have h1 : ¬ (0 < B.slots + b + 1 ∧ B.slots + b + 1 - 1 < B.slots) := by omega
    rw [patchAfter_def, if_neg h1, if_pos (by omega)]
  rw [hbefore, submatrix_embed (S := Set.univ)
      (fun x _ => B.gamePerm_swapP_place tab out' T₁ (fun _ => true) _ x)
          (fun a b h => by simp at h),
    submatrix_embed (S := Set.univ) (fun x _ => B.postG_place tab out' T₁ E ω _ x)
      (fun a b h => by simp at h)]
  have key : (embed (B.patchPlace tab out' (fun _ _ => none) T₁)
      ((((τ ⊗ₖ M).submatrix
        (liftPairs fun v : B.BV => if (fun _ => true) v.1.work then ancSwap (tab v.1.work)
          else Equiv.refl _).symm
        (liftPairs fun v : B.BV => if (fun _ => true) v.1.work then ancSwap (tab v.1.work)
          else Equiv.refl _).symm).submatrix
        (liftPairs fun v : B.BV => ancAdd (E.oracle ω (augLogs T₁ v.2.2.2))).symm
        (liftPairs fun v : B.BV => ancAdd (E.oracle ω (augLogs T₁ v.2.2.2))).symm))).submatrix
        (B.patchGamePerm tab out' (B.patchAfter tab (B.slots + b + 1))).symm
        (B.patchGamePerm tab out' (B.patchAfter tab (B.slots + b + 1))).symm =
      embed (B.patchPlace tab out' (fun _ _ => none) T₁)
        ((τ.submatrix (B.toKindAlg.postG E₁ ω₁).symm (B.toKindAlg.postG E₁ ω₁).symm) ⊗ₖ M) := by
    rw [hafter, submatrix_embed (S := Set.univ)
      (fun x _ => B.gamePerm_finishP_place tab out' T₁ (fun _ => true) _ x)
      (fun a b h => by simp at h)]
    congr 1
    rw [← submatrix_trans_symm, ← submatrix_trans_symm, liftPairs_trans, liftPairs_trans]
    refine (kronecker_ancMat_submatrix_liftPairs _ _
      (fun v : B.BV => reprogT (tab v.1.work) (E.oracle ω (augLogs T₁ v.2.2.2)))
      (fun v p => ⟨ancPerm_symm_anc_fst (tab v.1.work) (E.oracle ω (augLogs T₁ v.2.2.2)) p,
        ancPerm_symm_flag (tab v.1.work) (E.oracle ω (augLogs T₁ v.2.2.2)) p⟩)
      (fun v p hf => ancPerm_symm_sys (tab v.1.work) (E.oracle ω (augLogs T₁ v.2.2.2)) p hf)
      τ).trans ?_
    congr 1
    refine submatrix_congr_of_suppIn hinv fun g hg => ?_
    obtain ⟨⟨wc_, rq, rs, lg⟩, qs⟩ := g
    obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
    simp only [patchInv, Set.mem_setOf_eq, AlgShape.CntW.work_mk] at hg
    simp only [KindAlg.postG, queryPermOf_apply]
    refine Prod.ext rfl (funext fun i => ?_)
    change _ = (_, _ + E₁.oracle ω₁ lg _)
    simp only [AlgShape.CntW.work_mk]
    rw [horc lg, hg]
    rfl
  have e : ∀ (A' : Matrix (B.patchTag tab out').toKindAlg.G (B.patchTag tab out').toKindAlg.G ℂ)
      (π : Equiv.Perm (B.patchTag tab out').toKindAlg.G),
      A' = (A'.submatrix π.symm π.symm).submatrix π π := fun A' π => by
    ext a b
    simp
  rw [e (embed _ _) (B.patchGamePerm tab out' (B.patchAfter tab (B.slots + b + 1))), key]
  rfl

/-- **The last step of the patched mixed game** is `B`'s last step, placed. -/
theorem last_patchTag (σ : Matrix B.toKindAlg.G B.toKindAlg.G ℂ) :
    (B.patchTag tab out').toKindAlg.liftG lastStep (B.patchPend tab out' T₁ (B.slots + B.post) σ) =
      embed (B.patchPlace tab out' (fun _ _ => none) T₁)
        ((B.toKindAlg.liftG lastStep σ) ⊗ₖ ancMat KindAlg.x₀) := by
  rw [show B.patchPend tab out' T₁ (B.slots + B.post) σ =
    B.patchPend tab out' T₁ ((lastStep : StepIdx B.slots B.post) : ℕ) σ from rfl, liftG_patchPend]
  have hb : B.patchBefore tab ((lastStep : StepIdx B.slots B.post) : ℕ) = Equiv.refl _ := by
    simp [patchBefore, AlgShape.patchBefore]
  rw [hb]
  ext a b
  rfl

end AdaptiveIAlg

/-! ### Runs of slots and of post batches -/

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [AddGroup Y]
  {ksK : KindShape X Y Req Resp} (K : KindAlg ksK O) {Ω St : Type} {Q : ℕ} [OracleState St X Y]
  (E : Env Ω Req Resp X Y Q St) (ω : Ω)

/-- **The run of the slots `l`** of the mixed game, with the requests measured. -/
def slotsRun (l : List (Fin K.slots)) (ρ : Matrix K.G K.G ℂ) : Matrix K.G K.G ℂ :=
  (Circuit.concat
      (l.map fun k => Circuit.kraus (K.liftG (slotStep k)) (K.eventCirc E ω k true))).run
    (Equiv.refl _) ρ

/-- **The run of the post batches `l`** of the mixed game. -/
def postsRun (l : List (Fin K.post)) (ρ : Matrix K.G K.G ℂ) : Matrix K.G K.G ℂ :=
  (Circuit.concat (l.map fun b => Circuit.kraus (K.liftG (postStep b))
    (.kraus (KrausMap.ofPerm (K.postG E ω)) .nil))).run (Equiv.refl _) ρ

@[simp]
theorem slotsRun_nil (ρ : Matrix K.G K.G ℂ) : K.slotsRun E ω [] ρ = ρ :=
  rfl

@[simp]
theorem postsRun_nil (ρ : Matrix K.G K.G ℂ) : K.postsRun E ω [] ρ = ρ :=
  rfl

theorem slotsRun_cons (k : Fin K.slots) (l : List (Fin K.slots)) (ρ : Matrix K.G K.G ℂ) :
    K.slotsRun E ω (k :: l) ρ = K.slotsRun E ω l
      ((Circuit.kraus (K.liftG (slotStep k)) (K.eventCirc E ω k true)).run (Equiv.refl _) ρ) := by
  simp only [slotsRun, List.map_cons]
  exact Circuit.run_concat _ _ _ _

theorem postsRun_cons (b : Fin K.post) (l : List (Fin K.post)) (ρ : Matrix K.G K.G ℂ) :
    K.postsRun E ω (b :: l) ρ = K.postsRun E ω l
      ((Circuit.kraus (K.liftG (postStep b)) (.kraus (KrausMap.ofPerm (K.postG E ω)) .nil)).run
        (Equiv.refl _) ρ) := by
  simp only [postsRun, List.map_cons]
  exact Circuit.run_concat _ _ _ _

/-- **The mixed game is the slots, the post batches and the last step.** -/
theorem mgRun_eq_slotsRun (deph : Bool) (hdeph : deph = true) :
    K.mgRun E ω deph = K.liftG lastStep (K.postsRun E ω (List.finRange K.post)
      (K.slotsRun E ω (List.finRange K.slots) K.mgInit)) := by
  subst hdeph
  simp only [mgRun, mgCirc, Circuit.run_append, slotsRun, postsRun]
  rfl

end KindAlg

namespace AdaptiveIAlg

variable {X Y Req Resp O O' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shB : AlgShape X Y Req Resp} (B : AdaptiveIAlg shB O) (tab : B.W → X → Option Y) (out' : B.W → O')
  [AddGroup Y] [Nonempty X] [Nonempty Y] (T₁ : List Req → X → Option Y)
  {Ω St : Type} {Q : ℕ} [OracleState St X Y] (E : Env Ω (Req × (X → Option Y)) Resp X Y Q St)
  (ω : Ω) {Ω₁ St₁ : Type} {Q₁ : ℕ} [OracleState St₁ X Y] (E₁ : Env Ω₁ Req Resp X Y Q₁ St₁)
  (ω₁ : Ω₁)

theorem run_slots_patchTag
    (hans : ∀ (lg : LogReg Req B.slots) k, E.answer ω (augLogs T₁ lg) k = E₁.answer ω₁ lg k)
    (horc : ∀ lg : LogReg Req B.slots,
      E₁.oracle ω₁ lg = reprogT (T₁ (requests lg)) (E.oracle ω (augLogs T₁ lg)))
    (l : List (Fin B.slots)) (j : ℕ) (hl : l.map Fin.val = List.range' j l.length)
    {σ : Matrix B.toKindAlg.G B.toKindAlg.G ℂ} (hσ : SuppIn (B.toKindAlg.blankFrom j) σ)
    (hd : dephase (B.toKindAlg.logsBelow j) σ = σ)
    (hinv : ∀ i (hi : i < l.length), SuppIn (B.patchInv tab T₁ (j + i))
      (B.toKindAlg.liftG (slotStep l[i]) (B.toKindAlg.slotsRun E₁ ω₁ (l.take i) σ))) :
    (B.patchTag tab out').toKindAlg.slotsRun E ω l (B.patchPend tab out' T₁ j σ) =
      B.patchPend tab out' T₁ (j + l.length) (B.toKindAlg.slotsRun E₁ ω₁ l σ) := by
  induction l generalizing j σ with
  | nil => rfl
  | cons k l ih =>
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hl ⊢
    have hσ' : SuppIn (B.toKindAlg.blankFrom k) σ := by rw [hl.1]; exact hσ
    have hd' : dephase (B.toKindAlg.logsBelow k) σ = σ := by rw [hl.1]; exact hd
    have h0 := hinv 0 (by simp)
    simp only [List.getElem_cons_zero, List.take_zero, Nat.add_zero] at h0
    have h0' : SuppIn (B.patchInv tab T₁ k) (B.toKindAlg.liftG (slotStep k) σ) := by
      rw [hl.1]; exact h0
    rw [KindAlg.slotsRun_cons, KindAlg.slotsRun_cons,
      show B.patchPend tab out' T₁ j σ = B.patchPend tab out' T₁ k σ by rw [hl.1],
      B.slot_patchTag tab out' T₁ E ω E₁ ω₁ hans horc k hσ' hd' h0']
    rw [ih (k + 1) (by rw [hl.2, hl.1]) (B.suppIn_slot' E₁ ω₁ k hσ') (B.dephase_slot E₁ ω₁ k hd')
      fun i hi => by
        have := hinv (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ, List.take_succ_cons, KindAlg.slotsRun_cons] at this
        rw [show (k : ℕ) + 1 + i = j + (i + 1) by rw [hl.1]; omega]
        exact this]
    rw [show (k : ℕ) + 1 + l.length = j + (l.length + 1) by rw [hl.1]; omega]

theorem run_posts_patchTag
    (horc : ∀ lg : LogReg Req B.slots,
      E₁.oracle ω₁ lg = reprogT (T₁ (requests lg)) (E.oracle ω (augLogs T₁ lg)))
    (l : List (Fin B.post)) (b₀ : ℕ) (hl : l.map Fin.val = List.range' b₀ l.length)
    {σ : Matrix B.toKindAlg.G B.toKindAlg.G ℂ}
    (hinv : ∀ i (hi : i < l.length), SuppIn (B.patchInv tab T₁ B.slots)
      (B.toKindAlg.liftG (postStep l[i]) (B.toKindAlg.postsRun E₁ ω₁ (l.take i) σ))) :
    (B.patchTag tab out').toKindAlg.postsRun E ω l (B.patchPend tab out' T₁ (B.slots + b₀) σ) =
      B.patchPend tab out' T₁ (B.slots + (b₀ + l.length)) (B.toKindAlg.postsRun E₁ ω₁ l σ) := by
  induction l generalizing b₀ σ with
  | nil => rfl
  | cons b l ih =>
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hl ⊢
    have h0 := hinv 0 (by simp)
    simp only [List.getElem_cons_zero, List.take_zero, KindAlg.postsRun_nil] at h0
    rw [KindAlg.postsRun_cons, KindAlg.postsRun_cons,
      show B.patchPend tab out' T₁ (B.slots + b₀) σ = B.patchPend tab out' T₁ (B.slots + b) σ by
        rw [hl.1],
      B.post_patchTag tab out' T₁ E ω E₁ ω₁ horc b (σ := σ) h0]
    rw [show B.slots + (b : ℕ) + 1 = B.slots + (b₀ + 1) by rw [hl.1]; omega,
      ih (b₀ + 1) hl.2 fun i hi => by
        have := hinv (i + 1) (by simp; omega)
        simp only [List.getElem_cons_succ, List.take_succ_cons, KindAlg.postsRun_cons] at this
        exact this]
    rw [show b₀ + 1 + l.length = b₀ + (l.length + 1) by omega]

/-- **The mixed game of the patched adversary is `B`'s mixed game with clean ancillas, placed**
(module docstring): against `E` on the tape `ω`, its final state is that of `B` against `E₁` on
`ω₁` with clean ancillas, placed (`patchPlace` with a blank table register), when `E₁` is `E`
read through the tables `T₁` (`hans`, `horc`) and `B`'s workspace table is `T₁` of the requests so
far after each of `B`'s steps (`hinv`, `hinvPost`). -/
theorem mgRun_patchTag
    (hans : ∀ (lg : LogReg Req B.slots) k, E.answer ω (augLogs T₁ lg) k = E₁.answer ω₁ lg k)
    (horc : ∀ lg : LogReg Req B.slots,
      E₁.oracle ω₁ lg = reprogT (T₁ (requests lg)) (E.oracle ω (augLogs T₁ lg)))
    (hinv : ∀ k : Fin B.slots, SuppIn (B.patchInv tab T₁ k) (B.toKindAlg.liftG (slotStep k)
      (B.toKindAlg.slotsRun E₁ ω₁ ((List.finRange B.slots).take k) B.toKindAlg.mgInit)))
    (hinvPost : ∀ b : Fin B.post, SuppIn (B.patchInv tab T₁ B.slots)
      (B.toKindAlg.liftG (postStep b) (B.toKindAlg.postsRun E₁ ω₁ ((List.finRange B.post).take b)
        (B.toKindAlg.slotsRun E₁ ω₁ (List.finRange B.slots) B.toKindAlg.mgInit)))) :
    (B.patchTag tab out').toKindAlg.mgRun E ω true =
      embed (B.patchPlace tab out' (fun _ _ => none) T₁)
        (B.toKindAlg.mgRun E₁ ω₁ true ⊗ₖ ancMat KindAlg.x₀) := by
  rw [KindAlg.mgRun_eq_slotsRun _ _ _ _ rfl, KindAlg.mgRun_eq_slotsRun _ _ _ _ rfl]
  have h0 : (B.patchTag tab out').toKindAlg.mgInit =
      B.patchPend tab out' T₁ 0 B.toKindAlg.mgInit := by
    rw [mgInit_patchTag, patchPend]
    have : B.patchAfter tab 0 = Equiv.refl _ := by rw [patchAfter_def]; simp
    rw [this]
    ext a b
    rfl
  have hs := B.run_slots_patchTag tab out' T₁ E ω E₁ ω₁ hans horc (List.finRange B.slots) 0
    (by rw [List.map_coe_finRange_eq_range, List.range_eq_range', List.length_finRange])
    (σ := B.toKindAlg.mgInit) B.toKindAlg.suppIn_mgInit (by
      have hl : ∀ a b, B.toKindAlg.logsBelow 0 a = B.toKindAlg.logsBelow 0 b := fun a b =>
        funext fun k => by simp [KindAlg.logsBelow]
      ext a b
      simp [dephase, hl a b])
    fun i hi => by
      have := hinv ⟨i, by simpa using hi⟩
      simpa [List.getElem_finRange] using this
  rw [List.length_finRange, Nat.zero_add] at hs
  have hp := B.run_posts_patchTag tab out' T₁ E ω E₁ ω₁ horc (List.finRange B.post) 0
    (by rw [List.map_coe_finRange_eq_range, List.range_eq_range', List.length_finRange])
    (σ := B.toKindAlg.slotsRun E₁ ω₁ (List.finRange B.slots) B.toKindAlg.mgInit)
    fun i hi => by
      have := hinvPost ⟨i, by simpa using hi⟩
      simpa [List.getElem_finRange] using this
  rw [List.length_finRange, Nat.zero_add, Nat.add_zero] at hp
  rw [h0, hs, hp]
  exact B.last_patchTag tab out' T₁ _

end AdaptiveIAlg

end GordieHowe.Quantum
