-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.AssignPatchRun

@[expose] public section

/-!
# One slot of the patched adversary's mixed game

Proof tools for the law of `AdaptiveIAlg.patchTag`: the permutations of the patched mixed game on
the placed registers (`patchPlace`), as permutations of `B`'s game registers with the ancillas.

- Matrix tools: `kronecker_submatrix_prodCongr`, `dephase_kronecker_fst`,
  `SuppIn.kronecker_fst`, `submatrix_congr_of_suppIn`.
- `tagT T₁ k`: the table register on a request branch before slot `k`, `T₁` of the requests
  before it. `patchInv T₁ k`: the basis states whose workspace table is `T₁` of the requests
  before slot `k`.
- `gamePerm_tagP_place`, `gamePerm_tagP_place_tagT`: the tag written and cleared, on `patchInv`.
  `gamePerm_swapP_place`, `gamePerm_finishP_place`, `oraclePerm_place`, `postG_place`: the
  exchanges, the end of the reprogrammed queries and the queries act on the query pairs and the
  ancillas as lifts of pair permutations (`liftPairs`). `copyG_place`, `respG_place`,
  `dephase_place`: the copy of the tagged request, its reply and the measurement of the tagged
  log are those of `B`.
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.Quantum

/-! ### Matrix tools -/

section Mat

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem dephase_kronecker_fst {L : Type*} [DecidableEq L] (f : ι → L) (ρ : Matrix ι ι ℂ)
    (M : Matrix κ κ ℂ) : dephase (f ∘ Prod.fst) (ρ ⊗ₖ M) = (dephase f ρ) ⊗ₖ M := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [dephase, Function.comp, kroneckerMap_apply]
  split_ifs <;> simp

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem SuppIn.kronecker_fst {S : Set ι} {ρ : Matrix ι ι ℂ} (h : SuppIn S ρ) (M : Matrix κ κ ℂ) :
    SuppIn (Prod.fst ⁻¹' S) (ρ ⊗ₖ M) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ hab
  simp only [kroneckerMap_apply, Set.mem_preimage] at hab ⊢
  rw [h a c hab, zero_mul]

omit [DecidableEq ι] in
/-- **Basis permutations that agree on the support conjugate alike.** -/
theorem submatrix_congr_of_suppIn {S : Set ι} {ρ : Matrix ι ι ℂ} (h : SuppIn S ρ)
    {π π' : Equiv.Perm ι} (hπ : ∀ a ∈ S, π a = π' a) :
    ρ.submatrix π.symm π.symm = ρ.submatrix π'.symm π'.symm := by
  have key : ∀ a, π.symm a ∈ S ∨ π'.symm a ∈ S → π.symm a = π'.symm a := by
    intro a ha
    rcases ha with ha | ha
    · rw [Equiv.eq_symm_apply, ← hπ _ ha, Equiv.apply_symm_apply]
    · rw [Equiv.symm_apply_eq, hπ _ ha, Equiv.apply_symm_apply]
  ext a b
  simp only [submatrix_apply]
  by_cases ha : π.symm a ∈ S ∨ π'.symm a ∈ S
  · by_cases hb : π.symm b ∈ S ∨ π'.symm b ∈ S
    · rw [key a ha, key b hb]
    · push_neg at hb
      rw [h _ _ (Or.inr hb.1), h _ _ (Or.inr hb.2)]
  · push_neg at ha
    rw [h _ _ (Or.inl ha.1), h _ _ (Or.inl ha.2)]

/-- Conjugating by a composition is conjugating twice. -/
theorem submatrix_trans_symm (π τ : Equiv.Perm ι) (ρ : Matrix ι ι ℂ) :
    ρ.submatrix (π.trans τ).symm (π.trans τ).symm =
      (ρ.submatrix π.symm π.symm).submatrix τ.symm τ.symm := by
  ext a b
  rfl

/-- **Conjugations by commuting permutations commute.** -/
theorem submatrix_comm_of_comm {π τ : Equiv.Perm ι} (h : ∀ a, π (τ a) = τ (π a))
    (ρ : Matrix ι ι ℂ) :
    (ρ.submatrix π.symm π.symm).submatrix τ.symm τ.symm =
      (ρ.submatrix τ.symm τ.symm).submatrix π.symm π.symm := by
  have h' : ∀ a, π.symm (τ.symm a) = τ.symm (π.symm a) := fun a => by
    rw [Equiv.symm_apply_eq, Equiv.symm_apply_eq, ← h, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  ext a b
  simp only [submatrix_apply, h']

omit [Fintype ι] [DecidableEq ι] in
/-- **Dephasing commutes with a conjugation that keeps the dephased function.** -/
theorem dephase_submatrix_of_comp {L : Type*} [DecidableEq L] {f : ι → L} {π : Equiv.Perm ι}
    (h : ∀ a, f (π a) = f a) (ρ : Matrix ι ι ℂ) :
    dephase f (ρ.submatrix π.symm π.symm) = (dephase f ρ).submatrix π.symm π.symm := by
  have h' : ∀ a, f (π.symm a) = f a := fun a => by rw [← h (π.symm a), Equiv.apply_symm_apply]
  ext a b
  simp only [dephase, submatrix_apply, h']

end Mat

/-! ### Tagged logs -/

section Aug

variable {Req Tab : Type*} {m : ℕ} [DecidableEq Req]

/-- **Tagging after a request logged at slot `k`**, with the later logs blank: the tagged logs with
the tagged request at slot `k`. -/
theorem augLogs_update_of_blank (T₁ : List Req → Tab) {lg : LogReg Req m} {k : Fin m}
    (h : ∀ j : Fin m, (k : ℕ) ≤ j → lg j = none) (r : Req) :
    augLogs T₁ (Function.update lg k (some r)) =
      Function.update (augLogs T₁ lg) k (some (r, T₁ (requestsBefore lg k))) := by
  funext j
  have hb : requestsBefore (Function.update lg k (some r)) k = requestsBefore lg k :=
    requestsBefore_congr fun k' hk' => Function.update_of_ne (fun e => by subst e; omega) _ _
  by_cases hj : j = k
  · subst hj
    simp [augLogs, hb]
  · rw [Function.update_of_ne hj]
    simp only [augLogs, Function.update_of_ne hj]
    rcases lt_or_gt_of_ne (fun e : (j : ℕ) = k => hj (Fin.ext e)) with hl | hl
    · rw [requestsBefore_congr (lg' := lg) fun k' hk' => Function.update_of_ne
        (fun e => by subst e; omega) _ _]
    · rw [h j hl.le]
      rfl

end Aug

namespace AdaptiveIAlg

variable {X Y Req Resp O O' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shB : AlgShape X Y Req Resp} (B : AdaptiveIAlg shB O) (tab : B.W → X → Option Y) (out' : B.W → O')
  [AddGroup Y] [Nonempty X] [Nonempty Y] (T₁ : List Req → X → Option Y)

/-- The registers of `B`'s game beside the query pairs. -/
abbrev BV : Type := B.CntW × Req × Option Resp × LogReg Req B.slots

/-- **The table register on a request branch before slot `k`**: `T₁` of the requests before slot
`k`; blank on a query branch. -/
def tagT (k : ℕ) (v : B.BV) : X → Option Y :=
  if B.kind v.1.work then T₁ (requestsBefore v.2.2.2 k) else fun _ => none

/-- **The basis states whose workspace table is `T₁` of the requests before slot `k`.** -/
def patchInv (k : ℕ) : Set B.toKindAlg.G :=
  {g | tab g.1.1.work = T₁ (requestsBefore g.1.2.2.2 k)}

omit [AddGroup Y] [Nonempty X] [Nonempty Y] in
theorem tagP_apply (on : B.W → Bool) (d : B.PatchReg) :
    B.tagP tab on d = if on d.1.1.1 then
      ((d.1.1, (d.1.2.1.1, Equiv.swap (fun _ => none) (tab d.1.1.1) d.1.2.1.2), d.1.2.2), d.2)
      else d :=
  rfl

/-- A permutation of the patched registers on a game basis state. -/
theorem patchGamePerm_apply (π : Equiv.Perm B.PatchReg) (y : (B.patchTag tab out').toKindAlg.G) :
    B.patchGamePerm tab out' π y =
      ((((AlgShape.CntW.mk (π ((y.1.1.work, y.1.2.1, y.1.2.2.1), y.2)).1.1 y.1.1.cnt :
          (B.patchTag tab out').CntW),
        (π ((y.1.1.work, y.1.2.1, y.1.2.2.1), y.2)).1.2.1,
        (π ((y.1.1.work, y.1.2.1, y.1.2.2.1), y.2)).1.2.2, y.1.2.2.2)),
        (π ((y.1.1.work, y.1.2.1, y.1.2.2.1), y.2)).2) :=
  rfl

/-- **The tag written before slot `k`** on a basis state whose workspace table is `T₁` of the
requests before slot `k`. -/
theorem gamePerm_tagP_place (k : ℕ) {x : B.toKindAlg.G × AncReg X Y B.width}
    (hx : x.1 ∈ B.patchInv tab T₁ k) :
    B.patchGamePerm tab out' (B.tagP tab B.kind) (B.patchPlace tab out' (fun _ _ => none) T₁ x) =
      B.patchPlace tab out' (B.tagT T₁ k) T₁ x := by
  obtain ⟨⟨⟨wc_, rq, rs, lg⟩, qs⟩, a⟩ := x
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
  simp only [patchInv, Set.mem_setOf_eq] at hx
  rw [patchGamePerm_apply]
  by_cases hk : B.kind w = true
  · simp only [patchPlace, tagP_apply, AlgShape.CntW.work_mk, AlgShape.CntW.cnt_mk, AlgShape.PatchWS.fst_mk, hk, tagT, ← hx, Equiv.swap_apply_left]
    rfl
  · simp only [patchPlace, tagP_apply, AlgShape.CntW.work_mk, AlgShape.CntW.cnt_mk, AlgShape.PatchWS.fst_mk, hk, tagT]
    simp

/-- **The tag cleared after slot `k`.** -/
theorem gamePerm_tagP_place_tagT (k : ℕ) {x : B.toKindAlg.G × AncReg X Y B.width}
    (hx : x.1 ∈ B.patchInv tab T₁ k) :
    B.patchGamePerm tab out' (B.tagP tab B.kind) (B.patchPlace tab out' (B.tagT T₁ k) T₁ x) =
      B.patchPlace tab out' (fun _ _ => none) T₁ x := by
  obtain ⟨⟨⟨wc_, rq, rs, lg⟩, qs⟩, a⟩ := x
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
  simp only [patchInv, Set.mem_setOf_eq] at hx
  rw [patchGamePerm_apply]
  by_cases hk : B.kind w = true
  · simp only [patchPlace, tagP_apply, AlgShape.CntW.work_mk, AlgShape.CntW.cnt_mk, AlgShape.PatchWS.fst_mk, hk, tagT, ← hx, ite_true, Equiv.swap_apply_right]
  · simp only [patchPlace, tagP_apply, AlgShape.CntW.work_mk, AlgShape.CntW.cnt_mk, AlgShape.PatchWS.fst_mk, hk, tagT]
    simp

/-- **The exchanges with the ancillas** on the placed registers. -/
theorem gamePerm_swapP_place (on : B.W → Bool) (tg : B.BV → X → Option Y)
    (x : B.toKindAlg.G × AncReg X Y B.width) :
    B.patchGamePerm tab out' (B.swapP tab on) (B.patchPlace tab out' tg T₁ x) =
      B.patchPlace tab out' tg T₁
        (liftPairs (fun v : B.BV => if on v.1.work then ancSwap (tab v.1.work) else Equiv.refl _) x) :=
  rfl

/-- **The end of the reprogrammed queries** on the placed registers. -/
theorem gamePerm_finishP_place (on : B.W → Bool) (tg : B.BV → X → Option Y)
    (x : B.toKindAlg.G × AncReg X Y B.width) :
    B.patchGamePerm tab out' (B.finishP tab on) (B.patchPlace tab out' tg T₁ x) =
      B.patchPlace tab out' tg T₁ (liftPairs (fun v : B.BV => if on v.1.work then
        (ancSwap (tab v.1.work)).trans (ancAdd fun x => (tab v.1.work x).getD 0) else Equiv.refl _) x) :=
  rfl

variable {Ω St : Type} {Q : ℕ} [OracleState St X Y] (E : Env Ω (Req × (X → Option Y)) Resp X Y Q St)
  (ω : Ω)

/-- **The queries of a slot** on the placed registers. -/
theorem oraclePerm_place (tg : B.BV → X → Option Y) (x : B.toKindAlg.G × AncReg X Y B.width) :
    E.oraclePerm (B.patchTag tab out').toKindAlg.kind ω (B.patchPlace tab out' tg T₁ x) =
      B.patchPlace tab out' tg T₁ (liftPairs (fun v : B.BV => ancAdd
        (if B.kind v.1.work then 0 else E.oracle ω (augLogs T₁ v.2.2.2))) x) :=
  rfl

/-- **The post-phase queries** on the placed registers. -/
theorem postG_place (tg : B.BV → X → Option Y) (x : B.toKindAlg.G × AncReg X Y B.width) :
    (B.patchTag tab out').toKindAlg.postG E ω (B.patchPlace tab out' tg T₁ x) =
      B.patchPlace tab out' tg T₁ (liftPairs (fun v : B.BV => ancAdd
        (E.oracle ω (augLogs T₁ v.2.2.2))) x) :=
  rfl

/-- **The copy of the tagged request of slot `k`** on the placed registers is `B`'s copy, on
states whose logs from slot `k` on are blank. -/
theorem copyG_place (k : Fin B.slots) {x : B.toKindAlg.G × AncReg X Y B.width}
    (hx : x.1 ∈ B.toKindAlg.blankFrom k) :
    (B.patchTag tab out').toKindAlg.copyG k (B.patchPlace tab out' (B.tagT T₁ k) T₁ x) =
      B.patchPlace tab out' (B.tagT T₁ k) T₁ (B.toKindAlg.copyG k x.1, x.2) := by
  obtain ⟨⟨⟨wc_, rq, rs, lg⟩, qs⟩, a⟩ := x
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
  change LogReg Req B.slots at lg
  simp only [KindAlg.blankFrom, Set.mem_preimage, Set.mem_setOf_eq, splitLogs,
    Equiv.coe_fn_mk] at hx
  have hk0 : lg k = none := hx k le_rfl
  by_cases hk : B.kind w = true
  · have hb : requestsBefore (Function.update lg k (some rq)) k = requestsBefore lg k :=
      requestsBefore_congr fun k' hk' => Function.update_of_ne (fun e => by subst e; omega) _ _
    show (copyPerm _ k _, qs) = _
    simp only [KindAlg.copyG, Equiv.prodCongr_apply, Prod.map, Equiv.coe_refl, id, copyPerm_apply]
    simp only [patchPlace, tagT, toKindAlg_kind_mk, AlgShape.CntW.work_mk, AlgShape.CntW.cnt_mk, AlgShape.PatchWS.fst_mk, hk, ite_true, augLogs] at *
    simp only [hk0, Option.map_none, Equiv.swap_apply_left]
    rw [hb, augLogs_update_of_blank T₁ hx]
  · have hk' : B.kind w = false := by simpa using hk
    show (copyPerm _ k _, qs) = _
    simp only [KindAlg.copyG, Equiv.prodCongr_apply, Prod.map, Equiv.coe_refl, id, copyPerm_apply,
      patchPlace, toKindAlg_kind_mk, AlgShape.CntW.work_mk, AlgShape.CntW.cnt_mk, AlgShape.PatchWS.fst_mk, hk']
    simp

/-- **The measurement of the tagged log of slot `k`** is that of `B`'s log, on matrices dephased in
the logs below `k`. -/
theorem dephase_place (k : Fin B.slots) (tg : B.BV → X → Option Y)
    {M : Matrix (B.toKindAlg.G × AncReg X Y B.width) (B.toKindAlg.G × AncReg X Y B.width) ℂ}
    (hM : dephase (B.toKindAlg.logsBelow k ∘ Prod.fst) M = M) :
    dephase ((B.patchTag tab out').toKindAlg.logAt k) (embed (B.patchPlace tab out' tg T₁) M) =
      embed (B.patchPlace tab out' tg T₁) (dephase (B.toKindAlg.logAt k ∘ Prod.fst) M) := by
  rw [dephase_embed]
  congr 1
  ext a b
  by_cases hab : B.toKindAlg.logsBelow k a.1 = B.toKindAlg.logsBelow k b.1
  · have hc : requestsBefore (splitLogs a.1).2 k = requestsBefore (splitLogs b.1).2 k :=
      requestsBefore_congr fun j hj => by
        have := congrFun hab j
        simpa [KindAlg.logsBelow, hj] using this
    have key : ((B.patchTag tab out').toKindAlg.logAt k (B.patchPlace tab out' tg T₁ a) =
        (B.patchTag tab out').toKindAlg.logAt k (B.patchPlace tab out' tg T₁ b)) ↔
        (B.toKindAlg.logAt k a.1 = B.toKindAlg.logAt k b.1) := by
      change (Option.map (fun r => (r, T₁ (requestsBefore (splitLogs a.1).2 k)))
          ((splitLogs a.1).2 k) =
        Option.map (fun r => (r, T₁ (requestsBefore (splitLogs b.1).2 k))) ((splitLogs b.1).2 k)) ↔
        ((splitLogs a.1).2 k = (splitLogs b.1).2 k)
      rw [hc, (Option.map_injective fun r r' h => (Prod.mk.inj h).1).eq_iff]
    simp only [dephase, Function.comp]
    exact if_congr key rfl rfl
  · rw [← hM]
    simp only [dephase, Function.comp, if_neg hab]
    split_ifs <;> rfl

variable {Ω₁ St₁ : Type} {Q₁ : ℕ} [OracleState St₁ X Y] (E₁ : Env Ω₁ Req Resp X Y Q₁ St₁) (ω₁ : Ω₁)

/-- **The reply of slot `k`** on the placed registers is `B`'s, when the reply to the tagged logs is
the reply of `E₁` to the logs. -/
theorem respG_place (k : Fin B.slots) (tg : B.BV → X → Option Y)
    (htg : ∀ w rq rs rs' lg, tg (w, rq, rs, lg) = tg (w, rq, rs', lg))
    (hans : ∀ lg : LogReg Req B.slots, E.answer ω (augLogs T₁ lg) k = E₁.answer ω₁ lg k)
    (x : B.toKindAlg.G × AncReg X Y B.width) :
    (B.patchTag tab out').toKindAlg.respG E ω k (B.patchPlace tab out' tg T₁ x) =
      B.patchPlace tab out' tg T₁ (B.toKindAlg.respG E₁ ω₁ k x.1, x.2) := by
  obtain ⟨⟨⟨wc_, rq, rs, lg⟩, qs⟩, a⟩ := x
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
  change LogReg Req B.slots at lg
  show (respondPerm _ _ _, qs) = _
  simp only [KindAlg.respG, Equiv.prodCongr_apply, Prod.map, Equiv.coe_refl, id,
    respondPerm_apply, patchPlace, toKindAlg_kind_mk, AlgShape.CntW.work_mk, AlgShape.CntW.cnt_mk, AlgShape.PatchWS.fst_mk]
  by_cases hk : B.kind w = true
  · simp only [hk, ite_true, hans, AlgShape.CntW.work_mk, AlgShape.CntW.cnt_mk]
    rw [htg (AlgShape.CntW.mk w c) rq]
  · simp only [hk]
    simp

end AdaptiveIAlg

end GordieHowe.Quantum
