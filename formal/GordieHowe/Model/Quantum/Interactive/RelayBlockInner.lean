-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.LeadDilate
public import GordieHowe.Model.Quantum.Interactive.AbsorbAssign
public import GordieHowe.Model.Quantum.Interactive.RelayBlockSwap
public import GordieHowe.Model.Quantum.Interactive.RelayBlockRel

@[expose] public section

/-!
# The inner tower of the absorbed adversary

The steps of the adversary with an assigning challenger absorbed (`AdaptiveIAlg.absorbAssignP`),
with its query counter, are Kraus maps after the basis permutations that end the previous slot
(`AdaptiveIAlg.leadsBy_absorbAssignP`): the end of the reprogrammed queries and the clearing of the
tag (`patchAfter`), then the store of the main reply, the relayed reply and the clearing of the
relayed request (`afterAt`). Its pure distinguisher with these leading unitaries
(`AdaptiveIAlg.leadPureD`) is the inner distinguisher of the relay.

- `AdaptiveIAlg.absLead`, `AdaptiveIAlg.leadsBy_absorb_step`: the absorbed step after `afterAt`.
- `AdaptiveIAlg.patchLead`, `AdaptiveIAlg.patchLeadPerm`, `AdaptiveIAlg.leadsBy_absorbAssignP_step`:
  the patched step after `patchAfter` and `afterAt`.
- `AdaptiveIAlg.innerK`, `AdaptiveIAlg.innerP`, `AdaptiveIAlg.leadsBy_absorbAssignP`: with the
  query counter.
-/

open Finset Matrix
open GordieHowe.Quantum.AssignRelay (sideRelay)
open scoped BigOperators Kronecker


namespace GordieHowe.Quantum

namespace AbsorbedWork

variable {W Req Resp Resp' : Type} {m : ℕ}

/-- **The store moved slot by slot**: slot `i`'s reply moved by `φ i`. -/
def mapStore (φ : Fin m → Equiv.Perm Resp') : Equiv.Perm (AbsorbedWork W Req Resp Resp' m) where
  toFun w := { w with store := fun i => Equiv.optionCongr (φ i) (w.store i) }
  invFun w := { w with store := fun i => (Equiv.optionCongr (φ i)).symm (w.store i) }
  left_inv w :=
    AbsorbedWork.ext rfl rfl rfl rfl (funext fun i => (Equiv.optionCongr (φ i)).symm_apply_apply _)
  right_inv w :=
    AbsorbedWork.ext rfl rfl rfl rfl (funext fun i => (Equiv.optionCongr (φ i)).apply_symm_apply _)

@[simp] theorem mapStore_work (φ : Fin m → Equiv.Perm Resp')
    (w : AbsorbedWork W Req Resp Resp' m) : (mapStore φ w).work = w.work := rfl
@[simp] theorem mapStore_request (φ : Fin m → Equiv.Perm Resp')
    (w : AbsorbedWork W Req Resp Resp' m) : (mapStore φ w).request = w.request := rfl
@[simp] theorem mapStore_response (φ : Fin m → Equiv.Perm Resp')
    (w : AbsorbedWork W Req Resp Resp' m) : (mapStore φ w).response = w.response := rfl
@[simp] theorem mapStore_logs (φ : Fin m → Equiv.Perm Resp')
    (w : AbsorbedWork W Req Resp Resp' m) : (mapStore φ w).logs = w.logs := rfl

theorem mapStore_refl : mapStore (W := W) (Req := Req) (Resp := Resp) (m := m)
    (fun _ => Equiv.refl Resp') = Equiv.refl _ :=
  Equiv.ext fun w => AbsorbedWork.ext rfl rfl rfl rfl (funext fun i => by
    change Option.map id (w.store i) = w.store i
    rw [Option.map_id, id])

@[simp]
theorem mapStore_store (φ : Fin m → Equiv.Perm Resp') (w : AbsorbedWork W Req Resp Resp' m)
    (i : Fin m) : (mapStore φ w).store i = Equiv.optionCongr (φ i) (w.store i) :=
  rfl

end AbsorbedWork

namespace MultiRelay

variable {Req Resp : Type} (J : Req → Bool) (swO : Equiv.Perm Resp)

/-- **The index of the first request satisfying `J`** among the entries. -/
def firstJIdx (es : List (Option Req)) : Option ℕ :=
  es.findIdx? fun e => e.any J

/-- `lastSwO` of the record of a list. -/
def lastSwOL (b Q : ℕ) (es : List (Option Req)) : Equiv.Perm Resp :=
  lastSwO J swO b Q (fun i : Fin es.length => es[(i : ℕ)]?)

variable {J swO}

theorem lastSwO_eq_lastSwOL (b Q : ℕ) {m : ℕ} (rec : Fin m → Option (Option Req)) :
    lastSwO J swO b Q rec = lastSwOL J swO b Q (recList rec) := by
  unfold lastSwOL lastSwO
  rw [recList_getElem? _ le_rfl]

theorem lastSwOL_eq (b Q : ℕ) (es : List (Option Req)) :
    lastSwOL J swO b Q es = if 0 < es.length then
      (match blkAt b Q es (es.length - 1), es.getD (es.length - 1) none with
        | .rel, some r => swOAt J swO r
        | _, _ => Equiv.refl _)
      else Equiv.refl _ := by
  unfold lastSwOL lastSwO
  rw [recList_getElem? _ le_rfl]
  rfl

/-- **The last slot's permutation is the identity when the last entry is not a request satisfying
`J`.** -/
theorem lastSwOL_of_not (b Q : ℕ) {es : List (Option Req)}
    (h : ∀ r, es.getLast? = some (some r) → J r = false) : lastSwOL J swO b Q es = Equiv.refl _
        := by
  rw [lastSwOL_eq]
  split_ifs with hl
  · have hg : es.getD (es.length - 1) none = (es.getLast?).bind id := by
      rw [List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]
      rcases es[es.length - 1]? with _ | e <;> simp
    rw [hg]
    generalize blkAt b Q es (es.length - 1) = bk
    rcases hlast : es.getLast? with _ | e
    · cases bk <;> rfl
    · rcases e with _ | r
      · cases bk <;> rfl
      · cases bk <;> simp [swOAt, h r hlast]
  · rfl

theorem lastSwOL_append_of_not (b Q : ℕ) (es : List (Option Req)) {e : Option Req}
    (he : ∀ r, e = some r → J r = false) : lastSwOL J swO b Q (es ++ [e]) = Equiv.refl _ :=
  lastSwOL_of_not b Q fun r hr => he r (by simpa using hr)

theorem firstJIdx_append_of_some {es : List (Option Req)} {i : ℕ}
    (h : firstJIdx J es = some i) (e : Option Req) : firstJIdx J (es ++ [e]) = some i := by
  unfold firstJIdx at h ⊢
  rw [List.findIdx?_append, h]
  rfl

theorem firstJIdx_append_of_none {es : List (Option Req)} (h : firstJIdx J es = none)
    {e : Option Req} (he : e.any J = false) : firstJIdx J (es ++ [e]) = none := by
  unfold firstJIdx at h ⊢
  rw [List.findIdx?_append, h]
  simp [he]

theorem firstJIdx_lt {es : List (Option Req)} {i : ℕ} (h : firstJIdx J es = some i) :
    i < es.length :=
  (List.findIdx?_eq_some_iff_getElem.1 h).1

theorem firstJIdx_eq_some {es : List (Option Req)} {i : ℕ} {r : Req}
    (hi : es[i]? = some (some r)) (hr : J r = true)
    (hpre : ∀ i' < i, ∀ r', es[i']? = some (some r') → J r' = false) :
    firstJIdx J es = some i := by
  unfold firstJIdx
  have hlt : i < es.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hi
    exact absurd hi (by simp)
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨hlt, ?_, fun i' hi' => ?_⟩
  · rw [List.getElem?_eq_getElem hlt] at hi
    simp [Option.some_inj.1 hi, hr]
  · have h' : es[i']? = some es[i'] := List.getElem?_eq_getElem (by omega)
    rcases he : es[i'] with _ | r'
    · simp
    · rw [he] at h'
      simp [hpre i' hi' r' h']

theorem firstJIdx_append_of_lt {es : List (Option Req)} (e : Option Req) {i : ℕ}
    (hi : i < es.length) : firstJIdx J (es ++ [e]) = some i ↔ firstJIdx J es = some i := by
  constructor
  · intro h
    unfold firstJIdx at h ⊢
    rw [List.findIdx?_append] at h
    rcases hf : List.findIdx? (fun e => e.any J) es with _ | i'
    · rw [hf, Option.none_or, Option.map_eq_some_iff] at h
      obtain ⟨a, -, ha⟩ := h
      omega
    · rw [hf] at h
      simp only [Option.some_or, Option.some.injEq] at h
      rw [hf, h]
  · exact fun h => firstJIdx_append_of_some h e

theorem lastSwOL_cases (b Q : ℕ) (es : List (Option Req)) :
    lastSwOL J swO b Q es = swO ∨ lastSwOL J swO b Q es = Equiv.refl _ := by
  rw [lastSwOL_eq]
  split_ifs
  · generalize blkAt b Q es (es.length - 1) = bk
    generalize es.getD (es.length - 1) none = e
    rcases e with _ | r
    · cases bk <;> simp
    · cases bk <;> simp only [swOAt] <;> (try split_ifs) <;> simp
  · exact Or.inr rfl

end MultiRelay

namespace AdaptiveIAlg

section Absorb

variable {X Y Req Resp O Req' Resp' : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req']
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (F : SideRelay Req Resp Req' Resp')

/-- **The absorbed step without its leading permutation**: the adversary's step, then the
relayed request of slot `k` written (`setAt`). -/
def absLead (k : StepIdx A.slots A.post) :
    KrausMap (A.absorb F).R (DReg (A.absorb F).W A.width X Y Req' Resp')
      (DReg (A.absorb F).W A.width X Y Req' Resp') :=
  (KrausMap.ofPerm (A.setAt F k)).comp
    ((A.liftedStep k).comp (KrausMap.ofPerm (Equiv.refl _)))

/-- **The absorbed step is `absLead` after `afterAt`.** -/
theorem leadsBy_absorb_step (k : StepIdx A.slots A.post) :
    ((A.absorb F).step k).LeadsBy (A.absLead F k) (A.afterAt F k) := by
  rw [show (A.absorb F).step k = _ from A.absorbStep_eq F k]
  exact ((KrausMap.leadsBy_refl _).comp_ofPerm _).ofPerm_comp _

end Absorb

section Layers

variable {X Y Req Resp O O' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shB : AlgShape X Y Req Resp} (B : AdaptiveIAlg shB O)
  (K₁ : StepIdx B.slots B.post →
    KrausMap B.R (DReg B.W B.width X Y Req Resp) (DReg B.W B.width X Y Req Resp))
  (Q : StepIdx B.slots B.post → Equiv.Perm (DReg B.W B.width X Y Req Resp))

/-- **The step with its query counter without its leading permutation**: `toKindAlg`'s step of
`K₁ k` in place of `B`'s step. -/
def cntLead (k : StepIdx B.slots B.post) :
    KrausMap B.R (DReg B.toKindAlg.W B.width X Y Req Resp)
      (DReg B.toKindAlg.W B.width X Y Req Resp) :=
  if (k : ℕ) < B.slots then
    ((((K₁ k).tensorId (Fin (B.budget + 2))).reindex B.cntSplit.symm).restrict
      B.inBudget).permConj (Equiv.refl _) B.cntShift
  else ((K₁ k).tensorId (Fin (B.budget + 2))).reindex B.cntSplit.symm

/-- The leading permutation with the query counter alongside. -/
def cntLeadPerm (k : StepIdx B.slots B.post) :
    Equiv.Perm (DReg B.toKindAlg.W B.width X Y Req Resp) :=
  B.cntSplit.symm.permCongr ((Q k).prodCongr (Equiv.refl _))

variable {B K₁ Q}

/-- **The step with its query counter is `cntLead` after `cntLeadPerm`**, for steps `B.step k =
K₁ k` after `Q k`. -/
theorem leadsBy_toKindAlg (h : ∀ k, (B.step k).LeadsBy (K₁ k) (Q k))
    (k : StepIdx B.slots B.post) :
    (B.toKindAlg.step k).LeadsBy (B.cntLead K₁ k) (B.cntLeadPerm Q k) := by
  by_cases hk : (k : ℕ) < B.slots
  · rw [show B.toKindAlg.step k = ((((B.step k).tensorId (Fin (B.budget + 2))).reindex
        B.cntSplit.symm).restrict B.inBudget).permConj (Equiv.refl _) B.cntShift from
        B.toKindAlg_step_of_lt hk]
    simp only [cntLead, hk, ite_true]
    exact ((((h k).tensorId _).reindex _).restrict _).permConj_refl _
  · rw [show B.toKindAlg.step k = ((B.step k).tensorId (Fin (B.budget + 2))).reindex
        B.cntSplit.symm from B.toKindAlg_step_of_not_lt hk]
    simp only [cntLead, hk, ite_false]
    exact ((h k).tensorId _).reindex _

theorem cntShift_permCongr {g : Equiv.Perm (DReg B.W B.width X Y Req Resp)}
    (hg : ∀ d, B.kind (g d).1.1 = B.kind d.1.1) (d : DReg B.toKindAlg.W B.width X Y Req Resp) :
    B.cntShift (B.cntSplit.symm.permCongr (g.prodCongr (Equiv.refl _)) d) =
      B.cntSplit.symm.permCongr (g.prodCongr (Equiv.refl _)) (B.cntShift d) := by
  obtain ⟨⟨⟨w, c⟩, q, a⟩, qs⟩ := d
  change ((((g ((w, q, a), qs)).1.1, (if B.kind (g ((w, q, a), qs)).1.1 then Equiv.refl _
      else finRotate _) c), (g ((w, q, a), qs)).1.2.1, (g ((w, q, a), qs)).1.2.2),
      (g ((w, q, a), qs)).2) = ((((g ((w, q, a), qs)).1.1, (if B.kind w then Equiv.refl _
      else finRotate _) c), (g ((w, q, a), qs)).1.2.1, (g ((w, q, a), qs)).1.2.2),
      (g ((w, q, a), qs)).2)
  rw [hg]

theorem tpShift_permCongr {g : Equiv.Perm (DReg B.W B.width X Y Req Resp)}
    (hg : ∀ d, B.kind (g d).1.1 = B.kind d.1.1) (d : DReg B.toKindAlg.W B.width X Y Req Resp) :
    B.tpShift (B.cntSplit.symm.permCongr (g.prodCongr (Equiv.refl _)) d) =
      B.cntSplit.symm.permCongr (g.prodCongr (Equiv.refl _)) (B.tpShift d) := by
  obtain ⟨⟨⟨w, c⟩, q, a⟩, qs⟩ := d
  change ((((g ((w, q, a), qs)).1.1, (if B.kind (g ((w, q, a), qs)).1.1 then Equiv.refl _
      else B.rot) c), (g ((w, q, a), qs)).1.2.1, (g ((w, q, a), qs)).1.2.2),
      (g ((w, q, a), qs)).2) = ((((g ((w, q, a), qs)).1.1, (if B.kind w then Equiv.refl _
      else B.rot) c), (g ((w, q, a), qs)).1.2.1, (g ((w, q, a), qs)).1.2.2),
      (g ((w, q, a), qs)).2)
  rw [hg]

theorem endSwap_permCongr (g : Equiv.Perm (DReg B.W B.width X Y Req Resp))
    (d : DReg B.toKindAlg.W B.width X Y Req Resp) :
    B.endSwap (B.cntSplit.symm.permCongr (g.prodCongr (Equiv.refl _)) d) =
      B.cntSplit.symm.permCongr (g.prodCongr (Equiv.refl _)) (B.endSwap d) := by
  obtain ⟨⟨⟨w, c⟩, q, a⟩, qs⟩ := d
  rfl

theorem inBudget_permCongr {g : Equiv.Perm (DReg B.W B.width X Y Req Resp)}
    (hg : ∀ d, B.kind (g d).1.1 = B.kind d.1.1) (d : DReg B.toKindAlg.W B.width X Y Req Resp) :
    B.inBudget (B.cntSplit.symm.permCongr (g.prodCongr (Equiv.refl _)) d) = B.inBudget d := by
  obtain ⟨⟨⟨w, c⟩, q, a⟩, qs⟩ := d
  exact congrArg (· || _) (hg (((w, q, a), qs)))

/-- **The step with its counter keeps a move of the registers beside the counter** that keeps the
kind, when the step does. -/
theorem keepsPerm_cntLead {g : Equiv.Perm (DReg B.W B.width X Y Req Resp)}
    (hg : ∀ d, B.kind (g d).1.1 = B.kind d.1.1) (h : ∀ k, (K₁ k).KeepsPerm g)
    (k : StepIdx B.slots B.post) :
    (B.cntLead K₁ k).KeepsPerm (B.cntSplit.symm.permCongr (g.prodCongr (Equiv.refl _))) := by
  unfold cntLead
  by_cases hk : (k : ℕ) < B.slots
  · simp only [hk, ↓reduceIte]
    refine ((((h k).tensorId _).reindex _).restrict fun d => ?_).permConj_refl
      (cntShift_permCongr hg)
    obtain ⟨⟨⟨w, c⟩, q, a⟩, qs⟩ := d
    have := hg (((w, q, a), qs))
    simp only [inBudget, AlgShape.inBudget, Equiv.permCongr_apply, Equiv.symm_symm, cntSplit,
        AlgShape.cntSplit, Equiv.coe_fn_mk,
      Equiv.coe_fn_symm_mk, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply]
    exact congrArg (· || _) this
  · simp only [hk, ↓reduceIte]
    exact ((h k).tensorId _).reindex _

/-- **The step with its counter keeps the registers beside the counter that the step keeps.** -/
theorem keepsReg_cntLead {V : Type*} {f g : StepIdx B.slots B.post → DReg B.W B.width X Y Req
    Resp → V}
    (h : ∀ k, (K₁ k).KeepsReg (f k) (g k)) (k : StepIdx B.slots B.post) :
    (B.cntLead K₁ k).KeepsReg (fun d => f k (B.cntSplit d).1) fun d => g k (B.cntSplit d).1 := by
  unfold cntLead
  by_cases hk : (k : ℕ) < B.slots
  · simp only [hk, ↓reduceIte]
    exact (((((h k).tensorId_fst).reindex _).restrict _).permConj_refl _).mono_left fun _ => rfl
  · simp only [hk, ↓reduceIte]
    exact ((h k).tensorId_fst).reindex _

variable (K₁) in
/-- **The adversary's Kraus map with its counter alongside, without its leading permutation**:
`cntKraus` of `K₁ k`. -/
def cntKrausLead (k : StepIdx B.slots B.post) :
    KrausMap B.R (DReg B.toKindAlg.W B.width X Y Req Resp)
      (DReg B.toKindAlg.W B.width X Y Req Resp) :=
  ((K₁ k).tensorId (Fin (B.budget + 2))).reindex B.cntSplit.symm

theorem leadsBy_cntKraus (h : ∀ k, (B.step k).LeadsBy (K₁ k) (Q k)) (k : StepIdx B.slots B.post) :
    (B.cntKraus k).LeadsBy (B.cntKrausLead K₁ k) (B.cntLeadPerm Q k) :=
  ((h k).tensorId _).reindex _

theorem keepsPerm_cntKrausLead {g : Equiv.Perm (DReg B.W B.width X Y Req Resp)}
    (h : ∀ k, (K₁ k).KeepsPerm g) (k : StepIdx B.slots B.post) :
    (B.cntKrausLead K₁ k).KeepsPerm (B.cntSplit.symm.permCongr (g.prodCongr (Equiv.refl _))) :=
  ((h k).tensorId _).reindex _

theorem keepsReg_cntKrausLead {V : Type*}
    {f g : StepIdx B.slots B.post → DReg B.W B.width X Y Req Resp → V}
    (h : ∀ k, (K₁ k).KeepsReg (f k) (g k)) (k : StepIdx B.slots B.post) :
    (B.cntKrausLead K₁ k).KeepsReg (fun d => f k (B.cntSplit d).1) fun d => g k (B.cntSplit d).1 :=
  ((h k).tensorId_fst).reindex _

variable (K₁) in
/-- **The operators of the trace-preserving form without the leading permutation**: `tpRaw` with
`cntKrausLead` in place of `cntKraus`, without the halting operators. -/
noncomputable def tpLead (k : StepIdx B.slots B.post) :
    B.R ⊕ (B.R ⊕ Fin (B.budget + 2)) → Matrix B.CReg B.CReg ℂ
  | .inl r => if (k : ℕ) < B.slots then
      (((B.cntKrausLead K₁ k).restrict B.inBudget).permConj (Equiv.refl _) B.tpShift).op r
    else (B.cntKrausLead K₁ k).op r
  | .inr (.inl r) => if (k : ℕ) < B.slots then
      (((B.cntKrausLead K₁ k).restrict fun d => !B.inBudget d).permConj (Equiv.refl _)
        B.endSwap).op r
    else 0
  | .inr (.inr _) => 0

/-- **The operators of the trace-preserving form of a trace-preserving adversary are those
without the leading permutation after it.** -/
theorem tpRaw_eq_tpLead (hB : B.TracePreserving) (h : ∀ k, (B.step k).LeadsBy (K₁ k) (Q k))
    (k : StepIdx B.slots B.post) (z : B.R ⊕ (B.R ⊕ Fin (B.budget + 2))) (a b : B.CReg) :
    B.tpRaw k z a b = B.tpLead K₁ k z a (B.cntLeadPerm Q k b) := by
  rcases z with r | r | c
  · by_cases hk : (k : ℕ) < B.slots
    · simp only [tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, tpLead, hk, ↓reduceIte]
      exact (((B.leadsBy_cntKraus h k).restrict _).permConj_refl _) r a b
    · simp only [tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, tpLead, hk, ↓reduceIte]
      exact (B.leadsBy_cntKraus h k) r a b
  · by_cases hk : (k : ℕ) < B.slots
    · simp only [tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, tpLead, hk, ↓reduceIte]
      exact (((B.leadsBy_cntKraus h k).restrict _).permConj_refl _) r a b
    · simp only [tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, tpLead, hk, ↓reduceIte]
      rfl
  · simp only [tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, tpLead, hB.haltOp_eq_zero k,
      Matrix.zero_kronecker, Matrix.submatrix_zero]
    rfl

/-- **The operators without the leading permutation keep a move of the registers beside the
counter** that keeps the kind, when the steps do. -/
theorem tpLead_perm {g : Equiv.Perm (DReg B.W B.width X Y Req Resp)}
    (hg : ∀ d, B.kind (g d).1.1 = B.kind d.1.1) (h : ∀ k, (K₁ k).KeepsPerm g)
    (k : StepIdx B.slots B.post) (z : B.R ⊕ (B.R ⊕ Fin (B.budget + 2))) (a b : B.CReg) :
    B.tpLead K₁ k z (B.cntSplit.symm.permCongr (g.prodCongr (Equiv.refl _)) a)
      (B.cntSplit.symm.permCongr (g.prodCongr (Equiv.refl _)) b) = B.tpLead K₁ k z a b := by
  have hc := B.keepsPerm_cntKrausLead h k
  rcases z with r | r | c
  · by_cases hk : (k : ℕ) < B.slots
    · simp only [tpLead, hk, ↓reduceIte]
      exact ((hc.restrict (inBudget_permCongr hg)).permConj_refl (tpShift_permCongr hg)) r a b
    · simp only [tpLead, hk, ↓reduceIte]
      exact hc r a b
  · by_cases hk : (k : ℕ) < B.slots
    · simp only [tpLead, hk, ↓reduceIte]
      exact ((hc.restrict fun d => congrArg (!·) (inBudget_permCongr hg d)).permConj_refl
        (endSwap_permCongr g)) r a b
    · simp only [tpLead, hk, ↓reduceIte, Matrix.zero_apply]
  · rfl

/-- **The operators without the leading permutation read a register through the steps'
reading**, with the counter moves on the rows. -/
theorem tpLead_keeps {V : Type*} {f g : StepIdx B.slots B.post → DReg B.W B.width X Y Req Resp → V}
    (h : ∀ k, (K₁ k).KeepsReg (f k) (g k)) (k : StepIdx B.slots B.post)
    (z : B.R ⊕ (B.R ⊕ Fin (B.budget + 2))) (a b : B.CReg) (hab : B.tpLead K₁ k z a b ≠ 0) :
    f k (B.cntSplit a).1 = g k (B.cntSplit b).1 := by
  have hc := B.keepsReg_cntKrausLead h k
  rcases z with r | r | c
  · by_cases hk : (k : ℕ) < B.slots
    · simp only [tpLead, hk, ↓reduceIte] at hab
      exact (((hc.restrict _).permConj_refl _).mono_left fun _ => rfl) r a b hab
    · simp only [tpLead, hk, ↓reduceIte] at hab
      exact hc r a b hab
  · by_cases hk : (k : ℕ) < B.slots
    · simp only [tpLead, hk, ↓reduceIte] at hab
      exact (((hc.restrict _).permConj_refl _).mono_left fun _ => rfl) r a b hab
    · simp only [tpLead, hk, ↓reduceIte, Matrix.zero_apply] at hab
      exact absurd rfl hab
  · exact absurd rfl hab

/-- **The entries of the frozen operators**: the identity on the ended columns at the halting
operator of the ended value; the operator of the trace-preserving form on the other columns. -/
theorem tpOp_true_apply (k : StepIdx B.slots B.post) (z : B.R ⊕ (B.R ⊕ Fin (B.budget + 2)))
    (y x : B.CReg) :
    B.tpOp true k z y x = if B.isEndSlot z then (if x.workspace.cnt = B.ended then
        (1 : Matrix B.CReg B.CReg ℂ) y x else 0)
      else if x.workspace.cnt = B.ended then 0 else B.tpRaw k z y x := by
  simp only [tpOp_eq, ↓reduceIte]
  split_ifs with h1 h2 h2
  · simp only [endedMask, AlgShape.endedMask, Matrix.diagonal_apply, Matrix.one_apply]
    by_cases hyx : y = x
    · subst hyx
      simp [h2]
    · simp [hyx]
  · simp only [endedMask, AlgShape.endedMask, Matrix.diagonal_apply]
    by_cases hyx : y = x
    · subst hyx
      simp [h2]
    · simp [hyx]
  · simp [aliveMask, AlgShape.aliveMask, Matrix.mul_diagonal, h2]
  · simp [aliveMask, AlgShape.aliveMask, Matrix.mul_diagonal, h2]

theorem rot_ne_ended {c : Fin (B.budget + 2)} (hc : c ≠ B.ended) : B.rot c ≠ B.ended := by
  unfold rot AlgShape.rot
  rw [Equiv.trans_apply]
  intro h
  rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h
  apply hc
  apply (finRotate _).injective
  rw [h, ended, AlgShape.ended, finRotate_last]

theorem cntKrausLead_cnt (k : StepIdx B.slots B.post) (r : B.R) (a b : B.CReg)
    (h : (B.cntKrausLead K₁ k).op r a b ≠ 0) : a.workspace.cnt = b.workspace.cnt :=
  ((KrausMap.keepsReg_tensorId_snd (K₁ k) fun c : Fin (B.budget + 2) => c).reindex
    B.cntSplit.symm) r a b h

/-- **The operators without the leading permutation keep a live counter live, except the cut ones,
which end it on query branches.** -/
theorem tpLead_cnt (k : StepIdx B.slots B.post) (z : B.R ⊕ (B.R ⊕ Fin (B.budget + 2)))
    (a b : B.CReg) (h : B.tpLead K₁ k z a b ≠ 0) (hb : b.workspace.cnt ≠ B.ended) :
    (∀ r, z = .inl r → a.workspace.cnt ≠ B.ended) ∧
      (∀ r, z = .inr (.inl r) → a.workspace.cnt = B.ended ∧ B.kind a.workspace.work = false) := by
  rcases z with r | r | c
  · refine ⟨fun r' _ => ?_, fun r' h' => by cases h'⟩
    by_cases hk : (k : ℕ) < B.slots
    · simp only [tpLead, hk, ↓reduceIte] at h
      erw [restrict_permConj_op_apply] at h
      have hc := B.cntKrausLead_cnt k r _ b (right_ne_zero_of_mul h)
      obtain ⟨⟨wc_, q, a'⟩, qs⟩ := a
      obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
      have e : (B.tpShift.symm (((AlgShape.CntW.mk w c), q, a'), qs)).workspace.cnt =
          ((if B.kind w then Equiv.refl _ else B.rot).symm c) := by
        unfold tpShift AlgShape.tpShift AlgShape.wPerm
        rfl
      change ((if B.kind w then Equiv.refl _ else B.rot).symm c) = b.workspace.cnt at hc
      change c ≠ B.ended
      by_cases hw : B.kind w
      · rw [if_pos hw] at hc
        rw [← hc] at hb
        exact hb
      · rw [if_neg hw] at hc
        intro hce
        apply hb
        rw [← hc, hce]
        rw [Equiv.symm_apply_eq]
        unfold rot AlgShape.rot
        rw [Equiv.trans_apply, ended, AlgShape.ended, finRotate_last, Equiv.swap_apply_left]
    · simp only [tpLead, hk, ↓reduceIte] at h
      rw [B.cntKrausLead_cnt k r a b h]
      exact hb
  · refine ⟨(fun r' h' => by cases h'), fun r' _ => ?_⟩
    by_cases hk : (k : ℕ) < B.slots
    · simp only [tpLead, hk, ↓reduceIte] at h
      erw [restrict_permConj_op_apply] at h
      have hin := left_ne_zero_of_mul h
      have hc := B.cntKrausLead_cnt k r _ b (right_ne_zero_of_mul h)
      obtain ⟨⟨wc_, q, a'⟩, qs⟩ := a
      obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
      change (if (!(B.kind w || decide (Equiv.swap (Fin.castSucc (Fin.last B.budget)) B.ended c ≠
        Fin.castSucc (Fin.last B.budget)))) = true then (1 : ℂ) else 0) ≠ 0 at hin
      have hin' : B.kind w = false ∧ Equiv.swap (Fin.castSucc (Fin.last B.budget)) B.ended c =
          Fin.castSucc (Fin.last B.budget) := by
        split_ifs at hin with hh
        · simpa using hh
        · exact absurd rfl hin
      refine ⟨?_, hin'.1⟩
      change c = B.ended
      have := hin'.2
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at this
      exact this
    · simp only [tpLead, hk, ↓reduceIte, Matrix.zero_apply] at h
      exact absurd rfl h
  · exact absurd rfl h

variable [AddGroup Y] [Nonempty X] [Nonempty Y] (tab : B.W → X → Option Y) (out' : B.W → O')

variable (K₁ Q) in
/-- **The patched step without its leading permutation**: `patchBefore`, then `K₁ k` on `B`'s
registers. -/
def patchLead (k : StepIdx B.slots B.post) :
    KrausMap (B.patchTag tab out').R B.PatchReg B.PatchReg :=
  (KrausMap.ofPerm (B.patchBefore tab k)).comp
    ((((K₁ k).tensorId (AncReg X Y B.width × (X → Option Y))).reindex B.patchSplitB.symm).comp
      (KrausMap.ofPerm (Equiv.refl _)))

variable (Q) in
/-- The leading permutation of the patched step: `patchAfter`, then `Q k` on `B`'s registers. -/
def patchLeadPerm (k : StepIdx B.slots B.post) : Equiv.Perm B.PatchReg :=
  (B.patchAfter tab k).trans (B.patchSplitB.symm.permCongr ((Q k).prodCongr (Equiv.refl _)))

/-- **The patched step is `patchLead` after `patchLeadPerm`**, for steps `B.step k = K₁ k` after
`Q k`. -/
theorem leadsBy_patchTag (h : ∀ k, (B.step k).LeadsBy (K₁ k) (Q k))
    (k : StepIdx B.slots B.post) :
    ((B.patchTag tab out').step k).LeadsBy (B.patchLead K₁ tab out' k)
      (B.patchLeadPerm Q tab k) := by
  rw [patchTag_step]
  exact ((((h k).tensorId _).reindex _).comp_ofPerm _).ofPerm_comp _

/-- **The patched step without its leading permutation keeps a register of `B`'s registers** that
`K₁` and `patchBefore` keep. -/
theorem keepsReg_patchLead {V : Type*} {f g : DReg B.W B.width X Y Req Resp → V}
    (h : ∀ k, (K₁ k).KeepsReg f g) (k : StepIdx B.slots B.post)
    (hP : ∀ d, f (B.patchSplitB (B.patchBefore tab k d)).1 = f (B.patchSplitB d).1) :
    (B.patchLead K₁ tab out' k).KeepsReg (fun d => f (B.patchSplitB d).1)
      fun d => g (B.patchSplitB d).1 :=
  (KrausMap.keepsReg_ofPerm_of hP).comp
    ((((h k).tensorId_fst).reindex _).comp (KrausMap.keepsReg_ofPerm_of fun _ => rfl))

/-- **The patched step without its leading permutation reads the registers beside `B`'s** through
`patchBefore` and `K₁`'s reading of `B`'s registers. -/
theorem keepsReg_patchLead_rest {V : Type*}
    {f g : StepIdx B.slots B.post → DReg B.W B.width X Y Req Resp → V}
    (h : ∀ k, (K₁ k).KeepsReg (f k) (g k)) (k : StepIdx B.slots B.post) :
    (B.patchLead K₁ tab out' k).KeepsReg
      (fun e => (f k (B.patchSplitB ((B.patchBefore tab k).symm e)).1,
        (B.patchSplitB ((B.patchBefore tab k).symm e)).2))
      fun e => (g k (B.patchSplitB e).1, (B.patchSplitB e).2) :=
  (KrausMap.keepsReg_ofPerm _ _).comp
    ((((h k).tensorId_pair).reindex _).comp (KrausMap.keepsReg_ofPerm_of fun _ => rfl))

end Layers

section Swaps

variable {X Y Req Resp O Req' Resp' : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req']
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (F : SideRelay Req Resp Req' Resp')
  (φs : Fin A.slots → Equiv.Perm Resp') (φa : Equiv.Perm Resp')

/-- **The store and the main response register moved** on the absorbed registers. -/
def absSw : Equiv.Perm (DReg (A.absorb F).W A.width X Y Req' Resp') :=
  ((AbsorbedWork.mapStore φs).prodCongr
    ((Equiv.refl _).prodCongr (Equiv.optionCongr φa))).prodCongr (Equiv.refl _)

theorem absSw_eq : A.absSw F φs φa = A.absSplit.symm.permCongr ((Equiv.refl _).prodCongr
    ((Equiv.refl _).prodCongr ((Equiv.piCongrRight fun i => Equiv.optionCongr (φs i)).prodCongr
      ((Equiv.refl _).prodCongr (Equiv.optionCongr φa))))) := by
  ext ⟨⟨w, q, a⟩, qs⟩ <;> rfl

theorem setAt_absSw (k : ℕ) (d : DReg (A.absorb F).W A.width X Y Req' Resp') :
    A.setAt F k (A.absSw F φs φa d) = A.absSw F φs φa (A.setAt F k d) := by
  rw [AdaptiveIAlg.setAt_def]
  split_ifs
  · obtain ⟨⟨w, q, a⟩, qs⟩ := d
    by_cases hw : A.kind w.work
    · simp only [setPerm, AlgShape.setPerm, Function.Involutive.toPerm, Equiv.coe_fn_mk, absSw,
        Equiv.prodCongr_apply,
        Prod.map, AbsorbedWork.mapStore_work, hw, if_true, Equiv.refl_apply,
        AbsorbedWork.mapStore_logs, AbsorbedWork.mapStore_request]
      rfl
    · simp only [setPerm, AlgShape.setPerm, Function.Involutive.toPerm, Equiv.coe_fn_mk, absSw,
        Equiv.prodCongr_apply,
        Prod.map, AbsorbedWork.mapStore_work, hw, Bool.false_eq_true, ↓reduceIte]
  · rfl

/-- **The absorbed step without its leading permutation keeps the moves of the store and the
main response register.** -/
theorem keepsPerm_absLead (k : StepIdx A.slots A.post) :
    (A.absLead F k).KeepsPerm (A.absSw F φs φa) := by
  refine (KrausMap.keepsPerm_ofPerm (A.setAt_absSw F φs φa k)).comp
    (KrausMap.KeepsPerm.comp ?_ (KrausMap.keepsPerm_ofPerm fun _ => rfl))
  rw [absSw_eq]
  exact (KrausMap.KeepsPerm.tensorId (K := A.step k) (fun _ _ _ => rfl) _).reindex _

/-- The store and the main response register of the absorbed registers. -/
def storeResp (d : DReg (A.absorb F).W A.width X Y Req' Resp') :
    (Fin A.slots → Option Resp') × Option Resp' :=
  (d.1.1.store, d.1.2.2)

theorem storeResp_setAt (k : ℕ) (d : DReg (A.absorb F).W A.width X Y Req' Resp') :
    A.storeResp F (A.setAt F k d) = A.storeResp F d := by
  rw [AdaptiveIAlg.setAt_def]
  split_ifs
  · obtain ⟨⟨w, q, a⟩, qs⟩ := d
    by_cases hw : A.kind w.work
    · simp only [setPerm, AlgShape.setPerm, Function.Involutive.toPerm, Equiv.coe_fn_mk, hw,
        ↓reduceIte]
      rfl
    · simp only [setPerm, AlgShape.setPerm, Function.Involutive.toPerm, Equiv.coe_fn_mk, hw,
        Bool.false_eq_true,
        ↓reduceIte]
  · rfl

/-- **The absorbed step without its leading permutation keeps the store and the main response
register.** -/
theorem keepsReg_absLead (k : StepIdx A.slots A.post) :
    (A.absLead F k).KeepsReg (A.storeResp F) (A.storeResp F) :=
  (KrausMap.keepsReg_ofPerm_of (A.storeResp_setAt F k)).comp
    (KrausMap.KeepsReg.comp (KrausMap.KeepsReg.reindex
      (KrausMap.keepsReg_tensorId_snd (A.step k)
        fun p : A.AbsRest (Req' := Req') (Resp' := Resp') => (p.2.1, p.2.2.2)) A.absSplit.symm)
      (KrausMap.keepsReg_ofPerm_of fun _ => rfl))

theorem afterPerm_absSw_of_none (j : Fin A.slots) (d : DReg (A.absorb F).W A.width X Y Req' Resp')
    (h : d.1.1.logs j = none) :
    A.afterPerm F j (A.absSw F φs φa d) = A.absSw F φs φa (A.afterPerm F j d) := by
  rw [A.afterPerm_of_none F j h, A.afterPerm_of_none F j (d := A.absSw F φs φa d) h]

/-- **After a slot with a request, the move of the main response register moves the stored reply**,
on a blank store slot, for relayed replies that do not read the move. -/
theorem afterPerm_absSw_of_some (j : Fin A.slots) {r : Req}
    (d : DReg (A.absorb F).W A.width X Y Req' Resp') (h : d.1.1.logs j = some r)
    (hs : d.1.1.store j = none)
    (hF : ∀ c v, F.answer c r (Equiv.optionCongr φa v) = F.answer c r v) :
    A.afterPerm F j (A.absSw F φs φa d) =
      A.absSw F (Function.update φs j φa) (Equiv.refl _) (A.afterPerm F j d) := by
  rw [A.afterPerm_of_some F j (r := r) h, A.afterPerm_of_some F j (r := r) (d := A.absSw F φs φa
      d) h]
  obtain ⟨⟨w, q, a⟩, qs⟩ := d
  simp only [absSw, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, AbsorbedWork.mapStore_work,
    AbsorbedWork.mapStore_request, AbsorbedWork.mapStore_response, AbsorbedWork.mapStore_logs,
    AbsorbedWork.mapStore_store]
  simp only at hs h
  refine Prod.ext (Prod.ext (AbsorbedWork.ext rfl rfl ?_ rfl ?_) (Prod.ext rfl ?_)) rfl
  · simp only [AbsorbedWork.mapStore_response, hF]
  · funext i
    by_cases hi : i = j
    · subst hi
      simp
    · simp [Function.update_of_ne hi]
  · simp [hs]

/-- The registers of the absorbed adversary beside the adversary's. -/
def absRest (d : DReg (A.absorb F).W A.width X Y Req' Resp') :
    A.AbsRest (Req' := Req') (Resp' := Resp') :=
  (A.absSplit d).2

theorem setAt_symm (k : ℕ) : (A.setAt F k).symm = A.setAt F k := by
  rw [AdaptiveIAlg.setAt_def]
  split_ifs
  · exact Function.Involutive.toPerm_symm _
  · rfl

/-- **The absorbed step without its leading permutation reads the registers beside the
adversary's through `setAt`.** -/
theorem keepsReg_absLead_rest (k : StepIdx A.slots A.post) :
    (A.absLead F k).KeepsReg (fun z => A.absRest F (A.setAt F k z)) (A.absRest F) :=
  ((KrausMap.keepsReg_ofPerm _ _).mono_left fun z => by rw [setAt_symm]; rfl).comp
    (KrausMap.KeepsReg.comp (KrausMap.KeepsReg.reindex
      (KrausMap.keepsReg_tensorId_snd (A.step k)
        fun p : A.AbsRest (Req' := Req') (Resp' := Resp') => p) A.absSplit.symm)
      (KrausMap.keepsReg_ofPerm_of fun _ => rfl))

/-- **`afterAt` along the moves of the store and the response register**: when it stores a main
reply into a blank store slot, the move of the response register moves the stored reply; else the
moves are kept. -/
theorem afterAt_absSw (k : ℕ) (d : DReg (A.absorb F).W A.width X Y Req' Resp')
    (hF : ∀ c r v, F.answer c r (Equiv.optionCongr φa v) = F.answer c r v)
    (hs : ∀ h : 0 < k ∧ k - 1 < A.slots, (d.1.1.logs ⟨k - 1, h.2⟩).isSome →
      d.1.1.store ⟨k - 1, h.2⟩ = none) :
    A.afterAt F k (A.absSw F φs φa d) =
      if h : 0 < k ∧ k - 1 < A.slots then
        (if (d.1.1.logs ⟨k - 1, h.2⟩).isSome then
          A.absSw F (Function.update φs ⟨k - 1, h.2⟩ φa) (Equiv.refl _) (A.afterAt F k d)
        else A.absSw F φs φa (A.afterAt F k d))
      else A.absSw F φs φa (A.afterAt F k d) := by
  rw [AdaptiveIAlg.afterAt_def]
  by_cases hk : 0 < k ∧ k - 1 < A.slots
  · rw [dif_pos hk, dif_pos hk]
    rcases hl : d.1.1.logs ⟨k - 1, hk.2⟩ with _ | r
    · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      exact A.afterPerm_absSw_of_none F φs φa _ d hl
    · simp only [Option.isSome_some, ↓reduceIte]
      exact A.afterPerm_absSw_of_some F φs φa _ d hl (hs hk (by simp [hl])) (fun c => hF c r)
  · rw [dif_neg hk, dif_neg hk]
    rfl

theorem storeResp_afterAt (k : ℕ) (d : DReg (A.absorb F).W A.width X Y Req' Resp') :
    A.storeResp F (A.afterAt F k d) =
      if h : 0 < k ∧ k - 1 < A.slots then
        (if (d.1.1.logs ⟨k - 1, h.2⟩).isSome then
          (Function.update d.1.1.store ⟨k - 1, h.2⟩ d.1.2.2, d.1.1.store ⟨k - 1, h.2⟩)
        else (d.1.1.store, d.1.2.2))
      else (d.1.1.store, d.1.2.2) := by
  rw [AdaptiveIAlg.afterAt_def]
  by_cases hk : 0 < k ∧ k - 1 < A.slots
  · rw [dif_pos hk, dif_pos hk]
    rcases hl : d.1.1.logs ⟨k - 1, hk.2⟩ with _ | r
    · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      rw [A.afterPerm_of_none F _ hl]
      rfl
    · simp only [Option.isSome_some, ↓reduceIte]
      rw [A.afterPerm_of_some F _ hl]
      rfl
  · rw [dif_neg hk, dif_neg hk]
    rfl

theorem logs_afterAt (k : ℕ) (d : DReg (A.absorb F).W A.width X Y Req' Resp') :
    (A.afterAt F k d).1.1.logs = d.1.1.logs := by
  rw [AdaptiveIAlg.afterAt_def]
  split_ifs with hk
  · rcases hl : d.1.1.logs ⟨k - 1, hk.2⟩ with _ | r
    · rw [A.afterPerm_of_none F _ hl]
    · rw [A.afterPerm_of_some F _ hl]
  · rfl

theorem req_afterAt (k : ℕ) (d : DReg (A.absorb F).W A.width X Y Req' Resp') :
    (A.afterAt F k d).1.2.1 = if h : 0 < k ∧ k - 1 < A.slots then
      (d.1.1.logs ⟨k - 1, h.2⟩).elim d.1.2.1
        (fun r => Equiv.swap default (F.route (A.reqCount d.1.1.logs ⟨k - 1, h.2⟩) r) d.1.2.1)
      else d.1.2.1 := by
  rw [AdaptiveIAlg.afterAt_def]
  split_ifs with hk
  · rcases hl : d.1.1.logs ⟨k - 1, hk.2⟩ with _ | r
    · rw [A.afterPerm_of_none F _ hl]
      rfl
    · rw [A.afterPerm_of_some F _ hl]
      rfl
  · rfl

end Swaps

section PatchSwaps

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [AddGroup Y]
  {shB : AlgShape X Y Req Resp} (B : AdaptiveIAlg shB O) (tab : B.W → X → Option Y) (g : Equiv.Perm B.W)
  (φa : Equiv.Perm Resp)

/-- **A move of the workspace and of the response register on the patched registers.** -/
def patchLiftW : Equiv.Perm B.PatchReg :=
  ((g.prodCongr (Equiv.refl _)).prodCongr
    ((Equiv.refl _).prodCongr (Equiv.optionCongr φa))).prodCongr (Equiv.refl _)

theorem patchLiftW_eq : B.patchLiftW g φa = B.patchSplitB.symm.permCongr
    ((((g.prodCongr ((Equiv.refl _).prodCongr (Equiv.optionCongr φa))).prodCongr
      (Equiv.refl _))).prodCongr (Equiv.refl _)) := by
  ext ⟨⟨⟨w, an⟩, ⟨q, t⟩, a⟩, qs⟩ <;> rfl

theorem patchLiftW_apply (d : B.PatchReg) :
    B.patchLiftW g φa d =
      (@Prod.mk B.PatchW _ (g d.1.1.1, d.1.1.2) (d.1.2.1, Option.map φa d.1.2.2), d.2) := rfl

theorem patchSplit_apply (d : B.PatchReg) :
    B.patchSplit d = (((d.1.1.1, d.1.2.1, d.1.2.2), d.2), d.1.1.2) := rfl

theorem patchSplit_symm_apply (p : QueryReg B.PatchV B.width X Y × AncReg X Y B.width) :
    B.patchSplit.symm p =
      (@Prod.mk B.PatchW _ (p.1.1.1, p.2) (p.1.1.2.1, p.1.1.2.2), p.1.2) := rfl

variable {B tab g}

theorem tagP_patchLiftW (hg : ∀ w, tab (g w) = tab w) {on : B.W → Bool}
    (hon : ∀ w, on (g w) = on w) (d : B.PatchReg) :
    B.tagP tab on (B.patchLiftW g φa d) = B.patchLiftW g φa (B.tagP tab on d) := by
  obtain ⟨⟨⟨w, an⟩, ⟨q, t⟩, a⟩, qs⟩ := d
  by_cases h : on w
  · simp only [tagP, AlgShape.tagP, Function.Involutive.toPerm, Equiv.coe_fn_mk, patchLiftW_apply,
      Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, hon, h, hg, ↓reduceIte] <;> rfl
  · simp only [tagP, AlgShape.tagP, Function.Involutive.toPerm, Equiv.coe_fn_mk, patchLiftW_apply,
      Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, hon, h, Bool.false_eq_true, ↓reduceIte] <;> rfl

theorem swapP_patchLiftW (hg : ∀ w, tab (g w) = tab w) {on : B.W → Bool}
    (hon : ∀ w, on (g w) = on w) (d : B.PatchReg) :
    B.swapP tab on (B.patchLiftW g φa d) = B.patchLiftW g φa (B.swapP tab on d) := by
  rw [swapP, AlgShape.swapP, Equiv.permCongr_apply, Equiv.permCongr_apply]
  simp only [Equiv.permCongr_apply, Equiv.symm_symm, patchSplit_apply, patchSplit_symm_apply,
    liftPairs_apply, patchLiftW_apply, Equiv.prodCongr_apply, Prod.map,
    Equiv.refl_apply, hon, hg] <;> rfl

theorem finishP_patchLiftW (hg : ∀ w, tab (g w) = tab w) {on : B.W → Bool}
    (hon : ∀ w, on (g w) = on w) (d : B.PatchReg) :
    B.finishP tab on (B.patchLiftW g φa d) = B.patchLiftW g φa (B.finishP tab on d) := by
  rw [finishP, AlgShape.finishP, Equiv.permCongr_apply, Equiv.permCongr_apply]
  simp only [Equiv.permCongr_apply, Equiv.symm_symm, patchSplit_apply, patchSplit_symm_apply,
    liftPairs_apply, patchLiftW_apply, Equiv.prodCongr_apply, Prod.map,
    Equiv.refl_apply, hon, hg] <;> rfl

theorem patchBefore_patchLiftW (hg : ∀ w, tab (g w) = tab w) (hk : ∀ w, B.kind (g w) = B.kind w)
    (k : ℕ) (d : B.PatchReg) :
    B.patchBefore tab k (B.patchLiftW g φa d) = B.patchLiftW g φa (B.patchBefore tab k d) := by
  rw [AdaptiveIAlg.patchBefore_def]
  split_ifs
  · simp only [Equiv.trans_apply]
    rw [tagP_patchLiftW φa hg hk, swapP_patchLiftW φa hg (fun w => by rw [hk])]
  · exact swapP_patchLiftW φa hg (fun _ => rfl) d
  · rfl

theorem patchAfter_patchLiftW (hg : ∀ w, tab (g w) = tab w) (hk : ∀ w, B.kind (g w) = B.kind w)
    (k : ℕ) (d : B.PatchReg) :
    B.patchAfter tab k (B.patchLiftW g φa d) = B.patchLiftW g φa (B.patchAfter tab k d) := by
  rw [AdaptiveIAlg.patchAfter_def]
  split_ifs
  · simp only [Equiv.trans_apply]
    rw [tagP_patchLiftW φa hg hk, finishP_patchLiftW φa hg (fun w => by rw [hk])]
  · exact finishP_patchLiftW φa hg (fun _ => rfl) d
  · rfl

variable (tab) in
theorem resp_tagP (on : B.W → Bool) (d : B.PatchReg) : ((B.tagP tab on) d).1.2.2 = d.1.2.2 := by
  change (if on d.1.1.1 then _ else d).1.2.2 = _
  split_ifs <;> rfl

variable (tab) in
theorem resp_patchBefore (k : ℕ) (d : B.PatchReg) : ((B.patchBefore tab k) d).1.2.2 = d.1.2.2 := by
  rw [AdaptiveIAlg.patchBefore_def]
  split_ifs
  · rw [Equiv.trans_apply]
    exact B.resp_tagP tab _ d
  · rfl
  · rfl

variable (tab) in
theorem resp_patchAfter (k : ℕ) (d : B.PatchReg) : ((B.patchAfter tab k) d).1.2.2 = d.1.2.2 := by
  rw [AdaptiveIAlg.patchAfter_def]
  split_ifs
  · rw [Equiv.trans_apply]
    exact B.resp_tagP tab _ d
  · rfl
  · rfl

variable (tab) in
theorem req_tagP (on : B.W → Bool) (d : B.PatchReg) :
    ((B.tagP tab on) d).1.2.1 = if on d.1.1.1 then
      (d.1.2.1.1, Equiv.swap (fun _ => none) (tab d.1.1.1) d.1.2.1.2) else d.1.2.1 := by
  change (if on d.1.1.1 then _ else d).1.2.1 = _
  split_ifs <;> rfl

variable (tab) in
/-- **The request register after `patchBefore`**: the table tagged on a request branch before a
slot. -/
theorem req_patchBefore (k : ℕ) (d : B.PatchReg) :
    ((B.patchBefore tab k) d).1.2.1 = if k < B.slots ∧ B.kind d.1.1.1 = true then
      (d.1.2.1.1, Equiv.swap (fun _ => none) (tab d.1.1.1) d.1.2.1.2) else d.1.2.1 := by
  rw [AdaptiveIAlg.patchBefore_def]
  by_cases hk : k < B.slots
  · rw [if_pos hk, Equiv.trans_apply]
    change ((B.tagP tab B.kind) d).1.2.1 = _
    rw [req_tagP]
    by_cases hw : B.kind d.1.1.1 = true
    · rw [if_pos hw, if_pos ⟨hk, hw⟩]
    · rw [if_neg hw, if_neg fun h => hw h.2]
  · rw [if_neg hk, if_neg (show ¬(k < B.slots ∧ B.kind d.1.1.1 = true) from fun h => hk h.1)]
    split_ifs <;> rfl

variable (tab) in
/-- **The request register after `patchAfter`**: the tag cleared on a request branch after a
slot. -/
theorem req_patchAfter (k : ℕ) (d : B.PatchReg) :
    ((B.patchAfter tab k) d).1.2.1 = if (0 < k ∧ k - 1 < B.slots) ∧ B.kind d.1.1.1 = true then
      (d.1.2.1.1, Equiv.swap (fun _ => none) (tab d.1.1.1) d.1.2.1.2) else d.1.2.1 := by
  rw [AdaptiveIAlg.patchAfter_def]
  by_cases hk : 0 < k ∧ k - 1 < B.slots
  · rw [if_pos hk, Equiv.trans_apply]
    change ((B.tagP tab B.kind) d).1.2.1 = _
    rw [req_tagP]
    by_cases hw : B.kind d.1.1.1 = true
    · rw [if_pos hw, if_pos ⟨hk, hw⟩]
    · rw [if_neg hw, if_neg fun h => hw h.2]
  · rw [if_neg hk, if_neg (show ¬((0 < k ∧ k - 1 < B.slots) ∧ B.kind d.1.1.1 = true) from
      fun h => hk h.1)]
    split_ifs <;> rfl

variable (tab) in
theorem req_patchBefore_symm (k : ℕ) (e : B.PatchReg) :
    ((B.patchBefore tab k).symm e).1.2.1 = if k < B.slots ∧ B.kind e.1.1.1 = true then
      (e.1.2.1.1, Equiv.swap (fun _ => none) (tab e.1.1.1) e.1.2.1.2) else e.1.2.1 := by
  have h1 := B.req_patchBefore tab k ((B.patchBefore tab k).symm e)
  have hw := B.workB_patchBefore tab k ((B.patchBefore tab k).symm e)
  rw [Equiv.apply_symm_apply] at h1 hw
  rw [← hw] at h1
  rw [h1]
  split_ifs
  · simp
  · rfl

end PatchSwaps

section PatchAbsorb

variable {X Y Req Resp O Req' Resp' : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req']
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (F : SideRelay Req Resp Req' Resp')
  (φs : Fin A.slots → Equiv.Perm Resp') (φa : Equiv.Perm Resp')

variable [AddGroup Y] {rv : Resp' → X → Option Y}

instance instDecidableEqAbsPatchW : DecidableEq (A.absorb F).PatchW :=
  @instDecidableEqProd _ _ (A.absorb F).instDecidableEqW inferInstance

instance instDecidableEqAbsPatchReg : DecidableEq (A.absorb F).PatchReg :=
  @DReg.instDecidableEq _ _ _ _ _ _ (A.instDecidableEqAbsPatchW F) _ _ _ _

instance instDecidableEqAbsPatchSplit :
    DecidableEq (DReg (A.absorb F).W A.width X Y Req' Resp' ×
      (AncReg X Y (A.absorb F).width × (X → Option Y))) :=
  @instDecidableEqProd _ _ (@DReg.instDecidableEq _ _ _ _ _ _ (A.absorb F).instDecidableEqW _ _ _ _)
    inferInstance

omit [AddGroup Y] in
theorem storeTab_mapStore (hrv : ∀ i x, rv (φs i x) = rv x) (w : A.AbsW (Resp' := Resp')) :
    A.storeTab rv (AbsorbedWork.mapStore φs w) = A.storeTab rv w := by
  unfold storeTab
  congr 2
  funext i
  simp only [AbsorbedWork.mapStore_store]
  cases w.store i <;> simp [Equiv.optionCongr_apply, hrv]

/-- **The patched absorbed step without its leading permutation keeps the moves of the store and
the main response register**, for moves of the stored replies that keep their tables. -/
theorem keepsPerm_patchLead [Nonempty X] [Nonempty Y] {O' : Type} (out' : (A.absorb F).W → O')
    (hrv : ∀ i x, rv (φs i x) = rv x) (k : StepIdx A.slots A.post) :
    ((A.absorb F).patchLead (A.absLead F) (A.storeTab rv) out' k).KeepsPerm
      ((A.absorb F).patchLiftW (AbsorbedWork.mapStore φs) φa) := by
  refine (KrausMap.keepsPerm_ofPerm (patchBefore_patchLiftW φa
    (storeTab_mapStore A φs hrv) (fun _ => rfl) k)).comp
    (KrausMap.KeepsPerm.comp ?_ (KrausMap.keepsPerm_ofPerm fun _ => rfl))
  rw [patchLiftW_eq]
  exact ((A.keepsPerm_absLead F φs φa k).tensorId _).reindex _


/-- **The patched absorbed step without its leading permutation keeps the store and the main
response register.** -/
theorem keepsReg_patchLead_absorb [Nonempty X] [Nonempty Y] {O' : Type}
    (out' : (A.absorb F).W → O')
    (k : StepIdx A.slots A.post) :
    ((A.absorb F).patchLead (A.absLead F) (A.storeTab rv) out' k).KeepsReg
      (fun d => A.storeResp F ((A.absorb F).patchSplitB d).1)
      fun d => A.storeResp F ((A.absorb F).patchSplitB d).1 :=
  keepsReg_patchLead (B := A.absorb F) (A.storeTab rv) out' (fun k => A.keepsReg_absLead F k) k
    fun d => by
    unfold storeResp
    rw [Prod.mk.injEq]
    exact ⟨congrArg AbsorbedWork.store ((A.absorb F).workB_patchBefore _ k d),
      (A.absorb F).resp_patchBefore _ k d⟩

theorem patchSplitB_patchLiftW (φs' : Fin A.slots → Equiv.Perm Resp') (φa' : Equiv.Perm Resp')
    (e : (A.absorb F).PatchReg) :
    (A.absorb F).patchSplitB ((A.absorb F).patchLiftW (AbsorbedWork.mapStore φs') φa' e) =
      (A.absSw F φs' φa' ((A.absorb F).patchSplitB e).1, ((A.absorb F).patchSplitB e).2) :=
  rfl

/-- **The leading permutation of the patched absorbed step along the moves of the store and the
response register**, from `afterAt`'s on the column after `patchAfter`. -/
theorem patchLeadPerm_patchLiftW (φs' : Fin A.slots → Equiv.Perm Resp') (φa' : Equiv.Perm Resp')
    (hrv : ∀ i x, rv (φs i x) = rv x) (k : StepIdx A.slots A.post) (e : (A.absorb F).PatchReg)
    (h : A.afterAt F k (A.absSw F φs φa ((A.absorb F).patchSplitB
        ((A.absorb F).patchAfter (A.storeTab rv) k e)).1) =
      A.absSw F φs' φa' (A.afterAt F k ((A.absorb F).patchSplitB
        ((A.absorb F).patchAfter (A.storeTab rv) k e)).1)) :
    (A.absorb F).patchLeadPerm (fun k => A.afterAt F k) (A.storeTab rv) k
        ((A.absorb F).patchLiftW (AbsorbedWork.mapStore φs) φa e) =
      (A.absorb F).patchLiftW (AbsorbedWork.mapStore φs') φa'
        ((A.absorb F).patchLeadPerm (fun k => A.afterAt F k) (A.storeTab rv) k e) := by
  simp only [patchLeadPerm, Equiv.trans_apply]
  rw [patchAfter_patchLiftW φa (storeTab_mapStore A φs hrv) (fun _ => rfl)]
  simp only [Equiv.permCongr_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
    Equiv.symm_symm]
  erw [patchSplitB_patchLiftW A F φs φa]
  rw [h]
  rfl

end PatchAbsorb

section Inner

variable {X Y Req Resp O Req' Resp' Xs Ys : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req] [Inhabited X]
  [Inhabited Req'] [Nonempty X] [AddGroup Y] [Nonempty Y]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (G : AssignRelay X Y Req Resp Req' Resp' Xs Ys) (Q : ℕ)

variable (Req' Resp') in
/-- **The inner steps**: the steps of `absorbAssignP` with its query counter, without their
leading permutations. -/
noncomputable def innerK (k : StepIdx A.slots A.post) :
    KrausMap (A.absorbAssignP Req' Resp' Q).R (DReg (A.absorbAssignP Req' Resp' Q).toKindAlg.W
        A.width X Y
      ((Req × Fin (Q + 1)) × (X → Option Y)) (AssignRelay.RespD X Y Resp Req' Resp'))
      (DReg (A.absorbAssignP Req' Resp' Q).toKindAlg.W A.width X Y
      ((Req × Fin (Q + 1)) × (X → Option Y)) (AssignRelay.RespD X Y Resp Req' Resp')) :=
  (A.absorbAssignP Req' Resp' Q).cntLead
    ((A.absorbAssignB Req' Resp' Q).patchLead (A.absLead (sideRelay X Y Req Resp Req' Resp' Q))
      (A.assignTab (Req' := Req') (Resp' := Resp')) (fun w => (A.out w.work, A.assignTab w))) k

variable (Req' Resp') in
/-- **The leading permutations of the inner steps**: `patchAfter`, then `afterAt`. -/
noncomputable def innerP (k : StepIdx A.slots A.post) :
    Equiv.Perm (DReg (A.absorbAssignP Req' Resp' Q).toKindAlg.W A.width X Y
      ((Req × Fin (Q + 1)) × (X → Option Y)) (AssignRelay.RespD X Y Resp Req' Resp')) :=
  (A.absorbAssignP Req' Resp' Q).cntLeadPerm
    ((A.absorbAssignB Req' Resp' Q).patchLeadPerm (fun k => A.afterAt (sideRelay X Y Req Resp Req'
        Resp' Q) k)
      (A.assignTab (Req' := Req') (Resp' := Resp'))) k

/-- **The steps of `absorbAssignP` with its query counter are `innerK` after `innerP`.** -/
theorem leadsBy_absorbAssignP (k : StepIdx A.slots A.post) :
    ((A.absorbAssignP Req' Resp' Q).toKindAlg.step k).LeadsBy (A.innerK Req' Resp' Q k) (A.innerP
        Req' Resp' Q k) :=
  leadsBy_toKindAlg (B := A.absorbAssignP Req' Resp' Q)
    (leadsBy_patchTag (B := A.absorbAssignB Req' Resp' Q) _ _ fun k => A.leadsBy_absorb_step _ k) k

variable (φs : Fin A.slots → Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp'))
  (φa : Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp'))

variable (Req' Resp') in
/-- **The store and the main response register moved** on the registers of the inner steps. -/
noncomputable def innerSw : Equiv.Perm (DReg (A.absorbAssignP Req' Resp' Q).toKindAlg.W A.width X Y
    ((Req × Fin (Q + 1)) × (X → Option Y)) (AssignRelay.RespD X Y Resp Req' Resp')) :=
  (A.absorbAssignP Req' Resp' Q).cntSplit.symm.permCongr
    (((A.absorbAssignB Req' Resp' Q).patchLiftW (AbsorbedWork.mapStore φs) φa).prodCongr (Equiv.refl
        _))

/-- **The inner steps keep the moves of the store and the main response register**, for moves of
the stored replies that keep their tables. -/
theorem keepsPerm_innerK (hφ : ∀ i x, (φs i x).2.1 = x.2.1) (k : StepIdx A.slots A.post) :
    (A.innerK Req' Resp' Q k).KeepsPerm (A.innerSw Req' Resp' Q φs φa) :=
  keepsPerm_cntLead (B := A.absorbAssignP Req' Resp' Q) (fun _ => rfl)
    (fun k => A.keepsPerm_patchLead (sideRelay X Y Req Resp Req' Resp' Q) φs φa _ (rv := fun x =>
        x.2.1) hφ k) k

variable (Req' Resp') in
/-- The store and the main response register of the registers of the inner steps. -/
def innerSR (z : DReg (A.absorbAssignP Req' Resp' Q).toKindAlg.W A.width X Y
    ((Req × Fin (Q + 1)) × (X → Option Y)) (AssignRelay.RespD X Y Resp Req' Resp')) :
    (Fin A.slots → Option (AssignRelay.RespD X Y Resp Req' Resp')) ×
      Option (AssignRelay.RespD X Y Resp Req' Resp') :=
  (z.1.1.1.1.store, z.1.2.2)

theorem innerSR_innerSw (z : DReg (A.absorbAssignP Req' Resp' Q).toKindAlg.W A.width X Y
      ((Req × Fin (Q + 1)) × (X → Option Y)) (AssignRelay.RespD X Y Resp Req' Resp')) :
    A.innerSR Req' Resp' Q (A.innerSw Req' Resp' Q φs φa z) =
      (fun i => Equiv.optionCongr (φs i) ((A.innerSR Req' Resp' Q z).1 i),
        Equiv.optionCongr φa (A.innerSR Req' Resp' Q z).2) :=
  rfl

/-- **Two moves of the store and the response register agree on a basis state** when they agree on
its store and response register. -/
theorem innerSw_eq_of {φs' : Fin A.slots → Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp')}
    {φa' : Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp')}
    (z : DReg (A.absorbAssignP Req' Resp' Q).toKindAlg.W A.width X Y
      ((Req × Fin (Q + 1)) × (X → Option Y)) (AssignRelay.RespD X Y Resp Req' Resp'))
    (h : A.innerSR Req' Resp' Q (A.innerSw Req' Resp' Q φs φa z) = A.innerSR Req' Resp' Q (A.innerSw
        Req' Resp' Q φs' φa' z)) :
    A.innerSw Req' Resp' Q φs φa z = A.innerSw Req' Resp' Q φs' φa' z := by
  obtain ⟨⟨⟨⟨w, an⟩, c⟩, q, a⟩, qs⟩ := z
  rw [innerSR_innerSw, innerSR_innerSw, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  change ((((AbsorbedWork.mapStore φs w, an), c), q, Equiv.optionCongr φa a), qs) =
    ((((AbsorbedWork.mapStore φs' w, an), c), q, Equiv.optionCongr φa' a), qs)
  rw [show AbsorbedWork.mapStore φs w = AbsorbedWork.mapStore φs' w from
    AbsorbedWork.ext rfl rfl rfl rfl h1]
  change Equiv.optionCongr φa a = Equiv.optionCongr φa' a at h2
  rw [h2]

/-- **The inner steps keep the store and the main response register.** -/
theorem keepsReg_innerK (k : StepIdx A.slots A.post) :
    (A.innerK Req' Resp' Q k).KeepsReg (A.innerSR Req' Resp' Q) (A.innerSR Req' Resp' Q) :=
  keepsReg_cntLead (B := A.absorbAssignP Req' Resp' Q)
    (f := fun _ d => A.storeResp (sideRelay X Y Req Resp Req' Resp' Q) ((A.absorbAssignB Req' Resp'
        Q).patchSplitB d).1)
    (g := fun _ d => A.storeResp (sideRelay X Y Req Resp Req' Resp' Q) ((A.absorbAssignB Req' Resp'
        Q).patchSplitB d).1)
    (fun k => A.keepsReg_patchLead_absorb (sideRelay X Y Req Resp Req' Resp' Q) (rv := fun x =>
        x.2.1) _ k) k

/-- **The leading permutation of an inner step along the moves of the store and the response
register**, from `afterAt`'s on the column after `patchAfter`. -/
theorem innerP_innerSw (φs' : Fin A.slots → Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp'))
    (φa' : Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp')) (hφ : ∀ i x, (φs i x).2.1 = x.2.1)
    (k : StepIdx A.slots A.post) (x : DReg (A.absorbAssignP Req' Resp' Q).toKindAlg.W A.width X Y
      ((Req × Fin (Q + 1)) × (X → Option Y)) (AssignRelay.RespD X Y Resp Req' Resp'))
    (h : A.afterAt (sideRelay X Y Req Resp Req' Resp' Q) k (A.absSw (sideRelay X Y Req Resp Req'
        Resp' Q) φs φa
        ((A.absorbAssignB Req' Resp' Q).patchSplitB ((A.absorbAssignB Req' Resp' Q).patchAfter
          (A.assignTab (Req' := Req') (Resp' := Resp')) k ((A.absorbAssignP Req' Resp' Q).cntSplit
              x).1)).1) =
      A.absSw (sideRelay X Y Req Resp Req' Resp' Q) φs' φa' (A.afterAt (sideRelay X Y Req Resp Req'
          Resp' Q) k
        ((A.absorbAssignB Req' Resp' Q).patchSplitB ((A.absorbAssignB Req' Resp' Q).patchAfter
          (A.assignTab (Req' := Req') (Resp' := Resp')) k ((A.absorbAssignP Req' Resp' Q).cntSplit
              x).1)).1)) :
    A.innerP Req' Resp' Q k (A.innerSw Req' Resp' Q φs φa
        x) = A.innerSw Req' Resp' Q φs' φa' (A.innerP Req' Resp' Q k x) := by
  change (A.absorbAssignP Req' Resp' Q).cntSplit.symm ((A.absorbAssignB Req' Resp' Q).patchLeadPerm
      (fun k => A.afterAt (sideRelay X Y Req Resp Req' Resp' Q) k) A.assignTab k
      ((A.absorbAssignB Req' Resp' Q).patchLiftW (AbsorbedWork.mapStore φs) φa
        ((A.absorbAssignP Req' Resp' Q).cntSplit x).1), ((A.absorbAssignP Req' Resp'
            Q).cntSplit x).2) =
    (A.absorbAssignP Req' Resp' Q).cntSplit.symm ((A.absorbAssignB Req' Resp' Q).patchLiftW
      (AbsorbedWork.mapStore φs') φa' ((A.absorbAssignB Req' Resp' Q).patchLeadPerm
        (fun k => A.afterAt (sideRelay X Y Req Resp Req' Resp' Q) k) A.assignTab k ((A.absorbAssignP
            Req' Resp' Q).cntSplit x).1),
      ((A.absorbAssignP Req' Resp' Q).cntSplit x).2)
  rw [A.patchLeadPerm_patchLiftW (sideRelay X Y Req Resp Req' Resp' Q) φs φa φs' φa' (rv := fun x =>
      x.2.1) hφ k _ h]

variable (Req' Resp') in
/-- The registers of the inner steps beside the adversary's: those of the absorbed registers, the
ancillas and the table register. -/
noncomputable def innerRest (u : DReg (A.absorbAssignP Req' Resp' Q).toKindAlg.W A.width X Y
    ((Req × Fin (Q + 1)) × (X → Option Y)) (AssignRelay.RespD X Y Resp Req' Resp')) :
    A.AbsRest (Req' := Req × Fin (Q + 1)) (Resp' := AssignRelay.RespD X Y Resp Req' Resp') ×
      (AncReg X Y A.width × (X → Option Y)) :=
  (A.absRest (sideRelay X Y Req Resp Req' Resp' Q) ((A.absorbAssignB Req' Resp' Q).patchSplitB
      ((A.absorbAssignP Req' Resp' Q).cntSplit u).1).1,
    ((A.absorbAssignB Req' Resp' Q).patchSplitB ((A.absorbAssignP Req' Resp' Q).cntSplit u).1).2)

/-- **The inner step `k` reads the registers beside the adversary's** through `patchBefore` and
`setAt` undone on its rows. -/
theorem keepsReg_innerK_rest (k : StepIdx A.slots A.post) :
    (A.innerK Req' Resp' Q k).KeepsReg (fun z => (A.absRest (sideRelay X Y Req Resp Req' Resp' Q)
        (A.setAt (sideRelay X Y Req Resp Req' Resp' Q) k
        ((A.absorbAssignB Req' Resp' Q).patchSplitB (((A.absorbAssignB Req' Resp' Q).patchBefore
          (A.assignTab (Req' := Req') (Resp' := Resp')) k).symm
          ((A.absorbAssignP Req' Resp' Q).cntSplit z).1)).1),
      ((A.absorbAssignB Req' Resp' Q).patchSplitB (((A.absorbAssignB Req' Resp' Q).patchBefore
          (A.assignTab (Req' := Req') (Resp' := Resp')) k).symm
          ((A.absorbAssignP Req' Resp' Q).cntSplit z).1)).2)) (A.innerRest Req' Resp' Q) :=
  keepsReg_cntLead (B := A.absorbAssignP Req' Resp' Q)
    (fun k => keepsReg_patchLead_rest (B := A.absorbAssignB Req' Resp' Q) _ _
      (fun k => A.keepsReg_absLead_rest (sideRelay X Y Req Resp Req' Resp' Q) k) k) k

/-- **The store and the response register after the leading permutation of an inner step**:
`afterAt`'s, on the absorbed registers. -/
theorem innerSR_innerP (k : StepIdx A.slots A.post)
    (x : DReg (A.absorbAssignP Req' Resp' Q).toKindAlg.W A.width X Y
      ((Req × Fin (Q + 1)) × (X → Option Y)) (AssignRelay.RespD X Y Resp Req' Resp')) :
    A.innerSR Req' Resp' Q (A.innerP Req' Resp' Q k x) =
      if h : 0 < (k : ℕ) ∧ (k : ℕ) - 1 < A.slots then
        (if (x.1.1.1.1.logs ⟨k - 1, h.2⟩).isSome then
          (Function.update x.1.1.1.1.store ⟨k - 1, h.2⟩ x.1.2.2, x.1.1.1.1.store ⟨k - 1, h.2⟩)
        else (x.1.1.1.1.store, x.1.2.2))
      else (x.1.1.1.1.store, x.1.2.2) := by
  have h1 := (A.absorbAssignB Req' Resp' Q).workB_patchAfter (A.assignTab (Req' := Req') (Resp' :=
      Resp')) k
    ((A.absorbAssignP Req' Resp' Q).cntSplit x).1
  have h2 := (A.absorbAssignB Req' Resp' Q).resp_patchAfter (A.assignTab (Req' := Req') (Resp' :=
      Resp')) k
    ((A.absorbAssignP Req' Resp' Q).cntSplit x).1
  have e : A.innerSR Req' Resp' Q (A.innerP Req' Resp' Q k x) = A.storeResp (sideRelay X Y Req Resp
      Req' Resp' Q)
      (A.afterAt (sideRelay X Y Req Resp Req' Resp' Q) k ((A.absorbAssignB Req' Resp' Q).patchSplitB
        ((A.absorbAssignB Req' Resp' Q).patchAfter (A.assignTab (Req' := Req') (Resp' := Resp')) k
          ((A.absorbAssignP Req' Resp' Q).cntSplit x).1)).1) := rfl
  rw [e, storeResp_afterAt]
  have hw : ((A.absorbAssignB Req' Resp' Q).patchSplitB ((A.absorbAssignB Req' Resp' Q).patchAfter
      (A.assignTab (Req' := Req') (Resp' := Resp')) k ((A.absorbAssignP Req' Resp' Q).cntSplit
          x).1)).1.1.1 =
      x.1.1.1.1 := h1
  have ha : ((A.absorbAssignB Req' Resp' Q).patchSplitB ((A.absorbAssignB Req' Resp' Q).patchAfter
      (A.assignTab (Req' := Req') (Resp' := Resp')) k ((A.absorbAssignP Req' Resp' Q).cntSplit
          x).1)).1.1.2.2 =
      x.1.2.2 := h2
  simp only [hw, ha]

/-- **An entry of a matrix along two moves of the store and the response register**: if the matrix
keeps the column's move and the store and response register, and the two moves agree on the
column's store and response register, the row's move can replace the column's. -/
theorem innerSw_entry {M : Matrix (DReg (A.absorbAssignP Req' Resp' Q).toKindAlg.W A.width X Y
      ((Req × Fin (Q + 1)) × (X → Option Y)) (AssignRelay.RespD X Y Resp Req' Resp'))
      (DReg (A.absorbAssignP Req' Resp' Q).toKindAlg.W A.width X Y
      ((Req × Fin (Q + 1)) × (X → Option Y)) (AssignRelay.RespD X Y Resp Req' Resp')) ℂ}
    {φs' : Fin A.slots → Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp')}
    {φa' : Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp')}
    (hc : ∀ a b, M (A.innerSw Req' Resp' Q φs φa a) (A.innerSw Req' Resp' Q φs φa b) = M a b)
    (hk : ∀ a b, M a b ≠ 0 → A.innerSR Req' Resp' Q a = A.innerSR Req' Resp' Q b)
    (u : DReg (A.absorbAssignP Req' Resp' Q).toKindAlg.W A.width X Y
      ((Req × Fin (Q + 1)) × (X → Option Y)) (AssignRelay.RespD X Y Resp Req' Resp'))
    (hcore : A.innerSR Req' Resp' Q (A.innerSw Req' Resp' Q φs' φa' u) = A.innerSR Req' Resp' Q
        (A.innerSw Req' Resp' Q φs φa u))
    (z : DReg (A.absorbAssignP Req' Resp' Q).toKindAlg.W A.width X Y
      ((Req × Fin (Q + 1)) × (X → Option Y)) (AssignRelay.RespD X Y Resp Req' Resp')) :
    M (A.innerSw Req' Resp' Q φs' φa' z) (A.innerSw Req' Resp' Q φs φa u) = M z u := by
  refine Matrix.entry_perm_of_keeps (f := A.innerSR Req' Resp' Q) hc hk (fun z hz => ?_) (fun z hz
      => ?_) z
  · refine A.innerSw_eq_of Q φs' φa' z ?_
    rw [innerSR_innerSw, innerSR_innerSw, hz, ← innerSR_innerSw, ← innerSR_innerSw, hcore]
  · rw [← hcore, innerSR_innerSw, innerSR_innerSw]
    intro h
    apply hz
    rw [Prod.mk.injEq] at h
    refine Prod.ext (funext fun i => ?_) ((Equiv.optionCongr φa').injective h.2)
    exact (Equiv.optionCongr (φs' i)).injective (congrFun h.1 i)

omit [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] [Inhabited X] [Inhabited Req'] in
theorem absorbAssignP_tracePreserving (h : A.TracePreserving) :
    (A.absorbAssignP Req' Resp' Q).TracePreserving :=
  (A.absorbAssignB Req' Resp' Q).patchTag_tracePreserving _ _ (A.absorb_tracePreserving _ h)

/-- **The frozen operators on a live column**: those without the leading permutation, after it. -/
theorem tpOp_true_alive (h : A.TracePreserving) (k : StepIdx A.slots A.post)
    (z : (A.absorbAssignP Req' Resp' Q).R ⊕ ((A.absorbAssignP Req' Resp' Q).R ⊕
      Fin ((A.absorbAssignP Req' Resp' Q).budget + 2)))
    (y x : (A.absorbAssignP Req' Resp' Q).CReg) (hx : x.workspace.cnt ≠ (A.absorbAssignP Req' Resp'
        Q).ended) :
    (A.absorbAssignP Req' Resp' Q).tpOp true k z y x = if (A.absorbAssignP Req' Resp'
        Q).isEndSlot z then 0 else
      (A.absorbAssignP Req' Resp' Q).tpLead ((A.absorbAssignB Req' Resp' Q).patchLead (A.absLead
          (sideRelay X Y Req Resp Req' Resp' Q))
        (A.assignTab (Req' := Req') (Resp' := Resp')) (fun w => (A.out w.work, A.assignTab w))) k
            z y
        (A.innerP Req' Resp' Q k x) := by
  rw [tpOp_true_apply, if_neg hx, if_neg hx]
  split_ifs
  · rfl
  · exact tpRaw_eq_tpLead (A.absorbAssignP_tracePreserving Q h)
      (leadsBy_patchTag (B := A.absorbAssignB Req' Resp' Q) _ _ fun k => A.leadsBy_absorb_step _
          k) k z y x

omit [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] [Inhabited X] [Inhabited Req'] in
theorem innerSw_cnt (z : (A.absorbAssignP Req' Resp' Q).CReg) :
    (A.innerSw Req' Resp' Q φs φa z).workspace.cnt = z.workspace.cnt :=
  rfl

/-- **The frozen operators on a live column along the moves of the store and the response
register**: the row's move and the column's are related through the leading permutation and agree
on the store and response register after it. -/
theorem tpOp_true_alive_innerSw (h : A.TracePreserving) (hφ : ∀ i x, (φs i x).2.1 = x.2.1)
    (k : StepIdx A.slots A.post)
    (z : (A.absorbAssignP Req' Resp' Q).R ⊕ ((A.absorbAssignP Req' Resp' Q).R ⊕
      Fin ((A.absorbAssignP Req' Resp' Q).budget + 2)))
    {φsc φsr : Fin A.slots → Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp')}
    {φac φar : Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp')}
    (y x : (A.absorbAssignP Req' Resp' Q).CReg) (hx : x.workspace.cnt ≠ (A.absorbAssignP Req' Resp'
        Q).ended)
    (hP : A.innerP Req' Resp' Q k (A.innerSw Req' Resp' Q φsc φac x) = A.innerSw Req' Resp' Q φs φa
        (A.innerP Req' Resp' Q k x))
    (hcore : A.innerSR Req' Resp' Q (A.innerSw Req' Resp' Q φsr φar (A.innerP Req' Resp' Q k x)) =
      A.innerSR Req' Resp' Q (A.innerSw Req' Resp' Q φs φa (A.innerP Req' Resp' Q k x))) :
    (A.absorbAssignP Req' Resp' Q).tpOp true k z (A.innerSw Req' Resp' Q φsr φar y) (A.innerSw Req'
        Resp' Q φsc φac x) =
      (A.absorbAssignP Req' Resp' Q).tpOp true k z y x := by
  rw [A.tpOp_true_alive Q h k z (A.innerSw Req' Resp' Q φsr φar y) (A.innerSw Req' Resp' Q φsc φac
      x) hx,
    A.tpOp_true_alive Q h k z y x hx, hP]
  split_ifs
  · rfl
  · refine A.innerSw_entry Q φs φa (fun a b => ?_) (fun a b hab => ?_) _ hcore y
    · exact tpLead_perm (B := A.absorbAssignP Req' Resp' Q) (fun _ => rfl)
        (fun k => A.keepsPerm_patchLead (sideRelay X Y Req Resp Req' Resp' Q) φs φa _ (rv := fun x
            => x.2.1) hφ k) k z a b
    · exact tpLead_keeps (B := A.absorbAssignP Req' Resp' Q)
        (f := fun _ d => A.storeResp (sideRelay X Y Req Resp Req' Resp' Q) ((A.absorbAssignB Req'
            Resp' Q).patchSplitB d).1)
        (g := fun _ d => A.storeResp (sideRelay X Y Req Resp Req' Resp' Q) ((A.absorbAssignB Req'
            Resp' Q).patchSplitB d).1)
        (fun k => A.keepsReg_patchLead_absorb (sideRelay X Y Req Resp Req' Resp' Q) (rv := fun x =>
            x.2.1) _ k)
        k z a b hab

end Inner

section Tower

variable {X Y Req Resp O Req' Resp' : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (Q : ℕ) {E : Type} {c : ℕ}

/-- **The test of the relayed request number `j`**: a request tagged `j`, other than the blank
one. -/
def jTest (j : ℕ) (r : (Req × Fin (Q + 1)) × (X → Option Y)) : Bool :=
  decide (r.1.2.val = j ∧ r ≠ default)

variable (j bR : ℕ) (swO : Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp'))

/-- **The moves of the stored replies of the started slots**: `swO` on the first started request
satisfying the test, when its block is relayed. -/
def storeSwOf (es : List (Option ((Req × Fin (Q + 1)) × (X → Option Y)))) :
    Fin A.slots → Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp') :=
  fun i => if MultiRelay.firstJIdx (jTest Q j) es = some (i : ℕ) ∧
      MultiRelay.blkAt bR Q es i = .rel then swO else Equiv.refl _

/-- The store moved on a workspace of the absorbed adversary with its ancillas, its counter, the
extra registers `E` of the dilation and the flag of the post phase. -/
def wMove (φs : Fin A.slots → Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp')) :
    Equiv.Perm ((((A.AbsW (Resp' := AssignRelay.RespD X Y Resp Req' Resp') ×
      AncReg X Y A.width) × Fin c) × E) × Bool) :=
  (((((AbsorbedWork.mapStore φs).prodCongr (Equiv.refl _)).prodCongr (Equiv.refl _)).prodCongr
    (Equiv.refl _)).prodCongr (Equiv.refl _))

/-- **The permutations of the inner distinguisher's registers along the started slots**: the
stored reply of the first started request satisfying the test moved by `swO` (when its block is
relayed), and the response register moved by the last slot's permutation (`MultiRelay.lastSwO`). -/
def innerπ (es : List (Option ((Req × Fin (Q + 1)) × (X → Option Y)))) :
    Equiv.Perm (((((A.AbsW (Resp' := AssignRelay.RespD X Y Resp Req' Resp') ×
      AncReg X Y A.width) × Fin c) × E) × Bool) × ((Req × Fin (Q + 1)) × (X → Option Y)) ×
        Option (AssignRelay.RespD X Y Resp Req' Resp')) :=
  (A.wMove (E := E) (c := c) (A.storeSwOf Q j bR swO es)).prodCongr
    ((Equiv.refl _).prodCongr (Equiv.optionCongr (MultiRelay.lastSwOL (jTest Q j) swO bR Q es)))

/-- **`innerπ` moves the response register by the last slot's permutation.** -/
theorem respSw_innerπ [Fintype E] [DecidableEq E] [Inhabited X] :
    Distinguisher.RespSw (W := (((A.AbsW (Resp' := AssignRelay.RespD X Y Resp Req' Resp') ×
      AncReg X Y A.width) × Fin c) × E) × Bool) bR Q (jTest Q j) swO
      (A.innerπ Q (E := E) (c := c) j bR swO) := by
  intro m' rec w q a
  simp only [innerπ, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, Equiv.optionCongr_apply,
    MultiRelay.lastSwO_eq_lastSwOL]

theorem innerπ_request (es : List (Option ((Req × Fin (Q + 1)) × (X → Option Y))))
    (t : (((((A.AbsW (Resp' := AssignRelay.RespD X Y Resp Req' Resp') ×
      AncReg X Y A.width) × Fin c) × E) × Bool) × ((Req × Fin (Q + 1)) × (X → Option Y)) ×
        Option (AssignRelay.RespD X Y Resp Req' Resp'))) :
    (A.innerπ Q j bR swO es t).2.1 = t.2.1 :=
  rfl

theorem innerπ_work (es : List (Option ((Req × Fin (Q + 1)) × (X → Option Y))))
    (t : (((((A.AbsW (Resp' := AssignRelay.RespD X Y Resp Req' Resp') ×
      AncReg X Y A.width) × Fin c) × E) × Bool) × ((Req × Fin (Q + 1)) × (X → Option Y)) ×
        Option (AssignRelay.RespD X Y Resp Req' Resp'))) :
    (A.innerπ Q j bR swO es t).1.1.1.1.1.work = t.1.1.1.1.1.work ∧
      (A.innerπ Q j bR swO es t).1.1.1.2 = t.1.1.1.2 ∧ (A.innerπ Q j bR swO es t).1.1.2 = t.1.1.2 ∧
      (A.innerπ Q j bR swO es t).1.2 = t.1.2 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem innerπ_nil : A.innerπ Q (E := E) (c := c) j bR swO [] = Equiv.refl _ := by
  have h1 : A.storeSwOf Q j bR swO [] = fun _ => Equiv.refl _ := by
    funext i
    simp [storeSwOf, MultiRelay.firstJIdx]
  have h2 : MultiRelay.lastSwOL (jTest Q j) swO bR Q
      ([] : List (Option ((Req × Fin (Q + 1)) × (X → Option Y)))) = Equiv.refl _ := by
    simp [MultiRelay.lastSwOL, MultiRelay.lastSwO, MultiRelay.recList]
  unfold innerπ wMove
  rw [h1, h2, AbsorbedWork.mapStore_refl, Equiv.optionCongr_refl]
  rfl

/-- **The well-formed absorbed registers of a live branch** after the started slots `es`: the
copy of the logs records the started requests; the store is blank from the last started slot on;
after a request slot the main request register holds its tagged relayed request with the table of
the stored replies, the kind a request; after any other slot it is blank and, after a query slot,
the kind a query; after a slot other than a request the response register is blank; and each
started request is tagged with the number of requests before it. -/
structure LiveGood (es : List (Option ((Req × Fin (Q + 1)) × (X → Option Y))))
    (aw : A.AbsW (Resp' := AssignRelay.RespD X Y Resp Req' Resp'))
    (q : (Req × Fin (Q + 1)) × (X → Option Y)) (a : Option (AssignRelay.RespD X Y Resp Req'
        Resp')) :
    Prop where
  logs : ∀ i : Fin A.slots, (aw.logs i).isSome = (es[(i : ℕ)]?.bind id).isSome
  store : ∀ i : Fin A.slots, es.length ≤ i + 1 → aw.store i = none
  last : ∀ i : Fin A.slots, (i : ℕ) + 1 = es.length → ∀ r₀, aw.logs i = some r₀ →
    A.kind aw.work = true ∧
      q = ((r₀, ⟨min (A.reqCount aw.logs i) Q, Nat.lt_succ_of_le (min_le_right _ _)⟩),
        A.storeTab (fun x => x.2.1) aw) ∧ es[(i : ℕ)]? = some (some q)
  blank : (∀ i : Fin A.slots, (i : ℕ) + 1 = es.length → aw.logs i = none) → q = default
  kindQ : ∀ i : Fin A.slots, (i : ℕ) + 1 = es.length → aw.logs i = none → A.kind aw.work = false
  resp : (∀ r, es.getLast? ≠ some (some r)) → a = none
  tags : ∀ (i : Fin A.slots) r, es[(i : ℕ)]? = some (some r) →
    (r.1.2 : ℕ) = min (A.reqCount aw.logs i) Q

/-- **The well-formed absorbed registers are kept by the moves of the stored replies** that keep
their tables, and by moves of the response register. -/
theorem LiveGood.move {es : List (Option ((Req × Fin (Q + 1)) × (X → Option Y)))}
    {aw : A.AbsW (Resp' := AssignRelay.RespD X Y Resp Req' Resp')}
    {q : (Req × Fin (Q + 1)) × (X → Option Y)} {a : Option (AssignRelay.RespD X Y Resp Req' Resp')}
    (h : A.LiveGood Q es aw q a) (φs : Fin A.slots → Equiv.Perm (AssignRelay.RespD X Y Resp Req'
        Resp'))
    (hφ : ∀ i x, (φs i x).2.1 = x.2.1) (φa : Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp')) :
    A.LiveGood Q es (AbsorbedWork.mapStore φs aw) q (Equiv.optionCongr φa a) where
  logs := h.logs
  store i hi := by
    rw [AbsorbedWork.mapStore_store, h.store i hi]
    rfl
  last i hi r₀ hr := by
    obtain ⟨h1, h2, h3⟩ := h.last i hi r₀ hr
    refine ⟨h1, ?_, h3⟩
    rw [h2]
    simp only [AbsorbedWork.mapStore_logs]
    rw [A.storeTab_mapStore φs hφ]
  blank := h.blank
  kindQ := h.kindQ
  resp hr := by
    rw [h.resp hr]
    rfl
  tags := h.tags

theorem reqCount_lt_of_some {lg : LogReg Req A.slots} {i i' : Fin A.slots} {r : Req}
    (h : lg i = some r) (hii : i < i') : A.reqCount lg i < A.reqCount lg i' := by
  unfold reqCount
  have h1 : requestsBefore lg ((i : ℕ) + 1) = requestsBefore lg i ++ [r] := by
    rw [requestsBefore_succ_of_lt lg i.2, h]
    rfl
  have h2 := (requestsBefore_prefix lg (show (i : ℕ) + 1 ≤ i' from hii)).length_le
  rw [h1, List.length_append, List.length_singleton] at h2
  omega

/-- **At most one started request of a live branch satisfies the test**, for a test number below
`Q`. -/
theorem LiveGood.eq_of_jTest {es : List (Option ((Req × Fin (Q + 1)) × (X → Option Y)))}
    {aw : A.AbsW (Resp' := AssignRelay.RespD X Y Resp Req' Resp')}
    {q : (Req × Fin (Q + 1)) × (X → Option Y)} {a : Option (AssignRelay.RespD X Y Resp Req' Resp')}
    (h : A.LiveGood Q es aw q a) {j : ℕ} (hj : j < Q) {i i' : Fin A.slots} {r r' : (Req ×
      Fin (Q + 1)) × (X → Option Y)} (hi : es[(i : ℕ)]? = some (some r))
    (hi' : es[(i' : ℕ)]? = some (some r')) (hr : jTest Q j r = true) (hr' : jTest Q j r' = true) :
    i = i' := by
  have t := h.tags i r hi
  have t' := h.tags i' r' hi'
  simp only [jTest, decide_eq_true_eq] at hr hr'
  have hl : ∀ {i : Fin A.slots} {r : (Req × Fin (Q + 1)) × (X → Option Y)},
      es[(i : ℕ)]? = some (some r) → ∃ r₀, aw.logs i = some r₀ := fun {i r} hi => by
    have := h.logs i
    rw [hi] at this
    simp only [Option.bind_some, id, Option.isSome_some] at this
    exact Option.isSome_iff_exists.1 this
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · obtain ⟨r₀, hr₀⟩ := hl hi
    have := AdaptiveIAlg.reqCount_lt_of_some A hr₀ hlt
    omega
  · exact heq
  · obtain ⟨r₀, hr₀⟩ := hl hi'
    have := AdaptiveIAlg.reqCount_lt_of_some A hr₀ hgt
    omega

theorem storeSwOf_append_of_lt (es : List (Option ((Req × Fin (Q + 1)) × (X → Option Y))))
    (e : Option ((Req × Fin (Q + 1)) × (X → Option Y))) {i : Fin A.slots}
    (hi : (i : ℕ) < es.length) :
    A.storeSwOf Q j bR swO (es ++ [e]) i = A.storeSwOf Q j bR swO es i := by
  simp only [storeSwOf, MultiRelay.firstJIdx_append_of_lt e hi,
    MultiRelay.blkAt_append_of_lt bR Q e hi]

/-- **The stored reply's move at the last started request is the last slot's permutation** on a
live branch, for a test number below `Q`. -/
theorem LiveGood.storeSwOf_last {es : List (Option ((Req × Fin (Q + 1)) × (X → Option Y)))}
    {aw : A.AbsW (Resp' := AssignRelay.RespD X Y Resp Req' Resp')}
    {q : (Req × Fin (Q + 1)) × (X → Option Y)} {a : Option (AssignRelay.RespD X Y Resp Req' Resp')}
    (h : A.LiveGood Q es aw q a) (hj : j < Q) {i : Fin A.slots} (hi : (i : ℕ) + 1 = es.length)
    {r : (Req × Fin (Q + 1)) × (X → Option Y)} (hr : es[(i : ℕ)]? = some (some r)) :
    A.storeSwOf Q j bR swO es i = MultiRelay.lastSwOL (jTest Q j) swO bR Q es := by
  rw [MultiRelay.lastSwOL_eq, if_pos (by omega)]
  have hg : es.getD (es.length - 1) none = some r := by
    rw [List.getD_eq_getElem?_getD, show es.length - 1 = i by omega, hr]
    rfl
  rw [hg, show es.length - 1 = i by omega]
  unfold storeSwOf
  have key : MultiRelay.firstJIdx (jTest Q j) es = some (i : ℕ) ↔ jTest Q j r = true := by
    constructor
    · intro hf
      obtain ⟨hlt, hJ, hpre⟩ := List.findIdx?_eq_some_iff_getElem.1 hf
      have hrr : es[(i : ℕ)] = some r := by
        rw [List.getElem?_eq_getElem (by omega)] at hr
        exact Option.some_inj.1 hr
      simpa [hrr] using hJ
    · intro hJ
      refine MultiRelay.firstJIdx_eq_some hr hJ fun i' hi' r' hr' => ?_
      by_contra hJ'
      have hi's : i' < A.slots := by omega
      have := AdaptiveIAlg.LiveGood.eq_of_jTest A Q h hj (i := ⟨i', hi's⟩) (i' := i) hr' hr
        (by simpa using hJ') hJ
      rw [Fin.ext_iff] at this
      simp at this
      omega
  generalize MultiRelay.blkAt bR Q es i = bk
  cases bk
  · simp
  · simp
  · simp only [and_true, MultiRelay.swOAt]
    by_cases hJ : jTest Q j r = true
    · rw [if_pos (key.2 hJ), if_pos hJ]
    · rw [if_neg (fun h' => hJ (key.1 h')), if_neg hJ]

end Tower

section TowerStep

variable {X Y Req Resp O Req' Resp' Xs Ys : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req] [Inhabited X]
  [Inhabited Req'] [Nonempty X] [AddGroup Y] [Nonempty Y]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (G : AssignRelay X Y Req Resp Req' Resp' Xs Ys) (Q : ℕ)
  (j bR : ℕ) (swO : Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp'))

theorem storeSwOf_cases (es : List (Option ((Req × Fin (Q + 1)) × (X → Option Y))))
    (i : Fin A.slots) :
    A.storeSwOf Q j bR swO es i = swO ∨ A.storeSwOf Q j bR swO es i = Equiv.refl _ := by
  unfold storeSwOf
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **The frozen operators on a live well-formed column along `innerπ`'s moves**: the row's move
read from any list agreeing with the column's on its started slots, the column's from the column's
list. -/
theorem tpOp_true_live (h : A.TracePreserving) (hj : j < Q)
    (hswO : ∀ x, (swO x).1 = x.1 ∧ (swO x).2.1 = x.2.1) (k : StepIdx A.slots A.post)
    (es : List (Option ((Req × Fin (Q + 1)) × (X → Option Y)))) (hk : es.length = k)
    (x : (A.absorbAssignP Req' Resp' Q).CReg) (hx : x.workspace.cnt ≠ (A.absorbAssignP Req' Resp'
        Q).ended)
    (hL : A.LiveGood Q es x.1.1.1.1 x.1.2.1 x.1.2.2)
    (hpost : ∀ i r, A.slots ≤ i → es[i]? ≠ some (some r))
    (es' : List (Option ((Req × Fin (Q + 1)) × (X → Option Y))))
    (hes' : ∀ i : Fin A.slots, (i : ℕ) < es.length →
      A.storeSwOf Q j bR swO es' i = A.storeSwOf Q j bR swO es i)
    (φaR : Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp'))
    (z : (A.absorbAssignP Req' Resp' Q).R ⊕ ((A.absorbAssignP Req' Resp' Q).R ⊕
      Fin ((A.absorbAssignP Req' Resp' Q).budget + 2))) (y : (A.absorbAssignP Req' Resp' Q).CReg) :
    (A.absorbAssignP Req' Resp' Q).tpOp true k z (A.innerSw Req' Resp' Q (A.storeSwOf Q j bR swO
        es') φaR y)
      (A.innerSw Req' Resp' Q (A.storeSwOf Q j bR swO es) (MultiRelay.lastSwOL (jTest Q j) swO bR Q
          es) x) =
      (A.absorbAssignP Req' Resp' Q).tpOp true k z y x := by
  have hφ : ∀ (φs : Fin A.slots → Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp')),
      (∀ i, φs i = swO ∨ φs i = Equiv.refl _) → ∀ i x, (φs i x).2.1 = x.2.1 := fun φs hc i x => by
    rcases hc i with e | e <;> rw [e]
    · exact (hswO x).2
    · rfl
  have hsc := A.storeSwOf_cases Q j bR swO es
  have hlc := MultiRelay.lastSwOL_cases (J := jTest Q j) (swO := swO) bR Q es
  have hF : ∀ c r v, (sideRelay X Y Req Resp Req' Resp' Q).answer c r
      (Equiv.optionCongr (MultiRelay.lastSwOL (jTest Q j) swO bR Q es) v) =
      (sideRelay X Y Req Resp Req' Resp' Q).answer c r v := fun c r v => by
    rcases hlc with e | e <;> rw [e]
    · rcases v with _ | v
      · rfl
      · change (Option.map swO (some v)).bind (fun x => x.1) = (some v).bind fun x => x.1
        simp [(hswO v).1]
    · rcases v with _ | v <;> rfl
  have hw := (A.absorbAssignB Req' Resp' Q).workB_patchAfter (A.assignTab (Req' := Req') (Resp' :=
      Resp'))
    k ((A.absorbAssignP Req' Resp' Q).cntSplit x).1
  have hsR := A.innerSR_innerP Q k x
  have hstore : ∀ i : Fin A.slots, es.length ≤ (i : ℕ) + 1 → x.1.1.1.1.store i = none :=
    hL.store
  have hs : ∀ hk' : 0 < (k : ℕ) ∧ (k : ℕ) - 1 < A.slots,
      ((((A.absorbAssignB Req' Resp' Q).patchSplitB ((A.absorbAssignB Req' Resp' Q).patchAfter
        (A.assignTab (Req' := Req') (Resp' := Resp')) k
          ((A.absorbAssignP Req' Resp' Q).cntSplit x).1)).1).1.1.logs ⟨k - 1, hk'.2⟩).isSome →
      (((A.absorbAssignB Req' Resp' Q).patchSplitB ((A.absorbAssignB Req' Resp' Q).patchAfter
        (A.assignTab (Req' := Req') (Resp' := Resp')) k
          ((A.absorbAssignP Req' Resp' Q).cntSplit x).1)).1).1.1.store ⟨k - 1, hk'.2⟩ = none :=
    fun hk' _ => by
      change ((A.absorbAssignB Req' Resp' Q).patchAfter _ k ((A.absorbAssignP Req' Resp' Q).cntSplit
          x).1).1.1.1.store
        ⟨k - 1, hk'.2⟩ = none
      rw [hw]
      exact hstore _ (by simp; omega)
  have hA := A.afterAt_absSw (sideRelay X Y Req Resp Req' Resp' Q) (A.storeSwOf Q j bR swO es)
    (MultiRelay.lastSwOL (jTest Q j) swO bR Q es) k _ hF hs
  by_cases hk' : 0 < (k : ℕ) ∧ (k : ℕ) - 1 < A.slots
  · rw [dif_pos hk'] at hA hsR
    have hlg : (((A.absorbAssignB Req' Resp' Q).patchSplitB ((A.absorbAssignB Req' Resp'
        Q).patchAfter
        (A.assignTab (Req' := Req') (Resp' := Resp')) k
          ((A.absorbAssignP Req' Resp' Q).cntSplit x).1)).1).1.1.logs = x.1.1.1.1.logs :=
      congrArg AbsorbedWork.logs hw
    rw [hlg] at hA
    by_cases hl : (x.1.1.1.1.logs ⟨k - 1, hk'.2⟩).isSome
    · rw [if_pos hl] at hA hsR
      have hP := A.innerP_innerSw Q (A.storeSwOf Q j bR swO es)
        (MultiRelay.lastSwOL (jTest Q j) swO bR Q es) _ _ (hφ _ hsc) k x hA
      have hlast : es[(k : ℕ) - 1]? ≠ none := by
        have := hL.logs ⟨k - 1, hk'.2⟩
        rw [hl] at this
        intro h0
        simp only at this
        rw [h0] at this
        exact absurd this (by simp)
      obtain ⟨e, he⟩ := Option.ne_none_iff_exists'.1 hlast
      have hl' := hL.logs ⟨k - 1, hk'.2⟩
      rw [hl] at hl'
      simp only at hl'
      rw [he] at hl'
      rcases e with _ | r
      · exact absurd hl' (by simp)
      have hSO := hL.storeSwOf_last A Q j bR swO hj (i := ⟨k - 1, hk'.2⟩)
        (by simp; omega) he
      refine A.tpOp_true_alive_innerSw Q _ _ h (by
          intro i x
          by_cases hi : i = ⟨k - 1, hk'.2⟩
          · subst hi
            simp only [Function.update_self]
            rcases hlc with e | e <;> rw [e]
            · exact (hswO x).2
            · rfl
          · rw [Function.update_of_ne hi]
            exact hφ _ hsc i x) k z y x hx hP ?_
      rw [innerSR_innerSw, innerSR_innerSw, hsR]
      refine Prod.ext (funext fun i => ?_) ?_
      · dsimp only
        by_cases hi : i = ⟨k - 1, hk'.2⟩
        · subst hi
          simp only [Function.update_self]
          rw [hes' _ (by simp; omega), hSO]
        · simp only [Function.update_of_ne hi]
          by_cases hil : (i : ℕ) < (k : ℕ) - 1
          · rw [hes' i (by omega)]
          · rw [hstore i (by have : (i : ℕ) ≠ k - 1 := fun h' => hi (Fin.ext h'); omega)]
            rfl
      · simp only
        rw [hstore _ (by simp; omega)]
        rfl
    · rw [if_neg hl] at hA hsR
      have hP := A.innerP_innerSw Q (A.storeSwOf Q j bR swO es)
        (MultiRelay.lastSwOL (jTest Q j) swO bR Q es) _ _ (hφ _ hsc) k x hA
      have ha : x.1.2.2 = none := hL.resp fun r hr => by
        have hl' := hL.logs ⟨k - 1, hk'.2⟩
        rw [Bool.not_eq_true] at hl
        rw [hl] at hl'
        rw [List.getLast?_eq_getElem?, hk] at hr
        simp only at hl'
        rw [hr] at hl'
        exact absurd hl' (by simp)
      refine A.tpOp_true_alive_innerSw Q _ _ h (hφ _ hsc) k z y x hx hP ?_
      rw [innerSR_innerSw, innerSR_innerSw, hsR, ha]
      refine Prod.ext (funext fun i => ?_) rfl
      dsimp only
      by_cases hil : (i : ℕ) < es.length
      · rw [hes' i hil]
      · rw [hstore i (by omega)]
        rfl
  · rw [dif_neg hk'] at hA hsR
    have hP := A.innerP_innerSw Q (A.storeSwOf Q j bR swO es)
      (MultiRelay.lastSwOL (jTest Q j) swO bR Q es) _ _ (hφ _ hsc) k x hA
    have ha : x.1.2.2 = none := hL.resp fun r hr => by
      rw [List.getLast?_eq_getElem?] at hr
      by_cases hk0 : (k : ℕ) = 0
      · rw [hk, hk0] at hr
        have : es = [] := List.eq_nil_of_length_eq_zero (by omega)
        rw [this] at hr
        exact absurd hr (by simp)
      · exact hpost _ r (by omega) hr
    refine A.tpOp_true_alive_innerSw Q _ _ h (hφ _ hsc) k z y x hx hP ?_
    rw [innerSR_innerSw, innerSR_innerSw, hsR, ha]
    refine Prod.ext (funext fun i => ?_) rfl
    dsimp only
    by_cases hil : (i : ℕ) < es.length
    · rw [hes' i hil]
    · rw [hstore i (by omega)]
      rfl

omit [AddGroup Ys] [Fintype Ys] [DecidableEq Ys] [Inhabited X] [Inhabited Req'] in
theorem innerSw_request (φs : Fin A.slots → Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp'))
    (φa : Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp')) (z : (A.absorbAssignP Req' Resp'
        Q).CReg) :
    (A.innerSw Req' Resp' Q φs φa z).1.2.1 = z.1.2.1 :=
  rfl

/-- **The frozen operators on an ended column along two moves of the store and the response
register** that agree when the row's request register is blank, for a column with a blank request
register. -/
theorem tpOp_true_ended (k : StepIdx A.slots A.post)
    (z : (A.absorbAssignP Req' Resp' Q).R ⊕ ((A.absorbAssignP Req' Resp' Q).R ⊕
      Fin ((A.absorbAssignP Req' Resp' Q).budget + 2)))
    {φsr φsc : Fin A.slots → Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp')}
    {φar φac : Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp')}
    (y x : (A.absorbAssignP Req' Resp' Q).CReg) (hx : x.workspace.cnt = (A.absorbAssignP Req' Resp'
        Q).ended)
    (hq : x.1.2.1 = default) (hσ : y.1.2.1 = default → φsr = φsc ∧ φar = φac) :
    (A.absorbAssignP Req' Resp' Q).tpOp true k z (A.innerSw Req' Resp' Q φsr φar y) (A.innerSw Req'
        Resp' Q φsc φac x) =
      (A.absorbAssignP Req' Resp' Q).tpOp true k z y x := by
  erw [tpOp_true_apply (B := A.absorbAssignP Req' Resp' Q) k z (A.innerSw Req' Resp' Q φsr φar y),
    tpOp_true_apply (B := A.absorbAssignP Req' Resp' Q) k z y x]
  have hx' : (A.innerSw Req' Resp' Q φsc φac x).workspace.cnt = (A.absorbAssignP Req' Resp'
      Q).ended := hx
  rw [if_pos hx', if_pos hx]
  split_ifs
  · have key : A.innerSw Req' Resp' Q φsr φar y = A.innerSw Req' Resp' Q φsc φac x ↔ y = x := by
      constructor
      · intro he
        have hyq : y.1.2.1 = default := by
          have := congrArg (fun d => d.1.2.1) he
          simpa [innerSw_request, hq] using this
        obtain ⟨h1, h2⟩ := hσ hyq
        subst h1 h2
        exact (A.innerSw Req' Resp' Q φsr φar).injective he
      · rintro rfl
        obtain ⟨h1, h2⟩ := hσ hq
        rw [h1, h2]
    by_cases hyx : y = x
    · rw [key.2 hyx, hyx]
      erw [Matrix.one_apply_eq, Matrix.one_apply_eq]
    · erw [Matrix.one_apply_ne (fun h => hyx (key.1 h)), Matrix.one_apply_ne hyx]
  · rfl

theorem storeSwOf_append_of_not (es : List (Option ((Req × Fin (Q + 1)) × (X → Option Y))))
    {e : Option ((Req × Fin (Q + 1)) × (X → Option Y))} (he : e.any (jTest Q j) = false) :
    A.storeSwOf Q j bR swO (es ++ [e]) = A.storeSwOf Q j bR swO es := by
  funext i
  by_cases hi : (i : ℕ) < es.length
  · exact A.storeSwOf_append_of_lt Q j bR swO es e hi
  · have h1 : MultiRelay.firstJIdx (jTest Q j) es ≠ some (i : ℕ) := fun h =>
      hi (MultiRelay.firstJIdx_lt h)
    have h2 : MultiRelay.firstJIdx (jTest Q j) (es ++ [e]) ≠ some (i : ℕ) := by
      rcases hf : MultiRelay.firstJIdx (jTest Q j) es with _ | i₀
      · rw [MultiRelay.firstJIdx_append_of_none hf he]
        simp
      · rw [MultiRelay.firstJIdx_append_of_some hf]
        intro h'
        have := MultiRelay.firstJIdx_lt hf
        simp only [Option.some.injEq] at h'
        omega
    simp only [storeSwOf, h1, h2, false_and, ↓reduceIte]

/-- **The leading permutation of an inner step on a live well-formed column** clears the request
register and keeps the copy of the logs. -/
theorem innerP_live (k : StepIdx A.slots A.post)
    (es : List (Option ((Req × Fin (Q + 1)) × (X → Option Y)))) (hk : es.length = k)
    (x : (A.absorbAssignP Req' Resp' Q).CReg) (hL : A.LiveGood Q es x.1.1.1.1 x.1.2.1 x.1.2.2) :
    (A.innerP Req' Resp' Q k x).1.2.1 = default ∧ (A.innerP Req' Resp' Q k
        x).1.1.1.1.logs = x.1.1.1.1.logs := by
  obtain ⟨⟨⟨⟨aw, an⟩, c⟩, q, a⟩, qs⟩ := x
  simp only at hL
  set d : (A.absorbAssignB Req' Resp' Q).PatchReg := (((aw, an), q, a), qs) with hd
  have hq := (A.absorbAssignB Req' Resp' Q).req_patchAfter (A.assignTab (Req' := Req') (Resp' :=
      Resp')) k d
  have hw := (A.absorbAssignB Req' Resp' Q).workB_patchAfter (A.assignTab (Req' := Req') (Resp' :=
      Resp'))
    k d
  set e₁ := (A.absorbAssignB Req' Resp' Q).patchAfter (A.assignTab (Req' := Req') (Resp' :=
      Resp')) k d
    with he₁
  have hq' : e₁.1.2.1 = if (0 < (k : ℕ) ∧ (k : ℕ) - 1 < A.slots) ∧ A.kind aw.work = true then
      (q.1, Equiv.swap (fun _ => none) (A.assignTab aw) q.2) else q := hq
  have hw' : e₁.1.1.1 = aw := hw
  refine ⟨?_, ?_⟩
  · change ((A.afterAt (sideRelay X Y Req Resp Req' Resp' Q) k (((e₁.1.1.1, e₁.1.2.1.1, e₁.1.2.2),
      e₁.2))).1.2.1,
      e₁.1.2.1.2) = default
    rw [req_afterAt]
    simp only
    rw [hw']
    by_cases hk' : 0 < (k : ℕ) ∧ (k : ℕ) - 1 < A.slots
    · rw [dif_pos hk']
      rcases hl : aw.logs ⟨k - 1, hk'.2⟩ with _ | r₀
      · have hb := hL.blank fun i hi => by
          have : i = ⟨k - 1, hk'.2⟩ := Fin.ext (by simp; omega)
          rw [this, hl]
        have hkind := hL.kindQ ⟨k - 1, hk'.2⟩ (by simp; omega) hl
        rw [if_neg (fun h => absurd h.2 (by simp [hkind]))] at hq'
        simp only [Option.elim_none]
        rw [hq', hb]
      · obtain ⟨hkind, hqx, -⟩ := hL.last ⟨k - 1, hk'.2⟩ (by simp; omega) r₀ hl
        rw [if_pos ⟨hk', hkind⟩] at hq'
        simp only [Option.elim_some]
        rw [hq', hqx]
        simp only [AssignRelay.sideRelay, Equiv.swap_apply_right, Equiv.swap_apply_left]
        rfl
    · rw [dif_neg hk']
      have hb := hL.blank fun i hi => absurd hi (by omega)
      rw [if_neg (fun h => hk' h.1)] at hq'
      rw [hq', hb]
  · change (A.afterAt (sideRelay X Y Req Resp Req' Resp' Q) k (((e₁.1.1.1, e₁.1.2.1.1, e₁.1.2.2),
      e₁.2))).1.1.logs =
      aw.logs
    rw [logs_afterAt]
    simp only
    rw [hw']

/-- **A nonzero live operator of an inner step reads the registers beside the adversary's**:
`setAt` on the row with `patchBefore` undone, against the column. -/
theorem tpLead_rest (k : StepIdx A.slots A.post)
    (z : (A.absorbAssignP Req' Resp' Q).R ⊕ ((A.absorbAssignP Req' Resp' Q).R ⊕
      Fin ((A.absorbAssignP Req' Resp' Q).budget + 2))) (ys u : (A.absorbAssignP Req' Resp' Q).CReg)
    (h : (A.absorbAssignP Req' Resp' Q).tpLead ((A.absorbAssignB Req' Resp' Q).patchLead (A.absLead
        (sideRelay X Y Req Resp Req' Resp' Q))
      (A.assignTab (Req' := Req') (Resp' := Resp')) (fun w => (A.out w.work, A.assignTab w))) k z
      ys u ≠ 0) :
    A.absRest (sideRelay X Y Req Resp Req' Resp' Q) (A.setAt (sideRelay X Y Req Resp Req' Resp' Q) k
        ((A.absorbAssignB Req' Resp' Q).patchSplitB
        (((A.absorbAssignB Req' Resp' Q).patchBefore (A.assignTab (Req' := Req') (Resp' := Resp'))
            k).symm
          ((A.absorbAssignP Req' Resp' Q).cntSplit ys).1)).1) =
      A.absRest (sideRelay X Y Req Resp Req' Resp' Q) ((A.absorbAssignB Req' Resp' Q).patchSplitB
        ((A.absorbAssignP Req' Resp' Q).cntSplit u).1).1 ∧
    ((A.absorbAssignB Req' Resp' Q).patchSplitB
        (((A.absorbAssignB Req' Resp' Q).patchBefore (A.assignTab (Req' := Req') (Resp' := Resp'))
            k).symm
          ((A.absorbAssignP Req' Resp' Q).cntSplit ys).1)).2 =
      ((A.absorbAssignB Req' Resp' Q).patchSplitB ((A.absorbAssignP Req' Resp' Q).cntSplit
          u).1).2 :=
  Prod.mk.inj (tpLead_keeps (B := A.absorbAssignP Req' Resp' Q)
    (fun k => keepsReg_patchLead_rest (B := A.absorbAssignB Req' Resp' Q) _ _
      (fun k => A.keepsReg_absLead_rest (sideRelay X Y Req Resp Req' Resp' Q) k) k) k z ys u h)

/-- **The rows of a nonzero live operator of an inner step at a column with a blank request
register**: the store and the response register kept; before a slot on a request branch, the
request copied into log `k` and written, tagged and with the table, into the request register;
otherwise the logs kept and the request register blank. -/
theorem innerRow_live (k : StepIdx A.slots A.post)
    (z : (A.absorbAssignP Req' Resp' Q).R ⊕ ((A.absorbAssignP Req' Resp' Q).R ⊕
      Fin ((A.absorbAssignP Req' Resp' Q).budget + 2))) (ys u : (A.absorbAssignP Req' Resp' Q).CReg)
    (h : (A.absorbAssignP Req' Resp' Q).tpLead ((A.absorbAssignB Req' Resp' Q).patchLead (A.absLead
        (sideRelay X Y Req Resp Req' Resp' Q))
      (A.assignTab (Req' := Req') (Resp' := Resp')) (fun w => (A.out w.work, A.assignTab w))) k z
      ys u ≠ 0) (hu : u.1.2.1 = default) :
    ys.1.1.1.1.store = u.1.1.1.1.store ∧ ys.1.2.2 = u.1.2.2 ∧
      (∀ hk : (k : ℕ) < A.slots, A.kind ys.1.1.1.1.work = true →
        ys.1.1.1.1.logs = Function.update u.1.1.1.1.logs ⟨k, hk⟩
          (Equiv.swap none (some ys.1.1.1.1.request) (u.1.1.1.1.logs ⟨k, hk⟩)) ∧
        ys.1.2.1 = ((ys.1.1.1.1.request, ⟨min (A.reqCount u.1.1.1.1.logs ⟨k, hk⟩) Q,
          Nat.lt_succ_of_le (min_le_right _ _)⟩), A.assignTab ys.1.1.1.1)) ∧
      ((¬ (k : ℕ) < A.slots ∨ A.kind ys.1.1.1.1.work = false) →
        ys.1.1.1.1.logs = u.1.1.1.1.logs ∧ ys.1.2.1 = default) := by
  obtain ⟨h1, h2⟩ := A.tpLead_rest Q k z ys u h
  obtain ⟨⟨⟨⟨aw, an⟩, c⟩, q, a⟩, qs⟩ := ys
  obtain ⟨⟨⟨⟨uw, uan⟩, uc⟩, uq, ua⟩, uqs⟩ := u
  simp only at hu ⊢
  set e : (A.absorbAssignB Req' Resp' Q).PatchReg := (((aw, an), q, a), qs) with he
  set e' := ((A.absorbAssignB Req' Resp' Q).patchBefore (A.assignTab (Req' := Req') (Resp' :=
      Resp'))
      k).symm e
    with he'
  have hwe : e'.1.1.1 = aw := by
    have := (A.absorbAssignB Req' Resp' Q).workB_patchBefore (A.assignTab (Req' := Req') (Resp' :=
        Resp'))
        k e'
    rw [he', Equiv.apply_symm_apply] at this
    exact this.symm
  have hre : e'.1.2.2 = a := by
    have := (A.absorbAssignB Req' Resp' Q).resp_patchBefore (A.assignTab (Req' := Req') (Resp' :=
        Resp'))
        k e'
    rw [he', Equiv.apply_symm_apply] at this
    exact this.symm
  have hqe := (A.absorbAssignB Req' Resp' Q).req_patchBefore_symm (A.assignTab (Req' := Req') (Resp'
      :=
      Resp'))
    k e
  rw [← he'] at hqe
  change (A.absRest (sideRelay X Y Req Resp Req' Resp' Q) (A.setAt (sideRelay X Y Req Resp Req'
      Resp' Q) k
    (((e'.1.1.1, e'.1.2.1.1, e'.1.2.2), e'.2)))) = (uw.logs, uw.store, uq.1, ua) at h1
  change (e'.1.1.2, e'.1.2.1.2) = (uan, uq.2) at h2
  rw [hwe, hre] at h1
  have ht : e'.1.2.1.2 = fun _ => none := by
    rw [(Prod.mk.inj h2).2, hu]
    rfl
  by_cases hk : (k : ℕ) < A.slots
  · have hsa : A.setAt (sideRelay X Y Req Resp Req' Resp' Q) k = A.setPerm (sideRelay X Y Req Resp
      Req' Resp' Q) ⟨k, hk⟩ := by
      rw [AdaptiveIAlg.setAt_def]
      rw [dif_pos hk]
    rw [hsa] at h1
    by_cases hkind : A.kind aw.work = true
    · rw [A.setPerm_of_kind (sideRelay X Y Req Resp Req' Resp' Q) ⟨k, hk⟩ hkind] at h1
      simp only [absRest, absSplit, AlgShape.absSplit, Equiv.coe_fn_mk, Prod.mk.injEq] at h1
      obtain ⟨hl, hs, hq1, ha⟩ := h1
      rw [if_pos ⟨hk, hkind⟩] at hqe
      refine ⟨hs, ha, fun _ _ => ⟨?_, ?_⟩, fun h' => ?_⟩
      · rw [← hl]
        funext i
        by_cases hi : i = ⟨k, hk⟩
        · subst hi
          simp
        · simp [Function.update_of_ne hi]
      · have hc : A.reqCount uw.logs ⟨k, hk⟩ = A.reqCount aw.logs ⟨k, hk⟩ := by
          rw [← hl]
          exact congrArg List.length (requestsBefore_congr fun k' hk' =>
            Function.update_of_ne (fun e => by subst e; simp at hk') _ _)
        have hq1' : e'.1.2.1.1 = (sideRelay X Y Req Resp Req' Resp' Q).route (A.reqCount aw.logs ⟨k,
            hk⟩) aw.request := by
          rw [Equiv.swap_apply_eq_iff] at hq1
          rw [hq1, hu]
          exact Equiv.swap_apply_left _ _
        have hq' : q = (e'.1.2.1.1, Equiv.swap (fun _ => none) (A.assignTab aw) e'.1.2.1.2) := by
          rw [hqe]
          show q = (q.1, Equiv.swap (fun _ => none) (A.assignTab aw)
            (Equiv.swap (fun _ => none) (A.assignTab aw) q.2))
          rw [Equiv.swap_apply_self]
        rw [hq', hq1', ht, hc]
        simp only [Equiv.swap_apply_left]
        rfl
      · rcases h' with h' | h'
        · exact absurd hk h'
        · rw [hkind] at h'
          exact absurd h' (by decide)
    · have hkind' : A.kind aw.work = false := by simpa using hkind
      rw [A.setPerm_of_not_kind (sideRelay X Y Req Resp Req' Resp' Q) ⟨k, hk⟩ hkind'] at h1
      simp only [absRest, absSplit, AlgShape.absSplit, Equiv.coe_fn_mk, Prod.mk.injEq] at h1
      obtain ⟨hl, hs, hq1, ha⟩ := h1
      rw [if_neg (fun h' => hkind h'.2)] at hqe
      refine ⟨hs, ha, fun _ h' => absurd h' hkind, fun _ => ⟨hl, ?_⟩⟩
      have hqe' : e'.1.2.1 = q := hqe
      rw [← hqe']
      refine Prod.ext ?_ ht
      rw [hq1, hu]
  · have hsa : A.setAt (sideRelay X Y Req Resp Req' Resp' Q) k = Equiv.refl _ := by
      rw [AdaptiveIAlg.setAt_def]
      rw [dif_neg hk]
    rw [hsa] at h1
    simp only [Equiv.refl_apply, absRest, absSplit, AlgShape.absSplit, Equiv.coe_fn_mk,
        Prod.mk.injEq] at h1
    obtain ⟨hl, hs, hq1, ha⟩ := h1
    rw [if_neg (fun h' => hk h'.1)] at hqe
    refine ⟨hs, ha, fun hk' => absurd hk' hk, fun _ => ⟨hl, ?_⟩⟩
    have hqe' : e'.1.2.1 = q := hqe
    rw [← hqe']
    refine Prod.ext ?_ ht
    rw [hq1, hu]

/-- **After the leading permutation on a live well-formed column** the response register is blank
and the store blank from the started slots on. -/
theorem innerSR_innerP_live (k : StepIdx A.slots A.post)
    (es : List (Option ((Req × Fin (Q + 1)) × (X → Option Y)))) (hk : es.length = k)
    (x : (A.absorbAssignP Req' Resp' Q).CReg) (hL : A.LiveGood Q es x.1.1.1.1 x.1.2.1 x.1.2.2)
    (hpost : ∀ i r, A.slots ≤ i → es[i]? ≠ some (some r)) :
    (A.innerSR Req' Resp' Q (A.innerP Req' Resp' Q k x)).2 = none ∧
      ∀ i : Fin A.slots, (k : ℕ) ≤ i → (A.innerSR Req' Resp' Q (A.innerP Req' Resp' Q k
          x)).1 i = none := by
  have hstore : ∀ i : Fin A.slots, es.length ≤ (i : ℕ) + 1 → x.1.1.1.1.store i = none :=
    hL.store
  rw [A.innerSR_innerP Q k x]
  by_cases hk' : 0 < (k : ℕ) ∧ (k : ℕ) - 1 < A.slots
  · rw [dif_pos hk']
    by_cases hl : (x.1.1.1.1.logs ⟨k - 1, hk'.2⟩).isSome
    · rw [if_pos hl]
      refine ⟨hstore _ (by simp; omega), fun i hi => ?_⟩
      have hne : i ≠ ⟨k - 1, hk'.2⟩ := fun h' => by
        have := congrArg Fin.val h'
        simp at this
        omega
      change Function.update x.1.1.1.1.store ⟨k - 1, hk'.2⟩ x.1.2.2 i = none
      rw [Function.update_of_ne hne]
      exact hstore i (by omega)
    · rw [if_neg hl]
      refine ⟨hL.resp fun r hr => ?_, fun i hi => hstore i (by omega)⟩
      have hl' := hL.logs ⟨k - 1, hk'.2⟩
      rw [Bool.not_eq_true] at hl
      rw [hl] at hl'
      rw [List.getLast?_eq_getElem?, hk] at hr
      simp only at hl'
      rw [hr] at hl'
      exact absurd hl' (by simp)
  · rw [dif_neg hk']
    refine ⟨hL.resp fun r hr => ?_, fun i hi => hstore i (by omega)⟩
    rw [List.getLast?_eq_getElem?] at hr
    by_cases hk0 : (k : ℕ) = 0
    · rw [hk, hk0] at hr
      have : es = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [this] at hr
      exact absurd hr (by simp)
    · exact hpost _ r (by omega) hr

/-- **The live rows of a step at a live well-formed column are well formed**, with the entry of
the slot, and a request satisfying the test there is the only one. -/
theorem liveGood_row (hj : j < Q) (k : StepIdx A.slots A.post)
    (es : List (Option ((Req × Fin (Q + 1)) × (X → Option Y)))) (hk : es.length = k)
    (x ys : (A.absorbAssignP Req' Resp' Q).CReg) (hL : A.LiveGood Q es x.1.1.1.1 x.1.2.1 x.1.2.2)
    (hpost : ∀ i r, A.slots ≤ i → es[i]? ≠ some (some r))
    (z : (A.absorbAssignP Req' Resp' Q).R ⊕ ((A.absorbAssignP Req' Resp' Q).R ⊕
      Fin ((A.absorbAssignP Req' Resp' Q).budget + 2)))
    (hz : (A.absorbAssignP Req' Resp' Q).tpLead ((A.absorbAssignB Req' Resp' Q).patchLead (A.absLead
        (sideRelay X Y Req Resp Req' Resp' Q))
      (A.assignTab (Req' := Req') (Resp' := Resp')) (fun w => (A.out w.work, A.assignTab w))) k z
      ys (A.innerP Req' Resp' Q k x) ≠ 0)
    (e : Option ((Req × Fin (Q + 1)) × (X → Option Y)))
    (he : e = if (k : ℕ) < A.slots ∧ A.kind ys.1.1.1.1.work = true then some ys.1.2.1 else none) :
    A.LiveGood Q (es ++ [e]) ys.1.1.1.1 ys.1.2.1 ys.1.2.2 ∧
      ∀ r, e = some r → jTest Q j r = true → ∀ (i : ℕ) r', es[i]? = some (some r') →
        jTest Q j r' = true → False := by
  obtain ⟨hu, hulogs⟩ := A.innerP_live Q k es hk x hL
  obtain ⟨hs, ha, H1, H2⟩ := A.innerRow_live Q k z ys _ hz hu
  obtain ⟨hua, hust⟩ := A.innerSR_innerP_live Q k es hk x hL hpost
  have hya : ys.1.2.2 = none := ha.trans hua
  have hyst : ∀ i : Fin A.slots, (k : ℕ) ≤ i → ys.1.1.1.1.store i = none := fun i hi =>
    hs ▸ hust i hi
  have hxl : ∀ i : Fin A.slots, (k : ℕ) ≤ i → x.1.1.1.1.logs i = none := fun i hi => by
    have := hL.logs i
    rw [List.getElem?_eq_none (by omega)] at this
    simpa using this
  have hcnt : ∀ i : Fin A.slots, (i : ℕ) ≤ k → A.reqCount ys.1.1.1.1.logs i =
      A.reqCount x.1.1.1.1.logs i → True := fun _ _ _ => trivial
  by_cases hc : (k : ℕ) < A.slots ∧ A.kind ys.1.1.1.1.work = true
  · obtain ⟨hl, hq⟩ := H1 hc.1 hc.2
    rw [hulogs, hxl ⟨k, hc.1⟩ le_rfl] at hl
    rw [hulogs] at hq
    rw [if_pos hc] at he
    subst he
    have hlo : ∀ i : Fin A.slots, i ≠ ⟨k, hc.1⟩ → ys.1.1.1.1.logs i = x.1.1.1.1.logs i :=
      fun i hi => by rw [hl, Function.update_of_ne hi]
    have hlk : ys.1.1.1.1.logs ⟨k, hc.1⟩ = some ys.1.1.1.1.request := by
      rw [hl, Function.update_self]
      rfl
    have hrc : ∀ i : Fin A.slots, (i : ℕ) ≤ k →
        A.reqCount ys.1.1.1.1.logs i = A.reqCount x.1.1.1.1.logs i := fun i hi =>
      congrArg List.length (requestsBefore_congr fun k' hk' =>
        hlo k' (fun h' => by rw [h'] at hk'; simp at hk'; omega))
    refine ⟨⟨fun i => ?_, fun i hi => hyst i (by simp at hi; omega), fun i hi r₀ hr₀ => ?_,
      fun hb => ?_, fun i hi hn => ?_, fun _ => hya, fun i r hr => ?_⟩, fun r hr hJ i r' hr' hJ'
          => ?_⟩
    · by_cases hik : (i : ℕ) < k
      · rw [hlo i (fun h' => by rw [h'] at hik; simp at hik), List.getElem?_append_left (by omega)]
        exact hL.logs i
      · by_cases hik' : (i : ℕ) = k
        · have : i = ⟨k, hc.1⟩ := Fin.ext hik'
          subst this
          rw [hlk, List.getElem?_append_right (by omega)]
          simp [hk]
        · rw [hlo i (fun h' => hik' (by rw [h'])), hxl i (by omega),
            List.getElem?_eq_none (by simp; omega)]
          rfl
    · have : i = ⟨k, hc.1⟩ := Fin.ext (by simp at hi ⊢; omega)
      subst this
      rw [hlk] at hr₀
      cases hr₀
      refine ⟨hc.2, ?_, by rw [List.getElem?_append_right (by simp; omega)]; simp [hk]⟩
      rw [hq, hrc _ le_rfl]
    · exact absurd (hb ⟨k, hc.1⟩ (by simp [hk])) (by rw [hlk]; simp)
    · have : i = ⟨k, hc.1⟩ := Fin.ext (by simp at hi ⊢; omega)
      subst this
      exact absurd hn (by rw [hlk]; simp)
    · by_cases hik : (i : ℕ) < k
      · rw [List.getElem?_append_left (by omega)] at hr
        rw [hL.tags i r hr, hrc i hik.le]
      · have hik' : (i : ℕ) = k := by
          by_contra hne
          rw [List.getElem?_eq_none (by simp; omega)] at hr
          exact absurd hr (by simp)
        have : i = ⟨k, hc.1⟩ := Fin.ext hik'
        subst this
        rw [List.getElem?_append_right (by omega)] at hr
        simp only [hk, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hr
        rw [← hr, hq, hrc _ le_rfl]
    · cases hr
      have hi's : i < A.slots := by
        by_contra hn
        exact hpost i r' (by omega) hr'
      have hil : i < k := by
        rw [← hk]
        by_contra hn
        rw [List.getElem?_eq_none (by omega)] at hr'
        exact absurd hr' (by simp)
      have t' := hL.tags ⟨i, hi's⟩ r' hr'
      have hlx : ∃ r₀, x.1.1.1.1.logs ⟨i, hi's⟩ = some r₀ := by
        have := hL.logs ⟨i, hi's⟩
        rw [hr'] at this
        simpa [Option.isSome_iff_exists] using this
      obtain ⟨r₀, hr₀⟩ := hlx
      have hlt := AdaptiveIAlg.reqCount_lt_of_some A (i' := ⟨k, hc.1⟩) hr₀ (by simp; omega)
      simp only [jTest, decide_eq_true_eq] at hJ hJ'
      rw [hq] at hJ
      simp only at hJ
      omega
  · obtain ⟨hl, hq⟩ := H2 (by
      by_cases h1 : (k : ℕ) < A.slots
      · exact Or.inr (by simpa [h1] using hc)
      · exact Or.inl h1)
    rw [hulogs] at hl
    rw [if_neg hc] at he
    subst he
    refine ⟨⟨fun i => ?_, fun i hi => hyst i (by simp at hi; omega), fun i hi r₀ hr₀ => ?_,
      fun _ => hq, fun i hi hn => ?_, fun _ => hya, fun i r hr => ?_⟩,
      fun r hr => by cases hr⟩
    · rw [hl]
      by_cases hik : (i : ℕ) < k
      · rw [List.getElem?_append_left (by omega)]
        exact hL.logs i
      · rw [hxl i (by omega)]
        by_cases hik' : (i : ℕ) = k
        · rw [List.getElem?_append_right (by omega)]
          simp [hk, hik']
        · rw [List.getElem?_eq_none (by simp; omega)]
          rfl
    · rw [hl, hxl i (by simp at hi; omega)] at hr₀
      cases hr₀
    · by_contra hkind
      have hks : (k : ℕ) < A.slots := by
        have := i.2
        simp at hi
        omega
      exact hc ⟨hks, by simpa using hkind⟩
    · have hik : (i : ℕ) < k := by
        by_contra hn
        by_cases hik' : (i : ℕ) = k
        · rw [List.getElem?_append_right (by omega)] at hr
          simp [hk, hik'] at hr
        · rw [List.getElem?_eq_none (by simp; omega)] at hr
          exact absurd hr (by simp)
      rw [List.getElem?_append_left (by omega)] at hr
      rw [hL.tags i r hr, hl]

end TowerStep

section TowerD


variable {X Y Req Resp O Req' Resp' Xs Ys : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req']
  [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req] [Inhabited X]
  [Inhabited Req'] [Nonempty X] [AddGroup Y] [Nonempty Y]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (G : AssignRelay X Y Req Resp Req' Resp' Xs Ys) (Q : ℕ)
  (j bR : ℕ) (swO : Equiv.Perm (AssignRelay.RespD X Y Resp Req' Resp'))

set_option quotPrecheck false in
/-- The frozen trace-preserving form of `absorbAssignP` with its output forgotten. -/
local notation "KAf" => ((A.absorbAssignP Req' Resp' Q).toTPKindAlg true).unitOut

-- TODO(unbundle-M4): instance at `absorbAssignP`, whose registers reduce past the adversary; state
-- over {W} {n} (R6) or register the instance on M1b's named type
/-- The dilated workspace of `KAf` is finite (`instFintypeRelayDW` at `absorbAssignP`, whose
registers reduce past the adversary). -/
noncomputable instance instFintypeKAfDW : Fintype (KAf).DW :=
  (A.absorbAssignP Req' Resp' Q).instFintypeRelayDW

-- TODO(unbundle-M4): instance at `absorbAssignP`; state over {W} {n} (R6) or register the instance
-- on M1b's named type
/-- The dilated workspace of `KAf` with the post flag is finite (`instFintypeRelayBase`). -/
noncomputable instance instFintypeKAfBase : Fintype ((KAf).DW × Bool) :=
  (A.absorbAssignP Req' Resp' Q).instFintypeRelayBase

-- TODO(unbundle-M4): instance at `absorbAssignP`; state over {W} {n} (R6) or register the instance
-- on M1b's named type
/-- Decidable equality of the dilated workspace of `KAf` with the post flag
(`instDecidableEqRelayBase`). -/
noncomputable instance instDecidableEqKAfBase : DecidableEq ((KAf).DW × Bool) :=
  (A.absorbAssignP Req' Resp' Q).instDecidableEqRelayBase

omit [Inhabited X] [Inhabited Req'] in
theorem pureD_eq_withPostSlots : (A.absorbAssignP Req' Resp' Q).pureD =
    ((KAf).dilate ()).withPostSlots (fun i => (KAf).uStepD ((KAf).slots + 1 + i)) (KAf).post := by
  rw [pureD_eq]
  rfl

variable (Req' Resp') in
/-- **The well-formed registers of the inner distinguisher** after the started slots `es`: at most
the slots, no request in the post phase, the halting flag clear, the ancilla clean from the next
step on, the post flag set exactly after the slots; on a live counter the absorbed registers well
formed (`LiveGood`), on the ended counter a blank request register and a last entry other than a
request passing the test. -/
structure InnerGood (es : List (Option ((Req × Fin (Q + 1)) × (X → Option Y))))
    (t : ((KAf).DW × Bool) × ((Req × Fin (Q + 1)) × (X → Option Y)) ×
      Option (AssignRelay.RespD X Y Resp Req' Resp')) : Prop where
  len : es.length ≤ A.slots + A.post
  post_none : ∀ i r, A.slots ≤ i → es[i]? ≠ some (some r)
  halt : t.1.1.2.1 = false
  clean : MixedAlg.Clean es.length t.1.1.2.2
  pf : t.1.2 = decide (A.slots < es.length)
  live : t.1.1.1.2 ≠ (A.absorbAssignP Req' Resp' Q).ended → A.LiveGood Q es t.1.1.1.1.1 t.2.1 t.2.2
  ended : t.1.1.1.2 = (A.absorbAssignP Req' Resp' Q).ended →
    t.2.1 = default ∧ ∀ r, es.getLast? = some (some r) → jTest Q j r = false

variable (Req' Resp') in
/-- The well-formed registers of the inner distinguisher. -/
def innerGin (es : List (Option ((Req × Fin (Q + 1)) × (X → Option Y)))) :
    Set (((KAf).DW × Bool) × ((Req × Fin (Q + 1)) × (X → Option Y)) ×
      Option (AssignRelay.RespD X Y Resp Req' Resp')) :=
  {t | A.InnerGood Req' Resp' Q j es t}

theorem innerπ_prodCongr (es : List (Option ((Req × Fin (Q + 1)) × (X → Option Y)))) :
    (A.innerπ Q (E := Bool × (KAf).DAnc) (c := (A.absorbAssignP Req' Resp' Q).budget + 2) j bR swO
      es).prodCongr (Equiv.refl _) =
    Distinguisher.flagPermLift ((KAf).sysLift (A.innerSw Req' Resp' Q (A.storeSwOf Q j bR swO es)
      (MultiRelay.lastSwOL (jTest Q j) swO bR Q es))) := by
  ext ⟨⟨w, q, a⟩, qs⟩ <;> rfl

/-- **(c4) The inner distinguisher's steps along `innerπ`** (`Distinguisher.InnerSwap`), for a
trace-preserving adversary, a test number below `Q` and a move of the main requests' results that
keeps the relayed response and the assignments. -/
theorem innerSwap_pureD (h : A.TracePreserving) (hj : j < Q)
    (hswO : ∀ x, (swO x).1 = x.1 ∧ (swO x).2.1 = x.2.1) :
    Distinguisher.InnerSwap (A.absorbAssignP Req' Resp' Q).pureD
      (A.innerπ Q (E := Bool × (KAf).DAnc) (c := (A.absorbAssignP Req' Resp' Q).budget + 2) j bR
          swO)
      (A.innerGin Req' Resp' Q j) := by
  intro es y x hx
  have hk : es.length < (KAf).slots + (KAf).post + 1 := by
    have := hx.len
    change es.length < A.slots + A.post + 1
    omega
  set es' := if es.length < (KAf).slots + (KAf).post then
    es ++ [Distinguisher.entryOf (A.absorbAssignP Req' Resp' Q).pureD.kind y] else es with hes'def
  erw [innerπ_prodCongr, innerπ_prodCongr]
  have main := fun hr => KindAlg.unitaryMat_dilatePost_stepAt (KAf) () es.length hk y x
    (hx.clean.1 _ le_rfl)
    (A.innerSw Req' Resp' Q (A.storeSwOf Q j bR swO es') (MultiRelay.lastSwOL (jTest Q j) swO bR Q
        es'))
    (A.innerSw Req' Resp' Q (A.storeSwOf Q j bR swO es) (MultiRelay.lastSwOL (jTest Q j) swO bR Q
        es)) hr
  rw [show (A.absorbAssignP Req' Resp' Q).pureD.stepAt es.length =
    (((KAf).dilate ()).withPostSlots (fun i => (KAf).uStepD ((KAf).slots + 1 + i))
      (KAf).post).stepAt es.length from by rw [pureD_eq_withPostSlots]]
  convert main ?_ using 2
  intro r
  have hK : ∑ z, (((KAf).step ⟨es.length, hk⟩).op z)ᴴ *
      ((KAf).step ⟨es.length, hk⟩).op z = 1 :=
    (A.absorbAssignP Req' Resp' Q).toTPKindAlg_step_tp _
  have hc := KrausMap.completeOp_flagPerm (K := (KAf).step ⟨es.length, hk⟩)
    (P := Equiv.refl _)
    (σrF := A.innerSw Req' Resp' Q (A.storeSwOf Q j bR swO es')
      (MultiRelay.lastSwOL (jTest Q j) swO bR Q es'))
    (σrT := A.innerSw Req' Resp' Q (A.storeSwOf Q j bR swO es')
      (MultiRelay.lastSwOL (jTest Q j) swO bR Q es'))
    (σc := A.innerSw Req' Resp' Q (A.storeSwOf Q j bR swO es)
      (MultiRelay.lastSwOL (jTest Q j) swO bR Q es))
    ((KAf).relD.symm (flagSplitD y).1).1.1 ((KAf).relD.symm (flagSplitD x).1).1.1
    ((KAf).relD.symm (flagSplitD y).1).1.2 ((KAf).relD.symm (flagSplitD x).1).1.2
    ?hl ?hh ?hf r
  case hh =>
    intro _ _
    rw [KrausMap.haltOp_eq_zero hK]
    rfl
  case hf =>
    intro _ hxf
    have h0 : ((KAf).relD.symm (flagSplitD x).1).1.2 = false := hx.halt
    rw [h0] at hxf
    exact absurd hxf Bool.false_ne_true
  case hl =>
    intro _ _ z
    simp only [KindAlg.unitOut_step, AdaptiveIAlg.toTPKindAlg_step_op, AlgShape.tpStep_op]
    change (A.absorbAssignP Req' Resp' Q).tpOp true ⟨es.length, hk⟩ z _ _ =
      (A.absorbAssignP Req' Resp' Q).tpOp true ⟨es.length, hk⟩ z _ _
    simp only [Equiv.refl_apply]
    by_cases hcnt : x.1.1.1.1.cnt = (A.absorbAssignP Req' Resp' Q).ended
    · obtain ⟨hq, hlast⟩ := hx.ended hcnt
      refine A.tpOp_true_ended Q _ z _ _ hcnt hq fun hyq => ?_
      by_cases hm : es.length < (KAf).slots + (KAf).post
      · have he : (Distinguisher.entryOf (A.absorbAssignP Req' Resp' Q).pureD.kind y).any (jTest Q
          j) =
          false := by
          unfold Distinguisher.entryOf
          split_ifs
          · change jTest Q j y.1.2.1 = false
            rw [show y.1.2.1 = default from hyq]
            simp [jTest]
          · rfl
        have e1 : es' = es ++ [Distinguisher.entryOf (A.absorbAssignP Req' Resp' Q).pureD.kind
            y] := by
          rw [hes'def, if_pos hm]
        rw [e1, A.storeSwOf_append_of_not Q j bR swO es he,
          MultiRelay.lastSwOL_append_of_not bR Q es (fun r hr => by simpa [hr] using he),
          MultiRelay.lastSwOL_of_not bR Q hlast]
        exact ⟨rfl, rfl⟩
      · have e1 : es' = es := by rw [hes'def, if_neg hm]
        rw [e1]
        exact ⟨rfl, rfl⟩
    · refine A.tpOp_true_live Q j bR swO h hj hswO ⟨es.length, hk⟩ es rfl _ hcnt (hx.live hcnt)
        hx.post_none es' (fun i hi => ?_) _ z _
      by_cases hm : es.length < (KAf).slots + (KAf).post
      · have e1 : es' = es ++ [Distinguisher.entryOf (A.absorbAssignP Req' Resp' Q).pureD.kind
          y] := by
          rw [hes'def, if_pos hm]
        rw [e1]
        exact A.storeSwOf_append_of_lt Q j bR swO es _ hi
      · have e1 : es' = es := by rw [hes'def, if_neg hm]
        rw [e1]
  rw [Bool.cond_self, KindAlg.flagPerm_refl_refl, Equiv.refl_apply, Equiv.refl_apply] at hc
  exact hc

/-- **(c5) `innerπ` keeps the kind of the inner distinguisher.** -/
theorem innerπ_kind_pureD (es : List (Option ((Req × Fin (Q + 1)) × (X → Option Y))))
    (w : (KAf).DW × Bool) (q : (Req × Fin (Q + 1)) × (X → Option Y))
    (a : Option (AssignRelay.RespD X Y Resp Req' Resp')) :
    (A.absorbAssignP Req' Resp' Q).pureD.kind (A.innerπ Q (E := Bool × (KAf).DAnc)
      (c := (A.absorbAssignP Req' Resp' Q).budget + 2) j bR swO es (w, q,
          a)).1 = (A.absorbAssignP Req' Resp'
          Q).pureD.kind w := by
  -- TODO(unbundle-M4): `erw`: the workspace is spelled `tpKindS.DW` here and `unitOut.DW` in `pureD_kind`
  erw [pureD_kind, pureD_kind]
  rfl

/-- **(c5) The well-formed registers are kept by `innerπ`**, for a move of the main requests'
results that keeps the assignments. -/
theorem innerGin_innerπ (hswO : ∀ x, (swO x).2.1 = x.2.1)
    (es : List (Option ((Req × Fin (Q + 1)) × (X → Option Y))))
    (t : ((KAf).DW × Bool) × ((Req × Fin (Q + 1)) × (X → Option Y)) ×
      Option (AssignRelay.RespD X Y Resp Req' Resp')) (ht : t ∈ A.innerGin Req' Resp' Q j es) :
    A.innerπ Q (E := Bool × (KAf).DAnc) (c := (A.absorbAssignP Req' Resp' Q).budget +
        2) j bR swO es t
      ∈ A.innerGin Req' Resp' Q j es where
  len := ht.len
  post_none := ht.post_none
  halt := ht.halt
  clean := ht.clean
  pf := ht.pf
  live hc := (ht.live hc).move A Q (A.storeSwOf Q j bR swO es) (fun i x => by
      rcases A.storeSwOf_cases Q j bR swO es i with e | e <;> rw [e]
      · exact hswO x
      · rfl) _
  ended hc := ht.ended hc

/-- **(c2) The well-formed registers are closed under changes of the response register after a
request slot.** -/
theorem innerGin_resp (es : List (Option ((Req × Fin (Q + 1)) × (X → Option Y))))
    (w : (KAf).DW × Bool) (q : (Req × Fin (Q + 1)) × (X → Option Y))
    (a a' : Option (AssignRelay.RespD X Y Resp Req' Resp')) (ht : (w, q, a) ∈ A.innerGin Req' Resp'
        Q j es)
    (hl : ∃ r, es.getLast? = some (some r)) : (w, q, a') ∈ A.innerGin Req' Resp' Q j es where
  len := ht.len
  post_none := ht.post_none
  halt := ht.halt
  clean := ht.clean
  pf := ht.pf
  live hc := { (ht.live hc) with
    resp := fun hr => absurd hl fun ⟨r, hr'⟩ => hr r hr' }
  ended hc := ht.ended hc

theorem single_diag_ne_zero {ι : Type*} [DecidableEq ι] {e b : ι}
    (h : (Matrix.single e e (1 : ℂ)) b b ≠ 0) : b = e := by
  by_contra hb
  apply h
  rw [Matrix.single_apply, if_neg (fun h' => hb h'.1.symm)]

/-- **(c2) The initial state of the inner distinguisher is well formed.** -/
theorem innerGin_init (d : DReg ((KAf).DW × Bool) (KAf).width X Y ((Req × Fin (Q + 1)) × (X →
    Option Y))
      (AssignRelay.RespD X Y Resp Req' Resp'))
    (hd : (A.absorbAssignP Req' Resp' Q).pureD.init d ≠
        0) : d.1 ∈ A.innerGin Req' Resp' Q j [] := by
  obtain ⟨g, d0, rfl⟩ := exists_withFlag d
  rw [pureD_eq_withPostSlots] at hd
  have hg : g = false := by
    by_contra hg
    exact hd (embV_apply_of_notMem _ fun hr => hg (withFlag_mem_range_iff.1 hr))
  subst hg
  change embV (withFlag false) ((KAf).dilate ()).init (withFlag false d0) ≠ 0 at hd
  rw [embV_apply_self (withFlag_injective false), KindAlg.dilate_init] at hd
  change (KAf).gameMixed.dilInit () ((splitLogs.symm (((KAf).relD.symm d0).1.1,
    fun _ => none), ((KAf).relD.symm d0).1.2), ((KAf).relD.symm d0).2) ≠ 0 at hd
  simp only [MixedAlg.dilInit, appendKet_apply] at hd
  have hanc := right_ne_zero_of_mul hd
  have hpu := left_ne_zero_of_mul hd
  have hρ := fun h0 => hpu (purify_apply_eq_zero _ h0 _)
  simp only [KindAlg.gameMixed, MState.tensorKet_mat, Matrix.kroneckerMap_apply] at hρ
  have hfl := single_diag_ne_zero (right_ne_zero_of_mul hρ)
  have hm := left_ne_zero_of_mul hρ
  simp only [KindAlg.mgInitM, MState.reindex, MState.tensorKet_mat, Matrix.submatrix_apply,
    Equiv.symm_symm, Equiv.apply_symm_apply, Matrix.kroneckerMap_apply] at hm
  set S := ((KAf).relD.symm d0).1.1 with hS
  have h1 : (A.absorbAssignP Req' Resp' Q).init.mat ((A.absorbAssignP Req' Resp' Q).cntSplit S).1
      ((A.absorbAssignP Req' Resp' Q).cntSplit S).1 * (Matrix.single (0 : Fin _) 0 (1 : ℂ))
        ((A.absorbAssignP Req' Resp' Q).cntSplit S).2 ((A.absorbAssignP Req' Resp' Q).cntSplit
            S).2 ≠ 0 :=
    left_ne_zero_of_mul hm
  have hc0 := single_diag_ne_zero (right_ne_zero_of_mul h1)
  rw [AdaptiveIAlg.patchTag_init] at h1
  set P := ((A.absorbAssignP Req' Resp' Q).cntSplit S).1 with hP
  have h2 : (A.absorbAssignB Req' Resp' Q).init.mat ((A.absorbAssignB Req' Resp' Q).patchSplitB P).1
      ((A.absorbAssignB Req' Resp' Q).patchSplitB P).1 *
      ((ancState KindAlg.x₀).mat ((A.absorbAssignB Req' Resp' Q).patchSplitB P).2.1
        ((A.absorbAssignB Req' Resp' Q).patchSplitB P).2.1 *
        (Matrix.single (fun _ => none : X → Option Y) (fun _ => none) (1 : ℂ))
          ((A.absorbAssignB Req' Resp' Q).patchSplitB P).2.2 ((A.absorbAssignB Req' Resp'
              Q).patchSplitB P).2.2) ≠
              0 :=
    left_ne_zero_of_mul h1
  have htab := single_diag_ne_zero (right_ne_zero_of_mul (right_ne_zero_of_mul h2))
  rw [AdaptiveIAlg.absorb_init] at h2
  set Bb := ((A.absorbAssignB Req' Resp' Q).patchSplitB P).1 with hBb
  have h3 : A.init.mat (A.absSplit Bb).1 (A.absSplit Bb).1 *
      (Matrix.single A.absBlank A.absBlank (1 : ℂ)) (A.absSplit Bb).2 (A.absSplit Bb).2 ≠ 0 :=
    left_ne_zero_of_mul h2
  have hrest := single_diag_ne_zero (right_ne_zero_of_mul h3)
  have hr := Prod.mk.inj hrest
  have hlogs : d0.1.1.1.1.1.logs = fun _ => none := hr.1
  have hr2 := Prod.mk.inj hr.2
  have hstore : d0.1.1.1.1.1.store = fun _ => none := hr2.1
  have hr3 := Prod.mk.inj hr2.2
  have hq1 : d0.1.2.1.1 = default := hr3.1
  have ha : d0.1.2.2 = none := hr3.2
  have hq2 : d0.1.2.1.2 = fun _ => none := htab
  have hcnt : d0.1.1.1.2 = 0 := hc0
  have hanc' : d0.1.1.2.2.2 = (fun _ => Classical.arbitrary _, Classical.arbitrary Unit) := by
    by_contra hne
    exact hanc (if_neg hne)
  have hcl : MixedAlg.Clean 0 d0.1.1.2.2 := by
    refine ⟨fun i _ => ?_, ?_⟩
    · rw [show d0.1.1.2.2.2.1 = _ from congrArg Prod.fst hanc']
    · rw [show d0.1.1.2.2.2.2 = _ from congrArg Prod.snd hanc']
  have hpf : (withFlag false d0).1.1.2 = decide (A.slots < ([] : List (Option
      ((Req × Fin (Q + 1)) × (X → Option Y)))).length) := by
    simp [withFlag, flagSplitD]
  refine ⟨Nat.zero_le _, (fun i r _ => by simp), hfl, hcl, hpf, (fun _ => ?_), (fun hc => ?_)⟩
  · exact { logs := fun i => by
              change (d0.1.1.1.1.1.logs i).isSome = _
              simp [hlogs]
            store := fun i _ => by
              change d0.1.1.1.1.1.store i = none
              rw [hstore]
            last := fun i hi => absurd hi (by simp)
            blank := fun _ => by
              change d0.1.2.1 = default
              exact Prod.ext hq1 hq2
            kindQ := fun i hi => absurd hi (by simp)
            resp := fun _ => ha
            tags := fun i r hi => absurd hi (by simp) }
  · change d0.1.1.1.2 = _ at hc
    rw [hcnt] at hc
    exact absurd hc (by
      rw [AdaptiveIAlg.ended, AlgShape.ended]
      exact fun h => absurd (congrArg Fin.val h) (by simp))

/-- **(c2) The steps of the inner distinguisher keep the well-formed registers** before its last
slot, with the slot's entry, and a request satisfying the test there is the only one. -/
theorem innerGin_step (h : A.TracePreserving) (hj : j < Q)
    (es : List (Option ((Req × Fin (Q + 1)) × (X → Option Y))))
    (y x : DReg ((KAf).DW × Bool) (KAf).width X Y ((Req × Fin (Q + 1)) × (X → Option Y))
      (AssignRelay.RespD X Y Resp Req' Resp'))
    (hm : es.length < A.slots + A.post) (hx : x.1 ∈ A.innerGin Req' Resp' Q j es)
    (hne : unitaryMat ((A.absorbAssignP Req' Resp' Q).pureD.stepAt es.length) y x ≠ 0) :
    y.1 ∈ A.innerGin Req' Resp' Q j (es ++ [Distinguisher.entryOf (A.absorbAssignP Req' Resp'
        Q).pureD.kind y]) ∧
      ∀ r, Distinguisher.entryOf (A.absorbAssignP Req' Resp' Q).pureD.kind y = some r →
        jTest Q j r = true → ∀ (i : ℕ) (r' : (Req × Fin (Q + 1)) × (X → Option Y)),
          es[i]? = some (some r') → jTest Q j r' = false := by
  have hk : es.length < (KAf).slots + (KAf).post + 1 := by
    change es.length < A.slots + A.post + 1
    omega
  have hne' : unitaryMat ((((KAf).dilate ()).withPostSlots
      (fun i => (KAf).uStepD ((KAf).slots + 1 + i)) (KAf).post).stepAt es.length) y x ≠ 0 := by
    rw [show (A.absorbAssignP Req' Resp' Q).pureD.stepAt es.length = (((KAf).dilate
        ()).withPostSlots
      (fun i => (KAf).uStepD ((KAf).slots + 1 + i)) (KAf).post).stepAt es.length from by
        rw [pureD_eq_withPostSlots]] at hne
    exact hne
  obtain ⟨hpf, hop, hanc⟩ := KindAlg.dilatePost_stepAt_ne_zero (KAf) () es.length hk y x
    (hx.clean.1 _ le_rfl) hne'
  have hxf : ((KAf).relD.symm (flagSplitD x).1).1.2 = false := hx.halt
  have hK : ∑ z, (((KAf).step ⟨es.length, hk⟩).op z)ᴴ * ((KAf).step ⟨es.length, hk⟩).op z = 1 :=
    (A.absorbAssignP Req' Resp' Q).toTPKindAlg_step_tp _
  rw [show ((KAf).relD.symm (flagSplitD x).1).1 =
    (((KAf).relD.symm (flagSplitD x).1).1.1, false) from Prod.ext rfl hxf] at hop
  obtain ⟨z, -, hyf, hop'⟩ := KrausMap.completeOp_ne_zero_of_live (KrausMap.haltOp_eq_zero hK) hop
  simp only [KindAlg.unitOut_step, AdaptiveIAlg.toTPKindAlg_step_op, AlgShape.tpStep_op] at hop'
  change (A.absorbAssignP Req' Resp' Q).tpOp true ⟨es.length, hk⟩ z _ _ ≠ 0 at hop'
  have hcl : MixedAlg.Clean (es ++ [Distinguisher.entryOf
      (A.absorbAssignP Req' Resp' Q).pureD.kind y]).length y.1.1.1.2.2 := by
    rw [List.length_append, List.length_singleton]
    exact MixedAlg.clean_succ_of_reset hk hx.clean hanc
  have hpfy : y.1.1.2 = decide (A.slots < (es ++ [Distinguisher.entryOf
      (A.absorbAssignP Req' Resp' Q).pureD.kind y]).length) := by
    have hp := hpf
    have hpx : x.1.1.2 = decide (A.slots < es.length) := hx.pf
    change y.1.1.2 = (if es.length = A.slots then !x.1.1.2 else x.1.1.2) at hp
    rw [hp, hpx, List.length_append, List.length_singleton]
    by_cases hs : es.length = A.slots
    · rw [if_pos hs, hs]
      simp
    · rw [if_neg hs]
      by_cases hlt : A.slots < es.length
      · simp [hlt, show A.slots < es.length + 1 by omega]
      · simp [hlt, show ¬ A.slots < es.length + 1 by omega]
  have hentry : Distinguisher.entryOf (A.absorbAssignP Req' Resp' Q).pureD.kind y =
      if ((A.kind y.1.1.1.1.work.1.work || decide (y.1.1.1.1.cnt = (A.absorbAssignP Req' Resp' Q).ended))
          &&
        !y.1.1.2) = true then some y.1.2.1 else none := by
    unfold Distinguisher.entryOf
    have hyf' : y.1.1.1.2.1 = false := hyf
    -- TODO(unbundle-M4): `erw`: the workspace is spelled `tpKindS.DW` here and `unitOut.DW` in `pureD_kind`
    erw [pureD_kind]
    change (if ((A.kind y.1.1.1.1.work.1.work || decide (y.1.1.1.1.cnt = (A.absorbAssignP Req' Resp'
        Q).ended))
      || y.1.1.1.2.1) && !y.1.1.2 then _ else _) = _
    rw [hyf', Bool.or_false]
  have hpost' : ∀ r, A.slots ≤ es.length →
      Distinguisher.entryOf (A.absorbAssignP Req' Resp'
          Q).pureD.kind y ≠ some r := fun r hs hr => by
    rw [hentry, hpfy] at hr
    simp [List.length_append, show A.slots < es.length + 1 by omega] at hr
  have hpn : ∀ i r, A.slots ≤ i → (es ++ [Distinguisher.entryOf
      (A.absorbAssignP Req' Resp' Q).pureD.kind y])[i]? ≠ some (some r) := fun i r hs hr => by
    by_cases hi : i < es.length
    · rw [List.getElem?_append_left hi] at hr
      exact hx.post_none i r hs hr
    · by_cases hi' : i = es.length
      · subst hi'
        rw [List.getElem?_append_right le_rfl] at hr
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hr
        exact hpost' r hs hr
      · rw [List.getElem?_eq_none (by simp; omega)] at hr
        exact absurd hr (by simp)
  by_cases hcnt : x.1.1.1.1.cnt = (A.absorbAssignP Req' Resp' Q).ended
  · -- an ended column: the identity
    erw [tpOp_true_apply] at hop'
    have hcnt' : (((KAf).relD.symm (flagSplitD x).1).1.1 : (A.absorbAssignP Req' Resp'
        Q).CReg).workspace.cnt =
      (A.absorbAssignP Req' Resp' Q).ended := hcnt
    rw [if_pos hcnt'] at hop'
    split_ifs at hop' with hz
    · have hyx : ((KAf).relD.symm (flagSplitD y).1).1.1 = ((KAf).relD.symm (flagSplitD x).1).1.1
        := by
        by_contra hne0
        exact hop' (Matrix.one_apply_ne hne0)
      obtain ⟨hq, -⟩ := hx.ended hcnt
      have hyq : y.1.2.1 = default := by
        have := congrArg (fun d => d.1.2.1) hyx
        exact this.trans hq
      have hyc : y.1.1.1.1.cnt = (A.absorbAssignP Req' Resp' Q).ended := by
        have := congrArg (fun d => d.1.1.2) hyx
        exact this.trans hcnt
      have he : ∀ r, Distinguisher.entryOf (A.absorbAssignP Req' Resp' Q).pureD.kind y = some r →
          jTest Q j r = false := fun r hr => by
        rw [hentry] at hr
        split_ifs at hr
        · cases hr
          rw [hyq]
          simp [jTest]
      refine ⟨⟨by simp; omega, hpn, hyf, hcl, hpfy, fun hc => absurd hyc hc, fun _ => ⟨hyq,
        fun r hr => he r (by simpa using hr)⟩⟩, fun r hr hJ => absurd hJ (by rw [he r hr]; simp)⟩
    · exact absurd rfl hop'
  · erw [A.tpOp_true_alive Q h _ z _ ((KAf).relD.symm (flagSplitD x).1).1.1 hcnt] at hop'
    split_ifs at hop' with hz
    · exact absurd rfl hop'
    have hcu : ((A.innerP Req' Resp' Q ⟨es.length, hk⟩ ((KAf).relD.symm (flagSplitD
        x).1).1.1)).workspace.cnt ≠
        (A.absorbAssignP Req' Resp' Q).ended := hcnt
    obtain ⟨hinl, hcut⟩ := tpLead_cnt (B := A.absorbAssignP Req' Resp' Q) ⟨es.length,
        hk⟩ z _ _ hop' hcu
    rcases z with r | r | c
    · have hya : y.1.1.1.1.cnt ≠ (A.absorbAssignP Req' Resp' Q).ended := hinl r rfl
      obtain ⟨hLy, hJy⟩ := A.liveGood_row Q j hj ⟨es.length, hk⟩ es rfl
        ((KAf).relD.symm (flagSplitD x).1).1.1 ((KAf).relD.symm (flagSplitD y).1).1.1
        (hx.live hcnt) hx.post_none (.inl r) hop'
        (Distinguisher.entryOf (A.absorbAssignP Req' Resp' Q).pureD.kind y) (by
          rw [hentry, hpfy]
          simp only [List.length_append, List.length_singleton]
          have hya' : decide (y.1.1.1.1.cnt = (A.absorbAssignP Req' Resp' Q).ended) = false := by
            simpa using hya
          rw [hya', Bool.or_false]
          by_cases hs : es.length < A.slots
          · simp only [hs, show ¬ A.slots < es.length + 1 by omega, true_and, decide_false,
              Bool.not_false, Bool.and_true]
            rfl
          · simp [hs, show A.slots < es.length + 1 by omega])
      exact ⟨⟨by simp; omega, hpn, hyf, hcl, hpfy, fun _ => hLy, fun hc => absurd hc hya⟩,
        fun r hr hJ i r' hr' => by
          by_contra hJ'
          exact (hJy r hr hJ i r' hr' (by simpa using hJ')).elim⟩
    · obtain ⟨hyc, hyk⟩ := hcut r rfl
      obtain ⟨-, -, -, H2⟩ := A.innerRow_live Q ⟨es.length, hk⟩ (.inr (.inl r)) _ _ hop'
        (A.innerP_live Q ⟨es.length, hk⟩ es rfl _ (hx.live hcnt)).1
      have hyq : y.1.2.1 = default := (H2 (Or.inr hyk)).2
      have he : ∀ r, Distinguisher.entryOf (A.absorbAssignP Req' Resp' Q).pureD.kind y = some r →
          jTest Q j r = false := fun r hr => by
        rw [hentry] at hr
        split_ifs at hr
        · cases hr
          rw [hyq]
          simp [jTest]
      refine ⟨⟨by simp; omega, hpn, hyf, hcl, hpfy, fun hc => absurd hyc hc, fun _ => ⟨hyq,
        fun r hr => he r (by simpa using hr)⟩⟩, fun r hr hJ => absurd hJ (by rw [he r hr]; simp)⟩
    · exact absurd rfl hop'

/-- **(c2) The well-formed registers of `absorbAssignP`'s pure distinguisher**
(`Distinguisher.InnerSupp`), for a trace-preserving adversary and a test number below `Q`. -/
theorem innerSupp_pureD (h : A.TracePreserving) (hj : j < Q) :
    Distinguisher.InnerSupp (jTest Q j) (A.innerGin Req' Resp' Q j) (A.absorbAssignP Req' Resp'
        Q).pureD where
  resp es w q a a' ht hl := A.innerGin_resp Q j es w q a a' ht hl
  init d hd := A.innerGin_init Q j d hd
  step es y x hm hx hne := A.innerGin_step Q j h hj es y x hm hx hne

end TowerD

end AdaptiveIAlg

end GordieHowe.Quantum
