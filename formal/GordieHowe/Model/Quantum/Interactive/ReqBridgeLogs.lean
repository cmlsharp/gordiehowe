-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.ReqBridge
public import GordieHowe.Model.QROM.AdaptiveCount

@[expose] public section

-- The proofs below read the definition of the bridge (irreducible elsewhere).
set_option allowUnsafeReducibility true in
attribute [local reducible] GordieHowe.Quantum.bridgeAlg

/-!
# The requests of the bridge algorithm are read from the absorbed logs

The request of the bridge algorithm (`bridgeAlg`) at the step after slot `j` is the outer request
of the absorbed copy of slot `j`'s log, or the dummy. This file gives the supports of the run that
`GordieHowe/Model/Quantum/Interactive/ReqBridgeSlots.lean` carries to the logged requests of the
bridge's instance (`bridgeAlg_slotLogs`, `bridgeAlg_logs`).

- `AdaptiveIAlg.stepTab_logs`: a step of the adversary absorbed with a table changes no absorbed log
  but the one of its slot; `AdaptiveIAlg.absorbTab_tracePreserving`;
  `AdaptiveIAlg.toTPKindAlg_op_ne_zero`: with vanishing halting operators, an operator of the
  trace-preserving form is nonzero only where one of the adversary's operators is.
- `KindAlg.valid_fullCircBoth_ws`: a certificate of the compiled composition
  (`ReprogrammedCircuit.Valid`) from sets of workspaces carried by the adversary's steps;
  `AdaptiveIAlg.valid_logS`: for the adversary absorbed with a table, the sets `logS N n` (absorbed
  logs blank from slot `n`, every request of `N` the outer request of a logged one).
- `QueryAlg.supported_simStage_of`: supports of the simulated run from supports carried by the
  steps; `ExpandAdvSupp.expandAdv_step_supp`, `ExpandAdvSupp.expandAdv_step0_supp`: through the
  expansion.
- `cohSet`, `wSet`, `cohLogs`, `cohSet_congr`, `cohStep_supp`, `bridgeStep_supp`, `cohInit`,
  `initW`, `bridge_init_supp`, `bridge_hstep0`: the supports of the bridge's run and its steps.
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.Quantum

/-- A nonzero entry of a placed matrix comes from a nonzero entry of the matrix. -/
theorem embed_ne_zero_exists {κ ι : Type*} [Fintype κ] [DecidableEq ι] {e : κ → ι}
    {σ : Matrix κ κ ℂ} {i j : ι} (h : embed e σ i j ≠ 0) :
    ∃ a b, e a = i ∧ e b = j ∧ σ a b ≠ 0 := by
  unfold embed at h
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  by_cases hab : e a = i ∧ e b = j
  · rw [if_pos hab] at hb
    exact ⟨a, b, hab.1, hab.2, hb⟩
  · rw [if_neg hab] at hb
    exact absurd rfl hb

namespace AdaptiveIAlg

/-! ### The trace-preserving form follows the adversary's operators -/

section TP

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shB : AlgShape X Y Req Resp} (B : AdaptiveIAlg shB O)

theorem cntSplit_tpShift (z : B.CReg) : (B.cntSplit (B.tpShift z)).1 = (B.cntSplit z).1 := by
  obtain ⟨⟨⟨w, c⟩, rq, rs⟩, q⟩ := z
  rfl

theorem cntSplit_endSwap (z : B.CReg) : (B.cntSplit (B.endSwap z)).1 = (B.cntSplit z).1 := by
  obtain ⟨⟨⟨w, c⟩, rq, rs⟩, q⟩ := z
  rfl

/-- **An operator of the trace-preserving form is nonzero only where one of the adversary's
operators is**, when the adversary's halting operators vanish (a trace-preserving adversary,
`TracePreserving.haltOp_eq_zero`). -/
theorem toTPKindAlg_op_ne_zero (hB : ∀ k, (B.step k).haltOp = 0) {k : StepIdx B.slots B.post}
    {z : B.R ⊕ (B.R ⊕ Fin (B.budget + 2))} {y x : B.CReg}
    (h : (B.toTPKindAlg.step k).op z y x ≠ 0) :
    ∃ r, (B.step k).op r (B.cntSplit y).1 (B.cntSplit x).1 ≠ 0 := by
  simp only [AdaptiveIAlg.toTPKindAlg_step_op, AlgShape.tpStep_op] at h
  change B.tpOp false k z y x ≠ 0 at h
  rcases z with r | r | c
  · by_cases hk : (k : ℕ) < B.slots
    · simp only [tpOp_false, tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, hk, if_true,
        restrict_permConj_op_apply] at h
      have hK : (B.cntKraus k).op r (B.tpShift.symm y) x ≠ 0 := fun h' => h (by rw [h', mul_zero])
      rw [cntKraus_op_apply] at hK
      refine ⟨r, fun h' => hK ?_⟩
      rw [← B.cntSplit_tpShift (B.tpShift.symm y), Equiv.apply_symm_apply, h', zero_mul]
    · simp only [tpOp_false, tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, hk, if_false] at h
      rw [cntKraus_op_apply] at h
      exact ⟨r, left_ne_zero_of_mul h⟩
  · by_cases hk : (k : ℕ) < B.slots
    · simp only [tpOp_false, tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, hk, if_true,
        restrict_permConj_op_apply] at h
      have hK : (B.cntKraus k).op r (B.endSwap.symm y) x ≠ 0 := fun h' => h (by rw [h', mul_zero])
      rw [cntKraus_op_apply] at hK
      refine ⟨r, fun h' => hK ?_⟩
      rw [← B.cntSplit_endSwap (B.endSwap.symm y), Equiv.apply_symm_apply, h', zero_mul]
    · simp [tpOp_false, tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, hk] at h
  · simp only [tpOp_false, tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, hB k, Matrix.zero_kronecker,
      Matrix.submatrix_zero,
      Matrix.zero_apply] at h
    exact absurd rfl h

end TP

/-! ### A step of the adversary absorbed with a table -/

section Tab

variable {X Y Req Resp O Req₁ Resp₁ Req₂ Resp₂ : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂)

/-- **The steps of the adversary absorbed with a table are trace preserving** when the adversary's
are. -/
theorem stepTab_tp (h : A.TracePreserving) (k : StepIdx A.slots A.post) :
    ∑ r, ((A.stepTab F k).op r)ᴴ * (A.stepTab F k).op r = 1 := by
  rw [stepTab_eq]
  exact KrausMap.comp_tp (KrausMap.tp_ofPerm _)
    (KrausMap.comp_tp (KrausMap.reindex_tp _ (KrausMap.tensorId_tp
      (KrausMap.reindex_tp _ (KrausMap.tensorId_tp (h k) _)) _)) (KrausMap.tp_ofPerm _))

/-- **Absorbing with a table keeps trace preservation.** -/
theorem absorbTab_tracePreserving (h : A.TracePreserving) (tab : A.OuterTab Req₂ Resp₂) :
    (A.absorbTab F tab).TracePreserving := fun k => A.stepTab_tp F h k

theorem afterPermTab_logs' (t : A.OuterTab Req₂ Resp₂) (j : Fin A.slots)
    (d : DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁) :
    (A.afterPermTab F t j d).1.1.logs = d.1.1.logs := by
  have h1 : ∀ d' : DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁,
      (A.storePerm j d').1.1.logs = d'.1.1.logs := fun d' => by
    unfold AdaptiveIAlg.storePerm AlgShape.storePerm
    dsimp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
    by_cases h : (d'.1.1.logs j).isSome = true
    · rw [if_pos h]
    · rw [if_neg h]
  have h2 : ∀ d' : DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁,
      (A.answerPermTab F t j d').1.1.logs = d'.1.1.logs := fun d' => by
    unfold AdaptiveIAlg.answerPermTab
    dsimp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
    split <;> rfl
  have h3 : ∀ d' : DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁,
      (A.clearPerm F.base j d').1.1.logs = d'.1.1.logs := fun d' => by
    unfold AdaptiveIAlg.clearPerm AlgShape.clearPerm
    dsimp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
    split <;> rfl
  unfold AdaptiveIAlg.afterPermTab
  simp only [Equiv.trans_apply, h1, h2, h3]

theorem afterAtTab_logs' (k : ℕ)
    (d : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁) :
    (A.afterAtTab F k d).1.1.1.logs = d.1.1.1.logs := by
  unfold AdaptiveIAlg.afterAtTab
  split
  · exact A.afterPermTab_logs' F _ _ _
  · rfl

theorem setAt_logs (k : ℕ) (d : DReg (A.AbsW (Resp' := Resp₁)) A.width X Y Req₁ Resp₁)
    (j : Fin A.slots) (hj : (j : ℕ) ≠ k) : (A.setAt F.base k d).1.1.logs j = d.1.1.logs j := by
  rw [AdaptiveIAlg.setAt_def]
  split
  · rename_i h
    unfold AdaptiveIAlg.setPerm AlgShape.setPerm
    dsimp only [Function.Involutive.toPerm, Equiv.coe_fn_mk]
    split
    · exact Function.update_of_ne (fun e => hj (by rw [e])) _ _
    · rfl
  · rfl

/-- **A step of the adversary absorbed with a table changes no absorbed log but the one of its
slot.** -/
theorem stepTab_logs {k : StepIdx A.slots A.post} {r : (A.absorb F.base).R}
    {y x : DReg ((A.absorb F.base).W × A.OuterTab Req₂ Resp₂) A.width X Y Req₁ Resp₁}
    (h : (A.stepTab F k).op r y x ≠ 0) (j : Fin A.slots) (hj : (j : ℕ) ≠ k) :
    y.1.1.1.logs j = x.1.1.1.logs j := by
  simp only [stepTab_eq, KrausMap.comp, Matrix.mul_apply] at h
  obtain ⟨u, -, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hyu : y = A.tabLift F (A.setAt F.base k) u := by
    have := left_ne_zero_of_mul hu
    rw [KrausMap.ofPerm_op_apply] at this
    by_contra hne
    exact this (if_neg hne)
  obtain ⟨v, -, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul hu)
  have hvx : v = A.afterAtTab F k x := by
    have := right_ne_zero_of_mul hv
    rw [KrausMap.ofPerm_op_apply] at this
    by_contra hne
    exact this (if_neg hne)
  have huv : u.1.1.1.logs = v.1.1.1.logs := by
    have hL := left_ne_zero_of_mul hv
    rw [KrausMap.tensorId_reindex_op_apply] at hL
    have h1 := right_ne_zero_of_mul hL
    have h2 := left_ne_zero_of_mul hL
    rw [liftedStep, AlgShape.liftedStep, KrausMap.tensorId_reindex_op_apply] at h2
    have h3 := right_ne_zero_of_mul h2
    by_contra hne
    apply h3
    refine Matrix.one_apply_ne fun he => hne ?_
    exact congrArg (fun p => p.1) he
  rw [hyu]
  change (A.setAt F.base k (((u.1.1.1, u.1.2), u.2))).1.1.logs j = _
  rw [A.setAt_logs F k _ j hj]
  change u.1.1.1.logs j = _
  rw [huv, hvx, afterAtTab_logs']

end Tab

end AdaptiveIAlg

/-! ### A certificate from sets of workspaces -/

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O) (Ch : Challenger X Y Req Resp) (S : ℕ → Set B.W)

open Classical in
/-- **The supports at the queries from sets of workspaces** (proof-internal): during slot `j`,
the workspace in `S (j + 1)`; during post batch `b`, in `S (slots + b + 1)`. -/
noncomputable def wsG (k : ℕ) : Set (B.CW Ch) :=
  if k < B.slots * (Ch.q + B.width) then B.advIn Ch (S (k / (Ch.q + B.width) + 1))
  else B.advIn Ch (S (B.slots + (k - B.slots * (Ch.q + B.width)) / B.width + 1))

theorem slotLen_pos : 0 < Ch.q + B.width := by
  have := B.width_pos
  omega

theorem wsG_slot (j : Fin B.slots) {r : ℕ} (hr : r < Ch.q + B.width) :
    B.wsG Ch S ((j : ℕ) * (Ch.q + B.width) + r) = B.advIn Ch (S (j + 1)) := by
  have hlt : (j : ℕ) * (Ch.q + B.width) + r < B.slots * (Ch.q + B.width) :=
    calc (j : ℕ) * (Ch.q + B.width) + r < ((j : ℕ) + 1) * (Ch.q + B.width) := by
          rw [add_mul, one_mul]
          omega
      _ ≤ B.slots * (Ch.q + B.width) := Nat.mul_le_mul_right _ j.isLt
  have hdiv : ((j : ℕ) * (Ch.q + B.width) + r) / (Ch.q + B.width) = j := by
    rw [add_comm, Nat.add_mul_div_right _ _ (B.slotLen_pos Ch), Nat.div_eq_of_lt hr, zero_add]
  unfold wsG
  rw [if_pos hlt, hdiv]

theorem wsG_post (b : ℕ) {r : ℕ} (hr : r < B.width) :
    B.wsG Ch S (B.slots * (Ch.q + B.width) + b * B.width + r) =
      B.advIn Ch (S (B.slots + b + 1)) := by
  unfold wsG
  rw [if_neg (by omega)]
  have hw := B.width_pos
  rw [show B.slots * (Ch.q + B.width) + b * B.width + r - B.slots * (Ch.q + B.width) =
    r + b * B.width by omega, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hr, zero_add]

variable {B Ch S}

theorem advKraus_ne_zero' {k : StepIdx B.slots B.post} {z : B.R} {p' p : QueryReg (B.CW Ch) 1 X Y}
    (h : (B.advKraus Ch k).op z p' p ≠ 0) :
    (B.step k).op z p'.1.adv p.1.adv ≠ 0 := by
  rw [KindAlg.advKraus, KrausMap.tensorId_reindex_op_apply] at h
  exact left_ne_zero_of_mul h

variable [Nonempty X] [AddCommGroup Y]

open ReprogrammedCircuit

theorem ofPerm_eq_of_ne_zero {π : Equiv.Perm (QueryReg (B.CW Ch) 1 X Y)} {r : Unit}
    {p' p : QueryReg (B.CW Ch) 1 X Y} (h : (KrausMap.ofPerm π).op r p' p ≠ 0) : p' = π p := by
  rw [KrausMap.ofPerm_op_apply] at h
  by_contra hne
  exact h (if_neg hne)

/-- A basis permutation that keeps the workspace respects the certificate on a set of
workspaces. -/
theorem valid_ofPerm_ws {π : Equiv.Perm (QueryReg (B.CW Ch) 1 X Y)}
    (hπ : ∀ p, (π p).1.adv.workspace = p.1.adv.workspace) {T : Set B.W} {c : ReprogrammedCircuit (B.CW Ch) X Y}
    {k : ℕ} {Q : Set (B.CW Ch)} (hc : Valid (fun _ => Set.univ) (B.wsG Ch S) c k (B.advIn Ch T) Q) :
    Valid (fun _ => Set.univ) (B.wsG Ch S) (.kraus (KrausMap.ofPerm π) c) k (B.advIn Ch T) Q :=
  ⟨KrausMap.tp_ofPerm _, fun _ _ _ _ _ _ => Iff.rfl, B.advIn Ch T, fun r p' p hp h => by
    rw [ofPerm_eq_of_ne_zero h]
    change (π p).1.adv.workspace ∈ T
    rw [hπ]
    exact hp, hc⟩

theorem valid_advQueries_ws (ass : B.CW Ch → List (Assignment X Y)) (k₀ : ℕ) (T : Set B.W)
    (hG : ∀ r < B.width, B.wsG Ch S (k₀ + r) = B.advIn Ch T) :
    Valid (fun _ => Set.univ) (B.wsG Ch S) (B.advQueries Ch ass) k₀ (B.advIn Ch T) (B.advIn Ch T) := by
  refine Valid.concat_finRange (L := 1) (P := fun _ => B.advIn Ch T) (fun _ => rfl) fun k => ?_
  simp only [mul_one]
  have hG' := hG k k.isLt
  refine valid_ofPerm_ws (fun p => rfl) ?_
  refine ⟨fun v hv => by rw [hG']; exact hv, fun v _ hv => absurd trivial hv, ?_⟩
  rw [hG']
  exact valid_ofPerm_ws (fun p => rfl) subset_rfl

theorem valid_chalQueries_ws (j : Fin B.slots) :
    Valid (fun _ => Set.univ) (B.wsG Ch S) (B.chalQueries Ch j) ((j : ℕ) * (Ch.q + B.width))
      (B.advIn Ch (S (j + 1))) (B.advIn Ch (S (j + 1))) := by
  refine Valid.concat_finRange (L := 1) (P := fun _ => B.advIn Ch (S (j + 1))) (fun _ => rfl)
    fun i => ?_
  simp only [mul_one]
  have hG := B.wsG_slot Ch S j (r := i) (by omega)
  refine valid_ofPerm_ws (fun p => rfl) ?_
  refine ⟨fun v hv => by rw [hG]; exact hv, fun v _ hv => absurd trivial hv, ?_⟩
  rw [hG]
  exact valid_ofPerm_ws (fun p => rfl) subset_rfl

theorem writeReply_workspace (j : Fin B.slots) (p : QueryReg (B.CW Ch) 1 X Y) :
    (B.writeReply Ch j p).1.adv.workspace = p.1.adv.workspace := by
  change (if (p.1.chal.logs j).isSome = true then _ else p).1.adv.workspace = _
  split_ifs <;> rfl

theorem copyReq_workspace (j : Fin B.slots) (p : QueryReg (B.CW Ch) 1 X Y) :
    (B.copyReq Ch j p).1.adv.workspace = p.1.adv.workspace := by
  rw [copyReq_apply]
  split_ifs <;> rfl

variable (S)

/-- **Slot `j` carries the workspaces `S j` to `S (j + 1)`**, when the adversary's Kraus map
before slot `j` does (`hslot`). -/
theorem valid_slotCircBoth_ws (htp : B.StepsTP) (j : Fin B.slots)
    (hslot : ∀ z (y x : DReg B.W B.width X Y Req Resp), (B.step (slotStep j)).op z y x ≠ 0 →
      x.workspace ∈ S j → y.workspace ∈ S (j + 1)) :
    Valid (fun _ => Set.univ) (B.wsG Ch S) (B.slotCircBoth Ch j) ((j : ℕ) * (Ch.q + B.width))
      (B.advIn Ch (S j)) (B.advIn Ch (S (j + 1))) := by
  refine ⟨KrausMap.tp_tensorId_reindex (htp _) _, fun _ _ _ _ _ _ => Iff.rfl,
    B.advIn Ch (S (j + 1)), fun z p' p hp h => hslot z _ _ (advKraus_ne_zero' h) hp, ?_⟩
  refine ⟨KrausMap.tp_comp (KrausMap.tp_ofPerm _) (KrausMap.tp_measureFn _),
    fun _ _ _ _ _ _ => Iff.rfl, B.advIn Ch (S (j + 1)), fun o p' p hp h => ?_, ?_⟩
  · rw [AdaptiveIAlg.measReq_op_apply Ch j o p' p] at h
    have hy : p' = B.copyReq Ch j p := by
      by_contra h'
      exact h (mul_eq_zero_of_left (if_neg h') _)
    subst hy
    change (B.copyReq Ch j p).1.adv.workspace ∈ S (j + 1)
    rw [copyReq_workspace]
    exact hp
  refine Valid.append (valid_chalQueries_ws j) ?_
  rw [KindAlg.queries_chalQueries]
  refine valid_ofPerm_ws (writeReply_workspace j) ?_
  refine valid_advQueries_ws _ _ _ fun r hr => ?_
  rw [add_assoc]
  exact B.wsG_slot Ch S j (by omega)

/-- **Post batch `b` carries the workspaces `S (slots + b)` to `S (slots + b + 1)`.** -/
theorem valid_postCirc_ws (htp : B.StepsTP) (b : Fin B.post)
    (hpost : ∀ z (y x : DReg B.W B.width X Y Req Resp), (B.step (postStep b)).op z y x ≠ 0 →
      x.workspace ∈ S (B.slots + b) → y.workspace ∈ S (B.slots + b + 1)) :
    Valid (fun _ => Set.univ) (B.wsG Ch S) (B.postCirc Ch b)
      (B.slots * (Ch.q + B.width) + b * B.width) (B.advIn Ch (S (B.slots + b)))
      (B.advIn Ch (S (B.slots + b + 1))) := by
  refine ⟨KrausMap.tp_tensorId_reindex (htp _) _, fun _ _ _ _ _ _ => Iff.rfl,
    B.advIn Ch (S (B.slots + b + 1)), fun z p' p hp h => hpost z _ _ (advKraus_ne_zero' h) hp,
    ?_⟩
  exact valid_advQueries_ws _ _ _ fun r hr => B.wsG_post Ch S b hr

/-- **The certificate of the composition from sets of workspaces**: the support of the
workspace runs through `S 0, S 1, …, S (slots + post + 1)` when the adversary's Kraus map before
slot `j` maps `S j` into `S (j + 1)` (`hslot`) and the later one of step `k` maps `S k` into
`S (k + 1)` (`hpost`). -/
theorem valid_fullCircBoth_ws (htp : B.StepsTP)
    (hslot : ∀ (j : Fin B.slots) z (y x : DReg B.W B.width X Y Req Resp),
      (B.step (slotStep j)).op z y x ≠ 0 → x.workspace ∈ S j → y.workspace ∈ S (j + 1))
    (hpost : ∀ (k : StepIdx B.slots B.post), B.slots ≤ (k : ℕ) →
      ∀ z (y x : DReg B.W B.width X Y Req Resp),
      (B.step k).op z y x ≠ 0 → x.workspace ∈ S k → y.workspace ∈ S (k + 1)) :
    Valid (fun _ => Set.univ) (B.wsG Ch S) (B.fullCircBoth Ch) 0 (B.advIn Ch (S 0))
      (B.advIn Ch (S (B.slots + B.post + 1))) := by
  have h1 : Valid (fun _ => Set.univ) (B.wsG Ch S)
      (concat ((List.finRange B.slots).map fun j => B.slotCircBoth Ch j))
      0 (B.advIn Ch (S 0)) (B.advIn Ch (S B.slots)) :=
    Valid.concat_finRange (L := Ch.q + B.width) (P := fun j => B.advIn Ch (S j))
      (fun j => B.queries_slotCircBoth Ch j)
      fun j => by simpa using valid_slotCircBoth_ws S htp j (hslot j)
  have h2 : Valid (fun _ => Set.univ) (B.wsG Ch S)
      (concat ((List.finRange B.post).map (B.postCirc Ch)))
      (0 + B.slots * (Ch.q + B.width)) (B.advIn Ch (S (B.slots + 0)))
      (B.advIn Ch (S (B.slots + B.post))) :=
    Valid.concat_finRange (L := B.width) (P := fun b => B.advIn Ch (S (B.slots + b)))
      (fun b => B.queries_postCirc Ch b)
      fun b => by
        rw [zero_add]
        exact valid_postCirc_ws S htp b (hpost (postStep b) (by simp [postStep]))
  unfold KindAlg.fullCircBoth
  refine Valid.append (Q := B.advIn Ch (S (B.slots + B.post)))
    (Valid.append (Q := B.advIn Ch (S B.slots)) h1 ?_) ?_
  · rw [ReprogrammedCircuit.queries_concat_finRange (fun j => B.queries_slotCircBoth Ch j)]
    exact h2
  · exact ⟨KrausMap.tp_tensorId_reindex (htp _) _, fun _ _ _ _ _ _ => Iff.rfl,
      B.advIn Ch (S (B.slots + B.post + 1)), fun z p' p hp h =>
        hpost lastStep (by simp [lastStep]) z _ _ (advKraus_ne_zero' h) hp, subset_rfl⟩

end KindAlg

/-! ### The certificate of the adversary absorbed with a table -/

namespace AdaptiveIAlg

variable {X Y Req Resp O Req₁ Resp₁ Req₂ Resp₂ : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂)
  (tab : A.OuterTab Req₂ Resp₂)

/-- **The workspaces with the absorbed logs blank from slot `n` on and every request of `N` the
outer request of a logged request** (proof-internal). -/
def logS (N : Set Req₂) (n : ℕ) : Set (A.absorbTab F tab).toTPKindAlg.W :=
  {w | (∀ j : Fin A.slots, n ≤ (j : ℕ) → w.1.1.logs j = none) ∧
    ∀ x ∈ N, ∃ j r, w.1.1.logs j = some r ∧ F.outer (A.reqCount w.1.1.logs j) r = some x}

variable {A F tab}

/-- **A step of the trace-preserving form changes no absorbed log but the one of its slot**, for a
trace-preserving adversary. -/
theorem tp_absorbTab_logs (hA : A.TracePreserving) {k : StepIdx A.slots A.post}
    {z : (A.absorbTab F tab).R ⊕ ((A.absorbTab F tab).R ⊕ Fin (A.budget + 2))}
    {y x : DReg (A.absorbTab F tab).toTPKindAlg.W A.width X Y Req₁ Resp₁}
    (h : ((A.absorbTab F tab).toTPKindAlg.step k).op z y x ≠ 0) (j : Fin A.slots)
    (hj : (j : ℕ) ≠ k) : y.workspace.1.1.logs j = x.workspace.1.1.logs j := by
  obtain ⟨r, hr⟩ := (A.absorbTab F tab).toTPKindAlg_op_ne_zero
    (fun k => TracePreserving.haltOp_eq_zero (A.absorbTab_tracePreserving F hA tab) k) h
  exact A.stepTab_logs F hr j hj

/-- **The step of slot `n` carries `logS N n` to `logS N (n + 1)`.** -/
theorem logS_succ (hA : A.TracePreserving) (N : Set Req₂) {k : StepIdx A.slots A.post} {n : ℕ}
    (hk : (k : ℕ) = n)
    {z : (A.absorbTab F tab).R ⊕ ((A.absorbTab F tab).R ⊕ Fin (A.budget + 2))}
    {y x : DReg (A.absorbTab F tab).toTPKindAlg.W A.width X Y Req₁ Resp₁}
    (h : ((A.absorbTab F tab).toTPKindAlg.step k).op z y x ≠ 0)
    (hx : x.workspace ∈ A.logS F tab N n) : y.workspace ∈ A.logS F tab N (n + 1) := by
  obtain ⟨hb, he⟩ := hx
  refine ⟨fun j hj => ?_, fun x' hx' => ?_⟩
  · rw [tp_absorbTab_logs hA h j (by omega)]
    exact hb j (by omega)
  · obtain ⟨j, r, hjr, hr⟩ := he x' hx'
    have hjn : (j : ℕ) < n := by
      by_contra h'
      rw [hb j (by omega)] at hjr
      exact absurd hjr (by simp)
    have hc : A.reqCount y.workspace.1.1.logs j = A.reqCount x.workspace.1.1.logs j :=
      congrArg List.length (requestsBefore_congr fun i hi => tp_absorbTab_logs hA h i (by omega))
    exact ⟨j, r, by rw [tp_absorbTab_logs hA h j (by omega)]; exact hjr, by rw [hc]; exact hr⟩

/-- **A step after the slots carries `logS N n` to `logS N (n + 1)`.** -/
theorem logS_post (hA : A.TracePreserving) (N : Set Req₂) {k : StepIdx A.slots A.post} {n : ℕ}
    (hk : A.slots ≤ (k : ℕ))
    {z : (A.absorbTab F tab).R ⊕ ((A.absorbTab F tab).R ⊕ Fin (A.budget + 2))}
    {y x : DReg (A.absorbTab F tab).toTPKindAlg.W A.width X Y Req₁ Resp₁}
    (h : ((A.absorbTab F tab).toTPKindAlg.step k).op z y x ≠ 0)
    (hx : x.workspace ∈ A.logS F tab N n) : y.workspace ∈ A.logS F tab N (n + 1) := by
  have hne : ∀ j : Fin A.slots, (j : ℕ) ≠ k := fun j => by have := j.isLt; omega
  obtain ⟨hb, he⟩ := hx
  refine ⟨fun j hj => ?_, fun x' hx' => ?_⟩
  · rw [tp_absorbTab_logs hA h j (hne j)]
    exact hb j (by omega)
  · obtain ⟨j, r, hjr, hr⟩ := he x' hx'
    have hc : A.reqCount y.workspace.1.1.logs j = A.reqCount x.workspace.1.1.logs j :=
      congrArg List.length (requestsBefore_congr fun i _ => tp_absorbTab_logs hA h i (hne i))
    exact ⟨j, r, by rw [tp_absorbTab_logs hA h j (hne j)]; exact hjr, by rw [hc]; exact hr⟩

variable [Nonempty X] [AddCommGroup Y]

/-- **The certificate of the composition of the adversary absorbed with a table**, through the
sets `logS N`. -/
theorem valid_logS (hA : A.TracePreserving) (N : Set Req₂) (C₁ : Challenger X Y Req₁ Resp₁) :
    ReprogrammedCircuit.Valid (fun _ => Set.univ)
      ((A.absorbTab F tab).toTPKindAlg.wsG C₁ (A.logS F tab N))
      ((A.absorbTab F tab).toTPKindAlg.fullCircBoth C₁) 0
      ((A.absorbTab F tab).toTPKindAlg.advIn C₁ (A.logS F tab N 0))
      ((A.absorbTab F tab).toTPKindAlg.advIn C₁ (A.logS F tab N A.slots)) :=
  (KindAlg.valid_fullCircBoth_ws (A.logS F tab N) (A.absorbTab F tab).stepsTP_toTPKindAlg
    (fun j _ _ _ h hx => logS_succ hA N rfl h hx)
    (fun _ hk _ _ _ h hx => logS_post hA N hk h hx)).mono_right
    fun _ hv => ⟨fun j hj => absurd j.isLt (not_lt.2 hj), hv.2⟩

end AdaptiveIAlg

/-! ### Supports of the simulated run from supports of the steps -/

namespace QueryAlg

open GordieHowe.QROM

variable {m t : ℕ} {I J B O : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (e : BitStr I J ≃ B) (A : QueryAlg (Bits m) (BitStr I J) t O)

/-- **The simulated run has its work register in sets that the steps carry** (as
`QueryCount.supported_simStage_G`, with only the supports): `step 0` sends the initial state into
`S 0` and `step (k + 1)` sends `S k` into `S (k + 1)`. -/
theorem supported_simStage_of (S : ℕ → Set A.W)
    (h0 : Supported {r | r.1 ∈ S 0} ((A.toOracleAlg ∅).stepAt () 0 A.init))
    (hS : ∀ k < t, ∀ v, Supported {r | r.1 ∈ S k} v →
      Supported {r | r.1 ∈ S (k + 1)} ((A.toOracleAlg ∅).stepAt () (k + 1) v))
    {k : ℕ} (hk : k ≤ t) : Supported (workSet A.W t (S k)) (simStage e A k) := by
  induction k with
  | zero =>
    rintro ⟨r, s⟩ hr
    change simStep A 0 (simInit e A) (r, s) = 0
    rw [simStep, controlled_apply]
    by_cases hs : s = dbSlots e t (∅ : DB (Bits m) B)
    · have : (WithLp.toLp 2 fun i' => simInit e A (i', s) :
          QState (QueryReg A.W 1 (Bits m) (BitStr I J))) = A.init := by
        ext i'
        simp [simInit, hs]
      rw [this]
      exact h0 r hr
    · have : (WithLp.toLp 2 fun i' => simInit e A (i', s) :
          QState (QueryReg A.W 1 (Bits m) (BitStr I J))) = 0 := by
        ext i'
        simp [simInit, hs]
      rw [this, map_zero]
      rfl
  | succ k ih =>
    rw [GordieHowe.QROM.simStage_succ]
    exact supported_controlled_workSet (hS k (by omega))
      (supported_simQuery_workSet e (ih (by omega)))

end QueryAlg

/-! ### Supports of the instance's steps -/

namespace ReqQueryAlg

variable {X Y Req Resp O : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  [DecidableEq Req] [Fintype Req] [Fintype Resp] [DecidableEq Resp] {t : ℕ}
  (G : ReqQueryAlg X Y Req Resp t O) (a : ℕ → Req → Option Resp)
  (WS : Set Req → ℕ → Set G.W) (nd : LogReg Req (t + 1) → Set Req)

/-- The logs filled exactly below `k` (as `LogsAt`). -/
def FilledTo (k : ℕ) (lg : LogReg Req (t + 1)) : Prop :=
  ∀ j : Fin (t + 1), ((j : ℕ) < k ↔ (lg j).isSome)

omit [Fintype Req] in
theorem FilledTo.eq_none {k : Fin (t + 1)} {lg : LogReg Req (t + 1)} (h : FilledTo k lg) :
    lg k = none := by
  have := (h k).not.1 (lt_irrefl _)
  simpa using this

omit [Fintype Req] in
theorem filledTo_update {k : ℕ} (hk : k < t + 1) {lg : LogReg Req (t + 1)} (h : FilledTo k lg)
    (r : Req) : FilledTo (k + 1) (Function.update lg ⟨k, hk⟩ (some r)) := by
  intro j
  by_cases hj : j = ⟨k, hk⟩
  · subst hj
    simp
  · rw [Function.update_of_ne hj, ← h j]
    have : (j : ℕ) ≠ k := fun h' => hj (Fin.ext h')
    omega

theorem instStep_eq (k : Fin (t + 1)) (v : QState (QueryReg (G.W × LogReg Req (t + 1)) 1 X Y)) :
    G.instStep a k v = relabel G.logSplit.symm (controlled (fun _ => G.step k)
      (relabel G.logSplit (permOp ((G.reqPerm a k).prodCongr (Equiv.refl _)) v))) :=
  rfl

end ReqQueryAlg

/-! ### Supports of the instance's simulated run -/

namespace ReqQueryAlg

open GordieHowe.QROM

variable {m t : ℕ} {I J B Req Resp O : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (e : BitStr I J ≃ B) (G : ReqQueryAlg (Bits m) (BitStr I J) Req Resp t O)
  (a : ℕ → Req → Option Resp) (WS : Set Req → ℕ → Set G.W) (nd : LogReg Req (t + 1) → Set Req)

end ReqQueryAlg

/-! ### The steps of the expanded adversary -/

namespace ExpandAdvSupp

open GordieHowe.QROM GordieHowe.QROM.ExpandAdv

variable {X Y B C : Type} [Fintype X] [DecidableEq X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddCommGroup Y] (e : Y ≃ B) (E : Expansion X B C) (k : ℕ) {W : Type} [Fintype W]
  [DecidableEq W] (o : W → C)

/-- **The classical steps of the expansion keep `𝒜`'s work register.** -/
theorem expPerm_fst (j : ℕ) (b : ExpBasis (X := X) (Y := Y) k W) :
    (expPerm e E k o j b).1.1 = b.1.1 := by
  cases j with
  | zero => rfl
  | succ j =>
    simp only [expPerm, Equiv.trans_apply]
    unfold recordPerm
    split <;> rfl

/-- **A lifted unitary keeps the supports of `𝒜`'s work register as the unitary does.** -/
theorem supported_lift {S S' : Set W}
    {U : QState (QueryReg W 1 X Y) ≃ₗᵢ[ℂ] QState (QueryReg W 1 X Y)}
    (hU : ∀ v, Supported {r | r.1 ∈ S} v → Supported {r | r.1 ∈ S'} (U v))
    {x : QState (ExpBasis (X := X) (Y := Y) k W)} (hx : Supported {b | b.1.1 ∈ S} x) :
    Supported {b | b.1.1 ∈ S'} (lift k U x) := by
  intro b hb
  simp only [lift, LinearIsometryEquiv.trans_apply, relabel_symm]
  rw [relabel_apply, Equiv.symm_symm]
  change controlled (fun _ => U) (relabel (registerSplit k W) x)
    ((registerSplit k W b).1, (registerSplit k W b).2) = 0
  rw [controlled_apply]
  refine hU _ (fun r hr => ?_) _ hb
  rw [relabel_apply]
  exact hx _ hr

theorem supported_permOp_expPerm {S : Set W} (j : ℕ) {x : QState (ExpBasis (X := X) (Y := Y) k W)}
    (hx : Supported {b | b.1.1 ∈ S} x) :
    Supported {b | b.1.1 ∈ S} (permOp (expPerm e E k o j) x) :=
  hx.permOp fun b hb => by
    change (expPerm e E k o j b).1.1 ∈ S
    rw [expPerm_fst]
    exact hb

/-- **The steps of the expanded adversary carry the supports of `𝒜`'s work register** that `𝒜`'s
steps carry (`hstep`), the supports after `𝒜`'s last step growing (`hmono`). -/
theorem expandAdv_step_supp {t : ℕ} (𝒜 : QueryAlg X Y t C) (S : ℕ → Set 𝒜.W)
    (hstep : ∀ i, i + 1 ≤ t → ∀ u, Supported {r | r.1 ∈ S i} u →
      Supported {r | r.1 ∈ S (i + 1)} ((𝒜.toOracleAlg ∅).stepAt () (i + 1) u))
    (hmono : ∀ i, t ≤ i → S i ⊆ S (i + 1)) {i : ℕ} (hi : i + 1 < t + k + 1)
    {v : QState (ExpBasis (X := X) (Y := Y) k 𝒜.W)}
    (hv : Supported {b : ExpBasis (X := X) (Y := Y) k 𝒜.W | b.1.1 ∈ S i} v) :
    Supported {b : ExpBasis (X := X) (Y := Y) k 𝒜.W | b.1.1 ∈ S (i + 1)}
      ((expandAdv e E k 𝒜).step ⟨i + 1, hi⟩ v) := by
  change Supported _ (expStep e E k 𝒜 𝒜.out (i + 1) v)
  unfold expStep
  split_ifs with h1 h2
  · exact supported_lift k (hstep i (by omega)) hv
  · have e1 : (𝒜.toOracleAlg ∅).stepAt () t = (𝒜.toOracleAlg ∅).stepAt () (i + 1) := by
      rw [show i + 1 = t by omega]
    rw [LinearIsometryEquiv.trans_apply, e1]
    exact supported_permOp_expPerm e E k _ 0 (supported_lift k (hstep i (by omega)) hv)
  · exact supported_permOp_expPerm e E k _ _ (hv.mono fun b hb => hmono i (by omega) hb)

theorem supported_embed {S : Set W} {v : QState (QueryReg W 1 X Y)}
    (hv : Supported {r | r.1 ∈ S} v) :
    Supported {b : ExpBasis (X := X) (Y := Y) k W | b.1.1 ∈ S} (ExpandAdv.embed k v) := by
  intro b hb
  rw [ExpandAdv.embed, relabel_apply, Equiv.symm_symm, tensorKet_apply]
  rw [hv _ hb, zero_mul]

/-- **The first step of the expanded adversary carries the supports of `𝒜`'s work register** that
`𝒜`'s first step carries. -/
theorem expandAdv_step0_supp {t : ℕ} (𝒜 : QueryAlg X Y t C) {S₀ S₁ : Set 𝒜.W}
    (h : ∀ u, Supported {r | r.1 ∈ S₀} u →
      Supported {r | r.1 ∈ S₁} ((𝒜.toOracleAlg ∅).stepAt () 0 u))
    {v : QState (ExpBasis (X := X) (Y := Y) k 𝒜.W)}
    (hv : Supported {b : ExpBasis (X := X) (Y := Y) k 𝒜.W | b.1.1 ∈ S₀} v) :
    Supported {b : ExpBasis (X := X) (Y := Y) k 𝒜.W | b.1.1 ∈ S₁}
      ((expandAdv e E k 𝒜).step 0 v) := by
  change Supported _ (expStep e E k 𝒜 𝒜.out 0 v)
  unfold expStep
  split_ifs with h1 h2
  · exact supported_lift k h hv
  · subst h2
    rw [LinearIsometryEquiv.trans_apply]
    exact supported_permOp_expPerm e E k _ 0 (supported_lift k h hv)
  · omega

end ExpandAdvSupp

/-! ### The supports of the bridge's run -/

section Bridge

open GordieHowe.QROM GordieHowe.QROM.ExpandAdv

variable {m : ℕ} {I J B : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Req Resp Req₁ Resp₁ Req₂ Resp₂ O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp]
  [DecidableEq Resp] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [Inhabited Req₁]
  (e : BitStr I J ≃ B) {shA : AlgShape (Bits m) (BitStr I J) Req Resp} (A : AdaptiveIAlg shA O)
  (C₁ : Challenger (Bits m) (BitStr I J) Req₁ Resp₁)
  (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂) (d₂ : Req₂)
  (E : Expansion (Bits m) B (ExtReg A C₁ Req₂ Resp₂)) (kq : ℕ) (d₀ : ExtReg A C₁ Req₂ Resp₂)

omit [Inhabited Req₁] in
/-- The query registers of a composition are nonempty. -/
instance composeBothOut_nonempty {Req' Resp' O' : Type} [Fintype Req'] [DecidableEq Req']
    [Fintype Resp'] [DecidableEq Resp'] {ksT : KindShape (Bits m) (BitStr I J) Req' Resp'} (T : KindAlg ksT O')
    (C : Challenger (Bits m) (BitStr I J) Req' Resp') :
    Nonempty (QueryReg (KindAlg.composeBothOut C T id).V 1 (Bits m) (BitStr I J)) :=
  (KindAlg.composeBothOut C T id).init.nonempty

-- TODO(unbundle-M4): instance at a concrete shape because `composeBothOut_nonempty` over a free
-- `ksT` does not fire; state over {W} {n} (R6) or register the instance on M1b's named type
omit [Inhabited Req₁] in
/-- The query registers of the composition of the absorbed adversary are nonempty
(`composeBothOut_nonempty` at its shape, whose workspace reduces to a named type). -/
instance absorbTab_composeBothOut_nonempty :
    Nonempty (QueryReg ((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).V 1 (Bits m)
      (BitStr I J)) :=
  composeBothOut_nonempty _ _

/-- **The supports of the run of the composition after step `k`** (proof-internal), for the
requests `N`: the composed registers in the certificate's support after segment `k`
(`valid_logS`), the halting flag down, the ancilla clean from step `k + 1`. -/
def cohSet (N : Set Req₂) (k : ℕ) :
    Set ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut
      (extOut A C₁ F d₀ (tab₀ A))).W) :=
  {c | c.1.1.1 ∈ ReprogrammedCircuit.segOut
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.wsG C₁ (A.logS F (tab₀ A) N))
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.advIn C₁ (A.logS F (tab₀ A) N A.slots)) 0
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.fullCircBoth C₁).queries k ∧
    c.1.2 = false ∧
    (k < ((A.absorbTab F (tab₀ A)).toTPKindAlg.fullCircBoth C₁).queries →
      MixedAlg.Clean (k + 1) c.2)}

/-- **The supports of the bridge's work register after step `k`** (proof-internal): the run of
the composition in `cohSet N k`. -/
def wSet (N : Set Req₂) (k : ℕ) : Set (bridgeAlg e A C₁ F d₂ E kq d₀).W :=
  {w | w.1 ∈ cohSet A C₁ F d₀ N k}

/-- The absorbed copy of the logs, read from the register of the run of the composition. -/
noncomputable abbrev cohLogs (c : (((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut
    (extOut A C₁ F d₀ (tab₀ A))).W) : LogReg Req A.slots :=
  c.1.1.1.adv.workspace.1.1.logs

/-- **`cohSet` reads the absorbed logs, the halting flag and the ancilla**, the requests through
the logged ones. -/
theorem cohSet_congr {N N' : Set Req₂} {k : ℕ} {c c'} (hc : c ∈ cohSet A C₁ F d₀ N k)
    (hl : cohLogs A C₁ F d₀ c' = cohLogs A C₁ F d₀ c) (hf : c'.1.2 = c.1.2) (ha : c'.2 = c.2)
    (hE : ∀ x ∈ N', ∃ j r, cohLogs A C₁ F d₀ c' j = some r ∧
      F.outer (A.reqCount (cohLogs A C₁ F d₀ c') j) r = some x) :
    c' ∈ cohSet A C₁ F d₀ N' k := by
  obtain ⟨h1, h2, h3⟩ := hc
  refine ⟨?_, by rw [hf]; exact h2, by rw [ha]; exact h3⟩
  unfold ReprogrammedCircuit.segOut KindAlg.wsG at h1 ⊢
  split_ifs at h1 ⊢ <;>
    exact ⟨fun j hj => (congrFun hl j).trans (h1.1 j hj), hE⟩

/-- **Writing a reply of the bridge keeps the absorbed logs, the halting flag and the
ancilla.** -/
theorem bridgeAlg_write_spec (k : Fin ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth
      + kq) + 1)) (x : Option Resp₂) (w : (bridgeAlg e A C₁ F d₂ E kq d₀).W) :
    cohLogs A C₁ F d₀ ((bridgeAlg e A C₁ F d₂ E kq d₀).write k x w).1 = cohLogs A C₁ F d₀ w.1 ∧
      ((bridgeAlg e A C₁ F d₂ E kq d₀).write k x w).1.1.2 = w.1.1.2 ∧
      ((bridgeAlg e A C₁ F d₂ E kq d₀).write k x w).1.2 = w.1.2 := by
  rcases h : answerSlot A C₁ k with _ | j
  · have e1 : (bridgeAlg e A C₁ F d₂ E kq d₀).write k x = Equiv.refl _ := by
      change (match answerSlot A C₁ k with
        | none => Equiv.refl _
        | some j => liftAbs e A C₁ F E kq d₀ (answerDelta A F j x)) = _
      rw [h]
    rw [e1]
    exact ⟨rfl, rfl, rfl⟩
  · have e1 : (bridgeAlg e A C₁ F d₂ E kq d₀).write k x =
        liftAbs e A C₁ F E kq d₀ (answerDelta A F j x) := by
      change (match answerSlot A C₁ k with
        | none => Equiv.refl _
        | some j => liftAbs e A C₁ F E kq d₀ (answerDelta A F j x)) = _
      rw [h]
    rw [e1]
    exact ⟨answerDelta_logs A F j x _, rfl, rfl⟩

/-- **The initial state of the adversary absorbed with a table has blank absorbed logs.** -/
theorem init_logs_none {d d' : DReg (A.absorbTab F (tab₀ A)).toTPKindAlg.W A.width (Bits m)
      (BitStr I J) Req₁ Resp₁}
    (h : (A.absorbTab F (tab₀ A)).toTPKindAlg.init.mat d d' ≠ 0) (j : Fin A.slots) :
    d.workspace.1.1.logs j = none := by
  rw [AdaptiveIAlg.toTPKindAlg_init, AdaptiveIAlg.toKindAlg_init, AdaptiveIAlg.withConst_init,
    AdaptiveIAlg.absorb_init] at h
  erw [MState.reindex_tensorKet_mat, MState.reindex_tensorKet_mat, MState.reindex_tensorKet_mat,
    embed_embed, embed_embed] at h
  obtain ⟨y, y₂, rfl, -, -⟩ := embed_ne_zero_exists h
  rfl

/-- **The initial state of the composition has blank absorbed logs.** -/
theorem initSys_logs [Nonempty (Bits m)] (p : QueryReg ((A.absorbTab F (tab₀ A)).toTPKindAlg.CW C₁) 1
      (Bits m) (BitStr I J))
    (hp : ((A.absorbTab F (tab₀ A)).toTPKindAlg.initSys C₁).mat p p ≠ 0) :
    p.1 ∈ (A.absorbTab F (tab₀ A)).toTPKindAlg.advIn C₁ (A.logS F (tab₀ A) ∅ 0) := by
  change (∑ ω, (_ : ℂ) • (MState.reindex ((A.absorbTab F (tab₀ A)).toTPKindAlg.advSplit C₁)
    (((A.absorbTab F (tab₀ A)).toTPKindAlg.init).tensorKet _)).mat) p p ≠ 0 at hp
  rw [Matrix.sum_apply] at hp
  obtain ⟨ω, -, hω⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp
  rw [Matrix.smul_apply, smul_eq_mul] at hω
  have h2 := right_ne_zero_of_mul hω
  rw [MState.reindex_tensorKet_mat] at h2
  obtain ⟨d, d', hd, -, hdd⟩ := embed_ne_zero_exists h2
  subst hd
  exact ⟨fun j _ => init_logs_none A F hdd j, fun x hx => absurd hx (Set.notMem_empty x)⟩

variable [Nonempty (Bits m)]

/-- **A step of the run of the composition carries `cohSet N k` to `cohSet N (k + 1)`.** -/
theorem cohStep_supp (hA : A.TracePreserving) (N : Set Req₂) {k : ℕ}
    (hk : k + 1 ≤ ((A.absorbTab F (tab₀ A)).toTPKindAlg.fullCircBoth C₁).queries)
    (u : QState (QueryReg ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut
      (extOut A C₁ F d₀ (tab₀ A))).W) 1 (Bits m) (BitStr I J)))
    (hu : Supported {r | r.1 ∈ cohSet A C₁ F d₀ N k} u) :
    Supported {r | r.1 ∈ cohSet A C₁ F d₀ N (k + 1)}
      (((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut
        (extOut A C₁ F d₀ (tab₀ A))).toOracleAlg ∅).stepAt () (k + 1) u) := by
  have hv := A.valid_logS (F := F) (tab := tab₀ A) hA N C₁
  refine ReprogrammedCircuit.stepAt_compiled_supp _ _ _ _ _ hv hk ?_
  refine fun r hr => hu r fun h => hr ?_
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, h2, h3 (by omega)⟩
  have e1 : ReprogrammedCircuit.segOut ((A.absorbTab F (tab₀ A)).toTPKindAlg.wsG C₁ (A.logS F (tab₀ A) N))
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.advIn C₁ (A.logS F (tab₀ A) N A.slots)) 0
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.fullCircBoth C₁).queries k =
      (A.absorbTab F (tab₀ A)).toTPKindAlg.wsG C₁ (A.logS F (tab₀ A) N) (0 + k) := by
    unfold ReprogrammedCircuit.segOut
    rw [if_pos (by omega)]
  rw [e1] at h1
  exact h1

theorem cohSet_mono_of_le (N : Set Req₂) {k : ℕ}
    (hk : ((A.absorbTab F (tab₀ A)).toTPKindAlg.fullCircBoth C₁).queries ≤ k) :
    cohSet A C₁ F d₀ N k ⊆ cohSet A C₁ F d₀ N (k + 1) := by
  rintro c ⟨h1, h2, -⟩
  refine ⟨?_, h2, fun h => absurd h (by omega)⟩
  unfold ReprogrammedCircuit.segOut at h1 ⊢
  rw [if_neg (by omega)] at h1
  rw [if_neg (by omega)]
  exact h1

/-- **A step of the bridge carries `wSet N k` to `wSet N (k + 1)`**: the run of the composition,
lifted, then the classical steps of the expansion, which keep the composition's registers. -/
theorem bridgeStep_supp (hA : A.TracePreserving) (N : Set Req₂) {k : ℕ}
    (hk : k + 1 < (((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth + kq) + 1)
    (v : QState (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)))
    (hv : Supported {r | r.1 ∈ wSet e A C₁ F d₂ E kq d₀ N k} v) :
    Supported {r | r.1 ∈ wSet e A C₁ F d₂ E kq d₀ N (k + 1)}
      ((bridgeAlg e A C₁ F d₂ E kq d₀).step ⟨k + 1, hk⟩ v) := by
  have hD : ((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).depth =
      ((A.absorbTab F (tab₀ A)).toTPKindAlg.fullCircBoth C₁).queries :=
    ReprogrammedCircuit.depth_compiledAlg _ _ _ _
  exact ExpandAdvSupp.expandAdv_step_supp e E kq
    ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut
      (extOut A C₁ F d₀ (tab₀ A)))) (cohSet A C₁ F d₀ N)
    (fun i hi u hu => cohStep_supp A C₁ F d₀ hA N (by omega) u hu)
    (fun i hi => cohSet_mono_of_le A C₁ F d₀ N (by omega)) hk hv

/-- **The supports of the run of the composition at the start** (proof-internal): the composed
registers with blank absorbed logs, the halting flag down, the ancilla clean. -/
def cohInit : Set ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut
    (extOut A C₁ F d₀ (tab₀ A))).W) :=
  {c | c.1.1.1 ∈ (A.absorbTab F (tab₀ A)).toTPKindAlg.advIn C₁ (A.logS F (tab₀ A) ∅ 0) ∧
    c.1.2 = false ∧ MixedAlg.Clean 0 c.2}

theorem bridgeAlg_init_eq :
    (bridgeAlg e A C₁ F d₂ E kq d₀).init = ExpandAdv.embed kq
      ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut
      (extOut A C₁ F d₀ (tab₀ A)))).init := rfl

theorem cohInit_supp :
    Supported {r : QueryReg ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut
      (extOut A C₁ F d₀ (tab₀ A)))).W 1 (Bits m) (BitStr I J) | r.1 ∈ cohInit A C₁ F d₀}
      ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut
      (extOut A C₁ F d₀ (tab₀ A)))).init :=
  (GordieHowe.QROM.compiled_init_props (initSys_logs A C₁ F)).1.mono
      fun _ hr => ⟨hr.2.2.2, hr.2.1, hr.2.2.1⟩

/-- The bridge's work register at the start (proof-internal): the run of the composition in
`cohInit`. -/
def initW : Set (bridgeAlg e A C₁ F d₂ E kq d₀).W :=
  {w | w.1 ∈ cohInit A C₁ F d₀}

theorem bridge_init_supp :
    Supported {r | r.1 ∈ initW e A C₁ F d₂ E kq d₀} (bridgeAlg e A C₁ F d₂ E kq d₀).init := by
  intro r hr
  rw [bridgeAlg_init_eq, ExpandAdv.embed]
  erw [relabel_apply, Equiv.symm_symm, tensorKet_apply]
  erw [cohInit_supp A C₁ F d₀ ((r.1.1, r.2)) hr, zero_mul]

theorem mem_cohInit {c} : c ∈ cohInit A C₁ F d₀ ↔
    (∀ j, cohLogs A C₁ F d₀ c j = none) ∧ c.1.2 = false ∧ MixedAlg.Clean 0 c.2 := by
  constructor
  · rintro ⟨⟨hb, -⟩, h2, h3⟩
    exact ⟨fun j => hb j (Nat.zero_le _), h2, h3⟩
  · rintro ⟨hb, h2, h3⟩
    exact ⟨⟨fun j _ => hb j, fun x hx => absurd hx (Set.notMem_empty x)⟩, h2, h3⟩

omit [Inhabited Req₁] in
/-- `ReprogrammedCircuit.stepAt_compiled_supp` at the composition `composeBothOut`. -/
theorem stepAt_composeBothOut_supp {Req' Resp' O' O'' : Type} [Fintype Req'] [DecidableEq Req']
    [Fintype Resp'] [DecidableEq Resp'] {ksT : KindShape (Bits m) (BitStr I J) Req' Resp'}
    (T : KindAlg ksT O') (C : Challenger (Bits m) (BitStr I J) Req' Resp')
    (g : Option (T.CW C) → O'')
    [Nonempty (QueryReg (T.CW C × (Bits m × BitStr I J × Bool)) 1 (Bits m) (BitStr I J) × Bool)]
    {Cs G : ℕ → Set (T.CW C)} {P Q : Set (T.CW C)}
    (hv : ReprogrammedCircuit.Valid Cs G (T.fullCircBoth C) 0 P Q) {k : ℕ}
    (hk : k ≤ (T.fullCircBoth C).queries)
    {v : QState (QueryReg ((T.composeBothOut C id).toQueryAlgCoh.mapOut g).W 1 (Bits m) (BitStr I J))}
    (hS : Supported {r | r.1.1.1.1 ∈ ReprogrammedCircuit.segIn G P 0 k ∧ r.1.1.2 = false ∧
      MixedAlg.Clean k r.1.2} v) :
    Supported {r | r.1.1.1.1 ∈ ReprogrammedCircuit.segOut G Q 0 (T.fullCircBoth C).queries k ∧
      r.1.1.2 = false ∧ (k < (T.fullCircBoth C).queries → MixedAlg.Clean (k + 1) r.1.2)}
      ((((T.composeBothOut C id).toQueryAlgCoh.mapOut g).toOracleAlg ∅).stepAt () k v) :=
  ReprogrammedCircuit.stepAt_compiled_supp _ _ _ _ _ hv hk hS

theorem cohInit_step0 (hA : A.TracePreserving)
    (u : QState (QueryReg ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut
      (extOut A C₁ F d₀ (tab₀ A))).W) 1 (Bits m) (BitStr I J)))
    (hu : Supported {r | r.1 ∈ cohInit A C₁ F d₀} u) :
    Supported {r | r.1 ∈ cohSet A C₁ F d₀ ∅ 0}
      (((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut
        (extOut A C₁ F d₀ (tab₀ A))).toOracleAlg ∅).stepAt () 0 u) := by
  have hv := A.valid_logS (F := F) (tab := tab₀ A) hA ∅ C₁
  refine stepAt_composeBothOut_supp _ _ _ hv (Nat.zero_le _) ?_
  refine fun r hr => hu r fun h => hr ?_
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem bridge_hstep0 (hA : A.TracePreserving)
    (v : QState (QueryReg (bridgeAlg e A C₁ F d₂ E kq d₀).W 1 (Bits m) (BitStr I J)))
    (hv : Supported {r | r.1 ∈ initW e A C₁ F d₂ E kq d₀} v) :
    Supported {r | r.1 ∈ wSet e A C₁ F d₂ E kq d₀ ∅ 0} ((bridgeAlg e A C₁ F d₂ E kq d₀).step 0 v) := by
  have h := ExpandAdvSupp.expandAdv_step0_supp e E kq
    ((((A.absorbTab F (tab₀ A)).toTPKindAlg.composeBothOut C₁ id).toQueryAlgCoh.mapOut
      (extOut A C₁ F d₀ (tab₀ A)))) (cohInit_step0 A C₁ F d₀ hA) hv
  exact h

end Bridge

end GordieHowe.Quantum


