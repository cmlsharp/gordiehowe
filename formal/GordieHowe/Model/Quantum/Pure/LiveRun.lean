-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.Game

@[expose] public section

/-!
# Two distinguishers that agree on their live branches

Two distinguishers with the same kind, initial state and accepting set, whose accepting set lies
in a set `live` of workspaces, accept with the same probability on every set of logs when each
step keeps the branches outside `live` outside it and the two steps agree on the live part of their
images of live vectors. Both conditions need only hold on the vectors supported in a family of sets
`C k` that the runs stay in (in the intended use, the clean ancillas of a dilation).

- `mask_mask_of_subset`, `Supported.mask`, `mask_eq_zero_of_supported`: masks and supports.
- `mask_map_eq_of_live`: one step of the comparison on an arbitrary basis.
- `Distinguisher.wsSet`: the game basis states whose workspace lies in a set.
- **`Distinguisher.acceptProbOnAt_eq_of_live`**: the two distinguishers accept with the same
  probability on every set of logs.
-/

namespace GordieHowe.Quantum

section Live

variable {ι : Type*} [Fintype ι]

/-- A mask onto a subset of `B` after the mask onto `B` is the mask onto the subset. -/
theorem mask_mask_of_subset {A B : Set ι} (h : A ⊆ B) (v : QState ι) :
    mask A (mask B v) = mask A v := by
  ext i
  by_cases hA : i ∈ A
  · rw [mask_apply_of_mem _ hA, mask_apply_of_mem _ hA, mask_apply_of_mem _ (h hA)]
  · rw [mask_apply_of_notMem _ hA, mask_apply_of_notMem _ hA]

/-- The mask onto `S` of a vector supported in `C` is supported in `C ∩ S`. -/
theorem Supported.mask {C : Set ι} {v : QState ι} (hv : Supported C v) (S : Set ι) :
    Supported (C ∩ S) (Quantum.mask S v) := fun i hi => by
  by_cases hS : i ∈ S
  · rw [mask_apply_of_mem _ hS]
    exact hv i fun hC => hi ⟨hC, hS⟩
  · rw [mask_apply_of_notMem _ hS]

/-- The mask onto `S` of a vector supported outside `S` is zero. -/
theorem mask_eq_zero_of_supported {S : Set ι} {v : QState ι} (hv : Supported Sᶜ v) :
    mask S v = 0 := by
  ext i
  by_cases hS : i ∈ S
  · rw [mask_apply_of_mem _ hS, hv i (fun h => h hS)]
    rfl
  · rw [mask_apply_of_notMem _ hS]
    rfl

/-- **One step of the comparison**: if `U` and `U'` keep the vectors in `C` outside `S` outside
`S`, and agree on `S` on the vectors in `C ∩ S`, then on two vectors in `C` that agree on `S` their
images agree on `S`. -/
theorem mask_map_eq_of_live {S C : Set ι} (U U' : QState ι ≃ₗᵢ[ℂ] QState ι)
    (hdead : ∀ w, Supported (C ∩ Sᶜ) w → Supported Sᶜ (U w))
    (hdead' : ∀ w, Supported (C ∩ Sᶜ) w → Supported Sᶜ (U' w))
    (hagree : ∀ w, Supported (C ∩ S) w → mask S (U' w) = mask S (U w)) {v v' : QState ι}
    (hv : Supported C v) (hv' : Supported C v') (hvv : mask S v' = mask S v) :
    mask S (U' v') = mask S (U v) := by
  have hsplit : ∀ (V : QState ι ≃ₗᵢ[ℂ] QState ι) (u : QState ι), Supported C u →
      (∀ w, Supported (C ∩ Sᶜ) w → Supported Sᶜ (V w)) →
      mask S (V u) = mask S (V (mask S u)) := fun V u hu hV => by
    conv_lhs => rw [← mask_add_mask_compl S u]
    rw [map_add, map_add, mask_eq_zero_of_supported (hV _ (hu.mask Sᶜ)), add_zero]
  rw [hsplit U' v' hv' hdead', hsplit U v hv hdead, hvv]
  exact hagree _ (hv.mask S)

end Live

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} [DecidableEq Req] [DecidableEq A]

/-- The game basis states whose workspace lies in `B`. -/
def wsSet (B : Set W) : Set (GameReg W n X Y Req A m) :=
  {r | r.workspace ∈ B}

/-- The distinguisher's basis states whose workspace lies in `B`. -/
def wsSetD (B : Set W) : Set (DReg W n X Y Req A) :=
  {d | d.workspace ∈ B}

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] [DecidableEq Req]
  [DecidableEq A] in
theorem compl_wsSet (B : Set W) :
    (wsSet (n := n) (X := X) (Y := Y) (Req := Req) (A := A) (m := m) B)ᶜ = wsSet Bᶜ :=
  rfl

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] [DecidableEq Req]
  [DecidableEq A] in
theorem inter_wsSet (B B' : Set W) :
    wsSet (n := n) (X := X) (Y := Y) (Req := Req) (A := A) (m := m) B ∩ wsSet B' =
      wsSet (B ∩ B') :=
  rfl

omit [DecidableEq Req] [DecidableEq A] in
/-- A log-controlled unitary whose unitaries map the vectors with workspace in `B` to vectors with
workspace in `B'` does so on the game registers. -/
theorem supported_logControlled_wsSet {B B' : Set W}
    (U : LogReg Req m → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (hU : ∀ lg v, Supported (wsSetD B) v → Supported (wsSetD B') (U lg v))
    {v : QState (GameReg W n X Y Req A m)} (hv : Supported (wsSet B) v) :
    Supported (wsSet B') (logControlled U v) := fun r hr => by
  rw [logControlled_apply]
  exact hU _ _ (fun d hd => hv _ hd) _ hr

omit [DecidableEq Req] [DecidableEq A] in
/-- Two log-controlled unitaries whose unitaries agree on `S` on the vectors with workspace in
`B ∩ S` do so on the game registers. -/
theorem mask_logControlled_wsSet {B S : Set W}
    (U U' : LogReg Req m → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (hU : ∀ lg v, Supported (wsSetD (B ∩ S)) v →
      mask (wsSetD S) (U' lg v) = mask (wsSetD S) (U lg v))
    {v : QState (GameReg W n X Y Req A m)} (hv : Supported (wsSet (B ∩ S)) v) :
    mask (wsSet S) (logControlled U' v) = mask (wsSet S) (logControlled U v) := by
  ext r
  by_cases hr : r ∈ wsSet S
  · rw [mask_apply_of_mem _ hr, mask_apply_of_mem _ hr, logControlled_apply,
      logControlled_apply]
    have h := congrArg (fun u : QState (DReg W n X Y Req A) => u (splitLogs r).1)
      (hU (splitLogs r).2 (WithLp.toLp 2 fun d => v (splitLogs.symm (d, (splitLogs r).2)))
        (fun d hd => by
        change v (splitLogs.symm (d, (splitLogs r).2)) = 0
        exact hv _ hd))
    simp only at h
    rwa [mask_apply_of_mem _ (show (splitLogs r).1 ∈ wsSetD S from hr),
      mask_apply_of_mem _ (show (splitLogs r).1 ∈ wsSetD S from hr)] at h
  · rw [mask_apply_of_notMem _ hr, mask_apply_of_notMem _ hr]

omit [DecidableEq Req] [DecidableEq A] in
/-- A basis permutation that keeps the workspace commutes with the mask onto a set of
workspaces. -/
theorem mask_permOp_wsSet {S : Set W} {π : Equiv.Perm (GameReg W n X Y Req A m)}
    (hπ : ∀ r, (π r).workspace = r.workspace) (v : QState (GameReg W n X Y Req A m)) :
    mask (wsSet S) (permOp π v) = permOp π (mask (wsSet S) v) := by
  ext r
  have hm : π.symm r ∈ wsSet S ↔ r ∈ wsSet S := by
    change (π.symm r).workspace ∈ S ↔ r.workspace ∈ S
    rw [← hπ (π.symm r), Equiv.apply_symm_apply]
  by_cases hr : r ∈ wsSet S
  · rw [mask_apply_of_mem _ hr, permOp_apply, permOp_apply, mask_apply_of_mem _ (hm.2 hr)]
  · rw [mask_apply_of_notMem _ hr, permOp_apply, mask_apply_of_notMem _ (fun h => hr (hm.1 h))]

/-- **Two unitaries related on the live branches** from `C` to `C'`: each maps the vectors with
workspace in `C` to vectors with workspace in `C'`, keeps those outside `live` outside it, and the
two agree on `live` on the vectors with workspace in `C`. -/
structure StepRel (live C C' : Set W)
    (U U' : QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)) : Prop where
  clean : ∀ v, Supported (wsSetD C) v → Supported (wsSetD C') (U v)
  clean' : ∀ v, Supported (wsSetD C) v → Supported (wsSetD C') (U' v)
  dead : ∀ v, Supported (wsSetD (C ∩ liveᶜ)) v → Supported (wsSetD liveᶜ) (U v)
  dead' : ∀ v, Supported (wsSetD (C ∩ liveᶜ)) v → Supported (wsSetD liveᶜ) (U' v)
  agree : ∀ v, Supported (wsSetD C) v →
    mask (wsSetD live) (U' v) = mask (wsSetD live) (U v)

omit [DecidableEq Req] [DecidableEq A] in
/-- The identity is related to itself from `C` to any superset. -/
theorem StepRel.refl {live C C' : Set W} (h : C ⊆ C') :
    StepRel (n := n) (X := X) (Y := Y) (Req := Req) (A := A) live C C'
      (LinearIsometryEquiv.refl ℂ _) (LinearIsometryEquiv.refl ℂ _) where
  clean _ hv d hd := hv d fun h' => hd (h h')
  clean' _ hv d hd := hv d fun h' => hd (h h')
  dead _ hv d hd := hv d fun h' => hd h'.2
  dead' _ hv d hd := hv d fun h' => hd h'.2
  agree _ _ := rfl

/-- **Two distinguishers related on their live branches**: the same kind, initial state and
accepting set, the accepting set within the workspaces `live`, the initial state with workspace in
`C 0`, and the steps `k` related on the live branches from `C k` to `C (k + 1)`. -/
structure LiveRel (D D' : Distinguisher W X Y Req A n m) (live : Set W) (C : ℕ → Set W) :
    Prop where
  kind_eq : D'.kind = D.kind
  init_eq : D'.init = D.init
  accept_eq : D'.accept = D.accept
  accept_live : ∀ d ∈ D.accept, d.workspace ∈ live
  init_clean : Supported (wsSetD (C 0)) D.init
  step : ∀ k, StepRel live (C k) (C (k + 1)) (D.stepAt k) (D'.stepAt k)

variable {Ω : Type*} {St : Type _} [AddGroup Y] {Q : ℕ} [OracleState St X Y]
  (E : Env Ω Req A X Y Q St)

variable {D D' : Distinguisher W X Y Req A n m} {live : Set W} {C : ℕ → Set W}

theorem LiveRel.eventPerm_eq (h : LiveRel D D' live C) (ω : Ω) (k : ℕ) :
    D'.eventPerm E ω k = D.eventPerm E ω k := by
  simp only [eventPerm, h.kind_eq]

/-- **The runs agree on the live branches**: after step `k` both runs have their workspaces in
`C (k + 1)` and agree on `live`. -/
theorem LiveRel.stage (h : LiveRel D D' live C) (ω : Ω) (k : ℕ) :
    Supported (wsSet (C (k + 1))) (D.stage E ω k) ∧
      Supported (wsSet (C (k + 1))) (D'.stage E ω k) ∧
      mask (wsSet live) (D'.stage E ω k) = mask (wsSet live) (D.stage E ω k) := by
  have hstep : ∀ j {v v' : QState (GameReg W n X Y Req A m)}, Supported (wsSet (C j)) v →
      Supported (wsSet (C j)) v' → mask (wsSet live) v' = mask (wsSet live) v →
      Supported (wsSet (C (j + 1))) (D.liftedStep j v) ∧
        Supported (wsSet (C (j + 1))) (D'.liftedStep j v') ∧
        mask (wsSet live) (D'.liftedStep j v') = mask (wsSet live) (D.liftedStep j v) :=
    fun j v v' hv hv' hvv => by
    refine ⟨supported_logControlled_wsSet _ (fun _ u hu => (h.step j).clean u hu) hv,
      supported_logControlled_wsSet _ (fun _ u hu => (h.step j).clean' u hu) hv', ?_⟩
    refine mask_map_eq_of_live (C := wsSet (C j)) _ _ (fun w hw => ?_) (fun w hw => ?_)
      (fun w hw => ?_) hv hv' hvv
    · exact supported_logControlled_wsSet _ (fun _ u hu => (h.step j).dead u hu) hw
    · exact supported_logControlled_wsSet _ (fun _ u hu => (h.step j).dead' u hu) hw
    · exact mask_logControlled_wsSet (B := C j) _ _
        (fun _ u hu => (h.step j).agree u fun d hd => hu d fun h' => hd h'.1) hw
  have hinit : D'.gameInit = D.gameInit := by
    simp only [gameInit, h.init_eq]
  have hinitS : Supported (wsSet (C 0)) D.gameInit := fun r hr => by
    simp only [gameInit]
    split_ifs
    · exact h.init_clean _ hr
    · rfl
  induction k with
  | zero =>
    simp only [Distinguisher.stage, hybrid_zero]
    rw [hinit]
    exact hstep 0 hinitS hinitS rfl
  | succ k ih =>
    rw [stage_succ, stage_succ, LiveRel.eventPerm_eq E h ω k]
    have hw : ∀ r, (D.eventPerm E ω k r).workspace = r.workspace :=
      D.workspace_eventPerm E ω k
    have hπ : ∀ r ∈ wsSet (C (k + 1)), D.eventPerm E ω k r ∈ wsSet (C (k + 1)) := fun r hr => by
      show (D.eventPerm E ω k r).workspace ∈ C (k + 1)
      rw [hw]
      exact hr
    refine hstep (k + 1) (ih.1.permOp hπ) (ih.2.1.permOp hπ) ?_
    · rw [mask_permOp_wsSet hw, mask_permOp_wsSet hw, ih.2.2]

/-- **Two distinguishers related on their live branches accept with the same probability on
every set of logs**, for a final unitary that keeps the branches outside `live` outside it. -/
theorem LiveRel.acceptProbOnAt_eq (h : LiveRel D D' live C)
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (hpost : ∀ H v, Supported (wsSetD liveᶜ) v → Supported (wsSetD liveᶜ) (post H v))
    (L : Set (LogReg Req m)) (ω : Ω) :
    D'.acceptProbOnAt E post L ω = D.acceptProbOnAt E post L ω := by
  obtain ⟨-, -, hm⟩ := h.stage E ω m
  have hfin : mask (wsSet live) (D'.final E post ω) = mask (wsSet live) (D.final E post ω) := by
    refine mask_map_eq_of_live (C := Set.univ) _ _ (fun w hw => ?_) (fun w hw => ?_)
      (fun w _ => rfl) (fun _ h => absurd trivial h) (fun _ h => absurd trivial h) hm
    · exact supported_logControlled_wsSet _ (fun lg u hu => hpost _ u hu)
        (fun r hr => hw r fun h' => hr h'.2)
    · exact supported_logControlled_wsSet _ (fun lg u hu => hpost _ u hu)
        (fun r hr => hw r fun h' => hr h'.2)
  have hsub : D.gameAccept ∩ logsIn L ⊆ wsSet (n := n) (X := X) (Y := Y) (m := m) live :=
    fun r hr => h.accept_live _ hr.1
  have hacc : D'.gameAccept = D.gameAccept := by
    simp only [gameAccept, h.accept_eq]
  rw [acceptProbOnAt, acceptProbOnAt, hacc, prob, prob, ← mask_mask_of_subset hsub,
    ← mask_mask_of_subset hsub (D.final E post ω), hfin]

end Distinguisher

end GordieHowe.Quantum
