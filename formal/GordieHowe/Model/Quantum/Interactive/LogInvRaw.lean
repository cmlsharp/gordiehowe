-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.MultiRelayLogs
public import GordieHowe.Model.Quantum.Interactive.SplitRestrict
public import GordieHowe.Model.Quantum.Interactive.ThenProgOut
public import GordieHowe.Model.Quantum.Interactive.BaseShiftRestrict

@[expose] public section

/-!
# Sets of workspaces and logs carried by an adversary's own steps

`AdaptiveIAlg.LogInv` (`GordieHowe/Model/Quantum/Interactive/ReqBridgeSlots.lean`) asks for sets
of workspaces, request registers and absorbed logs carried by the steps of the adversary absorbed
with a table. `AdaptiveIAlg.LogInvRaw` asks the same of the adversary's own Kraus operators, the
logs updated as the absorption updates them; for a trace-preserving adversary it implies
`LogInv` for every relay and table
(`LogInvRaw.logInv`, through `tp_absorbTab_rel` and `tp_absorbTab_init_rel`), and it carries over
to the adversary at a fixed base component (`LogInvRaw.restrictAt`) and to the adversary followed
by a classical program (`LogInvRaw.thenProgWith`), along the projection of the workspace.

- `AdaptiveIAlg.tp_absorbTab_init_rel`: a nonzero entry of the initial state of the absorbed
  trace-preserving form is one of the adversary's initial state, with blank absorbed logs.
- `AdaptiveIAlg.LogInvRaw`, `AdaptiveIAlg.LogInvRaw.logInv`.
- `AdaptiveIAlg.LogInvRaw.restrictAt`, `AdaptiveIAlg.LogInvRaw.thenProgWith` (with
  `liftProg_op_ne_zero`, `embedIdx_op_ne_zero`, `ofPerm_op_ne_zero`, `startPerm_keeps`,
  `progPerm_keeps`).
- `AdaptiveIAlg.relayFull_step_raw`, `AdaptiveIAlg.relayFull_init_raw`,
  `AdaptiveIAlg.relayAdv_logInvRaw`, `AdaptiveIAlg.relayAdv_logsRaw_le`: the relayed adversary's
  bookkeeping on its own steps (`relayFull_step`, `relayFull_init`).
- `AdaptiveIAlg.logInv_restrictAt_thenProgWith_relayAdv`: the relayed adversary followed by a
  program, at the zero base component, logs at most `K · Q` requests satisfying `p`, on sets that
  writing the part of `restrictBaseW` keeps.
-/

open Matrix
open scoped BigOperators

namespace GordieHowe.Quantum

open GordieHowe.QROM

namespace AdaptiveIAlg

section Raw

variable {X Y Req Resp O Req₁ Resp₁ Req₂ Resp₂ : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂)

/-- **A nonzero entry of the initial state of the trace-preserving form of the adversary absorbed
with a table** is one of the adversary's initial state on its workspace and request register,
with blank absorbed logs. -/
theorem tp_absorbTab_init_rel (tab : A.OuterTab Req₂ Resp₂)
    {d d' : DReg (A.absorbTab F tab).toTPKindAlg.W A.width X Y Req₁ Resp₁}
    (h : ((A.absorbTab F tab).toTPKindAlg.init).mat d d' ≠ 0) :
    ∃ c c' : DReg A.W A.width X Y Req Resp, A.init.mat c c' ≠ 0 ∧
      c.1.1 = d.workspace.1.1.work ∧ c.1.2.1 = d.workspace.1.1.request ∧
      ∀ j, d.workspace.1.1.logs j = none := by
  rw [AdaptiveIAlg.toTPKindAlg_init, AdaptiveIAlg.toKindAlg_init, AdaptiveIAlg.withConst_init,
    AdaptiveIAlg.absorb_init] at h
  erw [MState.reindex_tensorKet_mat, MState.reindex_tensorKet_mat, MState.reindex_tensorKet_mat,
    embed_embed, embed_embed] at h
  obtain ⟨c, c', rfl, -, hc⟩ := embed_ne_zero_exists h
  exact ⟨c, c', hc, rfl, rfl, fun j => rfl⟩

/-- **Sets of workspaces, request registers and logs carried by the adversary's own steps**: on
every nonzero entry of the initial state the workspace and request register with blank logs lie in
`T 0`; on every nonzero entry `(a, b)` of an operator of the step before slot `j`, the logs updated
as the absorption updates them (the request logged at slot `j` when the kind is a request) carry
`T j` into `T (j + 1)`; and each step `k` after the slots carries `T k` into `T (k + 1)`. -/
structure LogInvRaw (T : ℕ → Set ((A.W × Req) × LogReg Req A.slots)) : Prop where
  /-- The initial workspaces and request registers, with blank logs, lie in `T 0`. -/
  init : ∀ c c' : DReg A.W A.width X Y Req Resp, A.init.mat c c' ≠ 0 →
    ((c.1.1, c.1.2.1), fun _ => none) ∈ T 0
  /-- The step before slot `j` carries `T j` into `T (j + 1)`. -/
  slot : ∀ (j : Fin A.slots) r (a b : DReg A.W A.width X Y Req Resp) (lx ly : LogReg Req A.slots),
    (A.step (slotStep j)).op r a b ≠ 0 →
    (∀ j' : Fin A.slots, ly j' = if (j' : ℕ) = j ∧ A.kind a.1.1 = true then
      Equiv.swap none (some a.1.2.1) (lx j') else lx j') →
    ((b.1.1, b.1.2.1), lx) ∈ T j → ((a.1.1, a.1.2.1), ly) ∈ T (j + 1)
  /-- The step `k` after the slots carries `T k` into `T (k + 1)`. The sets are indexed by the
  step: re-applying a step need not keep a set (re-applying the relay's last step can wrap its
  clock), so a set kept by every step after the slots would lose what the last step gives. -/
  post : ∀ (k : StepIdx A.slots A.post), A.slots ≤ (k : ℕ) →
    ∀ r (a b : DReg A.W A.width X Y Req Resp) (lx : LogReg Req A.slots),
    (A.step k).op r a b ≠ 0 → ((b.1.1, b.1.2.1), lx) ∈ T k →
      ((a.1.1, a.1.2.1), lx) ∈ T (k + 1)

variable {A}

/-- **Sets kept by every step after the slots are carried step by step**: from sets `T` whose
steps after the slots keep `T slots`, the sets `T (min n slots)`. -/
theorem LogInvRaw.post_const {T : ℕ → Set ((A.W × Req) × LogReg Req A.slots)}
    (init : ∀ c c' : DReg A.W A.width X Y Req Resp, A.init.mat c c' ≠ 0 →
      ((c.1.1, c.1.2.1), fun _ => none) ∈ T 0)
    (slot : ∀ (j : Fin A.slots) r (a b : DReg A.W A.width X Y Req Resp)
      (lx ly : LogReg Req A.slots), (A.step (slotStep j)).op r a b ≠ 0 →
      (∀ j' : Fin A.slots, ly j' = if (j' : ℕ) = j ∧ A.kind a.1.1 = true then
        Equiv.swap none (some a.1.2.1) (lx j') else lx j') →
      ((b.1.1, b.1.2.1), lx) ∈ T j → ((a.1.1, a.1.2.1), ly) ∈ T (j + 1))
    (post : ∀ (k : StepIdx A.slots A.post), A.slots ≤ (k : ℕ) →
      ∀ r (a b : DReg A.W A.width X Y Req Resp) (lx : LogReg Req A.slots),
      (A.step k).op r a b ≠ 0 → ((b.1.1, b.1.2.1), lx) ∈ T A.slots →
        ((a.1.1, a.1.2.1), lx) ∈ T A.slots) :
    A.LogInvRaw fun n => T (min n A.slots) where
  init c c' h := init c c' h
  slot j r a b lx ly h hlog hx := by
    rw [Nat.min_eq_left j.isLt.le] at hx
    rw [Nat.min_eq_left (Nat.succ_le_of_lt j.isLt)]
    exact slot j r a b lx ly h hlog hx
  post k hk r a b lx h hx := by
    rw [Nat.min_eq_right hk] at hx
    rw [Nat.min_eq_right (by omega)]
    exact post k hk r a b lx h hx

/-- **Sets carried by the adversary's own steps are carried by its steps absorbed with any
table**, for a trace-preserving adversary. -/
theorem LogInvRaw.logInv {T : ℕ → Set ((A.W × Req) × LogReg Req A.slots)} (hA : A.TracePreserving)
    (hT : A.LogInvRaw T) (tab : A.OuterTab Req₂ Resp₂) : A.LogInv F tab T where
  init d d' h := by
    obtain ⟨c, c', hc, h1, h2, h3⟩ := A.tp_absorbTab_init_rel F tab h
    have hl : d.workspace.1.1.logs = fun _ => none := funext h3
    rw [hl, ← h1, ← h2]
    exact hT.init c c' hc
  slot j z y x h hx := by
    obtain ⟨r', a, b, hab, ha1, ha2, hb1, hb2, hlog⟩ := A.tp_absorbTab_rel F hA tab h
    have h' := hT.slot j r' a b x.workspace.1.1.logs y.workspace.1.1.logs hab
      (fun j' => by rw [hlog j', ha1, ha2]) (by rw [hb1, hb2]; exact hx)
    rw [ha1, ha2] at h'
    exact h'
  post k hk z y x h hx := by
    obtain ⟨r', a, b, hab, ha1, ha2, hb1, hb2, hlog⟩ := A.tp_absorbTab_rel F hA tab h
    have hl : y.workspace.1.1.logs = x.workspace.1.1.logs := funext fun j' => by
      rw [hlog j']
      split_ifs with hj
      · have := j'.isLt
        omega
      · rfl
    have h' := hT.post k hk r' a b x.workspace.1.1.logs hab (by rw [hb1, hb2]; exact hx)
    rw [ha1, ha2, ← hl] at h'
    exact h'

end Raw

/-! ### At a fixed base component -/

section Restrict

variable {X Y Y₁ Y₂ Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂] [Fintype Req] [DecidableEq Req]
  [Fintype Resp] [DecidableEq Resp] [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]
  (sp : Y ≃+ Y₁ × Y₂) (H₁ : X → Y₁) {shA : AlgShape X Y Req Resp} {A : AdaptiveIAlg shA O}

/-- **Sets carried by the adversary's steps are carried by the steps of the adversary at a fixed
base component**, read along the projection of its workspace onto the adversary's. -/
theorem LogInvRaw.restrictAt {T : ℕ → Set ((A.W × Req) × LogReg Req A.slots)}
    (hT : A.LogInvRaw T) :
    (A.restrictAt sp H₁).LogInvRaw fun n => {x | ((x.1.1.1, x.1.2), x.2) ∈ T n} where
  init _ _ h := hT.init _ _ h
  slot j r _ _ lx ly h hlog hx := hT.slot j r _ _ lx ly h hlog hx
  post k hk r _ _ lx h hx := hT.post k hk r _ _ lx h hx

end Restrict

/-! ### Followed by a classical program -/

section ThenProg

open Quantum.OracleProg (ProgW)

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  {shA : AlgShape X Y Req Resp} {A : AdaptiveIAlg shA O} {Res : Type} (P : A.W → GordieHowe.OracleProg X Y Res) (q : ℕ)

omit [Nonempty X] [AddGroup Y] in
/-- **A nonzero entry of a Kraus map lifted to the registers with the program's** is one of the
map on `A`'s registers. -/
theorem liftProg_op_ne_zero {R : Type} [Fintype R]
    {K : KrausMap R (DReg A.W A.width X Y Req Resp) (DReg A.W A.width X Y Req Resp)} {r : R}
    {a b : DReg (A.W × ProgW X Y q) A.width X Y Req Resp}
    (h : (A.liftProg q K).op r a b ≠ 0) :
    K.op r (A.progSplit q a).1 (A.progSplit q b).1 ≠ 0 := by
  intro h0
  apply h
  rw [liftProg, KrausMap.tensorId_reindex_op_apply]
  simp only [Equiv.symm_symm, h0, zero_mul]

omit [Nonempty X] [AddGroup Y] in
/-- **A nonzero entry of a Kraus map with its operators re-indexed** is one of the map. -/
theorem embedIdx_op_ne_zero {ι R R' : Type} [Fintype ι] [DecidableEq ι] [Fintype R] [Fintype R']
    {K : KrausMap R ι ι} {f : R ↪ R'} {r' : R'} {a b : ι} (h : (K.embedIdx f).op r' a b ≠ 0) :
    ∃ r, K.op r a b ≠ 0 := by
  dsimp only [KrausMap.embedIdx] at h
  split_ifs at h with hr
  · exact ⟨_, h⟩
  · exact absurd rfl h

omit [Nonempty X] [AddGroup Y] in
/-- A nonzero entry of a basis permutation is on its graph. -/
theorem ofPerm_op_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι] {σ : Equiv.Perm ι} {r : Unit}
    {a b : ι} (h : (KrausMap.ofPerm σ).op r a b ≠ 0) : a = σ b := by
  rw [KrausMap.ofPerm_op_apply] at h
  by_contra hab
  exact h (by simp [hab])

/-- The start of the program keeps `A`'s workspace and the request and response registers. -/
theorem startPerm_keeps (p : DReg (A.W × ProgW X Y q) A.width X Y Req Resp) :
    (A.startPerm P q p).1.1.1 = p.1.1.1 ∧ (A.startPerm P q p).1.2 = p.1.2 :=
  ⟨rfl, rfl⟩

/-- The program's steps keep `A`'s workspace and the request and response registers. -/
theorem progPerm_keeps (i : Fin q) (p : DReg (A.W × ProgW X Y q) A.width X Y Req Resp) :
    (A.progPerm P q i p).1.1.1 = p.1.1.1 ∧ (A.progPerm P q i p).1.2 = p.1.2 :=
  ⟨rfl, rfl⟩

variable (hP : ∀ w, (P w).QueriesLE q) {O' : Type} (g : A.W → (Fin q → Y) → O')

/-- **Sets carried by the adversary's steps are carried by the steps of the adversary followed by
a classical program**, read along the projection of its workspace onto the adversary's: the
program's steps make no request and keep `A`'s workspace and request register, so after `A`'s last
step the set is `A`'s last one. -/
theorem LogInvRaw.thenProgWith {T : ℕ → Set ((A.W × Req) × LogReg Req A.slots)}
    (hT : A.LogInvRaw T) :
    (A.thenProgWith P q hP g).LogInvRaw fun n =>
      {x | ((x.1.1.1, x.1.2), x.2) ∈ T (min n (A.slots + A.post + 1))} where
  init c c' h := by
    refine hT.init (A.progSplit q c).1 (A.progSplit q c').1 fun h0 => h ?_
    change (A.init.tensorKet _).mat (A.progSplit q c) (A.progSplit q c') = 0
    rw [MState.tensorKet_mat, Matrix.kroneckerMap_apply, h0, zero_mul]
  slot j r a b lx ly h hlog hx := by
    change (A.thenStep P q (slotStep j)).op r a b ≠ 0 at h
    have hj : ((slotStep j : StepIdx A.slots (A.post + q)) : ℕ) < A.slots + A.post := by
      have := j.isLt
      change (j : ℕ) < A.slots at this
      change (j : ℕ) < _
      omega
    unfold thenStep at h
    simp only [hj, ↓reduceDIte] at h
    obtain ⟨r₀, h₀⟩ := embedIdx_op_ne_zero h
    have hj' : (j : ℕ) < A.slots := j.isLt
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [Nat.min_eq_left (by omega)] at hx
    rw [Nat.min_eq_left (by omega)]
    exact hT.slot j r₀ _ _ lx ly (liftProg_op_ne_zero q h₀) hlog hx
  post k hk r a b lx h hx := by
    change (A.thenStep P q k).op r a b ≠ 0 at h
    unfold thenStep at h
    simp only [Set.mem_setOf_eq] at hx ⊢
    split_ifs at h with h1 h2
    · obtain ⟨r₀, h₀⟩ := embedIdx_op_ne_zero h
      rw [Nat.min_eq_left (by omega)] at hx
      rw [Nat.min_eq_left (by omega)]
      exact hT.post ⟨k, by omega⟩ hk r₀ _ _ lx (liftProg_op_ne_zero q h₀) hx
    · obtain ⟨r₀, h₀⟩ := embedIdx_op_ne_zero h
      change (A.liftProg q (A.step lastStep)).op r₀ ((A.startPerm P q).symm a) b ≠ 0 at h₀
      have hs := startPerm_keeps P q ((A.startPerm P q).symm a)
      have e : A.startPerm P q ((A.startPerm P q).symm a) = a :=
        (A.startPerm P q).apply_symm_apply a
      rw [e] at hs
      rw [Nat.min_eq_left (by omega)] at hx
      rw [Nat.min_eq_right (by omega)]
      have h' := hT.post lastStep (by change A.slots ≤ A.slots + A.post; omega) r₀ _ _ lx
        (liftProg_op_ne_zero q h₀) (by rw [show (k : ℕ) = A.slots + A.post from h2] at hx; exact hx)
      change (((((A.startPerm P q).symm a).1.1.1, ((A.startPerm P q).symm a).1.2.1), lx) ∈
        T (A.slots + A.post + 1)) at h'
      change ((a.1.1.1, a.1.2.1), lx) ∈ T (A.slots + A.post + 1)
      rw [← hs.1, ← congrArg Prod.fst hs.2] at h'
      exact h'
    · obtain ⟨r₀, h₀⟩ := embedIdx_op_ne_zero h
      have hab := ofPerm_op_ne_zero h₀
      subst hab
      obtain ⟨e1, e2⟩ := progPerm_keeps P q _ b
      rw [Nat.min_eq_right (by omega)] at hx
      rw [Nat.min_eq_right (by omega)]
      change ((((A.progPerm P q _ b).1.1.1, (A.progPerm P q _ b).1.2.1), lx) ∈
        T (A.slots + A.post + 1))
      rw [e1, congrArg Prod.fst e2]
      exact hx

end ThenProg

/-! ### The relayed adversary -/

section Relay

open Classical

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) [AddGroup Y]
  {Req' Resp' O' : Type} [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Inhabited X] [Inhabited Req'] {Xs Ys : Type} [AddGroup Ys] [Fintype Ys] [DecidableEq Ys]
  (F : MultiRelay X Y Req Resp Req' Resp' Xs Ys) (Q : ℕ)
  (out' : A.RelayWS F → O') (p : Req' → Bool)

/-- **The relayed adversary's own steps carry the bookkeeping** (`relayFull_step` on the
adversary's Kraus operators): step `j` carries `RelayFull j` into `RelayFull (j + 1)`, the logs
updated as the absorption updates them, when the blank and the idle requests fail `p`. -/
theorem relayFull_step_raw (hpd : p default = false) (hpi : p F.idle = false)
    (j : StepIdx (A.relayAdv F Q out').slots (A.relayAdv F Q out').post)
    {r' : (A.relayAdv F Q out').R}
    {a b : DReg (A.relayAdv F Q out').W (A.relayAdv F Q out').width X Y Req' Resp'}
    {lx ly : LogReg Req' (A.relayAdv F Q out').slots}
    (hab : ((A.relayAdv F Q out').step j).op r' a b ≠ 0)
    (hlog : ∀ j' : Fin (A.relayAdv F Q out').slots, ly j' =
      if (j' : ℕ) = j ∧ (A.relayAdv F Q out').kind a.1.1 = true then
        Equiv.swap none (some a.1.2.1) (lx j') else lx j')
    (hx : ((b.1.1, b.1.2.1), lx) ∈ A.RelayFull F Q out' p j) :
    ((a.1.1, a.1.2.1), ly) ∈ A.RelayFull F Q out' p (j + 1) := by
  obtain ⟨zz, hpa, hrest⟩ := A.relayAdv_step_rel F Q out' hab
  have hn : 0 < (A.toTPKindAlg true).unitOut.width := (A.toTPKindAlg true).unitOut.width_pos
  have hy1 : a.1.1.1 = (((A.relayA F Q out').cntSplit a).1).1.1 := by
    rfl
  have hy2 : a.1.2.1 = (((A.relayA F Q out').cntSplit a).1).1.2.1 := by
    rfl
  have hx1 : b.1.1.1 = (((A.relayA F Q out').cntSplit b).1).1.1 := by
    rfl
  have hx2 : b.1.2.1 = (((A.relayA F Q out').cntSplit b).1).1.2.1 := by
    rfl
  -- the new log is the request register, the others are kept
  have hcases := fun (hbl : ∀ j' : Fin (A.relayAdv F Q out').slots, (j' : ℕ) = j →
      lx j' = none) {j'} {r''} (hl : ly j' = some r'') =>
    log_cases hlog hbl hl
  -- the new log satisfying `p` is an ask
  have hnew : ∀ es', Distinguisher.Booked F (A.budget + A.post) Q (j : ℕ) es'
      ((A.relayA F Q out').cntSplit a).1 → ∀ r'', r'' = a.1.2.1 → p r'' = true →
      F.AsksAt (A.toTPKindAlg true).unitOut.width (A.budget + A.post) Q es'
        a.1.1.1.store a.1.1.1.side j r'' := by
    intro es' hbk r'' hr hp
    obtain ⟨hbt, ⟨hbl, hbr, -⟩, hbq⟩ := hbk
    obtain ⟨hact, hidle⟩ := AdaptiveIAlg.ask_of_askOf F p hpd hpi (hr.trans (hy2.trans hbq)) hp
    have := MultiRelay.asksAt_of_actAt hact hidle
    rw [hbr, MultiRelay.recList_getElem? es' hbl, hbt] at this
    rw [hy1]
    exact this
  rcases hj : (j : ℕ) with _ | t
  · -- the first step
    rw [hj] at hx
    obtain ⟨ht0, hr0, hq0, hl0, hs0⟩ := hx
    have hrest' : Distinguisher.rest F zz =
        Distinguisher.rest F ((A.relayA F Q out').cntSplit b).1 := by
      simp only [hj, ↓reduceIte] at hrest
      exact hrest
    obtain ⟨es', hbk⟩ := Distinguisher.booked_zero F (A.budget + A.post) Q hn A.pureD.kind
      (hx1 ▸ ht0) (hx1 ▸ hr0) (hx2 ▸ hq0) hrest'
    rw [← hpa] at hbk
    refine ⟨es', ?_, ?_, ?_, fun j' hj' => ?_, fun j' r'' hl hp => ?_, ?_⟩
    rotate_right
    · rw [hy1, hpa]
      refine Distinguisher.side_setupFun_recordFun _ _
        (Distinguisher.side_consSide_of_rest hrest' ?_)
      rw [← hx1, hs0, hr0, F.consSide_blank]
    · rw [hy1]
      exact hbk.1
    · rw [hy1]
      exact hbk.2.1
    · rw [hy1, hy2]
      exact hbk.2.2
    · dsimp only
      rw [hlog j']
      split_ifs with hk
      · have := hk.1
        omega
      · exact hl0 j'
    · rcases hcases (fun j' _ => hl0 j') hl with ⟨hjj, hr⟩ | ⟨-, hl'⟩
      · rw [hjj]
        exact hnew es' (hj ▸ hbk) r'' hr hp
      · have h0 : lx j' = none := hl0 j'
        rw [h0] at hl'
        exact absurd hl' (by simp)
  · -- the later steps
    rw [hj] at hx
    obtain ⟨es, ht, hrec, hq, hbl, hask, hs⟩ := hx
    have hrest' : Distinguisher.rest F zz = Distinguisher.rest F (Distinguisher.finalizeFun F
        (A.budget + A.post) Q (Distinguisher.sideAddsPerm F (A.budget + A.post) Q
          (Distinguisher.tickPerm F (Distinguisher.teardownFun F
          (A.budget + A.post) Q ((A.relayA F Q out').cntSplit b).1)))) := by
      simp only [hj, Nat.add_one_ne_zero, ↓reduceIte] at hrest
      exact hrest
    have hbq : Distinguisher.Booked F (A.budget + A.post) Q t es
        ((A.relayA F Q out').cntSplit b).1 :=
      ⟨hx1 ▸ ht, hx1 ▸ hrec, by rw [← hx1, ← hx2]; exact hq⟩
    have htS : t < Distinguisher.relaySlots (A.toTPKindAlg true).unitOut.width
        ((A.toTPKindAlg true).unitOut.slots + A.post) F := by
      have := j.isLt
      change (j : ℕ) < Distinguisher.relaySlots (A.toTPKindAlg true).unitOut.width
        ((A.toTPKindAlg true).unitOut.slots + A.post) F + 0 + 1 at this
      omega
    obtain ⟨es', hes', hbk, hst, hsd⟩ := Distinguisher.booked_succ F (A.budget + A.post) Q hn
      A.pureD.kind htS hbq hrest'
    rw [← hpa] at hbk hst hsd
    refine ⟨es', ?_, ?_, ?_, fun j' hj' => ?_, fun j' r'' hl hp => ?_, ?_⟩
    rotate_right
    · rw [hy1, hpa]
      refine Distinguisher.side_setupFun_recordFun _ _
        (Distinguisher.side_consSide_of_rest hrest' ?_)
      have hpre := Distinguisher.side_preFun (F := F) (b := A.budget + A.post) (Q := Q) (t + 1)
        (Nat.add_one_ne_zero t) ((A.relayA F Q out').cntSplit b).1 (by rw [← hx1, ht]; exact hrec)
        (by rw [← hx1, ht]; exact htS) (by rw [← hx1]; exact hs)
      simpa only [Distinguisher.preFun, Nat.add_one_ne_zero, ↓reduceIte] using hpre
    · rw [hy1]
      exact hbk.1
    · rw [hy1]
      exact hbk.2.1
    · rw [hy1, hy2]
      exact hbk.2.2
    · dsimp only
      rw [hlog j']
      split_ifs with hk
      · have := hk.1
        omega
      · exact hbl j' (by omega)
    · rcases hcases (fun j' hj' => hbl j' (by omega)) hl with ⟨hjj, hr⟩ | ⟨hjj, hl'⟩
      · rw [hjj]
        exact hnew es' (hj ▸ hbk) r'' hr hp
      · have hle : (j' : ℕ) ≤ t := by
          by_contra hlt
          have h0 : lx j' = none := hbl j' (by omega)
          rw [h0] at hl'
          exact absurd hl' (by simp)
        have h1 := hask j' r'' hl' hp
        rw [hx1] at h1
        have h2 := hsd j' hle r'' h1
        have h3 : F.AsksAt (A.toTPKindAlg true).unitOut.width (A.budget + A.post) Q es'
            (((A.relayA F Q out').cntSplit a).1).1.1.store
            (((A.relayA F Q out').cntSplit a).1).1.1.side j' r'' := by
          rcases hes' with rfl | ⟨e, rfl⟩
          · exact h2
          · exact h2.append e
        rw [hy1]
        exact h3


/-- **The relayed adversary's initial states have the bookkeeping before step `0`**
(`relayFull_init` on the adversary's initial state), with blank logs. -/
theorem relayFull_init_raw
    {c c' : DReg (A.relayAdv F Q out').W (A.relayAdv F Q out').width X Y Req' Resp'}
    (h : (A.relayAdv F Q out').init.mat c c' ≠ 0) :
    ((c.1.1, c.1.2.1), fun _ => none) ∈ A.RelayFull F Q out' p 0 := by
  erw [MState.reindex_tensorKet_mat] at h
  obtain ⟨c₀, c₀', rfl, -, hc⟩ := embed_ne_zero_exists h
  have hv : (A.relayD F Q).init c₀ ≠ 0 := by
    intro h0
    apply hc
    rw [Distinguisher.toAdaptive_init_mat]
    change (A.relayD F Q).init c₀ * star ((A.relayD F Q).init c₀') = 0
    rw [h0, zero_mul]
  obtain ⟨d0, rfl⟩ : c₀ ∈ Set.range (Distinguisher.relayInit (W := (A.toTPKindAlg true).unitOut.DW × Bool)
      (Req := Req) (Resp := Resp) (n := (A.toTPKindAlg true).unitOut.width)
      (m := (A.toTPKindAlg true).unitOut.slots + A.post) F) := by
    by_contra hn
    rw [A.relayD_init] at hv
    exact hv (embV_apply_of_notMem _ hn)
  exact ⟨rfl, rfl, rfl, fun j => rfl, rfl⟩

/-- **The sets `RelayFull` are carried by the relayed adversary's own steps** (`LogInvRaw`), when
the blank and the idle requests fail `p`. -/
theorem relayAdv_logInvRaw (hpd : p default = false) (hpi : p F.idle = false) :
    (A.relayAdv F Q out').LogInvRaw (A.RelayFull F Q out' p) where
  init _ _ h := A.relayFull_init_raw F Q out' p h
  slot j _ _ _ _ _ h hlog hx := A.relayFull_step_raw F Q out' p hpd hpi (slotStep j) h hlog hx
  post k hk _ _ _ lx h hx := A.relayFull_step_raw F Q out' p hpd hpi k h
    (fun j' => by rw [if_neg (fun he => by have := j'.isLt; omega)]) hx

/-- **The relayed adversary logs at most `K · Q` requests satisfying `p`, on its own steps**
(`relayAdv_logs_le` in the form `LogInvRaw`), when the blank and the idle requests fail `p`. -/
theorem relayAdv_logsRaw_le (hpd : p default = false) (hpi : p F.idle = false) :
    ∃ T, (A.relayAdv F Q out').LogInvRaw T ∧
      ∀ x ∈ T ((A.relayAdv F Q out').slots + (A.relayAdv F Q out').post + 1),
        (Finset.univ.filter fun j => (x.2 j).any p = true).card ≤ F.K * Q :=
  ⟨A.RelayFull F Q out' p, A.relayAdv_logInvRaw F Q out' p hpd hpi,
    fun _ hx => A.countLE_of_relayFull F Q out' p hx⟩

end Relay

/-! ### The relayed adversary followed by a program, at the zero base component -/

section Packaged

variable {m : ℕ} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {Y Y₁ : Type} [Fintype Y] [DecidableEq Y] [Fintype Y₁] [DecidableEq Y₁] [AddGroup Y] [AddGroup Y₁]
  (sp : Y ≃+ Y₁ × BitStr I J)
  {Req Resp O : Type} [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  {shA : AlgShape (Bits m) Y Req Resp} (A : AdaptiveIAlg shA O)
  {Req' Resp' O' : Type} [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp']
  [Inhabited (Bits m)] [Inhabited Req'] (F : MultiRelay (Bits m) Y Req Resp Req' Resp') (Q : ℕ)
  (out' : A.RelayWS F → O') {Res : Type}
  (P : (A.relayAdv F Q out').W → GordieHowe.OracleProg (Bits m) Y Res) (q : ℕ)
  (hP : ∀ w, (P w).QueriesLE q) {O'' : Type}
  (g : (A.relayAdv F Q out').W → (Fin q → Y) → O'')
  {Req₁ Resp₁ Req₂ Resp₂ : Type} [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁]
  [DecidableEq Resp₁] [Inhabited Req₁] [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂]
  [DecidableEq Resp₂]

/-- **The relayed adversary followed by a classical program, at the zero base component, logs at
most `K · Q` requests satisfying `p`** (`relayAdv_logsRaw_le` through `LogInvRaw.thenProgWith` and
`LogInvRaw.restrictAt`): absorbed with any table through any relay, sets of its workspaces,
request registers and absorbed logs carried by its steps (`LogInv`), which writing the part of the
local queries of `restrictBaseW` keeps, end in the logs with at most `K · Q` requests satisfying
`p`, when the blank and the idle requests fail `p`. -/
theorem logInv_restrictAt_thenProgWith_relayAdv (p : Req' → Bool) (hpd : p default = false)
    (hpi : p F.idle = false) (G : TwoRelay Req' Resp' Req₁ Resp₁ Req₂ Resp₂)
    (tab : ((((A.relayAdv F Q out').thenProgWith P q hP g).restrictAt sp 0)).OuterTab Req₂ Resp₂) :
    ∃ T, (((A.relayAdv F Q out').thenProgWith P q hP g).restrictAt sp 0).LogInv G tab T ∧
      (∀ l x v, x ∈ T l →
        (((((A.relayAdv F Q out').thenProgWith P q hP g).restrictBaseW sp).Lw.set x.1.1 v,
          x.1.2), x.2) ∈ T l) ∧
      ∀ x ∈ T ((((A.relayAdv F Q out').thenProgWith P q hP g).restrictAt sp 0).slots +
          (((A.relayAdv F Q out').thenProgWith P q hP g).restrictAt sp 0).post + 1),
        (Finset.univ.filter fun j => (x.2 j).any p = true).card ≤ F.K * Q := by
  obtain ⟨T, hT, hTQ⟩ := A.relayAdv_logsRaw_le F Q out' p hpd hpi
  have hT' := (hT.thenProgWith P q hP g).restrictAt sp 0
  refine ⟨_, hT'.logInv G (tracePreserving_restrictAt sp 0 _
    (thenProgWith_tracePreserving _ P q hP g (relayAdv_tracePreserving A F Q out'))) tab,
    fun l x v hx => hx, fun x hx => hTQ ((x.1.1.1.1, x.1.2), x.2) ?_⟩
  have hm : min ((((A.relayAdv F Q out').thenProgWith P q hP g).restrictAt sp 0).slots +
      (((A.relayAdv F Q out').thenProgWith P q hP g).restrictAt sp 0).post + 1)
      ((A.relayAdv F Q out').slots + (A.relayAdv F Q out').post + 1) =
      (A.relayAdv F Q out').slots + (A.relayAdv F Q out').post + 1 := by
    change min ((A.relayAdv F Q out').slots + ((A.relayAdv F Q out').post + q) + 1) _ = _
    omega
  have hx' := hx
  simp only [Set.mem_setOf_eq] at hx'
  rw [hm] at hx'
  exact hx'

end Packaged

end AdaptiveIAlg

end GordieHowe.Quantum
