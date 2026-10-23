-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.Budget

@[expose] public section

/-!
# Relabelling the requests of a game

For an equivalence `e : Req ≃ Req'` of request types, a distinguisher `D` with requests in `Req`
becomes a distinguisher `D.mapReq e` with requests in `Req'` (`Distinguisher.mapReq`): its
registers are relabelled by `e` on the request register, its steps are conjugated by that
relabelling, and its accepting set is carried along. Against an environment `E'` with requests in
`Req'` it accepts with the probability of `D` against `E'.comapReq e`, the environment that
answers a request `req` as `E'` answers `e req` (`Distinguisher.acceptProb_mapReq`), and it keeps
the query budget of `D` (`Distinguisher.Budget.mapReq`).

The zero-knowledge proofs use it to read a kernel that sees the witness as a simulator on the
game whose statements are the requests (`GordieHowe/Model/QROM/LeafZK.lean`).
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

/-! ### Relabelling the computational basis -/

section Relabel

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **The unitary that relabels the computational basis along `g`**: `|i⟩ ↦ |g i⟩`. For a
permutation it is `permOp`. -/
noncomputable def relabelOp (g : ι ≃ κ) : QState ι ≃ₗᵢ[ℂ] QState κ :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ g

@[simp]
theorem relabelOp_apply (g : ι ≃ κ) (v : QState ι) (k : κ) : relabelOp g v k = v (g.symm k) :=
  rfl

@[simp]
theorem relabelOp_symm_relabelOp (g : ι ≃ κ) (v : QState ι) : relabelOp g.symm (relabelOp g v) = v := by
  ext i
  simp

@[simp]
theorem relabelOp_relabelOp_symm (g : ι ≃ κ) (v : QState κ) : relabelOp g (relabelOp g.symm v) = v := by
  ext i
  simp

/-- A measurement after a relabelling is the measurement of the preimage. -/
theorem prob_relabelOp (g : ι ≃ κ) (A : Set κ) (v : QState ι) :
    prob A (relabelOp g v) = prob (g ⁻¹' A) v := by
  classical
  simp only [prob, EuclideanSpace.norm_sq_eq, mask_apply, relabelOp_apply]
  rw [← g.sum_comp]
  refine sum_congr rfl fun i _ => ?_
  by_cases h : g i ∈ A <;> simp [Set.indicator, h]

/-- A relabelled vector is supported in `S` when the vector is supported in the preimage. -/
theorem supported_relabelOp_iff {g : ι ≃ κ} {S : Set κ} {v : QState ι} :
    Supported S (relabelOp g v) ↔ Supported (g ⁻¹' S) v := by
  constructor
  · intro h r hr
    have := h (g r) hr
    rwa [relabelOp_apply, Equiv.symm_apply_apply] at this
  · intro h r hr
    rw [relabelOp_apply]
    exact h _ (by simpa using hr)

/-- A basis permutation that corresponds to `π` along `g` commutes with the relabelling. -/
theorem permOp_relabelOp (g : ι ≃ κ) {π : Equiv.Perm ι} {π' : Equiv.Perm κ}
    (h : ∀ r, π' (g r) = g (π r)) (v : QState ι) :
    permOp π' (relabelOp g v) = relabelOp g (permOp π v) := by
  ext k
  have hk : π'.symm k = g (π.symm (g.symm k)) := by
    rw [Equiv.symm_apply_eq, h, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  simp only [permOp_apply, relabelOp_apply]
  rw [hk, Equiv.symm_apply_apply]

end Relabel

/-! ### Relabelling the request register -/

section Registers

variable {W X Y Req Req' A : Type*} (e : Req ≃ Req') {n m : ℕ}

/-- The logs relabelled along `e`. -/
def logsEquiv : LogReg Req m ≃ LogReg Req' m :=
  Equiv.arrowCongr (Equiv.refl _) (Equiv.optionCongr e)

@[simp]
theorem logsEquiv_apply (lg : LogReg Req m) (k : Fin m) : logsEquiv e lg k = (lg k).map e :=
  rfl

/-- The distinguisher's registers with the request register relabelled along `e`. -/
def dregEquiv : DReg W n X Y Req A ≃ DReg W n X Y Req' A :=
  Equiv.prodCongr (Equiv.prodCongr (Equiv.refl W) (Equiv.prodCongr e (Equiv.refl _))) (Equiv.refl _)

/-- The game registers with the request register and the logs relabelled along `e`. -/
def gameRegEquiv : GameReg W n X Y Req A m ≃ GameReg W n X Y Req' A m :=
  Equiv.prodCongr (Equiv.prodCongr (Equiv.refl W) (Equiv.prodCongr e
    (Equiv.prodCongr (Equiv.refl _) (logsEquiv e)))) (Equiv.refl _)

@[simp]
theorem workspace_dregEquiv (r : DReg W n X Y Req A) : (dregEquiv e r).workspace = r.workspace :=
  rfl

@[simp]
theorem workspace_dregEquiv_symm (r : DReg W n X Y Req' A) :
    ((dregEquiv e).symm r).workspace = r.workspace :=
  rfl

theorem splitLogs_gameRegEquiv (r : GameReg W n X Y Req A m) :
    splitLogs (gameRegEquiv e r) = (dregEquiv e (splitLogs r).1, logsEquiv e (splitLogs r).2) :=
  rfl

theorem splitLogs_symm_dregEquiv (d : DReg W n X Y Req A) (lg : LogReg Req m) :
    splitLogs.symm (dregEquiv e d, logsEquiv e lg) = gameRegEquiv e (splitLogs.symm (d, lg)) :=
  rfl

theorem requestsBefore_logsEquiv (lg : LogReg Req m) :
    ∀ k, requestsBefore (logsEquiv e lg) k = (requestsBefore lg k).map e
  | 0 => rfl
  | k + 1 => by
    rw [requestsBefore, requestsBefore, requestsBefore_logsEquiv lg k, List.map_append]
    split_ifs with h
    · cases hl : lg ⟨k, h⟩ <;> simp [hl]
    · rfl

theorem requests_logsEquiv (lg : LogReg Req m) : requests (logsEquiv e lg) = (requests lg).map e :=
  requestsBefore_logsEquiv e lg m

variable [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype Req'] [Fintype A]

/-- **A log-controlled unitary that corresponds to another along the relabelling** commutes with
it. -/
theorem logControlled_relabelOp
    {U : LogReg Req m → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)}
    {U' : LogReg Req' m → QState (DReg W n X Y Req' A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req' A)}
    (h : ∀ lg w, U' (logsEquiv e lg) (relabelOp (dregEquiv e) w) = relabelOp (dregEquiv e) (U lg w))
    (v : QState (GameReg W n X Y Req A m)) :
    logControlled U' (relabelOp (gameRegEquiv e) v) = relabelOp (gameRegEquiv e) (logControlled U v) := by
  ext r'
  obtain ⟨r, rfl⟩ := (gameRegEquiv e).surjective r'
  rw [logControlled_apply, relabelOp_apply, Equiv.symm_apply_apply, logControlled_apply,
    splitLogs_gameRegEquiv]
  have hw : (WithLp.toLp 2 fun d' => relabelOp (gameRegEquiv e) v
      (splitLogs.symm (d', logsEquiv e (splitLogs r).2)) : QState (DReg W n X Y Req' A)) =
      relabelOp (dregEquiv e) (WithLp.toLp 2 fun d => v (splitLogs.symm (d, (splitLogs r).2))) := by
    ext d'
    obtain ⟨d, rfl⟩ := (dregEquiv e).surjective d'
    rw [relabelOp_apply, relabelOp_apply, Equiv.symm_apply_apply, splitLogs_symm_dregEquiv,
      Equiv.symm_apply_apply]
  rw [hw, h, relabelOp_apply, Equiv.symm_apply_apply]

end Registers

/-! ### Environments read through a map of requests -/

namespace Env

variable {Ω Req Req' A X Y : Type*} {St : Type _} {Q : ℕ}

/-- **The environment that answers a request `req` as `E` answers `f req`.** -/
def comapReq (E : Env Ω Req' A X Y Q St) (f : Req → Req') : Env Ω Req A X Y Q St where
  μ := E.μ
  oracle₀ := E.oracle₀
  respond ω i req s := E.respond ω i (f req) s

variable (E : Env Ω Req' A X Y Q St) (f : Req → Req')

theorem oracleIn_comapReq (ω : Ω) (rs : List Req) :
    (E.comapReq f).oracleIn ω rs = E.oracleIn ω (rs.map f) := by
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    rw [oracleIn_append_singleton, List.map_append, List.map_singleton, oracleIn_append_singleton,
      ih, List.length_map]
    rfl

theorem answerAfter_comapReq (ω : Ω) (rs : List Req) (req : Req) :
    (E.comapReq f).answerAfter ω rs req = E.answerAfter ω (rs.map f) (f req) := by
  simp only [answerAfter, oracleIn_comapReq, List.length_map]
  rfl

variable (e : Req ≃ Req') {m : ℕ}

theorem answer_comapReq (ω : Ω) (lg : LogReg Req m) (k : Fin m) :
    (E.comapReq e).answer ω lg k = E.answer ω (logsEquiv e lg) k := by
  simp only [answer, logsEquiv_apply, requestsBefore_logsEquiv]
  cases lg k <;> simp [answerAfter_comapReq]

theorem oracle_comapReq [OracleState St X Y] (ω : Ω) (lg : LogReg Req m) :
    (E.comapReq e).oracle ω lg = E.oracle ω (logsEquiv e lg) := by
  simp only [oracle, requests_logsEquiv, oracleIn_comapReq]

end Env

/-! ### The relabelled distinguisher -/

namespace Distinguisher

variable {W X Y Req Req' A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req]
  [Fintype Req'] [Fintype A] {n m : ℕ} (D : Distinguisher W X Y Req A n m) (e : Req ≃ Req')

/-- **A distinguisher with its requests relabelled along `e`**: the same kind register, the initial
state and the steps relabelled on the request register, the accepting set carried along.

Running time: that of `D`; each step is `D`'s step between two relabellings of the request
register by `e` and its inverse. This running time is argued here, not proved in Lean. -/
noncomputable def mapReq : Distinguisher W X Y Req' A n m where
  kind := D.kind
  init := relabelOp (dregEquiv e) D.init
  norm_init := by rw [LinearIsometryEquiv.norm_map, D.norm_init]
  step k := (relabelOp (dregEquiv e).symm).trans ((D.step k).trans (relabelOp (dregEquiv e)))
  accept := (dregEquiv e).symm ⁻¹' D.accept

/-- **A final unitary relabelled along `e`.** -/
noncomputable def mapPost
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)) :
    (X → Y) → QState (DReg W n X Y Req' A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req' A) :=
  fun H => (relabelOp (dregEquiv e).symm).trans ((post H).trans (relabelOp (dregEquiv e)))

@[simp]
theorem mapPost_noPost : mapPost (W := W) (X := X) (Y := Y) (n := n) (A := A) e noPost = noPost := by
  funext H
  refine LinearIsometryEquiv.ext fun v => ?_
  simp [mapPost, noPost]

theorem stepAt_mapReq (k : ℕ) (v : QState (DReg W n X Y Req A)) :
    (D.mapReq e).stepAt k (relabelOp (dregEquiv e) v) = relabelOp (dregEquiv e) (D.stepAt k v) := by
  unfold stepAt
  split_ifs
  · simp [mapReq]
  · rfl

variable [DecidableEq Req] [DecidableEq Req'] [DecidableEq A]

omit [DecidableEq A] in
theorem gameInit_mapReq :
    (D.mapReq e).gameInit (m := m) = relabelOp (gameRegEquiv e) D.gameInit := by
  ext r'
  obtain ⟨r, rfl⟩ := (gameRegEquiv e).surjective r'
  rw [relabelOp_apply, Equiv.symm_apply_apply]
  have hl : (logsEquiv e (splitLogs r).2 = fun _ => none) ↔ (splitLogs r).2 = fun _ => none := by
    simp only [funext_iff, logsEquiv_apply, Option.map_eq_none_iff]
  simp only [gameInit, WithLp.ofLp_toLp]
  split_ifs with h1 h2 h2
  · simp [mapReq, splitLogs_gameRegEquiv]
  · exact absurd (hl.1 h1) h2
  · exact absurd (hl.2 h2) h1
  · rfl

omit [DecidableEq Req] [DecidableEq Req'] [DecidableEq A] in
theorem liftedStep_mapReq (k : ℕ) (v : QState (GameReg W n X Y Req A m)) :
    (D.mapReq e).liftedStep k (relabelOp (gameRegEquiv e) v) =
      relabelOp (gameRegEquiv e) (D.liftedStep k v) :=
  logControlled_relabelOp e (fun _ w => D.stepAt_mapReq e k w) v

variable {Ω : Type*} {St : Type _} [AddGroup Y] {Q : ℕ} [OracleState St X Y]
  (E : Env Ω Req' A X Y Q St)

theorem eventPerm_mapReq (ω : Ω) (k : ℕ) (r : GameReg W n X Y Req A m) :
    (D.mapReq e).eventPerm E ω k (gameRegEquiv e r) =
      gameRegEquiv e (D.eventPerm (E.comapReq e) ω k r) := by
  unfold eventPerm
  split_ifs with hk
  · rcases r with ⟨⟨w, req, a, lg⟩, qs⟩
    have hupd : ∀ x : Option Req, logsEquiv e (Function.update lg ⟨k, hk⟩ x) =
        Function.update (logsEquiv e lg) ⟨k, hk⟩ (x.map e) := fun x => by
      funext i
      by_cases hi : i = ⟨k, hk⟩
      · subst hi
        simp
      · simp [Function.update_of_ne hi]
    have hswap : ∀ x : Option Req, (Equiv.swap none (some req) x).map e =
        Equiv.swap none (some (e req)) (x.map e) := fun x =>
      (Option.map_injective e.injective).map_swap none (some req) x
    by_cases hw : D.kind w
    · have hw' : (D.mapReq e).kind w = true := hw
      simp only [Equiv.trans_apply, Env.requestPerm, Env.oraclePerm, Equiv.prodCongr_apply,
        Prod.map, copyPerm_apply, respondPerm_apply, queryPermOf_apply,
        gameRegEquiv, Equiv.refl_apply, hw, hw', ↓reduceIte]
      refine Prod.ext (Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))) ?_
      · simp [Env.answer_comapReq, hupd, hswap]
      · simp [hupd, hswap]
      · funext j
        simp
    · have hw'' : D.kind w = false := by simpa using hw
      have hw' : (D.mapReq e).kind w = false := hw''
      simp only [Equiv.trans_apply, Env.requestPerm, Env.oraclePerm, Equiv.prodCongr_apply,
        Prod.map, copyPerm_apply, respondPerm_apply, queryPermOf_apply,
        gameRegEquiv, Equiv.refl_apply, hw', hw'', Bool.false_eq_true, ↓reduceIte]
      refine Prod.ext rfl ?_
      funext j
      simp [Env.oracle_comapReq]
  · rfl

theorem stage_mapReq (ω : Ω) : ∀ k,
    (D.mapReq e).stage E ω k = relabelOp (gameRegEquiv e) (D.stage (E.comapReq e) ω k)
  | 0 => by
    rw [stage, stage, hybrid_zero, hybrid_zero, gameInit_mapReq, liftedStep_mapReq]
  | k + 1 => by
    rw [stage_succ, stage_succ, stage_mapReq ω k,
      permOp_relabelOp _ (fun r => D.eventPerm_mapReq e E ω k r), liftedStep_mapReq]

theorem final_mapReq
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)) (ω : Ω) :
    (D.mapReq e).final E (mapPost e post) ω =
      relabelOp (gameRegEquiv e) (D.final (E.comapReq e) post ω) := by
  rw [final, final, run, run, stage_mapReq]
  refine logControlled_relabelOp e (fun lg w => ?_) _
  rw [Env.oracle_comapReq]
  simp [mapPost]

theorem acceptProbAt_mapReq
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)) (ω : Ω) :
    (D.mapReq e).acceptProbAt E (mapPost e post) ω = D.acceptProbAt (E.comapReq e) post ω := by
  rw [acceptProbAt, acceptProbAt, final_mapReq, prob_relabelOp]
  congr 1
  ext r
  simp [gameAccept, splitLogs_gameRegEquiv, mapReq]

/-- **The relabelled distinguisher against `E` is the distinguisher against `E.comapReq e`.** -/
theorem acceptProb_mapReq [Fintype Ω]
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)) :
    (D.mapReq e).acceptProb E (mapPost e post) = D.acceptProb (E.comapReq e) post := by
  simp only [acceptProb, acceptProbAt_mapReq]
  rfl

variable {D}

/-- **The relabelled distinguisher keeps the query budget.** -/
def Budget.mapReq {q : ℕ} (b : D.Budget q) : (D.mapReq e).Budget q where
  inv := b.inv
  init hm := by
    have h : (D.mapReq e).step 0 (D.mapReq e).init = relabelOp (dregEquiv e) (D.step 0 D.init) := by
      simp [Distinguisher.mapReq]
    rw [h, supported_relabelOp_iff]
    exact b.init hm
  step k hk c bk v hv := by
    change Supported _ (relabelOp (dregEquiv e) (D.step ⟨k + 1, by omega⟩
      (relabelOp (dregEquiv e).symm v)))
    rw [supported_relabelOp_iff]
    exact b.step k hk c bk _ (supported_relabelOp_iff.2 hv)
  cap := b.cap

end Distinguisher

end GordieHowe.Quantum
