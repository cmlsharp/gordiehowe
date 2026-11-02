-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.CompressedSimReq
public import GordieHowe.Model.RingSignature.Adversary
public import GordieHowe.Model.Quantum.Interactive.MultiRelay
public import GordieHowe.Model.Quantum.Interactive.FromDistinguisher
public import GordieHowe.Model.Quantum.Interactive.BaseShift
public import GordieHowe.Model.Quantum.Interactive.BaseShiftSteps
public import GordieHowe.Model.Quantum.Interactive.CoSimSchedule

@[expose] public section

set_option linter.unusedSectionVars false

/-!
# The simulating distinguisher with real queries

A query algorithm with request points (`Quantum.ReqQueryAlg`) over the oracle `X → BitStr I J`,
whose steps are read after lists of *query points* (`StepAdds` on its query registers, every
addition on every branch, `StepAdds.AllOn`): before step `k`, the values `H (x k i p)` of a real
oracle `H : X → Y` added in sequence to the parts `L k i` of the query registers. The
distinguisher `coSimQ` holds the compressed-oracle simulation of the algorithm in its workspace,
sends the request points to a real challenger and makes a real query at each query point: per
step `k`, a request slot followed by `nb k` query slots (`CoSimSchedule`), the kind read from a
phase bit. Its run is the embedding at rest of `|Sim*⟩` of the instance of the algorithm read after
the query points at `H` (`run_coSimQ`); as an adversary (`advQ`) it makes `Σ nb` queries
(`queries_advQ`), keeps its budget against every challenger (`withinBudget_advQ`), and its law is
the coin average of the Born weights of `|Sim*⟩` (`toOuterMeasure_outLaw_advQ`).

- `WD`, `DD`, `RestD`, `splitD`, `liftSimD`, `setReqD`, `storeD`, `writeD`, `loadD`, `flipD`, and
  their `_apply` lemmas: the registers and their permutations.
- `restBlankD`, `initD`, `norm_initD`, `finishD`, `reqStepD`, `qryStepD`, `stepQ`, `coSimQ`,
  `stepQ_zero`, `stepQ_req`, `stepQ_qry`: the initial vector, the steps and the distinguisher.
- `GQ`, `RestQ`, `sigmaQ`, `liftG`, `restOf`, `iotaD`, `iotaD_injective`, `liftG_flipD_iotaD`,
  `logControlled_permOp`, `logControlled_liftSimD`, `logControlled_trans`, `logControlled_refl`,
  `iotaD_controlled`: the game registers and the embedding at rest.
- `wsLiftQ`, `wsLiftQ_mul`, `wsLiftQ_one`, `prefPerm`, `prefPerm_zero`, `prefPerm_succ`,
  `prefPerm_full`, `prefPerm_eq_perm`, `permOp_wsLiftQ_perm_of_nb`, `reqSlot`, `request_round`,
  `query_round`: the rounds on basis states.
- `oracleIn_reprogram_toPureEnv`, `oracle_toPureEnv`, `answer_spread_toPureEnv`: the challenger's
  environment on the spread logs.
- `Distinguisher.gameInit_eq`, `gameInit_coSimQ`, `simStep_withPerm_ws`, `liftedStep_coSimQ`,
  `finish_vEmb`, `query_load_vEmb`, `stage_qry`, `stage_block`, `stage_start`, `run_coSimQ`: the run.
- `kindAt`, `kindAt_start`, `kindAt_qry`, `kindAt_next`, `slot_cases`, `slotSet`, `slotSet'`,
  `queriesBefore_of_starts`, `slotSet_subset_budgetAt`, `KeepsPhase`, `KeepsPhase.trans`,
  `keepsPhase_refl`, `keepsPhase_permOp`, `keepsPhase_liftSimD`, `keepsPhase_finishD`,
  `logControlled_flip`, `logControlled_keep`, `logControlled_flipD`, `liftedStep_slotSet`,
  `eventPerm_slotSet`, `stage_zero_slotSet`, `stage_slotSet`: the budget against every
  environment.
- `outQ`, `advQ`, `output_emb_iotaD`, `history_emb_iotaD`, `toOuterMeasure_outLaw_advQ`,
  `withinBudget_advQ`, `tracePreserving_advQ`, `queries_advQ`: the adversary and its law.
- `noAdds`, `noAdds_allOn`, `withPerm_noAdds`, `coSimAdv`, `coSimAdv_tracePreserving`,
  `coSimAdv_withinBudget`, `coSimAdv_slots`, `coSimAdv_queries`,
  `toOuterMeasure_outLaw_coSimAdv_history`: the simulating adversary without query points, a
  request slot per step of `G` and no query.
-/

open Matrix
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

namespace ReqQueryAlg

open GordieHowe.QROM CoSimSchedule

variable {m t : ℕ} {I J B Req Resp O : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Inhabited Req]
  (e : BitStr I J ≃ B) (G : ReqQueryAlg (Bits m) (BitStr I J) Req Resp t O)
  (Y : Type) [Fintype Y] [DecidableEq Y] [AddGroup Y]

/-! ### The registers of the distinguisher -/

/-- The workspace of the distinguisher: `G`'s simulation register, the store of the replies, and
the phase (`true` before a request slot, `false` before a query slot). A named type, so that instance
search over the registers stops at its own instances (design rule R2). -/
def WD : Type := G.SimW (I := I) (J := J) (m := m) × Bool

/-- The registers of the distinguisher. -/
abbrev DD : Type := DReg (WD G) 1 (Bits m) Y Req Resp

/-- The other registers beside the simulation register. -/
abbrev RestD : Type :=
  ((Fin (t + 1) → Option Resp) × Bool) × (Req × Option Resp) × (Fin 1 → Bits m × Y)

instance WD.instFintype : Fintype (WD (I := I) (J := J) (m := m) G) :=
  inferInstanceAs (Fintype (G.SimW (I := I) (J := J) (m := m) × Bool))

instance WD.instDecidableEq : DecidableEq (WD (I := I) (J := J) (m := m) G) :=
  inferInstanceAs (DecidableEq (G.SimW (I := I) (J := J) (m := m) × Bool))

/-- A workspace is its simulation part and its phase. -/
@[simp] theorem WD.eta (w : WD (I := I) (J := J) (m := m) G) :
    ((w.1, w.2) : WD (I := I) (J := J) (m := m) G) = w :=
  rfl

instance DD.instFintype : Fintype (DD (I := I) (J := J) (m := m) G Y) := instFintypeProd _ _

instance RestD.instFintype : Fintype (RestD (t := t) (Resp := Resp) (Req := Req) (m := m) Y) :=
  instFintypeProd _ _

instance RestD.instDecidableEq :
    DecidableEq (RestD (t := t) (Resp := Resp) (Req := Req) (m := m) Y) :=
  instDecidableEqProd

instance DD.instFintypeSplit :
    Fintype (SimRegister G.W I J m t × RestD (t := t) (Resp := Resp) (Req := Req) (m := m) Y) :=
  instFintypeProd _ _

/-- The registers as the simulation register and the others. -/
def splitD : DD (I := I) (J := J) (m := m) G Y ≃
    SimRegister G.W I J m t × RestD (t := t) (Resp := Resp) (Req := Req) (m := m) Y where
  toFun d := (d.1.1.1.1, ((d.1.1.1.2, d.1.1.2), (d.1.2.1, d.1.2.2), d.2))
  invFun p := ((((p.1, p.2.1.1), p.2.1.2), p.2.2.1.1, p.2.2.1.2), p.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A unitary of the simulation register with the identity on the other registers. -/
noncomputable def liftSimD
    (V : QState (SimRegister G.W I J m t) ≃ₗᵢ[ℂ] QState (SimRegister G.W I J m t)) :
    QState (DD (I := I) (J := J) (m := m) G Y) ≃ₗᵢ[ℂ] QState (DD (I := I) (J := J) (m := m) G Y) :=
  (relabel (splitD G Y)).trans ((controlled fun _ => V).trans (relabel (splitD G Y).symm))

/-- The request register set to (or cleared from) the request of the request point `k`. -/
def setReqD (k : Fin (t + 1)) : Equiv.Perm (DD (I := I) (J := J) (m := m) G Y) :=
  Function.Involutive.toPerm
    (fun d => ((d.1.1, Equiv.swap default (G.req k d.1.1.1.1.1.1) d.1.2.1, d.1.2.2), d.2))
    fun d => by simp

/-- The response register swapped with the store of the request point `k`. -/
def storeD (k : Fin (t + 1)) : Equiv.Perm (DD (I := I) (J := J) (m := m) G Y) :=
  Function.Involutive.toPerm
    (fun d => ((((d.1.1.1.1, Function.update d.1.1.1.2 k d.1.2.2), d.1.1.2), d.1.2.1,
      d.1.1.1.2 k), d.2))
    fun d => by
      obtain ⟨⟨⟨⟨sw, st⟩, ph⟩, q, rs⟩, qs⟩ := d
      simp

/-- The stored reply of the request point `k` written into `G`'s work register. -/
def writeD (k : Fin (t + 1)) : Equiv.Perm (DD (I := I) (J := J) (m := m) G Y) where
  toFun d := ((((((G.write k (d.1.1.1.2 k) d.1.1.1.1.1.1, d.1.1.1.1.1.2), d.1.1.1.1.2),
    d.1.1.1.2), d.1.1.2), d.1.2), d.2)
  invFun d := (((((((G.write k (d.1.1.1.2 k)).symm d.1.1.1.1.1.1, d.1.1.1.1.1.2), d.1.1.1.1.2),
    d.1.1.1.2), d.1.1.2), d.1.2), d.2)
  left_inv d := by simp
  right_inv d := by simp

variable {G Y} (P : StepAdds (QueryReg G.W 1 (Bits m) (BitStr I J)) (Fin (t + 1)) (Bits m) Y)

/-- **The load (and unload) of query point `i` of step `k`**: the point copied into the blank
query input, the answer part swapped with the query answer. -/
def loadD (k : Fin (t + 1)) (i : Fin (P.nb k)) : Equiv.Perm (DD (I := I) (J := J) (m := m) G Y) :=
  Function.Involutive.toPerm
    (fun d => ((((((P.L k i).set d.1.1.1.1.1 (d.2 0).2, d.1.1.1.1.2), d.1.1.1.2), d.1.1.2),
        d.1.2),
      fun _ => (Equiv.swap default (P.x k i d.1.1.1.1.1) (d.2 0).1, (P.L k i).get d.1.1.1.1.1)))
    fun d => by
      obtain ⟨⟨⟨⟨⟨p, sl⟩, st⟩, ph⟩, rq⟩, qs⟩ := d
      simp only [RegLens.get_set, RegLens.set_set, RegLens.set_get, P.x_set k i _ _,
        Equiv.swap_apply_self]
      congr 1
      funext i
      rw [Subsingleton.elim i 0]

variable (G Y)

/-- The phase flipped. -/
def flipD : Equiv.Perm (DD (I := I) (J := J) (m := m) G Y) :=
  Function.Involutive.toPerm (fun d => (((d.1.1.1, !d.1.1.2), d.1.2), d.2)) fun d => by simp

/-! ### The permutations on basis states -/

section Apply

variable (d : DD (I := I) (J := J) (m := m) G Y) (k : Fin (t + 1))

theorem setReqD_apply : setReqD G Y k d =
    ((d.1.1, Equiv.swap default (G.req k d.1.1.1.1.1.1) d.1.2.1, d.1.2.2), d.2) :=
  rfl

theorem storeD_apply : storeD G Y k d =
    ((((d.1.1.1.1, Function.update d.1.1.1.2 k d.1.2.2), d.1.1.2), d.1.2.1, d.1.1.1.2 k), d.2) :=
  rfl

theorem writeD_apply : writeD G Y k d =
    ((((((G.write k (d.1.1.1.2 k) d.1.1.1.1.1.1, d.1.1.1.1.1.2), d.1.1.1.1.2), d.1.1.1.2),
      d.1.1.2), d.1.2), d.2) :=
  rfl

theorem flipD_apply : flipD G Y d = (((d.1.1.1, !d.1.1.2), d.1.2), d.2) :=
  rfl

theorem loadD_apply (i : Fin (P.nb k)) : loadD P k i d =
    ((((((P.L k i).set d.1.1.1.1.1 (d.2 0).2, d.1.1.1.1.2), d.1.1.1.2), d.1.1.2), d.1.2),
      fun _ => (Equiv.swap default (P.x k i d.1.1.1.1.1) (d.2 0).1, (P.L k i).get d.1.1.1.1.1)) :=
  rfl

end Apply

/-! ### The distinguisher -/

/-- The other registers blank: an empty store, the phase at a request, the blank request, no
response, a blank query pair. -/
def restBlankD : RestD (t := t) (Resp := Resp) (Req := Req) (m := m) Y :=
  ((fun _ => none, true), (default, none), fun _ => (default, 0))

/-- **The initial vector of the distinguisher**: `G`'s initial state with the empty database, the
other registers blank. -/
noncomputable def initD : QState (DD (I := I) (J := J) (m := m) G Y) :=
  relabel (splitD G Y).symm (tensorKet (simInitG e G) (restBlankD Y))

theorem norm_initD : ‖initD e G Y‖ = 1 := by
  rw [initD, LinearIsometryEquiv.norm_map, norm_tensorKet, simInitG, norm_tensorKet, G.norm_init]

/-- **The end of step `k`**: `G`'s step `k`, then the simulated query and the request of the
request point `k + 1` set (none after the last step). -/
noncomputable def finishD (k : Fin (t + 1)) : QState (DD (I := I) (J := J) (m := m) G Y) ≃ₗᵢ[ℂ]
    QState (DD (I := I) (J := J) (m := m) G Y) :=
  (liftSimD G Y (stepSim G k)).trans
    (if h : (k : ℕ) < t then (liftSimD G Y (simQueryIso e G.W)).trans
        (permOp (setReqD G Y ⟨k + 1, by omega⟩))
      else LinearIsometryEquiv.refl ℂ _)

variable {G Y}

/-- **The step after the request slot of step `k`**: the request cleared, the reply stored and
written; then query point `0` loaded and the phase flipped, or, without query points, the end of
step `k`. -/
noncomputable def reqStepD (k : Fin (t + 1)) : QState (DD (I := I) (J := J) (m := m) G Y) ≃ₗᵢ[ℂ]
    QState (DD (I := I) (J := J) (m := m) G Y) :=
  (permOp (setReqD G Y k)).trans ((permOp (storeD G Y k)).trans ((permOp (writeD G Y k)).trans
    (if h : 0 < P.nb k then (permOp (loadD P k ⟨0, h⟩)).trans (permOp (flipD G Y))
      else finishD e G Y k)))

/-- **The step after query slot `i` of step `k`**: query point `i` unloaded; then query point
`i + 1` loaded, or, after the last, the end of step `k` and the phase flipped. -/
noncomputable def qryStepD (k : Fin (t + 1)) (i : Fin (P.nb k)) :
    QState (DD (I := I) (J := J) (m := m) G Y) ≃ₗᵢ[ℂ] QState (DD (I := I) (J := J) (m := m) G Y) :=
  (permOp (loadD P k i)).trans
    (if h : (i : ℕ) + 1 < P.nb k then permOp (loadD P k ⟨i + 1, h⟩)
      else (finishD e G Y k).trans (permOp (flipD G Y)))

/-- **The step after slot `j - 1`** of the distinguisher (`step 0` first): before slot `0`, the
request of the request point `0` set; after a request slot, `reqStepD`; after a query slot,
`qryStepD`. -/
noncomputable def stepQ : ℕ → (QState (DD (I := I) (J := J) (m := m) G Y) ≃ₗᵢ[ℂ]
    QState (DD (I := I) (J := J) (m := m) G Y))
  | 0 => permOp (setReqD G Y 0)
  | j + 1 =>
    if (j : ℕ) = slotStart P.nb (slotBlock P.nb j) then
      reqStepD e P ⟨slotBlock P.nb j, Nat.lt_succ_of_le (slotBlock_le _ _)⟩
    else if h : j - slotStart P.nb (slotBlock P.nb j) - 1 <
        P.nb ⟨slotBlock P.nb j, Nat.lt_succ_of_le (slotBlock_le _ _)⟩ then
      qryStepD e P ⟨slotBlock P.nb j, Nat.lt_succ_of_le (slotBlock_le _ _)⟩
        ⟨j - slotStart P.nb (slotBlock P.nb j) - 1, h⟩
    else LinearIsometryEquiv.refl ℂ _

/-- **The simulating distinguisher with real queries**: workspace `WD`, one query register, per
step `k` of `G` a request slot and `nb k` query slots (the kind read from the phase), the initial
vector `initD`, the steps `stepQ`. -/
noncomputable def coSimQ : Distinguisher (WD (I := I) (J := J) (m := m) G) (Bits m) Y Req Resp 1
    (slotTotal P.nb) where
  kind w := w.2
  init := initD e G Y
  norm_init := norm_initD e G Y
  step j := stepQ e P j
  accept := Set.univ

theorem stepQ_zero : stepQ e P 0 = permOp (setReqD G Y 0) := rfl

/-- The step after the request slot of step `k`. -/
theorem stepQ_req (k : Fin (t + 1)) : stepQ e P (slotStart P.nb k + 1) = reqStepD e P k := by
  have hb : slotBlock P.nb (slotStart P.nb k) = k := by
    simpa using slotBlock_eq P.nb (Nat.le_of_lt_succ k.2) (o := 0) (Nat.zero_le _)
  simp only [stepQ, hb, ↓reduceIte]

/-- The step after query slot `i` of step `k`. -/
theorem stepQ_qry (k : Fin (t + 1)) (i : Fin (P.nb k)) :
    stepQ e P (slotStart P.nb k + 1 + i + 1) = qryStepD e P k i := by
  have hb : slotBlock P.nb (slotStart P.nb k + 1 + i) = k := by
    rw [show slotStart P.nb k + 1 + (i : ℕ) = slotStart P.nb k + (1 + i) by omega]
    exact slotBlock_eq P.nb (Nat.le_of_lt_succ k.2) (by rw [nbAt_fin]; omega)
  have hne : slotStart P.nb k + 1 + (i : ℕ) ≠ slotStart P.nb k := by omega
  have ho : slotStart P.nb k + 1 + (i : ℕ) - slotStart P.nb k - 1 = i := by omega
  have hcongr : ∀ (k' : Fin (t + 1)) (hk : k' = k) (i' : Fin (P.nb k')) (hi : (i' : ℕ) = i),
      qryStepD e P k' i' = qryStepD e P k i := by
    rintro _ rfl i' hi
    rw [Fin.ext hi]
  simp only [stepQ, hb, hne, ↓reduceIte]
  split
  · exact hcongr _ (Fin.ext hb) _ (by simp only; omega)
  · rename_i h
    exact absurd (by simp only [Fin.eta, ho]; exact i.2) h

/-! ### The game registers and the embedding at rest -/

variable (G Y) (M : ℕ)

/-- The game registers of a distinguisher with `M` slots on the registers `DD`. -/
abbrev GQ : Type := GameReg (WD (I := I) (J := J) (m := m) G) 1 (Bits m) Y Req Resp M

/-- The game registers other than the simulation register. -/
abbrev RestQ : Type :=
  (((Fin (t + 1) → Option Resp) × Bool) × Req × Option Resp × LogReg Req M) ×
    (Fin 1 → Bits m × Y)

instance GQ.instFintype : Fintype (GQ (I := I) (J := J) (m := m) G Y M) := instFintypeProd _ _

instance RestQ.instFintype : Fintype (RestQ (t := t) (Resp := Resp) (Req := Req) (m := m) Y M) :=
  instFintypeProd _ _

instance RestQ.instDecidableEq :
    DecidableEq (RestQ (t := t) (Resp := Resp) (Req := Req) (m := m) Y M) :=
  instDecidableEqProd

instance GQ.instFintypeSplit :
    Fintype (SimRegister G.W I J m t × RestQ (t := t) (Resp := Resp) (Req := Req) (m := m) Y M) :=
  instFintypeProd _ _

/-- The game registers as the simulation register and the others. -/
def sigmaQ : GQ (I := I) (J := J) (m := m) G Y M ≃
    SimRegister G.W I J m t × RestQ (t := t) (Resp := Resp) (Req := Req) (m := m) Y M where
  toFun r := (r.1.1.1.1, (((r.1.1.1.2, r.1.1.2), r.1.2), r.2))
  invFun p := ((((p.1, p.2.1.1.1), p.2.1.1.2), p.2.1.2), p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem sigmaQ_symm_apply
    (p : SimRegister G.W I J m t × RestQ (t := t) (Resp := Resp) (Req := Req) (m := m) Y M) :
    (sigmaQ G Y M).symm p =
      ((((((p.1, p.2.1.1.1), p.2.1.1.2) : WD (I := I) (J := J) (m := m) G), p.2.1.2), p.2.2) :
        GQ (I := I) (J := J) (m := m) G Y M) :=
  rfl

variable {G Y M}

/-- A permutation of the distinguisher's registers on the game registers (the identity on the
logs). -/
def liftG (π : Equiv.Perm (DD (I := I) (J := J) (m := m) G Y)) :
    Equiv.Perm (GQ (I := I) (J := J) (m := m) G Y M) :=
  (splitLogs.trans (π.prodCongr (Equiv.refl _))).trans splitLogs.symm

variable (nb : Fin (t + 1) → ℕ) (a : ℕ → Req → Option Resp)

/-- The other game registers at rest, for the logs `lg` and the phase `φ`: the replies of the logs
in the store (`storeOf`), the blank request, no response, the logs spread over the slots of the
schedule `nb`, the blank query pair. -/
def restOf (φ : Bool) (lg : LogReg Req (t + 1)) :
    RestQ (t := t) (Resp := Resp) (Req := Req) (m := m) Y (slotTotal nb) :=
  (((storeOf a lg, φ), default, none, spreadAt nb lg), fun _ => (default, 0))

variable (G Y)

/-- **The game basis state at rest of a basis state of the instance's simulation register**, at
the phase `φ`. -/
def iotaD (φ : Bool) (b : SimRegister (G.W × LogReg Req (t + 1)) I J m t) :
    GQ (I := I) (J := J) (m := m) G Y (slotTotal nb) :=
  (sigmaQ G Y (slotTotal nb)).symm ((wsSplit G.W (LogReg Req (t + 1)) b).1,
    restOf nb a φ (wsSplit G.W (LogReg Req (t + 1)) b).2)

variable {G Y}

theorem iotaD_injective (φ : Bool) : Function.Injective (iotaD G Y nb a φ) := by
  intro b b' h
  have h' := congrArg (sigmaQ G Y (slotTotal nb)) h
  simp only [iotaD, Equiv.apply_symm_apply, Prod.mk.injEq] at h'
  apply (wsSplit G.W (LogReg Req (t + 1))).injective
  refine Prod.ext h'.1 (spreadAt_injective nb ?_)
  have := congrArg (fun p : RestQ (t := t) (Resp := Resp) (Req := Req) (m := m) Y (slotTotal nb) =>
    p.1.2.2.2) h'.2
  exact this

/-- The phase flipped at rest. -/
theorem liftG_flipD_iotaD (φ : Bool) (b : SimRegister (G.W × LogReg Req (t + 1)) I J m t) :
    liftG (flipD G Y) (iotaD G Y nb a φ b) = iotaD G Y nb a (!φ) b :=
  rfl

/-! ### The steps on the game registers -/

theorem logControlled_permOp (π : Equiv.Perm (DD (I := I) (J := J) (m := m) G Y))
    (v : QState (GQ (I := I) (J := J) (m := m) G Y M)) :
    logControlled (fun _ => permOp π) v = permOp (liftG π) v := by
  ext r
  rfl

theorem logControlled_liftSimD
    (U : QState (SimRegister G.W I J m t) ≃ₗᵢ[ℂ] QState (SimRegister G.W I J m t))
    (v : QState (GQ (I := I) (J := J) (m := m) G Y M)) :
    logControlled (fun _ => liftSimD G Y U) v =
      relabel (sigmaQ G Y M).symm (controlled (fun _ => U) (relabel (sigmaQ G Y M) v)) := by
  ext r
  rfl

theorem logControlled_trans
    (A₁ A₂ : QState (DD (I := I) (J := J) (m := m) G Y) ≃ₗᵢ[ℂ]
      QState (DD (I := I) (J := J) (m := m) G Y))
    (v : QState (GQ (I := I) (J := J) (m := m) G Y M)) :
    logControlled (fun _ => A₁.trans A₂) v =
      logControlled (fun _ => A₂) (logControlled (fun _ => A₁) v) := by
  ext r
  rfl

theorem logControlled_refl {W' X' Y' Req' A' : Type} [Fintype W'] [Fintype X'] [Fintype Y']
    [Fintype Req'] [Fintype A'] {n' M' : ℕ} (v : QState (GameReg W' n' X' Y' Req' A' M')) :
    logControlled (fun _ => LinearIsometryEquiv.refl ℂ (QState (DReg W' n' X' Y' Req' A'))) v =
      v := by
  ext r
  rfl

/-- A unitary of the simulation register commutes with the embedding at rest. -/
theorem iotaD_controlled (φ : Bool)
    (V : QState (SimRegister G.W I J m t) ≃ₗᵢ[ℂ] QState (SimRegister G.W I J m t))
    (v : QState (SimRegister (G.W × LogReg Req (t + 1)) I J m t)) :
    relabel (sigmaQ G Y (slotTotal nb)).symm (controlled (fun _ => V)
      (relabel (sigmaQ G Y (slotTotal nb)) (vEmb (iotaD G Y nb a φ) v))) =
      vEmb (iotaD G Y nb a φ) (relabel (wsSplit G.W (LogReg Req (t + 1))).symm
        (controlled (fun _ => V) (relabel (wsSplit G.W (LogReg Req (t + 1))) v))) :=
  controlled_vEmb (sigmaQ G Y (slotTotal nb)) (wsSplit G.W (LogReg Req (t + 1)))
    (restOf nb a φ) V v

/-! ### One round on basis states -/

/-- A permutation of `G`'s query registers on the instance's simulation register. -/
def wsLiftQ (π : Equiv.Perm (QueryReg G.W 1 (Bits m) (BitStr I J))) :
    Equiv.Perm (SimRegister (G.W × LogReg Req (t + 1)) I J m t) :=
  (wsSplit G.W (LogReg Req (t + 1))).trans
    (((π.prodCongr (Equiv.refl _)).prodCongr (Equiv.refl _)).trans
      (wsSplit G.W (LogReg Req (t + 1))).symm)

theorem wsLiftQ_mul (π σ : Equiv.Perm (QueryReg G.W 1 (Bits m) (BitStr I J))) :
    wsLiftQ (Req := Req) (π * σ) = wsLiftQ π * wsLiftQ σ :=
  Equiv.ext fun _ => rfl

theorem wsLiftQ_one : wsLiftQ (G := G) (Req := Req) (I := I) (J := J) 1 = 1 :=
  Equiv.ext fun _ => rfl

variable (H : Bits m → Y)

/-- **The first `i` query points of step `k` at `H`**, in sequence. -/
def prefPerm (k : Fin (t + 1)) (i : ℕ) (hi : i ≤ P.nb k) :
    Equiv.Perm (QueryReg G.W 1 (Bits m) (BitStr I J)) :=
  seqPerm i fun i' => (P.add H k (Fin.castLE hi i')).perm

theorem prefPerm_zero (k : Fin (t + 1)) : prefPerm P H k 0 (Nat.zero_le _) = 1 := rfl

theorem prefPerm_succ (k : Fin (t + 1)) (i : Fin (P.nb k)) :
    prefPerm P H k (i + 1) i.2 = (P.add H k i).perm * prefPerm P H k i i.2.le := by
  simp only [prefPerm, seqPerm]
  congr 1

theorem prefPerm_full (k : Fin (t + 1)) : prefPerm P H k (P.nb k) le_rfl = P.perm H k :=
  rfl

variable (a : ℕ → Req → Option Resp)

/-- The request slot of step `k`. -/
abbrev reqSlot (nb : Fin (t + 1) → ℕ) (k : Fin (t + 1)) : Fin (slotTotal nb) :=
  ⟨slotStart nb k, slotStart_lt_total nb (Nat.le_of_lt_succ k.2)⟩

variable {Ω St : Type} {Q : ℕ} [OracleState St (Bits m) Y] (E : Env Ω Req Resp (Bits m) Y Q St)
  (ω : Ω)

/-- **A request round on basis states**: from the basis state at rest of a basis state of the
instance whose logs are filled exactly below `k`, at a request phase, with the request of `k`
set: the request slot (`eventPerm`: the copy into the log, the reply), then the request cleared
and the reply stored and written give the basis state at rest of the instance's request point. -/
theorem request_round (k : Fin (t + 1))
    (hans : ∀ (lg : LogReg Req (t + 1)) (w : G.W), LogsAt k lg →
      E.answer ω (Function.update (spreadAt P.nb lg) (reqSlot P.nb k) (some (G.req k w)))
        (reqSlot P.nb k) = a k (G.req k w))
    (b : SimRegister (G.W × LogReg Req (t + 1)) I J m t)
    (hb : LogsAt k (wsSplit G.W (LogReg Req (t + 1)) b).2) :
    liftG (writeD G Y k) (liftG (storeD G Y k) (liftG (setReqD G Y k)
      ((coSimQ e P).eventPerm E ω (slotStart P.nb k)
        (liftG (setReqD G Y k) (iotaD G Y P.nb a true b))))) =
      iotaD G Y P.nb a true (reqPermSim G a k b) := by
  obtain ⟨⟨⟨w, lg⟩, qs⟩, sl⟩ := b
  have hk : lg k = none := LogsAt.eq_none hb
  have hA := hans lg w hb
  have hlt : slotStart P.nb k < slotTotal P.nb := slotStart_lt_total P.nb (Nat.le_of_lt_succ k.2)
  have hsk : spreadAt P.nb lg (reqSlot P.nb k) = none := by
    rw [spreadAt_start, hk]
  have hs : storeOf a lg k = none := by simp [storeOf, hk]
  simp only [Distinguisher.eventPerm, dif_pos hlt]
  simp only [liftG, iotaD, sigmaQ_symm_apply, restOf, wsSplit, reqPermSim, ReqQueryAlg.reqPerm,
    Env.requestPerm, Env.oraclePerm, copyPerm_apply, respondPerm_apply, queryPermOf_apply,
    setReqD_apply, storeD_apply, writeD_apply, splitLogs, coSimQ, Equiv.trans_apply,
    Equiv.prodCongr_apply, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Equiv.coe_refl, Prod.map, id,
    Equiv.swap_apply_left, hk, hsk, Equiv.swap_apply_right, ite_true]
  simp only [hA, storeOf_update, hs, spreadAt_update, Function.update_self, ↓reduceIte, zero_add,
    Pi.zero_apply]

variable {P} (hP : P.AllOn)

include hP in
/-- **A query round on basis states**: from the basis state at rest at a query phase with query
point `i` of step `k` loaded, the query slot (`eventPerm`: the oracle `H` on the query pair) and
the unload give the basis state at rest of query point `i` of step `k` at `H`. -/
theorem query_round (horc : ∀ lg : LogReg Req (slotTotal P.nb), E.oracle ω lg = H)
    (k : Fin (t + 1)) (i : Fin (P.nb k)) (b : SimRegister (G.W × LogReg Req (t + 1)) I J m t) :
    liftG (loadD P k i) ((coSimQ e P).eventPerm E ω (slotStart P.nb k + 1 + i)
      (liftG (loadD P k i) (iotaD G Y P.nb a false b))) =
      iotaD G Y P.nb a false (wsLiftQ (P.add H k i).perm b) := by
  obtain ⟨⟨⟨w, lg⟩, qs⟩, sl⟩ := b
  have hlt : slotStart P.nb k + 1 + i < slotTotal P.nb := by
    have := slotStart_add_lt_total P.nb (Nat.le_of_lt_succ k.2) (o := 1 + i)
      (by rw [nbAt_fin]; omega)
    omega
  have hf : (P.add H k i).f (w, qs) = H (P.x k i (w, qs)) := StepAdds.add_of_allOn H hP k i _
  simp only [Distinguisher.eventPerm, dif_pos hlt]
  simp only [liftG, iotaD, sigmaQ_symm_apply, restOf, wsSplit, wsLiftQ, Env.requestPerm, Env.oraclePerm,
    copyPerm_apply, respondPerm_apply, queryPermOf_apply, loadD_apply, splitLogs, coSimQ,
    Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
    Equiv.coe_refl, Prod.map, id, Bool.false_eq_true, ↓reduceIte, horc, Equiv.swap_apply_left,
    RegLens.get_set, RegLens.set_set, P.x_set k i _ _, Equiv.swap_apply_right,
    RegAdd.perm_apply]
  rw [← hf]
  rfl

/-! ### The challenger's environment on the spread logs -/

variable [Nonempty Y]

/-- **A challenger without assignments keeps the oracle after any requests**: the reprogrammed
base oracle in force after the requests `rs` is `H`. -/
theorem oracleIn_reprogram_toPureEnv (C₂ : Challenger (Bits m) Y Req Resp)
    (hna : ∀ c (hist : List (HistoryEntry Req Resp)) r (H' : Bits m → Y),
      ((C₂.respond c hist r).run H').assignments = [])
    (H : Bits m → Y) (c : C₂.Coins) (rs : List Req) :
    ((C₂.toPureEnv.oracleIn (H, c) rs).base).reprogram (C₂.toPureEnv.oracleIn (H, c) rs).ass =
      H := by
  have hass : ∀ rs : List Req, (C₂.toPureEnv.oracleIn (H, c) rs).ass = [] := by
    intro rs
    induction rs using List.reverseRecOn with
    | nil => rfl
    | append_singleton rs r ih =>
      rw [Env.oracleIn_append_singleton, Env.update]
      split_ifs
      · change (C₂.toPureEnv.oracleIn (H, c) rs).ass ++ _ = []
        rw [ih, hna, List.append_nil]
      · exact ih
  rw [hass, C₂.stateAfter_base H c rs]
  rfl

/-- **A challenger without assignments keeps the oracle**: the oracle in force after any requests
is `H`. -/
theorem oracle_toPureEnv (C₂ : Challenger (Bits m) Y Req Resp)
    (hna : ∀ c (hist : List (HistoryEntry Req Resp)) r (H' : Bits m → Y),
      ((C₂.respond c hist r).run H').assignments = [])
    (H : Bits m → Y) (c : C₂.Coins) {M : ℕ} (lg : LogReg Req M) :
    C₂.toPureEnv.oracle (H, c) lg = H :=
  oracleIn_reprogram_toPureEnv C₂ hna H c (requests lg)

variable (P) in
/-- **The challenger's environment answers the request of the request slot of step `k` by
`aC c k`**, at logs filled exactly below `k`, for a challenger without assignments answering by
`aC` at the oracle `H`. -/
theorem answer_spread_toPureEnv (C₂ : Challenger (Bits m) Y Req Resp)
    (aC : C₂.Coins → ℕ → Req → Option Resp) (hR : t + 1 ≤ C₂.Q)
    (hdet : ∀ c (k : Fin (t + 1)) (hist : List (HistoryEntry Req Resp)) (w : G.W),
      hist.length = k → (C₂.respond c hist (G.req k w)).run H = ⟨aC c k (G.req k w), []⟩)
    (hna : ∀ c (hist : List (HistoryEntry Req Resp)) r (H' : Bits m → Y),
      ((C₂.respond c hist r).run H').assignments = []) (c : C₂.Coins) (k : Fin (t + 1))
    (lg : LogReg Req (t + 1)) (w : G.W)
    (hlg : LogsAt k lg) :
    C₂.toPureEnv.answer (H, c) (Function.update (spreadAt P.nb lg) (reqSlot P.nb k)
      (some (G.req k w))) (reqSlot P.nb k) = aC c k (G.req k w) := by
  have hrb : requestsBefore (Function.update (spreadAt P.nb lg) (reqSlot P.nb k)
      (some (G.req k w))) (slotStart P.nb k) = requestsBefore lg k := by
    rw [requestsBefore_congr (lg' := spreadAt P.nb lg) fun k' hk' => ?_]
    · exact requestsBefore_spreadAt P.nb lg k (by omega)
    · refine Function.update_of_ne (fun h => ?_) _ _
      rw [h] at hk'
      simp at hk'
  have hlen : (requestsBefore lg k).length = k :=
    length_requestsBefore_of_logsAt (Nat.le_of_lt_succ (Nat.lt_succ_of_lt k.2)) hlg
  have hQ : (requestsBefore lg k).length < C₂.Q := by omega
  simp only [Env.answer, Function.update_self, Option.elim, hrb, Env.answerAfter, dif_pos hQ]
  have hh : (C₂.toPureEnv.oracleIn (H, c) (requestsBefore lg k)).hist.length = k := by
    have := C₂.stateAfter_hist_length H c (requestsBefore lg k)
    simp only [Challenger.stateAfter] at this
    rw [this, hlen]
    omega
  set st := C₂.toPureEnv.oracleIn (H, c) (requestsBefore lg k) with hst
  change ((C₂.respond c st.hist (G.req k w)).run (st.base.reprogram st.ass)).response = _
  rw [oracleIn_reprogram_toPureEnv C₂ hna H c _, hdet c k _ w hh]

/-! ### The run of the distinguisher -/

/-- **The initial game state is the initial vector with blank logs.** -/
theorem _root_.GordieHowe.Quantum.Distinguisher.gameInit_eq {W X Y Req A : Type} [Fintype W]
    [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] [DecidableEq Req] [DecidableEq A] {n M : ℕ}
    (D : Distinguisher W X Y Req A n M) :
    D.gameInit = relabel splitLogs.symm (tensorKet D.init (fun _ => none : LogReg Req M)) := by
  ext r
  rw [relabel_apply, Equiv.symm_symm, tensorKet_apply]
  simp only [Distinguisher.gameInit]
  split_ifs with h <;> simp

variable (P) in
/-- The initial game state of the distinguisher is the embedding at rest of the instance's
initial simulated state. -/
theorem gameInit_coSimQ :
    (coSimQ e P).gameInit = vEmb (iotaD G Y P.nb a true)
      (preV e (G.withPerm fun k => P.perm H k) a 0) := by
  rw [Distinguisher.gameInit_eq]
  have hD : (coSimQ e P).init = initD e G Y := rfl
  have h1 : preV e (G.withPerm fun k => P.perm H k) a 0 =
      vEmb (fun x : QueryReg G.W 1 (Bits m) (BitStr I J) =>
        ((G.logSplit (X := Bits m) (Y := BitStr I J)).symm (x, fun _ => none),
          dbSlots e t (∅ : DB (Bits m) B))) G.init := by
    have h2 : preV e (G.withPerm fun k => P.perm H k) a 0 =
        tensorKet (relabel (G.logSplit (X := Bits m) (Y := BitStr I J)).symm
          (tensorKet G.init (fun _ => none))) (dbSlots e t (∅ : DB (Bits m) B)) := by
      ext b
      rfl
    rw [h2, tensorKet_eq_vEmb, relabel_eq_vEmb, tensorKet_eq_vEmb, vEmb_vEmb, vEmb_vEmb]
    rfl
  rw [hD, initD, simInitG, h1, vEmb_vEmb, relabel_eq_vEmb, tensorKet_eq_vEmb, relabel_eq_vEmb,
    tensorKet_eq_vEmb, tensorKet_eq_vEmb, vEmb_vEmb, vEmb_vEmb, vEmb_vEmb, vEmb_vEmb]
  congr 1
  funext x
  have hs : spreadAt P.nb (fun _ => none : LogReg Req (t + 1)) = fun _ => none := by
    funext j
    simp [spreadAt]
  simp only [Function.comp_apply, iotaD, restOf, wsSplit, logSplit, Equiv.coe_fn_mk,
    Equiv.coe_fn_symm_mk, hs]
  rfl

variable (P) in
/-- **The instance's step with the query points** on its simulation register: the query points
of step `k` at `H`, then `G`'s step. -/
theorem simStep_withPerm_ws (k : Fin (t + 1))
    (v : QState (SimRegister (G.W × LogReg Req (t + 1)) I J m t)) :
    relabel (wsSplit G.W (LogReg Req (t + 1))).symm
        (controlled (fun _ => stepSim (G.withPerm fun k => P.perm H k) k)
          (relabel (wsSplit G.W (LogReg Req (t + 1))) v)) =
      relabel (wsSplit G.W (LogReg Req (t + 1))).symm (controlled (fun _ => stepSim G k)
        (relabel (wsSplit G.W (LogReg Req (t + 1))) (permOp (wsLiftQ (P.perm H k)) v))) := by
  ext b
  rfl

variable (P) in
theorem liftedStep_coSimQ (j : ℕ) (hj : j < slotTotal P.nb + 1)
    (v : QState (GQ (I := I) (J := J) (m := m) G Y (slotTotal P.nb))) :
    (coSimQ e P).liftedStep j v = logControlled (fun _ => stepQ e P j) v := by
  simp only [Distinguisher.liftedStep, Distinguisher.stepAt, dif_pos hj]
  rfl

/-- **The end of step `k` on the run**: from the embedding at rest of the instance's request point
`k` and its query points at `H`, `G`'s step `k` and the simulated query give the embedding at rest
of the instance's run before step `k + 1` with the request of `k + 1` set, and after the last step
`|Sim*⟩` of the instance. -/
theorem finish_vEmb (k : Fin (t + 1)) (φ : Bool) :
    logControlled (fun _ => finishD e G Y k) (vEmb (iotaD G Y P.nb a φ)
      (permOp (wsLiftQ (P.perm H k)) (permOp (reqPermSim G a k)
        (preV e (G.withPerm fun k => P.perm H k) a k)))) =
      if h : (k : ℕ) < t then vEmb (liftG (setReqD G Y ⟨k + 1, by omega⟩) ∘ iotaD G Y P.nb a φ)
        (preV e (G.withPerm fun k => P.perm H k) a (k + 1))
      else vEmb (iotaD G Y P.nb a φ) (simState e ((G.withPerm fun k => P.perm H k).inst a)) := by
  unfold finishD
  rw [logControlled_trans, logControlled_liftSimD, iotaD_controlled (V := stepSim G k),
    ← simStep_withPerm_ws P H k]
  split
  · rename_i hk
    have hp : preV e (G.withPerm fun k => P.perm H k) a (k + 1) =
        relabel (wsSplit G.W (LogReg Req (t + 1))).symm (controlled (fun _ => simQueryIso e G.W)
          (relabel (wsSplit G.W (LogReg Req (t + 1))) (relabel (wsSplit G.W (LogReg Req (t + 1))).symm
            (controlled (fun _ => stepSim (G.withPerm fun k => P.perm H k) k)
              (relabel (wsSplit G.W (LogReg Req (t + 1)))
                (permOp (reqPermSim G a k) (preV e (G.withPerm fun k => P.perm H k) a k))))))) := by
      have h1 := simQuery_prod e G.W (LogReg Req (t + 1))
        (simStage e ((G.withPerm fun k => P.perm H k).inst a) k)
      have h2 := simStage_eq_preV e (G.withPerm fun k => P.perm H k) a k
      have h3 := simStep_inst (G.withPerm fun k => P.perm H k) a k
        (preV e (G.withPerm fun k => P.perm H k) a k)
      change simQuery e ((G.withPerm fun k => P.perm H k).inst a).W t
        (simStage e ((G.withPerm fun k => P.perm H k).inst a) k) = _
      exact h1.trans (by rw [h2]; exact congrArg _ (congrArg _ (congrArg _ h3)))
    rw [logControlled_trans, logControlled_liftSimD, iotaD_controlled (V := simQueryIso e G.W),
      logControlled_permOp, permOp_vEmb, hp]
  · rename_i hk
    have hk' : k = Fin.last t := Fin.ext (by simp only [Fin.val_last]; omega)
    subst hk'
    have hp : simState e ((G.withPerm fun k => P.perm H k).inst a) =
        relabel (wsSplit G.W (LogReg Req (t + 1))).symm
          (controlled (fun _ => stepSim (G.withPerm fun k => P.perm H k) (Fin.last t))
            (relabel (wsSplit G.W (LogReg Req (t + 1)))
              (permOp (reqPermSim G a (Fin.last t))
                (preV e (G.withPerm fun k => P.perm H k) a t)))) := by
      have h2 := simStage_eq_preV e (G.withPerm fun k => P.perm H k) a t
      have h3 := simStep_inst (G.withPerm fun k => P.perm H k) a (Fin.last t)
        (preV e (G.withPerm fun k => P.perm H k) a t)
      change simStage e ((G.withPerm fun k => P.perm H k).inst a) t = _
      rw [h2]
      exact h3
    rw [logControlled_refl, hp]
    rfl

include hP in
/-- **A query slot on the run**: from the embedding at rest with query point `i` of step `k`
loaded, the query slot and the unload give the embedding at rest of query point `i` at `H`. -/
theorem query_load_vEmb (horc : ∀ lg : LogReg Req (slotTotal P.nb), E.oracle ω lg = H)
    (k : Fin (t + 1)) (i : Fin (P.nb k))
    (w : QState (SimRegister (G.W × LogReg Req (t + 1)) I J m t)) :
    permOp (liftG (loadD P k i)) (permOp ((coSimQ e P).eventPerm E ω (slotStart P.nb k + 1 + i))
      (vEmb (liftG (loadD P k i) ∘ iotaD G Y P.nb a false) w)) =
      vEmb (iotaD G Y P.nb a false) (permOp (wsLiftQ (P.add H k i).perm) w) := by
  rw [permOp_vEmb, permOp_vEmb, vEmb_permOp]
  exact vEmb_congr fun b _ => query_round e H a E ω hP horc k i b

include hP in
/-- **The query slots of step `k` on the run**: from the stage after the request slot of step `k`
with query point `0` loaded, the stage after query slot `i` is the embedding at rest of the first
`i` query points at `H` with query point `i` loaded. -/
theorem stage_qry (horc : ∀ lg : LogReg Req (slotTotal P.nb), E.oracle ω lg = H)
    (k : Fin (t + 1)) (hnb : 0 < P.nb k)
    (h0 : (coSimQ e P).stage E ω (slotStart P.nb k + 1) =
      vEmb (liftG (loadD P k ⟨0, hnb⟩) ∘ iotaD G Y P.nb a false)
        (permOp (reqPermSim G a k) (preV e (G.withPerm fun k => P.perm H k) a k))) :
    ∀ (i : ℕ) (hi : i < P.nb k), (coSimQ e P).stage E ω (slotStart P.nb k + 1 + i) =
      vEmb (liftG (loadD P k ⟨i, hi⟩) ∘ iotaD G Y P.nb a false)
        (permOp (wsLiftQ (prefPerm P H k i hi.le)) (permOp (reqPermSim G a k)
          (preV e (G.withPerm fun k => P.perm H k) a k)))
  | 0, hi => by
    change (coSimQ e P).stage E ω (slotStart P.nb k + 1) = _
    rw [h0, prefPerm_zero, wsLiftQ_one]
    rfl
  | i + 1, hi => by
    have ih := stage_qry horc k hnb h0 i (by omega)
    have hlt : slotStart P.nb k + 1 + (i + 1) < slotTotal P.nb + 1 := by
      have := slotStart_add_lt_total P.nb (Nat.le_of_lt_succ k.2) (o := 1 + (i + 1))
        (by rw [nbAt_fin]; omega)
      omega
    rw [← Nat.add_assoc, Distinguisher.stage_succ, ih, liftedStep_coSimQ e P _ (by omega)]
    have hs := stepQ_qry e P k ⟨i, by omega⟩
    simp only at hs
    rw [hs]
    unfold qryStepD
    rw [dif_pos (show i + 1 < P.nb k by omega), logControlled_trans, logControlled_permOp,
      logControlled_permOp, query_load_vEmb e H a E ω hP horc k ⟨i, by omega⟩, permOp_vEmb]
    congr 1

theorem prefPerm_eq_perm (k : Fin (t + 1)) {i : ℕ} (h : i = P.nb k) :
    prefPerm P H k i (h ▸ le_rfl) = P.perm H k := by
  subst h
  rfl

theorem permOp_wsLiftQ_perm_of_nb {k : Fin (t + 1)} (hnb : P.nb k = 0)
    (v : QState (SimRegister (G.W × LogReg Req (t + 1)) I J m t)) :
    permOp (wsLiftQ (P.perm H k)) v = v := by
  rw [StepAdds.perm_of_off H (P := P) (k := k) fun i => absurd i.2 (by omega), wsLiftQ_one]
  rfl

include hP in
/-- **A step of `G` on the run**: from the stage before the request slot of step `k`, the stage
before the request slot of step `k + 1`, and after the last step the embedding at rest of `|Sim*⟩`
of the instance. -/
theorem stage_block (k : Fin (t + 1))
    (hans : ∀ (lg : LogReg Req (t + 1)) (w : G.W), LogsAt k lg →
      E.answer ω (Function.update (spreadAt P.nb lg) (reqSlot P.nb k) (some (G.req k w)))
        (reqSlot P.nb k) = a k (G.req k w))
    (horc : ∀ lg : LogReg Req (slotTotal P.nb), E.oracle ω lg = H)
    (h : (coSimQ e P).stage E ω (slotStart P.nb k) =
      vEmb (liftG (setReqD G Y k) ∘ iotaD G Y P.nb a true)
        (preV e (G.withPerm fun k => P.perm H k) a k)) :
    (coSimQ e P).stage E ω (slotStart P.nb (k + 1)) =
      if hk : (k : ℕ) < t then vEmb (liftG (setReqD G Y ⟨k + 1, by omega⟩) ∘ iotaD G Y P.nb a true)
        (preV e (G.withPerm fun k => P.perm H k) a (k + 1))
      else vEmb (iotaD G Y P.nb a true) (simState e ((G.withPerm fun k => P.perm H k).inst a)) := by
  -- the request slot and the reply
  have hreq : permOp (liftG (writeD G Y k)) (permOp (liftG (storeD G Y k))
      (permOp (liftG (setReqD G Y k)) (permOp ((coSimQ e P).eventPerm E ω (slotStart P.nb k))
        ((coSimQ e P).stage E ω (slotStart P.nb k))))) =
      vEmb (iotaD G Y P.nb a true) (permOp (reqPermSim G a k)
        (preV e (G.withPerm fun k => P.perm H k) a k)) := by
    rw [h, permOp_vEmb, permOp_vEmb, permOp_vEmb, permOp_vEmb, vEmb_permOp]
    exact vEmb_congr fun b hb => request_round e P a E ω k hans b
      (preV_supp e (G.withPerm fun k => P.perm H k) a k (by omega) b hb)
  have hlt0 : slotStart P.nb k + 1 < slotTotal P.nb + 1 := by
    have := slotStart_lt_total P.nb (Nat.le_of_lt_succ k.2)
    omega
  have hs1 : (coSimQ e P).stage E ω (slotStart P.nb k + 1) = logControlled (fun _ =>
      if h : 0 < P.nb k then (permOp (loadD P k ⟨0, h⟩)).trans (permOp (flipD G Y))
      else finishD e G Y k) (vEmb (iotaD G Y P.nb a true) (permOp (reqPermSim G a k)
        (preV e (G.withPerm fun k => P.perm H k) a k))) := by
    rw [Distinguisher.stage_succ, liftedStep_coSimQ e P _ hlt0, stepQ_req, ← hreq]
    unfold reqStepD
    rw [logControlled_trans, logControlled_trans, logControlled_trans, logControlled_permOp,
      logControlled_permOp, logControlled_permOp]
  by_cases hnb : 0 < P.nb k
  · rw [dif_pos hnb, logControlled_trans, logControlled_permOp, logControlled_permOp, permOp_vEmb,
      permOp_vEmb] at hs1
    have h0 : (coSimQ e P).stage E ω (slotStart P.nb k + 1) =
        vEmb (liftG (loadD P k ⟨0, hnb⟩) ∘ iotaD G Y P.nb a false)
          (permOp (reqPermSim G a k) (preV e (G.withPerm fun k => P.perm H k) a k)) := by
      rw [hs1]
      rfl
    have hq := stage_qry e H a E ω hP horc k hnb h0 (P.nb k - 1) (by omega)
    have hlt : slotStart P.nb k + 1 + (P.nb k - 1) < slotTotal P.nb + 1 := by
      have := slotStart_add_lt_total P.nb (Nat.le_of_lt_succ k.2) (o := P.nb k)
        (by rw [nbAt_fin])
      omega
    have hend : slotStart P.nb (k + 1) = slotStart P.nb k + 1 + (P.nb k - 1) + 1 := by
      rw [slotStart_succ, nbAt_fin]
      omega
    have hs := stepQ_qry e P k ⟨P.nb k - 1, by omega⟩
    simp only at hs
    have hle := slotStart_le_of_le P.nb (show (k : ℕ) + 1 ≤ t + 1 by omega)
    have htot : slotTotal P.nb = slotStart P.nb (t + 1) := rfl
    rw [hend, Distinguisher.stage_succ, hq, liftedStep_coSimQ e P _ (by omega), hs]
    unfold qryStepD
    rw [dif_neg (show ¬(P.nb k - 1 + 1 < P.nb k) by omega), logControlled_trans,
      logControlled_trans, logControlled_permOp, logControlled_permOp,
      query_load_vEmb e H a E ω hP horc k ⟨P.nb k - 1, by omega⟩]
    have hpp : permOp (wsLiftQ (P.add H k ⟨P.nb k - 1, by omega⟩).perm)
        (permOp (wsLiftQ (prefPerm P H k (P.nb k - 1) (by omega)))
          (permOp (reqPermSim G a k) (preV e (G.withPerm fun k => P.perm H k) a k))) =
        permOp (wsLiftQ (P.perm H k))
          (permOp (reqPermSim G a k) (preV e (G.withPerm fun k => P.perm H k) a k)) := by
      have h1 := prefPerm_succ P H k ⟨P.nb k - 1, by omega⟩
      have h2 := prefPerm_eq_perm (P := P) H k (i := P.nb k - 1 + 1) (by omega)
      simp only at h1
      rw [← h2, h1, wsLiftQ_mul]
      rfl
    rw [hpp, finish_vEmb e H a k false]
    split
    · rw [permOp_vEmb]
      rfl
    · exact permOp_vEmb _ _ _
  · have hnb0 : P.nb k = 0 := by omega
    rw [dif_neg hnb, ← permOp_wsLiftQ_perm_of_nb H hnb0 (permOp (reqPermSim G a k) _),
      finish_vEmb e H a k true] at hs1
    rw [slotStart_succ, nbAt_fin, hnb0]
    exact hs1

include hP in
/-- **The run before the request slot of step `k`**, for `k ≤ t`. -/
theorem stage_start
    (hans : ∀ (k : Fin (t + 1)) (lg : LogReg Req (t + 1)) (w : G.W), LogsAt k lg →
      E.answer ω (Function.update (spreadAt P.nb lg) (reqSlot P.nb k) (some (G.req k w)))
        (reqSlot P.nb k) = a k (G.req k w))
    (horc : ∀ lg : LogReg Req (slotTotal P.nb), E.oracle ω lg = H) :
    ∀ k (hk : k ≤ t), (coSimQ e P).stage E ω (slotStart P.nb k) =
      vEmb (liftG (setReqD G Y ⟨k, by omega⟩) ∘ iotaD G Y P.nb a true)
        (preV e (G.withPerm fun k => P.perm H k) a k)
  | 0, _ => by
    show (coSimQ e P).liftedStep 0 (coSimQ e P).gameInit = _
    rw [liftedStep_coSimQ e P 0 (by omega), stepQ_zero, logControlled_permOp,
      gameInit_coSimQ e P H a, permOp_vEmb]
    rfl
  | k + 1, hk => by
    have h := stage_block e H a E ω hP (k := ⟨k, by omega⟩) (hans ⟨k, by omega⟩) horc
      (stage_start hans horc k (by omega))
    rw [dif_pos (show k < t by omega)] at h
    exact h

include hP in
/-- **The run of the distinguisher is the embedding at rest of `|Sim*⟩` of the instance** of `G`
read after the query points at `H`, with the replies `a`: when the environment answers the request
of the request slot of step `k` by `a k` (`hans`) and its oracle is `H` (`horc`). -/
theorem run_coSimQ
    (hans : ∀ (k : Fin (t + 1)) (lg : LogReg Req (t + 1)) (w : G.W), LogsAt k lg →
      E.answer ω (Function.update (spreadAt P.nb lg) (reqSlot P.nb k) (some (G.req k w)))
        (reqSlot P.nb k) = a k (G.req k w))
    (horc : ∀ lg : LogReg Req (slotTotal P.nb), E.oracle ω lg = H) :
    (coSimQ e P).run E ω =
      vEmb (iotaD G Y P.nb a true) (simState e ((G.withPerm fun k => P.perm H k).inst a)) := by
  have h := stage_block e H a E ω hP (k := Fin.last t) (hans (Fin.last t)) horc
    (stage_start e H a E ω hP hans horc t le_rfl)
  rw [dif_neg (by simp)] at h
  exact h

/-! ### The budget against every environment -/

variable (P) in
/-- The phase before slot `j`: a request at the block starts and after the last slot. -/
def kindAt (j : ℕ) : Bool :=
  decide (slotStart P.nb (slotBlock P.nb j) = j ∨ slotTotal P.nb ≤ j)

variable (G Y P) in
/-- The game basis states before slot `j`: the phase `kindAt j`, the logs blank from slot `j` on
and filled exactly at the block starts below `j`. -/
def slotSet (j : ℕ) : Set (GQ (I := I) (J := J) (m := m) G Y (slotTotal P.nb)) :=
  {g | g.1.1.2 = kindAt P j ∧ ∀ i : Fin (slotTotal P.nb),
    (j ≤ i → g.1.2.2.2 i = none) ∧
      ((i : ℕ) < j → ((g.1.2.2.2 i).isSome ↔ slotStart P.nb (slotBlock P.nb i) = i))}

variable (G Y P) in
/-- The game basis states after slot `j`: as `slotSet j` with slot `j` passed. -/
def slotSet' (j : ℕ) : Set (GQ (I := I) (J := J) (m := m) G Y (slotTotal P.nb)) :=
  {g | g.1.1.2 = kindAt P j ∧ ∀ i : Fin (slotTotal P.nb),
    (j < i → g.1.2.2.2 i = none) ∧
      ((i : ℕ) ≤ j → ((g.1.2.2.2 i).isSome ↔ slotStart P.nb (slotBlock P.nb i) = i))}

/-- **The query slots before slot `j`** on logs filled exactly at the block starts below `j`. -/
theorem queriesBefore_of_starts {lg : LogReg Req (slotTotal P.nb)} {j : ℕ}
    (h : ∀ i : Fin (slotTotal P.nb), (i : ℕ) < j →
      ((lg i).isSome ↔ slotStart P.nb (slotBlock P.nb i) = i)) :
    ∀ i ≤ j, i ≤ slotTotal P.nb → queriesBefore lg i = slotQBefore P.nb i
  | 0, _, _ => queriesBefore_zero _
  | i + 1, hi, hiM => by
    rw [queriesBefore_succ, queriesBefore_of_starts h i (by omega) (by omega), slotQBefore_succ]
    have hq : queriedAt lg i = decide (slotStart P.nb (slotBlock P.nb i) ≠ i) := by
      simp only [queriedAt, show i < slotTotal P.nb by omega, ↓reduceDIte]
      have hh := h ⟨i, by omega⟩ (by simp only; omega)
      cases hl : lg ⟨i, by omega⟩ with
      | none =>
        rw [hl] at hh
        simp only [Option.isSome_none, Bool.false_eq_true, false_iff] at hh
        simp [hh]
      | some r =>
        rw [hl] at hh
        simp only [Option.isSome_some, true_iff] at hh
        simp [hh]
    rw [hq]
    split_ifs with h3 <;> simp_all

/-- The basis states before a slot keep the budget of `Σ nb` queries. -/
theorem slotSet_subset_budgetAt {j : ℕ} (hj : j < slotTotal P.nb) :
    slotSet G Y P j ⊆ (coSimQ e P).BudgetAt (slotQ P.nb (t + 1)) j := by
  intro g ⟨hph, hl⟩
  have hq := queriesBefore_of_starts (fun i hi => (hl i).2 hi) j le_rfl hj.le
  have hb := slotQBefore_le P.nb hj
  refine ⟨?_, fun hk => ?_⟩
  · omega
  · rw [hq]
    refine hb.2 fun he => ?_
    have : (coSimQ e P).kind g.1.1 = true := by
      change g.1.1.2 = true
      rw [hph, kindAt, decide_eq_true_iff]
      exact Or.inl he
    rw [this] at hk
    exact Bool.noConfusion hk

theorem kindAt_start (k : Fin (t + 1)) : kindAt P (slotStart P.nb k) = true := by
  have hb : slotBlock P.nb (slotStart P.nb k) = k := by
    simpa using slotBlock_eq P.nb (Nat.le_of_lt_succ k.2) (o := 0) (Nat.zero_le _)
  simp [kindAt, hb]

theorem kindAt_qry (k : Fin (t + 1)) (i : Fin (P.nb k)) :
    kindAt P (slotStart P.nb k + 1 + i) = false := by
  have hb : slotBlock P.nb (slotStart P.nb k + 1 + i) = k := by
    rw [show slotStart P.nb k + 1 + (i : ℕ) = slotStart P.nb k + (1 + i) by omega]
    exact slotBlock_eq P.nb (Nat.le_of_lt_succ k.2) (by rw [nbAt_fin]; omega)
  have hlt : slotStart P.nb k + 1 + (i : ℕ) < slotTotal P.nb := by
    have := slotStart_add_lt_total P.nb (Nat.le_of_lt_succ k.2) (o := 1 + i)
      (by rw [nbAt_fin]; omega)
    omega
  simp only [kindAt, hb, decide_eq_false_iff_not, not_or]
  omega

theorem kindAt_next (k : Fin (t + 1)) : kindAt P (slotStart P.nb (k + 1)) = true := by
  by_cases hk : (k : ℕ) < t
  · exact kindAt_start (P := P) ⟨k + 1, by omega⟩
  · have : (k : ℕ) + 1 = t + 1 := by omega
    simp [kindAt, this]

/-- A slot is a block start or a query slot of its block. -/
theorem slot_cases {j : ℕ} (hj : j < slotTotal P.nb) :
    ∃ k : Fin (t + 1), j = slotStart P.nb k ∨ ∃ i : Fin (P.nb k), j = slotStart P.nb k + 1 + i := by
  refine ⟨⟨slotBlock P.nb j, Nat.lt_succ_of_le (slotBlock_le _ _)⟩, ?_⟩
  have h1 := slotStart_slotBlock_le P.nb j
  have h2 := lt_slotStart_slotBlock P.nb hj
  rw [slotStart_succ, nbAt_fin P.nb ⟨slotBlock P.nb j, Nat.lt_succ_of_le (slotBlock_le _ _)⟩] at h2
  by_cases he : j = slotStart P.nb (slotBlock P.nb j)
  · exact Or.inl he
  · exact Or.inr ⟨⟨j - slotStart P.nb (slotBlock P.nb j) - 1, by omega⟩, by
      show j = slotStart P.nb (slotBlock P.nb j) + 1 + (j - slotStart P.nb (slotBlock P.nb j) - 1)
      omega⟩

section BudgetAll

/-- A unitary of the distinguisher's registers that keeps the supports on a phase. -/
def KeepsPhase (U : QState (DD (I := I) (J := J) (m := m) G Y) ≃ₗᵢ[ℂ]
    QState (DD (I := I) (J := J) (m := m) G Y)) : Prop :=
  ∀ (φ : Bool) x, Supported {d : DD (I := I) (J := J) (m := m) G Y | d.1.1.2 = φ} x →
    Supported {d : DD (I := I) (J := J) (m := m) G Y | d.1.1.2 = φ} (U x)

theorem KeepsPhase.trans {U V : QState (DD (I := I) (J := J) (m := m) G Y) ≃ₗᵢ[ℂ]
    QState (DD (I := I) (J := J) (m := m) G Y)} (hU : KeepsPhase U) (hV : KeepsPhase V) :
    KeepsPhase (U.trans V) := fun φ x hx => hV φ _ (hU φ x hx)

theorem keepsPhase_refl : KeepsPhase (LinearIsometryEquiv.refl ℂ
    (QState (DD (I := I) (J := J) (m := m) G Y))) := fun _ _ hx => hx

theorem keepsPhase_permOp {π : Equiv.Perm (DD (I := I) (J := J) (m := m) G Y)}
    (hπ : ∀ d, (π d).1.1.2 = d.1.1.2) : KeepsPhase (permOp π) :=
  fun φ _ hx => hx.permOp fun d hd => by
    change (π d).1.1.2 = φ
    rw [hπ]
    exact hd

theorem keepsPhase_liftSimD
    (U : QState (SimRegister G.W I J m t) ≃ₗᵢ[ℂ] QState (SimRegister G.W I J m t)) :
    KeepsPhase (liftSimD G Y U) := by
  intro φ x hx d hd
  change U (WithLp.toLp 2 fun s => relabel (splitD G Y) x (s, (splitD G Y d).2))
    (splitD G Y d).1 = 0
  have h0 : (WithLp.toLp 2 fun s => relabel (splitD G Y) x (s, (splitD G Y d).2) :
      QState (SimRegister G.W I J m t)) = 0 := by
    ext s
    rw [relabel_apply]
    exact hx _ hd
  rw [h0, map_zero]
  rfl

variable (G Y) in
theorem keepsPhase_finishD (k : Fin (t + 1)) : KeepsPhase (finishD e G Y k) := by
  unfold finishD
  refine (keepsPhase_liftSimD _).trans ?_
  split
  · exact (keepsPhase_liftSimD _).trans (keepsPhase_permOp fun d => rfl)
  · exact keepsPhase_refl

/-- **A step that flips the phase**: a unitary keeping the phase, then the phase flipped, maps
the supports on a phase to the supports on the other. -/
theorem logControlled_flip {U : QState (DD (I := I) (J := J) (m := m) G Y) ≃ₗᵢ[ℂ]
    QState (DD (I := I) (J := J) (m := m) G Y)} (hU : KeepsPhase U) (φ : Bool)
    (L : LogReg Req M → Prop) (v : QState (GQ (I := I) (J := J) (m := m) G Y M))
    (hv : Supported {g : GQ (I := I) (J := J) (m := m) G Y M | g.1.1.2 = φ ∧ L g.1.2.2.2} v) :
    Supported {g : GQ (I := I) (J := J) (m := m) G Y M | g.1.1.2 = !φ ∧ L g.1.2.2.2}
      (logControlled (fun _ => U.trans (permOp (flipD G Y))) v) := by
  intro r hr
  rw [logControlled_apply]
  by_cases hL : L (splitLogs r).2
  · have hs : Supported {d : DD (I := I) (J := J) (m := m) G Y | d.1.1.2 = φ}
        (WithLp.toLp 2 fun d => v (splitLogs.symm (d, (splitLogs r).2))) := fun d hd =>
      hv _ fun h => hd h.1
    have hU' := hU φ _ hs
    rw [LinearIsometryEquiv.trans_apply, permOp_apply]
    refine hU' _ fun h => hr ⟨?_, hL⟩
    change ((flipD G Y).symm (splitLogs r).1).1.1.2 = φ at h
    have : ((flipD G Y).symm (splitLogs r).1).1.1.2 = !r.1.1.2 := rfl
    rw [this] at h
    rw [← h, Bool.not_not]
  · have h0 : (WithLp.toLp 2 fun d => v (splitLogs.symm (d, (splitLogs r).2)) :
        QState (DD (I := I) (J := J) (m := m) G Y)) = 0 := by
      ext d
      exact hv _ fun h => hL h.2
    rw [h0, map_zero]
    rfl

/-- A unitary keeping the phase keeps the supports on a phase and a set of logs. -/
theorem logControlled_keep {U : QState (DD (I := I) (J := J) (m := m) G Y) ≃ₗᵢ[ℂ]
    QState (DD (I := I) (J := J) (m := m) G Y)} (hU : KeepsPhase U) (φ : Bool)
    (L : LogReg Req M → Prop) (v : QState (GQ (I := I) (J := J) (m := m) G Y M))
    (hv : Supported {g : GQ (I := I) (J := J) (m := m) G Y M | g.1.1.2 = φ ∧ L g.1.2.2.2} v) :
    Supported {g : GQ (I := I) (J := J) (m := m) G Y M | g.1.1.2 = φ ∧ L g.1.2.2.2}
      (logControlled (fun _ => U) v) := by
  intro r hr
  rw [logControlled_apply]
  by_cases hL : L (splitLogs r).2
  · have hs : Supported {d : DD (I := I) (J := J) (m := m) G Y | d.1.1.2 = φ}
        (WithLp.toLp 2 fun d => v (splitLogs.symm (d, (splitLogs r).2))) := fun d hd =>
      hv _ fun h => hd h.1
    exact hU φ _ hs _ fun h => hr ⟨h, hL⟩
  · have h0 : (WithLp.toLp 2 fun d => v (splitLogs.symm (d, (splitLogs r).2)) :
        QState (DD (I := I) (J := J) (m := m) G Y)) = 0 := by
      ext d
      exact hv _ fun h => hL h.2
    rw [h0, map_zero]
    rfl

/-- The phase flipped maps the supports on a phase to the supports on the other. -/
theorem logControlled_flipD (φ : Bool) (L : LogReg Req M → Prop)
    (v : QState (GQ (I := I) (J := J) (m := m) G Y M))
    (hv : Supported {g : GQ (I := I) (J := J) (m := m) G Y M | g.1.1.2 = φ ∧ L g.1.2.2.2} v) :
    Supported {g : GQ (I := I) (J := J) (m := m) G Y M | g.1.1.2 = !φ ∧ L g.1.2.2.2}
      (logControlled (fun _ => permOp (flipD G Y)) v) :=
  logControlled_flip (U := LinearIsometryEquiv.refl ℂ _) keepsPhase_refl φ L v hv

/-- **The steps keep the slot sets**: the step after slot `j` maps the basis states after slot `j`
to those before slot `j + 1`. -/
theorem liftedStep_slotSet (j : ℕ) (hj : j < slotTotal P.nb)
    (v : QState (GQ (I := I) (J := J) (m := m) G Y (slotTotal P.nb)))
    (hv : Supported (slotSet' G Y P j) v) :
    Supported (slotSet G Y P (j + 1)) ((coSimQ e P).liftedStep (j + 1) v) := by
  rw [liftedStep_coSimQ e P _ (by omega)]
  set L : LogReg Req (slotTotal P.nb) → Prop := fun lg => ∀ i : Fin (slotTotal P.nb),
    (j < i → lg i = none) ∧
      ((i : ℕ) ≤ j → ((lg i).isSome ↔ slotStart P.nb (slotBlock P.nb i) = i)) with hLdef
  have hv' : Supported {g : GQ (I := I) (J := J) (m := m) G Y (slotTotal P.nb) |
      g.1.1.2 = kindAt P j ∧ L g.1.2.2.2} v := hv
  have hset : ∀ φ, φ = kindAt P (j + 1) →
      {g : GQ (I := I) (J := J) (m := m) G Y (slotTotal P.nb) | g.1.1.2 = φ ∧ L g.1.2.2.2} =
        slotSet G Y P (j + 1) := by
    rintro φ rfl
    ext g
    simp only [slotSet, Set.mem_ofPred_eq, hLdef]
    refine and_congr Iff.rfl (forall_congr' fun i => and_congr ?_ ?_)
    · exact ⟨fun h hi => h (by omega), fun h hi => h (by omega)⟩
    · exact ⟨fun h hi => h (by omega), fun h hi => h (by omega)⟩
  have hperm : ∀ π : Equiv.Perm (DD (I := I) (J := J) (m := m) G Y), (∀ d, (π d).1.1.2 = d.1.1.2) →
      ∀ (φ : Bool) w, Supported {g : GQ (I := I) (J := J) (m := m) G Y (slotTotal P.nb) |
        g.1.1.2 = φ ∧ L g.1.2.2.2} w → Supported {g : GQ (I := I) (J := J) (m := m) G Y
          (slotTotal P.nb) | g.1.1.2 = φ ∧ L g.1.2.2.2} (logControlled (fun _ => permOp π) w) :=
    fun π hπ φ w hw => logControlled_keep (keepsPhase_permOp hπ) φ L w hw
  obtain ⟨k, rfl | ⟨i, rfl⟩⟩ := slot_cases (P := P) hj
  · rw [stepQ_req]
    unfold reqStepD
    rw [kindAt_start] at hv'
    rw [logControlled_trans, logControlled_trans, logControlled_trans]
    split
    · rename_i hnb
      rw [← hset false (by
        have := kindAt_qry (P := P) k ⟨0, hnb⟩
        simpa using this.symm), logControlled_trans]
      exact logControlled_flipD true L _ (hperm _ (fun d => rfl) _ _ (hperm _ (fun d => rfl) _ _
        (hperm _ (fun d => rfl) _ _ (hperm _ (fun d => rfl) _ _ hv'))))
    · rename_i hnb
      rw [← hset true (by
        have h := kindAt_next (P := P) k
        rw [slotStart_succ, nbAt_fin, show P.nb k = 0 by omega] at h
        exact h.symm)]
      exact logControlled_keep (keepsPhase_finishD e G Y k) true L _ (hperm _ (fun d => rfl) _ _
        (hperm _ (fun d => rfl) _ _ (hperm _ (fun d => rfl) _ _ hv')))
  · rw [stepQ_qry]
    unfold qryStepD
    rw [kindAt_qry] at hv'
    rw [logControlled_trans]
    split
    · rename_i hi
      rw [← hset false (by
        have := kindAt_qry (P := P) k ⟨i + 1, hi⟩
        simpa [Nat.add_assoc] using this.symm)]
      exact hperm _ (fun d => rfl) _ _ (hperm _ (fun d => rfl) _ _ hv')
    · rename_i hi
      rw [← hset true (by
        have h := kindAt_next (P := P) k
        rw [slotStart_succ, nbAt_fin, show P.nb k = i + 1 by omega] at h
        rw [← h]
        congr 1)]
      exact logControlled_flip (keepsPhase_finishD e G Y k) false L _
        (hperm _ (fun d => rfl) _ _ hv')

/-- **The slots keep the slot sets**: slot `j` maps the basis states before it to those after it. -/
theorem eventPerm_slotSet {Ω' St' : Type} {Q' : ℕ} [OracleState St' (Bits m) Y]
    (E' : Env Ω' Req Resp (Bits m) Y Q' St') (ω' : Ω') (j : ℕ) (hj : j < slotTotal P.nb)
    (g : GQ (I := I) (J := J) (m := m) G Y (slotTotal P.nb)) (hg : g ∈ slotSet G Y P j) :
    (coSimQ e P).eventPerm E' ω' j g ∈ slotSet' G Y P j := by
  obtain ⟨hph, hl⟩ := hg
  have hkind : kindAt P j = decide (slotStart P.nb (slotBlock P.nb j) = j) := by
    simp only [kindAt]
    congr 1
    exact propext ⟨fun h => h.resolve_right (by omega), Or.inl⟩
  simp only [Distinguisher.eventPerm, dif_pos hj]
  refine ⟨?_, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · change ((E'.oraclePerm (coSimQ e P).kind ω')
      ((E'.requestPerm (coSimQ e P).kind ω' ⟨j, hj⟩) g)).1.1.2 = _
    simp only [Env.requestPerm, Env.oraclePerm, queryPermOf_apply, Equiv.prodCongr_apply,
      Equiv.trans_apply, copyPerm_apply, respondPerm_apply, Prod.map]
    split_ifs <;> exact hph
  · have h1 := Env.logs_oraclePerm E' (coSimQ e P).kind ω'
      ((E'.requestPerm (coSimQ e P).kind ω' ⟨j, hj⟩) g)
    have h2 := Env.logs_requestPerm E' (coSimQ e P).kind ω' ⟨j, hj⟩ g
    change (splitLogs ((E'.oraclePerm (coSimQ e P).kind ω') ((E'.requestPerm (coSimQ e P).kind ω'
      ⟨j, hj⟩) g))).2 i = none
    rw [h1, h2]
    split_ifs
    · rw [Function.update_of_ne (fun h => by rw [h] at hi; simp at hi)]
      exact (hl i).1 (by omega)
    · exact (hl i).1 (by omega)
  · have h1 := Env.logs_oraclePerm E' (coSimQ e P).kind ω'
      ((E'.requestPerm (coSimQ e P).kind ω' ⟨j, hj⟩) g)
    have h2 := Env.logs_requestPerm E' (coSimQ e P).kind ω' ⟨j, hj⟩ g
    change ((splitLogs ((E'.oraclePerm (coSimQ e P).kind ω') ((E'.requestPerm (coSimQ e P).kind ω'
      ⟨j, hj⟩) g))).2 i).isSome ↔ _
    rw [h1, h2]
    have hk : (coSimQ e P).kind g.workspace = kindAt P j := hph
    by_cases hij : (i : ℕ) = j
    · have hi' : i = ⟨j, hj⟩ := Fin.ext hij
      have hlj : (splitLogs g).2 ⟨j, hj⟩ = none := (hl ⟨j, hj⟩).1 le_rfl
      rw [hk, hi', hkind]
      by_cases hj2 : slotStart P.nb (slotBlock P.nb j) = j
      · simp only [hj2, decide_true, ↓reduceIte, Function.update_self, hlj, Equiv.swap_apply_left,
          Option.isSome_some]
      · simp only [hj2, decide_false, Bool.false_eq_true, ↓reduceIte, hlj, Option.isSome_none]
    · have hlt : (i : ℕ) < j := by omega
      split_ifs
      · rw [Function.update_of_ne (fun h => hij (by rw [h]))]
        exact (hl i).2 hlt
      · exact (hl i).2 hlt

/-- The run before slot `0` lies in the slot set of slot `0`. -/
theorem stage_zero_slotSet {Ω' St' : Type} {Q' : ℕ} [OracleState St' (Bits m) Y]
    (E' : Env Ω' Req Resp (Bits m) Y Q' St') (ω' : Ω') :
    Supported (slotSet G Y P 0) ((coSimQ e P).stage E' ω' 0) := by
  set L : LogReg Req (slotTotal P.nb) → Prop := fun lg => ∀ i : Fin (slotTotal P.nb),
    (0 ≤ (i : ℕ) → lg i = none) ∧
      ((i : ℕ) < 0 → ((lg i).isSome ↔ slotStart P.nb (slotBlock P.nb i) = i)) with hLdef
  have hset : slotSet G Y P 0 = {g : GQ (I := I) (J := J) (m := m) G Y (slotTotal P.nb) |
      g.1.1.2 = true ∧ L g.1.2.2.2} := by
    have h0 := kindAt_start (P := P) 0
    simp only [Fin.val_zero, slotStart_zero] at h0
    ext g
    simp only [slotSet, hLdef, h0]
  rw [hset]
  show Supported _ ((coSimQ e P).liftedStep 0 (coSimQ e P).gameInit)
  rw [liftedStep_coSimQ e P 0 (by omega)]
  refine logControlled_keep (keepsPhase_permOp fun d => rfl) true L _ ?_
  intro r hr
  rw [Distinguisher.gameInit_eq, relabel_apply, Equiv.symm_symm, tensorKet_apply]
  by_cases hl : (splitLogs r).2 = fun _ => none
  · have hph : r.1.1.2 ≠ true := fun h => hr ⟨h, fun i => ⟨fun _ => by
      have := congrFun hl i
      exact this, fun h' => absurd h' (Nat.not_lt_zero _)⟩⟩
    rw [if_pos hl, mul_one]
    change relabel (splitD G Y).symm (tensorKet (simInitG e G) (restBlankD Y)) (splitLogs r).1 = 0
    rw [relabel_apply, Equiv.symm_symm, tensorKet_apply, if_neg, mul_zero]
    intro h
    apply hph
    have := congrArg (fun p : RestD (t := t) (Resp := Resp) (Req := Req) (m := m) Y => p.1.2) h
    exact this
  · rw [if_neg hl, mul_zero]

/-- **The run keeps the slot sets** against every environment. -/
theorem stage_slotSet {Ω' St' : Type} {Q' : ℕ} [OracleState St' (Bits m) Y]
    (E' : Env Ω' Req Resp (Bits m) Y Q' St') (ω' : Ω') :
    ∀ j < slotTotal P.nb, Supported (slotSet G Y P j) ((coSimQ e P).stage E' ω' j)
  | 0, _ => stage_zero_slotSet e E' ω'
  | j + 1, hj => by
    rw [Distinguisher.stage_succ]
    exact liftedStep_slotSet e j (by omega) _ ((stage_slotSet E' ω' j (by omega)).permOp
      fun g hg => eventPerm_slotSet e E' ω' j (by omega) g hg)

end BudgetAll

/-! ### The adversary and its law -/

variable (P)

variable (G) in
/-- The output of the distinguisher: `G`'s output and the database of the slots. -/
abbrev outQ (w : WD (I := I) (J := J) (m := m) G) : O × DB (Bits m) B :=
  (G.out w.1.1.1.1, slotsDB e w.1.1.2)

/-- **The simulating adversary with real queries**: the distinguisher `coSimQ` as an adversary
with run-time kinds, the budget `Σ nb` (`slotQ nb (t + 1)`), the output `outQ`. -/
noncomputable abbrev advQ :=
  (coSimQ e P).toAdaptive Nat.one_pos (slotQ P.nb (t + 1)) (outQ e G)

theorem output_emb_iotaD (C₂ : Challenger (Bits m) Y Req Resp) (c : C₂.Coins) (j : ℕ)
    (b : SimRegister (G.W × LogReg Req (t + 1)) I J m t) :
    (advQ e P).output C₂ ((advQ e P).toKindAlg.emb C₂ H c j
      (Distinguisher.fMid (slotQ P.nb (t + 1)) j (iotaD G Y P.nb a true b))).1 =
      (((G.withPerm fun k => P.perm H k).inst a).out b.1.1, slotsDB e b.2) :=
  rfl

theorem history_emb_iotaD (C₂ : Challenger (Bits m) Y Req Resp) (hR : t + 1 ≤ C₂.Q)
    (c : C₂.Coins) (b : SimRegister (G.W × LogReg Req (t + 1)) I J m t) :
    ((advQ e P).history C₂ ((advQ e P).toKindAlg.emb C₂ H c (slotTotal P.nb)
      (Distinguisher.fMid (slotQ P.nb (t + 1)) (slotTotal P.nb) (iotaD G Y P.nb a true b))).1).map HistoryEntry.request =
      requests b.1.1.2 := by
  have h := Challenger.map_request_regStateOf C₂.Q C₂.respond c (spreadAt P.nb b.1.1.2)
    ((advQ e P).toKindAlg.ansOf C₂ ((advQ e P).toKindAlg.emb C₂ H c (slotTotal P.nb)
      (Distinguisher.fMid (slotQ P.nb (t + 1)) (slotTotal P.nb) (iotaD G Y P.nb a true b))).1.chal) (slotTotal P.nb)
  rw [AdaptiveIAlg.history]
  refine h.trans ?_
  rw [requestsBefore_spreadAt P.nb b.1.1.2 (t + 1) le_rfl]
  exact List.take_of_length_le ((length_requestsBefore_le _ _).trans hR)

include hP in
/-- **The law of the simulating adversary with real queries, with its history**: against a
challenger answering at least `t + 1` requests (`hR`), whose reply to the request `req k w` after
`k` requests at the oracle `H` is `aC c k (req k w)` without assignments (`hdet`) and which never
assigns (`hna`), at the oracle `H`, the probability that the output and the requests of the history
satisfy `Pr` is the coin average of the Born weight of `|Sim*⟩` of the instance of `G` read after
the query points at `H`, with the replies `aC c`, on the outcomes whose output, database and logged
requests satisfy `Pr`. -/
theorem toOuterMeasure_outLaw_advQ (C₂ : Challenger (Bits m) Y Req Resp)
    (aC : C₂.Coins → ℕ → Req → Option Resp) (hR : t + 1 ≤ C₂.Q)
    (hdet : ∀ c (k : Fin (t + 1)) (hist : List (HistoryEntry Req Resp)) (w : G.W),
      hist.length = k → (C₂.respond c hist (G.req k w)).run H = ⟨aC c k (G.req k w), []⟩)
    (hna : ∀ c (hist : List (HistoryEntry Req Resp)) r (H' : Bits m → Y),
      ((C₂.respond c hist r).run H').assignments = [])
    (Pr : O × DB (Bits m) B → List Req → Prop) :
    (((advQ e P).toKindAlg.composeBothOut C₂ id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, Pr ((advQ e P).output C₂ v) (((advQ e P).history C₂ v).map
          HistoryEntry.request)} =
      ∑ c, C₂.coins c * bornWeight (simState e ((G.withPerm fun k => P.perm H k).inst (aC c)))
        {b | Pr (((G.withPerm fun k => P.perm H k).inst (aC c)).out b.1.1, slotsDB e b.2)
          (requests b.1.1.2)} := by
  classical
  have hans : ∀ c (k : Fin (t + 1)) (lg : LogReg Req (t + 1)) (w : G.W), LogsAt k lg →
      C₂.toPureEnv.answer (H, c) (Function.update (spreadAt P.nb lg) (reqSlot P.nb k)
        (some (G.req k w))) (reqSlot P.nb k) = aC c k (G.req k w) :=
    fun c k lg w hlg => answer_spread_toPureEnv P H C₂ aC hR hdet hna c k lg w hlg
  have horc : ∀ c (lg : LogReg Req (slotTotal P.nb)), C₂.toPureEnv.oracle (H, c) lg = H :=
    fun c lg => oracle_toPureEnv C₂ hna H c lg
  rw [Distinguisher.toOuterMeasure_outLaw_toAdaptive (coSimQ e P) Nat.one_pos (slotQ P.nb (t + 1))
    (outQ e G) C₂ H (fun c j hj r hr => stage_slotSet e C₂.toPureEnv (H, c) j hj r fun h =>
      hr (slotSet_subset_budgetAt e hj h))]
  have key : ∀ c, prob {g | Pr ((advQ e P).output C₂ ((advQ e P).toKindAlg.emb C₂ H c
        (slotTotal P.nb) (Distinguisher.fMid (slotQ P.nb (t + 1)) (slotTotal P.nb) g)).1)
      (((advQ e P).history C₂ ((advQ e P).toKindAlg.emb C₂ H c (slotTotal P.nb)
        (Distinguisher.fMid (slotQ P.nb (t + 1)) (slotTotal P.nb) g)).1).map HistoryEntry.request)}
        ((coSimQ e P).run C₂.toPureEnv (H, c)) =
      ∑ b, (if Pr (((G.withPerm fun k => P.perm H k).inst (aC c)).out b.1.1, slotsDB e b.2)
          (requests b.1.1.2) then 1 else 0) *
        ‖simState e ((G.withPerm fun k => P.perm H k).inst (aC c)) b‖ ^ 2 := by
    intro c
    rw [run_coSimQ e H (aC c) C₂.toPureEnv (H, c) hP (hans c) (horc c)]
    unfold Quantum.prob
    erw [norm_mask_sq, Finset.sum_filter]
    have hg := sum_norm_vEmb_sq (iotaD_injective (G := G) (Y := Y) P.nb (aC c) true)
      (simState e ((G.withPerm fun k => P.perm H k).inst (aC c)))
      (fun r => if Pr ((advQ e P).output C₂ ((advQ e P).toKindAlg.emb C₂ H c (slotTotal P.nb)
          (Distinguisher.fMid (slotQ P.nb (t + 1)) (slotTotal P.nb) r)).1)
        (((advQ e P).history C₂ ((advQ e P).toKindAlg.emb C₂ H c (slotTotal P.nb)
          (Distinguisher.fMid (slotQ P.nb (t + 1)) (slotTotal P.nb) r)).1).map HistoryEntry.request) then 1 else 0)
    calc _ = ∑ r, (if Pr ((advQ e P).output C₂ ((advQ e P).toKindAlg.emb C₂ H c (slotTotal P.nb)
            (Distinguisher.fMid (slotQ P.nb (t + 1)) (slotTotal P.nb) r)).1)
          (((advQ e P).history C₂ ((advQ e P).toKindAlg.emb C₂ H c (slotTotal P.nb)
            (Distinguisher.fMid (slotQ P.nb (t + 1)) (slotTotal P.nb) r)).1).map HistoryEntry.request)
            then 1 else 0) *
          ‖vEmb (iotaD G Y P.nb (aC c) true) (simState e ((G.withPerm fun k => P.perm H k).inst
            (aC c))) r‖ ^ 2 :=
          Finset.sum_congr rfl fun r _ => by
            simp only [Set.mem_setOf_eq]; split_ifs <;> simp only [one_mul, zero_mul]
      _ = _ := hg
      _ = _ := Finset.sum_congr rfl fun b _ => by
          rw [output_emb_iotaD e P H (aC c) C₂ c, history_emb_iotaD e P H (aC c) C₂ hR c b]
  simp only [key]
  rw [ENNReal.ofReal_sum_of_nonneg fun c _ => mul_nonneg ENNReal.toReal_nonneg
    (Finset.sum_nonneg fun b _ => mul_nonneg (by split_ifs <;> norm_num) (sq_nonneg _))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (PMF.apply_ne_top _ _),
    bornWeight_apply_eq_sum, ENNReal.ofReal_sum_of_nonneg fun b _ =>
      mul_nonneg (by split_ifs <;> norm_num) (sq_nonneg _)]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Set.indicator, Set.mem_ofPred_eq]
  split_ifs
  · rw [one_mul, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  · rw [zero_mul, ENNReal.ofReal_zero]


/-- **The simulating adversary with real queries is within its budget.** -/
theorem withinBudget_advQ : (advQ e P).WithinBudget := fun C H =>
  Distinguisher.withinBudgetAt_toAdaptive (coSimQ e P) Nat.one_pos (slotQ P.nb (t + 1)) (outQ e G)
    C H fun c j hj r hr => stage_slotSet e C.toPureEnv (H, c) j hj r fun h =>
      hr (slotSet_subset_budgetAt e hj h)

/-- **The simulating adversary with real queries is trace preserving.** -/
theorem tracePreserving_advQ : (advQ e P).TracePreserving :=
  Distinguisher.toAdaptive_tracePreserving _ _ _ _

/-- **The simulating adversary with real queries makes `Σ nb` queries.** -/
theorem queries_advQ :
    (advQ e P).width * ((advQ e P).budget + (advQ e P).post) = slotQ P.nb (t + 1) := by
  change 1 * (slotQ P.nb (t + 1) + 0) = slotQ P.nb (t + 1)
  ring

/-! ### The simulating adversary without query points -/

variable (G Y) in
/-- **No query points.** -/
def noAdds : StepAdds (QueryReg G.W 1 (Bits m) (BitStr I J)) (Fin (t + 1)) (Bits m) Y where
  nb _ := 0
  L _ i := i.elim0
  on _ i := i.elim0
  x _ i := i.elim0
  on_set _ i := i.elim0
  x_set _ i := i.elim0

theorem noAdds_allOn : (noAdds G Y).AllOn := fun _ i => i.elim0

/-- `G` read after no query points is `G`. -/
theorem withPerm_noAdds : (G.withPerm fun k => (noAdds G Y).perm H k) = G :=
  rfl

variable (G Y) in
/-- **The simulating adversary**: the simulating distinguisher without query points as an adversary,
a request slot per step of `G` and no query. -/
noncomputable abbrev coSimAdv :=
  advQ e (noAdds G Y)

/-- **The simulating adversary is trace preserving.** -/
theorem coSimAdv_tracePreserving : (coSimAdv e G Y).TracePreserving :=
  tracePreserving_advQ e _

/-- **The simulating adversary is within its budget.** -/
theorem coSimAdv_withinBudget : (coSimAdv e G Y).WithinBudget :=
  withinBudget_advQ e _

/-- **The simulating adversary has a slot per step of `G`.** -/
theorem coSimAdv_slots : (coSimAdv e G Y).slots = t + 1 := by
  change slotStart (t := t) (fun _ => 0) (t + 1) = t + 1
  rw [slotStart, slotQ_zero]

/-- **The simulating adversary makes no query.** -/
theorem coSimAdv_queries :
    (coSimAdv e G Y).width * ((coSimAdv e G Y).budget + (coSimAdv e G Y).post) = 0 :=
  (queries_advQ e _).trans (slotQ_zero _)

/-- **The run of the simulating adversary with its history**: against a challenger answering at
least `t + 1` requests (`hR`), whose reply to the request `req k w` after `k` requests at the
oracle `H` is `aC c k (req k w)` without assignments (`hdet`) and which never assigns (`hna`), the
probability that the output and the requests of the history satisfy `Pr` is the coin average of
the Born weight of `|Sim*⟩` of the instance with the replies `aC c`, on the outcomes whose output,
database and logged requests satisfy `Pr`. -/
theorem toOuterMeasure_outLaw_coSimAdv_history (C₂ : Challenger (Bits m) Y Req Resp)
    (aC : C₂.Coins → ℕ → Req → Option Resp) (hR : t + 1 ≤ C₂.Q)
    (hdet : ∀ c (k : Fin (t + 1)) (hist : List (HistoryEntry Req Resp)) (w : G.W),
      hist.length = k → (C₂.respond c hist (G.req k w)).run H = ⟨aC c k (G.req k w), []⟩)
    (hna : ∀ c (hist : List (HistoryEntry Req Resp)) r (H' : Bits m → Y),
      ((C₂.respond c hist r).run H').assignments = [])
    (Pr : O × DB (Bits m) B → List Req → Prop) :
    (((coSimAdv e G Y).toKindAlg.composeBothOut C₂ fun v =>
        ((coSimAdv e G Y).output C₂ v, (coSimAdv e G Y).history C₂ v)).outLaw H).toOuterMeasure
      {o | ∃ v ∈ o, Pr v.1 (v.2.map HistoryEntry.request)} =
      ∑ c, C₂.coins c * bornWeight (simState e (G.inst (aC c)))
        {b | Pr ((G.inst (aC c)).out b.1.1, slotsDB e b.2) (requests b.1.1.2)} := by
  rw [KindAlg.toOuterMeasure_outLaw_composeBothOut]
  exact toOuterMeasure_outLaw_advQ e (noAdds G Y) H noAdds_allOn C₂ aC hR hdet hna Pr

end ReqQueryAlg

end GordieHowe.Quantum
