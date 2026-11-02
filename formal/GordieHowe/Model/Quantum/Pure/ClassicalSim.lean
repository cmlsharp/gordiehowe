-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.Game
public import GordieHowe.Foundations.Probability.Interaction

@[expose] public section

/-!
# Quantum adversaries with classical interaction are classical randomized strategies

A distinguisher of the pure game (`GordieHowe/Model/Quantum/Pure/Game.lean`) is a quantum
algorithm that keeps its quantum state across all `m` slots and interacts with an environment
through classical messages: at each slot it either makes a classical request (measured: copied
into a log register, deferred measurement, Nielsen–Chuang section 4.4) or queries the oracle in
force. This file proves the **conditional-sampling simulation**: on every tape of the
environment, the joint law of the distinguisher's logged moves and its final measurement outcome
is the law of a classical randomized strategy, in the sense of
`GordieHowe/Foundations/Probability/Interaction.lean` (a behavioral strategy: Kuhn 1953), that
draws each move from the distinguisher's conditional law given the visible transcript so far and
its output from the conditional law given the whole transcript. The strategy is a function of
the distinguisher and the post-phase unitary only, so it is the same against every environment.

The strategy is unbounded: its conditional laws are computed from the distinguisher's state
vectors. Histories are lists of any length; no finite table of the strategy is formed. The
quantum workspace kept across slots, the adaptive choice between requests and queries, and the
superposition queries all appear only through the conditional state.

## The construction

The visible transcript of a slot is the move (`moveOf`: the request if the kind register reads
request, `none` for a query) and the reply (`visReply`): the response and the oracle in force
after the slot. The **conditional state** of a classical history (`condState`) is the
distinguisher's state after projecting, at each slot, on the branches of the history's move and
applying the slot's events with the history's reply (`slotPerm`: the response written, or the
query to the oracle in force) and the next step. Its squared norm is the probability of the
history's moves given its replies. The strategy (`Distinguisher.classical`) draws the next move
with probability `‖Π_e ψ_h‖² / ‖ψ_h‖²` (`Π_e` the projection on the branches of move `e`,
`ψ_h` the conditional state), and the output from the computational-basis measurement of the
conditional state after the post-phase unitary.

`Env.toClassical` is the environment as a classical challenger of the interaction model: its
coins are the tape, its input the initial oracle in force, and its reply to a move the visible
reply (a function of the tape and the earlier requests). The simulation gives the classical
strategy the oracle in force as part of each reply, a whole table: the statistical games in which
the adversary receives every oracle whole are exactly those where this adds nothing.

## Results

- `slice_stage`, `slice_final`: on every tape and every log, the slice of the game state at the
  log is the conditional state of the log's visible history (`Env.vis`).
- `ofReal_norm_sq_final_eq_cont`: on every tape, the probability of each pair of logs and final
  outcome is the classical interaction's probability of the visible history and output.
- `acceptProbOnAt_eq_cont`: **simulation on one tape**: the probability that the distinguisher
  accepts with logs in `L` is the probability that the classical strategy's moves lie in `L` and
  its output in the accepting set.
- `tsum_acceptProbOnAt_eq_winProb`, `acceptProbOn_eq_winProb`, `acceptProb_eq_winProb`: averaged
  over the tape, the game is the classical interaction (`Interaction.winProb`).
- `advantage_acceptProb_le_of_det`: with the derandomization of behavioral strategies
  (`Interaction.abs_winDiff_le_of_det`), a bound on the advantage of every deterministic
  classical strategy between two environments bounds the advantage of every distinguisher.

The interactive adversaries of `GordieHowe/Model/Quantum/Interactive` (`AdaptiveIAlg`) reach
this through their dilation to the pure game
(`GordieHowe/Model/Quantum/Interactive/ClassicalSim.lean`).
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

/-! ### The measurement law of a vector -/

section NormBorn

variable {ι : Type*} [Fintype ι]

/-- **The law of the computational-basis measurement of a vector**, normalized: outcome `i`
with probability `‖w i‖² / ‖w‖²`; the point mass at `d₀` for the zero vector. -/
noncomputable def normBorn (d₀ : ι) (w : QState ι) : PMF ι :=
  if hw : ‖w‖ = 0 then PMF.pure d₀ else
    PMF.ofFintype (fun i => ENNReal.ofReal (‖w i‖ ^ 2 / ‖w‖ ^ 2)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity, ← Finset.sum_div,
        ← EuclideanSpace.norm_sq_eq, div_self (pow_ne_zero 2 hw), ENNReal.ofReal_one])

theorem normBorn_apply_of_ne (d₀ : ι) {w : QState ι} (hw : ‖w‖ ≠ 0) (i : ι) :
    normBorn d₀ w i = ENNReal.ofReal (‖w i‖ ^ 2 / ‖w‖ ^ 2) := by
  simp [normBorn, hw]

/-- **The normalized law times the squared norm is the squared amplitude.** -/
theorem ofReal_norm_sq_mul_normBorn (d₀ : ι) (w : QState ι) (i : ι) :
    ENNReal.ofReal (‖w‖ ^ 2) * normBorn d₀ w i = ENNReal.ofReal (‖w i‖ ^ 2) := by
  by_cases hw : ‖w‖ = 0
  · have hw0 : w = 0 := norm_eq_zero.1 hw
    simp [hw0]
  · rw [normBorn_apply_of_ne d₀ hw, ← ENNReal.ofReal_mul (by positivity),
      mul_div_cancel₀ _ (pow_ne_zero 2 hw)]

end NormBorn

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} (D : Distinguisher W X Y Req A n m)

/-- The moves of the classical interaction: a request, or `none` for a query slot. -/
abbrev Move (Req : Type*) := Option Req

/-- The replies of the classical interaction: the response and the oracle in force after the
slot. -/
abbrev Rep (X Y A : Type*) := Option A × (X → Y)

/-- The classical histories of the interaction. -/
abbrev CHist (X Y Req A : Type*) := Interaction.Hist (Move Req) (Rep X Y A)

/-- **The move of a basis state** of the distinguisher's registers: its request if the kind
register reads request, `none` (a query) otherwise. -/
def moveOf (d : DReg W n X Y Req A) : Move Req :=
  if D.kind d.workspace then some d.request else none

/-- The swap of `none` and `a` in the response register. -/
def respSwap [DecidableEq A] (a : Option A) : Equiv.Perm (DReg W n X Y Req A) :=
  Equiv.prodCongr (Equiv.prodCongr (Equiv.refl W) (Equiv.prodCongr (Equiv.refl Req)
    (Equiv.swap none a))) (Equiv.refl _)

/-- **The events of a slot on the distinguisher's registers**, on the branches of the move `e`
with reply `r`: for a request, the response `r.1` written into the response register (the swap
of `none` and `r.1`, as `respondPerm`); for a query, the query to the oracle `r.2`. -/
def slotPerm [DecidableEq A] [AddGroup Y] (e : Move Req) (r : Rep X Y A) :
    Equiv.Perm (DReg W n X Y Req A) :=
  match e with
  | none => queryPerm r.2
  | some _ => respSwap r.1

variable [DecidableEq A] [AddGroup Y] [DecidableEq Req]

/-- One slot of the conditional state: the projection on the branches of the move, the events
of the slot with the reply, and the distinguisher's next step. -/
noncomputable def condStep (k : ℕ) (v : QState (DReg W n X Y Req A))
    (x : Move Req × Rep X Y A) : QState (DReg W n X Y Req A) :=
  D.stepAt (k + 1) (permOp (slotPerm x.1 x.2) (mask (D.moveOf ⁻¹' {x.1}) v))

/-- **The adversary's state conditioned on a classical history** (unnormalized): from the
initial state and `step 0`, for each slot of the history the projection on its move, the
events of the slot with its reply and the next step. Its squared norm is the probability of
the history's moves given its replies. -/
noncomputable def condState (h : CHist X Y Req A) : QState (DReg W n X Y Req A) :=
  (h.foldl (fun (a : QState (DReg W n X Y Req A) × ℕ) x => (D.condStep a.2 a.1 x, a.2 + 1))
    (D.stepAt 0 D.init, 0)).1

omit [DecidableEq Req] in
private theorem foldl_condStep_snd (h : CHist X Y Req A) (v : QState (DReg W n X Y Req A))
    (k : ℕ) :
    (h.foldl (fun (a : QState (DReg W n X Y Req A) × ℕ) x => (D.condStep a.2 a.1 x, a.2 + 1))
      (v, k)).2 = k + h.length := by
  induction h generalizing v k with
  | nil => simp
  | cons x h ih => simp only [List.foldl_cons, ih, List.length_cons]; omega

omit [DecidableEq Req] in
theorem condState_nil : D.condState [] = D.stepAt 0 D.init :=
  rfl

omit [DecidableEq Req] in
theorem condState_append_singleton (h : CHist X Y Req A) (x : Move Req × Rep X Y A) :
    D.condState (h ++ [x]) = D.condStep h.length (D.condState h) x := by
  unfold condState
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [foldl_condStep_snd, Nat.zero_add]

omit [DecidableEq Req] in
theorem norm_condStep (k : ℕ) (v : QState (DReg W n X Y Req A)) (x : Move Req × Rep X Y A) :
    ‖D.condStep k v x‖ = ‖mask (D.moveOf ⁻¹' {x.1}) v‖ := by
  rw [condStep, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]

omit [DecidableEq Req] in
theorem norm_condState_nil : ‖D.condState []‖ = 1 := by
  rw [condState_nil, LinearIsometryEquiv.norm_map, D.norm_init]

include D in
omit [DecidableEq A] [AddGroup Y] [DecidableEq Req] in
/-- The registers are nonempty, since the initial state is a unit vector. -/
theorem nonempty_dReg : Nonempty (DReg W n X Y Req A) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have : D.init = 0 := Subsingleton.elim _ _
  have h1 := D.norm_init
  rw [this, norm_zero] at h1
  exact zero_ne_one h1

/-- A basis state of the registers. -/
noncomputable def someReg : DReg W n X Y Req A :=
  Classical.choice D.nonempty_dReg

/-- The oracle in force after a history: the last reply's, or the input oracle `i`. -/
def lastOracle (i : X → Y) (h : CHist X Y Req A) : X → Y :=
  match h.getLast? with
  | some x => x.2.2
  | none => i

/-- **The classical strategy of a distinguisher** with post-phase unitary `post`: the next move
is drawn from the measurement of the move register (kind and request) of the conditional state,
the output from the computational-basis measurement of the conditional state after `post` with
the oracle in force. -/
noncomputable def classical
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)) :
    Interaction.Strategy (X → Y) (Move Req) (Rep X Y A) (DReg W n X Y Req A) where
  next _ h := (normBorn D.someReg (D.condState h)).map D.moveOf
  out i h := normBorn D.someReg (post (lastOracle i h) (D.condState h))

/-- The classical strategy reads only the kind, the initial state and the steps (not `accept`). -/
theorem classical_congr {D' : Distinguisher W X Y Req A n m} (hkind : D.kind = D'.kind)
    (hinit : D.init = D'.init) (hstep : D.step = D'.step)
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)) :
    D.classical post = D'.classical post := by
  obtain ⟨k, i, ni, s, a⟩ := D
  obtain ⟨k', i', ni', s', a'⟩ := D'
  subst hkind hinit hstep
  rfl

end Distinguisher

/-! ### The classical form of an environment -/

namespace Env

variable {Ω Req A X Y : Type*} {St : Type _} {Q : ℕ} (E : Env Ω Req A X Y Q St)
  [OracleState St X Y]

/-- **The visible reply** to the move `e` after the requests `rs`: for a request, its response
and the oracle in force after it; for a query, no response and the oracle in force. -/
def visReply (ω : Ω) (rs : List Req) : Option Req → Option A × (X → Y)
  | none => (none, OracleState.toOracle (E.oracleIn ω rs))
  | some r => (E.answerAfter ω rs r, OracleState.toOracle (E.oracleIn ω (rs ++ [r])))

/-- The requests of a classical history, in order. -/
def histReqs {R : Type*} (h : Interaction.Hist (Option Req) R) : List Req :=
  h.filterMap (·.1)

theorem histReqs_append_singleton {R : Type*} (h : Interaction.Hist (Option Req) R)
    (x : Option Req × R) : histReqs (h ++ [x]) = histReqs h ++ x.1.toList := by
  obtain ⟨e, r⟩ := x
  cases e <;> simp [histReqs, List.filterMap_append]

/-- **The environment as a classical challenger**, its tape `t ω'` drawn by drawing `ω' ← ν`:
the input is the initial oracle in force, and the reply to a move is the visible reply
(`visReply`) after the requests of the history. -/
noncomputable def toClassical {Ω' : Type*} (ν : PMF Ω') (t : Ω' → Ω) :
    Interaction.Challenger Ω' (X → Y) (Option Req) (Option A × (X → Y)) where
  coins := ν
  input ω' := OracleState.toOracle (E.oracle₀ (t ω'))
  reply ω' h e := PMF.pure (E.visReply (t ω') (histReqs h) e)

variable {m : ℕ}

/-- **The visible history of the logs `lg` up to slot `j`**: each slot's log and the visible
reply to it. -/
def vis (ω : Ω) (lg : LogReg Req m) : ℕ → Interaction.Hist (Option Req) (Option A × (X → Y))
  | 0 => []
  | j + 1 => vis ω lg j ++
      if h : j < m then [(lg ⟨j, h⟩, E.visReply ω (requestsBefore lg j) (lg ⟨j, h⟩))] else []

theorem vis_succ_of_lt (ω : Ω) (lg : LogReg Req m) {j : ℕ} (hj : j < m) :
    E.vis ω lg (j + 1) =
      E.vis ω lg j ++ [(lg ⟨j, hj⟩, E.visReply ω (requestsBefore lg j) (lg ⟨j, hj⟩))] := by
  simp [vis, hj]

theorem length_vis (ω : Ω) (lg : LogReg Req m) {j : ℕ} (hj : j ≤ m) :
    (E.vis ω lg j).length = j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [E.vis_succ_of_lt ω lg (by omega), List.length_append, ih (by omega)]; rfl

theorem histReqs_vis (ω : Ω) (lg : LogReg Req m) {j : ℕ} (hj : j ≤ m) :
    histReqs (E.vis ω lg j) = requestsBefore lg j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [E.vis_succ_of_lt ω lg (by omega), histReqs_append_singleton, ih (by omega),
      requestsBefore_succ_of_lt _ (by omega)]

/-- The visible history up to slot `j` reads only the logs below `j`. -/
theorem vis_congr (ω : Ω) {lg lg' : LogReg Req m} {j : ℕ}
    (h : ∀ k : Fin m, (k : ℕ) < j → lg k = lg' k) : E.vis ω lg j = E.vis ω lg' j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [vis, vis, ih fun k hk => h k (by omega)]
    split_ifs with hj
    · rw [h ⟨j, hj⟩ (by simp), requestsBefore_congr fun k hk => h k (by omega)]
    · rfl

end Env

/-! ### The game state on each log is the conditional state of its visible history -/

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} (D : Distinguisher W X Y Req A n m) [DecidableEq A] [AddGroup Y] [DecidableEq Req]
  {Ω : Type*} {St : Type _} {Q : ℕ} [OracleState St X Y] (E : Env Ω Req A X Y Q St)

/-- **The slice of a game vector at the logs `lg`**: the vector on the distinguisher's
registers. -/
def slice (v : QState (GameReg W n X Y Req A m)) (lg : LogReg Req m) :
    QState (DReg W n X Y Req A) :=
  WithLp.toLp 2 fun d => v (splitLogs.symm (d, lg))

omit [DecidableEq A] [AddGroup Y] [DecidableEq Req] in
theorem slice_apply (v : QState (GameReg W n X Y Req A m)) (lg : LogReg Req m)
    (d : DReg W n X Y Req A) : slice v lg d = v (splitLogs.symm (d, lg)) :=
  rfl

omit [DecidableEq A] [AddGroup Y] [DecidableEq Req] in
theorem slice_logControlled
    (U : LogReg Req m → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (v : QState (GameReg W n X Y Req A m)) (lg : LogReg Req m) :
    slice (logControlled U v) lg = U lg (slice v lg) := by
  ext d
  simp only [slice, logControlled_apply, Equiv.apply_symm_apply]

omit [AddGroup Y] [DecidableEq A] in
theorem slice_gameInit_blank : slice D.gameInit (fun _ => none) = D.init := by
  ext d
  simp [slice, gameInit]

omit [DecidableEq A] [AddGroup Y] [DecidableEq Req] [Fintype Req] in
/-- The only logs reachable before slot `0` are the blank ones. -/
theorem eq_blank_of_mem_reachableLogs_zero {lg : LogReg Req m} (h : lg ∈ reachableLogs 0) :
    lg = fun _ => none :=
  funext fun k => h k (Nat.zero_le _)

omit [DecidableEq A] [DecidableEq Req] in
theorem moveOf_queryPerm_symm (f : X → Y) (d : DReg W n X Y Req A) :
    D.moveOf ((queryPerm f).symm d) = D.moveOf d :=
  rfl

omit [AddGroup Y] [DecidableEq Req] [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] in
theorem respSwap_symm (a : Option A) :
    (respSwap (W := W) (n := n) (X := X) (Y := Y) (Req := Req) a).symm = respSwap a := by
  ext d <;> simp [respSwap]

omit [AddGroup Y] [DecidableEq Req] in
theorem moveOf_respSwap (a : Option A) (d : DReg W n X Y Req A) :
    D.moveOf (respSwap a d) = D.moveOf d :=
  rfl

omit [DecidableEq Req] in
theorem moveOf_slotPerm_symm (e : Move Req) (r : Rep X Y A) (d : DReg W n X Y Req A) :
    D.moveOf ((slotPerm e r).symm d) = D.moveOf d := by
  cases e with
  | none => rfl
  | some _ => simp only [slotPerm, respSwap_symm]; rfl

/-- **The preimage of a basis state under the events of slot `j`**: on a query branch, the logs
unchanged and the query undone with the oracle in force; on a request branch, the response
register swapped back with the answer of the slot, and log `j` swapped back with the request. -/
theorem eventPerm_symm_splitLogs (ω : Ω) {j : ℕ} (hj : j < m) (d : DReg W n X Y Req A)
    (lg : LogReg Req m) :
    (D.eventPerm E ω j).symm (splitLogs.symm (d, lg)) =
      if D.kind d.workspace then
        splitLogs.symm (respSwap (E.answer ω lg ⟨j, hj⟩) d,
          Function.update lg ⟨j, hj⟩ (Equiv.swap none (some d.request) (lg ⟨j, hj⟩)))
      else splitLogs.symm ((queryPerm (E.oracle ω lg)).symm d, lg) := by
  rw [Equiv.symm_apply_eq]
  obtain ⟨⟨w, rq, rs⟩, q⟩ := d
  by_cases hk : D.kind w
  · simp only [DReg.workspace, DReg.request, hk, if_true]
    simp only [eventPerm, hj, dif_pos, Equiv.trans_apply, Env.requestPerm, Env.oraclePerm,
      Equiv.prodCongr_apply, Prod.map, copyPerm_apply, respondPerm_apply, queryPermOf_apply,
      splitLogs, respSwap, Equiv.coe_fn_symm_mk, Equiv.refl_apply,
      Equiv.prodCongr_apply, hk, if_true, Function.update_self, Function.update_idem,
      Equiv.swap_apply_self, Function.update_eq_self, Pi.zero_apply, add_zero]
  · simp only [DReg.workspace, hk, Bool.false_eq_true, if_false]
    simp only [eventPerm, hj, dif_pos, Equiv.trans_apply, Env.requestPerm, Env.oraclePerm,
      Equiv.prodCongr_apply, Prod.map, copyPerm_apply, respondPerm_apply, queryPermOf_apply,
      splitLogs, Equiv.coe_fn_symm_mk,
      Equiv.refl_apply]
    ext <;> simp [queryPerm, hk]

omit [DecidableEq A] [AddGroup Y] [DecidableEq Req] in
/-- A vector supported on the logs reachable before slot `j` vanishes where log `j` is
filled. -/
theorem apply_eq_zero_of_log_ne_none {j : ℕ} {v : QState (GameReg W n X Y Req A m)}
    (hv : Supported (logsIn (reachableLogs j)) v) (hj : j < m) (d : DReg W n X Y Req A)
    {lg : LogReg Req m} (h : lg ⟨j, hj⟩ ≠ none) : v (splitLogs.symm (d, lg)) = 0 :=
  hv _ fun hr => h (by
    simp only [mem_logsIn, Equiv.apply_symm_apply, reachableLogs, Set.mem_setOf_eq] at hr
    exact hr ⟨j, hj⟩ le_rfl)

/-- **One slot of the game on the slices**: on logs reachable after slot `j`, the slice after
the events of slot `j` is the projection on the move logged at slot `j` of the slice with log
`j` blank, followed by the events of the slot with the visible reply. -/
theorem slice_permOp_eventPerm (ω : Ω) {j : ℕ} (hj : j < m)
    {v : QState (GameReg W n X Y Req A m)} (hv : Supported (logsIn (reachableLogs j)) v)
    {lg : LogReg Req m} (hlg : lg ∈ reachableLogs (j + 1)) :
    slice (permOp (D.eventPerm E ω j) v) lg =
      permOp (slotPerm (lg ⟨j, hj⟩) (E.visReply ω (requestsBefore lg j) (lg ⟨j, hj⟩)))
        (mask (D.moveOf ⁻¹' {lg ⟨j, hj⟩}) (slice v (Function.update lg ⟨j, hj⟩ none))) := by
  ext d
  rw [slice_apply, permOp_apply, eventPerm_symm_splitLogs D E ω hj, permOp_apply]
  set j' : Fin m := ⟨j, hj⟩
  have hmv := D.moveOf_slotPerm_symm (lg j') (E.visReply ω (requestsBefore lg j) (lg j')) d
  by_cases hk : D.kind d.workspace
  · rw [if_pos hk]
    have hmd : D.moveOf d = some d.request := by simp [moveOf, hk]
    by_cases he : lg j' = some d.request
    · rw [mask_apply_of_mem _ (by rw [Set.mem_preimage, Set.mem_singleton_iff, hmv, hmd, he])]
      have hans : E.answer ω lg j' = E.answerAfter ω (requestsBefore lg j) d.request := by
        simp [Env.answer, he, j']
      simp only [he, Equiv.swap_apply_right, slotPerm, Env.visReply, respSwap_symm, hans,
        slice_apply]
    · rw [mask_apply_of_notMem _ (by
        simp only [Set.mem_preimage, Set.mem_singleton_iff, hmv, hmd]; exact fun h => he h.symm)]
      refine apply_eq_zero_of_log_ne_none hv hj _ ?_
      rw [Function.update_self]
      rcases hl : lg j' with _ | r
      · simp
      · have hr : some r ≠ some d.request := fun h => he (hl.trans h)
        rw [Equiv.swap_apply_of_ne_of_ne (by simp) hr]
        simp
  · rw [if_neg hk]
    have hmd : D.moveOf d = none := by simp [moveOf, hk]
    by_cases he : lg j' = none
    · rw [mask_apply_of_mem _ (by rw [Set.mem_preimage, Set.mem_singleton_iff, hmv, hmd, he])]
      have hup : Function.update lg j' none = lg := by rw [← he, Function.update_eq_self]
      have hreq : requests lg = requestsBefore lg j := requests_eq_requestsBefore fun k hk' => by
        rcases Nat.lt_or_eq_of_le hk' with h | h
        · exact hlg k h
        · have : k = j' := Fin.ext h.symm
          rw [this, he]
      simp only [he, slotPerm, Env.visReply, hup, slice_apply, Env.oracle, hreq]
    · rw [mask_apply_of_notMem _ (by
        simp only [Set.mem_preimage, Set.mem_singleton_iff, hmv, hmd]; exact fun h => he h.symm)]
      exact apply_eq_zero_of_log_ne_none hv hj _ he

omit [DecidableEq A] [AddGroup Y] [DecidableEq Req] [Fintype Req] in
theorem update_mem_reachableLogs {j : ℕ} (hj : j < m) {lg : LogReg Req m}
    (hlg : lg ∈ reachableLogs (j + 1)) :
    Function.update lg ⟨j, hj⟩ none ∈ reachableLogs j := fun k hk => by
  by_cases h : k = ⟨j, hj⟩
  · rw [h, Function.update_self]
  · rw [Function.update_of_ne h]
    exact hlg k (by
      have : (k : ℕ) ≠ j := fun e => h (Fin.ext e)
      omega)

/-- **The game state on each log is the conditional state of the log's visible history**: after
`step j`, the slice of the game state at logs reachable before slot `j` is the distinguisher's
state conditioned on the visible history of the logs (`condState`). -/
theorem slice_stage (ω : Ω) :
    ∀ j ≤ m, ∀ lg ∈ reachableLogs j, slice (D.stage E ω j) lg = D.condState (E.vis ω lg j)
  | 0, _, lg, hlg => by
    rw [eq_blank_of_mem_reachableLogs_zero hlg]
    simp only [stage, hybrid_zero, liftedStep, slice_logControlled, slice_gameInit_blank,
      Env.vis, condState_nil]
  | j + 1, hj, lg, hlg => by
    have hj' : j < m := by omega
    rw [stage_succ, liftedStep, slice_logControlled,
      slice_permOp_eventPerm D E ω hj' (D.stage_supported E ω j) hlg,
      slice_stage ω j (by omega) _ (update_mem_reachableLogs hj' hlg),
      E.vis_congr ω (lg' := lg) fun k hk => Function.update_of_ne (fun e => by
        rw [e] at hk; simp at hk) _ _,
      E.vis_succ_of_lt ω lg hj', condState_append_singleton, E.length_vis ω lg (by omega)]
    rfl

omit [DecidableEq A] [AddGroup Y] [DecidableEq Req] [Fintype Req] in
theorem mem_reachableLogs_self (lg : LogReg Req m) : lg ∈ reachableLogs m :=
  fun k hk => absurd k.2 (by omega)

/-- **The final game state on each log** is the post-phase unitary, with the oracle in force,
applied to the conditional state of the log's visible history. -/
theorem slice_final
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (ω : Ω) (lg : LogReg Req m) :
    slice (D.final E post ω) lg = post (E.oracle ω lg) (D.condState (E.vis ω lg m)) := by
  rw [final, slice_logControlled, run, D.slice_stage E ω m le_rfl lg (mem_reachableLogs_self lg)]

open Classical in
/-- **The acceptance probability on logs `L` as a sum over the logs** of the squared amplitudes
of the accepting outcomes of the final slices. -/
theorem acceptProbOnAt_eq_sum
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (L : Set (LogReg Req m)) (ω : Ω) :
    D.acceptProbOnAt E post L ω = ∑ lg, if lg ∈ L then ∑ d, if d ∈ D.accept then
      ‖post (E.oracle ω lg) (D.condState (E.vis ω lg m)) d‖ ^ 2 else 0 else 0 := by
  rw [acceptProbOnAt, prob, norm_mask_sq, Finset.sum_filter,
    ← splitLogs.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun lg _ => ?_
  by_cases hL : lg ∈ L
  · rw [if_pos hL]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hmem : splitLogs.symm (d, lg) ∈ D.gameAccept ∩ logsIn L ↔ d ∈ D.accept := by
      simp [gameAccept, mem_logsIn, hL]
    by_cases hd : d ∈ D.accept
    · rw [if_pos (hmem.2 hd), if_pos hd, ← slice_apply, slice_final]
    · rw [if_neg (fun h => hd (hmem.1 h)), if_neg hd]
  · rw [if_neg hL]
    refine Finset.sum_eq_zero fun d _ => if_neg fun h => hL ?_
    simpa [mem_logsIn] using h.2

/-! ### The classical strategy's law -/

/-- A sum over a countable family of finite sums is the finite sum of the sums. -/
theorem _root_.ENNReal.tsum_finset_sum_comm {α β : Type*} [Fintype β] (f : α → β → ℝ≥0∞) :
    ∑' a, ∑ b, f a b = ∑ b, ∑' a, f a b := by
  have h : (fun a => ∑ b, f a b) = fun a => ∑' b, f a b := funext fun a => (tsum_fintype (f a)).symm
  rw [h, ENNReal.tsum_comm, tsum_fintype (fun b => ∑' a, f a b)]

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] [DecidableEq A] [AddGroup Y]
  [DecidableEq Req] in
theorem lastOracle_append_singleton (i : X → Y) (h : CHist X Y Req A) (x : Move Req × Rep X Y A) :
    lastOracle i (h ++ [x]) = x.2.2 := by
  simp [lastOracle]

omit [DecidableEq A] [AddGroup Y] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  [DecidableEq Req] in
/-- **The oracle in force after a visible history**: the oracle after its requests. -/
theorem lastOracle_vis (ω : Ω) (lg : LogReg Req m) {j : ℕ} (hj : j ≤ m) :
    lastOracle (OracleState.toOracle (E.oracle₀ ω)) (E.vis ω lg j) =
      OracleState.toOracle (E.oracleIn ω (requestsBefore lg j)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [E.vis_succ_of_lt ω lg (by omega), lastOracle_append_singleton,
      requestsBefore_succ_of_lt _ (by omega)]
    rcases lg ⟨j, by omega⟩ with _ | r <;> simp [Env.visReply]

/-- The moves of a classical history as logs: entry `k` of the history's moves, `none` past its
end. -/
def movesOf (h : CHist X Y Req A) : LogReg Req m :=
  fun k => match h[(k : ℕ)]? with
    | some x => x.1
    | none => none

omit [DecidableEq A] [AddGroup Y] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  [DecidableEq Req] in
theorem getElem?_vis (ω : Ω) (lg : LogReg Req m) {j : ℕ} (hj : j ≤ m) (k : Fin m)
    (hk : (k : ℕ) < j) :
    (E.vis ω lg j)[(k : ℕ)]? = some (lg k, E.visReply ω (requestsBefore lg k) (lg k)) := by
  induction j with
  | zero => omega
  | succ j ih =>
    rw [E.vis_succ_of_lt ω lg (by omega)]
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.1 hk) with h | h
    · rw [List.getElem?_append_left (by rw [E.length_vis ω lg (by omega)]; exact h),
        ih (by omega) h]
    · rw [List.getElem?_append_right (by rw [E.length_vis ω lg (by omega)]; omega)]
      simp only [E.length_vis ω lg (show j ≤ m by omega), h, Nat.sub_self, List.getElem?_cons_zero]
      have : (⟨j, by omega⟩ : Fin m) = k := Fin.ext h.symm
      rw [this]

omit [DecidableEq A] [AddGroup Y] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  [DecidableEq Req] in
theorem movesOf_vis (ω : Ω) (lg : LogReg Req m) : movesOf (E.vis ω lg m) = lg := by
  funext k
  simp [movesOf, getElem?_vis E ω lg le_rfl k k.2]

/-- The event that the moves lie in `L` and the output in the accepting set. -/
def acceptEvent (L : Set (LogReg Req m)) : Set (CHist X Y Req A × DReg W n X Y Req A) :=
  {p | movesOf p.1 ∈ L ∧ p.2 ∈ D.accept}

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] [DecidableEq Req] in
theorem ofReal_norm_sq_mul_map_normBorn {ι κ : Type*} [Fintype ι] [DecidableEq κ] (d₀ : ι)
    (g : ι → κ) (v : QState ι) (e : κ) :
    ENNReal.ofReal (‖v‖ ^ 2) * (normBorn d₀ v).map g e =
      ENNReal.ofReal (‖mask (g ⁻¹' {e}) v‖ ^ 2) := by
  classical
  rw [PMF.map_apply, tsum_fintype, Finset.mul_sum, norm_mask_sq, Finset.sum_filter,
    ENNReal.ofReal_sum_of_nonneg fun i _ => by split_ifs <;> positivity]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : g i = e
  · simp only [Set.mem_preimage, Set.mem_singleton_iff, h, if_true, ofReal_norm_sq_mul_normBorn]
  · simp [Set.mem_preimage, Ne.symm h, h]

variable (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
  {Ω' : Type*} (ν : PMF Ω') (t : Ω' → Ω)

open Classical in
/-- **The classical continuation from a visible history, weighted by its probability**: the
continuation of the classical strategy from the visible history of `lg₀` up to slot `j`, times
the squared norm of the conditional state, gives the complete visible history of `lg` and the
output `x` the squared amplitude of `x` in the final slice at `lg`, for the logs `lg` that agree
with `lg₀` below `j`. -/
theorem ofReal_mul_cont (ω' : Ω') (k : ℕ) :
    ∀ (j : ℕ) (lg₀ : LogReg Req m), j + k = m → ∀ p : CHist X Y Req A × DReg W n X Y Req A,
      ENNReal.ofReal (‖D.condState (E.vis (t ω') lg₀ j)‖ ^ 2) *
          Interaction.cont (D.classical post) (E.toClassical ν t) ω' (E.vis (t ω') lg₀ j) k p =
        ∑ lg, if (∀ i : Fin m, (i : ℕ) < j → lg i = lg₀ i) ∧ p.1 = E.vis (t ω') lg m then
          ENNReal.ofReal (‖post (E.oracle (t ω') lg) (D.condState (E.vis (t ω') lg m)) p.2‖ ^ 2)
          else 0 := by
  induction k with
  | zero =>
    intro j lg₀ hj p
    rw [Nat.add_zero] at hj
    subst j
    rw [Finset.sum_eq_single lg₀ (fun lg _ hne => if_neg fun h => hne (funext fun i =>
      h.1 i i.2)) (fun h => absurd (Finset.mem_univ _) h)]
    simp only [Interaction.cont, PMF.map_apply, tsum_fintype]
    obtain ⟨h1, x⟩ := p
    by_cases hp : h1 = E.vis (t ω') lg₀ m
    · subst hp
      rw [Finset.sum_eq_single x (fun o _ ho => by simp [Ne.symm ho]) (fun h => absurd
        (Finset.mem_univ _) h)]
      rw [if_pos rfl, if_pos (⟨fun _ _ => trivial, rfl⟩ : _ ∧ _)]
      have hlast := lastOracle_vis E (t ω') lg₀ (le_refl m)
      simp only [classical, Env.toClassical]
      rw [hlast, ← (post _).norm_map, ofReal_norm_sq_mul_normBorn]
      rfl
    · rw [if_neg fun h => hp h.2,
        Finset.sum_eq_zero fun o _ => if_neg fun h => hp (congrArg Prod.fst h), mul_zero]
  | succ k ih =>
    intro j lg₀ hj p
    have hjm : j < m := by omega
    simp only [Interaction.cont]
    rw [PMF.bind_apply, tsum_fintype, Finset.mul_sum]
    have hstep : ∀ e : Move Req,
        ENNReal.ofReal (‖D.condState (E.vis (t ω') lg₀ j)‖ ^ 2) *
          ((D.classical post).next ((E.toClassical ν t).input ω') (E.vis (t ω') lg₀ j) e *
            ((E.toClassical ν t).reply ω' (E.vis (t ω') lg₀ j) e).bind (fun r =>
              Interaction.cont (D.classical post) (E.toClassical ν t) ω'
                (E.vis (t ω') lg₀ j ++ [(e, r)]) k) p) =
        ∑ lg, if (∀ i : Fin m, (i : ℕ) < j → lg i = lg₀ i) ∧ lg ⟨j, hjm⟩ = e ∧
            p.1 = E.vis (t ω') lg m then
          ENNReal.ofReal (‖post (E.oracle (t ω') lg) (D.condState (E.vis (t ω') lg m)) p.2‖ ^ 2)
          else 0 := fun e => by
      set lge := Function.update lg₀ ⟨j, hjm⟩ e
      have h1 : lge ⟨j, hjm⟩ = e := Function.update_self _ _ _
      have h2 : ∀ i : Fin m, (i : ℕ) < j → lge i = lg₀ i := fun i hi =>
        Function.update_of_ne (fun h => by rw [h] at hi; simp at hi) _ _
      have hvis : E.vis (t ω') lge (j + 1) = E.vis (t ω') lg₀ j ++
          [(e, E.visReply (t ω') (Env.histReqs (E.vis (t ω') lg₀ j)) e)] := by
        rw [E.vis_succ_of_lt _ _ hjm, E.histReqs_vis _ _ hjm.le, h1, E.vis_congr (t ω') h2,
          requestsBefore_congr h2]
      simp only [Env.toClassical, PMF.pure_bind, classical]
      rw [← mul_assoc, ofReal_norm_sq_mul_map_normBorn]
      have hn : ‖mask (D.moveOf ⁻¹' {e}) (D.condState (E.vis (t ω') lg₀ j))‖ =
          ‖D.condState (E.vis (t ω') lg₀ j ++
            [(e, E.visReply (t ω') (Env.histReqs (E.vis (t ω') lg₀ j)) e)])‖ := by
        rw [condState_append_singleton, norm_condStep]
      rw [hn]
      have := ih (j + 1) lge (by omega) p
      simp only [classical, Env.toClassical] at this
      rw [hvis] at this
      rw [this]
      refine Finset.sum_congr rfl fun lg _ => ?_
      congr 1
      apply propext
      constructor
      · rintro ⟨g1, g2⟩
        exact ⟨fun i hi => (g1 i (by omega)).trans (h2 i hi),
          (g1 ⟨j, hjm⟩ (by simp)).trans h1, g2⟩
      · rintro ⟨g1, g2, g3⟩
        refine ⟨fun i hi => ?_, g3⟩
        by_cases hij : (i : ℕ) = j
        · have : i = ⟨j, hjm⟩ := Fin.ext hij
          rw [this, g2, h1]
        · exact (g1 i (by omega)).trans (h2 i (by omega)).symm
    simp only [hstep]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun lg _ => ?_
    rw [Finset.sum_eq_single (lg ⟨j, hjm⟩) (fun e _ he => if_neg fun h => he h.2.1.symm)
      (fun h => absurd (Finset.mem_univ _) h)]
    simp

open Classical in
/-- **The law of the classical interaction from the start**: the complete visible history of
`lg` and the output `x` have the squared amplitude of `x` in the final slice at `lg`. -/
theorem cont_nil_apply (ω' : Ω') (p : CHist X Y Req A × DReg W n X Y Req A) :
    Interaction.cont (D.classical post) (E.toClassical ν t) ω' [] m p =
      ∑ lg : LogReg Req m, if p.1 = E.vis (t ω') lg m then
        ENNReal.ofReal (‖post (E.oracle (t ω') lg) (D.condState (E.vis (t ω') lg m)) p.2‖ ^ 2)
        else 0 := by
  have h := D.ofReal_mul_cont E post ν t ω' m 0 (fun _ => none) (by omega) p
  simp only [Env.vis, norm_condState_nil, one_pow, ENNReal.ofReal_one, one_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun lg _ => ?_
  simp

open Classical in
/-- **The joint law of the logs and the outcome** on one tape: the probability that the final
measurement of the game finds the logs `lg` and the outcome `x` is the probability that the
classical interaction ends with the visible history of `lg` and the output `x`. -/
theorem ofReal_norm_sq_final_eq_cont (ω' : Ω') (lg : LogReg Req m) (x : DReg W n X Y Req A) :
    ENNReal.ofReal (‖D.final E post (t ω') (splitLogs.symm (x, lg))‖ ^ 2) =
      Interaction.cont (D.classical post) (E.toClassical ν t) ω' [] m
        (E.vis (t ω') lg m, x) := by
  rw [cont_nil_apply, Finset.sum_eq_single lg (fun lg' _ hne => if_neg fun h => hne (by
      have := congrArg (movesOf (m := m)) h
      simp only [movesOf_vis] at this
      exact this.symm)) (fun h => absurd (Finset.mem_univ _) h),
    if_pos rfl, ← slice_apply, slice_final]

open Classical in
/-- **Simulation on one tape**: the probability that the distinguisher accepts with logs in `L`,
on the tape `t ω'`, is the probability that the classical strategy's moves lie in `L` and its
output in the accepting set, in the classical interaction at the challenger's coins `ω'`. -/
theorem acceptProbOnAt_eq_cont (L : Set (LogReg Req m)) (ω' : Ω') :
    D.acceptProbOnAt E post L (t ω') =
      ((Interaction.cont (D.classical post) (E.toClassical ν t) ω' [] m).toOuterMeasure
        (D.acceptEvent L)).toReal := by
  rw [acceptProbOnAt_eq_sum, PMF.toOuterMeasure_apply]
  have hp : ∀ p, (D.acceptEvent L).indicator
      (Interaction.cont (D.classical post) (E.toClassical ν t) ω' [] m) p =
      ∑ lg : LogReg Req m, if p.1 = E.vis (t ω') lg m ∧ lg ∈ L ∧ p.2 ∈ D.accept then
        ENNReal.ofReal (‖post (E.oracle (t ω') lg) (D.condState (E.vis (t ω') lg m)) p.2‖ ^ 2)
        else 0 := fun p => by
    by_cases hp : p ∈ D.acceptEvent L
    · rw [Set.indicator_of_mem hp, cont_nil_apply]
      refine Finset.sum_congr rfl fun lg _ => ?_
      by_cases h1 : p.1 = E.vis (t ω') lg m
      · have hL : lg ∈ L := by have := hp.1; rwa [h1, movesOf_vis] at this
        simp [h1, hL, hp.2]
      · simp [h1]
    · rw [Set.indicator_of_notMem hp]
      refine (Finset.sum_eq_zero fun lg _ => if_neg fun h => hp ⟨?_, h.2.2⟩).symm
      rw [h.1, movesOf_vis]
      exact h.2.1
  have key : ∀ lg : LogReg Req m, ∑' p : CHist X Y Req A × DReg W n X Y Req A,
      (if p.1 = E.vis (t ω') lg m ∧ lg ∈ L ∧ p.2 ∈ D.accept then
        ENNReal.ofReal (‖post (E.oracle (t ω') lg) (D.condState (E.vis (t ω') lg m)) p.2‖ ^ 2)
        else 0) =
      ENNReal.ofReal (if lg ∈ L then ∑ d, if d ∈ D.accept then
        ‖post (E.oracle (t ω') lg) (D.condState (E.vis (t ω') lg m)) d‖ ^ 2 else 0 else 0) :=
      fun lg => by
    rw [ENNReal.tsum_prod']
    have hh : ∀ h : CHist X Y Req A, ∑' x : DReg W n X Y Req A,
        (if (h, x).1 = E.vis (t ω') lg m ∧ lg ∈ L ∧ (h, x).2 ∈ D.accept then
          ENNReal.ofReal (‖post (E.oracle (t ω') lg) (D.condState (E.vis (t ω') lg m)) x‖ ^ 2)
          else 0) =
        if h = E.vis (t ω') lg m then ∑' x : DReg W n X Y Req A,
          (if lg ∈ L ∧ x ∈ D.accept then
            ENNReal.ofReal (‖post (E.oracle (t ω') lg) (D.condState (E.vis (t ω') lg m)) x‖ ^ 2)
            else 0) else 0 := fun h => by
      by_cases hh : h = E.vis (t ω') lg m <;> simp [hh]
    rw [tsum_congr hh, tsum_ite_eq, tsum_fintype]
    by_cases hL : lg ∈ L
    · simp only [hL, true_and, if_true]
      rw [ENNReal.ofReal_sum_of_nonneg fun d _ => by split_ifs <;> positivity]
      refine Finset.sum_congr rfl fun d _ => ?_
      split_ifs <;> simp
    · simp [hL]
  simp only [hp]
  rw [ENNReal.tsum_finset_sum_comm]
  simp only [key]
  rw [ENNReal.toReal_sum fun lg _ => ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun lg _ => ?_
  rw [ENNReal.toReal_ofReal (by
    split_ifs
    · exact Finset.sum_nonneg fun d _ => by split_ifs <;> positivity
    · exact le_rfl)]

/-- **Simulation averaged over the tape**: the distinguisher's probability of accepting with
logs in `L`, averaged over the tape `t ω'` for `ω' ← ν`, is the probability that the classical
strategy's moves lie in `L` and its output in the accepting set, against the environment as a
classical challenger with coins `ω' ← ν`. -/
theorem tsum_acceptProbOnAt_eq_winProb (L : Set (LogReg Req m)) :
    ∑' ω', (ν ω').toReal * D.acceptProbOnAt E post L (t ω') =
      Interaction.winProb (D.classical post) (E.toClassical ν t) m (D.acceptEvent L) := by
  rw [Interaction.winProb, Interaction.exper, toReal_toOuterMeasure_bind]
  refine tsum_congr fun ω' => ?_
  rw [acceptProbOnAt_eq_cont]
  rfl

/-- **Simulation of the game** (`tsum_acceptProbOnAt_eq_winProb` for the environment's own
tape): the probability that the distinguisher accepts with logs in `L` is that of the classical
strategy against the environment as a classical challenger. -/
theorem acceptProbOn_eq_winProb [Fintype Ω] (L : Set (LogReg Req m)) :
    D.acceptProbOn E post L =
      Interaction.winProb (D.classical post) (E.toClassical E.μ id) m (D.acceptEvent L) := by
  rw [← tsum_acceptProbOnAt_eq_winProb, tsum_fintype]
  rfl

theorem acceptProb_eq_winProb [Fintype Ω] :
    D.acceptProb E post =
      Interaction.winProb (D.classical post) (E.toClassical E.μ id) m (D.acceptEvent Set.univ) := by
  rw [← acceptProbOn_eq_winProb]
  simp only [acceptProbOn, acceptProbOnAt_univ, acceptProb]

open Classical in
/-- **The classical strategy with a bit as output**: whether the output lies in the accepting
set. -/
noncomputable def classicalBit : Interaction.Strategy (X → Y) (Move Req) (Rep X Y A) Bool :=
  (D.classical post).mapOut fun d => decide (d ∈ D.accept)

theorem acceptProb_eq_winProb_bit [Fintype Ω] :
    D.acceptProb E post =
      Interaction.winProb (D.classicalBit post) (E.toClassical E.μ id) m {p | p.2 = true} := by
  rw [acceptProb_eq_winProb, classicalBit, Interaction.winProb_mapOut]
  congr 1
  ext p
  simp [acceptEvent]

/-- **Quantum distinguishers with classical interaction are no better than deterministic
classical strategies**: if every deterministic classical strategy (moves and a guess as
functions of the input oracle and the visible history) has advantage at most `ε` between two
environments as classical challengers, every distinguisher of the pure game (quantum memory
across all slots, classical requests, any post-phase unitary `post`) has advantage at most `ε`
between them. -/
theorem advantage_acceptProb_le_of_det [DecidableEq X] {Ω₀ Ω₁ : Type*} [Fintype Ω₀] [Fintype Ω₁]
    (E₀ : Env Ω₀ Req A X Y Q St) (E₁ : Env Ω₁ Req A X Y Q St) {ε : ℝ}
    (hdet : ∀ s : Interaction.DetStrategy (X → Y) (Move Req) (Rep X Y A) Bool,
      |Interaction.winProb s.toStrategy (E₀.toClassical E₀.μ id) m {p | p.2 = true} -
        Interaction.winProb s.toStrategy (E₁.toClassical E₁.μ id) m {p | p.2 = true}| ≤ ε) :
    GordieHowe.advantage (D.acceptProb E₀ post) (D.acceptProb E₁ post) ≤ ε := by
  rw [GordieHowe.advantage, acceptProb_eq_winProb_bit, acceptProb_eq_winProb_bit]
  exact Interaction.abs_winDiff_le_of_det _ _ _ _ m hdet

end Distinguisher

end GordieHowe.Quantum
