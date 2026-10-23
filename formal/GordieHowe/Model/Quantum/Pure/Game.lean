-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Pure.Algorithm

@[expose] public section

/-!
# Interactive oracle games with classical requests

A distinguisher interacts with an environment over `m` event slots. At each slot, on each branch of
its superposition, it either queries the oracle or makes a classical request; which one is read from
a kind register in its workspace (`Distinguisher.kind`). The environment holds an upfront random
tape and answers each request; between requests it may change the oracle. This is the experiment of
every definition of non-interactive zero knowledge in the random-oracle model (the paper's Section
6.1.1, Privacy), written in the pure-vector model of `GordieHowe/Model/Quantum/Pure/Algorithm.lean`.
`GordieHowe/Model/QROM/NIZK.lean` instantiates it with a prover and a simulator.

## Registers

The distinguisher's registers are a workspace `W`, a request register `Req`, a response register
`Option A` (`none` is the blank value) and `n` query registers, each a pair of a query input in `X`
and a query output in `Y`: the basis `DReg W n X Y Req A`. The game adds one log register
`Option Req` per slot (`LogReg Req m`); the full basis is
`GameReg W n X Y Req A m = QueryReg (W × Req × Option A × LogReg Req m) n X Y`, so an oracle acts on
it as in `GordieHowe/Model/Quantum/Core/Oracle.lean`.

## The model and its sources

- **The distinguisher** follows AHU19's model of a unitary oracle algorithm (Ambainis, Hamburg,
  Unruh, ePrint 2018/904, pp. 8–9, quoted sentence by sentence in `GordieHowe/Model/Quantum/Pure/Algorithm.lean`):
  an initial unit vector, unitaries alternating with events, and a final computational-basis
  measurement (`Distinguisher`). Its unitaries are fixed: they depend neither on the oracle nor on
  the environment's tape. AHU19 p. 9: "A alternatingly applies a fixed unitary U on all registers
  (independent of z and O)". The single exception is the unitary `post` applied after the last slot,
  which receives the whole oracle in force at the end: the phase after the last proof query in
  everlasting zero knowledge (the paper's Definition 6.2), Fractal's "unbounded adversaries that see
  the whole oracle" (ePrint 2019/1076, p. 39). The bounded game takes `post = noPost`.

- **The adaptive schedule.** Slot `k` is one basis permutation (`Distinguisher.eventPerm`)
  controlled by the kind register: on the branches whose workspace `w` has `kind w = true` it is
  the request of slot `k`; on the others it applies the oracle to all `n` query registers at once
  (AHU19 p. 9: parallel queries "apply the oracle O to Qi, Ri for each i = 1, …, n"). So the
  distinguisher decides, after its earlier queries and responses and in superposition, when to
  request, as Unruh's adversary does (Unruh 2017, ePrint 2017/398, Definition 6, p. 14:
  `A^{H,P′}` calls its oracles in any order). Every slot is one oracle step: on request branches
  the oracle applied is the zero function, the identity. The number of queries, counting the `n`
  parallel queries of a slot separately as AHU19 p. 9 do, is at most `n * m`. A query budget
  (`Distinguisher.Budget`, `GordieHowe/Model/Quantum/Pure/Budget.lean`) bounds, on every branch, the
  number of slots at which the branch queries, and the zero-knowledge games charge `n` queries
  for each of those slots.

- **Classical requests by deferred measurement.** A classical request measures the request
  register. By the principles of deferred and implicit measurement (Nielsen–Chuang, "Quantum
  Computation and Quantum Information", section 4.4) the measurement can be replaced by a copy
  into a fresh register that no later operation changes, provided every later operation is
  block-diagonal in that register's basis. Jaeger (ePrint 2024/797, p. 8, "Principle of Deferred
  Measurement") states the same for a register that is "otherwise unused". The request of slot
  `k` copies the request register into log register `k` (`copyPerm`: the log holds `none` and
  becomes `some req`); log `k` is written by slot `k` only, so it is fresh. The distinguisher's
  unitaries act as the identity on the logs (`logControlled`), and the environment only reads
  them, so every later operation is block-diagonal in the logs.

- **The environment** (`Env`) is a deterministic function of an upfront tape `ω` drawn from a
  distribution `μ` on a finite type, as the random data of `O2HSetting` in
  `GordieHowe/Model/Quantum/O2H/Basic.lean`. The tape holds the initial oracle and the coins of the prover or the
  simulator. The environment has a classical state in a type `St`, by default the oracle in force
  itself, with the oracle in force read from it by `OracleState.toOracle`; a challenger of
  `GordieHowe/Model/Quantum/Interactive/Basic.lean` keeps its history and assignments there
  (`Challenger.toPureEnv`). The requests of a branch, in slot order, are the filled logs
  (`requests`); the request of slot `k` is request number `c`, the number of filled logs before
  slot `k`. The environment answers the first `Q` requests: request `c < Q` with logged request
  `req` gets `(respond ω c req s).response`, where `s` is the state after the earlier requests,
  and the state becomes `(respond ω c req s).state`; a request numbered `Q` or later is answered by `none`
  and leaves the state unchanged (`Env.oracleIn`, `Env.answerAfter`). The response is
  written into the response register by the basis permutation `Equiv.swap none a`
  (`respondPerm`), which turns a blank register into `a`. AHU19 p. 10: "additional oracles can
  simply be encoded as part of z"; here the tape plays the role of `z`.

- **The oracle in force** is a function of the tape and the logs: `Env.oracle ω lg` applies the
  state updates of the logged requests in slot order and reads the oracle from the state. After `step k` the game state is supported
  on the basis states whose logs from slot `k` on are blank (`Distinguisher.stage_supported`), so
  at slot `k` the oracle in force is the one after the requests of the earlier slots. Since the
  requests are in superposition, the oracle is controlled by the log registers: a basis
  permutation that leaves the logs unchanged.

- **Semantics.** For a fixed tape the game is an alternation of unitaries: the distinguisher's
  steps lifted to the game basis and, for each slot, a basis permutation, followed by `post`
  controlled by the oracle in force (`Distinguisher.final`). Its acceptance probability is
  `prob` of the lifted accepting set in the final state (`Distinguisher.acceptProbAt`), and the
  game's acceptance probability is its `μ`-average (`Distinguisher.acceptProb`).
  `Distinguisher.acceptProbOn` restricts the accepting set to the basis states whose logs lie in
  a set `L`; the hybrids of zero-knowledge proofs compare the parts of two games on the logs
  where a given request was made.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

/-! ### Unitaries controlled by a classical register -/

section Controlled

variable {ι L : Type*} [Fintype ι] [Fintype L]

/-- The unitary `∑ l, U l ⊗ |l⟩⟨l|` on the basis `ι × L`: on the basis states with second
component `l` it applies `U l` to the first component (`controlled_apply`). With a constant
family it is `U ⊗ 1`. -/
noncomputable def controlled (U : L → QState ι ≃ₗᵢ[ℂ] QState ι) :
    QState (ι × L) ≃ₗᵢ[ℂ] QState (ι × L) :=
  let e : ι × L ≃ Σ _ : L, ι := (Equiv.prodComm ι L).trans (Equiv.sigmaEquivProd L ι).symm
  let c := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).trans
    (LinearIsometryEquiv.piLpCurry ℂ 2 fun (_ : L) (_ : ι) => ℂ)
  c.trans ((LinearIsometryEquiv.piLpCongrRight 2 U).trans c.symm)

theorem controlled_apply (U : L → QState ι ≃ₗᵢ[ℂ] QState ι) (v : QState (ι × L)) (i : ι)
    (l : L) : controlled U v (i, l) = U l (WithLp.toLp 2 fun i' => v (i', l)) i :=
  rfl

end Controlled

/-! ### Supports -/

section Support

variable {ι : Type*} [Fintype ι]

/-- A vector is supported in `B` if its amplitude on every basis state outside `B` is zero. -/
def Supported (B : Set ι) (v : QState ι) : Prop :=
  ∀ r ∉ B, v r = 0

/-- A basis permutation that maps `B` into `B'` maps vectors supported in `B` to vectors
supported in `B'`. -/
theorem Supported.permOp {B B' : Set ι} {v : QState ι} (hv : Supported B v) {π : Equiv.Perm ι}
    (hπ : ∀ r ∈ B, π r ∈ B') : Supported B' (Quantum.permOp π v) := by
  intro r hr
  rw [permOp_apply]
  refine hv _ fun h => hr ?_
  simpa using hπ _ h

/-- Two basis permutations that agree on `B` act equally on vectors supported in `B`. -/
theorem Supported.permOp_eq {B : Set ι} {v : QState ι} (hv : Supported B v)
    {π π' : Equiv.Perm ι} (h : ∀ r ∈ B, π r = π' r) :
    Quantum.permOp π v = Quantum.permOp π' v := by
  ext r
  simp only [permOp_apply]
  by_cases h1 : π.symm r ∈ B
  · have : π'.symm r = π.symm r := by
      rw [Equiv.symm_apply_eq, ← h _ h1, Equiv.apply_symm_apply]
    rw [this]
  · by_cases h2 : π'.symm r ∈ B
    · have : π.symm r = π'.symm r := by
        rw [Equiv.symm_apply_eq, h _ h2, Equiv.apply_symm_apply]
      exact absurd (this ▸ h2) h1
    · rw [hv _ h1, hv _ h2]

/-- A vector supported in `B` has no weight on a set disjoint from `B`. -/
theorem Supported.prob_eq_zero {B C : Set ι} {v : QState ι} (hv : Supported B v)
    (h : ∀ r ∈ C, r ∉ B) : prob C v = 0 := by
  have hm : mask C v = 0 := by
    ext r
    by_cases hr : r ∈ C
    · rw [mask_apply_of_mem _ hr, hv _ (h r hr)]
      rfl
    · rw [mask_apply_of_notMem _ hr]
      rfl
  rw [prob, hm, norm_zero, sq, mul_zero]

/-- If the unitaries preserve the supports `B k`, the initial vector is supported in `B 0`, and
the permutation of event `k` maps `B k` into `B (k + 1)`, the alternating run is supported in
`B k` after `k` events. -/
theorem hybrid_supported (U : ℕ → QState ι ≃ₗᵢ[ℂ] QState ι) (π : ℕ → Equiv.Perm ι)
    {B : ℕ → Set ι} {ψ : QState ι} (hU : ∀ k v, Supported (B k) v → Supported (B k) (U k v))
    (hψ : Supported (B 0) ψ) (hπ : ∀ k, ∀ r ∈ B k, π k r ∈ B (k + 1)) (k : ℕ) :
    Supported (B k) (hybrid U (fun i => Quantum.permOp (π i)) ψ k) := by
  induction k with
  | zero => exact hU 0 ψ hψ
  | succ k ih => exact hU (k + 1) _ (ih.permOp (hπ k))

/-- Two alternating runs agree after `m` events if, before each event `k < m`, the second run
is supported in a set `B k` on which the two event permutations agree. -/
theorem hybrid_eq_of_supported (U : ℕ → QState ι ≃ₗᵢ[ℂ] QState ι) {π π' : ℕ → Equiv.Perm ι}
    {B : ℕ → Set ι} (ψ : QState ι) {m : ℕ}
    (hsupp : ∀ k < m, Supported (B k) (hybrid U (fun i => Quantum.permOp (π' i)) ψ k))
    (hagree : ∀ k < m, ∀ r ∈ B k, π k r = π' k r) :
    hybrid U (fun i => Quantum.permOp (π i)) ψ m =
      hybrid U (fun i => Quantum.permOp (π' i)) ψ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [hybrid_succ, hybrid_succ,
      ih (fun k hk => hsupp k (hk.trans m.lt_succ_self))
        (fun k hk => hagree k (hk.trans m.lt_succ_self)),
      (hsupp m m.lt_succ_self).permOp_eq (hagree m m.lt_succ_self)]

end Support

/-! ### Registers -/

/-- The log registers of `m` slots: register `k` holds `none` unless slot `k` made a request,
which is copied into it. -/
abbrev LogReg (Req : Type*) (m : ℕ) := Fin m → Option Req

/-- The computational basis of the distinguisher's registers: a workspace `W`, a request
register `Req`, a response register `Option A` whose blank value is `none`, and `n` query
registers. -/
abbrev DReg (W : Type*) (n : ℕ) (X Y Req A : Type*) := QueryReg (W × Req × Option A) n X Y

/-- Decidable equality on the distinguisher's registers, assembled from the workspace factor (the
default search exceeds its size limit on the nested registers of the simulations). -/
instance DReg.instDecidableEq {W : Type*} {n : ℕ} {X Y Req A : Type*} [DecidableEq W]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Req] [DecidableEq A] :
    DecidableEq (DReg W n X Y Req A) :=
  have : DecidableEq (W × Req × Option A) := inferInstance
  inferInstance

/-- The computational basis of the game: the distinguisher's registers and the log registers.
The logs sit beside the workspace, so the basis is a `QueryReg` and oracles act on it as in
`GordieHowe/Model/Quantum/Core/Oracle.lean`. -/
abbrev GameReg (W : Type*) (n : ℕ) (X Y Req A : Type*) (m : ℕ) :=
  QueryReg (W × Req × Option A × LogReg Req m) n X Y

section Registers

variable {W X Y Req A : Type*} {n m : ℕ}

/-- The workspace of a basis state of the distinguisher's registers. -/
abbrev DReg.workspace (r : DReg W n X Y Req A) : W := r.1.1

/-- The request register of a basis state of the distinguisher's registers. -/
abbrev DReg.request (r : DReg W n X Y Req A) : Req := r.1.2.1

/-- The response register of a basis state of the distinguisher's registers. -/
abbrev DReg.response (r : DReg W n X Y Req A) : Option A := r.1.2.2

/-- The workspace of a game basis state. -/
abbrev GameReg.workspace (r : GameReg W n X Y Req A m) : W := r.1.1

/-- The request register of a game basis state. -/
abbrev GameReg.request (r : GameReg W n X Y Req A m) : Req := r.1.2.1

/-- The response register of a game basis state. -/
abbrev GameReg.response (r : GameReg W n X Y Req A m) : Option A := r.1.2.2.1

/-- The log registers of a game basis state. -/
abbrev GameReg.logs (r : GameReg W n X Y Req A m) : LogReg Req m := r.1.2.2.2

/-- A game basis state as a pair of a distinguisher basis state and the logs. -/
def splitLogs : GameReg W n X Y Req A m ≃ DReg W n X Y Req A × LogReg Req m where
  toFun r := (((r.1.1, r.1.2.1, r.1.2.2.1), r.2), r.1.2.2.2)
  invFun p := ((p.1.1.1, p.1.1.2.1, p.1.1.2.2, p.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]

/-- The unitary that applies `U lg` to the distinguisher's registers on the basis states whose
logs are `lg`, and leaves the logs unchanged. With a constant family it is a distinguisher
unitary tensored with the identity on the logs. -/
noncomputable def logControlled
    (U : LogReg Req m → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)) :
    QState (GameReg W n X Y Req A m) ≃ₗᵢ[ℂ] QState (GameReg W n X Y Req A m) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ splitLogs).trans
    ((controlled U).trans (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ splitLogs).symm)

theorem logControlled_apply
    (U : LogReg Req m → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (v : QState (GameReg W n X Y Req A m)) (r : GameReg W n X Y Req A m) :
    logControlled U v r = U (splitLogs r).2
      (WithLp.toLp 2 fun d => v (splitLogs.symm (d, (splitLogs r).2))) (splitLogs r).1 :=
  rfl

/-- The game basis states whose logs lie in `L`. -/
def logsIn (L : Set (LogReg Req m)) : Set (GameReg W n X Y Req A m) :=
  {r | (splitLogs r).2 ∈ L}

omit [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] in
@[simp]
theorem mem_logsIn {L : Set (LogReg Req m)} {r : GameReg W n X Y Req A m} :
    r ∈ logsIn L ↔ (splitLogs r).2 ∈ L :=
  Iff.rfl

/-- The slice of a vector supported in `logsIn L` at logs outside `L` is zero. -/
theorem Supported.slice_eq_zero {L : Set (LogReg Req m)} {v : QState (GameReg W n X Y Req A m)}
    (hv : Supported (logsIn L) v) {lg : LogReg Req m} (hlg : lg ∉ L) :
    (WithLp.toLp 2 fun d => v (splitLogs.symm (d, lg)) : QState (DReg W n X Y Req A)) = 0 := by
  ext d
  exact hv _ (by simpa using hlg)

/-- A log-controlled unitary preserves supports of the form `logsIn L`. -/
theorem Supported.logControlled {L : Set (LogReg Req m)} {v : QState (GameReg W n X Y Req A m)}
    (hv : Supported (logsIn L) v)
    (U : LogReg Req m → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)) :
    Supported (logsIn L) (Quantum.logControlled U v) := by
  intro r hr
  rw [logControlled_apply, hv.slice_eq_zero hr, map_zero]
  rfl

/-- Two log-controlled unitaries that agree at every log in `L` act equally on vectors supported
in `logsIn L`. -/
theorem Supported.logControlled_eq {L : Set (LogReg Req m)}
    {v : QState (GameReg W n X Y Req A m)} (hv : Supported (logsIn L) v)
    {U U' : LogReg Req m → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)}
    (h : ∀ lg ∈ L, U lg = U' lg) : Quantum.logControlled U v = Quantum.logControlled U' v := by
  ext r
  rw [logControlled_apply, logControlled_apply]
  by_cases hr : (splitLogs r).2 ∈ L
  · rw [h _ hr]
  · rw [hv.slice_eq_zero hr, map_zero, map_zero]

/-- A log-controlled unitary commutes with the mask of the basis states whose logs lie in `N`. -/
theorem mask_logControlled (N : Set (LogReg Req m))
    (U : LogReg Req m → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (v : QState (GameReg W n X Y Req A m)) :
    mask (logsIn N) (Quantum.logControlled U v) = Quantum.logControlled U (mask (logsIn N) v) := by
  ext r
  rw [logControlled_apply]
  by_cases hr : (splitLogs r).2 ∈ N
  · rw [mask_apply_of_mem _ (by simpa using hr), logControlled_apply]
    have : (WithLp.toLp 2 fun d => (mask (logsIn N) v) (splitLogs.symm (d, (splitLogs r).2)) :
        QState (DReg W n X Y Req A)) = WithLp.toLp 2 fun d => v (splitLogs.symm (d, (splitLogs r).2)) := by
      ext d
      simp [hr]
    rw [this]
  · rw [mask_apply_of_notMem _ (by simpa using hr)]
    have : (WithLp.toLp 2 fun d => (mask (logsIn N) v) (splitLogs.symm (d, (splitLogs r).2)) :
        QState (DReg W n X Y Req A)) = 0 := by
      ext d
      simp [hr]
    rw [this, map_zero]
    rfl

end Registers

/-! ### Requests -/

section Requests

variable {W Req A : Type*} {m : ℕ} [DecidableEq Req] [DecidableEq A] (kind : W → Bool)

/-- The log copy of slot `k`, deferred measurement: on the branches whose workspace has
`kind = true`, swap `none` and `some req` in log register `k` (a blank log becomes `some req`);
the identity elsewhere. -/
def copyPerm (k : Fin m) : Equiv.Perm (W × Req × Option A × LogReg Req m) :=
  Function.Involutive.toPerm
    (fun s => if kind s.1 then (s.1, s.2.1, s.2.2.1,
      Function.update s.2.2.2 k (Equiv.swap none (some s.2.1) (s.2.2.2 k))) else s)
    fun s => by by_cases h : kind s.1 <;> simp [h]

/-- Write the response `a lg`, a function of the logs, into the response register on the branches
whose workspace has `kind = true`, as the swap of `none` and `a lg` (a blank register becomes
`a lg`); the identity elsewhere. -/
def respondPerm (a : LogReg Req m → Option A) :
    Equiv.Perm (W × Req × Option A × LogReg Req m) :=
  Function.Involutive.toPerm
    (fun s => if kind s.1 then (s.1, s.2.1, Equiv.swap none (a s.2.2.2) s.2.2.1, s.2.2.2) else s)
    fun s => by by_cases h : kind s.1 <;> simp [h]

theorem copyPerm_apply (k : Fin m) (s : W × Req × Option A × LogReg Req m) :
    copyPerm kind k s = if kind s.1 then (s.1, s.2.1, s.2.2.1,
      Function.update s.2.2.2 k (Equiv.swap none (some s.2.1) (s.2.2.2 k))) else s :=
  rfl

theorem respondPerm_apply (a : LogReg Req m → Option A) (s : W × Req × Option A × LogReg Req m) :
    respondPerm kind a s =
      if kind s.1 then (s.1, s.2.1, Equiv.swap none (a s.2.2.2) s.2.2.1, s.2.2.2) else s :=
  rfl

end Requests

/-! ### The requests of a branch -/

section Logs

variable {Req : Type*} {m : ℕ}

/-- The logs that can carry nonzero amplitude just before slot `k`: every log from slot `k` on is
blank. -/
def reachableLogs (k : ℕ) : Set (LogReg Req m) :=
  {lg | ∀ k' : Fin m, k ≤ k' → lg k' = none}

/-- The requests logged before slot `k`, in slot order. -/
def requestsBefore (lg : LogReg Req m) : ℕ → List Req
  | 0 => []
  | k + 1 => requestsBefore lg k ++ if h : k < m then (lg ⟨k, h⟩).toList else []

/-- The requests of a branch: its filled logs, in slot order. -/
def requests (lg : LogReg Req m) : List Req :=
  requestsBefore lg m

theorem requestsBefore_succ_of_lt (lg : LogReg Req m) {k : ℕ} (h : k < m) :
    requestsBefore lg (k + 1) = requestsBefore lg k ++ (lg ⟨k, h⟩).toList := by
  simp [requestsBefore, h]

/-- Blank logs add no requests: if every log from slot `a` on is blank, the requests before
slot `b ≥ a` are those before slot `a`. -/
theorem requestsBefore_eq_of_blank {lg : LogReg Req m} {a b : ℕ} (hab : a ≤ b)
    (h : ∀ k' : Fin m, a ≤ k' → lg k' = none) : requestsBefore lg b = requestsBefore lg a := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    rw [requestsBefore, ih]
    split_ifs with hb
    · simp [h ⟨b, hb⟩ hab]
    · simp

/-- If every log from slot `k` on is blank, the requests of the branch are those before slot
`k`. -/
theorem requests_eq_requestsBefore {lg : LogReg Req m} {k : ℕ}
    (h : ∀ k' : Fin m, k ≤ k' → lg k' = none) : requests lg = requestsBefore lg k := by
  rcases le_total k m with hk | hk
  · exact requestsBefore_eq_of_blank hk h
  · exact (requestsBefore_eq_of_blank hk fun k' hk' => absurd k'.2 (by omega)).symm

/-- The requests before slot `k` do not see log `k` or later logs. -/
theorem requestsBefore_congr {lg lg' : LogReg Req m} :
    ∀ {k : ℕ}, (∀ k' : Fin m, (k' : ℕ) < k → lg k' = lg' k') →
      requestsBefore lg k = requestsBefore lg' k
  | 0, _ => rfl
  | k + 1, h => by
    rw [requestsBefore, requestsBefore, requestsBefore_congr fun k' hk' => h k' (by omega)]
    split_ifs with hk
    · rw [h ⟨k, hk⟩ (by simp)]
    · rfl

/-- Filling the blank log of slot `k`, with every later log blank, appends the request. -/
theorem requests_update {lg : LogReg Req m} {k : Fin m}
    (h : ∀ k' : Fin m, (k : ℕ) < k' → lg k' = none) (req : Req) :
    requests (Function.update lg k (some req)) = requestsBefore lg k ++ [req] := by
  rw [requests_eq_requestsBefore (k := k + 1) fun k' hk' => by
      rw [Function.update_of_ne (fun e => by subst e; omega)]
      exact h k' (by omega),
    requestsBefore_succ_of_lt _ k.2, Function.update_self]
  simp only [Option.toList_some]
  congr 1
  exact requestsBefore_congr fun k' hk' => Function.update_of_ne (fun e => by subst e; omega) _ _

end Logs

/-! ### Environments -/

/-- A type of environment states from which the oracle in force is read. The oracle itself,
`X → Y`, is such a state (`toOracle = id`); a stateful challenger's state holds its history
(`GordieHowe/Model/Quantum/Interactive/Basic.lean`). -/
class OracleState (St X Y : Type*) where
  /-- The oracle in force at a state. -/
  toOracle : St → X → Y

instance (X Y : Type*) : OracleState (X → Y) X Y :=
  ⟨id⟩

@[simp]
theorem OracleState.toOracle_fun {X Y : Type*} (H : X → Y) : OracleState.toOracle H = H :=
  rfl

/-- **An environment's reply** to a request: the response (`none` for no response) and the
environment's state after the request. -/
@[ext]
structure EnvReply (A St : Type*) where
  /-- The response. -/
  response : Option A
  /-- The state after the request. -/
  state : St

/-- A reply as its response and its state. -/
def EnvReply.equivProd (A St : Type*) : EnvReply A St ≃ Option A × St where
  toFun r := (r.response, r.state)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance {A St : Type*} [Fintype A] [Fintype St] : Fintype (EnvReply A St) :=
  Fintype.ofEquiv _ (EnvReply.equivProd A St).symm

instance {A St : Type*} [DecidableEq A] [DecidableEq St] : DecidableEq (EnvReply A St) :=
  (EnvReply.equivProd A St).decidableEq

instance {A St : Type*} [Nonempty St] : Nonempty (EnvReply A St) :=
  ⟨⟨none, Classical.arbitrary St⟩⟩

/-- An environment for `Q` classical requests with requests in `Req`, responses in `Option A`,
oracle `X → Y` and states in `St` (by default the oracle in force itself): a deterministic
function of a tape `ω ← μ`. This is a classical stateful oracle with all its coins drawn up front
(Unruh 2017, ePrint 2017/398, section 3, p. 8: "An oracle O consists of a state space H_O and a
quantum operation E_O", here classical).

- `oracle₀ ω` is the state before the first request;
- `respond ω c req s` is the reply to request number `c` with logged request `req` in state
  `s`: the response and the state after the request;
- the oracle in force at a state is `OracleState.toOracle`. -/
structure Env.{u, v} (Ω Req A : Type*) (X : Type u) (Y : Type v) (Q : ℕ)
    (St : Type (max u v) := X → Y) where
  /-- The distribution of the tape. -/
  μ : PMF Ω
  /-- The state before the first request. -/
  oracle₀ : Ω → St
  /-- The reply to request number `c`: the response and the state after it. -/
  respond : Ω → Fin Q → Req → St → EnvReply A St

namespace Env

variable {Ω Req A X Y : Type*} {St : Type _} {Q : ℕ} (E : Env Ω Req A X Y Q St)

/-- The state update of request number `c` with logged request `req`; requests numbered `Q` or
later leave the state unchanged. -/
def update (ω : Ω) (H : St) (p : Req × ℕ) : St :=
  if h : p.2 < Q then (E.respond ω ⟨p.2, h⟩ p.1 H).state else H

/-- The state after the requests `rs`, in order: the updates of `respond` applied to
`oracle₀ ω`. For `St = X → Y` it is the oracle in force. -/
def oracleIn (ω : Ω) (rs : List Req) : St :=
  rs.zipIdx.foldl (E.update ω) (E.oracle₀ ω)

/-- The response to the request `req` made after the requests `rs`: request number
`rs.length` is answered by `respond` on the oracle in force, and a request numbered `Q` or later
by `none`. -/
def answerAfter (ω : Ω) (rs : List Req) (req : Req) : Option A :=
  if h : rs.length < Q then (E.respond ω ⟨rs.length, h⟩ req (E.oracleIn ω rs)).response
  else none

theorem oracleIn_nil (ω : Ω) : E.oracleIn ω [] = E.oracle₀ ω :=
  rfl

theorem oracleIn_append_singleton (ω : Ω) (rs : List Req) (req : Req) :
    E.oracleIn ω (rs ++ [req]) = E.update ω (E.oracleIn ω rs) (req, rs.length) := by
  simp [oracleIn, List.zipIdx_append, List.foldl_append]

/-- Two environments compute the same oracle after `rs` if they start from the same oracle and
give each request of `rs` the same oracle update, at the oracle in force before it. -/
theorem oracleIn_eq_of_update_eq {Ω' : Type*} (E' : Env Ω' Req A X Y Q St) {ω : Ω} {ω' : Ω'}
    (h0 : E.oracle₀ ω = E'.oracle₀ ω') (rs : List Req)
    (h : ∀ (i : ℕ) (hi : i < rs.length), E.update ω (E.oracleIn ω (rs.take i)) (rs[i], i) =
      E'.update ω' (E.oracleIn ω (rs.take i)) (rs[i], i)) :
    E.oracleIn ω rs = E'.oracleIn ω' rs := by
  induction rs using List.reverseRecOn with
  | nil => exact h0
  | append_singleton l a ih =>
    have ih' := ih fun i hi => by
      have := h i (by simp; omega)
      simpa [List.take_append_of_le_length hi.le, List.getElem_append_left hi] using this
    rw [oracleIn_append_singleton, oracleIn_append_singleton, ← ih']
    simpa using h l.length (by simp)

/-- The oracle in force given the logs: the oracle of the state after the logged requests in slot
order. -/
def oracle [OracleState St X Y] {m : ℕ} (ω : Ω) (lg : LogReg Req m) : X → Y :=
  OracleState.toOracle (E.oracleIn ω (requests lg))

/-- The response of slot `k` given the logs: `answerAfter` for the requests before slot `k`, or
`none` if log `k` is blank. -/
def answer {m : ℕ} (ω : Ω) (lg : LogReg Req m) (k : Fin m) : Option A :=
  (lg k).elim none (E.answerAfter ω (requestsBefore lg k))

variable {W : Type*} {n m : ℕ} [AddGroup Y] [DecidableEq Req] [DecidableEq A] [OracleState St X Y]
  (kind : W → Bool)

/-- The request of slot `k` on tape `ω`, on the branches whose workspace has `kind = true`: copy
the request into log `k`, then write the response. -/
def requestPerm (ω : Ω) (k : Fin m) : Equiv.Perm (GameReg W n X Y Req A m) :=
  Equiv.prodCongr ((copyPerm kind k).trans (respondPerm kind fun lg => E.answer ω lg k))
    (Equiv.refl _)

/-- The oracle on tape `ω`, on the branches whose workspace has `kind = false`, controlled by the
logs: `queryPermOf` with `E.oracle ω lg`, and the zero function on the request branches. -/
def oraclePerm (ω : Ω) : Equiv.Perm (GameReg W n X Y Req A m) :=
  queryPermOf fun s => if kind s.1 then 0 else E.oracle ω s.2.2.2

omit [AddGroup Y] [OracleState St X Y] in
/-- A request changes only log `k`, on the request branches, by swapping `none` and the request. -/
theorem logs_requestPerm (ω : Ω) (k : Fin m) (r : GameReg W n X Y Req A m) :
    (splitLogs (E.requestPerm kind ω k r)).2 = if kind r.workspace then
      Function.update (splitLogs r).2 k (Equiv.swap none (some r.request) ((splitLogs r).2 k))
      else (splitLogs r).2 := by
  by_cases h : kind r.workspace <;> simp [requestPerm, copyPerm_apply, respondPerm_apply, h, splitLogs]

omit [DecidableEq Req] [DecidableEq A] in
/-- The oracle leaves the logs unchanged. -/
theorem logs_oraclePerm (ω : Ω) (r : GameReg W n X Y Req A m) :
    (splitLogs (E.oraclePerm kind ω r)).2 = (splitLogs r).2 :=
  rfl

omit [AddGroup Y] [OracleState St X Y] in
/-- A request leaves the workspace unchanged. -/
theorem workspace_requestPerm (ω : Ω) (k : Fin m) (r : GameReg W n X Y Req A m) :
    (E.requestPerm kind ω k r).1.1 = r.workspace := by
  by_cases h : kind r.workspace <;> simp [requestPerm, copyPerm_apply, respondPerm_apply, h]

end Env

/-! ### Distinguishers -/

/-- A distinguisher with workspace `W`, `n` parallel query registers for an oracle `X → Y`,
requests in `Req` with responses in `Option A`, and `m` slots. The run is `step 0`, slot `0`,
`step 1`, …, slot `m - 1`, `step m`, then a computational-basis measurement with accepting set
`accept`. At each slot, the branches whose workspace `w` has `kind w = true` make a request and
the others query the oracle. The initial state and the steps depend on neither the oracle nor
the environment. -/
structure Distinguisher (W X Y Req A : Type*) [Fintype W] [Fintype X] [Fintype Y] [Fintype Req]
    [Fintype A] (n m : ℕ) where
  /-- The kind register: request (`true`) or query (`false`), read from the workspace. -/
  kind : W → Bool
  /-- The initial state of the distinguisher's registers. -/
  init : QState (DReg W n X Y Req A)
  norm_init : ‖init‖ = 1
  /-- `step k` is applied after slot `k - 1` (`step 0` first). -/
  step : Fin (m + 1) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)
  /-- The outcomes of the final measurement on which the distinguisher outputs `1`. -/
  accept : Set (DReg W n X Y Req A)

/-- The final unitary of the bounded game: the identity for every oracle. -/
noncomputable def noPost {X Y DR : Type*} [Fintype DR] : (X → Y) → QState DR ≃ₗᵢ[ℂ] QState DR :=
  fun _ => LinearIsometryEquiv.refl ℂ _

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} (D : Distinguisher W X Y Req A n m)

/-- The steps indexed by `ℕ`, extended by the identity after `step m`. -/
noncomputable def stepAt (k : ℕ) : QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A) :=
  if h : k < m + 1 then D.step ⟨k, h⟩ else LinearIsometryEquiv.refl ℂ _

variable [DecidableEq Req] [DecidableEq A]

/-- The initial game state: the distinguisher's initial state with every log blank. -/
def gameInit : QState (GameReg W n X Y Req A m) :=
  WithLp.toLp 2 fun r => if (splitLogs r).2 = fun _ => none then D.init (splitLogs r).1 else 0

omit [DecidableEq A] in
theorem norm_gameInit : ‖D.gameInit‖ = 1 := by
  have h : ‖D.gameInit‖ ^ 2 = ‖D.init‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, ← splitLogs.symm.sum_comp,
      Fintype.sum_prod_type]
    refine sum_congr rfl fun d _ => ?_
    rw [Finset.sum_eq_single (fun _ => none)]
    · simp [gameInit]
    · intro lg _ hlg
      simp [gameInit, hlg]
    · simp
  rw [D.norm_init, one_pow] at h
  exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 (by rw [h, one_pow])

omit [DecidableEq A] in
theorem gameInit_supported : Supported (logsIn (reachableLogs 0)) D.gameInit := by
  intro r hr
  have hne : (splitLogs r).2 ≠ fun _ => none := fun h => hr (by
    simp [reachableLogs, h])
  simp [gameInit, hne]

/-- The accepting set on the game basis: the distinguisher's accepting set, any logs. -/
def gameAccept : Set (GameReg W n X Y Req A m) :=
  {r | (splitLogs r).1 ∈ D.accept}

variable {Ω : Type*} {St : Type _} [AddGroup Y] {Q : ℕ} [OracleState St X Y]
  (E : Env Ω Req A X Y Q St)

/-- The basis permutation of slot `k` on tape `ω`: the request of slot `k` on the request
branches, then the oracle on the query branches; the identity from slot `m` on. -/
def eventPerm (ω : Ω) (k : ℕ) : Equiv.Perm (GameReg W n X Y Req A m) :=
  if h : k < m then (E.requestPerm D.kind ω ⟨k, h⟩).trans (E.oraclePerm D.kind ω)
  else Equiv.refl _

/-- Every slot permutation maps the reachable basis states before slot `k` to the reachable basis
states before slot `k + 1`. -/
theorem eventPerm_mem_reachableSet (ω : Ω) {k : ℕ} {r : GameReg W n X Y Req A m}
    (hr : r ∈ logsIn (reachableLogs k)) : D.eventPerm E ω k r ∈ logsIn (reachableLogs (k + 1)) := by
  simp only [mem_logsIn, reachableLogs, Set.mem_setOf_eq] at hr ⊢
  unfold eventPerm
  split_ifs with hk
  · intro k' hk'
    rw [Equiv.trans_apply, Env.logs_oraclePerm, Env.logs_requestPerm]
    split_ifs
    · rw [Function.update_of_ne (fun e => by subst e; simp at hk')]
      exact hr k' (by omega)
    · exact hr k' (by omega)
  · intro k' hk'
    exact hr k' (by omega)

/-- The distinguisher's step `k`, tensored with the identity on the logs. -/
noncomputable def liftedStep (k : ℕ) :
    QState (GameReg W n X Y Req A m) ≃ₗᵢ[ℂ] QState (GameReg W n X Y Req A m) :=
  logControlled fun _ => D.stepAt k

/-- The game state on tape `ω` after `step k`: the lifted steps alternating with the slot
permutations. -/
noncomputable def stage (ω : Ω) (k : ℕ) : QState (GameReg W n X Y Req A m) :=
  hybrid D.liftedStep (fun k => permOp (D.eventPerm E ω k)) D.gameInit k

theorem stage_succ (ω : Ω) (k : ℕ) :
    D.stage E ω (k + 1) = D.liftedStep (k + 1) (permOp (D.eventPerm E ω k) (D.stage E ω k)) :=
  rfl

/-- The game state on tape `ω` after `step m`. -/
noncomputable def run (ω : Ω) : QState (GameReg W n X Y Req A m) :=
  D.stage E ω m

omit [DecidableEq A] [AddGroup Y] in
/-- Every run whose slot permutations map reachable states to reachable states is supported,
after `step k`, on the basis states whose logs are reachable before slot `k`. -/
theorem hybrid_supported_reachable (π : ℕ → Equiv.Perm (GameReg W n X Y Req A m))
    (hπ : ∀ k, ∀ r ∈ logsIn (reachableLogs k), π k r ∈ logsIn (reachableLogs (k + 1))) (k : ℕ) :
    Supported (logsIn (reachableLogs k)) (hybrid D.liftedStep (fun i => permOp (π i)) D.gameInit k) :=
  hybrid_supported (B := fun k => logsIn (reachableLogs k)) _ _ (fun _ _ hv => hv.logControlled _)
    D.gameInit_supported hπ k

/-- After `step k` the game state is supported on the basis states whose logs from slot `k` on
are blank. -/
theorem stage_supported (ω : Ω) (k : ℕ) : Supported (logsIn (reachableLogs k)) (D.stage E ω k) :=
  D.hybrid_supported_reachable _ (fun _ _ hr => D.eventPerm_mem_reachableSet E ω hr) k

/-- A slot leaves the workspace unchanged. -/
theorem workspace_eventPerm (ω : Ω) (k : ℕ) (r : GameReg W n X Y Req A m) :
    (D.eventPerm E ω k r).workspace = r.workspace := by
  unfold eventPerm
  split_ifs
  · rw [Equiv.trans_apply]
    exact E.workspace_requestPerm D.kind ω _ r
  · rfl

/-- The final game state on tape `ω`: after `run`, the unitary `post H` with `H` the oracle in
force, controlled by the logs. -/
noncomputable def final
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (ω : Ω) : QState (GameReg W n X Y Req A m) :=
  logControlled (fun lg => post (E.oracle ω lg)) (D.run E ω)

/-- The probability that the distinguisher outputs `1` on tape `ω`, with logs in `L`. -/
noncomputable def acceptProbOnAt
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (L : Set (LogReg Req m)) (ω : Ω) : ℝ :=
  prob (D.gameAccept ∩ logsIn L) (D.final E post ω)

/-- The probability that the distinguisher outputs `1` on tape `ω`. -/
noncomputable def acceptProbAt
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (ω : Ω) : ℝ :=
  prob D.gameAccept (D.final E post ω)

/-- The probability that the distinguisher outputs `1` with logs in `L`: the average of
`acceptProbOnAt` over the tape `ω ← E.μ`. -/
noncomputable def acceptProbOn [Fintype Ω]
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (L : Set (LogReg Req m)) : ℝ :=
  ∑ ω, (E.μ ω).toReal * D.acceptProbOnAt E post L ω

/-- The probability that the distinguisher outputs `1`: the average of `acceptProbAt` over the
tape `ω ← E.μ`. -/
noncomputable def acceptProb [Fintype Ω]
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)) : ℝ :=
  ∑ ω, (E.μ ω).toReal * D.acceptProbAt E post ω

theorem acceptProbOnAt_univ
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)) (ω : Ω) :
    D.acceptProbOnAt E post Set.univ ω = D.acceptProbAt E post ω := by
  simp [acceptProbOnAt, acceptProbAt, logsIn]

theorem acceptProbOn_univ [Fintype Ω]
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)) :
    D.acceptProbOn E post Set.univ = D.acceptProb E post := by
  simp [acceptProbOn, acceptProb, acceptProbOnAt_univ]

end Distinguisher

end GordieHowe.Quantum
