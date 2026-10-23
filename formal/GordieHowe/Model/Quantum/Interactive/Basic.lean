-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Core.Reprogram
public import GordieHowe.Model.Quantum.Pure.Game
public import GordieHowe.Model.NARG.OracleProg

@[expose] public section

/-!
# Interactive adversaries and classical challengers

An interactive adversary (`IAlg`) is a mixed adversary that, besides querying the random oracle,
makes classical requests to a challenger, at slots fixed in advance by its schedule (`sched`; the
fixed execution schedule `op_C` of Unruh's pure oracle circuits, Unruh 2017 section 3, p. 8, which
his extractability definitions use). Unruh's zero-knowledge adversaries are oracle algorithms
(p. 10), which choose at run time which oracle to call; those are `AdaptiveIAlg`
(`GordieHowe/Model/Quantum/Interactive/Adaptive.lean`), translated through the same `KindAlg` with the kind
read from the workspace. The contents of queries are quantum,
and a request is measured in the computational basis at its slot (`measReq`), so the challenger
receives a classical request. A challenger (`Challenger`) is a classical stateful
oracle with its coins drawn up front: Unruh 2017 (ePrint 2017/398), section 3, p. 8, "An oracle O
consists of a state space H_O and a quantum operation E_O", here classical, in the challenger
model of GHS16 (p. 10: "A does not automatically gain access to the inverse (adjoint) of quantum
operations performed by C, and C cannot be 'rewound' by the adversary"). Its reply to a request
may depend on the whole earlier history of requests and replies, its coins, and the oracle
values it reads with classical queries (AHU19 p. 9, "Classical oracles measure both their input
and their output"). A deterministic stateful challenger with up-front coins is of this form when
its state after a history is a function of the coins and the history; one whose state depends on
the oracle answers it read need not be. The challengers of the zero-knowledge and
simulation-extraction games are stateless. A reply may also reprogram
the oracle by an assignment list (Unruh 2017 section 2, p. 7).

The semantics of an interactive adversary with a challenger is **defined** by translation into
one core algorithm (`IAlg.compose`, `GordieHowe/Model/Quantum/Core/Model.lean`), whose query depth counts the
adversary's queries at its query slots, the challenger's classical queries at the request slots
and the post-phase queries (`IAlg.compose_depth`: `requests · q + querySlots · width +
width · post`).

## The translation (`compose`)

The work register of the composed algorithm holds the adversary's registers
(`DReg W width X Y Req Resp`: workspace, request, response, `width` query pairs), one log register
per slot (`LogReg Req slots`), a register of `q` query pairs per slot for the challenger's
classical queries, the challenger's coins, a classical slot counter (`IAlg.toKindAlg`, from which the
schedule is read as a kind bit on the workspace), and the ancilla of the reprogrammed query
(`GordieHowe/Model/Quantum/Core/Reprogram.lean`). The challenger's coins are a classical register in `ρ_init`, drawn
from its distribution. Slot `j` is (`Quantum.KindAlg.slotCirc (sched j) j`):

1. the adversary's Kraus map number `j`;
2. a measurement Kraus map (`measReq`) of the kind bit and the request register, whose outcome is
   copied into log `j`: the request becomes classical (ABKM22 p. 4: the purification of a
   measuring adversary is not used to define the model);
3. at a request slot, the challenger's `q` classical queries, each an ordinary query of the core on
   a basis state: the query input is computed from the coins, the history (read from the logs and
   the earlier answers) and the earlier answers of this request (`OracleProg.next`); the query is a
   reprogrammed query for the assignments in force; the query pair is then moved into the
   challenger's register for slot `j`. Steps after the program has returned are padded: the query
   reads the all-zero assignment list (`paddingAssignments`), so it adds `0`;
4. the challenger's reply, a function of the same classical registers, written into the
   response register;
5. at a query slot, the adversary's `width` queries, one after another (each query pair is
   exchanged with the query register), each a reprogrammed query for
   the assignments in force.

After the last slot come `post` batches of `width` reprogrammed queries for the final assignments,
with the adversary's remaining Kraus maps between them; these queries are counted by
`compose_depth` but not by the adversary's query bound (Fractal p. 39, "unbounded adversaries
that see the whole oracle"). The output is read from the adversary's workspace.
-/

open Finset Matrix
open scoped BigOperators ENNReal Kronecker ComplexOrder MatrixOrder

namespace GordieHowe.Quantum


/-! ### Programs fed with answers -/

namespace OracleProgAns

variable {A B R : Type*}

/-- The result of `p` once fed the answers `ans` to its queries, if it has returned. -/
def result : OracleProg A B R → List B → Option R
  | .pure r, _ => some r
  | .query _ _, [] => none
  | .query _ k, b :: ans => result (k b) ans

/-- Whether `p` makes a further query after the answers `ans`. -/
def wants : OracleProg A B R → List B → Bool
  | .pure _, _ => false
  | .query _ _, [] => true
  | .query _ k, b :: ans => wants (k b) ans

end OracleProgAns

/-! ### Interactive adversaries -/

/-! ### Kraus map indices -/

/-- **The index of a Kraus map** of an interactive adversary with `slots` slots and `post` query
batches after them: the run is `step 0`, slot `0`, `step 1`, …, slot `slots - 1`, `step slots`, then
the post batches with `step (slots + 1)`, …, `step (slots + post)` between and after them. -/
abbrev StepIdx (slots post : ℕ) : Type := Fin (slots + post + 1)

/-- The Kraus map before slot `j`. -/
abbrev slotStep {slots post : ℕ} (j : Fin slots) : StepIdx slots post := ⟨j, by omega⟩

/-- The Kraus map before post batch `b`. -/
abbrev postStep {slots post : ℕ} (b : Fin post) : StepIdx slots post := ⟨slots + b, by omega⟩

/-- The last Kraus map, after the last post batch. -/
abbrev lastStep {slots post : ℕ} : StepIdx slots post := ⟨slots + post, by omega⟩

/-- **An interactive mixed adversary with a kind register** (proof-internal): as `IAlg`, except that
whether slot `j` is a request is read from the workspace (`kind`) rather than fixed by a schedule.
It is the form of the distinguishers of `GordieHowe/Model/Quantum/Pure/Game.lean`, and the translation
(`IAlg.compose`) and the pure game (`KindAlg.composeBoth_eq_pureGame`) are proved through it: an
`IAlg` is a `KindAlg` whose workspace carries a slot counter (`Quantum.IAlg.toKindAlg`). The run is
`step 0`, slot `0`, `step 1`, …, slot `slots - 1`, `step slots`, then `post` batches of `width`
queries with `step (slots + 1)`, …, `step (slots + post)` between and after them. -/
structure KindAlg (X Y Req Resp O : Type) [Fintype X] [Fintype Y] [Fintype Req] [Fintype Resp]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Req] [DecidableEq Resp] where
  /-- The workspace. -/
  W : Type
  [instFintypeW : Fintype W]
  [instDecidableEqW : DecidableEq W]
  /-- The number of parallel query pairs. -/
  width : ℕ
  width_pos : 0 < width
  /-- The number of slots. -/
  slots : ℕ
  /-- The number of query batches after the last slot. -/
  post : ℕ
  /-- The kind bit: request (`true`) or query (`false`). -/
  kind : W → Bool
  /-- The index type of the Kraus operators. -/
  R : Type
  [instFintypeR : Fintype R]
  /-- The initial state. -/
  init : MState (DReg W width X Y Req Resp)
  /-- The Kraus maps. -/
  step : StepIdx slots post →
    KrausMap R (DReg W width X Y Req Resp) (DReg W width X Y Req Resp)
  /-- The output read from the workspace. -/
  out : W → O

attribute [instance] KindAlg.instFintypeW KindAlg.instDecidableEqW KindAlg.instFintypeR

/-- **An entry of a challenger's history**: a request and the response it received (`none` for
no response). -/
structure HistoryEntry (Req Resp : Type) where
  /-- The request. -/
  request : Req
  /-- The response. -/
  response : Option Resp

/-- **A challenger's reply** to a request: the response (`none` for no response) and the
assignments appended to the assignments in force (Unruh 2017 section 2, p. 7). -/
structure Reply (X Y Resp : Type) where
  /-- The response. -/
  response : Option Resp
  /-- The new assignments. -/
  assignments : List (Assignment X Y)

/-- **A challenger's record** after some requests: its history and the assignments in force. -/
structure ChallengerRecord (X Y Req Resp : Type) where
  /-- The requests and responses so far, in order. -/
  history : List (HistoryEntry Req Resp)
  /-- The assignments in force. -/
  assignments : List (Assignment X Y)

/-- **A classical challenger** (GHS16 p. 10, "challenger model") with requests in `Req` and replies in `Option Resp`: coins drawn
up front from `coins`, independently of the oracle; requests numbered `Q` or later get `none`;
the reply to a request is the result of a classical oracle program `respond ω hist req` that
makes at most `q` queries (`respond_queries`) to the oracle in force, from the coins `ω` and the
history `hist` of earlier requests and replies, and returns the reply and an assignment list
appended to the assignments in force (Unruh 2017 section 2, p. 7). -/
structure Challenger (X Y Req Resp : Type) where
  /-- The coins. -/
  Coins : Type
  [instFintypeCoins : Fintype Coins]
  [instDecidableEqCoins : DecidableEq Coins]
  /-- The distribution of the coins, independent of the oracle. -/
  coins : PMF Coins
  /-- The number of requests answered. -/
  Q : ℕ
  /-- The number of classical queries per request. -/
  q : ℕ
  /-- The reply and the new assignments, as a classical oracle program. -/
  respond : Coins → List (HistoryEntry Req Resp) → Req → OracleProg X Y (Reply X Y Resp)
  respond_queries : ∀ ω hist req H, ((respond ω hist req).trace H).length ≤ q

attribute [instance] Challenger.instFintypeCoins Challenger.instDecidableEqCoins

/-! ### The challenger's state read from the registers -/

/-- **The reply to request `req`** of the reply programs `respond` at the coins `ω` after the
history `hist`, when the program is fed the answers `ans`; no response and no assignments if it has
not returned. -/
def Challenger.outWithOf {X Y Req Resp Coins : Type}
    (respond : Coins → List (HistoryEntry Req Resp) → Req → OracleProg X Y (Reply X Y Resp))
    (ω : Coins) (hist : List (HistoryEntry Req Resp)) (req : Req) (ans : List Y) :
    Reply X Y Resp :=
  (OracleProgAns.result (respond ω hist req) ans).getD ⟨none, []⟩

/-- **The history and the assignments in force after the slots below `j`** of a challenger with
the request bound `Q` and the reply programs `respond`, read from the logs and the answers in the
challenger's registers: each logged request numbered below `Q` gets the reply and the assignments
of its program fed the answers of its slot. It reads no other part of a challenger (the coins'
distribution). -/
def Challenger.regStateOf {X Y Req Resp Coins : Type} (Q : ℕ)
    (respond : Coins → List (HistoryEntry Req Resp) → Req → OracleProg X Y (Reply X Y Resp))
    {m : ℕ} (ω : Coins) (lg : LogReg Req m) (ans : Fin m → List Y) :
    ℕ → ChallengerRecord X Y Req Resp
  | 0 => ⟨[], []⟩
  | j + 1 =>
    let s := regStateOf Q respond ω lg ans j
    if h : j < m then
      match lg ⟨j, h⟩ with
      | none => s
      | some r =>
        if s.history.length < Q then
          let o := outWithOf respond ω s.history r (ans ⟨j, h⟩)
          ⟨s.history ++ [⟨r, o.response⟩], s.assignments ++ o.assignments⟩
        else s
    else s


namespace Challenger

variable {X Y Req Resp : Type} (C : Challenger X Y Req Resp)

/-- The reply to request `req` after the history `hist`, when the program is fed the answers
`ans`; no response and no assignments if it has not returned (`outWithOf`). -/
def outWith (ω : C.Coins) (hist : List (HistoryEntry Req Resp)) (req : Req) (ans : List Y) :
    Reply X Y Resp :=
  outWithOf C.respond ω hist req ans

/-- **The history and the assignments in force after the slots below `j`**, read from the logs
and the answers in the challenger's registers (`regStateOf` at the request bound and the reply
programs). -/
def regState {m : ℕ} (ω : C.Coins) (lg : LogReg Req m) (ans : Fin m → List Y) :
    ℕ → ChallengerRecord X Y Req Resp :=
  regStateOf C.Q C.respond ω lg ans

/-- **The state after the slots below `j + 1`** from the state after those below `j`. -/
theorem regState_add_one {m : ℕ} (ω : C.Coins) (lg : LogReg Req m) (ans : Fin m → List Y) (j : ℕ) :
    C.regState ω lg ans (j + 1) =
      let s := C.regState ω lg ans j
      if h : j < m then
        match lg ⟨j, h⟩ with
        | none => s
        | some r =>
          if s.history.length < C.Q then
            let o := C.outWith ω s.history r (ans ⟨j, h⟩)
            ⟨s.history ++ [⟨r, o.response⟩], s.assignments ++ o.assignments⟩
          else s
      else s :=
  rfl

end Challenger


/-! ### Registers of the composed algorithm -/

/-- **The challenger's classical registers in the composition**: one log per slot, the challenger's
query pairs of each slot, and its coins. -/
@[ext]
structure ChallengerRegs (X Y Req : Type) (slots q : ℕ) (Coins : Type) where
  /-- The log of each slot. -/
  logs : LogReg Req slots
  /-- The challenger's query pairs of each slot. -/
  queries : Fin slots → Fin q → X × Y
  /-- The challenger's coins. -/
  coins : Coins

/-- The challenger's registers as their three parts. -/
def ChallengerRegs.equivProd (X Y Req : Type) (slots q : ℕ) (Coins : Type) :
    ChallengerRegs X Y Req slots q Coins ≃
      LogReg Req slots × (Fin slots → Fin q → X × Y) × Coins where
  toFun u := (u.logs, u.queries, u.coins)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance {X Y Req : Type} {slots q : ℕ} {Coins : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [Fintype Req] [Fintype Coins] : Fintype (ChallengerRegs X Y Req slots q Coins) :=
  Fintype.ofEquiv _ (ChallengerRegs.equivProd X Y Req slots q Coins).symm

instance {X Y Req : Type} {slots q : ℕ} {Coins : Type} [DecidableEq X] [DecidableEq Y]
    [DecidableEq Req] [DecidableEq Coins] : DecidableEq (ChallengerRegs X Y Req slots q Coins) :=
  @Equiv.decidableEq _ _ (ChallengerRegs.equivProd X Y Req slots q Coins)
    (@instDecidableEqProd _ _ inferInstance (@instDecidableEqProd _ _ inferInstance inferInstance))

/-- The challenger's registers with the request `req` swapped into log `j`. -/
def ChallengerRegs.swapLog {X Y Req : Type} [DecidableEq Req] {m q : ℕ} {Coins : Type}
    (u : ChallengerRegs X Y Req m q Coins) (j : Fin m) (req : Req) :
    ChallengerRegs X Y Req m q Coins :=
  { u with logs := Function.update u.logs j (Equiv.swap none (some req) (u.logs j)) }

@[simp] theorem ChallengerRegs.swapLog_swapLog {X Y Req : Type} [DecidableEq Req] {m q : ℕ}
    {Coins : Type} (u : ChallengerRegs X Y Req m q Coins) (j : Fin m) (req : Req) :
    (u.swapLog j req).swapLog j req = u := by
  cases u
  simp [ChallengerRegs.swapLog]

/-- **The work register of the composed algorithm** without the ancilla: the adversary's registers
and the challenger's. -/
@[ext]
structure CWork (W : Type) (width : ℕ) (X Y Req Resp : Type) (slots q : ℕ) (Coins : Type) where
  /-- The adversary's registers. -/
  adv : DReg W width X Y Req Resp
  /-- The challenger's registers. -/
  chal : ChallengerRegs X Y Req slots q Coins

/-- The work register as the adversary's registers and the challenger's. -/
def CWork.equivProd (W : Type) (width : ℕ) (X Y Req Resp : Type) (slots q : ℕ) (Coins : Type) :
    CWork W width X Y Req Resp slots q Coins ≃
      DReg W width X Y Req Resp × ChallengerRegs X Y Req slots q Coins where
  toFun v := (v.adv, v.chal)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance {W : Type} {width : ℕ} {X Y Req Resp : Type} {slots q : ℕ} {Coins : Type} [Fintype W]
    [Fintype X] [DecidableEq X] [Fintype Y] [Fintype Req] [Fintype Resp] [Fintype Coins] :
    Fintype (CWork W width X Y Req Resp slots q Coins) :=
  Fintype.ofEquiv _ (CWork.equivProd W width X Y Req Resp slots q Coins).symm

instance {W : Type} {width : ℕ} {X Y Req Resp : Type} {slots q : ℕ} {Coins : Type} [DecidableEq W]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Req] [DecidableEq Resp] [DecidableEq Coins] :
    DecidableEq (CWork W width X Y Req Resp slots q Coins) :=
  @Equiv.decidableEq _ _ (CWork.equivProd W width X Y Req Resp slots q Coins)
    (@instDecidableEqProd _ _ inferInstance inferInstance)

instance {W : Type} {width : ℕ} {X Y Req Resp : Type} {m : ℕ} [DecidableEq W] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Req] [DecidableEq Resp] :
    DecidableEq (DReg W width X Y Req Resp × Fin m) :=
  @instDecidableEqProd _ _ inferInstance inferInstance

/-- The composed registers other than the adversary's: the challenger's registers and the query
register. -/
abbrev CRest (X Y Req : Type) (slots q : ℕ) (Coins : Type) :=
  ChallengerRegs X Y Req slots q Coins × (Fin 1 → X × Y)

instance {X Y Req : Type} {slots q : ℕ} {Coins : Type} [DecidableEq X] [DecidableEq Y]
    [DecidableEq Req] [DecidableEq Coins] : DecidableEq (CRest X Y Req slots q Coins) :=
  @instDecidableEqProd _ _ inferInstance inferInstance

instance {W : Type} {width : ℕ} {X Y Req Resp : Type} {slots q : ℕ} {Coins : Type} [DecidableEq W]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Req] [DecidableEq Resp] [DecidableEq Coins] :
    DecidableEq (DReg W width X Y Req Resp × CRest X Y Req slots q Coins) :=
  @instDecidableEqProd _ _ inferInstance inferInstance

/-- The all-zero assignment list: a reprogrammed query for it adds `0` (a padded query). -/
noncomputable def paddingAssignments (X Y : Type) [Fintype X] [Zero Y] : List (Assignment X Y) :=
  (Finset.univ : Finset X).toList.map fun x => ⟨x, 0⟩

theorem lastAssign_paddingAssignments (X Y : Type) [Fintype X] [DecidableEq X] [Zero Y] (x : X) :
    lastAssign (paddingAssignments X Y) x = some 0 := by
  have key : ∀ l : List X, x ∈ l →
      lastAssign (l.map fun x => (⟨x, 0⟩ : Assignment X Y)) x = some 0 := by
    intro l
    induction l using List.reverseRecOn with
    | nil => simp
    | append_singleton l a ih =>
      intro hx
      rw [List.map_append, List.map_singleton, lastAssign_append_singleton]
      by_cases h : a = x
      · simp [h]
      · rw [if_neg h]
        exact ih (by simpa [Ne.symm h] using hx)
  exact key _ (by simp)

/-- **A query reprogrammed by the all-zero assignment list adds `0`.** -/
theorem reprogram_paddingAssignments {X Y : Type} [Fintype X] [DecidableEq X] [Zero Y] (H : X → Y) :
    H.reprogram (paddingAssignments X Y) = 0 := by
  funext x
  rw [reprogram_apply_eq_lastAssign, lastAssign_paddingAssignments]
  rfl

/-! ### Constructions of Kraus maps and states used by the translation -/

/-- **The projective measurement of a function of the basis state**: the projectors onto the
fibers of `f`, with outcome the value. -/
def KrausMap.measureFn {ι M : Type*} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]
    (f : ι → M) : KrausMap M ι ι where
  op m := Matrix.diagonal fun i => if f i = m then 1 else 0
  sum_le := by
    have h : ∑ m, (Matrix.diagonal fun i => if f i = m then (1 : ℂ) else 0)ᴴ *
        Matrix.diagonal (fun i => if f i = m then (1 : ℂ) else 0) = 1 := by
      ext i j
      simp only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.sum_apply,
        Matrix.diagonal_apply, Matrix.one_apply]
      by_cases hij : i = j <;> simp [hij, apply_ite]
    rw [h]

/-- A mixture of mixed states: `∑ ω, μ ω • ρ ω`. -/
def MState.mix {ι : Type*} {Ω : Type} [Fintype ι] [Fintype Ω] (μ : PMF Ω) (ρ : Ω → MState ι) :
    MState ι where
  mat := ∑ ω, ((μ ω).toReal : ℂ) • (ρ ω).mat
  posSemidef := Matrix.posSemidef_sum _ fun ω _ =>
    (ρ ω).posSemidef.smul (by exact_mod_cast ENNReal.toReal_nonneg)
  trace_eq_one := by
    rw [Matrix.trace_sum]
    simp only [Matrix.trace_smul, (ρ _).trace_eq_one, smul_eq_mul, mul_one]
    classical
    exact_mod_cast Alg.sum_toReal_pmf μ

/-- A mixed state moved along a basis equivalence. -/
def MState.reindex {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (ρ : MState ι) : MState κ where
  mat := ρ.mat.submatrix e.symm e.symm
  posSemidef := ρ.posSemidef.submatrix _
  trace_eq_one := by
    rw [← ρ.trace_eq_one, Matrix.trace, Matrix.trace]
    exact Equiv.sum_comp e.symm fun i => ρ.mat i i

theorem posSemidef_reprogAnc {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] (x₀ : X) :
    (reprogAnc (Y := Y) x₀).PosSemidef := by
  have h : reprogAnc (Y := Y) x₀ = (Matrix.of fun (_ : Unit) a =>
      ancWeight x₀ a / (Real.sqrt (Fintype.card Y) : ℂ))ᴴ *
      Matrix.of fun (_ : Unit) a => ancWeight x₀ a / (Real.sqrt (Fintype.card Y) : ℂ) := by
    ext a a'
    simp only [reprogAnc, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Finset.univ_unique, Finset.sum_singleton, star_div₀, Complex.star_def, Complex.conj_ofReal]
    have hw : ∀ b : X × Y × Bool, (starRingEnd ℂ) (ancWeight x₀ b) = ancWeight x₀ b := fun b => by
      unfold ancWeight
      split_ifs <;> simp
    rw [hw, div_mul_div_comm, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem trace_reprogAnc {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (x₀ : X) : (reprogAnc (Y := Y) x₀).trace = 1 := by
  simp only [Matrix.trace, reprogAnc, Matrix.diag, ancWeight]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single x₀ (fun b _ hb => by simp [hb]) (by simp)]
  simp only [true_and, Fintype.sum_prod_type, Fintype.sum_bool]
  simp [Finset.card_univ]

/-- The clean ancilla appended to a mixed state, as a mixed state. -/
noncomputable def MState.withAnc {V X Y : Type} [Fintype V] [DecidableEq V] [Fintype X]
    [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y] (x₀ : X) (ρ : MState (QueryReg V 1 X Y)) : MState (ReprogrammedQueryReg V X Y) where
  mat := Quantum.withAnc x₀ ρ.mat
  posSemidef := by
    rw [withAnc_eq_kronecker]
    exact (ρ.posSemidef.kronecker (posSemidef_reprogAnc x₀)).submatrix _
  trace_eq_one := by
    have h : (Quantum.withAnc x₀ ρ.mat).trace = (ρ.mat ⊗ₖ reprogAnc (Y := Y) x₀).trace :=
      Equiv.sum_comp (ancSplit V X Y) fun i => (ρ.mat ⊗ₖ reprogAnc x₀) i i
    rw [h, trace_kronecker, ρ.trace_eq_one, trace_reprogAnc, one_mul]

namespace ReprogrammedCircuit

variable {V X Y : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]

/-- The concatenation of a list of circuits. -/
def concat : List (ReprogrammedCircuit V X Y) → ReprogrammedCircuit V X Y
  | [] => nil
  | c :: cs => c ++ concat cs

theorem queries_concat (cs : List (ReprogrammedCircuit V X Y)) :
    (concat cs).queries = (cs.map queries).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [concat, queries_append, ih, List.map_cons, List.sum_cons]

end ReprogrammedCircuit

/-! ### Exchanging the query register with a pair in the work register -/

section PairSwap

variable {V X Y : Type}

/-- The basis permutation that exchanges the query pair with the pair `get v` of the work
register, for a lens `get`, `set` on the work register. -/
def pairSwap (get : V → X × Y) (set : V → X × Y → V) (hgs : ∀ v a, get (set v a) = a)
    (hss : ∀ v a b, set (set v a) b = set v b) (hsg : ∀ v, set v (get v) = v) :
    Equiv.Perm (QueryReg V 1 X Y) :=
  Function.Involutive.toPerm (fun p => (set p.1 (p.2 0), fun _ => get p.1)) fun p => by
    refine Prod.ext ?_ (funext fun i => ?_)
    · simp [hgs, hss, hsg]
    · simp [hgs, Fin.fin_one_eq_zero i]

end PairSwap

/-! ### The translation -/

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (A : KindAlg X Y Req Resp O) (C : Challenger X Y Req Resp)

/-- The work register of the composed algorithm without the ancilla. -/
abbrev CW := CWork A.W A.width X Y Req Resp A.slots C.q C.Coins

/-- The classical registers of the composed algorithm: logs, challenger registers, coins. -/
abbrev CCl := ChallengerRegs X Y Req A.slots C.q C.Coins

/-- The answers of the challenger's queries in slot `j`. -/
def ansOf (u : A.CCl C) : Fin A.slots → List Y :=
  fun j => List.ofFn fun i => (u.queries j i).2

/-- The challenger's history and assignments in force after the slots below `j`. -/
def stateAt (u : A.CCl C) (j : ℕ) : ChallengerRecord X Y Req Resp :=
  C.regState u.coins u.logs (A.ansOf C u) j

/-- The outcome of the request measurement of slot `j`: the request on the branches with
`kind = true`. -/
def reqOutcome (p : QueryReg (A.CW C) 1 X Y) : Option Req :=
  if A.kind p.1.adv.workspace then some p.1.adv.request else none

/-- Copy the request into log `j` on the branches with `kind = true` (an involution). -/
def copyReq (j : Fin A.slots) : Equiv.Perm (QueryReg (A.CW C) 1 X Y) :=
  Function.Involutive.toPerm
    (fun p => if A.kind p.1.adv.workspace then
      (⟨p.1.adv, p.1.chal.swapLog j p.1.adv.request⟩, p.2) else p)
    fun p => by
      by_cases h : A.kind p.1.adv.workspace
      · simp [h]
      · simp [h]

/-- **The request measurement of slot `j`**: measure the request on the branches with
`kind = true`, and copy the outcome into log `j`. -/
def measReq (j : Fin A.slots) :
    KrausMap (Option Req × Unit) (QueryReg (A.CW C) 1 X Y) (QueryReg (A.CW C) 1 X Y) :=
  (KrausMap.ofPerm (A.copyReq C j)).comp (KrausMap.measureFn (A.reqOutcome C))

variable [Nonempty X] [AddGroup Y]

/-- The fixed query input of a clean query register. -/
noncomputable def x₀ : X := Classical.arbitrary X

/-- The input of the challenger's query `i` in slot `j`: the next query of its program on the
answers so far; `x₀` on branches without a request, for requests numbered `Q` or later, and once
the program has returned. -/
noncomputable def chalInput (j : Fin A.slots) (i : Fin C.q) (u : A.CCl C) : X :=
  match u.logs j with
  | none => x₀
  | some r =>
    if (A.stateAt C u j).history.length < C.Q then
      (C.respond u.coins (A.stateAt C u j).history r).next x₀ ((A.ansOf C u j).take i)
    else x₀

/-- The assignments read by the challenger's query `i` in slot `j`: those in force before slot
`j` if the program makes that query, else the padding list. -/
noncomputable def chalAss (j : Fin A.slots) (i : Fin C.q) (u : A.CCl C) : List (Assignment X Y) :=
  match u.logs j with
  | none => paddingAssignments X Y
  | some r =>
    if (A.stateAt C u j).history.length < C.Q ∧
        OracleProgAns.wants (C.respond u.coins (A.stateAt C u j).history r) ((A.ansOf C u j).take i)
    then (A.stateAt C u j).assignments else paddingAssignments X Y

/-- Prepare the challenger's query `i` of slot `j`: the query input `x₀` becomes `chalInput`. -/
noncomputable def prepChal (j : Fin A.slots) (i : Fin C.q) :
    Equiv.Perm (QueryReg (A.CW C) 1 X Y) :=
  Function.Involutive.toPerm
    (fun p => (p.1, fun _ => (Equiv.swap x₀ (A.chalInput C j i p.1.chal) (p.2 0).1, (p.2 0).2)))
    fun p => by
      refine Prod.ext rfl (funext fun k => ?_)
      simp [Fin.fin_one_eq_zero k]

/-- Move the query pair into the challenger's register of query `i` of slot `j`. -/
def garSwap (j : Fin A.slots) (i : Fin C.q) : Equiv.Perm (QueryReg (A.CW C) 1 X Y) :=
  pairSwap (fun v => v.chal.queries j i)
    (fun v a => ⟨v.adv, { v.chal with
      queries := Function.update v.chal.queries j (Function.update (v.chal.queries j) i a) }⟩)
    (fun v a => by simp) (fun v a b => by simp) (fun v => by simp)

/-- The reply to the request of slot `j`, read from the classical registers. -/
def reply (j : Fin A.slots) (u : A.CCl C) : Option Resp :=
  match u.logs j with
  | none => none
  | some r =>
    if (A.stateAt C u j).history.length < C.Q then
      (C.outWith u.coins (A.stateAt C u j).history r (A.ansOf C u j)).response
    else none

/-- Write the reply of slot `j` into the response register, on the branches with a request. -/
def writeReply (j : Fin A.slots) : Equiv.Perm (QueryReg (A.CW C) 1 X Y) :=
  Function.Involutive.toPerm
    (fun p => if (p.1.chal.logs j).isSome then
      (⟨((p.1.adv.workspace, p.1.adv.request, Equiv.swap none (A.reply C j p.1.chal) p.1.adv.response),
        p.1.adv.2), p.1.chal⟩, p.2) else p)
    fun p => by
      obtain ⟨⟨⟨⟨w, req, resp⟩, prs⟩, u⟩, qr⟩ := p
      by_cases h : (u.logs j).isSome <;> simp [h, DReg.workspace, DReg.request, DReg.response]

/-- Exchange the query register with the adversary's query pair `k`. -/
def advSwap (k : Fin A.width) : Equiv.Perm (QueryReg (A.CW C) 1 X Y) :=
  pairSwap (fun v => v.adv.2 k) (fun v a => ⟨(v.adv.1, Function.update v.adv.2 k a), v.chal⟩)
    (fun v a => by simp) (fun v a b => by simp) (fun v => by simp)

/-- The assignments read by the adversary's queries in slot `j`: those in force after the slot's
request on branches without a request, else the padding list. -/
noncomputable def advAss (j : Fin A.slots) (u : A.CCl C) : List (Assignment X Y) :=
  match u.logs j with
  | none => (A.stateAt C u (j + 1)).assignments
  | some _ => paddingAssignments X Y

/-- The assignments read by the post-phase queries: those in force after the last slot. -/
def postAss (u : A.CCl C) : List (Assignment X Y) :=
  (A.stateAt C u A.slots).assignments

/-- **The post-phase assignments from the challenger's reply programs** (`Challenger.regStateOf`). -/
theorem postAss_eq_regStateOf (u : A.CCl C) :
    A.postAss C u = (Challenger.regStateOf C.Q C.respond u.coins u.logs
      (fun j => List.ofFn fun i => (u.queries j i).2) A.slots).assignments := by
  rfl

/-- The basis of the adversary's registers next to the rest of the composed registers. -/
def advSplit : DReg A.W A.width X Y Req Resp × CRest X Y Req A.slots C.q C.Coins ≃
    QueryReg (A.CW C) 1 X Y where
  toFun p := (⟨p.1, p.2.1⟩, p.2.2)
  invFun q := (q.1.adv, (q.1.chal, q.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The adversary's Kraus map number `k` on the composed registers. -/
def advKraus (k : StepIdx A.slots A.post) :
    KrausMap A.R (QueryReg (A.CW C) 1 X Y) (QueryReg (A.CW C) 1 X Y) :=
  ((A.step k).tensorId _).reindex (A.advSplit C)

/-- The adversary's `width` queries, each exchanged into the query register and reprogrammed
by `ass`. -/
def advQueries (ass : A.CW C → List (Assignment X Y)) : ReprogrammedCircuit (A.CW C) X Y :=
  ReprogrammedCircuit.concat ((List.finRange A.width).map fun k =>
    .kraus (KrausMap.ofPerm (A.advSwap C k)) (.rquery ass (.kraus (KrausMap.ofPerm (A.advSwap C k)) .nil)))

/-- The challenger's `q` classical queries of slot `j`. -/
noncomputable def chalQueries (j : Fin A.slots) : ReprogrammedCircuit (A.CW C) X Y :=
  ReprogrammedCircuit.concat ((List.finRange C.q).map fun i =>
    .kraus (KrausMap.ofPerm (A.prepChal C j i))
      (.rquery (fun v => A.chalAss C j i v.chal) (.kraus (KrausMap.ofPerm (A.garSwap C j i)) .nil)))

/-- **Slot `j` scheduled as a request (`b = true`) or as a query batch (`b = false`)**: the
adversary's Kraus map, the request measurement, the challenger's queries if `b`, its reply, the
adversary's queries if not `b`. -/
noncomputable def slotCirc (b : Bool) (j : Fin A.slots) : ReprogrammedCircuit (A.CW C) X Y :=
  .kraus (A.advKraus C (slotStep j)) (.kraus (A.measReq C j)
    ((if b then A.chalQueries C j else .nil) ++ .kraus (KrausMap.ofPerm (A.writeReply C j))
      (if b then .nil else A.advQueries C fun v => A.advAss C j v.chal)))

/-- **Post batch `b`**: the adversary's Kraus map, then `width` queries for the final
assignments. -/
def postCirc (b : Fin A.post) : ReprogrammedCircuit (A.CW C) X Y :=
  .kraus (A.advKraus C (postStep b)) (A.advQueries C fun v => A.postAss C v.chal)

/-- The whole run at the schedule `sched`: the slots, the post batches, the adversary's last
Kraus map. -/
noncomputable def fullCirc (sched : Fin A.slots → Bool) : ReprogrammedCircuit (A.CW C) X Y :=
  ReprogrammedCircuit.concat ((List.finRange A.slots).map fun j => A.slotCirc C (sched j) j) ++
    ReprogrammedCircuit.concat ((List.finRange A.post).map (A.postCirc C)) ++
      .kraus (A.advKraus C lastStep) .nil

variable [Nonempty Y]

/-- The initial state of the composed registers without the ancilla: the challenger's coins
drawn from their distribution as a classical register, the adversary's initial state, blank
logs, clean challenger registers and a clean query register. -/
noncomputable def initSys : MState (QueryReg (A.CW C) 1 X Y) :=
  MState.mix C.coins fun ω => MState.reindex (A.advSplit C)
    (A.init.tensorKet (⟨fun _ => none, fun _ _ => (x₀, 0), ω⟩, fun _ => (x₀, 0)))

theorem queries_advQueries (ass : A.CW C → List (Assignment X Y)) :
    (A.advQueries C ass).queries = A.width := by
  rw [advQueries, ReprogrammedCircuit.queries_concat, List.map_map]
  simp [Function.comp_def, ReprogrammedCircuit.queries]

theorem queries_chalQueries (j : Fin A.slots) : (A.chalQueries C j).queries = C.q := by
  rw [chalQueries, ReprogrammedCircuit.queries_concat, List.map_map]
  simp [Function.comp_def, ReprogrammedCircuit.queries]

theorem queries_slotCirc (b : Bool) (j : Fin A.slots) :
    (A.slotCirc C b j).queries = if b then C.q else A.width := by
  cases b <;> simp [slotCirc, ReprogrammedCircuit.queries, ReprogrammedCircuit.queries_append, queries_advQueries,
    queries_chalQueries]

theorem queries_postCirc (b : Fin A.post) : (A.postCirc C b).queries = A.width := by
  simp [postCirc, ReprogrammedCircuit.queries, queries_advQueries]

theorem queries_fullCirc (sched : Fin A.slots → Bool) :
    (A.fullCirc C sched).queries =
      (∑ j, if sched j then C.q else A.width) + A.width * A.post := by
  rw [fullCirc, ReprogrammedCircuit.queries_append, ReprogrammedCircuit.queries_append, ReprogrammedCircuit.queries_concat,
    ReprogrammedCircuit.queries_concat, List.map_map, List.map_map, Fin.sum_univ_def]
  have h1 : (List.finRange A.slots).map ((fun c => ReprogrammedCircuit.queries c) ∘
      fun j => A.slotCirc C (sched j) j) =
      (List.finRange A.slots).map fun j => if sched j then C.q else A.width :=
    List.map_congr_left fun j _ => A.queries_slotCirc C _ j
  have h2 : (List.finRange A.post).map ((fun c => ReprogrammedCircuit.queries c) ∘ A.postCirc C) =
      (List.finRange A.post).map fun _ => A.width :=
    List.map_congr_left fun b _ => A.queries_postCirc C b
  rw [h1, h2]
  simp [ReprogrammedCircuit.queries, mul_comm]

end KindAlg

/-! ### Interactive adversaries with a static schedule -/

/-- **An interactive mixed adversary** (closest published notion: Unruh 2017 section 3, pp. 8–10, an
oracle algorithm with several oracles) with requests in `Req`, replies in `Option Resp` and output
in `O`: a mixed adversary (`Alg`) whose registers are those of a distinguisher of
`GordieHowe/Model/Quantum/Pure/Game.lean` (`DReg W width X Y Req Resp`: workspace, request register, response
register with blank value `none`, `width` query pairs), with a static schedule `sched`: slot `j` is
a request if `sched j` and a batch of `width` parallel queries otherwise. The schedule is part of
the adversary's description, as the execution schedule of Unruh 2017 (ePrint 2017/398, section 3,
p. 8): "op_C – the execution schedule of C, that is, a sequence op_C = op_1, ..., op_s for some s
where each op_i is either compute or call_j for some j ∈ {1, ..., t}"; the contents of the queries
are quantum, and a request is measured in the computational basis at its slot (`measReq`). An
adversary that decides at run time whether to request is not in this class: it is an `AdaptiveIAlg`
(`GordieHowe/Model/Quantum/Interactive/Adaptive.lean`, Unruh 2017 p. 10, oracle algorithms). Simulating one by a
fixed schedule would make every slot it might use a slot of both kinds, with the unused requests
sent outside the relation and counted among the `Q` answered ones, and the unused query slots
counted among the `t` queries. The run is `step 0`, slot `0`, `step 1`, …, slot `slots - 1`,
`step slots`, then `post` batches of `width` queries with `step (slots + 1)`, …,
`step (slots + post)` between and after them. The Kraus maps are trace-non-increasing. The output is
read from the computational-basis measurement of the workspace. -/
structure IAlg (X Y Req Resp O : Type) [Fintype X] [Fintype Y] [Fintype Req] [Fintype Resp]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Req] [DecidableEq Resp] where
  /-- The workspace. -/
  W : Type
  [instFintypeW : Fintype W]
  [instDecidableEqW : DecidableEq W]
  /-- The number of parallel query pairs. -/
  width : ℕ
  width_pos : 0 < width
  /-- The number of slots. -/
  slots : ℕ
  /-- The number of query batches after the last slot. -/
  post : ℕ
  /-- The schedule: slot `j` is a request (`true`) or a query batch (`false`). -/
  sched : Fin slots → Bool
  /-- The index type of the Kraus operators. -/
  R : Type
  [instFintypeR : Fintype R]
  /-- The initial state. -/
  init : MState (DReg W width X Y Req Resp)
  /-- The Kraus maps. -/
  step : StepIdx slots post →
    KrausMap R (DReg W width X Y Req Resp) (DReg W width X Y Req Resp)
  /-- The output read from the workspace. -/
  out : W → O

attribute [instance] IAlg.instFintypeW IAlg.instDecidableEqW IAlg.instFintypeR

namespace IAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (A : IAlg X Y Req Resp O) (C : Challenger X Y Req Resp)

/-- The number of request slots. -/
def requests : ℕ := (Finset.univ.filter fun j => A.sched j = true).card

/-- The query slots: the slots scheduled as query batches. -/
def querySlotSet : Finset (Fin A.slots) := Finset.univ.filter fun j => A.sched j = false

/-- The number of query slots. -/
def querySlots : ℕ := A.querySlotSet.card

theorem querySlots_le : A.querySlots ≤ A.slots :=
  (Finset.card_filter_le _ _).trans (Finset.card_fin _).le

/-- **Every step of `A` is trace preserving** (`∑ r, (op r)ᴴ * op r = 1`). -/
def TracePreserving : Prop :=
  ∀ k, ∑ r, ((A.step k).op r)ᴴ * (A.step k).op r = 1

/-- The adversary's registers with a slot counter, as the registers of the adversary without it
and the counter. -/
def cntSplit : DReg (A.W × Fin (A.slots + 1)) A.width X Y Req Resp ≃
    DReg A.W A.width X Y Req Resp × Fin (A.slots + 1) where
  toFun p := (((p.1.1.1, p.1.2.1, p.1.2.2), p.2), p.1.1.2)
  invFun q := ((((q.1.1.1, q.2), q.1.1.2.1, q.1.1.2.2)), q.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The counter advanced by one (cyclically) after the Kraus maps numbered `0, …, slots - 1` (the
maps before the slots `0, …, slots - 1`), so that after map `j` the counter is `j + 1`, for the
counter values `1, …, slots`. -/
def cntPerm (k : StepIdx A.slots A.post) :
    Equiv.Perm (DReg (A.W × Fin (A.slots + 1)) A.width X Y Req Resp) :=
  if (k : ℕ) < A.slots then
    Equiv.prodCongr (Equiv.prodCongr (Equiv.prodCongr (Equiv.refl A.W) (finRotate _))
      (Equiv.refl _)) (Equiv.refl _)
  else Equiv.refl _

/-- The kind read from the counter: after the Kraus map number `j < slots` the counter is
`j + 1`, and the kind is `sched j`. -/
def cntKind (w : A.W × Fin (A.slots + 1)) : Bool :=
  if h : (w.2 : ℕ) = 0 then false else A.sched ⟨w.2 - 1, by have := w.2.2; omega⟩

/-- **The adversary as one with a kind register** (proof-internal): its workspace carries a slot
counter, started at `0` and advanced by the Kraus maps before the slots, and the kind read from
it is the schedule. -/
def toKindAlg : KindAlg X Y Req Resp O where
  W := A.W × Fin (A.slots + 1)
  width := A.width
  width_pos := A.width_pos
  slots := A.slots
  post := A.post
  kind := A.cntKind
  R := A.R
  init := MState.reindex A.cntSplit.symm (A.init.tensorKet 0)
  step k := (((A.step k).tensorId (Fin (A.slots + 1))).reindex A.cntSplit.symm).permConj
    (Equiv.refl _) (A.cntPerm k)
  out w := A.out w.1

variable [Nonempty X] [AddGroup Y] [Nonempty Y]

/-- The whole run: slot `j` is a request slot or a query slot according to `sched j`. -/
noncomputable def fullCirc : ReprogrammedCircuit (A.toKindAlg.CW C) X Y :=
  A.toKindAlg.fullCirc C A.sched

/-- **The composed core algorithm** (the translation of the module docstring): the compiled
circuit `fullCirc` on the composed registers with the clean ancilla, the output read from the
adversary's workspace. -/
noncomputable abbrev compose : Alg X Y O :=
  (A.fullCirc C).toCircuit.toAlg (MState.withAnc KindAlg.x₀ (A.toKindAlg.initSys C))
    fun v => A.out v.1.adv.workspace.1

/-- **The query count of the composition**: the challenger's `q` classical queries per request
slot, the adversary's `width` queries per query slot, then `width` queries per post batch. -/
theorem compose_depth :
    (A.compose C).depth = A.requests * C.q + A.querySlots * A.width + A.width * A.post := by
  rw [compose, Circuit.toAlg_depth, ReprogrammedCircuit.queries_toCircuit, fullCirc]
  refine (A.toKindAlg.queries_fullCirc C A.sched).trans ?_
  show (∑ j : Fin A.slots, if A.sched j then C.q else A.width) + A.width * A.post = _
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
  simp only [requests, querySlots, querySlotSet, Bool.not_eq_true]

end IAlg

end GordieHowe.Quantum
