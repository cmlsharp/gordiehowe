-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.Basic

@[expose] public section

/-!
# The pure image of the interactive model

Proof tools relating the composed algorithm of an interactive adversary and a challenger
(`IAlg.compose`, `GordieHowe/Model/Quantum/Interactive/Basic.lean`) to the pure game of `GordieHowe/Model/Quantum/Pure/Game.lean`, which
the zero-knowledge argument (`GordieHowe/Model/QROM/SaltedZK.lean`) analyses.

- `Challenger.toPureEnv`: the challenger as an environment of the pure game. Its state is the
  base oracle, the history and the assignments in force (`ChallengerState`); its oracle in force is the base
  oracle reprogrammed by the assignments; its reply runs the program on the oracle in force.
- **The mixed game** (`Quantum.KindAlg.mgCirc`): for a fixed tape (oracle and coins), the adversary's Kraus
  maps on the game registers (logs untouched) alternating with the slot permutations of the pure
  game (`Env.requestPerm`, `Env.oraclePerm`), then the post batches with the oracle in force.
  With `deph = true` the request of each slot is measured: log `k` is dephased after the copy.
- **Deferred measurement** (`Quantum.KindAlg.mgAccept_deph`): the acceptance probability of the mixed game
  is the same with and without the dephasing (Nielsen–Chuang section 4.4). Every operation after
  the copy into log `k` leaves log `k` unchanged and acts block-diagonally in it, and the
  acceptance probability reads the diagonal only.
-/

open Finset Matrix
open scoped BigOperators ENNReal Kronecker ComplexOrder

namespace GordieHowe.Quantum


/-! ### Dephasing -/

section Dephase

variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq L]

/-- **Dephasing in a function `g` of the basis state**: the off-diagonal blocks between different
values of `g` are removed. -/
def dephase (g : ι → L) (ρ : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => if g i = g j then ρ i j else 0

@[simp]
theorem dephase_apply_self (g : ι → L) (ρ : Matrix ι ι ℂ) (i : ι) : dephase g ρ i i = ρ i i := by
  simp [dephase]

theorem KrausMap.measureFn_apply [Fintype L] (g : ι → L) (ρ : Matrix ι ι ℂ) :
    (KrausMap.measureFn g) ρ = dephase g ρ := by
  ext i j
  simp only [KrausMap.apply, KrausMap.measureFn, Matrix.sum_apply, Matrix.diagonal_conjTranspose,
    Matrix.mul_apply, Matrix.diagonal_apply, dephase]
  simp [Finset.sum_ite_eq', ite_mul, mul_ite, Finset.sum_ite_eq]

/-- A Kraus map is block-diagonal in `g` if its operators connect only basis states with the same
value of `g`. -/
def KrausMap.BlockDiag {R : Type*} [Fintype R] (g : ι → L) (K : KrausMap R ι ι) : Prop :=
  ∀ r i j, g i ≠ g j → K.op r i j = 0

/-- **A block-diagonal Kraus map commutes with dephasing.** -/
theorem KrausMap.apply_dephase {R : Type*} [Fintype R] {g : ι → L} {K : KrausMap R ι ι}
    (hK : K.BlockDiag g) (ρ : Matrix ι ι ℂ) :
    K (dephase g ρ) = dephase g (K ρ) := by
  ext i j
  simp only [KrausMap.apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    dephase]
  by_cases h : g i = g j
  · simp only [h, ite_true]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : g k = g l
    · simp [hk]
    · by_cases hik : g i = g k
      · have hjl : g j ≠ g l := fun e => hk (hik ▸ h ▸ e)
        simp [hk, hK r j l hjl]
      · simp [hK r i k hik]
  · simp only [h, ite_false]
    refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun l _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : g k = g l
    · by_cases hik : g i = g k
      · have hjl : g j ≠ g l := fun e => h (hik.trans (hk.trans e.symm))
        simp [hk, hK r j l hjl]
      · simp [hK r i k hik]
    · simp [hk]

/-- A basis permutation that preserves `g` is block-diagonal in `g`. -/
theorem KrausMap.blockDiag_ofPerm {π : Equiv.Perm ι} {g : ι → L} (hπ : ∀ i, g (π i) = g i) :
    (KrausMap.ofPerm π).BlockDiag g := by
  intro r i j hij
  simp only [KrausMap.ofPerm, KrausMap.permConj, KrausMap.identity, submatrix_apply, Equiv.coe_refl,
    id, Matrix.one_apply]
  rw [if_neg]
  intro h
  apply hij
  have : i = π j := by rw [← Equiv.symm_apply_eq]; exact h
  rw [this, hπ]

omit [DecidableEq L] in
/-- A measurement of a function `f` is block-diagonal in every `g`. -/
theorem KrausMap.blockDiag_measureFn {M : Type*} [Fintype M] [DecidableEq M] (f : ι → M)
    (g : ι → L) : (KrausMap.measureFn f).BlockDiag g := by
  intro r i j hij
  simp only [KrausMap.measureFn, Matrix.diagonal_apply]
  have hne : i ≠ j := fun h => hij (h ▸ rfl)
  simp [hne]

omit [Fintype ι] [DecidableEq ι] in
/-- Dephasing in `(g, g')` is dephasing in `g` after dephasing in `g'`. -/
theorem dephase_pair {L' : Type*} [DecidableEq L'] (g : ι → L) (g' : ι → L') (ρ : Matrix ι ι ℂ) :
    dephase (fun i => (g i, g' i)) ρ = dephase g (dephase g' ρ) := by
  ext i j
  simp only [dephase, Prod.mk.injEq]
  by_cases h : g i = g j <;> by_cases h' : g' i = g' j <;> simp [h, h']

end Dephase

/-! ### The challenger as an environment of the pure game -/

/-- The state of a challenger in the pure game: the base oracle, the history of requests and
replies, and the assignments in force. -/
structure ChallengerState (X Y Req Resp : Type) where
  /-- The base oracle. -/
  base : X → Y
  /-- The history of requests and replies. -/
  hist : List (HistoryEntry Req Resp)
  /-- The assignments in force. -/
  ass : List (Assignment X Y)

instance {X Y Req Resp : Type} [DecidableEq X] : OracleState (ChallengerState X Y Req Resp) X Y :=
  ⟨fun s => s.base.reprogram s.ass⟩

namespace Challenger

variable {X Y Req Resp : Type} [Fintype X] [DecidableEq X] [Fintype Y] (C : Challenger X Y Req Resp)

/-- **The challenger in the pure game**: the tape is the base oracle, uniform, and the coins; the
state starts with the base oracle and empty history and assignments; a request numbered below `Q`
runs the program on the oracle in force, appends the request and the reply to the history and the
new assignments to those in force. -/
noncomputable def toPureEnv [Nonempty Y] :
    Env ((X → Y) × C.Coins) Req Resp X Y C.Q (ChallengerState X Y Req Resp) where
  μ := (PMF.uniformOfFintype (X → Y)).bind fun H => C.coins.map fun c => (H, c)
  oracle₀ ω := ⟨ω.1, [], []⟩
  respond ω _ req s :=
    let o := (C.respond ω.2 s.hist req).run (s.base.reprogram s.ass)
    ⟨o.response, ⟨s.base, s.hist ++ [⟨req, o.response⟩], s.ass ++ o.assignments⟩⟩

end Challenger

/-! ### The mixed game -/

instance {W : Type} {n : ℕ} {X Y Req A : Type} {m : ℕ} [DecidableEq W] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Req] [DecidableEq A] : DecidableEq (GameReg W n X Y Req A m) :=
  @instDecidableEqProd _ _ (@instDecidableEqProd _ _ inferInstance
    (@instDecidableEqProd _ _ inferInstance (@instDecidableEqProd _ _ inferInstance inferInstance)))
    inferInstance

instance {W : Type} {n : ℕ} {X Y Req A : Type} {m : ℕ} [DecidableEq W] [DecidableEq X]
    [DecidableEq Y] [DecidableEq Req] [DecidableEq A] :
    DecidableEq (DReg W n X Y Req A × LogReg Req m) :=
  @instDecidableEqProd _ _ inferInstance inferInstance

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (A : KindAlg X Y Req Resp O)

/-- The game registers of `A` (`GameReg`). -/
abbrev G := GameReg A.W A.width X Y Req Resp A.slots

/-- A Kraus map on the adversary's registers, with the identity on the logs. -/
def liftG (k : StepIdx A.slots A.post) : KrausMap A.R A.G A.G :=
  ((A.step k).tensorId (LogReg Req A.slots)).reindex splitLogs.symm

/-- The log of slot `k` of a game basis state. -/
def logAt (k : Fin A.slots) (r : A.G) : Option Req :=
  (splitLogs r).2 k

variable [AddGroup Y] {Ω St : Type} {Q : ℕ} [OracleState St X Y] (E : Env Ω Req Resp X Y Q St)

/-- The copy of the request of slot `k` into log `k` (`copyPerm`). -/
def copyG (k : Fin A.slots) : Equiv.Perm A.G :=
  (copyPerm A.kind k).prodCongr (Equiv.refl _)

/-- The reply of slot `k` written into the response register (`respondPerm`). -/
def respG (ω : Ω) (k : Fin A.slots) : Equiv.Perm A.G :=
  (respondPerm A.kind fun lg => E.answer ω lg k).prodCongr (Equiv.refl _)

/-- The post-phase query to the oracle in force, on all query pairs. -/
def postG (ω : Ω) : Equiv.Perm A.G :=
  queryPermOf fun s => E.oracle ω s.2.2.2

/-- The events of slot `k`: the copy into log `k`, with `deph` the measurement of log `k`, the
reply, and the query on the branches without a request (`Env.oraclePerm`). Without the
measurement this is the slot permutation of the pure game (`Distinguisher.eventPerm`). -/
def eventCirc (ω : Ω) (k : Fin A.slots) (deph : Bool) : Circuit A.G :=
  .kraus (KrausMap.ofPerm (A.copyG k))
    ((if deph then Circuit.kraus (KrausMap.measureFn (A.logAt k)) else id)
      (.kraus (KrausMap.ofPerm (A.respG E ω k)) (.kraus (KrausMap.ofPerm (E.oraclePerm A.kind ω)) .nil)))

/-- The concatenation of a list of circuits. -/
def _root_.GordieHowe.Quantum.Circuit.concat {ι : Type} [Fintype ι] [DecidableEq ι] : List (Circuit ι) → Circuit ι
  | [] => .nil
  | c :: cs => c ++ Circuit.concat cs

theorem _root_.GordieHowe.Quantum.Circuit.run_concat {ι : Type} [Fintype ι] [DecidableEq ι] (π : Equiv.Perm ι)
    (c : Circuit ι) (cs : List (Circuit ι)) (ρ : Matrix ι ι ℂ) :
    (Circuit.concat (c :: cs)).run π ρ = (Circuit.concat cs).run π (c.run π ρ) :=
  Circuit.run_append π c _ ρ

/-- **The mixed game** on tape `ω`: the adversary's Kraus maps on the game registers alternating
with the slot events, then the post batches of queries to the oracle in force. -/
def mgCirc (ω : Ω) (deph : Bool) : Circuit A.G :=
  Circuit.concat ((List.finRange A.slots).map fun k : Fin A.slots =>
      .kraus (A.liftG (slotStep k)) (A.eventCirc E ω k deph)) ++
    Circuit.concat ((List.finRange A.post).map fun b : Fin A.post =>
      .kraus (A.liftG (postStep b)) (.kraus (KrausMap.ofPerm (A.postG E ω)) .nil)) ++
    .kraus (A.liftG lastStep) .nil

/-- The initial state of the mixed game: the adversary's initial state, blank logs. -/
def mgInit : Matrix A.G A.G ℂ :=
  (MState.reindex splitLogs.symm (A.init.tensorKet (fun _ => none : LogReg Req A.slots))).mat

/-- The final state of the mixed game. -/
def mgRun (ω : Ω) (deph : Bool) : Matrix A.G A.G ℂ :=
  (A.mgCirc E ω deph).run (Equiv.refl _) A.mgInit

/-- The probability that the mixed game outputs `o`. -/
def mgAccept [DecidableEq O] (o : O) (ω : Ω) (deph : Bool) : ℝ :=
  ∑ r : A.G, if A.out r.1.1 = o then (A.mgRun E ω deph r r).re else 0

/-! #### Deferred measurement -/

/-- The logs of the slots below `j`, the others read as blank. -/
def logsBelow (j : ℕ) (r : A.G) : LogReg Req A.slots :=
  fun k => if (k : ℕ) < j then (splitLogs r).2 k else none

theorem blockDiag_liftG {L : Type*} [DecidableEq L] (k : StepIdx A.slots A.post)
    (h : LogReg Req A.slots → L) : (A.liftG k).BlockDiag fun r => h (splitLogs r).2 := by
  intro r i j hij
  simp only [liftG, KrausMap.reindex, KrausMap.tensorId, Equiv.symm_symm, submatrix_apply,
    kroneckerMap_apply, Matrix.one_apply]
  rw [if_neg fun e => hij (by simp only [e]), mul_zero]

theorem blockDiag_liftG_logsBelow (k : StepIdx A.slots A.post) (j : ℕ) :
    (A.liftG k).BlockDiag (A.logsBelow j) :=
  A.blockDiag_liftG k fun (lg : LogReg Req A.slots) (k' : Fin A.slots) =>
    if (k' : ℕ) < j then lg k' else none

theorem logs_copyG (k : Fin A.slots) (r : A.G) (k' : Fin A.slots) (hk : k' ≠ k) :
    (splitLogs (A.copyG k r)).2 k' = (splitLogs r).2 k' := by
  by_cases h : A.kind r.1.1 <;> simp [copyG, copyPerm_apply, h, splitLogs, Function.update_of_ne hk]

theorem logs_respG (ω : Ω) (k : Fin A.slots) (r : A.G) :
    (splitLogs (A.respG E ω k r)).2 = (splitLogs r).2 := by
  by_cases h : A.kind r.1.1 <;> simp [respG, respondPerm_apply, h, splitLogs]

theorem logsBelow_copyG {j : ℕ} (k : Fin A.slots) (hk : j ≤ k) (r : A.G) :
    A.logsBelow j (A.copyG k r) = A.logsBelow j r := by
  funext k'
  simp only [logsBelow]
  split_ifs with h
  · exact A.logs_copyG k r k' (fun e => by subst e; omega)
  · rfl

/-- Dephasing in the logs below `j + 1` is dephasing in log `j` after dephasing in the logs
below `j`. -/
theorem dephase_logsBelow_succ (j : Fin A.slots) (ρ : Matrix A.G A.G ℂ) :
    dephase (A.logsBelow (j + 1)) ρ = dephase (A.logAt j) (dephase (A.logsBelow j) ρ) := by
  rw [← dephase_pair]
  ext a b
  simp only [dephase]
  congr 1
  apply propext
  constructor
  · intro h
    refine Prod.ext ?_ (funext fun k => ?_)
    · simpa [logsBelow, logAt] using congrFun h j
    · have := congrFun h k
      simp only [logsBelow] at this ⊢
      split_ifs with hk
      · simpa [show (k : ℕ) < j + 1 by omega] using this
      · rfl
  · intro h
    funext k
    have h1 := congrArg Prod.fst h
    have h2 := congrFun (congrArg Prod.snd h) k
    simp only [logsBelow, logAt] at h1 h2 ⊢
    split_ifs with hk
    · by_cases hkj : (k : ℕ) < j
      · simpa [hkj] using h2
      · have : k = j := Fin.ext (by omega)
        subst this
        exact h1
    · rfl

/-- **One slot of the mixed game with and without the measurement.** -/
theorem slot_run_deph (ω : Ω) (k : Fin A.slots) (ρ : Matrix A.G A.G ℂ) :
    (Circuit.kraus (A.liftG (slotStep k)) (A.eventCirc E ω k true)).run (Equiv.refl _)
        (dephase (A.logsBelow k) ρ) =
      dephase (A.logsBelow (k + 1))
        ((Circuit.kraus (A.liftG (slotStep k)) (A.eventCirc E ω k false)).run (Equiv.refl _) ρ) := by
  simp only [eventCirc, Circuit.run, ↓reduceIte, Bool.false_eq_true, id]
  rw [KrausMap.apply_dephase (A.blockDiag_liftG_logsBelow _ _),
    KrausMap.apply_dephase (KrausMap.blockDiag_ofPerm (A.logsBelow_copyG k le_rfl)),
    KrausMap.measureFn_apply, ← dephase_logsBelow_succ,
    KrausMap.apply_dephase (KrausMap.blockDiag_ofPerm fun r => by
      funext k'; simp only [logsBelow]; split_ifs <;> simp [A.logs_respG E ω k r]),
    KrausMap.apply_dephase (KrausMap.blockDiag_ofPerm fun r => by
      funext k'; simp only [logsBelow]; split_ifs <;> rfl)]

theorem slots_run_deph (ω : Ω) (l : List (Fin A.slots)) (j : ℕ)
    (hl : l.map Fin.val = List.range' j l.length) (ρ : Matrix A.G A.G ℂ) :
    (Circuit.concat (l.map fun k : Fin A.slots =>
        Circuit.kraus (A.liftG (slotStep k)) (A.eventCirc E ω k true))).run
        (Equiv.refl _) (dephase (A.logsBelow j) ρ) =
      dephase (A.logsBelow (j + l.length)) ((Circuit.concat (l.map fun k : Fin A.slots =>
        Circuit.kraus (A.liftG (slotStep k)) (A.eventCirc E ω k false))).run (Equiv.refl _) ρ) := by
  induction l generalizing j ρ with
  | nil => rfl
  | cons k l ih =>
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hl ⊢
    rw [Circuit.run_concat, Circuit.run_concat, ← hl.1, A.slot_run_deph E ω k ρ]
    rw [ih (↑k + 1) (by rw [hl.2, ← hl.1])]
    congr 2
    omega

theorem dephase_logsBelow_zero (ρ : Matrix A.G A.G ℂ) : dephase (A.logsBelow 0) ρ = ρ := by
  ext a b
  have h : A.logsBelow 0 a = A.logsBelow 0 b := by
    funext k
    simp [logsBelow]
  simp [dephase, h]

theorem post_run_deph (ω : Ω) (l : List (Fin A.post)) (ρ : Matrix A.G A.G ℂ) :
    (Circuit.concat (l.map fun b : Fin A.post =>
        .kraus (A.liftG (postStep b))
          (.kraus (KrausMap.ofPerm (A.postG E ω)) .nil))).run (Equiv.refl _)
        (dephase (A.logsBelow A.slots) ρ) =
      dephase (A.logsBelow A.slots) ((Circuit.concat (l.map fun b : Fin A.post =>
        .kraus (A.liftG (postStep b))
          (.kraus (KrausMap.ofPerm (A.postG E ω)) .nil))).run (Equiv.refl _) ρ) := by
  induction l generalizing ρ with
  | nil => rfl
  | cons b l ih =>
    simp only [List.map_cons]
    rw [Circuit.run_concat, Circuit.run_concat]
    simp only [Circuit.run]
    rw [KrausMap.apply_dephase (A.blockDiag_liftG_logsBelow _ _),
      KrausMap.apply_dephase (KrausMap.blockDiag_ofPerm fun r => rfl), ih]

/-- **Deferred measurement**: the final state of the mixed game with the requests measured is the
final state without the measurement, dephased in the logs. -/
theorem mgRun_deph (ω : Ω) :
    A.mgRun E ω true = dephase (A.logsBelow A.slots) (A.mgRun E ω false) := by
  simp only [mgRun, mgCirc, Circuit.run_append]
  conv_lhs => rw [← A.dephase_logsBelow_zero A.mgInit]
  rw [A.slots_run_deph E ω _ 0
      (by rw [List.map_coe_finRange_eq_range, List.range_eq_range', List.length_finRange]),
    List.length_finRange, Nat.zero_add, A.post_run_deph]
  simp only [Circuit.run]
  rw [KrausMap.apply_dephase (A.blockDiag_liftG_logsBelow _ _)]

/-- **Deferred measurement for the acceptance probability** (Nielsen–Chuang section 4.4): the
mixed game accepts with the same probability with and without the measurement of the requests. -/
theorem mgAccept_deph [DecidableEq O] (o : O) (ω : Ω) :
    A.mgAccept E o ω true = A.mgAccept E o ω false := by
  simp only [mgAccept, A.mgRun_deph E ω, dephase_apply_self]

end KindAlg

end GordieHowe.Quantum
