-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.PureGame
public import GordieHowe.Model.QROM.NIZK

@[expose] public section

/-!
# Zero knowledge in the interactive model

The honest prover and the simulator of a non-interactive argument as classical challengers
(`Challenger`) of the model (`GordieHowe/Model/Quantum/Core/Model.lean`, `GordieHowe/Model/Quantum/Interactive/Basic.lean`),
whose oracle use is a counted classical program, and their games against the environments of the
pure game of `GordieHowe/Model/QROM/NIZK.lean`.

- `Env.Bisimulation`: a bisimulation between two environments of the pure game on fixed tapes;
  bisimilar environments give the same final state and acceptance probability
  (`Distinguisher.final_eq_of_bisimulation`, `Distinguisher.acceptProbAt_eq_of_bisimulation`).
- `GordieHowe.NARG.Prover`, `GordieHowe.NARG.Simulator`: the honest prover and a simulator as counted oracle
  programs. Their classical semantics `toFn` run the program on the oracle in force.
- `GordieHowe.QROM.realChallenger`, `GordieHowe.QROM.simChallenger`: proof query number `c` with `(x, w)` is answered by
  the program on the coins of proof query `c` if `rel x w`, and by `none` otherwise; the simulator's
  assignments reprogram the oracle (Unruh 2017, Definition 6, p. 14).
- `GordieHowe.QROM.bisimulation_real`, `GordieHowe.QROM.bisimulation_sim`, `GordieHowe.QROM.acceptProb_real`,
  `GordieHowe.QROM.acceptProb_sim`: the challengers, as environments, are bisimilar to `GordieHowe.QROM.realEnv` and
  `GordieHowe.QROM.simEnv` for the pure images, so every distinguisher has the same acceptance probability
  against both.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe

/-! ### Bisimilar environments -/

namespace Quantum.Env

variable {Ω Ω' Req A X Y : Type*} {St St' : Type _} {Q : ℕ} [OracleState St X Y]
  [OracleState St' X Y]

/-- **A bisimulation between two environments** (the standard notion, for the deterministic
classical environments of the pure game) on fixed tapes `ω` and `ω'`: a relation
`R i` between the states of `E` and `E'` after `i` proof queries that holds at the start, is preserved
by every proof query (the updates of proof queries numbered `Q` or later leave the states unchanged), and
under which the two environments give the same reply and have the same oracle in force. -/
structure Bisimulation (E : Env Ω Req A X Y Q St) (E' : Env Ω' Req A X Y Q St') (ω : Ω) (ω' : Ω')
    (R : ℕ → St → St' → Prop) : Prop where
  init : R 0 (E.oracle₀ ω) (E'.oracle₀ ω')
  step : ∀ i (h : i < Q) req s s', R i s s' →
    R (i + 1) (E.respond ω ⟨i, h⟩ req s).state (E'.respond ω' ⟨i, h⟩ req s').state
  skip : ∀ i, Q ≤ i → ∀ s s', R i s s' → R (i + 1) s s'
  reply : ∀ i (h : i < Q) req s s', R i s s' →
    (E.respond ω ⟨i, h⟩ req s).response = (E'.respond ω' ⟨i, h⟩ req s').response
  oracle : ∀ i s s', R i s s' → OracleState.toOracle (X := X) (Y := Y) s = OracleState.toOracle s'

namespace Bisimulation

variable {E : Env Ω Req A X Y Q St} {E' : Env Ω' Req A X Y Q St'} {ω : Ω} {ω' : Ω'}
  {R : ℕ → St → St' → Prop}

/-- The states after the same proof queries are related. -/
theorem oracleIn (hs : Bisimulation E E' ω ω' R) :
    ∀ rs, R rs.length (E.oracleIn ω rs) (E'.oracleIn ω' rs) := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil => exact hs.init
  | append_singleton rs req ih =>
    rw [oracleIn_append_singleton, oracleIn_append_singleton, update, update, List.length_append,
      List.length_singleton]
    split_ifs with h
    · exact hs.step _ h req _ _ ih
    · exact hs.skip _ (not_lt.1 h) _ _ ih

/-- The oracles in force agree on every logs. -/
theorem oracle_eq (hs : Bisimulation E E' ω ω' R) {m : ℕ} (lg : LogReg Req m) :
    E.oracle ω lg = E'.oracle ω' lg :=
  hs.oracle _ _ _ (hs.oracleIn _)

/-- The replies agree on every logs. -/
theorem answer_eq (hs : Bisimulation E E' ω ω' R) {m : ℕ} (lg : LogReg Req m) (k : Fin m) :
    E.answer ω lg k = E'.answer ω' lg k := by
  unfold answer answerAfter
  cases lg k with
  | none => rfl
  | some req =>
    simp only [Option.elim]
    split_ifs with h
    · exact hs.reply _ h req _ _ (hs.oracleIn _)
    · rfl

end Bisimulation

end Quantum.Env

namespace Quantum.Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  [DecidableEq Req] [DecidableEq A] [AddGroup Y] {n m : ℕ} (D : Distinguisher W X Y Req A n m)
  {Ω Ω' : Type*} {St St' : Type _} {Q : ℕ} [OracleState St X Y] [OracleState St' X Y]

/-- **Bisimilar environments give the same game**: the final state, hence the acceptance
probability, on tapes related by a bisimulation. -/
theorem final_eq_of_bisimulation {E : Env Ω Req A X Y Q St} {E' : Env Ω' Req A X Y Q St'}
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    {ω : Ω} {ω' : Ω'} {R : ℕ → St → St' → Prop} (hs : E.Bisimulation E' ω ω' R) :
    D.final E post ω = D.final E' post ω' := by
  have hev : ∀ k, D.eventPerm E ω k = D.eventPerm E' ω' k := fun k => by
    simp only [eventPerm, Env.requestPerm, Env.oraclePerm, hs.oracle_eq, hs.answer_eq]
  simp only [final, run, stage, hev, hs.oracle_eq]

/-- Bisimilar environments have the same acceptance probability on related tapes. -/
theorem acceptProbAt_eq_of_bisimulation {E : Env Ω Req A X Y Q St} {E' : Env Ω' Req A X Y Q St'}
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    {ω : Ω} {ω' : Ω'} {R : ℕ → St → St' → Prop} (hs : E.Bisimulation E' ω ω' R) :
    D.acceptProbAt E post ω = D.acceptProbAt E' post ω' := by
  rw [acceptProbAt, acceptProbAt, D.final_eq_of_bisimulation post hs]

/-- The acceptance probability is nonnegative. -/
theorem acceptProb_nonneg [Fintype Ω] (E : Env Ω Req A X Y Q St)
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)) :
    0 ≤ D.acceptProb E post :=
  Finset.sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (prob_nonneg _ _)

end Quantum.Distinguisher

namespace Quantum.IAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] [DecidableEq O] (A : IAlg X Y Req Resp O)

end Quantum.IAlg

namespace QROM

variable {X Y Stmt Wit Proof Coins SimCoins : Type}

variable (rel : Stmt → Wit → Prop) [DecidableRel rel]

/-- **The real challenger** answering `Q` proof queries: proof query number `c` with `(x, w)` is answered
by the honest prover's program on the coins of proof query `c` if `rel x w`, by `none` otherwise; it
assigns nothing. -/
noncomputable def realChallenger [Fintype Coins] [DecidableEq Coins]
    (P : NARG.Prover X Y Stmt Wit Proof Coins) (Q : ℕ) : Quantum.Challenger X Y (ProofQuery Stmt Wit) Proof where
  Coins := Fin Q → Coins
  coins := PMF.pi fun _ => P.coins
  Q := Q
  q := P.q
  respond ω hist req :=
    if h : hist.length < Q then
      if rel req.stmt req.wit then
        (P.prog req.stmt req.wit (ω ⟨hist.length, h⟩)).bind fun π => .pure ⟨some π, []⟩
      else .pure ⟨none, []⟩
    else .pure ⟨none, []⟩
  respond_queries ω hist req H := by
    split_ifs
    · simpa using P.prog_queries _ _ _ H
    · simp
    · simp

/-- **The simulated challenger** answering `Q` proof queries: proof query number `c` with `(x, w)` and
`rel x w` runs the simulator's program on the coins of proof query `c` with the oracle in force,
answers with its proof and appends its assignment list; an invalid proof query is answered by
`none`. -/
noncomputable def simChallenger [Fintype SimCoins] [DecidableEq SimCoins]
    (S : NARG.Simulator X Y Stmt Proof SimCoins) (Q : ℕ) : Quantum.Challenger X Y (ProofQuery Stmt Wit) Proof where
  Coins := Fin Q → SimCoins
  coins := PMF.pi fun _ => S.coins
  Q := Q
  q := S.q
  respond ω hist req :=
    if h : hist.length < Q then
      if rel req.stmt req.wit then
        (S.prog req.stmt (ω ⟨hist.length, h⟩)).bind fun r => .pure ⟨some r.proof, r.assignments⟩
      else .pure ⟨none, []⟩
    else .pure ⟨none, []⟩
  respond_queries ω hist req H := by
    split_ifs
    · simpa using S.prog_queries _ _ H
    · simp
    · simp

/-! ### The pure images of the challengers -/

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

/-- On every tape, the real environment of the honest prover's pure image is bisimilar to the
real challenger: the challenger's state has the tape's oracle, no assignments and one history
entry per proof query numbered below `Q`. -/
theorem bisimulation_real [Fintype Coins] [DecidableEq Coins]
    (P : NARG.Prover X Y Stmt Wit Proof Coins) (Q : ℕ) (ω : (X → Y) × (Fin Q → Coins)) :
    (realEnv rel P.toFn Q).Bisimulation (realChallenger rel P Q).toPureEnv ω ω
      fun i H s => H = ω.1 ∧ s.base = ω.1 ∧ s.ass = [] ∧ s.hist.length = min i Q where
  init := by simp [realEnv, Quantum.Challenger.toPureEnv]
  step i h req H s := by
    rintro ⟨hH, hb, ha, hl⟩
    have hl' : s.hist.length = i := by rw [hl]; exact min_eq_left h.le
    subst hl'
    simp only [realEnv, Quantum.Challenger.toPureEnv, realChallenger, h, ↓reduceDIte]
    split_ifs <;> simp [hH, hb, ha, min_eq_left (Nat.succ_le_of_lt h)]
  skip i hi H s := by
    rintro ⟨hH, hb, ha, hl⟩
    exact ⟨hH, hb, ha, by rw [hl, min_eq_right hi, min_eq_right (by omega)]⟩
  reply i h req H s := by
    rintro ⟨hH, hb, ha, hl⟩
    have hl' : s.hist.length = i := by rw [hl]; exact min_eq_left h.le
    subst hl' hH
    simp only [realEnv, Quantum.Challenger.toPureEnv, realChallenger, h, ↓reduceDIte,
      NARG.Prover.toFn]
    split_ifs <;> simp [hb, ha, Function.reprogram]
  oracle i H s := by
    rintro ⟨hH, hb, ha, -⟩
    rw [Quantum.OracleState.toOracle_fun]
    change H = s.base.reprogram s.ass
    rw [hb, ha, hH]
    rfl

/-- On every tape, the simulated environment of the simulator's pure image is bisimilar to the
simulated challenger: the challenger's state has the tape's oracle as its base, the oracle in
force as its base reprogrammed by its assignments, and one history entry per proof query numbered
below `Q`. -/
theorem bisimulation_sim [Fintype SimCoins] [DecidableEq SimCoins]
    (S : NARG.Simulator X Y Stmt Proof SimCoins) (Q : ℕ) (ω : (X → Y) × (Fin Q → SimCoins)) :
    (simEnv rel S.toFn Q).Bisimulation (simChallenger (Wit := Wit) rel S Q).toPureEnv ω ω
      fun i H s => s.base = ω.1 ∧ s.base.reprogram s.ass = H ∧ s.hist.length = min i Q where
  init := by simp [simEnv, Quantum.Challenger.toPureEnv, Function.reprogram]
  step i h req H s := by
    rintro ⟨hb, hH, hl⟩
    have hl' : s.hist.length = i := by rw [hl]; exact min_eq_left h.le
    subst hl' hH
    simp only [simEnv, Quantum.Challenger.toPureEnv, simChallenger, h, ↓reduceDIte,
      NARG.Simulator.toFn]
    split_ifs <;> simp [hb, reprogram_append, min_eq_left (Nat.succ_le_of_lt h)]
  skip i hi H s := by
    rintro ⟨hb, hH, hl⟩
    exact ⟨hb, hH, by rw [hl, min_eq_right hi, min_eq_right (by omega)]⟩
  reply i h req H s := by
    rintro ⟨hb, hH, hl⟩
    have hl' : s.hist.length = i := by rw [hl]; exact min_eq_left h.le
    subst hl' hH
    simp only [simEnv, Quantum.Challenger.toPureEnv, simChallenger, h, ↓reduceDIte,
      NARG.Simulator.toFn]
    split_ifs <;> simp
  oracle i H s := by
    rintro ⟨-, hH, -⟩
    rw [Quantum.OracleState.toOracle_fun]
    exact hH.symm

variable [AddGroup Y] {W : Type} [Fintype W] [Fintype Stmt] [Fintype Wit] [DecidableEq Stmt]
  [DecidableEq Wit] [Fintype Proof] [DecidableEq Proof] {n m : ℕ}

/-- **The real challenger's game is the real game of the pure image**: the acceptance
probability of every distinguisher against the real challenger, as an environment, is that
against `realEnv` for the honest prover's pure image. -/
theorem acceptProb_real [Fintype Coins] [DecidableEq Coins]
    (P : NARG.Prover X Y Stmt Wit Proof Coins) (Q : ℕ)
    (D : Quantum.Distinguisher W X Y (ProofQuery Stmt Wit) Proof n m)
    (post : (X → Y) → Quantum.QState (Quantum.DReg W n X Y (ProofQuery Stmt Wit) Proof) ≃ₗᵢ[ℂ]
      Quantum.QState (Quantum.DReg W n X Y (ProofQuery Stmt Wit) Proof)) :
    D.acceptProb (realChallenger rel P Q).toPureEnv post =
      D.acceptProb (realEnv rel P.toFn Q) post :=
  Fintype.sum_congr _ _ fun ω => by
    rw [D.acceptProbAt_eq_of_bisimulation post (bisimulation_real rel P Q ω)]
    rfl

/-- **The simulated challenger's game is the simulated game of the pure image**. -/
theorem acceptProb_sim [Fintype SimCoins] [DecidableEq SimCoins]
    (S : NARG.Simulator X Y Stmt Proof SimCoins) (Q : ℕ)
    (D : Quantum.Distinguisher W X Y (ProofQuery Stmt Wit) Proof n m)
    (post : (X → Y) → Quantum.QState (Quantum.DReg W n X Y (ProofQuery Stmt Wit) Proof) ≃ₗᵢ[ℂ]
      Quantum.QState (Quantum.DReg W n X Y (ProofQuery Stmt Wit) Proof)) :
    D.acceptProb (simChallenger (Wit := Wit) rel S Q).toPureEnv post =
      D.acceptProb (simEnv rel S.toFn Q) post :=
  Fintype.sum_congr _ _ fun ω => by
    rw [D.acceptProbAt_eq_of_bisimulation post (bisimulation_sim rel S Q ω)]
    rfl

variable [Nonempty X] [DecidableEq Y] [Fintype Coins] [DecidableEq Coins] [Fintype SimCoins]
  [DecidableEq SimCoins]

variable {rel}

end QROM

end GordieHowe
