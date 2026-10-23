-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.ROM.Interactive
public import GordieHowe.Model.ROM.NIZK

@[expose] public section

/-!
# Zero knowledge against query-bounded classical adversaries

The zero-knowledge adversaries of the classical random-oracle model are the query-bounded
adversaries of `GordieHowe/Model/ROM/Interactive.lean` with proof queries `ProofQuery Stmt Wit`, responses
`Option Proof` and output a function `(X → Y) → Bool`, which the game applies to the whole oracle
in force after the steps (so the queries after the last step are unbounded, as in
`ROM.NIZK.IAlg.post`).

- `IAlg.accepts`, `QueryBoundedAdversary.acceptProb`, `QueryBoundedAdversary.advantage`: the game
  against an environment of `GordieHowe/Model/Quantum/Pure/Game.lean`, its responder read through
  `toResponder` (`ROM.NIZK.envResponder`).
- `GordieHowe.ROM.ZeroKnowledge rel P S ε`: every query-bounded adversary with a budget of
  `t` queries has advantage at most `ε t Q`.
- `IAlg.toNIZK`, `QueryBoundedAdversary.toNIZK`: the maps to the adversaries of
  `GordieHowe/Model/ROM/NIZK.lean`, with equal advantages (`advantage_toNIZK`).
-/

namespace GordieHowe.ROM

open GordieHowe.Quantum GordieHowe.QROM
open scoped ENNReal

variable {X Y Stmt Wit Proof : Type}

/-! ### Conversions of actions, replies and responders -/

/-- An action as an action of `ROM.NIZK`. -/
def Action.toNIZK : Action X (ProofQuery Stmt Wit) → NIZK.Action X Stmt Wit
  | .query x => .query x
  | .request r => .request r

/-- A reply as a reply of `ROM.NIZK`. -/
def Reply.toNIZK : Reply Y (Option Proof) → NIZK.Reply Y Proof
  | .answer y => .answer y
  | .response o => .response o

/-- A reply of `ROM.NIZK` as a reply. -/
def Reply.ofNIZK : NIZK.Reply Y Proof → Reply Y (Option Proof)
  | .answer y => .answer y
  | .response o => .response o

@[simp] theorem Reply.ofNIZK_toNIZK (r : Reply Y (Option Proof)) : Reply.ofNIZK r.toNIZK = r := by
  cases r <;> rfl

@[simp] theorem Reply.map_ofNIZK_toNIZK (l : List (Reply Y (Option Proof))) :
    (l.map Reply.toNIZK).map Reply.ofNIZK = l := by
  simp [List.map_map, Function.comp_def]

/-- A responder of `ROM.NIZK` as a responder. -/
def toResponder (R : NIZK.Responder X Y Stmt Wit Proof) :
    Responder X Y (ProofQuery Stmt Wit) (Option Proof) :=
  fun i r O => ((R i r O).response, (R i r O).state)

/-! ### The game -/

namespace IAlg

variable {m : ℕ} (𝒜 : IAlg X Y (ProofQuery Stmt Wit) (Option Proof) ((X → Y) → Bool) m)

/-- **The output bit against `R` from `O`**: the output function applied to the oracle in force
after the `m` steps. -/
def accepts (R : Responder X Y (ProofQuery Stmt Wit) (Option Proof)) (O : X → Y) : Bool :=
  𝒜.out (𝒜.run R O m).hist (𝒜.run R O m).oracle

/-- **The algorithm as an algorithm of `ROM.NIZK`**: the same actions, with the output function
applied by `post` to the final oracle. -/
def toNIZK : NIZK.IAlg X Y Stmt Wit Proof m where
  next hist := (𝒜.next (hist.map Reply.ofNIZK)).toNIZK
  post O hist := 𝒜.out (hist.map Reply.ofNIZK) O

/-- **The run of `toNIZK` is the run of the algorithm**, replies converted. -/
theorem run_toNIZK (R : NIZK.Responder X Y Stmt Wit Proof) (O : X → Y) :
    ∀ k, 𝒜.toNIZK.run R O k =
      ⟨(𝒜.run (toResponder R) O k).hist.map Reply.toNIZK, (𝒜.run (toResponder R) O k).oracle,
        (𝒜.run (toResponder R) O k).nreq⟩
  | 0 => rfl
  | k + 1 => by
    rw [NIZK.IAlg.run, run_toNIZK R O k, run_succ]
    have hn : 𝒜.toNIZK.next ((𝒜.run (toResponder R) O k).hist.map Reply.toNIZK) =
        (𝒜.next (𝒜.run (toResponder R) O k).hist).toNIZK := by
      simp [toNIZK, Function.comp_def, Reply.ofNIZK_toNIZK]
    unfold NIZK.IAlg.step step
    simp only at hn ⊢
    rw [hn]
    cases 𝒜.next (𝒜.run (toResponder R) O k).hist <;> simp [Action.toNIZK, Reply.toNIZK, toResponder]

theorem accepts_toNIZK (R : NIZK.Responder X Y Stmt Wit Proof) (O : X → Y) :
    𝒜.toNIZK.accepts R O = 𝒜.accepts (toResponder R) O := by
  rw [NIZK.IAlg.accepts, run_toNIZK, accepts]
  simp [toNIZK, Function.comp_def, Reply.ofNIZK_toNIZK]

theorem queryCount_toNIZK (R : NIZK.Responder X Y Stmt Wit Proof) (O : X → Y) :
    𝒜.toNIZK.queryCount R O = 𝒜.queryCount (toResponder R) O := by
  unfold NIZK.IAlg.queryCount queryCount
  congr 1
  refine Finset.filter_congr fun k _ => ?_
  rw [run_toNIZK]
  simp only [toNIZK, Reply.map_ofNIZK_toNIZK]
  cases 𝒜.next (𝒜.run (toResponder R) O k).hist <;> rfl

theorem budget_toNIZK {t : ℕ} (h : 𝒜.Budget t) : 𝒜.toNIZK.Budget t := fun R O => by
  rw [queryCount_toNIZK]
  exact h _ O

end IAlg

namespace QueryBoundedAdversary

variable {t : ℕ} (𝒜 : QueryBoundedAdversary X Y (ProofQuery Stmt Wit) (Option Proof)
  ((X → Y) → Bool) t)

/-- **The probability that `𝒜` outputs `true` against the environment `E`**, over its coins and
the environment's tape. -/
noncomputable def acceptProb {Ω : Type} {Q : ℕ} (E : Env Ω (ProofQuery Stmt Wit) Proof X Y Q) : ℝ :=
  (∑' r, 𝒜.coins r *
    Pr[ω ~ E.μ : (𝒜.alg r).accepts (toResponder (NIZK.envResponder E ω)) (E.oracle₀ ω) = true]).toReal

/-- **The adversary as an adversary of `ROM.NIZK`** (`IAlg.toNIZK` at each value of the coins). -/
def toNIZK : NIZK.Adversary X Y Stmt Wit Proof 𝒜.steps t where
  Coins := 𝒜.Coins
  coins := 𝒜.coins
  alg r := (𝒜.alg r).toNIZK
  budget r := (𝒜.alg r).budget_toNIZK (𝒜.budget r)

theorem acceptProb_toNIZK {Ω : Type} {Q : ℕ} (E : Env Ω (ProofQuery Stmt Wit) Proof X Y Q) :
    𝒜.toNIZK.acceptProb E = 𝒜.acceptProb E := by
  simp only [NIZK.Adversary.acceptProb, NIZK.IAlg.acceptProb, acceptProb, toNIZK,
    IAlg.accepts_toNIZK]
  rfl

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] (rel : Stmt → Wit → Prop)
  [DecidableRel rel] {Coins SimCoins : Type} [Fintype Coins] [Fintype SimCoins]

/-- **The advantage of `𝒜`** with `Q` proof queries answered: the difference of its acceptance
probabilities against the real environment of `P` and the simulated environment of `S`. -/
noncomputable def advantage (P : NARG.ProverFn X Y Stmt Wit Proof Coins)
    (S : NARG.SimulatorFn X Y Stmt Proof SimCoins) (Q : ℕ) : ℝ :=
  GordieHowe.advantage (𝒜.acceptProb (realEnv rel P Q)) (𝒜.acceptProb (simEnv rel S Q))

theorem advantage_toNIZK (P : NARG.ProverFn X Y Stmt Wit Proof Coins)
    (S : NARG.SimulatorFn X Y Stmt Proof SimCoins) (Q : ℕ) :
    𝒜.toNIZK.advantage rel P S Q = 𝒜.advantage rel P S Q := by
  rw [NIZK.Adversary.advantage, advantage, acceptProb_toNIZK, acceptProb_toNIZK]

end QueryBoundedAdversary

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] {rel : Stmt → Wit → Prop}
  [DecidableRel rel] {Coins SimCoins : Type} [Fintype Coins] [Fintype SimCoins]

end GordieHowe.ROM
