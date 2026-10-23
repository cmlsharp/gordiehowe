-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.QueryBoundedLastProofQuery
public import GordieHowe.Model.Quantum.Pure.PostSlots

@[expose] public section

/-!
# Query-counted zero knowledge against query-bounded adversaries

Unruh 2017 Definition 6 (ePrint 2017/398, p. 14) over the paper's `(t, Q)`-adversaries
(`QueryBoundedAdversary`, `def:adversary`) with every query counted: the bound `t` of the class
covers the query slots and the post phase (`QueryBoundedAdversary.queries_le`), and the output is the
measurement of the workspace, so nothing reads the oracle after the counted queries
(`GordieHowe.QROM.ZeroKnowledge`). It is implied by everlasting zero knowledge
(`GordieHowe.QROM.EverlastingZeroKnowledge.zeroKnowledge`), whose adversaries may query
without bound after their last proof query.

The pure counterpart (`GordieHowe.QROM.ZeroKnowledgeQueryBoundedPure`) quantifies over distinguishers with a
budget of `q` query slots and no final unitary. It gives the notion over the class
(`GordieHowe.QROM.ZeroKnowledgeQueryBoundedPure.zeroKnowledgeQueryBounded`): each adversary is, by deferred
measurement, its dilation (`AdaptiveIAlg.toReal_compose`), whose post phase of query batches is
moved into `post` further query slots (`Distinguisher.withPostSlots`); the dilation has a budget of
`budget` query slots (`AdaptiveIAlg.dilBudget`), so the new distinguisher has one of
`budget + post` slots, and `width * (budget + post) ≤ t`.
-/

open Finset Matrix
open scoped BigOperators ENNReal

namespace GordieHowe

namespace Quantum.KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] (A : KindAlg X Y Req Resp O)
  [AddGroup Y]

/-- **The post phase of the dilation is a post phase of query batches** (`Distinguisher.postN`). -/
theorem postOpN_eq_postN (H : X → Y) : ∀ i,
    A.postOpN H i = Distinguisher.postN (fun j => A.uStepD (A.slots + 1 + j)) H i
  | 0 => rfl
  | i + 1 => by
    rw [postOpN, postOpN_eq_postN H i]
    rfl

end Quantum.KindAlg

namespace Quantum.AdaptiveIAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  (A : AdaptiveIAlg X Y Req Resp O) [Nonempty X] [AddGroup Y] [Nonempty Y] [DecidableEq O]

/-- **The dilated adversary has a budget of `budget` query slots**: the invariant of
`dilRequestBudget` at the budget; a branch that queries has not halted and its counter, one more
than its query slots so far, is at most `budget`. -/
def dilBudget (o : O) : (A.toKindAlg.dilate o).Budget A.budget where
  inv := (A.dilRequestBudget A.requestsAfterAtMost_budget o).inv
  init := (A.dilRequestBudget A.requestsAfterAtMost_budget o).init
  step := (A.dilRequestBudget A.requestsAfterAtMost_budget o).step
  cap k hk c w hw hkind := by
    obtain ⟨-, hw⟩ := hw
    change (A.kind w.1.1 || w.2.1) = false at hkind
    rw [Bool.or_eq_false_iff] at hkind
    rcases hw with h | ⟨h1, h2, -⟩
    · rw [hkind.2] at h
      exact absurd h Bool.false_ne_true
    · rw [hkind.1] at h1
      simp only [Bool.false_eq_true, if_false] at h1
      omega

end Quantum.AdaptiveIAlg

namespace QROM

variable {X Y Stmt Wit Proof Coins SimCoins : Type} (rel : Stmt → Wit → Prop) [DecidableRel rel]
  [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [AddGroup Y]
  [Fintype Stmt] [Fintype Wit] [DecidableEq Stmt] [DecidableEq Wit] [Fintype Proof]
  [DecidableEq Proof] [Nonempty X] [DecidableEq Y] [Fintype Coins] [DecidableEq Coins]
  [Fintype SimCoins] [DecidableEq SimCoins]

/-- **Query-counted zero knowledge against query-bounded adversaries** (Unruh 2017 Definition 6,
p. 14, over the paper's `(t, Q)`-adversaries, `def:adversary`, all of whose queries are counted):
for all `t` and `Q`, every `t`-query adversary that outputs a bit (at most `t` queries on every
branch, over its query slots and its post phase, `QueryBoundedAdversary.queries_le`) outputs
`true` against the real challenger of `P` and against the simulated challenger of `S`, each
answering the first `Q` proof queries, with probabilities at most `ε t Q` apart. -/
def _root_.GordieHowe.QROM.ZeroKnowledge (P : NARG.Prover X Y Stmt Wit Proof Coins)
    (S : NARG.Simulator X Y Stmt Proof SimCoins) (ε : ℕ → ℕ → ℝ) : Prop :=
  ∀ (t Q : ℕ) (𝒟 : Quantum.QueryBoundedAdversary X Y (ProofQuery Stmt Wit) Proof Bool t),
    GordieHowe.advantage (𝒟.acceptProb (realChallenger rel P Q)).toReal
      (𝒟.acceptProb (simChallenger rel S Q)).toReal ≤ ε t Q

/-- **Query-counted zero knowledge against distinguishers with a query budget and no final
unitary**: for every query bound `t`, every distinguisher with `m` slots of `n` parallel queries or
one proof query and a budget of `q` query slots (`Distinguisher.Budget`) with `n * q ≤ t`, against
environments answering `Q` proof queries, without a final unitary (`noPost`), has advantage at most
`ε t Q` against the simulator `S`. -/
def ZeroKnowledgeQueryBoundedPure (P : NARG.ProverFn X Y Stmt Wit Proof Coins)
    (S : NARG.SimulatorFn X Y Stmt Proof SimCoins) (ε : ℕ → ℕ → ℝ) : Prop :=
  ∀ (t : ℕ) (W : Type) [Fintype W] (n m Q q : ℕ)
    (D : Quantum.Distinguisher W X Y (ProofQuery Stmt Wit) Proof n m) (_ : D.Budget q),
    n * q ≤ t → QROM.advantage (Q := Q) rel P S D Quantum.noPost ≤ ε t Q

variable {rel}

omit [Nonempty X] [DecidableEq Y] [DecidableEq Coins] [DecidableEq SimCoins] in
/-- A larger error bound. -/
theorem ZeroKnowledgeQueryBoundedPure.mono {P : NARG.ProverFn X Y Stmt Wit Proof Coins}
    {S : NARG.SimulatorFn X Y Stmt Proof SimCoins} {ε ε' : ℕ → ℕ → ℝ}
    (h : ZeroKnowledgeQueryBoundedPure rel P S ε) (hε : ∀ t Q, ε t Q ≤ ε' t Q) :
    ZeroKnowledgeQueryBoundedPure rel P S ε' :=
  fun t W _ n m Q q D bud hD => (h t W n m Q q D bud hD).trans (hε t Q)

/-- A larger error bound. -/
theorem _root_.GordieHowe.QROM.ZeroKnowledge.mono {P : NARG.Prover X Y Stmt Wit Proof Coins}
    {S : NARG.Simulator X Y Stmt Proof SimCoins} {ε ε' : ℕ → ℕ → ℝ}
    (h : GordieHowe.QROM.ZeroKnowledge rel P S ε) (hε : ∀ t Q, ε t Q ≤ ε' t Q) :
    GordieHowe.QROM.ZeroKnowledge rel P S ε' :=
  fun t Q 𝒟 => (h t Q 𝒟).trans (hε t Q)

/-- **Everlasting zero knowledge gives query-counted zero knowledge**: a `t`-query
adversary makes at most `t` queries before its last proof query (`requestsAfterAtMost_budget`). -/
theorem _root_.GordieHowe.QROM.EverlastingZeroKnowledge.zeroKnowledge
    {P : NARG.Prover X Y Stmt Wit Proof Coins} {S : NARG.Simulator X Y Stmt Proof SimCoins}
    {ε : ℕ → ℕ → ℝ} (h : GordieHowe.QROM.EverlastingZeroKnowledge rel P S ε) :
    GordieHowe.QROM.ZeroKnowledge rel P S ε := fun t Q 𝒟 =>
  h t Q t 𝒟 fun a => ⟨(𝒟.alg a).budget,
    (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)).trans (𝒟.queries_le a),
    (𝒟.alg a).requestsAfterAtMost_budget⟩

/-- **The pure notion gives the notion over query-bounded adversaries** (module docstring). -/
theorem ZeroKnowledgeQueryBoundedPure.zeroKnowledgeQueryBounded
    {P : NARG.Prover X Y Stmt Wit Proof Coins} {S : NARG.Simulator X Y Stmt Proof SimCoins}
    {ε : ℕ → ℕ → ℝ}
    (h : ZeroKnowledgeQueryBoundedPure rel P.toFn S.toFn ε) :
    GordieHowe.QROM.ZeroKnowledge rel P S ε := by
  intro t Q 𝒟
  refine PMF.abs_toReal_tsum_mul_sub_le 𝒟.aux (fun _ => PMF.toOuterMeasure_apply_le_one _ _)
    (fun _ => PMF.toOuterMeasure_apply_le_one _ _) fun a => ?_
  set A := 𝒟.alg a
  rw [Quantum.AdaptiveIAlg.toReal_compose, Quantum.AdaptiveIAlg.toReal_compose, acceptProb_real, acceptProb_sim]
  have hpost : A.toKindAlg.postOp =
      fun H => Quantum.Distinguisher.postN (fun j => A.toKindAlg.uStepD (A.toKindAlg.slots + 1 + j)) H
        A.toKindAlg.post := funext fun H => A.toKindAlg.postOpN_eq_postN H _
  rw [hpost, ← Quantum.Distinguisher.acceptProb_withPostSlots, ← Quantum.Distinguisher.acceptProb_withPostSlots]
  exact h t _ _ _ Q _ _ (Quantum.Distinguisher.Budget.withPostSlots _ _ _ (A.dilBudget true)) (𝒟.queries_le a)

end QROM

end GordieHowe
