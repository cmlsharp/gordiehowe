-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.NIZK
public import GordieHowe.Model.ROM.ProverCoins
public import GordieHowe.Model.Quantum.Pure.GameTape
public import GordieHowe.Model.Quantum.O2H.SaltReprogram

@[expose] public section

/-!
# The prover's coins in the real game of the quantum random-oracle model

The real environment of `GordieHowe/Model/QROM/NIZK.lean` draws independent coins for each proof
query from a coin law `μ`. Two facts about that law, against every distinguisher of the pure game
and every final unitary:

* `QROM.acceptProb_realEnv_eq_of_map`: a prover whose coins are a function `f` of another
  prover's coins, with the law pushed forward by `f`, and whose proofs agree through `f`, has the
  same acceptance probability.
* `QROM.abs_acceptProb_realEnv_law_sub_le`: replacing the coin law `ν` by `ν'` moves the
  acceptance probability by at most `Q · tvDist ν ν'` for `Q` proof queries.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.QROM

open GordieHowe.Quantum

variable {X Y Stmt Wit Proof : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  [AddGroup Y] (rel : Stmt → Wit → Prop) [DecidableRel rel] [Fintype Stmt] [DecidableEq Stmt]
  [Fintype Wit] [DecidableEq Wit] [Fintype Proof] [DecidableEq Proof]
  {Coins Coins' : Type} [Fintype Coins] [Fintype Coins'] {W : Type} [Fintype W] {n m : ℕ}
  (D : Distinguisher W X Y (ProofQuery Stmt Wit) Proof n m)
  (post : (X → Y) → QState (DReg W n X Y (ProofQuery Stmt Wit) Proof) ≃ₗᵢ[ℂ]
    QState (DReg W n X Y (ProofQuery Stmt Wit) Proof))

/-- **Pushing the coins forward**: if `P'.prove … (f c) = P.prove … c` and the coin law `ν'` of
`P'` is the law `ν` of `P` pushed forward by `f`, the two real games give every distinguisher and
every final unitary the same acceptance probability. -/
theorem acceptProb_realEnv_eq_of_map {Q : ℕ} (P : NARG.ProverFn X Y Stmt Wit Proof Coins)
    (P' : NARG.ProverFn X Y Stmt Wit Proof Coins') (ν : PMF Coins) (ν' : PMF Coins')
    (f : Coins → Coins') (hprove : ∀ H x w c, P'.prove H x w (f c) = P.prove H x w c)
    (hcoins : ν' = ν.map f) :
    D.acceptProb (realEnv rel P' ν' Q) post = D.acceptProb (realEnv rel P ν Q) post := by
  symm
  refine D.acceptProb_comap post (fun ω => (ω.1, fun i => f (ω.2 i))) ?_ (fun _ => rfl)
    fun ω => ?_
  · change tapeDist Q ν' = (tapeDist Q ν).map _
    rw [hcoins, ROM.NIZK.tapeDist_map]
  · funext i req H
    simp only [realEnv, hprove]

/-- **Changing the coin law**: the acceptance probabilities of a distinguisher against the real
games of `P` with coins drawn from `ν` and from `ν'`, answering `Q` proof queries, differ by at
most `Q · tvDist ν ν'`. -/
theorem abs_acceptProb_realEnv_law_sub_le {Q : ℕ} (P : NARG.ProverFn X Y Stmt Wit Proof Coins)
    (ν ν' : PMF Coins) :
    |D.acceptProb (realEnv rel P ν Q) post - D.acceptProb (realEnv rel P ν' Q) post| ≤
      Q * PMF.tvDist ν ν' := by
  have h := PMF.abs_sum_toReal_mul_sub_le (tapeDist (X := X) (Y := Y) Q ν) (tapeDist Q ν')
    (g := D.acceptProbAt (realEnv rel P ν Q) post) (M := 1)
    (fun ω => by
      rw [← Distinguisher.acceptProbOnAt_univ]
      exact D.acceptProbOnAt_nonneg post _ _ ω)
    (fun ω => by
      rw [← Distinguisher.acceptProbOnAt_univ]
      exact D.acceptProbOnAt_le_one post _ _ ω)
  rw [one_mul] at h
  have hat : ∀ ω, D.acceptProbAt (realEnv rel P ν' Q) post ω =
      D.acceptProbAt (realEnv rel P ν Q) post ω := fun ω =>
    D.acceptProbAt_congr _ _ (fun _ _ => rfl) (fun _ => rfl) post
  simp only [Distinguisher.acceptProb, hat]
  exact h.trans (ROM.NIZK.tvDist_tapeDist_le ν ν')

end GordieHowe.QROM
