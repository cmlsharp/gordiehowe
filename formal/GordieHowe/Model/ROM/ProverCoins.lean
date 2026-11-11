-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.ROM.NIZK

public section

/-!
# The prover's coins in the real environment

The real environment of `GordieHowe/Model/ROM/NIZK.lean` draws independent coins for each proof
query from a coin law `μ`. Three facts about that law:

* `IAlg.acceptProb_realEnv_eq_of_map`: a prover whose coins are a function `f` of another
  prover's coins, with the law pushed forward by `f`, and whose proofs agree through `f`, has the
  same acceptance probability against every algorithm.
* `Adversary.advantage_le_one`: an advantage is at most one.
* `Adversary.abs_acceptProb_realEnv_law_sub_le`: replacing the coin law `ν` by `ν'` moves
  the acceptance probability of every adversary with `Q` proof queries answered by at most
  `Q · tvDist ν ν'`.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.ROM.NIZK

open GordieHowe.Quantum GordieHowe.QROM

variable {X Y Stmt Wit Proof : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  (rel : Stmt → Wit → Prop) [DecidableRel rel] {Coins Coins' : Type} [Fintype Coins]
  [Fintype Coins']

/-- The tape of pushed-forward coins is the pushed-forward tape. -/
theorem tapeDist_map {Q : ℕ} (μ : PMF Coins) (f : Coins → Coins') :
    tapeDist (X := X) (Y := Y) Q (μ.map f) =
      (tapeDist Q μ).map fun ω => (ω.1, fun i => f (ω.2 i)) := by
  rw [tapeDist, tapeDist, PMF.map_bind]
  congr 1
  funext H
  rw [← PMF.pi_map, PMF.map_comp, PMF.map_comp]
  rfl

/-- **Pushing the coins forward**: if `P'.prove … (f c) = P.prove … c` and the coin law `ν'` of
`P'` is the law `ν` of `P` pushed forward by `f`, the two real environments give every algorithm
the same acceptance probability. -/
theorem IAlg.acceptProb_realEnv_eq_of_map {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) {Q : ℕ}
    (P : NARG.ProverFn X Y Stmt Wit Proof Coins) (P' : NARG.ProverFn X Y Stmt Wit Proof Coins')
    (ν : PMF Coins) (ν' : PMF Coins') (f : Coins → Coins')
    (hprove : ∀ H x w c, P'.prove H x w (f c) = P.prove H x w c) (hcoins : ν' = ν.map f) :
    A.acceptProb (realEnv rel P' ν' Q) = A.acceptProb (realEnv rel P ν Q) := by
  have hresp : ∀ ω : (X → Y) × (Fin Q → Coins),
      envResponder (realEnv rel P' ν' Q) (ω.1, fun i => f (ω.2 i)) =
        envResponder (realEnv rel P ν Q) ω :=
    fun ω => by
      funext i req O
      simp only [envResponder, realEnv, hprove]
  rw [IAlg.acceptProb, IAlg.acceptProb]
  change (tapeDist Q ν').toOuterMeasure _ = (tapeDist Q ν).toOuterMeasure _
  rw [hcoins, tapeDist_map, PMF.toOuterMeasure_map_apply]
  congr 1
  ext ω
  change A.accepts (envResponder (realEnv rel P' ν' Q) (ω.1, fun i => f (ω.2 i))) ω.1 = true ↔
    A.accepts (envResponder (realEnv rel P ν Q) ω) ω.1 = true
  rw [hresp]

/-- The tapes of two coin laws are within `Q` times the distance of the laws. -/
theorem tvDist_tapeDist_le {Q : ℕ} (ν ν' : PMF Coins) :
    PMF.tvDist (tapeDist (X := X) (Y := Y) Q ν) (tapeDist Q ν') ≤ Q * PMF.tvDist ν ν' := by
  rw [tapeDist, tapeDist]
  refine (PMF.tvDist_bind_left_le' _ _ _).trans ?_
  have hk : ∀ H : X → Y, PMF.tvDist ((PMF.pi fun _ : Fin Q => ν).map fun c => (H, c))
      ((PMF.pi fun _ : Fin Q => ν').map fun c => (H, c)) ≤ Q * PMF.tvDist ν ν' := fun H =>
    (PMF.tvDist_map_le _ _ _).trans ((PMF.tvDist_pi_le _ _).trans_eq (by simp))
  calc ∑' H, ((PMF.uniformOfFintype (X → Y)) H).toReal *
        PMF.tvDist ((PMF.pi fun _ : Fin Q => ν).map fun c => (H, c))
          ((PMF.pi fun _ : Fin Q => ν').map fun c => (H, c))
      ≤ ∑' H, ((PMF.uniformOfFintype (X → Y)) H).toReal * (Q * PMF.tvDist ν ν') := by
        rw [tsum_fintype, tsum_fintype]
        exact sum_le_sum fun H _ => mul_le_mul_of_nonneg_left (hk H) ENNReal.toReal_nonneg
    _ = Q * PMF.tvDist ν ν' := by
        rw [tsum_fintype, ← sum_mul, PMF.sum_toReal, one_mul]

/-- **Changing the coin law**: the acceptance probabilities of an algorithm against the real
environments of `P` with coins drawn from `ν` and from `ν'` differ by at most `Q · tvDist`. -/
theorem IAlg.abs_acceptProb_realEnv_law_sub_le {m : ℕ} (A : IAlg X Y Stmt Wit Proof m)
    {Q : ℕ} (P : NARG.ProverFn X Y Stmt Wit Proof Coins) (ν ν' : PMF Coins) :
    |(A.acceptProb (realEnv rel P ν Q)).toReal - (A.acceptProb (realEnv rel P ν' Q)).toReal|
      ≤ Q * PMF.tvDist ν ν' := by
  rw [IAlg.acceptProb, IAlg.acceptProb]
  exact (PMF.abs_toOuterMeasure_sub_le_tvDist _ _ _).trans (tvDist_tapeDist_le ν ν')

/-- **Changing the coin law, for an adversary**: `Q · tvDist` over its coins. -/
theorem Adversary.abs_acceptProb_realEnv_law_sub_le {m t : ℕ}
    (𝒜 : Adversary X Y Stmt Wit Proof m t) {Q : ℕ} (P : NARG.ProverFn X Y Stmt Wit Proof Coins)
    (ν ν' : PMF Coins) :
    |𝒜.acceptProb (realEnv rel P ν Q) - 𝒜.acceptProb (realEnv rel P ν' Q)| ≤
      Q * PMF.tvDist ν ν' :=
  𝒜.abs_acceptProb_sub_le _ _ fun r => (𝒜.alg r).abs_acceptProb_realEnv_law_sub_le rel P ν ν'

/-- **An advantage is at most one**: both acceptance probabilities lie in `[0, 1]`. -/
theorem Adversary.advantage_le_one {m t : ℕ} (𝒜 : Adversary X Y Stmt Wit Proof m t) {Q : ℕ}
    (P : NARG.ProverFn X Y Stmt Wit Proof Coins) (μ : PMF Coins) {SimCoins : Type}
    [Fintype SimCoins] (S : NARG.SimulatorFn X Y Stmt Proof SimCoins) :
    𝒜.advantage rel P μ S Q ≤ 1 := by
  rw [Adversary.advantage, GordieHowe.advantage]
  refine 𝒜.abs_acceptProb_sub_le _ _ fun r => abs_sub_le_iff.2 ⟨?_, ?_⟩ <;>
  · have h₀ : ((𝒜.alg r).acceptProb (realEnv rel P μ Q)).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by
        rw [ENNReal.ofReal_one]; exact PMF.toOuterMeasure_apply_le_one _ _)
    have h₁ : ((𝒜.alg r).acceptProb (simEnv rel S Q)).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by
        rw [ENNReal.ofReal_one]; exact PMF.toOuterMeasure_apply_le_one _ _)
    linarith [ENNReal.toReal_nonneg (a := (𝒜.alg r).acceptProb (realEnv rel P μ Q)),
      ENNReal.toReal_nonneg (a := (𝒜.alg r).acceptProb (simEnv rel S Q))]

end GordieHowe.ROM.NIZK
