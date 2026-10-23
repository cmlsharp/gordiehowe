-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.ROM.HiddenLeaves

@[expose] public section

/-!
# Query-counted zero knowledge with hidden leaf digests in the classical random-oracle model

**The notion** (`ZeroKnowledgeQueryBounded`): Unruh 2017 Definition 6 (ePrint 2017/398, p. 14)
with classical adversaries all of whose queries are counted: every adversary with a budget of `t`
queries whose output does not read the final oracle (`IAlg.PostOracleFree`), with `Q` proof queries
answered, has advantage at most `ε t Q`. It is implied by `ZeroKnowledge` (whose adversaries may
also read the whole final oracle), so the errors of `ZeroKnowledge` are errors here too
(`ZeroKnowledge.zeroKnowledgeQueryBounded`).

**The composite theorem** (`zeroKnowledgeQueryBounded_of_leafKernel`): the real game of a prover
`P` and the simulated game of a simulator `S` are compared through three intermediate games:

1. the game of a kernel `K₁` that is the honest-digest kernel `L.kL` of a leaf kernel up to a
   bijection of the coins, at the error `ε₁` of zero knowledge of `P` against `K₁` read as a
   simulator of the proof queries (`Kernel.toSimulator`, `GordieHowe/Model/ROM/ProgEnv.lean`);
2. the game of the uniform-digest kernel `L.kD`, at `Q (4 t |Pos| + 4 (Q |Pos|² + |Pos| |pub|)) / |N|`
   (`abs_toReal_acceptProb_progEnv_kL_sub_kD_le`, the hidden leaf digests, `GordieHowe/Model/ROM/HiddenLeaves.lean`);
3. the simulated game of `S`, at `Q ε₃` when the replies of `L.kD` and of `S` are within `ε₃` in
   total variation at every valid proof query and oracle (`abs_toReal_acceptProb_progEnv_sub_le`).
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.ROM.NIZK

open GordieHowe.Quantum GordieHowe.QROM

variable {X Y Stmt Wit Proof : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  (rel : Stmt → Wit → Prop) [DecidableRel rel] {Coins SimCoins : Type} [Fintype Coins]
  [Fintype SimCoins]

/-- **Zero knowledge in the classical random-oracle model against query-bounded adversaries**
(Unruh 2017 Definition 6, p. 14, with classical adversaries, whose oracle algorithm makes all its
queries within the bound): for all `m`, `t` and `Q`, every classical adversary with `m` steps and
a budget of `t` queries whose output does not read the final oracle, with its first `Q` proof queries
answered, has advantage at most `ε t Q` between the prover `P` and the simulator `S`. -/
def ZeroKnowledgeQueryBounded (P : NARG.ProverFn X Y Stmt Wit Proof Coins)
    (S : NARG.SimulatorFn X Y Stmt Proof SimCoins) (ε : ℕ → ℕ → ℝ) : Prop :=
  ∀ (m t Q : ℕ) (𝒜 : Adversary X Y Stmt Wit Proof m t), (∀ r, (𝒜.alg r).PostOracleFree) →
    𝒜.advantage rel P S Q ≤ ε t Q

variable {rel}

/-- **Zero knowledge against adversaries unbounded after their steps gives zero knowledge against
query-bounded adversaries**, at the same error. -/
theorem ZeroKnowledge.zeroKnowledgeQueryBounded {P : NARG.ProverFn X Y Stmt Wit Proof Coins}
    {S : NARG.SimulatorFn X Y Stmt Proof SimCoins} {ε : ℕ → ℕ → ℝ} (h : ZeroKnowledge rel P S ε) :
    ZeroKnowledgeQueryBounded rel P S ε :=
  fun m t Q 𝒜 _ => h m t Q 𝒜

/-- A larger error bound. -/
theorem ZeroKnowledgeQueryBounded.mono {P : NARG.ProverFn X Y Stmt Wit Proof Coins}
    {S : NARG.SimulatorFn X Y Stmt Proof SimCoins} {ε ε' : ℕ → ℕ → ℝ}
    (h : ZeroKnowledgeQueryBounded rel P S ε) (hε : ∀ t Q, ε t Q ≤ ε' t Q) :
    ZeroKnowledgeQueryBounded rel P S ε' :=
  fun m t Q 𝒜 h𝒜 => (h m t Q 𝒜 h𝒜).trans (hε t Q)

/-- **A deterministic algorithm as an adversary** with trivial coins. -/
noncomputable def Adversary.ofAlg {m t : ℕ} (A : IAlg X Y Stmt Wit Proof m) (hA : A.Budget t) :
    Adversary X Y Stmt Wit Proof m t where
  Coins := Unit
  coins := PMF.pure ()
  alg _ := A
  budget _ := hA

theorem Adversary.acceptProb_ofAlg {m t : ℕ} (A : IAlg X Y Stmt Wit Proof m) (hA : A.Budget t)
    {Ω : Type} {Q : ℕ} (E : Env Ω (ProofQuery Stmt Wit) Proof X Y Q) :
    (Adversary.ofAlg A hA).acceptProb E = (A.acceptProb E).toReal := by
  unfold Adversary.acceptProb Adversary.ofAlg
  rw [tsum_fintype, Fintype.sum_unique]
  change ((PMF.pure ()) () * A.acceptProb E).toReal = _
  rw [PMF.pure_apply_self, one_mul]

/-- **Kernels that agree up to a bijection of their coins give the same game.** -/
theorem toReal_acceptProb_progEnv_equiv {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) {C C' : Type}
    [Fintype C] [Nonempty C] [Fintype C'] [Nonempty C'] (e : C' ≃ C) (K : Kernel X Y Stmt Wit Proof C)
    (K' : Kernel X Y Stmt Wit Proof C') (hK : ∀ req O c, K' req O c = K req O (e c)) (Q : ℕ) :
    (A.acceptProb (progEnv rel K' Q)).toReal = (A.acceptProb (progEnv rel K Q)).toReal := by
  rw [toReal_acceptProb_progEnv, toReal_acceptProb_progEnv]
  let f : (X → Y) × (Fin Q → C') ≃ (X → Y) × (Fin Q → C) :=
    Equiv.prodCongr (Equiv.refl _) (Equiv.arrowCongr (Equiv.refl _) e)
  refine Fintype.expect_equiv f _ _ fun ω => ?_
  congr 2
  funext i req O
  simp only [envResponder, progEnv, kernelReply, f, Equiv.prodCongr_apply, Equiv.coe_refl,
    Prod.map, id, Equiv.arrowCongr_apply, Function.comp_apply, Equiv.refl_symm, hK]

variable [Fintype Proof]

/-- **Query-counted zero knowledge from a leaf kernel** (module docstring). For a prover `P`, a
simulator `S` and a leaf kernel `L` with its laws for the salt slot `nsalt` and the public salts
`pub` (`hL`), let `K₁` be `L.kL` up to the bijection `e` of the coins (`hK₁`), let `P` be zero
knowledge against `K₁` on the proof queries at the error `ε₁` (`h₁`), and let the replies of `L.kD` and
of `S` be within `ε₃` in total variation at every valid proof query and oracle (`h₃`). Then every
classical adversary with a budget of `t` queries whose output does not read the final oracle has
advantage at most

    ε₁ t Q + Q (4 t |Pos| + 4 (Q |Pos|² + |Pos| |pub|)) / |N| + Q ε₃

between `P` and `S` with `Q` proof queries answered. -/
theorem zeroKnowledgeQueryBounded_of_leafKernel {P : NARG.ProverFn X Y Stmt Wit Proof Coins}
    {S : NARG.SimulatorFn X Y Stmt Proof SimCoins} [Nonempty SimCoins] {Cm Pos N : Type} [Fintype Cm]
    [Nonempty Cm] [Fintype Pos] [DecidableEq Pos] [Fintype N] [DecidableEq N] [Nonempty N]
    {L : LeafKernel X Y Stmt Wit Proof Cm Pos N} {nsalt : X → Option N} {pub : Finset N}
    (hL : L.Laws nsalt pub) {C₁ : Type} [Fintype C₁] [Nonempty C₁]
    {K₁ : Kernel X Y Stmt Wit Proof C₁} (e : C₁ ≃ LeafCoins Cm Pos N Y)
    (hK₁ : ∀ req O c, K₁ req O c = L.kL req O (e c)) {ε₁ : ℕ → ℕ → ℝ}
    (h₁ : ZeroKnowledge (liftRel rel) P.liftReq K₁.toSimulator ε₁) {ε₃ : ℝ} (hε₃ : 0 ≤ ε₃)
    (h₃ : ∀ req O, rel req.stmt req.wit →
      PMF.tvDist ((PMF.uniformOfFintype (LeafCoins Cm Pos N Y)).map fun c => kernelReply rel L.kD c req O)
        ((PMF.uniformOfFintype SimCoins).map fun c => kernelReply rel (S.toKernel (Wit := Wit)) c req O) ≤
        ε₃) :
    ZeroKnowledgeQueryBounded rel P S fun t Q =>
      ε₁ t Q + Q * ((4 * t * Fintype.card Pos +
        4 * (Q * Fintype.card Pos ^ 2 + Fintype.card Pos * pub.card)) / Fintype.card N) + Q * ε₃ := by
  intro m t Q 𝒜 hpost
  refine 𝒜.abs_acceptProb_sub_le _ _ fun r => ?_
  set A := 𝒜.alg r
  have h1 := abs_acceptProb_realEnv_sub_progEnv_le rel h₁ (Adversary.ofAlg A (𝒜.budget r)) Q
  rw [Adversary.acceptProb_ofAlg, Adversary.acceptProb_ofAlg, GordieHowe.advantage,
    toReal_acceptProb_progEnv_equiv A e L.kL K₁ hK₁ Q] at h1
  have h2 := abs_toReal_acceptProb_progEnv_kL_sub_kD_le (rel := rel) hL A (𝒜.budget r) (hpost r) Q
  have h3 := abs_toReal_acceptProb_progEnv_sub_le rel L.kD (S.toKernel (Wit := Wit)) hε₃ h₃ A Q
  rw [acceptProb_simEnv_eq rel A S Q]
  have t1 := abs_sub_le (A.acceptProb (realEnv rel P Q)).toReal
    (A.acceptProb (progEnv rel L.kL Q)).toReal (A.acceptProb (progEnv rel (S.toKernel (Wit := Wit)) Q)).toReal
  have t2 := abs_sub_le (A.acceptProb (progEnv rel L.kL Q)).toReal
    (A.acceptProb (progEnv rel L.kD Q)).toReal (A.acceptProb (progEnv rel (S.toKernel (Wit := Wit)) Q)).toReal
  linarith

end GordieHowe.ROM.NIZK
