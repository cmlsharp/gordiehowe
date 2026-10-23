-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.ROM.SaltedZK

@[expose] public section

/-!
# Environments of programming kernels in the classical random-oracle model

A **programming kernel** (`Kernel`) answers a proof query, statement and witness, on the oracle
in force with uniform coins by a proof and an assignment list that reprograms the oracle, as a
simulator does (`GordieHowe.NARG.SimulatorFn`), except that it may read the witness. Its environment
(`progEnv`) answers proof query `i` with the coins of proof query `i` on the oracle in force; the
simulated environment of a simulator is the environment of the simulator's kernel
(`acceptProb_simEnv_eq`). These are intermediate games of the zero-knowledge hybrids
(`GordieHowe/Model/ROM/HiddenLeaves.lean`).

- `abs_toReal_acceptProb_progEnv_sub_le`: two kernels whose reply laws at every valid proof query and
  every oracle are within `ε` in total variation give games within `Q ε`, against every classical
  adversary, unbounded after its steps (a hybrid over the proof queries, each step the kernel step
  `IAlg.abs_expect_accepts_override_sub_le`).
- `IAlg.liftReq`, `Adversary.liftReq`: a proof query `⟨x, w⟩` read as the proof query `⟨⟨x, w⟩, ()⟩` of
  the game whose statements are the proof queries and whose witnesses are trivial, so that a kernel
  becomes a simulator (`Kernel.toSimulator`) and the zero-knowledge theorems of
  `GordieHowe/Model/ROM/SaltedZK.lean` apply to a kernel (`acceptProb_liftReq_realEnv`,
  `acceptProb_liftReq_simEnv`).
- `IAlg.PostOracleFree`: the output bit does not read the oracle after the steps, so every query
  of the adversary is one of its `m` steps and counts toward its budget.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.ROM.NIZK

open GordieHowe.Quantum GordieHowe.QROM

variable {X Y Stmt Wit Proof : Type}

/-! ### Adversaries whose output does not read the oracle -/

/-- **The output bit does not read the final oracle**: every query of the algorithm is one of
its steps, so a budget of `t` queries bounds all its queries (Unruh 2017 Definition 6, p. 14,
whose adversary is an oracle algorithm all of whose queries are counted). -/
def IAlg.PostOracleFree {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) : Prop :=
  ∀ O O' hist, A.post O hist = A.post O' hist

/-- With an oracle-free output, runs with the same replies give the same output. -/
theorem IAlg.accepts_eq_of_hist_eq {m : ℕ} {A : IAlg X Y Stmt Wit Proof m} (hA : A.PostOracleFree)
    {R R' : Responder X Y Stmt Wit Proof} {O O' : X → Y}
    (h : (A.run R O m).hist = (A.run R' O' m).hist) : A.accepts R O = A.accepts R' O' := by
  rw [IAlg.accepts, IAlg.accepts, h, hA]

/-! ### Kernels and their environments -/

/-- **A programming kernel**: from a proof query, the oracle in force and coins, a proof and an
assignment list that reprograms the oracle. A simulator that may read the witness. -/
abbrev Kernel (X Y Stmt Wit Proof C : Type) : Type :=
  ProofQuery Stmt Wit → (X → Y) → C → NARG.SimOutput X Y Proof

/-- **A kernel on proof queries read through `f`**: on `req` it replies as the kernel on `f req`. -/
def Kernel.comapReq {Stmt' Wit' C : Type} (K : Kernel X Y Stmt Wit Proof C)
    (f : ProofQuery Stmt' Wit' → ProofQuery Stmt Wit) : Kernel X Y Stmt' Wit' Proof C :=
  fun req O c => K (f req) O c

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] (rel : Stmt → Wit → Prop)
  [DecidableRel rel]

/-- **The reply of a kernel** with coins `c`: its proof and the oracle reprogrammed by its
assignment list on a valid proof query; `none` and the oracle unchanged on an invalid one. -/
def kernelReply {C : Type} (K : Kernel X Y Stmt Wit Proof C) (c : C) : ReplyFn X Y Stmt Wit Proof :=
  fun req O => if rel req.stmt req.wit then
    ⟨some (K req O c).proof, O.reprogram (K req O c).assignments⟩ else ⟨none, O⟩

/-- **The environment of a kernel** for `Q` proof queries: a uniform initial oracle and independent
uniform coins for each proof query; proof query `i` is answered by the kernel's reply with the coins of
proof query `i` on the oracle in force. -/
noncomputable def progEnv {C : Type} [Fintype C] [Nonempty C] (K : Kernel X Y Stmt Wit Proof C)
    (Q : ℕ) : Env ((X → Y) × (Fin Q → C)) (ProofQuery Stmt Wit) Proof X Y Q where
  μ := tapeDist Q (PMF.uniformOfFintype C)
  oracle₀ ω := ω.1
  respond ω i req O := kernelReply rel K (ω.2 i) req O

/-- **The kernel of a simulator**: its run at the proof query's statement. -/
def _root_.GordieHowe.NARG.SimulatorFn.toKernel {C : Type} (S : NARG.SimulatorFn X Y Stmt Proof C) :
    Kernel X Y Stmt Wit Proof C :=
  fun req O c => S.run O req.stmt c

/-- **The game of a kernel is an average over a uniform tape.** -/
theorem toReal_acceptProb_progEnv {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) {C : Type} [Fintype C]
    [Nonempty C] (K : Kernel X Y Stmt Wit Proof C) (Q : ℕ) :
    (A.acceptProb (progEnv rel K Q)).toReal =
      𝔼 ω : (X → Y) × (Fin Q → C), ind (A.accepts (envResponder (progEnv rel K Q) ω) ω.1) := by
  classical
  have hμ : (progEnv rel K Q).μ = PMF.uniformOfFintype ((X → Y) × (Fin Q → C)) :=
    tapeDist_uniformOfFintype
  rw [IAlg.acceptProb, hμ]
  change (GordieHowe.IOP.probUniform ((X → Y) × (Fin Q → C)) fun p =>
    A.accepts (envResponder (progEnv rel K Q) p) p.1 = true).toReal = _
  rw [GordieHowe.IOP.toReal_probUniform]
  rfl

/-- **The simulated game of a simulator is the game of its kernel.** -/
theorem acceptProb_simEnv_eq {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) {C : Type} [Fintype C]
    [Nonempty C] (S : NARG.SimulatorFn X Y Stmt Proof C) (Q : ℕ) :
    A.acceptProb (simEnv rel S Q) = A.acceptProb (progEnv rel (S.toKernel (Wit := Wit)) Q) := by
  have hμ : (simEnv rel S Q).μ = (progEnv rel (S.toKernel (Wit := Wit)) Q).μ := by
    change tapeDist Q S.coins = tapeDist Q (PMF.uniformOfFintype C)
    rw [NARG.SimulatorFn.coins_eq_uniform]
  unfold IAlg.acceptProb
  rw [hμ]
  rfl

/-! ### The hybrid of two kernels -/

section Hybrid

variable {C₁ C₂ : Type} [Fintype C₁] [Nonempty C₁] [Fintype C₂] [Nonempty C₂]
  (K₁ : Kernel X Y Stmt Wit Proof C₁) (K₂ : Kernel X Y Stmt Wit Proof C₂)

/-- **Hybrid `j` of two kernels** at the coins `c₁`, `c₂`: a proof query numbered `i < Q` is answered
by `K₂` with the coins `c₂ i` if `i < j` and by `K₁` with the coins `c₁ i` otherwise. -/
def kHyb {Q : ℕ} (j : ℕ) (c₁ : Fin Q → C₁) (c₂ : Fin Q → C₂) : Responder X Y Stmt Wit Proof :=
  fun i req O => if h : i < Q then
    (if i < j then kernelReply rel K₂ (c₂ ⟨i, h⟩) else kernelReply rel K₁ (c₁ ⟨i, h⟩)) req O
    else ⟨none, O⟩

omit [Fintype X] [Fintype Y] [Nonempty Y] [Fintype C₁] [Nonempty C₁] [Fintype C₂] [Nonempty C₂] in
/-- Hybrids `j` and `j + 1` agree off proof query `j`. -/
theorem kHyb_succ_of_ne {Q i j : ℕ} (c₁ : Fin Q → C₁) (c₂ : Fin Q → C₂) (h : i ≠ j) :
    kHyb rel K₁ K₂ (j + 1) c₁ c₂ i = kHyb rel K₁ K₂ j c₁ c₂ i := by
  funext req O
  unfold kHyb
  split_ifs <;> first | rfl | omega

omit [Fintype X] [Fintype Y] [Nonempty Y] [Fintype C₁] [Nonempty C₁] [Fintype C₂] [Nonempty C₂] in
/-- With proof query `j` overridden, the hybrid does not read proof query `j`'s coins. -/
theorem override_kHyb_update {Q j : ℕ} (hj : j < Q) (j' : ℕ) (c₁ : Fin Q → C₁) (c₂ : Fin Q → C₂)
    (a₁ : C₁) (a₂ : C₂) (g : ReplyFn X Y Stmt Wit Proof) :
    override (kHyb rel K₁ K₂ j' (Function.update c₁ ⟨j, hj⟩ a₁) (Function.update c₂ ⟨j, hj⟩ a₂)) j g =
      override (kHyb rel K₁ K₂ j' c₁ c₂) j g := by
  funext i req O
  by_cases hi : i = j
  · simp only [override, if_pos hi]
  · simp only [override, if_neg hi, kHyb]
    by_cases h1 : i < Q
    · have hne : (⟨i, h1⟩ : Fin Q) ≠ ⟨j, hj⟩ := fun e => hi (congrArg Fin.val e)
      simp only [dif_pos h1, Function.update_of_ne hne]
    · simp only [dif_neg h1]

omit [Fintype X] [Fintype Y] [Nonempty Y] [Fintype C₁] [Nonempty C₁] [Fintype C₂] [Nonempty C₂] in
/-- Hybrid `j` answers proof query `j` with `K₁`. -/
theorem override_kHyb_self {Q j : ℕ} (hj : j < Q) (c₁ : Fin Q → C₁) (c₂ : Fin Q → C₂) :
    override (kHyb rel K₁ K₂ j c₁ c₂) j (kernelReply rel K₁ (c₁ ⟨j, hj⟩)) = kHyb rel K₁ K₂ j c₁ c₂ := by
  funext i req O
  by_cases hi : i = j
  · subst hi
    simp only [override, if_true, kHyb, dif_pos hj, lt_irrefl, if_false]
  · simp only [override, if_neg hi]

omit [Fintype X] [Fintype Y] [Nonempty Y] [Fintype C₁] [Nonempty C₁] [Fintype C₂] [Nonempty C₂] in
/-- Hybrid `j + 1` answers proof query `j` with `K₂`. -/
theorem override_kHyb_succ {Q j : ℕ} (hj : j < Q) (c₁ : Fin Q → C₁) (c₂ : Fin Q → C₂) :
    override (kHyb rel K₁ K₂ j c₁ c₂) j (kernelReply rel K₂ (c₂ ⟨j, hj⟩)) =
      kHyb rel K₁ K₂ (j + 1) c₁ c₂ := by
  funext i req O
  by_cases hi : i = j
  · subst hi
    simp only [override, if_true, kHyb, dif_pos hj, Nat.lt_succ_self, if_true]
  · simp only [override, if_neg hi]
    rw [kHyb_succ_of_ne rel K₁ K₂ c₁ c₂ hi]

/-- **The probability that `A` outputs `true` in hybrid `j` of two kernels**, over a uniform
tape. -/
noncomputable def kHybProb {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) (Q j : ℕ) : ℝ :=
  𝔼 ω : (X → Y) × (Fin Q → C₁) × (Fin Q → C₂), ind (A.accepts (kHyb rel K₁ K₂ j ω.2.1 ω.2.2) ω.1)

omit [Fintype C₂] [Nonempty C₂] in
theorem kHyb_zero {Q : ℕ} (c₁ : Fin Q → C₁) (c₂ : Fin Q → C₂) (ω₀ : X → Y) :
    kHyb rel K₁ K₂ 0 c₁ c₂ = envResponder (progEnv rel K₁ Q) (ω₀, c₁) := by
  funext i req O
  simp only [kHyb, envResponder, progEnv, Nat.not_lt_zero, if_false]

omit [Fintype C₁] [Nonempty C₁] in
theorem kHyb_Q {Q : ℕ} (c₁ : Fin Q → C₁) (c₂ : Fin Q → C₂) (ω₀ : X → Y) :
    kHyb rel K₁ K₂ Q c₁ c₂ = envResponder (progEnv rel K₂ Q) (ω₀, c₂) := by
  funext i req O
  simp only [kHyb, envResponder, progEnv]
  split_ifs <;> rfl

theorem toReal_acceptProb_progEnv_eq_kHybProb_zero {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) (Q : ℕ) :
    (A.acceptProb (progEnv rel K₁ Q)).toReal = kHybProb rel K₁ K₂ A Q 0 := by
  rw [toReal_acceptProb_progEnv, kHybProb]
  let e : (X → Y) × (Fin Q → C₁) × (Fin Q → C₂) ≃ ((X → Y) × (Fin Q → C₁)) × (Fin Q → C₂) :=
    (Equiv.prodAssoc _ _ _).symm
  rw [Fintype.expect_equiv e _ (fun q => ind (A.accepts (envResponder (progEnv rel K₁ Q) q.1) q.1.1))
    fun ω => by simp only [e, Equiv.prodAssoc_symm_apply, kHyb_zero rel K₁ K₂ ω.2.1 ω.2.2 ω.1]]
  exact (expect_prod_fst _).symm

theorem toReal_acceptProb_progEnv_eq_kHybProb_Q {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) (Q : ℕ) :
    (A.acceptProb (progEnv rel K₂ Q)).toReal = kHybProb rel K₁ K₂ A Q Q := by
  rw [toReal_acceptProb_progEnv, kHybProb]
  let e : (X → Y) × (Fin Q → C₁) × (Fin Q → C₂) ≃ ((X → Y) × (Fin Q → C₂)) × (Fin Q → C₁) :=
    { toFun := fun ω => ((ω.1, ω.2.2), ω.2.1)
      invFun := fun q => (q.1.1, q.2, q.1.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.expect_equiv e _ (fun q => ind (A.accepts (envResponder (progEnv rel K₂ Q) q.1) q.1.1))
    fun ω => by simp only [e, Equiv.coe_fn_mk, kHyb_Q rel K₁ K₂ ω.2.1 ω.2.2 ω.1]]
  exact (expect_prod_fst _).symm

variable [Fintype Proof]

/-- **One step of the hybrid of two kernels**: hybrids `j` and `j + 1` differ by at most `ε` when
the two kernels' reply laws are within `ε` at every valid proof query and every oracle. -/
theorem abs_kHybProb_sub_le {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ req O, rel req.stmt req.wit →
      PMF.tvDist ((PMF.uniformOfFintype C₁).map fun c => kernelReply rel K₁ c req O)
        ((PMF.uniformOfFintype C₂).map fun c => kernelReply rel K₂ c req O) ≤ ε)
    {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) {Q j : ℕ} (hj : j < Q) :
    |kHybProb rel K₁ K₂ A Q j - kHybProb rel K₁ K₂ A Q (j + 1)| ≤ ε := by
  classical
  let upd : (X → Y) × (Fin Q → C₁) × (Fin Q → C₂) → C₁ × C₂ → (X → Y) × (Fin Q → C₁) × (Fin Q → C₂) :=
    fun ω a => (ω.1, Function.update ω.2.1 ⟨j, hj⟩ a.1, Function.update ω.2.2 ⟨j, hj⟩ a.2)
  have hlens : ∀ f : (X → Y) × (Fin Q → C₁) × (Fin Q → C₂) → ℝ,
      𝔼 ω, 𝔼 a : C₁ × C₂, f (upd ω a) = 𝔼 ω, f ω := fun f =>
    expect_lens upd (fun ω => (ω.2.1 ⟨j, hj⟩, ω.2.2 ⟨j, hj⟩)) (fun ω a => by simp [upd])
      (fun ω => by simp [upd]) (fun ω a b => by simp [upd]) f
  set R := fun ω : (X → Y) × (Fin Q → C₁) × (Fin Q → C₂) => kHyb rel K₁ K₂ j ω.2.1 ω.2.2
  have hj0 : ∀ ω a, ind (A.accepts (kHyb rel K₁ K₂ j (upd ω a).2.1 (upd ω a).2.2) (upd ω a).1) =
      ind (A.accepts (override (R ω) j (kernelReply rel K₁ a.1)) ω.1) := fun ω a => by
    rw [← override_kHyb_self rel K₁ K₂ hj]
    simp only [upd, R, Function.update_self]
    rw [override_kHyb_update rel K₁ K₂ hj j ω.2.1 ω.2.2]
  have hj1 : ∀ ω a, ind (A.accepts (kHyb rel K₁ K₂ (j + 1) (upd ω a).2.1 (upd ω a).2.2) (upd ω a).1) =
      ind (A.accepts (override (R ω) j (kernelReply rel K₂ a.2)) ω.1) := fun ω a => by
    rw [← override_kHyb_succ rel K₁ K₂ hj]
    simp only [upd, R, Function.update_self]
    rw [override_kHyb_update rel K₁ K₂ hj j ω.2.1 ω.2.2]
  rw [kHybProb, kHybProb, ← hlens, ← hlens (fun ω => ind (A.accepts (kHyb rel K₁ K₂ (j + 1) ω.2.1 ω.2.2) ω.1))]
  simp_rw [hj0, hj1]
  rw [← Finset.expect_sub_distrib]
  refine (Finset.abs_expect_le _ _).trans ?_
  refine (Finset.expect_le_expect fun ω _ => ?_).trans_eq (Finset.expect_const Finset.univ_nonempty ε)
  rw [← Finset.expect_sub_distrib]
  have hfst : 𝔼 a : C₁ × C₂, ind (A.accepts (override (R ω) j (kernelReply rel K₁ a.1)) ω.1) =
      𝔼 u : C₁, ind (A.accepts (override (R ω) j (kernelReply rel K₁ u)) ω.1) :=
    expect_prod_fst (fun u => ind (A.accepts (override (R ω) j (kernelReply rel K₁ u)) ω.1))
  have hsnd : 𝔼 a : C₁ × C₂, ind (A.accepts (override (R ω) j (kernelReply rel K₂ a.2)) ω.1) =
      𝔼 v : C₂, ind (A.accepts (override (R ω) j (kernelReply rel K₂ v)) ω.1) :=
    expect_prod_snd (fun v => ind (A.accepts (override (R ω) j (kernelReply rel K₂ v)) ω.1))
  rw [Finset.expect_sub_distrib, hfst, hsnd]
  refine A.abs_expect_accepts_override_sub_le (R ω) ω.1 j refuseReply (kernelReply rel K₁)
    (kernelReply rel K₂) hε fun k _ req _ _ => ?_
  by_cases hr : rel req.stmt req.wit
  · exact h req _ hr
  · have e1 : (fun c : C₁ => kernelReply rel K₁ c req (A.run (override (R ω) j refuseReply) ω.1 k).oracle) =
        fun _ => ⟨none, (A.run (override (R ω) j refuseReply) ω.1 k).oracle⟩ :=
      funext fun c => by simp only [kernelReply, if_neg hr]
    have e2 : (fun c : C₂ => kernelReply rel K₂ c req (A.run (override (R ω) j refuseReply) ω.1 k).oracle) =
        fun _ => ⟨none, (A.run (override (R ω) j refuseReply) ω.1 k).oracle⟩ :=
      funext fun c => by simp only [kernelReply, if_neg hr]
    rw [e1, e2]
    rw [show (fun _ : C₁ => (⟨none, (A.run (override (R ω) j refuseReply) ω.1 k).oracle⟩ :
        EnvReply Proof (X → Y))) = Function.const C₁ ⟨none, (A.run (override (R ω) j refuseReply) ω.1 k).oracle⟩
        from rfl,
      show (fun _ : C₂ => (⟨none, (A.run (override (R ω) j refuseReply) ω.1 k).oracle⟩ :
        EnvReply Proof (X → Y))) = Function.const C₂ ⟨none, (A.run (override (R ω) j refuseReply) ω.1 k).oracle⟩
        from rfl, PMF.map_const, PMF.map_const, PMF.tvDist_self]
    exact hε

/-- The sum of `Q` equal step errors. -/
theorem abs_kHybProb_zero_sub_le {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ req O, rel req.stmt req.wit →
      PMF.tvDist ((PMF.uniformOfFintype C₁).map fun c => kernelReply rel K₁ c req O)
        ((PMF.uniformOfFintype C₂).map fun c => kernelReply rel K₂ c req O) ≤ ε)
    {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) (Q : ℕ) :
    |kHybProb rel K₁ K₂ A Q 0 - kHybProb rel K₁ K₂ A Q Q| ≤ Q * ε := by
  rw [← Finset.sum_range_sub' (fun j => kHybProb rel K₁ K₂ A Q j)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun j hj => abs_kHybProb_sub_le rel K₁ K₂ hε h A
    (Finset.mem_range.1 hj)).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Two kernels whose replies are close give close games**: if at every valid proof query and every
oracle in force the reply laws of `K₁` and `K₂` over their uniform coins are within `ε` in total
variation, then every classical algorithm, unbounded after its steps, outputs `true` against
their environments for `Q` proof queries with probabilities at most `Q ε` apart. -/
theorem abs_toReal_acceptProb_progEnv_sub_le {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ req O, rel req.stmt req.wit →
      PMF.tvDist ((PMF.uniformOfFintype C₁).map fun c => kernelReply rel K₁ c req O)
        ((PMF.uniformOfFintype C₂).map fun c => kernelReply rel K₂ c req O) ≤ ε)
    {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) (Q : ℕ) :
    |(A.acceptProb (progEnv rel K₁ Q)).toReal - (A.acceptProb (progEnv rel K₂ Q)).toReal| ≤ Q * ε := by
  rw [toReal_acceptProb_progEnv_eq_kHybProb_zero rel K₁ K₂ A Q,
    toReal_acceptProb_progEnv_eq_kHybProb_Q rel K₁ K₂ A Q]
  exact abs_kHybProb_zero_sub_le rel K₁ K₂ hε h A Q

end Hybrid

/-! ### Kernels as simulators of the proof queries -/

section Lift

/-- A proof query as a statement of the game whose statements are the proof queries. -/
def Action.liftReq : Action X Stmt Wit → Action X (ProofQuery Stmt Wit) Unit
  | .query x => .query x
  | .request r => .request ⟨r, ()⟩

/-- **The algorithm on the game whose statements are the proof queries**: each proof query `r` is made as the
proof query `⟨r, ()⟩`; queries and the output are unchanged. -/
def IAlg.liftReq {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) : IAlg X Y (ProofQuery Stmt Wit) Unit Proof m where
  next hist := (A.next hist).liftReq
  post := A.post

/-- **The run of the lifted algorithm is the run of the algorithm** against a responder that
answers `⟨r, ()⟩` as the original answers `r`. -/
theorem IAlg.run_liftReq {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) {R : Responder X Y Stmt Wit Proof}
    {R' : Responder X Y (ProofQuery Stmt Wit) Unit Proof} (hR : ∀ i r, R' i ⟨r, ()⟩ = R i r)
    (O : X → Y) : ∀ k, A.liftReq.run R' O k = A.run R O k
  | 0 => rfl
  | k + 1 => by
    rw [IAlg.run_succ, IAlg.run_succ, IAlg.run_liftReq A hR O k]
    cases hn : A.next (A.run R O k).hist with
    | query x =>
      have hn' : A.liftReq.next (A.run R O k).hist = .query x := by
        simp only [IAlg.liftReq, hn, Action.liftReq]
      rw [IAlg.step_of_query hn, IAlg.step_of_query hn']
    | request r =>
      have hn' : A.liftReq.next (A.run R O k).hist = .request ⟨r, ()⟩ := by
        simp only [IAlg.liftReq, hn, Action.liftReq]
      rw [IAlg.step_of_request hn, IAlg.step_of_request hn', hR]

theorem IAlg.queryCount_liftReq {m : ℕ} (A : IAlg X Y Stmt Wit Proof m)
    {R : Responder X Y Stmt Wit Proof} {R' : Responder X Y (ProofQuery Stmt Wit) Unit Proof}
    (hR : ∀ i r, R' i ⟨r, ()⟩ = R i r) (O : X → Y) :
    A.liftReq.queryCount R' O = A.queryCount R O := by
  unfold IAlg.queryCount
  congr 1
  refine Finset.filter_congr fun k _ => ?_
  rw [A.run_liftReq hR O k]
  change (A.next (A.run R O k).hist).liftReq.IsQuery ↔ _
  cases A.next (A.run R O k).hist <;> rfl

/-- **The prover on the game whose statements are the proof queries**: on `⟨r, ()⟩` it proves `r`. -/
def _root_.GordieHowe.NARG.ProverFn.liftReq {Coins : Type} (P : NARG.ProverFn X Y Stmt Wit Proof Coins) :
    NARG.ProverFn X Y (ProofQuery Stmt Wit) Unit Proof Coins where
  prove H r _ c := P.prove H r.stmt r.wit c
  coins := P.coins

/-- **A kernel as a simulator of the proof queries**: on the statement `r` it runs the kernel on `r`.

Running time: one run of the kernel; the oracle points read, the assignment list and the coins
are the kernel's. This running time is argued here, not proved in Lean. -/
def Kernel.toSimulator {C : Type} [Nonempty C] (K : Kernel X Y Stmt Wit Proof C) :
    NARG.SimulatorFn X Y (ProofQuery Stmt Wit) Proof C where
  run O r c := K r O c
  coins_nonempty := inferInstance

/-- The relation on the proof queries: `⟨r, ()⟩` is valid when `r` is. -/
def liftRel : ProofQuery Stmt Wit → Unit → Prop := fun r _ => rel r.stmt r.wit

instance : DecidableRel (liftRel rel (Stmt := Stmt) (Wit := Wit)) := fun r _ =>
  inferInstanceAs (Decidable (rel r.stmt r.wit))

/-- The lifted algorithm in the real game of the lifted prover is the algorithm in the real game. -/
theorem acceptProb_liftReq_realEnv {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) {Coins : Type}
    [Fintype Coins] (P : NARG.ProverFn X Y Stmt Wit Proof Coins) (Q : ℕ) :
    A.liftReq.acceptProb (realEnv (liftRel rel) P.liftReq Q) = A.acceptProb (realEnv rel P Q) := by
  have h : ∀ ω : (X → Y) × (Fin Q → Coins),
      A.liftReq.accepts (envResponder (realEnv (liftRel rel) P.liftReq Q) ω) ω.1 =
        A.accepts (envResponder (realEnv rel P Q) ω) ω.1 := fun ω => by
    rw [IAlg.accepts, IAlg.accepts, A.run_liftReq (R := envResponder (realEnv rel P Q) ω)
      (fun i r => rfl)]
    rfl
  unfold IAlg.acceptProb
  have hμ : (realEnv (liftRel rel) P.liftReq Q).μ = (realEnv rel P Q).μ := rfl
  rw [hμ]
  congr 1
  ext ω
  change A.liftReq.accepts _ ω.1 = true ↔ A.accepts _ ω.1 = true
  rw [h ω]

/-- The lifted algorithm in the simulated game of a kernel's simulator is the algorithm in the
kernel's game. -/
theorem acceptProb_liftReq_simEnv {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) {C : Type} [Fintype C]
    [Nonempty C] (K : Kernel X Y Stmt Wit Proof C) (Q : ℕ) :
    A.liftReq.acceptProb (simEnv (liftRel rel) K.toSimulator Q) = A.acceptProb (progEnv rel K Q) := by
  have hμ : (simEnv (liftRel rel) K.toSimulator Q).μ = (progEnv rel K Q).μ := by
    change tapeDist Q K.toSimulator.coins = tapeDist Q (PMF.uniformOfFintype C)
    rw [NARG.SimulatorFn.coins_eq_uniform]
  have h : ∀ ω : (X → Y) × (Fin Q → C),
      A.liftReq.accepts (envResponder (simEnv (liftRel rel) K.toSimulator Q) ω) ω.1 =
        A.accepts (envResponder (progEnv rel K Q) ω) ω.1 := fun ω => by
    rw [IAlg.accepts, IAlg.accepts, A.run_liftReq (R := envResponder (progEnv rel K Q) ω)
      (fun i r => rfl)]
    rfl
  unfold IAlg.acceptProb
  rw [hμ]
  congr 1
  ext ω
  change A.liftReq.accepts _ ω.1 = true ↔ A.accepts _ ω.1 = true
  rw [h ω]

/-- **The lifted adversary**: the lifted algorithm at each value of the coins, with the same
budget. -/
def Adversary.liftReq {m t : ℕ} (𝒜 : Adversary X Y Stmt Wit Proof m t) :
    Adversary X Y (ProofQuery Stmt Wit) Unit Proof m t where
  Coins := 𝒜.Coins
  coins := 𝒜.coins
  alg r := (𝒜.alg r).liftReq
  budget r R' O := by
    rw [(𝒜.alg r).queryCount_liftReq (R := fun i r O => R' i ⟨r, ()⟩ O) (fun i r => rfl) O]
    exact 𝒜.budget r _ O

/-- **Zero knowledge of a prover against a kernel's simulator on the proof queries gives the bound
between the prover's real game and the kernel's game**, for every classical adversary. -/
theorem abs_acceptProb_realEnv_sub_progEnv_le {Coins C : Type} [Fintype Coins] [Fintype C]
    [Nonempty C] {P : NARG.ProverFn X Y Stmt Wit Proof Coins} {K : Kernel X Y Stmt Wit Proof C}
    {ε : ℕ → ℕ → ℝ} (h : ZeroKnowledge (liftRel rel) P.liftReq K.toSimulator ε) {m t : ℕ}
    (𝒜 : Adversary X Y Stmt Wit Proof m t) (Q : ℕ) :
    GordieHowe.advantage (𝒜.acceptProb (realEnv rel P Q)) (𝒜.acceptProb (progEnv rel K Q)) ≤ ε t Q := by
  have := h m t Q 𝒜.liftReq
  have e1 : 𝒜.liftReq.acceptProb (realEnv (liftRel rel) P.liftReq Q) =
      𝒜.acceptProb (realEnv rel P Q) := by
    simp only [Adversary.acceptProb, Adversary.liftReq, acceptProb_liftReq_realEnv]
    rfl
  have e2 : 𝒜.liftReq.acceptProb (simEnv (liftRel rel) K.toSimulator Q) =
      𝒜.acceptProb (progEnv rel K Q) := by
    simp only [Adversary.acceptProb, Adversary.liftReq, acceptProb_liftReq_simEnv]
    rfl
  rw [Adversary.advantage, e1, e2] at this
  exact this

end Lift

end GordieHowe.ROM.NIZK
