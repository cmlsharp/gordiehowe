-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.HiddenLeaves
public import GordieHowe.Model.Quantum.Pure.MapReq
public import GordieHowe.Model.Quantum.Interactive.QueryBoundedZK

@[expose] public section

/-!
# Query-counted zero knowledge with hidden leaf digests against quantum distinguishers

The quantum counterpart of `GordieHowe/Model/ROM/LeafZK.lean`: zero knowledge against distinguishers with a
budget of `q` query slots and no final unitary (`GordieHowe.QROM.ZeroKnowledgeQueryBoundedPure`, every query
counted), from a leaf kernel (`GordieHowe.QROM.zeroKnowledgeQueryBoundedPure_of_leafKernel`). The real game of
a prover `P` and the simulated game of a simulator `S` are compared through three intermediate
games:

1. the game of a kernel `K₁` that is the honest-digest kernel `L.kL` of a leaf kernel up to a
   bijection of the coins (`acceptProb_progEnv_equiv`), at the error `ε₁` of zero knowledge of `P`
   against `K₁` read as a simulator of the proof queries (`Kernel.toSimulator`): a distinguisher of the
   real game and the kernel's game is a distinguisher of the game whose statements are the
   proof queries, with its proof queries relabelled (`Distinguisher.mapReq`,
   `abs_acceptProb_realEnv_sub_progEnv_le`);
2. the game of the uniform-digest kernel `L.kD`, at
   `Q (4 t √(|Pos|/|N|) + 3 (|pub| |Pos| + Q |Pos|² + |Pos|²)/|N|)`
   (`abs_acceptProb_progEnv_kL_sub_kD_le`, `GordieHowe/Model/QROM/HiddenLeaves.lean`);
3. the simulated game of `S`, at `Q ε₃` when the replies of `L.kD` and of `S` are within `ε₃` in
   total variation at every valid proof query and oracle (`abs_acceptProb_progEnv_sub_le`, a hybrid
   over the proof queries whose steps are the kernel replacement
   `Distinguisher.abs_acceptProbOn_sub_le_of_kernel`).

The pure notion gives the notion over the paper's query-bounded adversaries by
`ZeroKnowledgeQueryBoundedPure.zeroKnowledgeQueryBounded` (`GordieHowe/Model/Quantum/Interactive/QueryBoundedZK.lean`).
-/

open Finset
open scoped BigOperators

namespace GordieHowe

namespace QROM

open GordieHowe.ROM.NIZK

variable {X Y Stmt Wit Proof : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  (rel : Stmt → Wit → Prop) [DecidableRel rel]

/-! ### Proof queries as statements -/

/-- A proof query as the proof query `⟨r, ()⟩` of the game whose statements are the proof queries. -/
def liftReqEquiv : ProofQuery Stmt Wit ≃ ProofQuery (ProofQuery Stmt Wit) Unit where
  toFun r := ⟨r, ()⟩
  invFun r := r.stmt
  left_inv _ := rfl
  right_inv _ := rfl

/-- The real game of the lifted prover, read on the proof queries, is the real game. -/
theorem realEnv_liftReq_comapReq {Coins : Type} [Fintype Coins] (P : NARG.ProverFn X Y Stmt Wit Proof Coins)
    (Q : ℕ) : (realEnv (liftRel rel) P.liftReq Q).comapReq liftReqEquiv = realEnv rel P Q :=
  rfl

variable [AddGroup Y] [Fintype Stmt] [DecidableEq Stmt] [Fintype Wit] [DecidableEq Wit]
  [Fintype Proof] [DecidableEq Proof] {W : Type} [Fintype W] {n m : ℕ}
  (D : Quantum.Distinguisher W X Y (ProofQuery Stmt Wit) Proof n m)
  (post : (X → Y) → Quantum.QState (Quantum.DReg W n X Y (ProofQuery Stmt Wit) Proof) ≃ₗᵢ[ℂ]
    Quantum.QState (Quantum.DReg W n X Y (ProofQuery Stmt Wit) Proof))

/-- The simulated game of a kernel's simulator, read on the proof queries, is the kernel's game. -/
theorem acceptProb_simEnv_liftReq_comapReq {C : Type} [Fintype C] [Nonempty C]
    (K : Kernel X Y Stmt Wit Proof C) (Q : ℕ) :
    D.acceptProb ((simEnv (liftRel rel) K.toSimulator Q).comapReq liftReqEquiv) post =
      D.acceptProb (progEnv rel K Q) post :=
  D.acceptProb_comap post id (by rw [PMF.map_id]; rfl) (fun _ => rfl) fun _ => rfl

/-- **The simulated game of a simulator is the game of its kernel.** -/
theorem acceptProb_simEnv_eq {C : Type} [Fintype C] [Nonempty C] (S : NARG.SimulatorFn X Y Stmt Proof C)
    (Q : ℕ) :
    D.acceptProb (simEnv rel S Q) post = D.acceptProb (progEnv rel (S.toKernel (Wit := Wit)) Q) post :=
  D.acceptProb_comap post id (by rw [PMF.map_id]; rfl) (fun _ => rfl) fun _ => rfl

/-- **Kernels that agree up to a bijection of their coins give the same game.** -/
theorem acceptProb_progEnv_equiv {C C' : Type} [Fintype C] [Nonempty C] [Fintype C'] [Nonempty C']
    (e : C' ≃ C) (K : Kernel X Y Stmt Wit Proof C) (K' : Kernel X Y Stmt Wit Proof C')
    (hK : ∀ req O c, K' req O c = K req O (e c)) (Q : ℕ) :
    D.acceptProb (progEnv rel K' Q) post = D.acceptProb (progEnv rel K Q) post := by
  let f : (X → Y) × (Fin Q → C') ≃ (X → Y) × (Fin Q → C) :=
    Equiv.prodCongr (Equiv.refl _) (Equiv.arrowCongr (Equiv.refl _) e)
  refine D.acceptProb_comap post f ?_ (fun _ => rfl) fun ω => ?_
  · change tapeDist Q _ = (tapeDist Q _).map f
    rw [tapeDist_uniformOfFintype, tapeDist_uniformOfFintype, PMF.map_uniformOfFintype_equiv]
  · funext i req O
    simp only [progEnv, kernelReply, f, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map, id,
      Equiv.arrowCongr_apply, Function.comp_apply, Equiv.refl_symm, hK]

/-- **Stage 1: zero knowledge of a prover against a kernel's simulator on the proof queries gives the
bound between the prover's real game and the kernel's game**, for every distinguisher with a budget
of `q` query slots with `n * q ≤ t` and every final unitary. -/
theorem abs_acceptProb_realEnv_sub_progEnv_le {Coins C : Type} [Fintype Coins] [Fintype C]
    [Nonempty C] {P : NARG.ProverFn X Y Stmt Wit Proof Coins} {K : Kernel X Y Stmt Wit Proof C}
    {ε : ℕ → ℕ → ℝ} (h : ZeroKnowledgeAfterAdaptive (liftRel rel) P.liftReq K.toSimulator ε)
    {t Q q : ℕ} (bud : D.Budget q) (hD : n * q ≤ t) :
    |D.acceptProb (realEnv rel P Q) post - D.acceptProb (progEnv rel K Q) post| ≤ ε t Q := by
  have h' := h t W n m Q q (D.mapReq liftReqEquiv) (Quantum.Distinguisher.mapPost liftReqEquiv post)
    (bud.mapReq liftReqEquiv) hD
  rw [QROM.advantage, GordieHowe.advantage, Quantum.Distinguisher.acceptProb_mapReq,
    Quantum.Distinguisher.acceptProb_mapReq, realEnv_liftReq_comapReq,
    acceptProb_simEnv_liftReq_comapReq] at h'
  exact h'

/-! ### The hybrid of two kernels -/

section Hybrid

variable {C₁ C₂ : Type} [Fintype C₁] [Nonempty C₁] [Fintype C₂] [Nonempty C₂]
  (K₁ : Kernel X Y Stmt Wit Proof C₁) (K₂ : Kernel X Y Stmt Wit Proof C₂)

/-- **Hybrid `j` of two kernels** on a uniform tape holding the initial oracle and both coins of
every proof query: a proof query numbered `i < j` is answered by `K₂` with its second coins, the others by
`K₁` with its first coins. -/
noncomputable def kHybEnv (Q j : ℕ) :
    Quantum.Env ((X → Y) × (Fin Q → C₁ × C₂)) (ProofQuery Stmt Wit) Proof X Y Q where
  μ := PMF.uniformOfFintype _
  oracle₀ ω := ω.1
  respond ω i := if (i : ℕ) < j then kernelReply rel K₂ (ω.2 i).2 else kernelReply rel K₁ (ω.2 i).1

/-- The hybrid tape as the tape of `K₁`'s game and the coins of `K₂`. -/
def kHybEquiv₁ (Q : ℕ) :
    (X → Y) × (Fin Q → C₁ × C₂) ≃ ((X → Y) × (Fin Q → C₁)) × (Fin Q → C₂) where
  toFun ω := ((ω.1, fun i => (ω.2 i).1), fun i => (ω.2 i).2)
  invFun p := (p.1.1, fun i => (p.1.2 i, p.2 i))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The hybrid tape as the tape of `K₂`'s game and the coins of `K₁`. -/
def kHybEquiv₂ (Q : ℕ) :
    (X → Y) × (Fin Q → C₁ × C₂) ≃ ((X → Y) × (Fin Q → C₂)) × (Fin Q → C₁) where
  toFun ω := ((ω.1, fun i => (ω.2 i).2), fun i => (ω.2 i).1)
  invFun p := (p.1.1, fun i => (p.2 i, p.1.2 i))
  left_inv _ := rfl
  right_inv _ := rfl

theorem acceptProb_progEnv_eq_kHyb_zero (Q : ℕ) :
    D.acceptProb (progEnv rel K₁ Q) post = D.acceptProb (kHybEnv rel K₁ K₂ Q 0) post := by
  refine (D.acceptProb_comap post (fun ω => (kHybEquiv₁ Q ω).1) ?_ (fun _ => rfl) fun ω => ?_).symm
  · change tapeDist Q _ = (PMF.uniformOfFintype _).map _
    rw [tapeDist_uniformOfFintype, ← PMF.map_fst_uniformOfFintype (β := Fin Q → C₂),
      ← PMF.map_uniformOfFintype_equiv (kHybEquiv₁ Q), PMF.map_comp]
    rfl
  · funext i
    simp only [kHybEnv, Nat.not_lt_zero, ↓reduceIte]
    rfl

theorem acceptProb_progEnv_eq_kHyb_Q (Q : ℕ) :
    D.acceptProb (progEnv rel K₂ Q) post = D.acceptProb (kHybEnv rel K₁ K₂ Q Q) post := by
  refine (D.acceptProb_comap post (fun ω => (kHybEquiv₂ Q ω).1) ?_ (fun _ => rfl) fun ω => ?_).symm
  · change tapeDist Q _ = (PMF.uniformOfFintype _).map _
    rw [tapeDist_uniformOfFintype, ← PMF.map_fst_uniformOfFintype (β := Fin Q → C₁),
      ← PMF.map_uniformOfFintype_equiv (kHybEquiv₂ Q), PMF.map_comp]
    rfl
  · funext i
    simp only [kHybEnv, i.2, ↓reduceIte]
    rfl

/-- The hybrid tape with the coins of proof query `j` set apart. -/
def kHybSplit {Q : ℕ} (j : Fin Q) :
    (X → Y) × (Fin Q → C₁ × C₂) ≃ ((X → Y) × ({i : Fin Q // i ≠ j} → C₁ × C₂)) × (C₁ × C₂) where
  toFun ω := ((ω.1, fun i => ω.2 i), ω.2 j)
  invFun p := (p.1.1, fun i => if h : i = j then p.2 else p.1.2 ⟨i, h⟩)
  left_inv ω := by
    refine Prod.ext rfl (funext fun i => ?_)
    by_cases h : i = j
    · subst h
      simp
    · simp [h]
  right_inv p := by
    refine Prod.ext (Prod.ext rfl (funext fun i => ?_)) ?_
    · simp [i.2]
    · simp

/-- **One step of the hybrid of two kernels**: hybrids `j` and `j + 1` differ by at most `ε` when
the two kernels' reply laws are within `ε` at every valid proof query and every oracle. -/
theorem abs_acceptProb_kHyb_succ_le {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ req O, rel req.stmt req.wit →
      PMF.tvDist ((PMF.uniformOfFintype C₁).map fun c => kernelReply rel K₁ c req O)
        ((PMF.uniformOfFintype C₂).map fun c => kernelReply rel K₂ c req O) ≤ ε)
    {Q : ℕ} (j : Fin Q) :
    |D.acceptProb (kHybEnv rel K₁ K₂ Q j) post - D.acceptProb (kHybEnv rel K₁ K₂ Q (j + 1)) post| ≤
      ε := by
  classical
  rw [← D.acceptProb_reindex post (kHybEnv rel K₁ K₂ Q j) (kHybSplit j),
    ← D.acceptProb_reindex post (kHybEnv rel K₁ K₂ Q (j + 1)) (kHybSplit j),
    ← Quantum.Distinguisher.acceptProbOn_univ, ← Quantum.Distinguisher.acceptProbOn_univ]
  have hμ : ∀ (E : Quantum.Env ((X → Y) × (Fin Q → C₁ × C₂)) (ProofQuery Stmt Wit) Proof X Y Q),
      E.μ = PMF.uniformOfFintype _ → ∀ v τ, (E.reindex (kHybSplit j)).μ (v, τ) =
        PMF.uniformOfFintype _ v * PMF.uniformOfFintype (C₁ × C₂) τ := fun E hE v τ => by
    simp only [Quantum.Env.reindex, hE, PMF.map_uniformOfFintype_equiv]
    exact Quantum.PMF.uniformOfFintype_prod_apply v τ
  have hsum : ∑ v, (PMF.uniformOfFintype ((X → Y) × ({i : Fin Q // i ≠ j} → C₁ × C₂)) v).toReal * ε =
      ε := by
    rw [← Finset.sum_mul, PMF.sum_toReal, one_mul]
  refine (D.abs_acceptProbOn_sub_le_of_kernel post _ _ (hμ _ rfl) (hμ _ rfl) j
    (fun _ _ _ => rfl) (fun v τ τ' i hi => ?_) (fun _ => ε) (fun _ => hε)
    (fun v τ₀ req rs _ => ?_) Set.univ).trans_eq hsum
  · have hne : (i : ℕ) ≠ j := fun e => hi (Fin.ext e)
    have hc : ∀ τ'' : C₁ × C₂, ((kHybSplit j).symm (v, τ'')).2 i = v.2 ⟨i, hi⟩ := fun τ'' => by
      simp [kHybSplit, hi]
    simp only [Quantum.Env.reindex, kHybEnv, hc]
    by_cases hlt : (i : ℕ) < j
    · have hlt' : (i : ℕ) < j + 1 := by omega
      simp only [hlt, hlt', ↓reduceIte]
    · have hlt' : ¬ (i : ℕ) < j + 1 := by omega
      simp only [hlt, hlt', ↓reduceIte]
  · have hc : ∀ τ : C₁ × C₂, ((kHybSplit j).symm (v, τ)).2 j = τ := fun τ => by simp [kHybSplit]
    set O := ((kHybEnv rel K₁ K₂ Q j).reindex (kHybSplit j)).oracleIn (v, τ₀) rs
    simp only [Quantum.Env.reindex, kHybEnv, hc, lt_irrefl, Nat.lt_succ_self, ↓reduceIte]
    have m1 : (PMF.uniformOfFintype (C₁ × C₂)).map (fun τ => kernelReply rel K₁ τ.1 req O) =
        (PMF.uniformOfFintype C₁).map fun c => kernelReply rel K₁ c req O := by
      conv_rhs => rw [← PMF.map_fst_uniformOfFintype (α := C₁) (β := C₂), PMF.map_comp]
      rfl
    have m2 : (PMF.uniformOfFintype (C₁ × C₂)).map (fun τ => kernelReply rel K₂ τ.2 req O) =
        (PMF.uniformOfFintype C₂).map fun c => kernelReply rel K₂ c req O := by
      conv_rhs => rw [← PMF.map_snd_uniformOfFintype (α := C₁) (β := C₂), PMF.map_comp]
      rfl
    rw [m1, m2]
    by_cases hr : rel req.stmt req.wit
    · exact h req O hr
    · have e1 : (fun c => kernelReply rel K₁ c req O) = Function.const C₁ ⟨none, O⟩ :=
        funext fun c => by simp [kernelReply, hr]
      have e2 : (fun c => kernelReply rel K₂ c req O) = Function.const C₂ ⟨none, O⟩ :=
        funext fun c => by simp [kernelReply, hr]
      rw [e1, e2, PMF.map_const, PMF.map_const, PMF.tvDist_self]
      exact hε

/-- **Two kernels whose replies are close give close games against quantum distinguishers**: if at
every valid proof query and every oracle in force the reply laws of `K₁` and `K₂` over their uniform
coins are within `ε` in total variation, then every distinguisher, with any final unitary,
outputs `1` against their environments for `Q` proof queries with probabilities at most `Q ε` apart. -/
theorem abs_acceptProb_progEnv_sub_le {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ req O, rel req.stmt req.wit →
      PMF.tvDist ((PMF.uniformOfFintype C₁).map fun c => kernelReply rel K₁ c req O)
        ((PMF.uniformOfFintype C₂).map fun c => kernelReply rel K₂ c req O) ≤ ε) (Q : ℕ) :
    |D.acceptProb (progEnv rel K₁ Q) post - D.acceptProb (progEnv rel K₂ Q) post| ≤ Q * ε := by
  rw [acceptProb_progEnv_eq_kHyb_zero rel D post K₁ K₂, acceptProb_progEnv_eq_kHyb_Q rel D post K₁ K₂]
  set a : ℕ → ℝ := fun j => D.acceptProb (kHybEnv rel K₁ K₂ Q j) post
  have : ∀ k ≤ Q, |a 0 - a k| ≤ k * ε := fun k => by
    induction k with
    | zero => intro; simp
    | succ k ih =>
      intro hk
      have h1 := abs_sub_le (a 0) (a k) (a (k + 1))
      have h2 := ih (by omega)
      have h3 := abs_acceptProb_kHyb_succ_le rel D post K₁ K₂ hε h (⟨k, by omega⟩ : Fin Q)
      change |a k - a (k + 1)| ≤ ε at h3
      push_cast
      linarith
  exact this Q le_rfl

end Hybrid

/-! ### The composite -/

/-- A budget of `q` query slots of `n` parallel queries with `n * q ≤ t` charges `q √n ≤ t`. -/
theorem mul_sqrt_le_of_mul_le {n q t : ℕ} (hD : n * q ≤ t) : (q : ℝ) * √n ≤ t := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · have h1 : √(n : ℝ) ≤ n := Real.sqrt_le_iff.2 ⟨by positivity, by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith⟩
    calc (q : ℝ) * √n ≤ q * n := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (n * q : ℕ) := by push_cast; ring
      _ ≤ t := by exact_mod_cast hD

variable {rel}

/-- **Query-counted zero knowledge from a leaf kernel against quantum distinguishers** (module
docstring). For a prover `P`, a simulator `S` and a leaf kernel `L` with its laws for the salt slot
`nsalt` and the public salts `pub` (`hL`), let `K₁` be `L.kL` up to the bijection `e` of the coins
(`hK₁`), let `P` be zero knowledge against `K₁` on the proof queries at the error `ε₁` (`h₁`), and let
the replies of `L.kD` and of `S` be within `ε₃` in total variation at every valid proof query and
oracle (`h₃`). Then every distinguisher with a budget of `q` query slots of `n` parallel queries,
`n * q ≤ t`, and no final unitary has advantage at most

    ε₁ t Q + Q (4 t √(|Pos|/|N|) + 3 (|pub| |Pos| + Q |Pos|² + |Pos|²)/|N|) + Q ε₃

between `P` and `S` with `Q` proof queries answered. -/
theorem zeroKnowledgeQueryBoundedPure_of_leafKernel {Coins SimCoins : Type} [Fintype Coins]
    [Fintype SimCoins] [Nonempty SimCoins] {P : NARG.ProverFn X Y Stmt Wit Proof Coins}
    {S : NARG.SimulatorFn X Y Stmt Proof SimCoins} {Cm Pos N : Type} [Fintype Cm]
    [Nonempty Cm] [Fintype Pos] [DecidableEq Pos] [Fintype N] [DecidableEq N] [Nonempty N]
    {L : LeafKernel X Y Stmt Wit Proof Cm Pos N} {nsalt : X → Option N} {pub : Finset N}
    (hL : L.Laws nsalt pub) {C₁ : Type} [Fintype C₁] [Nonempty C₁]
    {K₁ : Kernel X Y Stmt Wit Proof C₁} (e : C₁ ≃ LeafCoins Cm Pos N Y)
    (hK₁ : ∀ req O c, K₁ req O c = L.kL req O (e c)) {ε₁ : ℕ → ℕ → ℝ}
    (h₁ : ZeroKnowledgeAfterAdaptive (liftRel rel) P.liftReq K₁.toSimulator ε₁)
    {ε₃ : ℝ} (hε₃ : 0 ≤ ε₃)
    (h₃ : ∀ req O, rel req.stmt req.wit →
      PMF.tvDist ((PMF.uniformOfFintype (LeafCoins Cm Pos N Y)).map fun c => kernelReply rel L.kD c req O)
        ((PMF.uniformOfFintype SimCoins).map fun c => kernelReply rel (S.toKernel (Wit := Wit)) c req O) ≤
        ε₃) :
    ZeroKnowledgeQueryBoundedPure rel P S fun t Q =>
      ε₁ t Q + Q * (4 * t * √(Fintype.card Pos / Fintype.card N) +
        3 * ((pub.card * Fintype.card Pos + Q * Fintype.card Pos ^ 2 + Fintype.card Pos ^ 2) /
          Fintype.card N)) + Q * ε₃ := by
  intro t W _ n m Q q D bud hD
  have h1 := abs_acceptProb_realEnv_sub_progEnv_le rel D Quantum.noPost h₁ (Q := Q) bud hD
  rw [acceptProb_progEnv_equiv rel D Quantum.noPost e L.kL K₁ hK₁ Q] at h1
  have h2 := abs_acceptProb_progEnv_kL_sub_kD_le (Q := Q) rel L nsalt pub D hL bud
  have h3 := abs_acceptProb_progEnv_sub_le rel D Quantum.noPost L.kD (S.toKernel (Wit := Wit)) hε₃ h₃ Q
  have hq : 4 * (q : ℝ) * √(n * (Fintype.card Pos / Fintype.card N)) ≤
      4 * t * √(Fintype.card Pos / Fintype.card N) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg n), ← mul_assoc, mul_assoc 4 (q : ℝ)]
    have := mul_sqrt_le_of_mul_le hD
    gcongr
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hq' := mul_le_mul_of_nonneg_left hq hQ
  rw [QROM.advantage, GordieHowe.advantage, acceptProb_simEnv_eq rel D Quantum.noPost S Q]
  have t1 := abs_sub_le (D.acceptProb (realEnv rel P Q) Quantum.noPost)
    (D.acceptProb (progEnv rel L.kL Q) Quantum.noPost) (D.acceptProb (progEnv rel (S.toKernel (Wit := Wit)) Q) Quantum.noPost)
  have t2 := abs_sub_le (D.acceptProb (progEnv rel L.kL Q) Quantum.noPost)
    (D.acceptProb (progEnv rel L.kD Q) Quantum.noPost) (D.acceptProb (progEnv rel (S.toKernel (Wit := Wit)) Q) Quantum.noPost)
  nlinarith

end QROM

namespace QROM

open GordieHowe.ROM.NIZK

variable {X Y Stmt Wit Proof : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  [Fintype Stmt] [DecidableEq Stmt] [Fintype Wit] [DecidableEq Wit] [Fintype Proof]
  [DecidableEq Proof]

/-- A proof query read through maps of the statement and the witness. -/
def ProofQuery.map {Stmt' Wit' : Type} (fx : Stmt' → Stmt) (fw : Wit' → Wit) :
    ProofQuery Stmt' Wit' → ProofQuery Stmt Wit :=
  fun r => ⟨fx r.stmt, fw r.wit⟩

/-- **Query-counted zero knowledge of a salted argument from a leaf kernel, for statements and
witnesses read from finite types** (the form the compiled arguments use). For a prover `P` with a
per-proof salt, a simulator `S`, a leaf kernel `L` with its laws (`hL`), and a kernel `K₁` that is
`L.kL` up to the bijection `e` of the coins (`hK₁`), let `P` and `K₁` read as a simulator of the
proof queries be local in the salt (`hloc`) and close on a fresh slice at every salt within `η H`
(`hcl`, `ROM.NIZK.SliceCloseAt`), and let the replies of `L.kD` and of `S` be within `ε₃` (`h₃`).
Then, with statements and witnesses read through `fx` and `fw` from finite types, every
distinguisher with a budget of `q` query slots of `n` parallel queries, `n * q ≤ t`, and no final
unitary has advantage at most

    4 Q t / √|Sd| + Q (Q - 1) / |Sd| + Q · 𝔼 H, η H
    + Q (4 t √(|Pos|/|N|) + 3 (|pub| |Pos| + Q |Pos|² + |Pos|²)/|N|) + Q ε₃

(`zeroKnowledgeAfterAdaptive_of_sliceClose` for stage 1, then
`zeroKnowledgeQueryBoundedPure_of_leafKernel`). -/
theorem zeroKnowledgeQueryBoundedPure_comap_of_leafKernel {Stmt₀ Wit₀ : Type}
    {rel₀ : Stmt₀ → Wit₀ → Prop} [DecidableRel rel₀] [DecidableEq Y] [AddCommGroup Y]
    {Sd C SC : Type} [Fintype Sd] [DecidableEq Sd] [Nonempty Sd] [Fintype C] [Nonempty C]
    [Fintype SC] [Nonempty SC] {saltOf : X → Option Sd} {SimCoins : Type} [Fintype SimCoins]
    [Nonempty SimCoins] {P : NARG.ProverFn X Y Stmt₀ Wit₀ Proof (SaltedCoins Sd C)}
    {S : NARG.SimulatorFn X Y Stmt₀ Proof SimCoins} {Cm Pos N : Type} [Fintype Cm]
    [Nonempty Cm] [Fintype Pos] [DecidableEq Pos] [Fintype N] [DecidableEq N] [Nonempty N]
    {L : LeafKernel X Y Stmt₀ Wit₀ Proof Cm Pos N} {nsalt : X → Option N} {pub : Finset N}
    (hL : L.Laws nsalt pub) {K₁ : Kernel X Y Stmt₀ Wit₀ Proof (SaltedCoins Sd SC)}
    (e : SaltedCoins Sd SC ≃ LeafCoins Cm Pos N Y)
    (hK₁ : ∀ req O c, K₁ req O c = L.kL req O (e c)) {η : (X → Y) → ℝ}
    (hloc : SaltedLocal saltOf P.liftReq K₁.toSimulator)
    (hcl : SliceCloseAt saltOf (liftRel rel₀) P.liftReq K₁.toSimulator η)
    {ε₃ : ℝ} (hε₃ : 0 ≤ ε₃)
    (h₃ : ∀ req O, rel₀ req.stmt req.wit →
      PMF.tvDist ((PMF.uniformOfFintype (LeafCoins Cm Pos N Y)).map fun c => kernelReply rel₀ L.kD c req O)
        ((PMF.uniformOfFintype SimCoins).map fun c => kernelReply rel₀ (S.toKernel (Wit := Wit₀)) c req O) ≤
        ε₃) (fx : Stmt → Stmt₀) (fw : Wit → Wit₀) :
    ZeroKnowledgeQueryBoundedPure (fun x w => rel₀ (fx x) (fw w)) (P.comap fx fw)
      (S.comap fx) fun t Q =>
      4 * Q * t / √(Fintype.card Sd) + Q * (Q - 1) / Fintype.card Sd + Q * 𝔼[H ← (X → Y) : η H] +
        Q * (4 * t * √(Fintype.card Pos / Fintype.card N) +
          3 * ((pub.card * Fintype.card Pos + Q * Fintype.card Pos ^ 2 + Fintype.card Pos ^ 2) /
            Fintype.card N)) + Q * ε₃ := by
  set f : ProofQuery Stmt Wit → ProofQuery Stmt₀ Wit₀ := ProofQuery.map fx fw
  have hloc' : SaltedLocal saltOf (P.comap fx fw).liftReq (K₁.comapReq f).toSimulator :=
    hloc.comap f id
  have hcl' : SliceClose saltOf (liftRel fun x w => rel₀ (fx x) (fw w)) (P.comap fx fw).liftReq
      (K₁.comapReq f).toSimulator η := by
    have h0 := hcl.sliceClose
    exact h0.comap f id
  have h₁ := zeroKnowledgeAfterAdaptive_of_sliceClose saltOf _ _ _ hloc' hcl'
  have hc := zeroKnowledgeQueryBoundedPure_of_leafKernel (rel := fun x w => rel₀ (fx x) (fw w))
    (P := P.comap fx fw) (S := S.comap fx) (L := L.comapReq f) (K₁ := K₁.comapReq f)
    (hL.comapReq f) e
    (fun req O c => hK₁ (f req) O c) h₁ hε₃ (fun req O hr => h₃ (f req) O hr)
  exact hc

end QROM

end GordieHowe
