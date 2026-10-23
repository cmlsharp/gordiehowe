-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.SaltedZK
public import GordieHowe.Model.Quantum.O2H.RequestBudget

@[expose] public section

/-!
# Everlasting zero knowledge of a salted argument

`GordieHowe/Model/QROM/SaltedZK.lean` proves zero knowledge of a salted non-interactive argument against
distinguishers with a query budget (`GordieHowe.QROM.ZeroKnowledgeAfterAdaptive`), which charges every query
slot before the last slot. This file proves the same bound against distinguishers with a request
budget (`Distinguisher.RequestBudget`), which charges only the query slots before each proof query, so
the queries after a branch's last proof query, wherever it falls at run time, are unbounded: everlasting
zero knowledge (the paper's Definition 6.2, `def:narg-zk-post`). Only the O2H step changes
(`Distinguisher.advantage_acceptProbOn_made_le_of_fresh_secret_requestBudget`).

- `GordieHowe.QROM.EverlastingZeroKnowledgePure`: the notion for the pure games.
- `GordieHowe.QROM.everlastingZeroKnowledgePure_of_sliceClose`: the salted argument.
-/

open Finset
open scoped BigOperators

namespace GordieHowe

namespace QROM

section Notion

variable {X Y Stmt Wit Proof Coins SimCoins : Type*} (rel : Stmt → Wit → Prop) [DecidableRel rel]
  [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [AddGroup Y] [Fintype Stmt]
  [DecidableEq Stmt] [Fintype Wit] [DecidableEq Wit] [Fintype Proof] [DecidableEq Proof]
  [Fintype Coins] [Fintype SimCoins]

/-- **Everlasting zero knowledge, against distinguishers with a request budget** (Unruh
2017 Definition 6, p. 14, with the query bound of the paper's Definition 6.2, `def:narg-zk-post`).
For every query bound `t`, every distinguisher with `m` slots of `n` parallel queries or one proof query
and a request budget of `q` slots (`Distinguisher.RequestBudget`: on every branch at most `q` slots
before each proof query are queries, at slots and with proof queries the branch chooses at run time; after
its last proof query the branch queries at any number of slots) with `n * q ≤ t`, against environments
answering `Q` proof queries, and every final unitary `post` that depends on the whole oracle in force at
the end and keeps the halted branches, has advantage at most `ε t Q` against the simulator `S`.
Request slots are not counted. -/
def EverlastingZeroKnowledgePure (P : NARG.ProverFn X Y Stmt Wit Proof Coins)
    (S : NARG.SimulatorFn X Y Stmt Proof SimCoins) (ε : ℕ → ℕ → ℝ) : Prop :=
  ∀ (t : ℕ) (W : Type) [Fintype W] (n m Q q : ℕ)
    (D : Quantum.Distinguisher W X Y (ProofQuery Stmt Wit) Proof n m)
    (post : (X → Y) → Quantum.QState (Quantum.DReg W n X Y (ProofQuery Stmt Wit) Proof) ≃ₗᵢ[ℂ]
      Quantum.QState (Quantum.DReg W n X Y (ProofQuery Stmt Wit) Proof)) (rb : D.RequestBudget q),
    rb.PostRejectsHalted post → n * q ≤ t → QROM.advantage (Q := Q) rel P S D post ≤ ε t Q

variable {rel}

/-- A larger error bound. -/
theorem EverlastingZeroKnowledgePure.mono {P : NARG.ProverFn X Y Stmt Wit Proof Coins}
    {S : NARG.SimulatorFn X Y Stmt Proof SimCoins} {ε ε' : ℕ → ℕ → ℝ}
    (h : EverlastingZeroKnowledgePure rel P S ε) (hε : ∀ t Q, ε t Q ≤ ε' t Q) :
    EverlastingZeroKnowledgePure rel P S ε' :=
  fun t W _ n m Q q D post rb hpost hD => (h t W n m Q q D post rb hpost hD).trans (hε t Q)

end Notion

variable {X Y Sd Stmt Wit Proof C SC : Type*}

section Salted

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype Sd]
  [DecidableEq Sd] [Nonempty Sd] [Fintype C] [Nonempty C] [Fintype SC] [Nonempty SC]
  [Fintype Proof] [DecidableEq Proof] (saltOf : X → Option Sd) (rel : Stmt → Wit → Prop) [DecidableRel rel]
  (P : NARG.ProverFn X Y Stmt Wit Proof (SaltedCoins Sd C)) (S : NARG.SimulatorFn X Y Stmt Proof (SaltedCoins Sd SC))

variable [AddCommGroup Y] [Fintype Stmt] [DecidableEq Stmt] [Fintype Wit] [DecidableEq Wit]
  {W : Type} [Fintype W] {n m Q : ℕ}
  (D : Quantum.Distinguisher W X Y (ProofQuery Stmt Wit) Proof n m)
  (post : (X → Y) → Quantum.QState (Quantum.DReg W n X Y (ProofQuery Stmt Wit) Proof) ≃ₗᵢ[ℂ]
    Quantum.QState (Quantum.DReg W n X Y (ProofQuery Stmt Wit) Proof))

/-- Step 3 for the prover: O2H for the fresh slice of the prover's salt, charging the `q` query
slots of a budget `bud`. -/
theorem abs_stepEnvP_sub_le_requestBudget {q : ℕ} (rb : D.RequestBudget q)
    (hpost : rb.PostRejectsHalted post) (j : Fin Q) :
    |D.acceptProbOn (stepEnv rel P S j 0 (respProverFresh saltOf rel P)) post (Quantum.madeLogs (j : ℕ)) -
      D.acceptProbOn (stepEnv rel P S j (freshShift saltOf) (respProver rel P)) post
        (Quantum.madeLogs (j : ℕ))| ≤ 2 * q * √(n * (Fintype.card Sd : ℝ)⁻¹) := by
  refine D.advantage_acceptProbOn_made_le_of_fresh_secret_requestBudget post rb hpost _ _
    (μV := PMF.uniformOfFintype (HTape X Y Sd C SC Q))
    (ν := PMF.uniformOfFintype (FreshSlice X Y (SaltedCoins Sd C))) (T := fun τ => {y | saltOf y = some τ.coins.salt})
    j (fun v τ => uniformOfFintype_step_apply v τ) rfl
    (fun ω rs req => (stepEnv_answerAfter_of_resp rel P S j _ _ _ ω (fun _ _ => rfl) rs req).symm)
    (fun ω rs h => (stepEnv_oracleIn_of_resp rel P S j _ _ _ ω (fun _ _ => rfl) rs h).symm)
    (fun ω rs h x hx => ?_)
    (fun v σ σ' rs h => stepEnv_oracleIn_fresh rel P S j _ v σ σ' h)
    (fun v σ σ' rs req h => stepEnv_answerAfter_fresh rel P S j _ v σ σ' h req)
    (fun x => prob_saltSlot_le saltOf x)
  have h0 : freshShift saltOf ω x = 0 := sliceShift_eq_zero saltOf hx
  rw [stepEnv_oracleIn_shift rel P S j (freshShift saltOf) (respProver rel P)
    (respProverFresh saltOf rel P) ω rs h, Pi.add_apply, h0, add_zero]

/-- Step 3 for the simulator: O2H for the fresh slice of the simulator's salt, charging the `q`
query slots of a request budget `rb`. -/
theorem abs_stepEnvS_sub_le_requestBudget {q : ℕ} (rb : D.RequestBudget q)
    (hpost : rb.PostRejectsHalted post) (j : Fin Q) :
    |D.acceptProbOn (stepEnv rel P S j 0 (respSimFresh saltOf rel S)) post (Quantum.madeLogs (j : ℕ)) -
      D.acceptProbOn (stepEnv rel P S j (freshShift saltOf) (respSim rel S)) post
        (Quantum.madeLogs (j : ℕ))| ≤ 2 * q * √(n * (Fintype.card Sd : ℝ)⁻¹) := by
  refine D.advantage_acceptProbOn_made_le_of_fresh_secret_requestBudget post rb hpost _ _
    (μV := PMF.uniformOfFintype (HTape X Y Sd C SC Q))
    (ν := PMF.uniformOfFintype (FreshSlice X Y (SaltedCoins Sd SC))) (T := fun τ => {y | saltOf y = some τ.coins.salt})
    j (fun v τ => uniformOfFintype_step_apply v τ) rfl
    (fun ω rs req => (stepEnv_answerAfter_of_resp rel P S j _ _ _ ω (fun _ _ => rfl) rs req).symm)
    (fun ω rs h => (stepEnv_oracleIn_of_resp rel P S j _ _ _ ω (fun _ _ => rfl) rs h).symm)
    (fun ω rs h x hx => ?_)
    (fun v σ σ' rs h => stepEnv_oracleIn_fresh rel P S j _ v σ σ' h)
    (fun v σ σ' rs req h => stepEnv_answerAfter_fresh rel P S j _ v σ σ' h req)
    (fun x => prob_saltSlot_le saltOf x)
  have h0 : freshShift saltOf ω x = 0 := sliceShift_eq_zero saltOf hx
  rw [stepEnv_oracleIn_shift rel P S j (freshShift saltOf) (respSim rel S)
    (respSimFresh saltOf rel S) ω rs h, Pi.add_apply, h0, add_zero]

/-- **One step of the hybrid.** Hybrids `j` and `j + 1` are distinguished with advantage at
most `4 q √(n / |Sd|)` (two O2H steps over the `q` query slots of a request budget `rb`) plus
`2 j / |Sd|` (an earlier simulator drew proof query `j`'s salt, twice) plus `𝔼 H, η H` (proof query
`j`'s kernel). -/
theorem abs_acceptProb_hybridEnv_sub_le_requestBudget {η : (X → Y) → ℝ} (hloc : SaltedLocal saltOf P S)
    (hclose : SliceClose saltOf rel P S η) {q : ℕ} (rb : D.RequestBudget q)
    (hpost : rb.PostRejectsHalted post) (j : Fin Q) :
    |D.acceptProb (hybridEnv rel P S Q j) post - D.acceptProb (hybridEnv rel P S Q (j + 1)) post| ≤
      4 * q * √(n / Fintype.card Sd) + 2 * j / Fintype.card Sd +
        𝔼[H ← (X → Y) : η H] := by
  have hsplit : ∀ E : Quantum.Env (HTape X Y Sd C SC Q) (ProofQuery Stmt Wit) Proof X Y Q, D.acceptProb E post =
      D.acceptProbOn E post (Quantum.madeLogs (j : ℕ)) + D.acceptProbOn E post (Quantum.madeLogs (j : ℕ))ᶜ :=
    fun E => by
      rw [← Quantum.Distinguisher.acceptProbOn_univ, D.acceptProbOn_eq_add post E Set.univ (Quantum.madeLogs (j : ℕ)),
        Set.univ_inter, Set.univ_inter]
  rw [hsplit, hsplit, acceptProbOn_hybridEnv_notMade rel P S D post j,
    add_sub_add_right_eq_sub, acceptProbOn_hybridEnv_eq_relabelP saltOf rel P S D post hloc j,
    acceptProbOn_hybridEnv_eq_relabelS saltOf rel P S D post hloc j]
  have hsqrt : √(n * (Fintype.card Sd : ℝ)⁻¹) = √(n / Fintype.card Sd) := by rw [div_eq_mul_inv]
  have h1 := abs_relabelEnvP_sub_le saltOf rel P S D post hloc j
  have h2 := abs_stepEnvP_sub_le_requestBudget saltOf rel P S D post rb hpost j
  have h3 := abs_stepEnv_kernel_le saltOf rel P S D post hloc hclose j
  have h4 := abs_stepEnvS_sub_le_requestBudget saltOf rel P S D post rb hpost j
  have h5 := abs_relabelEnvS_sub_le saltOf rel P S D post hloc j
  rw [hsqrt] at h2 h4
  have e : ∀ a b c d e f : ℝ, |a - f| ≤ |a - b| + |c - b| + |c - d| + |d - e| + |f - e| := by
    intro a b c d e f
    calc |a - f| = |(a - b) - (c - b) + (c - d) + (d - e) - (f - e)| := by ring_nf
      _ ≤ |a - b| + |c - b| + |c - d| + |d - e| + |f - e| := by
        have h1 := abs_sub (a - b - (c - b) + (c - d) + (d - e)) (f - e)
        have h2 := abs_add_le (a - b - (c - b) + (c - d)) (d - e)
        have h3 := abs_add_le (a - b - (c - b)) (c - d)
        have h4 := abs_sub (a - b) (c - b)
        linarith
  refine (e _ (D.acceptProbOn (stepEnv rel P S j (freshShift saltOf) (respProver rel P)) post
    (Quantum.madeLogs (j : ℕ))) (D.acceptProbOn (stepEnv rel P S j 0 (respProverFresh saltOf rel P)) post
    (Quantum.madeLogs (j : ℕ))) (D.acceptProbOn (stepEnv rel P S j 0 (respSimFresh saltOf rel S)) post
    (Quantum.madeLogs (j : ℕ))) (D.acceptProbOn (stepEnv rel P S j (freshShift saltOf) (respSim rel S)) post
    (Quantum.madeLogs (j : ℕ))) _).trans ?_
  have hj2 : 2 * ((j : ℕ) : ℝ) / Fintype.card Sd = (j : ℕ) / Fintype.card Sd + (j : ℕ) / Fintype.card Sd := by
    ring
  have hm4 : 4 * (q : ℝ) * √(n / Fintype.card Sd) =
      2 * q * √(n / Fintype.card Sd) + 2 * q * √(n / Fintype.card Sd) := by ring
  rw [hj2, hm4]
  linarith

/-- **Everlasting zero knowledge of a salted argument**: if the argument is local in
its salt (`SaltedLocal`) and one proof is simulated within `η H` on a fresh slice (`SliceClose`),
then every distinguisher with `m` slots of `n` parallel queries or one proof query and a request
budget of `q` slots with `n * q ≤ t` (each branch queries at no more than `q` slots before each of
its proof queries, chosen at run time, and at any number after its last one), against environments
answering `Q` proof queries, followed by any unitary of the whole final oracle that keeps the halted
branches, has advantage at most `4 Q t / √|Sd| + Q (Q - 1) / |Sd| + Q · 𝔼 H, η H` against the
simulator `S`. The proof is that of `zeroKnowledgeAfterAdaptive_of_sliceClose`, with the O2H step
of `Distinguisher.advantage_acceptProbOn_made_le_of_fresh_secret_requestBudget`. -/
theorem everlastingZeroKnowledgePure_of_sliceClose {η : (X → Y) → ℝ}
    (hloc : SaltedLocal saltOf P S) (hclose : SliceClose saltOf rel P S η) :
    EverlastingZeroKnowledgePure rel P S fun t Q =>
      4 * Q * t / √(Fintype.card Sd) + Q * (Q - 1) / Fintype.card Sd + Q * 𝔼[H ← (X → Y) : η H] := by
  intro t W _ n m Q q D post rb hpost hD
  have hc : (0 : ℝ) < Fintype.card Sd := Nat.cast_pos.2 Fintype.card_pos
  -- the query count: `q √n ≤ t` for the `q` query slots
  have hmt : (q : ℝ) * √n ≤ t := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · have h1 : √(n : ℝ) ≤ n := Real.sqrt_le_iff.2 ⟨by positivity, by
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith⟩
      calc (q : ℝ) * √n ≤ q * n :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (n * q : ℕ) := by push_cast; ring
        _ ≤ t := by exact_mod_cast hD
  have hstep : ∀ j : Fin Q, |D.acceptProb (hybridEnv rel P S Q j) post -
      D.acceptProb (hybridEnv rel P S Q (j + 1)) post| ≤
        4 * t / √(Fintype.card Sd) + 2 * j / Fintype.card Sd + 𝔼[H ← (X → Y) : η H] := fun j => by
    refine (abs_acceptProb_hybridEnv_sub_le_requestBudget saltOf rel P S D post hloc hclose rb hpost j).trans ?_
    have : 4 * (q : ℝ) * √(n / Fintype.card Sd) ≤ 4 * t / √(Fintype.card Sd) := by
      rw [Real.sqrt_div' _ hc.le, mul_div_assoc', mul_assoc]
      gcongr
    linarith
  refine (advantage_le_sum_hybrid rel D post P S).trans ((Finset.sum_le_sum fun j _ => hstep j).trans ?_)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
  have hsum : ∑ j : Fin Q, 2 * (j : ℝ) / Fintype.card Sd = Q * (Q - 1) / Fintype.card Sd := by
    have key : ∀ q : ℕ, 2 * ∑ j ∈ Finset.range q, (j : ℝ) = q * (q - 1) := by
      intro q
      induction q with
      | zero => simp
      | succ q ih =>
        rw [Finset.sum_range_succ, mul_add, ih]
        push_cast
        ring
    rw [← Finset.sum_div, ← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun j => (j : ℝ)) Q, key]
  rw [hsum]
  ring_nf
  exact le_refl _

end Salted

end QROM

end GordieHowe
