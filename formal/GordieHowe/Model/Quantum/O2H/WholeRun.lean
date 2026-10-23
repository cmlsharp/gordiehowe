-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.O2H.Budget

@[expose] public section

/-!
# O2H over the whole run of a game without a final unitary

`Distinguisher.advantage_acceptProbOn_made_le_of_fresh_secret_budget` compares two environments
whose oracles differ only before a request, on a set fixed by a secret not read before it. Here the
oracles may differ at every slot, before and after every request, on a set `T σ` fixed by a
component `σ` of the tape that the first environment never reads (neither its oracles nor its
answers depend on `σ`), and the answers of the two environments are the same. Without a final
unitary (`noPost`) every query is one of the counted query slots, so a distinguisher with a budget
of `q` query slots distinguishes the two games with advantage at most `2 q √(n ε)`
(`Distinguisher.advantage_acceptProb_le_of_fresh_secret_budget`), with `ε` bounding
`Pr_σ[x ∈ T σ]`. The proof is `O2HSetting.o2h_fresh_secret_of_count` for `gameAlg`, the set being
`T σ` on every query branch.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} {D : Distinguisher W X Y Req A n m} {q : ℕ}
  [DecidableEq Req] [DecidableEq A] [AddGroup Y] {Q : ℕ} {Ω : Type*}

/-- Without a final unitary, the steps of the game read the environment only through its answers. -/
theorem gameStep_noPost_congr {E E' : Env Ω Req A X Y Q} {ω ω' : Ω}
    (hans : ∀ (lg : LogReg Req m) k, E.answer ω lg k = E'.answer ω' lg k) (t : ℕ) :
    D.gameStep E noPost ω t = D.gameStep E' noPost ω' t := by
  unfold gameStep
  split_ifs with h
  · simp only [Env.requestPerm, funext fun lg => hans lg ⟨t, h⟩]
  · rfl

variable {V R : Type*} [Fintype V] [Fintype R]

/-- **O2H over the whole run for a fresh secret, with a query budget** (module docstring). -/
theorem advantage_acceptProb_le_of_fresh_secret_budget (bud : D.Budget q)
    (E E' : Env (V × R) Req A X Y Q) {μV : PMF V} {ν : PMF R} {T : R → Set X} {ε : ℝ}
    (hμ : ∀ v σ, E.μ (v, σ) = μV v * ν σ) (hμ' : E'.μ = E.μ)
    (hans : ∀ ω rs req, E.answerAfter ω rs req = E'.answerAfter ω rs req)
    (hdiff : ∀ ω rs, ∀ x ∉ T ω.2, E.oracleIn ω rs x = E'.oracleIn ω rs x)
    (hfreshOracle : ∀ v σ σ' rs, E.oracleIn (v, σ) rs = E.oracleIn (v, σ') rs)
    (hfreshAnswer : ∀ v σ σ' rs req, E.answerAfter (v, σ) rs req = E.answerAfter (v, σ') rs req)
    (hε : ∀ x, (ν.toOuterMeasure {σ | x ∈ T σ}).toReal ≤ ε) :
    GordieHowe.advantage (D.acceptProb E noPost) (D.acceptProb E' noPost) ≤ 2 * q * √(n * ε) := by
  classical
  let M : Set (W × Req × Option A × LogReg Req m) := {w | D.kind w.1 = false}
  let s : O2HSetting (V × R) (V × R) (W × Req × Option A × LogReg Req m) X Y :=
    { μ := E.μ
      S := fun ω w => if w ∈ M then T ω.2 else ∅
      G := fun ω => E'.oracleFn D.kind ω
      H := fun ω => E.oracleFn D.kind ω
      z := id
      agree := fun ω w x hx => by
        simp only [Env.oracleFn, Env.oracle]
        by_cases hk : D.kind w.1 = true
        · simp [hk]
        · have hw : w ∈ M := by simpa [M] using hk
          simp only [hw, ite_true] at hx
          simp only [hk, Bool.false_eq_true, ite_false]
          exact (hdiff ω _ x hx).symm }
  have hans' : ∀ ω (lg : LogReg Req m) k, E.answer ω lg k = E'.answer ω lg k := fun ω lg k => by
    simp only [Env.answer, funext (hans ω (requestsBefore lg k))]
  have hpL : s.pLeft (D.gameAlg E noPost Set.univ) = D.acceptProb E noPost := by
    rw [← acceptProbOn_univ]
    exact sum_congr rfl fun ω _ => by rw [← D.acceptProb_gameAlg_self E noPost _ ω]; rfl
  have hA : D.gameAlg E noPost Set.univ = D.gameAlg E' noPost Set.univ := by
    unfold gameAlg
    congr 1
    funext ω t
    exact gameStep_noPost_congr (hans' ω) t
  have hpR : s.pRight (D.gameAlg E noPost Set.univ) = D.acceptProb E' noPost := by
    rw [← acceptProbOn_univ]
    change ∑ ω, (E.μ ω).toReal * _ = ∑ ω, (E'.μ ω).toReal * _
    rw [hμ']
    refine sum_congr rfl fun ω _ => ?_
    rw [← D.acceptProb_gameAlg_self E' noPost _ ω, ← hA]
    rfl
  have hcount := fun ω => bud.stepCount_gameAlg noPost E Set.univ ω
  have hMC : ∀ k < m, ∀ w ∈ M, w ∈ {s | bud.Holds k s} →
      w ∈ {s : W × Req × Option A × LogReg Req m | queriedAt s.2.2.2 k = true} :=
    fun k hk w hw hH => by
      have h := hH.logged hk
      rw [show D.kind w.1 = false from hw] at h
      exact h
  have hpre : ∀ v σ σ' i, mask {r : GameReg W n X Y Req A m | r.1 ∈ M}
      ((D.gameAlg E noPost Set.univ).pre (queryPermOf (s.H (v, σ))) (s.z (v, σ)) i) =
      mask {r : GameReg W n X Y Req A m | r.1 ∈ M}
        ((D.gameAlg E noPost Set.univ).pre (queryPermOf (s.H (v, σ'))) (s.z (v, σ')) i) := by
    intro v σ σ' i
    have hH : s.H (v, σ) = s.H (v, σ') := by
      funext w
      simp only [s, Env.oracleFn, Env.oracle, hfreshOracle v σ σ']
    rw [hH]
    congr 1
    refine (D.gameAlg E noPost Set.univ).pre_congr (z := (v, σ)) (z' := (v, σ')) _ rfl (fun k _ => ?_) i
    exact gameStep_noPost_congr (fun lg k => by
      simp only [Env.answer, funext (hfreshAnswer v σ σ' (requestsBefore lg k))]) k
  rw [← hpL, ← hpR]
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · refine (s.o2h_of_count _ _ _ q hcount fun ω k hk w hw x hx => isEmptyElim x).trans ?_
    have hq : ∀ ω, queriedOf (n := n) (Y := Y) (s.S ω) = ∅ := fun ω => by
      ext r
      simp only [queriedOf, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists]
      exact fun i => isEmptyElim (r.2 i).1
    have h0 : ∀ v : QState (GameReg W n X Y Req A m), prob ∅ v = 0 := fun v => by
      have hm : mask (∅ : Set (GameReg W n X Y Req A m)) v = 0 := by
        ext i
        simp
      rw [prob, hm, norm_zero, zero_pow two_ne_zero]
    simp only [hq, h0, sum_const_zero, mul_zero, Real.sqrt_zero]
    positivity
  have hε0 : 0 ≤ ε := ENNReal.toReal_nonneg.trans (hε x₀)
  exact s.o2h_fresh_secret_of_count _ M _ _ q hμ (fun v σ w hw => by simp [s, hw])
    (fun v σ w hw => by simp [s, hw]) hpre hcount hMC hε0 hε

end Distinguisher

end GordieHowe.Quantum
