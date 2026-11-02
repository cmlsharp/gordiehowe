-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.O2H.Budget
public import GordieHowe.Model.Quantum.O2H.JuntaDegree

@[expose] public section

/-!
# The degree of the game's amplitudes in the oracle, and the budget

For an environment of the pure game (`GordieHowe/Model/Quantum/Pure/Game.lean`) on tapes `F g`
that depend on a part `g : X → Y₁` of the random oracle, the amplitude of each basis state of the
game, as a function of `g`, has a degree (`GordieHowe/Model/Quantum/O2H/JuntaDegree.lean`)
bounded by the oracle values the branch has read: `n` per query slot (the `n` parallel queries)
and `d` per request, while the oracle in force is read pointwise from `g` and each answer has an
indicator of degree at most `d` (`stage_mem_degLE`). The bound holds on the branches with at most
`e` requests, for hypotheses on the first `e` requests only. This is the counting of GHHM21
(Grilo, Hövelmanns, Hülsing, Majenz, ASIACRYPT 2021) Lemma 1: after `q` queries the oracle
register is in the span of states that differ from the uniform superposition at no more than `q`
inputs.

`Budget.stage_supported`: for a distinguisher with a budget of `q` query slots, the state before
slot `k < m` is supported on the branches that queried at no more than `q` slots before `k`.
-/

open Finset
open scoped BigOperators

namespace GordieHowe.Quantum

namespace Distinguisher

variable {W X Y Y₁ Req A : Type*} [Fintype W] [Fintype X] [DecidableEq X] [Fintype Y]
  [Fintype Y₁] [Fintype Req] [Fintype A] {n m : ℕ} (D : Distinguisher W X Y Req A n m)
  [DecidableEq Req] [DecidableEq A] {Ω : Type*} [AddGroup Y] {Q : ℕ} {St : Type _}
  [OracleState St X Y]

omit [DecidableEq X] [DecidableEq Req] [DecidableEq A] [AddGroup Y] in
/-- A lifted step at `r` is a linear combination of the amplitudes with the logs of `r`, with
coefficients that depend only on the step. -/
theorem liftedStep_apply_eq_sum (k : ℕ) (v : QState (GameReg W n X Y Req A m))
    (r : GameReg W n X Y Req A m) :
    D.liftedStep k v r = ∑ d', D.stepAt k (EuclideanSpace.basisFun _ ℂ d') (splitLogs r).1 *
      v (splitLogs.symm (d', (splitLogs r).2)) := by
  rw [liftedStep, logControlled_apply]
  conv_lhs => rw [← (EuclideanSpace.basisFun _ ℂ).sum_repr
    (WithLp.toLp 2 fun d => v (splitLogs.symm (d, (splitLogs r).2)))]
  simp [map_sum, map_smul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- **One slot keeps the degree bound**: if the amplitudes before slot `k` have the degree bound
on the branches with at most `e` requests, so do the amplitudes after slot `k`, with one more
query slot or one more request. -/
theorem permOp_stage_mem_degLE (E : Env Ω Req A X Y Q St) (F : (X → Y₁) → Ω) {e d : ℕ}
    (horc : ∀ rs : List Req, rs.length ≤ e →
      Junta.ReadsPointwise fun g => (OracleState.toOracle (E.oracleIn (F g) rs) : X → Y))
    (hans : ∀ (rs : List Req) req a, rs.length < e →
      Junta.ofFun (fun g => if E.answerAfter (F g) rs req = a then 1 else 0) ∈ Junta.degLE d)
    (k : ℕ) (ih : ∀ r : GameReg W n X Y Req A m, (requests (splitLogs r).2).length ≤ e →
      Junta.ofFun (fun g => D.stage E (F g) k r) ∈
        Junta.degLE (n * queriesBefore (splitLogs r).2 k + d * (requests (splitLogs r).2).length))
    (s' : GameReg W n X Y Req A m) (hs' : (requests (splitLogs s').2).length ≤ e) :
    Junta.ofFun (fun g => permOp (D.eventPerm E (F g) k) (D.stage E (F g) k) s') ∈
      Junta.degLE (n * queriesBefore (splitLogs s').2 (k + 1) +
        d * (requests (splitLogs s').2).length) := by
  classical
  have hsum : ∀ g, permOp (D.eventPerm E (F g) k) (D.stage E (F g) k) s' =
      ∑ s, (if D.eventPerm E (F g) k s = s' then (1 : ℂ) else 0) * D.stage E (F g) k s := by
    intro g
    rw [permOp_apply, Finset.sum_eq_single ((D.eventPerm E (F g) k).symm s')]
    · simp
    · intro b _ hb
      have hb' : (D.eventPerm E (F g) k) b ≠ s' := fun h => hb (by rw [← h]; simp)
      simp [hb']
    · simp
  simp only [hsum]
  rw [Junta.ofFun_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  by_cases hreach : s ∈ logsIn (reachableLogs k)
  swap
  · have h0 : (fun g => (if D.eventPerm E (F g) k s = s' then (1 : ℂ) else 0) *
        D.stage E (F g) k s) = fun _ => 0 :=
      funext fun g => by rw [D.stage_supported E (F g) k s hreach, mul_zero]
    rw [h0]
    exact Junta.ofFun_const_mem_degLE 0 _
  by_cases hhit : ∃ g, D.eventPerm E (F g) k s = s'
  swap
  · simp only [not_exists] at hhit
    have h0 : (fun g => (if D.eventPerm E (F g) k s = s' then (1 : ℂ) else 0) *
        D.stage E (F g) k s) = fun _ => 0 :=
      funext fun g => by simp [hhit g]
    rw [h0]
    exact Junta.ofFun_const_mem_degLE 0 _
  obtain ⟨g₀, hg₀⟩ := hhit
  have hreq := D.requests_eventPerm E (F g₀) hreach
  rw [hg₀] at hreq
  have hlen : (requests (splitLogs s).2).length ≤ (requests (splitLogs s').2).length := by
    rw [hreq]
    split_ifs <;> simp
  have ihs := ih s (hlen.trans hs')
  by_cases hk : k < m
  · have hblank : (splitLogs s).2 ⟨k, hk⟩ = none := hreach ⟨k, hk⟩ le_rfl
    cases hkind : D.kind s.workspace
    · -- a query slot: the indicator reads the oracle in force at the `n` query inputs
      have hlogs : (splitLogs s').2 = (splitLogs s).2 := by
        rw [← hg₀, D.eventPerm_of_query E _ hk hkind]
        rfl
      have hq : queriedAt (splitLogs s).2 k = true := by simp [queriedAt, hk, hblank]
      refine Junta.ofFun_mul_mem_degLE (b := n * queriesBefore (splitLogs s).2 k +
        d * (requests (splitLogs s).2).length) (a := n) ?_ ihs ?_
      · refine Junta.ofFun_indicator_mem_of_iff (fun g => by
            rw [D.eventPerm_of_query E _ hk hkind]; exact Iff.rfl)
          (Junta.indicator_comp_mem_degLE (fun g i =>
            (OracleState.toOracle (E.oracleIn (F g) (requests (splitLogs s).2)) : X → Y) (s.2 i).1)
            (fun b => ?_) (fun b : Fin n → Y => ((s.1, fun i => ((s.2 i).1, (s.2 i).2 + b i)) :
              GameReg W n X Y Req A m) = s'))
        have hp : (fun g => if (fun i => (OracleState.toOracle
            (E.oracleIn (F g) (requests (splitLogs s).2)) : X → Y) (s.2 i).1) = b
            then (1 : ℂ) else 0) = fun g => ∏ i, if (OracleState.toOracle
            (E.oracleIn (F g) (requests (splitLogs s).2)) : X → Y) (s.2 i).1 = b i
            then (1 : ℂ) else 0 := by
          funext g
          rw [Finset.prod_boole]
          simp [funext_iff]
        rw [hp]
        have := Junta.prod_mem_degLE univ _ (a := 1) fun i _ =>
          (horc _ (hlen.trans hs')).indicator_mem_degLE (s.2 i).1 (b i)
        simpa using this
      · rw [hlogs, queriesBefore_succ, hq]
        simp only [ite_true, Nat.mul_succ]
        omega
    · -- a request slot: the indicator reads the answer
      have hlogs : (splitLogs s').2 = Function.update (splitLogs s).2 ⟨k, hk⟩ (some s.request) := by
        rw [← hg₀, D.eventPerm_of_request E _ hk hreach hkind]
        rfl
      simp only [hkind, hk, and_self, ite_true] at hreq
      have hlen' : (requests (splitLogs s').2).length = (requests (splitLogs s).2).length + 1 := by
        rw [hreq]
        simp
      have hqb : queriesBefore (splitLogs s').2 (k + 1) = queriesBefore (splitLogs s).2 k := by
        rw [queriesBefore_succ, hlogs]
        have hq : queriedAt (Function.update (splitLogs s).2 ⟨k, hk⟩ (some s.request)) k = false := by
          simp [queriedAt, hk]
        simp only [hq, Bool.false_eq_true, ite_false, add_zero]
        exact queriesBefore_congr fun i hi =>
          Function.update_of_ne (Fin.ne_of_val_ne (Nat.ne_of_lt hi)) _ _
      refine Junta.ofFun_mul_mem_degLE (b := n * queriesBefore (splitLogs s).2 k +
        d * (requests (splitLogs s).2).length) (a := d) ?_ ihs ?_
      · exact Junta.ofFun_indicator_mem_of_iff (fun g => by
            rw [D.eventPerm_of_request E _ hk hreach hkind])
          (Junta.indicator_comp_mem_degLE
            (fun g => E.answerAfter (F g) (requests (splitLogs s).2) s.request)
            (fun a => hans (requests (splitLogs s).2) s.request a (by omega))
            (fun a : Option A => (((s.workspace, s.request, Equiv.swap none a s.response,
              Function.update s.logs ⟨k, hk⟩ (some s.request)), s.2) :
                GameReg W n X Y Req A m) = s'))
      · rw [hqb, hlen']
        rw [Nat.mul_succ]
        omega
  · have hss : s = s' := by rw [← hg₀, D.eventPerm_of_le E _ (not_lt.1 hk)]
    subst hss
    refine Junta.ofFun_mul_mem_degLE (a := 0) ?_ ihs ?_
    · refine Junta.mem_degLE_of_dependsOn ∅ (by simp) fun g g' _ => ?_
      simp [Junta.ofFun_apply, D.eventPerm_of_le E _ (not_lt.1 hk)]
    · rw [queriesBefore_succ_of_le _ (not_lt.1 hk)]
      omega

/-- **The degree of the game's amplitudes in the oracle.** For tapes `F g`, if the oracle in
force after at most `e` requests is read pointwise from `g` and the answers to the first `e`
requests have indicators of degree at most `d`, then on every basis state whose logs hold at most
`e` requests the amplitude before slot `k`, as a function of `g`, has degree at most
`n · (query slots before k) + d · (requests)`. -/
theorem stage_mem_degLE (E : Env Ω Req A X Y Q St) (F : (X → Y₁) → Ω) {e d : ℕ}
    (horc : ∀ rs : List Req, rs.length ≤ e →
      Junta.ReadsPointwise fun g => (OracleState.toOracle (E.oracleIn (F g) rs) : X → Y))
    (hans : ∀ (rs : List Req) req a, rs.length < e →
      Junta.ofFun (fun g => if E.answerAfter (F g) rs req = a then 1 else 0) ∈ Junta.degLE d)
    (k : ℕ) (r : GameReg W n X Y Req A m) (hr : (requests (splitLogs r).2).length ≤ e) :
    Junta.ofFun (fun g => D.stage E (F g) k r) ∈
      Junta.degLE (n * queriesBefore (splitLogs r).2 k + d * (requests (splitLogs r).2).length) := by
  classical
  induction k generalizing r with
  | zero =>
    exact Junta.degLE_mono (Nat.zero_le _)
      (Junta.mem_degLE_of_dependsOn ∅ (by simp) fun g g' _ => rfl)
  | succ k ih =>
    have hs : (fun g => D.stage E (F g) (k + 1) r) = fun g =>
        ∑ d', D.stepAt (k + 1) (EuclideanSpace.basisFun _ ℂ d') (splitLogs r).1 *
          permOp (D.eventPerm E (F g) k) (D.stage E (F g) k) (splitLogs.symm (d', (splitLogs r).2)) :=
      funext fun g => by rw [stage_succ, liftedStep_apply_eq_sum]
    rw [hs, Junta.ofFun_sum]
    refine Submodule.sum_mem _ fun d' _ => ?_
    rw [Junta.ofFun_const_mul]
    refine Submodule.smul_mem _ _ ?_
    have h := D.permOp_stage_mem_degLE E F horc hans k ih (splitLogs.symm (d', (splitLogs r).2))
      (by simpa using hr)
    simpa using h

omit [DecidableEq X] in
/-- **The budget bounds the query slots of every branch**: for a distinguisher with a budget of
`q` query slots, the state before slot `k < m` is supported on the branches that queried at no
more than `q` slots before `k`. -/
theorem Budget.stage_supported {q : ℕ} (bud : D.Budget q) (E : Env Ω Req A X Y Q St) (ω : Ω)
    {k : ℕ} (hk : k < m) :
    Supported {r : GameReg W n X Y Req A m | queriesBefore (splitLogs r).2 k ≤ q}
      (D.stage E ω k) := by
  have key : ∀ k < m, Supported {r : GameReg W n X Y Req A m | bud.HoldsBefore k r.1}
      (D.stage E ω k) := by
    intro k
    induction k with
    | zero => exact fun hm => bud.holdsBefore_liftedStep_zero hm
    | succ k ih =>
      intro hk1
      rw [stage_succ]
      refine bud.holdsBefore_liftedStep k hk1 ((ih (by omega)).permOp fun r hr => ?_)
      rw [D.eventPerm_of_lt E ω (by omega)]
      exact bud.holds_requestPerm E ω (by omega) hr
  exact (key k hk).mono fun r hr => hr.count

end Distinguisher

end GordieHowe.Quantum
