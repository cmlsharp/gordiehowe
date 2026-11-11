-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.ROM.ProgEnv
public import GordieHowe.Foundations.ToMathlib.PMFOracleQuenched

public section

/-!
# Programming at a hidden salt in the classical random-oracle model

A simulator with salted coins `(σ, c)` that programs the oracle only on the slice of its salt
`σ`, reads the oracle only on salt-free inputs, and whose proof does not depend on `σ`
(`HiddenProgramming`): its assignments are invisible unless the adversary queries a point of the
slice of some proof query's salt. Since the salt enters nothing the adversary sees, against an
adversary that reads the oracle only through its `t` counted queries (`IAlg.PostOracleFree`) the
simulator and the simulator with its assignments dropped (`SimulatorFn.dropAssignments`) are
within `Q t / |Sd|` (`abs_acceptProb_simEnv_dropAssignments_le`): the two runs agree until a
query lands in the slice of one of the `Q` salts, and in the run without assignments the salts
are independent of every query.

The theorem completes `GordieHowe/Model/ROM/SaltedZK.lean` for simulators that program a point
keyed by a fresh hidden salt (a message representative `µ = H_µ(tr ‖ R ‖ ctx)` with a fresh `R`)
that a final simulator, which does not know the key, cannot program.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.ROM.NIZK

open GordieHowe.Quantum GordieHowe.QROM

variable {X Y Stmt Wit Proof Sd C : Type}

/-- **`S` with its assignments dropped**: the same proof, and the oracle in force unchanged.

Running time: one run of `S`, discarding its assignment list; the oracle points read and the
coins are those of `S`. This running time is argued here, not proved in Lean. -/
def _root_.GordieHowe.NARG.SimulatorFn.dropAssignments
    (S : NARG.SimulatorFn X Y Stmt Proof C) : NARG.SimulatorFn X Y Stmt Proof C where
  run H x c := ⟨(S.run H x c).proof, []⟩
  coins_nonempty := S.coins_nonempty

variable [DecidableEq Sd] (saltOf : X → Option Sd)

/-- **Programming at a hidden salt**: the simulator reads no salted point (`run_congr`: its run
depends on the oracle only through the salt-free inputs), its published proof does not depend on
the salt (`proof_salt`), and it programs only points of its own salt (`run_salt`). The sibling
condition of `GordieHowe/Model/ROM/SaltedZK.lean` is `GordieHowe.QROM.SaltedLocal`, where the
simulator may read its own slice and publishes a proof that may depend on the salt. -/
structure HiddenProgramming (S : NARG.SimulatorFn X Y Stmt Proof (SaltedCoins Sd C)) : Prop where
  /-- The run reads the oracle only on salt-free inputs. -/
  run_congr : ∀ (H H' : X → Y) x s, AgreeOffSalted saltOf H H' → S.run H x s = S.run H' x s
  /-- The proof does not depend on the salt. -/
  proof_salt : ∀ (H : X → Y) x c σ σ',
    (S.run H x ⟨σ, c⟩).proof = (S.run H x ⟨σ', c⟩).proof
  /-- Every assignment is on the slice of the salt. -/
  run_salt : ∀ (H : X → Y) x (s : SaltedCoins Sd C), ∀ a ∈ (S.run H x s).assignments,
    saltOf a.input = some s.salt

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype Sd] [Nonempty Sd]
  [Fintype C] [Nonempty C] (rel : Stmt → Wit → Prop) [DecidableRel rel]

section Proof

variable {saltOf rel} {S : NARG.SimulatorFn X Y Stmt Proof (SaltedCoins Sd C)} {Q : ℕ}

/-- `O` agrees with `H` off the slices of the salts `s`. -/
private def OffSalts (saltOf : X → Option Sd) (s : Fin Q → SaltedCoins Sd C) (H O : X → Y) :
    Prop :=
  ∀ x, (∀ i, saltOf x ≠ some (s i).salt) → O x = H x

omit [DecidableEq Sd] [Nonempty Sd] [Nonempty C] in
/-- The responder of the simulated environment. -/
private theorem envResponder_simEnv_apply (ω : (X → Y) × (Fin Q → SaltedCoins Sd C)) (n : ℕ)
    (req : ProofQuery Stmt Wit) (O : X → Y) :
    envResponder (simEnv rel S Q) ω n req O =
      if h : n < Q then
        (if rel req.stmt req.wit then
          ⟨some (S.run O req.stmt (ω.2 ⟨n, h⟩)).proof,
            O.reprogram (S.run O req.stmt (ω.2 ⟨n, h⟩)).assignments⟩
        else ⟨none, O⟩)
      else ⟨none, O⟩ := by
  simp only [envResponder, simEnv]

omit [DecidableEq Sd] [Nonempty Sd] [Nonempty C] in
/-- The responder of the simulated environment with the assignments dropped. -/
private theorem envResponder_drop_apply (ω : (X → Y) × (Fin Q → SaltedCoins Sd C)) (n : ℕ)
    (req : ProofQuery Stmt Wit) (O : X → Y) :
    envResponder (simEnv rel S.dropAssignments Q) ω n req O =
      if h : n < Q then
        (if rel req.stmt req.wit then ⟨some (S.run O req.stmt (ω.2 ⟨n, h⟩)).proof, O⟩
        else ⟨none, O⟩)
      else ⟨none, O⟩ := by
  simp only [envResponder, simEnv, NARG.SimulatorFn.dropAssignments]
  rfl

omit [DecidableEq Sd] [Nonempty Sd] [Nonempty C] in
/-- **The coupling**: while no query lands in the slice of a salt, the runs with and without the
assignments have the same replies and proof queries, the run without them keeps the initial
oracle, and the run with them agrees with it off the slices of the salts. -/
private theorem run_couple (hS : HiddenProgramming saltOf S) {m : ℕ} (A : IAlg X Y Stmt Wit Proof m)
    (ω : (X → Y) × (Fin Q → SaltedCoins Sd C)) :
    ∀ k, (∀ k' < k, ∀ x, A.next (A.run (envResponder (simEnv rel S.dropAssignments Q) ω) ω.1
        k').hist = .query x → ∀ i, saltOf x ≠ some (ω.2 i).salt) →
      (A.run (envResponder (simEnv rel S Q) ω) ω.1 k).hist =
          (A.run (envResponder (simEnv rel S.dropAssignments Q) ω) ω.1 k).hist ∧
        (A.run (envResponder (simEnv rel S Q) ω) ω.1 k).nreq =
          (A.run (envResponder (simEnv rel S.dropAssignments Q) ω) ω.1 k).nreq ∧
        (A.run (envResponder (simEnv rel S.dropAssignments Q) ω) ω.1 k).oracle = ω.1 ∧
        OffSalts saltOf ω.2 ω.1 (A.run (envResponder (simEnv rel S Q) ω) ω.1 k).oracle
  | 0, _ => ⟨rfl, rfl, rfl, fun _ _ => rfl⟩
  | k + 1, hk => by
    obtain ⟨hh, hn, ho, hoff⟩ := run_couple hS A ω k fun k' h' => hk k' (by omega)
    set sS := A.run (envResponder (simEnv rel S Q) ω) ω.1 k
    set sD := A.run (envResponder (simEnv rel S.dropAssignments Q) ω) ω.1 k
    rw [IAlg.run_succ, IAlg.run_succ]
    cases hnext : A.next sD.hist with
    | query x =>
      have hnS : A.next sS.hist = .query x := by rw [hh]; exact hnext
      rw [IAlg.step_of_query hnS, IAlg.step_of_query hnext]
      have hx : sS.oracle x = sD.oracle x := by
        rw [ho]; exact hoff x (hk k (by omega) x hnext)
      exact ⟨by simp only [hh, hx], hn, ho, hoff⟩
    | request req =>
      have hnS : A.next sS.hist = .request req := by rw [hh]; exact hnext
      rw [IAlg.step_of_request hnS, IAlg.step_of_request hnext, envResponder_simEnv_apply,
        envResponder_drop_apply, hn, ho]
      have hagree : AgreeOffSalted saltOf sS.oracle ω.1 := fun y hy =>
        hoff y fun i h => (Option.some_ne_none _ (hy ▸ h).symm).elim
      by_cases hQ : sD.nreq < Q
      · by_cases hr : rel req.stmt req.wit
        · rw [dite_eq_left hQ, ite_eq_left hr,
            dite_eq_left hQ, ite_eq_left hr, hS.run_congr _ _ _ _ hagree]
          refine ⟨by dsimp only; rw [hh], rfl, rfl, fun x hx => ?_⟩
          refine (reprogram_apply_of_forall_ne _ fun a ha he => ?_).trans (hoff x hx)
          have := hS.run_salt _ _ _ a ha
          rw [he] at this
          exact hx _ this
        · rw [dite_eq_left hQ, ite_eq_right hr,
            dite_eq_left hQ, ite_eq_right hr]
          exact ⟨by dsimp only; rw [hh], rfl, rfl, hoff⟩
      · rw [dite_eq_right hQ, dite_eq_right hQ]
        exact ⟨by dsimp only; rw [hh], rfl, rfl, hoff⟩

omit [DecidableEq Sd] [Nonempty Sd] [Nonempty C] in
/-- **Until a query lands in the slice of a salt, the outputs agree.** -/
private theorem accepts_eq_of_not_bad (hS : HiddenProgramming saltOf S) {m : ℕ}
    {A : IAlg X Y Stmt Wit Proof m} (hA : A.PostOracleFree)
    (ω : (X → Y) × (Fin Q → SaltedCoins Sd C))
    (hgood : ∀ k < m, ∀ x, A.next (A.run (envResponder (simEnv rel S.dropAssignments Q) ω) ω.1
      k).hist = .query x → ∀ i, saltOf x ≠ some (ω.2 i).salt) :
    A.accepts (envResponder (simEnv rel S Q) ω) ω.1 =
      A.accepts (envResponder (simEnv rel S.dropAssignments Q) ω) ω.1 := by
  obtain ⟨hh, -, -, -⟩ := run_couple hS A ω m hgood
  rw [IAlg.accepts, IAlg.accepts, hh, hA]

omit [DecidableEq Sd] [Nonempty Sd] [Nonempty C] in
/-- **Without assignments the run does not read the salts.** -/
private theorem envResponder_drop_eq (hS : HiddenProgramming saltOf S) (H : X → Y)
    (s s' : Fin Q → SaltedCoins Sd C) (hs : ∀ i, (s i).coins = (s' i).coins) :
    envResponder (simEnv rel S.dropAssignments Q) (H, s) =
      envResponder (simEnv rel S.dropAssignments Q) (H, s') := by
  funext n req O
  rw [envResponder_drop_apply, envResponder_drop_apply]
  by_cases hQ : n < Q
  · rw [dite_eq_left hQ, dite_eq_left hQ]
    have : (S.run O req.stmt (s ⟨n, hQ⟩)).proof = (S.run O req.stmt (s' ⟨n, hQ⟩)).proof := by
      change (S.run O req.stmt ⟨(s ⟨n, hQ⟩).salt, (s ⟨n, hQ⟩).coins⟩).proof =
        (S.run O req.stmt ⟨(s' ⟨n, hQ⟩).salt, (s' ⟨n, hQ⟩).coins⟩).proof
      rw [hs, hS.proof_salt]
    rw [this]
  · rw [dite_eq_right hQ, dite_eq_right hQ]

open Classical in
/-- **The bad event is rare**: in the run without assignments, a query lands in the slice of one of
the `Q` salts with probability at most `Q t / |Sd|`, since the run does not read the salts and
makes at most `t` queries. -/
private theorem expect_bad_le (hS : HiddenProgramming saltOf S) {m t : ℕ}
    {A : IAlg X Y Stmt Wit Proof m} (hA : A.Budget t) :
    𝔼 ω : (X → Y) × (Fin Q → SaltedCoins Sd C),
        (if ∃ k < m, ∃ x, A.next (A.run (envResponder (simEnv rel S.dropAssignments Q) ω) ω.1
          k).hist = .query x ∧ ∃ i, saltOf x = some (ω.2 i).salt then (1 : ℝ) else 0) ≤
      Q * t / Fintype.card Sd := by
  classical
  set σ₀ : Sd := Classical.arbitrary Sd
  let e : ((X → Y) × (Fin Q → C)) × (Fin Q → Sd) ≃ (X → Y) × (Fin Q → SaltedCoins Sd C) :=
    { toFun := fun q => (q.1.1, fun i => ⟨q.2 i, q.1.2 i⟩)
      invFun := fun ω => ((ω.1, fun i => (ω.2 i).coins), fun i => (ω.2 i).salt)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  -- the run at the tape `e (a, σ)` is the run at the fixed salts `σ₀`
  set Rd : (X → Y) × (Fin Q → C) → Responder X Y Stmt Wit Proof := fun a =>
    envResponder (simEnv rel S.dropAssignments Q) (a.1, fun i => ⟨σ₀, a.2 i⟩)
  have hR : ∀ a σ, envResponder (simEnv rel S.dropAssignments Q) (e (a, σ)) = Rd a := fun a σ =>
    envResponder_drop_eq hS a.1 _ _ fun _ => rfl
  rw [← Fintype.expect_equiv e _ _ fun _ => rfl, expect_prod_eq]
  -- for fixed oracle and coins, a union bound over the query steps and the salts
  have hstep : ∀ a : (X → Y) × (Fin Q → C),
      𝔼 σ : Fin Q → Sd, (if ∃ k < m, ∃ x, A.next (A.run (envResponder
          (simEnv rel S.dropAssignments Q) (e (a, σ))) (e (a, σ)).1 k).hist = .query x ∧
          ∃ i, saltOf x = some ((e (a, σ)).2 i).salt then (1 : ℝ) else 0) ≤
        Q * t / Fintype.card Sd := by
    intro a
    set qs := (range m).filter fun k => (A.next (A.run (Rd a) a.1 k).hist).IsQuery
    have hqs : (qs.card : ℝ) ≤ t := by exact_mod_cast hA (Rd a) a.1
    have hind : ∀ σ : Fin Q → Sd, (if ∃ k < m, ∃ x, A.next (A.run (envResponder
        (simEnv rel S.dropAssignments Q) (e (a, σ))) (e (a, σ)).1 k).hist = .query x ∧
        ∃ i, saltOf x = some ((e (a, σ)).2 i).salt then (1 : ℝ) else 0) ≤
          ∑ k ∈ qs, ∑ i : Fin Q, (match A.next (A.run (Rd a) a.1 k).hist with
            | .query x => if saltOf x = some (σ i) then (1 : ℝ) else 0
            | .request _ => 0) := by
      intro σ
      split_ifs with hb
      · obtain ⟨k, hk, x, hx, i, hi⟩ := hb
        rw [hR] at hx
        change A.next (A.run (Rd a) a.1 k).hist = .query x at hx
        change saltOf x = some (σ i) at hi
        have hkq : k ∈ qs := by
          simp only [qs, mem_filter, mem_range, hk, true_and]
          rw [hx]; trivial
        have hterm : ∀ k' ∈ qs, ∀ i', 0 ≤ (match A.next (A.run (Rd a) a.1 k').hist with
            | .query x => if saltOf x = some (σ i') then (1 : ℝ) else 0
            | .request _ => 0) := fun k' _ i' => by
          split
          · split_ifs <;> norm_num
          · exact le_rfl
        refine le_trans ?_ (single_le_sum (fun k' hk' => sum_nonneg fun i' _ => hterm k' hk' i')
          hkq)
        refine le_trans ?_ (single_le_sum (fun i' _ => hterm k hkq i') (mem_univ i))
        change (1 : ℝ) ≤ _
        rw [show A.next (A.run (Rd a) a.1 k).hist = .query x from hx]
        simp only
        rw [ite_eq_left hi]
      · exact sum_nonneg fun k _ => sum_nonneg fun i _ => by
          split
          · split_ifs <;> norm_num
          · exact le_rfl
    refine (expect_le_expect fun σ _ => hind σ).trans ?_
    rw [expect_sum_comm]
    calc ∑ k ∈ qs, 𝔼 σ : Fin Q → Sd, ∑ i : Fin Q,
          (match A.next (A.run (Rd a) a.1 k).hist with
            | .query x => if saltOf x = some (σ i) then (1 : ℝ) else 0
            | .request _ => 0)
        ≤ ∑ _k ∈ qs, (Q : ℝ) * (1 / Fintype.card Sd) := by
          refine sum_le_sum fun k _ => ?_
          rw [expect_sum_comm]
          rw [show (Q : ℝ) * (1 / Fintype.card Sd) = ∑ _i : Fin Q, (1 / (Fintype.card Sd : ℝ)) by
            rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]]
          refine sum_le_sum fun i _ => ?_
          cases A.next (A.run (Rd a) a.1 k).hist with
          | query x =>
            simp only
            rw [PMF.expect_apply_eval i (fun s => if saltOf x = some s then (1 : ℝ) else 0)]
            exact expect_ite_eq_some_le (saltOf x)
          | request _ =>
            simp only [Fintype.expect_const]
            positivity
      _ = qs.card * Q / Fintype.card Sd := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ Q * t / Fintype.card Sd := by
          rw [mul_comm (qs.card : ℝ)]
          gcongr
  exact (expect_le_expect fun a _ => hstep a).trans_eq (Fintype.expect_const _)

omit [DecidableEq Sd] in
/-- The acceptance probability against a simulated environment, as an average over its tape. -/
private theorem toReal_acceptProb_simEnv_eq {m : ℕ} (A : IAlg X Y Stmt Wit Proof m)
    (S' : NARG.SimulatorFn X Y Stmt Proof (SaltedCoins Sd C)) :
    (A.acceptProb (simEnv rel S' Q)).toReal =
      𝔼 ω : (X → Y) × (Fin Q → SaltedCoins Sd C),
        if A.accepts (envResponder (simEnv rel S' Q) ω) ω.1 = true then (1 : ℝ) else 0 := by
  classical
  have hμ : (simEnv rel S' Q).μ =
      PMF.uniformOfFintype ((X → Y) × (Fin Q → SaltedCoins Sd C)) := by
    change tapeDist Q S'.coins = _
    rw [NARG.SimulatorFn.coins_eq_uniform, tapeDist_uniformOfFintype]
  rw [IAlg.acceptProb, hμ]
  change (GordieHowe.IOP.probUniform ((X → Y) × (Fin Q → SaltedCoins Sd C)) fun ω =>
    A.accepts (envResponder (simEnv rel S' Q) ω) ω.1 = true).toReal = _
  rw [GordieHowe.IOP.toReal_probUniform]

end Proof


/-- **Dropping the assignments at a hidden salt.** For a simulator that programs at a hidden
salt (`HiddenProgramming`), every adversary that makes at most `t` oracle queries in total,
including after its last proof query, distinguishes the simulated environments of `S` and of `S`
with its assignments dropped with advantage at most `Q t / |Sd|` for `Q` proof queries.

The adversary's queries are its counted steps (`IAlg.PostOracleFree`): an output bit that read
the whole final oracle for free would see the programmed points. The sibling result for a
salted prover and its simulator is `zeroKnowledge_of_sliceCloseAt`
(`GordieHowe/Model/ROM/SaltedZK.lean`). -/
theorem abs_acceptProb_simEnv_dropAssignments_le
    {S : NARG.SimulatorFn X Y Stmt Proof (SaltedCoins Sd C)} (hS : HiddenProgramming saltOf S)
    {m t Q : ℕ} (𝒜 : Adversary X Y Stmt Wit Proof m t) (hpost : ∀ r, (𝒜.alg r).PostOracleFree) :
    |𝒜.acceptProb (simEnv rel S Q) - 𝒜.acceptProb (simEnv rel S.dropAssignments Q)| ≤
      Q * t / Fintype.card Sd := by
  classical
  refine 𝒜.abs_acceptProb_sub_le _ _ fun r => ?_
  rw [toReal_acceptProb_simEnv_eq, toReal_acceptProb_simEnv_eq, ← expect_sub_distrib]
  refine (abs_expect_le univ _).trans ((expect_le_expect fun ω _ => ?_).trans
    (expect_bad_le (rel := rel) hS (𝒜.budget r)))
  by_cases hb : ∃ k < m, ∃ x, (𝒜.alg r).next ((𝒜.alg r).run
      (envResponder (simEnv rel S.dropAssignments Q) ω) ω.1 k).hist = .query x ∧
      ∃ i, saltOf x = some (ω.2 i).salt
  · rw [ite_eq_left hb]
    split_ifs <;> norm_num
  · rw [ite_eq_right hb, accepts_eq_of_not_bad hS (hpost r) ω
      fun k hk x hx i hi => hb ⟨k, hk, x, hx, i, hi⟩, sub_self, abs_zero]

/-- **A simulator's proofs as a prover**: the simulator's proof on the oracle, the statement and
its coins; it ignores the witness. Its coin law is the simulator's, `S.coins`.

Running time: one run of `S`, whose cost is argued at its definition. -/
@[expose] def _root_.GordieHowe.NARG.SimulatorFn.toProver {SC : Type}
    (S : NARG.SimulatorFn X Y Stmt Proof SC) : NARG.ProverFn X Y Stmt Wit Proof SC where
  prove H x _ c := (S.run H x c).proof

omit [DecidableEq Sd] [Fintype Sd] [Nonempty Sd] [Fintype C] [Nonempty C] in
/-- **A simulator without assignments is a prover**: its simulated environment is the real
environment of its proofs (`SimulatorFn.toProver`) with the simulator's uniform coins. -/
theorem IAlg.acceptProb_simEnv_dropAssignments {SC : Type} [Fintype SC] {m : ℕ}
    (A : IAlg X Y Stmt Wit Proof m) (S : NARG.SimulatorFn X Y Stmt Proof SC) (Q : ℕ) :
    A.acceptProb (simEnv rel S.dropAssignments Q) =
      A.acceptProb (realEnv rel S.toProver S.coins Q) := by
  have hE : simEnv rel S.dropAssignments Q = realEnv rel (Wit := Wit) S.toProver S.coins Q := by
    rw [simEnv, realEnv]
    congr 1
    funext ω i req H
    by_cases h : rel req.stmt req.wit
    · rw [ite_eq_left h, ite_eq_left h]
      rfl
    · rw [ite_eq_right h, ite_eq_right h]
  rw [hE]

end GordieHowe.ROM.NIZK
