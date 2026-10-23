-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.ROM.SaltedZK

@[expose] public section

/-!
# Everlasting zero knowledge of a salted argument in the classical random-oracle model

`GordieHowe/Model/ROM/SaltedZK.lean` charges an adversary for every query of its steps (`IAlg.Budget t`). The
paper's everlasting zero knowledge (Definition 6.2, `def:narg-zk-post`) charges only the queries
before the adversary's last proof query, whose position is chosen at run time: `IAlg.RequestBudget t`,
at most `t` queries before each proof query, on every run. This file proves the same bound under it.

**The argument.** Only the bad event of a hybrid step changes. A query of the run before proof query
`j` that carries proof query `j`'s salt is charged only if it is among the run's first `t` queries
(`StepHitWithin`). If the first such query comes after `t` queries, the run has made more than `t`
queries, so by the request budget it makes no further proof query: proof query `j` is made neither in the
run nor in the relabelled runs that agree with it up to that query (`run_coupling` up to it), so
both sides of the hybrid step are `0` (`step_pointwise_requestBudget`). At most `t` steps are among
the first `t` queries, so the bad event has probability at most `(t + j) / |Sd|` as before.

- `IAlg.RequestBudget`, `IAlg.Budget.requestBudget`.
- `GordieHowe.ROM.NIZK.EverlastingZeroKnowledge`, and `GordieHowe.ROM.NIZK.everlastingZeroKnowledge_of_sliceCloseAt` with
  the error of `zeroKnowledge_of_sliceCloseAt`.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.ROM.NIZK

open GordieHowe.Quantum GordieHowe.QROM

variable {X Y Stmt Wit Proof : Type}

namespace IAlg

variable {m : ℕ} (A : IAlg X Y Stmt Wit Proof m)

/-- **The number of queries before step `k`** of the run of `A` against `R` from `O`. -/
def queriesBefore (R : Responder X Y Stmt Wit Proof) (O : X → Y) (k : ℕ) : ℕ :=
  ((range k).filter fun i => (A.next (A.run R O i).hist).IsQuery).card

theorem queriesBefore_succ (R : Responder X Y Stmt Wit Proof) (O : X → Y) (k : ℕ) :
    A.queriesBefore R O (k + 1) =
      A.queriesBefore R O k + if (A.next (A.run R O k).hist).IsQuery then 1 else 0 := by
  unfold queriesBefore
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun hk => by simp at hk)]
  · rfl

theorem queriesBefore_mono (R : Responder X Y Stmt Wit Proof) (O : X → Y) {k k' : ℕ}
    (h : k ≤ k') : A.queriesBefore R O k ≤ A.queriesBefore R O k' :=
  card_le_card fun i hi => by
    simp only [mem_filter, mem_range] at hi ⊢
    exact ⟨by omega, hi.2⟩

/-- **A budget of `t` queries before each proof query**: against every responder and every oracle, every
proof query of `A` comes after at most `t` queries of its run. The queries after the last proof query of a
run are not charged. -/
def RequestBudget (t : ℕ) : Prop :=
  ∀ R O, ∀ k < m, ∀ req, A.next (A.run R O k).hist = .request req → A.queriesBefore R O k ≤ t

variable {A}

/-- A budget of `t` queries is a budget of `t` queries before each proof query. -/
theorem Budget.requestBudget {t : ℕ} (h : A.Budget t) : A.RequestBudget t :=
  fun R O k hk _ _ => (A.queriesBefore_mono R O hk.le).trans (h R O)

/-- **No proof query after more than `t` queries**: if at step `k₁` the run has made at least `t`
queries, and has made at most `j` proof queries, then under a request budget of `t` it never
makes proof query `j`. -/
theorem RequestBudget.not_made {t : ℕ} (hA : A.RequestBudget t) {R : Responder X Y Stmt Wit Proof}
    {O : X → Y} {k₁ j : ℕ} {x : X} (hq : A.next (A.run R O k₁).hist = .query x)
    (ht : t ≤ A.queriesBefore R O k₁) (hn : (A.run R O k₁).nreq ≤ j) :
    ∀ k < m, ∀ req, (A.run R O k).nreq = j → A.next (A.run R O k).hist ≠ .request req := by
  intro k hk req hkn hr
  rcases lt_trichotomy k k₁ with hlt | heq | hgt
  · have := A.nreq_lt_of_request hr hlt
    omega
  · subst heq
    rw [hq] at hr
    cases hr
  · have h1 := hA R O k hk req hr
    have h2 := A.queriesBefore_mono R O (show k₁ + 1 ≤ k from hgt)
    rw [A.queriesBefore_succ, hq] at h2
    simp only [Action.IsQuery, ↓reduceIte] at h2
    omega

/-- The algorithm with another number of steps has the same runs. -/
theorem run_withSteps (m' : ℕ) (R : Responder X Y Stmt Wit Proof) (O : X → Y) :
    ∀ k, (⟨A.next, A.post⟩ : IAlg X Y Stmt Wit Proof m').run R O k = A.run R O k
  | 0 => rfl
  | k + 1 => by
    rw [IAlg.run_succ, IAlg.run_succ, run_withSteps m' R O k]
    rfl

end IAlg

/-- At most `t` steps are queries among the first `t` queries. -/
theorem card_filter_query_lt_le (N : ℕ → Action X Stmt Wit) (t K : ℕ) :
    ((range K).filter fun k => (N k).IsQuery ∧
      ((range k).filter fun i => (N i).IsQuery).card < t).card ≤ t := by
  classical
  suffices h : ∀ K, ((range K).filter fun k => (N k).IsQuery ∧
      ((range k).filter fun i => (N i).IsQuery).card < t).card ≤
        min t ((range K).filter fun i => (N i).IsQuery).card from (h K).trans (min_le_left _ _)
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    rw [range_add_one, filter_insert, filter_insert]
    by_cases hq : (N K).IsQuery
    · by_cases hc : ((range K).filter fun i => (N i).IsQuery).card < t
      · rw [if_pos ⟨hq, hc⟩, if_pos hq, card_insert_of_notMem (by simp),
          card_insert_of_notMem (by simp)]
        omega
      · rw [if_neg fun h => hc h.2, if_pos hq, card_insert_of_notMem (by simp)]
        omega
    · rw [if_neg fun h => hq h.1, if_neg hq]
      exact ih

section Notion

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] (rel : Stmt → Wit → Prop)
  [DecidableRel rel] {Coins SimCoins : Type} [Fintype Coins] [Fintype SimCoins]

/-- **Everlasting zero knowledge in the classical random-oracle model** (Unruh 2017
Definition 6, p. 14, with classical adversaries and the query bound of the paper's Definition 6.2,
`def:narg-zk-post`): for all `m`, `T`, `t` and `Q`, every classical adversary with `m` steps whose
algorithms make at most `t` queries before each of their proof queries on every run
(`IAlg.RequestBudget`), and any number after the last one, whose first `Q` proof queries are answered,
has advantage at most `ε t Q` between the honest prover `P` and the simulator `S`. The total budget
`T` of the adversary is not charged. -/
def EverlastingZeroKnowledge (P : NARG.ProverFn X Y Stmt Wit Proof Coins)
    (S : NARG.SimulatorFn X Y Stmt Proof SimCoins) (ε : ℕ → ℕ → ℝ) : Prop :=
  ∀ (m T t Q : ℕ) (𝒜 : Adversary X Y Stmt Wit Proof m T), (∀ r, (𝒜.alg r).RequestBudget t) →
    𝒜.advantage rel P S Q ≤ ε t Q

variable {rel}

/-- A larger error bound. -/
theorem EverlastingZeroKnowledge.mono {P : NARG.ProverFn X Y Stmt Wit Proof Coins}
    {S : NARG.SimulatorFn X Y Stmt Proof SimCoins} {ε ε' : ℕ → ℕ → ℝ}
    (h : EverlastingZeroKnowledge rel P S ε) (hε : ∀ t Q, ε t Q ≤ ε' t Q) :
    EverlastingZeroKnowledge rel P S ε' :=
  fun m T t Q 𝒜 h𝒜 => (h m T t Q 𝒜 h𝒜).trans (hε t Q)

end Notion

section Salted

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] {Sd C SC : Type} [Fintype Sd]
  [DecidableEq Sd] [Nonempty Sd] [Fintype C] [Nonempty C] [Fintype SC] [Nonempty SC]
  (saltOf : X → Option Sd) (rel : Stmt → Wit → Prop) [DecidableRel rel]
  (P : NARG.ProverFn X Y Stmt Wit Proof (SaltedCoins Sd C)) (S : NARG.SimulatorFn X Y Stmt Proof (SaltedCoins Sd SC))

/-- **One of the first `t` queries hits the salt of proof query `j`**: among the steps of the run of
`baseResp j ω` that come after fewer than `t` queries, a query carries the salt of proof query `j`. -/
def StepHitWithin {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) (t : ℕ) {Q : ℕ} {j : ℕ} (hj : j < Q)
    (ω : Tape X Y Sd C SC Q) : Prop :=
  ∃ k < m, A.queriesBefore (baseResp rel P S j ω) ω.oracle k < t ∧
    ∃ x, A.next (A.run (baseResp rel P S j ω) ω.oracle k).hist = .query x ∧
      saltOf x = some (ω.salts ⟨j, hj⟩)

open Classical in
/-- **One of the first `t` queries among `m` steps hits a uniform salt** with probability at most
`t / |Sd|`. -/
theorem expect_ite_exists_query_within_le (N : ℕ → Action X Stmt Wit) (m t : ℕ) :
    𝔼 a : Sd, (if ∃ k < m, ((range k).filter fun i => (N i).IsQuery).card < t ∧
        ∃ x, N k = .query x ∧ saltOf x = some a then (1 : ℝ) else 0) ≤ t / Fintype.card Sd := by
  classical
  set c : ℕ → Prop := fun k => ((range k).filter fun i => (N i).IsQuery).card < t
  have h1 : ∀ a : Sd, (if ∃ k < m, c k ∧ ∃ x, N k = .query x ∧ saltOf x = some a then (1 : ℝ)
      else 0) ≤ ∑ k ∈ range m, if c k ∧ ∃ x, N k = .query x ∧ saltOf x = some a then (1 : ℝ)
        else 0 := fun a => by
    have := ite_exists_le_sum (range m) (fun k => c k ∧ ∃ x, N k = .query x ∧ saltOf x = some a)
    simp only [Finset.mem_range] at this
    exact this
  have h2 : ∀ k, 𝔼 a : Sd, (if c k ∧ ∃ x, N k = .query x ∧ saltOf x = some a then (1 : ℝ)
      else 0) ≤ if (N k).IsQuery ∧ c k then (1 : ℝ) / Fintype.card Sd else 0 := fun k => by
    by_cases hc : c k
    · cases hN : N k with
      | query x =>
        simp only [hc, true_and, Action.query.injEq, exists_eq_left', Action.IsQuery, and_true,
          if_true]
        exact expect_ite_eq_some_le (saltOf x)
      | request req => simp [Action.IsQuery]
    · simp [hc]
  calc 𝔼 a : Sd, (if ∃ k < m, c k ∧ ∃ x, N k = .query x ∧ saltOf x = some a then (1 : ℝ) else 0)
      ≤ 𝔼 a : Sd, ∑ k ∈ range m, (if c k ∧ ∃ x, N k = .query x ∧ saltOf x = some a then (1 : ℝ)
          else 0) := Finset.expect_le_expect fun a _ => h1 a
    _ = ∑ k ∈ range m, 𝔼 a : Sd, (if c k ∧ ∃ x, N k = .query x ∧ saltOf x = some a then (1 : ℝ)
          else 0) := Finset.expect_sum_comm _ _ _
    _ ≤ ∑ k ∈ range m, if (N k).IsQuery ∧ c k then 1 / (Fintype.card Sd : ℝ) else 0 :=
        Finset.sum_le_sum fun k _ => h2 k
    _ = ((range m).filter fun k => (N k).IsQuery ∧ c k).card / Fintype.card Sd := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one_div]
    _ ≤ t / Fintype.card Sd := by
        gcongr
        exact_mod_cast card_filter_query_lt_le N t m

/-- **The bad events of step `j` before the last proof query** have probability at most
`(t + j) / |Sd|`, for any algorithm: one of the first `t` queries of the run before proof query `j`
reads proof query `j`'s salt, or an earlier proof query drew it. -/
theorem expect_ite_bad_within_le {m : ℕ} (A : IAlg X Y Stmt Wit Proof m) (t : ℕ) {Q j : ℕ}
    (hj : j < Q) [DecidablePred (fun ω : Tape X Y Sd C SC Q =>
      StepHitWithin saltOf rel P S A t hj ω ∨ StepColl hj ω)] :
    𝔼 ω : Tape X Y Sd C SC Q,
        (if StepHitWithin saltOf rel P S A t hj ω ∨ StepColl hj ω then (1 : ℝ) else 0) ≤
      (t + j) / Fintype.card Sd := by
  classical
  rw [← Tape.expect_updSalt ⟨j, hj⟩]
  set N : Tape X Y Sd C SC Q → ℕ → Action X Stmt Wit := fun ω k =>
    A.next (A.run (baseResp rel P S j ω) ω.oracle k).hist
  have hpt : ∀ (ω : Tape X Y Sd C SC Q) (a : Sd),
      (if StepHitWithin saltOf rel P S A t hj (ω.updSalt ⟨j, hj⟩ a) ∨
          StepColl hj (ω.updSalt ⟨j, hj⟩ a) then (1 : ℝ) else 0) ≤
      (if ∃ k < m, ((range k).filter fun i => (N ω i).IsQuery).card < t ∧
          ∃ x, N ω k = .query x ∧ saltOf x = some a then (1 : ℝ) else 0) +
        (if ∃ i : Fin Q, (i : ℕ) < j ∧ ω.salts i = a then (1 : ℝ) else 0) := by
    intro ω a
    have hH : StepHitWithin saltOf rel P S A t hj (ω.updSalt ⟨j, hj⟩ a) ↔
        ∃ k < m, ((range k).filter fun i => (N ω i).IsQuery).card < t ∧
          ∃ x, N ω k = .query x ∧ saltOf x = some a := by
      have ho : (ω.updSalt ⟨j, hj⟩ a).oracle = ω.oracle := rfl
      have hs : (ω.updSalt ⟨j, hj⟩ a).salts ⟨j, hj⟩ = a := by simp [Tape.updSalt]
      unfold StepHitWithin IAlg.queriesBefore
      rw [baseResp_updSalt, ho, hs]
    have hC : StepColl hj (ω.updSalt ⟨j, hj⟩ a) ↔ ∃ i : Fin Q, (i : ℕ) < j ∧ ω.salts i = a := by
      unfold StepColl
      refine exists_congr fun i => and_congr_right fun hi => ?_
      have hne : i ≠ ⟨j, hj⟩ := fun e => by rw [e] at hi; exact lt_irrefl _ hi
      simp [Tape.updSalt, Function.update_of_ne hne]
    rw [if_congr (or_congr hH hC) rfl rfl]
    split_ifs <;> simp_all
  calc 𝔼 ω : Tape X Y Sd C SC Q, 𝔼 a : Sd,
        (if StepHitWithin saltOf rel P S A t hj (ω.updSalt ⟨j, hj⟩ a) ∨
          StepColl hj (ω.updSalt ⟨j, hj⟩ a) then (1 : ℝ) else 0)
      ≤ 𝔼 ω : Tape X Y Sd C SC Q, 𝔼 a : Sd,
          ((if ∃ k < m, ((range k).filter fun i => (N ω i).IsQuery).card < t ∧
              ∃ x, N ω k = .query x ∧ saltOf x = some a then (1 : ℝ) else 0) +
            (if ∃ i : Fin Q, (i : ℕ) < j ∧ ω.salts i = a then (1 : ℝ) else 0)) :=
        Finset.expect_le_expect fun ω _ => Finset.expect_le_expect fun a _ => hpt ω a
    _ ≤ 𝔼 _ω : Tape X Y Sd C SC Q, ((t : ℝ) / Fintype.card Sd + j / Fintype.card Sd) := by
        refine Finset.expect_le_expect fun ω _ => ?_
        rw [Finset.expect_add_distrib]
        exact add_le_add (expect_ite_exists_query_within_le saltOf (N ω) m t)
          (expect_ite_exists_salt_le ω.salts j)
    _ = (t + j) / Fintype.card Sd := by rw [Fintype.expect_const, add_div]

variable {saltOf rel P S}

/-- **One hybrid step, pointwise, without a query of the salt before proof query `j`**: unless a
query of the run before proof query `j` or an earlier proof query has the salt of proof query `j`, the difference of the outputs of hybrids `j` and `j + 1` from the oracle
with that salt's slice answered by `F` is the difference of the outputs from the original oracle
when proof query `j` is answered with that slice by the prover and by the simulator. -/
theorem step_pointwise_of_noHit (hloc : SaltedLocal saltOf P S) {m : ℕ} (A : IAlg X Y Stmt Wit Proof m)
    {Q j : ℕ} (hj : j < Q) (ω : Tape X Y Sd C SC Q) (F : X → Y)
    (hH : ∀ k < m, ∀ x, (A.run (baseResp rel P S j ω) ω.oracle k).nreq ≤ j →
      A.next (A.run (baseResp rel P S j ω) ω.oracle k).hist = .query x →
        saltOf x ≠ some (ω.salts ⟨j, hj⟩)) (hC : ¬ StepColl hj ω) :
    ind (A.accepts (hybResp rel P S j ω) (replaceSlice saltOf (ω.salts ⟨j, hj⟩) ω.oracle F)) -
        ind (A.accepts (hybResp rel P S (j + 1) ω)
          (replaceSlice saltOf (ω.salts ⟨j, hj⟩) ω.oracle F)) =
      ind (A.accepts (override (hybResp rel P S j ω) j
          (realReplyAt saltOf rel P (ω.salts ⟨j, hj⟩) ⟨ω.proverCoins ⟨j, hj⟩, F⟩)) ω.oracle) -
        ind (A.accepts (override (hybResp rel P S j ω) j
          (simReplyAt saltOf rel S (ω.salts ⟨j, hj⟩) ⟨ω.simCoins ⟨j, hj⟩, F⟩)) ω.oracle) := by
  classical
  set σ := ω.salts ⟨j, hj⟩ with hσ
  set H := ω.oracle
  set R₁ := hybResp rel P S j ω with hR₁
  set R₁' := hybResp rel P S (j + 1) ω with hR₁'
  set gP := realReplyAt saltOf rel P σ ⟨ω.proverCoins ⟨j, hj⟩, F⟩
  set gS := simReplyAt saltOf rel S σ ⟨ω.simCoins ⟨j, hj⟩, F⟩
  have hcol : ∀ i : Fin Q, (i : ℕ) < j → ω.salts i ≠ σ := fun i hi e => hC ⟨i, hi, e⟩
  have hlt : ∀ i < j, ∀ req O,
      (R₁ i req (replaceSlice saltOf σ O F)).response = (R₁ i req O).response ∧
        (R₁ i req (replaceSlice saltOf σ O F)).state = replaceSlice saltOf σ (R₁ i req O).state F :=
    fun i hi req O => hybResp_replaceSlice hloc ω hcol F hi req O
  have hlt' : ∀ i < j, ∀ req O,
      (R₁' i req (replaceSlice saltOf σ O F)).response = (R₁' i req O).response ∧
        (R₁' i req (replaceSlice saltOf σ O F)).state = replaceSlice saltOf σ (R₁' i req O).state F :=
    fun i hi req O => by
      rw [hR₁', hybResp_succ_of_ne rel P S ω hi.ne]
      exact hlt i hi req O
  have h12 : ∀ i, i ≠ j → override R₁ j gP i = R₁ i := fun i hi => override_of_ne _ _ hi
  have h12' : ∀ i, i ≠ j → override R₁ j gS i = R₁' i := fun i hi => by
    rw [override_of_ne _ _ hi, hR₁', hybResp_succ_of_ne rel P S ω hi]
  have hj1 : ∀ req O, override R₁ j gP j req O = R₁ j req (replaceSlice saltOf σ O F) := by
    intro req O
    rw [override_self]
    simp only [gP, realReplyAt, hR₁, hybResp, dif_pos hj, lt_irrefl, if_false]
    rfl
  have hj1' : ∀ req O, override R₁ j gS j req O = R₁' j req (replaceSlice saltOf σ O F) := by
    intro req O
    rw [override_self]
    simp only [gS, simReplyAt, hR₁', hybResp, dif_pos hj, Nat.lt_succ_self, if_true]
    rfl
  have hagree : ∀ g g' : ReplyFn X Y Stmt Wit Proof, ∀ i < j, override R₁ j g i = override R₁ j g' i :=
    fun g g' i hi => by rw [override_of_ne _ _ hi.ne, override_of_ne _ _ hi.ne]
  -- the runs before proof query `j` are the run of `baseResp`
  have hpre : ∀ (g : ReplyFn X Y Stmt Wit Proof) k, (A.run (override R₁ j g) H k).nreq ≤ j →
      A.run (baseResp rel P S j ω) H k = A.run (override R₁ j g) H k :=
    fun g => A.run_eq_of_forall_lt (hagree g refuseReply)
  have hpre₀ : ∀ (g : ReplyFn X Y Stmt Wit Proof) k, (A.run (baseResp rel P S j ω) H k).nreq ≤ j →
      A.run (override R₁ j g) H k = A.run (baseResp rel P S j ω) H k :=
    fun g => A.run_eq_of_forall_lt (hagree refuseReply g)
  have hq : ∀ g : ReplyFn X Y Stmt Wit Proof, ∀ k < m, ∀ x, (A.run (override R₁ j g) H k).nreq ≤ j →
      A.next (A.run (override R₁ j g) H k).hist = .query x → saltOf x ≠ some σ :=
    fun g k hk x hn hx e => hH k hk x (by rw [hpre g k hn]; exact hn) (by rw [hpre g k hn]; exact hx) e
  have C1 := run_coupling saltOf A h12 hlt hj1 (hq gP)
  have C2 := run_coupling saltOf A h12' hlt' hj1' (hq gS)
  by_cases hM : ∃ k < m, ∃ req, (A.run (baseResp rel P S j ω) H k).nreq = j ∧
      A.next (A.run (baseResp rel P S j ω) H k).hist = .request req
  · obtain ⟨k, hk, req, hn, hr⟩ := hM
    have fin : ∀ (g : ReplyFn X Y Stmt Wit Proof) (R : Responder X Y Stmt Wit Proof),
        (((A.run (override R₁ j g) H m).nreq ≤ j ∧
          SliceRel saltOf σ F (A.run R (replaceSlice saltOf σ H F) m) (A.run (override R₁ j g) H m)) ∨
        (j < (A.run (override R₁ j g) H m).nreq ∧
          A.run R (replaceSlice saltOf σ H F) m = A.run (override R₁ j g) H m)) →
        A.accepts R (replaceSlice saltOf σ H F) = A.accepts (override R₁ j g) H := by
      intro g R hC'
      rcases hC' with ⟨hn', -⟩ | ⟨-, heq⟩
      · have he := hpre₀ g k hn.le
        have hr' : A.next (A.run (override R₁ j g) H k).hist = .request req := by rw [he]; exact hr
        have := A.nreq_lt_of_request hr' hk
        rw [he, hn] at this
        omega
      · exact A.accepts_eq_of_run_eq heq
    rw [fin gP R₁ (C1 m le_rfl), fin gS R₁' (C2 m le_rfl)]
  · push Not at hM
    have ha' : A.accepts (override R₁ j gP) H = A.accepts (override R₁ j gS) H := by
      rw [A.accepts_override_eq_of_not_made R₁ H refuseReply gP hM,
        A.accepts_override_eq_of_not_made R₁ H refuseReply gS hM]
    have ha : A.accepts R₁ (replaceSlice saltOf σ H F) = A.accepts R₁' (replaceSlice saltOf σ H F) := by
      refine A.accepts_eq_of_run_eq (A.run_eq_of_forall_ne (j := j)
        (fun i hi => (hybResp_succ_of_ne rel P S ω hi).symm) (fun k hk req hn hr => ?_) m le_rfl)
      rcases C1 k hk.le with ⟨hn2, hrel⟩ | ⟨hlt2, heq⟩
      · have hn3 : (A.run (override R₁ j gP) H k).nreq = j := by rw [← hrel.nreq]; exact hn
        have hr3 : A.next (A.run (override R₁ j gP) H k).hist = .request req := by
          rw [← hrel.hist]; exact hr
        have he := hpre gP k hn3.le
        rw [← he] at hn3 hr3
        exact absurd hr3 (hM k hk req hn3)
      · rw [heq] at hn
        omega
    rw [ha, ha', sub_self, sub_self]

/-- **One hybrid step at a run that makes no further proof query**: under a request budget of `t`, if no
query among the first `t` of the run before proof query `j` and no earlier proof query has the salt of
proof query `j`, the pointwise identity of `step_pointwise` holds. If a query of the run before
proof query `j` has that salt, the first one comes after `t` queries; then neither the run of
`baseResp j ω` nor the relabelled runs, which agree with it up to that query, make proof query `j`,
and both sides are `0`. -/
theorem step_pointwise_requestBudget (hloc : SaltedLocal saltOf P S) {m t : ℕ}
    (A : IAlg X Y Stmt Wit Proof m) (hA : A.RequestBudget t) {Q j : ℕ} (hj : j < Q)
    (ω : Tape X Y Sd C SC Q) (F : X → Y)
    (hH : ¬ StepHitWithin saltOf rel P S A t hj ω) (hC : ¬ StepColl hj ω) :
    ind (A.accepts (hybResp rel P S j ω) (replaceSlice saltOf (ω.salts ⟨j, hj⟩) ω.oracle F)) -
        ind (A.accepts (hybResp rel P S (j + 1) ω)
          (replaceSlice saltOf (ω.salts ⟨j, hj⟩) ω.oracle F)) =
      ind (A.accepts (override (hybResp rel P S j ω) j
          (realReplyAt saltOf rel P (ω.salts ⟨j, hj⟩) ⟨ω.proverCoins ⟨j, hj⟩, F⟩)) ω.oracle) -
        ind (A.accepts (override (hybResp rel P S j ω) j
          (simReplyAt saltOf rel S (ω.salts ⟨j, hj⟩) ⟨ω.simCoins ⟨j, hj⟩, F⟩)) ω.oracle) := by
  classical
  set σ := ω.salts ⟨j, hj⟩ with hσ
  set H := ω.oracle
  set B := baseResp rel P S j ω with hB
  by_cases hhit : ∃ k < m, (A.run B H k).nreq ≤ j ∧
      ∃ x, A.next (A.run B H k).hist = .query x ∧ saltOf x = some σ
  swap
  · exact step_pointwise_of_noHit hloc A hj ω F
      (fun k hk x hn hx e => hhit ⟨k, hk, hn, x, hx, e⟩) hC
  set R₁ := hybResp rel P S j ω with hR₁
  set R₁' := hybResp rel P S (j + 1) ω with hR₁'
  set H' := replaceSlice saltOf σ H F
  let p : ℕ → Prop := fun k => k < m ∧ (A.run B H k).nreq ≤ j ∧
    ∃ x, A.next (A.run B H k).hist = .query x ∧ saltOf x = some σ
  have hex : ∃ k, p k := by
    obtain ⟨k, hk, h⟩ := hhit
    exact ⟨k, hk, h⟩
  obtain ⟨hk₁m, hk₁n, x₁, hx₁, -⟩ := Nat.find_spec hex
  have hmin : ∀ k < Nat.find hex, ¬ p k := fun k hk => Nat.find_min hex hk
  set k₁ := Nat.find hex
  have ht : t ≤ A.queriesBefore B H k₁ := by
    by_contra hlt
    obtain ⟨-, -, x, hx, hs⟩ := Nat.find_spec hex
    exact hH ⟨k₁, hk₁m, not_le.1 hlt, x, hx, hs⟩
  -- the right side: proof query `j` is not made in the base run
  have hNB := hA.not_made hx₁ ht hk₁n
  have hR : ∀ g, A.accepts (override R₁ j g) H = A.accepts B H := fun g =>
    A.accepts_override_eq_of_not_made R₁ H refuseReply g hNB
  rw [hR, hR, sub_self]
  -- the left side: the relabelled run agrees with the base run up to step `k₁`
  set σc := ω.proverCoins ⟨j, hj⟩
  set gP := realReplyAt saltOf rel P σ ⟨σc, F⟩
  have hcol : ∀ i : Fin Q, (i : ℕ) < j → ω.salts i ≠ σ := fun i hi e => hC ⟨i, hi, e⟩
  have hlt : ∀ i < j, ∀ req O,
      (R₁ i req (replaceSlice saltOf σ O F)).response = (R₁ i req O).response ∧
        (R₁ i req (replaceSlice saltOf σ O F)).state = replaceSlice saltOf σ (R₁ i req O).state F :=
    fun i hi req O => hybResp_replaceSlice hloc ω hcol F hi req O
  have h12 : ∀ i, i ≠ j → override R₁ j gP i = R₁ i := fun i hi => override_of_ne _ _ hi
  have hj1 : ∀ req O, override R₁ j gP j req O = R₁ j req (replaceSlice saltOf σ O F) := by
    intro req O
    rw [override_self]
    simp only [gP, realReplyAt, hR₁, hybResp, dif_pos hj, lt_irrefl, if_false]
    rfl
  have hagree : ∀ i < j, override R₁ j refuseReply i = override R₁ j gP i :=
    fun i hi => by rw [override_of_ne _ _ hi.ne, override_of_ne _ _ hi.ne]
  -- the run of `override R₁ j gP` is the base run up to step `k₁`
  have hnle : ∀ k ≤ k₁, (A.run B H k).nreq ≤ j := fun k hk =>
    (A.nreq_run_mono hk).trans hk₁n
  have hpre : ∀ k ≤ k₁, A.run (override R₁ j gP) H k = A.run B H k := fun k hk =>
    A.run_eq_of_forall_lt hagree k (hnle k hk)
  let A' : IAlg X Y Stmt Wit Proof k₁ := ⟨A.next, A.post⟩
  have hA'run : ∀ R O k, A'.run R O k = A.run R O k := fun R O k => IAlg.run_withSteps k₁ R O k
  have hq' : ∀ k < k₁, ∀ x, (A'.run (override R₁ j gP) H k).nreq ≤ j →
      A'.next (A'.run (override R₁ j gP) H k).hist = .query x → saltOf x ≠ some σ := by
    intro k hk x _ hx e
    change A.next (A'.run (override R₁ j gP) H k).hist = .query x at hx
    rw [hA'run, hpre k hk.le] at hx
    exact hmin k hk ⟨hk.trans hk₁m, hnle k hk.le, x, hx, e⟩
  have C1 := run_coupling saltOf A' h12 hlt hj1 hq'
  have hrel : ∀ k ≤ k₁, (A.run R₁ H' k).hist = (A.run B H k).hist ∧
      (A.run R₁ H' k).nreq = (A.run B H k).nreq := by
    intro k hk
    rcases C1 k hk with ⟨-, hs⟩ | ⟨hn, -⟩
    · rw [hA'run, hA'run, hpre k hk] at hs
      exact ⟨hs.hist, hs.nreq⟩
    · rw [hA'run, hpre k hk] at hn
      exact absurd (hnle k hk) (not_le.2 hn)
  have hqb : A.queriesBefore R₁ H' k₁ = A.queriesBefore B H k₁ := by
    unfold IAlg.queriesBefore
    congr 1
    exact filter_congr fun i hi => by
      rw [(hrel i (by simp at hi; omega)).1]
  have hx₁' : A.next (A.run R₁ H' k₁).hist = .query x₁ := by rw [(hrel k₁ le_rfl).1, hx₁]
  have hNL := hA.not_made (j := j) hx₁' (hqb ▸ ht) (by rw [(hrel k₁ le_rfl).2]; exact hk₁n)
  have hrun : A.run R₁ H' m = A.run R₁' H' m :=
    A.run_eq_of_forall_ne (fun i hi => (hybResp_succ_of_ne rel P S ω hi).symm)
      (fun k hk req hn hr => absurd hr (hNL k hk req hn)) m le_rfl
  rw [A.accepts_eq_of_run_eq hrun, sub_self]

/-- **One hybrid step under a request budget**: hybrids `j` and `j + 1` differ by at most
`(t + j) / |Sd| + 𝔼 H, η H` for an algorithm with a budget of `t` queries before each proof query. -/
theorem abs_hyb_sub_le_requestBudget [Fintype Proof] (hloc : SaltedLocal saltOf P S) {η : (X → Y) → ℝ}
    (hcl : SliceCloseAt saltOf rel P S η) {m t : ℕ} (A : IAlg X Y Stmt Wit Proof m)
    (hA : A.RequestBudget t) {Q j : ℕ} (hj : j < Q) :
    |hyb rel P S A Q j - hyb rel P S A Q (j + 1)| ≤ (t + j) / Fintype.card Sd + 𝔼 H, η H := by
  classical
  set J : Fin Q := ⟨j, hj⟩
  let a : Tape X Y Sd C SC Q → (X → Y) → ℝ := fun ω F =>
    ind (A.accepts (hybResp rel P S j ω) (replaceSlice saltOf (ω.salts J) ω.oracle F))
  let b : Tape X Y Sd C SC Q → (X → Y) → ℝ := fun ω F =>
    ind (A.accepts (hybResp rel P S (j + 1) ω) (replaceSlice saltOf (ω.salts J) ω.oracle F))
  let Φ : Tape X Y Sd C SC Q → ReplyFn X Y Stmt Wit Proof → ℝ := fun ω g =>
    ind (A.accepts (override (hybResp rel P S j ω) j g) ω.oracle)
  let a' : Tape X Y Sd C SC Q → (X → Y) → ℝ := fun ω F =>
    Φ ω (realReplyAt saltOf rel P (ω.salts J) ⟨ω.proverCoins J, F⟩)
  let b' : Tape X Y Sd C SC Q → (X → Y) → ℝ := fun ω F =>
    Φ ω (simReplyAt saltOf rel S (ω.salts J) ⟨ω.simCoins J, F⟩)
  let Bad : Tape X Y Sd C SC Q → Prop := fun ω => StepHitWithin saltOf rel P S A t hj ω ∨ StepColl hj ω
  have ha : hyb rel P S A Q j = 𝔼 ω, 𝔼 F, a ω F :=
    (expect_relabel saltOf hj fun ω => ind (A.accepts (hybResp rel P S j ω) ω.oracle)).symm
  have hb : hyb rel P S A Q (j + 1) = 𝔼 ω, 𝔼 F, b ω F :=
    (expect_relabel saltOf hj fun ω => ind (A.accepts (hybResp rel P S (j + 1) ω) ω.oracle)).symm
  have hpt : ∀ ω F, a ω F - b ω F =
      (if Bad ω then a ω F - b ω F else 0) + (if Bad ω then 0 else a' ω F - b' ω F) := by
    intro ω F
    by_cases h : Bad ω
    · simp [h]
    · rw [if_neg h, if_neg h, zero_add]
      exact step_pointwise_requestBudget hloc A hA hj ω F (fun h' => h (Or.inl h'))
        (fun h' => h (Or.inr h'))
  have hsplit : hyb rel P S A Q j - hyb rel P S A Q (j + 1) =
      𝔼 ω, 𝔼 F, (if Bad ω then a ω F - b ω F else 0) +
        𝔼 ω, 𝔼 F, (if Bad ω then 0 else a' ω F - b' ω F) := by
    rw [ha, hb, ← Finset.expect_sub_distrib]
    rw [← Finset.expect_add_distrib univ (fun ω => 𝔼 F, (if Bad ω then a ω F - b ω F else 0))
      (fun ω => 𝔼 F, (if Bad ω then 0 else a' ω F - b' ω F))]
    refine Finset.expect_congr rfl fun ω _ => ?_
    rw [← Finset.expect_sub_distrib,
      ← Finset.expect_add_distrib univ (fun F => if Bad ω then a ω F - b ω F else 0)
        (fun F => if Bad ω then 0 else a' ω F - b' ω F)]
    exact Finset.expect_congr rfl fun F _ => hpt ω F
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · -- the bad events
    calc |𝔼 ω, 𝔼 F, (if Bad ω then a ω F - b ω F else 0)|
        ≤ 𝔼 ω : Tape X Y Sd C SC Q, (if Bad ω then (1 : ℝ) else 0) := by
          refine (Finset.abs_expect_le _ _).trans (Finset.expect_le_expect fun ω _ => ?_)
          refine (Finset.abs_expect_le _ _).trans ?_
          by_cases h : Bad ω
          · simp only [h, if_true]
            exact (Finset.expect_le_expect fun F _ => abs_ind_sub_ind_le _ _).trans_eq
              (Fintype.expect_const (1 : ℝ))
          · simp [h]
      _ ≤ (t + j) / Fintype.card Sd := expect_ite_bad_within_le saltOf rel P S A t hj
  · -- the kernel step at the fixed salt, on the good event
    set f : Tape X Y Sd C SC Q → ℝ := fun ω => 𝔼 F, (if Bad ω then 0 else a' ω F - b' ω F)
    have hupd : ∀ ω : Tape X Y Sd C SC Q, ∀ (s : SC) (c : C),
        f ((ω.updSim J s).updProver J c) = if Bad ω then 0 else
          (𝔼 F, Φ ω (realReplyAt saltOf rel P (ω.salts J) ⟨c, F⟩) -
            𝔼 F, Φ ω (simReplyAt saltOf rel S (ω.salts J) ⟨s, F⟩)) := by
      intro ω s c
      have hΦ : ∀ g, Φ ((ω.updSim J s).updProver J c) g = Φ ω g := fun g => by
        simp only [Φ]
        rw [override_hybResp_updProver, override_hybResp_updSim]
        rfl
      have hBad : Bad ((ω.updSim J s).updProver J c) ↔ Bad ω := by
        simp only [Bad, StepHitWithin, IAlg.queriesBefore, StepColl]
        rw [baseResp_updProver, baseResp_updSim]
        rfl
      have hpc : ((ω.updSim J s).updProver J c).proverCoins J = c := by simp [Tape.updProver]
      have hsc : ((ω.updSim J s).updProver J c).simCoins J = s := by
        simp [Tape.updProver, Tape.updSim]
      have hs : ((ω.updSim J s).updProver J c).salts = ω.salts := rfl
      simp only [f, a', b', hΦ, hs, hpc, hsc]
      by_cases h : Bad ω
      · have h' : Bad ((ω.updSim J s).updProver J c) := hBad.2 h
        simp [h, h']
      · have h' : ¬ Bad ((ω.updSim J s).updProver J c) := fun h'' => h (hBad.1 h'')
        simp only [h, h', if_false, Finset.expect_sub_distrib]
    have hfresh : ∀ {Cx : Type} [Fintype Cx] [Nonempty Cx] (g : FreshSlice X Y Cx → ℝ),
        𝔼 c : Cx, 𝔼 F : X → Y, g ⟨c, F⟩ = 𝔼 a, g a := by
      intro Cx _ _ g
      rw [← expect_prod_eq (fun p : Cx × (X → Y) => g ⟨p.1, p.2⟩)]
      exact Fintype.expect_equiv (FreshSlice.equivProd X Y _).symm _ _ fun _ => rfl
    have hker : ∀ ω : Tape X Y Sd C SC Q,
        |𝔼 s : SC, 𝔼 c : C, f ((ω.updSim J s).updProver J c)| ≤ η ω.oracle := by
      intro ω
      simp_rw [hupd]
      by_cases h : Bad ω
      · simp only [h, if_true, Fintype.expect_const, abs_zero]
        exact hcl.nonneg _
      · simp only [h, if_false]
        have e : 𝔼 s : SC, 𝔼 c : C,
            (𝔼 F, Φ ω (realReplyAt saltOf rel P (ω.salts J) ⟨c, F⟩) -
              𝔼 F, Φ ω (simReplyAt saltOf rel S (ω.salts J) ⟨s, F⟩)) =
            𝔼 c : C, 𝔼 F, Φ ω (realReplyAt saltOf rel P (ω.salts J) ⟨c, F⟩) -
              𝔼 s : SC, 𝔼 F, Φ ω (simReplyAt saltOf rel S (ω.salts J) ⟨s, F⟩) := by
          simp only [Finset.expect_sub_distrib, Fintype.expect_const]
        rw [e, hfresh (fun a => Φ ω (realReplyAt saltOf rel P (ω.salts J) a)),
          hfresh (fun a => Φ ω (simReplyAt saltOf rel S (ω.salts J) a))]
        refine A.abs_expect_accepts_override_sub_le (hybResp rel P S j ω) ω.oracle j refuseReply
          (realReplyAt saltOf rel P (ω.salts J)) (simReplyAt saltOf rel S (ω.salts J))
          (hcl.nonneg _) fun k _ req _ _ => ?_
        refine (tvDist_replyAt_le saltOf rel P S hcl _ req _).trans_eq (hcl.congr _ _ ?_)
        refine A.agreeOffSalted_run (saltOf := saltOf) (fun i req' O => ?_) ω.oracle k
        by_cases hi : i = j
        · rw [hi, override_self]
          exact fun _ _ => rfl
        · rw [override_of_ne _ _ hi]
          exact agreeOffSalted_hybResp hloc j ω i req' O
    calc |𝔼 ω, f ω|
        = |𝔼 ω : Tape X Y Sd C SC Q, 𝔼 s : SC, 𝔼 c : C, f ((ω.updSim J s).updProver J c)| := by
          rw [← Tape.expect_updProver J f]
          rw [← Tape.expect_updSim J fun ω => 𝔼 c : C, f (ω.updProver J c)]
      _ ≤ 𝔼 ω : Tape X Y Sd C SC Q, η ω.oracle :=
          (Finset.abs_expect_le _ _).trans (Finset.expect_le_expect fun ω _ => hker ω)
      _ = 𝔼 H, η H := Tape.expect_oracle η

/-- **The hybrids from the real to the simulated game**: hybrids `0` and `Q` differ by at most
`Q t / |Sd| + Q (Q - 1) / (2 |Sd|) + Q · 𝔼 H, η H` for an algorithm with a budget of `t`
queries before each proof query. -/
theorem abs_hyb_zero_sub_le_requestBudget [Fintype Proof] (hloc : SaltedLocal saltOf P S) {η : (X → Y) → ℝ}
    (hcl : SliceCloseAt saltOf rel P S η) {m t : ℕ} (A : IAlg X Y Stmt Wit Proof m)
    (hA : A.RequestBudget t) (Q : ℕ) :
    |hyb rel P S A Q 0 - hyb rel P S A Q Q| ≤
      Q * t / Fintype.card Sd + Q * (Q - 1) / (2 * Fintype.card Sd) + Q * 𝔼 H, η H := by
  rw [← Finset.sum_range_sub' (fun j => hyb rel P S A Q j), ← sum_range_stepError]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  exact abs_hyb_sub_le_requestBudget hloc hcl A hA (Finset.mem_range.1 hj)

/-- **Everlasting zero knowledge of a salted argument in the classical random-oracle
model.** For a prover and a simulator local in their salt (`hloc`) whose real and simulated slice
laws are within `η H` at every salt (`hcl`), every classical adversary with a budget of `t` queries
before each proof query and `Q` proof queries answered has advantage at most

    Q t / |Sd| + Q (Q - 1) / (2 |Sd|) + Q · 𝔼 H, η H

between the honest prover `P` and the simulator `S`, unbounded after its steps. -/
theorem everlastingZeroKnowledge_of_sliceCloseAt [Fintype Proof] (hloc : SaltedLocal saltOf P S)
    {η : (X → Y) → ℝ} (hcl : SliceCloseAt saltOf rel P S η) :
    EverlastingZeroKnowledge rel P S fun t Q =>
      Q * t / Fintype.card Sd + Q * (Q - 1) / (2 * Fintype.card Sd) + Q * 𝔼 H, η H := by
  intro m T t Q 𝒜 h𝒜
  refine 𝒜.abs_acceptProb_sub_le _ _ fun r => ?_
  rw [toReal_acceptProb_realEnv (S := S) (𝒜.alg r) hloc.coins_eq,
    toReal_acceptProb_simEnv (P := P) (𝒜.alg r)]
  exact abs_hyb_zero_sub_le_requestBudget hloc hcl (𝒜.alg r) (h𝒜 r) Q

end Salted

end GordieHowe.ROM.NIZK
