-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.O2H.SaltReprogram
public import GordieHowe.Model.Quantum.O2H.LabelBlocks

@[expose] public section

/-!
# Search in the QROM over the whole run of a game

The oracle `H : X → Y` has values split as `e : Y ≃ Y₁ × Y₂`, and points labelled by
`κ : X → Option L` (`GordieHowe/Model/Quantum/O2H/LabelBlocks.lean`). A label `l` is **hit** by
`H` when its block, the base components of `H` at the points of label `l`, satisfies a predicate
`P l`; every label is hit with probability at most `ε`. Requests carry labels
`lab : Req → Option L`. A distinguisher with a budget of `q` query slots of `n` parallel queries
plays against an environment on the tape `(H, c)`, `H ← μH` and `c ← ζ` independently, whose
oracle in force is `H` at every log and whose answers do not change when only the blocks of `H`
change. The event is that the final state lies in a set `Acc` with logs in which one of the first
`Q` logged requests has a hit label (`searchLogs`). Its probability is at most
`(√Q + 2 q √n)² ε` (`Distinguisher.eventProb_searchLogs_le`); for `n q ≤ t`, at most
`(√Q + 2 t)² ε` (`Distinguisher.eventProb_searchLogs_le_of_mul_le`).

**The proof** (one-way to hiding, AHU19 Theorem 3, square-root form, through
`Distinguisher.abs_sqrt_eventProb_sub_le_of_fresh_secret_budget`). The law of `H` is uniform on the
labels (`IsUniformOnLabels`), so the blocks of `H` may be replaced by uniform blocks `u`
(`IsUniformOnLabels.sum_mul_eq`), and uniform blocks are the mixture `mixBlocks P a σ` of `a`
uniform on the unmarked blocks and `σ` uniform (`sum_unmarkedLaw_mixBlocks`). For the rest `H₀` of
the oracle fixed, run the game on the tape `((a, c), σ)` against the oracle with blocks
`mixBlocks P a σ` and against the oracle `G` with blocks `a`. The answers are the same, and the
oracles differ only at the points of the labels where the block of `σ` is marked, a set `T σ` that
contains a given point with probability at most `ε`. The game against `G` never reads `σ`, so the
square roots of the two probabilities differ by at most `2 q √(n ε)`. Against `G`, a hit label is
one where the block of `σ` is marked (`marked_of_mixBlocks`), and `σ` is independent of the logs,
so the event has probability at most `Q ε` (`sum_mul_prob_logsIn_le`,
`toReal_toOuterMeasure_searchLogs_le`). Hence the square root of the probability is at most
`√(Q ε) + 2 q √(n ε)`.

- `searchLogs lab hit Q`: the logs in which one of the first `Q` logged requests has a label `l`
  with `hit l`.
- `toReal_toOuterMeasure_searchLogs_le`: for labels hit with probability at most `ε` each, given
  logs are in `searchLogs` with probability at most `Q ε` (the union bound).
- `sum_mul_prob_logsIn_le`: for log sets `Lσ σ` drawn so that every log lies in `Lσ σ` with
  probability at most `δ`, the averaged probability of measuring logs in `Lσ σ` is at most
  `δ ‖ψ‖²`.
- `mul_sqrt_le_of_mul_le`: `q √n ≤ t` for `n q ≤ t`.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

/-! ### The logs of a search -/

section Logs

variable {Req L : Type*} {m : ℕ}

/-- **The logs of a successful search**: one of the first `Q` logged requests has a label `l`
with `hit l`. -/
def searchLogs (lab : Req → Option L) (hit : L → Prop) (Q : ℕ) : Set (LogReg Req m) :=
  {lg | ∃ req ∈ (requests lg).take Q, ∃ l, lab req = some l ∧ hit l}

/-- More hit labels give more logs. -/
theorem searchLogs_mono {lab : Req → Option L} {hit hit' : L → Prop} (h : ∀ l, hit l → hit' l)
    (Q : ℕ) : searchLogs (m := m) lab hit Q ⊆ searchLogs lab hit' Q := by
  rintro lg ⟨req, hreq, l, hl, hhit⟩
  exact ⟨req, hreq, l, hl, h l hhit⟩

/-- **The union bound for a search**: if each label is hit with probability at most `ε` under
`σ ← ν`, given logs are in `searchLogs lab (hit σ) Q` with probability at most `Q ε`. -/
theorem toReal_toOuterMeasure_searchLogs_le {R : Type*} (ν : PMF R) (lab : Req → Option L)
    (hit : R → L → Prop) (Q : ℕ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ l, (ν.toOuterMeasure {σ | hit σ l}).toReal ≤ ε) (lg : LogReg Req m) :
    (ν.toOuterMeasure {σ | lg ∈ searchLogs lab (hit σ) Q}).toReal ≤ Q * ε := by
  set rs := (requests lg).take Q
  have hfin : ∀ t, ν.toOuterMeasure t ≠ ⊤ := fun t =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one ν t)
  have hsub : {σ | lg ∈ searchLogs lab (hit σ) Q} ⊆
      ⋃ j : Fin rs.length, {σ | ∃ l, lab rs[j] = some l ∧ hit σ l} := by
    rintro σ ⟨req, hreq, l, hl, hhit⟩
    obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hreq
    refine Set.mem_iUnion.2 ⟨⟨j, hj⟩, l, ?_, hhit⟩
    show lab rs[j] = some l
    rw [hjeq]
    exact hl
  have hone : ∀ j : Fin rs.length,
      (ν.toOuterMeasure {σ | ∃ l, lab rs[j] = some l ∧ hit σ l}).toReal ≤ ε := by
    intro j
    cases hl : lab rs[j] with
    | none => simpa [hl] using hε0
    | some l =>
      have : {σ | ∃ l', some l = some l' ∧ hit σ l'} = {σ | hit σ l} := by
        ext σ
        simp
      rw [this]
      exact hε l
  calc (ν.toOuterMeasure {σ | lg ∈ searchLogs lab (hit σ) Q}).toReal
      ≤ (ν.toOuterMeasure (⋃ j : Fin rs.length, {σ | ∃ l, lab rs[j] = some l ∧ hit σ l})).toReal :=
        ENNReal.toReal_mono (hfin _) (ν.toOuterMeasure.mono hsub)
    _ ≤ ∑ j : Fin rs.length, (ν.toOuterMeasure {σ | ∃ l, lab rs[j] = some l ∧ hit σ l}).toReal :=
        ν.toReal_toOuterMeasure_iUnion_le _
    _ ≤ ∑ _j : Fin rs.length, ε := sum_le_sum fun j _ => hone j
    _ = rs.length * ε := by simp
    _ ≤ Q * ε := by
        gcongr
        exact_mod_cast List.length_take_le Q _

variable {W X Y A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A] {n : ℕ}

/-- **Measuring the logs against a secret log set**: if every log lies in `Lσ σ` with probability
at most `δ` under `σ ← ν`, the average over `σ` of the probability of measuring logs in `Lσ σ` is at
most `δ ‖ψ‖²`. -/
theorem sum_mul_prob_logsIn_le {R : Type*} [Fintype R] (ν : PMF R) (Lσ : R → Set (LogReg Req m))
    (ψ : QState (GameReg W n X Y Req A m)) {δ : ℝ}
    (h : ∀ lg, (ν.toOuterMeasure {σ | lg ∈ Lσ σ}).toReal ≤ δ) :
    ∑ σ, (ν σ).toReal * prob (logsIn (Lσ σ)) ψ ≤ δ * ‖ψ‖ ^ 2 := by
  classical
  set g : GameReg W n X Y Req A m → LogReg Req m := fun r => (splitLogs r).2
  set p : LogReg Req m → ℝ := fun lg => prob (g ⁻¹' {lg}) ψ
  have hsplit : ∀ L : Set (LogReg Req m), prob (logsIn L) ψ = ∑ lg, if lg ∈ L then p lg else 0 :=
    fun L => by
      rw [show logsIn L = g ⁻¹' L from rfl, prob_preimage, sum_filter]
  calc ∑ σ, (ν σ).toReal * prob (logsIn (Lσ σ)) ψ
      = ∑ lg, p lg * (ν.toOuterMeasure {σ | lg ∈ Lσ σ}).toReal := by
        simp only [hsplit, mul_sum, PMF.toReal_toOuterMeasure_apply, Set.mem_ofPred_eq]
        rw [sum_comm]
        refine sum_congr rfl fun lg _ => sum_congr rfl fun σ _ => ?_
        split_ifs <;> ring
    _ ≤ ∑ lg, p lg * δ :=
        sum_le_sum fun lg _ => mul_le_mul_of_nonneg_left (h lg) (prob_nonneg _ _)
    _ = δ * ‖ψ‖ ^ 2 := by rw [← sum_mul, sum_prob_fiber, mul_comm]

end Logs

/-- `q √n ≤ t` for `n q ≤ t`. -/
theorem mul_sqrt_le_of_mul_le {n q t : ℕ} (h : n * q ≤ t) : (q : ℝ) * √(n : ℝ) ≤ t := by
  have hn : √(n : ℝ) ≤ n := by
    have h1 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow two_ne_zero n
    exact (Real.sqrt_le_sqrt h1).trans_eq (Real.sqrt_sq (Nat.cast_nonneg n))
  have ht : (n : ℝ) * q ≤ t := by exact_mod_cast h
  calc (q : ℝ) * √(n : ℝ) ≤ q * n := by gcongr
    _ ≤ t := by rw [mul_comm]; exact ht

/-! ### The search bound -/

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} {D : Distinguisher W X Y Req A n m} {q : ℕ}
  [DecidableEq Req] [DecidableEq A] [AddGroup Y] {Q : ℕ} {C : Type*} [Fintype C]
  {Y₁ Y₂ L : Type*} [DecidableEq X] [Fintype L] [DecidableEq L] [Fintype Y₁] [DecidableEq Y₁]
  {e : Y ≃ Y₁ × Y₂} {κ : X → Option L}

/-- **Search over the whole run of a game, in the QROM** (module docstring; our statement, proved
by one-way to hiding, AHU19 Theorem 3, square-root form). A distinguisher with a budget of `q`
query slots of `n` parallel queries plays against an environment `E` on the tape `(H, c)` with
`H ← μH` uniform on the labels and `c ← ζ` independent (`hμ`, `hμH`), whose oracle in force is `H`
at every log (`horacle`) and whose answers do not change when only the blocks of `H` change
(`hans`). If each label `l` is hit, `P l` of the block of `H` at `l`, with probability at most `ε`
(`hε`), the final state lies in `Acc` with logs in which one of the first `Q` logged requests has a
hit label with probability at most `(√Q + 2 q √n)² ε`. -/
theorem eventProb_searchLogs_le (bud : D.Budget q) (E : Env ((X → Y) × C) Req A X Y Q)
    {μH : PMF (X → Y)} {ζ : PMF C} (hμ : ∀ H c, E.μ (H, c) = μH H * ζ c)
    (hμH : IsUniformOnLabels e κ μH) (horacle : ∀ ω rs, E.oracleIn ω rs = ω.1)
    (hans : ∀ H H' c rs req, AgreeOffLabels e κ H H' →
      E.answerAfter (H, c) rs req = E.answerAfter (H', c) rs req)
    (P : (l : L) → ({x // κ x = some l} → Y₁) → Prop) [∀ l, DecidablePred (P l)]
    (lab : Req → Option L) (Acc : Set (GameReg W n X Y Req A m)) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ l, (μH.toOuterMeasure {H | P l (labelBlocks e κ H l)}).toReal ≤ ε) :
    D.eventProb E noPost
        (fun ω => Acc ∩ logsIn (searchLogs lab (fun l => P l (labelBlocks e κ ω.1 l)) Q)) ≤
      (√Q + 2 * q * √n) ^ 2 * ε := by
  classical
  set S : (X → Y) × C → Set (GameReg W n X Y Req A m) :=
    fun ω => Acc ∩ logsIn (searchLogs lab (fun l => P l (labelBlocks e κ ω.1 l)) Q)
  set b : ℝ := √(Q * ε) + 2 * q * √(n * ε)
  have hb : b ^ 2 = (√Q + 2 * q * √n) ^ 2 * ε := by
    simp only [b]
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_mul (Nat.cast_nonneg _)]
    rw [show √(Q : ℝ) * √ε + 2 * q * (√(n : ℝ) * √ε) = (√Q + 2 * q * √n) * √ε by ring, mul_pow,
      Real.sq_sqrt hε0]
  set F : (X → Y) × C → ℝ := fun ω => prob (S ω) (D.final E noPost ω)
  set f : (X → Y) → ℝ := fun H => ∑ c, (ζ c).toReal * F (H, c)
  have h1 : D.eventProb E noPost S = ∑ H, (μH H).toReal * f H := by
    unfold eventProb
    rw [Fintype.sum_prod_type]
    simp_rw [hμ, ENNReal.toReal_mul, mul_assoc, ← mul_sum]
    rfl
  -- the bound for each rest `H₀` of the oracle
  have hper : ∀ H₀, 𝔼 u, f (setLabelBlocks e κ H₀ u) ≤ b ^ 2 := by
    intro H₀
    have : Nonempty (LabelBlocks κ Y₁) := ⟨labelBlocks e κ H₀⟩
    set B := LabelBlocks κ Y₁
    set μV : PMF (B × C) := prodLaw (unmarkedLaw P) ζ
    set ν : PMF B := PMF.uniformOfFintype B
    set μ' : PMF ((B × C) × B) := prodLaw μV ν
    set τ₁ : (B × C) × B → (X → Y) × C :=
      fun ω' => (setLabelBlocks e κ H₀ (mixBlocks P ω'.1.1 ω'.2), ω'.1.2)
    set τ₂ : (B × C) × B → (X → Y) × C := fun ω' => (setLabelBlocks e κ H₀ ω'.1.1, ω'.1.2)
    set E₁ := E.comap μ' τ₁
    set E₂ := E.comap μ' τ₂
    set T : B → Set X := fun σ => {x | ∃ l, κ x = some l ∧ P l (σ l)}
    have hνP : ∀ l, (ν.toOuterMeasure {σ | P l (σ l)}).toReal ≤ ε := fun l => by
      rw [hμH.toReal_uniform_eq]
      exact hε l
    have hμ'apply : ∀ a c σ, (μ' ((a, c), σ)).toReal =
        (unmarkedLaw P a).toReal * ((ζ c).toReal * (ν σ).toReal) := fun a c σ => by
      simp only [μ', μV, prodLaw_apply, ENNReal.toReal_mul]
      ring
    -- the game against the mixed oracle is the uniform average
    have hP1 : D.eventProb E₁ noPost (S ∘ τ₁) = 𝔼 u, f (setLabelBlocks e κ H₀ u) := by
      rw [← sum_unmarkedLaw_mixBlocks (P := P) (fun u => f (setLabelBlocks e κ H₀ u))]
      unfold eventProb
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      refine sum_congr rfl fun a _ => ?_
      change ∑ c, ∑ σ, (μ' ((a, c), σ)).toReal * F (τ₁ ((a, c), σ)) = _
      simp only [hμ'apply, f, mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun σ _ => sum_congr rfl fun c _ => by ring
    -- the game against the oracle with the unmarked blocks finds a marked block of `σ`
    have hP2 : D.eventProb E₂ noPost (S ∘ τ₁) ≤ Q * ε := by
      set Lσ : B → Set (LogReg Req m) := fun σ => searchLogs lab (fun l => P l (σ l)) Q
      have hterm : ∀ ω' : (B × C) × B, (μ' ω').toReal * prob (S (τ₁ ω')) (D.final E₂ noPost ω') ≤
          (μ' ω').toReal * prob (logsIn (Lσ ω'.2)) (D.final E noPost (τ₂ ω')) := by
        rintro ⟨⟨a, c⟩, σ⟩
        by_cases ha : unmarkedLaw P a = 0
        · rw [hμ'apply, ha]
          simp
        refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
        have hmem := mem_piFinset_of_unmarkedLaw_ne_zero ha
        refine Supported.prob_le_of_inter_subset (G := Set.univ) (fun r hr => absurd trivial hr)
          fun r hr _ => ?_
        have hr' := hr.2
        simp only [τ₁, labelBlocks_setLabelBlocks] at hr'
        exact searchLogs_mono (fun l hl => marked_of_mixBlocks hmem hl) Q hr'
      calc D.eventProb E₂ noPost (S ∘ τ₁)
          ≤ ∑ ω' : (B × C) × B, (μ' ω').toReal *
              prob (logsIn (Lσ ω'.2)) (D.final E noPost (τ₂ ω')) :=
            sum_le_sum fun ω' _ => hterm ω'
        _ = ∑ v : B × C, (μV v).toReal * ∑ σ, (ν σ).toReal *
              prob (logsIn (Lσ σ)) (D.final E noPost (setLabelBlocks e κ H₀ v.1, v.2)) := by
            rw [Fintype.sum_prod_type]
            refine sum_congr rfl fun v _ => ?_
            rw [mul_sum]
            refine sum_congr rfl fun σ _ => ?_
            simp only [μ', prodLaw_apply, ENNReal.toReal_mul, τ₂]
            ring
        _ ≤ ∑ v : B × C, (μV v).toReal * (Q * ε) := by
            refine sum_le_sum fun v _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
            refine (sum_mul_prob_logsIn_le ν Lσ _ fun lg =>
              toReal_toOuterMeasure_searchLogs_le ν lab (fun σ l => P l (σ l)) Q hε0 hνP lg).trans
              ?_
            rw [D.norm_final, one_pow, mul_one]
        _ = Q * ε := by rw [← sum_mul, μV.sum_toReal, one_mul]
    -- one-way to hiding between the two games
    have hsq := D.abs_sqrt_eventProb_sub_le_of_fresh_secret_budget bud E₂ E₁ (S ∘ τ₁)
      (μV := μV) (ν := ν) (T := T) (ε := ε) (fun v σ => prodLaw_apply _ _ _ _) rfl
      (fun ω' rs req => by
        rw [Env.answerAfter_comap, Env.answerAfter_comap]
        exact hans _ _ _ rs req ((agreeOffLabels_setLabelBlocks H₀ _).symm.trans
          (agreeOffLabels_setLabelBlocks H₀ _)))
      (fun ω' rs x hx => by
        rw [Env.oracleIn_comap, Env.oracleIn_comap, horacle, horacle]
        cases hκ : κ x with
        | none => simp only [τ₁, τ₂, setLabelBlocks_of_none _ hκ]
        | some l =>
          simp only [τ₁, τ₂, setLabelBlocks_of_some _ hκ]
          rw [mixBlocks_of_not fun hP => hx ⟨l, hκ, hP⟩])
      (fun _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
      (fun x => by
        cases hκ : κ x with
        | none => simpa [T, hκ] using hε0
        | some l =>
          have : {σ : B | x ∈ T σ} = {σ | P l (σ l)} := by
            ext σ
            simp [T, hκ]
          rw [this]
          exact hνP l)
    have hP1nn : 0 ≤ D.eventProb E₁ noPost (S ∘ τ₁) :=
      sum_nonneg fun _ _ => mul_nonneg ENNReal.toReal_nonneg (prob_nonneg _ _)
    have hroot : √(D.eventProb E₁ noPost (S ∘ τ₁)) ≤ b := by
      have h2 := (abs_sub_le_iff.1 hsq).2
      have h3 : √(D.eventProb E₂ noPost (S ∘ τ₁)) ≤ √(Q * ε) := Real.sqrt_le_sqrt hP2
      simp only [b]
      linarith
    rw [← hP1, ← Real.sq_sqrt hP1nn]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 2
  rw [h1, hμH.sum_mul_eq f, ← hb]
  calc ∑ H₀, (μH H₀).toReal * 𝔼 u, f (setLabelBlocks e κ H₀ u)
      ≤ ∑ H₀, (μH H₀).toReal * b ^ 2 :=
        sum_le_sum fun H₀ _ => mul_le_mul_of_nonneg_left (hper H₀) ENNReal.toReal_nonneg
    _ = b ^ 2 := by rw [← sum_mul, μH.sum_toReal, one_mul]

/-- **Search over the whole run of a game, in the QROM, in terms of the query bound**: under the
hypotheses of `eventProb_searchLogs_le` and `n q ≤ t`, the probability is at most
`(√Q + 2 t)² ε`. -/
theorem eventProb_searchLogs_le_of_mul_le (bud : D.Budget q) (E : Env ((X → Y) × C) Req A X Y Q)
    {μH : PMF (X → Y)} {ζ : PMF C} (hμ : ∀ H c, E.μ (H, c) = μH H * ζ c)
    (hμH : IsUniformOnLabels e κ μH) (horacle : ∀ ω rs, E.oracleIn ω rs = ω.1)
    (hans : ∀ H H' c rs req, AgreeOffLabels e κ H H' →
      E.answerAfter (H, c) rs req = E.answerAfter (H', c) rs req)
    (P : (l : L) → ({x // κ x = some l} → Y₁) → Prop) [∀ l, DecidablePred (P l)]
    (lab : Req → Option L) (Acc : Set (GameReg W n X Y Req A m)) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ l, (μH.toOuterMeasure {H | P l (labelBlocks e κ H l)}).toReal ≤ ε) {t : ℕ}
    (ht : n * q ≤ t) :
    D.eventProb E noPost
        (fun ω => Acc ∩ logsIn (searchLogs lab (fun l => P l (labelBlocks e κ ω.1 l)) Q)) ≤
      (√Q + 2 * t) ^ 2 * ε := by
  refine (eventProb_searchLogs_le bud E hμ hμH horacle hans P lab Acc hε0 hε).trans ?_
  have h := mul_sqrt_le_of_mul_le ht
  have hle : √(Q : ℝ) + 2 * q * √n ≤ √Q + 2 * t := by linarith
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hle 2) hε0

end Distinguisher

end GordieHowe.Quantum
