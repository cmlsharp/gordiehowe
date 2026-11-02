-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.PMFTV

@[expose] public section

/-!
# Search problems with a uniform instance

The search experiment of a lattice assumption: an instance `x` drawn uniformly from a finite
type `S`, an adversary `A : S → PMF (Option T)` (`none`: no answer), and a win when the answer `s`
satisfies the problem's relation `Valid x s`. This is the experiment of VCVio's `SIS.Problem`
(`LatticeCrypto/HardnessAssumptions/ShortIntegerSolution.lean` at commit `eb0f6e4`:
`experiment` samples the challenge, runs the adversary and checks `isValid`; `advantage` is the
probability of `true`), restated over `PMF` without depending on VCVio, as
`GordieHowe/Foundations/Probability/Probability.lean` does for uniform draws. The instance is
uniform, which every search problem of the library has (a uniform matrix, a uniform seed).

- `winLaw A`, `winProb Valid A`: the law of the instance with the answer, and the probability of a
  win.
- `winProb_eq_sum`: the win probability as the average over the instance of the probability of a
  winning answer. `winProb_le_one`, `winProb_mono` (a weaker relation is won at least as often).
- **Multiple instances.** `multiValid Valid n`: `n` independent instances, given together, and an
  answer `(i, s)` for one of them. `guess A`: the single-instance adversary that draws `i` and the
  other instances uniformly, puts its own instance at `i`, runs `A` and keeps an answer for `i`.
  `multiWinProb_le_card_mul`: the `n`-instance win probability is at most `n` times the win
  probability of `guess A`.
- **Hardness of a class.** `Hard Valid 𝒜 ε`: every adversary of the class `𝒜` wins with probability
  at most `ε`. `hard_one` (every class at `ε = 1`), `Hard.mono_class`, `Hard.mono_valid`,
  `Hard.multi` (a class that contains `guess A` bounds the `n`-instance game by `n · ε`).

## Adversaries

The adversaries need not be efficient, and the library's lattice games have no oracle, so the
adversary is its output law at each instance. A quantum algorithm without oracle access, or an
explicit reduction that runs a quantum adversary and simulates its oracle itself, has such a law.
Without a restriction to a class, a problem whose instance determines a solution is won with
probability one by the adversary that outputs it; the hardness statements of the library are
therefore about a class `𝒜`, a parameter, and the reductions state their bounds at explicit
adversaries.
-/

namespace GordieHowe.Lattice

open PMF Finset
open scoped ENNReal BigOperators

variable {S T : Type} [Fintype S] [Nonempty S]

/-- **The law of a search experiment**: the instance `x` uniform on `S`, then the answer of `A`
on `x`, with the instance. -/
noncomputable def winLaw (A : S → PMF (Option T)) : PMF (S × Option T) :=
  (uniformOfFintype S).bind fun x => (A x).map fun o => (x, o)

/-- **A winning answer**: an answer `s` (not `none`) with `Valid x s`. -/
def Wins (Valid : S → T → Prop) (x : S) (o : Option T) : Prop :=
  ∃ s, o = some s ∧ Valid x s

/-- **The win probability** of `A` in the search problem with relation `Valid`. -/
noncomputable def winProb (Valid : S → T → Prop) (A : S → PMF (Option T)) : ℝ≥0∞ :=
  (winLaw A).toOuterMeasure {p | Wins Valid p.1 p.2}

/-- The win probability is the average over the instance of the probability of a winning
answer. -/
theorem winProb_eq_sum (Valid : S → T → Prop) (A : S → PMF (Option T)) :
    winProb Valid A =
      ∑ x, (Fintype.card S : ℝ≥0∞)⁻¹ * (A x).toOuterMeasure {o | Wins Valid x o} := by
  rw [winProb, winLaw, toOuterMeasure_bind_apply, tsum_fintype]
  refine sum_congr rfl fun x _ => ?_
  rw [uniformOfFintype_apply, toOuterMeasure_map_apply]
  rfl

theorem winProb_le_one (Valid : S → T → Prop) (A : S → PMF (Option T)) : winProb Valid A ≤ 1 :=
  toOuterMeasure_apply_le_one _ _

/-- **A readout of a law wins at least as often as an event that makes its answer valid**: for
laws `L x` of an outcome at each instance and a readout `r x` of the answer, the win probability of
the read-out laws is at least the average over the instance of the probability of an event `E`
on which the readout wins. -/
theorem sum_le_winProb_map {Ω : Type} (Valid : S → T → Prop) (L : S → PMF Ω)
    (r : S → Ω → Option T) (E : S → Ω → Prop) (hE : ∀ x ω, E x ω → Wins Valid x (r x ω)) :
    ∑ x, (Fintype.card S : ℝ≥0∞)⁻¹ * (L x).toOuterMeasure {ω | E x ω} ≤
      winProb Valid (fun x => (L x).map (r x)) := by
  rw [winProb_eq_sum]
  refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [toOuterMeasure_map_apply]
  exact (L x).toOuterMeasure.mono fun ω hω => hE x ω hω

/-- A relation implied by `Valid` is won at least as often. -/
theorem winProb_mono {Valid Valid' : S → T → Prop} (h : ∀ x s, Valid x s → Valid' x s)
    (A : S → PMF (Option T)) : winProb Valid A ≤ winProb Valid' A := by
  refine (winLaw A).toOuterMeasure.mono fun p ⟨s, hs, hv⟩ => ⟨s, hs, h _ _ hv⟩

/-! ### Multiple instances -/

/-- **The `n`-instance relation**: `n` instances given together, an answer `(i, s)` with `s` valid
for the instance `i`. -/
def multiValid (Valid : S → T → Prop) (n : ℕ) (xs : Fin n → S) (a : Fin n × T) : Prop :=
  Valid (xs a.1) a.2

/-- **The guessing adversary** of an `n`-instance adversary `A`: on its instance `x`, an index `i`
and instances `xs` uniform, then `A` on `xs` with `x` put at `i`; it keeps an answer for `i`. -/
noncomputable def guess {n : ℕ} [NeZero n] (A : (Fin n → S) → PMF (Option (Fin n × T))) :
    S → PMF (Option T) := fun x =>
  (uniformOfFintype (Fin n × (Fin n → S))).bind fun ixs =>
    (A (Function.update ixs.2 ixs.1 x)).map fun o =>
      o.bind fun a => if a.1 = ixs.1 then some a.2 else none

/-- **Putting an instance at `i`** is a bijection `S × (Fin n → S) ≃ (Fin n → S) × S`: the updated
family with the overwritten instance. -/
def updateEquiv {n : ℕ} [DecidableEq S] (i : Fin n) : S × (Fin n → S) ≃ (Fin n → S) × S where
  toFun p := (Function.update p.2 i p.1, p.2 i)
  invFun q := (q.1 i, Function.update q.1 i q.2)
  left_inv p := by simp
  right_inv q := by simp

/-- The answers of `A` at `xs` that win at the index `i`. -/
def WinsAt (Valid : S → T → Prop) {n : ℕ} (i : Fin n) (xs : Fin n → S)
    (o : Option (Fin n × T)) : Prop :=
  ∃ s, o = some (i, s) ∧ Valid (xs i) s

/-- **The guessing adversary's win probability**: the average over `i` of the probability that `A`
wins at `i`. -/
theorem winProb_guess (Valid : S → T → Prop) {n : ℕ} [NeZero n]
    (A : (Fin n → S) → PMF (Option (Fin n × T))) :
    winProb Valid (guess A) =
      (n : ℝ≥0∞)⁻¹ * ∑ i : Fin n, ∑ xs : Fin n → S,
        (Fintype.card (Fin n → S) : ℝ≥0∞)⁻¹ * (A xs).toOuterMeasure {o | WinsAt Valid i xs o} := by
  classical
  rw [winProb_eq_sum]
  -- Each term: the guessing adversary at `x` is an average over `(i, xs)`.
  have hterm : ∀ x : S, (guess A x).toOuterMeasure {o | Wins Valid x o} =
      ∑ i : Fin n, ∑ xs : Fin n → S,
        ((n : ℝ≥0∞)⁻¹ * (Fintype.card (Fin n → S) : ℝ≥0∞)⁻¹) *
          (A (Function.update xs i x)).toOuterMeasure
            {o | WinsAt Valid i (Function.update xs i x) o} := by
    intro x
    rw [guess, toOuterMeasure_bind_apply, tsum_fintype, Fintype.sum_prod_type]
    refine sum_congr rfl fun i _ => sum_congr rfl fun xs _ => ?_
    rw [uniformOfFintype_apply, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
      ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),
      toOuterMeasure_map_apply]
    congr 2
    ext o
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Wins, WinsAt, Function.update_self]
    constructor
    · rintro ⟨s, hs, hv⟩
      rcases o with _ | ⟨j, s'⟩
      · simp at hs
      · simp only [Option.bind_some] at hs
        split_ifs at hs with hj
        · cases hs
          exact ⟨s, by rw [hj], hv⟩
    · rintro ⟨s, rfl, hv⟩
      exact ⟨s, by simp, hv⟩
  simp_rw [hterm, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => ?_
  -- Reindex `(x, xs)` by the updated family and the overwritten instance.
  have hre : ∀ f : (Fin n → S) → ℝ≥0∞,
      ∑ x : S, ∑ xs : Fin n → S, f (Function.update xs i x) =
        ∑ ys : Fin n → S, (Fintype.card S : ℝ≥0∞) * f ys := by
    intro f
    rw [← Fintype.sum_prod_type' (f := fun x xs => f (Function.update xs i x))]
    rw [← (updateEquiv (S := S) i).symm.sum_comp]
    simp only [updateEquiv, Equiv.coe_fn_symm_mk, Function.update_idem, Function.update_eq_self]
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun ys _ => ?_
    dsimp only
    rw [sum_const, card_univ, nsmul_eq_mul]
  have key := hre fun ys => ((n : ℝ≥0∞)⁻¹ * (Fintype.card (Fin n → S) : ℝ≥0∞)⁻¹) *
    (A ys).toOuterMeasure {o | WinsAt Valid i ys o}
  calc ∑ x : S, ∑ xs : Fin n → S, (Fintype.card S : ℝ≥0∞)⁻¹ *
        (((n : ℝ≥0∞)⁻¹ * (Fintype.card (Fin n → S) : ℝ≥0∞)⁻¹) *
          (A (Function.update xs i x)).toOuterMeasure
            {o | WinsAt Valid i (Function.update xs i x) o})
      = (Fintype.card S : ℝ≥0∞)⁻¹ * ∑ x : S, ∑ xs : Fin n → S,
        (((n : ℝ≥0∞)⁻¹ * (Fintype.card (Fin n → S) : ℝ≥0∞)⁻¹) *
          (A (Function.update xs i x)).toOuterMeasure
            {o | WinsAt Valid i (Function.update xs i x) o}) := by
        simp_rw [Finset.mul_sum]
    _ = (Fintype.card S : ℝ≥0∞)⁻¹ * ∑ ys : Fin n → S, (Fintype.card S : ℝ≥0∞) *
        (((n : ℝ≥0∞)⁻¹ * (Fintype.card (Fin n → S) : ℝ≥0∞)⁻¹) *
          (A ys).toOuterMeasure {o | WinsAt Valid i ys o}) := by rw [key]
    _ = ∑ ys : Fin n → S, (n : ℝ≥0∞)⁻¹ * ((Fintype.card (Fin n → S) : ℝ≥0∞)⁻¹ *
          (A ys).toOuterMeasure {o | WinsAt Valid i ys o}) := by
        rw [Finset.mul_sum]
        refine sum_congr rfl fun ys _ => ?_
        rw [← mul_assoc, ENNReal.inv_mul_cancel (by simp) (ENNReal.natCast_ne_top _), one_mul,
          mul_assoc]

/-- **The `n`-instance game is won at most `n` times as often as the single-instance game**, by
the guessing adversary: `winProb (multiValid Valid n) A ≤ n · winProb Valid (guess A)`. -/
theorem multiWinProb_le_card_mul (Valid : S → T → Prop) {n : ℕ} [NeZero n]
    (A : (Fin n → S) → PMF (Option (Fin n × T))) :
    winProb (multiValid Valid n) A ≤ n * winProb Valid (guess A) := by
  classical
  rw [winProb_guess, ← mul_assoc, ENNReal.mul_inv_cancel (by simp [NeZero.ne n])
    (ENNReal.natCast_ne_top _), one_mul, winProb_eq_sum, Finset.sum_comm]
  refine sum_le_sum fun xs _ => ?_
  rw [← Finset.mul_sum]
  gcongr _ * ?_
  calc (A xs).toOuterMeasure {o | Wins (multiValid Valid n) xs o}
      ≤ (A xs).toOuterMeasure (⋃ i : Fin n, {o | WinsAt Valid i xs o}) := by
        refine (A xs).toOuterMeasure.mono fun o ⟨a, ha, hv⟩ => ?_
        exact Set.mem_iUnion.2 ⟨a.1, a.2, by rw [ha], hv⟩
    _ ≤ ∑' i : Fin n, (A xs).toOuterMeasure {o | WinsAt Valid i xs o} :=
        MeasureTheory.measure_iUnion_le _
    _ = ∑ i : Fin n, (A xs).toOuterMeasure {o | WinsAt Valid i xs o} := tsum_fintype _

/-! ### Hardness of a class of adversaries -/

/-- **Hardness of the search problem for the class `𝒜`**: every adversary of `𝒜` wins with
probability at most `ε`. -/
def Hard (Valid : S → T → Prop) (𝒜 : Set (S → PMF (Option T))) (ε : ℝ≥0∞) : Prop :=
  ∀ A ∈ 𝒜, winProb Valid A ≤ ε

/-- **Every class at `ε = 1`.** -/
theorem hard_one (Valid : S → T → Prop) (𝒜 : Set (S → PMF (Option T))) : Hard Valid 𝒜 1 :=
  fun A _ => winProb_le_one Valid A

theorem Hard.mono_class {Valid : S → T → Prop} {𝒜 𝒜' : Set (S → PMF (Option T))} {ε : ℝ≥0∞}
    (h : Hard Valid 𝒜 ε) (h𝒜 : 𝒜' ⊆ 𝒜) : Hard Valid 𝒜' ε :=
  fun A hA => h A (h𝒜 hA)

theorem Hard.mono_eps {Valid : S → T → Prop} {𝒜 : Set (S → PMF (Option T))} {ε ε' : ℝ≥0∞}
    (h : Hard Valid 𝒜 ε) (hε : ε ≤ ε') : Hard Valid 𝒜 ε' :=
  fun A hA => (h A hA).trans hε

/-- Hardness for a relation passes to a relation that implies it. -/
theorem Hard.mono_valid {Valid Valid' : S → T → Prop} {𝒜 : Set (S → PMF (Option T))} {ε : ℝ≥0∞}
    (h : Hard Valid' 𝒜 ε) (hv : ∀ x s, Valid x s → Valid' x s) : Hard Valid 𝒜 ε :=
  fun A hA => (winProb_mono hv A).trans (h A hA)

/-- **The `n`-instance bound from single-instance hardness**: if `𝒜` contains the guessing
adversary of `A`, then `A` wins the `n`-instance game with probability at most `n · ε`. -/
theorem Hard.multi {Valid : S → T → Prop} {𝒜 : Set (S → PMF (Option T))} {ε : ℝ≥0∞}
    (h : Hard Valid 𝒜 ε) {n : ℕ} [NeZero n] (A : (Fin n → S) → PMF (Option (Fin n × T)))
    (hA : guess A ∈ 𝒜) : winProb (multiValid Valid n) A ≤ n * ε :=
  (multiWinProb_le_card_mul Valid A).trans (by gcongr; exact h _ hA)

/-- **No class bound below one for a problem with a solution at every instance**: the adversary
that outputs a solution wins with probability one, so the unrestricted class is hard only at
`ε = 1`. -/
theorem not_hard_univ {Valid : S → T → Prop} (hsol : ∀ x, ∃ s, Valid x s) {ε : ℝ≥0∞}
    (hε : ε < 1) : ¬ Hard Valid Set.univ ε := by
  classical
  intro h
  let A : S → PMF (Option T) := fun x => PMF.pure (some (hsol x).choose)
  have hA : winProb Valid A = 1 := by
    rw [winProb_eq_sum]
    have : ∀ x, (A x).toOuterMeasure {o | Wins Valid x o} = 1 := fun x => by
      have hw : some (hsol x).choose ∈ {o | Wins Valid x o} := ⟨_, rfl, (hsol x).choose_spec⟩
      simp only [A, toOuterMeasure_pure_apply, hw, ↓reduceIte]
    simp_rw [this, mul_one, sum_const, card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _)
  exact absurd (h A (Set.mem_univ _)) (by rw [hA]; exact not_le.2 hε)

end GordieHowe.Lattice
