-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import LatticeCrypto.Ring.Transform
public import Mathlib.Probability.Distributions.Uniform
public import GordieHowe.Foundations.ToMathlib.PMFSumToReal

@[expose] public section

/-!
# Module-LWE

The decision and search Module-LWE problems over a negacyclic ring `R_q = Z_q[X]/(X^n + 1)`, with
the matrix in the transform domain acting by the vendored `TransformOps.coeffMatVecMul`
(`A * s`), and the law of the secret a parameter.

## Sources

- Module-LWE: Langlois and Stehlé, *Worst-case to average-case reductions for module lattices*
  (Des. Codes Cryptogr. 75(3), 2015; ePrint 2012/090), cited as the origin of the problem by KLS18
  §4.1.1 ("This assumption was introduced in [LS15]"). The text of Langlois–Stehlé has not been
  checked against the library's form here; the form is that of the three documents below.
- Decision MLWE: Kiltz, Lyubashevsky and Schaffner (EUROCRYPT 2018, ePrint 2017/916), §4.1.1;
  *CRYSTALS-Dilithium: Algorithm Specifications and Supporting Documentation* (Version 3.1), §6.1;
  Barbosa, Barthe, Doczkal, Don, Fehr, Grégoire, Huang, Hülsing, Lee and Wu (CRYPTO 2023, ePrint
  2023/246), §6.2, Definition 3:
  `Adv^MLWE_{m,k,D}(A) = |Pr[A(A, t) = 1 | A ← R_q^{m×k}; t ← R_q^m] −
  Pr[A(A, A s₁ + s₂) = 1 | A ← R_q^{m×k}; s₁ ← D^k; s₂ ← D^m]|`.
  The Dilithium specification states it for `D` uniform on the coefficients in `[−η, η]`
  (§6.2.1).
- Search MLWE: recover `(s₁, s₂)` from `(A, A s₁ + s₂)`; the experiment of VCVio's
  `NoisyLearning.searchExperiment` (commit `eb0f6e4`).

## The library's form

- `mlweUniformMean f`, `mlweRealMean S f`, `mlweAdvantage S f`: the means of a test
  `f : PolyMatrix Hat k l → PolyVec R k → ℝ` at a uniform `(A, t)` and at `(A, A * s.1 + s.2)` with
  `s ← S`, and their distance. Three generalizations of the sources, none of which changes their
  case: the algorithm is a test, its probability of outputting `1` on each input
  (`distinguisherTest D` for a distinguisher `D : _ → _ → PMF Bool`); the secret `(s₁, s₂)` has an
  arbitrary law `S` (the sources' `D^l × D^k` is one choice); the matrix is uniform in the
  transform domain, as FIPS 204 `ExpandA` outputs it.
- `abs_mlweRealMean_sub_mlweUniformMean_le`: the hop of a hybrid argument.
- `MLWEHard S 𝒜 ε`: every `[0, 1]`-valued test (`UnitTest`) of the class `𝒜` has advantage at
  most `ε`. Non-vacuity: `mlweHard_one` (every class at `ε = 1`), `mlweHard_const` (tests that
  ignore their input, at `ε = 0`). `not_mlweHard_univ`: the unrestricted class is not hard below
  `1 − |supp S| / |R_q^k|`, by `imageTest S`, the test of `t` lying in the image of the support of
  `S` under `s ↦ A * s.1 + s.2` (`mlweAdvantage_imageTest_ge`). `card_filter_map_ne_zero_le`: a
  law pushed forward from a finite type `W` has at most `|W|` points of positive weight.
- `mlweSearchProb S B`: the probability that `B` recovers the secret.
-/

namespace GordieHowe.Lattice

open LatticeCrypto TransformOps PMF Finset
open scoped ENNReal BigOperators

variable {Coeff : Type} [CommRing Coeff] {ring : NegacyclicRing Coeff} {Hat : Type}
  [AddCommGroup Hat] {k l : ℕ}
  [Fintype (PolyMatrix Hat k l)] [Nonempty (PolyMatrix Hat k l)]
  [Fintype (PolyVec ring.Poly k)] [Nonempty (PolyVec ring.Poly k)]
  [Fintype (PolyVec ring.Poly l)]

/-- **The uniform MLWE mean** of a test `f`: `𝔼[f(A, t)]` for `A` uniform on `Hat^{k×l}` and `t`
uniform on `R_q^k`, independent. -/
noncomputable def mlweUniformMean (f : PolyMatrix Hat k l → PolyVec ring.Poly k → ℝ) : ℝ :=
  ∑ A : PolyMatrix Hat k l, ∑ t : PolyVec ring.Poly k,
    (uniformOfFintype (PolyMatrix Hat k l) A).toReal *
      (uniformOfFintype (PolyVec ring.Poly k) t).toReal * f A t

variable [ops : TransformOps ring Hat]

/-- **The real MLWE mean** of a test `f`: `𝔼[f(A, A * s₁ + s₂)]` for `A` uniform on `Hat^{k×l}` and
`(s₁, s₂) ← S`, independent. -/
noncomputable def mlweRealMean (S : PMF (PolyVec ring.Poly l × PolyVec ring.Poly k))
    (f : PolyMatrix Hat k l → PolyVec ring.Poly k → ℝ) : ℝ :=
  ∑ A : PolyMatrix Hat k l, ∑ s : PolyVec ring.Poly l × PolyVec ring.Poly k,
    (uniformOfFintype (PolyMatrix Hat k l) A).toReal * (S s).toReal * f A (A * s.1 + s.2)

/-- **The decision MLWE advantage** of a test `f` against secrets with law `S`:
`|𝔼_uniform f − 𝔼_real f|`. -/
noncomputable def mlweAdvantage (S : PMF (PolyVec ring.Poly l × PolyVec ring.Poly k))
    (f : PolyMatrix Hat k l → PolyVec ring.Poly k → ℝ) : ℝ :=
  |mlweUniformMean f - mlweRealMean S f|

/-- **The test of a distinguisher**: its probability of outputting `1`. -/
noncomputable def distinguisherTest (D : PolyMatrix Hat k l → PolyVec ring.Poly k → PMF Bool) :
    PolyMatrix Hat k l → PolyVec ring.Poly k → ℝ :=
  fun A t => (D A t true).toReal

/-- **The MLWE hop**: for every test `f`, its real and uniform means differ by at most its
advantage. -/
theorem abs_mlweRealMean_sub_mlweUniformMean_le
    (S : PMF (PolyVec ring.Poly l × PolyVec ring.Poly k))
    (f : PolyMatrix Hat k l → PolyVec ring.Poly k → ℝ) :
    |mlweRealMean S f - mlweUniformMean f| ≤ mlweAdvantage S f := by
  rw [mlweAdvantage, abs_sub_comm]

/-! ### Hardness of a class of tests -/

/-- **A `[0, 1]`-valued test**, the probability of an algorithm's output `1`. -/
def UnitTest (f : PolyMatrix Hat k l → PolyVec ring.Poly k → ℝ) : Prop :=
  ∀ A t, 0 ≤ f A t ∧ f A t ≤ 1

/-- **Hardness of decision MLWE for the class `𝒜`** of tests, against secrets with law `S`: every
`[0, 1]`-valued test of `𝒜` (the test of an algorithm, `UnitTest`) has advantage at most `ε`. -/
def MLWEHard (S : PMF (PolyVec ring.Poly l × PolyVec ring.Poly k))
    (𝒜 : Set (PolyMatrix Hat k l → PolyVec ring.Poly k → ℝ)) (ε : ℝ) : Prop :=
  ∀ f ∈ 𝒜, UnitTest f → mlweAdvantage S f ≤ ε

omit [AddCommGroup Hat] ops [Fintype (PolyMatrix Hat k l)] [Nonempty (PolyMatrix Hat k l)]
  [Fintype (PolyVec ring.Poly k)] [Nonempty (PolyVec ring.Poly k)]
  [Fintype (PolyVec ring.Poly l)] in
theorem unitTest_distinguisherTest (D : PolyMatrix Hat k l → PolyVec ring.Poly k → PMF Bool) :
    UnitTest (distinguisherTest D) := fun A t =>
  ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by rw [ENNReal.ofReal_one]; exact coe_le_one _ _)⟩

omit ops in
/-- A weighted sum of a `[0, 1]`-valued function with weights of a law is in `[0, 1]`. -/
theorem sum_toReal_mul_mem_unit {X : Type*} [Fintype X] (μ : PMF X) (h : X → ℝ)
    (hh : ∀ x, 0 ≤ h x ∧ h x ≤ 1) : 0 ≤ ∑ x, (μ x).toReal * h x ∧ ∑ x, (μ x).toReal * h x ≤ 1 := by
  refine ⟨sum_nonneg fun x _ => mul_nonneg ENNReal.toReal_nonneg (hh x).1, ?_⟩
  calc ∑ x, (μ x).toReal * h x ≤ ∑ x, (μ x).toReal :=
        sum_le_sum fun x _ => mul_le_of_le_one_right ENNReal.toReal_nonneg (hh x).2
    _ = 1 := sum_toReal_eq_one μ

omit [AddCommGroup Hat] ops [Fintype (PolyVec ring.Poly l)] in
theorem mlweUniformMean_mem_unit {f : PolyMatrix Hat k l → PolyVec ring.Poly k → ℝ}
    (hf : UnitTest f) : 0 ≤ mlweUniformMean f ∧ mlweUniformMean f ≤ 1 := by
  have h := sum_toReal_mul_mem_unit (uniformOfFintype (PolyMatrix Hat k l))
    (fun A => ∑ t : PolyVec ring.Poly k, (uniformOfFintype (PolyVec ring.Poly k) t).toReal * f A t)
    fun A => sum_toReal_mul_mem_unit _ _ fun t => hf A t
  simpa only [mlweUniformMean, mul_sum, mul_assoc] using h

omit [Nonempty (PolyVec ring.Poly k)] in
theorem mlweRealMean_mem_unit (S : PMF (PolyVec ring.Poly l × PolyVec ring.Poly k))
    {f : PolyMatrix Hat k l → PolyVec ring.Poly k → ℝ} (hf : UnitTest f) :
    0 ≤ mlweRealMean S f ∧ mlweRealMean S f ≤ 1 := by
  have h := sum_toReal_mul_mem_unit (uniformOfFintype (PolyMatrix Hat k l))
    (fun A => ∑ s, (S s).toReal * f A (A * s.1 + s.2))
    fun A => sum_toReal_mul_mem_unit S _ fun s => hf A _
  simpa only [mlweRealMean, mul_sum, mul_assoc] using h

/-- **Every class is hard at `ε = 1`.** -/
theorem mlweHard_one (S : PMF (PolyVec ring.Poly l × PolyVec ring.Poly k))
    (𝒜 : Set (PolyMatrix Hat k l → PolyVec ring.Poly k → ℝ)) :
    MLWEHard S 𝒜 1 := fun f _ hf => by
  have h₁ := mlweUniformMean_mem_unit hf
  have h₂ := mlweRealMean_mem_unit S hf
  rw [mlweAdvantage, abs_le]
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

/-- **Tests that ignore their input have advantage `0`**, so their class is hard at `ε = 0`. -/
theorem mlweHard_const (S : PMF (PolyVec ring.Poly l × PolyVec ring.Poly k)) :
    MLWEHard S {f | ∃ c : ℝ, f = fun _ _ => c} 0 := by
  rintro f ⟨c, rfl⟩ -
  have hU : mlweUniformMean (Hat := Hat) (k := k) (l := l) (ring := ring) (fun _ _ => c) = c := by
    simp only [mlweUniformMean, ← sum_mul, ← mul_sum, sum_toReal_eq_one, mul_one, one_mul]
  have hR : mlweRealMean S (fun (_ : PolyMatrix Hat k l) (_ : PolyVec ring.Poly k) => c) = c := by
    simp only [mlweRealMean, ← sum_mul, ← mul_sum, sum_toReal_eq_one, mul_one, one_mul]
  rw [mlweAdvantage, hU, hR, sub_self, abs_zero]

/-! ### The unrestricted class -/

variable [DecidableEq (PolyVec ring.Poly k)]

open Classical in
/-- **The image test** of the law `S`: `t` is `A * s.1 + s.2` for some `s` in the support of
`S`. -/
noncomputable def imageTest (S : PMF (PolyVec ring.Poly l × PolyVec ring.Poly k)) :
    PolyMatrix Hat k l → PolyVec ring.Poly k → ℝ := fun A t =>
  if ∃ s : PolyVec ring.Poly l × PolyVec ring.Poly k, S s ≠ 0 ∧ A * s.1 + s.2 = t then 1 else 0

omit [Fintype (PolyMatrix Hat k l)] [Nonempty (PolyMatrix Hat k l)]
  [Nonempty (PolyVec ring.Poly k)] in
theorem unitTest_imageTest (S : PMF (PolyVec ring.Poly l × PolyVec ring.Poly k)) :
    UnitTest (imageTest (Hat := Hat) S) := fun A t => by
  unfold imageTest
  split_ifs <;> norm_num

open Classical in
/-- **The image test separates**: its advantage is at least `1 − |supp S| / |R_q^k|`. -/
theorem mlweAdvantage_imageTest_ge (S : PMF (PolyVec ring.Poly l × PolyVec ring.Poly k)) :
    1 - ((univ.filter fun s => S s ≠ 0).card : ℝ) / Fintype.card (PolyVec ring.Poly k) ≤
      mlweAdvantage S (imageTest (Hat := Hat) S) := by
  set supp := univ.filter fun s => S s ≠ 0
  -- The real mean is one: every secret of positive weight lands in the image.
  have hR : mlweRealMean S (imageTest (Hat := Hat) S) = 1 := by
    have : ∀ A : PolyMatrix Hat k l, ∑ s, (S s).toReal * imageTest S A (A * s.1 + s.2) = 1 := by
      intro A
      rw [← sum_toReal_eq_one S]
      refine sum_congr rfl fun s _ => ?_
      by_cases hs : S s = 0
      · simp [hs]
      · have he : ∃ s' : PolyVec ring.Poly l × PolyVec ring.Poly k,
            S s' ≠ 0 ∧ A * s'.1 + s'.2 = A * s.1 + s.2 := ⟨s, hs, rfl⟩
        simp only [imageTest, he, ↓reduceIte, mul_one]
    calc mlweRealMean S (imageTest (Hat := Hat) S)
        = ∑ A : PolyMatrix Hat k l, (uniformOfFintype (PolyMatrix Hat k l) A).toReal *
            ∑ s, (S s).toReal * imageTest S A (A * s.1 + s.2) := by
          simp only [mlweRealMean, mul_sum, mul_assoc]
      _ = 1 := by simp only [this, mul_one, sum_toReal_eq_one]
  -- The uniform mean is at most the image's share of `R_q^k`.
  have hU : mlweUniformMean (imageTest (Hat := Hat) S) ≤
      (supp.card : ℝ) / Fintype.card (PolyVec ring.Poly k) := by
    have hA : ∀ A : PolyMatrix Hat k l,
        ∑ t : PolyVec ring.Poly k, (uniformOfFintype (PolyVec ring.Poly k) t).toReal *
          imageTest S A t ≤ (supp.card : ℝ) / Fintype.card (PolyVec ring.Poly k) := by
      intro A
      have hsum : ∑ t : PolyVec ring.Poly k, (uniformOfFintype (PolyVec ring.Poly k) t).toReal *
          imageTest S A t =
            ((univ.filter fun t => ∃ s : PolyVec ring.Poly l × PolyVec ring.Poly k,
              S s ≠ 0 ∧ A * s.1 + s.2 = t).card : ℝ) /
              Fintype.card (PolyVec ring.Poly k) := by
        simp only [uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
          imageTest, mul_ite, mul_one, mul_zero, sum_ite, sum_const_zero, add_zero, sum_const,
          nsmul_eq_mul]
        rw [div_eq_mul_inv]
      rw [hsum]
      gcongr
      have himg : (univ.filter fun t => ∃ s : PolyVec ring.Poly l × PolyVec ring.Poly k,
          S s ≠ 0 ∧ A * s.1 + s.2 = t) =
          supp.image fun s : PolyVec ring.Poly l × PolyVec ring.Poly k =>
            (A * s.1 : PolyVec ring.Poly k) + s.2 := by
        ext t
        simp [supp]
      rw [himg]
      exact_mod_cast card_image_le
    calc mlweUniformMean (imageTest (Hat := Hat) S)
        = ∑ A : PolyMatrix Hat k l, (uniformOfFintype (PolyMatrix Hat k l) A).toReal *
            ∑ t : PolyVec ring.Poly k, (uniformOfFintype (PolyVec ring.Poly k) t).toReal *
              imageTest S A t := by
          simp only [mlweUniformMean, mul_sum, mul_assoc]
      _ ≤ ∑ A : PolyMatrix Hat k l, (uniformOfFintype (PolyMatrix Hat k l) A).toReal *
            ((supp.card : ℝ) / Fintype.card (PolyVec ring.Poly k)) :=
          sum_le_sum fun A _ => mul_le_mul_of_nonneg_left (hA A) ENNReal.toReal_nonneg
      _ = (supp.card : ℝ) / Fintype.card (PolyVec ring.Poly k) := by
          rw [← sum_mul, sum_toReal_eq_one, one_mul]
  rw [mlweAdvantage, hR, abs_sub_comm]
  calc 1 - (supp.card : ℝ) / Fintype.card (PolyVec ring.Poly k)
      ≤ 1 - mlweUniformMean (imageTest (Hat := Hat) S) := by linarith
    _ ≤ |1 - mlweUniformMean (imageTest (Hat := Hat) S)| := le_abs_self _

open Classical in
/-- **The unrestricted class is not hard** below `1 − |supp S| / |R_q^k|`: an algorithm that need
not be efficient decides whether `t` is in the image of the support. -/
theorem not_mlweHard_univ (S : PMF (PolyVec ring.Poly l × PolyVec ring.Poly k)) {ε : ℝ}
    (hε : ε < 1 - ((univ.filter fun s => S s ≠ 0).card : ℝ) /
      Fintype.card (PolyVec ring.Poly k)) :
    ¬ MLWEHard S (Set.univ : Set (PolyMatrix Hat k l → PolyVec ring.Poly k → ℝ)) ε := fun h =>
  absurd (h _ (Set.mem_univ _) (unitTest_imageTest S))
    (not_le.2 (hε.trans_le (mlweAdvantage_imageTest_ge S)))

omit [Fintype (PolyMatrix Hat k l)] [Nonempty (PolyMatrix Hat k l)]
  [Fintype (PolyVec ring.Poly k)] [Nonempty (PolyVec ring.Poly k)]
  [Fintype (PolyVec ring.Poly l)] [DecidableEq (PolyVec ring.Poly k)] ops in
/-- **A law pushed forward from a finite type `W`** has at most `|W|` points of positive weight. -/
theorem card_filter_map_ne_zero_le {W V : Type*} [Fintype W] [Fintype V] [DecidableEq V]
    (μ : PMF W) (g : W → V) [DecidablePred fun v => μ.map g v ≠ 0] :
    (univ.filter fun v => μ.map g v ≠ 0).card ≤ Fintype.card W := by
  calc (univ.filter fun v => μ.map g v ≠ 0).card ≤ (univ.image g).card := by
        refine card_le_card fun v hv => ?_
        have hv' : ∃ a ∈ μ.support, g a = v :=
          (mem_support_map_iff g μ v).1 ((mem_support_iff _ _).2 (mem_filter.1 hv).2)
        exact mem_image.2 (hv'.imp fun a ha => ⟨mem_univ _, ha.2⟩)
    _ ≤ Fintype.card W := card_image_le.trans (by rw [card_univ])

/-! ### Search MLWE -/

open Classical in
/-- **The search MLWE success probability** of `B`: `A` uniform and `s ← S`, then `B` on
`(A, A * s.1 + s.2)` outputs `s`. -/
noncomputable def mlweSearchProb (S : PMF (PolyVec ring.Poly l × PolyVec ring.Poly k))
    (B : PolyMatrix Hat k l → PolyVec ring.Poly k →
      PMF (PolyVec ring.Poly l × PolyVec ring.Poly k)) : ℝ≥0∞ :=
  ((uniformOfFintype (PolyMatrix Hat k l)).bind fun A =>
    S.bind fun s => (B A (A * s.1 + s.2)).map fun s' => decide (s' = s)) true

omit [Fintype (PolyVec ring.Poly k)] [Nonempty (PolyVec ring.Poly k)]
  [Fintype (PolyVec ring.Poly l)] in
theorem mlweSearchProb_le_one (S : PMF (PolyVec ring.Poly l × PolyVec ring.Poly k))
    (B : PolyMatrix Hat k l → PolyVec ring.Poly k →
      PMF (PolyVec ring.Poly l × PolyVec ring.Poly k)) : mlweSearchProb S B ≤ 1 :=
  coe_le_one _ _

end GordieHowe.Lattice
