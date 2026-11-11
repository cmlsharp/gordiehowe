-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.ToMathlib.PMFOracleLoop
public import GordieHowe.Foundations.ToMathlib.UniformFunction

@[expose] public section

/-!
# A signer against a fixed oracle with side data

The quenched core signer: its attempts read one oracle `H : V → C × Z` drawn once, whose column `v`
carries the signer's challenge `c` and side data `z`. An attempt draws `y ← P`, rejects unless
`acc y c` at the column `w1 y`, and keeps `w1 y` with probability `κ (w1 y, c) · g (w1 y, c, z)`.
The signer's coin `κ` and the keep factor `g` are probabilities, and `g` reads only the column
(`quenchedAttempt`). The signer's own target weight is `w (v, c) ≤ 1`, and the target of the column
is `β · w (v, c) · g (v, c, z)`.

* `quenchedAttempt_apply_some`: the attempt keeps `v` with probability
  `signerMass v c · κ (v, c) · g (v, c, z)`.
* `quenchedColDev`, `quenchedDev`, `quenchedDev_eq`: the deviation of the attempt from the target
  is the sum over columns of `g` times the signer's column deviation
  `|signerMass v c · κ (v, c) - β · w (v, c)|`, which does not read `g`.
* `quenchedColDev_le`: a column deviation is at most `Pr[w1 = v] + β`.
* `quenchedColError`, `quenchedMeanWeight`, `quenchedRelColError`: the signer's column error
  `𝔼_c` of its column deviation, its mean weight `𝔼_c w (v, c)`, and the relative column error
  `∑_v colError v / meanWeight v / (β |V|)`. None reads `g`.
* `expect_quenchedDev`, `expect_quenchedDev_of_eq`: against a uniform oracle, the mean deviation is
  `∑_v 𝔼_{c, z} g · colDev`, and `∑_v sideMean v · colError v` when `g` does not read `c`.
* `quenchedMass`, `expect_quenchedMass`, `expect_quenchedMass_of_eq`: the total target weight and
  its mean.
* `abs_quenchedDev_update_le`, `abs_quenchedMass_update_le`: changing the oracle at one column `v`
  moves the deviation by at most `Pr[w1 = v] + β` and the total target weight by at most `1`.
* `quenchedConc_le`: **the oracle concentration bound**. The term `E_H[(q H / q̄ - 1)⁺]`
  (`quenchedConc`), with `q H` the keep probability of one attempt against `H` and `q̄` its mean
  (`quenchedKeepProb`), is at most `√(δ / q̄) / 2` when every commitment has probability at most
  `δ`. The keep probability is a sum over columns of terms at most `δ`, each reading one column, and
  the columns of a uniform `H` are independent.

The ring signer `i` reads `H : N × V → C`. It is the case with side data the other members' values,
`Z = {j // j ≠ i} → C`, through the column split `columnSplit i : (N × V → C) ≃ (V → C × Z)`, which
carries the uniform law to the uniform law (`expect_comp_equiv`, `sum_uniformOfFintype_comp_equiv`).
The ring attempt with excluded sets is the case with `g` the indicator that every other member's
value misses its excluded set (`passFactor`, `ringAttempt_eq_quenchedAttempt`), so its oracle
concentration bound `oracleConcError_le` follows from `quenchedConc_le`. The weighted ring attempt
of `PMFOracleQuenched.lean` and the single signer of `PMFOracleSingle.lean` are the other cases.

About Mathlib objects only.
-/

open Finset
open scoped ENNReal BigOperators

namespace PMF

/-- A probability in `ℝ` is at most one. -/
theorem _root_.ENNReal.toReal_le_one_of_le_one {x : ℝ≥0∞} (h : x ≤ 1) : x.toReal ≤ 1 := by
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top h

/-! ### Averages over a uniform function -/

section Uniform

/-- **The pullback of a uniform function along an embedding is uniform.** -/
theorem expect_comp_embedding {A X' Y' : Type*} [Fintype A] [DecidableEq A] [Fintype X']
    [DecidableEq X'] [Fintype Y'] [Nonempty Y'] (f : A ↪ X') (Φ : (A → Y') → ℝ) :
    𝔼 G : X' → Y', Φ (fun a => G (f a)) = 𝔼 g : A → Y', Φ g := by
  rw [← Fintype.expect_equiv (GordieHowe.splitAlong f).symm
    (fun q => Φ (fun a => (GordieHowe.splitAlong f).symm q (f a))) (fun G => Φ fun a => G (f a))
    fun _ => rfl, ← Finset.univ_product_univ,
    Finset.expect_product' _ _ fun Fo FX =>
      Φ fun a => (GordieHowe.splitAlong f).symm (Fo, FX) (f a)]
  simp only [GordieHowe.splitAlong_symm_apply_embed]
  exact Fintype.expect_const _

/-- **One coordinate of a uniform function is uniform.** -/
theorem expect_apply_eval {X' Y' : Type*} [Fintype X'] [DecidableEq X'] [Fintype Y'] [Nonempty Y']
    (x : X') (φ : Y' → ℝ) : 𝔼 G : X' → Y', φ (G x) = 𝔼 y, φ y := by
  refine (expect_comp_embedding (A := Unit) ⟨fun _ => x, fun _ _ _ => rfl⟩
    (fun g => φ (g ()))).trans ?_
  exact Fintype.expect_equiv (Equiv.funUnique Unit Y') _ _ fun _ => rfl

/-- An average over pairs of a function of the first coordinate is its average, for any
`Fintype` instance on the pairs. -/
theorem _root_.Finset.expect_comp_fst {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    [hαβ : Fintype (α × β)] (f : α → ℝ) : 𝔼 x : α × β, f x.1 = 𝔼 a, f a := by
  obtain rfl : hαβ = instFintypeProd α β := Subsingleton.elim _ _
  rw [← Finset.univ_product_univ, Finset.expect_product]
  show 𝔼 a : α, 𝔼 _b : β, f a = _
  exact Finset.expect_congr rfl fun a _ => Finset.expect_const univ_nonempty _

/-- An average over pairs of a function of the second coordinate is its average, for any
`Fintype` instance on the pairs. -/
theorem _root_.Finset.expect_comp_snd {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    [hαβ : Fintype (α × β)] (f : β → ℝ) : 𝔼 x : α × β, f x.2 = 𝔼 b, f b := by
  obtain rfl : hαβ = instFintypeProd α β := Subsingleton.elim _ _
  rw [← Finset.univ_product_univ, Finset.expect_product]
  show 𝔼 _a : α, 𝔼 b : β, f b = _
  exact Finset.expect_const univ_nonempty _

/-- **The average of a product of functions of independent uniform coordinates** is the product
of the averages. -/
theorem expect_prod_apply {ι Y' : Type*} [Fintype ι] [DecidableEq ι] [Fintype Y'] [Nonempty Y']
    (φ : ι → Y' → ℝ) : 𝔼 g : ι → Y', ∏ j, φ j (g j) = ∏ j, 𝔼 y, φ j y := by
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_pi, Finset.prod_const, Finset.card_univ]
  rw [← Fintype.prod_sum, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  push_cast
  rfl

/-- A function of one column of a uniform oracle has the average over a uniform column. -/
theorem expect_column {N V C : Type*} [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V]
    [Fintype C] [Nonempty C] (v : V) (Φ : (N → C) → ℝ) :
    𝔼 H : N × V → C, Φ (fun j => H (j, v)) = 𝔼 col : N → C, Φ col :=
  expect_comp_embedding ⟨fun j => (j, v), fun _ _ h => (Prod.mk.inj h).1⟩ Φ

/-- **The collision probability of a function of a uniform point**: for `y` uniform on `Y`,
`∑_w Pr[f y = w]² = Pr_{y, y'}[f y = f y']` with `y, y'` independent. -/
theorem sum_sq_toReal_map_uniformOfFintype {Y W : Type*} [Fintype Y] [Nonempty Y] [Fintype W]
    [DecidableEq W] (f : Y → W) :
    ∑ w, ((uniformOfFintype Y).map f w).toReal ^ 2 =
      𝔼 y, 𝔼 y', if f y = f y' then (1 : ℝ) else 0 := by
  have h : ∀ w, ((uniformOfFintype Y).map f w).toReal = 𝔼 y, if f y = w then (1 : ℝ) else 0 := by
    intro w
    rw [toReal_map_apply, Fintype.expect_eq_sum_div_card, Finset.sum_div]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [toReal_uniformOfFintype_apply]
    split_ifs <;> simp
  simp_rw [h, sq, Finset.expect_mul_expect, ← Finset.expect_sum_comm]
  refine Finset.expect_congr rfl fun y _ => Finset.expect_congr rfl fun y' _ => ?_
  simp_rw [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp [eq_comm]

end Uniform

/-! ### Equivalences of oracles -/

section Transport

variable {α β γ : Type*} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]

/-- **A uniform law transported along an equivalence** is uniform, against a weight. -/
theorem sum_uniformOfFintype_comp_equiv (e : α ≃ β) (f : β → ℝ≥0∞) :
    ∑ a, uniformOfFintype α a * f (e a) = ∑ b, uniformOfFintype β b * f b := by
  have hc : Fintype.card α = Fintype.card β := Fintype.card_congr e
  simp only [uniformOfFintype_apply, hc]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

omit [Nonempty α] [Nonempty β] in
/-- An average transported along an equivalence. -/
theorem expect_comp_equiv (e : α ≃ β) (f : β → ℝ) : 𝔼 a, f (e a) = 𝔼 b, f b :=
  Fintype.expect_equiv e _ _ fun _ => rfl

/-- **One attempt against a uniform oracle**, read through an equivalence of oracles. -/
theorem jointAttempt_comp_equiv_apply_none (e : α ≃ β) (A : β → PMF (Option γ)) :
    jointAttempt (uniformOfFintype α) (fun a => A (e a)) none =
      jointAttempt (uniformOfFintype β) A none := by
  rw [jointAttempt_apply_none, jointAttempt_apply_none]
  exact sum_uniformOfFintype_comp_equiv e fun b => A b none

omit [Nonempty α] in
/-- **Two attempts with the same accepted masses are equal.** -/
theorem eq_of_apply_some_eq {A B : PMF (Option α)} (h : ∀ a, A (some a) = B (some a)) : A = B := by
  have hn : A none = B none := by
    have : 1 - A none = 1 - B none := by
      rw [← sum_apply_some, ← sum_apply_some]
      exact sum_congr rfl fun a _ => h a
    exact (ENNReal.sub_right_inj ENNReal.one_ne_top (coe_le_one _ _) (coe_le_one _ _)).1 this
  ext o
  cases o
  exacts [hn, h _]

end Transport

/-! ### The column split of a ring's oracle -/

section ColumnSplit

variable {N V C : Type*} [DecidableEq N]

/-- **The column split** of a ring's oracle `H : N × V → C` for the signer `i`: at each column `v`,
the signer's value `H (i, v)` and the other members' values. -/
def columnSplit (i : N) : (N × V → C) ≃ (V → C × ({j // j ≠ i} → C)) where
  toFun H v := (H (i, v), fun j => H (j.1, v))
  invFun F x := if h : x.1 = i then (F x.2).1 else (F x.2).2 ⟨x.1, h⟩
  left_inv H := by
    funext x
    obtain ⟨a, v⟩ := x
    by_cases h : a = i <;> simp [h]
  right_inv F := by
    funext v
    exact Prod.ext (by simp) (funext fun j => by simp [j.2])

theorem columnSplit_apply (i : N) (H : N × V → C) (v : V) :
    columnSplit i H v = (H (i, v), fun j => H (j.1, v)) :=
  rfl

end ColumnSplit

section Quenched

variable {V C Z Y : Type*} [Fintype V] [DecidableEq V] [Fintype C] [Fintype Z] [Fintype Y]
  (P : PMF Y) (w1 : Y → V) (acc : Y → C → Bool)
  (κ : V × C → ℝ≥0∞) (hκ : ∀ a, κ a ≤ 1) (g : V × C × Z → ℝ≥0∞) (hg : ∀ a, g a ≤ 1)
  (w : V × C → ℝ≥0∞)

/-- **The signer's attempt against the oracle `H` with side data**: `y ← P`; with
`(c, z) = H (w1 y)`, reject unless `acc y c`, and keep `w1 y` with probability
`κ (w1 y, c) · g (w1 y, c, z)`. -/
noncomputable def quenchedAttempt (H : V → C × Z) : PMF (Option V) :=
  P.bind fun y =>
    if acc y (H (w1 y)).1 = true then
      keepOrReject (w1 y) (κ (w1 y, (H (w1 y)).1) * g (w1 y, H (w1 y)))
        (mul_le_one' (hκ _) (hg _))
    else PMF.pure none

omit [Fintype C] [Fintype Z] in
/-- The attempt keeps `v` with probability `signerMass v c · κ (v, c) · g (v, c, z)` at
`(c, z) = H v`. -/
theorem quenchedAttempt_apply_some (H : V → C × Z) (v : V) :
    quenchedAttempt P w1 acc κ hκ g hg H (some v) =
      signerMass P w1 acc v (H v).1 * κ (v, (H v).1) * g (v, H v) := by
  rw [quenchedAttempt, bind_apply, tsum_fintype, signerMass, sum_mul, sum_mul]
  refine sum_congr rfl fun y _ => ?_
  by_cases hv : w1 y = v
  · subst hv
    by_cases ha : acc y (H (w1 y)).1 = true <;> simp [ha, keepOrReject_apply_some, mul_assoc]
  · have hv' : v ≠ w1 y := Ne.symm hv
    split_ifs <;> first | (exfalso; tauto) | simp [keepOrReject_apply_some, hv']

/-- **The signer's column deviation** at column `v` with challenge `c`:
`|signerMass v c · κ (v, c) - β · w (v, c)|`. It does not read the keep factor. -/
noncomputable def quenchedColDev (β : ℝ) (v : V) (c : C) : ℝ :=
  |(signerMass P w1 acc v c * κ (v, c)).toReal - β * (w (v, c)).toReal|

/-- **The deviation of the attempt at the oracle `H`** from `β` times the target weight
`w (v, c) · g (v, c, z)`: `∑_v |A_H (some v) - β · w (v, c) · g (v, c, z)|`. -/
noncomputable def quenchedDev (β : ℝ) (H : V → C × Z) : ℝ :=
  ∑ v, |(quenchedAttempt P w1 acc κ hκ g hg H (some v)).toReal -
    β * (w (v, (H v).1) * g (v, H v)).toReal|

omit [Fintype C] [Fintype Z] in
/-- **The deviation is a sum of column terms**: the keep factor times the column deviation. -/
theorem quenchedDev_eq (β : ℝ) (H : V → C × Z) :
    quenchedDev P w1 acc κ hκ g hg w β H =
      ∑ v, (g (v, H v)).toReal * quenchedColDev P w1 acc κ w β v (H v).1 := by
  refine Finset.sum_congr rfl fun v _ => ?_
  have key : ∀ a b c d : ℝ, 0 ≤ c → |a * c - d * (b * c)| = c * |a - d * b| := fun a b c d hc => by
    rw [show a * c - d * (b * c) = c * (a - d * b) by ring, abs_mul, abs_of_nonneg hc]
  have e1 : (signerMass P w1 acc v (H v).1 * κ (v, (H v).1) * g (v, H v)).toReal =
      (signerMass P w1 acc v (H v).1 * κ (v, (H v).1)).toReal * (g (v, H v)).toReal :=
    ENNReal.toReal_mul
  have e2 : (w (v, (H v).1) * g (v, H v)).toReal = (w (v, (H v).1)).toReal * (g (v, H v)).toReal :=
    ENNReal.toReal_mul
  rw [quenchedAttempt_apply_some, quenchedColDev, e1, e2]
  exact key _ _ _ _ ENNReal.toReal_nonneg

omit [Fintype V] [Fintype C] in
include hκ in
/-- A column deviation is at most `Pr[w1 = v] + β`, for a target weight `w ≤ 1`. -/
theorem quenchedColDev_le (hw : ∀ a, w a ≤ 1) {β : ℝ} (hβ : 0 ≤ β) (v : V) (c : C) :
    quenchedColDev P w1 acc κ w β v c ≤ (P.map w1 v).toReal + β := by
  have hm : (signerMass P w1 acc v c * κ (v, c)).toReal ≤ (P.map w1 v).toReal :=
    ENNReal.toReal_mono ((P.map w1).apply_ne_top v)
      ((mul_le_of_le_one_right' (hκ (v, c))).trans (signerMass_le_map P w1 acc v c))
  have hm0 : 0 ≤ (signerMass P w1 acc v c * κ (v, c)).toReal := ENNReal.toReal_nonneg
  have hw1 : (w (v, c)).toReal ≤ 1 := ENNReal.toReal_le_one_of_le_one (hw _)
  have hw0 : 0 ≤ (w (v, c)).toReal := ENNReal.toReal_nonneg
  have hbw : β * (w (v, c)).toReal ≤ β := mul_le_of_le_one_right hβ hw1
  have hbw0 : 0 ≤ β * (w (v, c)).toReal := mul_nonneg hβ hw0
  unfold quenchedColDev
  rw [abs_le]
  constructor <;> linarith

/-- **The total target weight at the oracle `H`**: `∑_v w (v, c) · g (v, c, z)`. -/
noncomputable def quenchedMass (H : V → C × Z) : ℝ :=
  ∑ v, (w (v, (H v).1) * g (v, H v)).toReal

variable [Nonempty C]

/-- **The signer's column error** at column `v`:
`𝔼_c |signerMass v c · κ (v, c) - β · w (v, c)|`. -/
noncomputable def quenchedColError (β : ℝ) (v : V) : ℝ :=
  𝔼 c, quenchedColDev P w1 acc κ w β v c

/-- **The signer's mean weight** at column `v`: `𝔼_c w (v, c)`. -/
noncomputable def quenchedMeanWeight (v : V) : ℝ := 𝔼 c : C, (w (v, c)).toReal

/-- **The signer's relative column error**: `∑_v colError v / 𝔼_c w (v, c)`, over `β · |V|`. It
compares the signer's kept mass at each column with `β` times its own weight, relative to its
mean weight, and does not read the keep factor. -/
noncomputable def quenchedRelColError (β : ℝ) : ℝ :=
  (∑ v, quenchedColError P w1 acc κ w β v / quenchedMeanWeight w v) / (β * Fintype.card V)

omit [Fintype V] [Nonempty C] in
theorem quenchedColError_nonneg (β : ℝ) (v : V) : 0 ≤ quenchedColError P w1 acc κ w β v :=
  Finset.expect_nonneg fun _ _ => abs_nonneg _

omit [Fintype V] [DecidableEq V] [Nonempty C] in
theorem quenchedMeanWeight_nonneg (v : V) : 0 ≤ quenchedMeanWeight w v :=
  Finset.expect_nonneg fun _ _ => ENNReal.toReal_nonneg

variable [Nonempty Z]

/-- **The mean of a sum of column terms against a uniform oracle**: each column of a uniform `H` is
uniform. -/
theorem expect_sum_column (F : V → C × Z → ℝ) :
    𝔼 H : V → C × Z, ∑ v, F v (H v) = ∑ v, 𝔼 cz : C × Z, F v cz := by
  rw [Finset.expect_sum_comm]
  exact Finset.sum_congr rfl fun v _ => expect_apply_eval v (F v)

/-- **The mean deviation against a uniform oracle**: at each column, the mean of the keep factor
times the column deviation. -/
theorem expect_quenchedDev (β : ℝ) :
    𝔼 H : V → C × Z, quenchedDev P w1 acc κ hκ g hg w β H =
      ∑ v, 𝔼 cz : C × Z, (g (v, cz)).toReal * quenchedColDev P w1 acc κ w β v cz.1 := by
  simp only [quenchedDev_eq]
  exact expect_sum_column fun v cz => (g (v, cz)).toReal * quenchedColDev P w1 acc κ w β v cz.1

omit [Nonempty C] [Nonempty Z] in
/-- The mean over a uniform `(c, z)` of a product of a function of `c` and a function of `z` is
the product of the means. -/
theorem expect_prod_mul (φ : C → ℝ) (ψ : Z → ℝ) :
    𝔼 cz : C × Z, φ cz.1 * ψ cz.2 = (𝔼 c, φ c) * 𝔼 z, ψ z := by
  rw [← Finset.univ_product_univ, Finset.expect_product, Finset.expect_mul_expect]

/-- **The mean deviation for a keep factor that does not read `c`**: with `g (v, c, z) = gz (v, z)`,
it is `∑_v 𝔼_z gz (v, z) · colError v`. -/
theorem expect_quenchedDev_of_eq (gz : V × Z → ℝ≥0∞) (hgz : ∀ v c z, g (v, c, z) = gz (v, z))
    (β : ℝ) :
    𝔼 H : V → C × Z, quenchedDev P w1 acc κ hκ g hg w β H =
      ∑ v, (𝔼 z, (gz (v, z)).toReal) * quenchedColError P w1 acc κ w β v := by
  rw [expect_quenchedDev]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [quenchedColError, mul_comm, ← expect_prod_mul]
  refine Finset.expect_congr rfl fun cz _ => ?_
  obtain ⟨c, z⟩ := cz
  rw [hgz, mul_comm]

/-- **The mean total target weight against a uniform oracle.** -/
theorem expect_quenchedMass :
    𝔼 H : V → C × Z, quenchedMass g w H = ∑ v, 𝔼 cz : C × Z, (w (v, cz.1) * g (v, cz)).toReal :=
  expect_sum_column fun v cz => (w (v, cz.1) * g (v, cz)).toReal

/-- **The mean total target weight for a keep factor that does not read `c`**:
`∑_v 𝔼_z gz (v, z) · 𝔼_c w (v, c)`. -/
theorem expect_quenchedMass_of_eq (gz : V × Z → ℝ≥0∞) (hgz : ∀ v c z, g (v, c, z) = gz (v, z)) :
    𝔼 H : V → C × Z, quenchedMass g w H =
      ∑ v, (𝔼 z, (gz (v, z)).toReal) * quenchedMeanWeight w v := by
  rw [expect_quenchedMass]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [quenchedMeanWeight, mul_comm, ← expect_prod_mul]
  refine Finset.expect_congr rfl fun cz _ => ?_
  obtain ⟨c, z⟩ := cz
  rw [hgz, ENNReal.toReal_mul]

end Quenched

/-! ### Bounded differences in one column -/

section Update

variable {V C Z Y : Type*} [Fintype V] [DecidableEq V] [Fintype C] [Fintype Z] [Fintype Y]
  (P : PMF Y) (w1 : Y → V) (acc : Y → C → Bool) (κ : V × C → ℝ≥0∞) (hκ : ∀ a, κ a ≤ 1)
  (g : V × C × Z → ℝ≥0∞) (hg : ∀ a, g a ≤ 1) (w : V × C → ℝ≥0∞)

omit [Fintype C] [Fintype Z] in
/-- **Bounded differences of a sum of column terms**: a sum over the columns of terms with values
in `[0, b v]`, each reading its column of `H`, moves by at most `b v` when `H` changes at `v`. -/
theorem abs_sum_apply_update_le (T : V → C × Z → ℝ) {b : V → ℝ}
    (hT : ∀ v cz, T v cz ∈ Set.Icc 0 (b v)) (H : V → C × Z) (v : V) (cz : C × Z) :
    |∑ v', T v' (Function.update H v cz v') - ∑ v', T v' (H v')| ≤ b v := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single v (fun v' _ hv' => by
    rw [Function.update_of_ne hv', sub_self]) (by simp), Function.update_self]
  have h1 := hT v cz
  have h2 := hT v (H v)
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

omit [Fintype C] [Fintype Z] in
include hg in
/-- **Bounded differences of the deviation**: changing the oracle at column `v` moves the deviation
by at most `Pr[w1 = v] + β`. -/
theorem abs_quenchedDev_update_le (hw : ∀ a, w a ≤ 1) {β : ℝ} (hβ : 0 ≤ β) (H : V → C × Z)
    (v : V) (cz : C × Z) :
    |quenchedDev P w1 acc κ hκ g hg w β (Function.update H v cz) -
        quenchedDev P w1 acc κ hκ g hg w β H| ≤ (P.map w1 v).toReal + β := by
  simp only [quenchedDev_eq]
  exact abs_sum_apply_update_le (fun v cz => (g (v, cz)).toReal *
    quenchedColDev P w1 acc κ w β v cz.1) (fun v cz => ⟨mul_nonneg ENNReal.toReal_nonneg
      (abs_nonneg _), (mul_le_of_le_one_left (abs_nonneg _)
        (ENNReal.toReal_le_one_of_le_one (hg _))).trans
          (quenchedColDev_le P w1 acc κ hκ w hw hβ v cz.1)⟩) H v cz

omit [Fintype C] [Fintype Z] in
include hg in
/-- **Bounded differences of the total target weight**: changing the oracle at column `v` moves it
by at most `1`. -/
theorem abs_quenchedMass_update_le (hw : ∀ a, w a ≤ 1) (H : V → C × Z) (v : V) (cz : C × Z) :
    |quenchedMass g w (Function.update H v cz) - quenchedMass g w H| ≤ 1 :=
  abs_sum_apply_update_le (fun v cz => (w (v, cz.1) * g (v, cz)).toReal) (b := fun _ => 1)
    (fun _ _ => ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_one_of_le_one
      (mul_le_one' (hw _) (hg _))⟩) H v cz

end Update

section QuenchedConc

variable {V C Z Y : Type*} [Fintype V] [DecidableEq V] [Fintype C] [Nonempty C] [Fintype Z]
  [Nonempty Z] [Fintype Y] (P : PMF Y) (w1 : Y → V)
  (acc : Y → C → Bool) (κ : V × C → ℝ≥0∞) (hκ : ∀ a, κ a ≤ 1) (g : V × C × Z → ℝ≥0∞)
  (hg : ∀ a, g a ≤ 1)

/-- **The keep probability** of one attempt against a uniform oracle with side data. -/
noncomputable def quenchedKeepProb : ℝ :=
  (1 - jointAttempt (uniformOfFintype (V → C × Z)) (quenchedAttempt P w1 acc κ hκ g hg) none).toReal

/-- **The oracle concentration term** of the signer with side data: `E_H[(q H / q̄ - 1)⁺]`, with
`q H` the keep probability of one attempt against the oracle `H` and `q̄` its mean over a uniform
`H`. -/
noncomputable def quenchedConc : ℝ :=
  (∑ H, uniformOfFintype (V → C × Z) H *
    ((1 - quenchedAttempt P w1 acc κ hκ g hg H none) /
      (1 - jointAttempt (uniformOfFintype _) (quenchedAttempt P w1 acc κ hκ g hg) none) - 1)).toReal

omit [Fintype Y] in
/-- The oracle concentration term is nonnegative. -/
theorem quenchedConc_nonneg : 0 ≤ quenchedConc P w1 acc κ hκ g hg :=
  ENNReal.toReal_nonneg

/-- **The oracle concentration bound**: if every commitment `w1 y = v` has probability at most
`δ`, the oracle concentration term is at most `√(δ / q̄) / 2`, with `q̄` the keep probability of
one attempt against a uniform oracle. -/
theorem quenchedConc_le {δ : ℝ} (hδ : ∀ v, (P.map w1 v).toReal ≤ δ)
    (h : jointAttempt (uniformOfFintype _) (quenchedAttempt P w1 acc κ hκ g hg) none ≠ 1) :
    quenchedConc P w1 acc κ hκ g hg ≤ √(δ / quenchedKeepProb P w1 acc κ hκ g hg) / 2 := by
  classical
  set U := uniformOfFintype (V → C × Z)
  set A := quenchedAttempt P w1 acc κ hκ g hg
  set J := jointAttempt U A
  set c0 : ℝ := (Fintype.card (V → C × Z) : ℝ)⁻¹
  have hU : ∀ H, (U H).toReal = c0 := fun H => toReal_uniformOfFintype_apply H
  have hc0 : ∑ _H : V → C × Z, c0 = 1 := by
    rw [sum_const, card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)
  have hc0nn : 0 ≤ c0 := inv_nonneg.2 (Nat.cast_nonneg _)
  -- the per-column keep probabilities
  let φ : V → C × Z → ℝ := fun v cz =>
    (signerMass P w1 acc v cz.1 * κ (v, cz.1) * g (v, cz)).toReal
  let G : V → (V → C × Z) → ℝ := fun v H => (A H (some v)).toReal
  have hG : ∀ v H, G v H = φ v (H v) := fun v H => by
    simp only [G, φ, A, quenchedAttempt_apply_some]
  have hφ0 : ∀ v cz, 0 ≤ φ v cz := fun _ _ => ENNReal.toReal_nonneg
  have hφδ : ∀ v cz, φ v cz ≤ δ := fun v cz => by
    refine le_trans (ENNReal.toReal_mono (apply_ne_top _ _) ?_) (hδ v)
    calc signerMass P w1 acc v cz.1 * κ (v, cz.1) * g (v, cz)
        ≤ signerMass P w1 acc v cz.1 * 1 * 1 := by
          gcongr
          · exact hκ _
          · exact hg _
      _ ≤ P.map w1 v := by rw [mul_one, mul_one]; exact signerMass_le_map P w1 acc v _
  set Q : (V → C × Z) → ℝ := fun H => ∑ v, G v H
  have hQ : ∀ H, (1 - A H none).toReal = Q H := fun H => by
    rw [← sum_apply_some, ENNReal.toReal_sum fun v _ => apply_ne_top _ _]
  -- the mean keep probability
  set m := quenchedKeepProb P w1 acc κ hκ g hg with hm_def
  have hsum : ∑ H, U H * (1 - A H none) + J none = 1 := by
    rw [show J = jointAttempt U A from rfl, jointAttempt_apply_none, ← sum_add_distrib]
    calc ∑ H, (U H * (1 - A H none) + U H * A H none) = ∑ H, U H :=
          sum_congr rfl fun H _ => by
            rw [← mul_add, tsub_add_cancel_of_le (coe_le_one _ _), mul_one]
      _ = 1 := sum_coe U
  have hJt : J none ≠ ⊤ := apply_ne_top _ _
  have hm : m = ∑ H, c0 * Q H := by
    rw [hm_def, quenchedKeepProb, ← ENNReal.eq_sub_of_add_eq hJt hsum,
      ENNReal.toReal_sum fun H _ => ENNReal.mul_ne_top (apply_ne_top _ _)
        (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)]
    exact sum_congr rfl fun H _ => by rw [ENNReal.toReal_mul, hU, hQ]
  have hs0 : 1 - J none ≠ 0 := one_sub_apply_none_ne_zero h
  have hm0 : 0 < m := ENNReal.toReal_pos hs0 (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
  -- the second moment
  have hmom : ∑ H, c0 * Q H ^ 2 ≤ m ^ 2 + δ * m := by
    have hexp : ∀ H, c0 * Q H ^ 2 = ∑ v, ∑ v', c0 * (G v H * G v' H) := fun H => by
      rw [sq, show Q H = ∑ v, G v H from rfl, sum_mul_sum, mul_sum]
      exact sum_congr rfl fun v _ => by rw [mul_sum]
    have hpair : ∀ v v', ∑ H, c0 * (G v H * G v' H) ≤
        (∑ H, c0 * G v H) * (∑ H, c0 * G v' H) + if v = v' then δ * ∑ H, c0 * G v H else 0 := by
      intro v v'
      by_cases hvv : v = v'
      · subst hvv
        rw [ite_eq_left rfl]
        have hle : ∑ H, c0 * (G v H * G v H) ≤ δ * ∑ H, c0 * G v H := by
          rw [mul_sum]
          refine sum_le_sum fun H _ => ?_
          rw [hG]
          have h0 := hφ0 v (H v)
          have h1 := hφδ v (H v)
          have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 h0) hc0nn
          linarith
        have hsq : 0 ≤ (∑ H, c0 * G v H) * (∑ H, c0 * G v H) := mul_self_nonneg _
        linarith
      · rw [ite_eq_right hvv, add_zero]
        simp only [hG]
        have h1 := sum_pi_mul_apply_mul_apply hvv (φ v) (φ v')
        have h2 := sum_pi_mul_apply v (φ v)
        have h3 := sum_pi_mul_apply v' (φ v')
        exact le_of_eq (h1.trans (by rw [← h2, ← h3]))
    calc ∑ H, c0 * Q H ^ 2 = ∑ v, ∑ v', ∑ H, c0 * (G v H * G v' H) := by
          simp only [hexp]
          rw [sum_comm]
          exact sum_congr rfl fun v _ => sum_comm
      _ ≤ ∑ v, ∑ v', ((∑ H, c0 * G v H) * (∑ H, c0 * G v' H) +
            if v = v' then δ * ∑ H, c0 * G v H else 0) :=
          sum_le_sum fun v _ => sum_le_sum fun v' _ => hpair v v'
      _ = (∑ v, ∑ H, c0 * G v H) ^ 2 + δ * ∑ v, ∑ H, c0 * G v H := by
          simp only [sum_add_distrib, sum_ite_eq, mem_univ, ite_true, ← mul_sum, ← sum_mul, sq]
      _ = m ^ 2 + δ * m := by
          have : ∑ v, ∑ H, c0 * G v H = m := by
            rw [hm, sum_comm]
            exact sum_congr rfl fun H _ => by rw [← mul_sum]
          rw [this]
  -- the concentration term in `ℝ`
  set X : (V → C × Z) → ℝ := fun H => Q H / m - 1
  have hconc : quenchedConc P w1 acc κ hκ g hg = ∑ H, c0 * max (X H) 0 := by
    rw [quenchedConc, ENNReal.toReal_sum fun H _ => ENNReal.mul_ne_top (apply_ne_top _ _)
      (ne_top_of_le_ne_top (ENNReal.div_ne_top ENNReal.one_ne_top hs0)
        (tsub_le_self.trans (ENNReal.div_le_div_right tsub_le_self _)))]
    refine sum_congr rfl fun H _ => ?_
    rw [ENNReal.toReal_mul, hU, ENNReal.toReal_tsub_one (ENNReal.div_ne_top
      (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self) hs0), ENNReal.toReal_div, hQ]
    rfl
  have hX0 : ∑ H, c0 * X H = 0 := by
    simp only [X, mul_sub, mul_one, sum_sub_distrib, hc0, mul_div_assoc', ← sum_div, ← hm,
      div_self hm0.ne', sub_self]
  have hmax : ∀ x : ℝ, max x 0 = (x + |x|) / 2 := fun x => by
    rcases le_total 0 x with hx | hx
    · rw [max_eq_left hx, abs_of_nonneg hx]; ring
    · rw [max_eq_right hx, abs_of_nonpos hx]; ring
  have hX2 : ∑ H, c0 * X H ^ 2 ≤ δ / m := by
    have hexp : ∀ H, c0 * X H ^ 2 = c0 * Q H ^ 2 / m ^ 2 - 2 * (c0 * Q H) / m + c0 := fun H => by
      simp only [X]; field_simp; ring
    have hmom' : c0 * ∑ H, Q H ^ 2 ≤ m ^ 2 + δ * m := by rw [mul_sum]; exact hmom
    simp only [hexp, sum_add_distrib, sum_sub_distrib, ← sum_div, ← mul_sum, ← hm, hc0]
    have : (c0 * ∑ H, Q H ^ 2) / m ^ 2 ≤ (m ^ 2 + δ * m) / m ^ 2 :=
      div_le_div_of_nonneg_right hmom' (by positivity)
    have h2 : (m ^ 2 + δ * m) / m ^ 2 = 1 + δ / m := by field_simp
    rw [show 2 * m / m = 2 by field_simp]
    linarith
  have hexpect : ∀ f : (V → C × Z) → ℝ, ∑ H, c0 * f H = 𝔼 H, f H := fun f => by
    rw [Fintype.expect_eq_sum_div_card, sum_div]
    exact sum_congr rfl fun H _ => by rw [div_eq_inv_mul]
  have habs : ∑ H, c0 * |X H| ≤ √(δ / m) := by
    rw [hexpect]
    calc 𝔼 H, |X H| = 𝔼 H, √(X H ^ 2) := by simp only [Real.sqrt_sq_eq_abs]
      _ ≤ √(𝔼 H, X H ^ 2) := Real.expect_sqrt_le_sqrt_expect _ fun H => sq_nonneg _
      _ ≤ √(δ / m) := Real.sqrt_le_sqrt (by rw [← hexpect]; exact hX2)
  rw [hconc]
  calc ∑ H, c0 * max (X H) 0 = (∑ H, c0 * X H + ∑ H, c0 * |X H|) / 2 := by
        simp only [hmax, mul_div_assoc', ← sum_div, mul_add, sum_add_distrib]
    _ ≤ √(δ / m) / 2 := by rw [hX0, zero_add]; gcongr

end QuenchedConc

/-! ### The ring attempt with excluded sets -/

section RingConc

variable {N V C Y : Type*} [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V] [Fintype C]
  [DecidableEq C] [Nonempty C] (E : ExclSets N C) (i : N) [Fintype Y] (P : PMF Y) (w1 : Y → V)
  (acc : Y → C → Bool) (κ : V × C → ℝ≥0∞) (hκ : ∀ a, κ a ≤ 1)

/-- **The pass factor** of the ring attempt: `1` if every other member's value misses its excluded
set, else `0`. -/
def passFactor (a : V × C × ({j // j ≠ i} → C)) : ℝ≥0∞ :=
  if ∀ j, a.2.2 j ∉ E.excl j.1 then 1 else 0

omit [Fintype V] [DecidableEq V] [Nonempty C] in
theorem passFactor_le_one (a : V × C × ({j // j ≠ i} → C)) : passFactor E i a ≤ 1 := by
  unfold passFactor
  split_ifs <;> simp

omit [Nonempty C] in
/-- **The ring attempt is the core attempt** with the pass factor, read through the column
split. -/
theorem ringAttempt_eq_quenchedAttempt (H : N × V → C) :
    ringAttempt E i P w1 acc κ hκ H =
      quenchedAttempt P w1 acc κ hκ (passFactor E i) (passFactor_le_one E i) (columnSplit i H) := by
  refine eq_of_apply_some_eq fun v => ?_
  rw [ringAttempt_apply_some, quenchedAttempt_apply_some, columnSplit_apply]
  congr 1
  have hiff : nonSignerPass E i H v ↔ ∀ j : {j // j ≠ i}, H (j.1, v) ∉ E.excl j.1 :=
    ⟨fun h j => h j.1 j.2, fun h j hj => h ⟨j, hj⟩⟩
  unfold passFactor
  by_cases h : nonSignerPass E i H v
  · rw [ite_eq_left h, ite_eq_left (hiff.1 h)]
  · rw [ite_eq_right h, ite_eq_right (mt hiff.2 h)]

/-- **The ring's oracle concentration term is the core's**, with the pass factor. -/
theorem oracleConcError_eq_quenchedConc :
    oracleConcError E i P w1 acc κ hκ =
      quenchedConc P w1 acc κ hκ (passFactor E i) (passFactor_le_one E i) := by
  have hA : ringAttempt E i P w1 acc κ hκ = fun H => quenchedAttempt P w1 acc κ hκ
      (passFactor E i) (passFactor_le_one E i) (columnSplit i H) :=
    funext (ringAttempt_eq_quenchedAttempt E i P w1 acc κ hκ)
  rw [oracleConcError, quenchedConc, hA, jointAttempt_comp_equiv_apply_none (columnSplit i)]
  beta_reduce
  exact congrArg ENNReal.toReal (sum_uniformOfFintype_comp_equiv (columnSplit i) fun F =>
    (1 - quenchedAttempt P w1 acc κ hκ (passFactor E i) (passFactor_le_one E i) F none) /
      (1 - jointAttempt (uniformOfFintype _)
        (quenchedAttempt P w1 acc κ hκ (passFactor E i) (passFactor_le_one E i)) none) - 1)

/-- **The oracle concentration bound of the ring attempt**: if every commitment `w1 y = v` has
probability at most `δ`, the term is at most `√(δ / q̄) / 2`, with `q̄` the keep probability of one
ring attempt against a uniform oracle (`quenchedConc_le` with the pass factor). -/
theorem oracleConcError_le {δ : ℝ} (hδ : ∀ v, (P.map w1 v).toReal ≤ δ)
    (h : jointAttempt (uniformOfFintype _) (ringAttempt E i P w1 acc κ hκ) none ≠ 1) :
    oracleConcError E i P w1 acc κ hκ ≤
      √(δ / (1 - jointAttempt (uniformOfFintype _) (ringAttempt E i P w1 acc κ hκ) none).toReal)
        / 2 := by
  have hA : ringAttempt E i P w1 acc κ hκ = fun H => quenchedAttempt P w1 acc κ hκ
      (passFactor E i) (passFactor_le_one E i) (columnSplit i H) :=
    funext (ringAttempt_eq_quenchedAttempt E i P w1 acc κ hκ)
  rw [hA, jointAttempt_comp_equiv_apply_none (columnSplit i)] at h ⊢
  rw [oracleConcError_eq_quenchedConc]
  exact quenchedConc_le P w1 acc κ hκ _ _ hδ h

end RingConc

end PMF
