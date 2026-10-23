-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.LayerPolynomial
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Nat.Bitwise

@[expose] public section

/-!
# Random evaluation of GKR claims

The selector is the actual product of Boolean equality factors. Nonzero
residual tables therefore give nonzero multilinear polynomials, with total
degree at most the number of challenge coordinates. Assertion nonzeroness
uses the fixed distinct-assertion-gate invariant, not a witness condition.
-/
namespace GordieHowe.GKR.ClaimEvaluation
open MvPolynomial
open scoped Classical NNReal
section
variable {F : Type} [Field F] {d : ℕ}
open LayerPolynomial (Cube boolValue)

noncomputable def chi (b : Cube d) : MvPolynomial (Fin d) F :=
  ∏ j, if b j then X j else 1 - X j

noncomputable def mle (w : Cube d → F) : MvPolynomial (Fin d) F := ∑ b, C (w b) * chi b

def value (w : Cube d → F) (r : Fin d → F) : F :=
  ∑ b, w b * ∏ j, if b j then r j else 1 - r j

@[simp] theorem eval_chi (b : Cube d) (r : Fin d → F) :
    eval r (chi b) = ∏ j, if b j then r j else 1-r j := by
  simp only [chi, map_prod]
  apply Finset.prod_congr rfl
  intro j _
  cases b j <;> simp

@[simp] theorem eval_mle (w : Cube d → F) (r : Fin d → F) :
    eval r (mle w) = value w r := by simp [mle, value]

/-- `chi b` has degree at most one in each variable. -/
theorem chi_degreeOf_le (b : Cube d) (v : Fin d) :
    (chi b : MvPolynomial (Fin d) F).degreeOf v ≤ 1 := by
  apply (degreeOf_prod_le v Finset.univ _).trans
  have hterm (j : Fin d) :
      (if b j then X j else 1 - X j : MvPolynomial (Fin d) F).degreeOf v ≤
        if v = j then 1 else 0 := by
    cases b j
    · exact (degreeOf_sub_le v _ _).trans (by simp [degreeOf_X, degreeOf_one])
    · simp [degreeOf_X]
  apply (Finset.sum_le_sum fun j _ => hterm j).trans
  simp

/-- A multilinear extension has degree at most one in each variable. -/
theorem mle_degreeOf_le (w : Cube d → F) (v : Fin d) : (mle w).degreeOf v ≤ 1 := by
  apply (degreeOf_sum_le v Finset.univ _).trans
  apply Finset.sup_le
  intro b _
  exact (degreeOf_C_mul_le _ _ _).trans (chi_degreeOf_le b v)

theorem chi_eq_selector (b : Cube d) :
    (chi b : MvPolynomial (Fin d) F) =
      rename Prod.snd (LayerPolynomial.selector false b) := by
  simp only [chi, LayerPolynomial.selector, map_prod]
  apply Finset.prod_congr rfl
  intro j _
  cases b j <;> simp

theorem chi_binary (n : ℕ) (r : Fin d → F) :
    eval r (chi (LayerPolynomial.binaryLabel n)) = PackedClaim.eqPt r n := by
  rw [eval_chi]
  rfl

@[simp] theorem chi_boolean (b x : Cube d) :
    eval (fun j => boolValue (F := F) (x j)) (chi b) = if b = x then 1 else 0 := by
  rw [chi_eq_selector, eval_rename]
  have hp : (fun j => boolValue (F := F) (x j)) ∘ Prod.snd =
      LayerPolynomial.point x x := by
    funext v
    rcases v with ⟨h,j⟩
    cases h <;> rfl
  rw [hp]
  exact LayerPolynomial.selector_eval false b x x

@[simp] theorem mle_boolean (w : Cube d → F) (x : Cube d) :
    eval (fun j => boolValue (F := F) (x j)) (mle w) = w x := by
  simp only [mle, map_sum, map_mul, eval_C, chi_boolean, mul_ite, mul_one, mul_zero]
  simp

theorem chi_degree (b : Cube d) : (chi b : MvPolynomial (Fin d) F).totalDegree ≤ d := by
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _j : Fin d, 1 := Finset.sum_le_sum (fun j _ => by
      cases b j
      · exact (totalDegree_sub _ _).trans (by simp)
      · simp)
    _ = d := by simp

theorem mle_degree (w : Cube d → F) : (mle w).totalDegree ≤ d := by
  apply totalDegree_finsetSum_le
  intro b _
  exact (totalDegree_mul _ _).trans (by simpa using chi_degree (F := F) b)

theorem mle_ne_zero (w : Cube d → F) (hne : ∃ b, w b ≠ 0) : mle w ≠ 0 := by
  intro h
  obtain ⟨b, hb⟩ := hne
  have he := congrArg (eval (fun j => boolValue (F := F) (b j))) h
  exact hb (by simpa only [mle_boolean, map_zero] using he)

theorem evaluation_count [Fintype F] (w : Cube d → F) (hne : ∃ b, w b ≠ 0) :
    (Finset.univ.filter fun r => value w r = 0).card * Fintype.card F ≤
      d * Fintype.card F ^ d := by
  have hF : (0 : ℚ≥0) < (Fintype.card F : ℚ≥0) := by exact_mod_cast Fintype.card_pos (α := F)
  have h := schwartz_zippel_totalDegree (mle_ne_zero w hne) (Finset.univ : Finset F)
  rw [Fintype.piFinset_univ, Finset.card_univ] at h
  rw [div_le_div_iff₀ (by positivity) hF] at h
  have hn : (Finset.univ.filter fun r => value w r = 0).card * Fintype.card F ≤
      (mle w).totalDegree * Fintype.card F ^ d := by
    simpa only [eval_mle] using (show
      (Finset.univ.filter fun r => eval r (mle w) = 0).card * Fintype.card F ≤
        (mle w).totalDegree * Fintype.card F ^ d by exact_mod_cast h)
  exact hn.trans (Nat.mul_le_mul_right _ (mle_degree w))

theorem evaluation_count_nnreal [Fintype F] (w : Cube d → F) (hne : ∃ b, w b ≠ 0) :
    ((Finset.univ.filter fun r => value w r = 0).card : ℝ≥0) ≤
      (d / (Fintype.card F : ℝ≥0)) * Fintype.card (Fin d → F) := by
  rw [div_mul_eq_mul_div, le_div_iff₀ (by exact_mod_cast Fintype.card_pos (α := F))]
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using
    (show ((Finset.univ.filter fun r => value w r = 0).card : ℝ≥0) * Fintype.card F ≤
      d * (Fintype.card F : ℝ≥0)^d by exact_mod_cast evaluation_count w hne)

/-- A single scalar batches the two input claims. -/
theorem scalar_batch_count [Fintype F] (e0 e1 : F) (h : e0 ≠ 0 ∨ e1 ≠ 0) :
    (Finset.univ.filter fun r : F => e0 + r * e1 = 0).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro r hr s hs
  have hr' := (Finset.mem_filter.mp hr).2
  have hs' := (Finset.mem_filter.mp hs).2
  have he : (r-s)*e1=0 := by linear_combination hr' - hs'
  rcases mul_eq_zero.mp he with he | he
  · exact sub_eq_zero.mp he
  · exact False.elim (h.elim (fun hn => hn (by simpa [he] using hr')) (fun hn => hn he))

/-- One coordinate of a multilinear table is bound to a challenge. -/
def collapse (w : Cube d → F) (i : Fin d) (r : F) (b : Cube d) : F :=
  (1-r)*w (Function.update b i false) + r*w (Function.update b i true)

/-- A nonzero multilinear table cannot disappear at more than one scalar
specialization, even after earlier coordinates have been fixed. -/
theorem collapse_count [Fintype F] (w : Cube d → F) (hne : ∃ b, w b ≠ 0) (i : Fin d) :
    (Finset.univ.filter fun r : F => ∀ b, collapse w i r b = 0).card ≤ 1 := by
  obtain ⟨b,hb⟩ := hne
  let c0 := w (Function.update b i false)
  let c1 := w (Function.update b i true)
  have hc : c0 ≠ 0 ∨ c1-c0 ≠ 0 := by
    by_contra h
    push Not at h
    have hc1 : c1 = 0 := by linear_combination h.1 + h.2
    have hb0 : w b = 0 := by
      cases hi : b i
      · have he : Function.update b i false = b := by rw [← hi]; exact Function.update_eq_self i b
        simpa only [c0, he] using h.1
      · have he : Function.update b i true = b := by rw [← hi]; exact Function.update_eq_self i b
        simpa only [c1, he] using hc1
    exact hb hb0
  apply (Finset.card_le_card (t := Finset.univ.filter fun r : F => c0+r*(c1-c0)=0) ?_).trans
    (scalar_batch_count c0 (c1-c0) hc)
  intro r hr
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hh := (Finset.mem_filter.mp hr).2 b
  dsimp [collapse] at hh
  dsimp [c0,c1]
  linear_combination hh

theorem weight_update (b : Cube d) (g : Fin d → F) (i : Fin d) (r : F) :
    (∏ j, if b j then (Function.update g i r) j else 1-(Function.update g i r) j) =
      (if b i then r else 1-r) * ∏ j ∈ Finset.univ.erase i, if b j then g j else 1-g j := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- The actual equality-weight evaluation is affine in the next coordinate. -/
theorem value_update (w : Cube d → F) (g : Fin d → F) (i : Fin d) (r : F) :
    value w (Function.update g i r) =
      (1-r)*value w (Function.update g i 0) + r*value w (Function.update g i 1) := by
  simp only [value, weight_update, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  cases b i <;> simp <;> ring

/-- Boolean evaluation of a coordinate specialization is the collapsed table. -/
theorem value_update_boolean (w : Cube d → F) (b : Cube d) (i : Fin d) (r : F) :
    value w (Function.update (fun j => boolValue (F := F) (b j)) i r) = collapse w i r b := by
  rw [value_update]
  have hpoint (v : Bool) :
      Function.update (fun j => boolValue (F := F) (b j)) i (boolValue v) =
        fun j => boolValue (Function.update b i v j) := by
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [Function.update_of_ne hj]
  have hzero := hpoint false
  have hone := hpoint true
  change Function.update (fun j => boolValue (F := F) (b j)) i 0 = _ at hzero
  change Function.update (fun j => boolValue (F := F) (b j)) i 1 = _ at hone
  rw [hzero, hone]
  simp only [← eval_mle, mle_boolean, collapse]

/-- If specialization makes the actual remaining MLE function identically
zero, its challenge belongs to a set of cardinal at most one. -/
theorem specialization_count [Fintype F] (w : Cube d → F) (hne : ∃ b, w b ≠ 0)
    (i : Fin d) :
    (Finset.univ.filter fun r : F => ∀ g, value w (Function.update g i r) = 0).card ≤ 1 := by
  apply (Finset.card_le_card (t := Finset.univ.filter fun r : F => ∀ b, collapse w i r b = 0) ?_).trans
    (collapse_count w hne i)
  intro r hr
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro b
  rw [← value_update_boolean]
  exact (Finset.mem_filter.mp hr).2 _

/-- Substitute one challenge coordinate while retaining all other variables. -/
noncomputable def specialize (p : MvPolynomial (Fin d) F) (i : Fin d) (r : F) :
    MvPolynomial (Fin d) F := eval₂Hom C (fun j => if j = i then C r else X j) p

theorem eval_specialize (p : MvPolynomial (Fin d) F) (i : Fin d) (r : F)
    (g : Fin d → F) : eval g (specialize p i r) = eval (Function.update g i r) p := by
  unfold specialize
  rw [map_eval₂Hom]
  have hC : (eval g).comp C = RingHom.id F := by ext x; simp
  rw [hC]
  change eval (fun j => eval g (if j = i then C r else X j)) p = _
  have hg : (fun j => eval g (if j = i then C r else X j)) = Function.update g i r := by
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [hj]
  rw [hg]

/-- Polynomial-zero specialization is covered by the scalar collapse bound. -/
theorem polynomial_specialization_count [Fintype F] (w : Cube d → F)
    (hne : ∃ b, w b ≠ 0) (i : Fin d) :
    (Finset.univ.filter fun r : F => specialize (mle w) i r = 0).card ≤ 1 := by
  apply (Finset.card_le_card (t := Finset.univ.filter fun r : F =>
      ∀ g, value w (Function.update g i r) = 0) ?_).trans (specialization_count w hne i)
  intro r hr
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro g
  rw [← eval_mle, ← eval_specialize, (Finset.mem_filter.mp hr).2, map_zero]

/-- The bit labels of distinct bounded integer indices are distinct. -/
theorem binaryLabel_injective (d : ℕ) :
    Function.Injective (fun i : Fin (2^d) => LayerPolynomial.binaryLabel (d := d) i.val) := by
  intro x y h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < d
  · exact congrFun h ⟨j,hj⟩
  · have hdj : d ≤ j := by omega
    have hp : 2^d ≤ 2^j := Nat.pow_le_pow_right (by decide) hdj
    rw [Nat.testBit_eq_false_of_lt (x.isLt.trans_le hp),
      Nat.testBit_eq_false_of_lt (y.isLt.trans_le hp)]

/-- The actual little-endian integer-to-cube indexing convention. -/
noncomputable def binaryLabelEquiv (d : ℕ) : Fin (2^d) ≃ Cube d :=
  Equiv.ofBijective (fun i => LayerPolynomial.binaryLabel i.val)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨binaryLabel_injective d, by simp [Cube]⟩)

@[simp] theorem binaryLabelEquiv_apply (i : Fin (2^d)) (j : Fin d) :
    binaryLabelEquiv d i j = i.val.testBit j.val := rfl

/-- The integer-indexed equality-weight expression checked by the verifier. -/
def evalTable (w : Fin (2^d) → F) (g : Fin d → F) : F :=
  ∑ i, PackedClaim.eqPt g i.val * w i

theorem evalTable_eq_value (w : Fin (2^d) → F) (g : Fin d → F) :
    evalTable w g = value (fun b => w ((binaryLabelEquiv d).symm b)) g := by
  unfold evalTable value
  rw [← (binaryLabelEquiv d).sum_comp (fun b =>
    w ((binaryLabelEquiv d).symm b) * ∏ j, if b j then g j else 1-g j)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Equiv.symm_apply_apply]
  change PackedClaim.eqPt g i.val * w i = w i * PackedClaim.eqPt g i.val
  exact mul_comm _ _

theorem evalTable_count [Fintype F] (w : Fin (2^d) → F) (hne : ∃ i, w i ≠ 0) :
    (Finset.univ.filter fun g => evalTable w g = 0).card * Fintype.card F ≤
      d * Fintype.card F^d := by
  simp only [evalTable_eq_value]
  apply evaluation_count
  obtain ⟨i,hi⟩ := hne
  exact ⟨binaryLabelEquiv d i, by simpa using hi⟩

variable {G W T : ℕ}

/-- Zero padding an indexed gate table into the Boolean cube. -/
def padded (label : Fin G → Cube d) (v : Fin G → F) (b : Cube d) : F :=
  ∑ g, if label g = b then v g else 0

theorem padded_at (label : Fin G → Cube d) (hinj : Function.Injective label)
    (v : Fin G → F) (g : Fin G) : padded label v (label g) = v g := by
  simp [padded, hinj.eq_iff]

/-- Padding preserves the exact weighted gate sum. -/
theorem value_padded (label : Fin G → Cube d) (v : Fin G → F) (r : Fin d → F) :
    value (padded label v) r = ∑ g, v g * eval r (chi (label g)) := by
  simp only [value, padded, Finset.sum_mul, eval_chi]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  simp

/-- Assertion random evaluation is the actual shared-weight assertion sum. -/
theorem assertion_value (Q : GKR.Layer F G W T) (label : Fin G → Cube d)
    (w : Fin W → F) (r : Fin d → F) :
    value (padded label (Layer.assertions Q w)) r =
      Layer.asserted Q w (fun g => eval r (chi (label g))) := by
  rw [value_padded]
  simp only [Layer.assertions, Layer.asserted, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (Q i).coefficient = 0
  · simp [hi, mul_comm]
  · simp [hi]

end
end GordieHowe.GKR.ClaimEvaluation
