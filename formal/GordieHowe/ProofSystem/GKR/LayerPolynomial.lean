-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.Layer
public import GordieHowe.ProofSystem.RingSwitching.PackedClaim

@[expose] public section

/-!
# The no-copy Longfellow layer polynomial

Variable hands are source `h[0]` and `h[1]`. `binaryLabel` uses little-endian
`Nat.testBit` coordinates, as in `Eqs::raw_eq`. The witness table includes all
padded cube positions. Wiring uses `Quad::prep_v`'s zero-coefficient replacement.
This is a single-layer result; scheduling and compiled wire mapping are separate.
-/
namespace GordieHowe.GKR.LayerPolynomial
open scoped Classical
open MvPolynomial
variable {F : Type} [Field F] {d G W T : ℕ}
abbrev Cube (d : ℕ) := Fin d → Bool
abbrev Vars (d : ℕ) := Bool × Fin d

def binaryLabel (n : ℕ) : Cube d := fun j => n.testBit j

def boolValue (b : Bool) : F := if b then 1 else 0

def point (x y : Cube d) : Vars d → F := fun (h, j) =>
  boolValue (if h then y j else x j)

noncomputable def selector (hand : Bool) (b : Cube d) : MvPolynomial (Vars d) F :=
  ∏ j, if b j then X (hand, j) else 1 - X (hand, j)

/-- The source integer-index equality weights are exactly the selector
polynomials evaluated on the corresponding hand, with bit zero first. -/
theorem selector_binary_eval (hand : Bool) (n : ℕ) (r : Vars d → F) :
    eval r (selector hand (binaryLabel n)) =
      GordieHowe.PackedClaim.eqPt (fun j => r (hand, j)) n := by
  simp only [selector, binaryLabel, GordieHowe.PackedClaim.eqPt, map_prod]
  apply Finset.prod_congr rfl
  intro j _
  split <;> simp_all

noncomputable def mle (hand : Bool) (w : Cube d → F) : MvPolynomial (Vars d) F :=
  ∑ b, C (w b) * selector hand b

@[simp] theorem selector_eval (hand : Bool) (b x y : Cube d) :
    eval (point x y) (selector hand b : MvPolynomial (Vars d) F) =
      if b = (if hand then y else x) then 1 else 0 := by
  classical
  simp only [selector, map_prod]
  by_cases hb : b = (if hand then y else x)
  · subst b
    simp only [ite_true]
    apply Finset.prod_eq_one
    intro j _
    cases hand <;> cases hx : x j <;> cases hy : y j <;> simp [point, boolValue, hx, hy]
  · simp only [hb, ite_false]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hb
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    cases hand <;> cases hbx : b j <;> cases hx : x j <;> cases hy : y j <;>
      simp_all [point, boolValue]

@[simp] theorem mle_eval (hand : Bool) (w : Cube d → F) (x y : Cube d) :
    eval (point x y) (mle hand w) = w (if hand then y else x) := by
  classical
  simp [mle]

theorem selector_degree (hand : Bool) (b : Cube d) (v : Vars d) :
    (selector hand b : MvPolynomial (Vars d) F).degreeOf v ≤ if v.1 = hand then 1 else 0 := by
  classical
  apply (degreeOf_prod_le v Finset.univ _).trans
  have hterm (j : Fin d) :
      (if b j then X (hand,j) else 1-X (hand,j) : MvPolynomial (Vars d) F).degreeOf v ≤
        if v = (hand,j) then 1 else 0 := by
    cases hb : b j
    · apply (degreeOf_sub_le v _ _).trans
      simp [degreeOf_X]
    · simp [degreeOf_X]
  apply (Finset.sum_le_sum fun j _ => hterm j).trans
  rcases v with ⟨h,i⟩
  by_cases hh : h = hand
  · subst h
    simp
  · simp [hh]

theorem mle_degree (hand : Bool) (w : Cube d → F) (v : Vars d) :
    (mle hand w).degreeOf v ≤ if v.1 = hand then 1 else 0 := by
  apply (degreeOf_sum_le v Finset.univ _).trans
  apply Finset.sup_le
  intro b _
  exact (degreeOf_C_mul_le _ _ _).trans (selector_degree hand b v)

noncomputable def coefficient (Q : GKR.Layer F G W T)
    (weight : Fin G → F) (beta : F) (i : Fin T) : F :=
  if (Q i).coefficient = 0 then beta * weight (Q i).gate
  else (Q i).coefficient * weight (Q i).gate

/-- `coefficient` with the zero test decided by the field's own decidable equality: the
executable form the verifier and the honest prover compute. -/
def coefficientDec [DecidableEq F] (Q : GKR.Layer F G W T)
    (weight : Fin G → F) (beta : F) (i : Fin T) : F :=
  if (Q i).coefficient = 0 then beta * weight (Q i).gate
  else (Q i).coefficient * weight (Q i).gate

theorem coefficientDec_eq [DecidableEq F] (Q : GKR.Layer F G W T)
    (weight : Fin G → F) (beta : F) (i : Fin T) :
    coefficientDec Q weight beta i = coefficient Q weight beta i := by
  unfold coefficientDec coefficient
  split_ifs <;> rfl

noncomputable def wiring (Q : GKR.Layer F G W T) (label : Fin W → Cube d)
    (weight : Fin G → F) (beta : F) : MvPolynomial (Vars d) F :=
  ∑ i, C (coefficient Q weight beta i) *
    (selector false (label (Q i).left) * selector true (label (Q i).right))

/-- The scalar wiring evaluation is the source `bind_gh_all` sum over
corners, using its integer h0/h1 indices and exact `prep_v` coefficients. -/
theorem wiring_binary_eval (Q : GKR.Layer F G W T)
    (weight : Fin G → F) (beta : F) (r : Vars d → F) :
    eval r (wiring Q (fun i => binaryLabel i.val) weight beta) =
      ∑ i, coefficient Q weight beta i *
        (GordieHowe.PackedClaim.eqPt (fun j => r (false,j)) (Q i).left.val *
         GordieHowe.PackedClaim.eqPt (fun j => r (true,j)) (Q i).right.val) := by
  simp [wiring, selector_binary_eval]

noncomputable def target (Q : GKR.Layer F G W T) (label : Fin W → Cube d)
    (w : Cube d → F) (weight : Fin G → F) (beta : F) : MvPolynomial (Vars d) F :=
  wiring Q label weight beta * (mle false w * mle true w)

theorem wiring_degree (Q : GKR.Layer F G W T) (label : Fin W → Cube d)
    (weight : Fin G → F) (beta : F) (v : Vars d) :
    (wiring Q label weight beta).degreeOf v ≤ 1 := by
  apply (degreeOf_sum_le v Finset.univ _).trans
  apply Finset.sup_le
  intro i _
  apply (degreeOf_C_mul_le _ _ _).trans
  apply (degreeOf_mul_le v _ _).trans
  have h0 := selector_degree (F := F) false (label (Q i).left) v
  have h1 := selector_degree (F := F) true (label (Q i).right) v
  cases h : v.1 <;> simp [h] at h0 h1 <;> omega

/-- Every variable has degree at most two: once in wiring and once in its witness hand. -/
theorem target_degree (Q : GKR.Layer F G W T) (label : Fin W → Cube d)
    (w : Cube d → F) (weight : Fin G → F) (beta : F) (v : Vars d) :
    (target Q label w weight beta).degreeOf v ≤ 2 := by
  apply (degreeOf_mul_le v _ _).trans
  have hw := wiring_degree Q label weight beta v
  have hm := degreeOf_mul_le v (mle false w) (mle true w)
  have h0 := mle_degree false w v
  have h1 := mle_degree true w v
  cases h : v.1 <;> simp [h] at h0 h1 <;> omega

/-- The terminal expression factors as in `bind_gh_all` and `layer_end`. -/
theorem terminal (Q : GKR.Layer F G W T) (label : Fin W → Cube d)
    (w : Cube d → F) (weight : Fin G → F) (beta : F) (r : Vars d → F) :
    eval r (target Q label w weight beta) =
      eval r (wiring Q label weight beta) * (eval r (mle false w) * eval r (mle true w)) := by
  simp [target]

/-- The Boolean sum recovers `prep_v` binding, including shared-beta assertions. -/
theorem cube_sum (Q : GKR.Layer F G W T) (label : Fin W → Cube d)
    (w : Cube d → F) (weight : Fin G → F) (beta : F) :
    (∑ x : Cube d, ∑ y : Cube d, eval (point x y) (target Q label w weight beta)) =
      Layer.bind Q (w ∘ label) weight beta := by
  classical
  simp only [target, map_mul, mle_eval, Bool.false_eq_true, ↓reduceIte]
  simp only [wiring, map_sum, map_mul, eval_C, selector_eval, Bool.false_eq_true, ↓reduceIte]
  simp_rw [Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext x
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  unfold Layer.bind
  apply Finset.sum_congr rfl
  intro i _
  simp [Layer.product, coefficient, mul_assoc]

/-- The exact incoming target under Longfellow's shared alpha and beta. -/
theorem cube_sum_combined (Q : GKR.Layer F G W T) (label : Fin W → Cube d)
    (w : Cube d → F) (weight0 weight1 : Fin G → F) (alpha beta : F) :
    (∑ x : Cube d, ∑ y : Cube d,
      eval (point x y) (target Q label w (fun g => weight0 g + alpha * weight1 g) beta)) =
      Layer.ordinary Q (w ∘ label) weight0 +
        alpha * Layer.ordinary Q (w ∘ label) weight1 +
        beta * (Layer.asserted Q (w ∘ label) weight0 +
          alpha * Layer.asserted Q (w ∘ label) weight1) := by
  rw [cube_sum, Layer.bind_combined]

end GordieHowe.GKR.LayerPolynomial
