-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA.Signing.Ideal
public import GordieHowe.Foundations.ToMathlib.NNRatENNReal

@[expose] public section

/-!
# The public cut-off of the flattened ML-DSA signer

The flattened signer keeps an accepted attempt at `(w₁, c̃)` with probability
`min(1, val(c̃) / aw)`, `aw` the acceptance weight there and `val` a public function of the
commitment hash (`Cutoff`), the public level `top` times a shape in `(0, 1]`. The kept mass of an
attempt is then `K · min(aw, val(c̃)) = K · top · min(1, aw / val(c̃)) · shape(c̃)`.

* `Cutoff`, `Cutoff.const`: the cut-off and the constant cut-off (`top = β`, shape `1`), whose
  value, level and shape reduce to `β`, `β` and `1` by projection.
* `Cutoff.val_le_top`, `Cutoff.val_ne_zero`, `Cutoff.val_le_one`: the cut-off is at most the
  level, positive when the level is, and at most one when the level is.
* `Cutoff.meanShape`: the mean shape over a uniform commitment hash, in `(0, 1]`, one at a
  constant cut-off, and at least every lower bound on the shape (`Cutoff.le_meanShape`).
-/

namespace GordieHowe.MLDSA

open _root_.MLDSA _root_.MLDSA.Concrete
open scoped ENNReal BigOperators

/-- A public cut-off of the flattened signer: the value `val c̃` that the keep coin compares the
acceptance weight with, as a public level `top` times a shape in `(0, 1]`. -/
structure Cutoff (p : Params) where
  /-- The public level: the kept mass of an attempt is at most `K · top`. -/
  top : ℚ≥0
  /-- The shape at `c̃`. -/
  shape : CommitHashBytes p → ℚ≥0
  /-- The shape is positive. -/
  shape_ne_zero : ∀ c, shape c ≠ 0
  /-- The shape is at most one. -/
  shape_le_one : ∀ c, shape c ≤ 1
  /-- The cut-off at `c̃`. -/
  val : CommitHashBytes p → ℚ≥0
  /-- The cut-off is the level times the shape. -/
  val_eq : ∀ c, val c = top * shape c

variable {p : Params}

/-- The constant cut-off. -/
abbrev Cutoff.const (β : ℚ≥0) : Cutoff p where
  top := β
  shape _ := 1
  shape_ne_zero _ := one_ne_zero
  shape_le_one _ := le_rfl
  val _ := β
  val_eq _ := (mul_one β).symm

namespace Cutoff

variable (cut : Cutoff p)

/-- The cut-off is at most the level. -/
theorem val_le_top (c : CommitHashBytes p) : cut.val c ≤ cut.top := by
  rw [cut.val_eq]
  exact mul_le_of_le_one_right' (cut.shape_le_one c)

/-- The cut-off in `ℝ≥0∞` is the level times the shape. -/
theorem coe_val (c : CommitHashBytes p) :
    (cut.val c : ℝ≥0∞) = (cut.top : ℝ≥0∞) * (cut.shape c : ℝ≥0∞) := by
  rw [cut.val_eq, ENNReal.nnratCast_mul]

/-- The cut-off in `ℝ≥0∞` is at most the level. -/
theorem coe_val_le_top (c : CommitHashBytes p) : (cut.val c : ℝ≥0∞) ≤ (cut.top : ℝ≥0∞) :=
  ENNReal.nnratCast_le_nnratCast.2 (cut.val_le_top c)

/-- The shape in `ℝ≥0∞` is at most one. -/
theorem coe_shape_le_one (c : CommitHashBytes p) : (cut.shape c : ℝ≥0∞) ≤ 1 :=
  ENNReal.nnratCast_le_one.2 (cut.shape_le_one c)

/-- The shape in `ℝ≥0∞` is positive. -/
theorem coe_shape_ne_zero (c : CommitHashBytes p) : (cut.shape c : ℝ≥0∞) ≠ 0 :=
  ENNReal.nnratCast_ne_zero.2 (cut.shape_ne_zero c)

/-- The cut-off is positive when the level is. -/
theorem coe_val_ne_zero (h : (cut.top : ℝ≥0∞) ≠ 0) (c : CommitHashBytes p) :
    (cut.val c : ℝ≥0∞) ≠ 0 := by
  rw [coe_val]
  exact mul_ne_zero h (cut.coe_shape_ne_zero c)

/-- The cut-off is positive when the level is. -/
theorem val_ne_zero (h : cut.top ≠ 0) (c : CommitHashBytes p) : cut.val c ≠ 0 :=
  ENNReal.nnratCast_ne_zero.1 (cut.coe_val_ne_zero (ENNReal.nnratCast_ne_zero.2 h) c)

/-- The cut-off is at most one when the level is. -/
theorem coe_val_le_one (h : (cut.top : ℝ≥0∞) ≤ 1) (c : CommitHashBytes p) :
    (cut.val c : ℝ≥0∞) ≤ 1 :=
  (cut.coe_val_le_top c).trans h

/-- The cut-off is at most one when the level is. -/
theorem val_le_one (h : cut.top ≤ 1) (c : CommitHashBytes p) : cut.val c ≤ 1 :=
  (cut.val_le_top c).trans h

/-- The mean shape of a cut-off over a uniform commitment hash. -/
noncomputable def meanShape : ℝ := 𝔼 c, (cut.shape c : ℝ)

/-- The mean shape is positive. -/
theorem meanShape_pos : 0 < cut.meanShape :=
  Finset.expect_pos (fun c _ => NNRat.cast_pos.2 (pos_iff_ne_zero.2 (cut.shape_ne_zero c)))
    Finset.univ_nonempty

/-- The mean shape is at most one. -/
theorem meanShape_le_one : cut.meanShape ≤ 1 :=
  (Finset.expect_le_expect fun c _ => (by exact_mod_cast cut.shape_le_one c :
    (cut.shape c : ℝ) ≤ 1)).trans_eq (Finset.expect_const Finset.univ_nonempty 1)

/-- A lower bound on the shape at every commitment hash bounds the mean shape. -/
theorem le_meanShape {a : ℝ} (h : ∀ c, a ≤ (cut.shape c : ℝ)) : a ≤ cut.meanShape :=
  (Finset.expect_const Finset.univ_nonempty a).symm.trans_le
    (Finset.expect_le_expect fun c _ => h c)

/-- The mean shape of a constant cut-off is one. -/
theorem meanShape_const (β : ℚ≥0) : (Cutoff.const β : Cutoff p).meanShape = 1 := by
  simp only [meanShape, NNRat.cast_one]
  exact Finset.expect_const Finset.univ_nonempty 1

end Cutoff

end GordieHowe.MLDSA
