-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Realized

@[expose] public section

/-!
# GordieHowe: the digit layout of an emulated ML-DSA program

The part of an emulated ML-DSA program that its export chooses and that the emulated frontend and
honest prover read as data (`MldsaELayout`): the digit decompositions of `w'`, of `z + 130993`, of
the UseHint offset and of the slack (each a base and its digit values, least significant first,
`DigitLayout`) and the range bound of the offset and the slack. Each emulated program instantiates
it once; its facts about the program are decided there.

With the expression a value bound to its digits reads (`DigitLayout.expr`), the honest digits
(`DigitLayout.digit`) and the reconstruction (`DigitLayout.sum_digitAt`).
-/

namespace GordieHowe.MLDSA44.Emulated

/-- **The digits of one decomposed quantity**: the base and the digit values, least significant
first; the digit count is the list's length. -/
structure DigitLayout where
  /-- The base. -/
  base : ℕ
  /-- The digit values, least significant first. -/
  ids : List ℕ
deriving DecidableEq

/-- **The digit layout of an emulated ML-DSA program**: the digits of `w'` (`signature.w`), of
`z + 130993` (`norm.z`, its first side), of the UseHint offset (`hint.offset`) and of the slack
(`hint.slack`), and the range bound of the offset and the slack. -/
structure MldsaELayout where
  /-- The digits of `w'`. -/
  w : DigitLayout
  /-- The digits of `z + 130993`. -/
  z : DigitLayout
  /-- The digits of the UseHint offset. -/
  offset : DigitLayout
  /-- The digits of the slack. -/
  slack : DigitLayout
  /-- The range bound of the offset and the slack. -/
  offsetBound : ℕ
deriving DecidableEq

namespace DigitLayout

/-- **The digits' sum from position `t` on**, added to `acc`: `acc + Σ_s b^(t+s) d_s`, left
nested as the export writes it. -/
def exprFrom (b : ℕ) : ℕ → RealizedProgram.Expr → List ℕ → RealizedProgram.Expr
  | _, acc, [] => acc
  | t, acc, d :: ds => exprFrom b (t + 1) (.add acc (.scale (.const (b ^ t)) (.leaf d))) ds

/-- **The expression a value bound to these digits reads**: `d_0 + b d_1 + b^2 d_2 + …`. -/
def expr (D : DigitLayout) : RealizedProgram.Expr :=
  match D.ids with
  | [] => .leaf 0
  | d :: ds => exprFrom D.base 1 (.leaf d) ds

@[simp] theorem exprFrom_nil (b t : ℕ) (acc : RealizedProgram.Expr) : exprFrom b t acc [] = acc := rfl

theorem exprFrom_cons (b t : ℕ) (acc : RealizedProgram.Expr) (d : ℕ) (ds : List ℕ) :
    exprFrom b t acc (d :: ds) = exprFrom b (t + 1) (.add acc (.scale (.const (b ^ t)) (.leaf d))) ds :=
  rfl

theorem expr_cons (b d : ℕ) (ds : List ℕ) :
    (⟨b, d :: ds⟩ : DigitLayout).expr = exprFrom b 1 (.leaf d) ds := rfl

/-- **Digit `s` of `n`** in base `b`. -/
def digitAt (b n s : ℕ) : ℕ := n / b ^ s % b

/-- **The honest digit value `v` of `n`**: the digit at `v`'s position. -/
def digit (D : DigitLayout) (n v : ℕ) : ℕ := digitAt D.base n (D.ids.idxOf v)

/-- **The digits a layout holds every natural up to `n` in**: some digit and room for `n`. -/
structure Fits (D : DigitLayout) (n : ℕ) : Prop where
  /-- There is a digit. -/
  ne : D.ids ≠ []
  /-- The digits hold `n`. -/
  le : n < D.base ^ D.ids.length

/-- **The digits reconstruct the residue**: `Σ_{s < k} b^s · digit_s(n) = n mod b^k`. -/
theorem sum_digitAt (b n k : ℕ) :
    ∑ s ∈ Finset.range k, b ^ s * digitAt b n s = n % b ^ k := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih => rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ, digitAt]

/-- **The honest digit at position `s`** is digit `s`. -/
theorem digit_getElem {D : DigitLayout} (hD : D.ids.Nodup) (n : ℕ) {s : ℕ}
    (hs : s < D.ids.length) : D.digit n D.ids[s] = digitAt D.base n s := by
  rw [digit, hD.idxOf_getElem]

end DigitLayout

/-- **The digit values of a layout**: those of `w'`, of `z + 130993`, of the offset and of the
slack. -/
def MldsaELayout.digitValues (L : MldsaELayout) : List ℕ :=
  L.w.ids ++ L.z.ids ++ L.offset.ids ++ L.slack.ids

end GordieHowe.MLDSA44.Emulated
