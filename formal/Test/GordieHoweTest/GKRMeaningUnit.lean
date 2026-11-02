-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe.Language.Realizations.Circuit.RelEntry

/-!
# The meaning check's normal form on a small program

A program over `F_97` with values `x`, `y` and the constant `0`, and two shared expressions,
`s = x + y` (ref `0`) and `t = s · s` (ref `1`). The meaning check (`nfUnitEqB`) compares the
normal forms with shared expressions as atoms (`nfS`), merged like terms, and unfolds a shared
expression only while the difference is not zero (`zeroLoop`):
* accepted: the two sides read the same shared expressions (no unfold); one side reads `t` and the
  other `s · s` (one unfold); `X = −Y`;
* accepted: a difference that is zero only once like terms merge after an unfold;
* rejected: a factor or a code changed.
-/

namespace GordieHoweTest.GKRMeaningUnit

open GordieHowe GordieHowe.RealizedProgram

/-- The program: `x`, `y` of length `1`, the constant `0`, `s = x + y`, `t = s · s`. -/
def tiny : RealizedProgram where
  phases := 1
  fields := [{ name := "F97", characteristic := 97, degree := 1 }]
  domains := [{ name := "A", field := 0 }]
  values := [{ name := "x", shape := [1], kind := .priv, type := .field },
    { name := "y", shape := [1], kind := .priv, type := .field },
    { name := "zero", shape := [1], kind := .constant [0], type := .field }]
  exprs := [.add (.leaf 0) (.leaf 1), .mul (.ref 0) (.ref 0)]
  predicates := []

/-- Accepted with no unfold: `s · (s + x) = s · s + x · s`, the shared expression `s` an atom. -/
example : tiny.nfUnitEqB 0 97 96 (.mul (.ref 0) (.add (.ref 0) (.leaf 0)))
    (.sub (.add (.mul (.ref 0) (.ref 0)) (.mul (.leaf 0) (.ref 0))) (.leaf 2)) = true := by
  decide +kernel

/-- Accepted with one unfold: `t = s · s`. -/
example : tiny.nfUnitEqB 0 97 96 (.ref 1) (.sub (.mul (.ref 0) (.ref 0)) (.leaf 2)) = true := by
  decide +kernel

/-- Accepted as the negation: `y − x = −(x − y)`. -/
example : tiny.nfUnitEqB 0 97 96 (.sub (.leaf 1) (.leaf 0)) (.sub (.leaf 0) (.leaf 1)) = true := by
  decide +kernel

/-- Accepted by cancellation: `t − (x + y) · s` is zero once `s` is unfolded and `x y`, `y x`
merge. -/
example : tiny.nfUnitEqB 0 97 96
    (.sub (.ref 1) (.mul (.add (.leaf 0) (.leaf 1)) (.ref 0)))
    (.sub (.leaf 2) (.leaf 2)) = true := by
  decide +kernel

/-- Rejected: a factor changed, `s · s` against `s · x`. -/
example : tiny.nfUnitEqB 0 97 96 (.ref 1) (.sub (.mul (.ref 0) (.leaf 0)) (.leaf 2)) = false := by
  decide +kernel

/-- Rejected: a code changed, `2 t` against `s · s`. -/
example : tiny.nfUnitEqB 0 97 96 (.scale (.const 2) (.ref 1))
    (.sub (.mul (.ref 0) (.ref 0)) (.leaf 2)) = false := by
  decide +kernel

end GordieHoweTest.GKRMeaningUnit
