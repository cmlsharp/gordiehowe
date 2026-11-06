-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Assumptions

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.Cells`

The definitions of `GordieHowe.Language.RealizedProgram.Cells` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/RealizedProgram/Cells.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- **A committed coordinate** of a program: coordinate `i` of the committed value `v`, coordinate
`i` of the pad of late value `v`, or filler input `j` of circuit `c`. -/
inductive CellKey where
  /-- Coordinate `i` of committed value `v`. -/
  | val (v i : ℕ)
  /-- Coordinate `i` of the pad of late value `v`. -/
  | pad (v i : ℕ)
  /-- Filler input `j` of circuit `c`. -/
  | filler (c j : ℕ)
  deriving DecidableEq, Repr

section

variable (ir : RealizedProgram)

/-- **Value `v` is committed in domain `d`**: a committed value or a pad copy of `d`. -/
def isCellValue (d v : ℕ) : Bool :=
  (ir.value v).domain == d &&
    match (ir.value v).kind with
    | .priv => true
    | .padCopy _ _ => true
    | _ => false

/-- A private value is a committed cell of its own domain. -/
theorem isCellValue_self_of_kind_priv {v : ℕ} (hk : (ir.value v).kind = .priv) :
    ir.isCellValue (ir.value v).domain v = true := by
  simp only [isCellValue, hk, beq_self_eq_true, Bool.true_and]

/-- **Value `v` is a late value of domain `d`**: a late value of `d` that lies in its domain (not
the tag of a MAC that no domain hosts, whose field no domain commits and whose pad is a cell of no
domain). -/
def isLateOf (d v : ℕ) : Bool :=
  (ir.value v).field.isNone && (ir.value v).domain == d && decide (ir.IsLate v)

end

end GordieHowe.RealizedProgram
