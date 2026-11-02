-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Completeness.Basic

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Completeness.Late`

The definitions of `GordieHowe.Language.Completeness.Late` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Completeness/Late.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable {ir : RealizedProgram}

variable (ir) in
/-- **The values and challenges the generator of value `v` (`genSrcOf`) reads**: a tag reads its H
operand's values and its key, a grouped `mod_q`'s accumulators and quotient digits read its
powers and its operand's values, an ungrouped digit-form `mod_q`'s accumulator and lower digits
read its left side's values. -/
def genInputsOf (G : Gens) (v : ℕ) : List ℕ × List ℕ :=
  match G.at v with
  | .tag p =>
    match (ir.predicate p).body with
    | .cross _ x _ _ _ real => (ir.exprNodes x, [real.key])
    | _ => ([], [])
  | .acc p =>
    match (ir.predicate p).body with
    | .mod _ _ L _ real =>
      match real.grouped, macUnits? L with
      | some _, some u => (u.powers :: ir.exprNodes u.operand, [])
      | _, _ => ([], [])
    | _ => ([], [])
  | .quotDigit p =>
    match (ir.predicate p).body with
    | .mod _ _ L _ real =>
      match real.grouped, macUnits? L with
      | some _, some u => (u.powers :: ir.exprNodes u.operand, [])
      | _, _ => ([], [])
    | _ => ([], [])
  | .digitsAcc p =>
    match (ir.predicate p).body with
    | .mod _ _ L _ _ => (ir.exprNodes L, [])
    | _ => ([], [])
  | .lowDigit p _ =>
    match (ir.predicate p).body with
    | .mod _ _ L _ _ => (ir.exprNodes L, [])
    | _ => ([], [])
  | _ => ([], [])

/-- **`GenCoveredC`, through the reads tables**, at a program reader. -/
def PReader.genCoveredCB (ir : RealizedProgram) [r : PReader] (G : Gens) (MT : NatTrie ℕ) (rs : List Read) (v : ℕ) :
    Bool :=
  (ir.genInputsOf G v).2.all (fun j => rs.contains (.chal j)) &&
    (ir.genInputsOf G v).1.all (PReader.srcCoveredB ir MT rs)

variable (ir) in
/-- **`GenCoveredC`, through the reads tables** (`PReader.genCoveredCB` at the program). -/
def genCoveredCB (G : Gens) (MT : NatTrie ℕ) (rs : List Read) (v : ℕ) : Bool :=
  @PReader.genCoveredCB ir (PReader.ofProgram ir) G MT rs v

end

end GordieHowe.RealizedProgram
