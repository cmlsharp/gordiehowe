-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.RealizeGrouped

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.Locality`

The definitions of `GordieHowe.Language.RealizedProgram.Locality` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/RealizedProgram/Locality.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

/-- **What of the committed assignment value `v` reads**, with `n` levels (as `RealizedProgram.read`): a
committed value, a pad copy or a late value itself, a value bound to its digits the values of its
expression, a public expression, an opaque value or a bit view what the values it reads read;
nothing for a message, a statement value, a constant or a challenge. -/
def asgReads : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, v =>
    match (ir.value v).kind with
    | .priv => [v]
    | .padCopy _ _ => [v]
    | .late => [v]
    | .bound e => ir.exprNodes e
    | .pub (.expr e) => (ir.exprNodes e).flatMap (asgReads n)
    | .pub (.opaque _ args) => args.flatMap (asgReads n)
    | .bits w _ => asgReads n w
    | _ => []

variable {ir I}

variable (ir) in
/-- **The step of `asgReads`.** -/
def asgReadsStep (r : ℕ → List ℕ) (v : ℕ) : List ℕ :=
  match (ir.value v).kind with
  | .priv => [v]
  | .padCopy _ _ => [v]
  | .late => [v]
  | .bound e => ir.exprNodes e
  | .pub (.expr e) => (ir.exprNodes e).flatMap r
  | .pub (.opaque _ args) => args.flatMap r
  | .bits w _ => r w
  | _ => []

variable (ir) in
/-- **The step of `asgReadsT`**: what value `v` reads of the committed assignment, from what the
values it reads read (`r`). -/
def asgStep (r : ℕ → List ℕ) (v : ℕ) (x : Value) : List ℕ :=
  match x.kind with
  | .priv => [v]
  | .padCopy _ _ => [v]
  | .late => [v]
  | .bound e => ir.exprNodes e
  | .pub (.expr e) => insertAll [] ((ir.nodesOf e).flatMap r)
  | .pub (.opaque _ args) => insertAll [] (args.flatMap r)
  | .bits w _ => r w
  | _ => []

variable (ir) in
/-- **The table of what each value reads of the committed assignment** (`asgReads`). -/
def asgReadsT : NatTrie (List ℕ) := memo ir.asgStep [] ir.values

end

end GordieHowe.RealizedProgram
