-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.RealizeGrouped

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.Derivation.Events`

The definitions of `GordieHowe.Language.Realizations.Derivation.Events` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/Derivation/Events.lean`, which imports this module.
-/

local notation "ℕ" => Nat

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export
section

variable {ir : RealizedProgram} {primeNodes : ℕ → List String}

variable (ir) in
/-- **A cross-field `equal`'s interval-free MAC shape**: hosted (`macHostedCoreB`) or two-tail
(`macTwoCoreB`), with a blind. -/
def macCoreOkB (pid : ℕ) : PredBody → Bool
  | .cross dx x dy y k real =>
    match real.blindX, real.blind with
    | none, some _ => ir.macHostedCoreB pid dx x dy y k real
    | some _, some _ => ir.macTwoCoreB pid x y k real
    | _, _ => false
  | _ => false

end

end GordieHowe.RealizedProgram
