-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Gadgets.EmulatedNorm
public import GordieHowe.Language.Realizations.Range
public import GordieHowe.Foundations.Algebra.IntLift
public import GordieHowe.Applications.Falcon512.Emulated.Rows
public import GordieHowe.Applications.Rows.MAC
public import GordieHowe.Language.Realizations.Bits
public import GordieHowe.Applications.Falcon512.Gadgets.EmulatedEncoding
public import GordieHowe.Applications.Falcon512.Spec.Encoding

@[expose] public section

/-!
# The Falcon public key's coefficients

`keyCoeffs h`: the coefficients of the public key `h` as natural numbers, read by the signature
rows.
-/

namespace GordieHowe.Falcon512.EmulatedAlgebraCircuit

/-- Public coefficients used in the signature rows. -/
-- spec-side
def keyCoeffs {n : ℕ} (h : _root_.Falcon.Rq n) : Fin n → ℕ :=
  fun i => (Falcon512.coeff h i).val

end GordieHowe.Falcon512.EmulatedAlgebraCircuit
