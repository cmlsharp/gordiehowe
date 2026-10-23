-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Gadgets.NativeNorm
public import GordieHowe.Applications.Falcon512.Gadgets.NativeEncoding
public import GordieHowe.Foundations.Algebra.ParityReduction
public import GordieHowe.Foundations.Algebra.ConvMatrix
public import GordieHowe.Foundations.Algebra.ReconstructSum
public import GordieHowe.Language.Realizations.Bits
public import GordieHowe.Language.Realizations.Range
public import GordieHowe.Applications.Falcon512.Native.Rows
public import GordieHowe.Applications.Rows.MAC
public import GordieHowe.Foundations.Algebra.DFT
public import GordieHowe.Foundations.Algebra.DFTExtra
public import GordieHowe.Applications.Falcon512.Spec.Encoding
public import GordieHowe.Language.Realizations.MAC

@[expose] public section

/-!
# Falcon-512 native norm indices

The native norm of Falcon-512's native A circuit (`norm` in
`lib/gordiehowe/examples/falcon/falcon_native.h`, `assert_norm_native` in `lib/gordiehowe/lib/norm.h`; a
field of characteristic `q = 12289`) reads the `1024` coefficients of `s₁ ‖ s₂` (`NativeNorm.run`):

* `normCoeffs_eq`, `normAppend_eq`: `2 * falcon512.n = falcon512.n + falcon512.n = 1024`;
* `lowIndex i`, `highIndex i`: the norm input index of coefficient `i` of `s₁` and of `s₂`.
-/

namespace GordieHowe.Falcon512.NativeAlgebraCircuit

variable {F : Type*} [Field F] [DecidableEq F]

/-- The native norm gadget's `1024` coefficient wires are the `2 * falcon512.n`
coefficients of `s₁ ‖ s₂`. -/
theorem normCoeffs_eq : 2 * falcon512.n = 1024 := rfl

/-- `normCoeffs_eq` at the length `falcon512.n + falcon512.n` that `Fin.append` produces. -/
theorem normAppend_eq : falcon512.n + falcon512.n = 1024 := (two_mul _).symm.trans normCoeffs_eq

/-- The norm input index of `s₁` coefficient `i`. -/
def lowIndex (i : Fin falcon512.n) : Fin 1024 := ⟨i, by have := normCoeffs_eq; omega⟩

/-- The norm input index of `s₂` coefficient `i`. -/
def highIndex (i : Fin falcon512.n) : Fin 1024 :=
  ⟨falcon512.n + i, by have := normCoeffs_eq; omega⟩

end GordieHowe.Falcon512.NativeAlgebraCircuit
