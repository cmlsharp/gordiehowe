-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Library.Eval
public import GordieHowe.Applications.Keccak.Gadgets.Shake256

@[expose] public section

/-!
# GordieHowe frontend: a program's SHAKE256 call

The frontend reads a program's hash through `SpongeView`: the input bytes and the output bytes of
one SHAKE256 call as functions of an environment, with the hash's soundness (where the source
program holds, every output byte is the vendored SHAKE256 of the input bytes,
`xofFin Shake256.SpongeSpec.shake256.xof`, the form `KeccakSponge.wordAbsorb_sound` concludes).
The view keeps the theorems that consume the hash (the selection, the application) independent of
the Keccak trace's shape; an instance proves `sound` from the program's Keccak predicates.
-/

namespace GordieHowe.RealizedProgram

open GordieHowe.Bits

/-- **One SHAKE256 call of a program**, in the field `f` of its domain, squeezing `outLen` bytes:
the input bytes (`len e` of them, a byte as `8` bit wires, little-endian), the output bytes, and the
hash's soundness where the source program holds. -/
structure SpongeView (ir : RealizedProgram) (I : Interp) (f outLen : ℕ) where
  /-- The number of input bytes. -/
  len : ir.Env I → ℕ
  /-- The input bytes. -/
  input : (e : ir.Env I) → Fin (len e) → BitWires (I f).K 8
  /-- The output bytes. -/
  out : ir.Env I → Fin outLen → BitWires (I f).K 8
  /-- **The hash's soundness**: where the source program holds, output byte `o` is byte `o` of the
  SHAKE256 output of the input bytes. -/
  sound : ∀ e, ir.SourceSatAt e → ∀ o, natOfBits (out e o) =
    xofFin Shake256.SpongeSpec.shake256.xof (Shake256.inputBytes (input e)) outLen o

end GordieHowe.RealizedProgram
