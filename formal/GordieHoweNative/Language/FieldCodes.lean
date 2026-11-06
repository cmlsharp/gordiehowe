-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.ProgramData
public import GordieHoweNative.Applications.FieldInterps.Codes

/-! # The field registry's compiled code arithmetic

The descriptor selects the same arithmetic as the semantic registry. Homomorphism proofs remain
in `GordieHowe.Applications.FieldInterps.Registry`.
-/

public section

namespace GordieHowe

open RealizedProgram

/-- **The code arithmetic of a key's field**, with the fast path at its prime subfield. -/
@[expose] def FieldKey.code : FieldKey → GKR.Fold.CodeArith
  | .gf128 => gf2_128Code.arith
  | .gf256 => gf2_256Code.arith
  | .fq6 => fq6Code.arith.withPrime 8380417
  | .fq9 => fq9Code.arith.withPrime 12289
  | .fq11 => fq11Code.arith.withPrime 8380417
  | .fq20 => fq20Code.arith.withPrime 12289
  | .gold2 => gold2Code.arith.withPrime 18446744069414584321
  | .gold4 => gold4Code.arith.withPrime 18446744069414584321
  | .p256 =>
    (GKR.Fold.primeArith
      115792089210356248762697446949407573530086143415290314195533631308867097853951).withPrime
      115792089210356248762697446949407573530086143415290314195533631308867097853951

end GordieHowe
