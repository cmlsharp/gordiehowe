-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.System.Source
public import GordieHowe.Applications.Falcon512.System.Params
public import GordieHowe.Foundations.Probability.RangeGroups
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative20
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative9
public import GordieHowe.Applications.Falcon512.Gadgets.NativeNormGroups

@[expose] public section

/-!
# Falcon native: the source assignment

The assignment of Falcon native before the randomized lowerings
(`lib/gordiehowe/examples/falcon/falcon_native.h`, `falcon_native`): the variables the
application declares, by domain.

* Domain H (Falcon emulated's domain H, `examples/falcon/falcon_hash.h`): the private inputs `nonce`
  (320 bits) and `message` (`8 msgLen` bits), the Keccak trace `h2p.shake.states`
  (`GordieHowe.Falcon512.Emulated.Words`), and the selected samples `select.raw` (`512 × 16` bits).
* Domain A: the sample bits `c_A` (`512 × 16`, `crossing.c_A`), the private input `s2`, and the
  algebra advice (`Committed`): `signature.s1`, the native norm's witness (`norm.a`, `norm.sq`,
  `norm.cc`, `norm.nd`, `norm.nc`, `norm.D`, `norm.Dc`: `NativeNorm.Wit`, whose top digit slot of
  each `s2` coefficient is the encoding's `encoding.h`) and `encoding.slack_hi`.

`Committed` is the algebra advice and `Source` the whole assignment.
-/

namespace GordieHowe.Falcon512.Native

open GordieHowe.Bits
open Emulated (Words)

/-- **The algebra advice of Falcon native** (`examples/falcon/falcon_native.h`, `norm.h:426-503`):
`signature.s1`, the native norm's witness on `s1 ‖ s2` (`NativeNorm.Wit`: per coefficient the
magnitude digits `norm.a`, the square digits `norm.sq` and the column carries `norm.cc`; per batch
the normalized digits `norm.nd` and carries `norm.nc`; the complement digits `norm.D` and their
carries `norm.Dc`), and the budget slack's committed high digit `encoding.slack_hi`. -/
@[ext] structure Committed (F : Type) where
  /-- `signature.s1`. -/
  s1 : Fin falcon512.n → F
  /-- The native norm's witness. -/
  norm : NativeNorm.Wit F
  /-- `encoding.slack_hi`. -/
  slackHi : F

/-- **The source assignment of Falcon native**, for a `msgLen`-byte message, with domain H's field
`KH` and domain A's field `F`. -/
structure Source (KH F : Type) (msgLen : ℕ) where
  /-- The nonce bits (`nonce`). -/
  nonce : BitWires KH (8 * falcon512.saltBytes)
  /-- The message bits (`message`). -/
  message : BitWires KH (8 * msgLen)
  /-- The Keccak trace words (`h2p.shake.states`). -/
  states : Words KH msgLen
  /-- The selected samples (`select.raw`). -/
  raw : Fin falcon512.n → BitWires KH falconSampleBits
  /-- The sample bits in A (`c_A`). -/
  cA : Fin falcon512.n → BitWires F falconSampleBits
  /-- The signature polynomial (`s2`). -/
  s2 : Fin falcon512.n → F
  /-- The algebra advice (`s1`, the norm's witness, `slack_hi`). -/
  alg : Committed F

end GordieHowe.Falcon512.Native
