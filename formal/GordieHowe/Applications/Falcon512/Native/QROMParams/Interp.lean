-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.FieldInterps.Basic
public import GordieHowe.Applications.Falcon512.Frontend.Fields
public import GordieHowe.Applications.FieldInterps.Fq20
public import GordieHowe.Applications.FieldInterps.GF256
public import GordieHowe.Language.RealizedProgram.Interval
public import GordieHowe.Language.RealizedProgram.WithPlan
public import GordieHowe.Language.Realizations.MaskSubfield
public import GordieHowe.Generated.Falcon512.Native.QROMParams.Program
public import GordieHowe.Generated.Falcon512.Native.QROMParams.Plan

@[expose] public section

/-!
# GordieHowe: the interpretation of `Falcon512.Native.QROMParams`

The fields of the realized program of the native Falcon proof of possession at the QROM parameters
(`GordieHowe.Generated.Falcon512.Native.QROMParams.Program.program`, export `c825eb05`: domain `H` over field
`0`, `GF(2^256)`; domain `A` over field `1`, `F_q^20`, `q = 12289`), read in Lean, for the proof system
and the frontend alike:

* **the interpretation** (`interp`): field `0` is `GF(2^256)` (`gf256`,
  `GordieHowe/Applications/FieldInterps/GF256.lean`), field `1` (and any other identifier) `F_q^20` (`fq20`,
  `GordieHowe/Applications/FieldInterps/Fq20.lean`); the opaque functions `targetBitsFn` (the program's
  opaque values are `statement.hhat`, of no argument, read from the statement, and
  `mac.target_bits`);
* **the model of the interpretation** (`interpModel`, `Interp.Model.of_models`): field `0` is
  `GF(2^256)` with its model at `bit`, field `1` `F_q^20` with its model at `GF(p^1)`; the names,
  characteristics and nodes by `decide`; the MAC field `GF(2^256)`; the field-form `mod_q`s in `A`,
  whose field reads linearly; with the registry (`interpModel.registered`), lawful integer readings
  (`interpModel.lawful`) and the MAC model (`interpModel.macModel`) read from it.
-/

namespace GordieHowe.Falcon512.Native.QROMParams

open RealizedProgram.Export RelativePacking
open Generated.Falcon512.Native.QROMParams.Program (program)

/-- **The interpretation of the program of `Falcon512.Native.QROMParams`**: field `0` is `GF(2^256)`, field
`1` (and any other identifier) `F_q^20`; the opaque functions `falconOps fq20` (it reads only `mac.target_bits`). -/
abbrev interp : RealizedProgram.Interp := RealizedProgram.falconInterpOf RealizedProgram.gf256 RealizedProgram.fq20

/-- **The model of the interpretation** (`Interp.Model.of_models`): field `0` is `GF(2^256)` with
its model at `bit`, field `1` `F_q^20` with its model at `GF(p^1)`; the names and characteristics,
the plan's prime-subfield nodes and the nodes of the node-typed `Bit` values are the fields', by
`decide`; no opaque `Bit` value computed from arguments is `key.coefficients`
(`falconOps_opaqueBit`); the one MAC tail has its powers in `GF(2^256)`, a binary MAC field of width
`256` with the taps `{0, 2, 5, 10}` (`gf256_macFieldOk`), and its target's bits computed by
`mac.target_bits` (`RealizedProgram.macTailsAt`, by `decide`); every field-form `mod_q` is in domain `A`,
whose field `F_q^20` reads linearly (`fq20_readLinear`). -/
theorem interpModel : interp.Model Generated.Falcon512.Native.QROMParams.Plan.plan program [] :=
  .of_models (RealizedProgram.falconInterpOf_models RealizedProgram.gf256_model RealizedProgram.fq20_model)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (RealizedProgram.falconOps_opaqueBit (by decide +kernel))
    (RealizedProgram.Interp.macModel_of_tails (f := 0) (nm := "mac.target_bits") (by decide +kernel)
      RealizedProgram.gf256_macFieldOk RealizedProgram.falconOps_target_bits)
    (RealizedProgram.Interp.fieldFormModel_of_field (f := 1) (by decide +kernel) RealizedProgram.fq20_readLinear)

end GordieHowe.Falcon512.Native.QROMParams
