-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.FieldInterps.Basic
public import GordieHowe.Applications.Falcon512.Frontend.Fields
public import GordieHowe.Language.RealizedProgram.Interval
public import GordieHowe.Language.RealizedProgram.WithPlan
public import GordieHowe.Language.Realizations.MaskSubfield
public import GordieHowe.Generated.Falcon512.Native.ROMParams.Program
public import GordieHowe.Generated.Falcon512.Native.ROMParams.Plan

@[expose] public section

/-!
# GordieHowe: the interpretation of `Falcon512.Native.ROMParams`

The fields of the realized program of the native Falcon proof of possession at the ROM parameters
(`GordieHowe.Generated.Falcon512.Native.ROMParams.Program.program`, export `c825eb05`: domain `H` over field
`0`, `GF(2^128)`; domain `A` over field `1`, `F_q^9`, `q = 12289`), read in Lean, for the proof system
and the frontend alike:

* **the interpretation** (`interp`): field `0` is `GF(2^128)` (`gf128`), field `1` (and any other
  identifier) `F_q^9` (`fq9`), both from `GordieHowe/Applications/FieldInterps/Basic.lean`; the opaque
  functions `targetBitsFn` (the program's opaque values are `statement.hhat`, of no argument, read
  from the statement, and `mac.target_bits`);
* **the model of the interpretation** (`interpModel`, `Interp.Model.of_models`): field `0` is
  `GF(2^128)` with its model at `bit`, field `1` `F_q^9` with its model at `GF(p^1)`; the names,
  characteristics and nodes by `decide`; the MAC field `GF(2^128)`; the field-form `mod_q`s in `A`,
  whose field reads linearly; with the registry (`interpModel.registered`), lawful integer readings
  (`interpModel.lawful`) and the MAC model (`interpModel.macModel`) read from it.
-/

namespace GordieHowe.Falcon512.Native.ROMParams

open RealizedProgram.Export RelativePacking
open Generated.Falcon512.Native.ROMParams.Program (program)

/-- **The interpretation of the program of `Falcon512.Native.ROMParams`**: field `0` is `GF(2^128)`, field
`1` (and any other identifier) `F_q^9`; the opaque functions `falconOps fq9` (it reads only `mac.target_bits`). -/
abbrev interp : RealizedProgram.Interp := RealizedProgram.falconInterpOf RealizedProgram.gf128 RealizedProgram.fq9

/-- **The model of the interpretation** (`Interp.Model.of_models`): field `0` is `GF(2^128)` with
its model at `bit`, field `1` `F_q^9` with its model at `GF(p^1)`; the names and characteristics,
the plan's prime-subfield nodes and the nodes of the node-typed `Bit` values are the fields', by
`decide`; no opaque `Bit` value computed from arguments is `key.coefficients`
(`falconOps_opaqueBit`); the one MAC tail has its powers in `GF(2^128)`, a binary MAC field of width
`128` with the taps `{0, 1, 2, 7}` (`gf128_macFieldOk`), and its target's bits computed by
`mac.target_bits` (`RealizedProgram.macTailsAt`, by `decide`); every field-form `mod_q` is in domain `A`,
whose field `F_q^9` reads linearly (`fq9_readLinear`). -/
theorem interpModel : interp.Model Generated.Falcon512.Native.ROMParams.Plan.plan program [] :=
  .of_models (RealizedProgram.falconInterpOf_models RealizedProgram.gf128_model RealizedProgram.fq9_model)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (RealizedProgram.falconOps_opaqueBit (by decide +kernel))
    (RealizedProgram.Interp.macModel_of_tails (f := 0) (nm := "mac.target_bits") (by decide +kernel)
      RealizedProgram.gf128_macFieldOk RealizedProgram.falconOps_target_bits)
    (RealizedProgram.Interp.fieldFormModel_of_field (f := 1) (by decide +kernel) RealizedProgram.fq9_readLinear)

end GordieHowe.Falcon512.Native.ROMParams
