-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.FieldInterps.Fq20
public import GordieHowe.Language.RealizedProgram.Interval
public import GordieHowe.Language.RealizedProgram.WithPlan
public import GordieHowe.Applications.Falcon512.Ring.Native.System.Params
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative20Relative
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative20Tower
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNativeCoords
public import GordieHowe.Language.Realizations.MaskSubfield
public import GordieHowe.Generated.Falcon512.Ring.Native.QROMParams.Program
public import GordieHowe.Generated.Falcon512.Ring.Native.QROMParams.Plan
public import GordieHowe.Language.Export.Valid
public import GordieHowe.Applications.Shared.TableauFq20

@[expose] public section

/-!
# GordieHowe: the interpretation of `Falcon512.Ring.Native.QROMParams`

The interpretation of the realized program of the native Falcon ring at the QROM parameters
(`GordieHowe.Generated.Falcon512.Ring.Native.QROMParams.Program.program`, export `b65a4929`: one domain `A` over
`F_q^20`, one GKR circuit `c.A`, the batches `norm.center` and `norm.column1`), whose domain proof
is the generic per-field one (`GordieHowe/Applications/Falcon512/Ring/Native/QROMParams/ProofSystem.lean`): the field
`F_q^20` (`fq20`, `GordieHowe/Applications/FieldInterps/Fq20.lean`) for every field identifier
(`interpQROM`); the opaque functions are never read.
-/

namespace GordieHowe.Falcon512.Ring.Native.QROMParams

open RealizedProgram.Export RelativePacking Ligero.MaskRow
open Generated.Falcon512.Ring.Native.QROMParams.Program (program)
open scoped NNReal

/-! ## The interpretation -/

/-- **The interpretation of the program of the native Falcon ring at the QROM parameters**: every field identifier is
`F_q^20` (the program has one field); the opaque functions are never read. -/
abbrev interpQROM : RealizedProgram.Interp := ⟨fun _ => RealizedProgram.fq20, fun _ _ _ => 0⟩

end GordieHowe.Falcon512.Ring.Native.QROMParams
