-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Interval
public import GordieHowe.Language.RealizedProgram.WithPlan
public import GordieHowe.Applications.FieldInterps.Basic
public import GordieHowe.Applications.Falcon512.Ring.Native.System.Params
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative9Relative
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNativeCoords
public import GordieHowe.Language.Realizations.MaskSubfield
public import GordieHowe.Generated.Falcon512.Ring.Native.ROMParams.Program
public import GordieHowe.Generated.Falcon512.Ring.Native.ROMParams.Plan
public import GordieHowe.Language.Export.Valid

@[expose] public section

/-!
# GordieHowe: the interpretation of `Falcon512.Ring.Native.ROMParams`

The interpretation of the realized program of the native Falcon ring at the ROM parameters
(`GordieHowe.Generated.Falcon512.Ring.Native.ROMParams.Program.program`, export `b65a4929`: one domain `A` over
`F_q^9`, one GKR circuit `c.A`, the batches `norm.center`, `norm.column0`, `norm.column1` and
`norm.column2`), whose domain proof is the generic per-field one
(`GordieHowe/Applications/Falcon512/Ring/Native/ROMParams/ProofSystem.lean`): the field `F_q^9` (`fq9`,
`GordieHowe/Applications/FieldInterps/Basic.lean`: constants decoded as casts of naturals, the integer reading
the constant coefficient, the node `GF(p^1)` the prime subfield `F_q`) for every field identifier
(`interpROM`); the program's opaque values take no arguments (read from the statement), so the
opaque functions are never read.
-/

namespace GordieHowe.Falcon512.Ring.Native.ROMParams

open RealizedProgram.Export RelativePacking Ligero.MaskRow
open Generated.Falcon512.Ring.Native.ROMParams.Program (program)
open scoped NNReal

/-! ## The interpretation -/

/-- **The interpretation of the program of the native Falcon ring at the ROM parameters**: every field identifier is
`F_q^9` (the program has one field); the opaque functions are never read (the program's opaque
values take no arguments). -/
abbrev interpROM : RealizedProgram.Interp := ⟨fun _ => RealizedProgram.fq9, fun _ _ _ => 0⟩

end GordieHowe.Falcon512.Ring.Native.ROMParams
