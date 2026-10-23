-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldFJ
public import GordieHowe.ProofSystem.Program.FieldForkSizes
public import GordieHowe.ProofSystem.Program.FieldPackings
public import GordieHowe.Applications.MLDSA44.Emulated.ROMParams.ProofSystem

@[expose] public section

/-!
# GordieHowe: the round charges of `MLDSA44.Emulated.ROMParams`'s domains

The prefix cells (`np0`, `np1`) of both domains' generic per-field domain proofs at their ready data
`ready` (`GordieHowe/Applications/MLDSA44/Emulated/ROMParams/ProofSystem.lean`), which their round charges
(`GordieHowe.RealizedProgram.FieldRoundsLe`) read.
-/

namespace GordieHowe.MLDSA44.Emulated.ROMParams

open RealizedProgram.Export IOP
open Generated.MLDSA44.Emulated.ROMParams.Program (program)
open HashField (interp)
open scoped NNReal

/-! ## The round charges -/

theorem np0 : RealizedProgram.npOf (ready domainA).Pk (ready domainA).rs = 2 * 2 := by decide +kernel

theorem np1 : RealizedProgram.npOf (ready domainH).Pk (ready domainH).rs = 48 := by decide +kernel

end GordieHowe.MLDSA44.Emulated.ROMParams
