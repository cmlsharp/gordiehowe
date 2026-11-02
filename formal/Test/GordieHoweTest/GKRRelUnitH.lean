-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHoweTest.GKRRelUnitData
import GordieHowe.Generated.RSA2048.Goldilocks2.Msg2KiB.ROMParams.GKR.H
import GordieHowe.Generated.MLDSA44.Native.ROMParams.GKR.H

/-!
# Family records of exported H circuits

RSA H's alignment entry is accepted with its filler block and rejected with another block.
MLDSA44 H's MAC H record (the C++ export) is accepted, and rejected with its powers pointer naming
the tag's node or one chunk's wire changed.
-/

namespace GordieHoweTest.GKRRelUnit

open GordieHowe GordieHowe.Twin GordieHowe.RealizedProgram GordieHowe.GKR.Rel GordieHowe.GKR.Fold
open GordieHowe.Generated.Falcon512.Native.ROMParams.Program

open GordieHowe.Generated.RSA2048.Goldilocks2.Msg2KiB.ROMParams in
/-- Accepted: RSA H's alignment entry, its pairs reading the filler block `13`. -/
example : okB (entryHeadE GordieHowe.Generated.RSA2048.Goldilocks2.Msg2KiB.ROMParams.Program.program
    GKR.H.cert.c GKR.H.ar GKR.H.cert 0) = true := by
  decide +kernel

open GordieHowe.Generated.RSA2048.Goldilocks2.Msg2KiB.ROMParams in
/-- Rejected: the alignment record naming block `12`. -/
example : okB (entryHeadE GordieHowe.Generated.RSA2048.Goldilocks2.Msg2KiB.ROMParams.Program.program
    GKR.H.cert.c GKR.H.ar
    (mutFam GKR.H.cert 0 fun _ => .alignment 12) 0) = false := by
  decide +kernel

/-- A MAC H record changed by `f`. -/
def mutMac (f : MacHCert → MacHCert) : FamCert → FamCert
  | .macH mc => .macH (f mc)
  | x => x

open GordieHowe.Generated.MLDSA44.Native.ROMParams in
/-- Accepted: MLDSA44 H's MAC H entry `10` (its guards: the powers' `powersB`, the tag, the
operand's padding; its item `U − Σ_c chunk_c · r_c`). -/
example : okB (entryHeadE GordieHowe.Generated.MLDSA44.Native.ROMParams.Program.program GKR.H.cert.c
    GKR.H.ar GKR.H.cert 10) = true := by
  decide +kernel

open GordieHowe.Generated.MLDSA44.Native.ROMParams in
/-- Accepted: its first four chunk cuts `Σ_i g^i · X[c w + i]`. -/
example : okB (famSliceE GordieHowe.Generated.MLDSA44.Native.ROMParams.Program.program GKR.H.cert.c
    GKR.H.ar GKR.H.cert 10 0 4) = true := by
  decide +kernel

open GordieHowe.Generated.MLDSA44.Native.ROMParams in
/-- Rejected: the powers pointer naming the tag's node. -/
example : okB (entryHeadE GordieHowe.Generated.MLDSA44.Native.ROMParams.Program.program GKR.H.cert.c
    GKR.H.ar (mutFam GKR.H.cert 10 (mutMac fun mc => { mc with powers := mc.tag })) 10)
      = false := by
  decide +kernel

open GordieHowe.Generated.MLDSA44.Native.ROMParams in
/-- Rejected: chunk `0`'s wire replaced by chunk `1`'s (its cut against the powers of `g`). -/
example : okB (famSliceE GordieHowe.Generated.MLDSA44.Native.ROMParams.Program.program GKR.H.cert.c
    GKR.H.ar (mutFam GKR.H.cert 10 (mutMac fun mc =>
      { mc with chunks := mc.chunks.getD 1 default :: mc.chunks.drop 1 })) 10 0 1) = false := by
  decide +kernel

end GordieHoweTest.GKRRelUnit
