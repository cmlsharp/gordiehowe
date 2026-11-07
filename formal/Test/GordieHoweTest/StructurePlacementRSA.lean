-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe.Language.RealizedProgram.Placement
import GordieHoweCerts.Generated.RSA2048.Goldilocks2.Msg2KiB.ROMParams.Program
import GordieHoweCerts.Generated.RSA2048.Goldilocks2.Msg2KiB.ROMParams.Structure

/-!
# Tests of the realized route at the structure records' pointer

On RSA2048 (Goldilocks², 2 KiB message, ROM parameters), the one program with a realized predicate
(predicate `728`, realized by predicate `729` through conversion `0`): the exported routes hold
that route, and the route check (`routeOkE`) accepts it and refuses a route with no conversion,
naming the wrong conversion, one too many, or another realizing predicate (`realized`). The
exported routes themselves are checked whole by the applications' placement check.
-/

namespace GordieHoweTest.StructurePlacementRSA

open GordieHowe GordieHowe.RealizedProgram GordieHowe.Twin
open GordieHowe.Generated.RSA2048.Goldilocks2.Msg2KiB.ROMParams

/-- The reason a twin reports, if any. -/
def reasonOf : Except StructFailure Unit → Option StructReason
  | .ok _ => none
  | .error f => some f.reason

/-- The program. -/
abbrev ir : RealizedProgram := Program.program

/-- The exported records. -/
abbrev S : Structure := Structure.records

/-- The exported routes give predicate `728` the realized route through conversion `0`. -/
example : S.routes.lookup 728 = some (.realized 729 [0]) := by decide +kernel

/-- The exported route checks. -/
example : reasonOf (ir.routeOkE 728 (ir.predicate 728) (.realized 729 [0])) = none := by
  decide +kernel

/-- No conversion: refused. -/
example : reasonOf (ir.routeOkE 728 (ir.predicate 728) (.realized 729 [])) = some .realized := by
  decide +kernel

/-- A conversion that pairs nothing here: refused. -/
example : reasonOf (ir.routeOkE 728 (ir.predicate 728) (.realized 729 [1])) = some .realized := by
  decide +kernel

/-- One conversion too many: refused. -/
example :
    reasonOf (ir.routeOkE 728 (ir.predicate 728) (.realized 729 [0, 0])) = some .realized := by
  decide +kernel

/-- Another realizing predicate: refused. -/
example : reasonOf (ir.routeOkE 728 (ir.predicate 728) (.realized 728 [0])) = some .realized := by
  decide +kernel

end GordieHoweTest.StructurePlacementRSA
