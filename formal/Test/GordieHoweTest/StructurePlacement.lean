-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe.Language.RealizedProgram.Placement
import GordieHowe.Generated.MLDSA44.Native.ROMParams.Program
import GordieHowe.Generated.MLDSA44.Native.ROMParams.Structure

/-!
# Tests of the cells checks at the structure records' placement pointers

On MLDSA44 Native, ROM parameters: the placement check (`placementE`) accepts the exported records
and gives the cells checks (`cellsValid_of_placementB`); each of its checkers refuses a corrupted
record or program through its twin, naming the reason (`StructReason`):

* the routes (`routesE`): a route to another part or entry (`routePointer`), a missing route
  (`routeMissing`), an extra route (`routeExtra`);
* the batch routes (`batchRoutesE`): routes moved to other parts (`batchRoutes`);
* the batches (`batchesE`): a batch failing the batch check (`batch`);
* the hosts (`logupHostsE`, `macHostsE`): a missing group (`logupKeys`), a host at another entry
  (`logupPointer`), a missing H half's host (`macHKeys`), an H half's host at another entry
  (`macHPointer`);
* the challenge values (`chalValuesE`): a listed value of another kind (`chalValue`), a challenge
  with no listed value (`chalSweep`);
* the sweeps (`alphasE`, `entriesE`, `typesE`) and the domains (`placementE`): a table whose
  challenge no value holds (`alpha`), an entry naming no predicate (`entry`), a value claimed
  node-typed (`types`), no domain (`nonempty`).

The realized route (`realized`) is tested on the one program with a realized predicate, RSA2048
(`GordieHoweTest.StructurePlacementRSA`).
-/

namespace GordieHoweTest.StructurePlacement

open GordieHowe GordieHowe.RealizedProgram GordieHowe.Twin
open GordieHowe.Generated.MLDSA44.Native.ROMParams

/-- The reason a twin reports, if any. -/
def reasonOf : Except StructFailure Unit → Option StructReason
  | .ok _ => none
  | .error f => some f.reason

/-- The program. -/
abbrev ir : RealizedProgram := Program.program

/-- The exported records. -/
abbrev S : Structure := Structure.records

/-- The exported records pass, and give the cells checks. -/
example : reasonOf (ir.placementE S) = none := by decide +kernel

theorem cellsValid : ir.CellsValid := cellsValid_of_placementB (S := S) (by decide +kernel)

/-- The verdict is the twin's. -/
example (T : Structure) : ir.placementB T = okB (ir.placementE T) := rfl

/-- The first entry of a list changed by `f`. -/
def modHead {α : Type} (f : α → α) : List α → List α
  | x :: xs => f x :: xs
  | [] => []

/-- A route moved to the next part, entry or row kind. -/
def bump : Route → Route
  | .batch b j => .batch b (j + 1)
  | .gkr c k => .gkr c (k + 1)
  | .affine v => .affine !v
  | r => r

/-- The first route moved: refused at its pointer. -/
example :
    reasonOf (ir.routesE { S with routes := modHead (fun pr => (pr.1, bump pr.2)) S.routes }) =
      some .routePointer := by
  decide +kernel

/-- Every batch route moved to the next part: refused by the batch routes' walk. -/
example :
    reasonOf (ir.batchRoutesE { S with routes := S.routes.map fun pr => (pr.1,
      match pr.2 with
      | .batch b j => .batch b (j + 1)
      | r => r) }) = some .batchRoutes := by
  decide +kernel

/-- The first route dropped: refused as missing. -/
example : reasonOf (ir.routesE { S with routes := S.routes.drop 1 }) = some .routeMissing := by
  decide +kernel

/-- A route past the predicates: refused as extra. -/
example :
    reasonOf (ir.routesE { S with routes := S.routes ++ [(ir.predicates.length, .quadratic)] }) =
      some .routeExtra := by
  decide +kernel

/-- Batch 0 with degree `0`: refused by the batch check. -/
example :
    reasonOf { ir with batches := modHead (fun B => { B with degree := 0 }) ir.batches }.batchesE =
      some .batch := by
  decide +kernel

/-- The first group's host dropped: the keys are not the groups. -/
example : reasonOf (ir.logupHostsE { S with logupHosts := S.logupHosts.drop 1 }) =
    some .logupKeys := by decide +kernel

/-- The first group's host moved to the next entry. -/
example : reasonOf (ir.logupHostsE
    { S with logupHosts := modHead (fun h => (h.1, (h.2.1, h.2.2 + 1))) S.logupHosts }) =
    some .logupPointer := by decide +kernel

/-- The H half's host dropped. -/
example : reasonOf (ir.macHostsE { S with macHosts := S.macHosts.drop 1 }) = some .macHKeys := by
  decide +kernel

/-- The H half's host moved to the next entry. -/
example : reasonOf (ir.macHostsE
    { S with macHosts := modHead (fun h => (h.1, (h.2.1, h.2.2 + 1))) S.macHosts }) =
    some .macHPointer := by decide +kernel

/-- The first challenge's value pointed at value `0`, a constant. -/
example :
    reasonOf (ir.chalValuesE
      { S with chalValues := modHead (fun jv => (jv.1, 0)) S.chalValues }) =
      some .chalValue := by
  decide +kernel

/-- The first challenge's value dropped: a value holds a challenge with no listed value. -/
example : reasonOf (ir.chalValuesE { S with chalValues := S.chalValues.drop 1 }) =
    some .chalSweep := by decide +kernel

/-- Table 0's challenge replaced by one no value holds. -/
example :
    reasonOf
      ({ ir with tables := modHead (fun T => { T with alpha := 100000 }) ir.tables }.alphasE S) =
      some .alpha := by
  decide +kernel

/-- Circuit 0 given an entry naming no predicate. -/
example : reasonOf ({ ir with
      circuits :=
        modHead (fun C => { C with entries := C.entries ++ [CircuitEntry.pred 1000000] })
          ir.circuits
    }.entriesE S) = some .entry := by decide +kernel

/-- Value 0, a constant, claimed node-typed. -/
example :
    reasonOf
      { ir with values := modHead (fun x => { x with typeSource := .node }) ir.values }.typesE =
      some .types := by
  decide +kernel

/-- No domain. -/
example : reasonOf ({ ir with domains := [] }.placementE S) = some .nonempty := by decide +kernel

end GordieHoweTest.StructurePlacement
