-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe.Generated.Falcon512.Native.ROMParams.Completion
import GordieHowe.Generated.MLDSA44.Native.ROMParams.Completion
import GordieHowe.Generated.RSA2048.Goldilocks2.Msg2KiB.ROMParams.Completion

/-!
# Tests of the MAC sites read at the structure records

The completeness certificate's MAC steps read their site at a `macSite` record (`macSiteAt`) and
check the role they name (`macRoleAtB`); a cross-field `equal`'s site is its record's `y`-side site
(`macCB`). On the exported records of Falcon512 Native (a grouped tail), MLDSA44 Native (a digit
tail) and RSA2048 (a one-digit tail): accepted at the exported pointers, refused at a wrong tail, a
wrong group, a role of another form, a record of another kind, a missing slot and a missing record,
each refusal also through the twin with its reason.
-/

namespace GordieHoweTest.MacStructure

open GordieHowe GordieHowe.RealizedProgram GordieHowe.Twin

/-- The failure a twin reports, if any. -/
def failOf {α : Type} : Except StructFailure α → Option StructFailure
  | .ok _ => none
  | .error f => some f

/-- A site as a triple, to compare. -/
def triple (st : Option MacSite) : Option (ℕ × Bool × ℕ) := st.map fun s => (s.pid, s.xSide, s.tail)

namespace Falcon

open GordieHowe.Generated.Falcon512.Native.ROMParams

/-- The program. -/
abbrev ir : RealizedProgram := Program.program
/-- The plan's prime-subfield nodes. -/
abbrev N := primeNodesOf Plan.plan Program.program
/-- The exported structure records. -/
abbrev S : Structure := Structure.records

/-- The exported certificate checks at the exported records. -/
example : ir.completionB N Honest.nodes S Cert.gens Cert.cderivs = true :=
  Completion.completionOk

/-- Record 0 names the MAC's only site: `mac.equal` (309), over `y`'s field, tail `mac` (307). -/
example : triple (ir.macSiteAt S 0 1) = some (309, false, 307) := by decide +kernel

/-- The site exported. -/
def st : MacSite := ⟨309, false, 307⟩

/-- The record has its kind's slots. -/
example : ir.macSiteB 0 (S.gadgets.getD 0 default) = true := by decide +kernel

/-- The record with its values swapped: refused, a slot mismatch. -/
example : failOf (ir.macSiteE 0 { S.gadgets.getD 0 default with
    values := (S.gadgets.getD 0 default).values.reverse }) = some ⟨0, 0, .slotMismatch⟩ := by
  decide +kernel

/-- The cross-field `equal`'s site checks. -/
example : ir.macCB N S Cert.gens 309 = true := by decide +kernel

/-- (a) The record's tail replaced by `mac.final.q` (306): the site's facts fail. -/
def badTail : Structure :=
  { S with gadgets := S.gadgets.set 0 { S.gadgets.getD 0 default with preds := [309, 306] } }

example : ir.macCB N badTail Cert.gens 309 = false := by decide +kernel
example : failOf (ir.macCE N badTail Cert.gens 309) = some ⟨0, 1, .siteFacts⟩ := by decide +kernel

/-- (b) Group 0's row step moved to `mac.A.g1` (286): the role fails there; group 1's holds. -/
example : (ir.cstepFact N S Cert.gens Cert.cderivs.ranks 0 286 (ir.predicate 286) []
    (.macRow 0 1 (.groupRow 0))).isNone = true := by decide +kernel
example : (ir.cstepFact N S Cert.gens Cert.cderivs.ranks 0 286 (ir.predicate 286) []
    (.macRow 0 1 (.groupRow 1))).isSome = true := by decide +kernel
example : failOf (ir.macRoleAtE N S st (.groupRow 0) 286) = some ⟨286, 0, .macRole⟩ := by
  decide +kernel

/-- (c) A digit tail's role on the grouped site: refused at `mac.gq` (305), which is the
quotient-digit lookup. -/
example : ir.macRoleAtB N S st .lowLookup 305 = false := by decide +kernel
example : failOf (ir.macRoleAtE N S st .lowLookup 305) = some ⟨305, 0, .macRole⟩ := by
  decide +kernel
example : ir.macRoleAtB N S st .gqLookup 305 = true := by decide +kernel

/-- (d) A record of another kind at the pointer: no site. -/
def fieldRecord : Gadget := { kind := .modField, preds := [308], values := [], params := [] }

/-- The exported records with a `modField` record appended (index 1). -/
def withField : Structure := { S with gadgets := S.gadgets ++ [fieldRecord] }

example : triple (ir.macSiteAt withField 1 1) = none := by decide +kernel
example : failOf (ir.macSiteAtE withField 1 1) = some ⟨1, 0, .notMacSite⟩ := by decide +kernel
/-- No record at the pointer, no site at slot `0`, none at slot `2` of a hosted MAC. -/
example : failOf (ir.macSiteAtE S 5 1) = some ⟨5, 0, .noRecord⟩ := by decide +kernel
example : failOf (ir.macSiteAtE S 0 0) = some ⟨0, 0, .noSlot⟩ := by decide +kernel
example : failOf (ir.macSiteAtE S 0 2) = some ⟨0, 2, .noSlot⟩ := by decide +kernel

/-- A step naming a record of another kind does not check. -/
example : (ir.cstepFact N withField Cert.gens Cert.cderivs.ranks 0 307 (ir.predicate 307) []
    (.macRow 1 1 .tail)).isNone = true := by decide +kernel

/-- (e) No record for the cross-field `equal`: refused, uncovered. -/
def noRecord : Structure := { S with gadgets := [] }

example : ir.macCB N noRecord Cert.gens 309 = false := by decide +kernel
example : failOf (ir.macCE N noRecord Cert.gens 309) = some ⟨309, 0, .uncovered⟩ := by
  decide +kernel

/-- The roles of the grouped tail's predicates, and none of the other forms'. -/
example : [(MacRole.tail, 307), (.h, 274), (.groupRow 0, 285), (.groupRow 3, 288),
    (.residues, 296), (.gqLookup, 305), (.quotLookup, 306)].all
      (fun (r, q) => ir.macRoleAtB N S st r q) = true := by decide +kernel
example : [(MacRole.tail, 306), (.h, 307), (.accRow, 285), (.groupRow 4, 285),
    (.residues, 305), (.quotLookup, 296), (.lowLookup, 305), (.topLookup, 306),
    (.wrap, 306)].all (fun (r, q) => !ir.macRoleAtB N S st r q) = true := by decide +kernel

end Falcon

namespace MLDSA

open GordieHowe.Generated.MLDSA44.Native.ROMParams

/-- The program. -/
abbrev ir : RealizedProgram := Program.program
/-- The plan's prime-subfield nodes. -/
abbrev N := primeNodesOf Plan.plan Program.program
/-- The exported structure records. -/
abbrev S : Structure := Structure.records

/-- Record 0 names the digit tail's site: `mac.equal` (272), tail `mac` (271). -/
example : triple (ir.macSiteAt Structure.records 0 1) = some (272, false, 271) := by decide +kernel

/-- The site exported. -/
def st : MacSite := ⟨272, false, 271⟩

/-- The ten roles on a digit tail: the tail, the accumulator row `mac.A` (4), the lookups
`mac.low` (15) and `mac.high` (16) and the no-wrap range (17) hold; no H predicate and none of the
grouped or one-digit tails' roles. -/
example : [(MacRole.tail, 271), (.accRow, 4), (.lowLookup, 15), (.topLookup, 16),
    (.wrap, 17)].all (fun (r, q) => ir.macRoleAtB N S st r q) = true := by decide +kernel
example : [(MacRole.h, 4), (.groupRow 0, 4), (.residues, 4), (.gqLookup, 15),
    (.quotLookup, 16), (.lowLookup, 16), (.tail, 4)].all
      (fun (r, q) => !ir.macRoleAtB N S st r q) = true := by decide +kernel

end MLDSA

namespace RSA

open GordieHowe.Generated.RSA2048.Goldilocks2.Msg2KiB.ROMParams

/-- The program. -/
abbrev ir : RealizedProgram := Program.program
/-- The plan's prime-subfield nodes. -/
abbrev N := primeNodesOf Plan.plan Program.program
/-- The exported structure records. -/
abbrev S : Structure := Structure.records

/-- Record 0 names the one-digit tail's site: `mac.equal` (739), tail `mac` (738). -/
example : triple (ir.macSiteAt Structure.records 0 1) = some (739, false, 738) := by decide +kernel

/-- The site exported. -/
def st : MacSite := ⟨739, false, 738⟩

/-- The ten roles on a one-digit tail: the tail, the H predicate `mac.H` (727), the accumulator row
`mac.A` (731) and the quotient lookup `mac.q` (737) hold; none of the grouped or digit tails'
roles. -/
example : [(MacRole.tail, 738), (.h, 727), (.accRow, 731), (.quotLookup, 737)].all
    (fun (r, q) => ir.macRoleAtB N S st r q) = true := by decide +kernel
example : [(MacRole.groupRow 0, 731), (.residues, 733), (.gqLookup, 737), (.lowLookup, 737),
    (.topLookup, 737), (.wrap, 737), (.h, 731)].all
      (fun (r, q) => !ir.macRoleAtB N S st r q) = true := by decide +kernel

end RSA

end GordieHoweTest.MacStructure
