-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHowe.Generated.MLDSA44.Native.ROMParams.Certified

/-!
# Types through the field table

A program's types reduce from its field table and the field registry at reducible transparency,
without unfolding its program or plan (`GordieHowe.ProgramData`,
`GordieHowe/Applications/FieldInterps/Registry.lean`), at `MLDSA44.Native.ROMParams`:

* T1: domain `A`'s packing facts' type is `F_q^6`'s;
* T2: circuit `1`'s field is `GF(2^128)`;
* T3: the certified data's type at the data's projections is its type at the program's constants;
* T4: T1-T3, and the certified data and the proof system, with the program and the plan
  irreducible.

Historical statement and implementation equality checks are run separately as gate evidence;
this module retains structural design regressions only.
-/

namespace GordieHoweTest.ProgramDataTypes

open GordieHowe RealizedProgram GordieHowe.Generated.MLDSA44.Native.ROMParams

/-- T1. -/
example : (data.interp.field (data.fieldTable.domainField 0)).Packing = fq6.Packing := by
  with_reducible rfl

/-- T2. -/
example : (data.interp (data.fieldTable.circuitField 1)).K = gf128.K := by
  with_reducible rfl

/-- T3. -/
example : CertifiedProgram data.plan data.program data.interp =
    CertifiedProgram Plan.plan Program.program interp := by
  with_reducible rfl

section T4

example : (data.interp.field (data.fieldTable.domainField 0)).Packing = fq6.Packing := by
  with_reducible rfl

example : (data.interp (data.fieldTable.circuitField 1)).K = gf128.K := by
  with_reducible rfl

example : CertifiedProgram data.plan data.program data.interp =
    CertifiedProgram Plan.plan Program.program interp := by
  with_reducible rfl

example : CertifiedProgram Plan.plan Program.program interp :=
  { runtimeInputs.certified completionInputs conditions.fullFacts with ready := ready }

example : ProofSystems :=
  runtimeInputs.proofSystemOf runtimeParts (conditions.certs runtimeParts_eq)
    conditions.coreFacts

end T4

/-! ## The plan's opaque-function set against the field table -/

/-- The exported plan names the field table's opaque-function set. -/
example : data.opaqueSetB = true := by
  decide +kernel

/-- A descriptor naming a different opaque-function set fails the part. -/
example : ({ data with fieldTable := { data.fieldTable with interp := .two .gf128 .gf128 .mdoc } }
    : ProgramData).opaqueSetB = false := by
  decide +kernel

/-- **A wrong `none`**: the plan and the descriptor agree on `none`, but this program's opaque values
take arguments. `none` would read them as the constant `0`, so the part fails. -/
example : ({ data with
    plan := { data.plan with opaqueSet := "none" }
    fieldTable := { data.fieldTable with interp := .two .gf128 .gf128 .none } }
    : ProgramData).opaqueSetB = false := by
  decide +kernel

/-- The converse: a set other than `none` for a program with no opaque arguments fails the part. -/
example : ({ data with program := { data.program with values := [] } }
    : ProgramData).opaqueSetB = false := by
  decide +kernel

/-- The program's check rejects a wrong `none`, through the soundness of `programOkB`. -/
example (d : ProgramData) (hk : d.fieldTable.interp.opaque = .none) (hf : d.opaqueFreeB = false) :
    d.programOkB ≠ true := fun h => by
  have := (programOk_sound d h).opaqueFree.1 hk
  simp [hf] at this

end GordieHoweTest.ProgramDataTypes
