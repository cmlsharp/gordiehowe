-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Native.QROMParams.Facts
public import GordieHowe.Applications.Falcon512.Ring.Honest

@[expose] public section

/-!
# GordieHowe: the honest prover's program facts of `Falcon512.Ring.Native.QROMParams`

The program facts the generic honest strategy of the native Falcon rings reads
(`GordieHowe.Falcon512.Norm.FalconNormHonest`, `GordieHowe.Falcon512.Ring.FalconRingRoleFacts`, `GordieHowe.Falcon512.Ring.FalconRingHonest`,
`GordieHowe.Falcon512.Ring.FalconRingSource`), decided on the tables of
`GordieHowe.Generated.Falcon512.Ring.Native.QROMParams.Program.program` (export `b65a4929`): the slack's digits
`23 … 26` and the budget `27`, the slack's expression `52` and its predicates `12` and `13`, the
high parts' complement `55` with the constant `22`, the static histograms `28 … 32`.
-/

namespace GordieHowe.Falcon512.Ring.Native.QROMParams

open Ring Norm RealizedProgram
open Generated.Falcon512.Ring.Native.QROMParams.Program (program)

set_option maxRecDepth 4096 in
/-- The honest norm's facts: the norm's values are private committed cells. -/
instance : FalconNormHonest program where
  privCell := by decide +kernel

set_option maxRecDepth 4096 in
/-- The roles of the honest values: each is its value's, a committed cell. -/
instance : FalconRingRoleFacts program where
  roles := by decide +kernel
  privCell := by decide +kernel

set_option maxRecDepth 4096 in
/-- The native honest strategy's facts: the norm in domain `0` of field `0`, the predicates' cover. -/
instance : FalconRingHonest program where
  dA_eq := rfl
  fA_eq := rfl
  s2_eq := rfl
  s1_eq := rfl
  cover := by decide +kernel

set_option maxRecDepth 4096 in
/-- The source strategy's facts. -/
instance : FalconRingSource program where
  wf := Generated.Falcon512.Ring.Native.QROMParams.Valid.wellFormed
  bounds := by decide +kernel
  noCross := by decide +kernel
  cells := by decide +kernel
  noPadCopy := by decide +kernel
  typed := by decide +kernel
  checks := by decide +kernel

end GordieHowe.Falcon512.Ring.Native.QROMParams
