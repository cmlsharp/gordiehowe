-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Carrier.QROMParams.Facts
public import GordieHowe.Applications.Falcon512.Ring.Carrier.Honest
public import GordieHowe.Generated.Falcon512.Ring.Carrier.QROMParams.Realize

@[expose] public section

/-!
# GordieHowe: the honest prover's program facts of `Falcon512.Ring.Carrier.QROMParams`

The program facts the honest strategy of the Falcon ring carriers reads
(`GordieHowe.Falcon512.Ring.FalconRingRoleFacts`, `GordieHowe.Falcon512.Ring.FalconRingSource`,
`GordieHowe.Falcon512.Ring.FalconCarrierHonest`), decided on the tables of
`GordieHowe.Generated.Falcon512.Ring.Carrier.QROMParams.Program.program` (export `b65a4929`), and domain `A`'s node
`GF(p^1)`, the prime subfield (`GordieHowe.Falcon512.Ring.PrimeNode`).
-/

namespace GordieHowe.Falcon512.Ring.Carrier.QROMParams

open Ring RealizedProgram
open Generated.Falcon512.Ring.Carrier.QROMParams.Program (program)

/-- Domain `A`'s node `GF(p^1)` is the prime subfield `F_p`. -/
instance : PrimeNode (interpQROM 0) :=
  ⟨⟨RelativePacking.fixedField _ pGold 1, fun x => by
    change x ∈ gold4Node "GF(p^1)" ↔ _
    rw [gold4Node, if_pos rfl]
    rfl⟩⟩

set_option maxRecDepth 4096 in
/-- The roles of the honest values: each is its value's, a committed cell. -/
instance : FalconRingRoleFacts program where
  roles := by decide +kernel
  privCell := by decide +kernel

set_option maxRecDepth 4096 in
/-- The source strategy's facts. -/
instance : FalconRingSource program where
  wf := Generated.Falcon512.Ring.Carrier.QROMParams.Valid.wellFormed
  bounds := by decide +kernel
  noCross := by decide +kernel
  cells := by decide +kernel
  noPadCopy := by decide +kernel
  typed := by decide +kernel
  checks := by decide +kernel

set_option maxRecDepth 4096 in
/-- The carrier's honest facts: the realization's predicates, the bound values. -/
instance : FalconCarrierHonest program where
  refsOrdered := (RealizedProgram.refsOrderedB_iff program).1 (by decide +kernel)
  idx9 := rfl
  realPreds := by decide +kernel
  quotKind := rfl
  mag1Kind := rfl
  sqKind := rfl
  fields := by decide +kernel
  roleFields := by decide +kernel
  sizes512 := by decide +kernel
  sizes1 := by decide +kernel
  lens := by decide +kernel
  bound := Generated.Falcon512.Ring.Carrier.QROMParams.Realize.derivable.elim fun _ hD => hD.bound
  cover := by decide +kernel

end GordieHowe.Falcon512.Ring.Carrier.QROMParams
