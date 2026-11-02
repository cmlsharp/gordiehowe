-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Carrier.HonestFull
public import GordieHowe.Applications.MLDSA44.Ring.Carrier.ROMParams.Frontend.Front
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.GadgetFacts
public import GordieHowe.Applications.MLDSA44.Emulated.ROMParams.GadgetFacts
public import GordieHowe.Generated.MLDSA44.Ring.Carrier.ROMParams.Realize

@[expose] public section

/-!
# GordieHowe: the gadget facts of `MLDSA44.Ring.Carrier.ROMParams`

The program facts the honest execution of the ML-DSA-44 ring carrier at the ROM parameters reads
(`GordieHowe.MLDSA44.Ring.Carrier.MldsaCarrierHonest`), decided on the tables of
`GordieHowe.Generated.MLDSA44.Ring.Carrier.ROMParams.Program.program` and of the native and emulated
programs it holds, and the proofs of possession's honest classes at the held programs.
-/

namespace GordieHowe.MLDSA44.Ring.Carrier.ROMParams

open Generated.MLDSA44.Ring.Carrier.ROMParams.Program RealizedProgram

/-- The native program the carrier holds has the honest hash's facts. -/
instance : MLDSA44.MldsaHHonest (CarrierHEmbed.nat program) :=
  inferInstanceAs (MLDSA44.MldsaHHonest nat)

/-- The native program the carrier holds has the memory check's facts. -/
instance : MLDSA44.MldsaHShuffle (CarrierHEmbed.nat program) :=
  inferInstanceAs (MLDSA44.MldsaHShuffle nat)

/-- The native program the carrier holds has SampleInBall's honest cells. -/
instance : MLDSA44.MldsaHSelHonest (CarrierHEmbed.nat program) :=
  inferInstanceAs (MLDSA44.MldsaHSelHonest nat)

/-- The emulated program's native program has the honest hash's facts. -/
instance : MLDSA44.MldsaHHonest
    (Emulated.MldsaEmbed.nat (CarrierAEmbed.emu program)) :=
  inferInstanceAs (MLDSA44.MldsaHHonest (Emulated.MldsaEmbed.nat emu))

/-- The emulated program's native program has SampleInBall's honest cells. -/
instance : MLDSA44.MldsaHSelHonest
    (Emulated.MldsaEmbed.nat (CarrierAEmbed.emu program)) :=
  inferInstanceAs (MLDSA44.MldsaHSelHonest (Emulated.MldsaEmbed.nat emu))

/-- The emulated program the carrier holds has the honest strategy's facts. -/
noncomputable instance : Emulated.MldsaEmulatedHonest (CarrierAEmbed.emu program)
    RealizedProgram.gold2 RealizedProgram.gf128 :=
  inferInstanceAs (Emulated.MldsaEmulatedHonest emu RealizedProgram.gold2 RealizedProgram.gf128)

set_option maxRecDepth 100000 in
-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- **The carrier's honest values' facts**, decided. -/
instance : MldsaCarrierHonest program where
  qD := ⟨645, [543, 544, 545]⟩
  kind64 := rfl
  qFits := ⟨by decide, by decide, by decide⟩
  member_nodup := by decide +kernel
  member_none := by decide +kernel
  member_noneA := by decide +kernel
  member_cells := by decide +kernel
  qSizes := by decide +kernel
  privCellH := by decide +kernel
  privCellA := by decide +kernel
  coreV := by decide +kernel
  selV := by decide +kernel
  aVals := by decide +kernel
  boundExprs := by decide +kernel
  bound := Generated.MLDSA44.Ring.Carrier.ROMParams.Realize.derivable.elim fun _ hD => hD.bound

/-- **The carrier's table selection's identifiers.** -/
instance : MldsaCarrierSelect program where
  idx58 := rfl
  pred0 := rfl
  idxPred8 := rfl

set_option maxRecDepth 100000 in
-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- **The carrier's quotient's facts**, decided. -/
instance : MldsaCarrierQuot program where
  sigReal := ⟨_, rfl, rfl, rfl, rfl, rfl⟩
  qRange := ⟨_, _, rfl, by decide⟩
  field64 := by decide +kernel
  size64 := by decide +kernel
  lt64 := by decide +kernel

/-- Domain `A`'s node `GF(p^1)` is the prime subfield `F_p`. -/
instance : CarrierANode RealizedProgram.gold2 :=
  ⟨⟨RelativePacking.fixedField _ pGold 1, fun x => by
    change x ∈ RealizedProgram.gold2Node "GF(p^1)" ↔ _
    rw [RealizedProgram.gold2Node, if_pos rfl]
    rfl⟩⟩

set_option maxRecDepth 100000 in
-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- **The carrier's execution facts**, decided. -/
instance : MldsaCarrierExec program where
  wf := Generated.MLDSA44.Ring.Carrier.ROMParams.Valid.wellFormed
  predicates_length := by decide +kernel
  nonSource := by decide +kernel
  checks := by decide +kernel
  ranges := by decide +kernel
  keysSize := by decide +kernel
  crossOperands := by decide +kernel
  len42 := by decide +kernel
  cell_classes := by decide +kernel

end GordieHowe.MLDSA44.Ring.Carrier.ROMParams
