-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Native.HonestFull
public import GordieHowe.Applications.MLDSA44.Ring.Native.QROMParams.Frontend.Front
public import GordieHowe.Applications.MLDSA44.Native.QROMParams.GadgetFacts
public import GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.Realize

@[expose] public section

/-!
# GordieHowe: the gadget facts of `MLDSA44.Ring.Native.QROMParams`

The program facts the honest execution of the native ML-DSA-44 ring program at the QROM parameters
reads (`GordieHowe.MLDSA44.Ring.Native.MldsaRingHonest`), decided on the tables of
`GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.Program.program` and of the native program it holds
(`GordieHowe.Generated.MLDSA44.Native.QROMParams.Program.program`), and the native program's honest classes
at the held program.
-/

namespace GordieHowe.MLDSA44.Ring.Native.QROMParams

open Generated.MLDSA44.Ring.Native.QROMParams.Program RealizedProgram

/-- The native program the ring holds has the honest hash's facts. -/
instance : MLDSA44.MldsaHHonest (MldsaRingEmbed.nat program) :=
  inferInstanceAs (MLDSA44.MldsaHHonest nat)

/-- The native program the ring holds has the memory check's facts. -/
instance : MLDSA44.MldsaHShuffle (MldsaRingEmbed.nat program) :=
  inferInstanceAs (MLDSA44.MldsaHShuffle nat)

/-- The native program the ring holds has SampleInBall's honest cells. -/
instance : MLDSA44.MldsaHSelHonest (MldsaRingEmbed.nat program) :=
  inferInstanceAs (MLDSA44.MldsaHSelHonest nat)

/-- The native program the ring holds has the honest strategy's facts. -/
noncomputable instance : MLDSA44.Native.MldsaNativeHonest (MldsaRingEmbed.nat program)
    RealizedProgram.fq11 RealizedProgram.gf256 :=
  inferInstanceAs (MLDSA44.Native.MldsaNativeHonest nat RealizedProgram.fq11
    RealizedProgram.gf256)

set_option maxRecDepth 100000 in
-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- **The ring program's honest values' facts**, decided. -/
instance : MldsaRingHonest program where
  inv := ringInv σQ
  inv_val := by decide +kernel
  member_ne := by decide +kernel
  member_nodup := by decide +kernel
  memberCells := by decide +kernel
  privCell := by decide +kernel
  coreV := by decide +kernel
  selV := by decide +kernel
  aV := by decide +kernel
  boundExprs := by decide +kernel
  len50 := by decide +kernel
  crossOperands := by decide +kernel
  bound := Generated.MLDSA44.Ring.Native.QROMParams.Realize.derivable.elim fun _ hD => hD.bound

set_option maxRecDepth 100000

-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
theorem predicates_length : program.predicates.length = 249 := by decide +kernel
-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
theorem nonSource : ∀ q ∈ [8, 9, 16, 21, 22, 23, 247], program.inSource (program.predicate q) = false := by
  decide +kernel
-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
theorem checks : program.statement.checks = [] := by decide +kernel
-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
theorem noBounds : program.declaredRanges = [] := by decide +kernel

-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- The committed source values' classes, decided. -/
theorem cell_classes : (List.range program.values.length).all (fun v =>
    !program.privCellB v || !decide (program.IsSourceValue v) ||
      ([MldsaRingRelation.aHat program, MldsaRingRelation.t1 program, MldsaRingFront.muA program,
          (TableSelect.shape program).idx].contains v && program.valueField v == 0 &&
        (program.value v).node.map (·.name) == some "GF(p^1)") ||
      (decide (MldsaRingHonest.inv program v ∈ ringV) &&
        (MldsaRingEmbed.σ program).val (MldsaRingHonest.inv program v) == v &&
        ((MLDSA44.Native.AValues.contains (MldsaRingHonest.inv program v) && program.valueField v == 0 &&
            (program.value v).node.map (·.name) == some "GF(p^1)") ||
          (natGF16B (MldsaRingHonest.inv program v) && program.valueField v == 1 &&
            (program.value v).node.map (·.name) == some "GF(2^16)") ||
          ([556, 561].contains (MldsaRingHonest.inv program v) && program.valueField v == 1 &&
            (program.value v).node.map (·.name) == some "bit")))) = true := by
  decide +kernel

/-- **The ring program's execution facts**, decided. -/
instance : MldsaRingExec program where
  wf := Generated.MLDSA44.Ring.Native.QROMParams.Valid.wellFormed
  predicates_length := predicates_length
  nonSource := nonSource
  predIds := ⟨rfl, rfl⟩
  checks := checks
  noBounds := noBounds
  cell_classes := cell_classes

end GordieHowe.MLDSA44.Ring.Native.QROMParams
