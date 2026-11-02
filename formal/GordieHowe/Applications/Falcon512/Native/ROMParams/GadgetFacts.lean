-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Generated.Falcon512.Native.ROMParams.Realize
public import GordieHowe.Applications.Falcon512.Native.HonestFull
public import GordieHowe.Applications.Falcon512.Native.ROMParams.Frontend.HashFacts
public import GordieHowe.Applications.Falcon512.Native.ROMParams.Frontend.AlgebraFacts

@[expose] public section

/-!
# GordieHowe: the gadget facts of `Falcon512.Native.ROMParams`

The program's instances of the honest strategy's classes on the tables of
`GordieHowe.Generated.Falcon512.Native.ROMParams.Program.program`: the hash's, the selection's, the norm's and domain `A`'s facts,
the values' distinctness, the operands of every cross-field `equal`, the covering of the source
predicates and the committed source cells' classes (`FalconHonestFull`). These read the program's
gadgets by index; the program-wide facts the honest strategy reads are its honest roles
(`Completion.rolesOk`).
-/

namespace GordieHowe.Falcon512.Native.ROMParams

open Generated.Falcon512.Native.ROMParams.Program

set_option maxRecDepth 4096 in
-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- The honest hash facts of the program of `Falcon512.Native.ROMParams`. -/
instance : FalconHHonest program where
  words_checks := by decide +kernel
  state_checks := by decide +kernel
  buf_checks := by decide +kernel

-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- The selection values of the program of `Falcon512.Native.ROMParams`. -/
instance : FalconHSelHonest program where
  sel_checks := by decide +kernel

set_option maxRecDepth 8192 in
-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- The honest norm facts of the program of `Falcon512.Native.ROMParams` (`Norm.FalconNormHonest`): the
norm's values are private committed cells. -/
noncomputable instance : Norm.FalconNormHonest program where
  privCell := by decide +kernel

set_option maxRecDepth 8192 in
-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- The facts of honest domain A of the program of `Falcon512.Native.ROMParams`: the norm at domain and field `1`, the
field-form signature `289`, `c_A`'s check `292` and `mac.equal` `309`. -/
noncomputable instance : FalconAHonest program where
  toFalconAAlg := inferInstance
  norm_dA := rfl
  norm_fA := rfl
  norm_ids := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  pSigE := 289
  pCA := 292
  pMac := 309
  a_checks := by decide +kernel
  sizes_H := by decide +kernel
  const44 := by decide +kernel
  sigE_body := ⟨_, rfl⟩
  sigE_len := by decide +kernel
  ca_body := ⟨_, rfl⟩
  mac_body := ⟨_, _, rfl, by decide⟩
  cross_fields := by decide +kernel

/-! ## The honest strategy's program facts -/

set_option maxRecDepth 4096 in
-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- The values of the program of `Falcon512.Native.ROMParams` are distinct where the honest valuation reads them. -/
instance : FalconHValues program where
  not_hash_sel := by decide +kernel
  not_hash_norm := by decide +kernel

namespace Facts

set_option maxRecDepth 4096 in
-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- Every source predicate and field-form row is the hash's or of `aPreds`, decided (`Falcon512.Native.FalconHonestFull.src_cover`). -/
theorem src_cover : ∀ q < program.predicates.length,
    (program.inSource (program.predicate q) = true ∨ program.fieldRowRealB q = true) →
      q < 270 ∨ q ∈ aPreds program := by
  decide +kernel

set_option maxRecDepth 4096 in
-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- The committed source values' classes, decided (`Falcon512.Native.FalconHonestFull.cell_classes`). -/
theorem cell_classes : (List.range program.values.length).all (fun v =>
    !program.privCellB v || !decide (program.IsSourceValue v) ||
      (program.valueField v == 0 && (program.value v).node.map (·.name) == some "GF(2^16)" &&
        (v == 96 || (wordsOwner? v).isSome || v == 588 || v == 590)) ||
      (program.valueField v == 0 && (program.value v).node.map (·.name) == some "bit" &&
        [45, 46, 47, 591].contains v) ||
      (program.valueField v == 1 && (program.value v).node.map (·.name) == some "GF(p^1)" &&
        (NormValues program).contains v)) = true := by
  decide +kernel

end Facts

-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- The program's one statement bound: the key's entries `hhat` below `q`. -/
theorem bounds : program.declaredRanges = [(593, 12289)] := by decide +kernel

open Facts RealizedProgram in
set_option maxRecDepth 4096 in
-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- **The honest-strategy facts of the program of `Falcon512.Native.ROMParams`**: the operands of every
cross-field `equal`, the covering of the source predicates, the committed source cells' classes. -/
noncomputable instance : FalconHonestFull program
    (RealizedProgram.primeNodesOf Generated.Falcon512.Native.ROMParams.Plan.plan program) where
  bounds := bounds
  crossOperands := by decide +kernel
  src_cover := Facts.src_cover
  checks_list := by decide +kernel
  cell_classes := Facts.cell_classes

end GordieHowe.Falcon512.Native.ROMParams
