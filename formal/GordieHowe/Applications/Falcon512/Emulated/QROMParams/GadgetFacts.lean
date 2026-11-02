-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Generated.Falcon512.Emulated.QROMParams.Realize
public import GordieHowe.Applications.Falcon512.Emulated.HonestFull
public import GordieHowe.Applications.Falcon512.Emulated.QROMParams.Frontend.HashFacts
public import GordieHowe.Applications.Falcon512.Emulated.QROMParams.Frontend.AlgebraFacts

@[expose] public section

/-!
# GordieHowe: the gadget facts of `Falcon512.Emulated.QROMParams`

The program's instances of the honest strategy's classes on the tables of
`GordieHowe.Generated.Falcon512.Emulated.QROMParams.Program.program`: the hash's, the selection's and domain `A`'s facts, the operands
of every cross-field `equal`, the covering of the source predicates and the committed source cells'
classes (`FalconEHonestFull`). These read the program's gadgets by index; the program-wide facts
the honest strategy reads are its honest roles (`Completion.rolesOk`).
-/

namespace GordieHowe.Falcon512.Emulated.QROMParams

open Generated.Falcon512.Emulated.QROMParams.Program (program)
open RealizedProgram

-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- The honest hash facts of the program of `Falcon512.Emulated.QROMParams`. -/
instance : FalconHHonest program where
  words_checks := by decide +kernel
  state_checks := by decide +kernel
  buf_checks := by decide +kernel

-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- The selection values of the program of `Falcon512.Emulated.QROMParams`. -/
instance : FalconHSelHonest program where
  sel_checks := by decide +kernel

-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- `magnitudes.mag1` is bound to its two base-`128` digits. -/
theorem mag1Kind :
    (program.value 598).kind = .bound (.add (.leaf 612) (.scale (.const 128) (.leaf 613))) :=
  Kind.eq_bound_of_isBoundTo (by decide +kernel)

-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- `norm.squares` is bound to its three base-`2048` digits. -/
theorem sqKind : (program.value 602).kind = .bound (.add (.add (.leaf 622)
    (.scale (.const 2048) (.leaf 623))) (.scale (.const 4194304) (.leaf 624))) :=
  Kind.eq_bound_of_isBoundTo (by decide +kernel)

-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- The facts of honest domain `A` of the program of `Falcon512.Emulated.QROMParams`. -/
instance : FalconEHonest program where
  mag1Kind := mag1Kind
  sqKind := sqKind
  bound := Generated.Falcon512.Emulated.QROMParams.Realize.derivable.elim fun _ hD => hD.bound
  a_cells := by decide +kernel
  digitSizes := by decide +kernel
  lens := by decide +kernel
  sigForm := ⟨_, rfl, rfl⟩
  high2Form := ⟨_, rfl, rfl⟩
  caBody := ⟨_, rfl⟩
  macBody := ⟨_, _, rfl, by decide⟩
  rawField := by decide +kernel

/-! ## The honest strategy's program facts -/

namespace Facts

-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- Every source predicate is the hash's or of `aPreds`, decided
(`Falcon512.Emulated.FalconEHonestFull.src_cover`). -/
theorem src_cover : ∀ q < program.predicates.length,
    program.inSource (program.predicate q) = true → q < 270 ∨ q ∈ aPreds := by
  decide +kernel

-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- The committed source values' classes, decided
(`Falcon512.Emulated.FalconEHonestFull.cell_classes`). -/
theorem cell_classes : (List.range program.values.length).all (fun v =>
    !program.privCellB v || !decide (program.IsSourceValue v) ||
      (program.valueField v == 0 && (program.value v).node.map (·.name) == some "GF(2^16)" &&
        (v == 96 || (wordsOwner? v).isSome || v == 588 || v == 590)) ||
      (program.valueField v == 0 && (program.value v).node.map (·.name) == some "bit" &&
        [45, 46, 47, 591].contains v) ||
      (program.valueField v == 1 && (program.value v).node.map (·.name) == some "GF(p^1)" &&
        aValues.contains v)) = true := by
  decide +kernel

end Facts

-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- The program's statement bounds: `hhat` and the key's coefficients below `q`. -/
theorem bounds : program.declaredRanges = [(593, 12289), (594, 12289)] := by decide +kernel

-- TODO(gadget-roles): gadget wiring by index; moves to recorded roles with item 14.
/-- **The honest-strategy facts of the program of `Falcon512.Emulated.QROMParams`**: the operands of
every cross-field `equal`, the covering of the source predicates, the committed source cells'
classes. -/
noncomputable instance : FalconEHonestFull program
    (RealizedProgram.primeNodesOf Generated.Falcon512.Emulated.QROMParams.Plan.plan program) where
  bounds := bounds
  crossOperands := by decide +kernel
  src_cover := Facts.src_cover
  checks_list := by decide +kernel
  cell_classes := Facts.cell_classes

end GordieHowe.Falcon512.Emulated.QROMParams
