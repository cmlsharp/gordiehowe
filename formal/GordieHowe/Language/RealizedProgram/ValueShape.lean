-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Check
public import GordieHoweNative.Language.RealizedProgram.ValueShape

public section

namespace GordieHowe.RealizedProgram

variable {ir : RealizedProgram} {v : Nat} {s : ValueShape}

/-- The compiled metadata reader agrees with the logical reader. -/
theorem valueShapeT_eq : ir.valueShapeT v = ir.valueShape v := by
  simp only [valueShapeT, valueT_eq, valueFieldT_eq, valueShape]

/-- A metadata equality determines the commitment domain. -/
theorem valueShape_domain (h : ir.valueShape v = s) : (ir.value v).domain = s.domain :=
  congrArg ValueShape.domain h

/-- A metadata equality determines the resolved field. -/
theorem valueShape_field (h : ir.valueShape v = s) : ir.valueField v = s.field :=
  congrArg ValueShape.field h

/-- A metadata equality determines the number of entries. -/
theorem valueShape_size (h : ir.valueShape v = s) : (ir.value v).size = s.size :=
  congrArg ValueShape.size h

/-- A metadata equality determines the commitment phase. -/
theorem valueShape_phase (h : ir.valueShape v = s) : (ir.value v).phase = s.phase :=
  congrArg ValueShape.phase h

/-- A metadata equality determines the packing node. -/
theorem valueShape_node (h : ir.valueShape v = s) : (ir.value v).node = s.node :=
  congrArg ValueShape.node h

/-- A metadata equality determines the source of type enforcement. -/
theorem valueShape_typeSource (h : ir.valueShape v = s) :
    (ir.value v).typeSource = s.typeSource :=
  congrArg ValueShape.typeSource h

/-- A metadata equality determines source or realization ownership. -/
theorem valueShape_role (h : ir.valueShape v = s) : (ir.value v).role = s.role :=
  congrArg ValueShape.role h

end GordieHowe.RealizedProgram
