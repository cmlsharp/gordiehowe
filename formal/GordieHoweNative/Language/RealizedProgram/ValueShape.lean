-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Check

public section

namespace GordieHowe.RealizedProgram

/-- The finite metadata of one value, excluding its expression, kind and certificate data. -/
structure ValueShape where
  /-- The commitment domain. -/
  domain : Nat
  /-- The resolved value field. -/
  field : Nat
  /-- The number of entries. -/
  size : Nat
  /-- The commitment phase. -/
  phase : Nat
  /-- The packing node, when present. -/
  node : Option NodeRef
  /-- Where the value's type is enforced. -/
  typeSource : TypeSource
  /-- Source value or generated realization. -/
  role : ValueRole
  deriving Repr, Inhabited

/-- Equality of the finite metadata is executable and kernel-reducible. -/
@[expose] instance : DecidableEq ValueShape
  | ⟨d, f, n, p, node, src, role⟩, ⟨d', f', n', p', node', src', role'⟩ =>
    if h : d = d' ∧ f = f' ∧ n = n' ∧ p = p' ∧ node = node' ∧ src = src' ∧ role = role' then
      isTrue (by rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩; rfl)
    else
      isFalse (fun e => h (ValueShape.mk.inj e))

/-- Read only the finite metadata from a value and its resolved field. -/
@[expose] def Value.shapeHeader (v : Value) (field : Nat) : ValueShape :=
  ⟨v.domain, field, v.size, v.phase, v.node, v.typeSource, v.role⟩

/-- The logical finite metadata of a program value. -/
@[expose] def valueShape (ir : RealizedProgram) (v : Nat) : ValueShape :=
  (ir.value v).shapeHeader (ir.valueField v)

/-- The same finite metadata through the compiled program tables. -/
@[expose] def valueShapeT (ir : RealizedProgram) (v : Nat) : ValueShape :=
  (ir.valueT v).shapeHeader (ir.valueFieldT v)

end GordieHowe.RealizedProgram
