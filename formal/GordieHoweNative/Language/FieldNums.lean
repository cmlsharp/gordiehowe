-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.ProgramData
public import GordieHoweNative.Language.Export.Valid

/-!
# GordieHowe: the registry's numbers of a field

The figures read three facts of each field of a program's interpretation
(`GordieHowe/Applications/FieldInterps/Registry.lean`): the bytes of an element (`FieldCodec.fb`),
the load and stream grant of its challenge reader (`CReader.load`, `CReader.grant`), and its
specification (`FieldInterp.spec`, whose size `Interp.specCard` is). Here they are numerals by key
(`FieldKey.fbN`, `loadN`, `grantN`, `specN`) and by field identifier of a descriptor
(`InterpDesc.fbN`, …); `InterpDesc.fb_eq`, `load_eq`, `grant_eq` and `specCard_eq` (Registry)
equate them with the registry's.
-/

public section

namespace GordieHowe

open RealizedProgram RealizedProgram.Export

/-- **The bytes of an element** of a key's field (`FieldKey.codec`'s `fb`; `0` for P-256, which has
no codec). -/
@[expose] def FieldKey.fbN : FieldKey → Nat
  | .gf128 => 16
  | .gf256 => 32
  | .fq6 => 18
  | .fq9 => 18
  | .fq11 => 32
  | .fq20 => 35
  | .gold2 => 16
  | .gold4 => 32
  | .p256 => 0

/-- **The load of a key's challenge reader**: its draws and bytes per draw (`CReader.load`). -/
@[expose] def FieldKey.loadN : FieldKey → Nat × Nat
  | .gf128 => (1, 16)
  | .gf256 => (1, 32)
  | .fq6 => (6, 3)
  | .fq9 => (9, 2)
  | .fq11 => (11, 3)
  | .fq20 => (20, 2)
  | .gold2 => (2, 8)
  | .gold4 => (4, 8)
  | .p256 => (0, 0)

/-- **The stream grant of a key's challenge reader** (`CReader.grant`): none. -/
@[expose] def FieldKey.grantN (_ : FieldKey) : Nat := 0

/-- **The specification of a key's field** (`FieldInterp.spec`). -/
@[expose] def FieldKey.specN : FieldKey → FieldSpec
  | .gf128 => gf2_128Entry.spec
  | .gf256 => gf2_256Entry.spec
  | .fq6 => mldsaNative6Entry.spec
  | .fq9 => falconNative9Entry.spec
  | .fq11 => mldsaNative11Entry.spec
  | .fq20 => falconNative20Entry.spec
  | .gold2 => goldilocksExt2Entry.spec
  | .gold4 => goldilocksExt4Entry.spec
  | .p256 => p256Entry.spec

/-- **The size of a key's field**: `characteristic ^ degree` (`Interp.specCard`). -/
@[expose] def FieldKey.cardN (k : FieldKey) : Nat := k.specN.characteristic ^ k.specN.degree

namespace InterpDesc

variable (D : InterpDesc) (f : Nat)

/-- The bytes of an element of field `f`. -/
@[expose] def fbN : Nat := (D.key f).fbN

/-- The load of field `f`'s challenge reader. -/
@[expose] def loadN : Nat × Nat := (D.key f).loadN

/-- The stream grant of field `f`'s challenge reader. -/
@[expose] def grantN : Nat := (D.key f).grantN

/-- The size of field `f`. -/
@[expose] def cardN : Nat := (D.key f).cardN

end InterpDesc

end GordieHowe
