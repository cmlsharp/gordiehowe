-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Export

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Export.Valid`

The field registry (`fieldRegistry`, the fields the Lean has, with their subfields), a domain's
registry entry and node degrees, and the nodes of a domain's tree, in the Mathlib-free library
`GordieHoweNative`. The declarations keep their names; their lemmas and the plan conditions are in
`GordieHowe/Language/Export/Valid.lean`, which imports this module.
-/

@[expose] public section

namespace GordieHowe.RealizedProgram.Export

/-! ## The field registry -/

/-- **A subfield the Lean has**, as the plan writes it: its specification and the bytes of one of
its elements in the C++ encoding (`kBytes` of its class; `0`: the C++ writes no element of this
subfield on its own). -/
structure SubfieldEntry where
  /-- The specification. -/
  spec : FieldSpec
  /-- The bytes of an element. -/
  bytes : Nat
  deriving Repr, DecidableEq

/-- **A field the Lean has**: its specification as the plan writes it, the bytes of an element in
the C++ encoding (`F::kBytes`), the size `q` of the evaluation-point domain on which the Lean's
points are injective (`Ligero.Relative.Shape.Valid`), and the subfields the Lean has in it. -/
structure FieldEntry where
  /-- The specification. -/
  spec : FieldSpec
  /-- The bytes of an element. -/
  bytes : Nat
  /-- The size of the evaluation-point domain. -/
  points : Nat
  /-- The subfields. -/
  subfields : List SubfieldEntry
  deriving Repr, DecidableEq

/-- The prime subfield `GF(2)` of a binary field, as the node `bit` (`⊥`, the image of `ZMod 2`). -/
def bitSubfield : SubfieldEntry := ⟨{ name := "bit", characteristic := 2, degree := 1 }, 0⟩

/-- The prime subfield `F_p` of an odd-characteristic field (`⊥`, the image of `ZMod p` under
`algebraMap`), whose elements the C++ writes in `bytes` bytes. -/
def primeSubfield (p bytes : Nat) : SubfieldEntry :=
  ⟨{ name := "GF(p^1)", characteristic := p, degree := 1 }, bytes⟩

/-- **`GF(2^16)` in `GF(2^128)`**: the Lean `gf2_128Subfield` (`GordieHowe/Foundations/Fields/GF2_128Selection.lean`,
the fixed field of the `2^16`-power Frobenius), with the modulus the C++ exports (the minimal
polynomial of its subfield generator), which the Lean does not state. -/
def gf2_16In128 : FieldSpec :=
  { name := "GF(2^16)", characteristic := 2, degree := 16,
    modulus := [16, 15, 13, 12, 11, 9, 8, 7, 5, 4, 0] }

/-- **`GF(2^16)` in `GF(2^256)`**: the Lean `gf2_256Subfield` (`GordieHowe/Foundations/Fields/GF2_256Selection.lean`),
with the modulus the C++ exports, which the Lean does not state. -/
def gf2_16In256 : FieldSpec :=
  { name := "GF(2^16)", characteristic := 2, degree := 16,
    modulus := [16, 14, 13, 12, 9, 8, 5, 3, 0] }

/-- **`GF(2^128)`**: the Lean `GF2_128` (`GordieHowe/Foundations/Fields/GF2_128.lean`), `GF(2)[X]/(X^128 + X^7 + X^2 +
X + 1)`, `16` bytes, points `2^16`; subfields `bit` and `GF(2^16)`, the Lean `gf2_128Subfield`
(`GordieHowe/Foundations/Fields/GF2_128Selection.lean`, the fixed field of the `2^16`-power Frobenius). The subfield's
modulus is the one the C++ exports (the minimal polynomial of its subfield generator); the Lean
does not state it. -/
def gf2_128Entry : FieldEntry where
  spec := { name := "GF(2^128)", characteristic := 2, degree := 128,
            modulus := [128, 7, 2, 1, 0] }
  bytes := 16
  points := 2 ^ 16
  subfields := [bitSubfield, ⟨gf2_16In128, 0⟩]

/-- **`GF(2^256)`**: the Lean `GF2_256` (`GordieHowe/Foundations/Fields/GF2_256.lean`), `GF(2)[X]/(X^256 + X^10 + X^5 +
X^2 + 1)`, `32` bytes, points `2^16`; subfields `bit` and `GF(2^16)`, the Lean `gf2_256Subfield`
(`GordieHowe/Foundations/Fields/GF2_256Selection.lean`), its modulus as the C++ exports it. -/
def gf2_256Entry : FieldEntry where
  spec := { name := "GF(2^256)", characteristic := 2, degree := 256,
            modulus := [256, 10, 5, 2, 0] }
  bytes := 32
  points := 2 ^ 16
  subfields := [bitSubfield, ⟨gf2_16In256, 0⟩]

/-- **`F_q^9`**, `q = 12289`: the Lean `FalconNativeField9` (`GordieHowe/Applications/Falcon512/Fields/FalconNative9.lean`),
`ZMod 12289 [X]/(X^9 - 2)` (the plan writes the coefficients `1, q - 2`), `18` bytes (`Fp14_N`,
`9 · 2`), points `q`; subfield `GF(p^1)`, `2` bytes. -/
def falconNative9Entry : FieldEntry where
  spec := { name := "F_q^9", characteristic := 12289, degree := 9, modulus := [9, 0],
            modulusCoeffs := [1, 12287] }
  bytes := 18
  points := 12289
  subfields := [primeSubfield 12289 2]

/-- **`F_q^20`**, `q = 12289`: the Lean `FalconNativeField20` (`GordieHowe/Applications/Falcon512/Fields/FalconNative20.lean`), the
tower `u^4 = 11`, `v^5 = u + 2`, `35` bytes (`NativeWide`, `⌈20 · 14 / 8⌉`), points `q`; subfield
`GF(p^1)`, `2` bytes. -/
def falconNative20Entry : FieldEntry where
  spec := { name := "F_q^20", characteristic := 12289, degree := 20,
            tower := [{ name := "u", degree := 4, relation := [(11, [0])] },
              { name := "v", degree := 5, relation := [(1, [1, 0]), (2, [0, 0])] }] }
  bytes := 35
  points := 12289
  subfields := [primeSubfield 12289 2]

/-- **`F_q^6`**, `q = 8380417`: the Lean `MLDSANativeField6` (`GordieHowe/Applications/MLDSA44/Fields/MLDSANative6.lean`),
`ZMod q [X]/(X^6 - 7)`, `18` bytes (`Fp24_6`, `6 · 3`), points `q`; subfield `GF(p^1)`, `3`
bytes. -/
def mldsaNative6Entry : FieldEntry where
  spec := { name := "F_q^6", characteristic := 8380417, degree := 6, modulus := [6, 0],
            modulusCoeffs := [1, 8380410] }
  bytes := 18
  points := 8380417
  subfields := [primeSubfield 8380417 3]

/-- **`F_q^11`**, `q = 8380417`: the Lean `MLDSANativeField11` (`GordieHowe/Applications/MLDSA44/Fields/MLDSANative11.lean`),
`ZMod q [X]/(X^11 - 2)`, `32` bytes (`NativeWide`, `⌈11 · 23 / 8⌉`), points `q`; subfield
`GF(p^1)`, `3` bytes. -/
def mldsaNative11Entry : FieldEntry where
  spec := { name := "F_q^11", characteristic := 8380417, degree := 11, modulus := [11, 0],
            modulusCoeffs := [1, 8380415] }
  bytes := 32
  points := 8380417
  subfields := [primeSubfield 8380417 3]

/-- **Goldilocks²**: the Lean `GoldilocksExt2` (`GordieHowe/Foundations/Fields/Goldilocks.lean`), `ZMod p [X]/(X^2 - 7)`,
`16` bytes, points `2^32` (the Goldilocks subgroup encoder); subfield `GF(p^1)`, `8` bytes. -/
def goldilocksExt2Entry : FieldEntry where
  spec := { name := "Goldilocks^2", characteristic := 18446744069414584321, degree := 2,
            modulus := [2, 0], modulusCoeffs := [1, 18446744069414584314] }
  bytes := 16
  points := 2 ^ 32
  subfields := [primeSubfield 18446744069414584321 8]

/-- **Goldilocks⁴**: the Lean `GoldilocksExt4` (`GordieHowe/Foundations/Fields/GoldilocksQuartic.lean`),
`ZMod p [X]/(X^4 - 7)`, `32` bytes, points `2^32`; subfield `GF(p^1)`, `8` bytes. -/
def goldilocksExt4Entry : FieldEntry where
  spec := { name := "Goldilocks^4", characteristic := 18446744069414584321, degree := 4,
            modulus := [4, 0], modulusCoeffs := [1, 18446744069414584314] }
  bytes := 32
  points := 2 ^ 32
  subfields := [primeSubfield 18446744069414584321 8]

/-- **The P-256 base field** `ZMod p256`: `32` bytes, points `p256`; no subfield. -/
def p256Entry : FieldEntry where
  spec := { name := "F_p256",
            characteristic :=
              115792089210356248762697446949407573530086143415290314195533631308867097853951,
            degree := 1 }
  bytes := 32
  points := 115792089210356248762697446949407573530086143415290314195533631308867097853951
  subfields := []

/-- **The prime field `Fp128`** `ZMod p`, `p = 2^128 − 2^108 + 1` (the C++ `Fp128`, RSA's prime
field): `16` bytes, points `2^108` (the subgroup encoder on its roots of unity,
`p − 1 = 2^108 (2^20 − 1)`; `lib/gordiehowe/instances.h`, `RsFp128`); no subfield. -/
def fp128Entry : FieldEntry where
  spec := { name := "Fp128", characteristic := 340282042402384805036647824275747635201,
            degree := 1 }
  bytes := 16
  points := 2 ^ 108
  subfields := []

/-- **The field registry**: the fields the Lean has, each with the Lean type named in its entry's
docstring. -/
def fieldRegistry : List FieldEntry :=
  [gf2_128Entry, gf2_256Entry, falconNative9Entry, falconNative20Entry, mldsaNative6Entry,
    mldsaNative11Entry, goldilocksExt2Entry, goldilocksExt4Entry, p256Entry, fp128Entry]

/-- The registry entry of a domain's field: the first entry whose specification is the field's. -/
def Domain.entry? (d : Domain) : Option FieldEntry := fieldRegistry.find? (·.spec = d.field)

/-- **The degree of a node of a domain's tree** by name: the field's, or a declared subfield's. -/
def Domain.nodeDegree (d : Domain) (name : String) : Option Nat :=
  if name = d.field.name then some d.field.degree
  else (d.subfields.find? (·.name = name)).map (·.degree)

/-- **The nodes of a domain's tree**: the field and every edge's child and parent. -/
def Domain.treeNodes (d : Domain) : List String :=
  d.field.name :: d.packing.flatMap fun e => [e.child, e.parent]

end GordieHowe.RealizedProgram.Export
