-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Native.Frontend.Relation
public import GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.Program

@[expose] public section

/-!
# GordieHowe frontend: the signature relation of `MLDSA44.Ring.Native.QROMParams`

The program facts of the signature relation (`GordieHowe.MLDSA44.Ring.Native.MldsaRingRelation`)
at the native ML-DSA-44 ring program at the QROM parameters
(`GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.Program.program`, fields `F_q^11` and `GF(2^256)`), decided
here: `member.a_hat` is value `54`, `member.t1` value `55`, `z` value `59`, `challenge.c` value `61`,
`signature.w` value `62`, `norm.z.offset` value `63`; `challenge.c.boolean` is predicate `13` and
`norm.z` predicate `17`. So `GordieHowe.MLDSA44.Ring.Native.algebra_eq` holds at this program.
-/

namespace GordieHowe.MLDSA44.Ring.Native.QROMParams

open Generated.MLDSA44.Ring.Native.QROMParams.Program (program)

set_option maxRecDepth 8192 in
/-- The native ML-DSA-44 ring program at the QROM parameters has the signature relation's facts. -/
instance : MldsaRingRelation program where
  aHat := 54
  t1 := 55
  z := 59
  c := 61
  w := 62
  zOff := 63
  cPred := 13
  normPred := 17
  domainField0 := by decide +kernel
  refsOrdered := (RealizedProgram.refsOrderedB_iff program).1 (by decide +kernel)
  refsLt := by decide +kernel
  rows := fun i => by fin_cases i <;> exact ⟨_, rfl⟩
  rowLen := by decide +kernel
  exprW := fun i => by fin_cases i <;> rfl
  exprA := fun i => by fin_cases i <;> rfl
  exprT := fun i => by fin_cases i <;> rfl
  exprZ := rfl
  exprS := rfl
  exprG := rfl
  const2 := by decide +kernel
  inSource := by decide +kernel
  cBool := by decide +kernel
  norm := ⟨_, rfl⟩
  offConst := by decide +kernel
  primeVals := by decide +kernel
  sizes := by decide +kernel

end GordieHowe.MLDSA44.Ring.Native.QROMParams
