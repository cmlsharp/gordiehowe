-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Native.Frontend.Relation
public import GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.Program

@[expose] public section

/-!
# GordieHowe frontend: the signature relation of `MLDSA44.Ring.Native.ROMParams`

The program facts of the signature relation (`GordieHowe.MLDSA44.Ring.Native.MldsaRingRelation`)
at the native ML-DSA-44 ring program at the ROM parameters
(`GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.Program.program`, fields `F_q^6` and `GF(2^128)`), decided
here: `member.a_hat` is value `55`, `member.t1` value `56`, `z` value `60`, `challenge.c` value `62`,
`signature.w` value `63`, `norm.z.offset` value `64`; `challenge.c.boolean` is predicate `13` and
`norm.z` predicate `17`. So `GordieHowe.MLDSA44.Ring.Native.algebra_eq` holds at this program.
-/

namespace GordieHowe.MLDSA44.Ring.Native.ROMParams

open Generated.MLDSA44.Ring.Native.ROMParams.Program (program)

set_option maxRecDepth 8192 in
/-- The native ML-DSA-44 ring program at the ROM parameters has the signature relation's facts. -/
instance : MldsaRingRelation program where
  aHat := 55
  t1 := 56
  z := 60
  c := 62
  w := 63
  zOff := 64
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

end GordieHowe.MLDSA44.Ring.Native.ROMParams
