-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.Program
public import GordieHowe.Applications.MLDSA44.Ring.Table

@[expose] public section

/-!
# The public table's selection of `MLDSA44.Ring.Native.QROMParams`

The selection `member.select` of the ring's public table (`GordieHowe.RealizedProgram.TableSelect`,
`lib/gordiehowe/lib/table.h`'s `select_row`) in
`GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.Program.program`, decided on its tables: the record
(shared expression `1`, `member.a_hat ‖ member.t1 ‖` the `24` limbs of `μ`), the map
`GordieHowe.MLDSA44.Ring.nativeMap`, the column blocks `ring.keys` (value `52`) and `ring.mu` (value `53`),
`64` rows, `6` index bits (`member.select.index`, value `57`), the challenge
`member.table.gamma` (value `58`, challenge `0`), the powers and the digests (values `526`, `527`).
-/

namespace GordieHowe.MLDSA44.Ring.Native.QROMParams

open Generated.MLDSA44.Ring.Native.QROMParams.Program RealizedProgram

/-- **The table's selection**: identifiers and row map. -/
def tableShape : TableShape where
  dom := 0
  one := 1
  zero := 0
  mOne := 8380416
  gamma := 58
  chal := 0
  pow := 526
  dig := 527
  idx := 57
  pred := 0
  idxPred := 11
  record := .ref 1
  map := nativeMap
  parts := [(52, 5120), (53, 24)]
  rows := 64
  bits := 6

set_option maxRecDepth 100000 in
/-- **The table's selection** of the program, decided on its tables. -/
instance : TableSelect program where
  shape := tableShape
  refsOrdered := (refsOrderedB_iff program).1 (by decide +kernel)
  exprs_pos := by decide +kernel
  values_pos := by decide +kernel
  mapWf := by decide +kernel
  width := by decide +kernel
  powOk := by decide +kernel
  digOk := by decide +kernel
  bodyOk := by decide +kernel
  powKind := rfl
  digKind := rfl
  idxBool := ⟨_, rfl⟩
  inSource := by decide +kernel
  consts := by decide +kernel
  gammaKind := rfl
  chalOk := by decide +kernel
  fields := by decide +kernel
  sizes := by decide +kernel
  idxPriv := rfl
  recordReads := by decide +kernel
  rowReads := by decide +kernel

end GordieHowe.MLDSA44.Ring.Native.QROMParams
