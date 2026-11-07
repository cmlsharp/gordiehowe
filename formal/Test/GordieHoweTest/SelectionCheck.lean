-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.SelectionCheck
public import GordieHoweCerts.Generated.Falcon512.Ring.Carrier.ROMParams.Program
public import GordieHoweCerts.Generated.MLDSA44.Ring.Native.ROMParams.Program
-- The checks below evaluate the sealed programs.
import all GordieHoweCerts.Generated.Falcon512.Ring.Carrier.ROMParams.Program
import all GordieHoweCerts.Generated.MLDSA44.Ring.Native.ROMParams.Program

public section

/-!
# The table selections' check on exported programs

`selectionsB` (`GordieHowe/Language/Realizations/SelectionCheck.lean`) at the Falcon ring carrier
at the ROM parameters, whose signature equation is a product form reading a table selection, and
at the native ML-DSA-44 ring at the ROM parameters, which has none. The carrier passes with its
certificate and fails without one, with the wrong predicate, the wrong record, the wrong transform
root, the wrong transform order, or a degree above the exported one.
-/

namespace GordieHoweTest.SelectionCheck

open GordieHowe GordieHowe.RealizedProgram

/-- **The Falcon ring carrier's selection** (`member.signer`): the record `key.spectrum` (value
`6`), the rows `statement.ring` (value `4`), the natural-order transform of length `512`. -/
@[expose] def falconCarrier : TableShape where
  dom := 0
  one := 0
  zero := 1
  mOne := 18446744069414584320
  gamma := 8
  chal := 0
  pow := 17
  dig := 18
  idx := 7
  pred := 0
  idxPred := 9
  record := .leaf 6
  map := [⟨true, true, 512, 0, 11353340290879379826⟩]
  parts := [(4, 512)]
  rows := 64
  bits := 6

/-- The Falcon ring carrier at the ROM parameters. -/
abbrev carrier := Generated.Falcon512.Ring.Carrier.ROMParams.Program.program

example : carrier.selectionsB [⟨0, falconCarrier⟩] = true := by decide +kernel
example : falconCarrier.selectB carrier = true := by decide +kernel

/-- A product form needs a certificate. -/
example : carrier.selectionsB [] = false := by decide +kernel
/-- The certificate names the selection's predicate. -/
example : carrier.selectionsB [⟨1, falconCarrier⟩] = false := by decide +kernel
/-- The record is the kernel's value. -/
example : carrier.selectionsB [⟨0, { falconCarrier with record := .leaf 5 }⟩] = false := by
  decide +kernel
/-- The transform's root is the kernel's. -/
example : carrier.selLinkB 0 ⟨0, [6], 4, 64, 512, 512, 11353340290879379826, true, 0, 511⟩
    { falconCarrier with map := [⟨true, true, 512, 0, 7⟩] } = false := by decide +kernel
/-- The transform's order is the kernel's. -/
example : carrier.selLinkB 0 ⟨0, [6], 4, 64, 512, 512, 11353340290879379826, true, 0, 511⟩
    { falconCarrier with map := [⟨true, false, 512, 0, 11353340290879379826⟩] } = false := by
  decide +kernel
/-- The gadget's degree is within the exported one. -/
example : carrier.selLinkB 0 ⟨0, [6], 4, 64, 512, 512, 11353340290879379826, true, 0, 510⟩
    falconCarrier = false := by decide +kernel
/-- The link at the kernel's own shape. -/
example : carrier.selLinkB 0 ⟨0, [6], 4, 64, 512, 512, 11353340290879379826, true, 0, 511⟩
    falconCarrier = true := by decide +kernel

/-- A program without a product form passes with no certificate. -/
example : Generated.MLDSA44.Ring.Native.ROMParams.Program.program.selectionsB [] = true := by
  decide +kernel

end GordieHoweTest.SelectionCheck
