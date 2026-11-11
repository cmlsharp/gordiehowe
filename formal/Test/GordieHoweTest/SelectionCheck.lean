-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.SelectionCheck
public import GordieHoweCerts.Generated.Falcon512.Ring.Carrier.ROMParams.Program
public import GordieHoweCerts.Generated.Falcon512.Ring.Carrier.ROMParams.Selections
public import GordieHoweCerts.Generated.MLDSA44.Ring.Native.ROMParams.Program
public import GordieHoweCerts.Generated.MLDSA44.Ring.Native.ROMParams.Selections
-- The checks below evaluate the sealed programs.
import all GordieHoweCerts.Generated.Falcon512.Ring.Carrier.ROMParams.Program
import all GordieHoweCerts.Generated.MLDSA44.Ring.Native.ROMParams.Program

public section

/-!
# The table selections' check on exported programs

`selectionsB` (`GordieHowe/Language/Realizations/SelectionCheck.lean`): every certificate's gadget
facts hold (`selectB`).

* **The Falcon ring carrier**: its membership's selection certificate passes; the same gadget with
  its index-bit predicate pointed at the fingerprint predicate is refused.
* **The native ML-DSA-44 ring**: its selection certificate passes.
-/

namespace GordieHoweTest.SelectionCheck

open GordieHowe GordieHowe.RealizedProgram

/-! ## The Falcon ring carrier -/

/-- The Falcon ring carrier at the ROM parameters. -/
abbrev carrier := Generated.Falcon512.Ring.Carrier.ROMParams.Program.program

/-- Its exported selection certificate's gadget facts hold. -/
example : (Generated.Falcon512.Ring.Carrier.ROMParams.selections.map (·.table)).all
    (·.selectB carrier) = true := by decide +kernel
example : carrier.selectionsB Generated.Falcon512.Ring.Carrier.ROMParams.selections = true := by
  decide +kernel
/-- The index bits' predicate is the gadget's `idx * idx = idx`. -/
example : carrier.selectionsB (Generated.Falcon512.Ring.Carrier.ROMParams.selections.map
    fun c => { c with table := { c.table with idxPred := c.table.pred } }) = false := by
  decide +kernel

/-! ## The native ML-DSA-44 ring -/

/-- Its exported selection certificate's gadget facts hold. -/
example : Generated.MLDSA44.Ring.Native.ROMParams.Program.program.selectionsB
    Generated.MLDSA44.Ring.Native.ROMParams.selections = true := by
  decide +kernel

end GordieHoweTest.SelectionCheck
