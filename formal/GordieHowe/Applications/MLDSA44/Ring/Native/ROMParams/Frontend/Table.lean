-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.SelectionCheck
public import GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.Program
public import GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.Core
public import GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts
public import GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.Certified
public import GordieHowe.Applications.MLDSA44.Ring.Table

@[expose] public section

/-!
# The public table's selection of `MLDSA44.Ring.Native.ROMParams`

The selection `member.select` of the ring's public table (`GordieHowe.RealizedProgram.TableSelect`,
`lib/gordiehowe/lib/table.h`'s `select_row`) in
`GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.Program.program`, from the program check's certificate (`selectionsB`): the record
(shared expression `1`, `member.a_hat ‖ member.t1 ‖` the `24` limbs of `μ`), the map
`GordieHowe.MLDSA44.Ring.nativeMap`, the column blocks `ring.keys` (value `53`) and `ring.mu` (value `54`),
`64` rows, `6` index bits (`member.select.index`, value `58`), the challenge
`member.table.gamma` (value `59`, challenge `0`), the powers and the digests (values `527`, `528`).
-/

namespace GordieHowe.MLDSA44.Ring.Native.ROMParams

open Generated.MLDSA44.Ring.Native.ROMParams.Program RealizedProgram
open Generated.MLDSA44.Ring.Native.ROMParams.ShapeFacts

/-- **The table's selection**, from the program check's certificate
(`GordieHowe.RealizedProgram.TableSelect.ofSelections` at `Generated.MLDSA44.Ring.Native.ROMParams.selections`). -/
instance : TableSelect program :=
  TableSelect.ofSelections (ir := program) (cs := Generated.MLDSA44.Ring.Native.ROMParams.selections)
    Generated.MLDSA44.Ring.Native.ROMParams.core.wellFormed
    Generated.MLDSA44.Ring.Native.ROMParams.checked.selections ⟨0, by decide⟩

end GordieHowe.MLDSA44.Ring.Native.ROMParams
