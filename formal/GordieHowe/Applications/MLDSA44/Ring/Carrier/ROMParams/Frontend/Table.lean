-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.SelectionCheck
public import GordieHowe.Generated.MLDSA44.Ring.Carrier.ROMParams.Program
public import GordieHowe.Generated.MLDSA44.Ring.Carrier.ROMParams.Core
public import GordieHowe.Generated.MLDSA44.Ring.Carrier.ROMParams.ShapeFacts
public import GordieHowe.Generated.MLDSA44.Ring.Carrier.ROMParams.Certified
public import GordieHowe.Applications.MLDSA44.Ring.Table

@[expose] public section

/-!
# The public table's selection of `MLDSA44.Ring.Carrier.ROMParams`

The selection `member.select` of the ring's public table (`GordieHowe.RealizedProgram.TableSelect`,
`lib/gordiehowe/lib/table.h`'s `select_row`) in
`GordieHowe.Generated.MLDSA44.Ring.Carrier.ROMParams.Program.program`, from the program check's certificate (`selectionsB`): the record
(shared expression `1`, `member.a_hat ‖ member.t1 ‖` the `24` limbs of `μ`), the map
`GordieHowe.MLDSA44.Ring.carrierMap`, the column blocks `ring.keys` (value `53`) and `ring.mu` (value `54`),
`64` rows, `6` index bits (`member.select.index`, value `58`), the challenge
`member.table.gamma` (value `59`, challenge `0`), the powers and the digests (values `528`, `529`).
-/

namespace GordieHowe.MLDSA44.Ring.Carrier.ROMParams

open Generated.MLDSA44.Ring.Carrier.ROMParams.Program RealizedProgram

/-- **The table's selection**, from the program check's certificate
(`GordieHowe.RealizedProgram.TableSelect.ofSelections` at `Generated.MLDSA44.Ring.Carrier.ROMParams.selections`). -/
instance : TableSelect program :=
  TableSelect.ofSelections (ir := program) (cs := Generated.MLDSA44.Ring.Carrier.ROMParams.selections)
    Generated.MLDSA44.Ring.Carrier.ROMParams.core.wellFormed
    Generated.MLDSA44.Ring.Carrier.ROMParams.checked.selections ⟨0, by decide⟩

end GordieHowe.MLDSA44.Ring.Carrier.ROMParams
