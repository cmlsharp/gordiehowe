-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.SelectionCheck
public import GordieHoweCerts.Generated.MLDSA44.Ring.Carrier.QROMParams.Program
public import GordieHoweCerts.Generated.MLDSA44.Ring.Carrier.QROMParams.Core
public import GordieHoweCerts.Generated.MLDSA44.Ring.Carrier.QROMParams.ShapeFacts
public import GordieHoweCerts.Generated.MLDSA44.Ring.Carrier.QROMParams.Certified
public import GordieHowe.Applications.MLDSA44.Ring.Table

@[expose] public section

/-!
# The public table's selection of `MLDSA44.Ring.Carrier.QROMParams`

The selection `member.select` of the ring's public table (`GordieHowe.RealizedProgram.TableSelect`,
`lib/gordiehowe/lib/table.h`'s `select_row`) in
`GordieHowe.Generated.MLDSA44.Ring.Carrier.QROMParams.Program.program`, from the program check's certificate (`selectionsB`): the record
(shared expression `1`, `member.a_hat ‖ member.t1 ‖` the `24` limbs of `μ`), the map
`GordieHowe.MLDSA44.Ring.carrierMap`, the column blocks `ring.keys` (value `53`) and `ring.mu` (value `54`),
`64` rows, `6` index bits (`member.select.index`, value `58`), the challenge
`member.table.gamma` (value `59`, challenge `0`), the powers and the digests (values `528`, `529`).
-/

namespace GordieHowe.MLDSA44.Ring.Carrier.QROMParams

open Generated.MLDSA44.Ring.Carrier.QROMParams.Program RealizedProgram

/-- **The table's selection**, from the program check's certificate
(`GordieHowe.RealizedProgram.TableSelect.ofSelections` at `Generated.MLDSA44.Ring.Carrier.QROMParams.selections`). -/
instance : TableSelect program :=
  TableSelect.ofSelections (ir := program) (cs := Generated.MLDSA44.Ring.Carrier.QROMParams.selections)
    Generated.MLDSA44.Ring.Carrier.QROMParams.core.wellFormed
    Generated.MLDSA44.Ring.Carrier.QROMParams.checked.selections ⟨0, by decide⟩

end GordieHowe.MLDSA44.Ring.Carrier.QROMParams
