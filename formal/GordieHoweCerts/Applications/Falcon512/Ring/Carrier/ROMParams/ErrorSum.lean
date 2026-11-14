-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Generated.Falcon512.Ring.Carrier.ROMParams.Data
public import GordieHowe.Applications.Program.FiguresCheck

import all GordieHoweCerts.Generated.Falcon512.Ring.Carrier.ROMParams.Program
import all GordieHoweCerts.Generated.Falcon512.Ring.Carrier.ROMParams.Plan

@[expose] public section

/-!
# The summed round errors and the domains of `Falcon512.Ring.Carrier.ROMParams`

The numeric summed round errors of the program (`FigCheck.errorSumN` at the numeric domain
figures) and the number of its domains, decided by the kernel in a module of its own, with the
program and the plan unfolded.
-/

namespace GordieHowe.Falcon512.Ring.Carrier.ROMParams

open GordieHowe RealizedProgram GordieHowe.Generated.Falcon512.Ring.Carrier.ROMParams

/-- **The numeric summed round errors are at most `84845906`**, in units of `2^-errorExp`. -/
theorem errorSumN_le :
    FigCheck.errorSumN data.program
      (@ProgramData.figuresDomains data (CellsReader.ofProgram data.program))
      data.fieldTable.interp.cardN data.figures.sourceErrors data.figures.figures.errorExp ≤
        84845906 := by
  decide +kernel

/-- **The program has `1` domain.** -/
theorem domains_length : Program.program.domains.length = 1 := by
  decide +kernel

end GordieHowe.Falcon512.Ring.Carrier.ROMParams
