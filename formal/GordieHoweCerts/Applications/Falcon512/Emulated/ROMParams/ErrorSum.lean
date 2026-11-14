-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Generated.Falcon512.Emulated.ROMParams.Data
public import GordieHowe.Applications.Program.FiguresCheck

import all GordieHoweCerts.Generated.Falcon512.Emulated.ROMParams.Program
import all GordieHoweCerts.Generated.Falcon512.Emulated.ROMParams.Plan

@[expose] public section

/-!
# The summed round errors and the domains of `Falcon512.Emulated.ROMParams`

The numeric summed round errors of the program (`FigCheck.errorSumN` at the numeric domain
figures) and the number of its domains, decided by the kernel in a module of its own, with the
program and the plan unfolded.
-/

namespace GordieHowe.Falcon512.Emulated.ROMParams

open GordieHowe RealizedProgram GordieHowe.Generated.Falcon512.Emulated.ROMParams

/-- **The numeric summed round errors are at most `131161305`**, in units of `2^-errorExp`. -/
theorem errorSumN_le :
    FigCheck.errorSumN data.program
      (@ProgramData.figuresDomains data (CellsReader.ofProgram data.program))
      data.fieldTable.interp.cardN data.figures.sourceErrors data.figures.figures.errorExp ≤
        131161305 := by
  decide +kernel

/-- **The program has `2` domains.** -/
theorem domains_length : Program.program.domains.length = 2 := by
  decide +kernel

end GordieHowe.Falcon512.Emulated.ROMParams
