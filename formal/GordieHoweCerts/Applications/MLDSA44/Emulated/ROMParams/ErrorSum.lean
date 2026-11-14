-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Generated.MLDSA44.Emulated.ROMParams.Data
public import GordieHowe.Applications.Program.FiguresCheck

import all GordieHoweCerts.Generated.MLDSA44.Emulated.ROMParams.Program
import all GordieHoweCerts.Generated.MLDSA44.Emulated.ROMParams.Plan

@[expose] public section

/-!
# The summed round errors and the domains of `MLDSA44.Emulated.ROMParams`

The numeric summed round errors of the program (`FigCheck.errorSumN` at the numeric domain
figures) and the number of its domains, decided by the kernel in a module of its own, with the
program and the plan unfolded.
-/

namespace GordieHowe.MLDSA44.Emulated.ROMParams

open GordieHowe RealizedProgram GordieHowe.Generated.MLDSA44.Emulated.ROMParams

/-- **The numeric summed round errors are at most `158982165`**, in units of `2^-errorExp`. -/
theorem errorSumN_le :
    FigCheck.errorSumN data.program
      (@ProgramData.figuresDomains data (CellsReader.ofProgram data.program))
      data.fieldTable.interp.cardN data.figures.sourceErrors data.figures.figures.errorExp ≤
        158982165 := by
  decide +kernel

/-- **The program has `2` domains.** -/
theorem domains_length : Program.program.domains.length = 2 := by
  decide +kernel

end GordieHowe.MLDSA44.Emulated.ROMParams
