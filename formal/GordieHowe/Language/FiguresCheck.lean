-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.FiguresCheck
public import GordieHowe.Language.RealizedProgram.CellsReader

/-! # Compilation of the figures part

The figures reader shares one cells context in compiled checks. This module is independent of
application conditions so the root program checker can import its compilation equality.
-/

public section

namespace GordieHowe.ProgramData

open RealizedProgram

/-- **Compiled figures share the cells context**, with the same checked result. -/
@[csimp] theorem figuresPartB_csimp : @figuresPartB = @figuresPartBC := by
  funext d w
  rw [figuresPartB, figuresPartBC, CellsReader.ofCtx_build]

end GordieHowe.ProgramData
