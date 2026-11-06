-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Annotations
public import GordieHowe.Language.RealizedProgram.Reader
public import GordieHoweNative.Language.RealizedProgram.WellFormedReader

/-!
# GordieHowe: the compiled well-formedness check through the annotations

Compiled code runs `wellFormedA` at the program's context built once (`wellFormedAC`,
`GordieHoweNative/Language/RealizedProgram/WellFormedReader.lean`): the kernel checker is its
generic form at the kernel's reader by definition (`wellFormedA_eq_reader`), and the context's
reader is the kernel's (`PReader.ofCtx_build`).
-/

public section

namespace GordieHowe.RealizedProgram

theorem wellFormedA_eq_reader (ir : RealizedProgram) (a : ExprAnn) :
    ir.wellFormedA a = @PReader.wellFormedA ir (PReader.ofProgram ir) (PReader.AnnReads.ofAnn a) :=
  rfl

theorem PReader.arrayOr_map_range {α : Type} (f : ℕ → α) (n : ℕ) :
    PReader.arrayOr ((List.range n).map f).toArray f = f := by
  funext j
  simp only [PReader.arrayOr]
  split
  · simp
  · rfl

theorem PReader.AnnArrays.reads_build (a : ExprAnn) (n : ℕ) :
    (PReader.AnnArrays.build a n).reads = PReader.AnnReads.ofAnn a := by
  simp only [PReader.AnnArrays.reads, PReader.AnnArrays.build, PReader.arrayOr_map_range]
  rfl

/-- **Compiled code runs `wellFormedA` at the program's context built once** (`wellFormedAC`). -/
@[csimp] theorem wellFormedA_csimp : @wellFormedA = @wellFormedAC := by
  funext ir a
  rw [wellFormedA_eq_reader, wellFormedAC]
  show _ = @PReader.wellFormedA ir (PReader.ofCtx (PCtx.build ir))
    (PReader.AnnArrays.build a ir.exprs.length).reads
  rw [PReader.ofCtx_build, PReader.AnnArrays.reads_build]

end GordieHowe.RealizedProgram
