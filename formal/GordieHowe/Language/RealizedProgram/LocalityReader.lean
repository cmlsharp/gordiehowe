-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Locality
public import GordieHowe.Language.RealizedProgram.Reader
public import GordieHoweNative.Language.RealizedProgram.LocalityReader

/-!
# GordieHowe: the compiled locality check

Compiled code runs the locality check (`localWithB`) at a context built once (`localWithBC`, in
`GordieHowe/Language/RealizedProgram/LocalityReader.lean` of `GordieHoweNative`), by
`localWithB_csimp`: the kernel checker is its generic form at the kernel's reader, by definition
(`localWithB_eq_reader`), and the context's reader is the kernel's (`LReader.ofCtx_build`): its
program reader's (`PReader.ofCtx_build`), and each domain's tables the kernel's, computed once.
-/

public section

namespace GordieHowe.RealizedProgram

theorem localWithB_eq_reader (ir : RealizedProgram) (ch : ℕ → Option ℕ)
    (treeNodes : ℕ → List String) :
    ir.localWithB ch treeNodes = @LReader.localWithB ir (LReader.ofProgram ir treeNodes) ch := rfl

theorem getElem?_map_range_toArray' {α : Type} (f : ℕ → α) (n d : ℕ) :
    ((List.range n).toArray.map f)[d]? = if d < n then some (f d) else none := by
  split_ifs with h <;> simp [h]

/-- **The compiled locality check's reader of the program's context is the kernel's.** -/
theorem LReader.ofCtx_build (ir : RealizedProgram) (treeNodes : ℕ → List String) :
    LReader.ofCtx ir treeNodes (LCtx.build ir treeNodes) = LReader.ofProgram ir treeNodes := by
  rw [LReader.ofCtx, LCtx.build, LReader.ofProgram, PReader.ofCtx_build]
  congr 1 <;> funext d <;> rw [getElem?_map_range_toArray'] <;>
    by_cases h : d < ir.domains.length <;> simp only [h, ↓reduceIte] <;> rfl

/-- **Compiled code runs the locality check at the context built once** (`localWithBC`). -/
@[csimp] theorem localWithB_csimp : @localWithB = @localWithBC := by
  funext ir ch treeNodes
  rw [localWithB_eq_reader, localWithBC]
  show _ = @LReader.localWithB ir (LReader.ofCtx ir treeNodes (LCtx.build ir treeNodes)) ch
  rw [LReader.ofCtx_build]

end GordieHowe.RealizedProgram
