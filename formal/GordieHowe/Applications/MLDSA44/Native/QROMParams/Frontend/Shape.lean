-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Frontend.Hash
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Frontend.Sample
public import GordieHowe.Generated.MLDSA44.Native.QROMParams.Program

@[expose] public section

/-!
# GordieHowe frontend: domain `H`'s facts of `MLDSA44.Native.QROMParams`

The realized program of the native ML-DSA-44 proof of possession at the QROM parameters (`GordieHowe.Generated.MLDSA44.Native.QROMParams.Program.program`,
export `c825eb05`) has the domain `H` of `MLDSA44.Native.ROMParams` up to its `GF(2^256)` constants: the
program facts of the generic ML-DSA domain-`H` frontend (`MldsaHBase` … `MldsaHSample`, decided on
the program's tables) and, over `GF(2^256)` (`gf256`), the program-and-field facts (`MldsaHConsts`:
constant `37` the embedding basis, the constant of `h2c.sample.mem.unit` and of expression `523`
`θ + 1`), decided in `GF(2^256)`.
-/

namespace GordieHowe.MLDSA44.Native.QROMParams

open Generated.MLDSA44.Native.QROMParams.Program (program)
open ROMParams

set_option maxRecDepth 8192 in
/-- The native program at the QROM parameters has these facts. -/
instance : MldsaHBase program where
  hPreds := by decide +kernel
  hTyped := by decide +kernel
  trKind := rfl

set_option maxRecDepth 8192 in
/-- The native program at the QROM parameters has these facts. -/
instance : MldsaHCross program where
  refsOrdered := (RealizedProgram.refsOrderedB_iff program).1 (by decide +kernel)
  lt525 := by decide +kernel
  lt524 := by decide +kernel
  expr525 := rfl
  expr524 := rfl
  len71 := by decide +kernel
  len523 := by decide +kernel
  len524 := by decide +kernel
  const36 := by decide +kernel
  entries36 := by decide +kernel
  field36 := by decide +kernel
  bitView71 := by decide +kernel
  domainField1 := by decide +kernel

set_option maxRecDepth 8192 in
/-- The native program at the QROM parameters has these facts. -/
instance : MldsaHSelect program where
  bitView555 := by decide +kernel
  bitView556 := by decide +kernel
  bitView559 := by decide +kernel
  pred264 := rfl
  pred265 := rfl
  pred266 := rfl
  expr508 := rfl
  expr509 := rfl
  expr510 := rfl
  expr511 := rfl
  expr512 := rfl
  expr513 := rfl
  expr514 := rfl
  expr515 := rfl
  expr516 := rfl
  expr517 := rfl
  expr518 := rfl
  expr519 := rfl
  refsSel := by decide +kernel
  selConstsA := by
    decide +kernel
  jFacts := by
    decide +kernel
  selLens := by decide +kernel
  stepConsts := by
    decide +kernel
  routeConsts := by
    decide +kernel
  routeLens := by decide +kernel

set_option maxRecDepth 8192 in
/-- The native program at the QROM parameters has these facts. -/
instance : MldsaHHashData program where
  roundShapes := by
    decide +kernel
  round_facts := by
    decide +kernel
  const_states := by
    decide +kernel
  const_rc := by
    decide +kernel

set_option maxRecDepth 8192 in
/-- The native program at the QROM parameters has these facts. -/
instance : MldsaHHash program where
  view_kinds := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  view_facts := by
    decide +kernel
  hash_exprs := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  expr_blk := by
    intro p h2 h7
    fin_cases p <;> first | (exfalso; simp at h2 h7; done) | exact ⟨rfl, rfl⟩
  hash_sizes := by
    decide +kernel
  pad_exprs := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  pad_facts := by
    decide +kernel
  bit_kinds := ⟨rfl, rfl⟩
  kind458 := rfl

set_option maxRecDepth 8192 in
/-- The native program at the QROM parameters has these facts. -/
instance : MldsaHShuffle program where
  phases_pos := by decide
  pred268 := rfl
  pred269 := rfl
  pred270 := rfl
  expr520 := rfl
  expr521 := rfl
  expr522 := rfl
  refsMem := by decide +kernel
  cellFacts := by
    decide +kernel
  memConsts := by
    decide +kernel
  freshLen := by decide +kernel
  pred269_body := rfl
  recConsts := by
    decide +kernel
  recLens := by
    decide +kernel

set_option maxRecDepth 8192 in
/-- The native program at the QROM parameters has these facts. -/
instance : MldsaHSample program where
  kind560 := RealizedProgram.Kind.eq_of_challenge? (by decide +kernel)
  field560 := by decide +kernel
  kind567 := RealizedProgram.Kind.eq_of_challenge? (by decide +kernel)
  field567 := by decide +kernel
  sampleReads_nil := by
    decide +kernel
  isSourceChal_iff := by
    intro j
    constructor
    · intro h
      have hj : j < 4 := h.1
      have key : ∀ j < 4, program.IsSourceChal j → j = 0 ∨ j = 1 := by decide +kernel
      exact key j hj h
    · rintro (rfl | rfl) <;> decide +kernel
  chalFacts := by
    decide +kernel
/-- **Entry `j < 8` of the constant `37` is `g^j`** in `GF(2^256)`, computed. -/
theorem c37_pow : ∀ j < 8,
    gf2_256OfNat ((program.constEntries 37).getD j 0) = gf2_256SubfieldGen ^ j := by
  decide +kernel

/-- The native program at the QROM parameters, over `GF(2^256)`: entry `j < 8` of the constant `37` is `g^j = e_j`. -/
instance : MldsaHConstsSelect program RealizedProgram.gf256 where
  c37 j hj := c37_pow j hj

set_option maxRecDepth 8192 in
/-- The native program at the QROM parameters, over `GF(2^256)`: the constant of `h2c.sample.mem.unit` is `θ + 1`. -/
instance : MldsaHConsts program RealizedProgram.gf256 where
  theta := ⟨340282366920938463481821351509772796213, rfl, rfl, by decide +kernel⟩

end GordieHowe.MLDSA44.Native.QROMParams
